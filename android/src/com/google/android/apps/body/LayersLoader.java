// Copyright 2011 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package com.google.android.apps.body;

import android.content.Context;
import android.graphics.Bitmap;
import android.graphics.Color;
import android.opengl.ETC1Util;
import android.os.Handler;
import android.util.Log;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.ShortBuffer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import com.google.android.apps.body.Render.Draw;
import com.google.android.apps.body.Render.DrawGroup;

/**
 * Responsible for loading all the layers of a body model.
 *
 * See README.txt for threading notes.
 */
class LayersLoader implements Runnable {

    /** Maps texture filenames to texture resources. */
    @SuppressWarnings("serial")
    static final Map<String, Integer> TEXTURES = new HashMap<String, Integer>() {{
        // FIXME(thakis): Put textures in assets/ instead.
    }};

    /** The next free color index. Every Draw has a unique color index assigned to it. */
    private short mMaxColorIndex = 1;

    /** Maps from color index to the corresponding Draw. */
    private Map<Integer, Draw> mSelectionColorMap = new HashMap<Integer, Draw>();

    /** Used to notify clients when a single layer has finished loading. */
    public interface Callback {
        public void finishLayerLoad(Results r, boolean isLoadDone);
    }

    /**
     * Contains the decoded data for a loaded layer.
     */
    public static class Results {
        public Results(int layerId, Render.DrawGroup[] groups,
                Map<Integer, Draw> colorMap, int maxColorIndex) {
            this.layerId = layerId;
            this.groups = groups;
            // All layers share one map, so handing this out after one layer is loaded
            // leads to raciness. Hence, hand out a copy.
            this.selectionColorMap = new HashMap<Integer, Render.Draw>(colorMap);
            this.maxColorIndex = maxColorIndex;
        }

        /** Layer id, see {@code Layers}. */
        int layerId;

        /** The layer's draw groups. */
        Render.DrawGroup[] groups;

        /** The selection color map of all layers loaded so far. */
        // TODO(thakis): Let this be an array instead.
        Map<Integer, Draw> selectionColorMap;

        /** The highest key in {@code selectionColorMap}. */
        int maxColorIndex;
    }

    /** Set to true by the UI to cancel a load. */
    private volatile boolean mCancelled = false;

    private Context mContext;
    private Callback mCallback;
    private Map<Integer, Integer> mLayerResources;
    private Handler mHandler;

    // Direct byte buffers are kind of stupid: The only way to get data in is
    // to call their put() method, which is a virtual method call _and_ a JNI
    // hop. It's faster to make a gratuitous copy of the data into an array so
    // that put() can be called less often :-/ This is this decode buffer.
    final static int BUFSIZE = 8192;
    static short[] mBuffer;

    /**
     * Creates a new LayersLoader. The load is kicked off by calling the
     * {@link #run()} method, and the callback is called every time a
     * layer has completed loading.
     *
     * @param context The context to load resources from.
     * @param callback Notified every time a layer has finished loading.
     * @param layerResources A map from layer id to the resource of the
     *     corresponding layer json resource.
     * @param handler Handler to the thread the callback is called on.
     */
    LayersLoader(Context context, Callback callback,
            Map<Integer, Integer> layerResources, Handler handler) {
        this.mContext = context;
        this.mCallback = callback;
        this.mLayerResources = layerResources;
        this.mHandler = handler;
    }

    private void createColorBuffer(DrawGroup drawGroup) {
        int numVertices = drawGroup.vertexBufferData.capacity() / 8;  // 3 pos, 3 norm, 2 texcoord

        ByteBuffer byteBuffer = ByteBuffer.allocateDirect(numVertices * 2);
        byteBuffer.order(ByteOrder.nativeOrder());
        drawGroup.colorBufferData = byteBuffer.asShortBuffer();

        for (Draw draw : drawGroup.draws) {
            short selectionColor = mMaxColorIndex++;
            mSelectionColorMap.put((int) selectionColor, draw);

            BodyJni.setColorForIndices(
                    drawGroup.colorBufferData, selectionColor,
                    drawGroup.indexBufferData, draw.offset, draw.count);
        }
    }

    /** A helper class that can load a slice of data described by an {@code
     * FP.FPEntry} from a larger set of data.
     */
    private static abstract class Loader {
        protected Render.DrawGroup group;
        protected FP.FPEntry entry;

        Loader(Render.DrawGroup group, FP.FPEntry entry) { this.group = group; this.entry = entry; }
        abstract void load(char[] data);
    }

    private static ShortBuffer decodeIndexBuffer(
            DrawGroup drawGroup, char[] data, int start, int length) {
        ByteBuffer byteBuffer = ByteBuffer.allocateDirect(length * 2);
        byteBuffer.order(ByteOrder.nativeOrder());
        ShortBuffer indexData = byteBuffer.asShortBuffer();
        int prev = 0;
        for (int i = 0; i < length;) {
            int limit = Math.min(length - i, BUFSIZE);
            int s = start + i;
            for (int j = 0; j < limit; ++j) {
                int word = data[s + j];
                prev += (word >> 1) ^ (-(word & 1));
                mBuffer[j] = (short)prev;
            }
            i += limit;
            indexData.put(mBuffer, 0, limit);
        }
        indexData.rewind();
        return indexData;
    }

    private static class IndexLoader extends Loader {
        IndexLoader(Render.DrawGroup dg, FP.FPEntry entry) { super(dg, entry); }
        void load(char[] data) {
            group.indexBufferData = decodeIndexBuffer(group, data, entry.start, entry.length);
        }
    }

    private static ShortBuffer decodeVertexBuffer(
            DrawGroup drawGroup, char[] data, int start, int length) {
        ByteBuffer byteBuffer = ByteBuffer.allocateDirect(length * 2);
        byteBuffer.order(ByteOrder.nativeOrder());
        ShortBuffer vertexData = byteBuffer.asShortBuffer();
        short prev0 = 0, prev1 = 0, prev2 = 0, prev3 = 0;
        short prev4 = 0, prev5 = 0, prev6 = 0, prev7 = 0;
        for (int i=0; i<length;) {
            int limit = Math.min(length - i, BUFSIZE);
            int s = start + i;
            for (int j = 0; j < limit;) {
                short word = (short) data[s + j];
                prev0 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)(prev0 - 8192);
                word = (short) data[s + j];
                prev1 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)(prev1 - 4096);
                word = (short) data[s + j];
                prev2 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)(prev2 - 8192);
                word = (short) data[s + j];
                prev3 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)((prev3 - 256) << 7);
                word = (short) data[s + j];
                prev4 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)((prev4 - 256) << 7);
                word = (short) data[s + j];
                prev5 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)((prev5 - 256) << 7);
                word = (short) data[s + j];
                prev6 += (word >> 1) ^ (-(word & 1));
                mBuffer[j++] = (short)prev6;
                word = (short) data[s + j];
                prev7 += (word >> 1) ^ (-(word & 1));
                // The web version flips the tex images instead.
                mBuffer[j++] = (short)(512 - prev7);
            }
            i += limit;
            vertexData.put(mBuffer, 0, limit);
        }
        vertexData.rewind();

        return vertexData;
    }

    private static class AttribLoader extends Loader {
        AttribLoader(Render.DrawGroup dg, FP.FPEntry entry) { super(dg, entry); }
        void load(char[] data) {
            group.vertexBufferData = decodeVertexBuffer(group, data, entry.start, entry.length);
        }
    }

    private void loadTexture(Context context, Render.DrawGroup drawGroup) {
        if (drawGroup.texture != null) {
            int resource = TEXTURES.get(drawGroup.texture.toLowerCase());

            InputStream is = context.getResources().openRawResource(resource);
            try {
                ETC1Util.ETC1Texture tex = ETC1Util.createTexture(is);
                is.close();
                drawGroup.loadedCompressedDiffuseTexture = tex;
            } catch (IOException e) {
                Log.e("Body", "Loading texture: " + e);
            }
        } else {
            int[] color = { Color.rgb(
                    (int)(drawGroup.diffuseColor[0] * 255 + 0.5),
                    (int)(drawGroup.diffuseColor[1] * 255 + 0.5),
                    (int)(drawGroup.diffuseColor[2] * 255 + 0.5))
            };
            Bitmap bitmap = Bitmap.createBitmap(color, 1, 1, Bitmap.Config.RGB_565);
            drawGroup.loadedDiffuseTexture = bitmap;
        }
    }

    /**
     * Loads a resource containing json text into a {@code JSONObject}.
     * @param context The context to load the resource from.
     * @param resource Resource identifier.
     * @return The result of loading and parsing the resource.
     *     {@code null} on error.
     */
    public static JSONObject loadJsonResource(Context context, int resource) {
        BufferedReader reader = new BufferedReader(
                new InputStreamReader(context.getResources().openRawResource(resource)));
        StringBuffer stringBuffer = new StringBuffer();
        try {
            // TODO(thakis): This is sad.
            String s;
            while ((s = reader.readLine()) != null)
                stringBuffer.append(s);
        } catch (IOException e) {
            Log.e("Body", e.toString());
        } finally {
            try {
                reader.close();
            } catch (IOException e) {
                Log.e("Body", e.toString());
            }
        }
        JSONObject object;
        try {
            object = new JSONObject(stringBuffer.toString());
        } catch (JSONException e) {
            Log.e("Body", e.toString());
            return null;
        }
        return object;
    }

    /** Synchronously loads a single layer. */
    private Render.DrawGroup[] load(Context context, int layerResource) {
        // TODO(thakis): this method is kinda ugly.
        // TODO(thakis): if we can bundle the resource files, rewrite them so that no conversion
        //               needs to happen at load time. The utf8 stuff is clever, but mostly overhead
        //               for local files.

        // Timers for different loading phases.
        float jsonReadS = 0;
        float jsonParseS = 0;
        float textureS = 0;
        float fileReadS = 0;
        float fileDecodeS = 0;
        float colorBufferS = 0;

        Render.DrawGroup[] drawGroups = null;

        long jsonReadStartNS = System.nanoTime();
        JSONObject object = loadJsonResource(context, layerResource);
        jsonReadS = (System.nanoTime() - jsonReadStartNS) / 1e9f;

        long jsonParseStartNS = System.nanoTime();
        Map<Integer, List<Loader>> toBeLoaded = new HashMap<Integer, List<Loader>>();
        try {
            JSONArray dataDrawGroups = object.getJSONArray("draw_groups");
            drawGroups = new Render.DrawGroup[dataDrawGroups.length()];
            for (int i = 0; i < drawGroups.length; ++i) {
                if (mCancelled) return null;

                JSONObject drawGroup = dataDrawGroups.getJSONObject(i);
                drawGroups[i] = new Render.DrawGroup();
                if (drawGroup.has("texture"))
                    drawGroups[i].texture = drawGroup.getString("texture");
                else if (drawGroup.has("diffuse_color")) {
                    JSONArray color = drawGroup.getJSONArray("diffuse_color");
                    drawGroups[i].diffuseColor = new float[3];
                    for (int j = 0; j < 3; ++j)
                        drawGroups[i].diffuseColor[j] = (float)color.getDouble(j);
                }
                JSONArray draws = drawGroup.getJSONArray("draws");
                drawGroups[i].draws = new ArrayList<Render.Draw>(draws.length());
                for (int j = 0; j < draws.length(); ++j) {
                    JSONObject jsonDraw = draws.getJSONObject(j);
                    Render.Draw draw = new Render.Draw();
                    draw.geometry = jsonDraw.getString("geometry");
                    draw.offset = jsonDraw.getJSONArray("range").getInt(0);
                    draw.count = jsonDraw.getJSONArray("range").getInt(1);
                    drawGroups[i].draws.add(draw);
                }
                long textureReadStartNS = System.nanoTime();
                loadTexture(mContext, drawGroups[i]);
                textureS += (System.nanoTime() - textureReadStartNS) / 1e9f;

                String indices = drawGroup.getString("indices");
                FP.FPEntry indicesFP = FP.get(indices);
                if (toBeLoaded.get(indicesFP.file) == null)
                    toBeLoaded.put(indicesFP.file, new ArrayList<Loader>());
                toBeLoaded.get(indicesFP.file).add(new IndexLoader(drawGroups[i], indicesFP));

                String attribs = drawGroup.getString("attribs");
                FP.FPEntry attribsFP = FP.get(attribs);
                if (toBeLoaded.get(attribsFP.file) == null)
                    toBeLoaded.put(attribsFP.file, new ArrayList<Loader>());
                toBeLoaded.get(attribsFP.file).add(new AttribLoader(drawGroups[i], attribsFP));

                drawGroups[i].numIndices = drawGroup.getInt("numIndices");
            }
        } catch (JSONException e) {
            Log.e("Body", e.toString());
        }
        jsonParseS = (System.nanoTime() - jsonParseStartNS) / 1e9f - textureS;

        for (int resource : toBeLoaded.keySet()) {
            if (mCancelled) return null;

            long fileReadStartNS = System.nanoTime();
            char[] data = new char[0];
            InputStream is = mContext.getResources().openRawResource(resource);
            try {
                // Comment from the ApiDemo content/ReadAsset.java in the Android SDK:
                // "We guarantee that the available method returns the total
                //  size of the asset...  of course, this does mean that a single
                //  asset can't be more than 2 gigs."
                data = new char[is.available()];
                Reader in = new InputStreamReader(is, "UTF-8");
                in.read(data, 0, data.length);
            } catch (UnsupportedEncodingException e) {
                Log.e("Body", e.toString());
            } catch (IOException e) {
                Log.e("Body", e.toString());
            } finally {
                try {
                    is.close();
                } catch (IOException e) {
                    Log.e("Body", e.toString());
                }
            }
            fileReadS += (System.nanoTime() - fileReadStartNS) / 1.0e9f;
            long fileDecodeStartNS = System.nanoTime();
            for (Loader l : toBeLoaded.get(resource)) {
                if (mCancelled) return null;

                l.load(data);
            }
            fileDecodeS += (System.nanoTime() - fileDecodeStartNS) / 1.0e9f;
        }

        long colorBufferStartNS = System.nanoTime();
        for (Render.DrawGroup drawGroup : drawGroups) {
            if (mCancelled) return null;
            createColorBuffer(drawGroup);
        }
        colorBufferS = (System.nanoTime() - colorBufferStartNS) / 1e9f;

        Log.i("Body", "JSON read: " + jsonReadS + ", JSON parse: " + jsonParseS + ", texture: " +
                textureS + ", res read: " + fileReadS + ", res decode: " +
                fileDecodeS + ", colorbuf: " + colorBufferS);

        return drawGroups;
    }

    /**
     * Stops the loading as soon as possible. Since LayersLoader doesn't wait()
     * or sleep(), we don't have to use the interruption facilities of thread.
     * 
     * The loader checks this flag several times during a layer load, making it
     * possible to cancel it with a latency of less than 0.5s. 
     */
    public void cancel () { mCancelled = true; }

    @Override
    public void run() {
        long totalStart = System.nanoTime();
        mMaxColorIndex = 1;
        mBuffer = new short[BUFSIZE];
        int layerIndex = 0;
        for (Integer layerId : mLayerResources.keySet()) {
            if (mCancelled) break;

            long start = System.nanoTime();
            Log.i("Body", "\nLoading layer " + layerId);
            Render.DrawGroup[] dgs = load(mContext, mLayerResources.get(layerId));
            Log.i("Body", "Layer took " + (System.nanoTime() - start) / 1e9f + " s");
            ++layerIndex;

            if (dgs != null && !mCancelled) {
                final Results results =
                        new Results(layerId, dgs, mSelectionColorMap, mMaxColorIndex);
                final int currentLayerIndex = layerIndex;
                mHandler.post(new Runnable() {
                        @Override
                        public void run() {
                            mCallback.finishLayerLoad(results,
                                                      currentLayerIndex == mLayerResources.size());
                        }});
            }
        }

        // Free the decoding buffer.
        mBuffer = null;

        Log.d("Body", "All layers took " + (System.nanoTime() - totalStart) / 1e9f + " s " +
                      "(cancelled: " + mCancelled + ")");
    }
}

import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import wasm from "vite-plugin-wasm";

export default defineConfig({
  plugins: [wasm(), react()],
  server: {
    port: 5173,
    strictPort: false,
    proxy: {
      "/liquidtestnet-api": {
        target: "https://liquidtestnet.com",
        changeOrigin: true,
        rewrite: (path) => path.replace(/^\/liquidtestnet-api/, "/api"),
      },
    },
  },
  build: {
    target: "es2022",
  },
});

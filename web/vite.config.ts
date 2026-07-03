import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { defineConfig } from "vite";
import type { Plugin } from "vite";
import react from "@vitejs/plugin-react";
import wasm from "vite-plugin-wasm";

const paperPdfPath = fileURLToPath(
  new URL("../permissionless-simplicity-multisig/out/main.pdf", import.meta.url),
);

// Serve the whitepaper in development when it has been built with `make pdf`.
// Deployments copy the PDF next to the app instead (.github/workflows/pages.yml).
function servePaperPdf(): Plugin {
  return {
    name: "serve-paper-pdf",
    configureServer(server) {
      server.middlewares.use("/paper.pdf", (_request, response, next) => {
        if (!existsSync(paperPdfPath)) {
          next();
          return;
        }
        response.setHeader("Content-Type", "application/pdf");
        response.end(readFileSync(paperPdfPath));
      });
    },
  };
}

export default defineConfig({
  plugins: [wasm(), react(), servePaperPdf()],
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

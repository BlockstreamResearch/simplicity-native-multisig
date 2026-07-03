# Web

Browser demo for the Simplicity native multisig on Liquid testnet.

It drives the full on-chain coordination flow: creating a multisig descriptor,
publishing and discovering participant descriptor announcements (`SIMPANNC`),
creating and discovering vote proposals (`SIMPVOTE`), and finalizing spends.
Contract logic runs in the browser through the WASM bindings from
`crates/wasm`; wallet scanning uses LWK.

## Development

```bash
npm install
npm run dev
```

`npm run dev` rebuilds the WASM bindings first (requires `wasm-pack`), then
starts Vite on `127.0.0.1`.

## Tests

```bash
npm run test:ui
```

Runs the Playwright end-to-end tests.

## Deployment

The app is fully static: contract logic runs in WASM and chain access goes
directly to public esplora/waterfalls APIs, so any static host works.
`.github/workflows/pages.yml` builds the site (including the paper at
`/paper.pdf`) and deploys it to GitHub Pages on every push to `main`; enable
it once under repository Settings → Pages → Source → GitHub Actions.

For a project page the assets must be built with the repository name as base
path (the workflow does this automatically):

```bash
npm run build -- --base=/simplicity-native-multisig/
```

One caveat: the in-app faucet request buttons only appear in local
development, because the faucet API is reached through the Vite dev-server
proxy (`/liquidtestnet-api`) and has no CORS headers. Hosted builds show a
copy-address button and link to the external faucet page instead.

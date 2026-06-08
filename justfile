set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

default: check

# Generate Simplex contract artifacts.
simplex-build:
    cd crates/contracts && simplex build

# Format Rust code.
fmt:
    cargo fmt --all

# Check Rust formatting.
fmtcheck:
    cargo fmt --all --check

# Run workspace Clippy checks.
clippy:
    cargo clippy --workspace --all-targets --all-features -- -D warnings

# Run Rust Bitcoin Maintainer Tools linting.
rbmt:
    cargo rbmt lint --lock-file existing

# Install Rust toolchains pinned for Rust Bitcoin Maintainer Tools.
rbmt-toolchains:
    cargo rbmt toolchains --lock-file existing

# Run Rust workspace tests.
test:
    cargo test --workspace --all-features

# Run Rust workspace tests with the configured MSRV.
test-msrv:
    cargo +1.91.0 test --workspace --all-features

# Run Simplex contract tests.
simplex-test:
    cd crates/contracts && simplex test --nocapture

# Run the local CI-equivalent check set.
check: simplex-build fmtcheck clippy rbmt test simplex-test

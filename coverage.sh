#!/bin/bash
set -e

# Use LLVM tools bundled with the Rust toolchain
LLVM_BIN="$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | grep host | cut -d' ' -f2)/bin"
LLVM_PROFDATA="$LLVM_BIN/llvm-profdata"
LLVM_COV="$LLVM_BIN/llvm-cov"

rm -rf target/coverage *.profraw *.profdata

RUSTFLAGS="-C instrument-coverage" \
LLVM_PROFILE_FILE="stringly-%p-%m.profraw" \
cargo test --all-features

"$LLVM_PROFDATA" merge -sparse *.profraw -o stringly.profdata

# Find all test binaries (unit tests and integration tests)
BINARIES=$(find target/debug/deps -type f -perm +111 ! -name '*.d' ! -name '*.so' ! -name '*.dylib' ! -name 'build-script-*' | head -20)
FIRST_BIN=$(echo "$BINARIES" | head -1)
OTHER_BINS=$(echo "$BINARIES" | tail -n +2 | sed 's/^/-object=/' | tr '\n' ' ')

"$LLVM_COV" report --instr-profile=stringly.profdata "$FIRST_BIN" $OTHER_BINS

"$LLVM_COV" show \
    --instr-profile=stringly.profdata \
    "$FIRST_BIN" $OTHER_BINS \
    --format=html \
    --output-dir=target/coverage \
    --ignore-filename-regex='/.cargo/registry|/rustc/'

echo "Coverage report: target/coverage/index.html"

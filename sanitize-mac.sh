#!/usr/bin/env bash

set -e
for i in {1..10000}; do
    echo ${i}
    ASAN_OPTIONS=detect_leaks=0 RUST_BACKTRACE=1 RUSTFLAGS="-Z sanitizer=address" cargo test --profile=release-with-debug --target aarch64-apple-darwin --test efrb-tree -- --nocapture
    ASAN_OPTIONS=detect_leaks=0 RUST_BACKTRACE=1 RUSTFLAGS="-Z sanitizer=address" cargo test --profile=release-with-debug --target aarch64-apple-darwin --test list -- --nocapture
done
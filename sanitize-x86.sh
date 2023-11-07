#!/usr/bin/env bash

set -e
for i in {1..10000}; do
    echo ${i}
    ASAN_OPTIONS=detect_leaks=0 RUSTFLAGS="-Z sanitizer=address" cargo test --profile=release-with-debug x86_64-unknown-linux-gnu -- ebr --nocapture
    RUSTFLAGS="-Z sanitizer=address" cargo test --profile=release-with-debug x86_64-unknown-linux-gnu -- hp --nocapture
done
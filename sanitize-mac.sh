#!/usr/bin/env bash

set -e
for i in {1..10000}; do
    echo ${i}
    RUSTFLAGS="-Z sanitizer=address" cargo test --profile=release-with-debug --target aarch64-apple-darwin -- --nocapture
done
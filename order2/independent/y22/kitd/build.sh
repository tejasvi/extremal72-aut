#!/bin/bash
# This box has no gcc: engine9 and tests/mincheck are prebuilt static binaries (gcc 15.2 -O3 -march=znver5 -static
# on the main VM, <CPU>); sha256 in SHA256SUMS. Nothing to build.
echo "prebuilt static binaries; verify with sha256sum -c SHA256SUMS"

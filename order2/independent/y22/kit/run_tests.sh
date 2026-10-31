#!/bin/bash
# Box-side checks: engine data encoding test and end-to-end formulation test (needs python3, ./build.sh first).
set -e
cd "$(dirname "$0")"
mkdir -p tmp
export TMPDIR=$PWD/tmp
nice -n 10 python3 -I tests/test_encoding.py sep_I28b.eng tests/sep_I28b_prep.pkl 22
nice -n 10 python3 -I tests/test_e2e.py y22 11

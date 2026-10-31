#!/bin/bash
# valcheckbox.sh CODE : frozen/check_box.sh (keep build) against bin/lwe8 for one explore code directory; log in logs/val/
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
LWE8=<HOME>/c72/c2opt/alg/bin/lwe8 /usr/bin/time -f "%e s wall" frozen/check_box.sh <HOME>/c72/explore/runs2/$1 keep > logs/val/checkbox_$1.log 2>&1

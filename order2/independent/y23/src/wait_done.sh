#!/bin/bash
while [ ! -f <HOME>/c72_indep/y23/out/join/driver_done.txt ]; do sleep 120; done
echo Y23_JOIN_DONE

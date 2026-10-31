#!/bin/bash
# Waits until the wave-2 kit holds at most 10 processes (its CAP_g), then runs the LTSB wave in this kit (audit code).
K=$HOME/audit_c2/kit
cnt() { find /proc -mindepth 2 -maxdepth 2 -name cwd -user $(id -u) \( -lname "$K" -o -lname "$K/*" \) 2>/dev/null | wc -l; }
while [ $(cnt) -gt 10 ]; do sleep 30; done
exec ./run_lb.sh

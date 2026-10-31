#!/bin/bash
# fleet57 (audit code, 2026-10-22): remove the stray subshells of the first launch and the old CAP raiser (argv checked),
# set up kit6x (the y26f-lb / y12-lb2 tasks, own working directory and cap 14, sharing kit6's bin, pkgs, scripts), and a
# raiser that gives kit6 a cap of 30 once kit6x is done.  kit6 keeps cap 16 until then: 16 + 14 + 2 = 32 processes.
set -u
H=$HOME/audit_c2
for p in 47707 47708 47709 47712; do
  a=$(tr "\0" " " < /proc/$p/cmdline 2>/dev/null) || { echo "$p gone"; continue; }
  case "$a" in
    "bash -c export TMPDIR=\$HOME/audit_c2/kit6/tmp; mkdir -p \$TMPDIR;"*|"bash -c sleep 1200; echo 32 > $H/kit6/CAP "|"sleep 1200 ") kill $p && echo "killed $p";;
    *) echo "SKIP $p: $a";;
  esac
done
mkdir -p $H/kit6x/logs $H/kit6x/work $H/kit6x/tmp
cd $H/kit6x || exit 1
ln -sfn ../kit6/bin bin; ln -sfn ../kit6/pkgs pkgs; ln -sfn ../kit6/scripts scripts
cp ../kit6/runtask6.sh ../kit6/run_all6.sh .; cp ../kit6/tasks6_extra.txt tasks6.txt; echo 14 > CAP; echo 16 > ../kit6/CAP
ls -la pkgs/y26f-lb/ pkgs/y12-lb2/ | grep -c "inst.txt\|sym.lts"

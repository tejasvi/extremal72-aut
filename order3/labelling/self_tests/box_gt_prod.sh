# run on a gtestS machine: binary gtestS.prod in $GT_DIR (default $HOME/c3class); input in $T (default $HOME/boxtest)
T=${BOXTEST_DIR:-$HOME/boxtest}
cd "${GT_DIR:-$HOME/c3class}" || exit 1; B=./gtestS.prod
echo "BIN $(sha256sum $B | cut -c1-16)"
$B E $T/boxtest_in.txt 2>&1 | grep '^code ' > $T/out_gt_E.txt
$B P 0.285 11 2>&1 | grep '^planted' > $T/out_gt_P.txt
$B Z 0.005 1 2>&1 | grep '^sextetZ' > $T/out_gt_Z.txt
cat $T/out_gt_E.txt $T/out_gt_P.txt $T/out_gt_Z.txt

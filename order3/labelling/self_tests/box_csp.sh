# run on a csp5p machine: $1 = kit dir; input boxtest_in.txt in $T (default $HOME/boxtest)
T=${BOXTEST_DIR:-$HOME/boxtest}
cd "$1" || exit 1
echo "BIN $(sha256sum csp5p_static_v3 | cut -c1-16) OCT $(sha256sum octdod.txt | cut -c1-16)"
env -u STOP16 -u PLANT -u COUNT ./csp5p_static_v3 24 E $T/boxtest_in.txt octdod.txt 2>&1 | grep '^id=' > $T/out_csp_E.txt
env -u STOP16 PLANT=11 COUNT=1 ./csp5p_static_v3 24 E $T/boxtest_in.txt octdod.txt 2>&1 | grep '^id=' > $T/out_csp_PLANT.txt
cat $T/out_csp_E.txt $T/out_csp_PLANT.txt

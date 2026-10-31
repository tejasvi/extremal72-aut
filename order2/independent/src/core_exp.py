"""Find a minimal infeasible core of words for the U-part problem (depth <= DMAX) of one X prefix."""
import sys, pickle, subprocess, os
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import wt
from y39_struct import *
D = "<HOME>/c72_indep/"
eng, prep, pref, dmax = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
pk = pickle.load(open(prep, "rb"))
words, fdepth = pk["words"], pk["full_depth"]
env = dict(os.environ, TMPDIR=D + "tmp")
open(D + "tmp/pref1.txt", "w").write(pref + "\n")
def feasible(active):
    open(D + "tmp/mask.txt", "w").write("\n".join(map(str, sorted(active))) + "\n")
    out = subprocess.run(["nice", "-n", "10", D + "src/engine2", eng, "feas", D + "tmp/pref1.txt", "40", str(dmax), D + "tmp/mask.txt"],
                         capture_output=True, text=True, env=env).stdout
    line = [l for l in out.split("\n") if l.startswith("FEAS")][0].split()
    return int(line[3]), int(line[4])
# candidate words: those with full depth <= dmax (plus all words is safe; restrict for speed)
cand = [i for i in range(len(words)) if fdepth[i] <= dmax]
print("candidates", len(cand), "feasible(all)?", feasible(set(range(len(words)))))
act = set(cand)
print("feasible(cand only)?", feasible(act))
for i in sorted(cand, key=lambda i: -fdepth[i]):
    trial = act - {i}
    f, nodes = feasible(trial)
    if not f:
        act = trial
print("core size", len(act))
def typ(y):
    return (wt(y), wt(y & m18), wt(y & m16), wt(y & m2))
from collections import Counter
print("core types", Counter(typ(words[i]) for i in act))
print("core:", sorted(act))
print("feasible(core)?", feasible(act))

"""Check pairwise inequivalence of the 41 codes via nauty canonical labelling (hash of canonical graph)."""
import sys, json, subprocess, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import low_weight_words_spanning
codes = json.load(open(HERE + '/data/codes41.json'))
hashes = []
for c in codes:
    w, words = low_weight_words_spanning(c['basis'], 36)
    N = 36 + len(words)
    adj = [[] for _ in range(N)]
    for j, ww in enumerate(words):
        for i in range(36):
            if (ww >> i) & 1:
                adj[i].append(36 + j)
    lines = ["c", "-a", "n=%d g" % N] + [" ".join(map(str, adj[i])) + ";" for i in range(N)]
    lines[-1] = lines[-1][:-1] + "."
    lines += ["f=[0:35|36:%d]" % (N - 1), "x", "z"]
    out = subprocess.run(["dreadnaut"], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout
    m = re.search(r"\[(\S+) (\S+) (\S+)\]", out)
    h = (w, len(words), m.group(0))
    hashes.append(h)
    print(c['idx'], h, flush=True)
print("distinct canonical hashes:", len(set(hashes)), "of", len(hashes))

import sys, json
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from autgroup import low_weight_spanning_set, aut_group
d = json.load(open("<HOME>/c72_indep/out/control.json"))
Y48 = d["Y48"]
S, w = low_weight_spanning_set(Y48, 24)
order, gens = aut_group(S, 24)
print("words of weight <=", w, "span Y48:", len(S), "|Aut(Y48)| =", order, "-> expected solutions mod gauge = |Aut|/24 =", order / 24)

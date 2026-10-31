import sys, json, pickle
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from engine_prep import *
from orders import greedy_word_order
d = json.load(open("<HOME>/c72_indep/out/control.json"))
Y48 = d["Y48"]; C = d["QR48_recoord_basis"]
P = Problem(Y48, 24, 12)
print("low words", len(P.low), "Eof", {w: P.Eof[w] for w in (6, 8, 10)})
print("gauge rank", rank(P.gauge, P.FS.N), "diag rank", rank([f for f, c in P.diag], P.FS.N))
# QR48's own form: for basis y_i find c in C with c0+c1 = y_i
mask = (1 << 24) - 1
from linalg import Elim
E = Elim()
for t, c in enumerate(C):
    E.add((c & mask) ^ (c >> 24), 1 << t)
M = []
c0s = []
for yi in Y48:
    combo, resid = E.express(yi)
    assert resid == 0
    c = 0
    for t in range(len(C)):
        if combo >> t & 1: c ^= C[t]
    assert (c & mask) ^ (c >> 24) == yi
    c0s.append(c & mask)
M = [sum(dot(c0s[i], Y48[j]) << j for j in range(12)) for i in range(12)]
print("QR48 form valid:", P.is_valid_form(M))
rows = P.code_CB(M)
assert rank(rows + C, 48) == 24 and rank(rows, 48) == 24
print("C_B(QR48 form) == QR48 (recoordinatized): True")
order = greedy_word_order(P)
ED = EngineData(P, order, Rmax=3)
print("nv", ED.nv, "events", len(ED.events))
ED.write("<HOME>/c72_indep/out/control2.eng")
v = ED.vars_from_form(M)
print("QR48 form vars: %032x" % v)
print("direct check of QR48 form: bad words =", len(ED.check_form(M)))
pickle.dump({"order": order, "M_qr": M, "v_qr": v}, open("<HOME>/c72_indep/out/control_prep.pkl", "wb"))

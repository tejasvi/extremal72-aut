"""Word orders for variable selection."""
import sys
sys.path.insert(0, "<HOME>/c72_indep/y23/src")
from linalg import Elim
from codes import wt


def greedy_word_order(P, words=None, max_words=None):
    """Repeatedly pick the word whose syndrome functionals add the fewest new dimensions (mod diag + chosen);
    ties broken by lower weight then list order."""
    FS = P.FS
    words = list(words if words is not None else P.low)
    funcs = {y: [FS.functional(y, x) for x in P.shortened_basis(y)] for y in words}
    E = Elim()
    for t, (f, c) in enumerate(P.diag):
        E.add(f, 0)
    order, remaining = [], list(words)
    while remaining and (max_words is None or len(order) < max_words):
        best = None
        for y in remaining:
            # count new dims
            tmp = Elim(); tmp.rows = dict(E.rows)
            r = 0
            for f in funcs[y]:
                ok, _ = tmp.add(f, 0)
                r += ok
            key = (r, wt(y))
            if best is None or key < best[0]:
                best = (key, y)
        y = best[1]
        for f in funcs[y]:
            E.add(f, 0)
        order.append(y)
        remaining.remove(y)
    return order

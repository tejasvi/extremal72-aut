# Shared inputs for the exclusion tiers: independent re-search status and audit coverage per code.
# CLI: python -I excl_common.py indep CODE            -> "status<TAB>text"
#      python -I excl_common.py audit PKG MANIFEST    -> "status<TAB>text"
import hashlib, os, re, sys

IND = '<HOME>/c72_indep'
COV = os.environ.get('C2E_TEST_COV', '<HOME>/c72/audit/c2audit/c3')   # override only for tests
RUNNING = set()                       # project, 2026-10-22: Y22 done 02:55, Y18 done 07:00; no separate-method run in progress
CROSS30 = {16, 17, 21, 27, 36, 38}    # project: about 1e5-1e6 CPU-h each with the separate method, not in progress


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def indep(code):
    rep = f'{IND}/REPORT_Y39.md' if code == 39 else f'{IND}/y{code}/REPORT_Y{code}.md'
    if os.path.exists(rep) and f'**Verdict: Y{code} has no solution.**' in open(rep).read():
        return 'done', f'done ({rep}, sha256 {sha(rep)}: "Y{code} has no solution")'
    if code in RUNNING:
        return 'running', f'running ({IND}/y{code}, no report yet)'
    pr = f'{IND}/y{code}/PROGRESS.md'
    if os.path.exists(pr) and 'INFEASIBLE with current designs' in open(pr).read():
        return 'not feasible', f'not feasible (the separate method judged Y{code} INFEASIBLE with its current designs: {pr})'
    if code in CROSS30:
        return 'not feasible', 'not feasible (project: about 1e5-1e6 CPU-h with the separate method; not in progress)'
    return 'none', 'none (not started)'


def audit(pkg, manifest):
    f = f'{COV}/cov_{pkg}.txt'
    if not os.path.exists(f):
        return 'pending', f'pending (no {f} yet)'
    t = open(f).read()
    ms = re.findall(r'^manifest sha256\(([^)]*)\) ([0-9a-f]{64})', t, re.M)
    hit = [d for d, m in ms if m == manifest]
    v = 'PASS' if re.search(r'^VERDICT PASS', t, re.M) else 'NOT PASS'
    if v == 'PASS' and hit:
        return 'PASS', f'PASS ({f}, sha256 {sha(f)[:16]}; its manifest ({hit[0]}) equals mine)'
    if v == 'PASS':
        return 'MISMATCH', f'PASS but no manifest equal to mine ({manifest[:16]}) in {f}'
    return 'FAIL', f'{v} ({f})'


def ltsb_audit(pkg):
    """rc11/lwe11b5 gate condition (1) (project, 2026-10-22 02:15): coverage-check's LTSB semantic check and planted tests on the
    package's own sym.ltsb: ltsbcheck_<pkg>.txt and ltsbplant_<pkg>.txt, each with a 'VERDICT PASS' line."""
    out = []
    for kind in ('ltsbcheck', 'ltsbplant'):
        f = f'{COV}/{kind}_{pkg}.txt'
        if not os.path.exists(f): out.append((kind, 'pending', f'no {f}'))
        elif re.search(r'^VERDICT PASS', open(f).read(), re.M): out.append((kind, 'PASS', f'{f} sha256 {sha(f)[:16]}'))
        else: out.append((kind, 'NOT PASS', f))
    st = 'PASS' if all(o[1] == 'PASS' for o in out) else ('pending' if not any(o[1] == 'NOT PASS' for o in out) else 'FAIL')
    return st, '; '.join(f'{k}: {v} ({t})' for k, v, t in out)


if __name__ == '__main__':
    if sys.argv[1] == 'indep':
        print('\t'.join(indep(int(sys.argv[2]))))
    elif sys.argv[1] == 'ltsb':
        print('\t'.join(ltsb_audit(sys.argv[2])))
    else:
        print('\t'.join(audit(sys.argv[2], sys.argv[3])))

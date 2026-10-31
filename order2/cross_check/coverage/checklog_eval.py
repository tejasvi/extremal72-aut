"""Apply cov_c2.py's check-log rules to single check logs (audit). usage: checklog_eval.py LTSB(0|1) ALLOWED_SHAS LOG..."""
import sys, re
ltsb = sys.argv[1] == '1'; allowed = set(x for x in sys.argv[2].split(',') if x)
NEG = ('DIFFER', 'MISMATCH', 'MISSING', 'NOT LISTED', 'FAILED', 'REFUS', 'PRESENT BUT')
for fn in sys.argv[3:]:
    txt = open(fn).read()
    need = ['inputs OK', 'frozen sources OK', 'PROBE OK']
    miss = [n for n in need if n not in txt]
    m = re.search(r'binary in use: (\S+)', txt)
    if not m: miss.append('binary in use')
    elif allowed and m.group(1) not in allowed: miss.append(f'binary {m.group(1)[:8]} not allowed')
    negs = [x for x in NEG if x in txt]
    end_ok = bool(re.search(r'END \S+ rc 0', txt))
    full = bool(re.search(r'LWE8/LWE11\w* IDENTICAL', txt)) and ((not ltsb) or ('IDENTICAL WITH LTSBFILE' in txt and 'LTSBFILE listed in INPUTS.sha256' in txt))
    ok = not miss and not negs and end_ok
    verdict = ('PASS (full check)' if full else 'PASS only as a light check (needs a full check in its family)') if ok else 'FAIL'
    reuse = 'REFERENCE REUSED' in txt; notreuse = 'REFERENCE NOT REUSED' in txt
    print(f'{fn.split("/")[-1]}: {verdict}; missing {miss}; negative markers {negs}; END rc 0 {end_ok}; reused {reuse}; not-reused {notreuse}')

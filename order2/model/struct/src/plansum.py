"""Regenerate runs/PLAN_SUMMARY.txt from the PLAN.txt files.  Usage: plansum.py STAMP RECOMMENDED(comma) OLDER(comma) [LARGE(comma)]"""
import sys, hashlib, re
B = '<HOME>/c72/c2opt/struct/runs'
stamp, rec, old = sys.argv[1], sys.argv[2].split(','), sys.argv[3].split(',')
large = sys.argv[4].split(',') if len(sys.argv) > 4 else []
keep = ('SPLIT_LEVEL', 'NPART', 'LTSBFILE', 'PROBE_LTS', 'SAMPLE_EST_NODES', 'EST_CPU_CORE_HOURS', 'EST_CPU', 'KEYH0', 'IDENTITY:')
out = [f"# STRUCT run packages (explore runs2 format), updated {stamp}. Frozen tools = copies of explore runs2/frozen + frozen3 (hashes in frozen*/FROZEN.sha256, unchanged).",
       "# Each yNN*/: flag.txt key.txt inst.txt(.meta,.pkl) sym.ltsh INPUTS.sha256 (by frozen/prep_code.py) + PLAN.txt + samples/ (32 box sample-part logs). All passed check_box (inputs, frozen, PROBE, LWE8/LWE10 identity).",
       f"# RECOMMENDED per code, by hostM core-h: {' '.join(rec)}. Older variants ({' '.join(old)}) kept for reference.",
       "# Per box: TMPDIR=<scratch> frozen3/check_box.sh yNN ; frozen3/run_parts.sh yNN SPL NPART FIRST LAST NPROC ; python3 frozen3/sumrun2.py yNN/parts NPART"]
if large: out.insert(3, f"# LARGE / HELD / RC11 (run on the project's decision; rc11 packages (PLAN line LTSBFILE sym.ltsb) = *-lb: y19b-lb y14-lb y0-lb y26f-lb approved and running, y32-lb and y20b-lb replace y32 and y20b; tier D held = y40 y12 y15 (+ their lb/); y19, y26, y26b, y32, y20b superseded): {' '.join(large)}.")
for c in rec + large + old:
    out.append(f"== {c}")
    for l in open(f'{B}/{c}/PLAN.txt'):
        if l.split(' ')[0] in keep: out.append(l.rstrip('\n'))
    h = hashlib.sha256(open(f'{B}/{c}/INPUTS.sha256', 'rb').read()).hexdigest()
    out.append(f"inputs: {c}/INPUTS.sha256 ({h[:16]}...)")
open(f'{B}/PLAN_SUMMARY.txt', 'w').write('\n'.join(out) + '\n')
print(len(rec) + len(large) + len(old), 'entries')

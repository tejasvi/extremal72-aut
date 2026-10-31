"""Write runs/yNN/PLAN.txt for the STRUCT packages from: runs/specs_abs.txt (code, flag file, key words), the box
sample summary (logs/pack/samples_summary.txt, output of boxsrc/sumsamples.py), box prefix times
(logs/pack/prefixtime_box.txt), local probes (logs/pack/probe20k_yNN.txt), raw probes (logs/scan*/...), keyh0."""
import re, os, hashlib, math
B = '<HOME>/c72/c2opt/struct'
desc = {
 '16': ('48', 'STRUCT invariant start s16_210 (ginvstart candidate 210 of Y16, dim<=7 G-invariant start + MAXL continuation by explore flagbeam4)', 'early key: first word from a 3-orbit (complete at level 5) + the earliest checkable words, r=8 (STRUCT rules a,c)'),
 '33': ('128', 'STRUCT fixed-word-first flag fx33 (the G-fixed weight-8 word 6442950720 first + MAXL continuation by flagbeam4)', 'early key: the G-fixed word (S0 = G) + the earliest checkable words, r=8 (rules c,d)'),
 '27': ('128', 'explore MAXL flag inst/y27_mx.flag', 'the G-fixed weight-8 word 806141964 (level 1, S0 = G) + the earliest words (levels 0-2), r=6 (rule c)'),
 '17': ('384', 'explore MAXL flag inst/y17_mx.flag', '8 words of a 16-orbit of weight-8 words, 8 of which are checkable by level 6 (rule a)'),
 '24': ('32', 'STRUCT invariant start s24_354 (ginvstart candidate 354 + MAXL continuation)', 'early key: the G-fixed weight-8 word first + earliest words, r=8 (rules c,d)'),
 '18': ('864', 'explore MAXL flag inst/y18_mx.flag', '8 words of a 36-orbit of weight-8 words (rule a)'),
 '11': ('384', 'explore g2 chain flag inst/y11_g2.flag', '12 words: the G-fixed weight-12 word (level 0, S0 = G) + early words; key stabiliser |H0| = 1 (rule b; a 4-word key had |H0| = 4)'),
 '38': ('48', 'STRUCT invariant start s38_4 (span of a 2-orbit first + MAXL continuation)', 'early key: first word of the 2-orbit + earliest words, r=8'),
 '2':  ('48', 'STRUCT fixed-word-first flag fx2 (G-fixed weight-8 word 51548525616 first + MAXL)', 'early key: the G-fixed word + earliest words, r=8 (rules c,d)'),
 '10': ('96', 'STRUCT invariant start b10_1 (span of a 3-orbit of weight-8 words, dim 2, first + MAXL continuation by flagbeam4)', 'early key: first word of the 3-orbit (complete at level 2) + earliest words, r=8 (rules a,c)'),
 '31': ('12', 'STRUCT flag v31_s2557_l1000: invariant start (ginvstart cand 2557 of Y31, 6w8+3w8, dim 7) + continuation by flagbeam4 with the DEFAULT total-nodes objective (not MAXL), beam 1000', 'early key: the G-fixed weight-8 word 8612093986 (level 2) + earliest words, r=8 (rules c,d)'),
 '6': ('32', 'STRUCT flag v6_b6_9_l3000: invariant start (box ginvstart cand 9 of Y6: G-fixed word 12956993568 + one more word, dim 2) + flagbeam4 total-nodes objective, beam 3000', 'early key: the G-fixed weight-8 word (level 0, S0 = G) + earliest words, r=8 (rules c,d)'),
 '18b': ('864', 'explore flagbeam4 MAXL flag with beam 5000 (no prefix; differs from inst/y18_mx.flag)', '8 words of a 48-orbit of weight-8 words, complete by level 6 (rule a); an early key on this flag is 7.7x worse'),
 '24b': ('32', 'STRUCT flag t24_s354_l1000: invariant start s354 of Y24 + flagbeam4 total-nodes objective (not MAXL), beam 1000', 'early key: the G-fixed weight-8 word first + earliest words, r=8 (rules c,d)'),
 '16b': ('48', 'STRUCT flag t16_s210_l1000: invariant start s210 of Y16 + flagbeam4 total-nodes objective (not MAXL), beam 1000', 'early key: first word from a 3-orbit + earliest words, r=8 (rules a,c)'),
 '10b': ('96', 'STRUCT flag t10_b10_1_l3000: invariant start b10_1 (3-orbit span) + flagbeam4 total-nodes objective, beam 3000', 'early key: first word of the 3-orbit (complete at level 2) + earliest words, r=8'),
 '18c': ('864', 'STRUCT flag u18_w5000_k4_l1000: first 4 vectors of the MAXL beam-5000 flag as forced prefix + flagbeam4 total-nodes objective, beam 1000', 'best-orbit key: 8 words of a 36-orbit (levels 1-4; checkability model), H0 = 1'),
 '11b': ('384', 'STRUCT flag u11_g2_k3_l1000: first 3 vectors of explore g2 flag (G-fixed weight-12 word first) + flagbeam4 total-nodes objective, beam 1000', 'early key: the G-fixed word (level 0, S0 = G) + earliest words, r=8'),
 '27b': ('128', 'STRUCT flag u27_mx_k4_l1000: first 4 vectors of explore MAXL flag + flagbeam4 total-nodes objective, beam 1000', 'early key: the G-fixed weight-8 word 806141964 + earliest words, r=8'),
 '28s': ('96', 'STRUCT flag u28_v828_k3_l1000: first 3 vectors of explore v28_828 flag + flagbeam4 total-nodes objective, beam 1000', 'best-orbit key: 6 words of a 6-orbit (levels 0-4), H0 = 1'),
 '36': ('48', 'STRUCT flag u36_mx_k3_l1000: first 3 vectors of explore MAXL flag + flagbeam4 total-nodes objective, beam 1000', 'best-orbit key: 8 words of a 24-orbit (levels 1-5), H0 = 1'),
 '7': ('80', 'STRUCT flag u7_b300_k4_l1000: first 4 vectors of a MAXL beam-300 flag + flagbeam4 total-nodes objective, beam 1000', 'best-orbit key: 8 words of a 10-orbit (levels 3-14; partial at the peak), H0 = 1'),
 '13': ('64', 'STRUCT flag w13_plain_500: flagbeam4 MAXL with beam 500 (no prefix; differs from inst/y13_mx.flag)', 'early key: the G-fixed weight-8 word 51554437120 (level 2) + earliest words, r=8'),
 '21': ('240', 'STRUCT flag u21_mx_k4_l1000: first 4 vectors of explore MAXL flag + flagbeam4 total-nodes objective, beam 1000', 'best-orbit key: 8 words of a 20-orbit (levels 3-6), H0 = 1'),
 '9': ('24', 'STRUCT flag hc9_a: box hill climb (k-prefix + flagbeam4 total-nodes continuation, beam 3000) from start b9_1; G-fixed weight-8 word 629195392 first', 'early key: the G-fixed word (level 0, S0 = G) + earliest words, r=8'),
 '37': ('64', 'STRUCT fixed-word-first flag fx37 (G-fixed weight-8 word 8858534213 first + MAXL)', 'early key: the G-fixed word + earliest words, r=8 (rules c,d)'),
 '25': ('36', 'STRUCT flag hc25_a: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: 8 words of an 18-orbit of weight-8 words (k0 at level 1; orbit only partly checkable at the peak), H0 = 1'),
 '3': ('288', 'STRUCT flag u3_b1500_k2_l1000: first 2 vectors of a flagbeam4 MAXL beam-1500 flag + flagbeam4 total-nodes objective, beam 1000', 'best-orbit key: 8 words of an 18-orbit of weight-8 words (6 words checkable at levels 4-5, last two at 14), H0 = 1'),
 '30': ('240', 'STRUCT flag hc30_a: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: 8 words of a 15-orbit of weight-8 words (6 checkable at levels 4-6, the last two at 13-14), H0 = 1'),
 '34': ('32', 'STRUCT flag hc34_a: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'early key: the G-fixed weight-8 word 806141964 (level 0, S0 = G) + earliest words, r=8 (rules c,d)'),
 '20': ('96', 'STRUCT flag hc20_a: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: the 6 words of a 6-orbit of weight-8 words (2 checkable at level 4, the rest at 13-15), H0 = 1'),
 '32': ('24', 'STRUCT flag hc32_a: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: the 6 words of a 6-orbit of weight-8 words (3 checkable at levels 1-2, the rest at 9-15), H0 = 1'),
 '20b': ('96', 'STRUCT flag fs2_20: box hill climb over flags scored by real LTS probes (boxsrc/flagsearch2.py: random k-prefix of the current best + flagbeam4 continuation; winner confirmed by exact parts), started from hc20_a', 'best-orbit key: 8 words of a 12-orbit of weight-8 words (key levels 4-6 for four, then 13-14), H0 = 1'),
 '19': ('8', 'STRUCT flag hc19_a: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: the 4 words of a 4-orbit of weight-12 words (levels 5-6), H0 = 1'),
 '14': ('48', 'STRUCT flag hl14: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: the 6 words of a 6-orbit of weight-8 words (levels 3-14), H0 = 1'),
 '0': ('48', 'STRUCT flag hl0: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: the 6 words of a 6-orbit of weight-8 words (levels 4-14), H0 = 1'),
 '40': ('6', 'STRUCT flag hl40: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'early key: the 3-orbit word 583010468 (level 0, S0 of order 2) + earliest words, r=8, H0 = 1'),
 '26': ('24', 'STRUCT flag hl26: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'early key: the G-fixed weight-12 word 15317623837 (level 0, S0 = G) + earliest words, r=8, H0 = 1'),
 '12': ('18', 'STRUCT flag hl12: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: 8 words of a 9-orbit of weight-8 words (levels 5-15), H0 = 1'),
 '15': ('36', 'STRUCT flag hl15: box hill climb over flags (random k-prefix of the current best + flagbeam4 continuation, MAXL or total-nodes objective, beam 300-8000; accepted on the checkability-model estimate)', 'best-orbit key: 8 words of an 18-orbit of weight-8 words (levels 2-14), H0 = 1'),
 '19b': ('8', 'STRUCT flag hc19_a (as y19)', 'key re-selected with the corrected checkability model (keycheck.py KCSHIFT=1): the 4 words of a 4-orbit of weight-8 words (levels 1, 4, 14, 15), H0 = 1'),
 '26b': ('24', 'STRUCT flag hl26 (as y26)', 'key re-selected with the corrected checkability model: 8 words of a 12-orbit of weight-8 words (levels 2-6), H0 = 1'),
}
raw = {'16': '1.667e+14 (s16_210, 50000 probes)', '33': '6.569e+14 (fx33)', '27': '9.320e+14 (y27_mx)', '17': '1.588e+15 (y17_mx)',
       '24': '6.22e+14 (s24_354)', '18': '5.383e+15 (y18_mx)', '11': '7.876e+15 (y11_g2)', '38': '1.53e+15 (s38_4)', '2': '1.860e+15 (fx2)', '37': '3.021e+15 (fx37)', '10': '3.47e+15 (b10_1)', '31': '3.48e+14 (v31_s2557_l1000)', '6': '1.36e+15 (v6_b6_9_l3000)', '18b': '1.9e+15 (w18_plain_5000)', '24b': '1.46e+14 (t24_s354_l1000)', '16b': '5.96e+13 (t16_s210_l1000)', '10b': '1.80e+15 (t10_b10_1_l3000)', '18c': '6.1e+14 (u18_w5000_k4_l1000)', '11b': '5.6e+15 (u11_g2_k3_l1000)', '27b': '8.3e+14 (u27_mx_k4_l1000)', '28s': '1.2e+15 (u28_v828_k3_l1000)', '36': '8.1e+14 (u36_mx_k3_l1000)', '7': '1.6e+15 (u7_b300_k4_l1000)', '13': '2.6e+15 (w13_plain_500)', '21': '3.2e+15 (u21_mx_k4_l1000)', '9': '8.96e+14 (hc9_a)', '25': '1.396e+15 (hc25_a)', '3': '7.492e+15 (u3_b1500_k2_l1000)', '30': '3.361e+16 (hc30_a)', '34': '1.063e+16 (hc34_a)', '20': '9.064e+15 (hc20_a)', '32': '7.374e+15 (hc32_a)', '20b': '9.160e+15 (fs2_20)', '19': '3.447e+15 (hc19_a)', '14': '4.819e+16 (hl14)', '0': '5.133e+16 (hl0)', '40': '2.739e+16 (hl40)', '26': '7.322e+16 (hl26)', '12': '3.639e+16 (hl12)', '15': '6.424e+16 (hl15)', '19b': '3.447e+15 (hc19_a)', '26b': '7.322e+16 (hl26)'}
specs = {l.split()[0]: l.split()[1:] for l in open(f'{B}/runs/specs_abs.txt')}
summ = {}
for l in open(f'{B}/logs/pack/samples_summary.txt'):
    m = re.match(r'y(\w+?) s(\d+) n(\d+): parts (\d+) mean ([\d.e+]+) sd ([\d.e+]+) max/mean ([\d.]+) total ([\d.e+]+) \(\+-([\d.]+)%\) user ([\d.]+)s \(max (\d+)s\) core-h (\d+) prefix ([\d.e+]+)', l)
    if m: summ[m.group(1)] = m.groups()
pre = {}
for l in open(f'{B}/logs/pack/prefixtime_box.txt'):
    for c, s, t in re.findall(r'y(\w+?) spl(\d+) prefix_user ([\d.]+)', l): pre[(c, s)] = float(t)
import sys
only = sys.argv[1:]
for c in desc:
    if only and c not in only: continue
    ci = int(''.join(ch for ch in c if ch.isdigit()))
    G, fdesc, kdesc = desc[c]; fl, key = specs[c]
    sm = summ.get(c)
    probe = [l for l in open(f'{B}/logs/pack/probe20k_y{c}.txt') if 'TOTAL' in l][0].split()[-1]
    spl = int(sm[1]); ns = int(sm[2]); nparts = int(sm[3]); mean = float(sm[4]); tot = float(sm[7]); err = float(sm[8])
    user = float(sm[9]); umax = int(sm[10]); prefix_nodes = float(sm[12]); pt = pre[(c, sm[1])]
    work_s = ns * max(user - pt, 1e-9)           # box user-s for the part work (levels > SPL), excluding prefix
    # production NPART: parts of at most ~2.5 h of lwe10 at box speed (~20 min with a 7x faster engine), power of two x 1000
    npart = 1000
    while work_s / npart > 9000 and npart < 64000: npart *= 2
    while npart > 2000 and npart * pt > 0.02 * work_s: npart //= 2   # keep the prefix overhead <= ~2%
    core_h = (work_s + npart * pt) / 3600
    fsha = hashlib.sha256(open(fl, 'rb').read()).hexdigest()
    lines = [
      f"CODE y{c}  (0-based index in codes36.txt: {ci}; |Aut| {G}; flag = {fdesc}; key = {kdesc}; |H0| = 1)",
      f"SPLIT_LEVEL {spl}",
      f"NPART {npart}",
      f"PROBE_LTS {probe}",
      f"PROBE_RAW {raw[c]}",
      f"SAMPLE_EST_NODES {tot:.3e}   ({nparts} seeded parts of 1/{ns} at split {spl} on these exact inputs, lwe10 on box hostM: mean {mean:.4e} nodes per part, +-{err}% (1 s.e.), max/mean {sm[6]}; levels > {spl})",
      f"EST_CPU_CORE_HOURS ~{core_h:.0f} with frozen3/lwe10 on box hostM (<CPU>, 200 concurrent processes on 224 vCPUs, user CPU): {user:.1f} s per 1/{ns} part (max {umax} s) incl. {pt:.1f} s prefix; part work {work_s/3600:.0f} core-h + prefix {npart*pt/3600:.0f} core-h at NPART {npart}. Per-node speed on an idle <CPU>/4/5 core is higher.",
      f"PREFIX {pt:.1f} s per part on hostM (levels <= {spl} recomputed by every part: {prefix_nodes:.3e} nodes at levels <= {spl}; {npart} parts -> ~{npart*pt/3600:.0f} core-h)",
      f"KEYH0 |H0| = 1 (struct/src/keyh0.py: no element of Aut(Y) fixes all key words and acts trivially on their syndromes)",
      f"BUILD: TMPDIR=<scratch> <HOME>/c72/venv/bin/python -I frozen/prep_code.py {ci} FLAGFILE words:{key} y{c}   (FLAGFILE = {fl}, sha256 {fsha}; flag.txt holds the same FLAG line)",
      f"RUN: TMPDIR=<scratch> frozen3/run_parts.sh y{c} {spl} {npart} 0 {npart-1} <NPROC>     (or any FIRST..LAST sub-range per box)",
      f"CHECK: frozen3/check_box.sh y{c} ; SUMMARY: python3 frozen3/sumrun2.py y{c}/parts {npart}",
      f"VALIDATION: key pattern covered by the STRUCT QR48 orbit-cover controls (orbit keys and H-fixed keys, r = 1,2,3,6; 28 configurations, closure 5760, 0 outside); lwe8/lwe10 identity and probe reproduction by check_box.sh (logs/pack/checkbox_y{c}.log on the main VM)",
    ]
    open(f'{B}/runs/y{c}/PLAN.txt', 'w').write('\n'.join(lines) + '\n')
    print(f"y{c}: SPL {spl} NPART {npart} probe {probe} est {tot:.3e} core-h {core_h:.0f}")

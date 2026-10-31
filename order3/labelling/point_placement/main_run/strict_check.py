"""Strict end-of-run check of csp5p production on one box (audit finding F1).
For every chunk file chunks/c_* of WORKDIR: out/<chunk>.out must exist and have exactly one line per input line,
in input order, with the same id; every output line must match the strict UNSAT format (anything else is counted
as SAT, ERROR or unparsed); per line pw8 = A8/3 (A8 from the input line), pw10 = 6072 - 8 pw8 (= A10/3, Gleason:
A10 = 18216 - 8 A8) and pw12 <= A12/3 = 52164 + 28 pw8.  The ids seen must be exactly the union of the expected
half-open ranges given on the command line, each once.  Non-empty out/*.err files and out/*.out files without a
chunk are reported.
usage: python3 -I strict_check.py WORKDIR N a:b [a:b ...]"""
import sys, os, re
W = sys.argv[1]; N = int(sys.argv[2]); ranges = [tuple(map(int, r.split(':'))) for r in sys.argv[3:]]
unsat_re = re.compile(r'^id=(\d+) res=UNSAT nsol=0 hash=0000000000000000 nodes=(\d+) wall=(\d+\.\d+) cpu=(\d+\.\d+) '
                      r'prep=(\d+\.\d+) pw8=(\d+) pw10=(\d+) pw12=(\d+) f8=(\d+) f12=(\d+)$')
loose_re = re.compile(r'^id=(\d+) res=(\S+)')
seen = bytearray(N)
chunks = sorted(f for f in os.listdir(os.path.join(W, 'chunks')) if f.startswith('c_'))
st = dict(chunks=len(chunks), in_lines=0, out_lines=0, unsat=0, sat=0, error=0, unparsed=0, missing_out=0,
          count_mismatch=0, id_mismatch=0, bad_input=0, pw8_mismatch=0, pw10_mismatch=0, pw12_violation=0,
          pw12_eq_A12over3=0, dup_ids=0, out_of_range=0, nonempty_err=0, orphan_out=0)
notes = []
def note(s):
    if len(notes) < 30: notes.append(s)
for c in chunks:
    ins = open(os.path.join(W, 'chunks', c)).read().splitlines()
    st['in_lines'] += len(ins)
    op = os.path.join(W, 'out', c + '.out')
    if not os.path.exists(op):
        st['missing_out'] += 1; note('missing output ' + c); continue
    outs = open(op, errors='replace').read().splitlines()
    st['out_lines'] += len(outs)
    if len(outs) != len(ins):
        st['count_mismatch'] += 1; note('%s: %d input lines, %d output lines' % (c, len(ins), len(outs)))
    for k in range(min(len(ins), len(outs))):
        fi = ins[k].split()
        if len(fi) != 6 or not fi[5].startswith('id='):
            st['bad_input'] += 1; note('%s line %d: bad input' % (c, k)); continue
        iid = int(fi[5][3:]); a8 = int(fi[2])
        m = unsat_re.match(outs[k])
        if m:
            oid = int(m.group(1)); st['unsat'] += 1
            pw8, pw10, pw12 = int(m.group(6)), int(m.group(7)), int(m.group(8))
            if 3 * pw8 != a8: st['pw8_mismatch'] += 1; note('%s id %d: pw8 %d vs A8 %d' % (c, oid, pw8, a8))
            if pw10 != 6072 - 8 * pw8: st['pw10_mismatch'] += 1; note('%s id %d: pw10 %d' % (c, oid, pw10))
            if pw12 > 52164 + 28 * pw8: st['pw12_violation'] += 1; note('%s id %d: pw12 %d' % (c, oid, pw12))
            elif pw12 == 52164 + 28 * pw8: st['pw12_eq_A12over3'] += 1
        else:
            ml = loose_re.match(outs[k])
            if not ml:
                st['unparsed'] += 1; note('%s line %d unparsed: %r' % (c, k, outs[k][:120])); continue
            oid = int(ml.group(1))
            if ml.group(2) == 'SAT': st['sat'] += 1; note('SAT %s: %s' % (c, outs[k][:200]))
            elif ml.group(2) == 'ERROR': st['error'] += 1; note('ERROR %s: %s' % (c, outs[k][:200]))
            else: st['unparsed'] += 1; note('%s line %d unparsed (format): %r' % (c, k, outs[k][:120]))
        if oid != iid:
            st['id_mismatch'] += 1; note('%s line %d: output id %d, input id %d' % (c, k, oid, iid))
        if 0 <= oid < N:
            if seen[oid]: st['dup_ids'] += 1
            seen[oid] = 1
        else: st['out_of_range'] += 1
    # output lines beyond the input count are unparsed extras (already counted in count_mismatch)
    ep = os.path.join(W, 'out', c + '.err')
    if os.path.exists(ep) and os.path.getsize(ep) > 0:
        st['nonempty_err'] += 1; note('non-empty %s.err: %r' % (c, open(ep, errors='replace').readline()[:120]))
cs = set(chunks)
for f in os.listdir(os.path.join(W, 'out')):
    if f.endswith('.out') and f[:-4] not in cs: st['orphan_out'] += 1; note('orphan output ' + f)
expected = sum(b - a for a, b in ranges)
in_ranges = sum(sum(seen[a:b]) for a, b in ranges)
total_seen = sum(seen)
st['expected_ids'] = expected; st['seen_in_ranges'] = in_ranges; st['seen_outside_ranges'] = total_seen - in_ranges
ok = (st['missing_out'] == 0 and st['count_mismatch'] == 0 and st['id_mismatch'] == 0 and st['bad_input'] == 0 and
      st['unparsed'] == 0 and st['sat'] == 0 and st['error'] == 0 and st['dup_ids'] == 0 and st['out_of_range'] == 0 and
      st['pw8_mismatch'] == 0 and st['pw10_mismatch'] == 0 and st['pw12_violation'] == 0 and st['orphan_out'] == 0 and
      in_ranges == expected and total_seen == expected and st['unsat'] == expected and st['in_lines'] == expected and
      st['out_lines'] == expected)
print('workdir', W, 'ranges', ' '.join('%d:%d' % r for r in ranges))
for k, v in st.items(): print('%s=%d' % (k, v))
print('STRICT_OK' if ok else 'STRICT_FAIL')
for s in notes: print('note:', s)

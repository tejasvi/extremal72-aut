"""Check MANIFEST_lwe.txt against the files of this directory.

Run from this directory: python3 check_manifest.py
Instance files may be stored gzipped (lwinst/lwf_*.txt.gz); their hash is taken over the decompressed
bytes, which is what the manifest records. The generator is at ../model/lwprep.py; in the supplement its two
absolute paths were replaced by paths relative to the script (REDACTIONS.tsv at the top level records the sha256 of the
original file, which is the one in the manifest), so its line is reported as edited, not checked. The run binary (lwe)
is not part of the supplement; its line is reported as not shipped. Exit status 1 on any mismatch or missing file.
"""
import gzip, hashlib, os, sys

MAP = {'c72/c2par/lwprep.py': os.path.join('..', 'model', 'lwprep.py')}
NOT_SHIPPED = {'lwe'}
EDITED = {'c72/c2par/lwprep.py'}

def sha(path):
    h = hashlib.sha256()
    opener = gzip.open if path.endswith('.gz') else open
    with opener(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

ok = bad = missing = 0
for line in open('MANIFEST_lwe.txt'):
    if line.startswith('#') or not line.strip():
        continue
    digest, name = line.split()
    if name in NOT_SHIPPED:
        print('NOT SHIPPED', name)
        continue
    if name in EDITED:
        print('EDITED (paths only, see REDACTIONS.tsv)', name)
        continue
    path = MAP.get(name, name)
    if not os.path.exists(path) and os.path.exists(path + '.gz'):
        path += '.gz'
    if not os.path.exists(path):
        print('MISSING', name); missing += 1
    elif sha(path) != digest:
        print('MISMATCH', name); bad += 1
    else:
        ok += 1
print('ok', ok, 'mismatch', bad, 'missing', missing)
sys.exit(1 if bad or missing else 0)

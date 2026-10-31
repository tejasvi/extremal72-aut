"""Task list for the box differential tests (audit code).  One line per task, run by runtask.sh.
  part  PKG SPL NPART PARTS(comma) TAG              random parts of the real instance (seeded), lwe8 vs rc7 vs lwe11b
  pin   PKG L NPREF SEED VARIANTS SPL2 NPART2 TAG    pinned sub-instances at prefixes surviving lwe8's tests
  pinns PKG L NPREF SEED VARIANTS SPL2 NPART2 TAG    the same without symmetry (planted solutions survive)
  core  PKG L NPREF SEED Q TAG                       lwe8 without symmetry vs the naive engine
Usage: mktasks.py KITDIR NPARTS_PER_PKG SEED > tasks.txt"""
import sys, os, random
kit, nparts, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rnd = random.Random(seed)
for pkg in sorted(os.listdir(os.path.join(kit, 'pkgs'))):
    plan = open(os.path.join(kit, 'pkgs', pkg, 'PLAN.txt')).read()
    spl = int([l for l in plan.split('\n') if l.startswith('SPLIT_LEVEL')][0].split()[1])
    parts = [rnd.randrange(200000) for _ in range(nparts)]
    for k in range(0, nparts, 4):
        print(f"part {pkg} {spl} 200000 {','.join(map(str, parts[k:k + 4]))} {pkg}_part{k // 4}")
    for L in (spl + 1, spl + 3, spl + 5):
        print(f"pin {pkg} {L} 12 {rnd.getrandbits(30)} exact,keep0.9,plant,plantkeep0.95 {L + 1} 3 {pkg}_pinL{L}")
        print(f"pinns {pkg} {L} 6 {rnd.getrandbits(30)} exact,keep0.97,plant {L + 1} 3 {pkg}_pinnsL{L}")
    print(f"core {pkg} {spl + 3} 20 {rnd.getrandbits(30)} 0.9 {pkg}_coreL{spl + 3}")

"""Question 1 sweep over partial regular semisimple Hessenberg varieties, n <= N.

All have H^odd = 0 (smooth projective, isolated fixed points). Group the data (kbar, h)
by the cover-count invariant of the face poset; report invariant classes whose members have
different Betti numbers. Such a class is a *candidate* counterexample, to be confirmed by an
actual poset isomorphism test (equal invariants are necessary, not sufficient)."""
import sys, time
from collections import defaultdict
import partial_hessenberg as ph

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
for n in range(3, N + 1):
    t = time.time(); classes = defaultdict(list); ncases = 0
    for kbar in ph.compositions(n):
        if len(kbar) < 2: continue
        for h in ph.hessenberg_functions(len(kbar)):
            classes[ph.invariant(n, kbar, h)].append((kbar, h, ph.poincare(n, kbar, h)))
            ncases += 1
    cand = [v for v in classes.values() if len({P for *_, P in v}) > 1]
    print(f"n={n}: {ncases} cases, {len(classes)} invariant classes, "
          f"{len(cand)} classes with differing Betti numbers  ({time.time()-t:.0f}s)")
    for v in cand:
        print("   CANDIDATE:")
        for kbar, h, P in v: print(f"      kbar={kbar} h={h} Betti={P}")
    sys.stdout.flush()

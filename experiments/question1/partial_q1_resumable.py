"""Question 1 sweep over partial Hessenberg varieties for one n: resumable and parallel.

Every finished case is appended to a JSONL checkpoint at once, so an interrupted run (the
cloud container can be recycled) resumes where it stopped. Work is spread over all cores.

Mirror symmetry: reversing the parts maps (kbar, h) to (kbar reversed, h*), where h* is the
Hessenberg function of the reversed graph Gamma_h. The inflated graphs are isomorphic, so the
face posets are isomorphic and the cover invariant is computed for one member of each pair.
This claim is checked on every case with n <= 5 before the sweep starts. Betti numbers are
computed for both members (they are cheap and serve as a further check).

Usage: python3 partial_q1_resumable.py N [workers]
"""
import json, os, sys, time
from multiprocessing import Pool
import partial_hessenberg as ph


def mirror(kbar, h):
    s = len(kbar)
    E = [(s + 1 - b, s + 1 - a) for a in range(1, s + 1) for b in range(a + 1, h[a - 1] + 1)]
    hs = tuple(max([c] + [d for c2, d in E if c2 == c]) for c in range(1, s + 1))
    assert all(hs[i] >= i + 1 for i in range(s)) and all(hs[i] <= hs[i + 1] for i in range(s - 1)), (kbar, h, hs)
    return tuple(reversed(kbar)), hs


def cases(n):
    return [(kbar, h) for kbar in ph.compositions(n) if len(kbar) >= 2
            for h in ph.hessenberg_functions(len(kbar))]


def key(kbar, h):
    return json.dumps([list(kbar), list(h)])


def work(case):
    (kbar, h), n = case, sum(case[0])
    inv = json.dumps(ph.invariant(n, kbar, h))
    mk, mh = mirror(kbar, h)
    return [(key(kbar, h), inv, list(ph.poincare(n, kbar, h))),
            (key(mk, mh), inv, list(ph.poincare(n, mk, mh)))]


def self_check():
    for n in (3, 4, 5):
        for kbar, h in cases(n):
            mk, mh = mirror(kbar, h)
            assert ph.invariant(n, kbar, h) == ph.invariant(n, mk, mh), ("mirror invariant", kbar, h)
            assert ph.poincare(n, kbar, h) == ph.poincare(n, mk, mh), ("mirror Betti", kbar, h)
    print("self-check passed: mirror pairs have equal invariants and Betti numbers for all n <= 5", flush=True)


def main():
    n = int(sys.argv[1]); workers = int(sys.argv[2]) if len(sys.argv) > 2 else os.cpu_count()
    ckpt = f"partial_q1_n{n}.jsonl"
    done = {}
    if os.path.exists(ckpt):
        for line in open(ckpt):
            if line.strip():
                k, inv, P = json.loads(line); done[k] = (inv, P)
    self_check()
    all_cases = cases(n)
    reps, seen = [], set(done)
    for kbar, h in all_cases:
        k, mk = key(kbar, h), key(*mirror(kbar, h))
        if k in seen:
            continue
        seen.update([k, mk]); reps.append((kbar, h))
    print(f"n={n}: {len(all_cases)} cases, {len(done)} already done, {len(reps)} mirror-representatives to compute, {workers} workers", flush=True)
    t0 = time.time()
    with open(ckpt, "a") as out, Pool(workers) as pool:
        for i, results in enumerate(pool.imap_unordered(work, reps, chunksize=1), 1):
            for k, inv, P in results:
                if k not in done:
                    done[k] = (inv, P); out.write(json.dumps([k, inv, P]) + "\n")
            out.flush()
            if i % 25 == 0 or i == len(reps):
                el = time.time() - t0
                print(f"  {i}/{len(reps)} representatives  ({el:.0f}s elapsed, ~{el / i * (len(reps) - i):.0f}s left)", flush=True)
    classes = {}
    for k, (inv, P) in done.items():
        classes.setdefault(inv, []).append((k, tuple(P)))
    cand = [v for v in classes.values() if len({P for _, P in v}) > 1]
    print(f"n={n}: {len(done)} cases, {len(classes)} invariant classes, "
          f"{len(cand)} classes with differing Betti numbers  ({time.time() - t0:.0f}s this run)", flush=True)
    for v in cand:
        print("   CANDIDATE:"); [print(f"      {k} Betti={P}") for k, P in v]


if __name__ == "__main__":
    main()

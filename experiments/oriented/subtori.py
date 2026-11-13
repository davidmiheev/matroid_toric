"""Track E, second round: subtori of rank 2.

Part 1 (item "acyclic = vertices").  For a Hamiltonian action the oriented matroid at a fixed
point p is acyclic iff mu(p) is a vertex of the moment polytope, totally cyclic iff mu(p) is an
interior point, and otherwise mu(p) lies in the relative interior of a proper face.  (Proof in
RESULTS.md.)  Checked here on Hessenberg varieties and Grassmannians with generic and
non-generic 2-dimensional subtori, where the weights at p are only some of the differences
mu(p') - mu(p), so the statement is not a tautology.

Part 2 (item "what do rank-2 subtori see").  For a generic T^2 the oriented matroid at p is a
cyclic word: the weights and their negatives in angular order.  Equivalently it is the function
theta -> ind_p(theta) on the circle of directions, up to rotation and reflection.  Question: does
the multiset of these words over the fixed points determine the Betti numbers, as it does for a
circle (where the word is {ind, n - ind}) and does not for the full torus?

Run:  ../../engine/.venv/bin/python subtori.py
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations
import random
import sys


def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]

def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def kind(vectors):
    """'acyclic', 'totally cyclic' or 'mixed' for nonzero vectors in the plane spanning it."""
    # acyclic: all in an open half-plane <=> some vector v has every other vector strictly to
    # its left or parallel in the same direction
    def half_plane_from(v):
        for u in vectors:
            c = cross(v, u)
            if c < 0 or (c == 0 and dot(v, u) < 0):
                return False
        return True
    if any(half_plane_from(v) for v in vectors):
        return "acyclic"
    # totally cyclic: no closed half-plane contains them all, unless all on a line through 0
    def closed_half_plane(v):                          # all on the closed left side of v
        return all(cross(v, u) >= 0 for u in vectors)
    if any(closed_half_plane(v) or closed_half_plane((-v[0], -v[1])) for v in vectors):
        return "mixed"
    return "totally cyclic"


def position(p, pts):
    """Position of p in the convex hull of pts: 'vertex', 'interior' or 'boundary'."""
    diffs = [(q[0] - p[0], q[1] - p[1]) for q in pts if q != p]
    k = kind(diffs)
    return {"acyclic": "vertex", "totally cyclic": "interior", "mixed": "boundary"}[k]


def word(vectors):
    """Canonical cyclic word of a planar configuration: directions of +-v in angular order,
    each direction with (number of weights pointing along it, number pointing against it);
    canonical under rotation and reflection."""
    from fractions import Fraction
    from math import gcd
    dirs = defaultdict(lambda: [0, 0])
    for v in vectors:
        g = gcd(abs(v[0]), abs(v[1]))
        d = (v[0] // g, v[1] // g)
        dirs[d][0] += 1
        dirs[(-d[0], -d[1])][1] += 1
    def half(d):
        return 0 if (d[1] > 0 or (d[1] == 0 and d[0] > 0)) else 1
    import functools
    def cmp(a, b):
        if half(a) != half(b):
            return half(a) - half(b)
        c = cross(a, b)
        return -1 if c > 0 else 1 if c < 0 else 0
    order = sorted(dirs, key=functools.cmp_to_key(cmp))
    seq = [tuple(dirs[d]) for d in order]
    cands = []
    for s in (seq, seq[::-1]):
        for r in range(len(s)):
            cands.append(tuple(s[r:] + s[:r]))
    return min(cands)


def index_set(vectors):
    """Numbers of negative weights over all generic directions."""
    out = set()
    for v in vectors:
        for eps in (1, -1):
            xi = (-v[1] * 1000 + eps * v[0], v[0] * 1000 + eps * v[1])      # just off the wall of v
            for s in (1, -1):
                x = (s * xi[0], s * xi[1])
                if all(dot(x, u) != 0 for u in vectors):
                    out.add(sum(1 for u in vectors if dot(x, u) < 0))
    return tuple(sorted(out))


def hessenberg_functions(n):
    def rec(i, lo):
        if i == n:
            yield ()
            return
        for v in range(max(lo, i + 1), n + 1):
            for rest in rec(i + 1, v):
                yield (v,) + rest
    return rec(0, 1)


def hess(n, h, a):
    """Fixed points of Hess(h) with the T^2 given by characters a[0..n-1] in Z^2:
    moment images and weights."""
    lam = list(range(n, 0, -1))
    pts, wts = [], []
    for w in permutations(range(n)):
        pts.append((sum(lam[k] * a[w[k]][0] for k in range(n)), sum(lam[k] * a[w[k]][1] for k in range(n))))
        wts.append([(a[w[i]][0] - a[w[j]][0], a[w[i]][1] - a[w[j]][1])
                    for j in range(n) for i in range(j + 1, h[j])])
    return pts, wts


def betti(n, h):
    c = Counter(sum(1 for j in range(n) for i in range(j + 1, h[j]) if w[i] < w[j]) for w in permutations(range(n)))
    return tuple(c[i] for i in range(max(c) + 1))


def grassmannian(k, n, a):
    pts, wts = [], []
    for J in combinations(range(n), k):
        pts.append((sum(a[x][0] for x in J), sum(a[x][1] for x in J)))
        wts.append([(a[y][0] - a[x][0], a[y][1] - a[x][1]) for x in J for y in range(n) if y not in J])
    return pts, wts


def main():
    ok = True
    random.seed(11)
    print("== Part 1. acyclic <=> vertex, totally cyclic <=> interior, mixed <=> boundary")
    cases = bad = 0
    stats = Counter()
    def test(pts, wts):
        nonlocal cases, bad
        if len(set(pts)) < len(pts) or any(w == (0, 0) for ws in wts for w in ws):
            return                                     # fixed points of the subtorus not isolated
        cases += 1
        for p, ws in zip(pts, wts):
            k, pos = kind(ws), position(p, pts)
            stats[(k, pos)] += 1
            if {"acyclic": "vertex", "totally cyclic": "interior", "mixed": "boundary"}[k] != pos:
                bad += 1
    for n in (3, 4, 5):
        for h in hessenberg_functions(n):
            if any(h[j] == j + 1 for j in range(n - 1)):
                continue                               # disconnected
            for trial in range(6 if n < 5 else 2):
                if trial % 2 == 0:
                    a = [(random.randint(-20, 20), random.randint(-20, 20)) for _ in range(n)]
                else:                                  # non-generic: characters on a small grid
                    a = [(random.randint(0, 2), random.randint(0, 2)) for _ in range(n)]
                test(*hess(n, h, a))
    for k, n in ((2, 4), (2, 5), (3, 6)):
        for trial in range(10):
            a = [(random.randint(-9, 9), random.randint(-9, 9)) for _ in range(n)]
            test(*grassmannian(k, n, a))
    good = bad == 0
    ok &= good
    print(f"[{'PASS' if good else 'FAIL'}] {cases} actions (Hessenberg n <= 5, Grassmannians), "
          f"fixed points by (oriented matroid, position): {dict(stats)}")

    print("\n== Part 2. cyclic words of a generic T^2")
    for n in (4, 5, 6):
        for trial in range(3 if n < 6 else 2):
            while True:
                a = [(random.randint(-30, 30), random.randint(-30, 30)) for _ in range(n)]
                diffs = [(a[i][0] - a[j][0], a[i][1] - a[j][1]) for i in range(n) for j in range(i)]
                if all(d != (0, 0) for d in diffs) and all(cross(u, v) != 0 for u, v in combinations(diffs, 2)):
                    break                              # weights pairwise non-parallel: generic
            by_words, by_idx, by_acyc = defaultdict(set), defaultdict(set), defaultdict(set)
            count = 0
            for h in hessenberg_functions(n):
                if any(h[j] == j + 1 for j in range(n - 1)):
                    continue
                count += 1
                pts, wts = hess(n, h, a)
                P = betti(n, h)
                by_words[tuple(sorted(Counter(word(ws) for ws in wts).items()))].add((h, P))
                by_idx[(len(wts[0]), tuple(sorted(Counter(index_set(ws) for ws in wts).items())))].add((h, P))
                by_acyc[(len(wts[0]), sum(1 for ws in wts if kind(ws) == "acyclic"))].add((h, P))
            def amb(groups):
                return sum(1 for v in groups.values() if len({P for _, P in v}) > 1)
            nP = len({P for v in by_words.values() for _, P in v})
            print(f"n = {n}, characters {a}: {count} connected Hessenberg functions, {nP} Poincare polynomials")
            print(f"    multiset of words:        {len(by_words)} classes, {amb(by_words)} with more than one Poincare polynomial")
            print(f"    multiset of index sets:   {len(by_idx)} classes, {amb(by_idx)} ambiguous")
            print(f"    dim and number of vertices: {len(by_acyc)} classes, {amb(by_acyc)} ambiguous")
            if n == 5:
                w1 = Counter(word(ws) for ws in hess(5, (2, 3, 5, 5, 5), a)[1])
                w2 = Counter(word(ws) for ws in hess(5, (2, 4, 4, 5, 5), a)[1])
                i1 = Counter(index_set(ws) for ws in hess(5, (2, 3, 5, 5, 5), a)[1])
                i2 = Counter(index_set(ws) for ws in hess(5, (2, 4, 4, 5, 5), a)[1])
                print(f"    Track A pair: words differ: {w1 != w2} ({len(w1)} and {len(w2)} distinct words); "
                      f"index sets: X1 {dict(sorted(i1.items()))}, X2 {dict(sorted(i2.items()))}")
    print("\nALL PASS" if ok else "\nFAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

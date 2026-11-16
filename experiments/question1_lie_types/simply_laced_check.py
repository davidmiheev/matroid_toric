"""Check of the lemma behind the simply-laced rigidity theorem (PROOF.md, Lemma 3).

For roots of a simply-laced system, normalised to (a, a) = 2, let C = (a_1, ..., a_k) be an
induced cycle of the non-orthogonality graph (consecutive roots have inner product +-1, all
other pairs are orthogonal).  Claim: the span of C has dimension k - 1 if the product of the
inner products around the cycle is (-1)^k, and k otherwise.  The script verifies this for the
induced cycles of the positive roots of A_2..A_6, D_4..D_6, E_6, E_7 (all of them up to the
caps below), and also that orthogonal roots span a plane with no further root.

Run:  python3 simply_laced_check.py
"""
from fractions import Fraction as Fr
from itertools import combinations
import sys


def simple_roots(t, n):
    if t == "A":
        return [tuple(Fr(int(k == i) - int(k == i + 1)) for k in range(n + 1)) for i in range(n)]
    if t == "D":
        S = [tuple(Fr(int(k == i) - int(k == i + 1)) for k in range(n)) for i in range(n - 1)]
        return S + [tuple(Fr(int(k == n - 2) + int(k == n - 1)) for k in range(n))]
    if t == "E":                     # E_8 in R^8 (Bourbaki), E_7 and E_6 as the first n simple roots
        h = Fr(1, 2)
        e = lambda i: tuple(Fr(int(k == i)) for k in range(8))
        sub = lambda a, b: tuple(x - y for x, y in zip(a, b))
        add = lambda a, b: tuple(x + y for x, y in zip(a, b))
        S = [(h, -h, -h, -h, -h, -h, -h, h), add(e(0), e(1))] + [sub(e(i + 1), e(i)) for i in range(6)]
        return S[:n]
    raise ValueError(t)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def positive_roots(S):
    refl = lambda a, v: tuple(x - 2 * dot(a, v) / dot(a, a) * y for x, y in zip(v, a))
    roots, todo = set(S), list(S)
    while todo:
        v = todo.pop()
        for a in S:
            w = refl(a, v)
            if w not in roots:
                roots.add(w)
                todo.append(w)
    # positive = nonnegative coordinates in the simple roots: decide by a generic functional
    # that is positive on the simple roots
    import random
    random.seed(1)
    while True:
        f = [Fr(random.randint(1, 10 ** 6)) for _ in S[0]]
        if all(dot(f, a) != 0 for a in roots):
            # make f positive on the simple roots: solve by reflecting into the chamber
            changed = True
            while changed:
                changed = False
                for a in S:
                    if dot(f, a) < 0:
                        f = list(refl(a, tuple(f)))
                        changed = True
            break
    return sorted(v for v in roots if dot(f, v) > 0)


def rank(vs):
    rows = [list(v) for v in vs]
    rk = 0
    for c in range(len(rows[0])):
        p = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        rows[rk], rows[p] = rows[p], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c] / rows[rk][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def induced_cycles(adj, n, max_len, cap):
    """Induced cycles of length 3..max_len, each once (smallest vertex first), at most cap."""
    out = []
    def extend(path, inpath):
        if len(out) >= cap:
            return
        last, first = path[-1], path[0]
        for v in adj[last]:
            if v <= first or v in inpath:
                continue
            # v must be adjacent to no path vertex other than last, and possibly first
            nb = [u for u in path[:-1] if v in adj[u]]
            if nb == [first] and len(path) >= 2:
                if path[1] < v:                       # orientation: count each cycle once
                    out.append(path + [v])
                continue
            if nb:
                continue
            if len(path) + 1 < max_len:
                extend(path + [v], inpath | {v})
    for s in range(n):
        extend([s], {s})
    return out


def main():
    ok = True
    for t, n, max_len, cap in [("A", 2, 8, 10 ** 6), ("A", 3, 8, 10 ** 6), ("A", 4, 8, 10 ** 6),
                               ("A", 5, 8, 10 ** 6), ("A", 6, 8, 10 ** 6), ("D", 4, 8, 10 ** 6),
                               ("D", 5, 8, 10 ** 6), ("D", 6, 7, 10 ** 6), ("E", 6, 7, 300000),
                               ("E", 7, 6, 300000)]:
        P = positive_roots(simple_roots(t, n))
        N = len(P)
        assert all(dot(a, a) == 2 for a in P)
        G = [[dot(a, b) for b in P] for a in P]
        allroots = set(P) | {tuple(-x for x in v) for v in P}
        bad_orth = 0
        for i, j in combinations(range(N), 2):
            if G[i][j] == 0:
                s = tuple(x + y for x, y in zip(P[i], P[j]))
                d = tuple(x - y for x, y in zip(P[i], P[j]))
                bad_orth += s in allroots or d in allroots
            else:
                assert G[i][j] in (1, -1)
        adj = [set(j for j in range(N) if j != i and G[i][j] != 0) for i in range(N)]
        cycles = induced_cycles(adj, N, max_len, cap)
        bad = 0
        by_len = {}
        for C in cycles:
            k = len(C)
            prod = 1
            for a in range(k):
                prod *= G[C[a]][C[(a + 1) % k]]
            want = k - 1 if prod == (-1) ** k else k
            got = rank([P[i] for i in C])
            bad += got != want
            by_len[k] = by_len.get(k, 0) + 1
        good = bad == 0 and bad_orth == 0
        ok &= good
        print(f"[{'PASS' if good else 'FAIL'}] {t}{n}: {N} positive roots, induced cycles by length "
              f"{dict(sorted(by_len.items()))}{' (capped)' if len(cycles) >= cap else ''}", flush=True)
    print("ALL PASS" if ok else "FAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

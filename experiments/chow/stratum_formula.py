"""The stratum polynomials e_sigma in closed form (Track F, item "compute e from the poset").

Setting: a torus action with isolated fixed points whose Poincare polynomial is
P_X(q) = sum_p q^ind(p), ind(p) = number of weights at p negative on a generic xi
(Bialynicki-Birula / Morse).  For a face sigma and a fixed point p of sigma let N_p(sigma)
be the set of weights of sigma at p that are negative on xi.  Claim:

    P_X(q) = sum_sigma (q - 1)^rk(sigma) e_sigma(q),
    e_sigma(q) = sum over fixed points p of sigma such that N_p(sigma) spans the weights of sigma
                 of T_{M(N_p(sigma))}(1, q),

where T is the Tutte polynomial of the linear matroid of N_p(sigma).

Checks.
 1. For connected Hessenberg graphs the formula agrees with e defined by the recursion
    P_sigma = sum_{tau <= sigma} (q-1)^rk e_tau (track_f.py), for the top face.
 2. The identity for P_X, with e_sigma computed from the formula and the engine's Tutte
    polynomial, on Fl(C^3), Fl(C^4), Gr(2,4), the Track A pair, and CP^3 with a T^2.
 3. e_top does not depend on xi (it could not, by 1, but the summands do).

Run:  ../../engine/.venv/bin/python stratum_formula.py
"""
from collections import defaultdict
from itertools import combinations, permutations
import sys

from mtengine.domain import matroids as mt
import track_f as tf


def tutte_at_x1(vectors):
    """T_M(1, y) as a coefficient list in y, from the engine's Tutte polynomial."""
    V = mt.parse_vectors(vectors)
    T = mt.invariants(V, tutte_max=20)["tutte_polynomial"]
    out = [0] * (max(int(k.split(",")[1]) for k in T) + 1)
    for k, c in T.items():
        out[int(k.split(",")[1])] += c
    return out


def e_formula(points, xi, flat_of=None):
    """points: list of weight lists.  Returns {(index of p, flat as frozenset of weight indices): ...}
    aggregated as sum over (p, F) of (q-1)^rk F * [N spans F] T_N(1, q)  -> the polynomial P_X,
    and the list of top contributions."""
    total = [0]
    top = [0]
    for ws in points:
        V = mt.parse_vectors(ws)
        levels = mt.flats_by_rank(V)
        neg = {j for j, w in enumerate(ws) if sum(a * b for a, b in zip(w, xi)) < 0}
        for k, level in enumerate(levels):
            for F in level:
                N = sorted(neg & F)
                if mt.rank_of(V, N) < k:
                    continue
                t = tutte_at_x1([ws[j] for j in N]) if N else [1]
                total = tf.padd(total, tf.pmul(tf.ppow([-1, 1], k), t))
                if k == len(levels) - 1:
                    top = tf.padd(top, t)
    return tf.trim(total), tf.trim(top)


def e_vec(n, i, j):
    v = [0] * n
    v[i] += 1
    v[j] -= 1
    return v


def hess_points(n, h):
    return [[e_vec(n, w[i], w[j]) for j in range(n) for i in range(j + 1, h[j])] for w in permutations(range(n))]


def main():
    ok = True
    def report(name, good, detail=""):
        nonlocal ok
        ok &= bool(good)
        print(f"[{'PASS' if good else 'FAIL'}] {name}{(' -- ' + detail) if detail else ''}", flush=True)

    # 1. formula vs recursion, all connected Hessenberg functions with n <= 5
    bad = cases = 0
    for n in range(2, 6):
        xi = [3 ** k for k in range(n)]
        for h in tf.hessenberg_functions(n):
            E = tf.graph(h)
            if len(tf.components(range(n), E)) > 1:
                continue
            cases += 1
            _, top = e_formula(hess_points(n, h), xi)
            if top != tf.trim(tf.e_poly(range(n), E)):
                bad += 1
                print("   mismatch", h, top, tf.e_poly(range(n), E))
    report("1. e_top from the Tutte formula = e_top from the recursion", bad == 0,
           f"{cases} connected Hessenberg functions, n <= 5")

    # 2. the identity for P_X
    def betti(points, xi):
        c = defaultdict(int)
        for ws in points:
            c[sum(1 for w in ws if sum(a * b for a, b in zip(w, xi)) < 0)] += 1
        return [c[i] for i in range(max(c) + 1)]
    gr24 = [[e_vec(4, y, x) for x in J for y in range(4) if y not in J] for J in combinations(range(4), 2)]
    a = [(0, 0), (9, 1), (2, 8), (4, 3)]
    cp3 = [[[q[0] - p[0], q[1] - p[1]] for j, q in enumerate(a) if j != i] for i, p in enumerate(a)]
    for name, pts, xi in [("Fl(C^3)", hess_points(3, (3, 3, 3)), [1, 3, 9]),
                          ("Fl(C^4)", hess_points(4, (4, 4, 4, 4)), [1, 3, 9, 27]),
                          ("Gr(2,4)", gr24, [1, 3, 9, 27]),
                          ("X1 = Hess(2,3,5,5,5)", hess_points(5, (2, 3, 5, 5, 5)), [1, 3, 9, 27, 81]),
                          ("X2 = Hess(2,4,4,5,5)", hess_points(5, (2, 4, 4, 5, 5)), [1, 3, 9, 27, 81]),
                          ("CP^3 with T^2", cp3, [5, 7])]:
        total, top = e_formula(pts, xi)
        report(f"2. P = sum (q-1)^rk e   for {name}", total == betti(pts, xi),
               f"P = {betti(pts, xi)}, e_top = {tf.show(top)}")

    # 3. independence of xi
    tops = set()
    for xi in ([1, 3, 9, 27, 81], [81, 1, 27, 3, 9], [5, -7, 11, 2, -30], [2, 3, 5, 7, 11]):
        tops.add(tuple(e_formula(hess_points(5, (2, 3, 5, 5, 5)), xi)[1]))
    report("3. e_top of X1 is the same for four different xi", len(tops) == 1, str(tops))
    print("ALL PASS" if ok else "FAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

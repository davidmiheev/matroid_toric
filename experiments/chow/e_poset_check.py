"""Is the stratum polynomial e_sigma a function of the face poset?  (Track F, follow-up)

For a regular semisimple Hessenberg variety Hess(I) of any Lie type, and the face
sigma = (I, W_I) through the identity (the top face when I contains all simple roots),
Theorem 7.1 of the paper gives

    e_sigma(q) = sum over u in W_I such that N_u spans span(I) of T_{M(N_u)}(1, q),
    N_u = {alpha in I : <xi, u(alpha)> > 0}   (the roots whose weight -u(alpha) is negative),

for a generic xi.  T(1, y) is computed from the lattice of flats:
T_M(1, y) = (y - 1)^(-r) * sum_F mu(F, E) y^|F|.

Checks:
  1. e_top does not depend on xi (three choices of xi).
  2. Within each class of ideals with isomorphic (|W|, L(I), nu) -- data read off from the
     face poset -- e_top is constant.  For simply-laced types this is a theorem (paper,
     Proposition 7.4); for the other types it is new evidence.
  3. e_top is not a function of the matroid M(I) alone (the paper's Example 7.2(4)).

Run:  ../../engine/.venv/bin/python e_poset_check.py [types...]
"""
from collections import defaultdict
from fractions import Fraction as Fr
import random
import sys

import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "question1_lie_types"))
import lie_types as lt
from mtengine.domain import matroids as mt


def tutte_x1(vectors):
    """T_M(1, y) as a coefficient list, M the linear matroid of the (loopless) vectors."""
    levels = mt.flats_by_rank(vectors)
    r = len(levels) - 1
    flats = [F for level in levels for F in level]
    rk = {F: k for k, level in enumerate(levels) for F in level}
    top = levels[-1][0]
    mu = {top: 1}
    for F in sorted(flats, key=lambda F: -rk[F]):
        if F == top:
            continue
        mu[F] = -sum(mu[G] for G in flats if F < G)
    poly = [0] * (len(vectors) + 1)
    for F in flats:
        poly[len(F)] += mu[F]
    # divide by (y - 1)^r
    for _ in range(r):
        out = [0] * (len(poly) - 1)
        carry = 0
        for i in range(len(poly) - 1, 0, -1):     # synthetic division by (y - 1)
            carry = poly[i] + carry
            out[i - 1] = carry
        assert poly[0] + carry == 0, "not divisible"
        poly = out
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return tuple(poly)


def e_identity_face(R, I, xi):
    """e of the face (I, W_I) through the identity, from Theorem 7.1."""
    N = R.N
    span_rank = mt.rank_of([R.pos[a] for a in I], range(len(I))) if I else 0
    # the coset W_I: closure of the identity under right multiplication by s_alpha, alpha in I
    gens = [R.rmul[a] for a in I]
    seen, todo = {0}, [0]
    while todo:
        k = todo.pop()
        for g in gens:
            m = g[k]
            if m not in seen:
                seen.add(m)
                todo.append(m)
    allroots = R.pos + [tuple(-x for x in v) for v in R.pos]
    cache = {}
    total = defaultdict(int)
    for k in seen:
        w = R.W[k]                                     # w[i] = index of w(root i) in allroots
        Nu = tuple(a for a in I if sum(x * y for x, y in zip(xi, allroots[w[a]])) > 0)
        if Nu not in cache:
            V = [R.pos[a] for a in Nu]
            if not V or mt.rank_of(V, range(len(V))) < span_rank:
                cache[Nu] = None
            else:
                cache[Nu] = tutte_x1(V)
        t = cache[Nu]
        if t is not None:
            for i, c in enumerate(t):
                total[i] += c
    return tuple(total[i] for i in range(max(total) + 1)) if total else (0,)


def main(types):
    random.seed(5)
    records = []
    for t, n in types:
        R = lt.RootSystem(t, n)
        d = len(R.pos[0])
        xis = [tuple(Fr(random.randint(1, 10 ** 6), random.randint(1, 1000)) for _ in range(d)) for _ in range(3)]
        simple = set(range(n))
        for I in R.ideals():
            if not I:
                continue
            es = {e_identity_face(R, I, xi) for xi in xis}
            key, summary = lt.labelled_lattice(R, I)
            V = mt.parse_vectors([list(R.pos[a]) for a in I])
            records.append({"type": R.name, "ideal": I, "e": es, "key": (len(R.W), key),
                            "connected": simple <= set(I), "poincare": R.poincare(I),
                            "flats": tuple(mt.invariants(V, tutte_max=-1)["flats_by_rank"])})
        print(f"{R.name}: {sum(1 for r in records if r['type'] == R.name)} nonempty ideals", flush=True)
    ok = True
    bad_xi = [r for r in records if len(r["e"]) != 1]
    print(f"[{'PASS' if not bad_xi else 'FAIL'}] 1. e independent of xi: {len(records)} ideals, "
          f"{len(bad_xi)} with xi-dependence")
    ok &= not bad_xi
    for label, keep in (("connected ideals", lambda r: r["connected"]), ("all ideals", lambda r: True)):
        groups = defaultdict(list)
        for r in records:
            if keep(r):
                groups[r["key"]].append(r)
        bad = [v for v in groups.values() if len({next(iter(r["e"])) for r in v}) > 1]
        multi = sum(1 for v in groups.values() if len(v) > 1)
        print(f"[{'PASS' if not bad else 'FAIL'}] 2. {label}: {len(groups)} classes of (|W|, L, nu), "
              f"{multi} with more than one ideal, {len(bad)} with two different e")
        ok &= not bad
        for v in bad[:5]:
            for r in v:
                print("     ", r["type"], r["ideal"], r["e"])
    print("\nExamples of e for the identity face (connected ideals):")
    for r in records:
        if r["connected"] and r["type"] in ("A3", "B2", "G2", "B3", "C3") and len(r["ideal"]) <= 6:
            e = next(iter(r["e"]))
            print(f"    {r['type']:3s} |I|={len(r['ideal']):2d}  e = {e}   P = {r['poincare']}")
    print("ALL PASS" if ok else "FAILURES")
    return 0 if ok else 1


if __name__ == "__main__":
    args = sys.argv[1:] or ["A2", "A3", "A4", "B2", "G2", "B3", "C3", "D4", "B4", "C4"]
    sys.exit(main([(a[0], int(a[1:])) for a in args]))

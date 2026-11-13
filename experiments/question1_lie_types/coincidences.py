"""Which ideals share a nu-labelled lattice of flats, and why?

For every class of (|W|, L, nu) from lie_types.py with more than one ideal, each pair of
ideals is tested for three explanations, in this order:
  diagram   the ideals are of the same type and differ by an automorphism of the Dynkin diagram;
  dual      the ideals correspond under alpha <-> alpha^vee: one is of type B_n and the
            other of type C_n and they span the same lines, or both are of a type isomorphic
            to its dual (B2, G2, F4);
  weyl      some w in W maps the lines of one ideal onto the lines of the other
            (types B_n and C_n have the same lines and the same W).
A pair with none of these is reported as unexplained.  In the first two cases the two
Hessenberg varieties are isomorphic, resp. have the same GKM graph up to scaling the labels;
in the third the face posets are isomorphic for a structural reason but the equality of the
Betti numbers is not automatic.

Run:  ../../engine/.venv/bin/python coincidences.py [types...]
"""
from collections import Counter, defaultdict
from fractions import Fraction as Fr
from itertools import permutations
from math import gcd
import sys

import lie_types as lt


def line(v):
    """Primitive integer vector on the line of v, first nonzero coordinate positive."""
    den = 1
    for x in v:
        den = den * x.denominator // gcd(den, x.denominator)
    w = [int(x * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    w = [x // g for x in w]
    if next(x for x in w if x) < 0:
        w = [-x for x in w]
    return tuple(w)


def diagram_automorphisms(R):
    n = R.rank
    S = [R.pos[R.co.index(tuple(Fr(int(k == i)) for k in range(n)))] for i in range(n)]
    dot = lambda a, b: sum(x * y for x, y in zip(a, b))
    cartan = [[2 * dot(S[i], S[j]) / dot(S[j], S[j]) for j in range(n)] for i in range(n)]
    index = {c: k for k, c in enumerate(R.co)}
    out = []
    for p in permutations(range(n)):
        if all(cartan[p[i]][p[j]] == cartan[i][j] for i in range(n) for j in range(n)):
            m = []
            for c in R.co:                                   # root sum c_i a_i -> sum c_i a_p(i)
                d = [Fr(0)] * n
                for i in range(n):
                    d[p[i]] = c[i]
                m.append(index[tuple(d)])
            out.append(m)
    return out


def self_duality(R):
    """For a root system isomorphic to its dual by reversing the diagram (B2, G2, F4): the
    map alpha -> alpha^vee followed by that isomorphism, on indices of positive roots."""
    n = R.rank
    S = [R.pos[R.co.index(tuple(Fr(int(k == i)) for k in range(n)))] for i in range(n)]
    dot = lambda a, b: sum(x * y for x, y in zip(a, b))
    index = {c: k for k, c in enumerate(R.co)}
    m = []
    for v, c in zip(R.pos, R.co):
        d = [c[i] * dot(S[i], S[i]) / dot(v, v) for i in range(n)]      # coordinates of the coroot
        d = tuple(reversed(d))
        if d not in index:
            return None
        m.append(index[d])
    return m


def main(types):
    systems = {}
    records = []
    for t, n in types:
        R = lt.RootSystem(t, n)
        systems[R.name] = R
        R.lines = [line(v) for v in R.pos]
        R.diag = diagram_automorphisms(R)
        R.selfdual = self_duality(R)
        simple = set(range(n))
        for I in R.ideals():
            key, summary = lt.labelled_lattice(R, I)
            records.append({"type": R.name, "ideal": I, "poincare": R.poincare(I), "key": (len(R.W), key),
                            "connected": simple <= set(I)})
        print(f"{R.name}: {len(R.diag)} diagram automorphisms, self-dual by reversing the diagram: "
              f"{R.selfdual is not None}", flush=True)
    groups = defaultdict(list)
    for r in records:
        groups[r["key"]].append(r)

    def lines_of(r):
        R = systems[r["type"]]
        return frozenset(R.lines[a] for a in r["ideal"])

    def weyl_images(r):
        R = systems[r["type"]]
        N = R.N
        return {frozenset(R.lines[w[a] % N] for a in r["ideal"]) for w in R.W}

    for label, keep in (("connected ideals (all simple roots)", lambda r: r["connected"]),
                        ("all ideals", lambda r: True)):
        print(f"\n==== {label}")
        tally = Counter()
        unexplained = []
        weyl_only = []
        for key, recs in groups.items():
            recs = [r for r in recs if keep(r)]
            for i in range(len(recs)):
                for j in range(i + 1, len(recs)):
                    a, b = recs[i], recs[j]
                    Ra = systems[a["type"]]
                    if a["type"] == b["type"] and any(
                            tuple(sorted(m[x] for x in a["ideal"])) == b["ideal"] for m in Ra.diag):
                        why = "diagram"
                    elif a["type"] != b["type"] and any(
                            frozenset(Ra.lines[m[x]] for x in a["ideal"]) == lines_of(b) for m in Ra.diag):
                        why = "dual"
                    elif a["type"] == b["type"] and Ra.selfdual and \
                            tuple(sorted(Ra.selfdual[x] for x in a["ideal"])) == b["ideal"]:
                        why = "dual"
                    elif lines_of(b) in weyl_images(a):
                        why = "weyl"
                        weyl_only.append((a, b))
                    else:
                        why = "unexplained"
                        unexplained.append((a, b))
                    tally[why] += 1
                    assert a["poincare"] == b["poincare"]
        print("pairs of ideals with the same (|W|, L, nu):", dict(tally))
        print("all of them have equal Poincare polynomials")
        for name, lst in (("related only by an element of W", weyl_only), ("unexplained", unexplained)):
            print(f"{name}: {len(lst)} pairs")
            for a, b in lst[:12]:
                print(f"    {a['type']} {a['ideal']}  ~  {b['type']} {b['ideal']}   P = {a['poincare']}")

if __name__ == "__main__":
    args = sys.argv[1:]
    default = [("A", 2), ("A", 3), ("A", 4), ("B", 2), ("G", 2), ("B", 3), ("C", 3), ("D", 4), ("B", 4), ("C", 4), ("F", 4)]
    main([(a[0], int(a[1:])) for a in args] if args else default)

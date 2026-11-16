"""Track F: Chow rings, augmented Chow rings and intersection cohomology of the local
weight matroids, and the test whether the face poset glues them to the size of H*(X).

Run with the engine's interpreter:  ../../engine/.venv/bin/python track_f.py

Part 1.  The local matroid of the Track A pair X1 = Hess(2,3,5,5,5), X2 = Hess(2,4,4,5,5):
         A(M), augmented A(M) (Macaulay2, from the presentations), IH(M) = Z-polynomial,
         Kazhdan-Lusztig polynomial, Orlik-Solomon algebra.
Part 2.  Dimension counts.  For a function f of a matroid, and the local matroid M_sigma
         of a face sigma (restriction: the weights tangent to the face; contraction: the
         weights normal to it), compare  sum_sigma (-1)^rk(sigma) f(M_sigma)  with the
         Euler characteristic of X, the number of fixed points.
Part 3.  The stratum polynomials e_sigma defined by
             P_sigma(q) = sum_{tau <= sigma} (q - 1)^rk(tau) e_tau(q),
         the unique way to write the Poincare polynomial as a sum over the face poset
         (e_tau is the E-polynomial of the quotient of the open stratum of tau by the
         complex torus).  For toric varieties e = 1.  Is e a matroid invariant?
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial
import sys

from mtengine import api
from mtengine.domain import matroids as mt

val = lambda r: r["value"]


def graph(h):                         # edges {j, i}, j < i <= h(j), vertices 0..n-1
    return [(j, i) for j in range(len(h)) for i in range(j + 1, h[j])]


def vectors(n, E):
    out = []
    for j, i in E:
        v = [0] * n
        v[i], v[j] = 1, -1
        out.append(v)
    return out


# ---------------------------------------------------------------- polynomials in q
def padd(a, b, s=1):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += s * x
    return out

def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out

def ppow(a, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, a)
    return out

def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def pdiv_exact(a, b):                 # a / b for polynomials with integer coefficients
    a = [Fraction(x) for x in trim(a)]
    b = trim(b)
    out = [Fraction(0)] * max(len(a) - len(b) + 1, 1)
    for k in range(len(a) - len(b), -1, -1):
        c = a[k + len(b) - 1] / b[-1]
        out[k] = c
        for i, y in enumerate(b):
            a[k + i] -= c * y
    assert all(x == 0 for x in a), "not divisible"
    assert all(x.denominator == 1 for x in out)
    return trim([int(x) for x in out])

def show(p):
    return " + ".join(f"{c}" + ("" if i == 0 else "q" if i == 1 else f"q^{i}") for i, c in enumerate(p) if c) or "0"


# ---------------------------------------------------------------- graphs and clusterings
def components(verts, E):
    verts = list(verts)
    comp = {v: v for v in verts}
    def find(v):
        while comp[v] != v:
            v = comp[v]
        return v
    for a, b in E:
        if a in comp and b in comp:
            comp[find(a)] = find(b)
    out = defaultdict(list)
    for v in verts:
        out[find(v)].append(v)
    return sorted(map(tuple, out.values()))

def clusterings(n, E):
    """All partitions of 0..n-1 into blocks inducing connected subgraphs = flats of M(G)."""
    seen = set()
    todo = [tuple((v,) for v in range(n))]
    seen.add(todo[0])
    while todo:
        C = todo.pop()
        blk = {v: i for i, B in enumerate(C) for v in B}
        for a, b in E:
            if blk[a] != blk[b]:
                merged = tuple(sorted(B for i, B in enumerate(C) if i not in (blk[a], blk[b]))
                               + [tuple(sorted(C[blk[a]] + C[blk[b]]))])
                merged = tuple(sorted(merged))
                if merged not in seen:
                    seen.add(merged)
                    todo.append(merged)
    return seen

def poincare_graph(verts, E):
    """sum over orderings w of q^(number of edges {j < i} with w(j) > w(i)); for an induced
    subgraph of an indifference graph this is the Poincare polynomial of its Hessenberg variety."""
    verts = sorted(verts)
    E = [(a, b) for a, b in E if a in verts and b in verts]
    pos = {v: k for k, v in enumerate(verts)}
    c = Counter()
    for w in permutations(range(len(verts))):
        c[sum(1 for a, b in E if w[pos[a]] > w[pos[b]])] += 1
    return [c[i] for i in range(max(c) + 1)]

_e_cache = {}
def e_poly(verts, E):
    """e of a connected induced subgraph (as a labelled graph: the order of the vertices matters)."""
    verts = tuple(sorted(verts))
    Ein = tuple(sorted((a, b) for a, b in E if a in verts and b in verts))
    key = (tuple(verts.index(a) for a in verts), tuple((verts.index(a), verts.index(b)) for a, b in Ein))
    if key in _e_cache:
        return _e_cache[key]
    m = len(verts)
    if m == 1:
        return [1]
    relab = {v: k for k, v in enumerate(verts)}
    E2 = [(relab[a], relab[b]) for a, b in Ein]
    rest = [0]
    for C in clusterings(m, E2):
        if len(C) == 1:
            continue
        term = [factorial(m)]
        for B in C:
            term = pmul(term, pmul(ppow([-1, 1], len(B) - 1), e_poly(B, E2)))
        den = 1
        for B in C:
            den *= factorial(len(B))
        rest = padd(rest, [x // den for x in term])
    P = poincare_graph(range(m), E2)
    out = pdiv_exact(padd(P, rest, -1), ppow([-1, 1], m - 1))
    _e_cache[key] = out
    return out


def hessenberg_functions(n):
    def rec(i, lo):
        if i == n:
            yield ()
            return
        for v in range(max(lo, i + 1), n + 1):
            for rest in rec(i + 1, v):
                yield (v,) + rest
    return rec(0, 1)


def main():
    h1, h2 = (2, 3, 5, 5, 5), (2, 4, 4, 5, 5)
    print("== Part 1. Local matroids of the Track A pair")
    rows = {}
    for name, h in (("X1", h1), ("X2", h2)):
        V = vectors(5, graph(h))
        inv = val(api.matroid_invariants(V))
        kl = val(api.kazhdan_lusztig(V))
        ch = val(api.chow_ring(V))
        au = val(api.chow_ring(V, augmented=True))
        os_ = val(api.orlik_solomon(V))
        rows[name] = (inv["flats_by_rank"], ch["hilbert_function"], au["hilbert_function"],
                      kl["kl_polynomial"], kl["z_polynomial"], os_["hilbert_function"])
        print(f"{name} = Hess{h}: rank {inv['rank']}, flats by rank {inv['flats_by_rank']}")
        print(f"    A(M)            {ch['hilbert_function']}   (presentation = FY basis: {ch['agrees']})")
        print(f"    augmented A(M)  {au['hilbert_function']}   (presentation = FY basis: {au['agrees']})")
        print(f"    KL polynomial   {kl['kl_polynomial']},  Z-polynomial = Hilbert series of IH(M)  {kl['z_polynomial']}")
        print(f"    Orlik-Solomon   {os_['hilbert_function']}")
    print("    all equal for X1 and X2:", rows["X1"] == rows["X2"])
    print("    Betti numbers:  X1", poincare_graph(range(5), graph(h1)), "  X2", poincare_graph(range(5), graph(h2)))

    print("\n== Part 2. Euler-characteristic counts over the face poset")
    fs = {
        "1": lambda V: 1,
        "dim A": lambda V: sum(mt.chow_hilbert_series(V)) if V else 1,
        "dim aug A": lambda V: sum(mt.chow_hilbert_series(V, True)) if V else 1,
        "dim IH": lambda V: mt.kazhdan_lusztig(V)["ih_total_dimension"] if V else 1,
        "P_KL(1)": lambda V: sum(mt.kazhdan_lusztig(V)["kl_polynomial"]) if V else 1,
        "dim OS": lambda V: sum(abs(x) for x in mt.invariants(V, tutte_max=-1)["poincare_polynomial"]) if V else 1,
    }
    def faces_hess(n, E):
        """(rank, number of faces of this type, restriction vectors, contraction vectors)."""
        out = []
        for C in clusterings(n, E):
            blk = {v: i for i, B in enumerate(C) for v in B}
            inside = [(a, b) for a, b in E if blk[a] == blk[b]]
            cnt = factorial(n)
            for B in C:
                cnt //= factorial(len(B))
            k = len(C)
            quot = []
            for a, b in E:
                if blk[a] != blk[b]:
                    v = [0] * k
                    v[blk[a]] -= 1
                    v[blk[b]] += 1
                    quot.append(v)
            out.append((n - k, cnt, vectors(n, inside), quot))
        return out
    def faces_cpn(n):
        out = []
        for k in range(n + 1):        # faces CP^k: choose k+1 of the n+1 fixed points
            from math import comb
            out.append((k, comb(n + 1, k + 1), [[int(i == j) for i in range(k)] for j in range(k)],
                        [[int(i == j) for i in range(n - k)] for j in range(n - k)]))
        return out
    spaces = [("CP^2", faces_cpn(2), 3), ("CP^3", faces_cpn(3), 4),
              ("Fl(C^3)", faces_hess(3, graph((3, 3, 3))), 6),
              ("X1", faces_hess(5, graph(h1)), 120), ("X2", faces_hess(5, graph(h2)), 120)]
    print(f"{'f':10s} {'matroid':12s} " + " ".join(f"{name:>9s}" for name, _, _ in spaces))
    print(f"{'target: number of fixed points':23s}" + " ".join(f"{chi:>9d}" for _, _, chi in spaces))
    for fname, f in fs.items():
        for kind, idx in (("restriction", 2), ("contraction", 3)):
            vals = []
            for name, faces, chi in spaces:
                tot = 0
                for face in faces:
                    V = mt.parse_vectors(face[idx]) if face[idx] else []
                    tot += (-1) ** face[0] * face[1] * f(V)
                vals.append(tot)
            print(f"{fname:10s} {kind:12s} " + " ".join(f"{v:>9d}" for v in vals))

    print("\n== Part 3. Stratum polynomials e")
    for name, h in (("Fl(C^3)", (3, 3, 3)), ("X1", h1), ("X2", h2)):
        n = len(h)
        print(f"{name}: e = {show(e_poly(range(n), graph(h)))}")
    # is e a function of the matroid?  All connected Hessenberg graphs, n <= 6, by Tutte polynomial
    by_tutte = defaultdict(set)
    count = 0
    for n in range(2, 7):
        for h in hessenberg_functions(n):
            E = graph(h)
            if len(components(range(n), E)) > 1:
                continue
            count += 1
            V = mt.parse_vectors(vectors(n, E))
            t = tuple(sorted(mt.invariants(V, tutte_max=20)["tutte_polynomial"].items()))
            by_tutte[t].add((h, tuple(e_poly(range(n), E))))
    clash = {t: v for t, v in by_tutte.items() if len({e for _, e in v}) > 1}
    print(f"connected Hessenberg functions with n <= 6: {count}; Tutte classes: {len(by_tutte)}; "
          f"classes in which e is not constant: {len(clash)}")
    for t, v in list(clash.items())[:4]:
        for h, e in sorted(v):
            print(f"    h = {h}: e = {show(list(e))}")
        print()
    print("trees (free matroid), e:", {show(e_poly(range(n), graph(tuple(min(i + 2, n) for i in range(n))))) for n in range(2, 7)})
    for n in range(3, 7):
        print(f"K_{n}: e = {show(e_poly(range(n), graph((n,) * n)))}")


if __name__ == "__main__":
    main()

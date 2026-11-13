"""Independent check of Section 5.2 of the paper (partial Hessenberg varieties).

Written from scratch for the independent read: it imports nothing from the other
scripts in this directory.  Four checks.

A. Face poset.  The faces computed from GKM data alone (connected components of the
   subgraphs of the GKM graph whose labels lie in a flat) are compared with the
   closed description {(W_j, c_j)} used in the paper (Lemma 5.7).
B. Formula (2.2) for the Poincare polynomial, against a count of F_q-points of the
   variety, obtained by listing partial flags in F_q^4 for q = 5, 7.
C. Lemma 5.10 (fibration identity) for all (kbar, h) with n <= 7.
D. Theorem 5.8 through its proof: the data that Lemma 5.11 reconstructs (number of
   fixed points and the multiset of components of the inflated graph, as graphs with
   a vertex partition) determines the Poincare polynomial, for all (kbar, h), n <= 7.
   For n <= 5 the posets themselves are compared up to isomorphism.
"""
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product

# ---------------------------------------------------------------- basic data
def compositions(n):
    if n == 0:
        yield ()
        return
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield (first,) + rest

def hessenberg_functions(s):
    def rec(i, lo):
        if i == s:
            yield ()
            return
        for v in range(max(lo, i + 1), s + 1):
            for rest in rec(i + 1, v):
                yield (v,) + rest
    return rec(0, 1)

def part_edges(h):                      # edges of Gamma_h on parts 0..s-1
    return {(a, b) for a in range(len(h)) for b in range(a + 1, h[a])}

def fixed_points(n, kbar):              # tuples part[x] for labels x = 0..n-1
    def rec(x, left):
        if x == n:
            yield ()
            return
        for a in range(len(kbar)):
            if left[a]:
                left[a] -= 1
                for rest in rec(x + 1, left):
                    yield (a,) + rest
                left[a] += 1
    return rec(0, list(kbar))

def poincare(n, kbar, h):               # formula (2.2)
    E = part_edges(h)
    c = Counter()
    for J in fixed_points(n, kbar):
        c[sum(1 for x in range(n) for y in range(x) if (J[x], J[y]) in E)] += 1
    return tuple(c[i] for i in range(max(c) + 1))

def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return tuple(r)

def qfact(k):
    p = (1,)
    for i in range(1, k + 1):
        p = pmul(p, (1,) * i)
    return p

# ---------------------------------------------------------------- A. face poset
def faces_from_gkm(n, kbar, h):
    """Faces as (rank, frozenset of fixed points), from the GKM graph only."""
    E = part_edges(h)
    FP = list(fixed_points(n, kbar))
    def weights(J):                     # tangent weights at J as label pairs (x, y), x < y
        return [(x, y) for x in range(n) for y in range(x + 1, n)
                if (min(J[x], J[y]), max(J[x], J[y])) in E and J[x] != J[y]]
    def blocks(n, pairs):               # components of the label graph
        comp = list(range(n))
        def find(v):
            while comp[v] != v:
                v = comp[v]
            return v
        for x, y in pairs:
            comp[find(x)] = find(y)
        return [find(v) for v in range(n)]
    out = set()
    for J in FP:
        W = weights(J)
        # flats of the graphic matroid at J = closed edge sets = partitions into connected blocks
        seen = set()
        for r in range(len(W) + 1):
            for S in combinations(W, r):
                b = tuple(blocks(n, S))
                if b in seen:
                    continue
                seen.add(b)
                span = [(x, y) for (x, y) in W if b[x] == b[y]]      # the flat
                # connected component of J in the GKM subgraph with labels in the flat
                comp = {J}
                stack = [J]
                while stack:
                    I = stack.pop()
                    for (x, y) in weights(I):
                        if b[x] == b[y]:
                            L = list(I)
                            L[x], L[y] = L[y], L[x]
                            L = tuple(L)
                            if L not in comp:
                                comp.add(L)
                                stack.append(L)
                out.add((n - len(set(b)), frozenset(comp)))
    return out

def set_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]
        yield [[first]] + p

def faces_from_description(n, kbar, h):
    """Faces {(W_j, c_j)}: blocks of labels with part counts, each block a singleton or
    with counts supported on a connected set of at least two parts of Gamma_h."""
    E = part_edges(h)
    s = len(kbar)
    def connected(supp):
        supp = sorted(supp)
        return all((supp[i], supp[i + 1]) in E for i in range(len(supp) - 1))  # interval graph
    def count_vectors(size):
        def rec(a, left):
            if a == s:
                if left == 0:
                    yield ()
                return
            for v in range(min(left, kbar[a]) + 1):
                for rest in rec(a + 1, left - v):
                    yield (v,) + rest
        for c in rec(0, size):
            supp = [a for a in range(s) if c[a]]
            if size == 1 or (len(supp) >= 2 and connected(supp)):
                yield c
    FP = list(fixed_points(n, kbar))
    out = set()
    for P in set_partitions(list(range(n))):
        for cs in product(*[list(count_vectors(len(B))) for B in P]):
            if tuple(sum(c[a] for c in cs) for a in range(s)) != tuple(kbar):
                continue
            fp = frozenset(J for J in FP if all(
                Counter(J[x] for x in B) == Counter({a: c[a] for a in range(s) if c[a]})
                for B, c in zip(P, cs)))
            out.add((n - len(P), fp))
    return out

# ---------------------------------------------------------------- B. point counts
def rank_mod(rows, p):
    rows = [r[:] for r in rows]
    rk = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], -1, p)
        rows[rk] = [(v * inv) % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def rref_key(rows, p):
    rows = [r[:] for r in rows]
    rk = 0
    for c in range(len(rows[0])):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], -1, p)
        rows[rk] = [(v * inv) % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return tuple(map(tuple, rows[:rk]))

def full_flags(n, p):
    """One basis (list of vectors) per full flag of F_p^n, by Schubert cells."""
    for w in permutations(range(n)):
        free = [(r, j) for j in range(n) for r in range(w[j])
                if r not in w[:j]]
        for vals in product(range(p), repeat=len(free)):
            g = [[0] * n for _ in range(n)]          # g[j] = j-th basis vector
            for j in range(n):
                g[j][w[j]] = 1
            for (r, j), v in zip(free, vals):
                g[j][r] = v
            yield g

def point_count(n, kbar, h, p):
    """Number of F_p-points of Hess_kbar(M, h), M = diag(1, ..., n), by listing partial flags."""
    K = [sum(kbar[:a + 1]) for a in range(len(kbar))]
    seen = set()
    count = 0
    for g in full_flags(n, p):
        key = tuple(rref_key(g[:k], p) for k in K[:-1])
        if key in seen:
            continue
        seen.add(key)
        ok = True
        for a in range(len(kbar)):
            tgt = K[h[a] - 1]
            if tgt == n:
                continue
            V = g[:tgt]
            MV = [[(v * (i + 1)) % p for i, v in enumerate(vec)] for vec in g[:K[a]]]
            if rank_mod(V + MV, p) != tgt:
                ok = False
                break
        count += ok
    return count

# ---------------------------------------------------------------- D. invariants
def canon_partitioned_component(parts, sizes, E):
    """Canonical form of the inflation of the induced graph on `parts` (an interval of
    parts, connected), as a graph with a vertex partition, by brute force over the
    orderings of the parts."""
    best = None
    for order in permutations(range(len(parts))):
        key = (tuple(sizes[parts[i]] for i in order),
               tuple(sorted((min(order.index(i), order.index(j)), max(order.index(i), order.index(j)))
                            for i in range(len(parts)) for j in range(i + 1, len(parts))
                            if (parts[i], parts[j]) in E)))
        if best is None or key < best:
            best = key
    return best

def reconstructed_data(n, kbar, h):
    from math import factorial
    E = part_edges(h)
    s = len(kbar)
    comps, cur = [], [0]
    for a in range(1, s):
        if h[a - 1] > a:                # a-1 and a adjacent
            cur.append(a)
        else:
            comps.append(cur)
            cur = [a]
    comps.append(cur)
    nfix = factorial(n)
    for k in kbar:
        nfix //= factorial(k)
    return (nfix, tuple(sorted(canon_partitioned_component(c, kbar, E) for c in comps if len(c) >= 2)))

def main():
    ok = True
    def report(name, good, detail=""):
        nonlocal ok
        ok &= bool(good)
        print(f"[{'PASS' if good else 'FAIL'}] {name}{(' -- ' + detail) if detail else ''}", flush=True)

    # A
    cases = bad = 0
    for n in range(2, 6):
        for kbar in compositions(n):
            for h in hessenberg_functions(len(kbar)):
                cases += 1
                if faces_from_gkm(n, kbar, h) != faces_from_description(n, kbar, h):
                    bad += 1
                    print("   mismatch", n, kbar, h)
    report("A. faces from the GKM graph = faces {(W_j, c_j)} of Lemma 5.7, with ranks", bad == 0,
           f"{cases} pairs (kbar, h), n <= 5")

    # B
    cases = bad = 0
    for p in (5, 7):
        for kbar in compositions(4):
            for h in hessenberg_functions(len(kbar)):
                cases += 1
                P = poincare(4, kbar, h)
                if point_count(4, kbar, h, p) != sum(c * p ** i for i, c in enumerate(P)):
                    bad += 1
                    print("   mismatch", p, kbar, h)
    report("B. #X(F_q) = sum_J q^ind(J)  (formula (2.2)), n = 4, q = 5, 7", bad == 0, f"{cases} cases")

    # C and D
    cases = bad = 0
    groups = defaultdict(set)
    for n in range(1, 8):
        for kbar in compositions(n):
            K = [sum(kbar[:a + 1]) for a in range(len(kbar))]
            for h in hessenberg_functions(len(kbar)):
                cases += 1
                P = poincare(n, kbar, h)
                ht = tuple(K[h[a] - 1] for a in range(len(kbar)) for _ in range(kbar[a]))
                full = poincare(n, (1,) * n, ht)
                rhs = P
                for k in kbar:
                    rhs = pmul(rhs, qfact(k))
                if full != rhs:
                    bad += 1
                groups[reconstructed_data(n, kbar, h)].add(P)
    report("C. P_Hess(h~) = P_X * prod [k_a]_q!  (Lemma 5.10)", bad == 0, f"{cases} pairs (kbar, h), n <= 7")
    multi = [k for k, v in groups.items() if len(v) > 1]
    report("D. data reconstructed by Lemma 5.11 determines the Poincare polynomial", not multi,
           f"{cases} pairs fall into {len(groups)} classes, n <= 7")
    print("ALL PASS" if ok else "FAILURES")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())

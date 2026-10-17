"""Partial regular semisimple Hessenberg varieties: fixed points, Betti numbers, face posets.

Data: n, a composition kbar = (k_1,...,k_s) of n, a Hessenberg function h on [s].
Gamma_h on [s] has edges {a,b}, a < b <= h(a).  (kbar = (1,...,1) is the full-flag case.)

* Fixed points: ordered set partitions J = (J_1,...,J_s) of [n], |J_a| = k_a
  (Ayzenberg-Buchstaber, IMRN 2024, Thm 2 proof, item I).
* Tangent weights at J: e_x - e_y, x in J_a, y in J_b, a < b <= h(a) (ibid., item II).
* Betti numbers (Bialynicki-Birula, generic cocharacter): beta_{2k} = #{J : ind(J) = k},
  ind(J) = #{(x in J_a, y in J_b) : a < b <= h(a), x > y}. For kbar = (1,...,1) this is the
  De Mari-Procesi-Shayman statistic used in experiments/counterexample/.
* Faces (ibid., item III): the face X_(C,kappa) depends only on the set partition
  {sigma(V_j)} of the coordinates [n] and, for each block, the vector of part-counts
  k_i(V_j). A block with count vector c is admissible iff the induced subgraph of the
  inflated graph Gamma_h(kbar) on it is connected: supp(c) is connected in Gamma_h and either
  |supp(c)| >= 2 or c is a single vertex (parts are independent sets in the inflation).
  A face is a set {(W_j, c_j)} with the W_j partitioning [n], |c_j| = |W_j|, sum_j c_j = kbar.
  Order: refine blocks, with counts adding up. Rank = n - #blocks.
"""
from itertools import combinations, permutations, product
from collections import Counter
from functools import lru_cache

def compositions(n):
    if n == 0:
        yield (); return
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield (first,) + rest

def hessenberg_functions(s):
    def rec(j, lo):
        if j > s: yield (); return
        for v in range(max(j, lo), s + 1):
            for rest in rec(j + 1, v): yield (v,) + rest
    return list(rec(1, 1))

def graph(h):
    s = len(h)
    return frozenset(frozenset((a, b)) for a in range(1, s + 1) for b in range(a + 1, h[a - 1] + 1))

def connected_support(supp, E):
    supp = set(supp)
    if not supp: return False
    start = next(iter(supp)); seen = {start}; stack = [start]
    while stack:
        a = stack.pop()
        for e in E:
            if a in e:
                (b,) = e - {a}
                if b in supp and b not in seen:
                    seen.add(b); stack.append(b)
    return seen == supp

def admissible(c, E):
    supp = [i + 1 for i, x in enumerate(c) if x]
    if len(supp) == 1: return sum(c) == 1
    return connected_support(supp, E)

def fixed_points(n, kbar):
    out = []
    def rec(remaining, a, acc):
        if a == len(kbar):
            out.append(tuple(acc)); return
        for blk in combinations(sorted(remaining), kbar[a]):
            rec(remaining - set(blk), a + 1, acc + [frozenset(blk)])
    rec(set(range(1, n + 1)), 0, [])
    return out

def poincare(n, kbar, h):
    s = len(kbar); E = graph(h); P = Counter()
    for J in fixed_points(n, kbar):
        ind = sum(1 for a in range(1, s + 1) for b in range(a + 1, h[a - 1] + 1)
                  for x in J[a - 1] for y in J[b - 1] if x > y)
        P[ind] += 1
    return tuple(P[k] for k in range(max(P) + 1))

def set_partitions(items):
    items = list(items)
    if not items: yield []; return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | {first}] + p[i + 1:]
        yield p + [{first}]

def count_vectors(size, kbar):
    for c in product(*(range(min(k, size) + 1) for k in kbar)):
        if sum(c) == size: yield c

def faces(n, kbar, h):
    """All faces as frozensets of (block, counts)."""
    E = graph(h); out = []
    for P in set_partitions(range(1, n + 1)):
        blocks = [frozenset(b) for b in P]
        options = [[c for c in count_vectors(len(b), kbar) if admissible(c, E)] for b in blocks]
        for choice in product(*options):
            if tuple(map(sum, zip(*choice))) == tuple(kbar):
                out.append(frozenset(zip(blocks, choice)))
    return out

def split_counts(c):
    """unordered ways to write c = c' + c'' with c', c'' nonzero."""
    for c1 in product(*(range(x + 1) for x in c)):
        c2 = tuple(a - b for a, b in zip(c, c1))
        if any(c1) and any(c2) and c1 <= c2: yield c1, c2

def lower_covers(face, E):
    n_cov = 0
    for W, c in face:
        if len(W) < 2: continue
        Wl = sorted(W)
        for r in range(1, len(Wl)):
            for A in combinations(Wl, r):
                if Wl[0] not in A: continue            # each unordered split once
                B = tuple(x for x in Wl if x not in A)
                for c1 in count_vectors(len(A), c):
                    c2 = tuple(a - b for a, b in zip(c, c1))
                    if all(v >= 0 for v in c2) and admissible(c1, E) and admissible(c2, E):
                        n_cov += 1
    return n_cov

def upper_covers(face, E):
    items = list(face)
    return sum(1 for (W1, c1), (W2, c2) in combinations(items, 2)
               if admissible(tuple(a + b for a, b in zip(c1, c2)), E))

def invariant(n, kbar, h):
    E = graph(h); inv = {}
    for f in faces(n, kbar, h):
        r = n - len(f)
        inv.setdefault(r, Counter())[(lower_covers(f, E), upper_covers(f, E))] += 1
    return tuple(tuple(sorted(inv[r].items())) for r in sorted(inv))

def leq(f1, f2):
    for W, c in f2:
        parts = [(W1, c1) for W1, c1 in f1 if W1 <= W]
        if sum(len(W1) for W1, _ in parts) != len(W): return False
        if tuple(map(sum, zip(*[c1 for _, c1 in parts]))) != c: return False
    return True

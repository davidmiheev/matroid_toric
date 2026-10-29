"""Check: Cl_Gamma determines Gamma up to isomorphism, for ALL simple graphs on <= N vertices.

Every graph on n vertices (nauty-geng, one per isomorphism class) gives its cluster-permutohedron
Cl_Gamma (Ayzenberg-Buchstaber, Def. 2.14), built from the definition with covers obtained by
merging two clusters joined by an edge. Its exact isomorphism class is the nauty canonical form of
the Hasse diagram coloured by rank. The claim holds iff no two graphs share a canonical form.
Graphs with different n are compared too (the forms record the cell sizes).

Usage: engine/.venv/bin/python reconstruction_check.py N
"""
import random, subprocess, sys, time
from collections import defaultdict
from itertools import permutations
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "engine" / "src"))
from mtengine.backends.nauty import canonical_form


def graphs(n):
    out = subprocess.run(["nauty-geng", "-q", str(n)], capture_output=True, text=True, check=True).stdout
    for line in out.split():
        data = [ord(c) - 63 for c in line[1:]]          # graph6, n <= 62
        bits = [(b >> (5 - i)) & 1 for b in data for i in range(6)]
        E, k = [], 0
        for j in range(1, n):
            for i in range(j):
                if bits[k]: E.append((i, j))
                k += 1
        yield E


def set_partitions(items):
    items = list(items)
    if not items: yield []; return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)): yield p[:i] + [p[i] | {first}] + p[i + 1:]
        yield p + [{first}]


def connected(block, adj):
    block = set(block); s = next(iter(block)); seen = {s}; st = [s]
    while st:
        v = st.pop()
        for w in adj[v]:
            if w in block and w not in seen: seen.add(w); st.append(w)
    return seen == block


def cluster_permutohedron(n, E):
    adj = defaultdict(set)
    for a, b in E: adj[a].add(b); adj[b].add(a)
    elems = {}
    for P in set_partitions(range(n)):
        if not all(connected(B, adj) for B in P): continue
        blocks = [frozenset(B) for B in P]
        for p in permutations(range(n)):
            e = frozenset((B, frozenset(p[v] for v in B)) for B in blocks)
            elems.setdefault(e, len(elems))
    rank = {e: n - len(e) for e in elems}
    hasse = []
    for e, i in elems.items():
        items = list(e)
        for x in range(len(items)):
            for y in range(x + 1, len(items)):
                (B1, S1), (B2, S2) = items[x], items[y]
                if any(w in adj[v] for v in B1 for w in B2):
                    up = frozenset([z for k, z in enumerate(items) if k not in (x, y)] + [(B1 | B2, S1 | S2)])
                    hasse.append((i, elems[up]))
    ranks = [0] * len(elems)
    for e, i in elems.items(): ranks[i] = rank[e]
    return len(elems), ranks, hasse


def relabelled_form(n, E, seed):
    """Canonical form of Cl for a randomly relabelled copy of the graph, with the poset's
    elements also listed in a shuffled order."""
    rng = random.Random(seed)
    p = list(range(n)); rng.shuffle(p)
    size, ranks, hasse = cluster_permutohedron(n, [(p[a], p[b]) for a, b in E])
    q = list(range(size)); rng.shuffle(q)
    hasse = [(q[a], q[b]) for a, b in hasse]
    cells = [[q[i] for i, r in enumerate(ranks) if r == k] for k in range(max(ranks) + 1)]
    return canonical_form(size, hasse, cells, algorithm="traces")


N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
# Non-vacuity: isomorphic inputs must give equal forms (all graphs with n <= 4, 3 relabellings).
for n in range(1, 5):
    for E in graphs(n):
        forms0 = {relabelled_form(n, E, seed) for seed in range(3)}
        assert len(forms0) == 1, (n, E)
print("self-check passed: relabelled copies give identical canonical forms (n <= 4)", flush=True)
forms = defaultdict(list)
for n in range(1, N + 1):
    count = 0
    for E in graphs(n):
        t0 = time.time()
        size, ranks, hasse = cluster_permutohedron(n, E)
        cells = [[i for i, r in enumerate(ranks) if r == k] for k in range(max(ranks) + 1)]
        forms[canonical_form(size, hasse, cells, algorithm="traces")].append((n, E))
        count += 1
        if n >= 6:
            print(f"  n={n} graph {count}: {len(E)} edges, {size} elements, {time.time() - t0:.1f}s",
                  file=sys.stderr, flush=True)
    print(f"n={n}: {count} graphs (all isomorphism classes)", flush=True)
clashes = [v for v in forms.values() if len(v) > 1]
print(f"total {sum(len(v) for v in forms.values())} graphs, {len(forms)} distinct Cl posets, "
      f"{len(clashes)} pairs of non-isomorphic graphs with isomorphic Cl")
for v in clashes: print("   CLASH:", v)

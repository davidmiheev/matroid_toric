# Track C results: face poset of Fl(Cⁿ) vs the tropical flag variety

**Question 3 (thesis v2, §5):** how does the face poset `S(Fl(Cⁿ)) ≅ Cl(Kₙ)` compare with the
fan structure of the flag Dressian? For n ≤ 5 the flag Dressian equals the tropical flag
variety (Brandt–Eur–Zhang), so we compare with `trop Fl_n`.

**Verdict: kill criterion met. The track is frozen.** No rank-preserving poset map exists,
for a structural reason at every n ≠ 4 and by counting at n = 4.

## Computation

| Step | File |
|---|---|
| Plücker ideal of Fl(Cⁿ) as a kernel of minors (Macaulay2) | `flag_ideal.m2` → `fl{3,4}.gfan` |
| gfan's parser mishandles variable names that share a prefix (`p1`, `p12`, …): it aborts with `Monomial p1^27 not found in p1^36`. Renamed to single letters, with a key | `fl{n}_letters.gfan`, `fl{n}_key.txt` |
| `gfan _tropicalstartingcone \| gfan _tropicaltraverse` | `trop_fl{3,4}.out` |
| Comparison | `compare_cl_trop.py` → `compare_cl_trop.log` |

| | dim | lineality | cones by dimension mod lineality |
|---|---|---|---|
| trop Fl₃ | 5 | 4 | (1, 3) |
| trop Fl₄ | 9 | 6 | (1, 20, 79, 78) |

Sanity check: the 78 maximal cones of trop Fl₄ agree with the known count.

| | elements by rank |
|---|---|
| Cl(K₃) | (6, 9, 1) |
| Cl(K₄) | (24, 72, 34, 1) |

## Why no comparison exists

- **Lengths.** Modulo lineality, trop Flₙ has dimension `dim Fl(Cⁿ) − (n−1) = (n−1)(n−2)/2`.
  This is the lineality of `T^n` plus the `n−1` level scalings, minus the one overlap, and it
  equals the **complexity** of the torus action on Fl(Cⁿ). The rank of Cl(Kₙ) is `n−1`, the
  **rank** of the torus. The two agree only at n = 4. So for every n ≠ 4 there is no
  rank-preserving map in either direction or orientation.
- **n = 4, counts.** Neither Cl(K₄) nor its dual Cl(K₄)^op admits a rank-preserving
  injection into the fan's face poset, nor a surjection onto it: some rank is too large on
  one side and too small on the other in every case (see the log).
- **Loophole: surjections onto a small subfan.** These exist (for example onto the faces
  of one maximal cone), but they are pure counting and carry no geometry, so they don't
  answer the question.

## What would make the question meaningful

A comparison has to be geometric, not a bare poset map. The natural candidate is the
Gelfand–Serganova stratification: a generic point of each face of the torus action has a
flag matroid, while the cones of trop Flₙ correspond to regular flag-matroidal subdivisions
of the permutohedron (Brandt–Eur–Zhang (d)). Relating those two is a research question,
not an afternoon experiment. It stays frozen unless a concrete conjecture comes up.

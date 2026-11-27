# eConjecturePrimitiveTrinomial: Lean 4 and Julia programs for "Parity Families of Lattice Paths"

Deep Bhattacharjee (ORCID 0000-0003-0466-750X)

This repository holds the machine checks for the paper *Parity Families of Lattice Paths:
Extremal Systems for All Lengths, Binary Ranks of Grids and Rigidity in Higher Dimensions*. The
paper is an extended and elaborated version of the Hexagon deposit hexagon:2610.00474v1
(https://hexagonmath.org/2610.00474v1).

## Lean 4 (`LatticePaths/`)

Lean 4.33.1 with Mathlib v4.33.1. Build with `lake build`; check axioms with
`lake env lean Axioms.lean` (output in `axioms.txt`). There is no `sorry`. Every theorem in the
`LatticePaths` namespace (102 theorems, including auxiliary ones) depends at most on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`.

### Formalised in general (all lengths)

`LatticePaths/General/Shankar.lean`:

| Lean name | statement | paper |
|---|---|---|
| `ce_cons` | the append rule for common edges | Lemma 2.1(b) |
| `ce_self`, `ce_comm` | `ce m x x = m`; symmetry | Lemma 2.1(a) |
| `split_lemma` | a set A^a can meet a set A'^b with a != b only if neither class is split | Lemma 2.4 |
| `admissible_G` | the systems G_0, G_1 of length m are admissible | Proposition 2.5(i) |
| `norm_le_G` | the norm of a system is at most the sum of the norms of G_0 and G_1 | Proposition 2.5(ii) |
| `shankar_inequality` | every admissible system of length m has sum of squared class sizes at most 2^m | Theorem 2.6 (Shankar) |
| `even_family_card_sq_le` | a one-weight family with pairwise common-edge counts of the parity of m has at most 2^(m/2) members | Example 2.4 + Theorem 2.6 |
| `even_family_square` | an even family of paths from (0,0) to (n,n) has at most 2^n members | Theorem 2.7(i) (Shankar) |

Convention: a word of length m is a map `Fin m → Bool`, `true` = north step, and the index `0`
is the *last* step. With this convention the common-edge count is defined by recursion on the
last step, which is exactly the append rule.

### Formalised only for small cases (finite checks by `decide +kernel`)

`LatticePaths/Finite/PathChecks.lean` and `LatticePaths/Finite/EnumChecks.lean` are the 29 finite
checks of the earlier archive, ported to Lean 4.33. The only change is that the sums over
permutations are formed along the insertion tree, to keep the kernel evaluation shallow.

They cover:
- the rigidity lemma for k <= 6 and the canonical pairs for k <= 7;
- the skeleton identity for m <= 6 and the number C(m, floor(m/2)) of skeletons for m <= 12;
- the Catalan classification for n <= 3;
- the three-row and window families, and the odd families for n = 7, 8;
- block families in dimensions 3 to 5;
- the Eulerian, Mantaci and Desarmenien-Foata identities for n <= 7, plus P_5;
- a caged example and the deformed Dumont counts;
- Q_0..Q_24 and the two Hankel determinants;
- the 2-Steiner matrix for n <= 10.

**Not formalised.** The following are proved in the paper but are not formalised in general:
- that skeleton systems are extremal, and the Catalan classification;
- the general count of skeletons (ballot numbers);
- the binary rank of grid graphs;
- all analytic results (Section 8 onwards).

## Exact computations

- `python/`: Python and C programs that recompute every numerical statement of the paper in
  exact arithmetic (see `python/README.md`).
- `julia/`: the Julia programs of the earlier archive (`julia run_all.jl`).

## License

MIT (see `LICENSE`).

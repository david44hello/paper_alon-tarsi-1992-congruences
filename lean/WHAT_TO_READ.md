# Reading guide

This Lean 4 library formalizes all results of *The Alon–Tarsi (1992) conjecture: for $n > 2$, congruences modulo divisors of $(n!)^3$ can prove it only at Drisko's orders*. Every claim in `AlonTarsi/Paper/Statements.lean` is proved solely from Lean 4's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom axioms, zero cited axioms, zero `sorry`, and zero external computer checks.

## Trust surface

A referee only needs to read the definitions and statements:

- [Basic definitions](AlonTarsi/Defs/Basic.lean): Latin squares, row/column/symbol signs, `evenCount`, `oddCount`, `delta` ($\Delta_n$), `reducedDelta` ($D_n$), `cVal` ($c_n$), `naturalModulus` ($M_q(n)$), `fVal` ($f_q(n, N)$), `qVal` ($v_q$), and isotopies.
- [Circuit definitions](AlonTarsi/Defs/Circuit.lean): multidigraphs, adjacency matrices, regularity, circuit partition polynomials `circuitPoly` ($j(H; x)$), `circuitEval` ($j(M)$), single-vertex elimination `elimDigraph`, profiles, subset elimination `splitDigraph`, and multidigraph automorphisms.
- [Order-$2q$ definitions](AlonTarsi/Defs/TwoQ.lean): elementary abelian subgroups, `elemRank`, signed fixed-point sums, the Sylow $q$-subgroup `sylowP` ($P \cong \mathbb{F}_q^6$), block normalizers (`blockSwapPerm`, `blockScalePerm`), complete-map sums `tauQ` ($\tau_q$) and `tQ` ($t_q$), rank-1 generators `ell0`, `ellB`, `ellC`, patterns, layers, centered subsets, and trace matrices `matA`, `matB`, `matE`, `matF`, `matU`, `matS`.
- [Formal statements](AlonTarsi/Paper/Statements.lean): all 43 formal claims, checked against the paper.

## Proof modules

| Section / Result | Proof file(s) | Axioms |
|---|---|---|
| Section 1–2 basics (odd orders, Janssen, isotopy invariance, normalization, reduced $c_n$) | [LatinBasics.lean](AlonTarsi/Proofs/LatinBasics.lean) | Standard axioms alone |
| Section 3 (Lemmas 3.1–3.3, Corollary 3.4, Propositions 3.5–3.6) & Lemma 5.1 | [CircuitPoly.lean](AlonTarsi/Proofs/CircuitPoly.lean) | Standard axioms alone |
| Section 4 (Theorem 4.1, Corollary 4.2, $n = 3q - 1$ boundary) | [Quadratic.lean](AlonTarsi/Proofs/Quadratic.lean) | Standard axioms alone |
| Section 5 (Remark 5.2, Lemmas 5.3–5.4, Theorem 5.5) | [SylowMid.lean](AlonTarsi/Proofs/SylowMid.lean) | Standard axioms alone |
| Section 6 (Lemmas 6.2–6.5: Möbius reduction, rank bound, signs, normalizers, complete maps) | [TwoQMobius.lean](AlonTarsi/Proofs/TwoQMobius.lean) | Standard axioms alone |
| Section 6 (Lemma 6.6: vanishing, rank-3 divisibility, exact rank-2 sum) | [TwoQRankTwoHelpers.lean](AlonTarsi/Proofs/TwoQRankTwoHelpers.lean), [TwoQRankTwo.lean](AlonTarsi/Proofs/TwoQRankTwo.lean) | Standard axioms alone |
| Section 6 (Lemmas 6.7–6.8, Proposition 6.9: rank-1 sign factorization and strata) | [TwoQRankOne.lean](AlonTarsi/Proofs/TwoQRankOne.lean) | Standard axioms alone |
| Section 6 (Lemmas 6.10–6.11, Proposition 6.12, Theorem 6.1, exact 3-part of $D_6$) | [TwoQTraces.lean](AlonTarsi/Proofs/TwoQTraces.lean) | Standard axioms alone |
| Stones–Wanless (2012) Theorem 3.5 (self-contained proof) | [StonesWanless35.lean](AlonTarsi/Proofs/StonesWanless35.lean) | Standard axioms alone |
| Drisko (1997) Theorem 1 (self-contained proof) | [Drisko1997.lean](AlonTarsi/Proofs/Drisko1997.lean) | Standard axioms alone |
| Section 1, 4, 7 assembly (Theorems A, B, C, uniform divisor, small orders, figure captions, numeric bounds) | [MainAssembly.lean](AlonTarsi/Proofs/MainAssembly.lean) | Standard axioms alone |

Both external results cited in Section 7 of the paper — Stones–Wanless Theorem 3.5 ($q \mid D_n$ for even $n$ and prime $n/2 < q \le n - 2$) and Drisko's 1997 congruence ($\Delta_{p+1} \equiv (-1)^{(p+1)/2} p^2 \pmod{p^3}$ for odd primes $p$) — are proved directly in Lean rather than taken as axioms or hypotheses.

## Checking the proof library

The [verification command](README.md#how-to-verify) builds the entire project, scans all Lean files for proof holes and forbidden constructs, and regenerates [AUDIT.md](AUDIT.md) from `#print axioms`. The [comparator](../comparator/README.md) compares all 43 theorems against independent `sorry`-stubbed statements that import only `AlonTarsi.Defs.*`. Its paranoid mode also checks the exported proofs with Lean's paranoid kernel, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`. Release checks include a fresh build from empty, `#print axioms` audit, kernel replay via `scripts/kernel_replay.sh`, and `lake comparator` in standard and `--paranoid` modes. GitHub's hosted build runs once the repository is public.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).

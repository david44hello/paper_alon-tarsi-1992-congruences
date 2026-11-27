# Audit notes

## Paper reference

The formal statements in `AlonTarsi/Paper/Statements.lean` correspond to the paper *The Alon–Tarsi (1992) conjecture: for $n > 2$, congruences modulo divisors of $(n!)^3$ can prove it only at Drisko's orders*, version `v1.60` (PDF MD5 `9b8715f39904f65a282de541c42187d4`, source tarball MD5 `7e86e1b493e50ecb6fc1a3003e6b4d36`).

## Axioms and published inputs

- **Custom axioms:** none.
- **Cited axioms:** none.
- **Sorry / admit / native_decide:** none.
- Every one of the 43 rows in `AUDIT.md` depends only on Lean 4's three standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
- Both external results used in Section 7 of the paper are proved directly from Lean's standard axioms:
  1. **Stones–Wanless (2012), Theorem 3.5** (`stones_wanless_thm_3_5`): proved directly in `AlonTarsi/Proofs/StonesWanless35.lean`.
  2. **Drisko (1997), Theorem 1** (`drisko_1997`): proved directly in `AlonTarsi/Proofs/Drisko1997.lean` using the translation group $(\mathbb{Z}/p\mathbb{Z})^3$ and Lemma 6.5 (`lem_6_5_complete`).

## Coverage notes

- All 28 numbered formal blocks (Theorems A, B, C; Theorems 4.1, 5.5, 6.1; Propositions 3.5, 3.6, 6.9, 6.12; Corollaries 3.4, 4.2; Remark 5.2; Lemmas 3.1–3.3, 5.1, 5.3–5.4, 6.2–6.8, 6.10–6.11) are stated individually in `AlonTarsi/Paper/Statements.lean` and proved without `sorry`.
- Supporting displayed identities, figure captions, and concrete numeric claims are covered explicitly by `odd_order_delta_zero`, `eq_orbit`, `sec1_small_orders_and_headline`, `sec1_fig1_small_counts`, `eq_janssen`, `eq_isotopy`, `eq_normal`, `eq_cn_reduced`, `sec3_fig4_elim_n4`, `sec4_numeric_bounds`, `sec5_three_q_minus_one`, `sec6_concrete_in_text`, `sec7_uniform_divisor`, `stones_wanless_thm_3_5`, and `drisko_1997`.
- All proofs follow the mathematical architecture of the paper; small concrete checks (`n = 2, 4, 6`, `q = 3`, `n = 8, 26`) are discharged directly inside Lean's kernel without `native_decide`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).

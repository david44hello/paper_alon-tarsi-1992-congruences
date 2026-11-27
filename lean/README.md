# The Alon–Tarsi (1992) conjecture: for $n > 2$, congruences modulo divisors of $(n!)^3$ can prove it only at Drisko's orders

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_alon-tarsi-1992-congruences).

All 43 claims of the paper — Theorems A, B, and C, Theorems 4.1, 5.5, and 6.1, all supporting propositions, corollaries, lemmas, remarks, displayed identities, numeric bounds, and both published inputs (Stones–Wanless Theorem 3.5 and Drisko 1997) — are proved in Lean 4 from Lean's three standard axioms alone, with zero custom axioms, zero cited axioms, and zero `sorry`.

The [reading guide](WHAT_TO_READ.md) maps each section and claim to its Lean files and summarizes how the release was checked.

## How to verify

Install Git, Python 3, ripgrep, and elan. Run the following command from the `lean/` directory.

```sh
./scripts/check.sh
```

The command builds the library, scans all Lean sources for proof holes or forbidden constructs, and runs `#print axioms` on every theorem in `AlonTarsi/Paper/Statements.lean` to regenerate `AUDIT.md`. Its last line is

```text
PASS: project builds; source policy passes; every paper claim proved from standard axioms only.
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).

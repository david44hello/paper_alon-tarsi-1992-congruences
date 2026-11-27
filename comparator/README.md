# Comparing the Lean statements

The challenge states all 43 claims of the paper (Theorems A, B, C, Theorems 4.1, 5.5, 6.1, all supporting propositions, corollaries, lemmas, remarks, displayed identities, numeric bounds, and both published inputs Stones–Wanless Theorem 3.5 and Drisko 1997) with open (`sorry`) proofs, importing only `AlonTarsi.Defs.Basic`, `AlonTarsi.Defs.Circuit`, and `AlonTarsi.Defs.TwoQ`. The solution in the `lean/` directory supplies the proofs. The comparison permits only Lean's three standard axioms (`propext`, `Quot.sound`, `Classical.choice`).

To run the comparison on Linux with Git, elan, and bubblewrap, start at the root of the checked-out repository.

```sh
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -xf - -C "$comparison_dir"
cp comparator/Challenge.lean comparator/comparator.json comparator/lakefile.toml "$comparison_dir/"
cd "$comparison_dir"
lake exe cache get
lake --no-cache comparator --config=comparator.json --paranoid
```

Lake compares all 43 declarations and checks the solution. A successful run ends with `Your solution is okay!`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).

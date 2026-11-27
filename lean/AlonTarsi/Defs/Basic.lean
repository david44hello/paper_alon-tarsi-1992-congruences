module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Core Definitions for Latin Squares, Signs, and Congruence Moduli

This file defines Latin squares of order `n`, their row/column/symbol permutations and signs,
the signed counts `Δ_n = L^e_n - L^o_n` and `D_n` (for reduced squares), the isotopy group
`S_n^3`, the `q`-adic valuation `v_q` with `v_q(0) = ∞`, the natural modulus `M_q(n)`,
the obstruction integer `c_n`, and the minimal factorial-valuation function `f_q(n, N)`.
-/

namespace AlonTarsi

/-- A Latin square of order `n`, indexed by `Fin n`. -/
structure LatinSquare (n : ℕ) where
  entry : Fin n → Fin n → Fin n
  row_bijective : ∀ r : Fin n, Function.Bijective (fun c => entry r c)
  col_bijective : ∀ c : Fin n, Function.Bijective (fun r => entry r c)

@[ext]
theorem LatinSquare.ext {n : ℕ} {L₁ L₂ : LatinSquare n}
    (h : L₁.entry = L₂.entry) : L₁ = L₂ := by
  cases L₁; cases L₂; cases h; rfl

/-- Equivalence between `LatinSquare n` and the subtype of bijective-row/column grids. -/
def latinSquareSubtypeEquiv (n : ℕ) :
    LatinSquare n ≃
      { f : Fin n → Fin n → Fin n //
        (∀ r, Function.Bijective (fun c => f r c)) ∧
        (∀ c, Function.Bijective (fun r => f r c)) } where
  toFun L := ⟨L.entry, L.row_bijective, L.col_bijective⟩
  invFun f := ⟨f.1, f.2.1, f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {n : ℕ} : DecidableEq (LatinSquare n) :=
  fun L₁ L₂ => decidable_of_iff (L₁.entry = L₂.entry)
    ⟨LatinSquare.ext, fun h => h ▸ rfl⟩

noncomputable instance {n : ℕ} : Fintype (LatinSquare n) := by
  classical
  exact Fintype.ofEquiv _ (latinSquareSubtypeEquiv n).symm

/-- Row `r` of a Latin square `L`, viewed as a permutation of `Fin n`. -/
noncomputable def rowPerm {n : ℕ} (L : LatinSquare n) (r : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun c => L.entry r c) (L.row_bijective r)

/-- Column `c` of a Latin square `L`, viewed as a permutation of `Fin n`. -/
noncomputable def colPerm {n : ℕ} (L : LatinSquare n) (c : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun r => L.entry r c) (L.col_bijective c)

/-- Symbol permutation `ζ_s` sending row `r` to the unique column `c` with `L(r, c) = s`. -/
noncomputable def symPerm {n : ℕ} (L : LatinSquare n) (s : Fin n) : Equiv.Perm (Fin n) where
  toFun r := (rowPerm L r).symm s
  invFun c := (colPerm L c).symm s
  left_inv r := by
    apply (colPerm L ((rowPerm L r).symm s)).injective
    rw [Equiv.apply_symm_apply]
    exact (Equiv.apply_symm_apply (rowPerm L r) s).symm
  right_inv c := by
    apply (rowPerm L ((colPerm L c).symm s)).injective
    rw [Equiv.apply_symm_apply]
    exact (Equiv.apply_symm_apply (colPerm L c) s).symm

/-- Product of the signs of all rows of `L`. -/
noncomputable def rowSign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  ∏ r : Fin n, Equiv.Perm.sign (rowPerm L r)

/-- Product of the signs of all columns of `L`. -/
noncomputable def colSign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  ∏ c : Fin n, Equiv.Perm.sign (colPerm L c)

/-- Product of the signs of all symbol permutations of `L`. -/
noncomputable def symSign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  ∏ s : Fin n, Equiv.Perm.sign (symPerm L s)

/-- The sign `ε(L) = sgn_row(L) * sgn_col(L)` of a Latin square `L`. -/
noncomputable def squareSign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  rowSign L * colSign L

/-- Number `L^e_n` of even Latin squares of order `n`. -/
noncomputable def evenCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun L : LatinSquare n => squareSign L = 1).card

/-- Number `L^o_n` of odd Latin squares of order `n`. -/
noncomputable def oddCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun L : LatinSquare n => squareSign L = -1).card

/-- The signed count `Δ_n = L^e_n - L^o_n`. -/
noncomputable def delta (n : ℕ) : ℤ :=
  (evenCount n : ℤ) - (oddCount n : ℤ)

/-- A Latin square is reduced if its first row and first column are `0, 1, ..., n - 1`. -/
def IsReduced {n : ℕ} (L : LatinSquare n) : Prop :=
  ∀ h : 0 < n, (∀ c : Fin n, L.entry ⟨0, h⟩ c = c) ∧ (∀ r : Fin n, L.entry r ⟨0, h⟩ = r)

/-- The signed count `D_n` of reduced Latin squares of order `n`. -/
noncomputable def reducedDelta (n : ℕ) : ℤ := by
  classical
  exact ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => IsReduced L), (squareSign L : ℤ)

/-- The isotopy group `S_n^3`, acting on rows, columns, and symbols. -/
abbrev Isotopy (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

/-- Action of an isotopy `σ = (σ₁, σ₂, σ₃)` on a Latin square:
`(σ L)(σ₁ r, σ₂ c) = σ₃ (L(r, c))`. -/
def isotopyAct {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) : LatinSquare n where
  entry r c := σ.2.2 (L.entry (σ.1.symm r) (σ.2.1.symm c))
  row_bijective r :=
    σ.2.2.bijective.comp ((L.row_bijective (σ.1.symm r)).comp σ.2.1.symm.bijective)
  col_bijective c :=
    σ.2.2.bijective.comp ((L.col_bijective (σ.2.1.symm c)).comp σ.1.symm.bijective)

instance {n : ℕ} : MulAction (Isotopy n) (LatinSquare n) where
  smul := isotopyAct
  one_smul L := by
    ext r c
    rfl
  mul_smul σ τ L := by
    ext r c
    rfl

/-- Transpose of a Latin square (exchanging rows and columns). -/
def transposeSquare {n : ℕ} (L : LatinSquare n) : LatinSquare n where
  entry r c := L.entry c r
  row_bijective r := L.col_bijective r
  col_bijective c := L.row_bijective c

/-- The `q`-adic valuation `v_q(x)` of an integer `x`, with the convention `v_q(0) = ∞`. -/
noncomputable def qVal (q : ℕ) (x : ℤ) : ℕ∞ :=
  if x = 0 then ⊤ else (padicValInt q x : ℕ∞)

/-- The natural modulus `M_q(n) = q^(v_q(n!) + v_q(n))` of `D_n` at a prime `q`. -/
noncomputable def naturalModulus (q n : ℕ) : ℕ :=
  q ^ (padicValNat q n.factorial + padicValNat q n)

/-- The Stones–Wanless obstruction integer `c_n = (n!)^3 / gcd(|Δ_n|, (n!)^3)`. -/
noncomputable def cVal (n : ℕ) : ℕ :=
  n.factorial ^ 3 / Nat.gcd (delta n).natAbs (n.factorial ^ 3)

/-- The minimal exponent `f_q(n, N)` of `q` in `m₁! ⋯ m_N!` over all positive integer
compositions `m₁ + ⋯ + m_N = n`. -/
noncomputable def fVal (q n N : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ m : Fin N → ℕ, (∀ i, 0 < m i) ∧ (∑ i, m i = n) ∧
    k = padicValNat q (∏ i, (m i).factorial) }

end AlonTarsi

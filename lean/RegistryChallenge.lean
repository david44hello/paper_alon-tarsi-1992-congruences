-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
set_option backward.proofsInPublic true

/-!
# The Alon–Tarsi (1992) conjecture: congruences modulo divisors of `(n!)^3`

Standalone Mathlib-only definitions and statements of Theorems A, B, and C for the signed
count `Δ_n = L^e_n - L^o_n` of even and odd Latin squares of order `n`, the reduced signed
count `D_n`, the natural modulus `M_q(n) = q^(v_q(n!) + v_q(n))`, the obstruction integer
`c_n = (n!)^3 / gcd(|Δ_n|, (n!)^3)`, and the minimal factorial-valuation function `f_q(n, N)`.
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

/-- Product of the signs of all rows of `L`. -/
noncomputable def rowSign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  ∏ r : Fin n, Equiv.Perm.sign (rowPerm L r)

/-- Product of the signs of all columns of `L`. -/
noncomputable def colSign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  ∏ c : Fin n, Equiv.Perm.sign (colPerm L c)

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

namespace AlonTarsi.Paper

open AlonTarsi

/-- **Theorem A**: For every even `n ≥ 8`, `c_n = n - 1` if `n - 1` is prime and `c_n = 1`
otherwise; equivalently, `(n!)^3 ∣ Δ_n` when `n - 1` is composite, and
`(n!)^3 / (n - 1) ∣ Δ_n` while `(n!)^3 ∤ Δ_n` when `n - 1` is prime. -/
theorem thm_A (n : ℕ) (heven : Even n) (hn : 8 ≤ n) :
    cVal n = (if (n - 1).Prime then n - 1 else 1) ∧
    (¬ (n - 1).Prime → ((n.factorial : ℤ) ^ 3 ∣ delta n)) ∧
    ((n - 1).Prime →
      (((n.factorial ^ 3 / (n - 1) : ℕ) : ℤ) ∣ delta n) ∧
      ¬ ((n.factorial : ℤ) ^ 3 ∣ delta n)) := by sorry

/-- **Theorem B**: For every even `n ≥ 8` and every prime `q ≤ n - 2`, the natural modulus
`M_q(n) = q^(v_q(n!) + v_q(n))` divides `D_n`. -/
theorem thm_B (n q : ℕ) (heven : Even n) (hn : 8 ≤ n) (hq : q.Prime) (hqle : q ≤ n - 2) :
    (naturalModulus q n : ℤ) ∣ reducedDelta n := by sorry

/-- **Theorem C**: For every even `n` and every prime `q`,
`v_q(L^e_n - L^o_n) ≥ v_q((n-1)!) + ∑_{N=1}^{n-1} f_q(n, N)`, which is at least
`v_q(n! (n-1)!) + a(a-1)/2` for `a = ⌊n/q⌋`, and at least `v_2((n-1)!) + n^2/4` for `q = 2`. -/
theorem thm_C (n q : ℕ) (heven : Even n) (hq : q.Prime) :
    qVal q (delta n) ≥
      (padicValNat q (n - 1).factorial : ℕ∞) +
        (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞) ∧
    (padicValNat q (n - 1).factorial : ℕ∞) +
        (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞) ≥
      (padicValNat q (n.factorial * (n - 1).factorial) : ℕ∞) +
        (((n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) ∧
    (q = 2 →
      (padicValNat 2 (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal 2 n N : ℕ∞) ≥
        (padicValNat 2 (n - 1).factorial : ℕ∞) + ((n ^ 2 / 4 : ℕ) : ℕ∞)) := by sorry

end AlonTarsi.Paper

module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Proofs.TwoQRankTwo

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Section 6 (Lemmas 6.7–6.8, Proposition 6.9): Rank-One Shapes, Strata, and Reduction

This file proves:
- Inversion-count sign formula on `Fin n`, `sumBijectionSign` shuffle identities, and
  `thetaSign` properties (exported for `TwoQTraces.lean`);
- **Lemma 6.7** (`lem_6_7_factor`): sign factorization for squares fixed by `ℓ_0, ℓ_B, ℓ_C`;
- **Lemma 6.8** (`lem_6_8_strata`): `S(⟨ℓ_0⟩)`, mixed-stratum stabilizer `⟨ℓ⟩`, and
  homogeneous-stratum contributions to `S(⟨ℓ_B⟩)` and `S(⟨ℓ_C⟩)`;
- **Proposition 6.9** (`prop_6_9_rankone`): Babbage's congruence, rank-1 shape assembly,
  normalization `Δ_{2q} = (2q)!(2q-1)! D_{2q}`, `q^2 ∣ D_{2q}`, and
  `2 (D_{2q} / q^2) ≡ 2 N_B - N_C (mod q)`.
-/

namespace AlonTarsi.Proofs

open scoped BigOperators
open AlonTarsi

section InversionSign

/-! ### Inversion Count and Permutation Sign on `Fin n` -/

/-- Number of inversions of a permutation `π : Equiv.Perm (Fin n)`. -/
def invCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1).card

/-- Parity of inversion count of a permutation on `Fin n`. -/
def invSign {n : ℕ} (π : Equiv.Perm (Fin n)) : ℤˣ :=
  (-1 : ℤˣ) ^ invCount π

private lemma invCount_one (n : ℕ) : invCount (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold invCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ⟨i, j⟩ _ ⟨h1, h2⟩
  exact absurd h1 (not_lt_of_gt h2)

/-- Left-multiplying `π` by an adjacent swap `(k, k+1)` flips `invSign`. -/
private lemma invSign_swap_succ_mul {n : ℕ} (k : ℕ) (hk : k + 1 < n) (π : Equiv.Perm (Fin n)) :
    invSign (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩ * π) = -invSign π := by
  let a : Fin n := ⟨k, by omega⟩
  let b : Fin n := ⟨k + 1, hk⟩
  let τ : Equiv.Perm (Fin n) := Equiv.swap a b
  have hab : a < b := Nat.lt_succ_self k
  let i₀ := π.symm a
  let j₀ := π.symm b
  have hij : i₀ ≠ j₀ := fun h => ne_of_lt hab (by simpa [i₀, j₀] using congrArg π h)
  -- For any pair `(i, j)` with `i < j` and `(i, j) ∉ {(i₀, j₀), (j₀, i₀)}`,
  -- `(τ * π) j < (τ * π) i ↔ π j < π i`.
  have hother : ∀ p : Fin n × Fin n, p.1 < p.2 → p ≠ (i₀, j₀) → p ≠ (j₀, i₀) →
      ((τ * π) p.2 < (τ * π) p.1 ↔ π p.2 < π p.1) := by
    rintro ⟨i, j⟩ hlt hne1 hne2
    simp only [Equiv.Perm.mul_apply, τ]
    have hcases : ∀ x y : Fin n, ¬(x = a ∧ y = b) → ¬(x = b ∧ y = a) →
        (Equiv.swap a b x < Equiv.swap a b y ↔ x < y) := by
      intro x y h1 h2
      by_cases hxa : x = a
      · subst hxa
        have hyb : y ≠ b := fun h => h1 ⟨rfl, h⟩
        by_cases hya : y = a
        · subst hya; simp
        · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hya hyb]
          change (k + 1 < y.val) ↔ (k < y.val)
          have : y.val ≠ k + 1 := fun h => hyb (Fin.ext h)
          omega
      · by_cases hxb : x = b
        · subst hxb
          have hya : y ≠ a := fun h => h2 ⟨rfl, h⟩
          by_cases hyb : y = b
          · subst hyb; simp
          · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hya hyb]
            change (k < y.val) ↔ (k + 1 < y.val)
            have : y.val ≠ k := fun h => hya (Fin.ext h)
            have : y.val ≠ k + 1 := fun h => hyb (Fin.ext h)
            omega
        · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
          by_cases hya : y = a
          · subst hya; rw [Equiv.swap_apply_left]
            change (x.val < k + 1) ↔ (x.val < k)
            have : x.val ≠ k := fun h => hxa (Fin.ext h)
            omega
          · by_cases hyb : y = b
            · subst hyb; rw [Equiv.swap_apply_right]
              change (x.val < k) ↔ (x.val < k + 1)
              have : x.val ≠ k := fun h => hxa (Fin.ext h)
              have : x.val ≠ k + 1 := fun h => hxb (Fin.ext h)
              omega
            · rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
    refine hcases (π j) (π i) ?_ ?_
    · rintro ⟨h1, h2⟩; apply hne2; ext
      · exact congrArg Fin.val ((Equiv.symm_apply_eq π).mpr h2.symm).symm
      · exact congrArg Fin.val ((Equiv.symm_apply_eq π).mpr h1.symm).symm
    · rintro ⟨h1, h2⟩; apply hne1; ext
      · exact congrArg Fin.val ((Equiv.symm_apply_eq π).mpr h2.symm).symm
      · exact congrArg Fin.val ((Equiv.symm_apply_eq π).mpr h1.symm).symm
  let S₁ := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ (τ * π) p.2 < (τ * π) p.1
  let S₀ := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ π p.2 < π p.1
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- `i₀ < j₀`: `(i₀, j₀)` is in `S₁` and NOT in `S₀`
    have hnot0 : (i₀, j₀) ∉ S₀ := by
      simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, i₀, j₀, Equiv.apply_symm_apply]
      exact fun ⟨_, h⟩ => not_lt_of_gt hab h
    have heq : S₁ = insert (i₀, j₀) S₀ := by
      ext p
      simp only [S₁, S₀, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hp1 : p = (i₀, j₀)
      · subst hp1
        simp only [Equiv.Perm.mul_apply, τ, i₀, j₀, Equiv.apply_symm_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, true_or, iff_true]
        exact ⟨hlt, hab⟩
      · constructor
        · intro ⟨h1, h2⟩
          have hp2' : p ≠ (j₀, i₀) := fun h => by rw [h] at h1; exact not_lt_of_gt hlt h1
          exact Or.inr ⟨h1, (hother p h1 hp1 hp2').mp h2⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact absurd rfl hp1
          · have hp2' : p ≠ (j₀, i₀) := fun h => by rw [h] at h1; exact not_lt_of_gt hlt h1
            exact ⟨h1, (hother p h1 hp1 hp2').mpr h2⟩
    have hcard : invCount (τ * π) = invCount π + 1 := by
      change S₁.card = S₀.card + 1
      rw [heq, Finset.card_insert_of_notMem hnot0]
    unfold invSign
    rw [hcard, pow_succ]
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ invCount π) with h | h <;> rw [h] <;> decide
  · -- `j₀ < i₀`: `(j₀, i₀)` is in `S₀` and NOT in `S₁`
    have hnot1 : (j₀, i₀) ∉ S₁ := by
      intro hmem
      dsimp only [S₁] at hmem
      rw [Finset.mem_filter] at hmem
      have h2 := hmem.2.2
      simp only [Equiv.Perm.mul_apply, τ, i₀, j₀, Equiv.apply_symm_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right] at h2
      exact not_lt_of_gt hab h2
    have heq : S₀ = insert (j₀, i₀) S₁ := by
      ext p
      simp only [S₁, S₀, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hp2 : p = (j₀, i₀)
      · subst hp2
        simp only [i₀, j₀, Equiv.apply_symm_apply, true_or, iff_true]
        exact ⟨hgt, hab⟩
      · constructor
        · intro ⟨h1, h2⟩
          have hp1' : p ≠ (i₀, j₀) := fun h => by rw [h] at h1; exact not_lt_of_gt hgt h1
          exact Or.inr ⟨h1, (hother p h1 hp1' hp2).mpr h2⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact absurd rfl hp2
          · have hp1' : p ≠ (i₀, j₀) := fun h => by rw [h] at h1; exact not_lt_of_gt hgt h1
            exact ⟨h1, (hother p h1 hp1' hp2).mp h2⟩
    have hcard : invCount π = invCount (τ * π) + 1 := by
      change S₀.card = S₁.card + 1
      rw [heq, Finset.card_insert_of_notMem hnot1]
    unfold invSign
    rw [hcard, pow_succ]
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ invCount (τ * π)) with h | h <;> rw [h] <;> decide

/-- Left-multiplying `π` by ANY transposition `(a, b)` (`a ≠ b`) flips `invSign`. -/
private lemma invSign_swap_mul {n : ℕ} {a b : Fin n} (hab : a ≠ b) (π : Equiv.Perm (Fin n)) :
    invSign (Equiv.swap a b * π) = -invSign π := by
  suffices hlt : ∀ d : ℕ, ∀ (x y : Fin n) (σ : Equiv.Perm (Fin n)),
      x.val + d + 1 = y.val → invSign (Equiv.swap x y * σ) = -invSign σ by
    rcases lt_or_gt_of_ne hab with h | h
    · exact hlt (b.val - a.val - 1) a b π (by omega)
    · rw [Equiv.swap_comm]
      exact hlt (a.val - b.val - 1) b a π (by omega)
  intro d
  induction d with
  | zero =>
    intro x y σ hxy
    have hxy' : x.val + 1 = y.val := by simpa using hxy
    have hxlt : x.val + 1 < n := by have := y.isLt; omega
    have hy : y = ⟨x.val + 1, hxlt⟩ := Fin.ext hxy'.symm
    rw [hy]
    exact invSign_swap_succ_mul x.val hxlt σ
  | succ d ih =>
    intro x y σ hxy
    have hzlt : y.val - 1 < n := by have := y.isLt; omega
    let z : Fin n := ⟨y.val - 1, hzlt⟩
    have hzy_lt : z.val + 1 < n := by have := y.isLt; dsimp [z]; omega
    have hy : y = ⟨z.val + 1, hzy_lt⟩ := Fin.ext (by dsimp [z]; omega)
    have hxz : x.val + d + 1 = z.val := by dsimp [z]; omega
    have hxnez : x ≠ z := fun h => by have := congrArg Fin.val h; omega
    have hxy' : x ≠ y := fun h => by have := congrArg Fin.val h; omega
    have hzy : z ≠ y := fun h => by have := congrArg Fin.val h; dsimp [z] at this; omega
    have hconj : Equiv.swap x y = Equiv.swap z y * Equiv.swap x z * Equiv.swap z y := by
      ext t
      simp only [Equiv.Perm.mul_apply]
      by_cases htx : t = x
      · rw [htx, Equiv.swap_apply_of_ne_of_ne hxnez hxy', Equiv.swap_apply_left,
          Equiv.swap_apply_left, Equiv.swap_apply_left]
      · by_cases hty : t = y
        · rw [hty, Equiv.swap_apply_right, Equiv.swap_apply_right, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne hxnez hxy']
        · by_cases htz : t = z
          · rw [htz, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxy'.symm hzy.symm,
              Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxnez.symm hzy]
          · rw [Equiv.swap_apply_of_ne_of_ne htz hty, Equiv.swap_apply_of_ne_of_ne htx htz,
              Equiv.swap_apply_of_ne_of_ne htz hty, Equiv.swap_apply_of_ne_of_ne htx hty]
    rw [hconj, mul_assoc, mul_assoc, hy]
    rw [invSign_swap_succ_mul z.val hzy_lt, ← hy, ih x z _ hxz, hy,
      invSign_swap_succ_mul z.val hzy_lt]
    simp

/-- Permutation sign on `Fin n` equals `(-1)^(invCount π)`. -/
theorem sign_eq_invSign {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = invSign π := by
  induction π using Equiv.Perm.swap_induction_on with
  | one =>
    rw [map_one]; unfold invSign; rw [invCount_one, pow_zero]
  | swap_mul σ x y hxy ih =>
    rw [map_mul, Equiv.Perm.sign_swap hxy, ih, invSign_swap_mul hxy]
    simp

/-! ### Shuffle Signs and `sumBijectionSign` Splitting -/

/-- `invCount` of the canonical union map `A ⊕ Aᶜ ≃ ZMod q` equals `∑ x ∈ A, x.val - C(|A|, 2)`. -/
private lemma sumBijectionSign_union_eq_thetaSign {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    let ι : (A ⊕ (Aᶜ : Finset (ZMod q))) ≃ ZMod q :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun x => if hx : x ∈ A then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩
        left_inv := fun s => by
          rcases s with ⟨x, hx⟩ | ⟨x, hx⟩
          · simp [hx]
          · simp [Finset.mem_compl.mp hx]
        right_inv := fun x => by by_cases hx : x ∈ A <;> simp [hx] }
    sumBijectionSign ι = thetaSign A := by
  intro ι
  unfold sumBijectionSign thetaSign
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  letI : LinearOrder A := Subtype.instLinearOrder _
  letI : LinearOrder (Aᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
  have hcard : Fintype.card (A ⊕ₗ (Aᶜ : Finset (ZMod q))) = q := by
    have h1 : Fintype.card (A ⊕ₗ (Aᶜ : Finset (ZMod q))) =
        Fintype.card (A ⊕ (Aᶜ : Finset (ZMod q))) := Fintype.card_congr ofLex
    rw [h1]; simpa [ZMod.card] using Fintype.card_congr ι
  let eDom : Fin q ≃o (A ⊕ₗ (Aᶜ : Finset (ZMod q))) :=
    Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ (Aᶜ : Finset (ZMod q))) hcard
  let eCod : Fin q ≃o ZMod q := Fintype.orderIsoFinOfCardEq (α := ZMod q) (ZMod.card q)
  let π : Equiv.Perm (Fin q) := eDom.toEquiv.trans (ofLex.trans (ι.trans eCod.toEquiv.symm))
  change Equiv.Perm.sign π = _
  rw [sign_eq_invSign]
  unfold invSign invCount
  -- Identify `eCod.symm x = ⟨x.val, x.val_lt⟩`
  have heCod : ∀ i : Fin q, (eCod i).val = i.val := by
    let f : Fin q ≃o ZMod q :=
      { toFun := fun i => (i.val : ZMod q)
        invFun := fun x => ⟨x.val, x.val_lt⟩
        left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
        right_inv := fun x => ZMod.natCast_zmod_val x
        map_rel_iff' := fun {i j} => by
          change (i.val : ZMod q).val ≤ (j.val : ZMod q).val ↔ i.val ≤ j.val
          rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] }
    have huniq : eCod = f := Subsingleton.elim _ _
    intro i; rw [huniq]; exact ZMod.val_natCast_of_lt i.isLt
  have hπ_val : ∀ i : Fin q, (π i).val = (ι (ofLex (eDom i))).val := by
    intro i
    have := heCod (π i)
    simpa [π] using this.symm
  -- Bijection between inversions of `π` and `{ (x, y) ∈ A ×ˢ Aᶜ | y.val < x.val }`
  have hinv_eq :
      (Finset.univ.filter fun p : Fin q × Fin q => p.1 < p.2 ∧ π p.2 < π p.1).card =
      ((A ×ˢ Aᶜ).filter fun p : ZMod q × ZMod q => p.2.val < p.1.val).card := by
    refine Finset.card_bij (fun p _ => (ι (ofLex (eDom p.1)), ι (ofLex (eDom p.2)))) ?_ ?_ ?_
    · rintro ⟨i, j⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hij_lex : eDom i < eDom j := eDom.strictMono hp.1
      have hval_lt : (ι (ofLex (eDom j))).val < (ι (ofLex (eDom i))).val := by
        rw [← hπ_val j, ← hπ_val i]; exact hp.2
      -- Both cannot be in `A` (else `eDom i < eDom j` implies `val_i < val_j`),
      -- and both cannot be in `Aᶜ` (same), and `i` cannot be in `Aᶜ` with `j` in `A`.
      rcases hi : ofLex (eDom i) with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
        rcases hj : ofLex (eDom j) with ⟨y, hy⟩ | ⟨y, hy⟩
      · exfalso
        have h1 : toLex (Sum.inl (⟨x, hx⟩ : A) : A ⊕ (Aᶜ : Finset (ZMod q))) <
            toLex (Sum.inl (⟨y, hy⟩ : A) : A ⊕ (Aᶜ : Finset (ZMod q))) := by
          rw [← hi, ← hj]; exact hij_lex
        have hxy : (⟨x, hx⟩ : A) < ⟨y, hy⟩ := (Sum.Lex.inl_lt_inl_iff).mp h1
        have hxy_val : x.val < y.val := hxy
        rw [hi, hj] at hval_lt
        simp only [ι, Equiv.coe_fn_mk, Sum.elim_inl] at hval_lt
        omega
      · rw [hi, hj] at hval_lt
        simp only [Finset.mem_filter, Finset.mem_product, ι, Equiv.coe_fn_mk,
          Sum.elim_inl, Sum.elim_inr] at hval_lt ⊢
        exact ⟨⟨hx, hy⟩, hval_lt⟩
      · exfalso
        have h1 : toLex (Sum.inr (⟨x, hx⟩ : (Aᶜ : Finset (ZMod q))) : A ⊕ (Aᶜ : Finset (ZMod q))) <
            toLex (Sum.inl (⟨y, hy⟩ : A) : A ⊕ (Aᶜ : Finset (ZMod q))) := by
          rw [← hi, ← hj]; exact hij_lex
        exact (not_lt_of_gt (Sum.Lex.inl_lt_inr _ _)) h1
      · exfalso
        have h1 : toLex (Sum.inr (⟨x, hx⟩ : (Aᶜ : Finset (ZMod q))) : A ⊕ (Aᶜ : Finset (ZMod q))) <
            toLex (Sum.inr (⟨y, hy⟩ : (Aᶜ : Finset (ZMod q))) : A ⊕ (Aᶜ : Finset (ZMod q))) := by
          rw [← hi, ← hj]; exact hij_lex
        have hxy : (⟨x, hx⟩ : (Aᶜ : Finset (ZMod q))) < ⟨y, hy⟩ := (Sum.Lex.inr_lt_inr_iff).mp h1
        have hxy_val : x.val < y.val := hxy
        rw [hi, hj] at hval_lt
        simp only [ι, Equiv.coe_fn_mk, Sum.elim_inr] at hval_lt
        omega
    · rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hEq
      have h1 := ι.injective (congrArg Prod.fst hEq)
      have h2 := ι.injective (congrArg Prod.snd hEq)
      exact Prod.ext (eDom.injective (ofLex.injective h1)) (eDom.injective (ofLex.injective h2))
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      let i := eDom.symm (toLex (Sum.inl ⟨x, hp.1.1⟩))
      let j := eDom.symm (toLex (Sum.inr ⟨y, hp.1.2⟩))
      refine ⟨(i, j), ?_, by simp [i, j, ι]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [← eDom.lt_iff_lt]
        simp only [i, j, OrderIso.apply_symm_apply]
        exact Sum.Lex.inl_lt_inr _ _
      · change (π j).val < (π i).val
        rw [hπ_val j, hπ_val i]
        simpa [i, j, ι] using hp.2
  -- Compute `((A ×ˢ Aᶜ).filter (y.val < x.val)).card = (∑ x ∈ A, x.val) - A.card.choose 2`
  have hsum_id :
      ((A ×ˢ Aᶜ).filter fun p : ZMod q × ZMod q => p.2.val < p.1.val).card +
        A.card.choose 2 = ∑ x ∈ A, x.val := by
    have hsplit : ∀ x ∈ A,
        (Aᶜ.filter fun y : ZMod q => y.val < x.val).card +
        (A.filter fun y : ZMod q => y.val < x.val).card = x.val := by
      intro x _
      have hdisj : Disjoint (Aᶜ.filter fun y : ZMod q => y.val < x.val)
          (A.filter fun y : ZMod q => y.val < x.val) :=
        Finset.disjoint_filter_filter disjoint_compl_left
      rw [← Finset.card_union_of_disjoint hdisj]
      have hunion : (Aᶜ.filter fun y : ZMod q => y.val < x.val) ∪
          (A.filter fun y : ZMod q => y.val < x.val) =
          Finset.univ.filter fun y : ZMod q => y.val < x.val := by
        ext y; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_univ,
          true_and]; tauto
      rw [hunion]
      have hbij : (Finset.univ.filter fun y : ZMod q => y.val < x.val).card =
          (Finset.range x.val).card := by
        refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
        · intro y hy; exact Finset.mem_range.mpr (Finset.mem_filter.mp hy).2
        · intro y₁ _ y₂ _ h; exact ZMod.val_injective q h
        · intro k hk
          have hk' : k < x.val := Finset.mem_range.mp hk
          refine ⟨(k : ZMod q), ?_, ZMod.val_natCast_of_lt (lt_trans hk' x.val_lt)⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            ZMod.val_natCast_of_lt (lt_trans hk' x.val_lt)]
          exact hk'
      rw [hbij, Finset.card_range]
    have h1 : ((A ×ˢ Aᶜ).filter fun p : ZMod q × ZMod q => p.2.val < p.1.val).card =
        ∑ x ∈ A, (Aᶜ.filter fun y : ZMod q => y.val < x.val).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product] at hp
        simp only [Finset.mem_sigma, Finset.mem_filter]
        exact ⟨hp.1.1, hp.1.2, hp.2⟩
      · rintro ⟨x₁, y₁⟩ _ ⟨x₂, y₂⟩ _ hEq
        cases hEq; rfl
      · rintro ⟨x, y⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_filter] at hp
        exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1, hp.2.1⟩, hp.2.2⟩, rfl⟩
    have h2 : A.card.choose 2 = ∑ x ∈ A, (A.filter fun y : ZMod q => y.val < x.val).card := by
      let eA : Fin A.card ≃o A := A.orderIsoOfFin rfl
      have h3 : ∑ x ∈ A, (A.filter fun y : ZMod q => y.val < x.val).card =
          ∑ i : Fin A.card, i.val := by
        rw [← Finset.sum_attach A (fun x => (A.filter fun y : ZMod q => y.val < x.val).card)]
        change ∑ x : A, (A.filter fun y : ZMod q => y.val < x.1.val).card = _
        rw [← Equiv.sum_comp eA.toEquiv]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hbij : (A.filter fun y : ZMod q => y.val < (eA i).1.val).card =
            (Finset.univ.filter fun j : Fin A.card => j < i).card := by
          symm
          refine Finset.card_bij (fun j _ => (eA j).1) ?_ ?_ ?_
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            exact ⟨(eA j).2, eA.strictMono hj⟩
          · intro j₁ _ j₂ _ hEq; exact eA.injective (Subtype.ext hEq)
          · intro y hy
            simp only [Finset.mem_filter] at hy
            refine ⟨eA.symm ⟨y, hy.1⟩, ?_, by simp⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← eA.lt_iff_lt, OrderIso.apply_symm_apply]
            exact hy.2
        change (A.filter fun y : ZMod q => y.val < (eA i).1.val).card = i.val
        rw [hbij]
        have h4 : (Finset.univ.filter fun j : Fin A.card => j < i).card = i.val := by
          have : (Finset.univ.filter fun j : Fin A.card => j < i).card =
              (Finset.range i.val).card := by
            refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
            · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
            · intro j₁ _ j₂ _ h; exact Fin.ext h
            · intro k hk
              have hk' := Finset.mem_range.mp hk
              exact ⟨⟨k, lt_trans hk' i.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, rfl⟩
          rw [this, Finset.card_range]
        exact h4
      rw [h3]
      have hfin : ∀ m : ℕ, ∑ i : Fin m, i.val = m.choose 2 := fun m => by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.choose_succ_succ, Nat.choose_one_right,
            add_comm]
      exact (hfin A.card).symm
    rw [h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplit
  rw [hinv_eq]
  congr 1
  omega

/-- For odd `q`, `thetaSign Iᶜ = thetaSign I`. -/
theorem thetaSign_compl {q : ℕ} [NeZero q] (hodd : Odd q) (I : Finset (ZMod q)) :
    thetaSign Iᶜ = thetaSign I := by
  unfold thetaSign
  have hfin_sum : ∀ m : ℕ, ∑ i : Fin m, i.val = m.choose 2 := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.choose_succ_succ, Nat.choose_one_right,
        add_comm]
  have hsum_all : ∑ x : ZMod q, x.val = q.choose 2 := by
    have hbij : ∑ x : ZMod q, x.val = ∑ i : Fin q, i.val := by
      refine Finset.sum_bij (fun x _ => ⟨x.val, x.val_lt⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun x₁ _ x₂ _ h => ZMod.val_injective q (congrArg Fin.val h))
        (fun i _ => ⟨(i.val : ZMod q), Finset.mem_univ _,
          Fin.ext (ZMod.val_natCast_of_lt i.isLt)⟩)
        (fun _ _ => rfl)
    rw [hbij, hfin_sum]
  have hle : ∀ A : Finset (ZMod q), A.card.choose 2 ≤ ∑ x ∈ A, x.val := by
    intro A
    letI : LinearOrder (ZMod q) := zmodLinearOrder q
    let eA : Fin A.card ≃o A := A.orderIsoOfFin rfl
    have hmono : ∀ (k : ℕ) (hk : k < A.card), k ≤ (eA ⟨k, hk⟩).1.val := fun k => by
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hlt : (eA ⟨k, Nat.lt_of_succ_lt hk⟩).1.val < (eA ⟨k + 1, hk⟩).1.val :=
          eA.strictMono (by show k < k + 1; omega)
        have hprev := ih (Nat.lt_of_succ_lt hk)
        omega
    calc A.card.choose 2 = ∑ i : Fin A.card, i.val := (hfin_sum A.card).symm
      _ ≤ ∑ i : Fin A.card, (eA i).1.val := Finset.sum_le_sum fun i _ => hmono i.val i.isLt
      _ = ∑ x ∈ A, x.val := by
          rw [← Finset.sum_attach A (fun x => x.val)]
          change ∑ i : Fin A.card, (eA i).1.val = ∑ x : A, x.1.val
          exact Equiv.sum_comp eA.toEquiv (fun x => x.1.val)
  have htot := Finset.sum_add_sum_compl I (fun x : ZMod q => x.val)
  rw [hsum_all] at htot
  have hcard_c : Iᶜ.card = q - I.card := by simp [Finset.card_compl, ZMod.card]
  have hm_le : I.card ≤ q := by simpa [ZMod.card] using I.card_le_univ
  have hchoose : I.card.choose 2 + (q - I.card).choose 2 + I.card * (q - I.card) = q.choose 2 := by
    have h1 : ∀ a b : ℕ, a.choose 2 + b.choose 2 + a * b = (a + b).choose 2 := fun a b => by
      have h2x : ∀ n, 2 * n.choose 2 = n * (n - 1) := fun n => by
        rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
      cases a with
      | zero => simp
      | succ a =>
        cases b with
        | zero => simp
        | succ b =>
          have h2' : 2 * (a + 1).choose 2 = (a + 1) * a := by
            simpa [Nat.add_sub_cancel] using h2x (a + 1)
          have h3' : 2 * (b + 1).choose 2 = (b + 1) * b := by
            simpa [Nat.add_sub_cancel] using h2x (b + 1)
          have h4' : 2 * (a + 1 + (b + 1)).choose 2 = (a + 1 + (b + 1)) * (a + 1 + b) := by
            simpa [Nat.add_sub_cancel] using h2x (a + 1 + (b + 1))
          have hmul : 2 * ((a + 1).choose 2 + (b + 1).choose 2 + (a + 1) * (b + 1)) =
              2 * (a + 1 + (b + 1)).choose 2 := by
            calc 2 * ((a + 1).choose 2 + (b + 1).choose 2 + (a + 1) * (b + 1))
                = 2 * (a + 1).choose 2 + 2 * (b + 1).choose 2 + 2 * ((a + 1) * (b + 1)) := by ring
              _ = (a + 1) * a + (b + 1) * b + 2 * ((a + 1) * (b + 1)) := by rw [h2', h3']
              _ = (a + 1 + (b + 1)) * (a + 1 + b) := by ring
              _ = 2 * (a + 1 + (b + 1)).choose 2 := h4'.symm
          omega
    have := h1 I.card (q - I.card)
    rwa [Nat.add_sub_of_le hm_le] at this
  have hpar : Even (I.card * (q - I.card)) := by
    rcases Nat.even_or_odd I.card with he | ho
    · exact he.mul_right _
    · rcases hodd with ⟨k, hk⟩
      rcases ho with ⟨r, hr⟩
      refine ⟨I.card * (k - r), ?_⟩
      have : q - I.card = 2 * (k - r) := by omega
      rw [this]; ring
  have hsum_diff :
      ((∑ x ∈ I, x.val) - I.card.choose 2) + ((∑ x ∈ Iᶜ, x.val) - Iᶜ.card.choose 2) =
        I.card * (q - I.card) := by
    have hle1 := hle I
    have hle2 := hle Iᶜ
    rw [hcard_c] at hle2 ⊢
    omega
  -- Two natural numbers with even sum give the same power of `-1`
  have hpow : ∀ a b : ℕ, Even (a + b) → (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b := fun a b ⟨t, ht⟩ => by
    have hmul : (-1 : ℤˣ) ^ a * (-1 : ℤˣ) ^ b = 1 := by
      rw [← pow_add, ht, ← two_mul, pow_mul]; simp
    have hsq : (-1 : ℤˣ) ^ b * (-1 : ℤˣ) ^ b = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ a * ((-1 : ℤˣ) ^ b * (-1 : ℤˣ) ^ b) := by rw [hsq, mul_one]
      _ = ((-1 : ℤˣ) ^ a * (-1 : ℤˣ) ^ b) * (-1 : ℤˣ) ^ b := by rw [mul_assoc]
      _ = (-1 : ℤˣ) ^ b := by rw [hmul, one_mul]
  exact (hpow _ _ (by rw [hsum_diff]; exact hpar)).symm

/-- Helper order isomorphism `Fin q ≃o (α ⊕ₗ β)` built from order isomorphisms on `α` and `β`. -/
private def finSumOrderIso {α β : Type*} [LinearOrder α] [LinearOrder β] {m n q : ℕ}
    (eα : Fin m ≃o α) (eβ : Fin n ≃o β) (h : m + n = q) : Fin q ≃o (α ⊕ₗ β) :=
  let eSp : (Fin m ⊕ Fin n) ≃ Fin q := finSumFinEquiv.trans (finCongr h)
  { toEquiv := eSp.symm.trans ((Equiv.sumCongr eα.toEquiv eβ.toEquiv).trans toLex)
    map_rel_iff' := by
      intro u v
      obtain ⟨su, rfl⟩ := eSp.surjective u
      obtain ⟨sv, rfl⟩ := eSp.surjective v
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rcases su with x | x <;> rcases sv with y | y
      · simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.Lex.inl_le_inl_iff,
          OrderIso.coe_toEquiv, OrderIso.le_iff_le, eSp, Equiv.trans_apply,
          finSumFinEquiv_apply_left, finCongr_apply, Fin.le_def, Fin.val_cast, Fin.val_castAdd]
      · have hle_lex : toLex (Sum.inl (eα x) : α ⊕ β) ≤ toLex (Sum.inr (eβ y) : α ⊕ β) :=
          le_of_lt (Sum.Lex.inl_lt_inr _ _)
        simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, OrderIso.coe_toEquiv,
          hle_lex, true_iff, eSp, Equiv.trans_apply, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right, finCongr_apply, Fin.le_def, Fin.val_cast,
          Fin.val_castAdd, Fin.val_natAdd]
        have := x.isLt; omega
      · have hnot_lex : ¬ toLex (Sum.inr (eβ x) : α ⊕ β) ≤ toLex (Sum.inl (eα y) : α ⊕ β) :=
          not_le_of_gt (Sum.Lex.inl_lt_inr _ _)
        simp only [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, OrderIso.coe_toEquiv,
          hnot_lex, false_iff, not_le, eSp, Equiv.trans_apply, finSumFinEquiv_apply_left,
          finSumFinEquiv_apply_right, finCongr_apply, Fin.lt_def, Fin.val_cast,
          Fin.val_castAdd, Fin.val_natAdd]
        have := y.isLt; omega
      · simp only [Equiv.sumCongr_apply, Sum.map_inr, Sum.Lex.inr_le_inr_iff,
          OrderIso.coe_toEquiv, OrderIso.le_iff_le, eSp, Equiv.trans_apply,
          finSumFinEquiv_apply_right, finCongr_apply, Fin.le_def, Fin.val_cast, Fin.val_natAdd]
        omega }

private lemma finSumOrderIso_apply_lt {α β : Type*} [LinearOrder α] [LinearOrder β] {m n q : ℕ}
    (eα : Fin m ≃o α) (eβ : Fin n ≃o β) (h : m + n = q) (i : Fin q) (hi : i.val < m) :
    ofLex (finSumOrderIso eα eβ h i) = Sum.inl (eα ⟨i.val, hi⟩) := by
  let eSp : (Fin m ⊕ Fin n) ≃ Fin q := finSumFinEquiv.trans (finCongr h)
  have heq : i = eSp (Sum.inl ⟨i.val, hi⟩) := Fin.ext (by simp [eSp])
  conv_lhs => rw [heq]
  change ofLex (toLex (Sum.map eα eβ (eSp.symm (eSp (Sum.inl ⟨i.val, hi⟩))))) = _
  rw [Equiv.symm_apply_apply]; rfl

private lemma finSumOrderIso_apply_ge {α β : Type*} [LinearOrder α] [LinearOrder β] {m n q : ℕ}
    (eα : Fin m ≃o α) (eβ : Fin n ≃o β) (h : m + n = q) (i : Fin q) (hi : ¬ i.val < m) :
    ofLex (finSumOrderIso eα eβ h i) = Sum.inr (eβ ⟨i.val - m, by have := i.isLt; omega⟩) := by
  let eSp : (Fin m ⊕ Fin n) ≃ Fin q := finSumFinEquiv.trans (finCongr h)
  have heq : i = eSp (Sum.inr ⟨i.val - m, by have := i.isLt; omega⟩) :=
    Fin.ext (by simp [eSp]; omega)
  conv_lhs => rw [heq]
  change ofLex (toLex (Sum.map eα eβ (eSp.symm (eSp (Sum.inr ⟨i.val - m, _⟩))))) = _
  rw [Equiv.symm_apply_apply]; rfl

/-- Disjoint-union sign rule: if `f : (A ⊕ B) ≃ ZMod q` maps `A` onto `Y` and `B` onto `Yᶜ`,
then `sumBijectionSign f = thetaSign Y * orderedSign (f|_A) * orderedSign (f|_B)`. -/
theorem sumBijectionSign_split {q : ℕ} [NeZero q] {A B Y : Finset (ZMod q)}
    (f : (A ⊕ B) ≃ ZMod q)
    (hAY : A.card = Y.card) (hBY : B.card = Yᶜ.card)
    (fA : A ≃ Y) (fB : B ≃ (Yᶜ : Finset (ZMod q)))
    (hfA : ∀ x : A, f (Sum.inl x) = (fA x).1)
    (hfB : ∀ x : B, f (Sum.inr x) = (fB x).1) :
    sumBijectionSign f = thetaSign Y * orderedSign hAY fA * orderedSign hBY fB := by
  let ι : (Y ⊕ (Yᶜ : Finset (ZMod q))) ≃ ZMod q :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun x => if hx : x ∈ Y then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩
      left_inv := fun s => by
        rcases s with ⟨x, hx⟩ | ⟨x, hx⟩
        · simp [hx]
        · simp [Finset.mem_compl.mp hx]
      right_inv := fun x => by by_cases hx : x ∈ Y <;> simp [hx] }
  have hfac : f = (Equiv.sumCongr fA fB).trans ι := by
    ext s; rcases s with x | x
    · exact hfA x
    · exact hfB x
  rw [← sumBijectionSign_union_eq_thetaSign Y]
  -- Transfer both sides to `Equiv.Perm (Fin q)` and split into `Fin |Y|` and `Fin |Yᶜ|`
  unfold sumBijectionSign orderedSign
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  letI : LinearOrder A := Subtype.instLinearOrder _
  letI : LinearOrder B := Subtype.instLinearOrder _
  letI : LinearOrder Y := Subtype.instLinearOrder _
  letI : LinearOrder (Yᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
  have hcardAB : Fintype.card (A ⊕ₗ B) = q := by
    have h1 : Fintype.card (A ⊕ₗ B) = Fintype.card (A ⊕ B) := Fintype.card_congr ofLex
    rw [h1]; simpa [ZMod.card] using Fintype.card_congr f
  have hcardY : Fintype.card (Y ⊕ₗ (Yᶜ : Finset (ZMod q))) = q := by
    have h1 : Fintype.card (Y ⊕ₗ (Yᶜ : Finset (ZMod q))) =
        Fintype.card (Y ⊕ (Yᶜ : Finset (ZMod q))) := Fintype.card_congr ofLex
    rw [h1]; simpa [ZMod.card] using Fintype.card_congr ι
  let eAB : Fin q ≃o (A ⊕ₗ B) := Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ B) hcardAB
  let eY : Fin q ≃o (Y ⊕ₗ (Yᶜ : Finset (ZMod q))) :=
    Fintype.orderIsoFinOfCardEq (α := Y ⊕ₗ (Yᶜ : Finset (ZMod q))) hcardY
  let eCod : Fin q ≃o ZMod q := Fintype.orderIsoFinOfCardEq (α := ZMod q) (ZMod.card q)
  let σ_ι : Equiv.Perm (Fin q) := eY.toEquiv.trans (ofLex.trans (ι.trans eCod.toEquiv.symm))
  let σ_mid : Equiv.Perm (Fin q) :=
    eAB.toEquiv.trans (ofLex.trans ((Equiv.sumCongr fA fB).trans (toLex.trans eY.toEquiv.symm)))
  have hcomp : eAB.toEquiv.trans (ofLex.trans (f.trans eCod.toEquiv.symm)) = σ_ι * σ_mid := by
    ext i
    simp [σ_ι, σ_mid, hfac]
  change Equiv.Perm.sign (eAB.toEquiv.trans (ofLex.trans (f.trans eCod.toEquiv.symm))) =
    Equiv.Perm.sign σ_ι * _ * _
  rw [hcomp, map_mul, mul_assoc]
  congr 1
  -- Show `Equiv.Perm.sign σ_mid = sign(pA) * sign(pB)` where `σ_mid` acts on `Fin |Y| ⊕ Fin |Yᶜ|`!
  let pA : Equiv.Perm (Fin A.card) :=
    (A.orderIsoOfFin rfl).toEquiv.trans (fA.trans (Y.orderIsoOfFin hAY.symm).toEquiv.symm)
  let pB : Equiv.Perm (Fin B.card) :=
    (B.orderIsoOfFin rfl).toEquiv.trans (fB.trans (Yᶜ.orderIsoOfFin hBY.symm).toEquiv.symm)
  have hsum_card : A.card + B.card = q := by
    have : A.card + B.card = Fintype.card (A ⊕ B) := by simp
    rw [this]; simpa [ZMod.card] using Fintype.card_congr f
  let eSplit : (Fin A.card ⊕ Fin B.card) ≃ Fin q :=
    finSumFinEquiv.trans (finCongr hsum_card)
  let fAB : Fin q ≃o (A ⊕ₗ B) := finSumOrderIso (A.orderIsoOfFin rfl) (B.orderIsoOfFin rfl) hsum_card
  let fY : Fin q ≃o (Y ⊕ₗ (Yᶜ : Finset (ZMod q))) :=
    finSumOrderIso (Y.orderIsoOfFin hAY.symm) (Yᶜ.orderIsoOfFin hBY.symm) hsum_card
  have hordAB : eAB = fAB := Subsingleton.elim _ _
  have hordY : eY = fY := Subsingleton.elim _ _
  have hconj : eSplit.permCongr (Equiv.sumCongr pA pB) = σ_mid := by
    ext i
    obtain ⟨s, rfl⟩ := eSplit.surjective i
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, σ_mid, hordAB, hordY]
    rcases s with x | x <;> simp [fAB, fY, finSumOrderIso, eSplit, pA, pB]
  rw [← hconj, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

/-- Master block-shuffle sign lemma: if `p : Equiv.Perm (Fin (2 * q))` maps `(0, d)` (`d ∈ A₀`)
and `(1, d)` (`d ∈ A₁`) into symbol block `0` via `f0 : A₀ ⊕ A₁ ≃ ZMod q`, and maps the
complements into symbol block `1` via `f1 : A₀ᶜ ⊕ A₁ᶜ ≃ ZMod q`, then
`sign p = thetaSign A₀ * thetaSign A₁ * (-1)^(|A₀ᶜ| * |A₁|) * sumBijectionSign f0 * sumBijectionSign f1`. -/
lemma sign_block_split {q : ℕ} [NeZero q] (hodd : Odd q)
    (A₀ A₁ : Finset (ZMod q)) (hcard : A₀.card + A₁.card = q)
    (f0 : (A₀ ⊕ A₁) ≃ ZMod q)
    (f1 : ((A₀ᶜ : Finset (ZMod q)) ⊕ (A₁ᶜ : Finset (ZMod q))) ≃ ZMod q)
    (p : Equiv.Perm (Fin (2 * q)))
    (hp00 : ∀ d (hd : d ∈ A₀), p (blockEquiv q (0, d)) = blockEquiv q (0, f0 (Sum.inl ⟨d, hd⟩)))
    (hp01 : ∀ d (hd : d ∈ A₀ᶜ), p (blockEquiv q (0, d)) = blockEquiv q (1, f1 (Sum.inl ⟨d, hd⟩)))
    (hp10 : ∀ d (hd : d ∈ A₁), p (blockEquiv q (1, d)) = blockEquiv q (0, f0 (Sum.inr ⟨d, hd⟩)))
    (hp11 : ∀ d (hd : d ∈ A₁ᶜ), p (blockEquiv q (1, d)) = blockEquiv q (1, f1 (Sum.inr ⟨d, hd⟩))) :
    Equiv.Perm.sign p =
      thetaSign A₀ * thetaSign A₁ * (-1 : ℤˣ) ^ (A₀ᶜ.card * A₁.card) *
        sumBijectionSign f0 * sumBijectionSign f1 := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  letI : LinearOrder A₀ := Subtype.instLinearOrder _
  letI : LinearOrder A₁ := Subtype.instLinearOrder _
  letI : LinearOrder (A₀ᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
  letI : LinearOrder (A₁ᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
  let eCod : Fin q ≃o ZMod q := Fintype.orderIsoFinOfCardEq (α := ZMod q) (ZMod.card q)
  have heCod : ∀ i : Fin q, (eCod i).val = i.val := by
    let f : Fin q ≃o ZMod q :=
      { toFun := fun i => (i.val : ZMod q)
        invFun := fun x => ⟨x.val, x.val_lt⟩
        left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
        right_inv := fun x => ZMod.natCast_zmod_val x
        map_rel_iff' := fun {i j} => by
          change (i.val : ZMod q).val ≤ (j.val : ZMod q).val ↔ i.val ≤ j.val
          rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] }
    have : eCod = f := Subsingleton.elim _ _
    intro i; rw [this]; exact ZMod.val_natCast_of_lt i.isLt
  -- Step 1: Within each block `b`, `π_b : Equiv.Perm (ZMod q)` maps `0..|A_b|-1` to `A_b` and
  -- `|A_b|..q-1` to `A_bᶜ` in increasing order; its sign is `thetaSign A_b`.
  let mkUnion (A : Finset (ZMod q)) : Equiv.Perm (ZMod q) :=
    let ι : (A ⊕ (Aᶜ : Finset (ZMod q))) ≃ ZMod q :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun x => if hx : x ∈ A then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩
        left_inv := fun s => by
          rcases s with ⟨x, hx⟩ | ⟨x, hx⟩
          · simp [hx]
          · simp [Finset.mem_compl.mp hx]
        right_inv := fun x => by by_cases hx : x ∈ A <;> simp [hx] }
    have hA : Fintype.card (A ⊕ₗ (Aᶜ : Finset (ZMod q))) = q := by
      rw [Fintype.card_congr ofLex]; simpa [ZMod.card] using Fintype.card_congr ι
    eCod.toEquiv.symm.trans ((Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ (Aᶜ : Finset (ZMod q))) hA).toEquiv.trans
      (ofLex.trans ι))
  have hsign_mkUnion : ∀ A : Finset (ZMod q), Equiv.Perm.sign (mkUnion A) = thetaSign A := fun A => by
    rw [← sumBijectionSign_union_eq_thetaSign A]
    unfold sumBijectionSign mkUnion
    letI : LinearOrder A := Subtype.instLinearOrder _
    letI : LinearOrder (Aᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
    let ι : (A ⊕ (Aᶜ : Finset (ZMod q))) ≃ ZMod q :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun x => if hx : x ∈ A then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩
        left_inv := fun s => by
          rcases s with ⟨x, hx⟩ | ⟨x, hx⟩
          · simp [hx]
          · simp [Finset.mem_compl.mp hx]
        right_inv := fun x => by by_cases hx : x ∈ A <;> simp [hx] }
    have hA : Fintype.card (A ⊕ₗ (Aᶜ : Finset (ZMod q))) = q := by
      rw [Fintype.card_congr ofLex]; simpa [ZMod.card] using Fintype.card_congr ι
    let σ : Equiv.Perm (Fin q) :=
      (Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ (Aᶜ : Finset (ZMod q))) hA).toEquiv.trans
        (ofLex.trans (ι.trans eCod.toEquiv.symm))
    have hconj : eCod.toEquiv.permCongr σ =
        eCod.toEquiv.symm.trans ((Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ (Aᶜ : Finset (ZMod q))) hA).toEquiv.trans
          (ofLex.trans ι)) := by
      ext x; simp [σ, Equiv.permCongr_apply]
    change Equiv.Perm.sign (eCod.toEquiv.symm.trans _) = Equiv.Perm.sign σ
    rw [← hconj, Equiv.Perm.sign_permCongr]
  -- Explicit formula for `mkUnion A` on `x : ZMod q`
  have hmkUnion_apply : ∀ (A : Finset (ZMod q)) (i : Fin q),
      mkUnion A (eCod i) =
        if h : i.val < A.card then (A.orderIsoOfFin rfl ⟨i.val, h⟩).1
        else (Aᶜ.orderIsoOfFin (k := q - A.card) (by simp [Finset.card_compl, ZMod.card])
          ⟨i.val - A.card, by
            have := i.isLt
            have hle : A.card ≤ q := by simpa [ZMod.card] using A.card_le_univ
            omega⟩).1 := by
    intro A i
    letI : LinearOrder A := Subtype.instLinearOrder _
    letI : LinearOrder (Aᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
    have hAc : Aᶜ.card = q - A.card := by simp [Finset.card_compl, ZMod.card]
    have hsumA : A.card + Aᶜ.card = q := by
      have : A.card ≤ q := by simpa [ZMod.card] using A.card_le_univ
      omega
    let fA : Fin q ≃o (A ⊕ₗ (Aᶜ : Finset (ZMod q))) :=
      finSumOrderIso (A.orderIsoOfFin rfl) (Aᶜ.orderIsoOfFin rfl) hsumA
    have hcardA : Fintype.card (A ⊕ₗ (Aᶜ : Finset (ZMod q))) = q := by
      rw [Fintype.card_congr ofLex, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, hsumA]
    have hord : Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ (Aᶜ : Finset (ZMod q))) hcardA = fA :=
      Subsingleton.elim _ _
    dsimp only [mkUnion]
    have heCod_id : eCod.toEquiv.symm (eCod i) = i := eCod.symm_apply_apply i
    simp only [Equiv.trans_apply, heCod_id, hord]
    split_ifs with hlt
    · change Sum.elim Subtype.val Subtype.val (ofLex (fA i)) = _
      rw [finSumOrderIso_apply_lt _ _ _ i hlt]; rfl
    · change Sum.elim Subtype.val Subtype.val (ofLex (fA i)) = _
      rw [finSumOrderIso_apply_ge _ _ _ i hlt]; dsimp only [Sum.elim]
      congr 1
  -- Step 2: `midSwap : Equiv.Perm (Fin (2 * q))` swaps `[|A₀|..q-1]` and `[q..q+|A₁|-1]`,
  -- sending `[0..|A₀|-1] ↦ [0..|A₀|-1]`, `[|A₀|..q-1] ↦ [q..q+|A₀ᶜ|-1]`,
  -- `[q..q+|A₁|-1] ↦ [|A₀|..q-1]`, `[q+|A₁|..2q-1] ↦ [q+|A₀ᶜ|..2q-1]`.
  set m0 := A₀.card
  set m1 := A₁.card
  have hm01 : m0 + m1 = q := hcard
  have hAc0 : A₀ᶜ.card = m1 := by simp [Finset.card_compl, ZMod.card, m0]; omega
  have hAc1 : A₁ᶜ.card = m0 := by simp [Finset.card_compl, ZMod.card, m1]; omega
  let midFun (i : Fin (2 * q)) : Fin (2 * q) :=
    if h1 : i.val < m0 then i
    else if h2 : i.val < q then ⟨i.val + m1, by omega⟩
    else if h3 : i.val < q + m1 then ⟨i.val - m1, by omega⟩
    else i
  have hmidFun_val : ∀ i : Fin (2 * q), (midFun i).val =
      if i.val < m0 then i.val
      else if i.val < q then i.val + m1
      else if i.val < q + m1 then i.val - m1
      else i.val := fun i => by
    dsimp only [midFun]; split_ifs <;> rfl
  have hmidFun_invol : ∀ i : Fin (2 * q), midFun (midFun i) = i := fun i => by
    apply Fin.ext
    rw [hmidFun_val, hmidFun_val]
    have hi := i.isLt
    by_cases h1 : i.val < m0
    · simp [h1]
    · by_cases h2 : i.val < q
      · have ha : ¬ (i.val + m1 < m0) := by omega
        have hb : ¬ (i.val + m1 < q) := by omega
        have hc : i.val + m1 < q + m1 := by omega
        simp only [h1, h2, ha, hb, hc, ↓reduceIte]; omega
      · by_cases h3 : i.val < q + m1
        · have ha : ¬ (i.val - m1 < m0) := by omega
          have hb : i.val - m1 < q := by omega
          simp only [h1, h2, h3, ha, hb, ↓reduceIte]; omega
        · simp [h1, h2, h3]
  let midSwap : Equiv.Perm (Fin (2 * q)) :=
    { toFun := midFun
      invFun := midFun
      left_inv := hmidFun_invol
      right_inv := hmidFun_invol }
  have hsign_midSwap : Equiv.Perm.sign midSwap = (-1 : ℤˣ) ^ (A₀ᶜ.card * A₁.card) := by
    rw [sign_eq_invSign]; unfold invSign invCount
    -- Inversions of `midSwap` are exact pairs `(i, j)` with `m0 ≤ i < q` and `q ≤ j < q + m1`
    have hfilt :
        (Finset.univ.filter fun r : Fin (2 * q) × Fin (2 * q) =>
          r.1 < r.2 ∧ midSwap r.2 < midSwap r.1) =
        (Finset.univ.filter fun i : Fin (2 * q) => m0 ≤ i.val ∧ i.val < q) ×ˢ
        (Finset.univ.filter fun j : Fin (2 * q) => q ≤ j.val ∧ j.val < q + m1) := by
      ext ⟨i, j⟩
      have hi_lt := i.isLt
      have hj_lt := j.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, midSwap,
        Equiv.coe_fn_mk, Fin.lt_def, hmidFun_val]
      constructor
      · intro ⟨hij, hms⟩
        split_ifs at hms <;> omega
      · intro ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩
        refine ⟨by omega, ?_⟩
        split_ifs <;> omega
    rw [hfilt, Finset.card_product]
    have hc1 : (Finset.univ.filter fun i : Fin (2 * q) => m0 ≤ i.val ∧ i.val < q).card = m1 := by
      have : (Finset.univ.filter fun i : Fin (2 * q) => m0 ≤ i.val ∧ i.val < q).card =
          (Finset.range m1).card := by
        refine Finset.card_bij (fun i _ => i.val - m0) ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_range.mpr (by omega)
        · intro i₁ hi₁ i₂ hi₂ hEq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
          exact Fin.ext (by omega)
        · intro k hk
          have hk' := Finset.mem_range.mp hk
          exact ⟨⟨m0 + k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩,
            by dsimp; omega⟩
      rw [this, Finset.card_range]
    have hc2 : (Finset.univ.filter fun j : Fin (2 * q) => q ≤ j.val ∧ j.val < q + m1).card = m1 := by
      have : (Finset.univ.filter fun j : Fin (2 * q) => q ≤ j.val ∧ j.val < q + m1).card =
          (Finset.range m1).card := by
        refine Finset.card_bij (fun j _ => j.val - q) ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact Finset.mem_range.mpr (by omega)
        · intro j₁ hj₁ j₂ hj₂ hEq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
          exact Fin.ext (by omega)
        · intro k hk
          have hk' := Finset.mem_range.mp hk
          exact ⟨⟨q + k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩,
            by dsimp; omega⟩
      rw [this, Finset.card_range]
    rw [hc1, hc2, hAc0]
  -- Step 3: `φ_c : Equiv.Perm (ZMod q)` corresponds to `f0` (on block 0) and `f1` (on block 1)
  have hcard0 : Fintype.card (A₀ ⊕ₗ A₁) = q := by
    rw [Fintype.card_congr ofLex]; simpa [ZMod.card] using Fintype.card_congr f0
  have hcard1 : Fintype.card ((A₀ᶜ : Finset (ZMod q)) ⊕ₗ (A₁ᶜ : Finset (ZMod q))) = q := by
    rw [Fintype.card_congr ofLex]; simpa [ZMod.card] using Fintype.card_congr f1
  let σ0 : Equiv.Perm (ZMod q) :=
    eCod.toEquiv.symm.trans ((Fintype.orderIsoFinOfCardEq (α := A₀ ⊕ₗ A₁) hcard0).toEquiv.trans
      (ofLex.trans f0))
  let σ1 : Equiv.Perm (ZMod q) :=
    eCod.toEquiv.symm.trans
      ((Fintype.orderIsoFinOfCardEq (α := (A₀ᶜ : Finset (ZMod q)) ⊕ₗ (A₁ᶜ : Finset (ZMod q))) hcard1).toEquiv.trans
        (ofLex.trans f1))
  have hsign_σ0 : Equiv.Perm.sign σ0 = sumBijectionSign f0 := by
    unfold sumBijectionSign
    let τ : Equiv.Perm (Fin q) :=
      (Fintype.orderIsoFinOfCardEq (α := A₀ ⊕ₗ A₁) hcard0).toEquiv.trans
        (ofLex.trans (f0.trans eCod.toEquiv.symm))
    have hconj : eCod.toEquiv.permCongr τ = σ0 := by ext x; simp [σ0, τ, Equiv.permCongr_apply]
    change Equiv.Perm.sign σ0 = Equiv.Perm.sign τ
    rw [← hconj, Equiv.Perm.sign_permCongr]
  have hsign_σ1 : Equiv.Perm.sign σ1 = sumBijectionSign f1 := by
    unfold sumBijectionSign
    let τ : Equiv.Perm (Fin q) :=
      (Fintype.orderIsoFinOfCardEq (α := (A₀ᶜ : Finset (ZMod q)) ⊕ₗ (A₁ᶜ : Finset (ZMod q))) hcard1).toEquiv.trans
        (ofLex.trans (f1.trans eCod.toEquiv.symm))
    have hconj : eCod.toEquiv.permCongr τ = σ1 := by ext x; simp [σ1, τ, Equiv.permCongr_apply]
    change Equiv.Perm.sign σ1 = Equiv.Perm.sign τ
    rw [← hconj, Equiv.Perm.sign_permCongr]
  -- Verify `p * blockPerm q 1 (fun b => if b = 0 then mkUnion A₀ else mkUnion A₁) = blockPerm q 1 (fun c => if c = 0 then σ0 else σ1) * midSwap`!
  let P1 := blockPerm q 1 (fun b => if b = 0 then mkUnion A₀ else mkUnion A₁)
  let P3 := blockPerm q 1 (fun c => if c = 0 then σ0 else σ1)
  -- Helper: evaluate `σ0 (eCod i)` and `σ1 (eCod i)` explicitly
  have hσ0_apply : ∀ i : Fin q,
      σ0 (eCod i) =
        if h : i.val < m0 then f0 (Sum.inl (A₀.orderIsoOfFin rfl ⟨i.val, h⟩))
        else f0 (Sum.inr (A₁.orderIsoOfFin rfl ⟨i.val - m0, by have := i.isLt; omega⟩)) := by
    intro i
    let f01 : Fin q ≃o (A₀ ⊕ₗ A₁) := finSumOrderIso (A₀.orderIsoOfFin rfl) (A₁.orderIsoOfFin rfl) hm01
    have hord : Fintype.orderIsoFinOfCardEq (α := A₀ ⊕ₗ A₁) hcard0 = f01 := Subsingleton.elim _ _
    have heCod_id : eCod.toEquiv.symm (eCod i) = i := eCod.symm_apply_apply i
    dsimp only [σ0]
    simp only [Equiv.trans_apply, heCod_id, hord]
    split_ifs with hlt
    · exact congrArg f0 (finSumOrderIso_apply_lt _ _ _ i hlt)
    · exact congrArg f0 (finSumOrderIso_apply_ge _ _ _ i hlt)
  have hσ1_apply : ∀ i : Fin q,
      σ1 (eCod i) =
        if h : i.val < m1 then f1 (Sum.inl (A₀ᶜ.orderIsoOfFin hAc0 ⟨i.val, h⟩))
        else f1 (Sum.inr (A₁ᶜ.orderIsoOfFin hAc1 ⟨i.val - m1, by have := i.isLt; omega⟩)) := by
    intro i
    have hsumC : A₀ᶜ.card + A₁ᶜ.card = q := by omega
    let f01 : Fin q ≃o ((A₀ᶜ : Finset (ZMod q)) ⊕ₗ (A₁ᶜ : Finset (ZMod q))) :=
      finSumOrderIso (A₀ᶜ.orderIsoOfFin hAc0) (A₁ᶜ.orderIsoOfFin hAc1) (by omega : m1 + m0 = q)
    have hord : Fintype.orderIsoFinOfCardEq (α := (A₀ᶜ : Finset (ZMod q)) ⊕ₗ (A₁ᶜ : Finset (ZMod q))) hcard1 = f01 :=
      Subsingleton.elim _ _
    have heCod_id : eCod.toEquiv.symm (eCod i) = i := eCod.symm_apply_apply i
    dsimp only [σ1]
    simp only [Equiv.trans_apply, heCod_id, hord]
    split_ifs with hlt
    · exact congrArg f1 (finSumOrderIso_apply_lt _ _ _ i hlt)
    · exact congrArg f1 (finSumOrderIso_apply_ge _ _ _ i hlt)
  have hfactor : p * P1 = P3 * midSwap := by
    apply Equiv.Perm.ext; intro k
    obtain ⟨⟨b, x⟩, rfl⟩ := (blockEquiv q).surjective k
    obtain ⟨i, rfl⟩ := eCod.surjective x
    have hbe_val : ∀ (c : Fin 2) (j : Fin q),
        (blockEquiv q (c, eCod j)).val = c.val * q + j.val := fun c j => by
      change c.val * q + (eCod j).val = c.val * q + j.val
      rw [heCod]
    simp only [Equiv.Perm.mul_apply, P1, P3, blockPerm_apply, Equiv.Perm.one_apply]
    fin_cases b
    · -- Block 0: `i < m0` vs `m0 ≤ i < q`
      simp only [Fin.mk_zero, Fin.isValue, ↓reduceIte]
      rw [hmkUnion_apply A₀ i]
      by_cases hlt : i.val < m0
      · rw [dif_pos hlt]
        have hmid : midSwap (blockEquiv q (0, eCod i)) = blockEquiv q (0, eCod i) := by
          apply Fin.ext; change (midFun (blockEquiv q (0, eCod i))).val = _
          rw [hmidFun_val, hbe_val]; simp [hlt]
        rw [hmid, blockPerm_apply, Equiv.Perm.one_apply]
        simp only [Fin.isValue, ↓reduceIte]
        rw [hσ0_apply i, dif_pos hlt, hp00 _ (A₀.orderIsoOfFin rfl ⟨i.val, hlt⟩).2]
      · rw [dif_neg hlt]
        let j : Fin q := ⟨i.val - m0, by have := i.isLt; omega⟩
        have hmid : midSwap (blockEquiv q (0, eCod i)) = blockEquiv q (1, eCod j) := by
          apply Fin.ext; change (midFun (blockEquiv q (0, eCod i))).val = _
          rw [hmidFun_val, hbe_val, hbe_val]
          simp only [Fin.val_zero, zero_mul, zero_add, Fin.val_one, one_mul, hlt, ↓reduceIte,
            i.isLt, j]
          omega
        rw [hmid, blockPerm_apply, Equiv.Perm.one_apply]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
        have hjlt : j.val < m1 := by dsimp [j]; have := i.isLt; omega
        rw [hσ1_apply j, dif_pos hjlt]
        have hmem := (A₀ᶜ.orderIsoOfFin (k := q - m0) (by simp [Finset.card_compl, ZMod.card, m0])
          ⟨i.val - m0, by have := i.isLt; omega⟩).2
        rw [hp01 _ hmem]
        congr 1
    · -- Block 1: `i < m1` vs `m1 ≤ i < q`
      simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [hmkUnion_apply A₁ i]
      by_cases hlt : i.val < m1
      · rw [dif_pos hlt]
        let j : Fin q := ⟨m0 + i.val, by omega⟩
        have hmid : midSwap (blockEquiv q (1, eCod i)) = blockEquiv q (0, eCod j) := by
          apply Fin.ext; change (midFun (blockEquiv q (1, eCod i))).val = _
          rw [hmidFun_val, hbe_val, hbe_val]
          have h1 : ¬ (q + i.val < m0) := by omega
          have h2 : ¬ (q + i.val < q) := by omega
          have h3 : q + i.val < q + m1 := by omega
          simp only [Fin.val_one, one_mul, Fin.val_zero, zero_mul, zero_add, h1, h2, h3,
            ↓reduceIte, j]
          omega
        rw [hmid, blockPerm_apply, Equiv.Perm.one_apply]
        simp only [Fin.isValue, ↓reduceIte]
        have hjnot : ¬ j.val < m0 := by dsimp [j]; omega
        rw [hσ0_apply j, dif_neg hjnot, hp10 _ (A₁.orderIsoOfFin rfl ⟨i.val, hlt⟩).2]
        congr 1; congr 1
        exact congrArg f0 (congrArg Sum.inr (congrArg (A₁.orderIsoOfFin rfl) (Fin.ext (by dsimp [j]; omega))))
      · rw [dif_neg hlt]
        have hmid : midSwap (blockEquiv q (1, eCod i)) = blockEquiv q (1, eCod i) := by
          apply Fin.ext; change (midFun (blockEquiv q (1, eCod i))).val = _
          rw [hmidFun_val, hbe_val]
          have h1 : ¬ (q + i.val < m0) := by omega
          have h2 : ¬ (q + i.val < q) := by omega
          have h3 : ¬ (q + i.val < q + m1) := by omega
          simp [h1, h2, h3]
        rw [hmid, blockPerm_apply, Equiv.Perm.one_apply]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [hσ1_apply i, dif_neg hlt]
        have hmem := (A₁ᶜ.orderIsoOfFin (k := q - m1) (by simp [Finset.card_compl, ZMod.card, m1])
          ⟨i.val - m1, by have := i.isLt; omega⟩).2
        rw [hp11 _ hmem]
        congr 1
  -- Take signs of `p * P1 = P3 * midSwap`
  have hsign_eq := congrArg Equiv.Perm.sign hfactor
  rw [map_mul, map_mul, sign_blockPerm_eq hodd, sign_blockPerm_eq hodd, hsign_midSwap] at hsign_eq
  simp only [↓reduceIte, one_mul, one_ne_zero, hsign_mkUnion, hsign_σ0, hsign_σ1] at hsign_eq
  have hsq : ∀ u : ℤˣ, u * u = 1 := fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  calc Equiv.Perm.sign p
      = Equiv.Perm.sign p * (thetaSign A₀ * thetaSign A₁) * (thetaSign A₀ * thetaSign A₁) := by
          rw [mul_assoc, hsq, mul_one]
    _ = (sumBijectionSign f0 * sumBijectionSign f1 * (-1 : ℤˣ) ^ (A₀ᶜ.card * A₁.card)) *
          (thetaSign A₀ * thetaSign A₁) := by rw [hsign_eq]
    _ = thetaSign A₀ * thetaSign A₁ * (-1 : ℤˣ) ^ (A₀ᶜ.card * A₁.card) *
          sumBijectionSign f0 * sumBijectionSign f1 := by ac_rfl

end InversionSign

section RankOneFactorAndStrata

/-! ### Lemma 6.7: Sign Factorization for `ℓ_0`, `ℓ_B`, `ℓ_C` -/

/-- A fixed layer on a pattern `O` contributes `+1` to the product of the 4 signs. -/
private lemma fixed_layer_sign_eq_one {q m : ℕ} [NeZero q] (hodd : Odd q)
    (O : Pattern q m)
    (φ : ∀ a b : Fin 2, O.O a b → ZMod q)
    (hrow : ∀ a : Fin 2, Function.Bijective (fun s : O.O a 0 ⊕ O.O a 1 => Sum.elim (φ a 0) (φ a 1) s))
    (hcol : ∀ b : Fin 2, Function.Bijective (fun s : O.O 0 b ⊕ O.O 1 b => Sum.elim (φ 0 b) (φ 1 b) s)) :
    (∏ a : Fin 2, sumBijectionSign (Equiv.ofBijective _ (hrow a))) *
    (∏ b : Fin 2, sumBijectionSign (Equiv.ofBijective _ (hcol b))) = 1 := by
  classical
  let Y : Finset (ZMod q) := Finset.univ.image (φ 0 0)
  have hφ_inj : ∀ a b, Function.Injective (φ a b) := fun a b x y hxy => by
    fin_cases b
    · have := (hrow a).1 (show Sum.elim (φ a 0) (φ a 1) (Sum.inl x) =
        Sum.elim (φ a 0) (φ a 1) (Sum.inl y) from hxy)
      exact Sum.inl.inj this
    · have := (hrow a).1 (show Sum.elim (φ a 0) (φ a 1) (Sum.inr x) =
        Sum.elim (φ a 0) (φ a 1) (Sum.inr y) from hxy)
      exact Sum.inr.inj this
  have himg00 : Finset.univ.image (φ 0 0) = Y := rfl
  have himg01 : Finset.univ.image (φ 0 1) = Yᶜ := by
    ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, Y]
    constructor
    · rintro ⟨x, rfl⟩ ⟨y, hy⟩
      exact Sum.inl_ne_inr ((hrow 0).1 hy)
    · intro hz
      rcases (hrow 0).2 z with ⟨x | x, hx⟩
      · exact (hz ⟨x, hx⟩).elim
      · exact ⟨x, hx⟩
  have himg10 : Finset.univ.image (φ 1 0) = Yᶜ := by
    ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, Y]
    constructor
    · rintro ⟨x, rfl⟩ ⟨y, hy⟩
      exact Sum.inl_ne_inr ((hcol 0).1 hy)
    · intro hz
      rcases (hcol 0).2 z with ⟨x | x, hx⟩
      · exact (hz ⟨x, hx⟩).elim
      · exact ⟨x, hx⟩
  have himg11 : Finset.univ.image (φ 1 1) = Y := by
    ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      by_contra hz
      have hzc : φ 1 1 x ∈ Yᶜ := Finset.mem_compl.mpr hz
      rw [← himg10] at hzc
      rcases Finset.mem_image.mp hzc with ⟨y, _, hy⟩
      exact Sum.inl_ne_inr ((hrow 1).1 hy)
    · intro hz
      rcases (hrow 1).2 z with ⟨x | x, hx⟩
      · exfalso
        have hzc : z ∈ Yᶜ := by rw [← himg10]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
        exact Finset.mem_compl.mp hzc hz
      · exact ⟨x, hx⟩
  have hYcard : Y.card = m := by
    dsimp [Y]; rw [Finset.card_image_of_injective _ (hφ_inj 0 0), Finset.card_attach, O.card_00]
  have hYccard : Yᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, hYcard]
  have hc00 : (O.O 0 0).card = Y.card := by rw [O.card_00, hYcard]
  have hc01 : (O.O 0 1).card = Yᶜ.card := by rw [O.card_01, hYccard]
  have hc10 : (O.O 1 0).card = Yᶜ.card := by rw [O.card_10, hYccard]
  have hc11 : (O.O 1 1).card = Y.card := by rw [O.card_11, hYcard]
  have hc11' : (O.O 1 1).card = (Yᶜᶜ : Finset (ZMod q)).card := by simpa using hc11
  let e00 : O.O 0 0 ≃ Y :=
    Equiv.ofBijective (fun d => ⟨φ 0 0 d, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      ⟨fun x y h => hφ_inj 0 0 (congrArg Subtype.val h),
       fun ⟨z, hz⟩ => by rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
  let e01 : O.O 0 1 ≃ (Yᶜ : Finset (ZMod q)) :=
    Equiv.ofBijective (fun d => ⟨φ 0 1 d, by rw [← himg01]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      ⟨fun x y h => hφ_inj 0 1 (congrArg Subtype.val h),
       fun ⟨z, hz⟩ => by rw [← himg01] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
  let e10 : O.O 1 0 ≃ (Yᶜ : Finset (ZMod q)) :=
    Equiv.ofBijective (fun d => ⟨φ 1 0 d, by rw [← himg10]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      ⟨fun x y h => hφ_inj 1 0 (congrArg Subtype.val h),
       fun ⟨z, hz⟩ => by rw [← himg10] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
  let e11' : O.O 1 1 ≃ (Yᶜᶜ : Finset (ZMod q)) :=
    Equiv.ofBijective (fun d => ⟨φ 1 1 d, by simp [← himg11]⟩)
      ⟨fun x y h => hφ_inj 1 1 (congrArg Subtype.val h),
       fun ⟨z, hz⟩ => by
         have hz' : z ∈ Y := by simpa using hz
         rw [← himg11] at hz'; rcases Finset.mem_image.mp hz' with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  rw [sumBijectionSign_split (Equiv.ofBijective _ (hrow 0)) hc00 hc01 e00 e01
        (fun _ => rfl) (fun _ => rfl),
      sumBijectionSign_split (Equiv.ofBijective _ (hrow 1)) hc10 hc11' e10 e11'
        (fun _ => rfl) (fun _ => rfl),
      sumBijectionSign_split (Equiv.ofBijective _ (hcol 0)) hc00 hc10 e00 e10
        (fun _ => rfl) (fun _ => rfl),
      sumBijectionSign_split (Equiv.ofBijective _ (hcol 1)) hc01 hc11' e01 e11'
        (fun _ => rfl) (fun _ => rfl)]
  have hsq : ∀ u : ℤˣ, u * u = 1 := fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  calc (thetaSign Y * orderedSign hc00 e00 * orderedSign hc01 e01) *
        (thetaSign Yᶜ * orderedSign hc10 e10 * orderedSign hc11' e11') *
        ((thetaSign Y * orderedSign hc00 e00 * orderedSign hc10 e10) *
         (thetaSign Yᶜ * orderedSign hc01 e01 * orderedSign hc11' e11'))
      = (thetaSign Y * thetaSign Y) * (thetaSign Yᶜ * thetaSign Yᶜ) *
        (orderedSign hc00 e00 * orderedSign hc00 e00) *
        (orderedSign hc01 e01 * orderedSign hc01 e01) *
        (orderedSign hc10 e10 * orderedSign hc10 e10) *
        (orderedSign hc11' e11' * orderedSign hc11' e11') := by ac_rfl
    _ = 1 := by simp [hsq]

/-- Extract the pattern `O` of a square fixed by `ℓ ∈ {ℓ_0, ℓ_B, ℓ_C}`. -/
private lemma pattern_of_fix_rankone {q : ℕ} [NeZero q] (w : Fin 2 → ZMod q)
    (L : LatinSquare (2 * q))
    (hL : L ∈ fixSet ((Subgroup.zpowers (sylowElem q 1 1 1 1 (w 0) (w 1))).map (sylowP q).subtype)) :
    let m := stratumOf q L
    ∃ hm : m ≤ q, ∃ O : Pattern q m,
      ∀ a b : Fin 2, ∀ x d : ZMod q,
        d ∈ O.O a b ↔
          ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := by
  classical
  let ℓ := sylowElem q 1 1 1 1 (w 0) (w 1)
  have hshift : ∀ a b : Fin 2, ∀ x d : ZMod q,
      L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
        blockEquiv q
          (((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1,
           ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 +
             w ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 * x) := by
    intro a b x d
    have hpow : ℓ ^ x.val ∈ Subgroup.zpowers ℓ := Subgroup.pow_mem _ (Subgroup.mem_zpowers ℓ) _
    have hfix := (sylow_fix_entry_iff (ℓ ^ x.val) L).mp (hL (ℓ ^ x.val).1 ⟨ℓ ^ x.val, hpow, rfl⟩)
      a b 0 d
    have hvec : sylowToVec (ℓ ^ x.val) = (fun _ => x, fun _ => x, fun c => w c * x) := by
      have h1 : sylowToVec ℓ = (fun _ => 1, fun _ => 1, w) := by
        dsimp [ℓ]; rw [sylowToVec_sylowElem]
        refine Prod.ext (funext fun i => by fin_cases i <;> rfl)
          (Prod.ext (funext fun i => by fin_cases i <;> rfl)
            (funext fun c => by fin_cases c <;> rfl))
      have hpow_v : ∀ n : ℕ, sylowToVec (ℓ ^ n) =
          (fun _ => (n : ZMod q), fun _ => (n : ZMod q), fun c => (n : ZMod q) * w c) := fun n => by
        induction n with
        | zero => simp [sylowToVec_one]; rfl
        | succ n ih =>
          rw [pow_succ, sylowToVec_mul, ih, h1]
          refine Prod.ext (funext fun _ => by change (n : ZMod q) + 1 = _; push_cast; rfl)
            (Prod.ext (funext fun _ => by change (n : ZMod q) + 1 = _; push_cast; rfl)
              (funext fun c => by change (n : ZMod q) * w c + w c = _; push_cast; ring))
      rw [hpow_v, ZMod.natCast_zmod_val]
      refine Prod.ext rfl (Prod.ext rfl (funext fun c => mul_comm _ _))
    rw [hvec] at hfix
    simpa [zero_add, add_comm] using hfix
  let A : Fin 2 → Fin 2 → Finset (ZMod q) := fun a b =>
    Finset.univ.filter fun d : ZMod q =>
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 0
  have hA_row : ∀ a : Fin 2, (A a 0).card + (A a 1).card = q := by
    intro a
    -- In row `(a, 0)`, the symbols in `Σ_0` have count `q`
    let S := Finset.univ.filter fun col : Fin (2 * q) =>
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) col)).1 = 0
    have hS : S.card = q := by
      have hbij : S.card = (Finset.univ : Finset (ZMod q)).card := by
        refine Finset.card_bij (fun col _ => ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) col)).2)
          (fun _ _ => Finset.mem_univ _)
          (fun c₁ hc₁ c₂ hc₂ hEq => by
            have h1 := (Finset.mem_filter.mp hc₁).2
            have h2 := (Finset.mem_filter.mp hc₂).2
            exact (L.row_bijective _).1 ((blockEquiv q).symm.injective (Prod.ext (h1.trans h2.symm) hEq)))
          (fun z _ => by
            rcases (L.row_bijective (blockEquiv q (a, 0))).2 (blockEquiv q (0, z)) with ⟨col, hcol⟩
            refine ⟨col, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hcol]⟩, by simp [hcol]⟩)
      rw [hbij, Finset.card_univ, ZMod.card]
    have hS_split : S.card = (A a 0).card + (A a 1).card := by
      have hbij : S.card = Fintype.card (A a 0 ⊕ A a 1) := by
        symm
        refine Finset.card_bij (fun s _ => Sum.elim (fun d => blockEquiv q (0, d.1))
            (fun d => blockEquiv q (1, d.1)) s) ?_ ?_ ?_
        · rintro (⟨d, hd⟩ | ⟨d, hd⟩) _ <;>
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩
        · rintro (⟨d₁, _⟩ | ⟨d₁, _⟩) _ (⟨d₂, _⟩ | ⟨d₂, _⟩) _ hEq
          · exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective hEq)))
          · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) Fin.zero_ne_one
          · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) one_ne_zero
          · exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective hEq)))
        · intro col hcol
          obtain ⟨⟨b, d⟩, rfl⟩ := (blockEquiv q).surjective col
          have h0 := (Finset.mem_filter.mp hcol).2
          fin_cases b
          · exact ⟨Sum.inl ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩, Finset.mem_univ _, rfl⟩
          · exact ⟨Sum.inr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩, Finset.mem_univ _, rfl⟩
      rw [hbij, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    omega
  have hA_col : ∀ b : Fin 2, (A 0 b).card + (A 1 b).card = q := by
    intro b
    let S := Finset.univ.filter fun r : Fin (2 * q) =>
      ((blockEquiv q).symm (L.entry r (blockEquiv q (b, 0)))).1 = 0
    have hS : S.card = q := by
      have hbij : S.card = (Finset.univ : Finset (ZMod q)).card := by
        refine Finset.card_bij (fun r _ => ((blockEquiv q).symm (L.entry r (blockEquiv q (b, 0)))).2)
          (fun _ _ => Finset.mem_univ _)
          (fun r₁ hr₁ r₂ hr₂ hEq => by
            have h1 := (Finset.mem_filter.mp hr₁).2
            have h2 := (Finset.mem_filter.mp hr₂).2
            exact (L.col_bijective _).1 ((blockEquiv q).symm.injective (Prod.ext (h1.trans h2.symm) hEq)))
          (fun z _ => by
            rcases (L.col_bijective (blockEquiv q (b, 0))).2 (blockEquiv q (0, z)) with ⟨r, hr⟩
            refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hr]⟩, by simp [hr]⟩)
      rw [hbij, Finset.card_univ, ZMod.card]
    have hS_split : S.card = (A 0 b).card + (A 1 b).card := by
      have hbij : S.card = Fintype.card (A 0 b ⊕ A 1 b) := by
        symm
        refine Finset.card_bij (fun s _ => Sum.elim (fun d => blockEquiv q (0, -d.1))
            (fun d => blockEquiv q (1, -d.1)) s) ?_ ?_ ?_
        · rintro (⟨d, hd⟩ | ⟨d, hd⟩) _
          · have hsh := hshift 0 b (-d) d
            simp only [neg_add_cancel] at hsh
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              dsimp only [Sum.elim]; rw [hsh, Equiv.symm_apply_apply]; exact (Finset.mem_filter.mp hd).2⟩
          · have hsh := hshift 1 b (-d) d
            simp only [neg_add_cancel] at hsh
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              dsimp only [Sum.elim]; rw [hsh, Equiv.symm_apply_apply]; exact (Finset.mem_filter.mp hd).2⟩
        · rintro (⟨d₁, _⟩ | ⟨d₁, _⟩) _ (⟨d₂, _⟩ | ⟨d₂, _⟩) _ hEq
          · exact congrArg Sum.inl (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective hEq))))
          · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) Fin.zero_ne_one
          · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) one_ne_zero
          · exact congrArg Sum.inr (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective hEq))))
        · intro r hr
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          have h0 := (Finset.mem_filter.mp hr).2
          have hsh := hshift a b x (-x)
          simp only [add_neg_cancel] at hsh
          rw [hsh, Equiv.symm_apply_apply] at h0
          fin_cases a
          · exact ⟨Sum.inl ⟨-x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩, Finset.mem_univ _, by simp⟩
          · exact ⟨Sum.inr ⟨-x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩, Finset.mem_univ _, by simp⟩
      rw [hbij, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    omega
  have hr0 := hA_row 0; have hr1 := hA_row 1; have hc0 := hA_col 0; have hc1 := hA_col 1
  have hm_le : stratumOf q L ≤ q := by
    change (A 0 0).card ≤ q; omega
  refine ⟨hm_le,
    { O := A
      card_00 := rfl
      card_11 := by change (A 1 1).card = (A 0 0).card; omega
      card_01 := by change (A 0 1).card = q - (A 0 0).card; omega
      card_10 := by change (A 1 0).card = q - (A 0 0).card; omega }, ?_⟩
  intro a b x d
  rw [hshift a b x d, Equiv.symm_apply_apply]
  simp [A]

/-- **Lemma 6.7** (`lem_6_7_factor`): Sign factorization for squares fixed by `ℓ_0, ℓ_B, ℓ_C`. -/
theorem lem_6_7_factor (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    (∀ L : LatinSquare (2 * q),
      L ∈ fixSet ((Subgroup.zpowers (ell0 q)).map (sylowP q).subtype) →
        squareSign L = 1) ∧
    (∀ (L : LatinSquare (2 * q)) (m : ℕ) (hm : m ≤ q) (O : Pattern q m)
      (h1 : Layer (O.compl hm)),
      L ∈ fixSet ((Subgroup.zpowers (ellB q)).map (sylowP q).subtype) →
      (∀ a b : Fin 2, ∀ x d : ZMod q,
        (d ∈ O.O a b ↔
          ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0) ∧
        ∀ hd : d ∈ (O.compl hm).O a b,
          L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
            blockEquiv q (1, x + h1.h a b ⟨d, hd⟩)) →
        squareSign L = layerSign h1) ∧
    (∀ (L : LatinSquare (2 * q)) (m : ℕ) (hm : m ≤ q) (O : Pattern q m)
      (h0 : Layer O) (h1 : Layer (O.compl hm)),
      L ∈ fixSet ((Subgroup.zpowers (ellC q)).map (sylowP q).subtype) →
      (∀ a b : Fin 2, ∀ x d : ZMod q,
        (∀ hd : d ∈ O.O a b,
          L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
            blockEquiv q (0, x + h0.h a b ⟨d, hd⟩)) ∧
        (∀ hd : d ∈ (O.compl hm).O a b,
          L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
            blockEquiv q (1, x + h1.h a b ⟨d, hd⟩))) →
        squareSign L = layerSign h0 * layerSign h1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have hsq : ∀ u : ℤˣ, u * u = 1 := fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  -- Unified sign reduction: for any `ℓ = sylowElem 1 1 1 1 w0 w1` and `L ∈ Fix(⟨ℓ⟩)`
  -- with pattern `O` and row/col bijections `r0, r1, c0, c1` on `Σ_0` and `Σ_1`,
  -- `squareSign L` equals the product of the 4 `sumBijectionSign`s on `Σ_0` times those on `Σ_1`!
  have hunified : ∀ (w0 w1 : ZMod q) (L : LatinSquare (2 * q)) (m : ℕ) (hm : m ≤ q)
      (O : Pattern q m)
      (r0 : ∀ a : Fin 2, (O.O a 0 ⊕ O.O a 1) ≃ ZMod q)
      (r1 : ∀ a : Fin 2, (((O.O a 0)ᶜ : Finset (ZMod q)) ⊕ ((O.O a 1)ᶜ : Finset (ZMod q))) ≃ ZMod q)
      (c0 : ∀ b : Fin 2, (O.O 0 b ⊕ O.O 1 b) ≃ ZMod q)
      (c1 : ∀ b : Fin 2, (((O.O 0 b)ᶜ : Finset (ZMod q)) ⊕ ((O.O 1 b)ᶜ : Finset (ZMod q))) ≃ ZMod q),
      L ∈ fixSet ((Subgroup.zpowers (sylowElem q 1 1 1 1 w0 w1)).map (sylowP q).subtype) →
      (∀ a d (hd : d ∈ O.O a 0), L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d)) =
        blockEquiv q (0, r0 a (Sum.inl ⟨d, hd⟩))) →
      (∀ a d (hd : d ∈ O.O a 1), L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d)) =
        blockEquiv q (0, r0 a (Sum.inr ⟨d, hd⟩))) →
      (∀ a d (hd : d ∈ (O.O a 0)ᶜ), L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d)) =
        blockEquiv q (1, r1 a (Sum.inl ⟨d, hd⟩))) →
      (∀ a d (hd : d ∈ (O.O a 1)ᶜ), L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d)) =
        blockEquiv q (1, r1 a (Sum.inr ⟨d, hd⟩))) →
      (∀ b d (hd : d ∈ O.O 0 b), L.entry (blockEquiv q (0, -d)) (blockEquiv q (b, 0)) =
        blockEquiv q (0, c0 b (Sum.inl ⟨d, hd⟩))) →
      (∀ b d (hd : d ∈ O.O 1 b), L.entry (blockEquiv q (1, -d)) (blockEquiv q (b, 0)) =
        blockEquiv q (0, c0 b (Sum.inr ⟨d, hd⟩))) →
      (∀ b d (hd : d ∈ (O.O 0 b)ᶜ), L.entry (blockEquiv q (0, -d)) (blockEquiv q (b, 0)) =
        blockEquiv q (1, c1 b (Sum.inl ⟨d, hd⟩))) →
      (∀ b d (hd : d ∈ (O.O 1 b)ᶜ), L.entry (blockEquiv q (1, -d)) (blockEquiv q (b, 0)) =
        blockEquiv q (1, c1 b (Sum.inr ⟨d, hd⟩))) →
      squareSign L =
        ((∏ a : Fin 2, sumBijectionSign (r0 a)) * (∏ b : Fin 2, sumBijectionSign (c0 b))) *
        ((∏ a : Fin 2, sumBijectionSign (r1 a)) * (∏ b : Fin 2, sumBijectionSign (c1 b))) := by
    intro w0 w1 L m hm O r0 r1 c0 c1 hL hr0_0 hr0_1 hr1_0 hr1_1 hc0_0 hc0_1 hc1_0 hc1_1
    let ℓ := sylowElem q 1 1 1 1 w0 w1
    let H := Subgroup.zpowers ℓ
    have hrow_mv : ∀ a : Fin 2, ∃ g ∈ H, (sylowToVec g).1 a ≠ 0 := fun a =>
      ⟨ℓ, Subgroup.mem_zpowers ℓ, by dsimp [ℓ]; rw [sylowToVec_sylowElem]; fin_cases a <;> simp⟩
    have hcol_mv : ∀ b : Fin 2, ∃ g ∈ H, (sylowToVec g).2.1 b ≠ 0 := fun b =>
      ⟨ℓ, Subgroup.mem_zpowers ℓ, by dsimp [ℓ]; rw [sylowToVec_sylowElem]; fin_cases b <;> simp⟩
    rw [squareSign_of_all_moving hodd H L hL hrow_mv hcol_mv]
    -- Re-index column `(b, 0)` by `negBlock = blockPerm q 1 (fun _ => Equiv.neg (ZMod q))` (even!)
    let negBlock := blockPerm q 1 (fun _ => Equiv.neg (ZMod q))
    have hnegBlock : Equiv.Perm.sign negBlock = 1 := by
      rw [sign_blockPerm_eq hq_odd]; simp [hsq]
    have hrow_card : ∀ a : Fin 2, (O.O a 0).card + (O.O a 1).card = q := fun a => by
      fin_cases a <;> simp [O.card_00, O.card_01, O.card_10, O.card_11] <;> omega
    have hcol_card : ∀ b : Fin 2, (O.O 0 b).card + (O.O 1 b).card = q := fun b => by
      fin_cases b <;> simp [O.card_00, O.card_01, O.card_10, O.card_11] <;> omega
    have hsr : ∀ a : Fin 2,
        Equiv.Perm.sign (rowPerm L (blockEquiv q (a, 0))) =
        thetaSign (O.O a 0) * thetaSign (O.O a 1) *
          (-1 : ℤˣ) ^ ((O.O a 0)ᶜ.card * (O.O a 1).card) *
          sumBijectionSign (r0 a) * sumBijectionSign (r1 a) := fun a =>
      sign_block_split hq_odd (O.O a 0) (O.O a 1) (hrow_card a) (r0 a) (r1 a)
        (rowPerm L (blockEquiv q (a, 0)))
        (fun d hd => by simpa [rowPerm] using hr0_0 a d hd)
        (fun d hd => by simpa [rowPerm] using hr1_0 a d hd)
        (fun d hd => by simpa [rowPerm] using hr0_1 a d hd)
        (fun d hd => by simpa [rowPerm] using hr1_1 a d hd)
    have hsc : ∀ b : Fin 2,
        Equiv.Perm.sign (colPerm L (blockEquiv q (b, 0))) =
        thetaSign (O.O 0 b) * thetaSign (O.O 1 b) *
          (-1 : ℤˣ) ^ ((O.O 0 b)ᶜ.card * (O.O 1 b).card) *
          sumBijectionSign (c0 b) * sumBijectionSign (c1 b) := fun b => by
      have hmul : Equiv.Perm.sign (colPerm L (blockEquiv q (b, 0))) =
          Equiv.Perm.sign (colPerm L (blockEquiv q (b, 0)) * negBlock) := by
        rw [map_mul, hnegBlock, mul_one]
      rw [hmul]
      refine sign_block_split hq_odd (O.O 0 b) (O.O 1 b) (hcol_card b) (c0 b) (c1 b)
        (colPerm L (blockEquiv q (b, 0)) * negBlock) ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Equiv.Perm.mul_apply, negBlock, blockPerm_apply, Equiv.Perm.one_apply,
          Equiv.neg_apply]
        simpa [colPerm] using hc0_0 b d hd
      · intro d hd
        simp only [Equiv.Perm.mul_apply, negBlock, blockPerm_apply, Equiv.Perm.one_apply,
          Equiv.neg_apply]
        simpa [colPerm] using hc1_0 b d hd
      · intro d hd
        simp only [Equiv.Perm.mul_apply, negBlock, blockPerm_apply, Equiv.Perm.one_apply,
          Equiv.neg_apply]
        simpa [colPerm] using hc0_1 b d hd
      · intro d hd
        simp only [Equiv.Perm.mul_apply, negBlock, blockPerm_apply, Equiv.Perm.one_apply,
          Equiv.neg_apply]
        simpa [colPerm] using hc1_1 b d hd
    rw [hsr 0, hsr 1, hsc 0, hsc 1, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two,
      Fin.prod_univ_two]
    have hcard_sh :
        (O.O 0 0)ᶜ.card * (O.O 0 1).card = (O.O 0 0)ᶜ.card * (O.O 1 0).card ∧
        (O.O 1 0)ᶜ.card * (O.O 1 1).card = (O.O 0 1)ᶜ.card * (O.O 1 1).card := by
      simp [Finset.card_compl, ZMod.card, O.card_00, O.card_01, O.card_10, O.card_11]
    rw [hcard_sh.1, hcard_sh.2]
    calc _ =
        (thetaSign (O.O 0 0) * thetaSign (O.O 0 0)) *
        (thetaSign (O.O 0 1) * thetaSign (O.O 0 1)) *
        (thetaSign (O.O 1 0) * thetaSign (O.O 1 0)) *
        (thetaSign (O.O 1 1) * thetaSign (O.O 1 1)) *
        ((-1 : ℤˣ) ^ ((O.O 0 0)ᶜ.card * (O.O 1 0).card) *
          (-1 : ℤˣ) ^ ((O.O 0 0)ᶜ.card * (O.O 1 0).card)) *
        ((-1 : ℤˣ) ^ ((O.O 0 1)ᶜ.card * (O.O 1 1).card) *
          (-1 : ℤˣ) ^ ((O.O 0 1)ᶜ.card * (O.O 1 1).card)) *
        ((sumBijectionSign (r0 0) * sumBijectionSign (r0 1)) *
          (sumBijectionSign (c0 0) * sumBijectionSign (c0 1))) *
        ((sumBijectionSign (r1 0) * sumBijectionSign (r1 1)) *
          (sumBijectionSign (c1 0) * sumBijectionSign (c1 1))) := by ac_rfl
      _ = _ := by simp [hsq]
  -- Now deduce all three parts from `hunified` + `fixed_layer_sign_eq_one`!
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: `ℓ_0` (both symbol blocks are fixed)
    intro L hL
    obtain ⟨hm, O, hO⟩ := pattern_of_fix_rankone (fun _ => 0) L hL
    have hshift0 : ∀ a b : Fin 2, ∀ x d : ZMod q,
        L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
          L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) := by
      intro a b x d
      have hpow : ell0 q ^ x.val ∈ Subgroup.zpowers (ell0 q) :=
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      have hfix := (sylow_fix_entry_iff (ell0 q ^ x.val) L).mp
        (hL (ell0 q ^ x.val).1 ⟨ell0 q ^ x.val, hpow, rfl⟩) a b 0 d
      have hvec : sylowToVec (ell0 q ^ x.val) = (fun _ => x, fun _ => x, fun _ => 0) := by
        have h1 : sylowToVec (ell0 q) = (fun _ => 1, fun _ => 1, fun _ => 0) := by
          dsimp [ell0]; rw [sylowToVec_sylowElem]
          refine Prod.ext (funext fun i => by fin_cases i <;> rfl)
            (Prod.ext (funext fun i => by fin_cases i <;> rfl)
              (funext fun c => by fin_cases c <;> rfl))
        have hpow_v : ∀ n : ℕ, sylowToVec (ell0 q ^ n) =
            (fun _ => (n : ZMod q), fun _ => (n : ZMod q), fun _ => 0) := fun n => by
          induction n with
          | zero => simp [sylowToVec_one]; rfl
          | succ n ih =>
            rw [pow_succ, sylowToVec_mul, ih, h1]
            refine Prod.ext (funext fun _ => by change (n : ZMod q) + 1 = _; push_cast; rfl)
              (Prod.ext (funext fun _ => by change (n : ZMod q) + 1 = _; push_cast; rfl)
                (funext fun _ => by simp))
        rw [hpow_v, ZMod.natCast_zmod_val]
      rw [hvec] at hfix
      have hL0 := (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))
      simpa [zero_add, add_comm, hL0] using hfix
    let φ0 : ∀ a b : Fin 2, O.O a b → ZMod q := fun a b d =>
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d.1)))).2
    let φ1 : ∀ a b : Fin 2, (O.compl hm).O a b → ZMod q := fun a b d =>
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d.1)))).2
    have hmem0 : ∀ a b d (hd : d ∈ O.O a b),
        L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) = blockEquiv q (0, φ0 a b ⟨d, hd⟩) := by
      intro a b d hd
      have h0 := (hO a b 0 d).mp hd
      simp only [zero_add] at h0
      conv_lhs => rw [← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))]
      exact congrArg (blockEquiv q) (Prod.ext h0 rfl)
    have hmem1 : ∀ a b d (hd : d ∈ (O.O a b)ᶜ),
        L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) = blockEquiv q (1, φ1 a b ⟨d, hd⟩) := by
      intro a b d hd
      have h1 : ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 ≠ 0 := by
        intro h0; exact Finset.mem_compl.mp hd ((hO a b 0 d).mpr (by simpa using h0))
      have h1' : ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 1 := by
        generalize ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = c at h1 ⊢
        fin_cases c; exact (h1 rfl).elim; rfl
      conv_lhs => rw [← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))]
      exact congrArg (blockEquiv q) (Prod.ext h1' rfl)
    have hr0_bij : ∀ a : Fin 2, Function.Bijective (fun s : O.O a 0 ⊕ O.O a 1 => Sum.elim (φ0 a 0) (φ0 a 1) s) := by
      intro a; refine ⟨?_, ?_⟩
      · rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₂)) by
              rw [hmem0 a 0 d₁ hd₁, hmem0 a 0 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective h)))
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₂)) by
              rw [hmem0 a 0 d₁ hd₁, hmem0 a 1 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) Fin.zero_ne_one
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₂)) by
              rw [hmem0 a 1 d₁ hd₁, hmem0 a 0 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) one_ne_zero
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₂)) by
              rw [hmem0 a 1 d₁ hd₁, hmem0 a 1 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective h)))
      · intro z
        rcases (L.row_bijective (blockEquiv q (a, 0))).2 (blockEquiv q (0, z)) with ⟨col, hcol⟩
        obtain ⟨⟨b, d⟩, rfl⟩ := (blockEquiv q).surjective col
        have hd : d ∈ O.O a b := (hO a b 0 d).mpr (by simp [hcol])
        fin_cases b
        · simp only [Fin.mk_zero] at hcol; exact ⟨Sum.inl ⟨d, hd⟩, by simp [φ0, hcol]⟩
        · simp only [Fin.mk_one] at hcol; exact ⟨Sum.inr ⟨d, hd⟩, by simp [φ0, hcol]⟩
    have hr1_bij : ∀ a : Fin 2, Function.Bijective (fun s : (O.compl hm).O a 0 ⊕ (O.compl hm).O a 1 =>
        Sum.elim (φ1 a 0) (φ1 a 1) s) := by
      intro a; refine ⟨?_, ?_⟩
      · rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₂)) by
              rw [hmem1 a 0 d₁ hd₁, hmem1 a 0 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective h)))
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₂)) by
              rw [hmem1 a 0 d₁ hd₁, hmem1 a 1 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) Fin.zero_ne_one
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₂)) by
              rw [hmem1 a 1 d₁ hd₁, hmem1 a 0 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) one_ne_zero
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₂)) by
              rw [hmem1 a 1 d₁ hd₁, hmem1 a 1 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective h)))
      · intro z
        rcases (L.row_bijective (blockEquiv q (a, 0))).2 (blockEquiv q (1, z)) with ⟨col, hcol⟩
        obtain ⟨⟨b, d⟩, rfl⟩ := (blockEquiv q).surjective col
        have hd : d ∈ (O.compl hm).O a b := Finset.mem_compl.mpr fun h0 => by
          have := (hO a b 0 d).mp h0; simp [hcol] at this
        fin_cases b
        · simp only [Fin.mk_zero] at hcol; exact ⟨Sum.inl ⟨d, hd⟩, by simp [φ1, hcol]⟩
        · simp only [Fin.mk_one] at hcol; exact ⟨Sum.inr ⟨d, hd⟩, by simp [φ1, hcol]⟩
    have hc0_bij : ∀ b : Fin 2, Function.Bijective (fun s : O.O 0 b ⊕ O.O 1 b => Sum.elim (φ0 0 b) (φ0 1 b) s) := by
      intro b; refine ⟨?_, ?_⟩
      · rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 0 b (-d₁) d₁; have s2 := hshift0 0 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 0 b d₁ hd₁, hmem0 0 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inl (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective h))))
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 0 b (-d₁) d₁; have s2 := hshift0 1 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 0 b d₁ hd₁, hmem0 1 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) Fin.zero_ne_one
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 1 b (-d₁) d₁; have s2 := hshift0 0 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 1 b d₁ hd₁, hmem0 0 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) one_ne_zero
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 1 b (-d₁) d₁; have s2 := hshift0 1 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 1 b d₁ hd₁, hmem0 1 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inr (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective h))))
      · intro z
        rcases (L.col_bijective (blockEquiv q (b, 0))).2 (blockEquiv q (0, z)) with ⟨r, hr⟩
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        have hs := hshift0 a b x (-x); simp only [add_neg_cancel] at hs; dsimp only at hr; rw [hr] at hs
        have hd : -x ∈ O.O a b := (hO a b 0 (-x)).mpr (by simp [← hs])
        fin_cases a
        · simp only [Fin.mk_zero] at hs; exact ⟨Sum.inl ⟨-x, hd⟩, by simp [φ0, ← hs]⟩
        · simp only [Fin.mk_one] at hs; exact ⟨Sum.inr ⟨-x, hd⟩, by simp [φ0, ← hs]⟩
    have hc1_bij : ∀ b : Fin 2, Function.Bijective (fun s : (O.compl hm).O 0 b ⊕ (O.compl hm).O 1 b =>
        Sum.elim (φ1 0 b) (φ1 1 b) s) := by
      intro b; refine ⟨?_, ?_⟩
      · rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 0 b (-d₁) d₁; have s2 := hshift0 0 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem1 0 b d₁ hd₁, hmem1 0 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact congrArg Sum.inl (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective h))))
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 0 b (-d₁) d₁; have s2 := hshift0 1 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem1 0 b d₁ hd₁, hmem1 1 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) Fin.zero_ne_one
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 1 b (-d₁) d₁; have s2 := hshift0 0 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem1 1 b d₁ hd₁, hmem1 0 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) one_ne_zero
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 1 b (-d₁) d₁; have s2 := hshift0 1 b (-d₂) d₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem1 1 b d₁ hd₁, hmem1 1 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (1, z)) hEq)
          exact congrArg Sum.inr (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective h))))
      · intro z
        rcases (L.col_bijective (blockEquiv q (b, 0))).2 (blockEquiv q (1, z)) with ⟨r, hr⟩
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        have hs := hshift0 a b x (-x); simp only [add_neg_cancel] at hs; dsimp only at hr; rw [hr] at hs
        have hd : -x ∈ (O.compl hm).O a b := Finset.mem_compl.mpr fun h0 => by
          have := (hO a b 0 (-x)).mp h0; simp [← hs] at this
        fin_cases a
        · simp only [Fin.mk_zero] at hs; exact ⟨Sum.inl ⟨-x, hd⟩, by simp [φ1, ← hs]⟩
        · simp only [Fin.mk_one] at hs; exact ⟨Sum.inr ⟨-x, hd⟩, by simp [φ1, ← hs]⟩
    rw [hunified 0 0 L (stratumOf q L) hm O
      (fun a => Equiv.ofBijective _ (hr0_bij a))
      (fun a => Equiv.ofBijective _ (hr1_bij a))
      (fun b => Equiv.ofBijective _ (hc0_bij b))
      (fun b => Equiv.ofBijective _ (hc1_bij b))
      hL
      (fun a d hd => hmem0 a 0 d hd)
      (fun a d hd => hmem0 a 1 d hd)
      (fun a d hd => hmem1 a 0 d hd)
      (fun a d hd => hmem1 a 1 d hd)
      (fun b d hd => by
        have hs := hshift0 0 b (-d) d; simp only [neg_add_cancel] at hs
        rw [hs]; exact hmem0 0 b d hd)
      (fun b d hd => by
        have hs := hshift0 1 b (-d) d; simp only [neg_add_cancel] at hs
        rw [hs]; exact hmem0 1 b d hd)
      (fun b d hd => by
        have hs := hshift0 0 b (-d) d; simp only [neg_add_cancel] at hs
        rw [hs]; exact hmem1 0 b d hd)
      (fun b d hd => by
        have hs := hshift0 1 b (-d) d; simp only [neg_add_cancel] at hs
        rw [hs]; exact hmem1 1 b d hd)]
    rw [fixed_layer_sign_eq_one hq_odd O φ0 hr0_bij hc0_bij, one_mul]
    exact fixed_layer_sign_eq_one hq_odd (O.compl hm) φ1 hr1_bij hc1_bij
  · -- Part 2: `ℓ_B` (block `0` fixed, block `1` moving via `h1`)
    intro L m hm O h1 hL hdata
    have hshift0 : ∀ a b : Fin 2, ∀ x d : ZMod q, d ∈ O.O a b →
        L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
          L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) := by
      intro a b x d hd
      have hpow : ellB q ^ x.val ∈ Subgroup.zpowers (ellB q) :=
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      have hfix := (sylow_fix_entry_iff (ellB q ^ x.val) L).mp
        (hL (ellB q ^ x.val).1 ⟨ellB q ^ x.val, hpow, rfl⟩) a b 0 d
      have hvec : sylowToVec (ellB q ^ x.val) =
          (fun _ => x, fun _ => x, fun c => if c = 0 then 0 else x) := by
        have h1v : sylowToVec (ellB q) = (fun _ => 1, fun _ => 1, fun c => if c = 0 then 0 else 1) := by
          dsimp [ellB]; rw [sylowToVec_sylowElem]
          refine Prod.ext (funext fun i => by fin_cases i <;> rfl)
            (Prod.ext (funext fun i => by fin_cases i <;> rfl)
              (funext fun c => by fin_cases c <;> rfl))
        have hpow_v : ∀ n : ℕ, sylowToVec (ellB q ^ n) =
            (fun _ => (n : ZMod q), fun _ => (n : ZMod q), fun c => if c = 0 then 0 else (n : ZMod q)) := fun n => by
          induction n with
          | zero => simp [sylowToVec_one]; rfl
          | succ n ih =>
            rw [pow_succ, sylowToVec_mul, ih, h1v]
            refine Prod.ext (funext fun _ => by change (n : ZMod q) + 1 = _; push_cast; rfl)
              (Prod.ext (funext fun _ => by change (n : ZMod q) + 1 = _; push_cast; rfl)
                (funext fun c => by fin_cases c <;> simp))
        rw [hpow_v, ZMod.natCast_zmod_val]
      rw [hvec] at hfix
      dsimp only at hfix
      have h0 := (hdata a b 0 d).1.mp hd
      simp only [zero_add] at h0
      rw [h0] at hfix
      simp only [zero_add, ↓reduceIte, add_zero] at hfix
      rw [add_comm, hfix, ← h0, Prod.mk.eta, Equiv.apply_symm_apply]
    let φ0 : ∀ a b : Fin 2, O.O a b → ZMod q := fun a b d =>
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d.1)))).2
    have hmem0 : ∀ a b d (hd : d ∈ O.O a b),
        L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) = blockEquiv q (0, φ0 a b ⟨d, hd⟩) := by
      intro a b d hd
      have h0 := (hdata a b 0 d).1.mp hd; simp only [zero_add] at h0
      conv_lhs => rw [← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))]
      exact congrArg (blockEquiv q) (Prod.ext h0 rfl)
    have hr0_bij : ∀ a : Fin 2, Function.Bijective (fun s : O.O a 0 ⊕ O.O a 1 => Sum.elim (φ0 a 0) (φ0 a 1) s) := by
      intro a; refine ⟨?_, ?_⟩
      · rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₂)) by
              rw [hmem0 a 0 d₁ hd₁, hmem0 a 0 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective h)))
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₂)) by
              rw [hmem0 a 0 d₁ hd₁, hmem0 a 1 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) Fin.zero_ne_one
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, d₂)) by
              rw [hmem0 a 1 d₁ hd₁, hmem0 a 0 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) one_ne_zero
        · have h := (L.row_bijective (blockEquiv q (a, 0))).1
            (show L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₁)) =
                L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, d₂)) by
              rw [hmem0 a 1 d₁ hd₁, hmem0 a 1 d₂ hd₂]; exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective h)))
      · intro z
        rcases (L.row_bijective (blockEquiv q (a, 0))).2 (blockEquiv q (0, z)) with ⟨col, hcol⟩
        obtain ⟨⟨b, d⟩, rfl⟩ := (blockEquiv q).surjective col
        have hd : d ∈ O.O a b := (hdata a b 0 d).1.mpr (by simp [hcol])
        fin_cases b
        · simp only [Fin.mk_zero] at hcol; exact ⟨Sum.inl ⟨d, hd⟩, by simp [φ0, hcol]⟩
        · simp only [Fin.mk_one] at hcol; exact ⟨Sum.inr ⟨d, hd⟩, by simp [φ0, hcol]⟩
    have hc0_bij : ∀ b : Fin 2, Function.Bijective (fun s : O.O 0 b ⊕ O.O 1 b => Sum.elim (φ0 0 b) (φ0 1 b) s) := by
      intro b; refine ⟨?_, ?_⟩
      · rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 0 b (-d₁) d₁ hd₁; have s2 := hshift0 0 b (-d₂) d₂ hd₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 0 b d₁ hd₁, hmem0 0 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inl (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective h))))
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 0 b (-d₁) d₁ hd₁; have s2 := hshift0 1 b (-d₂) d₂ hd₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 0 b d₁ hd₁, hmem0 1 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) Fin.zero_ne_one
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 1 b (-d₁) d₁ hd₁; have s2 := hshift0 0 b (-d₂) d₂ hd₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 1 b d₁ hd₁, hmem0 0 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact absurd (congrArg Prod.fst ((blockEquiv q).injective h)) one_ne_zero
        · have h := (L.col_bijective (blockEquiv q (b, 0))).1
            (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
                L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) by
              have s1 := hshift0 1 b (-d₁) d₁ hd₁; have s2 := hshift0 1 b (-d₂) d₂ hd₂
              simp only [neg_add_cancel] at s1 s2
              rw [s1, s2, hmem0 1 b d₁ hd₁, hmem0 1 b d₂ hd₂]
              exact congrArg (fun z => blockEquiv q (0, z)) hEq)
          exact congrArg Sum.inr (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective h))))
      · intro z
        rcases (L.col_bijective (blockEquiv q (b, 0))).2 (blockEquiv q (0, z)) with ⟨r, hr⟩
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        have hd : -x ∈ O.O a b := (hdata a b x (-x)).1.mpr (by simp [hr])
        have hs := hshift0 a b x (-x) hd; simp only [add_neg_cancel] at hs; dsimp only at hr; rw [hr] at hs
        fin_cases a
        · simp only [Fin.mk_zero] at hs; exact ⟨Sum.inl ⟨-x, hd⟩, by simp [φ0, ← hs]⟩
        · simp only [Fin.mk_one] at hs; exact ⟨Sum.inr ⟨-x, hd⟩, by simp [φ0, ← hs]⟩
    rw [hunified 0 1 L m hm O
      (fun a => Equiv.ofBijective _ (hr0_bij a))
      (fun a => Equiv.ofBijective _ (h1.L1 a))
      (fun b => Equiv.ofBijective _ (hc0_bij b))
      (fun b => Equiv.ofBijective _ (h1.L2 b))
      hL
      (fun a d hd => hmem0 a 0 d hd)
      (fun a d hd => hmem0 a 1 d hd)
      (fun a d hd => by
        have h := (hdata a 0 0 d).2 hd; simp only [zero_add] at h
        rw [h]; rfl)
      (fun a d hd => by
        have h := (hdata a 1 0 d).2 hd; simp only [zero_add] at h
        rw [h]; rfl)
      (fun b d hd => by
        have hs := hshift0 0 b (-d) d hd; simp only [neg_add_cancel] at hs
        rw [hs]; exact hmem0 0 b d hd)
      (fun b d hd => by
        have hs := hshift0 1 b (-d) d hd; simp only [neg_add_cancel] at hs
        rw [hs]; exact hmem0 1 b d hd)
      (fun b d hd => by
        have h := (hdata 0 b (-d) d).2 hd; simp only [neg_add_cancel] at h
        rw [h]; congr 1; refine Prod.ext rfl ?_
        change -d + h1.h 0 b ⟨d, hd⟩ = h1.h 0 b ⟨d, hd⟩ - d; ring)
      (fun b d hd => by
        have h := (hdata 1 b (-d) d).2 hd; simp only [neg_add_cancel] at h
        rw [h]; congr 1; refine Prod.ext rfl ?_
        change -d + h1.h 1 b ⟨d, hd⟩ = h1.h 1 b ⟨d, hd⟩ - d; ring)]
    rw [fixed_layer_sign_eq_one hq_odd O φ0 hr0_bij hc0_bij, one_mul]
    rfl
  · -- Part 3: `ℓ_C` (both symbol blocks moving via `h0` and `h1`)
    intro L m hm O h0 h1 hL hdata
    rw [hunified 1 1 L m hm O
      (fun a => Equiv.ofBijective _ (h0.L1 a))
      (fun a => Equiv.ofBijective _ (h1.L1 a))
      (fun b => Equiv.ofBijective _ (h0.L2 b))
      (fun b => Equiv.ofBijective _ (h1.L2 b))
      hL
      (fun a d hd => by
        have h := (hdata a 0 0 d).1 hd; simp only [zero_add] at h
        rw [h]; rfl)
      (fun a d hd => by
        have h := (hdata a 1 0 d).1 hd; simp only [zero_add] at h
        rw [h]; rfl)
      (fun a d hd => by
        have h := (hdata a 0 0 d).2 hd; simp only [zero_add] at h
        rw [h]; rfl)
      (fun a d hd => by
        have h := (hdata a 1 0 d).2 hd; simp only [zero_add] at h
        rw [h]; rfl)
      (fun b d hd => by
        have h := (hdata 0 b (-d) d).1 hd; simp only [neg_add_cancel] at h
        rw [h]; congr 1; refine Prod.ext rfl ?_
        change -d + h0.h 0 b ⟨d, hd⟩ = h0.h 0 b ⟨d, hd⟩ - d; ring)
      (fun b d hd => by
        have h := (hdata 1 b (-d) d).1 hd; simp only [neg_add_cancel] at h
        rw [h]; congr 1; refine Prod.ext rfl ?_
        change -d + h0.h 1 b ⟨d, hd⟩ = h0.h 1 b ⟨d, hd⟩ - d; ring)
      (fun b d hd => by
        have h := (hdata 0 b (-d) d).2 hd; simp only [neg_add_cancel] at h
        rw [h]; congr 1; refine Prod.ext rfl ?_
        change -d + h1.h 0 b ⟨d, hd⟩ = h1.h 0 b ⟨d, hd⟩ - d; ring)
      (fun b d hd => by
        have h := (hdata 1 b (-d) d).2 hd; simp only [neg_add_cancel] at h
        rw [h]; congr 1; refine Prod.ext rfl ?_
        change -d + h1.h 1 b ⟨d, hd⟩ = h1.h 1 b ⟨d, hd⟩ - d; ring)]
    rfl

/-! ### Lemma 6.8: `S(⟨ℓ_0⟩)`, Mixed-Stratum Stabilizers, and Homogeneous Strata -/

/-- A nonempty proper subset of `ZMod q` (`q` prime) has trivial translation stabilizer. -/
lemma zmod_subset_add_eq_self_imp_zero {q : ℕ} [Fact q.Prime]
    {S : Finset (ZMod q)} (hpos : 0 < S.card) (hlt : S.card < q) {t : ZMod q}
    (ht : ∀ d : ZMod q, d ∈ S ↔ d + t ∈ S) : t = 0 := by
  by_contra hne
  rcases Finset.card_pos.mp hpos with ⟨d₀, hd₀⟩
  have hmem_mul : ∀ k : ℕ, d₀ + (k : ZMod q) * t ∈ S := fun k => by
    induction k with
    | zero => simpa using hd₀
    | succ k ih =>
      have := (ht _).mp ih
      convert this using 1; push_cast; ring
  have hall : S = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    let k : ZMod q := (x - d₀) * t⁻¹
    have hk := hmem_mul k.val
    rw [ZMod.natCast_zmod_val] at hk
    convert hk using 1
    dsimp [k]
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, add_sub_cancel]
  rw [hall, Finset.card_univ, ZMod.card] at hlt
  exact lt_irrefl _ hlt

/-- Helper: `sylowToVec (ℓ ^ n)` for `ℓ = sylowElem 1 1 1 1 w0 w1`. -/
private lemma sylowToVec_pow_1111 {q : ℕ} [NeZero q] (w0 w1 : ZMod q) (n : ℕ) :
    sylowToVec ((sylowElem q 1 1 1 1 w0 w1) ^ n) =
      (fun _ => (n : ZMod q), fun _ => (n : ZMod q),
       fun c => (n : ZMod q) * (if c = 0 then w0 else w1)) := by
  induction n with
  | zero => simp [sylowToVec_one]; rfl
  | succ n ih =>
    rw [pow_succ, sylowToVec_mul, ih, sylowToVec_sylowElem]
    refine Prod.ext (funext fun a => by fin_cases a <;> (change (n : ZMod q) + 1 = _; push_cast; rfl))
      (Prod.ext (funext fun b => by fin_cases b <;> (change (n : ZMod q) + 1 = _; push_cast; rfl))
        (funext fun c => by fin_cases c <;> (change (n : ZMod q) * _ + _ = _; push_cast; ring)))

private abbrev Dom0 (q : ℕ) [NeZero q] :=
  Σ Y : { Y : Finset (Fin (2 * q)) // Y.card = q },
    (ZMod q ≃ Y.1) × (ZMod q ≃ (Y.1ᶜ : Finset (Fin (2 * q)))) ×
    (ZMod q ≃ (Y.1ᶜ : Finset (Fin (2 * q)))) × (ZMod q ≃ Y.1)

private def mkSq0 {q : ℕ} [NeZero q] (t : Dom0 q) : LatinSquare (2 * q) :=
  { entry := fun r col =>
      let pr := (blockEquiv q).symm r
      let pc := (blockEquiv q).symm col
      if pr.1 = 0 ∧ pc.1 = 0 then (t.2.1 (pc.2 - pr.2)).1
      else if pr.1 = 0 ∧ pc.1 = 1 then (t.2.2.1 (pc.2 - pr.2)).1
      else if pr.1 = 1 ∧ pc.1 = 0 then (t.2.2.2.1 (pc.2 - pr.2)).1
      else (t.2.2.2.2 (pc.2 - pr.2)).1
    row_bijective := fun r => by
      rw [← Finite.injective_iff_bijective]
      intro c₁ c₂ hEq
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective c₁
      obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective c₂
      simp only [Equiv.symm_apply_apply] at hEq
      fin_cases a <;> fin_cases b₁ <;> fin_cases b₂ <;> simp at hEq
      · congr 1; exact Prod.ext rfl hEq
      · exact (Finset.mem_compl.mp (t.2.2.1 (y₂ - x)).2 (hEq ▸ (t.2.1 (y₁ - x)).2)).elim
      · exact (Finset.mem_compl.mp (t.2.2.1 (y₁ - x)).2 (hEq.symm ▸ (t.2.1 (y₂ - x)).2)).elim
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl hEq
      · exact (Finset.mem_compl.mp (t.2.2.2.1 (y₁ - x)).2 (hEq.symm ▸ (t.2.2.2.2 (y₂ - x)).2)).elim
      · exact (Finset.mem_compl.mp (t.2.2.2.1 (y₂ - x)).2 (hEq ▸ (t.2.2.2.2 (y₁ - x)).2)).elim
      · congr 1; exact Prod.ext rfl hEq
    col_bijective := fun col => by
      rw [← Finite.injective_iff_bijective]
      intro r₁ r₂ hEq
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
      obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
      simp only [Equiv.symm_apply_apply] at hEq
      fin_cases b <;> fin_cases a₁ <;> fin_cases a₂ <;> simp at hEq
      · congr 1; exact Prod.ext rfl hEq
      · exact (Finset.mem_compl.mp (t.2.2.2.1 (y - x₂)).2 (hEq ▸ (t.2.1 (y - x₁)).2)).elim
      · exact (Finset.mem_compl.mp (t.2.2.2.1 (y - x₁)).2 (hEq.symm ▸ (t.2.1 (y - x₂)).2)).elim
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl hEq
      · exact (Finset.mem_compl.mp (t.2.2.1 (y - x₁)).2 (hEq.symm ▸ (t.2.2.2.2 (y - x₂)).2)).elim
      · exact (Finset.mem_compl.mp (t.2.2.1 (y - x₂)).2 (hEq ▸ (t.2.2.2.2 (y - x₁)).2)).elim
      · congr 1; exact Prod.ext rfl hEq }

private lemma lem_6_8_partA (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    S_twoq q (Subgroup.zpowers (ell0 q)) = ((2 * q).choose q : ℤ) * (q.factorial : ℤ) ^ 4 ∧
    S_twoq q (Subgroup.zpowers (ell0 q)) = ((2 * q).factorial : ℤ) * (q.factorial : ℤ) ^ 2 ∧
    ∀ L : LatinSquare (2 * q),
      L ∈ fixSet ((Subgroup.zpowers (ell0 q)).map (sylowP q).subtype) → squareSign L = 1 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hfac := lem_6_7_factor q hq hodd
  have heven := hfac.1
  have hcount : S_twoq q (Subgroup.zpowers (ell0 q)) =
      ((2 * q).choose q : ℤ) * (q.factorial : ℤ) ^ 4 := by
      unfold S_twoq signedFixSum
      have h1 : ∀ L ∈ Finset.univ.filter (fun L : LatinSquare (2 * q) =>
          L ∈ fixSet ((Subgroup.zpowers (ell0 q)).map (sylowP q).subtype)),
          (squareSign L : ℤ) = 1 := fun L hL => by
        rw [heven L (Finset.mem_filter.mp hL).2]; rfl
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard_bij : (Finset.univ.filter (fun L : LatinSquare (2 * q) =>
          L ∈ fixSet ((Subgroup.zpowers (ell0 q)).map (sylowP q).subtype))).card =
          Fintype.card (Dom0 q) := by
        symm
        refine Finset.card_bij (fun t _ => mkSq0 t) ?_ ?_ ?_
        · intro t _
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rintro _ ⟨g, hg, rfl⟩
          change g.1 • mkSq0 t = mkSq0 t
          rw [sylow_fix_entry_iff]
          rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
          have hk : ∃ n : ℕ, ell0 q ^ k = ell0 q ^ n := by
            have hord : ell0 q ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 (ell0 q) trivial
            refine ⟨(k % (q : ℤ)).toNat, ?_⟩
            have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
            have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
            conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
            rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
          rcases hk with ⟨n, hn⟩
          rw [hn, show ell0 q = sylowElem q 1 1 1 1 0 0 from rfl, sylowToVec_pow_1111 0 0 n]
          intro a b x y
          dsimp only [mkSq0]; simp only [Equiv.symm_apply_apply]
          have hsub : y + (n : ZMod q) - (x + (n : ZMod q)) = y - x := by ring
          fin_cases a <;> fin_cases b <;> simp [hsub]
        · intro t₁ _ t₂ _ hEq
          have hent : ∀ a b d, (mkSq0 t₁).entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) =
              (mkSq0 t₂).entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) := fun a b d =>
            congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d))) hEq
          have hYeq : t₁.1 = t₂.1 := by
            apply Subtype.ext; ext s
            constructor
            · intro hs
              obtain ⟨d, hd⟩ := t₁.2.1.surjective ⟨s, hs⟩
              have h00 := hent 0 0 d
              simp only [mkSq0, Equiv.symm_apply_apply, Fin.isValue, and_self, ↓reduceIte,
                sub_zero] at h00
              rw [hd] at h00; dsimp only at h00; rw [h00]; exact (t₂.2.1 d).2
            · intro hs
              obtain ⟨d, hd⟩ := t₂.2.1.surjective ⟨s, hs⟩
              have h00 := hent 0 0 d
              simp only [mkSq0, Equiv.symm_apply_apply, Fin.isValue, and_self, ↓reduceIte,
                sub_zero] at h00
              rw [hd] at h00; dsimp only at h00; rw [← h00]; exact (t₁.2.1 d).2
          rcases t₁ with ⟨Y₁, f00₁, f01₁, f10₁, f11₁⟩
          rcases t₂ with ⟨Y₂, f00₂, f01₂, f10₂, f11₂⟩
          dsimp only at hYeq; subst hYeq
          congr 1
          refine Prod.ext (Equiv.ext fun d => Subtype.ext (by simpa [mkSq0] using hent 0 0 d))
            (Prod.ext (Equiv.ext fun d => Subtype.ext (by simpa [mkSq0] using hent 0 1 d))
              (Prod.ext (Equiv.ext fun d => Subtype.ext (by simpa [mkSq0] using hent 1 0 d))
                (Equiv.ext fun d => Subtype.ext (by simpa [mkSq0] using hent 1 1 d))))
        · intro L hL
          have hLfix := (Finset.mem_filter.mp hL).2
          have hshift : ∀ a b x y, L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
              L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)) := by
            intro a b x y
            have hpow : ell0 q ^ x.val ∈ Subgroup.zpowers (ell0 q) :=
              Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
            have hfix := (sylow_fix_entry_iff (ell0 q ^ x.val) L).mp
              (hLfix (ell0 q ^ x.val).1 ⟨ell0 q ^ x.val, hpow, rfl⟩) a b 0 (y - x)
            rw [show ell0 q = sylowElem q 1 1 1 1 0 0 from rfl, sylowToVec_pow_1111 0 0 x.val,
              ZMod.natCast_zmod_val] at hfix
            have hL0 := (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)))
            simpa [zero_add, sub_add_cancel, hL0] using hfix
          let f : Fin 2 → Fin 2 → ZMod q → Fin (2 * q) := fun a b d =>
            L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d))
          have hfinj : ∀ a b, Function.Injective (f a b) := fun a b d₁ d₂ hEq => by
            have := (L.row_bijective (blockEquiv q (a, 0))).1 hEq
            exact congrArg Prod.snd ((blockEquiv q).injective this)
          let Y : Finset (Fin (2 * q)) := Finset.univ.image (f 0 0)
          have hYc : Y.card = q := by
            dsimp [Y]; rw [Finset.card_image_of_injective _ (hfinj 0 0), Finset.card_univ, ZMod.card]
          have himg01 : Finset.univ.image (f 0 1) = Yᶜ := by
            ext s; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, Y]
            constructor
            · rintro ⟨d₁, rfl⟩ ⟨d₂, hEq⟩
              exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective
                ((L.row_bijective (blockEquiv q (0, 0))).1 hEq)))
            · intro hs
              rcases (L.row_bijective (blockEquiv q (0, 0))).2 s with ⟨col, hcol⟩
              obtain ⟨⟨b, d⟩, rfl⟩ := (blockEquiv q).surjective col
              fin_cases b
              · exact (hs ⟨d, hcol⟩).elim
              · exact ⟨d, hcol⟩
          have himg10 : Finset.univ.image (f 1 0) = Yᶜ := by
            ext s; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, Y]
            constructor
            · rintro ⟨d₁, rfl⟩ ⟨d₂, hEq⟩
              have h1 := hshift 1 0 (-d₁) 0; have h2 := hshift 0 0 (-d₂) 0
              simp only [zero_sub, neg_neg] at h1 h2
              have hcol := (L.col_bijective (blockEquiv q (0, 0))).1
                (show L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (0, 0)) =
                    L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (0, 0)) by
                  rw [h1, h2]; exact hEq.symm)
              exact one_ne_zero (congrArg Prod.fst ((blockEquiv q).injective hcol))
            · intro hs
              rcases (L.col_bijective (blockEquiv q (0, 0))).2 s with ⟨r, hr⟩
              obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
              dsimp only at hr
              rw [hshift a 0 x 0, zero_sub] at hr
              fin_cases a
              · exact (hs ⟨-x, hr⟩).elim
              · exact ⟨-x, hr⟩
          have himg11 : Finset.univ.image (f 1 1) = Y := by
            ext s; simp only [Finset.mem_image, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨d₁, rfl⟩
              by_contra hs
              have hsc : f 1 1 d₁ ∈ Yᶜ := Finset.mem_compl.mpr hs
              rw [← himg10] at hsc
              rcases Finset.mem_image.mp hsc with ⟨d₂, _, hEq⟩
              exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective
                ((L.row_bijective (blockEquiv q (1, 0))).1 hEq)))
            · intro hs
              rcases (L.row_bijective (blockEquiv q (1, 0))).2 s with ⟨col, hcol⟩
              obtain ⟨⟨b, d⟩, rfl⟩ := (blockEquiv q).surjective col
              fin_cases b
              · exfalso
                have hsc : s ∈ Yᶜ := by rw [← himg10]; exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hcol⟩
                exact Finset.mem_compl.mp hsc hs
              · exact ⟨d, hcol⟩
          let e00 : ZMod q ≃ Y := Equiv.ofBijective (fun d => ⟨f 0 0 d, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
            ⟨fun x y h => hfinj 0 0 (congrArg Subtype.val h),
             fun ⟨s, hs⟩ => by rcases Finset.mem_image.mp hs with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
          let e01 : ZMod q ≃ (Yᶜ : Finset (Fin (2 * q))) := Equiv.ofBijective
            (fun d => ⟨f 0 1 d, by rw [← himg01]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
            ⟨fun x y h => hfinj 0 1 (congrArg Subtype.val h),
             fun ⟨s, hs⟩ => by rw [← himg01] at hs; rcases Finset.mem_image.mp hs with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
          let e10 : ZMod q ≃ (Yᶜ : Finset (Fin (2 * q))) := Equiv.ofBijective
            (fun d => ⟨f 1 0 d, by rw [← himg10]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
            ⟨fun x y h => hfinj 1 0 (congrArg Subtype.val h),
             fun ⟨s, hs⟩ => by rw [← himg10] at hs; rcases Finset.mem_image.mp hs with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
          let e11 : ZMod q ≃ Y := Equiv.ofBijective
            (fun d => ⟨f 1 1 d, by rw [← himg11]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
            ⟨fun x y h => hfinj 1 1 (congrArg Subtype.val h),
             fun ⟨s, hs⟩ => by rw [← himg11] at hs; rcases Finset.mem_image.mp hs with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
          refine ⟨⟨⟨Y, hYc⟩, e00, e01, e10, e11⟩, Finset.mem_univ _, ?_⟩
          ext r col
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
          rw [hshift a b x y]
          fin_cases a <;> fin_cases b <;>
            (simp only [mkSq0, Fin.mk_zero, Fin.mk_one, Fin.isValue, and_self, Fin.zero_ne_one,
              one_ne_zero, and_false, false_and, ↓reduceIte, Equiv.symm_apply_apply]; rfl)
      rw [hcard_bij]
      have hcardDom : Fintype.card (Dom0 q) = (2 * q).choose q * q.factorial ^ 4 := by
        dsimp only [Dom0]
        rw [Fintype.card_sigma]
        have hfib : ∀ Y : { Y : Finset (Fin (2 * q)) // Y.card = q },
            Fintype.card ((ZMod q ≃ Y.1) × (ZMod q ≃ (Y.1ᶜ : Finset (Fin (2 * q)))) ×
              (ZMod q ≃ (Y.1ᶜ : Finset (Fin (2 * q)))) × (ZMod q ≃ Y.1)) = q.factorial ^ 4 := by
          intro ⟨Y, hYc⟩
          have hYcc : Yᶜ.card = q := by simp [Finset.card_compl, Fintype.card_fin, hYc]; omega
          have h1 : Fintype.card (ZMod q ≃ Y) = q.factorial := by
            rw [Fintype.card_equiv (Fintype.equivOfCardEq (by rw [ZMod.card, Fintype.card_coe, hYc])),
              ZMod.card]
          have h2 : Fintype.card (ZMod q ≃ (Yᶜ : Finset (Fin (2 * q)))) = q.factorial := by
            rw [Fintype.card_equiv (Fintype.equivOfCardEq (by rw [ZMod.card, Fintype.card_coe, hYcc])),
              ZMod.card]
          simp only [Fintype.card_prod, h1, h2]; ring
        simp_rw [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have hsub : Fintype.card { Y : Finset (Fin (2 * q)) // Y.card = q } = (2 * q).choose q := by
          rw [Fintype.card_subtype]
          have hpow : Finset.univ.filter (fun Y : Finset (Fin (2 * q)) => Y.card = q) =
              Finset.powersetCard q (Finset.univ : Finset (Fin (2 * q))) := by
            ext Y; simp [Finset.mem_powersetCard]
          rw [hpow, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        rw [hsub]
      rw [hcardDom]; push_cast; rfl
  have hcount2 : S_twoq q (Subgroup.zpowers (ell0 q)) =
      ((2 * q).factorial : ℤ) * (q.factorial : ℤ) ^ 2 := by
    rw [hcount]
    have hch := Nat.choose_mul_factorial_mul_factorial (show q ≤ 2 * q by omega)
    have h2q : 2 * q - q = q := by omega
    rw [h2q] at hch
    have hchZ : ((2 * q).choose q : ℤ) * (q.factorial : ℤ) * (q.factorial : ℤ) =
        ((2 * q).factorial : ℤ) := by exact_mod_cast hch
    calc ((2 * q).choose q : ℤ) * (q.factorial : ℤ) ^ 4
        = (((2 * q).choose q : ℤ) * (q.factorial : ℤ) * (q.factorial : ℤ)) *
            (q.factorial : ℤ) ^ 2 := by ring
      _ = ((2 * q).factorial : ℤ) * (q.factorial : ℤ) ^ 2 := by rw [hchZ]
  exact ⟨hcount, hcount2, heven⟩

private lemma lem_6_8_partB (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    ∀ ℓ ∈ ({ellB q, ellC q} : Finset (sylowP q)),
      ∀ L : LatinSquare (2 * q),
        L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) →
        0 < stratumOf q L → stratumOf q L < q →
        ∀ g : sylowP q, g.1 • L = L ↔ g ∈ Subgroup.zpowers ℓ := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    intro ℓ hℓ L hL hm0 hmq g
    constructor
    · intro hgL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
      let wℓ : Fin 2 → ZMod q := if ℓ = ellB q then fun c => if c = 0 then 0 else 1 else fun _ => 1
      have hℓ_eq : ℓ = sylowElem q 1 1 1 1 (wℓ 0) (wℓ 1) := by
        rcases hℓ with rfl | rfl
        · dsimp only [wℓ]; simp only [↓reduceIte, one_ne_zero]; rfl
        · have hne : ellC q ≠ ellB q := fun h => by
            have := congrArg (fun x => (sylowToVec x).2.2 0) h
            simp [ellC, ellB, sylowToVec_sylowElem] at this
          dsimp only [wℓ]; simp only [hne, ↓reduceIte]; rfl
      have hL' : L ∈ fixSet ((Subgroup.zpowers (sylowElem q 1 1 1 1 (wℓ 0) (wℓ 1))).map (sylowP q).subtype) :=
        hℓ_eq ▸ hL
      obtain ⟨hmle, O, hO⟩ := pattern_of_fix_rankone wℓ L hL'
      let u := (sylowToVec g).1
      let v := (sylowToVec g).2.1
      let w := (sylowToVec g).2.2
      -- `g` preserves `O.O a b` under translation by `v b - u a`
      have hO_inv : ∀ a b d, d ∈ O.O a b ↔ d + (v b - u a) ∈ O.O a b := by
        intro a b d
        have hg := (sylow_fix_entry_iff g L).mp hgL a b 0 d
        have h1 := (hO a b 0 d)
        have h2 := (hO a b (u a) (d + (v b - u a)))
        have hsum : u a + (d + (v b - u a)) = d + v b := by ring
        rw [zero_add] at h1; rw [hsum] at h2
        rw [h1, h2]
        have hsym : ((blockEquiv q).symm (L.entry (blockEquiv q (a, u a)) (blockEquiv q (b, d + v b)))).1 =
            ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 := by
          have := congrArg (fun k => ((blockEquiv q).symm k).1) hg
          simpa [u, v, zero_add] using this
        rw [hsym]
      have huv : ∀ a b : Fin 2, v b = u a := by
        intro a b
        have hpos : 0 < (O.O a b).card := by
          fin_cases a <;> fin_cases b <;> simp [O.card_00, O.card_01, O.card_10, O.card_11] <;> omega
        have hlt : (O.O a b).card < q := by
          fin_cases a <;> fin_cases b <;> simp [O.card_00, O.card_01, O.card_10, O.card_11] <;> omega
        have h0 := zmod_subset_add_eq_self_imp_zero hpos hlt (hO_inv a b)
        exact sub_eq_zero.mp h0
      let s₀ : ZMod q := u 0
      have hu : u = fun _ => s₀ := funext fun a => by
        fin_cases a
        · rfl
        · exact (huv 1 0).symm.trans (huv 0 0)
      have hv : v = fun _ => s₀ := funext fun b => huv 0 b
      -- Shift formula for `ℓ`
      have hshift : ∀ a b x d, L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
          blockEquiv q (((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1,
            ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 +
              wℓ ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 * x) := by
        intro a b x d
        have hpow : ℓ ^ x.val ∈ Subgroup.zpowers ℓ := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
        have hfix := (sylow_fix_entry_iff (ℓ ^ x.val) L).mp (hL (ℓ ^ x.val).1 ⟨ℓ ^ x.val, hpow, rfl⟩)
          a b 0 d
        rw [hℓ_eq, sylowToVec_pow_1111, ZMod.natCast_zmod_val] at hfix
        have hwℓ : ∀ c : Fin 2, (if c = 0 then wℓ 0 else wℓ 1) = wℓ c := fun c => by fin_cases c <;> rfl
        simpa [zero_add, add_comm, hwℓ, mul_comm] using hfix
      -- Determine `w 1 = s₀` (using any `d ∈ (O.O 0 0)ᶜ`, which is nonempty since `m < q`)
      have hO00c_pos : 0 < (O.O 0 0)ᶜ.card := by
        simp [Finset.card_compl, ZMod.card, O.card_00]; omega
      rcases Finset.card_pos.mp hO00c_pos with ⟨d₁, hd₁⟩
      have hc1 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d₁)))).1 = 1 := by
        have h0 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d₁)))).1 ≠ 0 :=
          fun h => Finset.mem_compl.mp hd₁ ((hO 0 0 0 d₁).mpr (by simpa using h))
        generalize ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d₁)))).1 = c at h0 ⊢
        fin_cases c; exact (h0 rfl).elim; rfl
      have hw1 : w 1 = s₀ := by
        have hg := (sylow_fix_entry_iff g L).mp hgL 0 0 0 d₁
        dsimp only at hg
        have hs := hshift 0 0 s₀ d₁
        have hu0 : (sylowToVec g).1 0 = s₀ := congrFun hu 0
        have hv0 : (sylowToVec g).2.1 0 = s₀ := congrFun hv 0
        rw [hu0, hv0, zero_add, add_comm d₁ s₀] at hg
        rw [hs, hc1] at hg
        have hwℓ1 : wℓ 1 = 1 := by dsimp [wℓ]; split_ifs <;> rfl
        have h2 := congrArg Prod.snd ((blockEquiv q).injective hg)
        simp only [hwℓ1, one_mul] at h2
        dsimp only [w]; linear_combination h2.symm
      -- Determine `w 0 = wℓ 0 * s₀`
      have hw0 : w 0 = wℓ 0 * s₀ := by
        rcases hℓ with rfl | rfl
        · -- `ℓ = ellB`: `wℓ 0 = 0`, pick `d₀ ∈ O.O 0 0` (nonempty since `m > 0`)
          have hwℓ0 : wℓ 0 = 0 := by simp [wℓ]
          rw [hwℓ0, zero_mul]
          rcases Finset.card_pos.mp (by rw [O.card_00]; exact hm0) with ⟨d₀, hd₀⟩
          have hg := (sylow_fix_entry_iff g L).mp hgL 0 0 0 d₀
          dsimp only at hg
          have hs := hshift 0 0 s₀ d₀
          have hu0 : (sylowToVec g).1 0 = s₀ := congrFun hu 0
          have hv0 : (sylowToVec g).2.1 0 = s₀ := congrFun hv 0
          rw [hu0, hv0, zero_add, add_comm d₀ s₀, hs] at hg
          have hc0 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d₀)))).1 = 0 := by
            simpa using (hO 0 0 0 d₀).mp hd₀
          rw [hc0, hwℓ0, zero_mul, add_zero] at hg
          have h2 := congrArg Prod.snd ((blockEquiv q).injective hg)
          dsimp only [w]; linear_combination h2.symm
        · -- `ℓ = ellC`: `wℓ 0 = 1`, pick `d₀ ∈ O.O 0 0` (nonempty since `m > 0`)
          have hne : ellC q ≠ ellB q := fun h => by
            have := congrArg (fun x => (sylowToVec x).2.2 0) h
            simp [ellC, ellB, sylowToVec_sylowElem] at this
          have hwℓ0 : wℓ 0 = 1 := by simp [wℓ, hne]
          rcases Finset.card_pos.mp (by rw [O.card_00]; exact hm0) with ⟨d₀, hd₀⟩
          have hc0 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d₀)))).1 = 0 := by
            simpa using (hO 0 0 0 d₀).mp hd₀
          have hg := (sylow_fix_entry_iff g L).mp hgL 0 0 0 d₀
          dsimp only at hg
          have hs := hshift 0 0 s₀ d₀
          have hu0 : (sylowToVec g).1 0 = s₀ := congrFun hu 0
          have hv0 : (sylowToVec g).2.1 0 = s₀ := congrFun hv 0
          rw [hu0, hv0, zero_add, add_comm d₀ s₀, hs, hc0, hwℓ0, one_mul] at hg
          have h2 := congrArg Prod.snd ((blockEquiv q).injective hg)
          rw [hwℓ0, one_mul]; dsimp only [w]; linear_combination h2.symm
      -- Conclude `g = ℓ ^ s₀.val ∈ Subgroup.zpowers ℓ`!
      have hg_eq : g = ℓ ^ s₀.val := by
        apply sylowToVec_injective
        rw [hℓ_eq, sylowToVec_pow_1111, ZMod.natCast_zmod_val]
        refine Prod.ext hu (Prod.ext hv (funext fun c => ?_))
        fin_cases c
        · simp [w, hw0, mul_comm]
        · have hwℓ1 : wℓ 1 = 1 := by dsimp [wℓ]; split_ifs <;> rfl
          simp [w, hw1, hwℓ1]
      rw [hg_eq]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ℓ) _
    · intro hg
      exact hL g.1 ⟨g, hg, rfl⟩

open Classical in
private lemma lem_6_8_homog_sym (q : ℕ) [NeZero q] (hq : q.Prime) :
    ∀ ℓ ∈ ({ellB q, ellC q} : Finset (sylowP q)),
      homogStrataSum q ℓ =
        2 * ∑ L ∈ (Finset.univ : Finset (LatinSquare (2 * q))).filter
            (fun L => L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) ∧ stratumOf q L = q),
          (squareSign L : ℤ) := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    intro ℓ hℓ
    let F := (Finset.univ : Finset (LatinSquare (2 * q))).filter
      (fun L => L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype))
    have hsplit : homogStrataSum q ℓ =
        (∑ L ∈ F.filter (fun L => stratumOf q L = 0), (squareSign L : ℤ)) +
        (∑ L ∈ F.filter (fun L => stratumOf q L = q), (squareSign L : ℤ)) := by
      unfold homogStrataSum
      rw [← Finset.sum_union]
      · congr 1; ext L; simp only [F, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      · rw [Finset.disjoint_left]; intro L h1 h2
        have e1 := (Finset.mem_filter.mp h1).2; have e2 := (Finset.mem_filter.mp h2).2
        have := hq.ne_zero; omega
    rw [hsplit]
    let σ : Isotopy (2 * q) := (1, blockSwapPerm q, 1)
    have hcomm : σ * ℓ.1 = ℓ.1 * σ := by
      have h1 : ∀ g : sylowP q, (sylowToVec g).2.1 0 = (sylowToVec g).2.1 1 →
          σ * g.1 = g.1 * σ := fun g hv => by
        have hval := sylowToVec_val g
        have hconj := blockSwapPerm_conj_blockTransPerm (sylowToVec g).2.1
        have hfeq : (fun b : Fin 2 => (sylowToVec g).2.1 (1 - b)) = (sylowToVec g).2.1 := by
          ext b; fin_cases b; exact hv.symm; exact hv
        rw [hfeq] at hconj
        have hmul : blockSwapPerm q * blockTransPerm q (sylowToVec g).2.1 =
            blockTransPerm q (sylowToVec g).2.1 * blockSwapPerm q := by
          have := congrArg (· * blockSwapPerm q) hconj
          simpa [mul_assoc] using this
        rw [hval]
        change (1 * blockTransPerm q (sylowToVec g).1,
            blockSwapPerm q * blockTransPerm q (sylowToVec g).2.1,
            1 * blockTransPerm q (sylowToVec g).2.2) =
          (blockTransPerm q (sylowToVec g).1 * 1,
            blockTransPerm q (sylowToVec g).2.1 * blockSwapPerm q,
            blockTransPerm q (sylowToVec g).2.2 * 1)
        simp [hmul]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
      rcases hℓ with rfl | rfl <;> exact h1 _ (by simp [ellB, ellC, sylowToVec_sylowElem])
    have hσ_fix : ∀ L : LatinSquare (2 * q), L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) →
        σ • L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) := by
      intro L hL
      rintro _ ⟨g, hg, rfl⟩
      rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
      have hk : σ * (ℓ ^ k).1 = (ℓ ^ k).1 * σ := by
        have : ∀ m : ℤ, σ * ℓ.1 ^ m = ℓ.1 ^ m * σ := fun m => Commute.zpow_right hcomm m
        simpa using this k
      change (ℓ ^ k).1 • (σ • L) = σ • L
      rw [← mul_smul, ← hk, mul_smul, hL (ℓ ^ k).1 ⟨ℓ ^ k, hg, rfl⟩]
    have hσ_strat : ∀ L, L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) →
        stratumOf q (σ • L) = q - stratumOf q L := by
      intro L hL
      simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
      let wℓ : Fin 2 → ZMod q := if ℓ = ellB q then fun c => if c = 0 then 0 else 1 else fun _ => 1
      have hℓ_eq : ℓ = sylowElem q 1 1 1 1 (wℓ 0) (wℓ 1) := by
        rcases hℓ with rfl | rfl
        · dsimp only [wℓ]; simp only [↓reduceIte, one_ne_zero]; rfl
        · have hne : ellC q ≠ ellB q := fun h => by
            have := congrArg (fun x => (sylowToVec x).2.2 0) h
            simp [ellC, ellB, sylowToVec_sylowElem] at this
          dsimp only [wℓ]; simp only [hne, ↓reduceIte]; rfl
      obtain ⟨_, O, hO⟩ := pattern_of_fix_rankone wℓ L (hℓ_eq ▸ hL)
      have hσ_entry : ∀ d : ZMod q, (σ • L).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)) =
          L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, d)) := fun d => by
        change L.entry (blockEquiv q (0, 0)) ((blockSwapPerm q).symm (blockEquiv q (0, d))) = _
        congr 1; simp [blockSwapPerm]
      have hset : (Finset.univ.filter fun d : ZMod q =>
          ((blockEquiv q).symm ((σ • L).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)))).1 = 0) =
          O.O 0 1 := by
        ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ_entry]
        have h := hO 0 1 0 d; rw [zero_add] at h; exact h.symm
      change (Finset.univ.filter fun d : ZMod q =>
          ((blockEquiv q).symm ((σ • L).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)))).1 = 0).card =
        q - stratumOf q L
      rw [hset, O.card_01]
    have hσ_inv : ∀ L : LatinSquare (2 * q), σ • (σ • L) = L := fun L => by
      rw [← mul_smul]
      have hσ2 : σ * σ = 1 := by
        refine Prod.ext (by simp [σ]) (Prod.ext ?_ (by simp [σ]))
        apply Equiv.Perm.ext; intro k
        change blockSwapPerm q (blockSwapPerm q k) = k
        obtain ⟨⟨b, x⟩, rfl⟩ := (blockEquiv q).surjective k
        simp only [blockSwapPerm, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_fn_mk]
        congr 1; exact Prod.ext (by fin_cases b <;> rfl) rfl
      rw [hσ2, one_smul]
    have hbij0q :
        (∑ L ∈ F.filter (fun L => stratumOf q L = 0), (squareSign L : ℤ)) =
        (∑ L ∈ F.filter (fun L => stratumOf q L = q), (squareSign L : ℤ)) := by
      refine Finset.sum_bij (fun L _ => σ • L) ?_ ?_ ?_ ?_
      · intro L hL
        have hLf := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
        have hLs := (Finset.mem_filter.mp hL).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ_fix L hLf⟩, ?_⟩
        rw [hσ_strat L hLf, hLs, Nat.sub_zero]
      · intro L₁ _ L₂ _ hEq
        have := congrArg (fun M : LatinSquare (2 * q) => σ • M) hEq; rwa [hσ_inv, hσ_inv] at this
      · intro L hL
        have hLf := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
        have hLs := (Finset.mem_filter.mp hL).2
        refine ⟨σ • L, ?_, hσ_inv L⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ_fix L hLf⟩, ?_⟩
        rw [hσ_strat L hLf, hLs, Nat.sub_self]
      · intro L _
        rw [squareSign_isotopyAct_even (even_two_mul q)]
    rw [hbij0q]
    have hfilt_eq : F.filter (fun L => stratumOf q L = q) =
        (Finset.univ : Finset (LatinSquare (2 * q))).filter
          (fun L => L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) ∧ stratumOf q L = q) := by
      ext L; simp [F]
    rw [hfilt_eq]; ring

private abbrev CMq (q : ℕ) [NeZero q] := { h : Equiv.Perm (ZMod q) // IsCompleteMap h }
private abbrev DomB (q : ℕ) [NeZero q] := Equiv.Perm (ZMod q) × Equiv.Perm (ZMod q) × CMq q × CMq q

private def mkB {q : ℕ} [NeZero q] (t : DomB q) : LatinSquare (2 * q) :=
  { entry := fun r col =>
      let pr := (blockEquiv q).symm r
      let pc := (blockEquiv q).symm col
      if pr.1 = 0 ∧ pc.1 = 0 then blockEquiv q (0, t.1 (pc.2 - pr.2))
      else if pr.1 = 1 ∧ pc.1 = 1 then blockEquiv q (0, t.2.1 (pc.2 - pr.2))
      else if pr.1 = 0 ∧ pc.1 = 1 then blockEquiv q (1, pr.2 + t.2.2.1.1 (pc.2 - pr.2))
      else blockEquiv q (1, pr.2 + t.2.2.2.1 (pc.2 - pr.2))
    row_bijective := fun r => by
      rw [← Finite.injective_iff_bijective]
      intro c₁ c₂ hEq
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective c₁
      obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective c₂
      simp only [Equiv.symm_apply_apply] at hEq
      fin_cases a <;> fin_cases b₁ <;> fin_cases b₂ <;> simp at hEq
      · congr 1; exact Prod.ext rfl (by linear_combination hEq)
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl (by linear_combination hEq)
    col_bijective := fun col => by
      rw [← Finite.injective_iff_bijective]
      intro r₁ r₂ hEq
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
      obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
      simp only [Equiv.symm_apply_apply] at hEq
      fin_cases b <;> fin_cases a₁ <;> fin_cases a₂ <;> simp at hEq
      · congr 1; exact Prod.ext rfl hEq
      · have hsub : t.2.2.2.1 (y - x₁) - (y - x₁) = t.2.2.2.1 (y - x₂) - (y - x₂) := by
          linear_combination hEq
        have := t.2.2.2.2.1 hsub; congr 1; exact Prod.ext rfl (by linear_combination -this)
      · have hsub : t.2.2.1.1 (y - x₁) - (y - x₁) = t.2.2.1.1 (y - x₂) - (y - x₂) := by
          linear_combination hEq
        have := t.2.2.1.2.1 hsub; congr 1; exact Prod.ext rfl (by linear_combination -this)
      · congr 1; exact Prod.ext rfl hEq }

private lemma mkB_fix {q : ℕ} [NeZero q] (hq : q.Prime) (t : DomB q) :
    mkB t ∈ fixSet ((Subgroup.zpowers (ellB q)).map (sylowP q).subtype) := by
  have : Fact q.Prime := ⟨hq⟩
  rintro _ ⟨g, hg, rfl⟩
  change g.1 • mkB t = mkB t; rw [sylow_fix_entry_iff]
  rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
  have hk : ∃ n : ℕ, ellB q ^ k = ellB q ^ n := by
    have hord : ellB q ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 (ellB q) trivial
    refine ⟨(k % (q : ℤ)).toNat, ?_⟩
    have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
    have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
    conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  rcases hk with ⟨n, hn⟩; rw [hn, show ellB q = sylowElem q 1 1 1 1 0 1 from rfl, sylowToVec_pow_1111 0 1 n]
  intro a b x y; dsimp only [mkB]; simp only [Equiv.symm_apply_apply]
  have hsub : y + (n : ZMod q) - (x + (n : ZMod q)) = y - x := by ring
  fin_cases a <;> fin_cases b <;> simp [hsub] <;> ring

private lemma mkB_sign {q : ℕ} [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) (t : DomB q) :
    (squareSign (mkB t) : ℤ) =
      (Equiv.Perm.sign t.2.2.1.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.2.2.1.1 x - x) t.2.2.1.2) : ℤ) *
      (Equiv.Perm.sign t.2.2.2.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.2.2.2.1 x - x) t.2.2.2.2) : ℤ) := by
  have : Fact q.Prime := ⟨hq⟩
  have hfix := mkB_fix hq t
  have hrow_mv : ∀ a : Fin 2, ∃ g ∈ Subgroup.zpowers (ellB q), (sylowToVec g).1 a ≠ 0 := fun a =>
    ⟨ellB q, Subgroup.mem_zpowers _, by dsimp [ellB]; rw [sylowToVec_sylowElem]; fin_cases a <;> simp⟩
  have hcol_mv : ∀ b : Fin 2, ∃ g ∈ Subgroup.zpowers (ellB q), (sylowToVec g).2.1 b ≠ 0 := fun b =>
    ⟨ellB q, Subgroup.mem_zpowers _, by dsimp [ellB]; rw [sylowToVec_sylowElem]; fin_cases b <;> simp⟩
  rw [squareSign_of_all_moving hodd _ (mkB t) hfix hrow_mv hcol_mv]
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  let negP : Equiv.Perm (ZMod q) := Equiv.neg (ZMod q)
  let p1 : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.2.2.1.1 x - x) t.2.2.1.2
  let p2 : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.2.2.2.1 x - x) t.2.2.2.2
  have hr0 : rowPerm (mkB t) (blockEquiv q (0, 0)) =
      blockPerm q 1 (fun b => if b = 0 then t.1 else t.2.2.1.1) := by
    apply Equiv.Perm.ext; intro col; obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    rw [blockPerm_apply]; change (mkB t).entry (blockEquiv q (0, 0)) (blockEquiv q (b, y)) = _
    fin_cases b <;> simp [mkB]
  have hr1 : rowPerm (mkB t) (blockEquiv q (1, 0)) =
      blockPerm q (Equiv.swap 0 1) (fun b => if b = 0 then t.2.2.2.1 else t.2.1) := by
    apply Equiv.Perm.ext; intro col; obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    rw [blockPerm_apply]; change (mkB t).entry (blockEquiv q (1, 0)) (blockEquiv q (b, y)) = _
    fin_cases b <;> simp [mkB]
  have hc0 : colPerm (mkB t) (blockEquiv q (0, 0)) =
      blockPerm q 1 (fun a => if a = 0 then negP.trans t.1 else negP.trans p2) := by
    apply Equiv.Perm.ext; intro r; obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    rw [blockPerm_apply]; change (mkB t).entry (blockEquiv q (a, x)) (blockEquiv q (0, 0)) = _
    fin_cases a
    · simp [mkB, negP, p2, Equiv.ofBijective_apply]
    · simp only [mkB, negP, p2, Fin.mk_one, Fin.isValue, one_ne_zero, Fin.zero_ne_one, and_false,
        false_and, true_and, and_true, ↓reduceIte, Equiv.symm_apply_apply, Equiv.trans_apply,
        Equiv.neg_apply, Equiv.Perm.one_apply, zero_sub]
      congr 1; refine Prod.ext rfl ?_
      change x + t.2.2.2.1 (-x) = t.2.2.2.1 (-x) - (-x); ring
  have hc1 : colPerm (mkB t) (blockEquiv q (1, 0)) =
      blockPerm q (Equiv.swap 0 1) (fun a => if a = 0 then negP.trans p1 else negP.trans t.2.1) := by
    apply Equiv.Perm.ext; intro r; obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    rw [blockPerm_apply]; change (mkB t).entry (blockEquiv q (a, x)) (blockEquiv q (1, 0)) = _
    fin_cases a
    · simp only [mkB, negP, p1, Fin.mk_zero, Fin.isValue, one_ne_zero, Fin.zero_ne_one, and_false,
        false_and, true_and, and_true, and_self, ↓reduceIte, Equiv.symm_apply_apply,
        Equiv.trans_apply, Equiv.neg_apply, Equiv.swap_apply_left, zero_sub]
      congr 1; refine Prod.ext rfl ?_
      change x + t.2.2.1.1 (-x) = t.2.2.1.1 (-x) - (-x); ring
    · simp [mkB, negP, p1, Equiv.ofBijective_apply]
  rw [hr0, hr1, hc0, hc1, sign_blockPerm_eq hq_odd, sign_blockPerm_eq hq_odd,
    sign_blockPerm_eq hq_odd, sign_blockPerm_eq hq_odd]
  have hsw : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
  have hneg_tr : ∀ φ : Equiv.Perm (ZMod q),
      Equiv.Perm.sign (negP.trans φ) = Equiv.Perm.sign φ * Equiv.Perm.sign negP := fun φ => by
    change Equiv.Perm.sign (φ * negP) = _; exact map_mul _ _ _
  simp only [↓reduceIte, hsw, one_ne_zero, hneg_tr]
  have hsqZ : ∀ u : ℤˣ, (u : ℤ) ^ 2 = 1 := fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  push_cast
  calc ((1 : ℤ) * ↑(Equiv.Perm.sign t.1) * ↑(Equiv.Perm.sign t.2.2.1.1)) *
        ((-1 : ℤ) * ↑(Equiv.Perm.sign t.2.2.2.1) * ↑(Equiv.Perm.sign t.2.1)) *
        ((1 : ℤ) * (↑(Equiv.Perm.sign t.1) * ↑(Equiv.Perm.sign negP)) *
          (↑(Equiv.Perm.sign p2) * ↑(Equiv.Perm.sign negP))) *
        ((-1 : ℤ) * (↑(Equiv.Perm.sign p1) * ↑(Equiv.Perm.sign negP)) *
          (↑(Equiv.Perm.sign t.2.1) * ↑(Equiv.Perm.sign negP)))
      = (↑(Equiv.Perm.sign t.1) : ℤ) ^ 2 * (↑(Equiv.Perm.sign t.2.1) : ℤ) ^ 2 *
        ((↑(Equiv.Perm.sign negP) : ℤ) ^ 2) ^ 2 *
        (↑(Equiv.Perm.sign t.2.2.1.1) * ↑(Equiv.Perm.sign p1) *
         ↑(Equiv.Perm.sign t.2.2.2.1) * ↑(Equiv.Perm.sign p2)) := by ring
    _ = ↑(Equiv.Perm.sign t.2.2.1.1) * ↑(Equiv.Perm.sign p1) *
        ↑(Equiv.Perm.sign t.2.2.2.1) * ↑(Equiv.Perm.sign p2) := by
      rw [hsqZ, hsqZ, hsqZ]; ring

private lemma lem_6_8_homogB (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    homogStrataSum q (ellB q) = 2 * (q.factorial : ℤ) ^ 2 * (tauQ q) ^ 2 := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    rw [lem_6_8_homog_sym q hq (ellB q) (by simp)]
    have hbij :
        (∑ L ∈ (Finset.univ : Finset (LatinSquare (2 * q))).filter
            (fun L => L ∈ fixSet ((Subgroup.zpowers (ellB q)).map (sylowP q).subtype) ∧ stratumOf q L = q),
          (squareSign L : ℤ)) =
        ∑ t : DomB q, (squareSign (mkB t) : ℤ) := by
      symm
      refine Finset.sum_bij (fun t _ => mkB t) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro t _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mkB_fix hq t, by unfold stratumOf; simp [mkB, ZMod.card]⟩
      · intro t₁ _ t₂ _ hEq
        have hent : ∀ a b d, (mkB t₁).entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) =
            (mkB t₂).entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) := fun a b d =>
          congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d))) hEq
        refine Prod.ext (Equiv.ext fun d => by
            have h := hent 0 0 d; simp only [mkB, Equiv.symm_apply_apply, Fin.isValue, and_self,
              ↓reduceIte, sub_zero] at h; exact congrArg Prod.snd ((blockEquiv q).injective h))
          (Prod.ext (Equiv.ext fun d => by
            have h := hent 1 1 d; simp only [mkB, Equiv.symm_apply_apply, Fin.isValue, and_self,
              ↓reduceIte, sub_zero, one_ne_zero] at h; exact congrArg Prod.snd ((blockEquiv q).injective h))
            (Prod.ext (Subtype.ext (Equiv.ext fun d => by
              have h := hent 0 1 d; simp only [mkB, Equiv.symm_apply_apply, Fin.isValue, and_self,
                ↓reduceIte, sub_zero, zero_ne_one, one_ne_zero, and_false, false_and, zero_add] at h
              exact congrArg Prod.snd ((blockEquiv q).injective h)))
              (Subtype.ext (Equiv.ext fun d => by
                have h := hent 1 0 d; simp only [mkB, Equiv.symm_apply_apply, Fin.isValue, and_self,
                  ↓reduceIte, sub_zero, zero_ne_one, one_ne_zero, and_false, false_and, zero_add] at h
                exact congrArg Prod.snd ((blockEquiv q).injective h)))))
      · intro L hL
        rcases (Finset.mem_filter.mp hL).2 with ⟨hLfix, hLq⟩
        obtain ⟨hmle, O, hO⟩ := pattern_of_fix_rankone (fun c => if c = 0 then 0 else 1) L hLfix
        have hO00 : O.O 0 0 = Finset.univ := Finset.eq_univ_of_card _ (by rw [O.card_00, hLq, ZMod.card])
        have hO11 : O.O 1 1 = Finset.univ := Finset.eq_univ_of_card _ (by rw [O.card_11, hLq, ZMod.card])
        have hO01 : O.O 0 1 = ∅ := Finset.card_eq_zero.mp (by rw [O.card_01, hLq, Nat.sub_self])
        have hO10 : O.O 1 0 = ∅ := Finset.card_eq_zero.mp (by rw [O.card_10, hLq, Nat.sub_self])
        have hshift : ∀ a b x y, L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
            blockEquiv q (((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)))).1,
              ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)))).2 +
                (if ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)))).1 = 0 then 0 else x)) := by
          intro a b x y
          have hpow : ellB q ^ x.val ∈ Subgroup.zpowers (ellB q) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
          have hfix := (sylow_fix_entry_iff (ellB q ^ x.val) L).mp
            (hLfix (ellB q ^ x.val).1 ⟨ellB q ^ x.val, hpow, rfl⟩) a b 0 (y - x)
          rw [show ellB q = sylowElem q 1 1 1 1 0 1 from rfl, sylowToVec_pow_1111, ZMod.natCast_zmod_val] at hfix
          have : ∀ c : Fin 2, x * (if c = 0 then (0 : ZMod q) else 1) = if c = 0 then 0 else x := fun c => by
            fin_cases c <;> simp
          simpa [zero_add, sub_add_cancel, this] using hfix
        have hblk : ∀ a b d, ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 =
            if a = b then 0 else 1 := fun a b d => by
          fin_cases a <;> fin_cases b
          · simpa using (hO 0 0 0 d).mp (by rw [hO00]; exact Finset.mem_univ d)
          · have h0 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, d)))).1 ≠ 0 := fun h => by
              have := (hO 0 1 0 d).mpr (by simpa using h); rw [hO01] at this; exact Finset.notMem_empty _ this
            simp only [Fin.mk_zero, Fin.mk_one, Fin.zero_ne_one, ↓reduceIte]
            generalize ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, d)))).1 = c at h0 ⊢
            fin_cases c; exact (h0 rfl).elim; rfl
          · have h0 : ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, d)))).1 ≠ 0 := fun h => by
              have := (hO 1 0 0 d).mpr (by simpa using h); rw [hO10] at this; exact Finset.notMem_empty _ this
            simp only [Fin.mk_zero, Fin.mk_one, one_ne_zero, ↓reduceIte]
            generalize ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, d)))).1 = c at h0 ⊢
            fin_cases c; exact (h0 rfl).elim; rfl
          · simpa using (hO 1 1 0 d).mp (by rw [hO11]; exact Finset.mem_univ d)
        let f : Fin 2 → Fin 2 → ZMod q → ZMod q := fun a b d =>
          ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2
        have hfbij : ∀ a b, Function.Bijective (f a b) := fun a b => by
          rw [← Finite.injective_iff_bijective]
          intro d₁ d₂ hEq
          have hL12 : L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d₁)) =
              L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d₂)) :=
            (blockEquiv q).symm.injective (Prod.ext ((hblk a b d₁).trans (hblk a b d₂).symm) hEq)
          exact congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 hL12))
        have hcm : ∀ a b, a ≠ b → IsCompleteMap (Equiv.ofBijective (f a b) (hfbij a b)) := fun a b hab => by
          rw [IsCompleteMap, ← Finite.injective_iff_bijective]
          intro d₁ d₂ hEq
          have h1 := hshift a b (-d₁) 0; have h2 := hshift a b (-d₂) 0
          simp only [zero_sub, neg_neg, hblk a b, hab, ↓reduceIte] at h1 h2
          have hL12 : L.entry (blockEquiv q (a, -d₁)) (blockEquiv q (b, 0)) =
              L.entry (blockEquiv q (a, -d₂)) (blockEquiv q (b, 0)) := by
            rw [h1, h2]; congr 1; refine Prod.ext rfl ?_
            simp only [one_ne_zero, ↓reduceIte]
            have hEq' : f a b d₁ - d₁ = f a b d₂ - d₂ := hEq
            simp only [f] at hEq'
            linear_combination hEq'
          exact neg_injective (congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 hL12)))
        refine ⟨(Equiv.ofBijective (f 0 0) (hfbij 0 0),
                 Equiv.ofBijective (f 1 1) (hfbij 1 1),
                 ⟨Equiv.ofBijective (f 0 1) (hfbij 0 1), hcm 0 1 Fin.zero_ne_one⟩,
                 ⟨Equiv.ofBijective (f 1 0) (hfbij 1 0), hcm 1 0 one_ne_zero⟩),
          Finset.mem_univ _, ?_⟩
        ext r col
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
        rw [hshift a b x y, hblk a b (y - x)]
        fin_cases a <;> fin_cases b <;> simp [mkB, f] <;> ring
    rw [hbij]
    dsimp only [DomB]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    let g : CMq q → ℤ := fun h =>
      (Equiv.Perm.sign h.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ)
    have hsign4 : ∀ (a b : Equiv.Perm (ZMod q)) (c d : CMq q),
        (squareSign (mkB (a, b, c, d)) : ℤ) = g c * g d := fun a b c d => by
      rw [mkB_sign hq hodd]; dsimp only [g]; ring
    have htau : ∑ h : CMq q, g h = tauQ q := rfl
    simp_rw [hsign4, ← Finset.mul_sum, htau, ← Finset.sum_mul, htau,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, ZMod.card, nsmul_eq_mul]
    ring

private abbrev DomC (q : ℕ) [NeZero q] := CMq q × CMq q × CMq q × CMq q

private def mkC {q : ℕ} [NeZero q] (t : DomC q) : LatinSquare (2 * q) :=
  { entry := fun r col =>
      let pr := (blockEquiv q).symm r
      let pc := (blockEquiv q).symm col
      if pr.1 = 0 ∧ pc.1 = 0 then blockEquiv q (0, pr.2 + t.1.1 (pc.2 - pr.2))
      else if pr.1 = 1 ∧ pc.1 = 1 then blockEquiv q (0, pr.2 + t.2.1.1 (pc.2 - pr.2))
      else if pr.1 = 0 ∧ pc.1 = 1 then blockEquiv q (1, pr.2 + t.2.2.1.1 (pc.2 - pr.2))
      else blockEquiv q (1, pr.2 + t.2.2.2.1 (pc.2 - pr.2))
    row_bijective := fun r => by
      rw [← Finite.injective_iff_bijective]
      intro c₁ c₂ hEq
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective c₁
      obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective c₂
      simp only [Equiv.symm_apply_apply] at hEq
      fin_cases a <;> fin_cases b₁ <;> fin_cases b₂ <;> simp at hEq
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl hEq
      · congr 1; exact Prod.ext rfl hEq
    col_bijective := fun col => by
      rw [← Finite.injective_iff_bijective]
      intro r₁ r₂ hEq
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
      obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
      simp only [Equiv.symm_apply_apply] at hEq
      fin_cases b <;> fin_cases a₁ <;> fin_cases a₂ <;> simp at hEq
      · have hsub : t.1.1 (y - x₁) - (y - x₁) = t.1.1 (y - x₂) - (y - x₂) := by linear_combination hEq
        have := t.1.2.1 hsub; congr 1; exact Prod.ext rfl (by linear_combination -this)
      · have hsub : t.2.2.2.1 (y - x₁) - (y - x₁) = t.2.2.2.1 (y - x₂) - (y - x₂) := by linear_combination hEq
        have := t.2.2.2.2.1 hsub; congr 1; exact Prod.ext rfl (by linear_combination -this)
      · have hsub : t.2.2.1.1 (y - x₁) - (y - x₁) = t.2.2.1.1 (y - x₂) - (y - x₂) := by linear_combination hEq
        have := t.2.2.1.2.1 hsub; congr 1; exact Prod.ext rfl (by linear_combination -this)
      · have hsub : t.2.1.1 (y - x₁) - (y - x₁) = t.2.1.1 (y - x₂) - (y - x₂) := by linear_combination hEq
        have := t.2.1.2.1 hsub; congr 1; exact Prod.ext rfl (by linear_combination -this) }

private lemma mkC_fix {q : ℕ} [NeZero q] (hq : q.Prime) (t : DomC q) :
    mkC t ∈ fixSet ((Subgroup.zpowers (ellC q)).map (sylowP q).subtype) := by
  have : Fact q.Prime := ⟨hq⟩
  rintro _ ⟨g, hg, rfl⟩
  change g.1 • mkC t = mkC t; rw [sylow_fix_entry_iff]
  rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
  have hk : ∃ n : ℕ, ellC q ^ k = ellC q ^ n := by
    have hord : ellC q ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 (ellC q) trivial
    refine ⟨(k % (q : ℤ)).toNat, ?_⟩
    have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
    have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
    conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  rcases hk with ⟨n, hn⟩; rw [hn, show ellC q = sylowElem q 1 1 1 1 1 1 from rfl, sylowToVec_pow_1111 1 1 n]
  intro a b x y; dsimp only [mkC]; simp only [Equiv.symm_apply_apply]
  have hsub : y + (n : ZMod q) - (x + (n : ZMod q)) = y - x := by ring
  fin_cases a <;> fin_cases b <;> simp [hsub] <;> ring

private lemma mkC_sign {q : ℕ} [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) (t : DomC q) :
    (squareSign (mkC t) : ℤ) =
      ((Equiv.Perm.sign t.1.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.1.1 x - x) t.1.2) : ℤ)) *
      ((Equiv.Perm.sign t.2.1.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.2.1.1 x - x) t.2.1.2) : ℤ)) *
      ((Equiv.Perm.sign t.2.2.1.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.2.2.1.1 x - x) t.2.2.1.2) : ℤ)) *
      ((Equiv.Perm.sign t.2.2.2.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.2.2.2.1 x - x) t.2.2.2.2) : ℤ)) := by
  have : Fact q.Prime := ⟨hq⟩
  have hrow_mv : ∀ a : Fin 2, ∃ g ∈ Subgroup.zpowers (ellC q), (sylowToVec g).1 a ≠ 0 := fun a =>
    ⟨ellC q, Subgroup.mem_zpowers _, by dsimp [ellC]; rw [sylowToVec_sylowElem]; fin_cases a <;> simp⟩
  have hcol_mv : ∀ b : Fin 2, ∃ g ∈ Subgroup.zpowers (ellC q), (sylowToVec g).2.1 b ≠ 0 := fun b =>
    ⟨ellC q, Subgroup.mem_zpowers _, by dsimp [ellC]; rw [sylowToVec_sylowElem]; fin_cases b <;> simp⟩
  rw [squareSign_of_all_moving hodd _ (mkC t) (mkC_fix hq t) hrow_mv hcol_mv]
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  let negP : Equiv.Perm (ZMod q) := Equiv.neg (ZMod q)
  let p00 : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.1.1 x - x) t.1.2
  let p11 : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.2.1.1 x - x) t.2.1.2
  let p01 : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.2.2.1.1 x - x) t.2.2.1.2
  let p10 : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.2.2.2.1 x - x) t.2.2.2.2
  have hr0 : rowPerm (mkC t) (blockEquiv q (0, 0)) =
      blockPerm q 1 (fun b => if b = 0 then t.1.1 else t.2.2.1.1) := by
    apply Equiv.Perm.ext; intro col; obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    rw [blockPerm_apply]; change (mkC t).entry (blockEquiv q (0, 0)) (blockEquiv q (b, y)) = _
    fin_cases b <;> simp [mkC]
  have hr1 : rowPerm (mkC t) (blockEquiv q (1, 0)) =
      blockPerm q (Equiv.swap 0 1) (fun b => if b = 0 then t.2.2.2.1 else t.2.1.1) := by
    apply Equiv.Perm.ext; intro col; obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    rw [blockPerm_apply]; change (mkC t).entry (blockEquiv q (1, 0)) (blockEquiv q (b, y)) = _
    fin_cases b <;> simp [mkC]
  have hc0 : colPerm (mkC t) (blockEquiv q (0, 0)) =
      blockPerm q 1 (fun a => if a = 0 then negP.trans p00 else negP.trans p10) := by
    apply Equiv.Perm.ext; intro r; obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    rw [blockPerm_apply]; change (mkC t).entry (blockEquiv q (a, x)) (blockEquiv q (0, 0)) = _
    fin_cases a
    · simp only [mkC, negP, p00, p10, Fin.mk_zero, Fin.isValue, and_self, true_and, and_true,
        ↓reduceIte, Equiv.symm_apply_apply, Equiv.trans_apply, Equiv.neg_apply,
        Equiv.Perm.one_apply, zero_sub]
      congr 1; refine Prod.ext rfl ?_
      change x + t.1.1 (-x) = t.1.1 (-x) - (-x); ring
    · simp only [mkC, negP, p00, p10, Fin.mk_one, Fin.isValue, one_ne_zero, Fin.zero_ne_one,
        and_false, false_and, true_and, and_true, ↓reduceIte, Equiv.symm_apply_apply,
        Equiv.trans_apply, Equiv.neg_apply, Equiv.Perm.one_apply, zero_sub]
      congr 1; refine Prod.ext rfl ?_
      change x + t.2.2.2.1 (-x) = t.2.2.2.1 (-x) - (-x); ring
  have hc1 : colPerm (mkC t) (blockEquiv q (1, 0)) =
      blockPerm q (Equiv.swap 0 1) (fun a => if a = 0 then negP.trans p01 else negP.trans p11) := by
    apply Equiv.Perm.ext; intro r; obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    rw [blockPerm_apply]; change (mkC t).entry (blockEquiv q (a, x)) (blockEquiv q (1, 0)) = _
    fin_cases a
    · simp only [mkC, negP, p01, p11, Fin.mk_zero, Fin.isValue, one_ne_zero, Fin.zero_ne_one,
        and_false, false_and, true_and, and_true, and_self, ↓reduceIte, Equiv.symm_apply_apply,
        Equiv.trans_apply, Equiv.neg_apply, Equiv.swap_apply_left, zero_sub]
      congr 1; refine Prod.ext rfl ?_
      change x + t.2.2.1.1 (-x) = t.2.2.1.1 (-x) - (-x); ring
    · simp only [mkC, negP, p01, p11, Fin.mk_one, Fin.isValue, one_ne_zero, Fin.zero_ne_one,
        and_false, false_and, true_and, and_true, and_self, ↓reduceIte, Equiv.symm_apply_apply,
        Equiv.trans_apply, Equiv.neg_apply, Equiv.swap_apply_right, zero_sub]
      congr 1; refine Prod.ext rfl ?_
      change x + t.2.1.1 (-x) = t.2.1.1 (-x) - (-x); ring
  rw [hr0, hr1, hc0, hc1, sign_blockPerm_eq hq_odd, sign_blockPerm_eq hq_odd,
    sign_blockPerm_eq hq_odd, sign_blockPerm_eq hq_odd]
  have hsw : Equiv.swap (0 : Fin 2) 1 ≠ 1 := by decide
  have hneg_tr : ∀ φ : Equiv.Perm (ZMod q),
      Equiv.Perm.sign (negP.trans φ) = Equiv.Perm.sign φ * Equiv.Perm.sign negP := fun φ => by
    change Equiv.Perm.sign (φ * negP) = _; exact map_mul _ _ _
  simp only [↓reduceIte, hsw, one_ne_zero, hneg_tr]
  have hsqZ : ∀ u : ℤˣ, (u : ℤ) ^ 2 = 1 := fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  push_cast
  calc ((1 : ℤ) * ↑(Equiv.Perm.sign t.1.1) * ↑(Equiv.Perm.sign t.2.2.1.1)) *
        ((-1 : ℤ) * ↑(Equiv.Perm.sign t.2.2.2.1) * ↑(Equiv.Perm.sign t.2.1.1)) *
        ((1 : ℤ) * (↑(Equiv.Perm.sign p00) * ↑(Equiv.Perm.sign negP)) *
          (↑(Equiv.Perm.sign p10) * ↑(Equiv.Perm.sign negP))) *
        ((-1 : ℤ) * (↑(Equiv.Perm.sign p01) * ↑(Equiv.Perm.sign negP)) *
          (↑(Equiv.Perm.sign p11) * ↑(Equiv.Perm.sign negP)))
      = ((↑(Equiv.Perm.sign negP) : ℤ) ^ 2) ^ 2 *
        ((↑(Equiv.Perm.sign t.1.1) * ↑(Equiv.Perm.sign p00)) *
         (↑(Equiv.Perm.sign t.2.1.1) * ↑(Equiv.Perm.sign p11)) *
         (↑(Equiv.Perm.sign t.2.2.1.1) * ↑(Equiv.Perm.sign p01)) *
         (↑(Equiv.Perm.sign t.2.2.2.1) * ↑(Equiv.Perm.sign p10))) := by ring
    _ = (↑(Equiv.Perm.sign t.1.1) * ↑(Equiv.Perm.sign p00)) *
        (↑(Equiv.Perm.sign t.2.1.1) * ↑(Equiv.Perm.sign p11)) *
        (↑(Equiv.Perm.sign t.2.2.1.1) * ↑(Equiv.Perm.sign p01)) *
        (↑(Equiv.Perm.sign t.2.2.2.1) * ↑(Equiv.Perm.sign p10)) := by
      rw [hsqZ]; ring

private lemma lem_6_8_homogC (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    homogStrataSum q (ellC q) = 2 * (tauQ q) ^ 4 := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    rw [lem_6_8_homog_sym q hq (ellC q) (by simp)]
    have hbij :
        (∑ L ∈ (Finset.univ : Finset (LatinSquare (2 * q))).filter
            (fun L => L ∈ fixSet ((Subgroup.zpowers (ellC q)).map (sylowP q).subtype) ∧ stratumOf q L = q),
          (squareSign L : ℤ)) =
        ∑ t : DomC q, (squareSign (mkC t) : ℤ) := by
      symm
      refine Finset.sum_bij (fun t _ => mkC t) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro t _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mkC_fix hq t, by unfold stratumOf; simp [mkC, ZMod.card]⟩
      · intro t₁ _ t₂ _ hEq
        have hent : ∀ a b d, (mkC t₁).entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) =
            (mkC t₂).entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)) := fun a b d =>
          congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d))) hEq
        refine Prod.ext (Subtype.ext (Equiv.ext fun d => by
            have h := hent 0 0 d; simp only [mkC, Equiv.symm_apply_apply, Fin.isValue, and_self,
              ↓reduceIte, sub_zero, zero_add] at h; exact congrArg Prod.snd ((blockEquiv q).injective h)))
          (Prod.ext (Subtype.ext (Equiv.ext fun d => by
            have h := hent 1 1 d; simp only [mkC, Equiv.symm_apply_apply, Fin.isValue, and_self,
              ↓reduceIte, sub_zero, one_ne_zero, zero_add] at h
            exact congrArg Prod.snd ((blockEquiv q).injective h)))
            (Prod.ext (Subtype.ext (Equiv.ext fun d => by
              have h := hent 0 1 d; simp only [mkC, Equiv.symm_apply_apply, Fin.isValue, and_self,
                ↓reduceIte, sub_zero, zero_ne_one, one_ne_zero, and_false, false_and, zero_add] at h
              exact congrArg Prod.snd ((blockEquiv q).injective h)))
              (Subtype.ext (Equiv.ext fun d => by
                have h := hent 1 0 d; simp only [mkC, Equiv.symm_apply_apply, Fin.isValue, and_self,
                  ↓reduceIte, sub_zero, zero_ne_one, one_ne_zero, and_false, false_and, zero_add] at h
                exact congrArg Prod.snd ((blockEquiv q).injective h)))))
      · intro L hL
        rcases (Finset.mem_filter.mp hL).2 with ⟨hLfix, hLq⟩
        obtain ⟨hmle, O, hO⟩ := pattern_of_fix_rankone (fun _ => 1) L hLfix
        have hO00 : O.O 0 0 = Finset.univ := Finset.eq_univ_of_card _ (by rw [O.card_00, hLq, ZMod.card])
        have hO11 : O.O 1 1 = Finset.univ := Finset.eq_univ_of_card _ (by rw [O.card_11, hLq, ZMod.card])
        have hO01 : O.O 0 1 = ∅ := Finset.card_eq_zero.mp (by rw [O.card_01, hLq, Nat.sub_self])
        have hO10 : O.O 1 0 = ∅ := Finset.card_eq_zero.mp (by rw [O.card_10, hLq, Nat.sub_self])
        have hshift : ∀ a b x y, L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
            blockEquiv q (((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)))).1,
              ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, y - x)))).2 + x) := by
          intro a b x y
          have hpow : ellC q ^ x.val ∈ Subgroup.zpowers (ellC q) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
          have hfix := (sylow_fix_entry_iff (ellC q ^ x.val) L).mp
            (hLfix (ellC q ^ x.val).1 ⟨ellC q ^ x.val, hpow, rfl⟩) a b 0 (y - x)
          rw [show ellC q = sylowElem q 1 1 1 1 1 1 from rfl, sylowToVec_pow_1111, ZMod.natCast_zmod_val] at hfix
          simpa [zero_add, sub_add_cancel] using hfix
        have hblk : ∀ a b d, ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 =
            if a = b then 0 else 1 := fun a b d => by
          fin_cases a <;> fin_cases b
          · simpa using (hO 0 0 0 d).mp (by rw [hO00]; exact Finset.mem_univ d)
          · have h0 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, d)))).1 ≠ 0 := fun h => by
              have := (hO 0 1 0 d).mpr (by simpa using h); rw [hO01] at this; exact Finset.notMem_empty _ this
            simp only [Fin.mk_zero, Fin.mk_one, Fin.zero_ne_one, ↓reduceIte]
            generalize ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, d)))).1 = c at h0 ⊢
            fin_cases c; exact (h0 rfl).elim; rfl
          · have h0 : ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, d)))).1 ≠ 0 := fun h => by
              have := (hO 1 0 0 d).mpr (by simpa using h); rw [hO10] at this; exact Finset.notMem_empty _ this
            simp only [Fin.mk_zero, Fin.mk_one, one_ne_zero, ↓reduceIte]
            generalize ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, d)))).1 = c at h0 ⊢
            fin_cases c; exact (h0 rfl).elim; rfl
          · simpa using (hO 1 1 0 d).mp (by rw [hO11]; exact Finset.mem_univ d)
        let f : Fin 2 → Fin 2 → ZMod q → ZMod q := fun a b d =>
          ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2
        have hfbij : ∀ a b, Function.Bijective (f a b) := fun a b => by
          rw [← Finite.injective_iff_bijective]
          intro d₁ d₂ hEq
          have hL12 : L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d₁)) =
              L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d₂)) :=
            (blockEquiv q).symm.injective (Prod.ext ((hblk a b d₁).trans (hblk a b d₂).symm) hEq)
          exact congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 hL12))
        have hcm : ∀ a b, IsCompleteMap (Equiv.ofBijective (f a b) (hfbij a b)) := fun a b => by
          rw [IsCompleteMap, ← Finite.injective_iff_bijective]
          intro d₁ d₂ hEq
          have h1 := hshift a b (-d₁) 0; have h2 := hshift a b (-d₂) 0
          simp only [zero_sub, neg_neg, hblk a b] at h1 h2
          have hL12 : L.entry (blockEquiv q (a, -d₁)) (blockEquiv q (b, 0)) =
              L.entry (blockEquiv q (a, -d₂)) (blockEquiv q (b, 0)) := by
            rw [h1, h2]; congr 1; refine Prod.ext rfl ?_
            have hEq' : f a b d₁ - d₁ = f a b d₂ - d₂ := hEq
            dsimp only [f] at hEq'
            linear_combination hEq'
          exact neg_injective (congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 hL12)))
        refine ⟨(⟨Equiv.ofBijective (f 0 0) (hfbij 0 0), hcm 0 0⟩,
                 ⟨Equiv.ofBijective (f 1 1) (hfbij 1 1), hcm 1 1⟩,
                 ⟨Equiv.ofBijective (f 0 1) (hfbij 0 1), hcm 0 1⟩,
                 ⟨Equiv.ofBijective (f 1 0) (hfbij 1 0), hcm 1 0⟩),
          Finset.mem_univ _, ?_⟩
        ext r col
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
        rw [hshift a b x y, hblk a b (y - x)]
        fin_cases a <;> fin_cases b <;> simp [mkC, f] <;> ring
    rw [hbij]
    dsimp only [DomC]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    let g : CMq q → ℤ := fun h =>
      (Equiv.Perm.sign h.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ)
    have hsign4 : ∀ (a b c d : CMq q),
        (squareSign (mkC (a, b, c, d)) : ℤ) = g a * (g b * (g c * g d)) := fun a b c d => by
      rw [mkC_sign hq hodd]; dsimp only [g]; ring
    have htau : ∑ h : CMq q, g h = tauQ q := rfl
    simp_rw [hsign4, ← Finset.mul_sum, htau, ← Finset.sum_mul, htau]
    ring

private lemma lem_6_8_decomp (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    ∀ ℓ ∈ ({ellB q, ellC q} : Finset (sylowP q)),
      S_twoq q (Subgroup.zpowers ℓ) =
        homogStrataSum q ℓ + (q : ℤ) ^ 5 * ∑ m ∈ Finset.Ioo 0 q, mixedOrbitCount q ℓ m := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    let _ : Fintype (sylowP q) := Fintype.ofFinite _
    intro ℓ hℓ
    let F := (Finset.univ : Finset (LatinSquare (2 * q))).filter
      (fun L => L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype))
    have hstr_le : ∀ L ∈ F, stratumOf q L ∈ Finset.range (q + 1) := by
      intro L _; rw [Finset.mem_range]
      have : stratumOf q L ≤ q := by
        unfold stratumOf
        simpa [ZMod.card] using Finset.card_filter_le (Finset.univ : Finset (ZMod q))
          (fun d : ZMod q => ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)))).1 = 0)
      omega
    have hfib : S_twoq q (Subgroup.zpowers ℓ) =
        ∑ m ∈ Finset.range (q + 1),
          ∑ L ∈ F.filter (fun L => stratumOf q L = m), (squareSign L : ℤ) := by
      change ∑ L ∈ F, (squareSign L : ℤ) = _
      exact (Finset.sum_fiberwise_of_maps_to (s := F) (t := Finset.range (q + 1))
        (g := stratumOf q) hstr_le (fun L => (squareSign L : ℤ))).symm
    have hrange : Finset.range (q + 1) = insert 0 (insert q (Finset.Ioo 0 q)) := by
      ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      have := hq.pos; omega
    have h0not : (0 : ℕ) ∉ insert q (Finset.Ioo 0 q) := by
      simp [hq.ne_zero.symm]
    have hqnot : q ∉ Finset.Ioo 0 q := by simp
    rw [hfib, hrange, Finset.sum_insert h0not, Finset.sum_insert hqnot]
    have hhom :
        (∑ L ∈ F.filter (fun L => stratumOf q L = 0), (squareSign L : ℤ)) +
        (∑ L ∈ F.filter (fun L => stratumOf q L = q), (squareSign L : ℤ)) =
        homogStrataSum q ℓ := by
      unfold homogStrataSum
      rw [← Finset.sum_union]
      · congr 1; ext L; simp only [F, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      · rw [Finset.disjoint_left]; intro L h1 h2
        have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2
        have := hq.ne_zero; omega
    rw [← add_assoc, hhom, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := (Finset.mem_Ioo.mp hm).1
    have hmq : m < q := (Finset.mem_Ioo.mp hm).2
    -- Every `P`-orbit in `StratumFix q ℓ m` has size `q^5` and constant sign!
    unfold mixedOrbitCount
    set R : Setoid (StratumFix q ℓ m) :=
      { r := fun L₁ L₂ => ∃ g : sylowP q, g.1 • L₁.1 = L₂.1
        iseqv :=
          ⟨fun L => ⟨1, one_smul _ _⟩,
           fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg]; simp⟩,
           fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ => ⟨g₂ * g₁, by rw [← h₂, ← h₁]; exact mul_smul _ _ _⟩⟩ }
    have hsum_sub :
        (∑ L ∈ F.filter (fun L => stratumOf q L = m), (squareSign L : ℤ)) =
        ∑ L : StratumFix q ℓ m, (squareSign L.1 : ℤ) := by
      symm
      refine Finset.sum_bij (fun L _ => L.1) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro L _; exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.2.1⟩, L.2.2⟩
      · intro L₁ _ L₂ _ h; exact Subtype.ext h
      · intro L hL
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
        have h2 := (Finset.mem_filter.mp hL).2
        exact ⟨⟨L, h1, h2⟩, Finset.mem_univ _, rfl⟩
    rw [hsum_sub]
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Quotient R)))
      (g := Quotient.mk R) (fun _ _ => Finset.mem_univ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    have hconst : ∀ L ∈ Finset.univ.filter (fun L : StratumFix q ℓ m => Quotient.mk R L = o),
        (squareSign L.1 : ℤ) = (squareSign (Quotient.out o).1 : ℤ) := by
      intro L hL
      have hqeq : Quotient.mk R L = Quotient.mk R (Quotient.out o) := by
        rw [(Finset.mem_filter.mp hL).2, Quotient.out_eq]
      rcases Quotient.exact hqeq with ⟨g, hg⟩
      rw [← hg, squareSign_isotopyAct_even (even_two_mul q)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    -- Count orbit size `= q^5` via `sylowP q ⧸ Subgroup.zpowers ℓ`!
    have horb_card :
        (Finset.univ.filter (fun L : StratumFix q ℓ m => Quotient.mk R L = o)).card = q ^ 5 := by
      let L₀ := Quotient.out o
      have hL0_pos : 0 < stratumOf q L₀.1 := by rw [L₀.2.2]; exact hm0
      have hL0_lt : stratumOf q L₀.1 < q := by rw [L₀.2.2]; exact hmq
      have hstab : ∀ g : sylowP q, g.1 • L₀.1 = L₀.1 ↔ g ∈ Subgroup.zpowers ℓ :=
        lem_6_8_partB q hq hodd ℓ hℓ L₀.1 L₀.2.1 hL0_pos hL0_lt
      -- Bijection between `sylowP q ⧸ Subgroup.zpowers ℓ` and the orbit fiber
      have hact_mem : ∀ g : sylowP q,
          g.1 • L₀.1 ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) ∧
          stratumOf q (g.1 • L₀.1) = m := by
        intro g
        refine ⟨?_, ?_⟩
        · rintro _ ⟨h, hh, rfl⟩
          change h.1 • (g.1 • L₀.1) = g.1 • L₀.1
          have hcomm : h * g = g * h := (isElemAbelian_sylowP_subgroup q ⊤).1 h trivial g trivial
          have hcomm1 : h.1 * g.1 = g.1 * h.1 := congrArg Subtype.val hcomm
          rw [← mul_smul, hcomm1, mul_smul, L₀.2.1 h.1 ⟨h, hh, rfl⟩]
        · -- `g` translates offsets by `v 0 - u 0`, preserving `card`!
          have hL0_m : stratumOf q L₀.1 = m := L₀.2.2
          trans (stratumOf q L₀.1)
          swap; · exact hL0_m
          unfold stratumOf
          let u0 := (sylowToVec g).1 0; let v0 := (sylowToVec g).2.1 0
          refine Finset.card_bij (fun d _ => d + (u0 - v0)) ?_ ?_ ?_
          · intro d hd
            have h0 := (Finset.mem_filter.mp hd).2
            have hgval := sylowToVec_val g
            have hent : (g.1 • L₀.1).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)) =
                blockTransPerm q (sylowToVec g).2.2
                  (L₀.1.entry (blockEquiv q (0, -u0)) (blockEquiv q (0, d - v0))) := by
              change g.1.2.2 (L₀.1.entry (g.1.1.symm (blockEquiv q (0, 0)))
                (g.1.2.1.symm (blockEquiv q (0, d)))) = _
              rw [hgval]
              have hinv1 : (blockTransPerm q (sylowToVec g).1).symm (blockEquiv q (0, 0)) =
                  blockEquiv q (0, -u0) := by
                apply (blockTransPerm q (sylowToVec g).1).injective
                rw [Equiv.apply_symm_apply, blockTransPerm_apply]; simp [u0]
              have hinv2 : (blockTransPerm q (sylowToVec g).2.1).symm (blockEquiv q (0, d)) =
                  blockEquiv q (0, d - v0) := by
                apply (blockTransPerm q (sylowToVec g).2.1).injective
                rw [Equiv.apply_symm_apply, blockTransPerm_apply]; simp [v0]
              rw [hinv1, hinv2]
            rw [hent] at h0
            have hbt : ∀ k : Fin (2 * q), ((blockEquiv q).symm (blockTransPerm q (sylowToVec g).2.2 k)).1 =
                ((blockEquiv q).symm k).1 := fun k => by
              obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
              rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
            rw [hbt] at h0
            -- Shift `L₀` by `ℓ ^ (-u0).val` to move row `(0, -u0)` back to `(0, 0)`!
            have hpow : ℓ ^ u0.val ∈ Subgroup.zpowers ℓ := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
            have hfix := (sylow_fix_entry_iff (ℓ ^ u0.val) L₀.1).mp
              (L₀.2.1 (ℓ ^ u0.val).1 ⟨ℓ ^ u0.val, hpow, rfl⟩) 0 0 (-u0) (d - v0)
            have hℓu : (sylowToVec (ℓ ^ u0.val)).1 0 = u0 ∧ (sylowToVec (ℓ ^ u0.val)).2.1 0 = u0 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
              rcases hℓ with rfl | rfl
              · rw [show ellB q = sylowElem q 1 1 1 1 0 1 from rfl, sylowToVec_pow_1111, ZMod.natCast_zmod_val]; exact ⟨rfl, rfl⟩
              · rw [show ellC q = sylowElem q 1 1 1 1 1 1 from rfl, sylowToVec_pow_1111, ZMod.natCast_zmod_val]; exact ⟨rfl, rfl⟩
            rw [hℓu.1, hℓu.2, neg_add_cancel] at hfix
            have h1 := congrArg (fun k => ((blockEquiv q).symm k).1) hfix
            simp only [Equiv.symm_apply_apply] at h1
            have hadd : d - v0 + u0 = d + (u0 - v0) := by ring
            rw [hadd] at h1
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h1, h0]⟩
          · intro d₁ _ d₂ _ hEq; linear_combination hEq
          · intro d hd
            refine ⟨d - (u0 - v0), ?_, by ring⟩
            have h0 := (Finset.mem_filter.mp hd).2
            have hpow : ℓ ^ u0.val ∈ Subgroup.zpowers ℓ := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
            have hfix := (sylow_fix_entry_iff (ℓ ^ u0.val) L₀.1).mp
              (L₀.2.1 (ℓ ^ u0.val).1 ⟨ℓ ^ u0.val, hpow, rfl⟩) 0 0 (-u0) (d - (u0 - v0) - v0)
            have hℓu : (sylowToVec (ℓ ^ u0.val)).1 0 = u0 ∧ (sylowToVec (ℓ ^ u0.val)).2.1 0 = u0 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
              rcases hℓ with rfl | rfl
              · rw [show ellB q = sylowElem q 1 1 1 1 0 1 from rfl, sylowToVec_pow_1111, ZMod.natCast_zmod_val]; exact ⟨rfl, rfl⟩
              · rw [show ellC q = sylowElem q 1 1 1 1 1 1 from rfl, sylowToVec_pow_1111, ZMod.natCast_zmod_val]; exact ⟨rfl, rfl⟩
            rw [hℓu.1, hℓu.2, neg_add_cancel] at hfix
            have hadd : d - (u0 - v0) - v0 + u0 = d := by ring
            rw [hadd] at hfix
            have h1 := congrArg (fun k => ((blockEquiv q).symm k).1) hfix
            simp only [Equiv.symm_apply_apply] at h1
            have hgval := sylowToVec_val g
            have hent : (g.1 • L₀.1).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d - (u0 - v0))) =
                blockTransPerm q (sylowToVec g).2.2
                  (L₀.1.entry (blockEquiv q (0, -u0)) (blockEquiv q (0, d - (u0 - v0) - v0))) := by
              change g.1.2.2 (L₀.1.entry (g.1.1.symm (blockEquiv q (0, 0)))
                (g.1.2.1.symm (blockEquiv q (0, d - (u0 - v0))))) = _
              rw [hgval]
              have hinv1 : (blockTransPerm q (sylowToVec g).1).symm (blockEquiv q (0, 0)) =
                  blockEquiv q (0, -u0) := by
                apply (blockTransPerm q (sylowToVec g).1).injective
                rw [Equiv.apply_symm_apply, blockTransPerm_apply]; simp [u0]
              have hinv2 : (blockTransPerm q (sylowToVec g).2.1).symm (blockEquiv q (0, d - (u0 - v0))) =
                  blockEquiv q (0, d - (u0 - v0) - v0) := by
                apply (blockTransPerm q (sylowToVec g).2.1).injective
                rw [Equiv.apply_symm_apply, blockTransPerm_apply]; simp [v0]
              rw [hinv1, hinv2]
            have hbt : ∀ k : Fin (2 * q), ((blockEquiv q).symm (blockTransPerm q (sylowToVec g).2.2 k)).1 =
                ((blockEquiv q).symm k).1 := fun k => by
              obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
              rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hent, hbt, ← h1, h0]⟩
      let φ : sylowP q ⧸ Subgroup.zpowers ℓ → StratumFix q ℓ m :=
        Quotient.lift (fun g => ⟨g.1 • L₀.1, hact_mem g⟩) (fun g₁ g₂ hrel => by
          apply Subtype.ext; dsimp
          have hmem : g₁⁻¹ * g₂ ∈ Subgroup.zpowers ℓ := QuotientGroup.leftRel_apply.mp hrel
          have hfix : (g₁⁻¹ * g₂).1 • L₀.1 = L₀.1 := (hstab _).mpr hmem
          have := congrArg (g₁.1 • ·) hfix
          rw [← mul_smul] at this
          have h1 : g₁.1 * (g₁⁻¹ * g₂).1 = g₂.1 := by
            change (g₁ * (g₁⁻¹ * g₂)).1 = g₂.1; group
          rw [h1] at this; exact this.symm)
      have hcard_eq : (Finset.univ.filter (fun L : StratumFix q ℓ m => Quotient.mk R L = o)).card =
          Fintype.card (sylowP q ⧸ Subgroup.zpowers ℓ) := by
        symm
        refine Finset.card_bij (fun x _ => φ x) ?_ ?_ ?_
        · intro x _
          obtain ⟨g, rfl⟩ := Quotient.exists_rep x
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : Quotient.mk R (φ (QuotientGroup.mk g)) = Quotient.mk R L₀ :=
            Quotient.sound ⟨g⁻¹, by dsimp [φ]; rw [← mul_smul]; change (g⁻¹ * g).1 • L₀.1 = L₀.1; simp⟩
          rw [this, Quotient.out_eq]
        · intro x₁ _ x₂ _ hEq
          obtain ⟨g₁, rfl⟩ := Quotient.exists_rep x₁
          obtain ⟨g₂, rfl⟩ := Quotient.exists_rep x₂
          apply Quotient.sound
          change (QuotientGroup.leftRel (Subgroup.zpowers ℓ)) g₁ g₂
          rw [QuotientGroup.leftRel_apply, ← hstab]
          have hval : g₁.1 • L₀.1 = g₂.1 • L₀.1 := congrArg Subtype.val hEq
          have := congrArg (g₁⁻¹.1 • ·) hval
          rw [← mul_smul, ← mul_smul] at this
          have h1 : g₁⁻¹.1 * g₁.1 = 1 := by change (g₁⁻¹ * g₁).1 = 1; simp
          have h2 : g₁⁻¹.1 * g₂.1 = (g₁⁻¹ * g₂).1 := rfl
          rw [h1, one_smul, h2] at this; exact this.symm
        · intro L hL
          have hqeq : Quotient.mk R L₀ = Quotient.mk R L := by
            rw [Quotient.out_eq, (Finset.mem_filter.mp hL).2]
          rcases Quotient.exact hqeq with ⟨g, hg⟩
          exact ⟨QuotientGroup.mk g, Finset.mem_univ _, Subtype.ext hg⟩
      rw [hcard_eq, ← Nat.card_eq_fintype_card]
      have hlag := Subgroup.card_mul_index (Subgroup.zpowers ℓ)
      rw [natCard_sylowP] at hlag
      have hcard_zpow : Nat.card (Subgroup.zpowers ℓ) = q := by
        rw [Nat.card_zpowers]
        have hne : ℓ ≠ 1 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
          rcases hℓ with rfl | rfl <;> intro h1 <;>
            · have := congrArg (fun x => (sylowToVec x).1 0) h1
              simp [ellB, ellC, sylowToVec_sylowElem, sylowToVec_one] at this
        have hdvd : orderOf ℓ ∣ q := orderOf_dvd_of_pow_eq_one
          ((isElemAbelian_sylowP_subgroup q ⊤).2 ℓ trivial)
        rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
        · exact (hne (orderOf_eq_one_iff.mp h1)).elim
        · exact hq'
      rw [hcard_zpow] at hlag
      have hidx : (Subgroup.zpowers ℓ).index = q ^ 5 := by
        have hpos : 0 < q := hq.pos
        have : q * (Subgroup.zpowers ℓ).index = q * q ^ 5 := by rw [hlag]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      simpa [Subgroup.index] using hidx
    rw [horb_card]; push_cast; rfl

/-- **Lemma 6.8** (`lem_6_8_strata`):
(a) `S(⟨ℓ_0⟩) = C(2q, q) (q!)^4 = (2q)! (q!)^2` with all squares even;
(b) mixed-stratum squares have `Stab_P(L) = ⟨ℓ⟩`;
(c) homogeneous strata contribute `2 (q!)^2 τ_q^2` for `ℓ_B` and `2 τ_q^4` for `ℓ_C`,
and `S(⟨ℓ_B⟩) = 2 (q!)^2 τ_q^2 + q^5 N_B`, `S(⟨ℓ_C⟩) = 2 τ_q^4 + q^5 N_C`. -/
theorem lem_6_8_strata (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    (S_twoq q (Subgroup.zpowers (ell0 q)) =
      ((2 * q).choose q : ℤ) * (q.factorial : ℤ) ^ 4 ∧
     S_twoq q (Subgroup.zpowers (ell0 q)) =
      ((2 * q).factorial : ℤ) * (q.factorial : ℤ) ^ 2 ∧
     ∀ L : LatinSquare (2 * q),
      L ∈ fixSet ((Subgroup.zpowers (ell0 q)).map (sylowP q).subtype) →
        squareSign L = 1) ∧
    (∀ ℓ ∈ ({ellB q, ellC q} : Finset (sylowP q)),
      ∀ L : LatinSquare (2 * q),
        L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) →
        0 < stratumOf q L → stratumOf q L < q →
        ∀ g : sylowP q, g.1 • L = L ↔ g ∈ Subgroup.zpowers ℓ) ∧
    (homogStrataSum q (ellB q) = 2 * (q.factorial : ℤ) ^ 2 * (tauQ q) ^ 2) ∧
    (homogStrataSum q (ellC q) = 2 * (tauQ q) ^ 4) ∧
    (S_twoq q (Subgroup.zpowers (ellB q)) =
      2 * (q.factorial : ℤ) ^ 2 * (tauQ q) ^ 2 + (q : ℤ) ^ 5 * NB q) ∧
    (S_twoq q (Subgroup.zpowers (ellC q)) =
      2 * (tauQ q) ^ 4 + (q : ℤ) ^ 5 * NC q) := by
  refine ⟨lem_6_8_partA q hq hodd, lem_6_8_partB q hq hodd,
    lem_6_8_homogB q hq hodd, lem_6_8_homogC q hq hodd, ?_, ?_⟩
  · rw [lem_6_8_decomp q hq hodd (ellB q) (by simp), lem_6_8_homogB q hq hodd]; rfl
  · rw [lem_6_8_decomp q hq hodd (ellC q) (by simp), lem_6_8_homogC q hq hodd]; rfl

end RankOneFactorAndStrata

section PropRankOne

/-! ### Babbage's Congruence, Normalization, and Proposition 6.9 -/

/-- For an odd prime `q`, `C(2q, q) ≡ 2 (mod q^2)` (Babbage's congruence). -/
lemma babbage_congruence {q : ℕ} (hq : q.Prime) (hodd : q ≠ 2) :
    ((2 * q).choose q : ℤ) ≡ 2 [ZMOD (q : ℤ) ^ 2] := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  -- Step 1: `C(2q, q) * (q - 1)! = 2 * ∏_{i ∈ Ico 1 q} (q + i)` in `ℕ`
  have hfac_prod : ∀ m : ℕ, (∏ i ∈ Finset.Ico 1 (m + 1), i) = m.factorial := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_Ico_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]
  have h2q_fac : (2 * q).factorial =
      2 * q ^ 2 * (q - 1).factorial * ∏ i ∈ Finset.Ico 1 q, (q + i) := by
    have h1 : (2 * q).factorial = ∏ i ∈ Finset.Ico 1 (2 * q + 1), i := (hfac_prod (2 * q)).symm
    have hsplit1 : Finset.Ico 1 (2 * q + 1) = Finset.Ico 1 (q + 1) ∪ Finset.Ico (q + 1) (2 * q + 1) := by
      ext k; simp only [Finset.mem_union, Finset.mem_Ico]; have := hq.pos; omega
    have hdisj1 : Disjoint (Finset.Ico 1 (q + 1)) (Finset.Ico (q + 1) (2 * q + 1)) := by
      rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
    have h2 : (∏ i ∈ Finset.Ico (q + 1) (2 * q + 1), i) =
        (2 * q) * ∏ i ∈ Finset.Ico 1 q, (q + i) := by
      have htop : Finset.Ico (q + 1) (2 * q + 1) = insert (2 * q) (Finset.Ico (q + 1) (2 * q)) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Ico]; have := hq.pos; omega
      have hnot : 2 * q ∉ Finset.Ico (q + 1) (2 * q) := by simp
      rw [htop, Finset.prod_insert hnot]
      congr 1
      refine Finset.prod_bij (fun k _ => k - q) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
      · intro k₁ hk₁ k₂ hk₂ hEq; simp only [Finset.mem_Ico] at hk₁ hk₂; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi
        exact ⟨q + i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    rw [h1, hsplit1, Finset.prod_union hdisj1, hfac_prod, h2]
    have hqfac : q.factorial = q * (q - 1).factorial := (Nat.mul_factorial_pred hq.ne_zero).symm
    rw [hqfac]; ring
  have hch := Nat.choose_mul_factorial_mul_factorial (show q ≤ 2 * q by omega)
  have h2qm : 2 * q - q = q := by omega
  rw [h2qm, h2q_fac] at hch
  have hqfac : q.factorial = q * (q - 1).factorial := (Nat.mul_factorial_pred hq.ne_zero).symm
  rw [hqfac] at hch
  have hrel : (2 * q).choose q * (q - 1).factorial = 2 * ∏ i ∈ Finset.Ico 1 q, (q + i) := by
    have hpos : 0 < q ^ 2 * (q - 1).factorial :=
      Nat.mul_pos (pow_pos hq.pos 2) (Nat.factorial_pos _)
    have hmul : (q ^ 2 * (q - 1).factorial) * ((2 * q).choose q * (q - 1).factorial) =
        (q ^ 2 * (q - 1).factorial) * (2 * ∏ i ∈ Finset.Ico 1 q, (q + i)) := by
      linarith [hch]
    exact Nat.eq_of_mul_eq_mul_left hpos hmul
  -- Step 2: Expand `∏_{i ∈ s} (q + i) ≡ ∏_{i ∈ s} i + q * ∑_{i ∈ s} ∏_{j ∈ s.erase i} j [ZMOD q^2]`
  have hexpand : ∀ s : Finset ℕ,
      (∏ i ∈ s, ((q : ℤ) + (i : ℤ))) ≡
        (∏ i ∈ s, (i : ℤ)) + (q : ℤ) * ∑ i ∈ s, ∏ j ∈ s.erase i, (j : ℤ) [ZMOD (q : ℤ) ^ 2] := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha]
      have hterm : ∑ x ∈ s, ∏ j ∈ (insert a s).erase x, (j : ℤ) =
          (a : ℤ) * ∑ x ∈ s, ∏ j ∈ s.erase x, (j : ℤ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : a ≠ x := fun h => ha (h ▸ hx)
        have herase : (insert a s).erase x = insert a (s.erase x) := by
          ext y; simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hyx, rfl | hys⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hyx, hys⟩
          · rintro (rfl | ⟨hyx, hys⟩)
            · exact ⟨hne, Or.inl rfl⟩
            · exact ⟨hyx, Or.inr hys⟩
        rw [herase, Finset.prod_insert (by simp [ha])]
      rw [hterm]
      have hq2 : (q : ℤ) ^ 2 ≡ 0 [ZMOD (q : ℤ) ^ 2] := Int.modEq_zero_iff_dvd.mpr dvd_rfl
      calc ((q : ℤ) + (a : ℤ)) * ∏ i ∈ s, ((q : ℤ) + (i : ℤ))
          ≡ ((q : ℤ) + (a : ℤ)) *
              ((∏ i ∈ s, (i : ℤ)) + (q : ℤ) * ∑ i ∈ s, ∏ j ∈ s.erase i, (j : ℤ)) [ZMOD (q : ℤ) ^ 2] :=
            Int.ModEq.mul_left _ ih
        _ = (a : ℤ) * (∏ i ∈ s, (i : ℤ)) +
              (q : ℤ) * ((∏ i ∈ s, (i : ℤ)) + (a : ℤ) * ∑ i ∈ s, ∏ j ∈ s.erase i, (j : ℤ)) +
              (q : ℤ) ^ 2 * (∑ i ∈ s, ∏ j ∈ s.erase i, (j : ℤ)) := by ring
        _ ≡ (a : ℤ) * (∏ i ∈ s, (i : ℤ)) +
              (q : ℤ) * ((∏ i ∈ s, (i : ℤ)) + (a : ℤ) * ∑ i ∈ s, ∏ j ∈ s.erase i, (j : ℤ)) +
              0 * (∑ i ∈ s, ∏ j ∈ s.erase i, (j : ℤ)) [ZMOD (q : ℤ) ^ 2] :=
            Int.ModEq.add_left _ (Int.ModEq.mul_right _ hq2)
        _ = _ := by ring
  -- Step 3: `q ∣ ∑_{i ∈ Ico 1 q} ∏_{j ∈ (Ico 1 q).erase i} j`
  have hdvd_sum : (q : ℤ) ∣ ∑ i ∈ Finset.Ico 1 q, ∏ j ∈ (Finset.Ico 1 q).erase i, (j : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have hprod_Ico : (∏ i ∈ Finset.Ico 1 q, (i : ZMod q)) = ((q - 1).factorial : ZMod q) := by
      have h := hfac_prod (q - 1)
      rw [Nat.sub_add_cancel hq.pos] at h
      rw [← Nat.cast_prod, h]
    have hterm : ∀ i ∈ Finset.Ico 1 q,
        (∏ j ∈ (Finset.Ico 1 q).erase i, (j : ZMod q)) = -(i : ZMod q)⁻¹ := by
      intro i hi
      have hne0 : (i : ZMod q) ≠ 0 := by
        simp only [Finset.mem_Ico] at hi
        intro h0
        have := (ZMod.natCast_eq_zero_iff i q).mp h0
        exact absurd (Nat.le_of_dvd hi.1 this) (not_le_of_gt hi.2)
      have hmul : (i : ZMod q) * (∏ j ∈ (Finset.Ico 1 q).erase i, (j : ZMod q)) = -1 := by
        rw [Finset.mul_prod_erase _ _ hi, hprod_Ico, ZMod.wilsons_lemma q]
      calc (∏ j ∈ (Finset.Ico 1 q).erase i, (j : ZMod q))
          = (i : ZMod q)⁻¹ * ((i : ZMod q) * ∏ j ∈ (Finset.Ico 1 q).erase i, (j : ZMod q)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hne0, one_mul]
        _ = (i : ZMod q)⁻¹ * -1 := by rw [hmul]
        _ = -(i : ZMod q)⁻¹ := by ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    have hbij : (∑ i ∈ Finset.Ico 1 q, (i : ZMod q)⁻¹) =
        ∑ x ∈ (Finset.univ : Finset (ZMod q)).erase 0, x := by
      refine Finset.sum_bij (fun i _ => (i : ZMod q)⁻¹) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Ico] at hi
        have hne0 : (i : ZMod q) ≠ 0 := fun h0 =>
          absurd (Nat.le_of_dvd hi.1 ((ZMod.natCast_eq_zero_iff i q).mp h0)) (not_le_of_gt hi.2)
        exact Finset.mem_erase.mpr ⟨inv_ne_zero hne0, Finset.mem_univ _⟩
      · intro i₁ hi₁ i₂ hi₂ hEq
        have heq := inv_injective hEq
        simp only [Finset.mem_Ico] at hi₁ hi₂
        have hval := congrArg ZMod.val heq
        rwa [ZMod.val_natCast_of_lt hi₁.2, ZMod.val_natCast_of_lt hi₂.2] at hval
      · intro x hx
        have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
        have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
        have hpos : 0 < x⁻¹.val := Nat.pos_of_ne_zero fun h => hinv0 ((ZMod.val_eq_zero _).mp h)
        refine ⟨x⁻¹.val, Finset.mem_Ico.mpr ⟨hpos, x⁻¹.val_lt⟩, ?_⟩
        rw [ZMod.natCast_zmod_val, inv_inv]
      · intro _ _; rfl
    rw [hbij]
    have hsum0 := sum_univ_zmod_odd (hq.odd_of_ne_two hodd)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), zero_add] at hsum0
    rw [hsum0, neg_zero]
  -- Step 4: `∏ (q + i) ≡ (q - 1)! [ZMOD q^2]`, then cancel `(q - 1)!`
  have hprod_cong : (∏ i ∈ Finset.Ico 1 q, ((q : ℤ) + (i : ℤ))) ≡ ((q - 1).factorial : ℤ) [ZMOD (q : ℤ) ^ 2] := by
    rcases hdvd_sum with ⟨k, hk⟩
    have h1 := hexpand (Finset.Ico 1 q)
    rw [hk] at h1
    have hfac_eq : (∏ i ∈ Finset.Ico 1 q, (i : ℤ)) = ((q - 1).factorial : ℤ) := by
      have h := hfac_prod (q - 1); rw [Nat.sub_add_cancel hq.pos] at h; rw [← Nat.cast_prod, h]
    rw [hfac_eq] at h1
    have hq2k : (q : ℤ) * ((q : ℤ) * k) ≡ 0 [ZMOD (q : ℤ) ^ 2] :=
      Int.modEq_zero_iff_dvd.mpr ⟨k, by ring⟩
    calc (∏ i ∈ Finset.Ico 1 q, ((q : ℤ) + (i : ℤ)))
        ≡ ((q - 1).factorial : ℤ) + (q : ℤ) * ((q : ℤ) * k) [ZMOD (q : ℤ) ^ 2] := h1
      _ ≡ ((q - 1).factorial : ℤ) + 0 [ZMOD (q : ℤ) ^ 2] := Int.ModEq.add_left _ hq2k
      _ = ((q - 1).factorial : ℤ) := add_zero _
  have hrelZ : ((2 * q).choose q : ℤ) * ((q - 1).factorial : ℤ) =
      2 * ∏ i ∈ Finset.Ico 1 q, ((q : ℤ) + (i : ℤ)) := by
    have h := congrArg (Nat.cast (R := ℤ)) hrel
    push_cast at h; exact h
  have hmul_cong : ((2 * q).choose q : ℤ) * ((q - 1).factorial : ℤ) ≡
      2 * ((q - 1).factorial : ℤ) [ZMOD (q : ℤ) ^ 2] := by
    rw [hrelZ]; exact Int.ModEq.mul_left 2 hprod_cong
  have hcop : IsCoprime ((q - 1).factorial : ℤ) ((q : ℤ) ^ 2) := by
    have hndvd_lt : ∀ k < q, ¬ q ∣ k.factorial := by
      intro k
      induction k with
      | zero => intro _ hdvd; exact hq.not_dvd_one hdvd
      | succ k ih =>
        intro hk hdvd
        rw [Nat.factorial_succ] at hdvd
        rcases hq.dvd_mul.mp hdvd with h1 | h2
        · exact absurd (Nat.le_of_dvd (Nat.succ_pos k) h1) (not_le_of_gt hk)
        · exact ih (Nat.lt_of_succ_lt hk) h2
    have hndvd : ¬ q ∣ (q - 1).factorial := hndvd_lt (q - 1) (Nat.sub_lt hq.pos Nat.one_pos)
    have hnat : Nat.Coprime (q - 1).factorial (q ^ 2) :=
      Nat.Coprime.pow_right 2 (hq.coprime_iff_not_dvd.mpr hndvd).symm
    exact_mod_cast hnat.isCoprime
  have hdvd : (q : ℤ) ^ 2 ∣ (((2 * q).choose q : ℤ) - 2) * ((q - 1).factorial : ℤ) := by
    have h := Int.modEq_iff_dvd.mp hmul_cong.symm
    convert h using 1; ring
  have hdvd' : (q : ℤ) ^ 2 ∣ ((2 * q).choose q : ℤ) - 2 :=
    (hcop.symm.dvd_of_dvd_mul_right hdvd)
  exact (Int.modEq_iff_dvd.mpr hdvd').symm

/-- Normalization identity `Δ_n = n! (n - 1)! D_n` for positive even `n`. -/
lemma delta_eq_fac_mul_reducedDelta (n : ℕ) (hn : 0 < n) (heven : Even n) :
    delta n = (n.factorial : ℤ) * ((n - 1).factorial : ℤ) * reducedDelta n := by
  classical
  rw [delta_eq_sum_squareSign]
  unfold reducedDelta
  let Red := Finset.univ.filter (fun L : LatinSquare n => IsReduced L)
  let Stab0 := { σ : Equiv.Perm (Fin n) // σ ⟨0, hn⟩ = ⟨0, hn⟩ }
  let Dom := Equiv.Perm (Fin n) × Stab0 × Red
  let build (t : Dom) : LatinSquare n := (t.2.1.1, (1 : Equiv.Perm (Fin n)), t.1) • t.2.2.1
  have hbij : (∑ L : LatinSquare n, (squareSign L : ℤ)) =
      ∑ t : Dom, (squareSign (build t) : ℤ) := by
    symm
    refine Finset.sum_bij (fun t _ => build t) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨τ₁, ⟨σ₁, hσ₁⟩, ⟨L₁, hL₁⟩⟩ _ ⟨τ₂, ⟨σ₂, hσ₂⟩, ⟨L₂, hL₂⟩⟩ _ hEq
      have hr1 := (Finset.mem_filter.mp hL₁).2 hn
      have hr2 := (Finset.mem_filter.mp hL₂).2 hn
      have hτ : τ₁ = τ₂ := by
        apply Equiv.Perm.ext; intro c
        have h := congrArg (fun M => M.entry ⟨0, hn⟩ c) hEq
        change τ₁ (L₁.entry (σ₁.symm ⟨0, hn⟩) c) = τ₂ (L₂.entry (σ₂.symm ⟨0, hn⟩) c) at h
        have hs1 : σ₁.symm ⟨0, hn⟩ = ⟨0, hn⟩ := (Equiv.symm_apply_eq σ₁).mpr hσ₁.symm
        have hs2 : σ₂.symm ⟨0, hn⟩ = ⟨0, hn⟩ := (Equiv.symm_apply_eq σ₂).mpr hσ₂.symm
        rw [hs1, hs2, hr1.1 c, hr2.1 c] at h
        exact h
      subst hτ
      have hσ : σ₁ = σ₂ := by
        apply Equiv.Perm.ext; intro r
        have h := congrArg (fun M => M.entry (σ₁ r) ⟨0, hn⟩) hEq
        change τ₁ (L₁.entry (σ₁.symm (σ₁ r)) ⟨0, hn⟩) =
            τ₁ (L₂.entry (σ₂.symm (σ₁ r)) ⟨0, hn⟩) at h
        rw [Equiv.symm_apply_apply, hr1.2 r, hr2.2] at h
        have h2 := τ₁.injective h
        exact (Equiv.symm_apply_eq σ₂).mp h2.symm
      subst hσ
      have hL : L₁ = L₂ := by
        ext r c
        have h := congrArg (fun M => M.entry (σ₁ r) c) hEq
        change τ₁ (L₁.entry (σ₁.symm (σ₁ r)) c) = τ₁ (L₂.entry (σ₁.symm (σ₁ r)) c) at h
        rw [Equiv.symm_apply_apply] at h
        exact congrArg Fin.val (τ₁.injective h)
      subst hL; rfl
    · intro L _
      let τ : Equiv.Perm (Fin n) := rowPerm L ⟨0, hn⟩
      let L1 : LatinSquare n := ((1 : Equiv.Perm (Fin n)), (1 : Equiv.Perm (Fin n)), τ⁻¹) • L
      have hL1_row0 : ∀ c : Fin n, L1.entry ⟨0, hn⟩ c = c := fun c => by
        change τ.symm (L.entry ⟨0, hn⟩ c) = c
        exact Equiv.symm_apply_apply (rowPerm L ⟨0, hn⟩) c
      let σ : Equiv.Perm (Fin n) := (colPerm L1 ⟨0, hn⟩)⁻¹
      have hσ0 : σ ⟨0, hn⟩ = ⟨0, hn⟩ := by
        change (colPerm L1 ⟨0, hn⟩).symm ⟨0, hn⟩ = ⟨0, hn⟩
        rw [Equiv.symm_apply_eq]
        exact (hL1_row0 ⟨0, hn⟩).symm
      let L0 : LatinSquare n := (σ⁻¹, (1 : Equiv.Perm (Fin n)), (1 : Equiv.Perm (Fin n))) • L1
      have hL0_red : IsReduced L0 := fun h =>
        ⟨fun c => by
          change L1.entry (σ ⟨0, hn⟩) c = c
          rw [hσ0]; exact hL1_row0 c,
         fun r => by
          change L1.entry (σ r) ⟨0, hn⟩ = r
          exact Equiv.apply_symm_apply (colPerm L1 ⟨0, hn⟩) r⟩
      refine ⟨(τ, ⟨σ, hσ0⟩, ⟨L0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL0_red⟩⟩),
        Finset.mem_univ _, ?_⟩
      dsimp only [build, L0, L1]
      rw [← mul_smul, ← mul_smul]
      have hmul : (σ, (1 : Equiv.Perm (Fin n)), τ) * (σ⁻¹, 1, 1) * (1, 1, τ⁻¹) = 1 := by
        ext <;> simp
      rw [hmul, one_smul]
  rw [hbij]
  have hsign : ∀ t : Dom, (squareSign (build t) : ℤ) = (squareSign t.2.2.1 : ℤ) := fun t => by
    dsimp only [build]; rw [squareSign_isotopyAct_even heven]
  dsimp only [Dom]
  simp_rw [hsign, Fintype.sum_prod_type]
  simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hcard_stab : Fintype.card Stab0 = (n - 1).factorial := by
    -- Bijection `Stab0 ≃ Equiv.Perm (Fin (n - 1))`
    let eFin : { r : Fin n // r ≠ ⟨0, hn⟩ } ≃ Fin (n - 1) :=
      { toFun := fun r => ⟨r.1.val - 1, by
          have h0 : r.1.val ≠ 0 := fun h => r.2 (Fin.ext h)
          have := r.1.isLt
          omega⟩
        invFun := fun i => ⟨⟨i.val + 1, by have := i.isLt; omega⟩, fun h => by
          have h' := congrArg Fin.val h; dsimp at h'; omega⟩
        left_inv := fun r => Subtype.ext (Fin.ext (by
          have h0 : r.1.val ≠ 0 := fun h => r.2 (Fin.ext h)
          dsimp; omega))
        right_inv := fun i => Fin.ext (Nat.add_sub_cancel i.val 1) }
    let eStab : Stab0 ≃ Equiv.Perm { r : Fin n // r ≠ ⟨0, hn⟩ } :=
      { toFun := fun ⟨σ, hσ⟩ =>
          { toFun := fun r => ⟨σ r.1, fun h => r.2 (σ.injective (h.trans hσ.symm))⟩
            invFun := fun r => ⟨σ.symm r.1, fun h => r.2 (by
              have h' := congrArg σ h; rw [Equiv.apply_symm_apply, hσ] at h'; exact h')⟩
            left_inv := fun r => Subtype.ext (Equiv.symm_apply_apply σ r.1)
            right_inv := fun r => Subtype.ext (Equiv.apply_symm_apply σ r.1) }
        invFun := fun τ =>
          ⟨{ toFun := fun r => if h : r = ⟨0, hn⟩ then ⟨0, hn⟩ else (τ ⟨r, h⟩).1
             invFun := fun r => if h : r = ⟨0, hn⟩ then ⟨0, hn⟩ else (τ.symm ⟨r, h⟩).1
             left_inv := fun r => by
               by_cases h : r = ⟨0, hn⟩
               · simp [h]
               · simp only [dif_neg h, dif_neg (τ ⟨r, h⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply]
             right_inv := fun r => by
               by_cases h : r = ⟨0, hn⟩
               · simp [h]
               · simp only [dif_neg h, dif_neg (τ.symm ⟨r, h⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply] },
           by simp⟩
        left_inv := fun ⟨σ, hσ⟩ => Subtype.ext (Equiv.Perm.ext fun r => by
          by_cases h : r = ⟨0, hn⟩
          · subst h; simp [hσ]
          · simp [h])
        right_inv := fun τ => Equiv.Perm.ext fun ⟨r, hr⟩ => Subtype.ext (by simp [hr]) }
    rw [Fintype.card_congr (eStab.trans (Equiv.permCongr eFin)), Fintype.card_perm, Fintype.card_fin]
  have hsum_red : (∑ L : Red, (squareSign L.1 : ℤ)) = ∑ L ∈ Red, (squareSign L : ℤ) :=
    Finset.sum_coe_sort Red (fun L => (squareSign L : ℤ))
  rw [hcard_stab, hsum_red]
  push_cast; ring

/-- Symbol block rescaling isotopy. -/
private def symScaleIso (q : ℕ) [NeZero q] (c₀ : Fin 2) (lam : (ZMod q)ˣ) : Isotopy (2 * q) :=
  (1, 1, blockScalePerm q c₀ lam)

/-- Symbol block swap isotopy. -/
private def symSwapIso (q : ℕ) [NeZero q] : Isotopy (2 * q) :=
  (1, 1, blockSwapPerm q)

private lemma symScaleIso_conj_mem {q : ℕ} [NeZero q] (c₀ : Fin 2) (lam : (ZMod q)ˣ)
    (g : Isotopy (2 * q)) (hg : g ∈ sylowP q) :
    symScaleIso q c₀ lam * g * (symScaleIso q c₀ lam)⁻¹ ∈ sylowP q := by
  rcases hg with ⟨v, rfl⟩
  let w := Multiplicative.toAdd v
  refine ⟨Multiplicative.ofAdd (w.1, w.2.1, fun c => if c = c₀ then lam.1 * w.2.2 c else w.2.2 c), ?_⟩
  change (blockTransPerm q w.1, blockTransPerm q w.2.1,
      blockTransPerm q (fun c => if c = c₀ then lam.1 * w.2.2 c else w.2.2 c)) =
    (1 * blockTransPerm q w.1 * 1⁻¹, 1 * blockTransPerm q w.2.1 * 1⁻¹,
     blockScalePerm q c₀ lam * blockTransPerm q w.2.2 * (blockScalePerm q c₀ lam)⁻¹)
  simp [blockScalePerm_conj_blockTransPerm]

private lemma symSwapIso_conj_mem {q : ℕ} [NeZero q]
    (g : Isotopy (2 * q)) (hg : g ∈ sylowP q) :
    symSwapIso q * g * (symSwapIso q)⁻¹ ∈ sylowP q := by
  rcases hg with ⟨v, rfl⟩
  let w := Multiplicative.toAdd v
  refine ⟨Multiplicative.ofAdd (w.1, w.2.1, fun c => w.2.2 (1 - c)), ?_⟩
  change (blockTransPerm q w.1, blockTransPerm q w.2.1, blockTransPerm q (fun c => w.2.2 (1 - c))) =
    (1 * blockTransPerm q w.1 * 1⁻¹, 1 * blockTransPerm q w.2.1 * 1⁻¹,
     blockSwapPerm q * blockTransPerm q w.2.2 * (blockSwapPerm q)⁻¹)
  simp [blockSwapPerm_conj_blockTransPerm]

/-- **Proposition 6.9** (`prop_6_9_rankone`):
`Δ_{2q} ≡ q^5 (2 N_B - N_C) (mod q^6)`, `q^2 ∣ D_{2q}`, and
`2 * (D_{2q} / q^2) ≡ 2 N_B - N_C (mod q)`. -/
theorem prop_6_9_rankone (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    delta (2 * q) ≡ (q : ℤ) ^ 5 * (2 * NB q - NC q) [ZMOD (q : ℤ) ^ 6] ∧
    ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧
    2 * (reducedDelta (2 * q) / (q : ℤ) ^ 2) ≡ 2 * NB q - NC q [ZMOD (q : ℤ)] := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := hq.two_le; omega
  have hcardU : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]
  -- Step 1: `delta (2 * q) ≡ ∑_{r=1} S(H) [ZMOD q^6]` from Lemmas 6.3 and 6.6
  have h63 := (lem_6_3_orbred q hq hodd).2
  have h66 := lem_6_6_vanish q hq hodd
  have hr2_dvd : (q : ℤ) ^ 6 ∣ (q : ℤ) * ∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H := by
    rcases h66.2.2.2 with ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  have hr3_dvd : (q : ℤ) ^ 6 ∣ (q : ℤ) ^ 3 * ∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H := by
    have hsum : (q : ℤ) ^ 3 ∣ ∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H :=
      Finset.dvd_sum fun H hH =>
        (h66.2.1 H (Finset.mem_filter.mp hH).2).2
    rcases hsum with ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  have hdelta_r1 : delta (2 * q) ≡ ∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H [ZMOD (q : ℤ) ^ 6] := by
    have h2 : (q : ℤ) * (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) ≡ 0 [ZMOD (q : ℤ) ^ 6] :=
      Int.modEq_zero_iff_dvd.mpr hr2_dvd
    have h3 : (q : ℤ) ^ 3 * (∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H) ≡ 0 [ZMOD (q : ℤ) ^ 6] :=
      Int.modEq_zero_iff_dvd.mpr hr3_dvd
    calc delta (2 * q)
        ≡ (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) -
          (q : ℤ) * (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) +
          (q : ℤ) ^ 3 * (∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H) [ZMOD (q : ℤ) ^ 6] := h63
      _ ≡ (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) - 0 + 0 [ZMOD (q : ℤ) ^ 6] :=
          (Int.ModEq.sub_left _ h2).add h3
      _ = ∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H := by ring
  -- Step 2: Classify all `H ∈ sylowSubgroupsOfRank q 1` with `u 0, u 1, v 0, v 1 ≠ 0`
  -- Normalize generator to have `u 0 = 1`: unique `(u₁, v₀, v₁) : (ZMod q)ˣ^3` and `(w₀, w₁) : ZMod q × ZMod q`
  let genSub (p : (ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ × ZMod q × ZMod q) : Subgroup (sylowP q) :=
    Subgroup.zpowers (sylowElem q 1 p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2.1 p.2.2.2.2)
  have hgen_rank : ∀ p, elemRank q (genSub p) = 1 := by
    intro p
    unfold elemRank genSub
    rw [Nat.card_zpowers]
    have hne : sylowElem q 1 p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2.1 p.2.2.2.2 ≠ 1 := fun h => by
      have := congrArg (fun x => (sylowToVec x).1 0) h
      simp [sylowToVec_sylowElem, sylowToVec_one] at this
    have hdvd : orderOf (sylowElem q 1 p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2.1 p.2.2.2.2) ∣ q :=
      orderOf_dvd_of_pow_eq_one ((isElemAbelian_sylowP_subgroup q ⊤).2 _ trivial)
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
    · exact (hne (orderOf_eq_one_iff.mp h1)).elim
    · rw [hq']; simpa using Nat.log_pow hq.one_lt 1
  have hgen_inj : Function.Injective genSub := by
    rintro ⟨u₁, v₀, v₁, w₀, w₁⟩ ⟨u₁', v₀', v₁', w₀', w₁'⟩ hEq
    have hmem : sylowElem q 1 u₁.1 v₀.1 v₁.1 w₀ w₁ ∈ genSub (u₁', v₀', v₁', w₀', w₁') := by
      rw [← hEq]; exact Subgroup.mem_zpowers _
    rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨k, hk⟩
    have hpow_nat : ∃ n : ℕ, sylowElem q 1 u₁'.1 v₀'.1 v₁'.1 w₀' w₁' ^ k =
        sylowElem q 1 u₁'.1 v₀'.1 v₁'.1 w₀' w₁' ^ n := by
      have hord : sylowElem q 1 u₁'.1 v₀'.1 v₁'.1 w₀' w₁' ^ q = 1 :=
        (isElemAbelian_sylowP_subgroup q ⊤).2 _ trivial
      refine ⟨(k % (q : ℤ)).toNat, ?_⟩
      have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
      have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
      conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
    rcases hpow_nat with ⟨n, hn⟩
    rw [hn] at hk
    have hv := congrArg sylowToVec hk
    have hpow_v : ∀ (g : sylowP q) (m : ℕ), sylowToVec (g ^ m) =
        (fun a => (m : ZMod q) * (sylowToVec g).1 a,
         fun b => (m : ZMod q) * (sylowToVec g).2.1 b,
         fun c => (m : ZMod q) * (sylowToVec g).2.2 c) := fun g m => by
      induction m with
      | zero => simp [sylowToVec_one]; rfl
      | succ m ih =>
        rw [pow_succ, sylowToVec_mul, ih]
        refine Prod.ext (funext fun a => by change (m : ZMod q) * _ + _ = _; push_cast; ring)
          (Prod.ext (funext fun b => by change (m : ZMod q) * _ + _ = _; push_cast; ring)
            (funext fun c => by change (m : ZMod q) * _ + _ = _; push_cast; ring))
    rw [hpow_v, sylowToVec_sylowElem, sylowToVec_sylowElem] at hv
    have hn1 : (n : ZMod q) = 1 := by simpa using congrArg (fun p => p.1 0) hv
    rw [hn1] at hv
    refine Prod.ext (Units.ext (by simpa using (congrArg (fun p => p.1 1) hv).symm))
      (Prod.ext (Units.ext (by simpa using (congrArg (fun p => p.2.1 0) hv).symm))
        (Prod.ext (Units.ext (by simpa using (congrArg (fun p => p.2.1 1) hv).symm))
          (Prod.ext (by simpa using (congrArg (fun p => p.2.2 0) hv).symm)
            (by simpa using (congrArg (fun p => p.2.2 1) hv).symm))))
  -- Any `H ∈ sylowSubgroupsOfRank q 1` not in `range genSub` has `S_twoq q H = 0`!
  have hsum_r1 :
      (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) =
      ∑ p : (ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ × ZMod q × ZMod q, S_twoq q (genSub p) := by
    let S1 := (sylowSubgroupsOfRank q 1).filter (fun H => ∃ p, H = genSub p)
    have hsub : ∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H = ∑ H ∈ S1, S_twoq q H := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro H hH hnot
      simp only [S1, Finset.mem_filter, not_and] at hnot
      have hrank : elemRank q H = 1 := (Finset.mem_filter.mp hH).2
      let _ : Fintype (sylowP q) := Fintype.ofFinite _
      have hcardH : Nat.card H = q := by
        rw [card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H), hrank, pow_one]
      have hne : H ≠ ⊥ := by
        intro hbot; rw [hbot] at hrank; simp [elemRank, Nat.log_one_right] at hrank
      -- Pick a nontrivial element `g ∈ H`; then `H = zpowers g` (since both have card `q`!)
      have hgt1 : 1 < Nat.card H := by rw [hcardH]; exact hq.one_lt
      have hex : ∃ g : H, g ≠ 1 := by
        haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp hgt1
        exact exists_ne 1
      rcases hex with ⟨⟨g, hgH⟩, hg1⟩
      have hgne1 : g ≠ 1 := fun h => hg1 (Subtype.ext h)
      have hH_eq : H = Subgroup.zpowers g := by
        have hle : Subgroup.zpowers g ≤ H := Subgroup.zpowers_le.mpr hgH
        have hcz : Nat.card (Subgroup.zpowers g) = q := by
          rw [Nat.card_zpowers]
          have hdvd : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one
            ((isElemAbelian_sylowP_subgroup q ⊤).2 g trivial)
          rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
          · exact (hgne1 (orderOf_eq_one_iff.mp h1)).elim
          · exact hq'
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardH, hcz])).symm
      -- If any of `u 0, u 1, v 0, v 1` of `g` is `0`, `H` fixes that block -> `S_twoq q H = 0`!
      have hfix_r : ∀ a : Fin 2, (sylowToVec g).1 a = 0 → S_twoq q H = 0 := fun a ha => by
        refine h66.1 H hne (Or.inr ⟨blockEquiv q (a, 0), fun h hh => ?_⟩)
        rw [hH_eq] at hh
        rcases Subgroup.mem_zpowers_iff.mp hh with ⟨k, rfl⟩
        have hpow_nat : ∃ n : ℕ, g ^ k = g ^ n := by
          have hord : g ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 g trivial
          refine ⟨(k % (q : ℤ)).toNat, ?_⟩
          have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
          have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
          conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
          rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
        rcases hpow_nat with ⟨n, hn⟩; rw [hn]
        have hgn_r : ∀ m : ℕ, (sylowToVec (g ^ m)).1 a = 0 := fun m => by
          induction m with
          | zero => simp [sylowToVec_one]
          | succ m ih =>
            rw [pow_succ, sylowToVec_mul]
            simp [ih, ha]
        have hv := sylowToVec_val (g ^ n)
        have hrow : (g ^ n).1.1 = blockTransPerm q (sylowToVec (g ^ n)).1 := by rw [hv]
        rw [hrow, blockTransPerm_apply, hgn_r n, add_zero]
      have hfix_c : ∀ b : Fin 2, (sylowToVec g).2.1 b = 0 → S_twoq q H = 0 := fun b hb => by
        refine h66.1 H hne (Or.inl ⟨blockEquiv q (b, 0), fun h hh => ?_⟩)
        rw [hH_eq] at hh
        rcases Subgroup.mem_zpowers_iff.mp hh with ⟨k, rfl⟩
        have hpow_nat : ∃ n : ℕ, g ^ k = g ^ n := by
          have hord : g ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 g trivial
          refine ⟨(k % (q : ℤ)).toNat, ?_⟩
          have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
          have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
          conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
          rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
        rcases hpow_nat with ⟨n, hn⟩; rw [hn]
        have hgn_c : ∀ m : ℕ, (sylowToVec (g ^ m)).2.1 b = 0 := fun m => by
          induction m with
          | zero => simp [sylowToVec_one]
          | succ m ih =>
            rw [pow_succ, sylowToVec_mul]
            simp [ih, hb]
        have hv := sylowToVec_val (g ^ n)
        have hcol : (g ^ n).1.2.1 = blockTransPerm q (sylowToVec (g ^ n)).2.1 := by rw [hv]
        rw [hcol, blockTransPerm_apply, hgn_c n, add_zero]
      by_cases hu0 : (sylowToVec g).1 0 = 0; · exact hfix_r 0 hu0
      by_cases hu1 : (sylowToVec g).1 1 = 0; · exact hfix_r 1 hu1
      by_cases hv0 : (sylowToVec g).2.1 0 = 0; · exact hfix_c 0 hv0
      by_cases hv1 : (sylowToVec g).2.1 1 = 0; · exact hfix_c 1 hv1
      exfalso; apply hnot hH
      let t := ((sylowToVec g).1 0)⁻¹
      have ht : t ≠ 0 := inv_ne_zero hu0
      let g' := g ^ t.val
      have hg'H : g' ∈ H := H.pow_mem hgH t.val
      have hg'v : sylowToVec g' =
          (fun a => t * (sylowToVec g).1 a,
           fun b => t * (sylowToVec g).2.1 b,
           fun c => t * (sylowToVec g).2.2 c) := by
        have hpow_v : ∀ m : ℕ, sylowToVec (g ^ m) =
            (fun a => (m : ZMod q) * (sylowToVec g).1 a,
             fun b => (m : ZMod q) * (sylowToVec g).2.1 b,
             fun c => (m : ZMod q) * (sylowToVec g).2.2 c) := fun m => by
          induction m with
          | zero => simp [sylowToVec_one]; rfl
          | succ m ih =>
            rw [pow_succ, sylowToVec_mul, ih]
            refine Prod.ext (funext fun a => by change (m : ZMod q) * _ + _ = _; push_cast; ring)
              (Prod.ext (funext fun b => by change (m : ZMod q) * _ + _ = _; push_cast; ring)
                (funext fun c => by change (m : ZMod q) * _ + _ = _; push_cast; ring))
        rw [hpow_v, ZMod.natCast_zmod_val]
      have hg'_eq : g' = sylowElem q 1 (t * (sylowToVec g).1 1)
          (t * (sylowToVec g).2.1 0) (t * (sylowToVec g).2.1 1)
          (t * (sylowToVec g).2.2 0) (t * (sylowToVec g).2.2 1) := by
        apply sylowToVec_injective
        rw [hg'v, sylowToVec_sylowElem]
        refine Prod.ext (funext fun a => by fin_cases a <;> simp [t, inv_mul_cancel₀ hu0])
          (Prod.ext (funext fun b => by fin_cases b <;> rfl) (funext fun c => by fin_cases c <;> rfl))
      have hg'ne1 : g' ≠ 1 := fun h1 => by
        have := congrArg (fun x => (sylowToVec x).1 0) h1
        rw [hg'_eq, sylowToVec_sylowElem, sylowToVec_one] at this; exact one_ne_zero this
      have hH_eq' : H = Subgroup.zpowers g' := by
        have hle : Subgroup.zpowers g' ≤ H := Subgroup.zpowers_le.mpr hg'H
        have hcz : Nat.card (Subgroup.zpowers g') = q := by
          rw [Nat.card_zpowers]
          have hdvd : orderOf g' ∣ q := orderOf_dvd_of_pow_eq_one
            ((isElemAbelian_sylowP_subgroup q ⊤).2 g' trivial)
          rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
          · exact (hg'ne1 (orderOf_eq_one_iff.mp h1)).elim
          · exact hq'
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardH, hcz])).symm
      refine ⟨(Units.mk0 _ (mul_ne_zero ht hu1), Units.mk0 _ (mul_ne_zero ht hv0),
        Units.mk0 _ (mul_ne_zero ht hv1), t * (sylowToVec g).2.2 0, t * (sylowToVec g).2.2 1), ?_⟩
      simpa [genSub, hg'_eq] using hH_eq'
    rw [hsub]
    symm
    refine Finset.sum_bij (fun p _ => genSub p) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro p _
      simp only [S1, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hgen_rank p, p, rfl⟩
    · intro p₁ _ p₂ _ hEq; exact hgen_inj hEq
    · intro H hH
      rcases (Finset.mem_filter.mp hH).2 with ⟨p, rfl⟩
      exact ⟨p, Finset.mem_univ _, rfl⟩
  -- Step 3: Conjugate every `genSub (u₁, v₀, v₁, w₀, w₁)` to `⟨ℓ_0⟩`, `⟨ℓ_B⟩`, or `⟨ℓ_C⟩`!
  have hS_gen : ∀ (u₁ v₀ v₁ : (ZMod q)ˣ) (w₀ w₁ : ZMod q),
      S_twoq q (genSub (u₁, v₀, v₁, w₀, w₁)) =
      if w₀ = 0 ∧ w₁ = 0 then S_twoq q (Subgroup.zpowers (ell0 q))
      else if (w₀ = 0 ∧ w₁ ≠ 0) ∨ (w₀ ≠ 0 ∧ w₁ = 0) then S_twoq q (Subgroup.zpowers (ellB q))
      else S_twoq q (Subgroup.zpowers (ellC q)) := by
    intro u₁ v₀ v₁ w₀ w₁
    -- Conjugate row/col coordinates `(1, u₁; v₀, v₁)` to `(1, 1; 1, 1)`
    let ψ_rc : Isotopy (2 * q) :=
      (blockScalePerm q 1 u₁⁻¹, blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹, 1)
    have hψ_rc : ∀ g ∈ sylowP q, ψ_rc * g * ψ_rc⁻¹ ∈ sylowP q := by
      rintro _ ⟨v, rfl⟩
      let w := Multiplicative.toAdd v
      refine ⟨Multiplicative.ofAdd
        (fun a => if a = 1 then (u₁⁻¹).1 * w.1 a else w.1 a,
         fun b => if b = 0 then (v₀⁻¹).1 * w.2.1 b else (v₁⁻¹).1 * w.2.1 b,
         w.2.2), ?_⟩
      have hcol : (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹) * blockTransPerm q w.2.1 *
          (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹)⁻¹ =
          blockTransPerm q (fun b => if b = 0 then (v₀⁻¹).1 * w.2.1 b else (v₁⁻¹).1 * w.2.1 b) := by
        have hre : (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹) * blockTransPerm q w.2.1 *
            (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹)⁻¹ =
            blockScalePerm q 0 v₀⁻¹ * (blockScalePerm q 1 v₁⁻¹ * blockTransPerm q w.2.1 *
              (blockScalePerm q 1 v₁⁻¹)⁻¹) * (blockScalePerm q 0 v₀⁻¹)⁻¹ := by group
        rw [hre, blockScalePerm_conj_blockTransPerm, blockScalePerm_conj_blockTransPerm]
        congr 1; ext b; fin_cases b
        · simp only [Fin.mk_zero, ↓reduceIte, if_neg Fin.zero_ne_one]
        · simp only [Fin.mk_one, ↓reduceIte, if_neg one_ne_zero]
      change (blockTransPerm q _, blockTransPerm q _, blockTransPerm q _) =
        (blockScalePerm q 1 u₁⁻¹ * blockTransPerm q w.1 * (blockScalePerm q 1 u₁⁻¹)⁻¹,
         (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹) * blockTransPerm q w.2.1 *
          (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹)⁻¹,
         1 * blockTransPerm q w.2.2 * 1⁻¹)
      rw [blockScalePerm_conj_blockTransPerm, hcol]
      simp only [one_mul, inv_one, mul_one]
      rfl
    have hconj_rc : conjSylowSub ψ_rc hψ_rc (genSub (u₁, v₀, v₁, w₀, w₁)) =
        Subgroup.zpowers (sylowElem q 1 1 1 1 w₀ w₁) := by
      have hgen_img : (⟨ψ_rc * (sylowElem q 1 u₁.1 v₀.1 v₁.1 w₀ w₁).1 * ψ_rc⁻¹,
          hψ_rc _ (sylowElem q 1 u₁.1 v₀.1 v₁.1 w₀ w₁).2⟩ : sylowP q) =
          sylowElem q 1 1 1 1 w₀ w₁ := by
        apply Subtype.ext
        have hcol : (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹) *
            blockTransPerm q (fun b => if b = 0 then v₀.1 else v₁.1) *
            (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹)⁻¹ =
            blockTransPerm q (fun b => if b = 0 then (1 : ZMod q) else 1) := by
          have hre : (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹) *
              blockTransPerm q (fun b => if b = 0 then v₀.1 else v₁.1) *
              (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹)⁻¹ =
              blockScalePerm q 0 v₀⁻¹ * (blockScalePerm q 1 v₁⁻¹ *
                blockTransPerm q (fun b => if b = 0 then v₀.1 else v₁.1) *
                (blockScalePerm q 1 v₁⁻¹)⁻¹) * (blockScalePerm q 0 v₀⁻¹)⁻¹ := by group
          rw [hre, blockScalePerm_conj_blockTransPerm, blockScalePerm_conj_blockTransPerm]
          congr 1; ext b; fin_cases b <;>
            simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero, Units.inv_mul]
        change (blockScalePerm q 1 u₁⁻¹ * blockTransPerm q (fun a => if a = 0 then 1 else u₁.1) *
            (blockScalePerm q 1 u₁⁻¹)⁻¹,
          (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹) *
            blockTransPerm q (fun b => if b = 0 then v₀.1 else v₁.1) *
            (blockScalePerm q 0 v₀⁻¹ * blockScalePerm q 1 v₁⁻¹)⁻¹,
          1 * blockTransPerm q (fun c => if c = 0 then w₀ else w₁) * 1⁻¹) = _
        rw [blockScalePerm_conj_blockTransPerm, hcol]
        have hrow : (fun a : Fin 2 => if a = 1 then (u₁⁻¹).1 * (if a = 0 then 1 else u₁.1)
            else if a = 0 then 1 else u₁.1) = fun a => if a = 0 then (1 : ZMod q) else 1 := by
          ext a; fin_cases a <;>
            simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero, Units.inv_mul]
        rw [hrow, one_mul, inv_one, mul_one]; rfl
      unfold conjSylowSub genSub
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hgen_img
    rw [← S_twoq_conjSylowSub hodd ψ_rc hψ_rc, hconj_rc]
    -- Now normalize `(w₀, w₁)` using `symScaleIso` and `symSwapIso`!
    by_cases hw0 : w₀ = 0 <;> by_cases hw1 : w₁ = 0
    · subst hw0 hw1; simp [ell0]
    · subst hw0
      rw [if_neg (by simp [hw1]), if_pos (Or.inl ⟨rfl, hw1⟩)]
      let u : (ZMod q)ˣ := Units.mk0 w₁ hw1
      rw [← S_twoq_conjSylowSub hodd (symScaleIso q 1 u⁻¹) (symScaleIso_conj_mem 1 u⁻¹)
        (Subgroup.zpowers _)]
      refine congrArg (S_twoq q) ?_
      unfold conjSylowSub
      rw [MonoidHom.map_zpowers]
      refine congrArg Subgroup.zpowers (Subtype.ext ?_)
      change (1 * blockTransPerm q _ * 1⁻¹, 1 * blockTransPerm q _ * 1⁻¹,
        blockScalePerm q 1 u⁻¹ * blockTransPerm q (fun c => if c = 0 then 0 else w₁) *
          (blockScalePerm q 1 u⁻¹)⁻¹) = (ellB q).1
      rw [blockScalePerm_conj_blockTransPerm]
      have hsym : (fun c : Fin 2 => if c = 1 then (u⁻¹).1 * (if c = 0 then 0 else w₁)
          else if c = 0 then 0 else w₁) = fun c => if c = 0 then (0 : ZMod q) else 1 := by
        ext c; fin_cases c <;>
          simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero,
            u, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hw1]
      rw [hsym, one_mul, inv_one, mul_one]; rfl
    · subst hw1
      rw [if_neg (by simp [hw0]), if_pos (Or.inr ⟨hw0, rfl⟩)]
      let u : (ZMod q)ˣ := Units.mk0 w₀ hw0
      rw [← S_twoq_conjSylowSub hodd (symSwapIso q) symSwapIso_conj_mem (Subgroup.zpowers _)]
      have hsw : conjSylowSub (symSwapIso q) symSwapIso_conj_mem
          (Subgroup.zpowers (sylowElem q 1 1 1 1 w₀ 0)) =
          Subgroup.zpowers (sylowElem q 1 1 1 1 0 w₀) := by
        unfold conjSylowSub; rw [MonoidHom.map_zpowers]; refine congrArg Subgroup.zpowers (Subtype.ext ?_)
        change (1 * blockTransPerm q _ * 1⁻¹, 1 * blockTransPerm q _ * 1⁻¹,
          blockSwapPerm q * blockTransPerm q (fun c => if c = 0 then w₀ else 0) *
            (blockSwapPerm q)⁻¹) = _
        rw [blockSwapPerm_conj_blockTransPerm]
        have hsym : (fun c : Fin 2 => if 1 - c = 0 then w₀ else 0) =
            fun c => if c = 0 then 0 else w₀ := by ext c; fin_cases c <;> rfl
        rw [hsym, one_mul, inv_one, mul_one]; rfl
      rw [hsw, ← S_twoq_conjSylowSub hodd (symScaleIso q 1 u⁻¹) (symScaleIso_conj_mem 1 u⁻¹)
        (Subgroup.zpowers _)]
      refine congrArg (S_twoq q) ?_
      unfold conjSylowSub; rw [MonoidHom.map_zpowers]; refine congrArg Subgroup.zpowers (Subtype.ext ?_)
      change (1 * blockTransPerm q _ * 1⁻¹, 1 * blockTransPerm q _ * 1⁻¹,
        blockScalePerm q 1 u⁻¹ * blockTransPerm q (fun c => if c = 0 then 0 else w₀) *
          (blockScalePerm q 1 u⁻¹)⁻¹) = (ellB q).1
      rw [blockScalePerm_conj_blockTransPerm]
      have hsym : (fun c : Fin 2 => if c = 1 then (u⁻¹).1 * (if c = 0 then 0 else w₀)
          else if c = 0 then 0 else w₀) = fun c => if c = 0 then (0 : ZMod q) else 1 := by
        ext c; fin_cases c <;>
          simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero,
            u, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hw0]
      rw [hsym, one_mul, inv_one, mul_one]; rfl
    · rw [if_neg (by simp [hw0]), if_neg (by simp [hw0, hw1])]
      let u0 : (ZMod q)ˣ := Units.mk0 w₀ hw0
      let u1 : (ZMod q)ˣ := Units.mk0 w₁ hw1
      rw [← S_twoq_conjSylowSub hodd (symScaleIso q 0 u0⁻¹) (symScaleIso_conj_mem 0 u0⁻¹)
        (Subgroup.zpowers _)]
      have h0 : conjSylowSub (symScaleIso q 0 u0⁻¹) (symScaleIso_conj_mem 0 u0⁻¹)
          (Subgroup.zpowers (sylowElem q 1 1 1 1 w₀ w₁)) =
          Subgroup.zpowers (sylowElem q 1 1 1 1 1 w₁) := by
        unfold conjSylowSub; rw [MonoidHom.map_zpowers]; refine congrArg Subgroup.zpowers (Subtype.ext ?_)
        change (1 * blockTransPerm q _ * 1⁻¹, 1 * blockTransPerm q _ * 1⁻¹,
          blockScalePerm q 0 u0⁻¹ * blockTransPerm q (fun c => if c = 0 then w₀ else w₁) *
            (blockScalePerm q 0 u0⁻¹)⁻¹) = _
        rw [blockScalePerm_conj_blockTransPerm]
        have hsym : (fun c : Fin 2 => if c = 0 then (u0⁻¹).1 * (if c = 0 then w₀ else w₁)
            else if c = 0 then w₀ else w₁) = fun c => if c = 0 then 1 else w₁ := by
          ext c; fin_cases c <;>
            simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero,
              u0, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hw0]
        rw [hsym, one_mul, inv_one, mul_one]; rfl
      rw [h0, ← S_twoq_conjSylowSub hodd (symScaleIso q 1 u1⁻¹) (symScaleIso_conj_mem 1 u1⁻¹)
        (Subgroup.zpowers _)]
      refine congrArg (S_twoq q) ?_
      unfold conjSylowSub; rw [MonoidHom.map_zpowers]; refine congrArg Subgroup.zpowers (Subtype.ext ?_)
      change (1 * blockTransPerm q _ * 1⁻¹, 1 * blockTransPerm q _ * 1⁻¹,
        blockScalePerm q 1 u1⁻¹ * blockTransPerm q (fun c => if c = 0 then 1 else w₁) *
          (blockScalePerm q 1 u1⁻¹)⁻¹) = (ellC q).1
      rw [blockScalePerm_conj_blockTransPerm]
      have hsym : (fun c : Fin 2 => if c = 1 then (u1⁻¹).1 * (if c = 0 then 1 else w₁)
          else if c = 0 then 1 else w₁) = fun c => if c = 0 then (1 : ZMod q) else 1 := by
        ext c; fin_cases c <;>
          simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero,
            u1, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hw1]
      rw [hsym, one_mul, inv_one, mul_one]; rfl
  -- Evaluate the rank-1 sum:
  have hsum_r1_val :
      (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) =
      ((q : ℤ) - 1) ^ 3 * S_twoq q (Subgroup.zpowers (ell0 q)) +
      2 * ((q : ℤ) - 1) ^ 4 * S_twoq q (Subgroup.zpowers (ellB q)) +
      ((q : ℤ) - 1) ^ 5 * S_twoq q (Subgroup.zpowers (ellC q)) := by
    rw [hsum_r1]
    simp_rw [Fintype.sum_prod_type, hS_gen]
    have hinner :
        (∑ w₀ : ZMod q, ∑ w₁ : ZMod q,
          if w₀ = 0 ∧ w₁ = 0 then S_twoq q (Subgroup.zpowers (ell0 q))
          else if (w₀ = 0 ∧ w₁ ≠ 0) ∨ (w₀ ≠ 0 ∧ w₁ = 0) then S_twoq q (Subgroup.zpowers (ellB q))
          else S_twoq q (Subgroup.zpowers (ellC q))) =
        S_twoq q (Subgroup.zpowers (ell0 q)) +
        2 * ((q : ℤ) - 1) * S_twoq q (Subgroup.zpowers (ellB q)) +
        ((q : ℤ) - 1) ^ 2 * S_twoq q (Subgroup.zpowers (ellC q)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
      have hw0_zero :
          (∑ w₁ : ZMod q,
            if (0 : ZMod q) = 0 ∧ w₁ = 0 then S_twoq q (Subgroup.zpowers (ell0 q))
            else if ((0 : ZMod q) = 0 ∧ w₁ ≠ 0) ∨ ((0 : ZMod q) ≠ 0 ∧ w₁ = 0)
              then S_twoq q (Subgroup.zpowers (ellB q))
            else S_twoq q (Subgroup.zpowers (ellC q))) =
          S_twoq q (Subgroup.zpowers (ell0 q)) +
          ((q : ℤ) - 1) * S_twoq q (Subgroup.zpowers (ellB q)) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
        congr 1
        · simp
        · have hnz : ∀ w₁ ∈ (Finset.univ : Finset (ZMod q)).erase 0,
              (if (0 : ZMod q) = 0 ∧ w₁ = 0 then S_twoq q (Subgroup.zpowers (ell0 q))
               else if ((0 : ZMod q) = 0 ∧ w₁ ≠ 0) ∨ ((0 : ZMod q) ≠ 0 ∧ w₁ = 0)
                 then S_twoq q (Subgroup.zpowers (ellB q))
               else S_twoq q (Subgroup.zpowers (ellC q))) =
              S_twoq q (Subgroup.zpowers (ellB q)) := fun w₁ hw₁ => by
            have hne := (Finset.mem_erase.mp hw₁).1; simp [hne]
          rw [Finset.sum_congr rfl hnz, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, ZMod.card, nsmul_eq_mul, hcast]
      have hw0_nz : ∀ w₀ ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          (∑ w₁ : ZMod q,
            if w₀ = 0 ∧ w₁ = 0 then S_twoq q (Subgroup.zpowers (ell0 q))
            else if (w₀ = 0 ∧ w₁ ≠ 0) ∨ (w₀ ≠ 0 ∧ w₁ = 0) then S_twoq q (Subgroup.zpowers (ellB q))
            else S_twoq q (Subgroup.zpowers (ellC q))) =
          S_twoq q (Subgroup.zpowers (ellB q)) +
          ((q : ℤ) - 1) * S_twoq q (Subgroup.zpowers (ellC q)) := fun w₀ hw₀ => by
        have hne0 := (Finset.mem_erase.mp hw₀).1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
        congr 1
        · simp [hne0]
        · have hnz : ∀ w₁ ∈ (Finset.univ : Finset (ZMod q)).erase 0,
              (if w₀ = 0 ∧ w₁ = 0 then S_twoq q (Subgroup.zpowers (ell0 q))
               else if (w₀ = 0 ∧ w₁ ≠ 0) ∨ (w₀ ≠ 0 ∧ w₁ = 0) then S_twoq q (Subgroup.zpowers (ellB q))
               else S_twoq q (Subgroup.zpowers (ellC q))) =
              S_twoq q (Subgroup.zpowers (ellC q)) := fun w₁ hw₁ => by
            have hne1 := (Finset.mem_erase.mp hw₁).1; simp [hne0, hne1]
          rw [Finset.sum_congr rfl hnz, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, ZMod.card, nsmul_eq_mul, hcast]
      rw [hw0_zero, Finset.sum_congr rfl hw0_nz, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, nsmul_eq_mul, hcast]
      ring
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, hcardU, nsmul_eq_mul, hcast]
    ring
  -- Step 4: Substitute Lemma 6.8 and prove `q^6 ∣ Ξ` using Wilson + Babbage + Lemma 6.5!
  have h68 := lem_6_8_strata q hq hodd
  have h65 := lem_6_5_complete q hq hodd
  let Ξ : ℤ :=
    ((q : ℤ) - 1) ^ 3 * ((2 * q).choose q : ℤ) * (q.factorial : ℤ) ^ 4 +
    4 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2 * (tauQ q) ^ 2 +
    2 * ((q : ℤ) - 1) ^ 5 * (tauQ q) ^ 4
  have hr1_eq : (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) =
      Ξ + (q : ℤ) ^ 5 * (2 * ((q : ℤ) - 1) ^ 4 * NB q + ((q : ℤ) - 1) ^ 5 * NC q) := by
    rw [hsum_r1_val, h68.1.1, h68.2.2.2.2.1, h68.2.2.2.2.2]; dsimp [Ξ]; ring
  have hXi_dvd : (q : ℤ) ^ 6 ∣ Ξ := by
    have hqfac : (q.factorial : ℤ) = (q : ℤ) * ((q - 1).factorial : ℤ) := by
      exact_mod_cast (Nat.mul_factorial_pred hq.ne_zero).symm
    have hfactor : Ξ = (q : ℤ) ^ 4 * (((q : ℤ) - 1) ^ 3 *
        (2 * (((q - 1).factorial : ℤ) ^ 2 + ((q : ℤ) - 1) * (tQ q) ^ 2) ^ 2 +
         (((2 * q).choose q : ℤ) - 2) * ((q - 1).factorial : ℤ) ^ 4)) := by
      dsimp [Ξ]; rw [hqfac, h65.1]; ring
    rw [hfactor]
    -- Both terms inside are divisible by `q^2`!
    have hterm1 : (q : ℤ) ∣ (((q - 1).factorial : ℤ) ^ 2 + ((q : ℤ) - 1) * (tQ q) ^ 2) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have htq' : (tQ q : ZMod q) = -1 := by
        simpa using (ZMod.intCast_eq_intCast_iff (tQ q) (-1) q).mpr h65.2.1
      push_cast; rw [ZMod.wilsons_lemma q, htq', ZMod.natCast_self]; ring
    have hterm1_sq : (q : ℤ) ^ 2 ∣
        2 * (((q - 1).factorial : ℤ) ^ 2 + ((q : ℤ) - 1) * (tQ q) ^ 2) ^ 2 := by
      rcases hterm1 with ⟨k, hk⟩; exact ⟨2 * k ^ 2, by rw [hk]; ring⟩
    have hterm2 : (q : ℤ) ^ 2 ∣ (((2 * q).choose q : ℤ) - 2) * ((q - 1).factorial : ℤ) ^ 4 := by
      have hbab : (q : ℤ) ^ 2 ∣ ((2 * q).choose q : ℤ) - 2 :=
        Int.modEq_iff_dvd.mp (babbage_congruence hq hodd).symm
      exact dvd_mul_of_dvd_left hbab _
    have hsum_q2 : (q : ℤ) ^ 2 ∣ ((q : ℤ) - 1) ^ 3 *
        (2 * (((q - 1).factorial : ℤ) ^ 2 + ((q : ℤ) - 1) * (tQ q) ^ 2) ^ 2 +
         (((2 * q).choose q : ℤ) - 2) * ((q - 1).factorial : ℤ) ^ 4) :=
      dvd_mul_of_dvd_right (dvd_add hterm1_sq hterm2) _
    rcases hsum_q2 with ⟨m, hm⟩
    exact ⟨m, by rw [hm]; ring⟩
  -- Hence `delta (2 * q) ≡ q^5 * (2 * NB - NC) [ZMOD q^6]`
  have hdelta_cong : delta (2 * q) ≡ (q : ℤ) ^ 5 * (2 * NB q - NC q) [ZMOD (q : ℤ) ^ 6] := by
    have hcoef : (q : ℤ) ∣ (2 * ((q : ℤ) - 1) ^ 4 * NB q + ((q : ℤ) - 1) ^ 5 * NC q) -
        (2 * NB q - NC q) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast; rw [ZMod.natCast_self]; ring
    have hq6_coef : (q : ℤ) ^ 6 ∣
        (q : ℤ) ^ 5 * (2 * ((q : ℤ) - 1) ^ 4 * NB q + ((q : ℤ) - 1) ^ 5 * NC q) -
        (q : ℤ) ^ 5 * (2 * NB q - NC q) := by
      rcases hcoef with ⟨k, hk⟩
      exact ⟨k, by linear_combination (q : ℤ) ^ 5 * hk⟩
    have hXi0 : Ξ ≡ 0 [ZMOD (q : ℤ) ^ 6] := Int.modEq_zero_iff_dvd.mpr hXi_dvd
    have h1 : (q : ℤ) ^ 5 * (2 * ((q : ℤ) - 1) ^ 4 * NB q + ((q : ℤ) - 1) ^ 5 * NC q) ≡
        (q : ℤ) ^ 5 * (2 * NB q - NC q) [ZMOD (q : ℤ) ^ 6] :=
      (Int.modEq_iff_dvd.mpr hq6_coef).symm
    calc delta (2 * q)
        ≡ Ξ + (q : ℤ) ^ 5 * (2 * ((q : ℤ) - 1) ^ 4 * NB q + ((q : ℤ) - 1) ^ 5 * NC q)
            [ZMOD (q : ℤ) ^ 6] := by rwa [← hr1_eq]
      _ ≡ 0 + (q : ℤ) ^ 5 * (2 * NB q - NC q) [ZMOD (q : ℤ) ^ 6] := hXi0.add h1
      _ = (q : ℤ) ^ 5 * (2 * NB q - NC q) := zero_add _
  -- Step 5: Deduce `q^2 ∣ D_{2q}` and `2 * (D_{2q} / q^2) ≡ 2 N_B - N_C [ZMOD q]`!
  have hnorm := delta_eq_fac_mul_reducedDelta (2 * q) (by have := hq.pos; omega) (even_two_mul q)
  -- Factor `(2q)! * (2q - 1)! = q^3 * Λ` with `Λ ≡ 2 (mod q)`
  have hfac_prod : ∀ m : ℕ, (∏ i ∈ Finset.Ico 1 (m + 1), i) = m.factorial := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.prod_Ico_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]
  let P2 := ∏ i ∈ Finset.Ico 1 q, (q + i)
  have h2qm1_fac : (2 * q - 1).factorial = q * (q - 1).factorial * P2 := by
    have h1 : (2 * q - 1).factorial = ∏ i ∈ Finset.Ico 1 (2 * q), i := by
      have := hfac_prod (2 * q - 1)
      have h2 : 2 * q - 1 + 1 = 2 * q := by have := hq.pos; omega
      rw [h2] at this; exact this.symm
    have hsplit : Finset.Ico 1 (2 * q) = Finset.Ico 1 (q + 1) ∪ Finset.Ico (q + 1) (2 * q) := by
      ext k; simp only [Finset.mem_union, Finset.mem_Ico]; have := hq.pos; omega
    have hdisj : Disjoint (Finset.Ico 1 (q + 1)) (Finset.Ico (q + 1) (2 * q)) := by
      rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
    have hP2 : (∏ i ∈ Finset.Ico (q + 1) (2 * q), i) = P2 := by
      dsimp [P2]
      refine Finset.prod_bij (fun k _ => k - q) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
      · intro k₁ hk₁ k₂ hk₂ hEq; simp only [Finset.mem_Ico] at hk₁ hk₂; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi
        exact ⟨q + i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    rw [h1, hsplit, Finset.prod_union hdisj, hfac_prod, hP2]
    have hqfac : q.factorial = q * (q - 1).factorial := (Nat.mul_factorial_pred hq.ne_zero).symm
    rw [hqfac]
  have h2q_fac : (2 * q).factorial = 2 * q * (2 * q - 1).factorial :=
    (Nat.mul_factorial_pred (show 2 * q ≠ 0 by have := hq.pos; omega)).symm
  let Λ : ℤ := 2 * ((q - 1).factorial : ℤ) ^ 2 * (P2 : ℤ) ^ 2
  have hfac_eq : ((2 * q).factorial : ℤ) * ((2 * q - 1).factorial : ℤ) = (q : ℤ) ^ 3 * Λ := by
    have hnat : (2 * q).factorial * (2 * q - 1).factorial =
        q ^ 3 * (2 * (q - 1).factorial ^ 2 * P2 ^ 2) := by
      rw [h2q_fac, h2qm1_fac]; ring
    dsimp only [Λ]
    exact_mod_cast hnat
  have hΛ_mod : (Λ : ZMod q) = 2 := by
    have hP2_mod : (P2 : ZMod q) = -1 := by
      dsimp [P2]; push_cast
      have hcongr : (∏ i ∈ Finset.Ico 1 q, ((q : ZMod q) + (i : ZMod q))) =
          ∏ i ∈ Finset.Ico 1 q, (i : ZMod q) :=
        Finset.prod_congr rfl fun i _ => by rw [ZMod.natCast_self, zero_add]
      rw [hcongr]
      have h := hfac_prod (q - 1); rw [Nat.sub_add_cancel hq.pos] at h
      have hcast' : (∏ i ∈ Finset.Ico 1 q, (i : ZMod q)) = ((q - 1).factorial : ZMod q) := by
        rw [← Nat.cast_prod, h]
      rw [hcast', ZMod.wilsons_lemma q]
    dsimp [Λ]; push_cast; rw [ZMod.wilsons_lemma q, hP2_mod]; ring
  have hΛ_cop : IsCoprime Λ (q : ℤ) := by
    have hne0 : (Λ : ZMod q) ≠ 0 := by
      rw [hΛ_mod]
      intro h20
      have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h20)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact hq.ne_one h1
      · exact hodd h2
    have hndvd : ¬ ((q : ℤ) ∣ Λ) := fun h => hne0 ((ZMod.intCast_zmod_eq_zero_iff_dvd Λ q).mpr h)
    exact ((Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hndvd).symm
  -- Cancel `q^3` from `q^3 * Λ * D_{2q} ≡ q^5 * (2 N_B - N_C) [ZMOD q^6]`
  rw [hnorm, hfac_eq] at hdelta_cong
  have hq3_cancel : Λ * reducedDelta (2 * q) ≡ (q : ℤ) ^ 2 * (2 * NB q - NC q) [ZMOD (q : ℤ) ^ 3] := by
    have hdvd6 := Int.modEq_iff_dvd.mp hdelta_cong.symm
    rcases hdvd6 with ⟨k, hk⟩
    have hq3_ne : (q : ℤ) ^ 3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast hq.ne_zero)
    have h3 : Λ * reducedDelta (2 * q) - (q : ℤ) ^ 2 * (2 * NB q - NC q) = (q : ℤ) ^ 3 * k := by
      apply mul_left_cancel₀ hq3_ne
      linear_combination hk
    exact (Int.modEq_iff_dvd.mpr ⟨k, h3⟩).symm
  have hq2_dvd_prod : (q : ℤ) ^ 2 ∣ Λ * reducedDelta (2 * q) := by
    rcases Int.modEq_iff_dvd.mp hq3_cancel.symm with ⟨k, hk⟩
    exact ⟨2 * NB q - NC q + (q : ℤ) * k, by linear_combination hk⟩
  have hq2_dvd : (q : ℤ) ^ 2 ∣ reducedDelta (2 * q) :=
    (hΛ_cop.pow_right (n := 2)).symm.dvd_of_dvd_mul_left hq2_dvd_prod
  have hquot_cong : 2 * (reducedDelta (2 * q) / (q : ℤ) ^ 2) ≡ 2 * NB q - NC q [ZMOD (q : ℤ)] := by
    have hD : reducedDelta (2 * q) = (q : ℤ) ^ 2 * (reducedDelta (2 * q) / (q : ℤ) ^ 2) :=
      (Int.mul_ediv_cancel' hq2_dvd).symm
    rcases Int.modEq_iff_dvd.mp hq3_cancel.symm with ⟨k, hk⟩
    rw [hD] at hk
    have hq2_ne : (q : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hq.ne_zero)
    have h1 : Λ * (reducedDelta (2 * q) / (q : ℤ) ^ 2) - (2 * NB q - NC q) = (q : ℤ) * k := by
      apply mul_left_cancel₀ hq2_ne
      linear_combination hk
    have h0 : ((Λ * (reducedDelta (2 * q) / (q : ℤ) ^ 2) - (2 * NB q - NC q) : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr ⟨k, h1⟩
    rw [Int.cast_sub, Int.cast_mul, hΛ_mod] at h0
    have hmod' : ((2 * (reducedDelta (2 * q) / (q : ℤ) ^ 2) : ℤ) : ZMod q) =
        ((2 * NB q - NC q : ℤ) : ZMod q) := by
      rw [Int.cast_mul, Int.cast_ofNat]
      exact sub_eq_zero.mp h0
    exact (ZMod.intCast_eq_intCast_iff _ _ q).mp hmod'
  exact ⟨by rw [hnorm, hfac_eq]; exact hdelta_cong, hq2_dvd, hquot_cong⟩

end PropRankOne

end AlonTarsi.Proofs

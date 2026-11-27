/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Defs.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Basic Identities for Latin Squares, Signs, Isotopies, and Normalization

Proves the Section 1 and Section 2 identities directly from Lean's standard axioms:
- `odd_order_delta_zero_proved`: `L^e_n = L^o_n` and `Δ_n = 0` for odd `n > 1`.
- `eq_janssen_proved`: Janssen's identity `sgn_row(L) * sgn_col(L) * sgn_sym(L) = (-1)^(n(n-1)/2)`.
- `eq_isotopy_proved`: Isotopy sign transformation formulas and invariance for even `n`.
- `eq_normal_proved`: Normalization `Δ_n = n! (n - 1)! D_n` for even `n`.
- `eq_cn_reduced_proved`: `c_n = (n! n) / gcd(|D_n|, n! n)` and `q ∤ c_n ↔ M_q(n) ∣ D_n`.
-/

namespace AlonTarsi.Proofs

open AlonTarsi

/-- `Δ_n = ∑_L ε(L)`. -/
lemma delta_eq_sum (n : ℕ) :
    delta n = ∑ L : LatinSquare n, (squareSign L : ℤ) := by
  classical
  have hpart :
      (∑ L : LatinSquare n, (squareSign L : ℤ)) =
        (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1),
          (squareSign L : ℤ)) +
        (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L ≠ 1),
          (squareSign L : ℤ)) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have h1 :
      (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1),
        (squareSign L : ℤ)) = (evenCount n : ℤ) := by
    rw [evenCount]
    calc ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1), (squareSign L : ℤ)
        = ∑ _L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1), (1 : ℤ) := by
          refine Finset.sum_congr rfl fun L hL => ?_
          rw [(Finset.mem_filter.mp hL).2]; rfl
      _ = ((Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1)).card : ℤ) := by
          simp
  have hfilter :
      Finset.univ.filter (fun L : LatinSquare n => squareSign L ≠ 1) =
        Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1) := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Int.units_eq_one_or (squareSign L) with h | h <;> simp [h]
  have h2 :
      (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L ≠ 1),
        (squareSign L : ℤ)) = -(oddCount n : ℤ) := by
    rw [hfilter, oddCount]
    calc ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1), (squareSign L : ℤ)
        = ∑ _L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1), (-1 : ℤ) := by
          refine Finset.sum_congr rfl fun L hL => ?_
          rw [(Finset.mem_filter.mp hL).2]; rfl
      _ = -((Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1)).card : ℤ) := by
          simp
  rw [hpart, h1, h2, delta, sub_eq_add_neg]

/-- Row permutation of `σ • L` at `σ.1 r`. -/
lemma rowPerm_smul {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) (r : Fin n) :
    rowPerm (σ • L) (σ.1 r) = σ.2.2 * rowPerm L r * σ.2.1⁻¹ := by
  apply Equiv.ext
  intro c
  change σ.2.2 (L.entry (σ.1.symm (σ.1 r)) (σ.2.1.symm c)) =
    σ.2.2 (L.entry r (σ.2.1.symm c))
  rw [σ.1.symm_apply_apply]

/-- Column permutation of `σ • L` at `σ.2.1 c`. -/
lemma colPerm_smul {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) (c : Fin n) :
    colPerm (σ • L) (σ.2.1 c) = σ.2.2 * colPerm L c * σ.1⁻¹ := by
  apply Equiv.ext
  intro r
  change σ.2.2 (L.entry (σ.1.symm r) (σ.2.1.symm (σ.2.1 c))) =
    σ.2.2 (L.entry (σ.1.symm r) c)
  rw [σ.2.1.symm_apply_apply]

/-- Proof of Section 2 (Isotopy invariance). -/
theorem eq_isotopy_proved (n : ℕ) (σ : Isotopy n) (L : LatinSquare n) :
    rowSign (σ • L) =
      rowSign L * (Equiv.Perm.sign σ.2.1 * Equiv.Perm.sign σ.2.2) ^ n ∧
    colSign (σ • L) =
      colSign L * (Equiv.Perm.sign σ.1 * Equiv.Perm.sign σ.2.2) ^ n ∧
    (Even n → squareSign (σ • L) = squareSign L) := by
  have hrow : rowSign (σ • L) =
      rowSign L * (Equiv.Perm.sign σ.2.1 * Equiv.Perm.sign σ.2.2) ^ n := by
    unfold rowSign
    rw [← Equiv.prod_comp σ.1 (fun r => Equiv.Perm.sign (rowPerm (σ • L) r))]
    simp_rw [rowPerm_smul, map_mul, map_inv, Int.units_inv_eq_self]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_pow]
    ac_rfl
  have hcol : colSign (σ • L) =
      colSign L * (Equiv.Perm.sign σ.1 * Equiv.Perm.sign σ.2.2) ^ n := by
    unfold colSign
    rw [← Equiv.prod_comp σ.2.1 (fun c => Equiv.Perm.sign (colPerm (σ • L) c))]
    simp_rw [colPerm_smul, map_mul, map_inv, Int.units_inv_eq_self]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_pow]
    ac_rfl
  refine ⟨hrow, hcol, ?_⟩
  intro heven
  unfold squareSign
  rw [hrow, hcol]
  rcases heven with ⟨k, rfl⟩
  have hsq : ∀ u : ℤˣ, u ^ (k + k) = 1 := fun u => by
    rw [← two_mul, pow_mul]
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  rw [hsq, hsq, mul_one, mul_one]

/-- Proof of Section 1 (odd orders `n > 1`): `L^e_n = L^o_n` and `Δ_n = 0`. -/
theorem odd_order_delta_zero_proved (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    evenCount n = oddCount n ∧ delta n = 0 := by
  classical
  let r0 : Fin n := ⟨0, by omega⟩
  let r1 : Fin n := ⟨1, hn⟩
  have hne : r0 ≠ r1 := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  let τ : Equiv.Perm (Fin n) := Equiv.swap r0 r1
  let σ : Isotopy n := (τ, 1, 1)
  have hsign : ∀ L : LatinSquare n, squareSign (σ • L) = -squareSign L := by
    intro L
    have hiso := eq_isotopy_proved n σ L
    unfold squareSign
    rw [hiso.1, hiso.2.1]
    simp only [σ, τ, map_one, one_pow, mul_one, Equiv.Perm.sign_swap hne]
    rcases hodd with ⟨k, rfl⟩
    have hneg : (-1 : ℤˣ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [hneg]
    simp [mul_assoc]
  have heq : evenCount n = oddCount n := by
    unfold evenCount oddCount
    refine Finset.card_bij (fun L _ => σ • L) ?_ ?_ ?_
    · intro L hL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
      rw [hsign, hL]
    · intro L₁ _ L₂ _ h
      have h1 := congrArg (σ⁻¹ • ·) h
      simpa [inv_smul_smul] using h1
    · intro L hL
      refine ⟨σ⁻¹ • L, ?_, smul_inv_smul σ L⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
      have := hsign (σ⁻¹ • L)
      rw [smul_inv_smul, hL] at this
      exact neg_inj.mp this.symm
  refine ⟨heq, ?_⟩
  rw [delta, heq, sub_self]

/-- Sign of a fiberwise permutation `(a, b) ↦ (a, f a b)` on `α × β`. -/
lemma sign_fiberwise {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α → Equiv.Perm β) :
    Equiv.Perm.sign
      ({ toFun := fun p : α × β => (p.1, f p.1 p.2)
         invFun := fun p : α × β => (p.1, (f p.1).symm p.2)
         left_inv := fun p => by ext <;> simp
         right_inv := fun p => by ext <;> simp } : Equiv.Perm (α × β)) =
    ∏ a : α, Equiv.Perm.sign (f a) := by
  let single : α → Equiv.Perm β → Equiv.Perm (α × β) := fun a g =>
    { toFun := fun p => (p.1, if p.1 = a then g p.2 else p.2)
      invFun := fun p => (p.1, if p.1 = a then g.symm p.2 else p.2)
      left_inv := fun p => by
        apply Prod.ext
        · rfl
        · dsimp; split_ifs <;> simp
      right_inv := fun p => by
        apply Prod.ext
        · rfl
        · dsimp; split_ifs <;> simp }
  let fiberOn : Finset α → Equiv.Perm (α × β) := fun s =>
    { toFun := fun p => (p.1, if p.1 ∈ s then f p.1 p.2 else p.2)
      invFun := fun p => (p.1, if p.1 ∈ s then (f p.1).symm p.2 else p.2)
      left_inv := fun p => by
        apply Prod.ext
        · rfl
        · dsimp; split_ifs <;> simp
      right_inv := fun p => by
        apply Prod.ext
        · rfl
        · dsimp; split_ifs <;> simp }
  have hsign_single : ∀ a g, Equiv.Perm.sign (single a g) = Equiv.Perm.sign g := by
    intro a g
    let emb : β ↪ α × β := ⟨fun b => (a, b), fun _ _ h => (Prod.mk.inj h).2⟩
    let e : β ≃ Set.range emb := Equiv.ofInjective emb emb.injective
    have heq : single a g = g.extendDomain e := by
      apply Equiv.ext
      rintro ⟨a', b'⟩
      by_cases h : a' = a
      · subst h
        have h1 : g.extendDomain e (a', b') = (e (g b')).1 :=
          Equiv.Perm.extendDomain_apply_image g e b'
        rw [h1]
        simp [single, e, emb]
        rfl
      · have hmem : (a', b') ∉ Set.range emb := by
          rintro ⟨b, hb⟩; exact h (Prod.mk.inj hb).1.symm
        rw [Equiv.Perm.extendDomain_apply_not_subtype g e hmem]
        change (a', if a' = a then g b' else b') = (a', b')
        simp [h]
    rw [heq, Equiv.Perm.sign_extendDomain]
  have hsub : ∀ s : Finset α, Equiv.Perm.sign (fiberOn s) = ∏ a ∈ s, Equiv.Perm.sign (f a) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h1 : fiberOn ∅ = 1 := by
        apply Equiv.ext; intro p; apply Prod.ext <;> simp [fiberOn]
      rw [h1, map_one, Finset.prod_empty]
    | @insert a s ha ih =>
      have hmul : fiberOn (insert a s) = single a (f a) * fiberOn s := by
        apply Equiv.ext
        intro p
        apply Prod.ext
        · rfl
        · change (if p.1 ∈ insert a s then f p.1 p.2 else p.2) =
            (if p.1 = a then f a (if p.1 ∈ s then f p.1 p.2 else p.2)
             else if p.1 ∈ s then f p.1 p.2 else p.2)
          by_cases hpa : p.1 = a
          · subst hpa; simp [ha]
          · simp [hpa]
      rw [hmul, map_mul, hsign_single, ih, Finset.prod_insert ha]
  have huniv :
      ({ toFun := fun p : α × β => (p.1, f p.1 p.2)
         invFun := fun p : α × β => (p.1, (f p.1).symm p.2)
         left_inv := fun p => by ext <;> simp
         right_inv := fun p => by ext <;> simp } : Equiv.Perm (α × β)) = fiberOn Finset.univ := by
    apply Equiv.ext; intro p; apply Prod.ext <;> simp [fiberOn]
  rw [huniv]
  exact hsub Finset.univ

/-- Sign of the coordinate swap `(r, s) ↦ (s, r)` on `Fin n × Fin n` is `(-1)^(n(n-1)/2)`. -/
lemma sign_prod_swap (n : ℕ) :
    Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
  have hcard : pairs.card = n * (n - 1) / 2 := by
    have h1 : pairs.card = n.choose 2 := by
      have hbi : pairs.card = (Finset.powersetCard 2 (Finset.univ : Finset (Fin n))).card := by
        refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin n))) ?_ ?_ ?_
        · intro p hp
          have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, Finset.card_pair (ne_of_lt hlt)⟩
        · intro p₁ hp₁ p₂ hp₂ heq
          have h1 : p₁.1 < p₁.2 := (Finset.mem_filter.mp hp₁).2
          have h2 : p₂.1 < p₂.2 := (Finset.mem_filter.mp hp₂).2
          have h1mem : p₁.1 ∈ ({p₂.1, p₂.2} : Finset (Fin n)) := by
            rw [← heq]; simp
          have h2mem : p₁.2 ∈ ({p₂.1, p₂.2} : Finset (Fin n)) := by
            rw [← heq]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at h1mem h2mem
          rcases h1mem with ha | ha <;> rcases h2mem with hb | hb
          · exfalso; exact ne_of_lt h1 (ha.trans hb.symm)
          · exact Prod.ext ha hb
          · exfalso; rw [ha, hb] at h1; exact not_lt_of_gt h2 h1
          · exfalso; exact ne_of_lt h1 (ha.trans hb.symm)
        · intro s hs
          rw [Finset.mem_powersetCard] at hs
          rcases Finset.card_eq_two.mp hs.2 with ⟨a, b, hab, rfl⟩
          rcases lt_or_gt_of_ne hab with hlt | hgt
          · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
          · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, Finset.pair_comm b a⟩
      rw [hbi, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [h1, Nat.choose_two_right]
  let swapOn : Finset (Fin n × Fin n) → Equiv.Perm (Fin n × Fin n) := fun s =>
    { toFun := fun x => if x ∈ s ∨ (x.2, x.1) ∈ s then (x.2, x.1) else x
      invFun := fun x => if x ∈ s ∨ (x.2, x.1) ∈ s then (x.2, x.1) else x
      left_inv := fun x => by dsimp; split_ifs with h1 h2 <;> simp_all [or_comm]
      right_inv := fun x => by dsimp; split_ifs with h1 h2 <;> simp_all [or_comm] }
  have hsub : ∀ s : Finset (Fin n × Fin n), s ⊆ pairs →
      Equiv.Perm.sign (swapOn s) = (-1 : ℤˣ) ^ s.card := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
      have h1 : swapOn ∅ = 1 := by apply Equiv.ext; intro x; simp [swapOn]
      rw [h1, map_one, Finset.card_empty, pow_zero]
    | @insert p s hp ih =>
      have hs' : s ⊆ pairs := fun x hx => hs (Finset.mem_insert_of_mem hx)
      have hp_mem : p ∈ pairs := hs (Finset.mem_insert_self p s)
      have hp_lt : p.1 < p.2 := (Finset.mem_filter.mp hp_mem).2
      have hp_ne : p ≠ (p.2, p.1) := fun h => ne_of_lt hp_lt (Prod.mk.inj h).1
      have hmul : swapOn (insert p s) = Equiv.swap p (p.2, p.1) * swapOn s := by
        apply Equiv.ext
        intro x
        change (if x ∈ insert p s ∨ (x.2, x.1) ∈ insert p s then (x.2, x.1) else x) =
          Equiv.swap p (p.2, p.1) (if x ∈ s ∨ (x.2, x.1) ∈ s then (x.2, x.1) else x)
        by_cases hxp : x = p
        · subst hxp
          have hnot : ¬ (x ∈ s ∨ (x.2, x.1) ∈ s) := by
            rintro (h | h)
            · exact hp h
            · have := (Finset.mem_filter.mp (hs' h)).2
              exact not_lt_of_gt hp_lt this
          simp [hnot]
        · by_cases hxp' : (x.2, x.1) = p
          · have hxeq : x = (p.2, p.1) := by cases hxp'; rfl
            subst hxeq
            have hnot : ¬ ((p.2, p.1) ∈ s ∨ (p.1, p.2) ∈ s) := by
              rintro (h | h)
              · have := (Finset.mem_filter.mp (hs' h)).2
                exact not_lt_of_gt hp_lt this
              · exact hp h
            simp [hnot]
          · have hne2 : x ≠ (p.2, p.1) := fun h => hxp' (by rw [h])
            by_cases hxs : x ∈ s ∨ (x.2, x.1) ∈ s
            · have hne3 : (x.2, x.1) ≠ (p.2, p.1) :=
                fun h => hxp (Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1)
              have hmem : x ∈ insert p s ∨ (x.2, x.1) ∈ insert p s :=
                hxs.imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
              rw [if_pos hmem, if_pos hxs, Equiv.swap_apply_of_ne_of_ne hxp' hne3]
            · have hnot : ¬ (x ∈ insert p s ∨ (x.2, x.1) ∈ insert p s) := by
                rintro (h | h) <;> simp only [Finset.mem_insert] at h
                · rcases h with rfl | h
                  · exact hxp rfl
                  · exact hxs (Or.inl h)
                · rcases h with h | h
                  · exact hxp' h
                  · exact hxs (Or.inr h)
              rw [if_neg hnot, if_neg hxs, Equiv.swap_apply_of_ne_of_ne hxp hne2]
      rw [hmul, map_mul, Equiv.Perm.sign_swap hp_ne, ih hs', Finset.card_insert_of_notMem hp,
        pow_succ, mul_comm]
  have heq : Equiv.prodComm (Fin n) (Fin n) = swapOn pairs := by
    apply Equiv.ext
    intro x
    change (x.2, x.1) = if x ∈ pairs ∨ (x.2, x.1) ∈ pairs then (x.2, x.1) else x
    rcases lt_trichotomy x.1 x.2 with h | h | h
    · have hm : x ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      simp [hm]
    · have hnot : ¬ (x ∈ pairs ∨ (x.2, x.1) ∈ pairs) := by
        rintro (hm | hm) <;> simp [pairs, h] at hm
      rw [if_neg hnot]
      exact Prod.ext h.symm h
    · have hm : (x.2, x.1) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      simp [hm]
  rw [heq, hsub pairs (Finset.Subset.refl _), hcard]

/-- Proof of Section 2 (Janssen's identity). -/
theorem eq_janssen_proved (n : ℕ) (L : LatinSquare n) :
    rowSign L * colSign L * symSign L = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  let P_row : Equiv.Perm (Fin n × Fin n) :=
    { toFun := fun p => (p.1, rowPerm L p.1 p.2)
      invFun := fun p => (p.1, (rowPerm L p.1).symm p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  let Q_col : Equiv.Perm (Fin n × Fin n) :=
    { toFun := fun p => (p.1, colPerm L p.1 p.2)
      invFun := fun p => (p.1, (colPerm L p.1).symm p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  let P_col : Equiv.Perm (Fin n × Fin n) :=
    (Equiv.prodComm (Fin n) (Fin n)).trans (Q_col.trans (Equiv.prodComm (Fin n) (Fin n)))
  let Q_sym : Equiv.Perm (Fin n × Fin n) :=
    { toFun := fun p => (p.1, symPerm L p.1 p.2)
      invFun := fun p => (p.1, (symPerm L p.1).symm p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  have hcomp : P_col * P_row⁻¹ = Q_sym * Equiv.prodComm (Fin n) (Fin n) := by
    apply Equiv.ext
    rintro ⟨r, s⟩
    apply Prod.ext
    · change L.entry r ((rowPerm L r).symm s) = s
      exact (rowPerm L r).apply_symm_apply s
    · rfl
  have h1 : Equiv.Perm.sign P_row = rowSign L := sign_fiberwise (rowPerm L)
  have h2 : Equiv.Perm.sign P_col = colSign L := by
    have hconj : P_col = Equiv.prodComm (Fin n) (Fin n) * Q_col * (Equiv.prodComm (Fin n) (Fin n))⁻¹ := by
      apply Equiv.ext; rintro ⟨r, c⟩; rfl
    rw [hconj, map_mul, map_mul, map_inv, Int.units_inv_eq_self]
    have hsq : Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) *
        Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n))) with h | h <;>
        simp [h]
    calc Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) * Equiv.Perm.sign Q_col *
            Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n))
        = Equiv.Perm.sign Q_col *
            (Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n)) *
              Equiv.Perm.sign (Equiv.prodComm (Fin n) (Fin n))) := by ac_rfl
      _ = Equiv.Perm.sign Q_col := by rw [hsq, mul_one]
      _ = colSign L := sign_fiberwise (colPerm L)
  have h3 : Equiv.Perm.sign Q_sym = symSign L := sign_fiberwise (symPerm L)
  have h4 := congrArg Equiv.Perm.sign hcomp
  rw [map_mul, map_inv, Int.units_inv_eq_self, map_mul, h1, h2, h3, sign_prod_swap] at h4
  have hsym_sq : symSign L * symSign L = 1 := by
    rcases Int.units_eq_one_or (symSign L) with h | h <;> simp [h]
  calc rowSign L * colSign L * symSign L
      = (colSign L * rowSign L) * symSign L := by ac_rfl
    _ = (symSign L * (-1 : ℤˣ) ^ (n * (n - 1) / 2)) * symSign L := by rw [h4]
    _ = (symSign L * symSign L) * (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by ac_rfl
    _ = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by rw [hsym_sq, one_mul]

/-- Proof of Section 2 (Normalization): for even `n`, `Δ_n = n! (n - 1)! D_n`. -/
theorem eq_normal_proved (n : ℕ) (heven : Even n) :
    delta n = ((n.factorial * (n - 1).factorial : ℕ) : ℤ) * reducedDelta n := by
  classical
  cases n with
  | zero =>
    rw [delta_eq_sum, reducedDelta]
    have hred : Finset.univ.filter (fun L : LatinSquare 0 => IsReduced L) = Finset.univ := by
      ext L; simp [IsReduced]
    rw [hred]
    simp
  | succ m =>
    have hpos : 0 < m + 1 := Nat.succ_pos m
    let z : Fin (m + 1) := ⟨0, hpos⟩
    let Fix0 := { τ : Equiv.Perm (Fin (m + 1)) // τ z = z }
    let RedSq := { R : LatinSquare (m + 1) // IsReduced R }
    let toL : Fix0 × Equiv.Perm (Fin (m + 1)) × RedSq → LatinSquare (m + 1) :=
      fun ⟨τ, σ₃, R⟩ => ((τ.1, (1 : Equiv.Perm (Fin (m + 1))), σ₃) : Isotopy (m + 1)) • R.1
    have hbij : Function.Bijective toL := by
      refine ⟨?_, ?_⟩
      · rintro ⟨τ₁, σ₁, R₁⟩ ⟨τ₂, σ₂, R₂⟩ h
        have hrow0 : σ₁ = σ₂ := by
          apply Equiv.ext
          intro c
          have hc := congrArg (fun L : LatinSquare (m + 1) => L.entry z c) h
          have hτ1 : τ₁.1.symm z = z := by
            apply τ₁.1.injective; rw [τ₁.1.apply_symm_apply, τ₁.2]
          have hτ2 : τ₂.1.symm z = z := by
            apply τ₂.1.injective; rw [τ₂.1.apply_symm_apply, τ₂.2]
          change σ₁ (R₁.1.entry (τ₁.1.symm z) c) = σ₂ (R₂.1.entry (τ₂.1.symm z) c) at hc
          rw [hτ1, hτ2, (R₁.2 hpos).1 c, (R₂.2 hpos).1 c] at hc
          exact hc
        subst hrow0
        have hcol0 : τ₁ = τ₂ := by
          apply Subtype.ext
          apply Equiv.symm_bijective.injective
          apply Equiv.ext
          intro r
          have hr := congrArg (fun L : LatinSquare (m + 1) => L.entry r z) h
          change σ₁ (R₁.1.entry (τ₁.1.symm r) z) = σ₁ (R₂.1.entry (τ₂.1.symm r) z) at hr
          have hr' := σ₁.injective hr
          rw [(R₁.2 hpos).2 _, (R₂.2 hpos).2 _] at hr'
          exact hr'
        subst hcol0
        have hR : R₁ = R₂ := by
          apply Subtype.ext
          have hsmul : ((τ₁.1, 1, σ₁) : Isotopy (m + 1)) • R₁.1 =
              ((τ₁.1, 1, σ₁) : Isotopy (m + 1)) • R₂.1 := h
          have hinv := congrArg (((τ₁.1, 1, σ₁) : Isotopy (m + 1))⁻¹ • ·) hsmul
          simpa [inv_smul_smul] using hinv
        subst hR
        rfl
      · intro L
        let σ₃ : Equiv.Perm (Fin (m + 1)) := rowPerm L z
        let τ_inv : Equiv.Perm (Fin (m + 1)) := (colPerm L z).trans σ₃.symm
        have hτ0 : τ_inv z = z := by
          show σ₃.symm (L.entry z z) = z
          exact (rowPerm L z).symm_apply_apply z
        let τ : Fix0 := ⟨τ_inv.symm, by
          apply τ_inv.injective; rw [τ_inv.apply_symm_apply, hτ0]⟩
        let R_raw : LatinSquare (m + 1) := ((τ.1, 1, σ₃) : Isotopy (m + 1))⁻¹ • L
        have hR : IsReduced R_raw := by
          intro _
          refine ⟨fun c => ?_, fun r => ?_⟩
          · change σ₃.symm (L.entry (τ.1 z) c) = c
            rw [τ.2]
            exact (rowPerm L z).symm_apply_apply c
          · show σ₃.symm (L.entry (τ.1 r) z) = r
            show τ_inv (τ_inv.symm r) = r
            exact τ_inv.apply_symm_apply r
        refine ⟨(τ, σ₃, ⟨R_raw, hR⟩), ?_⟩
        show ((τ.1, 1, σ₃) : Isotopy (m + 1)) • (((τ.1, 1, σ₃) : Isotopy (m + 1))⁻¹ • L) = L
        exact smul_inv_smul _ L
    have hcard_fix0 : Fintype.card Fix0 = m.factorial := by
      let e : Fix0 ≃ Equiv.Perm (Fin m) :=
        { toFun := fun τ =>
            { toFun := fun i => (τ.1 i.succ).pred (by
                intro h
                have : τ.1 i.succ = τ.1 z := h.trans τ.2.symm
                exact Fin.succ_ne_zero i (τ.1.injective this))
              invFun := fun i => (τ.1.symm i.succ).pred (by
                intro h
                have hτz : τ.1.symm z = z := by
                  apply τ.1.injective; rw [τ.1.apply_symm_apply, τ.2]
                have : τ.1.symm i.succ = τ.1.symm z := h.trans hτz.symm
                exact Fin.succ_ne_zero i (τ.1.symm.injective this))
              left_inv := fun i => by simp
              right_inv := fun i => by simp }
          invFun := fun g =>
            ⟨{ toFun := fun i => Fin.cases z (fun j => (g j).succ) i
               invFun := fun i => Fin.cases z (fun j => (g.symm j).succ) i
               left_inv := fun i => by
                 refine Fin.cases ?_ ?_ i
                 · rfl
                 · intro j; simp
               right_inv := fun i => by
                 refine Fin.cases ?_ ?_ i
                 · rfl
                 · intro j; simp }, rfl⟩
          left_inv := fun τ => by
            apply Subtype.ext
            apply Equiv.ext
            intro i
            refine Fin.cases ?_ ?_ i
            · exact τ.2.symm
            · intro j; simp
          right_inv := fun g => by
            apply Equiv.ext
            intro i; simp }
      rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]
    rw [delta_eq_sum]
    rw [← Equiv.sum_comp (Equiv.ofBijective toL hbij)]
    have hsign_eq : ∀ x : Fix0 × Equiv.Perm (Fin (m + 1)) × RedSq,
        (squareSign (toL x) : ℤ) = (squareSign x.2.2.1 : ℤ) := by
      rintro ⟨τ, σ₃, R⟩
      exact congrArg Units.val ((eq_isotopy_proved (m + 1) (τ.1, 1, σ₃) R.1).2.2 heven)
    simp_rw [Equiv.ofBijective_apply, hsign_eq]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, hcard_fix0,
      Fintype.card_perm, Fintype.card_fin]
    have hred_sum :
        (∑ R : RedSq, (squareSign R.1 : ℤ)) = reducedDelta (m + 1) := by
      unfold reducedDelta
      let s : Finset (LatinSquare (m + 1)) := Finset.univ.filter (fun L => IsReduced L)
      change (∑ R : RedSq, (squareSign R.1 : ℤ)) = ∑ L ∈ s, (squareSign L : ℤ)
      rw [← Finset.sum_coe_sort s]
      let eR : RedSq ≃ { L : LatinSquare (m + 1) // L ∈ s } :=
        Equiv.subtypeEquivRight (fun L => by simp [s])
      exact Fintype.sum_equiv eR (fun R => (squareSign R.1 : ℤ))
        (fun R => (squareSign R.1 : ℤ)) (fun _ => rfl)
    rw [hred_sum]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul]
    push_cast
    ring

/-- Proof of Section 2 (Reduced formula for `c_n`). -/
theorem eq_cn_reduced_proved (n : ℕ) (heven : Even n) (hn : 0 < n) :
    cVal n = (n.factorial * n) / Nat.gcd (reducedDelta n).natAbs (n.factorial * n) ∧
    ∀ q : ℕ, q.Prime → (¬ (q ∣ cVal n) ↔ (naturalModulus q n : ℤ) ∣ reducedDelta n) := by
  have hnorm := eq_normal_proved n heven
  have hfact_eq : n.factorial ^ 3 = (n.factorial * (n - 1).factorial) * (n.factorial * n) := by
    have h1 : n.factorial = n * (n - 1).factorial := (Nat.mul_factorial_pred (ne_of_gt hn)).symm
    calc n.factorial ^ 3 = n.factorial * n.factorial * n.factorial := by ring
      _ = n.factorial * (n * (n - 1).factorial) * n.factorial := by rw [← h1]
      _ = (n.factorial * (n - 1).factorial) * (n.factorial * n) := by ring
  have hpos_k : 0 < n.factorial * (n - 1).factorial :=
    Nat.mul_pos (Nat.factorial_pos n) (Nat.factorial_pos (n - 1))
  have habs : (delta n).natAbs = (n.factorial * (n - 1).factorial) * (reducedDelta n).natAbs := by
    rw [hnorm, Int.natAbs_mul, Int.natAbs_natCast]
  have hcn : cVal n = (n.factorial * n) / Nat.gcd (reducedDelta n).natAbs (n.factorial * n) := by
    unfold cVal
    rw [habs, hfact_eq, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hpos_k]
  refine ⟨hcn, ?_⟩
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  have hM_pos : 0 < n.factorial * n := Nat.mul_pos (Nat.factorial_pos n) hn
  have hg_dvd : Nat.gcd (reducedDelta n).natAbs (n.factorial * n) ∣ n.factorial * n :=
    Nat.gcd_dvd_right _ _
  have hval_M : padicValNat q (n.factorial * n) = padicValNat q n.factorial + padicValNat q n :=
    padicValNat.mul (Nat.factorial_ne_zero n) (ne_of_gt hn)
  have hcn_pos : 0 < cVal n := by
    rw [hcn]
    exact Nat.div_pos (Nat.le_of_dvd hM_pos hg_dvd)
      (Nat.pos_of_dvd_of_pos hg_dvd hM_pos)
  have hmul : cVal n * Nat.gcd (reducedDelta n).natAbs (n.factorial * n) = n.factorial * n := by
    rw [hcn, Nat.div_mul_cancel hg_dvd]
  have hval_mul : padicValNat q (cVal n) +
      padicValNat q (Nat.gcd (reducedDelta n).natAbs (n.factorial * n)) =
      padicValNat q n.factorial + padicValNat q n := by
    rw [← hval_M, ← padicValNat.mul (ne_of_gt hcn_pos)
      (ne_of_gt (Nat.pos_of_dvd_of_pos hg_dvd hM_pos)), hmul]
  have hnot_dvd_iff : ¬ (q ∣ cVal n) ↔ padicValNat q (cVal n) = 0 := by
    constructor
    · intro hnd
      exact padicValNat.eq_zero_of_not_dvd hnd
    · intro hz hd
      have h1 : 1 ≤ padicValNat q (cVal n) :=
        one_le_padicValNat_of_dvd (ne_of_gt hcn_pos) hd
      omega
  rw [hnot_dvd_iff]
  have hM_dvd_iff : (naturalModulus q n : ℤ) ∣ reducedDelta n ↔
      q ^ (padicValNat q n.factorial + padicValNat q n) ∣ (reducedDelta n).natAbs := by
    unfold naturalModulus
    exact Int.natCast_dvd
  rw [hM_dvd_iff]
  have hpow_dvd_M : q ^ (padicValNat q n.factorial + padicValNat q n) ∣ n.factorial * n := by
    rw [← hval_M]
    exact pow_padicValNat_dvd
  constructor
  · intro hz
    have hv_gcd : padicValNat q (Nat.gcd (reducedDelta n).natAbs (n.factorial * n)) =
        padicValNat q n.factorial + padicValNat q n := by omega
    calc q ^ (padicValNat q n.factorial + padicValNat q n)
        = q ^ padicValNat q (Nat.gcd (reducedDelta n).natAbs (n.factorial * n)) := by rw [hv_gcd]
      _ ∣ Nat.gcd (reducedDelta n).natAbs (n.factorial * n) := pow_padicValNat_dvd
      _ ∣ (reducedDelta n).natAbs := Nat.gcd_dvd_left _ _
  · intro hd
    have hd_gcd : q ^ (padicValNat q n.factorial + padicValNat q n) ∣
        Nat.gcd (reducedDelta n).natAbs (n.factorial * n) :=
      Nat.dvd_gcd hd hpow_dvd_M
    have hge : padicValNat q n.factorial + padicValNat q n ≤
        padicValNat q (Nat.gcd (reducedDelta n).natAbs (n.factorial * n)) := by
      exact (padicValNat_dvd_iff_le
        (ne_of_gt (Nat.pos_of_dvd_of_pos hg_dvd hM_pos))).mp hd_gcd
    omega

end AlonTarsi.Proofs

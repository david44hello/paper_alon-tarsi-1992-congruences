module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Proofs.TwoQRankOne
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Section 6 (Lemmas 6.10–6.11, Proposition 6.12, Theorem 6.1): Layers, Traces, and Evaluation

This file proves:
- **Lemma 6.10** (`lem_6_10_layers`): centering mixed `P`-orbits for `ℓ_B` and `ℓ_C`;
- **Lemma 6.11** (`lem_6_11_traces`): circulant-minor formula for `Z_Y(I, J)`, trace formulas
  for `Ω(O)` and `Ω(O^c)`, transpose/symmetry of `A_X, B_X, E, F, U`, and
  `∑_O Ω(O^c) = tr((E F)^2)`, `N_{C,m} = tr((U S)^4)`;
- **Proposition 6.12** (`prop_6_12_zeval`): explicit lower-unitriangular binomial change of
  basis over `ZMod q`, Cauchy–Binet, Jacobi's complementary-minor identity over
  `FractionRing (MvPolynomial (ZMod q) (ZMod q))`, nilpotence restriction, and
  `N_{B,m} ≡ N_{C,m} ≡ 1 / m^2 (mod q)`;
- **Theorem 6.1** (`thm_6_1_twoq`): `q^2 ∣ D_{2q}` for every odd prime `q`, and `q^3 ∣ D_{2q}`
  for every prime `q ≥ 5`.
-/

namespace AlonTarsi.Proofs

open scoped BigOperators Matrix
open AlonTarsi

section Lemma610Layers

/-! ### Lemma 6.10: Centering Mixed `P`-Orbits -/

/-- A fixed layer on a pattern `O` (bijective on rows and columns without `- d`). -/
private structure FixedLayer {q m : ℕ} [NeZero q] (O : Pattern q m) where
  φ : ∀ a b : Fin 2, O.O a b → ZMod q
  L1 : ∀ a : Fin 2, Function.Bijective (fun s : O.O a 0 ⊕ O.O a 1 => Sum.elim (φ a 0) (φ a 1) s)
  L2 : ∀ b : Fin 2, Function.Bijective (fun s : O.O 0 b ⊕ O.O 1 b => Sum.elim (φ 0 b) (φ 1 b) s)

@[ext]
private lemma FixedLayer.ext {q m : ℕ} [NeZero q] {O : Pattern q m} {f₁ f₂ : FixedLayer O}
    (h : f₁.φ = f₂.φ) : f₁ = f₂ := by
  cases f₁; cases f₂; cases h; rfl

private noncomputable instance {q m : ℕ} [NeZero q] (O : Pattern q m) : Fintype (FixedLayer O) := by
  classical
  let e : FixedLayer O ≃
      { φ : ∀ a b : Fin 2, O.O a b → ZMod q //
        (∀ a, Function.Bijective (fun s : O.O a 0 ⊕ O.O a 1 => Sum.elim (φ a 0) (φ a 1) s)) ∧
        (∀ b, Function.Bijective (fun s : O.O 0 b ⊕ O.O 1 b => Sum.elim (φ 0 b) (φ 1 b) s)) } :=
    { toFun := fun f => ⟨f.φ, f.L1, f.L2⟩
      invFun := fun f => ⟨f.1, f.2.1, f.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e.symm

private lemma fin2_eq_one_of_ne_zero {a : Fin 2} (h : a ≠ 0) : a = 1 :=
  Fin.ext (by have := a.isLt; have : a.val ≠ 0 := fun h0 => h (Fin.ext h0); omega)

private lemma pattern_row_bijective_of_inj {q k : ℕ} [NeZero q] (hk : k ≤ q) (O : Pattern q k)
    (a : Fin 2) (f : O.O a 0 ⊕ O.O a 1 → ZMod q) (hinj : Function.Injective f) :
    Function.Bijective f := by
  refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩
  fin_cases a <;>
    simp [Fintype.card_sum, Fintype.card_coe, ZMod.card, O.card_00, O.card_01, O.card_10, O.card_11] <;>
    omega

private lemma pattern_col_bijective_of_inj {q k : ℕ} [NeZero q] (hk : k ≤ q) (O : Pattern q k)
    (b : Fin 2) (f : O.O 0 b ⊕ O.O 1 b → ZMod q) (hinj : Function.Injective f) :
    Function.Bijective f := by
  refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩
  fin_cases b <;>
    simp [Fintype.card_sum, Fintype.card_coe, ZMod.card, O.card_00, O.card_01, O.card_10, O.card_11] <;>
    omega

/-- Number of fixed layers on any pattern `O` of size `m`: `q! * m! * (q - m)!`. -/
private lemma card_fixedLayer {q m : ℕ} [NeZero q] (hm : m ≤ q) (O : Pattern q m) :
    Fintype.card (FixedLayer O) = q.factorial * m.factorial * (q - m).factorial := by
  classical
  let Dom := Σ Y : { Y : Finset (ZMod q) // Y.card = m },
    (O.O 0 0 ≃ Y.1) × (O.O 0 1 ≃ (Y.1ᶜ : Finset (ZMod q))) ×
    (O.O 1 0 ≃ (Y.1ᶜ : Finset (ZMod q))) × (O.O 1 1 ≃ Y.1)
  have hbij : Fintype.card (FixedLayer O) = Fintype.card Dom := by
    symm
    change (Finset.univ : Finset Dom).card = (Finset.univ : Finset (FixedLayer O)).card
    let mkFL (t : Dom) : FixedLayer O :=
      { φ := fun a b d =>
          if ha : a = 0 then
            if hb : b = 0 then (t.2.1 ⟨d.1, by subst ha; subst hb; exact d.2⟩).1
            else (t.2.2.1 ⟨d.1, by have hb1 := fin2_eq_one_of_ne_zero hb; subst ha; subst hb1; exact d.2⟩).1
          else
            if hb : b = 0 then (t.2.2.2.1 ⟨d.1, by have ha1 := fin2_eq_one_of_ne_zero ha; subst ha1; subst hb; exact d.2⟩).1
            else (t.2.2.2.2 ⟨d.1, by
              have ha1 := fin2_eq_one_of_ne_zero ha
              have hb1 := fin2_eq_one_of_ne_zero hb
              subst ha1; subst hb1; exact d.2⟩).1
        L1 := fun a => by
          fin_cases a
          · refine pattern_row_bijective_of_inj hm O 0 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_zero, Fin.isValue, ↓reduceDIte, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.2.1.injective (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.1 d₂).2 (hEq ▸ (t.2.1 d₁).2)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.1 d₁).2 (hEq.symm ▸ (t.2.1 d₂).2)).elim
            · simp only [Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.1.injective (Subtype.ext hEq))
          · refine pattern_row_bijective_of_inj hm O 1 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.2.2.2.1.injective (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.1 d₁).2 (hEq.symm ▸ (t.2.2.2.2 d₂).2)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.1 d₂).2 (hEq ▸ (t.2.2.2.2 d₁).2)).elim
            · simp only [Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.2.2.injective (Subtype.ext hEq))
        L2 := fun b => by
          fin_cases b
          · refine pattern_col_bijective_of_inj hm O 0 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_zero, Fin.isValue, ↓reduceDIte, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.2.1.injective (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.1 d₂).2 (hEq ▸ (t.2.1 d₁).2)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.1 d₁).2 (hEq.symm ▸ (t.2.1 d₂).2)).elim
            · simp only [Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.2.1.injective (Subtype.ext hEq))
          · refine pattern_col_bijective_of_inj hm O 1 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.2.2.1.injective (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.1 d₁).2 (hEq.symm ▸ (t.2.2.2.2 d₂).2)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.1 d₂).2 (hEq ▸ (t.2.2.2.2 d₁).2)).elim
            · simp only [Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.2.2.injective (Subtype.ext hEq)) }
    refine Finset.card_bij (fun t _ => mkFL t) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · rintro ⟨Y₁, e00₁, e01₁, e10₁, e11₁⟩ _ ⟨Y₂, e00₂, e01₂, e10₂, e11₂⟩ _ hEq
      have hY : Y₁ = Y₂ := by
        apply Subtype.ext; ext z; constructor
        · intro hz
          obtain ⟨d, hd⟩ := e00₁.surjective ⟨z, hz⟩
          have h := congrFun (congrFun (congrFun (congrArg FixedLayer.φ hEq) 0) 0) d
          simp only [mkFL, ↓reduceDIte, Subtype.coe_eta] at h
          rw [hd] at h; dsimp only at h; rw [h]; exact (e00₂ d).2
        · intro hz
          obtain ⟨d, hd⟩ := e00₂.surjective ⟨z, hz⟩
          have h := congrFun (congrFun (congrFun (congrArg FixedLayer.φ hEq) 0) 0) d
          simp only [mkFL, ↓reduceDIte, Subtype.coe_eta] at h
          rw [hd] at h; dsimp only at h; rw [← h]; exact (e00₁ d).2
      subst hY
      congr 1
      refine Prod.ext (Equiv.ext fun d => Subtype.ext (by
          simpa [mkFL] using congrFun (congrFun (congrFun (congrArg FixedLayer.φ hEq) 0) 0) d))
        (Prod.ext (Equiv.ext fun d => Subtype.ext (by
          simpa [mkFL] using congrFun (congrFun (congrFun (congrArg FixedLayer.φ hEq) 0) 1) d))
          (Prod.ext (Equiv.ext fun d => Subtype.ext (by
            simpa [mkFL] using congrFun (congrFun (congrFun (congrArg FixedLayer.φ hEq) 1) 0) d))
            (Equiv.ext fun d => Subtype.ext (by
              simpa [mkFL] using congrFun (congrFun (congrFun (congrArg FixedLayer.φ hEq) 1) 1) d))))
    · intro f _
      have hφ_inj : ∀ a b, Function.Injective (f.φ a b) := fun a b x y h => by
        fin_cases b
        · exact Sum.inl.inj ((f.L1 a).1 h)
        · exact Sum.inr.inj ((f.L1 a).1 h)
      let Y : Finset (ZMod q) := Finset.univ.image (f.φ 0 0)
      have hYc : Y.card = m := by
        dsimp [Y]; rw [Finset.card_image_of_injective _ (hφ_inj 0 0), Finset.card_attach, O.card_00]
      have himg01 : Finset.univ.image (f.φ 0 1) = Yᶜ := by
        ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, Y]
        constructor
        · rintro ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inl_ne_inr ((f.L1 0).1 hy)
        · intro hz; rcases (f.L1 0).2 z with ⟨x | x, hx⟩
          · exact (hz ⟨x, hx⟩).elim
          · exact ⟨x, hx⟩
      have himg10 : Finset.univ.image (f.φ 1 0) = Yᶜ := by
        ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, Y]
        constructor
        · rintro ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inl_ne_inr ((f.L2 0).1 hy)
        · intro hz; rcases (f.L2 0).2 z with ⟨x | x, hx⟩
          · exact (hz ⟨x, hx⟩).elim
          · exact ⟨x, hx⟩
      have himg11 : Finset.univ.image (f.φ 1 1) = Y := by
        ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, rfl⟩; by_contra hz
          have hzc : f.φ 1 1 x ∈ Yᶜ := Finset.mem_compl.mpr hz
          rw [← himg10] at hzc; rcases Finset.mem_image.mp hzc with ⟨y, _, hy⟩
          exact Sum.inl_ne_inr ((f.L1 1).1 hy)
        · intro hz; rcases (f.L1 1).2 z with ⟨x | x, hx⟩
          · exfalso; have hzc : z ∈ Yᶜ := by rw [← himg10]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
            exact Finset.mem_compl.mp hzc hz
          · exact ⟨x, hx⟩
      let e00 : O.O 0 0 ≃ Y :=
        Equiv.ofBijective (fun d => ⟨f.φ 0 0 d, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          ⟨fun x y h => hφ_inj 0 0 (congrArg Subtype.val h),
           fun ⟨z, hz⟩ => by rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
      let e01 : O.O 0 1 ≃ (Yᶜ : Finset (ZMod q)) :=
        Equiv.ofBijective (fun d => ⟨f.φ 0 1 d, by rw [← himg01]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          ⟨fun x y h => hφ_inj 0 1 (congrArg Subtype.val h),
           fun ⟨z, hz⟩ => by rw [← himg01] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
      let e10 : O.O 1 0 ≃ (Yᶜ : Finset (ZMod q)) :=
        Equiv.ofBijective (fun d => ⟨f.φ 1 0 d, by rw [← himg10]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          ⟨fun x y h => hφ_inj 1 0 (congrArg Subtype.val h),
           fun ⟨z, hz⟩ => by rw [← himg10] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
      let e11 : O.O 1 1 ≃ Y :=
        Equiv.ofBijective (fun d => ⟨f.φ 1 1 d, by rw [← himg11]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          ⟨fun x y h => hφ_inj 1 1 (congrArg Subtype.val h),
           fun ⟨z, hz⟩ => by rw [← himg11] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
      refine ⟨⟨⟨Y, hYc⟩, e00, e01, e10, e11⟩, Finset.mem_univ _, ?_⟩
      ext a b d
      fin_cases a <;> fin_cases b <;>
        simp only [mkFL, e00, e01, e10, e11, Fin.mk_zero, Fin.mk_one, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] <;>
        rfl
  rw [hbij]
  dsimp only [Dom]
  rw [Fintype.card_sigma]
  have hfib : ∀ Y : { Y : Finset (ZMod q) // Y.card = m },
      Fintype.card ((O.O 0 0 ≃ Y.1) × (O.O 0 1 ≃ (Y.1ᶜ : Finset (ZMod q))) ×
        (O.O 1 0 ≃ (Y.1ᶜ : Finset (ZMod q))) × (O.O 1 1 ≃ Y.1)) =
      m.factorial ^ 2 * (q - m).factorial ^ 2 := by
    intro ⟨Y, hYc⟩
    have h00 : Fintype.card (O.O 0 0 ≃ Y) = m.factorial := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [O.card_00, hYc])),
        Fintype.card_coe, O.card_00]
    have h11 : Fintype.card (O.O 1 1 ≃ Y) = m.factorial := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [O.card_11, hYc])),
        Fintype.card_coe, O.card_11]
    have h01 : Fintype.card (O.O 0 1 ≃ (Yᶜ : Finset (ZMod q))) = (q - m).factorial := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [O.card_01, Finset.card_compl, ZMod.card, hYc])),
        Fintype.card_coe, O.card_01]
    have h10 : Fintype.card (O.O 1 0 ≃ (Yᶜ : Finset (ZMod q))) = (q - m).factorial := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp [O.card_10, Finset.card_compl, ZMod.card, hYc])),
        Fintype.card_coe, O.card_10]
    simp only [Fintype.card_prod, h00, h01, h10, h11]; ring
  simp_rw [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hsub : Fintype.card { Y : Finset (ZMod q) // Y.card = m } = q.choose m := by
    rw [Fintype.card_subtype]
    have hpow : Finset.univ.filter (fun Y : Finset (ZMod q) => Y.card = m) =
        Finset.powersetCard m (Finset.univ : Finset (ZMod q)) := by
      ext Y; simp [Finset.mem_powersetCard]
    rw [hpow, Finset.card_powersetCard, Finset.card_univ, ZMod.card]
  rw [hsub]
  have hch := Nat.choose_mul_factorial_mul_factorial hm
  calc q.choose m * (m.factorial ^ 2 * (q - m).factorial ^ 2)
      = (q.choose m * m.factorial * (q - m).factorial) * m.factorial * (q - m).factorial := by ring
    _ = q.factorial * m.factorial * (q - m).factorial := by rw [hch]

/-- Every moving layer on a pattern `E` (for odd `q`) forces `∑_{a,b} ∑_{d ∈ E_{ab}} d = 0`. -/
private lemma layer_pattern_sum_zero {q k : ℕ} [NeZero q] (hodd : Odd q)
    (E : Pattern q k) (h : Layer E) :
    (∑ a : Fin 2, ∑ b : Fin 2, ∑ d ∈ E.O a b, d) = 0 := by
  have hL1_sum : ∀ a : Fin 2,
      (∑ d : E.O a 0, h.h a 0 d) + (∑ d : E.O a 1, h.h a 1 d) = 0 := fun a => by
    have := Equiv.sum_comp (Equiv.ofBijective _ (h.L1 a)) (fun x : ZMod q => x)
    rw [Fintype.sum_sum_type, sum_univ_zmod_odd hodd] at this
    exact this
  have hL2_sum : ∀ b : Fin 2,
      (∑ d : E.O 0 b, (h.h 0 b d - d.1)) + (∑ d : E.O 1 b, (h.h 1 b d - d.1)) = 0 := fun b => by
    have := Equiv.sum_comp (Equiv.ofBijective _ (h.L2 b)) (fun x : ZMod q => x)
    rw [Fintype.sum_sum_type, sum_univ_zmod_odd hodd] at this
    exact this
  have htot1 : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d : E.O a b, h.h a b d) = 0 := by
    simp_rw [Fin.sum_univ_two, hL1_sum]; ring
  have htot2 : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d : E.O a b, (h.h a b d - d.1)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [Fin.sum_univ_two, hL2_sum]; ring
  have hdiff : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d : E.O a b, h.h a b d) -
      (∑ a : Fin 2, ∑ b : Fin 2, ∑ d : E.O a b, (h.h a b d - d.1)) =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ d ∈ E.O a b, d := by
    simp_rw [← Finset.sum_sub_distrib, sub_sub_cancel]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact Finset.sum_coe_sort (E.O a b) (fun d => d)
  rw [← hdiff, htot1, htot2, sub_self]

/-- On a centered pattern `E` (odd `q`), a layer `h` is centered iff its `(0, 0)` phase sum is `0`. -/
private lemma layer_isCentered_iff_00 {q k : ℕ} [NeZero q] (hodd : Odd q)
    (E : Pattern q k) (hE : E.IsCentered) (h : Layer E) :
    h.IsCentered ↔ (∑ d : E.O 0 0, h.h 0 0 d) = 0 := by
  constructor
  · intro hc; exact hc 0 0
  · intro h00
    have hL1 : ∀ a : Fin 2,
        (∑ d : E.O a 0, h.h a 0 d) + (∑ d : E.O a 1, h.h a 1 d) = 0 := fun a => by
      have := Equiv.sum_comp (Equiv.ofBijective _ (h.L1 a)) (fun x : ZMod q => x)
      rw [Fintype.sum_sum_type, sum_univ_zmod_odd hodd] at this
      exact this
    have hL2 : ∀ b : Fin 2,
        (∑ d : E.O 0 b, h.h 0 b d) + (∑ d : E.O 1 b, h.h 1 b d) = 0 := fun b => by
      have h1 : (∑ d : E.O 0 b, (h.h 0 b d - d.1)) + (∑ d : E.O 1 b, (h.h 1 b d - d.1)) = 0 := by
        have := Equiv.sum_comp (Equiv.ofBijective _ (h.L2 b)) (fun x : ZMod q => x)
        rw [Fintype.sum_sum_type, sum_univ_zmod_odd hodd] at this
        exact this
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_coe_sort (E.O 0 b) (fun d => d),
        Finset.sum_coe_sort (E.O 1 b) (fun d => d), hE 0 b, hE 1 b, sub_zero, sub_zero] at h1
      exact h1
    intro a b
    have h01 : (∑ d : E.O 0 1, h.h 0 1 d) = 0 := by linear_combination hL1 0 - h00
    have h10 : (∑ d : E.O 1 0, h.h 1 0 d) = 0 := by linear_combination hL2 0 - h00
    have h11 : (∑ d : E.O 1 1, h.h 1 1 d) = 0 := by linear_combination hL1 1 - h10
    fin_cases a <;> fin_cases b
    · exact h00
    · exact h01
    · exact h10
    · exact h11

private def buildSquareC_aux {q m : ℕ} [NeZero q] (hm : m ≤ q)
    (O : Pattern q m) (h0 : Layer O) (h1 : Layer (O.compl hm))
    (a b : Fin 2) (x y : ZMod q) : Fin (2 * q) :=
  if hd : y - x ∈ O.O a b then
    blockEquiv q (0, x + h0.h a b ⟨y - x, hd⟩)
  else
    blockEquiv q (1, x + h1.h a b ⟨y - x, Finset.mem_compl.mpr hd⟩)

/-- For `L ∈ StratumFix q (ellC q) m`, build a square from `(O, h0, h1)`. -/
private def buildSquareC {q m : ℕ} [NeZero q] (hm : m ≤ q)
    (O : Pattern q m) (h0 : Layer O) (h1 : Layer (O.compl hm)) : LatinSquare (2 * q) where
  entry r col :=
    buildSquareC_aux hm O h0 h1
      ((blockEquiv q).symm r).1 ((blockEquiv q).symm col).1
      ((blockEquiv q).symm r).2 ((blockEquiv q).symm col).2
  row_bijective r := by
    rw [← Finite.injective_iff_bijective]
    intro c₁ c₂ hEq
    obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective c₁
    obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective c₂
    simp only [Equiv.symm_apply_apply] at hEq
    dsimp only [buildSquareC_aux] at hEq
    split_ifs at hEq with hd₁ hd₂ hd₂
    · have hv : h0.h a b₁ ⟨y₁ - x, hd₁⟩ = h0.h a b₂ ⟨y₂ - x, hd₂⟩ := by
        have := congrArg Prod.snd ((blockEquiv q).injective hEq); linear_combination this
      fin_cases b₁ <;> fin_cases b₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((h0.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
      · exact absurd ((h0.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((h0.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((h0.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) Fin.zero_ne_one
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) one_ne_zero
    · have hv : h1.h a b₁ ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩ =
          h1.h a b₂ ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩ := by
        have := congrArg Prod.snd ((blockEquiv q).injective hEq); linear_combination this
      fin_cases b₁ <;> fin_cases b₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((h1.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
      · exact absurd ((h1.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((h1.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((h1.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
  col_bijective col := by
    rw [← Finite.injective_iff_bijective]
    intro r₁ r₂ hEq
    obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
    obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
    simp only [Equiv.symm_apply_apply] at hEq
    dsimp only [buildSquareC_aux] at hEq
    split_ifs at hEq with hd₁ hd₂ hd₂
    · have hv : h0.h a₁ b ⟨y - x₁, hd₁⟩ - (y - x₁) = h0.h a₂ b ⟨y - x₂, hd₂⟩ - (y - x₂) := by
        have := congrArg Prod.snd ((blockEquiv q).injective hEq); linear_combination this
      fin_cases a₁ <;> fin_cases a₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((h0.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))
      · exact absurd ((h0.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((h0.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((h0.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) Fin.zero_ne_one
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) one_ne_zero
    · have hv : h1.h a₁ b ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩ - (y - x₁) =
          h1.h a₂ b ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩ - (y - x₂) := by
        have := congrArg Prod.snd ((blockEquiv q).injective hEq); linear_combination this
      fin_cases a₁ <;> fin_cases a₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((h1.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))
      · exact absurd ((h1.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((h1.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((h1.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))

private lemma buildSquareC_entry {q m : ℕ} [NeZero q] (hm : m ≤ q)
    (O : Pattern q m) (h0 : Layer O) (h1 : Layer (O.compl hm))
    (a b : Fin 2) (x y : ZMod q) :
    (buildSquareC hm O h0 h1).entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
      if hd : y - x ∈ O.O a b then blockEquiv q (0, x + h0.h a b ⟨y - x, hd⟩)
      else blockEquiv q (1, x + h1.h a b ⟨y - x, Finset.mem_compl.mpr hd⟩) := by
  simp only [buildSquareC, Equiv.symm_apply_apply]
  rfl

private def buildSquareB_aux {q m : ℕ} [NeZero q] (hm : m ≤ q)
    (O : Pattern q m) (φ : FixedLayer O) (h1 : Layer (O.compl hm))
    (a b : Fin 2) (x y : ZMod q) : Fin (2 * q) :=
  if hd : y - x ∈ O.O a b then
    blockEquiv q (0, φ.φ a b ⟨y - x, hd⟩)
  else
    blockEquiv q (1, x + h1.h a b ⟨y - x, Finset.mem_compl.mpr hd⟩)

/-- Build a square in `StratumFix q (ellB q) m` from `(O, φ, h1)`. -/
private def buildSquareB {q m : ℕ} [NeZero q] (hm : m ≤ q)
    (O : Pattern q m) (φ : FixedLayer O) (h1 : Layer (O.compl hm)) : LatinSquare (2 * q) where
  entry r col :=
    buildSquareB_aux hm O φ h1
      ((blockEquiv q).symm r).1 ((blockEquiv q).symm col).1
      ((blockEquiv q).symm r).2 ((blockEquiv q).symm col).2
  row_bijective r := by
    rw [← Finite.injective_iff_bijective]
    intro c₁ c₂ hEq
    obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective c₁
    obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective c₂
    simp only [Equiv.symm_apply_apply] at hEq
    dsimp only [buildSquareB_aux] at hEq
    split_ifs at hEq with hd₁ hd₂ hd₂
    · have hv : φ.φ a b₁ ⟨y₁ - x, hd₁⟩ = φ.φ a b₂ ⟨y₂ - x, hd₂⟩ :=
        congrArg Prod.snd ((blockEquiv q).injective hEq)
      fin_cases b₁ <;> fin_cases b₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((φ.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
      · exact absurd ((φ.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((φ.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((φ.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) Fin.zero_ne_one
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) one_ne_zero
    · have hv : h1.h a b₁ ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩ =
          h1.h a b₂ ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩ := by
        have := congrArg Prod.snd ((blockEquiv q).injective hEq); linear_combination this
      fin_cases b₁ <;> fin_cases b₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((h1.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
      · exact absurd ((h1.L1 a).1 (a₁ := Sum.inl ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((h1.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((h1.L1 a).1 (a₁ := Sum.inr ⟨y₁ - x, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y₂ - x, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination congrArg Subtype.val this)
  col_bijective col := by
    rw [← Finite.injective_iff_bijective]
    intro r₁ r₂ hEq
    obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
    obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
    simp only [Equiv.symm_apply_apply] at hEq
    dsimp only [buildSquareB_aux] at hEq
    split_ifs at hEq with hd₁ hd₂ hd₂
    · have hv : φ.φ a₁ b ⟨y - x₁, hd₁⟩ = φ.φ a₂ b ⟨y - x₂, hd₂⟩ :=
        congrArg Prod.snd ((blockEquiv q).injective hEq)
      fin_cases a₁ <;> fin_cases a₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((φ.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))
      · exact absurd ((φ.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((φ.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((φ.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) Fin.zero_ne_one
    · exact absurd (congrArg Prod.fst ((blockEquiv q).injective hEq)) one_ne_zero
    · have hv : h1.h a₁ b ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩ - (y - x₁) =
          h1.h a₂ b ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩ - (y - x₂) := by
        have := congrArg Prod.snd ((blockEquiv q).injective hEq); linear_combination this
      fin_cases a₁ <;> fin_cases a₂ <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue] at hv ⊢
      · have := Sum.inl.inj ((h1.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))
      · exact absurd ((h1.L2 b).1 (a₁ := Sum.inl ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inl_ne_inr
      · exact absurd ((h1.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inl ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv) Sum.inr_ne_inl
      · have := Sum.inr.inj ((h1.L2 b).1 (a₁ := Sum.inr ⟨y - x₁, Finset.mem_compl.mpr hd₁⟩) (a₂ := Sum.inr ⟨y - x₂, Finset.mem_compl.mpr hd₂⟩) hv)
        congr 1; exact Prod.ext rfl (by linear_combination -(congrArg Subtype.val this))

private lemma buildSquareB_entry {q m : ℕ} [NeZero q] (hm : m ≤ q)
    (O : Pattern q m) (φ : FixedLayer O) (h1 : Layer (O.compl hm))
    (a b : Fin 2) (x y : ZMod q) :
    (buildSquareB hm O φ h1).entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
      if hd : y - x ∈ O.O a b then blockEquiv q (0, φ.φ a b ⟨y - x, hd⟩)
      else blockEquiv q (1, x + h1.h a b ⟨y - x, Finset.mem_compl.mpr hd⟩) := by
  simp only [buildSquareB, Equiv.symm_apply_apply]
  rfl

/-- Translate a pattern `O` by `(u, v)`: `O'_{ab} = O_{ab} + (v_b - u_a)`. -/
private def translatePattern {q m : ℕ} [NeZero q] (O : Pattern q m) (u v : Fin 2 → ZMod q) :
    Pattern q m where
  O a b := (O.O a b).image (fun d => d + (v b - u a))
  card_00 := by rw [Finset.card_image_of_injective _ (add_left_injective _), O.card_00]
  card_11 := by rw [Finset.card_image_of_injective _ (add_left_injective _), O.card_11]
  card_01 := by rw [Finset.card_image_of_injective _ (add_left_injective _), O.card_01]
  card_10 := by rw [Finset.card_image_of_injective _ (add_left_injective _), O.card_10]

/-- Action of `g = (u, v, w) ∈ P` on entry `((a, x), (b, x + d))` of a square `L`. -/
private lemma sylowP_act_entry {q : ℕ} [NeZero q] (g : sylowP q) (L : LatinSquare (2 * q))
    (a b : Fin 2) (x d : ZMod q) :
    let u := (sylowToVec g).1
    let v := (sylowToVec g).2.1
    let w := (sylowToVec g).2.2
    (g.1 • L).entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
      blockTransPerm q w (L.entry (blockEquiv q (a, x - u a)) (blockEquiv q (b, x + d - v b))) := by
  change g.1.2.2 (L.entry (g.1.1.symm (blockEquiv q (a, x)))
    (g.1.2.1.symm (blockEquiv q (b, x + d)))) = _
  have hval := sylowToVec_val g
  rw [hval]
  have hinv1 : (blockTransPerm q (sylowToVec g).1).symm (blockEquiv q (a, x)) =
      blockEquiv q (a, x - (sylowToVec g).1 a) := by
    apply (blockTransPerm q (sylowToVec g).1).injective
    rw [Equiv.apply_symm_apply, blockTransPerm_apply]; simp
  have hinv2 : (blockTransPerm q (sylowToVec g).2.1).symm (blockEquiv q (b, x + d)) =
      blockEquiv q (b, x + d - (sylowToVec g).2.1 b) := by
    apply (blockTransPerm q (sylowToVec g).2.1).injective
    rw [Equiv.apply_symm_apply, blockTransPerm_apply]; simp
  rw [hinv1, hinv2]

/-- Powers of `ellC q` in vector coordinates. -/
private lemma sylowToVec_ellC_pow {q : ℕ} [NeZero q] (n : ℕ) :
    sylowToVec (ellC q ^ n) = (fun _ => (n : ZMod q), fun _ => (n : ZMod q), fun _ => (n : ZMod q)) := by
  induction n with
  | zero => simp [sylowToVec_one]; rfl
  | succ n ih =>
    rw [pow_succ, sylowToVec_mul, ih]; dsimp [ellC]; rw [sylowToVec_sylowElem]
    refine Prod.ext (funext fun a => by fin_cases a <;> (change (n : ZMod q) + 1 = _; push_cast; rfl))
      (Prod.ext (funext fun b => by fin_cases b <;> (change (n : ZMod q) + 1 = _; push_cast; rfl))
        (funext fun c => by fin_cases c <;> (change (n : ZMod q) + 1 = _; push_cast; rfl)))

/-- Powers of `ellB q` in vector coordinates. -/
private lemma sylowToVec_ellB_pow {q : ℕ} [NeZero q] (n : ℕ) :
    sylowToVec (ellB q ^ n) =
      (fun _ => (n : ZMod q), fun _ => (n : ZMod q), fun c => if c = 0 then 0 else (n : ZMod q)) := by
  induction n with
  | zero => simp [sylowToVec_one]; rfl
  | succ n ih =>
    rw [pow_succ, sylowToVec_mul, ih]; dsimp [ellB]; rw [sylowToVec_sylowElem]
    refine Prod.ext (funext fun a => by fin_cases a <;> (change (n : ZMod q) + 1 = _; push_cast; rfl))
      (Prod.ext (funext fun b => by fin_cases b <;> (change (n : ZMod q) + 1 = _; push_cast; rfl))
        (funext fun c => by
          fin_cases c
          · simp
          · change (n : ZMod q) + 1 = ((n + 1 : ℕ) : ZMod q); push_cast; rfl))

/-- `P` preserves `StratumFix q ℓ m` for `ℓ ∈ {ellB q, ellC q}`. -/
private lemma sylowP_preserves_stratumFix {q m : ℕ} [NeZero q]
    (ℓ : sylowP q) (hℓ : ℓ ∈ ({ellB q, ellC q} : Finset (sylowP q)))
    (g : sylowP q) (L : StratumFix q ℓ m) :
    g.1 • L.1 ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) ∧
    stratumOf q (g.1 • L.1) = m := by
  classical
  refine ⟨?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    change h.1 • (g.1 • L.1) = g.1 • L.1
    have hcomm : h.1 * g.1 = g.1 * h.1 :=
      congrArg Subtype.val ((isElemAbelian_sylowP_subgroup q ⊤).1 h trivial g trivial)
    rw [← mul_smul, hcomm, mul_smul, L.2.1 h.1 ⟨h, hh, rfl⟩]
  · trans stratumOf q L.1
    swap
    · exact L.2.2
    unfold stratumOf
    let u0 := (sylowToVec g).1 0; let v0 := (sylowToVec g).2.1 0
    have hpow_u : ∀ x : ZMod q, (sylowToVec (ℓ ^ x.val)).1 0 = x ∧ (sylowToVec (ℓ ^ x.val)).2.1 0 = x := by
      intro x
      have h1 : (sylowToVec ℓ).1 0 = 1 ∧ (sylowToVec ℓ).2.1 0 = 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
        rcases hℓ with rfl | rfl <;> simp [ellB, ellC, sylowToVec_sylowElem]
      have hpow_n : ∀ n : ℕ, (sylowToVec (ℓ ^ n)).1 0 = (n : ZMod q) ∧
          (sylowToVec (ℓ ^ n)).2.1 0 = (n : ZMod q) := fun n => by
        induction n with
        | zero => simp [sylowToVec_one]
        | succ n ih =>
          rw [pow_succ, sylowToVec_mul]
          exact ⟨by change (sylowToVec (ℓ ^ n)).1 0 + (sylowToVec ℓ).1 0 = _; rw [ih.1, h1.1]; push_cast; rfl,
                 by change (sylowToVec (ℓ ^ n)).2.1 0 + (sylowToVec ℓ).2.1 0 = _; rw [ih.2, h1.2]; push_cast; rfl⟩
      simpa [ZMod.natCast_zmod_val] using hpow_n x.val
    have hmem_iff : ∀ d : ZMod q,
        ((blockEquiv q).symm ((g.1 • L.1).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)))).1 = 0 ↔
        ((blockEquiv q).symm (L.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d + (u0 - v0))))).1 = 0 := by
      intro d
      have ha := sylowP_act_entry g L.1 0 0 0 d
      simp only [zero_add, zero_sub] at ha
      rw [ha]
      have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q (sylowToVec g).2.2 k)).1 =
          ((blockEquiv q).symm k).1 := fun k => by
        obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
        rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [hbt]
      have hpow : ℓ ^ u0.val ∈ Subgroup.zpowers ℓ := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      have hfix := (sylow_fix_entry_iff (ℓ ^ u0.val) L.1).mp
        (L.2.1 (ℓ ^ u0.val).1 ⟨ℓ ^ u0.val, hpow, rfl⟩) 0 0 (-u0) (d - v0)
      rw [(hpow_u u0).1, (hpow_u u0).2, neg_add_cancel] at hfix
      have h1 := congrArg (fun k => ((blockEquiv q).symm k).1) hfix
      simp only [Equiv.symm_apply_apply] at h1
      have hadd : d - v0 + u0 = d + (u0 - v0) := by ring
      rw [hadd] at h1; rw [h1]
    refine Finset.card_bij (fun d _ => d + (u0 - v0)) ?_ ?_ ?_
    · intro d hd; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem_iff d).mp (Finset.mem_filter.mp hd).2⟩
    · intro d₁ _ d₂ _ h; linear_combination h
    · intro d hd
      exact ⟨d - (u0 - v0), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hmem_iff _).mpr (by convert (Finset.mem_filter.mp hd).2 using 2; ring)⟩, by ring⟩

/-- Unique centering parameters `(u₁, v₀, v₁)` for any pattern `O` with `∑_{ab} s(O_{ab}) = 0`. -/
private lemma existsUnique_center_pattern {q m : ℕ} [NeZero q] (hq : q.Prime)
    (hm0 : 0 < m) (hmq : m < q) (O : Pattern q m)
    (hsum0 : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d ∈ O.O a b, d) = 0) :
    ∃! p : ZMod q × ZMod q × ZMod q,
      (translatePattern O (fun a => if a = 0 then 0 else p.1)
        (fun b => if b = 0 then p.2.1 else p.2.2)).IsCentered := by
  have : Fact q.Prime := ⟨hq⟩
  have hm : m ≤ q := le_of_lt hmq
  have hm_ne : (m : ZMod q) ≠ 0 := fun h0 =>
    absurd (Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff m q).mp h0)) (not_le_of_gt hmq)
  have hqm_ne : ((q - m : ℕ) : ZMod q) ≠ 0 := by
    have hpos : 0 < q - m := by omega
    have hlt : q - m < q := by omega
    intro h0
    exact absurd (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff (q - m) q).mp h0)) (not_le_of_gt hlt)
  have hqm_cast : ((q - m : ℕ) : ZMod q) = -(m : ZMod q) := by
    rw [Nat.cast_sub hm, ZMod.natCast_self, zero_sub]
  let s : Fin 2 → Fin 2 → ZMod q := fun a b => ∑ d ∈ O.O a b, d
  let o00 := s 0 0 * (m : ZMod q)⁻¹
  let o01 := s 0 1 * ((q - m : ℕ) : ZMod q)⁻¹
  let o10 := s 1 0 * ((q - m : ℕ) : ZMod q)⁻¹
  let o11 := s 1 1 * (m : ZMod q)⁻¹
  have hmean_sum : o00 - o01 - o10 + o11 = 0 := by
    have htot : s 0 0 + s 0 1 + s 1 0 + s 1 1 = 0 := by
      simpa [Fin.sum_univ_two, s, add_assoc] using hsum0
    have hs00 : s 0 0 = (m : ZMod q) * o00 := by
      dsimp [o00]; rw [mul_comm, mul_assoc, inv_mul_cancel₀ hm_ne, mul_one]
    have hs11 : s 1 1 = (m : ZMod q) * o11 := by
      dsimp [o11]; rw [mul_comm, mul_assoc, inv_mul_cancel₀ hm_ne, mul_one]
    have hs01 : s 0 1 = -(m : ZMod q) * o01 := by
      dsimp [o01]; rw [← hqm_cast, mul_comm, mul_assoc, inv_mul_cancel₀ hqm_ne, mul_one]
    have hs10 : s 1 0 = -(m : ZMod q) * o10 := by
      dsimp [o10]; rw [← hqm_cast, mul_comm, mul_assoc, inv_mul_cancel₀ hqm_ne, mul_one]
    rw [hs00, hs01, hs10, hs11] at htot
    have hfac : (m : ZMod q) * (o00 - o01 - o10 + o11) = 0 := by linear_combination htot
    exact (mul_eq_zero.mp hfac).resolve_left hm_ne
  have htr_sum : ∀ (u v : Fin 2 → ZMod q) (a b : Fin 2),
      (∑ d ∈ (translatePattern O u v).O a b, d) =
        s a b + ((O.O a b).card : ZMod q) * (v b - u a) := by
    intro u v a b
    dsimp [translatePattern, s]
    rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h), Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul]
  refine ⟨(o10 - o00, -o00, -o01), ?_, ?_⟩
  · intro a b
    rw [htr_sum]
    fin_cases a <;> fin_cases b <;> simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue]
    · rw [O.card_00]; dsimp [o00]; simp only [↓reduceIte, sub_zero]
      rw [mul_neg, mul_comm (m : ZMod q), mul_assoc, inv_mul_cancel₀ hm_ne, mul_one, add_neg_cancel]
    · rw [O.card_01]; dsimp [o01]; simp only [one_ne_zero, ↓reduceIte, sub_zero]
      rw [mul_neg, mul_comm ((q - m : ℕ) : ZMod q), mul_assoc, inv_mul_cancel₀ hqm_ne, mul_one,
        add_neg_cancel]
    · rw [O.card_10]; simp only [one_ne_zero, ↓reduceIte]
      have hdiff : -o00 - (o10 - o00) = -o10 := by ring
      rw [hdiff]; dsimp [o10]
      rw [mul_neg, mul_comm ((q - m : ℕ) : ZMod q), mul_assoc, inv_mul_cancel₀ hqm_ne, mul_one,
        add_neg_cancel]
    · rw [O.card_11]; simp only [one_ne_zero, ↓reduceIte]
      have hdiff : -o01 - (o10 - o00) = -o11 := by linear_combination hmean_sum
      rw [hdiff]; dsimp [o11]
      rw [mul_neg, mul_comm (m : ZMod q), mul_assoc, inv_mul_cancel₀ hm_ne, mul_one, add_neg_cancel]
  · rintro ⟨u₁, v₀, v₁⟩ hc
    have h00 := hc 0 0; have h01 := hc 0 1; have h10 := hc 1 0
    rw [htr_sum, O.card_00] at h00
    rw [htr_sum, O.card_01] at h01
    rw [htr_sum, O.card_10] at h10
    simp only [Fin.isValue, ↓reduceIte, sub_zero, one_ne_zero] at h00 h01 h10
    have hv₀ : v₀ = -o00 := by
      dsimp [o00]
      have : (m : ZMod q) * v₀ = -s 0 0 := by linear_combination h00
      calc v₀ = (m : ZMod q)⁻¹ * ((m : ZMod q) * v₀) := by rw [← mul_assoc, inv_mul_cancel₀ hm_ne, one_mul]
        _ = (m : ZMod q)⁻¹ * (-s 0 0) := by rw [this]
        _ = -(s 0 0 * (m : ZMod q)⁻¹) := by ring
    have hv₁ : v₁ = -o01 := by
      dsimp [o01]
      have : ((q - m : ℕ) : ZMod q) * v₁ = -s 0 1 := by linear_combination h01
      calc v₁ = ((q - m : ℕ) : ZMod q)⁻¹ * (((q - m : ℕ) : ZMod q) * v₁) := by
            rw [← mul_assoc, inv_mul_cancel₀ hqm_ne, one_mul]
        _ = ((q - m : ℕ) : ZMod q)⁻¹ * (-s 0 1) := by rw [this]
        _ = -(s 0 1 * ((q - m : ℕ) : ZMod q)⁻¹) := by ring
    have hu₁ : u₁ = o10 - o00 := by
      dsimp [o10]
      have : ((q - m : ℕ) : ZMod q) * (v₀ - u₁) = -s 1 0 := by linear_combination h10
      have hdiff : v₀ - u₁ = -o10 := by
        calc v₀ - u₁ = ((q - m : ℕ) : ZMod q)⁻¹ * (((q - m : ℕ) : ZMod q) * (v₀ - u₁)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hqm_ne, one_mul]
          _ = ((q - m : ℕ) : ZMod q)⁻¹ * (-s 1 0) := by rw [this]
          _ = -(s 1 0 * ((q - m : ℕ) : ZMod q)⁻¹) := by ring
      rw [hv₀] at hdiff; linear_combination -hdiff
    exact Prod.ext hu₁ (Prod.ext hv₀ hv₁)

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

/-- Helper: extract a moving `Layer P` from a Latin square `L` whose entries on `P` all lie in
symbol block `c` and shift diagonally by `+ x`. -/
private noncomputable def extractMovingLayer {q k : ℕ} [NeZero q] (hk : k ≤ q)
    (L : LatinSquare (2 * q)) (P : Pattern q k) (c : Fin 2)
    (hblk : ∀ a b d, d ∈ P.O a b →
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = c)
    (hsh : ∀ a b x d, d ∈ P.O a b →
      L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
        blockEquiv q (c, ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 + x)) :
    Layer P :=
  { h := fun a b d => ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d.1)))).2
    L1 := fun a => pattern_row_bijective_of_inj hk P a _ (by
      rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
      · dsimp only [Sum.elim_inl] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 0 d₁ hd₁).trans (hblk a 0 d₂ hd₂).symm) hEq)
        exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 hL))))
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 0 d₁ hd₁).trans (hblk a 1 d₂ hd₂).symm) hEq)
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.row_bijective _).1 hL))) Fin.zero_ne_one
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 1 d₁ hd₁).trans (hblk a 0 d₂ hd₂).symm) hEq)
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.row_bijective _).1 hL))) one_ne_zero
      · dsimp only [Sum.elim_inr] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 1 d₁ hd₁).trans (hblk a 1 d₂ hd₂).symm) hEq)
        exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 hL)))))
    L2 := fun b => pattern_col_bijective_of_inj hk P b _ (by
      rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
      · dsimp only [Sum.elim_inl] at hEq
        have s1 := hsh 0 b (-d₁) d₁ hd₁; have s2 := hsh 0 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl (by simpa [sub_eq_add_neg] using hEq)
        exact congrArg Sum.inl (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 hL)))))
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have s1 := hsh 0 b (-d₁) d₁ hd₁; have s2 := hsh 1 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl (by simpa [sub_eq_add_neg] using hEq)
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.col_bijective _).1 hL))) Fin.zero_ne_one
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have s1 := hsh 1 b (-d₁) d₁ hd₁; have s2 := hsh 0 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl (by simpa [sub_eq_add_neg] using hEq)
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.col_bijective _).1 hL))) one_ne_zero
      · dsimp only [Sum.elim_inr] at hEq
        have s1 := hsh 1 b (-d₁) d₁ hd₁; have s2 := hsh 1 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl (by simpa [sub_eq_add_neg] using hEq)
        exact congrArg Sum.inr (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 hL)))))) }

/-- Helper: extract a fixed layer `FixedLayer P` from a Latin square `L` whose entries on `P`
all lie in symbol block `0` and are invariant along diagonals. -/
private noncomputable def extractFixedLayer {q k : ℕ} [NeZero q] (hk : k ≤ q)
    (L : LatinSquare (2 * q)) (P : Pattern q k)
    (hblk : ∀ a b d, d ∈ P.O a b →
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 0)
    (hsh : ∀ a b x d, d ∈ P.O a b →
      L.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
        blockEquiv q (0, ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2)) :
    FixedLayer P :=
  { φ := fun a b d => ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d.1)))).2
    L1 := fun a => pattern_row_bijective_of_inj hk P a _ (by
      rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
      · dsimp only [Sum.elim_inl] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 0 d₁ hd₁).trans (hblk a 0 d₂ hd₂).symm) hEq)
        exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 hL))))
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 0 d₁ hd₁).trans (hblk a 1 d₂ hd₂).symm) hEq)
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.row_bijective _).1 hL))) Fin.zero_ne_one
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 1 d₁ hd₁).trans (hblk a 0 d₂ hd₂).symm) hEq)
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.row_bijective _).1 hL))) one_ne_zero
      · dsimp only [Sum.elim_inr] at hEq
        have hL := (blockEquiv q).symm.injective (Prod.ext ((hblk a 1 d₁ hd₁).trans (hblk a 1 d₂ hd₂).symm) hEq)
        exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 hL)))))
    L2 := fun b => pattern_col_bijective_of_inj hk P b _ (by
      rintro (⟨d₁, hd₁⟩ | ⟨d₁, hd₁⟩) (⟨d₂, hd₂⟩ | ⟨d₂, hd₂⟩) hEq
      · dsimp only [Sum.elim_inl] at hEq
        have s1 := hsh 0 b (-d₁) d₁ hd₁; have s2 := hsh 0 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl hEq
        exact congrArg Sum.inl (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 hL)))))
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have s1 := hsh 0 b (-d₁) d₁ hd₁; have s2 := hsh 1 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl hEq
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.col_bijective _).1 hL))) Fin.zero_ne_one
      · dsimp only [Sum.elim_inl, Sum.elim_inr] at hEq
        have s1 := hsh 1 b (-d₁) d₁ hd₁; have s2 := hsh 0 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl hEq
        exact absurd (congrArg Prod.fst ((blockEquiv q).injective ((L.col_bijective _).1 hL))) one_ne_zero
      · dsimp only [Sum.elim_inr] at hEq
        have s1 := hsh 1 b (-d₁) d₁ hd₁; have s2 := hsh 1 b (-d₂) d₂ hd₂; simp only [neg_add_cancel] at s1 s2
        have hL : L.entry (blockEquiv q (1, -d₁)) (blockEquiv q (b, 0)) =
            L.entry (blockEquiv q (1, -d₂)) (blockEquiv q (b, 0)) := by
          rw [s1, s2]; congr 1; exact Prod.ext rfl hEq
        exact congrArg Sum.inr (Subtype.ext (neg_injective (congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 hL)))))) }

/-- Part 2 of Lemma 6.10: `N_{C,m} = ∑_O Ω(O) Ω(O^c)`. -/
private lemma lem_6_10_partC (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    mixedOrbitCountC q m =
      ∑ O ∈ centeredPatterns q m, OmegaSum O * OmegaSum (O.compl (le_of_lt hmq)) := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    have hq_odd : Odd q := hq.odd_of_ne_two hodd
    have hm : m ≤ q := le_of_lt hmq
    have hm_ne : (m : ZMod q) ≠ 0 := fun h0 =>
      absurd (Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff m q).mp h0)) (not_le_of_gt hmq)
    have hqm_ne : ((q - m : ℕ) : ZMod q) ≠ 0 := by
      have hpos : 0 < q - m := by omega
      have hlt : q - m < q := by omega
      intro h0
      exact absurd (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff (q - m) q).mp h0)) (not_le_of_gt hlt)
    have h67 := lem_6_7_factor q hq hodd
    unfold mixedOrbitCountC mixedOrbitCount
    set R : Setoid (StratumFix q (ellC q) m) :=
      { r := fun L₁ L₂ => ∃ g : sylowP q, g.1 • L₁.1 = L₂.1
        iseqv :=
          ⟨fun L => ⟨1, one_smul _ _⟩,
           fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg]; simp⟩,
           fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ => ⟨g₂ * g₁, by rw [← h₂, ← h₁]; exact mul_smul _ _ _⟩⟩ }
    -- Define the finset of centered triples `(O, h0, h1)`
    let CentC := Σ O : { O : Pattern q m // O.IsCentered },
      { h0 : Layer O.1 // h0.IsCentered } × { h1 : Layer (O.1.compl hm) // h1.IsCentered }
    have hsum_cent :
        (∑ t : CentC, (layerSign t.2.1.1 : ℤ) * (layerSign t.2.2.1 : ℤ)) =
        ∑ O ∈ centeredPatterns q m, OmegaSum O * OmegaSum (O.compl hm) := by
      dsimp only [CentC]
      rw [Fintype.sum_sigma]
      have hinner : ∀ O : { O : Pattern q m // O.IsCentered },
          (∑ p : { h0 : Layer O.1 // h0.IsCentered } × { h1 : Layer (O.1.compl hm) // h1.IsCentered },
            (layerSign p.1.1 : ℤ) * (layerSign p.2.1 : ℤ)) =
          OmegaSum O.1 * OmegaSum (O.1.compl hm) := by
        intro O
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
        unfold OmegaSum
        have hsub_sum : ∀ {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (f : α → ℤ),
            (∑ x : { a : α // P a }, f x.1) = ∑ a ∈ Finset.univ.filter P, f a := by
          intro α _ P _ f
          refine Finset.sum_bij (fun x _ => x.1)
            (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun a ha => ⟨⟨a, (Finset.mem_filter.mp ha).2⟩, Finset.mem_univ _, rfl⟩)
            (fun _ _ => rfl)
        rw [hsub_sum (fun L : Layer O.1 => L.IsCentered) (fun L => (layerSign L : ℤ)),
            hsub_sum (fun L : Layer (O.1.compl hm) => L.IsCentered) (fun L => (layerSign L : ℤ))]
      simp_rw [hinner]
      unfold centeredPatterns
      refine Finset.sum_bij (fun O _ => O.1)
        (fun O _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.2⟩)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun O hO => ⟨⟨O, (Finset.mem_filter.mp hO).2⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    rw [← hsum_cent]
    -- Map each `t : CentC` to its `P`-orbit in `Quotient R` and prove it is a BIJECTION preserving sign!
    have hmkC_mem : ∀ t : CentC,
        buildSquareC hm t.1.1 t.2.1.1 t.2.2.1 ∈
          fixSet ((Subgroup.zpowers (ellC q)).map (sylowP q).subtype) ∧
        stratumOf q (buildSquareC hm t.1.1 t.2.1.1 t.2.2.1) = m := by
      intro ⟨⟨O, _⟩, ⟨h0, _⟩, ⟨h1, _⟩⟩
      refine ⟨?_, ?_⟩
      · rintro _ ⟨g, hg, rfl⟩
        change g.1 • buildSquareC hm O h0 h1 = buildSquareC hm O h0 h1
        rw [sylow_fix_entry_iff]
        rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
        have hk : ∃ n : ℕ, ellC q ^ k = ellC q ^ n := by
          have hord : ellC q ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 (ellC q) trivial
          refine ⟨(k % (q : ℤ)).toNat, ?_⟩
          have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
          have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
          conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
          rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
        rcases hk with ⟨n, hn⟩; rw [hn, sylowToVec_ellC_pow]
        intro a b x y
        rw [buildSquareC_entry, buildSquareC_entry]
        have hsub : y + (n : ZMod q) - (x + (n : ZMod q)) = y - x := by ring
        rw [hsub]
        split_ifs <;> simp <;> ring
      · unfold stratumOf
        have hfilt : (Finset.univ.filter fun d : ZMod q =>
            ((blockEquiv q).symm ((buildSquareC hm O h0 h1).entry (blockEquiv q (0, 0))
              (blockEquiv q (0, d)))).1 = 0) = O.O 0 0 := by
          ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, buildSquareC_entry,
            Equiv.symm_apply_apply, sub_zero]
          split_ifs with hd <;> simp [hd]
        rw [hfilt, O.card_00]
    have hmkC_sign : ∀ t : CentC,
        (squareSign (buildSquareC hm t.1.1 t.2.1.1 t.2.2.1) : ℤ) =
        (layerSign t.2.1.1 : ℤ) * (layerSign t.2.2.1 : ℤ) := by
      intro t
      have h := h67.2.2 (buildSquareC hm t.1.1 t.2.1.1 t.2.2.1) m hm t.1.1 t.2.1.1 t.2.2.1
        (hmkC_mem t).1 (fun a b x d => ⟨fun hd => by
          rw [buildSquareC_entry]; simp [hd], fun hd => by
          have hnd : d ∉ t.1.1.O a b := Finset.mem_compl.mp hd
          rw [buildSquareC_entry]; simp [hnd]⟩)
      rw [h]; push_cast; rfl
    symm
    refine Finset.sum_bij (fun t _ => Quotient.mk R ⟨buildSquareC hm t.1.1 t.2.1.1 t.2.2.1, hmkC_mem t⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · -- Injective: two centered triples in the same `P`-orbit must be equal!
      intro t₁ _ t₂ _ hEq
      rcases Quotient.exact hEq with ⟨g, hg⟩
      -- Shift `g` by `ℓ_C ^ (-u₀)` so `u 0 = 0`!
      let u0 := (sylowToVec g).1 0
      let g' := g * (ellC q ^ (-u0).val)
      have hg' : g'.1 • buildSquareC hm t₁.1.1 t₁.2.1.1 t₁.2.2.1 =
          buildSquareC hm t₂.1.1 t₂.2.1.1 t₂.2.2.1 := by
        change (g.1 * (ellC q ^ (-u0).val).1) • _ = _
        have hfix : (ellC q ^ (-u0).val).1 • buildSquareC hm t₁.1.1 t₁.2.1.1 t₁.2.2.1 =
            buildSquareC hm t₁.1.1 t₁.2.1.1 t₁.2.2.1 :=
          (hmkC_mem t₁).1 (ellC q ^ (-u0).val).1 ⟨ellC q ^ (-u0).val, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _, rfl⟩
        rw [mul_smul, hfix]
        exact hg
      have hu0 : (sylowToVec g').1 0 = 0 := by
        dsimp [g']; rw [sylowToVec_mul, sylowToVec_ellC_pow, ZMod.natCast_zmod_val]
        change u0 + -u0 = 0; exact add_neg_cancel _
      let u := (sylowToVec g').1; let v := (sylowToVec g').2.1; let w := (sylowToVec g').2.2
      -- Compare patterns: `t₂.1.1 = translatePattern t₁.1.1 u v`
      have hOeq : t₂.1.1 = translatePattern t₁.1.1 u v := by
        ext a b d
        have hent := congrArg (fun M => ((blockEquiv q).symm (M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d)))).1) hg'
        rw [sylowP_act_entry] at hent
        have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q w k)).1 = ((blockEquiv q).symm k).1 := fun k => by
          obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
          rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rw [hbt] at hent
        have h1 : ((blockEquiv q).symm ((buildSquareC hm t₂.1.1 t₂.2.1.1 t₂.2.2.1).entry
            (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d)))).1 = 0 ↔ d ∈ t₂.1.1.O a b := by
          rw [buildSquareC_entry]; simp only [add_sub_cancel_left]; split_ifs with hd <;> simp [hd]
        have h2 : ((blockEquiv q).symm ((buildSquareC hm t₁.1.1 t₁.2.1.1 t₁.2.2.1).entry
            (blockEquiv q (a, 0 - u a)) (blockEquiv q (b, 0 + d - v b)))).1 = 0 ↔
            d - (v b - u a) ∈ t₁.1.1.O a b := by
          have hsub : 0 + d - v b - (0 - u a) = d - (v b - u a) := by ring
          rw [buildSquareC_entry]; simp only [hsub]; split_ifs with hd <;> simp [hd]
        rw [← h1, ← hent, h2]
        simp only [translatePattern, Finset.mem_image]
        exact ⟨fun h => ⟨d - (v b - u a), h, by ring⟩, fun ⟨d', hd', hd''⟩ => by
          have : d - (v b - u a) = d' := by linear_combination -hd''
          rwa [this]⟩
      -- By uniqueness of centering on `t₁.1.1` (which is ALREADY centered!), `u₁ = v₀ = v₁ = 0`!
      have hsum0 : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d ∈ t₁.1.1.O a b, d) = 0 := by
        simp only [show ∀ a b, ∑ d ∈ t₁.1.1.O a b, d = 0 from t₁.1.2, Finset.sum_const_zero]
      have huniq := existsUnique_center_pattern hq hm0 hmq t₁.1.1 hsum0
      let p0 : ZMod q × ZMod q × ZMod q := (0, 0, 0)
      let p1 : ZMod q × ZMod q × ZMod q := (u 1, v 0, v 1)
      have hp0 : (translatePattern t₁.1.1 (fun a => if a = 0 then 0 else p0.1)
          (fun b => if b = 0 then p0.2.1 else p0.2.2)).IsCentered := by
        intro a b; simp only [p0, translatePattern, ite_self, sub_self, add_zero, Finset.image_id']
        exact t₁.1.2 a b
      have hp1 : (translatePattern t₁.1.1 (fun a => if a = 0 then 0 else p1.1)
          (fun b => if b = 0 then p1.2.1 else p1.2.2)).IsCentered := by
        have htr : translatePattern t₁.1.1 (fun a => if a = 0 then 0 else p1.1)
            (fun b => if b = 0 then p1.2.1 else p1.2.2) = t₂.1.1 := by
          rw [hOeq]; congr 1
          · ext a; fin_cases a; exact hu0.symm; rfl
          · ext b; fin_cases b <;> rfl
        rw [htr]; exact t₂.1.2
      have hp_eq : p1 = p0 := huniq.unique hp1 hp0
      have hu1 : u 1 = 0 := congrArg Prod.fst hp_eq
      have hv0 : v 0 = 0 := congrArg (fun p => p.2.1) hp_eq
      have hv1 : v 1 = 0 := congrArg (fun p => p.2.2) hp_eq
      have hu_all : u = 0 := funext fun a => by fin_cases a <;> assumption
      have hv_all : v = 0 := funext fun b => by fin_cases b <;> assumption
      have hO_same : t₁.1 = t₂.1 := by
        apply Subtype.ext; rw [hOeq]; ext a b d
        simp [translatePattern, hu_all, hv_all]
      -- Now `w 0 = 0` and `w 1 = 0` from centering of `h0` and `h1`!
      rcases t₁ with ⟨O₁, ⟨h0₁, hh0₁⟩, ⟨h1₁, hh1₁⟩⟩
      rcases t₂ with ⟨O₂, ⟨h0₂, hh0₂⟩, ⟨h1₂, hh1₂⟩⟩
      dsimp only at hO_same; subst hO_same
      have hshift0 : ∀ a b (d : O₁.1.O a b), h0₂.h a b d = h0₁.h a b d + w 0 := by
        intro a b ⟨d, hd⟩
        have hent := congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d))) hg'
        rw [sylowP_act_entry] at hent
        have hu_a : (sylowToVec g').1 a = 0 := congrFun hu_all a
        have hv_b : (sylowToVec g').2.1 b = 0 := congrFun hv_all b
        rw [buildSquareC_entry, buildSquareC_entry] at hent
        simp only [hu_a, hv_b, sub_zero, zero_add, hd, ↓reduceDIte, blockTransPerm_apply] at hent
        exact (congrArg Prod.snd ((blockEquiv q).injective hent)).symm
      have hshift1 : ∀ a b (d : (O₁.1.compl hm).O a b), h1₂.h a b d = h1₁.h a b d + w 1 := by
        intro a b ⟨d, hd⟩
        have hnd : d ∉ O₁.1.O a b := Finset.mem_compl.mp hd
        have hent := congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d))) hg'
        rw [sylowP_act_entry] at hent
        have hu_a : (sylowToVec g').1 a = 0 := congrFun hu_all a
        have hv_b : (sylowToVec g').2.1 b = 0 := congrFun hv_all b
        rw [buildSquareC_entry, buildSquareC_entry] at hent
        simp only [hu_a, hv_b, sub_zero, zero_add, hnd, ↓reduceDIte, blockTransPerm_apply] at hent
        exact (congrArg Prod.snd ((blockEquiv q).injective hent)).symm
      have hw0 : w 0 = 0 := by
        have h1 := hh0₂ 0 0; have h2 := hh0₁ 0 0
        simp_rw [hshift0 0 0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, O₁.1.card_00, nsmul_eq_mul, h2, zero_add] at h1
        exact (mul_eq_zero.mp h1).resolve_left hm_ne
      have hw1 : w 1 = 0 := by
        have h1 := hh1₂ 0 0; have h2 := hh1₁ 0 0
        simp_rw [hshift1 0 0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, (O₁.1.compl hm).card_00, nsmul_eq_mul, h2, zero_add] at h1
        exact (mul_eq_zero.mp h1).resolve_left hqm_ne
      congr 1; refine Prod.ext (Subtype.ext (Layer.ext ?_)) (Subtype.ext (Layer.ext ?_))
      · funext a b d; rw [hshift0 a b d, hw0, add_zero]
      · funext a b d; rw [hshift1 a b d, hw1, add_zero]
    · -- Surjective: every `P`-orbit in `StratumFix q (ellC q) m` contains a centered square!
      intro o _
      let L₀ := Quotient.out o
      -- Extract raw `(O, h0, h1)` from `L₀`
      obtain ⟨hm', O', hO'⟩ := pattern_of_fix_rankone (fun _ => 1) L₀.1 L₀.2.1
      have hstrat : stratumOf q L₀.1 = m := L₀.2.2
      let O : Pattern q m :=
        { O := O'.O
          card_00 := by rw [O'.card_00, hstrat]
          card_11 := by rw [O'.card_11, hstrat]
          card_01 := by rw [O'.card_01, hstrat]
          card_10 := by rw [O'.card_10, hstrat] }
      have hO : ∀ a b x d, d ∈ O.O a b ↔
          ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := hO'
      have hshift : ∀ a b x d, L₀.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
          blockEquiv q (((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1,
            ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 + x) := by
        intro a b x d
        have hpow : ellC q ^ x.val ∈ Subgroup.zpowers (ellC q) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
        have hfix := (sylow_fix_entry_iff (ellC q ^ x.val) L₀.1).mp
          (L₀.2.1 (ellC q ^ x.val).1 ⟨ellC q ^ x.val, hpow, rfl⟩) a b 0 d
        rw [sylowToVec_ellC_pow, ZMod.natCast_zmod_val] at hfix
        simpa [zero_add, add_comm] using hfix
      -- Construct raw `h0 : Layer O` so we get `∑ s(O_{ab}) = 0`!
      let h0_raw : Layer O := extractMovingLayer hm L₀.1 O 0
        (fun a b d hd => by simpa using (hO a b 0 d).mp hd)
        (fun a b x d hd => by
          have h1 := (hO a b 0 d).mp hd; simp only [zero_add] at h1
          rw [hshift a b x d, h1])
      obtain ⟨⟨u₁, v₀, v₁⟩, hOc, _⟩ := existsUnique_center_pattern hq hm0 hmq O (layer_pattern_sum_zero hq_odd O h0_raw)
      -- First translate `L₀` by `g_pat = (0, u₁; v₀, v₁; 0, 0)` to center its pattern to `Oc`
      let u : Fin 2 → ZMod q := fun a => if a = 0 then 0 else u₁
      let v : Fin 2 → ZMod q := fun b => if b = 0 then v₀ else v₁
      let Oc := translatePattern O u v
      let g_pat : sylowP q := vecToSylow (u, v, 0)
      let L1 : StratumFix q (ellC q) m := ⟨g_pat.1 • L₀.1, sylowP_preserves_stratumFix (ellC q) (by simp) g_pat L₀⟩
      -- Extract `h0_1, h1_1` on `Oc`, then shift symbol blocks by `w0, w1` to center both!
      have hL1_O : ∀ a b x d, d ∈ Oc.O a b ↔
          ((blockEquiv q).symm (L1.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := by
        intro a b x d
        change _ ↔ ((blockEquiv q).symm ((g_pat.1 • L₀.1).entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0
        rw [sylowP_act_entry]
        have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q (sylowToVec g_pat).2.2 k)).1 =
            ((blockEquiv q).symm k).1 := fun k => by
          obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
          rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rw [hbt, show (sylowToVec g_pat).1 = u from by simp [g_pat],
            show (sylowToVec g_pat).2.1 = v from by simp [g_pat]]
        have hsub : x + d - v b = (x - u a) + (d - (v b - u a)) := by ring
        rw [hsub, ← hO a b (x - u a) (d - (v b - u a))]
        simp only [Oc, translatePattern, Finset.mem_image]
        exact ⟨fun ⟨d', hd', hd''⟩ => by
                 have hdeq : d - (v b - u a) = d' := by linear_combination -hd''
                 rwa [hdeq],
               fun h => ⟨d - (v b - u a), h, by ring⟩⟩
      let Φ0 : ZMod q := ∑ d : Oc.O 0 0, ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2
      let Φ1 : ZMod q := ∑ d : (Oc.compl hm).O 0 0, ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2
      let w : Fin 2 → ZMod q := fun c =>
        if c = 0 then -(Φ0 * (m : ZMod q)⁻¹) else -(Φ1 * ((q - m : ℕ) : ZMod q)⁻¹)
      let g_sym : sylowP q := vecToSylow (0, 0, w)
      let L2 : StratumFix q (ellC q) m := ⟨g_sym.1 • L1.1, sylowP_preserves_stratumFix (ellC q) (by simp) g_sym L1⟩
      -- Extract centered `h0, h1` directly from `L2`!
      have hL2_O : ∀ a b x d, d ∈ Oc.O a b ↔
          ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := by
        intro a b x d
        change _ ↔ ((blockEquiv q).symm ((g_sym.1 • L1.1).entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0
        rw [sylowP_act_entry]
        have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q (sylowToVec g_sym).2.2 k)).1 =
            ((blockEquiv q).symm k).1 := fun k => by
          obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
          rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rw [hbt]
        have hu0' : (sylowToVec g_sym).1 = 0 := by simp [g_sym]
        have hv0' : (sylowToVec g_sym).2.1 = 0 := by simp [g_sym]
        rw [hu0', hv0']; simp only [Pi.zero_apply, sub_zero]; exact hL1_O a b x d
      have hL2_sh : ∀ a b x d, L2.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
          blockEquiv q (((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1,
            ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 + x) := by
        intro a b x d
        have hpow : ellC q ^ x.val ∈ Subgroup.zpowers (ellC q) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
        have hfix := (sylow_fix_entry_iff (ellC q ^ x.val) L2.1).mp
          (L2.2.1 (ellC q ^ x.val).1 ⟨ellC q ^ x.val, hpow, rfl⟩) a b 0 d
        rw [sylowToVec_ellC_pow, ZMod.natCast_zmod_val] at hfix
        simpa [zero_add, add_comm] using hfix
      have hL2_c1 : ∀ a b d, d ∈ (Oc.compl hm).O a b →
          ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 1 := by
        intro a b d hd
        have hne : ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 ≠ 0 :=
          fun h0 => Finset.mem_compl.mp hd ((hL2_O a b 0 d).mpr (by simpa using h0))
        generalize ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = c at hne ⊢
        fin_cases c; exact (hne rfl).elim; rfl
      let h0_c : Layer Oc := extractMovingLayer hm L2.1 Oc 0
        (fun a b d hd => by simpa using (hL2_O a b 0 d).mp hd)
        (fun a b x d hd => by
          have h1 := (hL2_O a b 0 d).mp hd; simp only [zero_add] at h1
          rw [hL2_sh a b x d, h1])
      let h1_c : Layer (Oc.compl hm) := extractMovingLayer (Nat.sub_le q m) L2.1 (Oc.compl hm) 1
        hL2_c1 (fun a b x d hd => by rw [hL2_sh a b x d, hL2_c1 a b d hd])
      have h0_cent : h0_c.IsCentered := (layer_isCentered_iff_00 hq_odd Oc hOc h0_c).mpr (by
        have hterm : ∀ d : Oc.O 0 0, h0_c.h 0 0 d =
            ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2 + w 0 := by
          intro d
          change ((blockEquiv q).symm ((g_sym.1 • L1.1).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2 = _
          have ha := sylowP_act_entry g_sym L1.1 0 0 0 d.1
          simp only [zero_add, zero_sub, g_sym, sylowToVec_vecToSylow, Pi.zero_apply, neg_zero, sub_zero] at ha
          rw [ha]
          have h0 := (hL1_O 0 0 0 d.1).mp d.2; simp only [zero_add] at h0
          conv_lhs => rw [← (blockEquiv q).apply_symm_apply (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))]
          rw [blockTransPerm_apply, Equiv.symm_apply_apply, h0]
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          Oc.card_00, nsmul_eq_mul]
        change Φ0 + (m : ZMod q) * (-(Φ0 * (m : ZMod q)⁻¹)) = 0
        rw [mul_neg, mul_comm (m : ZMod q), mul_assoc, inv_mul_cancel₀ hm_ne, mul_one, add_neg_cancel])
      have hOc_compl : (Oc.compl hm).IsCentered := by
        intro a b
        have htot := Finset.sum_add_sum_compl (Oc.O a b) (fun d : ZMod q => d)
        rw [hOc a b, zero_add, sum_univ_zmod_odd hq_odd] at htot; exact htot
      have h1_cent : h1_c.IsCentered := (layer_isCentered_iff_00 hq_odd (Oc.compl hm) hOc_compl h1_c).mpr (by
        have hterm : ∀ d : (Oc.compl hm).O 0 0, h1_c.h 0 0 d =
            ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2 + w 1 := by
          intro d
          change ((blockEquiv q).symm ((g_sym.1 • L1.1).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2 = _
          have ha := sylowP_act_entry g_sym L1.1 0 0 0 d.1
          simp only [zero_add, zero_sub, g_sym, sylowToVec_vecToSylow, Pi.zero_apply, neg_zero, sub_zero] at ha
          rw [ha]
          have hne : ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).1 ≠ 0 :=
            fun h0 => Finset.mem_compl.mp d.2 ((hL1_O 0 0 0 d.1).mpr (by simpa using h0))
          have h1 : ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).1 = 1 := by
            generalize ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).1 = c at hne ⊢
            fin_cases c; exact (hne rfl).elim; rfl
          conv_lhs => rw [← (blockEquiv q).apply_symm_apply (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))]
          rw [blockTransPerm_apply, Equiv.symm_apply_apply, h1]
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          (Oc.compl hm).card_00, nsmul_eq_mul]
        change Φ1 + ((q - m : ℕ) : ZMod q) * (-(Φ1 * ((q - m : ℕ) : ZMod q)⁻¹)) = 0
        rw [mul_neg, mul_comm ((q - m : ℕ) : ZMod q), mul_assoc, inv_mul_cancel₀ hqm_ne, mul_one,
          add_neg_cancel])
      have hL2_eq : buildSquareC hm Oc h0_c h1_c = L2.1 := by
        apply LatinSquare.ext; funext r col
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
        have hs := hL2_sh a b x (y - x)
        rw [add_sub_cancel] at hs; rw [hs, buildSquareC_entry]
        split_ifs with hd
        · have h0 := (hL2_O a b 0 (y - x)).mp hd; simp only [zero_add] at h0
          rw [h0]; apply congrArg (blockEquiv q); exact Prod.ext rfl (by dsimp [h0_c, extractMovingLayer]; ring)
        · have h1 := hL2_c1 a b (y - x) (Finset.mem_compl.mpr hd)
          rw [h1]; apply congrArg (blockEquiv q); exact Prod.ext rfl (by dsimp [h1_c, extractMovingLayer]; ring)
      refine ⟨⟨⟨Oc, hOc⟩, ⟨h0_c, h0_cent⟩, ⟨h1_c, h1_cent⟩⟩, Finset.mem_univ _, ?_⟩
      rw [← Quotient.out_eq o]
      apply Quotient.sound
      refine ⟨(g_sym * g_pat)⁻¹, ?_⟩
      dsimp only [L2, L1] at hL2_eq
      change (g_sym * g_pat)⁻¹.1 • buildSquareC hm Oc h0_c h1_c = L₀.1
      rw [hL2_eq, ← mul_smul]
      change ((g_sym * g_pat)⁻¹ * (g_sym * g_pat)).1 • L₀.1 = L₀.1
      simp
    · -- Signs match!
      intro t _
      have hqeq : Quotient.mk R (Quotient.out (Quotient.mk R ⟨buildSquareC hm t.1.1 t.2.1.1 t.2.2.1, hmkC_mem t⟩)) =
          Quotient.mk R ⟨buildSquareC hm t.1.1 t.2.1.1 t.2.2.1, hmkC_mem t⟩ := Quotient.out_eq _
      rcases Quotient.exact hqeq with ⟨g, hg⟩
      change g.1 • (Quotient.out (Quotient.mk R ⟨buildSquareC hm t.1.1 t.2.1.1 t.2.2.1, hmkC_mem t⟩)).1 =
        buildSquareC hm t.1.1 t.2.1.1 t.2.2.1 at hg
      rw [← hmkC_sign t]
      have hs := congrArg (fun M => (squareSign M : ℤ)) hg
      rw [squareSign_isotopyAct_even (even_two_mul q)] at hs
      exact hs.symm

/-- Helper for Lemma 6.10 Part B: every `P`-orbit in `StratumFix q (ellB q) m` has a centered representative. -/
private lemma lem_6_10_partB_exists_cent (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) (L₀ : StratumFix q (ellB q) m) :
    ∃ (O : { O : Pattern q m // O.IsCentered }) (φ : FixedLayer O.1)
      (h1 : { h1 : Layer (O.1.compl (le_of_lt hmq)) // h1.IsCentered }),
      ∃ g : sylowP q, g.1 • buildSquareB (le_of_lt hmq) O.1 φ h1.1 = L₀.1 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have hm : m ≤ q := le_of_lt hmq
  have hqm_ne : ((q - m : ℕ) : ZMod q) ≠ 0 := by
    have hpos : 0 < q - m := by omega
    have hlt : q - m < q := by omega
    intro h0
    exact absurd (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff (q - m) q).mp h0)) (not_le_of_gt hlt)
  obtain ⟨hm', O', hO'⟩ := pattern_of_fix_rankone (fun c => if c = 0 then 0 else 1) L₀.1 L₀.2.1
  have hstrat : stratumOf q L₀.1 = m := L₀.2.2
  let O : Pattern q m :=
    { O := O'.O
      card_00 := by rw [O'.card_00, hstrat]
      card_11 := by rw [O'.card_11, hstrat]
      card_01 := by rw [O'.card_01, hstrat]
      card_10 := by rw [O'.card_10, hstrat] }
  have hO : ∀ a b x d, d ∈ O.O a b ↔
      ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := hO'
  have hshift : ∀ a b x d, L₀.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
      blockEquiv q (((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1,
        ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 +
          (if ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 0 then 0 else x)) := by
    intro a b x d
    have hpow : ellB q ^ x.val ∈ Subgroup.zpowers (ellB q) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    have hfix := (sylow_fix_entry_iff (ellB q ^ x.val) L₀.1).mp
      (L₀.2.1 (ellB q ^ x.val).1 ⟨ellB q ^ x.val, hpow, rfl⟩) a b 0 d
    rw [sylowToVec_ellB_pow, ZMod.natCast_zmod_val] at hfix
    simpa [zero_add, add_comm] using hfix
  have hL0_c1 : ∀ a b d, d ∈ (O.compl hm).O a b →
      ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 1 := by
    intro a b d hd
    have hne : ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 ≠ 0 :=
      fun h0 => Finset.mem_compl.mp hd ((hO a b 0 d).mpr (by simpa using h0))
    generalize ((blockEquiv q).symm (L₀.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = c at hne ⊢
    fin_cases c; exact (hne rfl).elim; rfl
  let h1_raw : Layer (O.compl hm) := extractMovingLayer (Nat.sub_le q m) L₀.1 (O.compl hm) 1
    hL0_c1 (fun a b x d hd => by
      rw [hshift a b x d, hL0_c1 a b d hd]; simp only [one_ne_zero, ↓reduceIte])
  have hOsum0 : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d ∈ O.O a b, d) = 0 := by
    have hc := layer_pattern_sum_zero hq_odd (O.compl hm) h1_raw
    have hneg : ∀ a b, (∑ d ∈ (O.compl hm).O a b, d) = -(∑ d ∈ O.O a b, d) := fun a b => by
      have htot := Finset.sum_add_sum_compl (O.O a b) (fun d : ZMod q => d)
      rw [sum_univ_zmod_odd hq_odd] at htot
      change (∑ d ∈ (O.O a b)ᶜ, d) = _; linear_combination htot
    simp_rw [hneg, Finset.sum_neg_distrib] at hc
    exact neg_eq_zero.mp hc
  obtain ⟨⟨u₁, v₀, v₁⟩, hOc, _⟩ := existsUnique_center_pattern hq hm0 hmq O hOsum0
  let u : Fin 2 → ZMod q := fun a => if a = 0 then 0 else u₁
  let v : Fin 2 → ZMod q := fun b => if b = 0 then v₀ else v₁
  let Oc := translatePattern O u v
  let g_pat : sylowP q := vecToSylow (u, v, 0)
  let L1 : StratumFix q (ellB q) m := ⟨g_pat.1 • L₀.1, sylowP_preserves_stratumFix (ellB q) (by simp) g_pat L₀⟩
  have hL1_O : ∀ a b x d, d ∈ Oc.O a b ↔
      ((blockEquiv q).symm (L1.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := by
    intro a b x d
    change _ ↔ ((blockEquiv q).symm ((g_pat.1 • L₀.1).entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0
    rw [sylowP_act_entry]
    have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q (sylowToVec g_pat).2.2 k)).1 =
        ((blockEquiv q).symm k).1 := fun k => by
      obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
      rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rw [hbt, show (sylowToVec g_pat).1 = u from by simp [g_pat],
        show (sylowToVec g_pat).2.1 = v from by simp [g_pat]]
    have hsub : x + d - v b = (x - u a) + (d - (v b - u a)) := by ring
    rw [hsub, ← hO a b (x - u a) (d - (v b - u a))]
    simp only [Oc, translatePattern, Finset.mem_image]
    exact ⟨fun ⟨d', hd', hd''⟩ => by
             have hdeq : d - (v b - u a) = d' := by linear_combination -hd''
             rwa [hdeq],
           fun h => ⟨d - (v b - u a), h, by ring⟩⟩
  let Φ1 : ZMod q := ∑ d : (Oc.compl hm).O 0 0,
    ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2
  let w : Fin 2 → ZMod q := fun c => if c = 0 then 0 else -(Φ1 * ((q - m : ℕ) : ZMod q)⁻¹)
  let g_sym : sylowP q := vecToSylow (0, 0, w)
  let L2 : StratumFix q (ellB q) m := ⟨g_sym.1 • L1.1, sylowP_preserves_stratumFix (ellB q) (by simp) g_sym L1⟩
  have hL2_O : ∀ a b x d, d ∈ Oc.O a b ↔
      ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0 := by
    intro a b x d
    change _ ↔ ((blockEquiv q).symm ((g_sym.1 • L1.1).entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)))).1 = 0
    rw [sylowP_act_entry]
    have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q (sylowToVec g_sym).2.2 k)).1 =
        ((blockEquiv q).symm k).1 := fun k => by
      obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
      rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rw [hbt]
    have hu0' : (sylowToVec g_sym).1 = 0 := by simp [g_sym]
    have hv0' : (sylowToVec g_sym).2.1 = 0 := by simp [g_sym]
    rw [hu0', hv0']; simp only [Pi.zero_apply, sub_zero]; exact hL1_O a b x d
  have hL2_sh : ∀ a b x d, L2.1.entry (blockEquiv q (a, x)) (blockEquiv q (b, x + d)) =
      blockEquiv q (((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1,
        ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).2 +
          (if ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 0 then 0 else x)) := by
    intro a b x d
    have hpow : ellB q ^ x.val ∈ Subgroup.zpowers (ellB q) := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    have hfix := (sylow_fix_entry_iff (ellB q ^ x.val) L2.1).mp
      (L2.2.1 (ellB q ^ x.val).1 ⟨ellB q ^ x.val, hpow, rfl⟩) a b 0 d
    rw [sylowToVec_ellB_pow, ZMod.natCast_zmod_val] at hfix
    simpa [zero_add, add_comm] using hfix
  have hL2_c1 : ∀ a b d, d ∈ (Oc.compl hm).O a b →
      ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = 1 := by
    intro a b d hd
    have hne : ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 ≠ 0 :=
      fun h0 => Finset.mem_compl.mp hd ((hL2_O a b 0 d).mpr (by simpa using h0))
    generalize ((blockEquiv q).symm (L2.1.entry (blockEquiv q (a, 0)) (blockEquiv q (b, d)))).1 = c at hne ⊢
    fin_cases c; exact (hne rfl).elim; rfl
  let φ_c : FixedLayer Oc := extractFixedLayer hm L2.1 Oc
    (fun a b d hd => by simpa using (hL2_O a b 0 d).mp hd)
    (fun a b x d hd => by
      have h1 := (hL2_O a b 0 d).mp hd; simp only [zero_add] at h1
      rw [hL2_sh a b x d, h1]; simp only [↓reduceIte, add_zero])
  let h1_c : Layer (Oc.compl hm) := extractMovingLayer (Nat.sub_le q m) L2.1 (Oc.compl hm) 1
    hL2_c1 (fun a b x d hd => by
      rw [hL2_sh a b x d, hL2_c1 a b d hd]; simp only [one_ne_zero, ↓reduceIte])
  have hOc_compl : (Oc.compl hm).IsCentered := by
    intro a b
    have htot := Finset.sum_add_sum_compl (Oc.O a b) (fun d : ZMod q => d)
    rw [hOc a b, zero_add, sum_univ_zmod_odd hq_odd] at htot; exact htot
  have h1_cent : h1_c.IsCentered := (layer_isCentered_iff_00 hq_odd (Oc.compl hm) hOc_compl h1_c).mpr (by
    have hterm : ∀ d : (Oc.compl hm).O 0 0, h1_c.h 0 0 d =
        ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2 + w 1 := by
      intro d
      change ((blockEquiv q).symm ((g_sym.1 • L1.1).entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).2 = _
      have ha := sylowP_act_entry g_sym L1.1 0 0 0 d.1
      simp only [zero_add, g_sym, sylowToVec_vecToSylow, Pi.zero_apply, sub_zero] at ha
      rw [ha]
      have hne : ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).1 ≠ 0 :=
        fun h0 => Finset.mem_compl.mp d.2 ((hL1_O 0 0 0 d.1).mpr (by simpa using h0))
      have h1 : ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).1 = 1 := by
        generalize ((blockEquiv q).symm (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))).1 = c at hne ⊢
        fin_cases c; exact (hne rfl).elim; rfl
      conv_lhs => rw [← (blockEquiv q).apply_symm_apply (L1.1.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d.1)))]
      rw [blockTransPerm_apply, Equiv.symm_apply_apply, h1]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      (Oc.compl hm).card_00, nsmul_eq_mul]
    change Φ1 + ((q - m : ℕ) : ZMod q) * (-(Φ1 * ((q - m : ℕ) : ZMod q)⁻¹)) = 0
    rw [mul_neg, mul_comm ((q - m : ℕ) : ZMod q), mul_assoc, inv_mul_cancel₀ hqm_ne, mul_one,
      add_neg_cancel])
  have hL2_eq : buildSquareB hm Oc φ_c h1_c = L2.1 := by
    apply LatinSquare.ext; funext r col
    obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
    obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    have hs := hL2_sh a b x (y - x)
    rw [add_sub_cancel] at hs; rw [hs, buildSquareB_entry]
    by_cases hd : y - x ∈ Oc.O a b
    · rw [dif_pos hd]
      have h0 := (hL2_O a b 0 (y - x)).mp hd; simp only [zero_add] at h0
      rw [h0]; simp [φ_c, extractFixedLayer]
    · rw [dif_neg hd]
      have h1 := hL2_c1 a b (y - x) (Finset.mem_compl.mpr hd)
      rw [h1]; simp only [one_ne_zero, ↓reduceIte]; apply congrArg (blockEquiv q)
      exact Prod.ext rfl (by dsimp [h1_c, extractMovingLayer]; ring)
  refine ⟨⟨Oc, hOc⟩, φ_c, ⟨h1_c, h1_cent⟩, (g_sym * g_pat)⁻¹, ?_⟩
  dsimp only [L2, L1] at hL2_eq
  change (g_sym * g_pat)⁻¹.1 • buildSquareB hm Oc φ_c h1_c = L₀.1
  rw [hL2_eq, ← mul_smul]
  change ((g_sym * g_pat)⁻¹ * (g_sym * g_pat)).1 • L₀.1 = L₀.1; simp

/-- Part 1 of Lemma 6.10: `N_{B,m} = (q-1)! m! (q-m)! ∑_O Ω(O^c)`. -/
private lemma lem_6_10_partB (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    mixedOrbitCountB q m =
      (((q - 1).factorial * m.factorial * (q - m).factorial : ℕ) : ℤ) *
        ∑ O ∈ centeredPatterns q m, OmegaSum (O.compl (le_of_lt hmq)) := by
    classical
    have : Fact q.Prime := ⟨hq⟩
    have hq_odd : Odd q := hq.odd_of_ne_two hodd
    have hm : m ≤ q := le_of_lt hmq
    have hqm_ne : ((q - m : ℕ) : ZMod q) ≠ 0 := by
      have hpos : 0 < q - m := by omega
      have hlt : q - m < q := by omega
      intro h0
      exact absurd (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff (q - m) q).mp h0)) (not_le_of_gt hlt)
    have h67 := lem_6_7_factor q hq hodd
    -- Prove `q * mixedOrbitCountB q m = ∑_{t : CentB} layerSign t.h1 = (q! * m! * (q-m)!) * ∑_O Ω(O^c)`
    -- and cancel `q`!
    unfold mixedOrbitCountB mixedOrbitCount
    set R : Setoid (StratumFix q (ellB q) m) :=
      { r := fun L₁ L₂ => ∃ g : sylowP q, g.1 • L₁.1 = L₂.1
        iseqv :=
          ⟨fun L => ⟨1, one_smul _ _⟩,
           fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg]; simp⟩,
           fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ => ⟨g₂ * g₁, by rw [← h₂, ← h₁]; exact mul_smul _ _ _⟩⟩ }
    let CentB := Σ O : { O : Pattern q m // O.IsCentered },
      FixedLayer O.1 × { h1 : Layer (O.1.compl hm) // h1.IsCentered }
    have hsum_cent :
        (∑ t : CentB, (layerSign t.2.2.1 : ℤ)) =
        ((q.factorial * m.factorial * (q - m).factorial : ℕ) : ℤ) *
          ∑ O ∈ centeredPatterns q m, OmegaSum (O.compl hm) := by
      dsimp only [CentB]
      rw [Fintype.sum_sigma]
      have hinner : ∀ O : { O : Pattern q m // O.IsCentered },
          (∑ p : FixedLayer O.1 × { h1 : Layer (O.1.compl hm) // h1.IsCentered },
            (layerSign p.2.1 : ℤ)) =
          ((q.factorial * m.factorial * (q - m).factorial : ℕ) : ℤ) * OmegaSum (O.1.compl hm) := by
        intro O
        rw [Fintype.sum_prod_type]
        dsimp only
        rw [Finset.sum_const, Finset.card_univ, card_fixedLayer hm O.1, nsmul_eq_mul]
        refine congrArg (((q.factorial * m.factorial * (q - m).factorial : ℕ) : ℤ) * ·) ?_
        unfold OmegaSum
        refine Finset.sum_bij (fun x _ => x.1)
          (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun y hy => ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)
      simp_rw [hinner, ← Finset.mul_sum]
      refine congrArg (((q.factorial * m.factorial * (q - m).factorial : ℕ) : ℤ) * ·) ?_
      unfold centeredPatterns
      refine Finset.sum_bij (fun O _ => O.1)
        (fun O _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.2⟩)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun O hO => ⟨⟨O, (Finset.mem_filter.mp hO).2⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    have hmkB_mem : ∀ t : CentB,
        buildSquareB hm t.1.1 t.2.1 t.2.2.1 ∈
          fixSet ((Subgroup.zpowers (ellB q)).map (sylowP q).subtype) ∧
        stratumOf q (buildSquareB hm t.1.1 t.2.1 t.2.2.1) = m := by
      intro ⟨⟨O, _⟩, φ, ⟨h1, _⟩⟩
      refine ⟨?_, ?_⟩
      · rintro _ ⟨g, hg, rfl⟩
        change g.1 • buildSquareB hm O φ h1 = buildSquareB hm O φ h1
        rw [sylow_fix_entry_iff]
        rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
        have hk : ∃ n : ℕ, ellB q ^ k = ellB q ^ n := by
          have hord : ellB q ^ q = 1 := (isElemAbelian_sylowP_subgroup q ⊤).2 (ellB q) trivial
          refine ⟨(k % (q : ℤ)).toNat, ?_⟩
          have hmod : k = (q : ℤ) * (k / (q : ℤ)) + k % (q : ℤ) := (Int.mul_ediv_add_emod k q).symm
          have hnn : 0 ≤ k % (q : ℤ) := Int.emod_nonneg k (by exact_mod_cast hq.ne_zero)
          conv_lhs => rw [hmod, zpow_add, zpow_mul, zpow_natCast, hord, one_zpow, one_mul]
          rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
        rcases hk with ⟨n, hn⟩; rw [hn, sylowToVec_ellB_pow]
        intro a b x y
        rw [buildSquareB_entry, buildSquareB_entry]
        have hsub : y + (n : ZMod q) - (x + (n : ZMod q)) = y - x := by ring
        rw [hsub]
        split_ifs <;> simp <;> ring
      · unfold stratumOf
        have hfilt : (Finset.univ.filter fun d : ZMod q =>
            ((blockEquiv q).symm ((buildSquareB hm O φ h1).entry (blockEquiv q (0, 0))
              (blockEquiv q (0, d)))).1 = 0) = O.O 0 0 := by
          ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, buildSquareB_entry,
            Equiv.symm_apply_apply, sub_zero]
          split_ifs with hd <;> simp [hd]
        rw [hfilt, O.card_00]
    have hmkB_sign : ∀ t : CentB,
        (squareSign (buildSquareB hm t.1.1 t.2.1 t.2.2.1) : ℤ) = (layerSign t.2.2.1 : ℤ) := by
      intro t
      have h := h67.2.1 (buildSquareB hm t.1.1 t.2.1 t.2.2.1) m hm t.1.1 t.2.2.1
        (hmkB_mem t).1 (fun a b x d => ⟨by
          rw [buildSquareB_entry]; simp only [add_sub_cancel_left]
          split_ifs with hd <;> simp [hd],
          fun hd => by
            have hnd : d ∉ t.1.1.O a b := Finset.mem_compl.mp hd
            rw [buildSquareB_entry]; simp [hnd]⟩)
      rw [h]
    -- Map `CentB → Quotient R`, fiberwise each fiber has size `q` and constant sign `squareSign (out o)`!
    let proj : CentB → Quotient R := fun t =>
      Quotient.mk R ⟨buildSquareB hm t.1.1 t.2.1 t.2.2.1, hmkB_mem t⟩
    have hfib_sum : (∑ t : CentB, (layerSign t.2.2.1 : ℤ)) =
        (q : ℤ) * ∑ o : Quotient R, (squareSign (Quotient.out o).1 : ℤ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Quotient R)))
        (g := proj) (fun _ _ => Finset.mem_univ _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun o _ => ?_
      have hconst : ∀ t ∈ Finset.univ.filter (fun t : CentB => proj t = o),
          (layerSign t.2.2.1 : ℤ) = (squareSign (Quotient.out o).1 : ℤ) := by
        intro t ht
        have hqeq : Quotient.mk R ⟨buildSquareB hm t.1.1 t.2.1 t.2.2.1, hmkB_mem t⟩ =
            Quotient.mk R (Quotient.out o) := by rw [Quotient.out_eq]; exact (Finset.mem_filter.mp ht).2
        rcases Quotient.exact hqeq with ⟨g, hg⟩
        rw [← hmkB_sign t, ← hg, squareSign_isotopyAct_even (even_two_mul q)]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      -- Show `(univ.filter (proj t = o)).card = q`:
      -- First prove fiber is nonempty (same centering argument as `hNC`!), then show it is in bijection with `ZMod q` via shifting `φ` by `w₀`!
      have hnonempty : ∃ t₀ : CentB, proj t₀ = o := by
        obtain ⟨O, φ, h1, g, hg⟩ := lem_6_10_partB_exists_cent q m hq hodd hm0 hmq (Quotient.out o)
        refine ⟨⟨O, φ, h1⟩, ?_⟩
        dsimp [proj]; rw [← Quotient.out_eq o]; apply Quotient.sound
        exact ⟨g, hg⟩
      rcases hnonempty with ⟨t₀, ht₀⟩
      -- Shift `t₀.φ` by `w₀ : ZMod q`: bijection `ZMod q ≃ { t : CentB // proj t = o }`!
      let shiftFL (w₀ : ZMod q) : FixedLayer t₀.1.1 :=
        { φ := fun a b d => t₀.2.1.φ a b d + w₀
          L1 := fun a => by
            convert (Equiv.addRight w₀).bijective.comp (t₀.2.1.L1 a) using 1
            ext s; rcases s with d | d <;> rfl
          L2 := fun b => by
            convert (Equiv.addRight w₀).bijective.comp (t₀.2.1.L2 b) using 1
            ext s; rcases s with d | d <;> rfl }
      have hcard_fib : (Finset.univ.filter (fun t : CentB => proj t = o)).card = q := by
        trans (Finset.univ : Finset (ZMod q)).card
        swap
        · rw [Finset.card_univ, ZMod.card]
        symm
        refine Finset.card_bij (fun w₀ _ => (⟨t₀.1, shiftFL w₀, t₀.2.2⟩ : CentB)) ?_ ?_ ?_
        · intro w₀ _
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← ht₀]; dsimp [proj]; apply Quotient.sound
          refine ⟨vecToSylow (0, 0, fun c => if c = 0 then -w₀ else 0), ?_⟩
          apply LatinSquare.ext; funext r col
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
          change ((vecToSylow (0, 0, fun c => if c = 0 then -w₀ else 0)).1 •
            buildSquareB hm t₀.1.1 (shiftFL w₀) t₀.2.2.1).entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) = _
          have ha := sylowP_act_entry (vecToSylow (0, 0, fun c => if c = 0 then -w₀ else 0))
            (buildSquareB hm t₀.1.1 (shiftFL w₀) t₀.2.2.1) a b x (y - x)
          rw [add_sub_cancel] at ha; rw [ha, buildSquareB_entry, buildSquareB_entry]
          simp only [sylowToVec_vecToSylow, Pi.zero_apply, sub_zero]
          split_ifs with hd
          · simp [blockTransPerm_apply, shiftFL]
          · simp [blockTransPerm_apply]
        · intro w₁ _ w₂ _ hEq
          have hφ : shiftFL w₁ = shiftFL w₂ :=
            congrArg Prod.fst (eq_of_heq (Sigma.mk.inj hEq).2)
          rcases Finset.card_pos.mp (by rw [t₀.1.1.card_00]; exact hm0) with ⟨d₀, hd₀⟩
          have h := congrFun (congrFun (congrFun (congrArg FixedLayer.φ hφ) 0) 0) ⟨d₀, hd₀⟩
          dsimp [shiftFL] at h; linear_combination h
        · intro t ht
          have hqeq : Quotient.mk R ⟨buildSquareB hm t₀.1.1 t₀.2.1 t₀.2.2.1, hmkB_mem t₀⟩ =
              Quotient.mk R ⟨buildSquareB hm t.1.1 t.2.1 t.2.2.1, hmkB_mem t⟩ :=
            ht₀.trans (Finset.mem_filter.mp ht).2.symm
          rcases Quotient.exact hqeq with ⟨g, hg⟩
          let u0 := (sylowToVec g).1 0
          let g' := g * (ellB q ^ (-u0).val)
          have hg' : g'.1 • buildSquareB hm t₀.1.1 t₀.2.1 t₀.2.2.1 =
              buildSquareB hm t.1.1 t.2.1 t.2.2.1 := by
            change (g.1 * (ellB q ^ (-u0).val).1) • _ = _
            have hfix : (ellB q ^ (-u0).val).1 • buildSquareB hm t₀.1.1 t₀.2.1 t₀.2.2.1 =
                buildSquareB hm t₀.1.1 t₀.2.1 t₀.2.2.1 :=
              (hmkB_mem t₀).1 (ellB q ^ (-u0).val).1 ⟨ellB q ^ (-u0).val, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _, rfl⟩
            rw [mul_smul, hfix]
            exact hg
          have hu0 : (sylowToVec g').1 0 = 0 := by
            dsimp [g']; rw [sylowToVec_mul, sylowToVec_ellB_pow, ZMod.natCast_zmod_val]
            change u0 + -u0 = 0; exact add_neg_cancel _
          let u := (sylowToVec g').1; let v := (sylowToVec g').2.1; let w := (sylowToVec g').2.2
          have hOeq : t.1.1 = translatePattern t₀.1.1 u v := by
            ext a b d
            have hent := congrArg (fun M => ((blockEquiv q).symm (M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d)))).1) hg'
            rw [sylowP_act_entry] at hent
            have hbt : ∀ k, ((blockEquiv q).symm (blockTransPerm q w k)).1 = ((blockEquiv q).symm k).1 := fun k => by
              obtain ⟨⟨c, z⟩, rfl⟩ := (blockEquiv q).surjective k
              rw [blockTransPerm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
            rw [hbt] at hent
            have h1 : ((blockEquiv q).symm ((buildSquareB hm t.1.1 t.2.1 t.2.2.1).entry
                (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d)))).1 = 0 ↔ d ∈ t.1.1.O a b := by
              rw [buildSquareB_entry]; simp only [add_sub_cancel_left]; split_ifs with hd <;> simp [hd]
            have h2 : ((blockEquiv q).symm ((buildSquareB hm t₀.1.1 t₀.2.1 t₀.2.2.1).entry
                (blockEquiv q (a, 0 - u a)) (blockEquiv q (b, 0 + d - v b)))).1 = 0 ↔
                d - (v b - u a) ∈ t₀.1.1.O a b := by
              have hsub : 0 + d - v b - (0 - u a) = d - (v b - u a) := by ring
              rw [buildSquareB_entry]; simp only [hsub]; split_ifs with hd <;> simp [hd]
            rw [← h1, ← hent, h2]; simp only [translatePattern, Finset.mem_image]
            exact ⟨fun h => ⟨d - (v b - u a), h, by ring⟩, fun ⟨d', hd', hd''⟩ => by
              have hdeq : d - (v b - u a) = d' := by linear_combination -hd''
              rwa [hdeq]⟩
          have hsum0 : (∑ a : Fin 2, ∑ b : Fin 2, ∑ d ∈ t₀.1.1.O a b, d) = 0 := by
            simp only [show ∀ a b, ∑ d ∈ t₀.1.1.O a b, d = 0 from t₀.1.2, Finset.sum_const_zero]
          have huniq := existsUnique_center_pattern hq hm0 hmq t₀.1.1 hsum0
          let p0 : ZMod q × ZMod q × ZMod q := (0, 0, 0)
          let p1 : ZMod q × ZMod q × ZMod q := (u 1, v 0, v 1)
          have hp0 : (translatePattern t₀.1.1 (fun a => if a = 0 then 0 else p0.1)
              (fun b => if b = 0 then p0.2.1 else p0.2.2)).IsCentered := fun a b => by
            simp only [p0, translatePattern, ite_self, sub_self, add_zero, Finset.image_id']
            exact t₀.1.2 a b
          have hp1 : (translatePattern t₀.1.1 (fun a => if a = 0 then 0 else p1.1)
              (fun b => if b = 0 then p1.2.1 else p1.2.2)).IsCentered := by
            have htr : translatePattern t₀.1.1 (fun a => if a = 0 then 0 else p1.1)
                (fun b => if b = 0 then p1.2.1 else p1.2.2) = t.1.1 := by
              rw [hOeq]; congr 1
              · ext a; fin_cases a; exact hu0.symm; rfl
              · ext b; fin_cases b <;> rfl
            rw [htr]; exact t.1.2
          have hp_eq : p1 = p0 := huniq.unique hp1 hp0
          have hu_all : u = 0 := funext fun a => by fin_cases a; exact hu0; exact congrArg Prod.fst hp_eq
          have hv_all : v = 0 := funext fun b => by fin_cases b; exact congrArg (fun p => p.2.1) hp_eq; exact congrArg (fun p => p.2.2) hp_eq
          have hO_same : t₀.1 = t.1 := by
            apply Subtype.ext; rw [hOeq]; ext a b d; simp [translatePattern, hu_all, hv_all]
          rcases t with ⟨Ot, φt, ⟨h1t, hh1t⟩⟩
          dsimp only at hO_same; subst hO_same
          have hshift1 : ∀ a b (d : (t₀.1.1.compl hm).O a b), h1t.h a b d = t₀.2.2.1.h a b d + w 1 := by
            intro a b ⟨d, hd⟩
            have hnd : d ∉ t₀.1.1.O a b := Finset.mem_compl.mp hd
            have hent := congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d))) hg'
            rw [sylowP_act_entry] at hent
            have hu_a : (sylowToVec g').1 a = 0 := congrFun hu_all a
            have hv_b : (sylowToVec g').2.1 b = 0 := congrFun hv_all b
            rw [buildSquareB_entry, buildSquareB_entry] at hent
            simp only [hu_a, hv_b, sub_zero, zero_add, hnd, ↓reduceDIte, blockTransPerm_apply] at hent
            exact (congrArg Prod.snd ((blockEquiv q).injective hent)).symm
          have hw1 : w 1 = 0 := by
            have h1 := hh1t 0 0; have h2 := t₀.2.2.2 0 0
            simp_rw [hshift1 0 0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_coe, (t₀.1.1.compl hm).card_00, nsmul_eq_mul, h2, zero_add] at h1
            exact (mul_eq_zero.mp h1).resolve_left hqm_ne
          have hshift0 : ∀ a b (d : t₀.1.1.O a b), φt.φ a b d = t₀.2.1.φ a b d + w 0 := by
            intro a b ⟨d, hd⟩
            have hent := congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0 + d))) hg'
            rw [sylowP_act_entry] at hent
            have hu_a : (sylowToVec g').1 a = 0 := congrFun hu_all a
            have hv_b : (sylowToVec g').2.1 b = 0 := congrFun hv_all b
            rw [buildSquareB_entry, buildSquareB_entry] at hent
            simp only [hu_a, hv_b, sub_zero, zero_add, hd, ↓reduceDIte, blockTransPerm_apply] at hent
            exact (congrArg Prod.snd ((blockEquiv q).injective hent)).symm
          refine ⟨w 0, Finset.mem_univ _, ?_⟩
          congr 1; refine Prod.ext (FixedLayer.ext ?_) (Subtype.ext (Layer.ext ?_))
          · funext a b d; exact (hshift0 a b d).symm
          · funext a b d; rw [hshift1 a b d, hw1, add_zero]
      rw [hcard_fib]
    rw [hsum_cent] at hfib_sum
    have hqfac : (q.factorial : ℤ) = (q : ℤ) * ((q - 1).factorial : ℤ) := by
      have hnat : q.factorial = q * (q - 1).factorial := by
        cases q with
        | zero => exact (hq.ne_zero rfl).elim
        | succ k => simp [Nat.factorial_succ]
      exact_mod_cast hnat
    have hq_ne : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
    apply mul_left_cancel₀ hq_ne
    rw [← hfib_sum]
    push_cast; rw [hqfac]; ring

/-- **Lemma 6.10** (`lem_6_10_layers`): For `0 < m < q`,
`N_{B,m} = (q-1)! m! (q-m)! ∑_O Ω(O^c)` and `N_{C,m} = ∑_O Ω(O) Ω(O^c)`. -/
theorem lem_6_10_layers (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    mixedOrbitCountB q m =
      (((q - 1).factorial * m.factorial * (q - m).factorial : ℕ) : ℤ) *
        ∑ O ∈ centeredPatterns q m, OmegaSum (O.compl (le_of_lt hmq)) ∧
    mixedOrbitCountC q m =
      ∑ O ∈ centeredPatterns q m, OmegaSum O * OmegaSum (O.compl (le_of_lt hmq)) :=
  ⟨lem_6_10_partB q m hq hodd hm0 hmq, lem_6_10_partC q m hq hodd hm0 hmq⟩

end Lemma610Layers

section Lemma611Traces

/-! ### Lemma 6.11: Circulant-Minor Coefficients, Traces, and Matrix Symmetry -/

/-- Coordinate evaluation of `subsetMonomial Y`. -/
private lemma subsetMonomial_apply {q : ℕ} [NeZero q] (Y : Finset (ZMod q)) (d : ZMod q) :
    subsetMonomial Y d = if d ∈ Y then 1 else 0 := rfl

/-- Product of `MvPolynomial.X (f i)` is a single monomial. -/
private lemma prod_X_eq_monomial {ι σ R : Type*} [CommSemiring R] (s : Finset ι) (f : ι → σ) :
    (∏ i ∈ s, (MvPolynomial.X (f i) : MvPolynomial σ R)) =
      MvPolynomial.monomial (∑ i ∈ s, Finsupp.single (f i) 1) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.monomial_zero']
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

/-- Part (a) of Lemma 6.11: `Z_Y(I, J) = [x^Y] det Γ(x)[I, J]`. -/
lemma ZY_eq_det_coeff {q : ℕ} [NeZero q] (Y I J : Finset (ZMod q))
    (hIJ : I.card = J.card) (hYI : Y.card = I.card) :
    ZY Y I J = (circulantSubmatrix hIJ).det.coeff (subsetMonomial Y) := by
  classical
  have hYJ : Y.card = J.card := hYI.trans hIJ
  unfold ZY circulantSubmatrix genericCirculant
  rw [dif_pos hYI, dif_pos hYJ]
  let : LinearOrder (ZMod q) := zmodLinearOrder q
  let eI : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let eJ : Fin I.card ≃o J := J.orderIsoOfFin hIJ.symm
  let eY : Fin Y.card ≃o Y := Y.orderIsoOfFin rfl
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  -- Evaluate each permutation `σ : Equiv.Perm (Fin I.card)`'s contribution to `coeff (subsetMonomial Y)`
  have hprod_mon : ∀ σ : Equiv.Perm (Fin I.card),
      (∏ r : Fin I.card, MvPolynomial.X ((eI (σ r)).1 - (eJ r).1) : MvPolynomial (ZMod q) ℤ) =
        MvPolynomial.monomial (∑ r : Fin I.card, Finsupp.single ((eI (σ r)).1 - (eJ r).1) 1) 1 := by
    intro σ
    exact prod_X_eq_monomial Finset.univ (fun r : Fin I.card => (eI (σ r)).1 - (eJ r).1)
  -- `Matrix.det_apply M = ∑ σ : Perm n, σ.sign • ∏ i, M (σ i) i`!
  have hterm : ∀ σ : Equiv.Perm (Fin I.card),
      ((Equiv.Perm.sign σ • ∏ r : Fin I.card,
          (Matrix.of fun r c => (Matrix.of fun i j => (MvPolynomial.X (i - j) : MvPolynomial (ZMod q) ℤ)) (eI r).1 (eJ c).1) (σ r) r)).coeff
        (subsetMonomial Y) =
      if (∀ r : Fin I.card, (eI (σ r)).1 - (eJ r).1 ∈ Y) ∧
          Function.Injective (fun r : Fin I.card => (eI (σ r)).1 - (eJ r).1)
      then (Equiv.Perm.sign σ : ℤ) else 0 := by
    intro σ
    rw [Units.smul_def, MvPolynomial.coeff_smul, smul_eq_mul]
    have hM : (∏ r : Fin I.card,
        (Matrix.of fun r c => (Matrix.of fun i j => (MvPolynomial.X (i - j) : MvPolynomial (ZMod q) ℤ)) (eI r).1 (eJ c).1) (σ r) r) =
        MvPolynomial.monomial (∑ r : Fin I.card, Finsupp.single ((eI (σ r)).1 - (eJ r).1) 1) 1 := by
      simpa [Matrix.of_apply] using hprod_mon σ
    rw [hM, MvPolynomial.coeff_monomial]
    -- `∑ r, single (g r) 1 = subsetMonomial Y ↔ (∀ r, g r ∈ Y) ∧ Injective g`!
    let g : Fin I.card → ZMod q := fun r => (eI (σ r)).1 - (eJ r).1
    have hiff : (∑ r : Fin I.card, Finsupp.single (g r) 1) = subsetMonomial Y ↔
        (∀ r, g r ∈ Y) ∧ Function.Injective g := by
      constructor
      · intro hEq
        have hcount : ∀ d : ZMod q, (Finset.univ.filter fun r : Fin I.card => g r = d).card =
            if d ∈ Y then 1 else 0 := fun d => by
          have hd := congrArg (fun f : ZMod q →₀ ℕ => f d) hEq
          rw [Finsupp.finsetSum_apply, subsetMonomial_apply] at hd
          simp only [Finsupp.single_apply] at hd
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one] at hd
          exact hd
        refine ⟨fun r => ?_, fun r₁ r₂ hgr => ?_⟩
        · have h1 := hcount (g r)
          have hpos : 0 < (Finset.univ.filter fun x : Fin I.card => g x = g r).card :=
            Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
          split_ifs at h1 with hmem
          · exact hmem
          · omega
        · have h1 := hcount (g r₁)
          have hle : (Finset.univ.filter fun x : Fin I.card => g x = g r₁).card ≤ 1 := by
            split_ifs at h1 <;> omega
          exact Finset.card_le_one.mp hle
            r₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
            r₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgr.symm⟩)
      · rintro ⟨hmem, hinj⟩
        have hbij : Function.Bijective (fun r : Fin I.card => (⟨g r, hmem r⟩ : Y)) := by
          have hcard : Fintype.card (Fin I.card) = Fintype.card Y := by
            simp [Fintype.card_coe, hYI]
          exact (Fintype.bijective_iff_injective_and_card _).mpr
            ⟨fun r₁ r₂ h => hinj (congrArg Subtype.val h), hcard⟩
        ext d
        rw [Finsupp.finsetSum_apply, subsetMonomial_apply]
        simp only [Finsupp.single_apply]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        by_cases hd : d ∈ Y
        · rw [if_pos hd]
          obtain ⟨r₀, hr₀⟩ := hbij.2 ⟨d, hd⟩
          have hfilt : (Finset.univ.filter fun r : Fin I.card => g r = d) = {r₀} := by
            ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            exact ⟨fun h => hinj (h.trans (congrArg Subtype.val hr₀).symm),
                   fun h => h ▸ congrArg Subtype.val hr₀⟩
          rw [hfilt, Finset.card_singleton]
        · rw [if_neg hd]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro r _ hgr; exact hd (hgr ▸ hmem r)
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact (h2 (hiff.mp h1)).elim
    · exact (h1 (hiff.mpr h2)).elim
    · rw [mul_zero]
  change _ = ∑ σ : Equiv.Perm (Fin I.card),
    ((Equiv.Perm.sign σ • ∏ r : Fin I.card,
      (Matrix.of fun r c => (Matrix.of fun i j => (MvPolynomial.X (i - j) : MvPolynomial (ZMod q) ℤ)) (eI r).1 (eJ c).1) (σ r) r)).coeff
      (subsetMonomial Y)
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  -- Now establish a sign-preserving bijection between:
  -- LHS: `{ h : Y ≃ I | (∀ d, (h d).1 - d.1 ∈ J) ∧ Bijective (d ↦ (h d).1 - d.1) }`
  -- RHS: `{ σ : Perm (Fin I.card) | (∀ r, (eI (σ r)).1 - (eJ r).1 ∈ Y) ∧ Injective (r ↦ (eI (σ r)).1 - (eJ r).1) }`
  -- Under `h ↦ σ := eJ.toEquiv.trans ((h - id)⁻¹.trans (h.trans eI.toEquiv.symm))` (so `eI (σ r) = h d` where `h d - d = eJ r`)!
  let LHS := (Finset.univ : Finset (Y ≃ I)).filter fun h =>
    ∃ hmem : ∀ d : Y, (h d).1 - d.1 ∈ J,
      Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : J))
  let RHS := (Finset.univ : Finset (Equiv.Perm (Fin I.card))).filter fun σ =>
    (∀ r : Fin I.card, (eI (σ r)).1 - (eJ r).1 ∈ Y) ∧
      Function.Injective (fun r : Fin I.card => (eI (σ r)).1 - (eJ r).1)
  have hL_eq :
      (∑ h : Y ≃ I,
        if hmem : ∀ d : Y, (h d).1 - d.1 ∈ J then
          if hbij : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : J)) then
            (orderedSign hYI h : ℤ) *
              (orderedSign hYJ (Equiv.ofBijective _ hbij) : ℤ)
          else 0
        else 0) =
      ∑ h ∈ LHS,
        if hmem : ∀ d : Y, (h d).1 - d.1 ∈ J then
          if hbij : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : J)) then
            (orderedSign hYI h : ℤ) *
              (orderedSign hYJ (Equiv.ofBijective _ hbij) : ℤ)
          else 0
        else 0 := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun h _ hnot => ?_
    simp only [LHS, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hnot
    split_ifs with hmem hbij
    · exact (hnot hmem hbij).elim
    · rfl
    · rfl
  rw [hL_eq]
  refine Finset.sum_bij
    (fun h hh =>
      let hmem := (Finset.mem_filter.mp hh).2.choose
      let hbij := (Finset.mem_filter.mp hh).2.choose_spec
      eJ.toEquiv.trans ((Equiv.ofBijective _ hbij).symm.trans (h.trans eI.toEquiv.symm)))
    ?_ ?_ ?_ ?_
  · intro h hh
    have hmem := (Finset.mem_filter.mp hh).2.choose
    have hbij := (Finset.mem_filter.mp hh).2.choose_spec
    let eD : Y ≃ J := Equiv.ofBijective _ hbij
    let σ : Equiv.Perm (Fin I.card) := eJ.toEquiv.trans (eD.symm.trans (h.trans eI.toEquiv.symm))
    have hg : ∀ r : Fin I.card, (eI (σ r)).1 - (eJ r).1 = (eD.symm (eJ r)).1 := fun r => by
      have h0 : eI (σ r) = h (eD.symm (eJ r)) := by
        dsimp only [σ]
        exact eI.toEquiv.apply_symm_apply (h (eD.symm (eJ r)))
      rw [h0]
      have h1 : (eD (eD.symm (eJ r))).1 = (eJ r).1 := congrArg Subtype.val (eD.apply_symm_apply (eJ r))
      have h2 : (eD (eD.symm (eJ r))).1 = (h (eD.symm (eJ r))).1 - (eD.symm (eJ r)).1 := rfl
      linear_combination h1 - h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r => ?_, fun r₁ r₂ hEq => ?_⟩
    · rw [hg r]; exact (eD.symm (eJ r)).2
    · change (eI (σ r₁)).1 - (eJ r₁).1 = (eI (σ r₂)).1 - (eJ r₂).1 at hEq
      rw [hg r₁, hg r₂] at hEq
      exact eJ.injective (eD.symm.injective (Subtype.ext hEq))
  · intro h₁ hh₁ h₂ hh₂ hEq
    have hmem₁ := (Finset.mem_filter.mp hh₁).2.choose
    have hbij₁ := (Finset.mem_filter.mp hh₁).2.choose_spec
    have hmem₂ := (Finset.mem_filter.mp hh₂).2.choose
    have hbij₂ := (Finset.mem_filter.mp hh₂).2.choose_spec
    let eD₁ : Y ≃ J := Equiv.ofBijective _ hbij₁
    let eD₂ : Y ≃ J := Equiv.ofBijective _ hbij₂
    have hD : eD₁.symm = eD₂.symm := by
      ext j
      obtain ⟨r, rfl⟩ := eJ.surjective j
      have h1 : (eI ((eJ.toEquiv.trans (eD₁.symm.trans (h₁.trans eI.toEquiv.symm))) r)).1 - (eJ r).1 =
          (eD₁.symm (eJ r)).1 := by
        have h0 : eI ((eJ.toEquiv.trans (eD₁.symm.trans (h₁.trans eI.toEquiv.symm))) r) = h₁ (eD₁.symm (eJ r)) :=
          eI.toEquiv.apply_symm_apply _
        rw [h0]
        have := congrArg Subtype.val (eD₁.apply_symm_apply (eJ r))
        have hdef : (eD₁ (eD₁.symm (eJ r))).1 = (h₁ (eD₁.symm (eJ r))).1 - (eD₁.symm (eJ r)).1 := rfl
        linear_combination this - hdef
      have h2 : (eI ((eJ.toEquiv.trans (eD₂.symm.trans (h₂.trans eI.toEquiv.symm))) r)).1 - (eJ r).1 =
          (eD₂.symm (eJ r)).1 := by
        have h0 : eI ((eJ.toEquiv.trans (eD₂.symm.trans (h₂.trans eI.toEquiv.symm))) r) = h₂ (eD₂.symm (eJ r)) :=
          eI.toEquiv.apply_symm_apply _
        rw [h0]
        have := congrArg Subtype.val (eD₂.apply_symm_apply (eJ r))
        have hdef : (eD₂ (eD₂.symm (eJ r))).1 = (h₂ (eD₂.symm (eJ r))).1 - (eD₂.symm (eJ r)).1 := rfl
        linear_combination this - hdef
      rw [hEq] at h1
      exact h1.symm.trans h2
    ext d
    obtain ⟨r, hr⟩ := eJ.surjective (eD₁ d)
    have hσ := congrArg (fun σ => eI (σ r)) hEq
    change eI (eI.symm (h₁ (eD₁.symm (eJ r)))) = eI (eI.symm (h₂ (eD₂.symm (eJ r)))) at hσ
    rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply, hr, Equiv.symm_apply_apply] at hσ
    have hd2 : eD₂.symm (eD₁ d) = d := by rw [← hD, Equiv.symm_apply_apply]
    rw [hd2] at hσ
    exact congrArg Subtype.val hσ
  · intro σ hσ
    rcases (Finset.mem_filter.mp hσ).2 with ⟨hmem, hinj⟩
    have hgbij : Function.Bijective (fun r : Fin I.card => (⟨(eI (σ r)).1 - (eJ r).1, hmem r⟩ : Y)) := by
      have hcard : Fintype.card (Fin I.card) = Fintype.card Y := by simp [Fintype.card_coe, hYI]
      exact (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun r₁ r₂ h => hinj (congrArg Subtype.val h), hcard⟩
    let eG : Fin I.card ≃ Y := Equiv.ofBijective _ hgbij
    let h : Y ≃ I := eG.symm.trans (σ.trans eI.toEquiv)
    have hmem_h : ∀ d : Y, (h d).1 - d.1 ∈ J := fun d => by
      have hg : (eI (σ (eG.symm d))).1 - (eJ (eG.symm d)).1 = d.1 :=
        congrArg Subtype.val (eG.apply_symm_apply d)
      have hsub : (h d).1 - d.1 = (eJ (eG.symm d)).1 := by
        dsimp [h]; linear_combination hg
      rw [hsub]; exact (eJ (eG.symm d)).2
    have hbij_h : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem_h d⟩ : J)) := by
      have heq : (fun d : Y => (⟨(h d).1 - d.1, hmem_h d⟩ : J)) = eG.symm.trans eJ.toEquiv := by
        funext d; apply Subtype.ext
        have hg : (eI (σ (eG.symm d))).1 - (eJ (eG.symm d)).1 = d.1 :=
          congrArg Subtype.val (eG.apply_symm_apply d)
        dsimp [h]; linear_combination hg
      rw [heq]; exact (eG.symm.trans eJ.toEquiv).bijective
    refine ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem_h, hbij_h⟩, ?_⟩
    ext r
    have h1 : (Equiv.ofBijective (fun d : Y => (⟨(h d).1 - d.1, hmem_h d⟩ : J)) hbij_h).symm (eJ r) = eG r := by
      apply (Equiv.ofBijective (fun d : Y => (⟨(h d).1 - d.1, hmem_h d⟩ : J)) hbij_h).injective
      rw [Equiv.apply_symm_apply]; apply Subtype.ext
      change (eJ r).1 = (eI (σ (eG.symm (eG r)))).1 - (eG r).1
      rw [Equiv.symm_apply_apply]; dsimp [eG]; ring
    have hstep : eI.toEquiv.symm (h ((Equiv.ofBijective (fun d : Y => (⟨(h d).1 - d.1, hmem_h d⟩ : J)) hbij_h).symm (eJ r))) = σ r := by
      rw [h1]; dsimp only [h, Equiv.trans_apply]; rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact congrArg Fin.val hstep
  · intro h hh
    have hmem := (Finset.mem_filter.mp hh).2.choose
    have hbij := (Finset.mem_filter.mp hh).2.choose_spec
    rw [dif_pos hmem, dif_pos hbij]
    let eD : Y ≃ J := Equiv.ofBijective _ hbij
    let p1 : Equiv.Perm (Fin Y.card) := eY.toEquiv.trans (h.trans (I.orderIsoOfFin hYI.symm).toEquiv.symm)
    let p2 : Equiv.Perm (Fin Y.card) := eY.toEquiv.trans (eD.trans (J.orderIsoOfFin hYJ.symm).toEquiv.symm)
    let σ : Equiv.Perm (Fin I.card) := eJ.toEquiv.trans (eD.symm.trans (h.trans eI.toEquiv.symm))
    have hconj : (finCongr hYI).permCongr (p1 * p2⁻¹) = σ := by
      ext r
      have hI_ord : ∀ k : Fin Y.card, I.orderIsoOfFin hYI.symm k = eI (finCongr hYI k) := by
        intro k
        have hcast : ∀ (n : ℕ) (hn : I.card = n) (x : Fin n),
            I.orderIsoOfFin hn x = I.orderIsoOfFin rfl (finCongr hn.symm x) := by
          rintro _ rfl _; rfl
        exact hcast Y.card hYI.symm k
      have hJ_ord : ∀ k : Fin Y.card, J.orderIsoOfFin hYJ.symm k = eJ (finCongr hYI k) := by
        intro k
        have hcast : ∀ (n : ℕ) (hn : J.card = n) (x : Fin n),
            J.orderIsoOfFin hn x = J.orderIsoOfFin hIJ.symm (finCongr (hn.symm.trans hIJ.symm) x) := by
          rintro _ rfl _; rfl
        simpa [eJ] using hcast Y.card hYJ.symm k
      apply congrArg Fin.val
      simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, p1, p2, σ,
        Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
      apply eI.injective
      change eI (finCongr hYI ((I.orderIsoOfFin hYI.symm).symm _)) = eI (eI.symm _)
      rw [← hI_ord, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
      congr 1; rw [eY.toEquiv.apply_symm_apply]; congr 1
    have hsign_eq : Equiv.Perm.sign σ = Equiv.Perm.sign p1 * Equiv.Perm.sign p2 := by
      rw [← hconj, Equiv.Perm.sign_permCongr, map_mul, map_inv]
      have hinv_eq : (Equiv.Perm.sign p2)⁻¹ = Equiv.Perm.sign p2 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign p2) with h2 | h2 <;> rw [h2] <;> decide
      rw [hinv_eq]
    unfold orderedSign
    change (Equiv.Perm.sign p1 : ℤ) * (Equiv.Perm.sign p2 : ℤ) = (Equiv.Perm.sign σ : ℤ)
    rw [hsign_eq]; push_cast; rfl

/-- Symmetry `ZY Y J I = ZY (-Y) I J` via `h ↦ (h - id) ∘ (-id)`. -/
lemma ZY_transpose_eq_neg {q : ℕ} [NeZero q] (Y I J : Finset (ZMod q)) :
    ZY Y J I = ZY (Y.image fun d => -d) I J := by
  classical
  have hcard_neg : (Y.image fun d => -d).card = Y.card :=
    Finset.card_image_of_injective Y neg_injective
  unfold ZY
  by_cases hYJ : Y.card = J.card
  · by_cases hYI : Y.card = I.card
    · rw [dif_pos hYJ, dif_pos hYI, dif_pos (hcard_neg.trans hYI), dif_pos (hcard_neg.trans hYJ)]
      let eNeg : (Y.image fun d => -d) ≃ Y :=
        { toFun := fun ⟨d, hd⟩ => ⟨-d, by
            rcases Finset.mem_image.mp hd with ⟨x, hx, hEq⟩
            have : -d = x := by linear_combination hEq
            rwa [this]⟩
          invFun := fun ⟨x, hx⟩ => ⟨-x, Finset.mem_image_of_mem _ hx⟩
          left_inv := fun ⟨d, _⟩ => Subtype.ext (neg_neg d)
          right_inv := fun ⟨x, _⟩ => Subtype.ext (neg_neg x) }
      -- Map each valid `h : Y ≃ J` to `h' := eNeg.trans (h - id) : (-Y) ≃ I`!
      let LHS := (Finset.univ : Finset (Y ≃ J)).filter fun h =>
        ∃ hmem : ∀ d : Y, (h d).1 - d.1 ∈ I,
          Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : I))
      let RHS := (Finset.univ : Finset ((Y.image fun d => -d) ≃ I)).filter fun h' =>
        ∃ hmem : ∀ d : (Y.image fun d => -d), (h' d).1 - d.1 ∈ J,
          Function.Bijective (fun d : (Y.image fun d => -d) => (⟨(h' d).1 - d.1, hmem d⟩ : J))
      have hL : (∑ h : Y ≃ J,
          if hmem : ∀ d : Y, (h d).1 - d.1 ∈ I then
            if hbij : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : I)) then
              (orderedSign hYJ h : ℤ) * (orderedSign hYI (Equiv.ofBijective _ hbij) : ℤ)
            else 0 else 0) =
          ∑ h ∈ LHS,
            if hmem : ∀ d : Y, (h d).1 - d.1 ∈ I then
              if hbij : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : I)) then
                (orderedSign hYJ h : ℤ) * (orderedSign hYI (Equiv.ofBijective _ hbij) : ℤ)
              else 0 else 0 := by
        symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun h _ hnot => ?_
        simp only [LHS, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hnot
        split_ifs with h1 h2
        · exact (hnot h1 h2).elim
        · rfl
        · rfl
      have hR : (∑ h' : (Y.image fun d => -d) ≃ I,
          if hmem : ∀ d, (h' d).1 - d.1 ∈ J then
            if hbij : Function.Bijective (fun d => (⟨(h' d).1 - d.1, hmem d⟩ : J)) then
              (orderedSign (hcard_neg.trans hYI) h' : ℤ) *
                (orderedSign (hcard_neg.trans hYJ) (Equiv.ofBijective _ hbij) : ℤ)
            else 0 else 0) =
          ∑ h' ∈ RHS,
            if hmem : ∀ d, (h' d).1 - d.1 ∈ J then
              if hbij : Function.Bijective (fun d => (⟨(h' d).1 - d.1, hmem d⟩ : J)) then
                (orderedSign (hcard_neg.trans hYI) h' : ℤ) *
                  (orderedSign (hcard_neg.trans hYJ) (Equiv.ofBijective _ hbij) : ℤ)
              else 0 else 0 := by
        symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun h' _ hnot => ?_
        simp only [RHS, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hnot
        split_ifs with h1 h2
        · exact (hnot h1 h2).elim
        · rfl
        · rfl
      rw [hL, hR]
      refine Finset.sum_bij
        (fun h hh => eNeg.trans (Equiv.ofBijective _ (Finset.mem_filter.mp hh).2.choose_spec))
        ?_ ?_ ?_ ?_
      · intro h hh
        have hmem := (Finset.mem_filter.mp hh).2.choose
        have hbij := (Finset.mem_filter.mp hh).2.choose_spec
        let h' : (Y.image fun d => -d) ≃ I := eNeg.trans (Equiv.ofBijective _ hbij)
        have hdiff : ∀ d : (Y.image fun d => -d), (h' d).1 - d.1 = (h (eNeg d)).1 := fun d => by
          change ((h (eNeg d)).1 - (-d.1)) - d.1 = (h (eNeg d)).1; ring
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun d => by rw [hdiff d]; exact (h (eNeg d)).2, ?_⟩
        have heq : (fun d : (Y.image fun d => -d) => (⟨(h' d).1 - d.1, by rw [hdiff d]; exact (h (eNeg d)).2⟩ : J)) =
            eNeg.trans h := funext fun d => Subtype.ext (hdiff d)
        rw [heq]; exact (eNeg.trans h).bijective
      · intro h₁ hh₁ h₂ hh₂ hEq
        ext d
        have h1 := congrArg (fun f => (f (eNeg.symm d)).1) hEq
        change (h₁ (eNeg (eNeg.symm d))).1 - (eNeg (eNeg.symm d)).1 =
          (h₂ (eNeg (eNeg.symm d))).1 - (eNeg (eNeg.symm d)).1 at h1
        rw [Equiv.apply_symm_apply] at h1
        linear_combination h1
      · intro h' hh'
        have hmem' := (Finset.mem_filter.mp hh').2.choose
        have hbij' := (Finset.mem_filter.mp hh').2.choose_spec
        let h : Y ≃ J := eNeg.symm.trans (Equiv.ofBijective _ hbij')
        have hdiff : ∀ d : Y, (h d).1 - d.1 = (h' (eNeg.symm d)).1 := fun d => by
          change ((h' (eNeg.symm d)).1 - (-d.1)) - d.1 = (h' (eNeg.symm d)).1; ring
        have hmem : ∀ d : Y, (h d).1 - d.1 ∈ I := fun d => by rw [hdiff d]; exact (h' (eNeg.symm d)).2
        have hbij : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : I)) := by
          have heq : (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : I)) = eNeg.symm.trans h' :=
            funext fun d => Subtype.ext (hdiff d)
          rw [heq]; exact (eNeg.symm.trans h').bijective
        refine ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem, hbij⟩, ?_⟩
        ext d; change (h (eNeg d)).1 - (eNeg d).1 = (h' d).1
        rw [hdiff (eNeg d), Equiv.symm_apply_apply]
      · intro h hh
        have hmem := (Finset.mem_filter.mp hh).2.choose
        have hbij := (Finset.mem_filter.mp hh).2.choose_spec
        let eD : Y ≃ I := Equiv.ofBijective _ hbij
        let h' : (Y.image fun d => -d) ≃ I := eNeg.trans eD
        have hdiff : ∀ d : (Y.image fun d => -d), (h' d).1 - d.1 = (h (eNeg d)).1 := fun d => by
          change ((h (eNeg d)).1 - (-d.1)) - d.1 = (h (eNeg d)).1; ring
        have hmem' : ∀ d, (h' d).1 - d.1 ∈ J := fun d => by rw [hdiff d]; exact (h (eNeg d)).2
        have hbij' : Function.Bijective (fun d => (⟨(h' d).1 - d.1, hmem' d⟩ : J)) := by
          have heq : (fun d => (⟨(h' d).1 - d.1, hmem' d⟩ : J)) = eNeg.trans h :=
            funext fun d => Subtype.ext (hdiff d)
          rw [heq]; exact (eNeg.trans h).bijective
        rw [dif_pos hmem, dif_pos hbij, dif_pos hmem', dif_pos hbij']
        have heq_eD' : Equiv.ofBijective (fun d => (⟨(h' d).1 - d.1, hmem' d⟩ : J)) hbij' = eNeg.trans h :=
          Equiv.ext fun d => Subtype.ext (hdiff d)
        rw [heq_eD']
        -- Both `orderedSign (eNeg.trans eD)` and `orderedSign (eNeg.trans h)` multiply by the SAME `orderedSign eNeg`!
        have hcomp : ∀ {B : Finset (ZMod q)} (hB : Y.card = B.card) (f : Y ≃ B),
            orderedSign (hcard_neg.trans hB) (eNeg.trans f) =
              orderedSign hcard_neg eNeg * orderedSign hB f := by
          intro B hB f
          unfold orderedSign
          let : LinearOrder (ZMod q) := zmodLinearOrder q
          have hcast_symm : ∀ {C : Finset (ZMod q)} {m n : ℕ} (hm : C.card = m) (hn : C.card = n) (x : C),
              (C.orderIsoOfFin hm).symm x = finCongr (hn.symm.trans hm) ((C.orderIsoOfFin hn).symm x) := by
            rintro C _ _ rfl rfl x; rfl
          let τ : Equiv.Perm (Fin (Y.image fun d => -d).card) :=
            ((Y.image fun d => -d).orderIsoOfFin rfl).toEquiv.trans
              (eNeg.trans (Y.orderIsoOfFin hcard_neg.symm).toEquiv.symm)
          let σ : Equiv.Perm (Fin Y.card) :=
            (Y.orderIsoOfFin rfl).toEquiv.trans (f.trans (B.orderIsoOfFin hB.symm).toEquiv.symm)
          have hmul :
              ((Y.image fun d => -d).orderIsoOfFin rfl).toEquiv.trans
                ((eNeg.trans f).trans (B.orderIsoOfFin (hcard_neg.trans hB).symm).toEquiv.symm) =
              ((finCongr hcard_neg).symm.permCongr σ) * τ := by
            ext k
            simp only [Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_symm,
              Equiv.trans_apply, τ, σ]
            have hY_c : ∀ x, (Y.orderIsoOfFin hcard_neg.symm).symm x =
                (finCongr hcard_neg).symm ((Y.orderIsoOfFin rfl).symm x) := fun x =>
              hcast_symm hcard_neg.symm rfl x
            have hB_c : ∀ x, (B.orderIsoOfFin (hcard_neg.trans hB).symm).symm x =
                (finCongr hcard_neg).symm ((B.orderIsoOfFin hB.symm).symm x) := fun x =>
              hcast_symm (hcard_neg.trans hB).symm hB.symm x
            change ((B.orderIsoOfFin (hcard_neg.trans hB).symm).symm (f (eNeg ((Y.image fun d => -d).orderIsoOfFin rfl k)))).val = _
            rw [hB_c]
            congr 1
            refine congrArg (fun x => (finCongr hcard_neg).symm ((B.orderIsoOfFin hB.symm).symm (f x))) ?_
            change eNeg _ = (Y.orderIsoOfFin rfl) (finCongr hcard_neg ((Y.orderIsoOfFin hcard_neg.symm).symm (eNeg _)))
            rw [hY_c, Equiv.apply_symm_apply, OrderIso.apply_symm_apply]; rfl
          dsimp only
          rw [hmul, map_mul, Equiv.Perm.sign_permCongr, mul_comm]
        rw [hcomp hYI eD, hcomp hYJ h]
        have hsq : (orderedSign hcard_neg eNeg : ℤ) * (orderedSign hcard_neg eNeg : ℤ) = 1 := by
          rcases Int.units_eq_one_or (orderedSign hcard_neg eNeg) with hu | hu <;> rw [hu] <;> decide
        push_cast
        calc (orderedSign hYJ h : ℤ) * (orderedSign hYI eD : ℤ)
            = ((orderedSign hcard_neg eNeg : ℤ) * (orderedSign hcard_neg eNeg : ℤ)) *
                ((orderedSign hYJ h : ℤ) * (orderedSign hYI eD : ℤ)) := by rw [hsq, one_mul]
          _ = _ := by ring
    · rw [dif_pos hYJ, dif_neg hYI, dif_neg (by omega)]
  · by_cases hYI : Y.card = I.card
    · rw [dif_neg hYJ, dif_pos (hcard_neg.trans hYI), dif_neg (by omega)]
    · rw [dif_neg hYJ, dif_neg (by omega)]

/-- General `OmegaSum` fiberwise expansion for any centered pattern `E` of size `k ≤ q`. -/
private lemma lem_6_11_Omega_gen {q k : ℕ} [NeZero q] (hq_odd : Odd q) (hk : k ≤ q)
    (E : Pattern q k) (hE : E.IsCentered) :
    OmegaSum E =
      ∑ I : CenteredIdx q k, ∑ J : CenteredIdx q k,
        ∑ I' : CenteredIdx q k, ∑ J' : CenteredIdx q k,
          ZY (E.O 0 0) I.1 J.1 *
          ((thetaSign I'.1 : ℤ) * (thetaSign J.1 : ℤ) * ZY (E.O 1 0) I'.1ᶜ J.1ᶜ) *
          ZY (E.O 1 1) I'.1 J'.1 *
          ((thetaSign I.1 : ℤ) * (thetaSign J'.1 : ℤ) * ZY (E.O 0 1) I.1ᶜ J'.1ᶜ) := by
    classical
    -- For any centered layer `L` on `E`, define its 4 centered index sets `(I, J, I', J')`
    have hL_inj : ∀ (L : Layer E) (a b : Fin 2), Function.Injective (L.h a b) := fun L a b x y h => by
      fin_cases b
      · exact Sum.inl.inj ((L.L1 a).1 h)
      · exact Sum.inr.inj ((L.L1 a).1 h)
    have hLd_inj : ∀ (L : Layer E) (a b : Fin 2), Function.Injective (fun d : E.O a b => L.h a b d - d.1) :=
      fun L a b x y h => by
        fin_cases a
        · exact Sum.inl.inj ((L.L2 b).1 h)
        · exact Sum.inr.inj ((L.L2 b).1 h)
    let imgI (L : Layer E) (a b : Fin 2) : Finset (ZMod q) := Finset.univ.image (L.h a b)
    let imgJ (L : Layer E) (a b : Fin 2) : Finset (ZMod q) := Finset.univ.image (fun d : E.O a b => L.h a b d - d.1)
    have hI_cent : ∀ (L : Layer E) (hL : L.IsCentered) (a b : Fin 2),
        (imgI L a b).card = (E.O a b).card ∧ ∑ z ∈ imgI L a b, z = 0 := fun L hL a b =>
      ⟨by dsimp [imgI]; rw [Finset.card_image_of_injective _ (hL_inj L a b), Finset.card_attach],
       by dsimp [imgI]; rw [Finset.sum_image (fun _ _ _ _ h => hL_inj L a b h)]; exact hL a b⟩
    have hJ_cent : ∀ (L : Layer E) (hL : L.IsCentered) (a b : Fin 2),
        (imgJ L a b).card = (E.O a b).card ∧ ∑ z ∈ imgJ L a b, z = 0 := fun L hL a b =>
      ⟨by dsimp [imgJ]; rw [Finset.card_image_of_injective _ (hLd_inj L a b), Finset.card_attach],
       by
         dsimp [imgJ]; rw [Finset.sum_image (fun _ _ _ _ h => hLd_inj L a b h), Finset.sum_sub_distrib]
         rw [show (∑ x ∈ (E.O a b).attach, L.h a b x) = 0 from hL a b,
           Finset.sum_attach (E.O a b) (fun d => d), hE a b, sub_self]⟩
    have hI01 : ∀ L : Layer E, imgI L 0 1 = (imgI L 0 0)ᶜ := fun L => by
      ext z; simp only [imgI, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · rintro ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inl_ne_inr ((L.L1 0).1 hy)
      · intro hz; rcases (L.L1 0).2 z with ⟨x | x, hx⟩
        · exact (hz ⟨x, hx⟩).elim
        · exact ⟨x, hx⟩
    have hI10 : ∀ L : Layer E, imgI L 1 0 = (imgI L 1 1)ᶜ := fun L => by
      ext z; simp only [imgI, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · rintro ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inr_ne_inl ((L.L1 1).1 hy)
      · intro hz; rcases (L.L1 1).2 z with ⟨x | x, hx⟩
        · exact ⟨x, hx⟩
        · exact (hz ⟨x, hx⟩).elim
    have hJ10 : ∀ L : Layer E, imgJ L 1 0 = (imgJ L 0 0)ᶜ := fun L => by
      ext z; simp only [imgJ, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · rintro ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inl_ne_inr ((L.L2 0).1 hy)
      · intro hz; rcases (L.L2 0).2 z with ⟨x | x, hx⟩
        · exact (hz ⟨x, hx⟩).elim
        · exact ⟨x, hx⟩
    have hJ01 : ∀ L : Layer E, imgJ L 0 1 = (imgJ L 1 1)ᶜ := fun L => by
      ext z; simp only [imgJ, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · rintro ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inr_ne_inl ((L.L2 1).1 hy)
      · intro hz; rcases (L.L2 1).2 z with ⟨x | x, hx⟩
        · exact ⟨x, hx⟩
        · exact (hz ⟨x, hx⟩).elim
    -- Fiber `OmegaSum E` over `(I, J, I', J') : CenteredIdx q k × ...`!
    let CentL := Finset.univ.filter (fun L : Layer E => L.IsCentered)
    let toIdx (L : Layer E) : CenteredIdx q k × CenteredIdx q k × CenteredIdx q k × CenteredIdx q k :=
      if hL : L.IsCentered then
        (⟨imgI L 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hI_cent L hL 0 0).1, E.card_00], (hI_cent L hL 0 0).2⟩⟩,
         ⟨imgJ L 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hJ_cent L hL 0 0).1, E.card_00], (hJ_cent L hL 0 0).2⟩⟩,
         ⟨imgI L 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hI_cent L hL 1 1).1, E.card_11], (hI_cent L hL 1 1).2⟩⟩,
         ⟨imgJ L 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hJ_cent L hL 1 1).1, E.card_11], (hJ_cent L hL 1 1).2⟩⟩)
      else
        (⟨E.O 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, E.card_00, hE 0 0⟩⟩,
         ⟨E.O 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, E.card_00, hE 0 0⟩⟩,
         ⟨E.O 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, E.card_11, hE 1 1⟩⟩,
         ⟨E.O 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, E.card_11, hE 1 1⟩⟩)
    unfold OmegaSum
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := (Finset.univ : Finset (CenteredIdx q k × CenteredIdx q k × CenteredIdx q k × CenteredIdx q k)))
      (g := toIdx) (fun _ _ => Finset.mem_univ _)]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
      Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun J' _ => ?_
    -- Compute the fiber over `(I, J, I', J')` as the product of the four `ZY` sums times `θ(I) θ(J) θ(I') θ(J')`!
    have hIc : I.1.card = k := (Finset.mem_filter.mp I.2).2.1
    have hJc : J.1.card = k := (Finset.mem_filter.mp J.2).2.1
    have hI'c : I'.1.card = k := (Finset.mem_filter.mp I'.2).2.1
    have hJ'c : J'.1.card = k := (Finset.mem_filter.mp J'.2).2.1
    have h00I : (E.O 0 0).card = I.1.card := by rw [E.card_00, hIc]
    have h00J : (E.O 0 0).card = J.1.card := by rw [E.card_00, hJc]
    have h10I : (E.O 1 0).card = I'.1ᶜ.card := by simp [E.card_10, Finset.card_compl, ZMod.card, hI'c]
    have h10J : (E.O 1 0).card = J.1ᶜ.card := by simp [E.card_10, Finset.card_compl, ZMod.card, hJc]
    have h11I : (E.O 1 1).card = I'.1.card := by rw [E.card_11, hI'c]
    have h11J : (E.O 1 1).card = J'.1.card := by rw [E.card_11, hJ'c]
    have h01I : (E.O 0 1).card = I.1ᶜ.card := by simp [E.card_01, Finset.card_compl, ZMod.card, hIc]
    have h01J : (E.O 0 1).card = J'.1ᶜ.card := by simp [E.card_01, Finset.card_compl, ZMod.card, hJ'c]
    -- Define the 4 valid-bijection subtypes for `(00, 10, 11, 01)`
    let Valid (A B C : Finset (ZMod q)) :=
      { f : A ≃ B // ∃ hmem : ∀ d : A, (f d).1 - d.1 ∈ C,
        Function.Bijective (fun d : A => (⟨(f d).1 - d.1, hmem d⟩ : C)) }
    let zTerm {A B C : Finset (ZMod q)} (hAB : A.card = B.card) (hAC : A.card = C.card)
        (f : Valid A B C) : ℤ :=
      (orderedSign hAB f.1 : ℤ) * (orderedSign hAC (Equiv.ofBijective _ f.2.choose_spec) : ℤ)
    have hZY_eq' : ∀ {A B C : Finset (ZMod q)} (hAB : A.card = B.card) (hAC : A.card = C.card),
        ZY A B C = ∑ f : Valid A B C, zTerm hAB hAC f := by
      intro A B C hAB hAC
      unfold ZY; rw [dif_pos hAB, dif_pos hAC]
      let S := (Finset.univ : Finset (A ≃ B)).filter fun f =>
        ∃ hmem : ∀ d : A, (f d).1 - d.1 ∈ C,
          Function.Bijective (fun d : A => (⟨(f d).1 - d.1, hmem d⟩ : C))
      have h1 : (∑ f : A ≃ B,
          if hmem : ∀ d : A, (f d).1 - d.1 ∈ C then
            if hbij : Function.Bijective (fun d : A => (⟨(f d).1 - d.1, hmem d⟩ : C)) then
              (orderedSign hAB f : ℤ) * (orderedSign hAC (Equiv.ofBijective _ hbij) : ℤ)
            else 0 else 0) =
          ∑ f ∈ S,
            if hmem : ∀ d : A, (f d).1 - d.1 ∈ C then
              if hbij : Function.Bijective (fun d : A => (⟨(f d).1 - d.1, hmem d⟩ : C)) then
                (orderedSign hAB f : ℤ) * (orderedSign hAC (Equiv.ofBijective _ hbij) : ℤ)
              else 0 else 0 := by
        symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun f _ hnot => ?_
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hnot
        split_ifs with h1 h2
        · exact (hnot h1 h2).elim
        · rfl
        · rfl
      rw [h1]
      refine Finset.sum_bij (fun f hf => ⟨f, (Finset.mem_filter.mp hf).2⟩)
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun f _ => ⟨f.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.2⟩, rfl⟩) ?_
      intro f hf
      have hmem := (Finset.mem_filter.mp hf).2.choose
      have hbij := (Finset.mem_filter.mp hf).2.choose_spec
      rw [dif_pos hmem, dif_pos hbij]
    rw [hZY_eq' h00I h00J, hZY_eq' h10I h10J, hZY_eq' h11I h11J, hZY_eq' h01I h01J]
    -- Bijection between `Valid 00 × Valid 10 × Valid 11 × Valid 01` and the fiber `CentL.filter (toIdx L = (I, J, I', J'))`!
    let Prod4 := Valid (E.O 0 0) I.1 J.1 × Valid (E.O 1 0) I'.1ᶜ J.1ᶜ ×
      Valid (E.O 1 1) I'.1 J'.1 × Valid (E.O 0 1) I.1ᶜ J'.1ᶜ
    let mkL (t : Prod4) : Layer E :=
      { h := fun a b d =>
          if ha : a = 0 then
            if hb : b = 0 then (t.1.1 ⟨d.1, by subst ha; subst hb; exact d.2⟩).1
            else (t.2.2.2.1 ⟨d.1, by have hb1 := fin2_eq_one_of_ne_zero hb; subst ha; subst hb1; exact d.2⟩).1
          else
            if hb : b = 0 then (t.2.1.1 ⟨d.1, by have ha1 := fin2_eq_one_of_ne_zero ha; subst ha1; subst hb; exact d.2⟩).1
            else (t.2.2.1.1 ⟨d.1, by
              have ha1 := fin2_eq_one_of_ne_zero ha
              have hb1 := fin2_eq_one_of_ne_zero hb
              subst ha1; subst hb1; exact d.2⟩).1
        L1 := fun a => by
          fin_cases a
          · refine pattern_row_bijective_of_inj hk E 0 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_zero, Fin.isValue, ↓reduceDIte, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.1.1.injective (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.1 d₂).2 (hEq ▸ (t.1.1 d₁).2)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.1 d₁).2 (hEq.symm ▸ (t.1.1 d₂).2)).elim
            · simp only [Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.2.1.injective (Subtype.ext hEq))
          · refine pattern_row_bijective_of_inj hk E 1 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.2.1.1.injective (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.1.1 d₁).2 (hEq.symm ▸ (t.2.2.1.1 d₂).2)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.1.1 d₂).2 (hEq ▸ (t.2.2.1.1 d₁).2)).elim
            · simp only [Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.1.1.injective (Subtype.ext hEq))
        L2 := fun b => by
          fin_cases b
          · refine pattern_col_bijective_of_inj hk E 0 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_zero, Fin.isValue, ↓reduceDIte, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.1.2.choose_spec.1 (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.1.2.choose d₂) (hEq ▸ t.1.2.choose d₁)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.1.2.choose d₁) (hEq.symm ▸ t.1.2.choose d₂)).elim
            · simp only [Sum.elim_inr, Fin.mk_zero, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.1.2.choose_spec.1 (Subtype.ext hEq))
          · refine pattern_col_bijective_of_inj hk E 1 _ ?_
            rintro (d₁ | d₁) (d₂ | d₂) hEq
            · simp only [Sum.elim_inl, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inl (t.2.2.2.2.choose_spec.1 (Subtype.ext hEq))
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.2.choose d₁) (hEq.symm ▸ t.2.2.1.2.choose d₂)).elim
            · simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact (Finset.mem_compl.mp (t.2.2.2.2.choose d₂) (hEq ▸ t.2.2.1.2.choose d₁)).elim
            · simp only [Sum.elim_inr, Fin.mk_one, Fin.isValue, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] at hEq
              exact congrArg Sum.inr (t.2.2.1.2.choose_spec.1 (Subtype.ext hEq)) }
    have hmkL_sign : ∀ t : Prod4,
        (layerSign (mkL t) : ℤ) =
          zTerm h00I h00J t.1 *
          ((thetaSign I'.1 : ℤ) * (thetaSign J.1 : ℤ) * zTerm h10I h10J t.2.1) *
          zTerm h11I h11J t.2.2.1 *
          ((thetaSign I.1 : ℤ) * (thetaSign J'.1 : ℤ) * zTerm h01I h01J t.2.2.2) := by
      intro t
      unfold layerSign
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      have hI'cc : (E.O 1 1).card = (I'.1ᶜᶜ : Finset (ZMod q)).card := by simpa using h11I
      have hJ'cc : (E.O 1 1).card = (J'.1ᶜᶜ : Finset (ZMod q)).card := by simpa using h11J
      let eI'cc : I'.1 ≃ (I'.1ᶜᶜ : Finset (ZMod q)) :=
        { toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
          invFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let eJ'cc : J'.1 ≃ (J'.1ᶜᶜ : Finset (ZMod q)) :=
        { toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
          invFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hord_cc : ∀ {A B B' : Finset (ZMod q)} (hBB' : B = B')
          (hAB : A.card = B.card) (hAB' : A.card = B'.card)
          (f : A ≃ B) (eB : B ≃ B') (he : ∀ x : B, (eB x).1 = x.1),
          orderedSign hAB' (f.trans eB) = orderedSign hAB f := by
        rintro A B _ rfl hAB _ f eB he
        have : eB = Equiv.refl B := Equiv.ext fun x => Subtype.ext (he x)
        subst this; rfl
      rw [sumBijectionSign_split (Equiv.ofBijective _ ((mkL t).L1 0)) h00I h01I t.1.1 t.2.2.2.1
            (fun _ => rfl) (fun _ => rfl),
          sumBijectionSign_split (Equiv.ofBijective _ ((mkL t).L1 1)) h10I hI'cc t.2.1.1
            (t.2.2.1.1.trans eI'cc) (fun _ => rfl) (fun _ => rfl),
          sumBijectionSign_split (Equiv.ofBijective _ ((mkL t).L2 0)) h00J h10J
            (Equiv.ofBijective _ t.1.2.choose_spec) (Equiv.ofBijective _ t.2.1.2.choose_spec)
            (fun _ => rfl) (fun _ => rfl),
          sumBijectionSign_split (Equiv.ofBijective _ ((mkL t).L2 1)) h01J hJ'cc
            (Equiv.ofBijective _ t.2.2.2.2.choose_spec)
            ((Equiv.ofBijective _ t.2.2.1.2.choose_spec).trans eJ'cc)
            (fun _ => rfl) (fun _ => rfl)]
      rw [hord_cc (compl_compl I'.1).symm h11I hI'cc t.2.2.1.1 eI'cc (fun _ => rfl),
        hord_cc (compl_compl J'.1).symm h11J hJ'cc (Equiv.ofBijective _ t.2.2.1.2.choose_spec) eJ'cc (fun _ => rfl),
        thetaSign_compl hq_odd I'.1, thetaSign_compl hq_odd J'.1]
      dsimp only [zTerm]; push_cast; ring
    have hbij_fib :
        (∑ L ∈ CentL.filter (fun L => toIdx L = (I, J, I', J')), (layerSign L : ℤ)) =
        ∑ t : Prod4, (layerSign (mkL t) : ℤ) := by
      symm
      refine Finset.sum_bij (fun t _ => mkL t) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro t _
        have hcent : (mkL t).IsCentered := by
          intro a b
          fin_cases a <;> fin_cases b
          · change ∑ d : E.O 0 0, (t.1.1 d).1 = 0
            rw [Equiv.sum_comp t.1.1 (fun x : I.1 => x.1), Finset.sum_coe_sort I.1 (fun z => z)]
            exact (Finset.mem_filter.mp I.2).2.2
          · change ∑ d : E.O 0 1, (t.2.2.2.1 d).1 = 0
            rw [Equiv.sum_comp t.2.2.2.1 (fun x : (I.1ᶜ : Finset (ZMod q)) => x.1),
              Finset.sum_coe_sort I.1ᶜ (fun z => z)]
            have htot := Finset.sum_add_sum_compl I.1 (fun z : ZMod q => z)
            rw [(Finset.mem_filter.mp I.2).2.2, zero_add, sum_univ_zmod_odd hq_odd] at htot; exact htot
          · change ∑ d : E.O 1 0, (t.2.1.1 d).1 = 0
            rw [Equiv.sum_comp t.2.1.1 (fun x : (I'.1ᶜ : Finset (ZMod q)) => x.1),
              Finset.sum_coe_sort I'.1ᶜ (fun z => z)]
            have htot := Finset.sum_add_sum_compl I'.1 (fun z : ZMod q => z)
            rw [(Finset.mem_filter.mp I'.2).2.2, zero_add, sum_univ_zmod_odd hq_odd] at htot; exact htot
          · change ∑ d : E.O 1 1, (t.2.2.1.1 d).1 = 0
            rw [Equiv.sum_comp t.2.2.1.1 (fun x : I'.1 => x.1), Finset.sum_coe_sort I'.1 (fun z => z)]
            exact (Finset.mem_filter.mp I'.2).2.2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcent⟩, ?_⟩
        dsimp only [toIdx]; rw [dif_pos hcent]
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
        · ext z; simp only [imgI, mkL, ↓reduceDIte, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun ⟨d, hd⟩ => hd ▸ (t.1.1 d).2, fun hz => ⟨t.1.1.symm ⟨z, hz⟩, by simp⟩⟩
        · ext z; simp only [imgJ, mkL, ↓reduceDIte, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun ⟨d, hd⟩ => hd ▸ t.1.2.choose d,
            fun hz => by rcases t.1.2.choose_spec.2 ⟨z, hz⟩ with ⟨d, hd⟩; exact ⟨d, congrArg Subtype.val hd⟩⟩
        · ext z; simp only [imgI, mkL, one_ne_zero, ↓reduceDIte, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun ⟨d, hd⟩ => hd ▸ (t.2.2.1.1 d).2, fun hz => ⟨t.2.2.1.1.symm ⟨z, hz⟩, by simp⟩⟩
        · ext z; simp only [imgJ, mkL, one_ne_zero, ↓reduceDIte, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun ⟨d, hd⟩ => hd ▸ t.2.2.1.2.choose d,
            fun hz => by rcases t.2.2.1.2.choose_spec.2 ⟨z, hz⟩ with ⟨d, hd⟩; exact ⟨d, congrArg Subtype.val hd⟩⟩
      · intro t₁ _ t₂ _ hEq
        refine Prod.ext (Subtype.ext (Equiv.ext fun d => Subtype.ext (by
            simpa [mkL] using congrFun (congrFun (congrFun (congrArg Layer.h hEq) 0) 0) d)))
          (Prod.ext (Subtype.ext (Equiv.ext fun d => Subtype.ext (by
            simpa [mkL] using congrFun (congrFun (congrFun (congrArg Layer.h hEq) 1) 0) d)))
            (Prod.ext (Subtype.ext (Equiv.ext fun d => Subtype.ext (by
              simpa [mkL] using congrFun (congrFun (congrFun (congrArg Layer.h hEq) 1) 1) d)))
              (Subtype.ext (Equiv.ext fun d => Subtype.ext (by
                simpa [mkL] using congrFun (congrFun (congrFun (congrArg Layer.h hEq) 0) 1) d)))))
      · intro L hL
        have hLc : L.IsCentered := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
        have hidx := (Finset.mem_filter.mp hL).2
        dsimp only [toIdx] at hidx; rw [dif_pos hLc] at hidx
        have hI00 : imgI L 0 0 = I.1 := congrArg (fun p => p.1.1) hidx
        have hJ00 : imgJ L 0 0 = J.1 := congrArg (fun p => p.2.1.1) hidx
        have hI11 : imgI L 1 1 = I'.1 := congrArg (fun p => p.2.2.1.1) hidx
        have hJ11 : imgJ L 1 1 = J'.1 := congrArg (fun p => p.2.2.2.1) hidx
        have hI01' : imgI L 0 1 = I.1ᶜ := (hI01 L).trans (congrArg _ hI00)
        have hI10' : imgI L 1 0 = I'.1ᶜ := (hI10 L).trans (congrArg _ hI11)
        have hJ10' : imgJ L 1 0 = J.1ᶜ := (hJ10 L).trans (congrArg _ hJ00)
        have hJ01' : imgJ L 0 1 = J'.1ᶜ := (hJ01 L).trans (congrArg _ hJ11)
        let mkV (a b : Fin 2) (B C : Finset (ZMod q)) (hB : imgI L a b = B) (hC : imgJ L a b = C) :
            Valid (E.O a b) B C :=
          let f : E.O a b ≃ B := Equiv.ofBijective (fun d => ⟨L.h a b d, by rw [← hB]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
            ⟨fun x y h => hL_inj L a b (congrArg Subtype.val h),
             fun ⟨z, hz⟩ => by rw [← hB] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩
          ⟨f, fun d => by rw [← hC]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _),
            ⟨fun x y h => hLd_inj L a b (congrArg Subtype.val h),
             fun ⟨z, hz⟩ => by rw [← hC] at hz; rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩; exact ⟨d, rfl⟩⟩⟩
        refine ⟨(mkV 0 0 I.1 J.1 hI00 hJ00, mkV 1 0 I'.1ᶜ J.1ᶜ hI10' hJ10',
                 mkV 1 1 I'.1 J'.1 hI11 hJ11, mkV 0 1 I.1ᶜ J'.1ᶜ hI01' hJ01'),
          Finset.mem_univ _, ?_⟩
        ext a b d
        fin_cases a <;> fin_cases b <;>
          simp only [mkL, mkV, Fin.mk_zero, Fin.mk_one, ↓reduceDIte, one_ne_zero, Subtype.coe_eta] <;>
          rfl
    rw [hbij_fib]
    simp_rw [hmkL_sign]
    dsimp only [Prod4]
    simp_rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- **Lemma 6.11** (`lem_6_11_traces`): Trace formulas and symmetry of `A_X, B_X, E, F, U`. -/
theorem lem_6_11_traces (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    (∀ Y I J : Finset (ZMod q), ∀ hIJ : I.card = J.card,
      Y.card = I.card →
      ZY Y I J = (circulantSubmatrix hIJ).det.coeff (subsetMonomial Y)) ∧
    (∀ (O : Pattern q m) (hO : O.IsCentered),
      let hq_odd : Odd q := hq.odd_of_ne_two hodd
      let X1 : CenteredIdx q m :=
        ⟨O.O 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.card_00, hO 0 0⟩⟩
      let X2 : CenteredIdx q m := complCentered hq_odd (le_of_lt hmq) (O.O 0 1) O.card_01 (hO 0 1)
      let X3 : CenteredIdx q m := complCentered hq_odd (le_of_lt hmq) (O.O 1 0) O.card_10 (hO 1 0)
      let X4 : CenteredIdx q m :=
        ⟨O.O 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.card_11, hO 1 1⟩⟩
      OmegaSum O =
        Matrix.trace (matA q m X1 * (matB q m X3)ᵀ * matA q m X4 * (matB q m X2)ᵀ) ∧
      OmegaSum (O.compl (le_of_lt hmq)) =
        Matrix.trace (matB q m X1 * (matA q m X3)ᵀ * matB q m X4 * (matA q m X2)ᵀ)) ∧
    (∀ X : CenteredIdx q m,
      (matA q m X)ᵀ = matA q m (negCentered X) ∧
      (matB q m X)ᵀ = matB q m (negCentered X)) ∧
    ((matE q m)ᵀ = matE q m ∧ (matF q m)ᵀ = matF q m ∧ (matU q m)ᵀ = matU q m) ∧
    ((∑ O ∈ centeredPatterns q m, OmegaSum (O.compl (le_of_lt hmq))) =
      Matrix.trace ((matE q m * matF q m) ^ 2) ∧
     mixedOrbitCountC q m = Matrix.trace ((matU q m * matS q m) ^ 4)) := by
  classical
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have hm : m ≤ q := le_of_lt hmq
  -- Part (a)
  have hpartA : ∀ Y I J : Finset (ZMod q), ∀ hIJ : I.card = J.card, Y.card = I.card →
      ZY Y I J = (circulantSubmatrix hIJ).det.coeff (subsetMonomial Y) :=
    fun Y I J hIJ hYI => ZY_eq_det_coeff Y I J hIJ hYI
  -- Part (b): deduce both `OmegaSum O` and `OmegaSum (O.compl hm)` from `lem_6_11_Omega_gen`!
  have hOmega_gen : ∀ (k : ℕ) (hk : k ≤ q) (E : Pattern q k) (hE : E.IsCentered),
      OmegaSum E =
        ∑ I : CenteredIdx q k, ∑ J : CenteredIdx q k,
          ∑ I' : CenteredIdx q k, ∑ J' : CenteredIdx q k,
            ZY (E.O 0 0) I.1 J.1 *
            ((thetaSign I'.1 : ℤ) * (thetaSign J.1 : ℤ) * ZY (E.O 1 0) I'.1ᶜ J.1ᶜ) *
            ZY (E.O 1 1) I'.1 J'.1 *
            ((thetaSign I.1 : ℤ) * (thetaSign J'.1 : ℤ) * ZY (E.O 0 1) I.1ᶜ J'.1ᶜ) :=
    fun _ hk E hE => lem_6_11_Omega_gen hq_odd hk E hE
  -- Part (b): deduce both `OmegaSum O` and `OmegaSum (O.compl hm)` from `hOmega_gen`!
  have hpartB :
      ∀ (O : Pattern q m) (hO : O.IsCentered),
        let X1 : CenteredIdx q m :=
          ⟨O.O 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.card_00, hO 0 0⟩⟩
        let X2 : CenteredIdx q m := complCentered hq_odd hm (O.O 0 1) O.card_01 (hO 0 1)
        let X3 : CenteredIdx q m := complCentered hq_odd hm (O.O 1 0) O.card_10 (hO 1 0)
        let X4 : CenteredIdx q m :=
          ⟨O.O 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.card_11, hO 1 1⟩⟩
        OmegaSum O =
          Matrix.trace (matA q m X1 * (matB q m X3)ᵀ * matA q m X4 * (matB q m X2)ᵀ) ∧
        OmegaSum (O.compl hm) =
          Matrix.trace (matB q m X1 * (matA q m X3)ᵀ * matB q m X4 * (matA q m X2)ᵀ) := by
    intro O hO X1 X2 X3 X4
    have hX2c : X2.1ᶜ = O.O 0 1 := compl_compl (O.O 0 1)
    have hX3c : X3.1ᶜ = O.O 1 0 := compl_compl (O.O 1 0)
    constructor
    · rw [hOmega_gen m hm O hO]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
        matA, matB, Matrix.of_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      have hcomm1 : ∀ (f : CenteredIdx q m → CenteredIdx q m → CenteredIdx q m → ℤ),
          (∑ J, ∑ I', ∑ J', f J I' J') = ∑ J', ∑ I', ∑ J, f J I' J' := fun f => by
        calc (∑ J, ∑ I', ∑ J', f J I' J')
            = ∑ J, ∑ J', ∑ I', f J I' J' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ J', ∑ J, ∑ I', f J I' J' := Finset.sum_comm
          _ = ∑ J', ∑ I', ∑ J, f J I' J' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      rw [hcomm1]
      refine Finset.sum_congr rfl fun J' _ => Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun J _ => ?_
      rw [hX2c, hX3c]
    · have hOc : (O.compl hm).IsCentered := fun a b => by
        have htot := Finset.sum_add_sum_compl (O.O a b) (fun d : ZMod q => d)
        rw [hO a b, zero_add, sum_univ_zmod_odd hq_odd] at htot; exact htot
      rw [hOmega_gen (q - m) (Nat.sub_le q m) (O.compl hm) hOc]
      -- Re-index `CenteredIdx q (q - m)` via complement `eC : CenteredIdx q m ≃ CenteredIdx q (q - m)`!
      let eC : CenteredIdx q m ≃ CenteredIdx q (q - m) :=
        { toFun := fun X => complCentered hq_odd (Nat.sub_le q m) X.1
            (by rw [Nat.sub_sub_self hm]; exact (Finset.mem_filter.mp X.2).2.1)
            (Finset.mem_filter.mp X.2).2.2
          invFun := fun Y => complCentered hq_odd hm Y.1
            (Finset.mem_filter.mp Y.2).2.1 (Finset.mem_filter.mp Y.2).2.2
          left_inv := fun X => Subtype.ext (compl_compl X.1)
          right_inv := fun Y => Subtype.ext (compl_compl Y.1) }
      rw [← Equiv.sum_comp eC]
      simp_rw [← Equiv.sum_comp eC]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
        matA, matB, Matrix.of_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      have hcomm1 : ∀ (f : CenteredIdx q m → CenteredIdx q m → CenteredIdx q m → ℤ),
          (∑ J, ∑ I', ∑ J', f J I' J') = ∑ J', ∑ I', ∑ J, f J I' J' := fun f => by
        calc (∑ J, ∑ I', ∑ J', f J I' J')
            = ∑ J, ∑ J', ∑ I', f J I' J' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ J', ∑ J, ∑ I', f J I' J' := Finset.sum_comm
          _ = ∑ J', ∑ I', ∑ J, f J I' J' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      rw [hcomm1]
      refine Finset.sum_congr rfl fun J' _ => Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun J _ => ?_
      have hcc : ∀ X : CenteredIdx q m, (eC X).1ᶜ = X.1 := fun X => compl_compl X.1
      have hth : ∀ X : CenteredIdx q m, thetaSign (eC X).1 = thetaSign X.1 := fun X =>
        thetaSign_compl hq_odd X.1
      simp only [hcc, hth]
      change ZY X1.1ᶜ I.1ᶜ J.1ᶜ *
          ((thetaSign I'.1 : ℤ) * (thetaSign J.1 : ℤ) * ZY X3.1 I'.1 J.1) *
          ZY X4.1ᶜ I'.1ᶜ J'.1ᶜ *
          ((thetaSign I.1 : ℤ) * (thetaSign J'.1 : ℤ) * ZY X2.1 I.1 J'.1) = _
      ring
  -- Part (c): Transpose of `matA` and `matB`
  have hpartC : ∀ X : CenteredIdx q m,
      (matA q m X)ᵀ = matA q m (negCentered X) ∧
      (matB q m X)ᵀ = matB q m (negCentered X) := by
    intro X
    constructor
    · ext I J
      simp only [Matrix.transpose_apply, matA, Matrix.of_apply, negCentered]
      exact ZY_transpose_eq_neg X.1 I.1 J.1
    · ext I J
      simp only [Matrix.transpose_apply, matB, Matrix.of_apply, negCentered]
      have hneg_compl : (X.1.image fun d => -d)ᶜ = X.1ᶜ.image fun d => -d := by
        ext z; simp only [Finset.mem_compl, Finset.mem_image]
        constructor
        · intro hz; refine ⟨-z, fun h => hz ⟨-z, h, neg_neg z⟩, neg_neg z⟩
        · rintro ⟨w, hw, rfl⟩ ⟨y, hy, hEq⟩
          exact hw (neg_injective hEq ▸ hy)
      rw [hneg_compl, ← ZY_transpose_eq_neg X.1ᶜ I.1ᶜ J.1ᶜ]
      ring
  -- Part (d): Symmetry of `E, F, U`
  have hpartD : (matE q m)ᵀ = matE q m ∧ (matF q m)ᵀ = matF q m ∧ (matU q m)ᵀ = matU q m := by
    let eNeg : CenteredIdx q m ≃ CenteredIdx q m :=
      { toFun := negCentered
        invFun := negCentered
        left_inv := fun X => Subtype.ext (by
          ext z; simp only [negCentered, Finset.mem_image]
          exact ⟨fun ⟨w, ⟨y, hy, hw⟩, h⟩ => by rw [← h, ← hw, neg_neg]; exact hy,
                 fun hz => ⟨-z, ⟨z, hz, rfl⟩, neg_neg z⟩⟩)
        right_inv := fun X => Subtype.ext (by
          ext z; simp only [negCentered, Finset.mem_image]
          exact ⟨fun ⟨w, ⟨y, hy, hw⟩, h⟩ => by rw [← h, ← hw, neg_neg]; exact hy,
                 fun hz => ⟨-z, ⟨z, hz, rfl⟩, neg_neg z⟩⟩) }
    refine ⟨?_, ?_, ?_⟩
    · unfold matE; rw [Matrix.transpose_sum]
      simp_rw [(hpartC _).1]; exact Equiv.sum_comp eNeg (matA q m)
    · unfold matF; rw [Matrix.transpose_sum]
      simp_rw [(hpartC _).2]; exact Equiv.sum_comp eNeg (matB q m)
    · unfold matU; rw [Matrix.transpose_sum]
      have hk : ∀ X : CenteredIdx q m,
          (kronMat (matA q m X) (matB q m X))ᵀ = kronMat (matA q m (negCentered X)) (matB q m (negCentered X)) := by
        intro X; ext ⟨I₁, I₂⟩ ⟨J₁, J₂⟩
        simp only [Matrix.transpose_apply, kronMat, Matrix.of_apply]
        rw [← Matrix.transpose_apply (matA q m X), ← Matrix.transpose_apply (matB q m X),
          (hpartC X).1, (hpartC X).2]
      simp_rw [hk]
      exact Equiv.sum_comp eNeg (fun X => kronMat (matA q m X) (matB q m X))
  -- Part (e): `∑_O Ω(O^c) = tr((E F)^2)` and `N_{C,m} = tr((U S)^4)`
  have hpartE :
      (∑ O ∈ centeredPatterns q m, OmegaSum (O.compl hm)) =
        Matrix.trace ((matE q m * matF q m) ^ 2) ∧
      mixedOrbitCountC q m = Matrix.trace ((matU q m * matS q m) ^ 4) := by
    -- Bijection `centeredPatterns q m ≃ CenteredIdx q m ^ 4`
    let mkPat (t : CenteredIdx q m × CenteredIdx q m × CenteredIdx q m × CenteredIdx q m) : Pattern q m :=
      { O := fun a b =>
          if a = 0 ∧ b = 0 then t.1.1
          else if a = 0 ∧ b = 1 then t.2.1.1ᶜ
          else if a = 1 ∧ b = 0 then t.2.2.1.1ᶜ
          else t.2.2.2.1
        card_00 := (Finset.mem_filter.mp t.1.2).2.1
        card_11 := (Finset.mem_filter.mp t.2.2.2.2).2.1
        card_01 := by simp [Finset.card_compl, ZMod.card, (Finset.mem_filter.mp t.2.1.2).2.1]
        card_10 := by simp [Finset.card_compl, ZMod.card, (Finset.mem_filter.mp t.2.2.1.2).2.1] }
    have hmkPat_cent : ∀ t, (mkPat t).IsCentered := fun t a b => by
      fin_cases a <;> fin_cases b
      · exact (Finset.mem_filter.mp t.1.2).2.2
      · have htot := Finset.sum_add_sum_compl t.2.1.1 (fun d : ZMod q => d)
        rw [(Finset.mem_filter.mp t.2.1.2).2.2, zero_add, sum_univ_zmod_odd hq_odd] at htot
        simpa [mkPat] using htot
      · have htot := Finset.sum_add_sum_compl t.2.2.1.1 (fun d : ZMod q => d)
        rw [(Finset.mem_filter.mp t.2.2.1.2).2.2, zero_add, sum_univ_zmod_odd hq_odd] at htot
        simpa [mkPat] using htot
      · exact (Finset.mem_filter.mp t.2.2.2.2).2.2
    have hsum_pat : ∀ f : Pattern q m → ℤ,
        (∑ O ∈ centeredPatterns q m, f O) =
        ∑ X1 : CenteredIdx q m, ∑ X2 : CenteredIdx q m,
          ∑ X3 : CenteredIdx q m, ∑ X4 : CenteredIdx q m, f (mkPat (X1, X2, X3, X4)) := by
      intro f
      rw [show (∑ X1 : CenteredIdx q m, ∑ X2 : CenteredIdx q m,
            ∑ X3 : CenteredIdx q m, ∑ X4 : CenteredIdx q m, f (mkPat (X1, X2, X3, X4))) =
          ∑ t : CenteredIdx q m × CenteredIdx q m × CenteredIdx q m × CenteredIdx q m, f (mkPat t) by
        simp only [Fintype.sum_prod_type]]
      symm
      refine Finset.sum_bij (fun t _ => mkPat t)
        (fun t _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmkPat_cent t⟩) ?_ ?_ (fun _ _ => rfl)
      · rintro ⟨a1, a2, a3, a4⟩ _ ⟨b1, b2, b3, b4⟩ _ hEq
        have h00 : a1.1 = b1.1 := by simpa [mkPat] using congrFun (congrFun (congrArg Pattern.O hEq) 0) 0
        have h01 : a2.1ᶜ = b2.1ᶜ := by simpa [mkPat] using congrFun (congrFun (congrArg Pattern.O hEq) 0) 1
        have h10 : a3.1ᶜ = b3.1ᶜ := by simpa [mkPat] using congrFun (congrFun (congrArg Pattern.O hEq) 1) 0
        have h11 : a4.1 = b4.1 := by simpa [mkPat] using congrFun (congrFun (congrArg Pattern.O hEq) 1) 1
        exact Prod.ext (Subtype.ext h00) (Prod.ext (Subtype.ext (compl_injective h01))
          (Prod.ext (Subtype.ext (compl_injective h10)) (Subtype.ext h11)))
      · intro O hO
        have hOc := (Finset.mem_filter.mp hO).2
        refine ⟨(⟨O.O 0 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.card_00, hOc 0 0⟩⟩,
                 complCentered hq_odd hm (O.O 0 1) O.card_01 (hOc 0 1),
                 complCentered hq_odd hm (O.O 1 0) O.card_10 (hOc 1 0),
                 ⟨O.O 1 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.card_11, hOc 1 1⟩⟩),
          Finset.mem_univ _, ?_⟩
        ext a b d; fin_cases a <;> fin_cases b <;> simp [mkPat, complCentered]
    constructor
    · rw [hsum_pat]
      have hterm : ∀ X1 X2 X3 X4 : CenteredIdx q m,
          OmegaSum ((mkPat (X1, X2, X3, X4)).compl hm) =
            Matrix.trace (matB q m X1 * (matA q m X3)ᵀ * matB q m X4 * (matA q m X2)ᵀ) := by
        intro X1 X2 X3 X4
        have h := (hpartB (mkPat (X1, X2, X3, X4)) (hmkPat_cent (X1, X2, X3, X4))).2
        have h1 : (⟨(mkPat (X1, X2, X3, X4)).O 0 0,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mkPat (X1, X2, X3, X4)).card_00,
              hmkPat_cent (X1, X2, X3, X4) 0 0⟩⟩ : CenteredIdx q m) = X1 := Subtype.ext rfl
        have h2 : complCentered hq_odd hm ((mkPat (X1, X2, X3, X4)).O 0 1)
            (mkPat (X1, X2, X3, X4)).card_01 (hmkPat_cent (X1, X2, X3, X4) 0 1) = X2 :=
          Subtype.ext (compl_compl X2.1)
        have h3 : complCentered hq_odd hm ((mkPat (X1, X2, X3, X4)).O 1 0)
            (mkPat (X1, X2, X3, X4)).card_10 (hmkPat_cent (X1, X2, X3, X4) 1 0) = X3 :=
          Subtype.ext (compl_compl X3.1)
        have h4 : (⟨(mkPat (X1, X2, X3, X4)).O 1 1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mkPat (X1, X2, X3, X4)).card_11,
              hmkPat_cent (X1, X2, X3, X4) 1 1⟩⟩ : CenteredIdx q m) = X4 := Subtype.ext rfl
        simpa [h1, h2, h3, h4] using h
      have htr_sum : ∀ {ι α : Type} [Fintype ι] [Fintype α] (M : ι → Matrix α α ℤ),
          (∑ i : ι, Matrix.trace (M i)) = Matrix.trace (∑ i : ι, M i) := fun M => by
        simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]; rw [Finset.sum_comm]
      simp_rw [hterm]
      simp_rw [htr_sum]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      have hEA : (∑ X : CenteredIdx q m, (matA q m X)ᵀ) = matE q m := by
        rw [← Matrix.transpose_sum]; exact hpartD.1
      have hFB : (∑ X : CenteredIdx q m, matB q m X) = matF q m := rfl
      rw [hEA, hFB, sq]
      calc Matrix.trace (matF q m * matE q m * matF q m * matE q m)
          = Matrix.trace ((matF q m * matE q m * matF q m) * matE q m) := rfl
        _ = Matrix.trace (matE q m * (matF q m * matE q m * matF q m)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (matE q m * matF q m * (matE q m * matF q m)) := by simp [Matrix.mul_assoc]
    · rw [(lem_6_10_layers q m hq hodd hm0 hmq).2, hsum_pat]
      have hterm : ∀ X1 X2 X3 X4 : CenteredIdx q m,
          OmegaSum (mkPat (X1, X2, X3, X4)) * OmegaSum ((mkPat (X1, X2, X3, X4)).compl hm) =
            Matrix.trace (
              kronMat (matA q m X1) (matB q m X1) *
              kronMat (matB q m X3)ᵀ (matA q m X3)ᵀ *
              kronMat (matA q m X4) (matB q m X4) *
              kronMat (matB q m X2)ᵀ (matA q m X2)ᵀ) := by
        intro X1 X2 X3 X4
        have h := hpartB (mkPat (X1, X2, X3, X4)) (hmkPat_cent (X1, X2, X3, X4))
        have h1 : (⟨(mkPat (X1, X2, X3, X4)).O 0 0,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mkPat (X1, X2, X3, X4)).card_00,
              hmkPat_cent (X1, X2, X3, X4) 0 0⟩⟩ : CenteredIdx q m) = X1 := Subtype.ext rfl
        have h2 : complCentered hq_odd hm ((mkPat (X1, X2, X3, X4)).O 0 1)
            (mkPat (X1, X2, X3, X4)).card_01 (hmkPat_cent (X1, X2, X3, X4) 0 1) = X2 :=
          Subtype.ext (compl_compl X2.1)
        have h3 : complCentered hq_odd hm ((mkPat (X1, X2, X3, X4)).O 1 0)
            (mkPat (X1, X2, X3, X4)).card_10 (hmkPat_cent (X1, X2, X3, X4) 1 0) = X3 :=
          Subtype.ext (compl_compl X3.1)
        have h4 : (⟨(mkPat (X1, X2, X3, X4)).O 1 1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mkPat (X1, X2, X3, X4)).card_11,
              hmkPat_cent (X1, X2, X3, X4) 1 1⟩⟩ : CenteredIdx q m) = X4 := Subtype.ext rfl
        rw [h.1, h.2]
        simp only [h1, h2, h3, h4]
        have hk_mul : ∀ (A₁ A₂ B₁ B₂ : Matrix (CenteredIdx q m) (CenteredIdx q m) ℤ),
            kronMat A₁ B₁ * kronMat A₂ B₂ = kronMat (A₁ * A₂) (B₁ * B₂) := by
          intro A₁ A₂ B₁ B₂; ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
          simp only [Matrix.mul_apply, kronMat, Matrix.of_apply, Fintype.sum_prod_type,
            Finset.sum_mul, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
        have hk_tr : ∀ (A B : Matrix (CenteredIdx q m) (CenteredIdx q m) ℤ),
            Matrix.trace (kronMat A B) = Matrix.trace A * Matrix.trace B := by
          intro A B
          simp only [Matrix.trace, Matrix.diag, kronMat, Matrix.of_apply, Fintype.sum_prod_type,
            Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
        rw [hk_mul, hk_mul, hk_mul, hk_tr]
      have htr_sum : ∀ {ι α : Type} [Fintype ι] [Fintype α] (M : ι → Matrix α α ℤ),
          (∑ i : ι, Matrix.trace (M i)) = Matrix.trace (∑ i : ι, M i) := fun M => by
        simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]; rw [Finset.sum_comm]
      simp_rw [hterm]
      simp_rw [htr_sum]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      have hU_eq : (∑ X : CenteredIdx q m, kronMat (matA q m X) (matB q m X)) = matU q m := rfl
      have hS_l : ∀ (M : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) ℤ)
          (p r : CenteredIdx q m × CenteredIdx q m),
          (matS q m * M) p r = M (p.2, p.1) r := by
        intro M ⟨a, b⟩ r
        simp only [Matrix.mul_apply, matS, Matrix.of_apply, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single b]
        · rw [Finset.sum_eq_single a]
          · simp
          · intro y _ hy; simp [Ne.symm hy]
          · intro h; exact (h (Finset.mem_univ _)).elim
        · intro x _ hx
          exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hx]
        · intro h; exact (h (Finset.mem_univ _)).elim
      have hS_r : ∀ (M : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) ℤ)
          (p r : CenteredIdx q m × CenteredIdx q m),
          (M * matS q m) p r = M p (r.2, r.1) := by
        intro M p ⟨a, b⟩
        simp only [Matrix.mul_apply, matS, Matrix.of_apply, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single b]
        · rw [Finset.sum_eq_single a]
          · simp
          · intro y _ hy; simp [hy]
          · intro h; exact (h (Finset.mem_univ _)).elim
        · intro x _ hx
          exact Finset.sum_eq_zero fun y _ => by simp [hx]
        · intro h; exact (h (Finset.mem_univ _)).elim
      have hSUS : (∑ X : CenteredIdx q m, kronMat (matB q m X)ᵀ (matA q m X)ᵀ) =
          matS q m * matU q m * matS q m := by
        rw [← hpartD.2.2]
        have h1 : ∀ X : CenteredIdx q m,
            kronMat (matB q m X)ᵀ (matA q m X)ᵀ =
              matS q m * (kronMat (matA q m X) (matB q m X))ᵀ * matS q m := by
          intro X; ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
          rw [hS_r, hS_l]
          simp only [Matrix.transpose_apply, kronMat, Matrix.of_apply]; ring
        simp_rw [h1]; rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.transpose_sum]; rfl
      rw [hU_eq, hSUS]
      have hEq4 :
          matU q m * (matS q m * matU q m * matS q m) * matU q m * (matS q m * matU q m * matS q m) =
          (matU q m * matS q m) ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
      rw [hEq4]
  exact ⟨hpartA, hpartB, hpartC, hpartD, hpartE⟩

end Lemma611Traces

section Prop612Eval

/-! ### Proposition 6.12: Nilpotence, Compound Matrices, Jacobi's Identity, and Evaluation mod `q` -/

/-- Any nilpotent square matrix over a field has trace `0` (in ANY characteristic!). -/
private lemma trace_eq_zero_of_nilpotent_fin {F : Type*} [Field F] :
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F) {N : ℕ}, A ^ N = 0 → Matrix.trace A = 0 := by
  intro n
  induction n with
  | zero => intro A _ _; simp [Matrix.trace]
  | succ n ih =>
    intro A N hAN
    by_cases hA0 : A = 0
    · rw [hA0, Matrix.trace_zero]
    -- Find `m` such that `A ^ m ≠ 0` and `A ^ (m + 1) = 0`
    have hex : ∃ m : ℕ, A ^ m ≠ 0 ∧ A ^ (m + 1) = 0 := by
      have h0 : A ^ 0 ≠ 0 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrFun (congrFun h (0 : Fin (n + 1))) (0 : Fin (n + 1)))
      suffices h : ∀ k : ℕ, A ^ k = 0 → ∃ m < k, A ^ m ≠ 0 ∧ A ^ (m + 1) = 0 by
        rcases h N hAN with ⟨m, _, hm⟩; exact ⟨m, hm⟩
      intro k
      induction k with
      | zero => intro hk; exact (h0 hk).elim
      | succ k ihk =>
        intro hk1
        by_cases hk : A ^ k = 0
        · rcases ihk hk with ⟨m, hmk, hm⟩; exact ⟨m, Nat.lt_succ_of_lt hmk, hm⟩
        · exact ⟨k, Nat.lt_succ_self k, hk, hk1⟩
    rcases hex with ⟨m, hm_ne, hm1⟩
    -- Pick a nonzero entry `(i₀, j₀)` of `A ^ m`, let `v = col j₀ (A ^ m)`; then `A *ᵥ v = 0` and `v i₀ ≠ 0`!
    have hex_ij : ∃ i₀ j₀ : Fin (n + 1), (A ^ m) i₀ j₀ ≠ 0 := by
      by_contra hall; push Not at hall; apply hm_ne; ext i j; exact hall i j
    rcases hex_ij with ⟨i₀, j₀, hv0⟩
    let v : Fin (n + 1) → F := fun i => (A ^ m) i j₀
    have hAv : ∀ i : Fin (n + 1), ∑ k : Fin (n + 1), A i k * v k = 0 := fun i => by
      have h := congrFun (congrFun hm1 i) j₀
      rw [pow_succ', Matrix.mul_apply] at h; exact h
    -- Build explicit invertible `P, Q : Matrix (Fin (n + 1)) (Fin (n + 1)) F` with `Q * P = 1` and col 0 of `P` equal to `v`!
    let eRest : Fin n ≃ { i : Fin (n + 1) // i ≠ i₀ } :=
      (Fintype.equivFinOfCardEq (by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]; omega)).symm
    let P : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      if hj : j = 0 then v i
      else if i = (eRest ⟨j.val - 1, by have : j.val ≠ 0 := fun h => hj (Fin.ext h); omega⟩).1 then 1 else 0
    let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      if hi : i = 0 then if j = i₀ then (v i₀)⁻¹ else 0
      else
        let r := (eRest ⟨i.val - 1, by have : i.val ≠ 0 := fun h => hi (Fin.ext h); omega⟩).1
        (if j = r then 1 else 0) - (if j = i₀ then v r * (v i₀)⁻¹ else 0)
    have hQP : Q * P = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply]
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      · subst hi hj
        simp only [Q, P, Matrix.of_apply, ↓reduceDIte, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
        exact inv_mul_cancel₀ hv0
      · subst hi
        have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
        have hrj : i₀ ≠ (eRest ⟨j.val - 1, by omega⟩).1 := (eRest ⟨j.val - 1, by omega⟩).2.symm
        simp only [Q, P, Matrix.of_apply, ↓reduceDIte, hj, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte, hrj, mul_zero, Ne.symm hj]
      · subst hj
        have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp only [Q, P, Matrix.of_apply, hi, ↓reduceDIte, sub_mul, ite_mul, one_mul, zero_mul,
          Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [mul_assoc, inv_mul_cancel₀ hv0, mul_one, sub_self]
      · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
        let ki : Fin n := ⟨i.val - 1, by omega⟩
        let kj : Fin n := ⟨j.val - 1, by omega⟩
        have hne_i0 : (eRest kj).1 ≠ i₀ := (eRest kj).2
        simp only [Q, P, Matrix.of_apply, hi, hj, ↓reduceDIte, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        change (if (eRest kj).1 = (eRest ki).1 then (1 : F) else 0) -
          (if (eRest kj).1 = i₀ then v (eRest ki).1 * (v i₀)⁻¹ else 0) = if i = j then 1 else 0
        rw [if_neg hne_i0, sub_zero]
        by_cases hij : i = j
        · subst hij; simp [ki, kj]
        · have hne : (eRest kj).1 ≠ (eRest ki).1 := fun h => hij (by
            have := eRest.injective (Subtype.ext h)
            have := congrArg Fin.val this; exact Fin.ext (by dsimp [ki, kj] at this; omega))
          simp [hij, hne]
    have hPQ : P * Q = 1 := by
      have hdet : P.det ≠ 0 := fun h0 => by
        have := congrArg Matrix.det hQP
        rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
        exact one_ne_zero this.symm
      have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hdet)
      have hQeq : Q = P⁻¹ := by
        calc Q = Q * (P * P⁻¹) := by rw [hPinv, Matrix.mul_one]
          _ = (Q * P) * P⁻¹ := by rw [Matrix.mul_assoc]
          _ = P⁻¹ := by rw [hQP, Matrix.one_mul]
      rw [hQeq, hPinv]
    let B := Q * A * P
    have hB_col0 : ∀ i : Fin (n + 1), B i 0 = 0 := fun i => by
      dsimp only [B]
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hAP : (A * P) k 0 = 0 := by
        rw [Matrix.mul_apply]; simpa [P] using hAv k
      rw [hAP, mul_zero]
    let B' : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => B i.succ j.succ
    have hB_pow : ∀ r : ℕ, ∀ i j : Fin n, (B ^ r) i.succ j.succ = (B' ^ r) i j := fun r => by
      induction r with
      | zero => intro i j; simp [Matrix.one_apply]
      | succ r ihr =>
        intro i j
        rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ]
        have h0 : B 0 j.succ = B 0 j.succ := rfl
        have hcol0 : (B ^ r) i.succ 0 = 0 := by
          cases r with
          | zero => simp [Matrix.one_apply]
          | succ r' =>
            rw [pow_succ, Matrix.mul_apply]
            exact Finset.sum_eq_zero fun k _ => by rw [hB_col0 k, mul_zero]
        rw [hcol0, zero_mul, zero_add]
        exact Finset.sum_congr rfl fun k _ => by rw [ihr i k]; rfl
    have hBN : B ^ N = 0 := by
      have hconj : ∀ r : ℕ, B ^ r = Q * A ^ r * P := fun r => by
        induction r with
        | zero => simp [hQP]
        | succ r ihr =>
          rw [pow_succ, pow_succ, ihr]
          calc Q * A ^ r * P * (Q * A * P)
              = Q * A ^ r * (P * Q) * A * P := by simp only [Matrix.mul_assoc]
            _ = Q * (A ^ r * A) * P := by rw [hPQ]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      rw [hconj, hAN, Matrix.mul_zero, Matrix.zero_mul]
    have hB'N : B' ^ N = 0 := by
      ext i j; rw [← hB_pow N i j, hBN]; rfl
    have htrB' : Matrix.trace B' = 0 := ih B' hB'N
    have htrA : Matrix.trace A = Matrix.trace B := by
      dsimp only [B]
      rw [Matrix.trace_mul_comm (Q * A) P, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    rw [htrA]
    unfold Matrix.trace Matrix.diag
    rw [Fin.sum_univ_succ, hB_col0 0, zero_add]
    exact htrB'

private lemma trace_eq_zero_of_nilpotent {α F : Type*} [Fintype α] [DecidableEq α] [Field F]
    (A : Matrix α α F) {N : ℕ} (hAN : A ^ N = 0) : Matrix.trace A = 0 := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let B : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) F := A.submatrix e.symm e.symm
  have hB_pow : ∀ r : ℕ, B ^ r = (A ^ r).submatrix e.symm e.symm := fun r => by
    induction r with
    | zero => ext i j; simp [Matrix.one_apply]
    | succ r ih =>
      rw [pow_succ, pow_succ, ih]; ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, B]
      exact Equiv.sum_comp e.symm (fun k => (A ^ r) (e.symm i) k * A k (e.symm j))
  have hBN : B ^ N = 0 := by rw [hB_pow, hAN]; ext i j; rfl
  have htr : Matrix.trace A = Matrix.trace B := by
    unfold Matrix.trace Matrix.diag
    exact (Equiv.sum_comp e.symm fun a => A a a).symm
  rw [htr]
  exact trace_eq_zero_of_nilpotent_fin B hBN

/-- Index type of `m`-subsets of `ZMod q`. -/
private abbrev SubIdx (q m : ℕ) [NeZero q] := { I : Finset (ZMod q) // I.card = m }

/-- Weight `∑ x ∈ I, x.val` of an `m`-subset `I ⊆ ZMod q` (strictly grades upper-triangular compounds!). -/
private def subWeight {q m : ℕ} [NeZero q] (I : SubIdx q m) : ℕ :=
  ∑ x ∈ I.1, x.val

/-- The `m`-th compound matrix of a `q × q` matrix `M` over any commutative ring `R`. -/
private noncomputable def compound {q : ℕ} [NeZero q] (m : ℕ) {R : Type*} [CommRing R]
    (M : Matrix (ZMod q) (ZMod q) R) : Matrix (SubIdx q m) (SubIdx q m) R := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  exact Matrix.of fun I J =>
    (M.submatrix (fun r : Fin m => (I.1.orderIsoOfFin I.2 r).1)
      (fun c : Fin m => (J.1.orderIsoOfFin J.2 c).1)).det

/-- Cauchy–Binet formula: `compound m (M * N) = compound m M * compound m N`. -/
private lemma compound_mul {q m : ℕ} [NeZero q] {R : Type*} [CommRing R]
    (M N : Matrix (ZMod q) (ZMod q) R) :
    compound m (M * N) = compound m M * compound m N := by
  classical
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  ext I J
  simp only [compound, Matrix.mul_apply, Matrix.of_apply]
  let eI : Fin m → ZMod q := fun r => (I.1.orderIsoOfFin I.2 r).1
  let eJ : Fin m → ZMod q := fun c => (J.1.orderIsoOfFin J.2 c).1
  rw [Matrix.det_apply]
  simp only [Matrix.submatrix_apply]
  have hprod : ∀ σ : Equiv.Perm (Fin m),
      (∏ r : Fin m, (M * N) (eI (σ r)) (eJ r)) =
      ∑ f : Fin m → ZMod q, ∏ r : Fin m, (M (eI (σ r)) (f r) * N (f r) (eJ r)) := fun σ => by
    simp only [Matrix.mul_apply]
    exact Fintype.prod_sum (fun r k => M (eI (σ r)) k * N k (eJ r))
  change (∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ r : Fin m, (M * N) (eI (σ r)) (eJ r)) = _
  simp_rw [hprod, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hsplit : ∀ f : Fin m → ZMod q,
      (∑ σ : Equiv.Perm (Fin m),
        Equiv.Perm.sign σ • ∏ r : Fin m, (M (eI (σ r)) (f r) * N (f r) (eJ r))) =
      (M.submatrix eI f).det * ∏ r : Fin m, N (f r) (eJ r) := fun f => by
    simp_rw [Finset.prod_mul_distrib, ← smul_mul_assoc, ← Finset.sum_mul, Matrix.det_apply]
    rfl
  simp_rw [hsplit]
  -- Drop non-injective `f` (whose determinant is `0`!)
  let InjF := (Finset.univ : Finset (Fin m → ZMod q)).filter Function.Injective
  have hdrop :
      (∑ f : Fin m → ZMod q, (M.submatrix eI f).det * ∏ r : Fin m, N (f r) (eJ r)) =
      ∑ f ∈ InjF, (M.submatrix eI f).det * ∏ r : Fin m, N (f r) (eJ r) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun f _ hnot => ?_
    simp only [InjF, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    unfold Function.Injective at hnot; push Not at hnot
    rcases hnot with ⟨r₁, r₂, hfr, hne⟩
    have hdet0 : (M.submatrix eI f).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun r => by simp [hfr])
    rw [hdet0, zero_mul]
  rw [hdrop]
  -- Bijection `SubIdx q m × Perm (Fin m) ≃ InjF` via `(K, τ) ↦ fun r => (eK (τ r)).1`!
  have hbij :
      (∑ f ∈ InjF, (M.submatrix eI f).det * ∏ r : Fin m, N (f r) (eJ r)) =
      ∑ p : SubIdx q m × Equiv.Perm (Fin m),
        (M.submatrix eI (fun r => (p.1.1.orderIsoOfFin p.1.2 (p.2 r)).1)).det *
          ∏ r : Fin m, N (p.1.1.orderIsoOfFin p.1.2 (p.2 r)).1 (eJ r) := by
    symm
    refine Finset.sum_bij (fun p _ => fun r => (p.1.1.orderIsoOfFin p.1.2 (p.2 r)).1)
      ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨K, τ⟩ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r₁ r₂ h =>
        τ.injective ((K.1.orderIsoOfFin K.2).injective (Subtype.ext h))⟩
    · rintro ⟨K₁, τ₁⟩ _ ⟨K₂, τ₂⟩ _ hEq
      have hK : K₁ = K₂ := by
        apply Subtype.ext; ext z
        constructor
        · intro hz
          let k := (K₁.1.orderIsoOfFin K₁.2).symm ⟨z, hz⟩
          have h := congrFun hEq (τ₁.symm k)
          simp only [Equiv.apply_symm_apply] at h
          have hz_eq : (K₁.1.orderIsoOfFin K₁.2 k).1 = z :=
            congrArg Subtype.val (OrderIso.apply_symm_apply (K₁.1.orderIsoOfFin K₁.2) ⟨z, hz⟩)
          rw [← hz_eq, h]
          exact (K₂.1.orderIsoOfFin K₂.2 (τ₂ (τ₁.symm k))).2
        · intro hz
          let k := (K₂.1.orderIsoOfFin K₂.2).symm ⟨z, hz⟩
          have h := congrFun hEq (τ₂.symm k)
          simp only [Equiv.apply_symm_apply] at h
          have hz_eq : (K₂.1.orderIsoOfFin K₂.2 k).1 = z :=
            congrArg Subtype.val (OrderIso.apply_symm_apply (K₂.1.orderIsoOfFin K₂.2) ⟨z, hz⟩)
          rw [← hz_eq, ← h]
          exact (K₁.1.orderIsoOfFin K₁.2 (τ₁ (τ₂.symm k))).2
      subst hK
      refine Prod.ext rfl (Equiv.Perm.ext fun r => ?_)
      exact (K₁.1.orderIsoOfFin K₁.2).injective (Subtype.ext (congrFun hEq r))
    · intro f hf
      have hinj : Function.Injective f := (Finset.mem_filter.mp hf).2
      let K : Finset (ZMod q) := Finset.univ.image f
      have hKc : K.card = m := by
        dsimp [K]; rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hbij_f : Function.Bijective (fun r : Fin m => (⟨f r, Finset.mem_image_of_mem f (Finset.mem_univ r)⟩ : K)) :=
        ⟨fun r₁ r₂ h => hinj (congrArg Subtype.val h),
         fun ⟨z, hz⟩ => by rcases Finset.mem_image.mp hz with ⟨r, _, rfl⟩; exact ⟨r, rfl⟩⟩
      let τ : Equiv.Perm (Fin m) := (Equiv.ofBijective _ hbij_f).trans (K.orderIsoOfFin hKc).toEquiv.symm
      refine ⟨(⟨K, hKc⟩, τ), Finset.mem_univ _, funext fun r => ?_⟩
      dsimp only [τ]; simp
  rw [hbij, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hperm_det : ∀ τ : Equiv.Perm (Fin m),
      (M.submatrix eI (fun r => (K.1.orderIsoOfFin K.2 (τ r)).1)).det =
        Equiv.Perm.sign τ • (M.submatrix eI (fun r => (K.1.orderIsoOfFin K.2 r).1)).det := fun τ => by
    have hsub : M.submatrix eI (fun r => (K.1.orderIsoOfFin K.2 (τ r)).1) =
        (M.submatrix eI (fun r => (K.1.orderIsoOfFin K.2 r).1)).submatrix id τ := rfl
    rw [hsub, Matrix.det_permute', ← zsmul_eq_mul, ← Units.smul_def]
  simp_rw [hperm_det, smul_mul_assoc, ← mul_smul_comm, ← Finset.mul_sum]
  congr 1
  rw [Matrix.det_apply]
  simp only [Matrix.submatrix_apply]
  rfl

/-- Compound of an upper-triangular matrix with constant diagonal `c` is `subWeight`-upper-graded
with constant diagonal `c^m`. -/
private lemma compound_upperTri {q m : ℕ} [NeZero q] {R : Type*} [CommRing R]
    (U : Matrix (ZMod q) (ZMod q) R) (c : R)
    (hU_tri : ∀ i j : ZMod q, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : ZMod q, U i i = c) :
    (∀ I J : SubIdx q m, subWeight J < subWeight I → compound m U I J = 0) ∧
    (∀ I J : SubIdx q m, subWeight J = subWeight I → I ≠ J → compound m U I J = 0) ∧
    (∀ I : SubIdx q m, compound m U I I = c ^ m) := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  have hterm_zero : ∀ (I J : SubIdx q m) (σ : Equiv.Perm (Fin m)),
      (∃ r : Fin m, (J.1.orderIsoOfFin J.2 r).1.val < (I.1.orderIsoOfFin I.2 (σ r)).1.val) →
      (∏ r : Fin m, U (I.1.orderIsoOfFin I.2 (σ r)).1 (J.1.orderIsoOfFin J.2 r).1) = 0 := by
    intro I J σ ⟨r, hr⟩
    exact Finset.prod_eq_zero (Finset.mem_univ r) (hU_tri _ _ hr)
  have hsum_ord : ∀ I : SubIdx q m, ∑ r : Fin m, (I.1.orderIsoOfFin I.2 r).1.val = subWeight I := fun I => by
    unfold subWeight
    rw [← Finset.sum_attach I.1 (fun x => x.val)]
    exact Equiv.sum_comp (I.1.orderIsoOfFin I.2).toEquiv (fun x : I.1 => x.1.val)
  refine ⟨?_, ?_, ?_⟩
  · intro I J hlt
    simp only [compound, Matrix.of_apply, Matrix.det_apply, Matrix.submatrix_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have hex : ∃ r : Fin m, (J.1.orderIsoOfFin J.2 r).1.val < (I.1.orderIsoOfFin I.2 (σ r)).1.val := by
      by_contra hall; push Not at hall
      have hle : ∑ r : Fin m, (I.1.orderIsoOfFin I.2 (σ r)).1.val ≤
          ∑ r : Fin m, (J.1.orderIsoOfFin J.2 r).1.val := Finset.sum_le_sum fun r _ => hall r
      rw [Equiv.sum_comp σ (fun r => (I.1.orderIsoOfFin I.2 r).1.val), hsum_ord I, hsum_ord J] at hle
      omega
    rw [hterm_zero I J σ hex, smul_zero]
  · intro I J heq hne
    simp only [compound, Matrix.of_apply, Matrix.det_apply, Matrix.submatrix_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have hex : ∃ r : Fin m, (J.1.orderIsoOfFin J.2 r).1.val < (I.1.orderIsoOfFin I.2 (σ r)).1.val := by
      by_contra hall; push Not at hall
      have heq_all : ∀ r : Fin m, (I.1.orderIsoOfFin I.2 (σ r)).1.val = (J.1.orderIsoOfFin J.2 r).1.val := by
        have hsum_eq : ∑ r : Fin m, (I.1.orderIsoOfFin I.2 (σ r)).1.val =
            ∑ r : Fin m, (J.1.orderIsoOfFin J.2 r).1.val := by
          rw [Equiv.sum_comp σ (fun r => (I.1.orderIsoOfFin I.2 r).1.val), hsum_ord I, hsum_ord J, heq]
        intro r
        by_contra hr_ne
        have hr_lt : (I.1.orderIsoOfFin I.2 (σ r)).1.val < (J.1.orderIsoOfFin J.2 r).1.val :=
          lt_of_le_of_ne (hall r) hr_ne
        have hlt_sum : ∑ x : Fin m, (I.1.orderIsoOfFin I.2 (σ x)).1.val <
            ∑ x : Fin m, (J.1.orderIsoOfFin J.2 x).1.val :=
          Finset.sum_lt_sum (fun x _ => hall x) ⟨r, Finset.mem_univ r, hr_lt⟩
        omega
      apply hne; apply Subtype.ext; ext z; constructor
      · intro hz
        let k := (I.1.orderIsoOfFin I.2).symm ⟨z, hz⟩
        have h := ZMod.val_injective q (heq_all (σ.symm k))
        simp only [Equiv.apply_symm_apply] at h
        have hz_eq : (I.1.orderIsoOfFin I.2 k).1 = z :=
          congrArg Subtype.val (OrderIso.apply_symm_apply (I.1.orderIsoOfFin I.2) ⟨z, hz⟩)
        rw [← hz_eq, h]
        exact (J.1.orderIsoOfFin J.2 (σ.symm k)).2
      · intro hz
        let k := (J.1.orderIsoOfFin J.2).symm ⟨z, hz⟩
        have h := ZMod.val_injective q (heq_all k)
        have hz_eq : (J.1.orderIsoOfFin J.2 k).1 = z :=
          congrArg Subtype.val (OrderIso.apply_symm_apply (J.1.orderIsoOfFin J.2) ⟨z, hz⟩)
        rw [← hz_eq, ← h]
        exact (I.1.orderIsoOfFin I.2 (σ k)).2
    rw [hterm_zero I J σ hex, smul_zero]
  · intro I
    simp only [compound, Matrix.of_apply, Matrix.det_apply, Matrix.submatrix_apply]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin m))]
    · simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.one_apply, hU_diag, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    · intro σ _ hσ1
      have hex : ∃ r : Fin m, (I.1.orderIsoOfFin I.2 r).1.val < (I.1.orderIsoOfFin I.2 (σ r)).1.val := by
        by_contra hall; push Not at hall
        have heq_all : ∀ r : Fin m, (I.1.orderIsoOfFin I.2 (σ r)).1.val = (I.1.orderIsoOfFin I.2 r).1.val := by
          have hsum_eq : ∑ r : Fin m, (I.1.orderIsoOfFin I.2 (σ r)).1.val =
              ∑ r : Fin m, (I.1.orderIsoOfFin I.2 r).1.val :=
            Equiv.sum_comp σ (fun r => (I.1.orderIsoOfFin I.2 r).1.val)
          intro r; by_contra hr_ne
          have hlt := Finset.sum_lt_sum (fun x _ => hall x)
            ⟨r, Finset.mem_univ r, lt_of_le_of_ne (hall r) hr_ne⟩
          omega
        apply hσ1; ext r
        exact congrArg Fin.val ((I.1.orderIsoOfFin I.2).injective (Subtype.ext (ZMod.val_injective q (heq_all r))))
      rw [hterm_zero I I σ hex, smul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim

/-- Jacobi's complementary-minor identity for any invertible `q × q` matrix `Γ` over a field `F`. -/
private lemma jacobi_complementary_minor {q m : ℕ} [NeZero q] (hm : m ≤ q)
    {F : Type*} [Field F] (Γ : Matrix (ZMod q) (ZMod q) F) (hdet : Γ.det ≠ 0)
    (I J : SubIdx q m) :
    letI : LinearOrder (ZMod q) := zmodLinearOrder q
    have hIc : I.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, I.2]
    have hJc : J.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, J.2]
    compound m (Γᵀ)⁻¹ I J =
      (thetaSign I.1 : F) * (thetaSign J.1 : F) * (Γ.det)⁻¹ *
        (Γ.submatrix (fun r : Fin (q - m) => (I.1ᶜ.orderIsoOfFin hIc r).1)
          (fun c : Fin (q - m) => (J.1ᶜ.orderIsoOfFin hJc c).1)).det := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  have hIc : I.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, I.2]
  have hJc : J.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, J.2]
  have hsum : m + (q - m) = q := Nat.add_sub_of_le hm
  -- Build the permutation `πI : Fin m ⊕ Fin (q - m) ≃ ZMod q` listing `I` then `Iᶜ` in order!
  let mkPerm (K : SubIdx q m) (hKc : K.1ᶜ.card = q - m) : (Fin m ⊕ Fin (q - m)) ≃ ZMod q :=
    { toFun := Sum.elim (fun r => (K.1.orderIsoOfFin K.2 r).1) (fun r => (K.1ᶜ.orderIsoOfFin hKc r).1)
      invFun := fun x => if hx : x ∈ K.1 then Sum.inl ((K.1.orderIsoOfFin K.2).symm ⟨x, hx⟩)
        else Sum.inr ((K.1ᶜ.orderIsoOfFin hKc).symm ⟨x, Finset.mem_compl.mpr hx⟩)
      left_inv := fun s => by
        rcases s with r | r
        · simp only [Sum.elim_inl, (K.1.orderIsoOfFin K.2 r).2, ↓reduceDIte, Subtype.coe_eta,
            OrderIso.symm_apply_apply]
        · have hnot : (K.1ᶜ.orderIsoOfFin hKc r).1 ∉ K.1 := Finset.mem_compl.mp (K.1ᶜ.orderIsoOfFin hKc r).2
          simp only [Sum.elim_inr, hnot, ↓reduceDIte, Subtype.coe_eta, OrderIso.symm_apply_apply]
      right_inv := fun x => by
        by_cases hx : x ∈ K.1
        · simp only [hx, ↓reduceDIte, Sum.elim_inl]
          exact congrArg Subtype.val (OrderIso.apply_symm_apply (K.1.orderIsoOfFin K.2) ⟨x, hx⟩)
        · simp only [hx, ↓reduceDIte, Sum.elim_inr]
          exact congrArg Subtype.val (OrderIso.apply_symm_apply (K.1ᶜ.orderIsoOfFin hKc) ⟨x, Finset.mem_compl.mpr hx⟩) }
  let πI := mkPerm I hIc
  let πJ := mkPerm J hJc
  -- Show `sign (πK.symm ∘ eCod) = thetaSign K.1` via `sumBijectionSign_split`!
  let eCod : Fin q ≃o ZMod q := Fintype.orderIsoFinOfCardEq (α := ZMod q) (ZMod.card q)
  have hsign_π : ∀ (K : SubIdx q m) (hKc : K.1ᶜ.card = q - m),
      Equiv.Perm.sign (((finSumFinEquiv.trans (finCongr hsum)).symm.trans (mkPerm K hKc)).trans eCod.toEquiv.symm) =
        thetaSign K.1 := by
    intro K hKc
    let ι : (K.1 ⊕ (K.1ᶜ : Finset (ZMod q))) ≃ ZMod q :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun x => if hx : x ∈ K.1 then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr hx⟩
        left_inv := fun s => by
          rcases s with ⟨x, hx⟩ | ⟨x, hx⟩
          · simp [hx]
          · have hnot : x ∉ K.1 := Finset.mem_compl.mp hx; simp [hnot]
        right_inv := fun x => by by_cases hx : x ∈ K.1 <;> simp [hx] }
    have hι_sign : sumBijectionSign ι = thetaSign K.1 := by
      have hsp := sumBijectionSign_split ι (rfl : K.1.card = K.1.card) (rfl : (K.1ᶜ : Finset (ZMod q)).card = (K.1ᶜ : Finset (ZMod q)).card)
        (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
      have hord1 : ∀ (A : Finset (ZMod q)), orderedSign (rfl : A.card = A.card) (Equiv.refl A) = 1 := fun A => by
        unfold orderedSign
        dsimp only
        have : (A.orderIsoOfFin rfl).toEquiv.trans ((Equiv.refl A).trans (A.orderIsoOfFin rfl).toEquiv.symm) = 1 := by
          ext i; simp
        rw [this, map_one]
      rw [hsp, hord1, hord1, mul_one, mul_one]
    rw [← hι_sign]
    unfold sumBijectionSign
    let : LinearOrder K.1 := Subtype.instLinearOrder _
    let : LinearOrder (K.1ᶜ : Finset (ZMod q)) := Subtype.instLinearOrder _
    let eSp : (Fin m ⊕ Fin (q - m)) ≃ Fin q := finSumFinEquiv.trans (finCongr hsum)
    let fK : Fin q ≃o (K.1 ⊕ₗ (K.1ᶜ : Finset (ZMod q))) :=
      { toEquiv := eSp.symm.trans
          ((Equiv.sumCongr (K.1.orderIsoOfFin K.2).toEquiv (K.1ᶜ.orderIsoOfFin hKc).toEquiv).trans toLex)
        map_rel_iff' := by
          intro u v
          obtain ⟨su, rfl⟩ := eSp.surjective u
          obtain ⟨sv, rfl⟩ := eSp.surjective v
          simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
          rcases su with x | x <;> rcases sv with y | y
          · simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.Lex.toLex_le_toLex, Sum.lex_inl_inl,
              RelIso.coe_fn_toEquiv, OrderIso.le_iff_le]
            simp only [eSp, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply,
              Fin.le_iff_val_le_val, Fin.val_cast, Fin.val_castAdd]
          · constructor
            · intro _; simp only [eSp, Equiv.trans_apply, finSumFinEquiv_apply_left,
                finSumFinEquiv_apply_right, finCongr_apply, Fin.le_iff_val_le_val,
                Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]; omega
            · intro _; exact Sum.Lex.sep _ _
          · constructor
            · intro h; cases h
            · intro h; simp only [eSp, Equiv.trans_apply, finSumFinEquiv_apply_left,
                finSumFinEquiv_apply_right, finCongr_apply, Fin.le_iff_val_le_val,
                Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at h; omega
          · simp only [Equiv.sumCongr_apply, Sum.map_inr, Sum.Lex.toLex_le_toLex, Sum.lex_inr_inr,
              RelIso.coe_fn_toEquiv, OrderIso.le_iff_le]
            simp only [eSp, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply,
              Fin.le_iff_val_le_val, Fin.val_cast, Fin.val_natAdd]
            omega }
    have hcardK : Fintype.card (K.1 ⊕ₗ (K.1ᶜ : Finset (ZMod q))) = q := by
      simp [Fintype.card_sum, Fintype.card_coe, K.2, hKc, hsum]
    have hord : Fintype.orderIsoFinOfCardEq (α := K.1 ⊕ₗ (K.1ᶜ : Finset (ZMod q))) hcardK = fK :=
      Subsingleton.elim _ _
    congr 1; ext i; obtain ⟨s, rfl⟩ := eSp.surjective i
    rw [hord]
    rcases s with r | r <;> simp [fK, mkPerm, ι, eSp, eCod, Equiv.symm_apply_apply]
  -- Block matrices `M = Γ.submatrix πI πJ` and `Minv = Γ⁻¹.submatrix πJ πI`
  let M : Matrix (Fin m ⊕ Fin (q - m)) (Fin m ⊕ Fin (q - m)) F := Γ.submatrix πI πJ
  let Minv : Matrix (Fin m ⊕ Fin (q - m)) (Fin m ⊕ Fin (q - m)) F := Γ⁻¹.submatrix πJ πI
  have hM_mul : M * Minv = 1 := by
    have hΓinv : Γ * Γ⁻¹ = 1 := Matrix.mul_nonsing_inv Γ (isUnit_iff_ne_zero.mpr hdet)
    ext s t
    simp only [Matrix.mul_apply, M, Minv, Matrix.submatrix_apply, Matrix.one_apply]
    rw [Equiv.sum_comp πJ (fun x => Γ (πI s) x * Γ⁻¹ x (πI t))]
    have := congrFun (congrFun hΓinv (πI s)) (πI t)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]; simp
  let A := Matrix.toBlocks₁₁ M; let B := Matrix.toBlocks₁₂ M
  let C := Matrix.toBlocks₂₁ M; let D := Matrix.toBlocks₂₂ M
  let A' := Matrix.toBlocks₁₁ Minv; let C' := Matrix.toBlocks₂₁ Minv
  have hblock_mul : M * Matrix.fromBlocks A' 0 C' 1 = Matrix.fromBlocks 1 B 0 D := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [Matrix.fromBlocks_multiply]
    have h1_11 : (1 : Matrix (Fin m ⊕ Fin (q - m)) (Fin m ⊕ Fin (q - m)) F).toBlocks₁₁ = 1 := by
      ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    have h1_21 : (1 : Matrix (Fin m ⊕ Fin (q - m)) (Fin m ⊕ Fin (q - m)) F).toBlocks₂₁ = 0 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have h1 : M.toBlocks₁₁ * A' + M.toBlocks₁₂ * C' = 1 := by
      have := congrArg Matrix.toBlocks₁₁ hM_mul
      rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks Minv,
        Matrix.fromBlocks_multiply, h1_11] at this
      simpa [A', C'] using this
    have h2 : M.toBlocks₂₁ * A' + M.toBlocks₂₂ * C' = 0 := by
      have := congrArg Matrix.toBlocks₂₁ hM_mul
      rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks Minv,
        Matrix.fromBlocks_multiply, h1_21] at this
      simpa [A', C'] using this
    simp [Matrix.fromBlocks_inj, h1, h2, B, D]
  have hdet_eq := congrArg Matrix.det hblock_mul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one, one_mul] at hdet_eq
  -- Compute `M.det = thetaSign I * thetaSign J * Γ.det`
  have hdetM : M.det = (thetaSign I.1 : F) * (thetaSign J.1 : F) * Γ.det := by
    let eSp : (Fin m ⊕ Fin (q - m)) ≃ Fin q := finSumFinEquiv.trans (finCongr hsum)
    let σI : Equiv.Perm (Fin q) := (eSp.symm.trans πI).trans eCod.toEquiv.symm
    let σJ : Equiv.Perm (Fin q) := (eSp.symm.trans πJ).trans eCod.toEquiv.symm
    have hM_sub : M = (((Γ.submatrix eCod eCod).submatrix σI id).submatrix id σJ).submatrix eSp eSp := by
      ext s t; simp [M, σI, σJ]
    rw [hM_sub, Matrix.det_submatrix_equiv_self eSp, Matrix.det_permute', Matrix.det_permute,
      show (Γ.submatrix eCod eCod).det = Γ.det from Matrix.det_submatrix_equiv_self eCod.toEquiv Γ,
      hsign_π I hIc, hsign_π J hJc]
    ring
  -- Compute `A'.det = compound m (Γᵀ)⁻¹ I J`!
  have hinvT : (Γᵀ)⁻¹ = (Γ⁻¹)ᵀ := by
    have h1 : Γᵀ * (Γ⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul Γ (isUnit_iff_ne_zero.mpr hdet), Matrix.transpose_one]
    have h2 : (Γᵀ)⁻¹ * Γᵀ = 1 :=
      Matrix.nonsing_inv_mul Γᵀ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet)
    calc (Γᵀ)⁻¹ = (Γᵀ)⁻¹ * (Γᵀ * (Γ⁻¹)ᵀ) := by rw [h1, Matrix.mul_one]
      _ = ((Γᵀ)⁻¹ * Γᵀ) * (Γ⁻¹)ᵀ := by rw [Matrix.mul_assoc]
      _ = (Γ⁻¹)ᵀ := by rw [h2, Matrix.one_mul]
  have hdetA' : A'.det = compound m (Γᵀ)⁻¹ I J := by
    have hA'_eq : A'ᵀ = (Γᵀ)⁻¹.submatrix (fun r => (I.1.orderIsoOfFin I.2 r).1)
        (fun c => (J.1.orderIsoOfFin J.2 c).1) := by
      ext r c
      simp only [Matrix.transpose_apply, A', Matrix.toBlocks₁₁, Minv, Matrix.submatrix_apply,
        πI, πJ, mkPerm, Equiv.coe_fn_mk, Sum.elim_inl, Matrix.of_apply]
      rw [hinvT, Matrix.transpose_apply]
    rw [← Matrix.det_transpose, hA'_eq]; rfl
  -- Combine `hdet_eq`, `hdetM`, `hdetA'`!
  rw [hdetM, hdetA'] at hdet_eq
  have hsq : ∀ u : ℤˣ, (u : F) * (u : F) = 1 := fun u => by
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  have hD_eq : D = Γ.submatrix (fun r => (I.1ᶜ.orderIsoOfFin hIc r).1)
      (fun c => (J.1ᶜ.orderIsoOfFin hJc c).1) := rfl
  dsimp only
  rw [← hD_eq, ← hdet_eq]
  calc compound m (Γᵀ)⁻¹ I J
      = ((thetaSign I.1 : F) * (thetaSign I.1 : F)) * ((thetaSign J.1 : F) * (thetaSign J.1 : F)) *
          ((Γ.det)⁻¹ * Γ.det) * compound m (Γᵀ)⁻¹ I J := by
            rw [hsq, hsq, inv_mul_cancel₀ hdet, one_mul, one_mul, one_mul]
    _ = (thetaSign I.1 : F) * (thetaSign J.1 : F) * (Γ.det)⁻¹ *
          ((thetaSign I.1 : F) * (thetaSign J.1 : F) * Γ.det * compound m (Γᵀ)⁻¹ I J) := by ring

/-- `[x^Y] (∑ d : ZMod q, X d)^k = (k! : ZMod q)` for any `Y` with `Y.card = k`. -/
private lemma coeff_sum_X_pow {q k : ℕ} [NeZero q] (Y : Finset (ZMod q)) (hYk : Y.card = k) :
    ((∑ d : ZMod q, (MvPolynomial.X d : MvPolynomial (ZMod q) (ZMod q))) ^ k).coeff
      (subsetMonomial Y) = (k.factorial : ZMod q) := by
  classical
  have hexp : (∑ d : ZMod q, (MvPolynomial.X d : MvPolynomial (ZMod q) (ZMod q))) ^ k =
      ∑ f : Fin k → ZMod q, MvPolynomial.monomial (∑ r : Fin k, Finsupp.single (f r) 1) 1 := by
    rw [Finset.sum_pow']
    refine Finset.sum_congr rfl fun f _ => ?_
    exact prod_X_eq_monomial Finset.univ f
  rw [hexp, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Count `{ f : Fin k → ZMod q | ∑ r, single (f r) 1 = subsetMonomial Y } = k!`!
  have hcard :
      ((Finset.univ : Finset (Fin k → ZMod q)).filter fun f =>
        ∑ r : Fin k, Finsupp.single (f r) 1 = subsetMonomial Y).card = k.factorial := by
    have hbij : ((Finset.univ : Finset (Fin k → ZMod q)).filter fun f =>
        ∑ r : Fin k, Finsupp.single (f r) 1 = subsetMonomial Y).card = Fintype.card (Fin k ≃ Y) := by
      symm
      refine Finset.card_bij (fun e _ => fun r => (e r).1) ?_ ?_ ?_
      · intro e _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        ext d
        rw [Finsupp.finsetSum_apply, subsetMonomial_apply]
        simp only [Finsupp.single_apply]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        by_cases hd : d ∈ Y
        · rw [if_pos hd]
          have hfilt : (Finset.univ.filter fun r : Fin k => (e r).1 = d) = {e.symm ⟨d, hd⟩} := by
            ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            exact ⟨fun h => e.injective (by rw [Equiv.apply_symm_apply]; exact Subtype.ext h),
                   fun h => by rw [h, Equiv.apply_symm_apply]⟩
          rw [hfilt, Finset.card_singleton]
        · rw [if_neg hd, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro r _ hr; exact hd (hr ▸ (e r).2)
      · intro e₁ _ e₂ _ hEq; exact Equiv.ext fun r => Subtype.ext (congrFun hEq r)
      · intro f hf
        have hEq := (Finset.mem_filter.mp hf).2
        have hcount : ∀ d : ZMod q, (Finset.univ.filter fun r : Fin k => f r = d).card =
            if d ∈ Y then 1 else 0 := fun d => by
          have hd := congrArg (fun g : ZMod q →₀ ℕ => g d) hEq
          rw [Finsupp.finsetSum_apply, subsetMonomial_apply] at hd
          simp only [Finsupp.single_apply] at hd
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one] at hd; exact hd
        have hmem : ∀ r : Fin k, f r ∈ Y := fun r => by
          have h1 := hcount (f r)
          have hpos : 0 < (Finset.univ.filter fun x : Fin k => f x = f r).card :=
            Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
          split_ifs at h1 with hm
          · exact hm
          · omega
        have hinj : Function.Injective f := fun r₁ r₂ h => by
          have h1 := hcount (f r₁)
          have hle : (Finset.univ.filter fun x : Fin k => f x = f r₁).card ≤ 1 := by
            split_ifs at h1 <;> omega
          exact Finset.card_le_one.mp hle
            r₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
            r₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩)
        have hbij_f : Function.Bijective (fun r : Fin k => (⟨f r, hmem r⟩ : Y)) :=
          (Fintype.bijective_iff_injective_and_card _).mpr
            ⟨fun r₁ r₂ h => hinj (congrArg Subtype.val h), by simp [hYk]⟩
        exact ⟨Equiv.ofBijective _ hbij_f, Finset.mem_univ _, rfl⟩
    rw [hbij, Fintype.card_equiv (Fintype.equivOfCardEq (by simp [hYk])), Fintype.card_fin]
  rw [hcard]

/-- Prime `p` divides `p.choose k` for `0 < k < p`. -/
private lemma prime_dvd_choose_self {p k : ℕ} (hp : p.Prime) (hk0 : k ≠ 0) (hkp : k < p) :
    p ∣ p.choose k := by
  have hnot_fac : ∀ n : ℕ, n < p → ¬ p ∣ n.factorial := by
    intro n
    induction n with
    | zero => intro _ h; exact absurd (Nat.le_of_dvd Nat.one_pos h) (not_le_of_gt hp.one_lt)
    | succ n ih =>
      intro hlt h
      rw [Nat.factorial_succ] at h
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact absurd (Nat.le_of_dvd (Nat.succ_pos n) h1) (not_le_of_gt hlt)
      · exact ih (Nat.lt_of_succ_lt hlt) h2
  have hmul := Nat.choose_mul_factorial_mul_factorial (le_of_lt hkp)
  have hdvd : p ∣ p.choose k * k.factorial * (p - k).factorial := by
    rw [hmul]; exact Nat.dvd_factorial hp.pos le_rfl
  exact (hp.dvd_mul.mp ((hp.dvd_mul.mp hdvd).resolve_right (hnot_fac (p - k) (by omega)))).resolve_right
    (hnot_fac k hkp)

/-- Count of centered `m`-subsets: `K * q = q.choose m` and `(m : ZMod q) * (K : ZMod q) = (-1)^(m-1)`. -/
private lemma card_centeredSubsets {q m : ℕ} [NeZero q] (hq : q.Prime) (hm0 : 0 < m) (hmq : m < q) :
    (centeredSubsets q m).card * q = q.choose m ∧
    (centeredSubsets q m).card * m.factorial * (q - m).factorial = (q - 1).factorial ∧
    ((m : ZMod q) * ((centeredSubsets q m).card : ZMod q) = (-1 : ZMod q) ^ (m - 1)) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hm : m ≤ q := le_of_lt hmq
  have hm_ne : (m : ZMod q) ≠ 0 := fun h0 =>
    absurd (Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff m q).mp h0)) (not_le_of_gt hmq)
  -- Bijection `centeredSubsets q m × ZMod q ≃ { I : Finset (ZMod q) // I.card = m }` via `(X, t) ↦ X + t`!
  have hcard1 : (centeredSubsets q m).card * q = q.choose m := by
    have hpow : (Finset.univ.filter fun I : Finset (ZMod q) => I.card = m).card = q.choose m := by
      have : Finset.univ.filter (fun I : Finset (ZMod q) => I.card = m) =
          Finset.powersetCard m (Finset.univ : Finset (ZMod q)) := by
        ext I; simp [Finset.mem_powersetCard]
      rw [this, Finset.card_powersetCard, Finset.card_univ, ZMod.card]
    have hmul : (centeredSubsets q m).card * q =
        (centeredSubsets q m ×ˢ (Finset.univ : Finset (ZMod q))).card := by
      rw [Finset.card_product, Finset.card_univ, ZMod.card]
    rw [hmul, ← hpow]
    refine Finset.card_bij (fun p _ => p.1.image (fun d => d + p.2)) ?_ ?_ ?_
    · rintro ⟨X, t⟩ hp
      have hX := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.card_image_of_injective _ (add_left_injective t), hX.1]
    · rintro ⟨X₁, t₁⟩ hp₁ ⟨X₂, t₂⟩ hp₂ hEq
      have hX₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).1).2
      have hX₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).1).2
      have hsum : (m : ZMod q) * t₁ = (m : ZMod q) * t₂ := by
        have hs := congrArg (fun S : Finset (ZMod q) => ∑ d ∈ S, d) hEq
        rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h),
            Finset.sum_image (fun _ _ _ _ h => add_right_cancel h),
            Finset.sum_add_distrib, Finset.sum_add_distrib, hX₁.2, hX₂.2, zero_add, zero_add,
            Finset.sum_const, Finset.sum_const, hX₁.1, hX₂.1, nsmul_eq_mul, nsmul_eq_mul] at hs
        exact hs
      have ht : t₁ = t₂ := mul_left_cancel₀ hm_ne hsum
      subst ht
      refine Prod.ext ?_ rfl
      ext d
      have hd := congrArg (fun S : Finset (ZMod q) => d + t₁ ∈ S) hEq
      simp only [Finset.mem_image, add_left_inj, exists_eq_right] at hd
      exact eq_iff_iff.mp hd
    · intro I hI
      have hIc : I.card = m := (Finset.mem_filter.mp hI).2
      let t : ZMod q := (∑ d ∈ I, d) * (m : ZMod q)⁻¹
      let X : Finset (ZMod q) := I.image (fun d => d - t)
      have hXc : X.card = m := by
        dsimp [X]; rw [Finset.card_image_of_injective _ (fun _ _ h => sub_left_injective h), hIc]
      have hXs : ∑ d ∈ X, d = 0 := by
        dsimp [X]
        rw [Finset.sum_image (fun _ _ _ _ h => sub_left_injective h), Finset.sum_sub_distrib,
          Finset.sum_const, hIc, nsmul_eq_mul]
        dsimp [t]; rw [mul_comm (m : ZMod q), mul_assoc, inv_mul_cancel₀ hm_ne, mul_one, sub_self]
      refine ⟨(X, t), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hXc, hXs⟩,
        Finset.mem_univ _⟩, ?_⟩
      ext d; simp only [X, Finset.mem_image]
      exact ⟨fun ⟨a, ⟨b, hb, hab⟩, hda⟩ => by
               have hbd : b = d := by linear_combination hab + hda
               rwa [← hbd],
             fun hd => ⟨d - t, ⟨d, hd, rfl⟩, sub_add_cancel d t⟩⟩
  have hcard2 : (centeredSubsets q m).card * m.factorial * (q - m).factorial = (q - 1).factorial := by
    have hch := Nat.choose_mul_factorial_mul_factorial hm
    rw [← hcard1] at hch
    have hqfac : q.factorial = q * (q - 1).factorial := by
      cases q with
      | zero => exact (hq.ne_zero rfl).elim
      | succ k => simp [Nat.factorial_succ]
    rw [hqfac] at hch
    have : q * ((centeredSubsets q m).card * m.factorial * (q - m).factorial) = q * (q - 1).factorial := by
      linarith [hch]
    exact Nat.eq_of_mul_eq_mul_left hq.pos this
  have hcard3 : (m : ZMod q) * ((centeredSubsets q m).card : ZMod q) = (-1 : ZMod q) ^ (m - 1) := by
    -- `m * K = (q - 1).choose (m - 1)` in `ℕ`!
    have hmK : m * (centeredSubsets q m).card = (q - 1).choose (m - 1) := by
      have hch := Nat.add_one_mul_choose_eq (q - 1) (m - 1)
      rw [Nat.sub_add_cancel hq.pos, Nat.sub_add_cancel hm0] at hch
      -- `q * (q - 1).choose (m - 1) = q.choose m * m`!
      rw [← hcard1] at hch
      have : q * (m * (centeredSubsets q m).card) = q * (q - 1).choose (m - 1) := by linarith [hch]
      exact Nat.eq_of_mul_eq_mul_left hq.pos this
    have hch_mod : ∀ k : ℕ, k < q → (((q - 1).choose k : ℕ) : ZMod q) = (-1 : ZMod q) ^ k := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hpas : (q - 1).choose k + (q - 1).choose (k + 1) = q.choose (k + 1) := by
          conv_rhs => rw [← Nat.sub_add_cancel hq.pos, Nat.choose_succ_succ]
        have hdvd : q ∣ q.choose (k + 1) := prime_dvd_choose_self hq (Nat.succ_ne_zero k) hk
        have hzero : ((q.choose (k + 1) : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
        have hsum : (((q - 1).choose k : ℕ) : ZMod q) + (((q - 1).choose (k + 1) : ℕ) : ZMod q) = 0 := by
          rw [← Nat.cast_add, hpas, hzero]
        rw [ih (Nat.lt_of_succ_lt hk)] at hsum
        rw [pow_succ]; linear_combination hsum
    have hcast : ((m * (centeredSubsets q m).card : ℕ) : ZMod q) = (((q - 1).choose (m - 1) : ℕ) : ZMod q) :=
      congrArg Nat.cast hmK
    push_cast at hcast
    rw [hcast, hch_mod (m - 1) (by omega)]
  exact ⟨hcard1, hcard2, hcard3⟩

/-- The `m`-th compound of the identity matrix is the identity matrix. -/
private lemma compound_one {q : ℕ} [NeZero q] (m : ℕ) {R : Type*} [CommRing R] :
    compound m (1 : Matrix (ZMod q) (ZMod q) R) = 1 := by
  let : LinearOrder (ZMod q) := zmodLinearOrder q
  ext I J
  simp only [compound, Matrix.of_apply, Matrix.one_apply]
  by_cases hIJ : I = J
  · subst hIJ
    have h1 : (1 : Matrix (ZMod q) (ZMod q) R).submatrix
        (fun r => (I.1.orderIsoOfFin I.2 r).1) (fun c => (I.1.orderIsoOfFin I.2 c).1) = 1 := by
      ext r c; simp [Matrix.one_apply]
    rw [h1, Matrix.det_one, if_pos rfl]
  · rw [if_neg hIJ]
    have hne : ∃ r : Fin m, (I.1.orderIsoOfFin I.2 r).1 ∉ J.1 := by
      by_contra hall; push Not at hall
      apply hIJ; apply Subtype.ext
      have hsub : I.1 ⊆ J.1 := fun z hz => by
        let r := (I.1.orderIsoOfFin I.2).symm ⟨z, hz⟩
        have hr := hall r; simpa [r] using hr
      exact Finset.eq_of_subset_of_card_le hsub (by rw [I.2, J.2])
    rcases hne with ⟨r, hr⟩
    exact Matrix.det_eq_zero_of_row_eq_zero r fun c => by
      have hne' : (I.1.orderIsoOfFin I.2 r).1 ≠ (J.1.orderIsoOfFin J.2 c).1 :=
        fun h => hr (h ▸ (J.1.orderIsoOfFin J.2 c).2)
      simp only [Matrix.submatrix_apply, Matrix.one_apply, if_neg hne']

/-- Explicit lower-unitriangular Pascal matrix over `ZMod q` that simultaneously upper-triangularizes
every circulant shift matrix `T_d` in characteristic `q`. -/
private def pascalMat (q : ℕ) [NeZero q] : Matrix (ZMod q) (ZMod q) (ZMod q) :=
  Matrix.of fun i j => (i.val.choose j.val : ZMod q)

/-- Circulant shift matrix `T_d` over `ZMod q`. -/
private def shiftMat (q : ℕ) [NeZero q] (d : ZMod q) : Matrix (ZMod q) (ZMod q) (ZMod q) :=
  Matrix.of fun i j => if i - j = d then 1 else 0

/-- Properties of `pascalMat q`: `det = 1`, invertible, and `P⁻¹ * T_d * P` is upper unitriangular. -/
private lemma pascalMat_props (q : ℕ) [NeZero q] (hq : q.Prime) :
    (pascalMat q)⁻¹ * pascalMat q = 1 ∧
    pascalMat q * (pascalMat q)⁻¹ = 1 ∧
    ∀ d : ZMod q,
      (∀ i j : ZMod q, j.val < i.val → ((pascalMat q)⁻¹ * shiftMat q d * pascalMat q) i j = 0) ∧
      (∀ i : ZMod q, ((pascalMat q)⁻¹ * shiftMat q d * pascalMat q) i i = 1) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  let P := pascalMat q
  let T := shiftMat q
  have hP_low : ∀ i j : ZMod q, i.val < j.val → P i j = 0 := fun i j hlt => by
    simp [P, pascalMat, Nat.choose_eq_zero_of_lt hlt]
  have hP_diag : ∀ i : ZMod q, P i i = 1 := fun i => by simp [P, pascalMat]
  have hP_det : P.det = 1 := by
    let eCod : Fin q ≃ ZMod q :=
      { toFun := fun i => (i.val : ZMod q)
        invFun := fun x => ⟨x.val, x.val_lt⟩
        left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
        right_inv := fun x => ZMod.natCast_zmod_val x }
    rw [← Matrix.det_submatrix_equiv_self eCod, ← Matrix.det_transpose]
    have hup : (P.submatrix eCod eCod)ᵀ.BlockTriangular id := fun i j hij => by
      change P (j.val : ZMod q) (i.val : ZMod q) = 0
      exact hP_low _ _ (by rw [ZMod.val_natCast_of_lt j.isLt, ZMod.val_natCast_of_lt i.isLt]; exact hij)
    rw [Matrix.det_of_isUpperTriangular hup]
    exact Finset.prod_eq_one fun i _ => by change P (i.val : ZMod q) (i.val : ZMod q) = 1; exact hP_diag _
  have hP_inv_l : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (by rw [hP_det]; exact isUnit_one)
  have hP_inv_r : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (by rw [hP_det]; exact isUnit_one)
  let J₁ : Matrix (ZMod q) (ZMod q) (ZMod q) :=
    Matrix.of fun i j => if i = j then 1 else if i.val + 1 = j.val then 1 else 0
  have hTJ : T (-1) * P = P * J₁ := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hL : (∑ k : ZMod q, T (-1) i k * P k j) = P (i + 1) j := by
      trans ∑ k : ZMod q, if k = i + 1 then P k j else 0
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hiff : i - k = -1 ↔ k = i + 1 :=
          ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
        simp [T, shiftMat, hiff]
      · simp
    have hR : (∑ k : ZMod q, P i k * J₁ k j) =
        P i j + (if j.val = 0 then 0 else P i ((j.val - 1 : ℕ) : ZMod q)) := by
      by_cases hj0 : j.val = 0
      · rw [if_pos hj0, add_zero]
        trans ∑ k : ZMod q, if k = j then P i k else 0
        · refine Finset.sum_congr rfl fun k _ => ?_
          dsimp [J₁]; split_ifs with h1 h2
          · simp
          · omega
          · simp
        · simp
      · rw [if_neg hj0]
        let j' : ZMod q := ((j.val - 1 : ℕ) : ZMod q)
        have hj'val : j'.val = j.val - 1 := ZMod.val_natCast_of_lt (by have := j.val_lt; omega)
        have hj'ne : j' ≠ j := fun h => by have := congrArg ZMod.val h; omega
        have hsum_pair : (∑ k : ZMod q, P i k * J₁ k j) =
            ∑ k : ZMod q, ((if k = j then P i k else 0) + (if k = j' then P i k else 0)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hiff : k.val + 1 = j.val ↔ k = j' := by
            constructor
            · intro h; apply ZMod.val_injective q; omega
            · intro h; rw [h, hj'val]; omega
          dsimp [J₁]
          by_cases hk1 : k = j
          · subst hk1; simp [hj'ne.symm]
          · by_cases hk2 : k = j'
            · subst hk2; simp [hk1, hiff.mpr rfl]
            · simp [hk1, hk2, mt hiff.mp hk2]
        rw [hsum_pair, Finset.sum_add_distrib]; simp [j']
    rw [hL, hR]
    by_cases hj0 : j.val = 0
    · simp [P, pascalMat, hj0]
    · rw [if_neg hj0]
      have hjm1 : (((j.val - 1 : ℕ) : ZMod q)).val = j.val - 1 :=
        ZMod.val_natCast_of_lt (by have := j.val_lt; omega)
      simp only [P, pascalMat, Matrix.of_apply, hjm1]
      have hpas : ((i.val + 1).choose j.val : ZMod q) =
          (i.val.choose j.val : ZMod q) + (i.val.choose (j.val - 1) : ZMod q) := by
        have h := Nat.choose_succ_succ i.val (j.val - 1)
        have hj1 : (j.val - 1).succ = j.val := by omega
        rw [hj1, Nat.succ_eq_add_one] at h
        rw [h, Nat.cast_add, add_comm]
      by_cases hi : i.val + 1 < q
      · have hiv : (i + 1).val = i.val + 1 := by
          have : i + 1 = ((i.val + 1 : ℕ) : ZMod q) := by push_cast; rw [ZMod.natCast_zmod_val]
          rw [this, ZMod.val_natCast_of_lt hi]
        rw [hiv, hpas]
      · have hiq : i.val + 1 = q := by have := i.val_lt; omega
        have hi0 : i + 1 = 0 := by
          have : i + 1 = ((i.val + 1 : ℕ) : ZMod q) := by push_cast; rw [ZMod.natCast_zmod_val]
          rw [this, hiq, ZMod.natCast_self]
        rw [hi0, ZMod.val_zero, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0), Nat.cast_zero, ← hpas, hiq]
        symm
        exact (ZMod.natCast_eq_zero_iff (q.choose j.val) q).mpr (prime_dvd_choose_self hq hj0 j.val_lt)
  have hT_mul : ∀ a b : ZMod q, T a * T b = T (a + b) := fun a b => by
    ext i j; rw [Matrix.mul_apply]
    trans ∑ k : ZMod q, if k = i - a then (if k - j = b then (1 : ZMod q) else 0) else 0
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hiff : i - k = a ↔ k = i - a := ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
      simp only [T, shiftMat, Matrix.of_apply, hiff]; split_ifs <;> simp
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, T, shiftMat, Matrix.of_apply]
      have hiff : i - a - j = b ↔ i - j = a + b := ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
      simp [hiff]
  have hT_pow : ∀ n : ℕ, T (-1) ^ n = T (-(n : ZMod q)) := fun n => by
    induction n with
    | zero => ext i j; simp [T, shiftMat, Matrix.one_apply, sub_eq_zero]
    | succ n ih =>
      rw [pow_succ, ih, hT_mul]; congr 1; push_cast; ring
  have hJ_tri : ∀ i j : ZMod q, j.val < i.val → J₁ i j = 0 := fun i j hlt => by
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
    have hne2 : i.val + 1 ≠ j.val := by omega
    simp [J₁, hne, hne2]
  have hJ_diag : ∀ i : ZMod q, J₁ i i = 1 := fun i => by simp [J₁]
  have hJ_pow_tri : ∀ n : ℕ,
      (∀ i j : ZMod q, j.val < i.val → (J₁ ^ n) i j = 0) ∧
      (∀ i : ZMod q, (J₁ ^ n) i i = 1) := fun n => by
    induction n with
    | zero =>
      exact ⟨fun i j hlt => by simp [Matrix.one_apply, show i ≠ j from fun h => by subst h; omega],
             fun i => by simp [Matrix.one_apply]⟩
    | succ n ih =>
      refine ⟨fun i j hlt => ?_, fun i => ?_⟩
      · rw [pow_succ, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val < i.val
        · rw [ih.1 i k hk, zero_mul]
        · rw [hJ_tri k j (by omega), mul_zero]
      · rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
        · rw [ih.2 i, hJ_diag i, mul_one]
        · intro k _ hki
          by_cases hk : k.val < i.val
          · rw [ih.1 i k hk, zero_mul]
          · have hlt : i.val < k.val := lt_of_le_of_ne (not_lt.mp hk) (fun h => hki (ZMod.val_injective q h.symm))
            rw [hJ_tri k i hlt, mul_zero]
        · intro h; exact (h (Finset.mem_univ _)).elim
  refine ⟨hP_inv_l, hP_inv_r, fun d => ?_⟩
  have hTd : T d = T (-1) ^ (-d).val := by
    rw [hT_pow, ZMod.natCast_zmod_val, neg_neg]
  have hconj : P⁻¹ * T (-1) * P = J₁ := by
    rw [Matrix.mul_assoc, hTJ, ← Matrix.mul_assoc, hP_inv_l, Matrix.one_mul]
  have hconj_pow : ∀ n : ℕ, P⁻¹ * T (-1) ^ n * P = J₁ ^ n := fun n => by
    induction n with
    | zero => simp [hP_inv_l]
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih, ← hconj]
      calc P⁻¹ * (T (-1) ^ n * T (-1)) * P
          = (P⁻¹ * T (-1) ^ n * (P * P⁻¹)) * T (-1) * P := by rw [hP_inv_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = P⁻¹ * T (-1) ^ n * P * (P⁻¹ * T (-1) * P) := by simp only [Matrix.mul_assoc]
  change (∀ i j : ZMod q, j.val < i.val → (P⁻¹ * T d * P) i j = 0) ∧
    (∀ i : ZMod q, (P⁻¹ * T d * P) i i = 1)
  rw [hTd, hconj_pow]
  exact hJ_pow_tri (-d).val

/-- Full `SubIdx q m` operators `Ahat` and `Bhat` over `ZMod q` (for Proposition 6.12). -/
private noncomputable def AhatMat (q m : ℕ) [NeZero q] (X : SubIdx q m) :
    Matrix (SubIdx q m) (SubIdx q m) (ZMod q) :=
  Matrix.of fun I J => (ZY X.1 I.1 J.1 : ZMod q)

private noncomputable def BhatMat (q m : ℕ) [NeZero q] (X : SubIdx q m) :
    Matrix (SubIdx q m) (SubIdx q m) (ZMod q) :=
  Matrix.of fun I J => ((thetaSign I.1 : ℤ) * (thetaSign J.1 : ℤ) * ZY X.1ᶜ I.1ᶜ J.1ᶜ : ZMod q)

/-- Steps 3–5 of Proposition 6.12: conjugation by `Q₀ = compound m (pascalMat q)` makes every
`AhatMat X` upper-graded with diagonal `m!` and every `BhatMat X` upper-graded with diagonal `(q-m)!`. -/
private lemma prop_6_12_upper_graded (q m : ℕ) [NeZero q] (hq : q.Prime) (hm : m ≤ q) :
    let Q₀ : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := compound m (pascalMat q)
    let Q₀inv : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := compound m (pascalMat q)⁻¹
    Q₀inv * Q₀ = 1 ∧
    Q₀ * Q₀inv = 1 ∧
    (∀ X : SubIdx q m,
      (∀ I J, subWeight J < subWeight I → (Q₀inv * AhatMat q m X * Q₀) I J = 0) ∧
      (∀ I J, subWeight J = subWeight I → I ≠ J → (Q₀inv * AhatMat q m X * Q₀) I J = 0) ∧
      (∀ I, (Q₀inv * AhatMat q m X * Q₀) I I = (m.factorial : ZMod q))) ∧
    (∀ X : SubIdx q m,
      (∀ I J, subWeight J < subWeight I → (Q₀inv * BhatMat q m X * Q₀) I J = 0) ∧
      (∀ I J, subWeight J = subWeight I → I ≠ J → (Q₀inv * BhatMat q m X * Q₀) I J = 0) ∧
      (∀ I, (Q₀inv * BhatMat q m X * Q₀) I I = ((q - m).factorial : ZMod q))) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hP_inv_l, hP_inv_r, hPT_tri⟩ := pascalMat_props q hq
  let P := pascalMat q
  let T := shiftMat q
  let R := MvPolynomial (ZMod q) (ZMod q)
  let F := FractionRing R
  let toR : ZMod q →+* R := MvPolynomial.C
  let toF : R →+* F := algebraMap R F
  let P_R : Matrix (ZMod q) (ZMod q) R := P.map toR
  let Pinv_R : Matrix (ZMod q) (ZMod q) R := P⁻¹.map toR
  have hPR_l : Pinv_R * P_R = 1 := by
    have := congrArg (Matrix.map · toR) hP_inv_l
    rwa [Matrix.map_mul, Matrix.map_one toR (map_zero toR) (map_one toR)] at this
  have hPR_r : P_R * Pinv_R = 1 := by
    have := congrArg (Matrix.map · toR) hP_inv_r
    rwa [Matrix.map_mul, Matrix.map_one toR (map_zero toR) (map_one toR)] at this
  let Γ_R : Matrix (ZMod q) (ZMod q) R := Matrix.of fun i j => MvPolynomial.X (i - j)
  let S_R : R := ∑ d : ZMod q, MvPolynomial.X d
  have hΓ_decomp : Γ_R = ∑ d : ZMod q, (MvPolynomial.X d : R) • (T d).map toR := by
    apply Matrix.ext; intro i j
    simp only [Γ_R, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
      T, shiftMat, smul_eq_mul]
    trans ∑ d : ZMod q, if d = i - j then (MvPolynomial.X d : R) else 0
    · simp
    · refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : i - j = d
      · subst hd; simp [toR]
      · simp [hd, Ne.symm hd, toR]
  have hΓt_decomp : Γ_Rᵀ = ∑ d : ZMod q, (MvPolynomial.X d : R) • (T (-d)).map toR := by
    apply Matrix.ext; intro i j
    simp only [Matrix.transpose_apply, Γ_R, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, T, shiftMat, smul_eq_mul]
    trans ∑ d : ZMod q, if d = j - i then (MvPolynomial.X d : R) else 0
    · simp
    · refine Finset.sum_congr rfl fun d _ => ?_
      have hiff : i - j = -d ↔ d = j - i := ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
      by_cases hd : i - j = -d
      · simp only [hd, hiff.mp hd, ↓reduceIte, toR, map_one, mul_one]
      · simp only [hd, mt hiff.mpr hd, ↓reduceIte, toR, map_zero, mul_zero]
  let U_R : Matrix (ZMod q) (ZMod q) R := Pinv_R * Γ_R * P_R
  let Ut_R : Matrix (ZMod q) (ZMod q) R := Pinv_R * Γ_Rᵀ * P_R
  have hU_R : (∀ i j : ZMod q, j.val < i.val → U_R i j = 0) ∧ (∀ i : ZMod q, U_R i i = S_R) := by
    have hrew : U_R = ∑ d : ZMod q, (MvPolynomial.X d : R) • (P⁻¹ * T d * P).map toR := by
      dsimp only [U_R]; rw [hΓ_decomp, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1; simp only [Pinv_R, P_R, Matrix.map_mul]
    rw [hrew]
    refine ⟨fun i j hlt => ?_, fun i => ?_⟩
    · simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact Finset.sum_eq_zero fun d _ => by rw [(hPT_tri d).1 i j hlt, map_zero, mul_zero]
    · simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, S_R]
      exact Finset.sum_congr rfl fun d _ => by rw [(hPT_tri d).2 i, map_one, mul_one]
  have hUt_R : (∀ i j : ZMod q, j.val < i.val → Ut_R i j = 0) ∧ (∀ i : ZMod q, Ut_R i i = S_R) := by
    have hrew : Ut_R = ∑ d : ZMod q, (MvPolynomial.X d : R) • (P⁻¹ * T (-d) * P).map toR := by
      dsimp only [Ut_R]; rw [hΓt_decomp, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1; simp only [Pinv_R, P_R, Matrix.map_mul]
    rw [hrew]
    refine ⟨fun i j hlt => ?_, fun i => ?_⟩
    · simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact Finset.sum_eq_zero fun d _ => by rw [(hPT_tri (-d)).1 i j hlt, map_zero, mul_zero]
    · simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, S_R]
      exact Finset.sum_congr rfl fun d _ => by rw [(hPT_tri (-d)).2 i, map_one, mul_one]
  have hdet_ΓR : Γ_R.det = S_R ^ q := by
    have h1 : U_R.det = Γ_R.det := by
      dsimp only [U_R]
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm Pinv_R.det, mul_assoc, ← Matrix.det_mul,
        hPR_l, Matrix.det_one, mul_one]
    rw [← h1]
    let eCod : Fin q ≃ ZMod q :=
      { toFun := fun i => (i.val : ZMod q)
        invFun := fun x => ⟨x.val, x.val_lt⟩
        left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
        right_inv := fun x => ZMod.natCast_zmod_val x }
    rw [← Matrix.det_submatrix_equiv_self eCod]
    have hup : (U_R.submatrix eCod eCod).BlockTriangular id := fun i j hij =>
      hU_R.1 _ _ (by
        dsimp only [eCod, Equiv.coe_fn_mk]
        rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt]; exact hij)
    rw [Matrix.det_of_isUpperTriangular hup]
    simp [hU_R.2]
  have hSR_ne : S_R ≠ 0 := by
    intro h0
    have hc := congrArg (fun p : R => p.coeff (Finsupp.single (0 : ZMod q) 1)) h0
    change (∑ d : ZMod q, (MvPolynomial.X d : R)).coeff (Finsupp.single (0 : ZMod q) 1) =
      (0 : R).coeff (Finsupp.single (0 : ZMod q) 1) at hc
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hc
    simp_rw [MvPolynomial.coeff_X] at hc
    have h1 : (∑ d : ZMod q, if Finsupp.single d 1 = Finsupp.single (0 : ZMod q) 1 then (1 : ZMod q) else 0) = 1 := by
      rw [Finset.sum_eq_single (0 : ZMod q)]
      · simp
      · intro d _ hd
        rw [if_neg]; intro heq
        have := congrArg (fun f : ZMod q →₀ ℕ => f d) heq; simp [hd] at this
      · intro h; exact (h (Finset.mem_univ _)).elim
    rw [h1] at hc; exact one_ne_zero hc
  let Q₀ : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := compound m P
  let Q₀inv : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := compound m P⁻¹
  have hQ₀_l : Q₀inv * Q₀ = 1 := by
    dsimp only [Q₀, Q₀inv]; rw [← compound_mul, hP_inv_l, compound_one]
  have hQ₀_r : Q₀ * Q₀inv = 1 := by
    dsimp only [Q₀, Q₀inv]; rw [← compound_mul, hP_inv_r, compound_one]
  have hord_cast : ∀ {n₁ n₂ : ℕ} (S : Finset (ZMod q)) (h₁ : S.card = n₁) (h₂ : S.card = n₂) (r : Fin n₁),
      let : LinearOrder (ZMod q) := zmodLinearOrder q
      S.orderIsoOfFin h₁ r = S.orderIsoOfFin h₂ (finCongr (h₁.symm.trans h₂) r) := by
    rintro _ _ S rfl rfl r; rfl
  have hAhat_coeff : ∀ (X I J : SubIdx q m),
      AhatMat q m X I J = (compound m Γ_R I J).coeff (subsetMonomial X.1) := by
    intro X I J
    dsimp only [AhatMat, Matrix.of_apply]
    rw [ZY_eq_det_coeff X.1 I.1 J.1 (I.2.trans J.2.symm) (X.2.trans I.2.symm)]
    let φ : MvPolynomial (ZMod q) ℤ →+* R := MvPolynomial.map (Int.castRingHom (ZMod q))
    have hcoeff : ((circulantSubmatrix (I.2.trans J.2.symm)).det.coeff (subsetMonomial X.1) : ZMod q) =
        (φ (circulantSubmatrix (I.2.trans J.2.symm)).det).coeff (subsetMonomial X.1) := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [hcoeff, RingHom.map_det]
    congr 1; unfold compound
    let : LinearOrder (ZMod q) := zmodLinearOrder q
    have hsub : φ.mapMatrix (circulantSubmatrix (I.2.trans J.2.symm)) =
        (Γ_R.submatrix (fun r : Fin m => (I.1.orderIsoOfFin I.2 r).1)
          (fun c : Fin m => (J.1.orderIsoOfFin J.2 c).1)).submatrix (finCongr I.2) (finCongr I.2) := by
      apply Matrix.ext; intro r c
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, circulantSubmatrix, genericCirculant,
        Matrix.of_apply, Matrix.submatrix_apply, Γ_R, φ]
      have hI_c := hord_cast I.1 rfl I.2 r
      have hJ_c := hord_cast J.1 (I.2.trans J.2.symm).symm J.2 c
      rw [hI_c, hJ_c, MvPolynomial.map_X]
    rw [hsub, Matrix.det_submatrix_equiv_self]; rfl
  let B_R : Matrix (SubIdx q m) (SubIdx q m) R := by
    let : LinearOrder (ZMod q) := zmodLinearOrder q
    exact Matrix.of fun I J =>
      let hIc : I.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, I.2]
      let hJc : J.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, J.2]
      (thetaSign I.1 : R) * (thetaSign J.1 : R) *
        (Γ_R.submatrix (fun r : Fin (q - m) => (I.1ᶜ.orderIsoOfFin hIc r).1)
          (fun c : Fin (q - m) => (J.1ᶜ.orderIsoOfFin hJc c).1)).det
  have hBhat_coeff : ∀ (X I J : SubIdx q m),
      BhatMat q m X I J = (B_R I J).coeff (subsetMonomial X.1ᶜ) := by
    intro X I J
    dsimp only [BhatMat, Matrix.of_apply]
    have hIc : I.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, I.2]
    have hJc : J.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, J.2]
    have hXc : X.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, X.2]
    rw [ZY_eq_det_coeff X.1ᶜ I.1ᶜ J.1ᶜ (hIc.trans hJc.symm) (hXc.trans hIc.symm)]
    let φ : MvPolynomial (ZMod q) ℤ →+* R := MvPolynomial.map (Int.castRingHom (ZMod q))
    push_cast
    have hcoeff : ((circulantSubmatrix (hIc.trans hJc.symm)).det.coeff (subsetMonomial X.1ᶜ) : ZMod q) =
        (φ (circulantSubmatrix (hIc.trans hJc.symm)).det).coeff (subsetMonomial X.1ᶜ) := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [hcoeff, RingHom.map_det]
    dsimp only [B_R, Matrix.of_apply]
    have hC1 : (thetaSign I.1 : R) = MvPolynomial.C (thetaSign I.1 : ZMod q) := by
      rcases Int.units_eq_one_or (thetaSign I.1) with h | h <;> simp [h]
    have hC2 : (thetaSign J.1 : R) = MvPolynomial.C (thetaSign J.1 : ZMod q) := by
      rcases Int.units_eq_one_or (thetaSign J.1) with h | h <;> simp [h]
    rw [hC1, hC2, mul_assoc (MvPolynomial.C _), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, mul_assoc]
    congr 1; congr 1
    let : LinearOrder (ZMod q) := zmodLinearOrder q
    have hsub : φ.mapMatrix (circulantSubmatrix (hIc.trans hJc.symm)) =
        (Γ_R.submatrix (fun r : Fin (q - m) => (I.1ᶜ.orderIsoOfFin hIc r).1)
          (fun c : Fin (q - m) => (J.1ᶜ.orderIsoOfFin hJc c).1)).submatrix (finCongr hIc) (finCongr hIc) := by
      apply Matrix.ext; intro r c
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, circulantSubmatrix, genericCirculant,
        Matrix.of_apply, Matrix.submatrix_apply, Γ_R, φ]
      have hI_c := hord_cast I.1ᶜ rfl hIc r
      have hJ_c := hord_cast J.1ᶜ (hIc.trans hJc.symm).symm hJc c
      rw [hI_c, hJ_c, MvPolynomial.map_X]
    rw [hsub, Matrix.det_submatrix_equiv_self]
  have hconj_coeff : ∀ (M_R : Matrix (SubIdx q m) (SubIdx q m) R) (M_Z : Matrix (SubIdx q m) (SubIdx q m) (ZMod q))
      (μ : ZMod q →₀ ℕ),
      (∀ I J, M_Z I J = (M_R I J).coeff μ) →
      ∀ I J, (Q₀inv * M_Z * Q₀) I J = ((Q₀inv.map toR * M_R * Q₀.map toR) I J).coeff μ := by
    intro M_R M_Z μ hMZ I J
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_mul, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [mul_comm _ (toR (Q₀ K J)), ← mul_assoc, ← map_mul]
    dsimp only [toR]
    rw [MvPolynomial.coeff_C_mul, ← hMZ L K]
    ring
  have hQ₀_Ahat : ∀ X : SubIdx q m,
      (∀ I J, subWeight J < subWeight I → (Q₀inv * AhatMat q m X * Q₀) I J = 0) ∧
      (∀ I J, subWeight J = subWeight I → I ≠ J → (Q₀inv * AhatMat q m X * Q₀) I J = 0) ∧
      (∀ I, (Q₀inv * AhatMat q m X * Q₀) I I = (m.factorial : ZMod q)) := by
    intro X
    have hcomp_R : Q₀inv.map toR * compound m Γ_R * Q₀.map toR = compound m U_R := by
      have h1 : Q₀inv.map toR = compound m Pinv_R := by
        apply Matrix.ext; intro I J
        simp only [Q₀inv, compound, Matrix.map_apply, Matrix.of_apply, RingHom.map_det]; rfl
      have h2 : Q₀.map toR = compound m P_R := by
        apply Matrix.ext; intro I J
        simp only [Q₀, compound, Matrix.map_apply, Matrix.of_apply, RingHom.map_det]; rfl
      rw [h1, h2, ← compound_mul, ← compound_mul]
    have htri := compound_upperTri (m := m) U_R S_R hU_R.1 hU_R.2
    refine ⟨fun I J hlt => ?_, fun I J heq hne => ?_, fun I => ?_⟩
    · rw [hconj_coeff (compound m Γ_R) (AhatMat q m X) (subsetMonomial X.1) (hAhat_coeff X), hcomp_R,
        htri.1 I J hlt, MvPolynomial.coeff_zero]; rfl
    · rw [hconj_coeff (compound m Γ_R) (AhatMat q m X) (subsetMonomial X.1) (hAhat_coeff X), hcomp_R,
        htri.2.1 I J heq hne, MvPolynomial.coeff_zero]; rfl
    · rw [hconj_coeff (compound m Γ_R) (AhatMat q m X) (subsetMonomial X.1) (hAhat_coeff X), hcomp_R,
        htri.2.2 I]
      exact coeff_sum_X_pow X.1 X.2
  have hQ₀_Bhat : ∀ X : SubIdx q m,
      (∀ I J, subWeight J < subWeight I → (Q₀inv * BhatMat q m X * Q₀) I J = 0) ∧
      (∀ I J, subWeight J = subWeight I → I ≠ J → (Q₀inv * BhatMat q m X * Q₀) I J = 0) ∧
      (∀ I, (Q₀inv * BhatMat q m X * Q₀) I I = ((q - m).factorial : ZMod q)) := by
    intro X
    let Γ_F : Matrix (ZMod q) (ZMod q) F := Γ_R.map toF
    let P_F : Matrix (ZMod q) (ZMod q) F := P_R.map toF
    let Pinv_F : Matrix (ZMod q) (ZMod q) F := Pinv_R.map toF
    let S_F : F := toF S_R
    have hSF_ne : S_F ≠ 0 := by
      intro h0; exact hSR_ne (IsFractionRing.injective R F (by simpa [S_F, toF] using h0))
    have hdet_ΓF : Γ_F.det = S_F ^ q := by
      change (toF.mapMatrix Γ_R).det = toF S_R ^ q
      rw [← RingHom.map_det, hdet_ΓR, map_pow]
    have hdet_ΓF_ne : Γ_F.det ≠ 0 := by rw [hdet_ΓF]; exact pow_ne_zero q hSF_ne
    have hB_jacobi : B_R.map toF = Γ_F.det • compound m (Γ_Fᵀ)⁻¹ := by
      apply Matrix.ext; intro I J
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      have hjac := jacobi_complementary_minor hm Γ_F hdet_ΓF_ne I J
      rw [hjac]
      let : LinearOrder (ZMod q) := zmodLinearOrder q
      have hIc : I.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, I.2]
      have hJc : J.1ᶜ.card = q - m := by simp [Finset.card_compl, ZMod.card, J.2]
      have hD_F : (Γ_F.submatrix (fun r : Fin (q - m) => (I.1ᶜ.orderIsoOfFin hIc r).1)
          (fun c : Fin (q - m) => (J.1ᶜ.orderIsoOfFin hJc c).1)).det =
          toF ((Γ_R.submatrix (fun r : Fin (q - m) => (I.1ᶜ.orderIsoOfFin hIc r).1)
            (fun c : Fin (q - m) => (J.1ᶜ.orderIsoOfFin hJc c).1)).det) := by
        rw [RingHom.map_det]; rfl
      dsimp only [B_R, Matrix.of_apply]
      rw [map_mul, map_mul, ← hD_F]
      have hth1 : toF (thetaSign I.1 : R) = (thetaSign I.1 : F) := by
        rcases Int.units_eq_one_or (thetaSign I.1) with h | h <;> simp [h]
      have hth2 : toF (thetaSign J.1 : R) = (thetaSign J.1 : F) := by
        rcases Int.units_eq_one_or (thetaSign J.1) with h | h <;> simp [h]
      rw [hth1, hth2]
      calc (thetaSign I.1 : F) * (thetaSign J.1 : F) * _
          = (Γ_F.det * (Γ_F.det)⁻¹) * ((thetaSign I.1 : F) * (thetaSign J.1 : F) * _) := by
              rw [mul_inv_cancel₀ hdet_ΓF_ne, one_mul]
        _ = _ := by ring
    let Ut_F : Matrix (ZMod q) (ZMod q) F := Ut_R.map toF
    have hUt_F_tri : ∀ i j : ZMod q, j.val < i.val → Ut_F i j = 0 := fun i j hlt => by
      simp [Ut_F, hUt_R.1 i j hlt]
    have hUt_F_diag : ∀ i : ZMod q, Ut_F i i = S_F := fun i => by simp [Ut_F, hUt_R.2 i, S_F]
    have hPF_l : Pinv_F * P_F = 1 := by
      have := congrArg (Matrix.map · toF) hPR_l
      rwa [Matrix.map_mul, Matrix.map_one toF (map_zero toF) (map_one toF)] at this
    have hPF_r : P_F * Pinv_F = 1 := by
      have := congrArg (Matrix.map · toF) hPR_r
      rwa [Matrix.map_mul, Matrix.map_one toF (map_zero toF) (map_one toF)] at this
    have hUtF_eq : Ut_F = Pinv_F * Γ_Fᵀ * P_F := by
      dsimp only [Ut_F, Ut_R, Pinv_F, P_F, Γ_F]
      rw [Matrix.map_mul, Matrix.map_mul]; congr 1
    have hUtF_det : Ut_F.det ≠ 0 := by
      rw [hUtF_eq, Matrix.det_mul, Matrix.det_mul, mul_comm Pinv_F.det, mul_assoc, ← Matrix.det_mul,
        hPF_l, Matrix.det_one, mul_one, Matrix.det_transpose]
      exact hdet_ΓF_ne
    have hUtF_inv_eq : Pinv_F * (Γ_Fᵀ)⁻¹ * P_F = Ut_F⁻¹ := by
      have hmul : Ut_F * (Pinv_F * (Γ_Fᵀ)⁻¹ * P_F) = 1 := by
        rw [hUtF_eq]
        have hΓt_inv : Γ_Fᵀ * (Γ_Fᵀ)⁻¹ = 1 :=
          Matrix.mul_nonsing_inv Γ_Fᵀ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet_ΓF_ne)
        calc Pinv_F * Γ_Fᵀ * P_F * (Pinv_F * (Γ_Fᵀ)⁻¹ * P_F)
            = Pinv_F * Γ_Fᵀ * (P_F * Pinv_F) * (Γ_Fᵀ)⁻¹ * P_F := by simp only [Matrix.mul_assoc]
          _ = Pinv_F * (Γ_Fᵀ * (Γ_Fᵀ)⁻¹) * P_F := by rw [hPF_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
          _ = 1 := by rw [hΓt_inv, Matrix.mul_one, hPF_l]
      have h1 := congrArg (Ut_F⁻¹ * ·) hmul
      rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Ut_F (isUnit_iff_ne_zero.mpr hUtF_det),
        Matrix.one_mul, Matrix.mul_one] at h1
    have hUtF_inv_tri : (∀ i j : ZMod q, j.val < i.val → Ut_F⁻¹ i j = 0) ∧
        (∀ i : ZMod q, Ut_F⁻¹ i i = S_F⁻¹) := by
      have hmul : Ut_F * Ut_F⁻¹ = 1 := Matrix.mul_nonsing_inv Ut_F (isUnit_iff_ne_zero.mpr hUtF_det)
      have hstep : ∀ d : ℕ, ∀ i : ZMod q, q - 1 - i.val = d →
          (∀ j : ZMod q, j.val < i.val → Ut_F⁻¹ i j = 0) ∧ Ut_F⁻¹ i i = S_F⁻¹ := by
        intro d
        induction d using Nat.strong_induction_on with
        | h d ihd =>
          intro i hd
          refine ⟨fun j hji => ?_, ?_⟩
          · have h0 := congrFun (congrFun hmul i) j
            rw [Matrix.mul_apply, Matrix.one_apply, if_neg (fun h => by subst h; exact lt_irrefl _ hji)] at h0
            have hsum : (∑ k : ZMod q, Ut_F i k * Ut_F⁻¹ k j) = S_F * Ut_F⁻¹ i j := by
              rw [Finset.sum_eq_single i]
              · rw [hUt_F_diag i]
              · intro k _ hki
                by_cases hk : k.val < i.val
                · rw [hUt_F_tri i k hk, zero_mul]
                · have hlt : i.val < k.val := lt_of_le_of_ne (not_lt.mp hk) (fun h => hki (ZMod.val_injective q h.symm))
                  have hkd : q - 1 - k.val < d := by have := k.val_lt; omega
                  rw [(ihd (q - 1 - k.val) hkd k rfl).1 j (lt_trans hji hlt), mul_zero]
              · intro h; exact (h (Finset.mem_univ _)).elim
            rw [hsum] at h0
            exact (mul_eq_zero.mp h0).resolve_left hSF_ne
          · have h1 := congrFun (congrFun hmul i) i
            rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at h1
            have hsum : (∑ k : ZMod q, Ut_F i k * Ut_F⁻¹ k i) = S_F * Ut_F⁻¹ i i := by
              rw [Finset.sum_eq_single i]
              · rw [hUt_F_diag i]
              · intro k _ hki
                by_cases hk : k.val < i.val
                · rw [hUt_F_tri i k hk, zero_mul]
                · have hlt : i.val < k.val := lt_of_le_of_ne (not_lt.mp hk) (fun h => hki (ZMod.val_injective q h.symm))
                  have hkd : q - 1 - k.val < d := by have := k.val_lt; omega
                  rw [(ihd (q - 1 - k.val) hkd k rfl).1 i hlt, mul_zero]
              · intro h; exact (h (Finset.mem_univ _)).elim
            rw [hsum] at h1
            calc Ut_F⁻¹ i i = S_F⁻¹ * (S_F * Ut_F⁻¹ i i) := by rw [← mul_assoc, inv_mul_cancel₀ hSF_ne, one_mul]
              _ = S_F⁻¹ := by rw [h1, mul_one]
      exact ⟨fun i j hlt => (hstep (q - 1 - i.val) i rfl).1 j hlt,
             fun i => (hstep (q - 1 - i.val) i rfl).2⟩
    have hQB_F : (Q₀inv.map toR * B_R * Q₀.map toR).map toF = S_F ^ q • compound m Ut_F⁻¹ := by
      rw [Matrix.map_mul, Matrix.map_mul, hB_jacobi, Matrix.mul_smul, Matrix.smul_mul, hdet_ΓF]
      congr 1
      have h1 : (Q₀inv.map toR).map toF = compound m Pinv_F := by
        apply Matrix.ext; intro I J
        simp only [Q₀inv, compound, Matrix.map_apply, Matrix.of_apply, RingHom.map_det]; rfl
      have h2 : (Q₀.map toR).map toF = compound m P_F := by
        apply Matrix.ext; intro I J
        simp only [Q₀, compound, Matrix.map_apply, Matrix.of_apply, RingHom.map_det]; rfl
      rw [h1, h2, ← compound_mul, ← compound_mul, hUtF_inv_eq]
    have htriF := compound_upperTri (m := m) Ut_F⁻¹ S_F⁻¹ hUtF_inv_tri.1 hUtF_inv_tri.2
    have hinjF := IsFractionRing.injective R F
    refine ⟨fun I J hlt => ?_, fun I J heq hne => ?_, fun I => ?_⟩
    · rw [hconj_coeff B_R (BhatMat q m X) (subsetMonomial X.1ᶜ) (hBhat_coeff X)]
      have hzero : (Q₀inv.map toR * B_R * Q₀.map toR) I J = 0 := hinjF (by
        have h := congrFun (congrFun hQB_F I) J
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, htriF.1 I J hlt, mul_zero] at h
        rw [h, map_zero])
      rw [hzero, MvPolynomial.coeff_zero]; rfl
    · rw [hconj_coeff B_R (BhatMat q m X) (subsetMonomial X.1ᶜ) (hBhat_coeff X)]
      have hzero : (Q₀inv.map toR * B_R * Q₀.map toR) I J = 0 := hinjF (by
        have h := congrFun (congrFun hQB_F I) J
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, htriF.2.1 I J heq hne, mul_zero] at h
        rw [h, map_zero])
      rw [hzero, MvPolynomial.coeff_zero]; rfl
    · rw [hconj_coeff B_R (BhatMat q m X) (subsetMonomial X.1ᶜ) (hBhat_coeff X)]
      have hdiag : (Q₀inv.map toR * B_R * Q₀.map toR) I I = S_R ^ (q - m) := hinjF (by
        have h := congrFun (congrFun hQB_F I) I
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, htriF.2.2 I] at h
        rw [h, map_pow]
        change S_F ^ q * (S_F⁻¹) ^ m = S_F ^ (q - m)
        have hpow : S_F ^ q = S_F ^ (q - m) * S_F ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
        rw [inv_pow, hpow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hSF_ne), mul_one])
      rw [hdiag]
      exact coeff_sum_X_pow X.1ᶜ (by simp [Finset.card_compl, ZMod.card, X.2])
  exact ⟨hQ₀_l, hQ₀_r, hQ₀_Ahat, hQ₀_Bhat⟩

/-- Steps 6–7 of Proposition 6.12: `tr((E_q * F_q)^2)` and `tr((U_q * S_q)^4)` in `ZMod q`. -/
private lemma prop_6_12_traces_mod_q (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    let K : ℕ := (centeredSubsets q m).card
    let E_q : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q) := (matE q m).map (Int.castRingHom (ZMod q))
    let F_q : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q) := (matF q m).map (Int.castRingHom (ZMod q))
    let U_q : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q) :=
      (matU q m).map (Int.castRingHom (ZMod q))
    let S_q : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q) :=
      (matS q m).map (Int.castRingHom (ZMod q))
    Matrix.trace ((E_q * F_q) ^ 2) = (K : ZMod q) * ((K : ZMod q) * ((q - 1).factorial : ZMod q)) ^ 2 ∧
    Matrix.trace ((U_q * S_q) ^ 4) = (K : ZMod q) ^ 2 * ((q - 1).factorial : ZMod q) ^ 4 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have hm : m ≤ q := le_of_lt hmq
  obtain ⟨hQ₀_l, hQ₀_r, hQ₀_Ahat, hQ₀_Bhat⟩ := prop_6_12_upper_graded q m hq hm
  let Q₀ : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := compound m (pascalMat q)
  let Q₀inv : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := compound m (pascalMat q)⁻¹
  let Ahat := AhatMat q m
  let Bhat := BhatMat q m
  have hnilp_of_strict : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (wt : ι → ℕ) (M : ℕ)
      (hwt : ∀ x, wt x < M) (D : Matrix ι ι (ZMod q)),
      (∀ i j, wt j ≤ wt i → D i j = 0) → D ^ M = 0 := by
    intro ι _ _ wt M hwt D hD
    have hpow : ∀ k : ℕ, ∀ i j : ι, wt j < wt i + k → (D ^ k) i j = 0 := fun k => by
      induction k with
      | zero => intro i j hlt; simp [show i ≠ j from fun h => by subst h; omega]
      | succ k ihk =>
        intro i j hlt
        rw [pow_succ, Matrix.mul_apply]
        refine Finset.sum_eq_zero fun r _ => ?_
        by_cases hr : wt r < wt i + k
        · rw [ihk i r hr, zero_mul]
        · rw [hD r j (by omega), mul_zero]
    ext i j; exact hpow M i j (by have := hwt j; omega)
  have hgrade_mul : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (wt : ι → ℕ)
      (M₁ M₂ : Matrix ι ι (ZMod q)) (c₁ c₂ : ZMod q),
      ((∀ i j, wt j < wt i → M₁ i j = 0) ∧ (∀ i j, wt j = wt i → i ≠ j → M₁ i j = 0) ∧ (∀ i, M₁ i i = c₁)) →
      ((∀ i j, wt j < wt i → M₂ i j = 0) ∧ (∀ i j, wt j = wt i → i ≠ j → M₂ i j = 0) ∧ (∀ i, M₂ i i = c₂)) →
      ((∀ i j, wt j < wt i → (M₁ * M₂) i j = 0) ∧
       (∀ i j, wt j = wt i → i ≠ j → (M₁ * M₂) i j = 0) ∧
       (∀ i, (M₁ * M₂) i i = c₁ * c₂)) := by
    intro ι _ _ wt M₁ M₂ c₁ c₂ h₁ h₂
    refine ⟨fun i j hlt => ?_, fun i j heq hne => ?_, fun i => ?_⟩
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : wt k < wt i
      · rw [h₁.1 i k hk, zero_mul]
      · rw [h₂.1 k j (by omega), mul_zero]
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk1 : wt k < wt i
      · rw [h₁.1 i k hk1, zero_mul]
      · by_cases hk2 : wt j < wt k
        · rw [h₂.1 k j hk2, mul_zero]
        · have hkeq : wt k = wt i := by omega
          by_cases hki : i = k
          · subst hki; rw [h₂.2.1 i j heq hne, mul_zero]
          · rw [h₁.2.1 i k hkeq hki, zero_mul]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [h₁.2.2 i, h₂.2.2 i]
      · intro k _ hki
        by_cases hk1 : wt k < wt i
        · rw [h₁.1 i k hk1, zero_mul]
        · by_cases hk2 : wt i < wt k
          · rw [h₂.1 k i hk2, mul_zero]
          · rw [h₁.2.1 i k (by omega) hki.symm, zero_mul]
      · intro h; exact (h (Finset.mem_univ _)).elim
  have hZY_sum_zero : ∀ (X I J : Finset (ZMod q)),
      (∑ d ∈ X, d) = 0 → (∑ x ∈ I, x) ≠ (∑ y ∈ J, y) → ZY X I J = 0 := by
    intro X I J hXs hIJne
    unfold ZY; split_ifs with hXI hXJ
    · refine Finset.sum_eq_zero fun h _ => ?_
      split_ifs with hmem hbij
      · exfalso; apply hIJne
        have h1 : ∑ d : X, (h d).1 = ∑ x ∈ I, x := by
          rw [Equiv.sum_comp h (fun x : I => x.1), Finset.sum_coe_sort I (fun x => x)]
        have h2 : ∑ d : X, ((h d).1 - d.1) = ∑ y ∈ J, y := by
          change ∑ d : X, ((Equiv.ofBijective (fun d : X => (⟨(h d).1 - d.1, hmem d⟩ : J)) hbij) d).1 = _
          rw [Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun y : J => y.1), Finset.sum_coe_sort J (fun y => y)]
        rw [Finset.sum_sub_distrib, h1, Finset.sum_coe_sort X (fun d => d), hXs, sub_zero] at h2
        exact h2
      · rfl
      · rfl
    · rfl
    · rfl
  let isCent (I : SubIdx q m) : Prop := ∑ x ∈ I.1, x = 0
  let incC : CenteredIdx q m → SubIdx q m := fun I => ⟨I.1, (Finset.mem_filter.mp I.2).2.1⟩
  have hAhat_inv : ∀ (X : CenteredIdx q m) (I J : SubIdx q m),
      isCent I → ¬ isCent J → Ahat (incC X) I J = 0 := by
    intro X I J hI hJ
    dsimp only [Ahat, AhatMat, Matrix.of_apply]
    have h0 := hZY_sum_zero X.1 I.1 J.1 (Finset.mem_filter.mp X.2).2.2 (by
      intro heq; apply hJ; dsimp [isCent] at hI ⊢; exact heq.symm.trans hI)
    rw [h0, Int.cast_zero]
  have hBhat_inv : ∀ (X : CenteredIdx q m) (I J : SubIdx q m),
      isCent I → ¬ isCent J → Bhat (incC X) I J = 0 := by
    intro X I J hI hJ
    dsimp only [Bhat, BhatMat, Matrix.of_apply]
    have hXc : ∑ d ∈ X.1ᶜ, d = 0 := by
      have htot := Finset.sum_add_sum_compl X.1 (fun d : ZMod q => d)
      rw [(Finset.mem_filter.mp X.2).2.2, zero_add, sum_univ_zmod_odd hq_odd] at htot; exact htot
    have hIJ : ∑ x ∈ I.1ᶜ, x ≠ ∑ y ∈ J.1ᶜ, y := by
      have h1 := Finset.sum_add_sum_compl I.1 (fun d : ZMod q => d)
      have h2 := Finset.sum_add_sum_compl J.1 (fun d : ZMod q => d)
      rw [sum_univ_zmod_odd hq_odd] at h1 h2
      intro heq; apply hJ; dsimp [isCent] at hI ⊢
      linear_combination h2 - h1 + hI + heq
    rw [hZY_sum_zero X.1ᶜ I.1ᶜ J.1ᶜ hXc hIJ, Int.cast_zero, mul_zero]
  let K : ℕ := (centeredSubsets q m).card
  have hK := card_centeredSubsets hq hm0 hmq
  let Ehat : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := ∑ X : CenteredIdx q m, Ahat (incC X)
  let Fhat : Matrix (SubIdx q m) (SubIdx q m) (ZMod q) := ∑ X : CenteredIdx q m, Bhat (incC X)
  let E_q : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q) := (matE q m).map (Int.castRingHom (ZMod q))
  let F_q : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q) := (matF q m).map (Int.castRingHom (ZMod q))
  have hEhat_res : ∀ I J : CenteredIdx q m, Ehat (incC I) (incC J) = E_q I J := fun I J => by
    simp [Ehat, E_q, matE, Ahat, AhatMat, matA, Matrix.sum_apply, incC]
  have hFhat_res : ∀ I J : CenteredIdx q m, Fhat (incC I) (incC J) = F_q I J := fun I J => by
    simp [Fhat, F_q, matF, Bhat, BhatMat, matB, Matrix.sum_apply, incC]
  have hEhat_inv : ∀ I J : SubIdx q m, isCent I → ¬ isCent J → Ehat I J = 0 := fun I J hI hJ => by
    simp only [Ehat, Matrix.sum_apply]
    exact Finset.sum_eq_zero fun X _ => hAhat_inv X I J hI hJ
  have hFhat_inv : ∀ I J : SubIdx q m, isCent I → ¬ isCent J → Fhat I J = 0 := fun I J hI hJ => by
    simp only [Fhat, Matrix.sum_apply]
    exact Finset.sum_eq_zero fun X _ => hBhat_inv X I J hI hJ
  have hres_mul : ∀ (M₁ M₂ : Matrix (SubIdx q m) (SubIdx q m) (ZMod q))
      (N₁ N₂ : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q)),
      (∀ I J, isCent I → ¬ isCent J → M₁ I J = 0) →
      (∀ I J : CenteredIdx q m, M₁ (incC I) (incC J) = N₁ I J) →
      (∀ I J : CenteredIdx q m, M₂ (incC I) (incC J) = N₂ I J) →
      ∀ I J : CenteredIdx q m, (M₁ * M₂) (incC I) (incC J) = (N₁ * N₂) I J := by
    intro M₁ M₂ N₁ N₂ hinv h1 h2 I J
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hsplit : (∑ L : SubIdx q m, M₁ (incC I) L * M₂ L (incC J)) =
        ∑ L ∈ Finset.univ.filter isCent, M₁ (incC I) L * M₂ L (incC J) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun L _ hnot => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      rw [hinv (incC I) L (Finset.mem_filter.mp I.2).2.2 hnot, zero_mul]
    rw [hsplit]
    symm
    refine Finset.sum_bij (fun L _ => incC L)
      (fun L _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp L.2).2.2⟩)
      (fun L₁ _ L₂ _ h => Subtype.ext (congrArg (fun x : SubIdx q m => x.1) h))
      (fun L hL => ⟨⟨L.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.2, (Finset.mem_filter.mp hL).2⟩⟩,
        Finset.mem_univ _, rfl⟩)
      (fun L _ => by rw [h1 I L, h2 L J])
  let cEF : ZMod q := (K : ZMod q) * ((q - 1).factorial : ZMod q)
  have htr_EF2 : Matrix.trace ((E_q * F_q) ^ 2) = (K : ZMod q) * cEF ^ 2 := by
    have hQE : (∀ I J, subWeight J < subWeight I → (Q₀inv * Ehat * Q₀) I J = 0) ∧
        (∀ I J, subWeight J = subWeight I → I ≠ J → (Q₀inv * Ehat * Q₀) I J = 0) ∧
        (∀ I, (Q₀inv * Ehat * Q₀) I I = (K : ZMod q) * (m.factorial : ZMod q)) := by
      have hsum : Q₀inv * Ehat * Q₀ = ∑ X : CenteredIdx q m, (Q₀inv * Ahat (incC X) * Q₀) := by
        dsimp only [Ehat]; rw [Matrix.mul_sum, Matrix.sum_mul]
      rw [hsum]
      refine ⟨fun I J hlt => by simp only [Matrix.sum_apply]; exact Finset.sum_eq_zero fun X _ => (hQ₀_Ahat _).1 I J hlt,
        fun I J heq hne => by simp only [Matrix.sum_apply]; exact Finset.sum_eq_zero fun X _ => (hQ₀_Ahat _).2.1 I J heq hne,
        fun I => by
          simp only [Matrix.sum_apply]
          dsimp only [Q₀, Q₀inv, Ahat]
          simp_rw [(hQ₀_Ahat _).2.2 I]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]⟩
    have hQF : (∀ I J, subWeight J < subWeight I → (Q₀inv * Fhat * Q₀) I J = 0) ∧
        (∀ I J, subWeight J = subWeight I → I ≠ J → (Q₀inv * Fhat * Q₀) I J = 0) ∧
        (∀ I, (Q₀inv * Fhat * Q₀) I I = (K : ZMod q) * ((q - m).factorial : ZMod q)) := by
      have hsum : Q₀inv * Fhat * Q₀ = ∑ X : CenteredIdx q m, (Q₀inv * Bhat (incC X) * Q₀) := by
        dsimp only [Fhat]; rw [Matrix.mul_sum, Matrix.sum_mul]
      rw [hsum]
      refine ⟨fun I J hlt => by simp only [Matrix.sum_apply]; exact Finset.sum_eq_zero fun X _ => (hQ₀_Bhat _).1 I J hlt,
        fun I J heq hne => by simp only [Matrix.sum_apply]; exact Finset.sum_eq_zero fun X _ => (hQ₀_Bhat _).2.1 I J heq hne,
        fun I => by
          simp only [Matrix.sum_apply]
          dsimp only [Q₀, Q₀inv, Bhat]
          simp_rw [(hQ₀_Bhat _).2.2 I]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]⟩
    have hQEF_eq : Q₀inv * (Ehat * Fhat) * Q₀ = (Q₀inv * Ehat * Q₀) * (Q₀inv * Fhat * Q₀) := by
      calc Q₀inv * (Ehat * Fhat) * Q₀
          = Q₀inv * Ehat * (Q₀ * Q₀inv) * Fhat * Q₀ := by rw [hQ₀_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = (Q₀inv * Ehat * Q₀) * (Q₀inv * Fhat * Q₀) := by simp only [Matrix.mul_assoc]
    have hdiag_EF : (K : ZMod q) * (m.factorial : ZMod q) * ((K : ZMod q) * ((q - m).factorial : ZMod q)) = cEF := by
      have hK2 : ((K * m.factorial * (q - m).factorial : ℕ) : ZMod q) = ((q - 1).factorial : ZMod q) :=
        congrArg Nat.cast hK.2.1
      push_cast at hK2
      dsimp [cEF]; rw [← hK2]; ring
    have hQEF := hgrade_mul subWeight _ _ _ _ hQE hQF
    rw [← hQEF_eq, hdiag_EF] at hQEF
    have hQEF2 := hgrade_mul subWeight _ _ _ _ hQEF hQEF
    have hQEF2_eq : Q₀inv * (Ehat * Fhat) ^ 2 * Q₀ = (Q₀inv * (Ehat * Fhat) * Q₀) * (Q₀inv * (Ehat * Fhat) * Q₀) := by
      rw [sq]
      calc Q₀inv * (Ehat * Fhat * (Ehat * Fhat)) * Q₀
          = Q₀inv * (Ehat * Fhat) * (Q₀ * Q₀inv) * (Ehat * Fhat) * Q₀ := by rw [hQ₀_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = (Q₀inv * (Ehat * Fhat) * Q₀) * (Q₀inv * (Ehat * Fhat) * Q₀) := by simp only [Matrix.mul_assoc]
    rw [← hQEF2_eq, ← sq] at hQEF2
    let Dhat := (Ehat * Fhat) ^ 2 - cEF ^ 2 • (1 : Matrix (SubIdx q m) (SubIdx q m) (ZMod q))
    have hQD_nilp : (Q₀inv * Dhat * Q₀) ^ (q * q) = 0 := by
      refine hnilp_of_strict subWeight (q * q) (fun I => ?_) (Q₀inv * Dhat * Q₀) (fun I J hle => ?_)
      · unfold subWeight
        calc ∑ x ∈ I.1, x.val ≤ ∑ _x ∈ I.1, (q - 1) := Finset.sum_le_sum fun x _ => by have := x.val_lt; omega
          _ = m * (q - 1) := by rw [Finset.sum_const, I.2, smul_eq_mul]
          _ ≤ q * (q - 1) := Nat.mul_le_mul_right _ hm
          _ < q * q := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hq.pos Nat.one_pos) hq.pos
      · have hrew : Q₀inv * Dhat * Q₀ = Q₀inv * (Ehat * Fhat) ^ 2 * Q₀ - cEF ^ 2 • 1 := by
          dsimp only [Dhat]
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ₀_l]
        rw [hrew, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
        by_cases hlt : subWeight J < subWeight I
        · rw [hQEF2.1 I J hlt, if_neg (fun h => by subst h; exact lt_irrefl _ hlt), smul_zero, sub_zero]
        · have heq : subWeight J = subWeight I := by omega
          by_cases hIJ : I = J
          · subst hIJ; rw [hQEF2.2.2 I, if_pos rfl, smul_eq_mul, mul_one, sub_self]
          · rw [hQEF2.2.1 I J heq hIJ, if_neg hIJ, smul_zero, sub_zero]
    have hDhat_nilp : Dhat ^ (q * q) = 0 := by
      have hconj_pow : ∀ r : ℕ, (Q₀inv * Dhat * Q₀) ^ r = Q₀inv * Dhat ^ r * Q₀ := fun r => by
        induction r with
        | zero => simp only [pow_zero, Matrix.mul_one]; exact hQ₀_l.symm
        | succ r ihr =>
          rw [pow_succ, pow_succ, ihr]
          calc Q₀inv * Dhat ^ r * Q₀ * (Q₀inv * Dhat * Q₀)
              = Q₀inv * Dhat ^ r * (Q₀ * Q₀inv) * Dhat * Q₀ := by simp only [Matrix.mul_assoc]
            _ = Q₀inv * (Dhat ^ r * Dhat) * Q₀ := by rw [hQ₀_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      rw [hconj_pow] at hQD_nilp
      have := congrArg (fun M => Q₀ * M * Q₀inv) hQD_nilp
      simp only [Matrix.mul_zero, Matrix.zero_mul] at this
      calc Dhat ^ (q * q) = (Q₀ * Q₀inv) * Dhat ^ (q * q) * (Q₀ * Q₀inv) := by rw [hQ₀_r, Matrix.one_mul, Matrix.mul_one]
        _ = Q₀ * (Q₀inv * Dhat ^ (q * q) * Q₀) * Q₀inv := by simp only [Matrix.mul_assoc]
        _ = 0 := this
    let D_q := (E_q * F_q) ^ 2 - cEF ^ 2 • (1 : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q))
    have hDhat_inv : ∀ I J, isCent I → ¬ isCent J → Dhat I J = 0 := by
      have hEF_inv : ∀ I J, isCent I → ¬ isCent J → (Ehat * Fhat) I J = 0 := fun I J hI hJ => by
        rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun L _ => ?_
        by_cases hL : isCent L
        · rw [hFhat_inv L J hL hJ, mul_zero]
        · rw [hEhat_inv I L hI hL, zero_mul]
      have hEF2_inv : ∀ I J, isCent I → ¬ isCent J → ((Ehat * Fhat) ^ 2) I J = 0 := fun I J hI hJ => by
        rw [sq, Matrix.mul_apply]; refine Finset.sum_eq_zero fun L _ => ?_
        by_cases hL : isCent L
        · rw [hEF_inv L J hL hJ, mul_zero]
        · rw [hEF_inv I L hI hL, zero_mul]
      intro I J hI hJ
      have hne : I ≠ J := fun h => hJ (h ▸ hI)
      dsimp only [Dhat]; rw [Matrix.sub_apply, hEF2_inv I J hI hJ, Matrix.smul_apply, Matrix.one_apply,
        if_neg hne, smul_zero, sub_zero]
    have hDhat_res : ∀ I J : CenteredIdx q m, Dhat (incC I) (incC J) = D_q I J := by
      have hEF_res := hres_mul Ehat Fhat E_q F_q hEhat_inv hEhat_res hFhat_res
      have hEF_inv : ∀ I J, isCent I → ¬ isCent J → (Ehat * Fhat) I J = 0 := fun I J hI hJ => by
        rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun L _ => ?_
        by_cases hL : isCent L
        · rw [hFhat_inv L J hL hJ, mul_zero]
        · rw [hEhat_inv I L hI hL, zero_mul]
      have hEF2_res : ∀ I J : CenteredIdx q m, ((Ehat * Fhat) ^ 2) (incC I) (incC J) = ((E_q * F_q) ^ 2) I J := by
        rw [sq, sq]; exact hres_mul (Ehat * Fhat) (Ehat * Fhat) (E_q * F_q) (E_q * F_q) hEF_inv hEF_res hEF_res
      intro I J
      dsimp only [Dhat, D_q]
      rw [Matrix.sub_apply, Matrix.sub_apply, hEF2_res I J, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.one_apply]
      have hiff : incC I = incC J ↔ I = J :=
        ⟨fun h => Subtype.ext (congrArg (fun x : SubIdx q m => x.1) h), fun h => h ▸ rfl⟩
      simp [hiff]
    have hDpow_res : ∀ r : ℕ, ∀ I J : CenteredIdx q m, (Dhat ^ r) (incC I) (incC J) = (D_q ^ r) I J := fun r => by
      induction r with
      | zero =>
        intro I J; simp only [pow_zero, Matrix.one_apply]
        have hiff : incC I = incC J ↔ I = J :=
          ⟨fun h => Subtype.ext (congrArg (fun x : SubIdx q m => x.1) h), fun h => h ▸ rfl⟩
        simp [hiff]
      | succ r ihr =>
        rw [pow_succ', pow_succ']
        exact hres_mul Dhat (Dhat ^ r) D_q (D_q ^ r) hDhat_inv hDhat_res ihr
    have hDq_nilp : D_q ^ (q * q) = 0 := by
      ext I J; rw [← hDpow_res (q * q) I J, hDhat_nilp]; rfl
    have htr0 : Matrix.trace D_q = 0 := trace_eq_zero_of_nilpotent D_q hDq_nilp
    dsimp only [D_q] at htr0
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_coe, smul_eq_mul] at htr0
    linear_combination htr0
  let U_q : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q) :=
    (matU q m).map (Int.castRingHom (ZMod q))
  let S_q : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q) :=
    (matS q m).map (Int.castRingHom (ZMod q))
  have htr_US4 : Matrix.trace ((U_q * S_q) ^ 4) =
      (K : ZMod q) ^ 2 * ((q - 1).factorial : ZMod q) ^ 4 := by
    let Uhat : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q) :=
      ∑ X : CenteredIdx q m, kronMat (Ahat (incC X)) (Bhat (incC X))
    let Shat : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q) :=
      Matrix.of fun p r => if p.1 = r.2 ∧ p.2 = r.1 then 1 else 0
    let Q2 := kronMat Q₀ Q₀
    let Q2inv := kronMat Q₀inv Q₀inv
    have hk_mul : ∀ (A₁ A₂ B₁ B₂ : Matrix (SubIdx q m) (SubIdx q m) (ZMod q)),
        kronMat A₁ B₁ * kronMat A₂ B₂ = kronMat (A₁ * A₂) (B₁ * B₂) := fun A₁ A₂ B₁ B₂ => by
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [Matrix.mul_apply, kronMat, Matrix.of_apply, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by ring
    have hQ2_l : Q2inv * Q2 = 1 := by
      dsimp only [Q2, Q2inv]; rw [hk_mul, hQ₀_l]
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [kronMat, Matrix.one_apply, Prod.ext_iff]; split_ifs <;> tauto
    have hQ2_r : Q2 * Q2inv = 1 := by
      dsimp only [Q2, Q2inv]; rw [hk_mul, hQ₀_r]
      ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [kronMat, Matrix.one_apply, Prod.ext_iff]; split_ifs <;> tauto
    let wt2 (p : SubIdx q m × SubIdx q m) : ℕ := subWeight p.1 + subWeight p.2
    have hQU : (∀ p r, wt2 r < wt2 p → (Q2inv * Uhat * Q2) p r = 0) ∧
        (∀ p r, wt2 r = wt2 p → p ≠ r → (Q2inv * Uhat * Q2) p r = 0) ∧
        (∀ p, (Q2inv * Uhat * Q2) p p = ((q - 1).factorial : ZMod q)) := by
      have hrew : Q2inv * Uhat * Q2 =
          ∑ X : CenteredIdx q m, kronMat (Q₀inv * Ahat (incC X) * Q₀) (Q₀inv * Bhat (incC X) * Q₀) := by
        dsimp only [Uhat, Q2, Q2inv]; rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun X _ => by rw [hk_mul, hk_mul]
      rw [hrew]
      have hterm : ∀ X : CenteredIdx q m,
          (∀ p r, wt2 r < wt2 p → kronMat (Q₀inv * Ahat (incC X) * Q₀) (Q₀inv * Bhat (incC X) * Q₀) p r = 0) ∧
          (∀ p r, wt2 r = wt2 p → p ≠ r → kronMat (Q₀inv * Ahat (incC X) * Q₀) (Q₀inv * Bhat (incC X) * Q₀) p r = 0) ∧
          (∀ p, kronMat (Q₀inv * Ahat (incC X) * Q₀) (Q₀inv * Bhat (incC X) * Q₀) p p =
            (m.factorial : ZMod q) * ((q - m).factorial : ZMod q)) := by
        intro X
        have hA := hQ₀_Ahat (incC X); have hB := hQ₀_Bhat (incC X)
        refine ⟨fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ hlt => ?_, fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ heq hne => ?_, fun ⟨i₁, i₂⟩ => ?_⟩
        · dsimp only [kronMat, Matrix.of_apply]
          by_cases h1 : subWeight j₁ < subWeight i₁
          · rw [hA.1 i₁ j₁ h1, zero_mul]
          · rw [hB.1 i₂ j₂ (by dsimp [wt2] at hlt; omega), mul_zero]
        · dsimp only [kronMat, Matrix.of_apply]
          by_cases h1 : subWeight j₁ < subWeight i₁
          · rw [hA.1 i₁ j₁ h1, zero_mul]
          · by_cases h2 : subWeight j₂ < subWeight i₂
            · rw [hB.1 i₂ j₂ h2, mul_zero]
            · have heq1 : subWeight j₁ = subWeight i₁ := by dsimp [wt2] at heq; omega
              have heq2 : subWeight j₂ = subWeight i₂ := by dsimp [wt2] at heq; omega
              by_cases hi1 : i₁ = j₁
              · have hi2 : i₂ ≠ j₂ := fun h => hne (Prod.ext hi1 h)
                rw [hB.2.1 i₂ j₂ heq2 hi2, mul_zero]
              · rw [hA.2.1 i₁ j₁ heq1 hi1, zero_mul]
        · dsimp only [kronMat, Matrix.of_apply]; rw [hA.2.2 i₁, hB.2.2 i₂]
      refine ⟨fun p r hlt => by simp only [Matrix.sum_apply]; exact Finset.sum_eq_zero fun X _ => (hterm X).1 p r hlt,
        fun p r heq hne => by simp only [Matrix.sum_apply]; exact Finset.sum_eq_zero fun X _ => (hterm X).2.1 p r heq hne,
        fun p => by
          simp only [Matrix.sum_apply]
          simp_rw [(hterm _).2.2 p]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          have hK2 : ((K * m.factorial * (q - m).factorial : ℕ) : ZMod q) = ((q - 1).factorial : ZMod q) :=
            congrArg Nat.cast hK.2.1
          push_cast at hK2; linear_combination hK2⟩
    have hSl : ∀ (M : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q))
        (a b : SubIdx q m) (r : SubIdx q m × SubIdx q m), (Shat * M) (a, b) r = M (b, a) r := by
      intro M a b r
      simp only [Matrix.mul_apply, Shat, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro y _ hy; simp [Ne.symm hy]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro x _ hx; exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hx]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hSr : ∀ (M : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q))
        (p : SubIdx q m × SubIdx q m) (a b : SubIdx q m), (M * Shat) p (a, b) = M p (b, a) := by
      intro M p a b
      simp only [Matrix.mul_apply, Shat, Matrix.of_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro y _ hy; simp [hy]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · intro x _ hx; exact Finset.sum_eq_zero fun y _ => by simp [hx]
      · intro h; exact (h (Finset.mem_univ _)).elim
    have hS_act : ∀ (M : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q))
        (p r : SubIdx q m × SubIdx q m),
        (Shat * M * Shat) p r = M (p.2, p.1) (r.2, r.1) := fun M ⟨p₁, p₂⟩ ⟨r₁, r₂⟩ => by
      rw [hSr, hSl]
    have hS_Q2 : ∀ (M : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q)),
        Q2inv * (Shat * M * Shat) * Q2 = Shat * (Q2inv * M * Q2) * Shat := by
      have hcomm : ∀ (A : Matrix (SubIdx q m) (SubIdx q m) (ZMod q)),
          kronMat A A * Shat = Shat * kronMat A A := by
        intro A; ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
        rw [hSr, hSl]; dsimp [kronMat]; ring
      intro M
      calc Q2inv * (Shat * M * Shat) * Q2
          = (Q2inv * Shat) * M * (Shat * Q2) := by simp only [Matrix.mul_assoc]
        _ = (Shat * Q2inv) * M * (Q2 * Shat) := by rw [hcomm Q₀inv, ← hcomm Q₀]
        _ = Shat * (Q2inv * M * Q2) * Shat := by simp only [Matrix.mul_assoc]
    have hQSUS : (∀ p r, wt2 r < wt2 p → (Q2inv * (Shat * Uhat * Shat) * Q2) p r = 0) ∧
        (∀ p r, wt2 r = wt2 p → p ≠ r → (Q2inv * (Shat * Uhat * Shat) * Q2) p r = 0) ∧
        (∀ p, (Q2inv * (Shat * Uhat * Shat) * Q2) p p = ((q - 1).factorial : ZMod q)) := by
      rw [hS_Q2 Uhat]
      have hwt_sw : ∀ p : SubIdx q m × SubIdx q m, wt2 (p.2, p.1) = wt2 p := fun ⟨_, _⟩ => add_comm _ _
      refine ⟨fun p r hlt => by rw [hS_act]; exact hQU.1 _ _ (by rwa [hwt_sw, hwt_sw]),
        fun p r heq hne => by
          rw [hS_act]; exact hQU.2.1 _ _ (by rwa [hwt_sw, hwt_sw]) (fun h => hne (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))),
        fun p => by rw [hS_act]; exact hQU.2.2 _⟩
    have hQUS2 := hgrade_mul wt2 _ _ _ _ hQU hQSUS
    have hQUS2_eq : Q2inv * (Uhat * (Shat * Uhat * Shat)) * Q2 =
        (Q2inv * Uhat * Q2) * (Q2inv * (Shat * Uhat * Shat) * Q2) := by
      calc Q2inv * (Uhat * (Shat * Uhat * Shat)) * Q2
          = Q2inv * Uhat * (Q2 * Q2inv) * (Shat * Uhat * Shat) * Q2 := by rw [hQ2_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = (Q2inv * Uhat * Q2) * (Q2inv * (Shat * Uhat * Shat) * Q2) := by simp only [Matrix.mul_assoc]
    rw [← hQUS2_eq] at hQUS2
    have hQUS4 := hgrade_mul wt2 _ _ _ _ hQUS2 hQUS2
    have hUS4_eq : (Uhat * Shat) ^ 4 =
        (Uhat * (Shat * Uhat * Shat)) * (Uhat * (Shat * Uhat * Shat)) := by
      simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
    have hQUS4_eq : Q2inv * (Uhat * Shat) ^ 4 * Q2 =
        (Q2inv * (Uhat * (Shat * Uhat * Shat)) * Q2) * (Q2inv * (Uhat * (Shat * Uhat * Shat)) * Q2) := by
      rw [hUS4_eq]
      calc Q2inv * ((Uhat * (Shat * Uhat * Shat)) * (Uhat * (Shat * Uhat * Shat))) * Q2
          = Q2inv * (Uhat * (Shat * Uhat * Shat)) * (Q2 * Q2inv) * (Uhat * (Shat * Uhat * Shat)) * Q2 := by
              rw [hQ2_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [← hQUS4_eq] at hQUS4
    let c4 : ZMod q := ((q - 1).factorial : ZMod q) ^ 4
    have hc4_eq : ((q - 1).factorial : ZMod q) * ((q - 1).factorial : ZMod q) *
        (((q - 1).factorial : ZMod q) * ((q - 1).factorial : ZMod q)) = c4 := by dsimp [c4]; ring
    rw [hc4_eq] at hQUS4
    let D2hat := (Uhat * Shat) ^ 4 - c4 • (1 : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q))
    have hQD2_nilp : (Q2inv * D2hat * Q2) ^ (2 * q * q) = 0 := by
      refine hnilp_of_strict wt2 (2 * q * q) (fun ⟨I₁, I₂⟩ => ?_) (Q2inv * D2hat * Q2) (fun p r hle => ?_)
      · dsimp [wt2]; unfold subWeight
        have h1 : ∑ x ∈ I₁.1, x.val < q * q :=
          calc ∑ x ∈ I₁.1, x.val ≤ ∑ _x ∈ I₁.1, (q - 1) := Finset.sum_le_sum fun x _ => by have := x.val_lt; omega
            _ = m * (q - 1) := by rw [Finset.sum_const, I₁.2, smul_eq_mul]
            _ ≤ q * (q - 1) := Nat.mul_le_mul_right _ hm
            _ < q * q := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hq.pos Nat.one_pos) hq.pos
        have h2 : ∑ x ∈ I₂.1, x.val < q * q :=
          calc ∑ x ∈ I₂.1, x.val ≤ ∑ _x ∈ I₂.1, (q - 1) := Finset.sum_le_sum fun x _ => by have := x.val_lt; omega
            _ = m * (q - 1) := by rw [Finset.sum_const, I₂.2, smul_eq_mul]
            _ ≤ q * (q - 1) := Nat.mul_le_mul_right _ hm
            _ < q * q := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hq.pos Nat.one_pos) hq.pos
        linarith
      · have hrew : Q2inv * D2hat * Q2 = Q2inv * (Uhat * Shat) ^ 4 * Q2 - c4 • 1 := by
          dsimp only [D2hat]
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ2_l]
        rw [hrew, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
        by_cases hlt : wt2 r < wt2 p
        · rw [hQUS4.1 p r hlt, if_neg (fun h => by subst h; exact lt_irrefl _ hlt), smul_zero, sub_zero]
        · have heq : wt2 r = wt2 p := by omega
          by_cases hpr : p = r
          · subst hpr; rw [hQUS4.2.2 p, if_pos rfl, smul_eq_mul, mul_one, sub_self]
          · rw [hQUS4.2.1 p r heq hpr, if_neg hpr, smul_zero, sub_zero]
    have hD2hat_nilp : D2hat ^ (2 * q * q) = 0 := by
      have hconj_pow : ∀ r : ℕ, (Q2inv * D2hat * Q2) ^ r = Q2inv * D2hat ^ r * Q2 := fun r => by
        induction r with
        | zero => simp [hQ2_l]
        | succ r ihr =>
          rw [pow_succ, pow_succ, ihr]
          calc Q2inv * D2hat ^ r * Q2 * (Q2inv * D2hat * Q2)
              = Q2inv * D2hat ^ r * (Q2 * Q2inv) * D2hat * Q2 := by simp only [Matrix.mul_assoc]
            _ = Q2inv * (D2hat ^ r * D2hat) * Q2 := by rw [hQ2_r]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      rw [hconj_pow] at hQD2_nilp
      have := congrArg (fun M => Q2 * M * Q2inv) hQD2_nilp
      simp only [Matrix.mul_zero, Matrix.zero_mul] at this
      calc D2hat ^ (2 * q * q) = (Q2 * Q2inv) * D2hat ^ (2 * q * q) * (Q2 * Q2inv) := by rw [hQ2_r, Matrix.one_mul, Matrix.mul_one]
        _ = Q2 * (Q2inv * D2hat ^ (2 * q * q) * Q2) * Q2inv := by simp only [Matrix.mul_assoc]
        _ = 0 := this
    let isCent2 (p : SubIdx q m × SubIdx q m) : Prop := isCent p.1 ∧ isCent p.2
    let incC2 (p : CenteredIdx q m × CenteredIdx q m) : SubIdx q m × SubIdx q m := (incC p.1, incC p.2)
    have hres_mul2 : ∀ (M₁ M₂ : Matrix (SubIdx q m × SubIdx q m) (SubIdx q m × SubIdx q m) (ZMod q))
        (N₁ N₂ : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q)),
        (∀ p r, isCent2 p → ¬ isCent2 r → M₁ p r = 0) →
        (∀ p r, M₁ (incC2 p) (incC2 r) = N₁ p r) →
        (∀ p r, M₂ (incC2 p) (incC2 r) = N₂ p r) →
        ∀ p r, (M₁ * M₂) (incC2 p) (incC2 r) = (N₁ * N₂) p r := by
      intro M₁ M₂ N₁ N₂ hinv h1 h2 p r
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hsplit : (∑ L : SubIdx q m × SubIdx q m, M₁ (incC2 p) L * M₂ L (incC2 r)) =
          ∑ L ∈ Finset.univ.filter isCent2, M₁ (incC2 p) L * M₂ L (incC2 r) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun L _ hnot => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        rw [hinv (incC2 p) L ⟨(Finset.mem_filter.mp p.1.2).2.2, (Finset.mem_filter.mp p.2.2).2.2⟩ hnot, zero_mul]
      rw [hsplit]
      symm
      refine Finset.sum_bij (fun L _ => incC2 L)
        (fun L _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp L.1.2).2.2, (Finset.mem_filter.mp L.2.2).2.2⟩)
        (fun L₁ _ L₂ _ h => Prod.ext (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.1.1) h)) (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.2.1) h)))
        (fun L hL => ⟨(⟨L.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.1.2, (Finset.mem_filter.mp hL).2.1⟩⟩,
                       ⟨L.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.2.2, (Finset.mem_filter.mp hL).2.2⟩⟩),
          Finset.mem_univ _, rfl⟩)
        (fun L _ => by rw [h1 p L, h2 L r])
    have hUhat_inv : ∀ p r, isCent2 p → ¬ isCent2 r → Uhat p r = 0 := fun ⟨p₁, p₂⟩ ⟨r₁, r₂⟩ ⟨hp₁, hp₂⟩ hnr => by
      simp only [Uhat, Matrix.sum_apply, kronMat, Matrix.of_apply]
      refine Finset.sum_eq_zero fun X _ => ?_
      by_cases hr₁ : isCent r₁
      · have hr₂ : ¬ isCent r₂ := fun h => hnr ⟨hr₁, h⟩
        rw [hBhat_inv X p₂ r₂ hp₂ hr₂, mul_zero]
      · rw [hAhat_inv X p₁ r₁ hp₁ hr₁, zero_mul]
    have hShat_inv : ∀ p r, isCent2 p → ¬ isCent2 r → Shat p r = 0 := fun ⟨p₁, p₂⟩ ⟨r₁, r₂⟩ ⟨hp₁, hp₂⟩ hnr => by
      dsimp only [Shat, Matrix.of_apply]
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hnr ⟨hp₂, hp₁⟩
    have hUhat_res : ∀ p r, Uhat (incC2 p) (incC2 r) = U_q p r := fun ⟨p₁, p₂⟩ ⟨r₁, r₂⟩ => by
      simp [Uhat, U_q, matU, kronMat, Ahat, AhatMat, Bhat, BhatMat, matA, matB, Matrix.sum_apply, incC2, incC]
    have hShat_res : ∀ p r, Shat (incC2 p) (incC2 r) = S_q p r := fun ⟨p₁, p₂⟩ ⟨r₁, r₂⟩ => by
      simp only [Shat, S_q, matS, Matrix.map_apply, Matrix.of_apply, incC2]
      have h1 : incC p₁ = incC r₂ ↔ p₁ = r₂ := ⟨fun h => Subtype.ext (congrArg (fun x : SubIdx q m => x.1) h), fun h => h ▸ rfl⟩
      have h2 : incC p₂ = incC r₁ ↔ p₂ = r₁ := ⟨fun h => Subtype.ext (congrArg (fun x : SubIdx q m => x.1) h), fun h => h ▸ rfl⟩
      simp [h1, h2]
    have hUS_inv : ∀ p r, isCent2 p → ¬ isCent2 r → (Uhat * Shat) p r = 0 := fun p r hp hnr => by
      rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun L _ => ?_
      by_cases hL : isCent2 L
      · rw [hShat_inv L r hL hnr, mul_zero]
      · rw [hUhat_inv p L hp hL, zero_mul]
    have hUS_res := hres_mul2 Uhat Shat U_q S_q hUhat_inv hUhat_res hShat_res
    have hUS_pow_inv : ∀ k : ℕ, ∀ p r, isCent2 p → ¬ isCent2 r → ((Uhat * Shat) ^ k) p r = 0 := fun k => by
      induction k with
      | zero => intro p r hp hnr; simp [Matrix.one_apply, show p ≠ r from fun h => hnr (h ▸ hp)]
      | succ k ihk =>
        intro p r hp hnr; rw [pow_succ', Matrix.mul_apply]
        refine Finset.sum_eq_zero fun L _ => ?_
        by_cases hL : isCent2 L
        · rw [ihk L r hL hnr, mul_zero]
        · rw [hUS_inv p L hp hL, zero_mul]
    have hUS_pow_res : ∀ k : ℕ, ∀ p r, ((Uhat * Shat) ^ k) (incC2 p) (incC2 r) = ((U_q * S_q) ^ k) p r := fun k => by
      induction k with
      | zero =>
        intro p r; simp only [pow_zero, Matrix.one_apply]
        have hiff : incC2 p = incC2 r ↔ p = r :=
          ⟨fun h => Prod.ext (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.1.1) h)) (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.2.1) h)),
           fun h => h ▸ rfl⟩
        simp [hiff]
      | succ k ihk =>
        rw [pow_succ', pow_succ']
        exact hres_mul2 (Uhat * Shat) ((Uhat * Shat) ^ k) (U_q * S_q) ((U_q * S_q) ^ k) hUS_inv hUS_res ihk
    let D2_q := (U_q * S_q) ^ 4 - c4 • (1 : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q))
    have hD2_inv : ∀ p r, isCent2 p → ¬ isCent2 r → D2hat p r = 0 := fun p r hp hnr => by
      have hne : p ≠ r := fun h => hnr (h ▸ hp)
      dsimp only [D2hat]; rw [Matrix.sub_apply, hUS_pow_inv 4 p r hp hnr, Matrix.smul_apply,
        Matrix.one_apply, if_neg hne, smul_zero, sub_zero]
    have hD2_res : ∀ p r, D2hat (incC2 p) (incC2 r) = D2_q p r := fun p r => by
      dsimp only [D2hat, D2_q]
      rw [Matrix.sub_apply, Matrix.sub_apply, hUS_pow_res 4 p r, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.one_apply]
      have hiff : incC2 p = incC2 r ↔ p = r :=
        ⟨fun h => Prod.ext (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.1.1) h)) (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.2.1) h)),
         fun h => h ▸ rfl⟩
      simp [hiff]
    have hD2pow_res : ∀ k : ℕ, ∀ p r, (D2hat ^ k) (incC2 p) (incC2 r) = (D2_q ^ k) p r := fun k => by
      induction k with
      | zero =>
        intro p r; simp only [pow_zero, Matrix.one_apply]
        have hiff : incC2 p = incC2 r ↔ p = r :=
          ⟨fun h => Prod.ext (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.1.1) h)) (Subtype.ext (congrArg (fun x : SubIdx q m × SubIdx q m => x.2.1) h)),
           fun h => h ▸ rfl⟩
        simp [hiff]
      | succ k ihk =>
        rw [pow_succ', pow_succ']; exact hres_mul2 D2hat (D2hat ^ k) D2_q (D2_q ^ k) hD2_inv hD2_res ihk
    have hD2q_nilp : D2_q ^ (2 * q * q) = 0 := by
      ext p r; rw [← hD2pow_res (2 * q * q) p r, hD2hat_nilp]; rfl
    have htr0 : Matrix.trace D2_q = 0 := trace_eq_zero_of_nilpotent D2_q hD2q_nilp
    dsimp only [D2_q] at htr0
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_prod, Fintype.card_coe,
      smul_eq_mul] at htr0
    dsimp only [c4] at htr0
    push_cast at htr0
    linear_combination htr0
  exact ⟨htr_EF2, htr_US4⟩

/-- **Proposition 6.12** (`prop_6_12_zeval`): For odd prime `q` and `0 < m < q`,
`N_{B,m} ≡ N_{C,m} ≡ 1 / m^2 (mod q)`. -/
theorem prop_6_12_zeval (q m : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    ((mixedOrbitCountB q m : ZMod q) = ((m : ZMod q) ^ 2)⁻¹) ∧
    ((mixedOrbitCountC q m : ZMod q) = ((m : ZMod q) ^ 2)⁻¹) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have h610 := lem_6_10_layers q m hq hodd hm0 hmq
  have h611 := lem_6_11_traces q m hq hodd hm0 hmq
  let K : ℕ := (centeredSubsets q m).card
  have hK := card_centeredSubsets hq hm0 hmq
  let E_q : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q) := (matE q m).map (Int.castRingHom (ZMod q))
  let F_q : Matrix (CenteredIdx q m) (CenteredIdx q m) (ZMod q) := (matF q m).map (Int.castRingHom (ZMod q))
  let U_q : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q) :=
    (matU q m).map (Int.castRingHom (ZMod q))
  let S_q : Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) (ZMod q) :=
    (matS q m).map (Int.castRingHom (ZMod q))
  obtain ⟨htr_EF2, htr_US4⟩ := prop_6_12_traces_mod_q q m hq hodd hm0 hmq
  let cEF : ZMod q := (K : ZMod q) * ((q - 1).factorial : ZMod q)
  have hwil : ((q - 1).factorial : ZMod q) = -1 := ZMod.wilsons_lemma q
  have hm_ne : (m : ZMod q) ≠ 0 := fun h0 =>
    absurd (Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff m q).mp h0)) (not_le_of_gt hmq)
  have hK2_eq : (K : ZMod q) ^ 2 = ((m : ZMod q) ^ 2)⁻¹ := by
    have h1 := hK.2.2
    have h2 : ((m : ZMod q) ^ 2) * (K : ZMod q) ^ 2 = 1 := by
      calc (m : ZMod q) ^ 2 * (K : ZMod q) ^ 2
          = ((m : ZMod q) * (K : ZMod q)) ^ 2 := by ring
        _ = ((-1 : ZMod q) ^ (m - 1)) ^ 2 := by rw [h1]
        _ = ((-1 : ZMod q) ^ 2) ^ (m - 1) := by rw [← pow_mul, mul_comm, pow_mul]
        _ = 1 := by simp
    calc (K : ZMod q) ^ 2 = ((m : ZMod q) ^ 2)⁻¹ * ((m : ZMod q) ^ 2 * (K : ZMod q) ^ 2) := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hm_ne), one_mul]
      _ = ((m : ZMod q) ^ 2)⁻¹ := by rw [h2, mul_one]
  have hK_ne : (K : ZMod q) ≠ 0 := fun h0 => by
    have := hK.2.2; rw [h0, mul_zero] at this
    have hne1 : (-1 : ZMod q) ^ (m - 1) ≠ 0 := pow_ne_zero _ (by simp)
    exact hne1 this.symm
  have hfac_prod : (m.factorial : ZMod q) * ((q - m).factorial : ZMod q) = -(K : ZMod q)⁻¹ := by
    have h1 : (K : ZMod q) * ((m.factorial : ZMod q) * ((q - m).factorial : ZMod q)) = -1 := by
      have hcast : ((K * m.factorial * (q - m).factorial : ℕ) : ZMod q) = ((q - 1).factorial : ZMod q) :=
        congrArg Nat.cast hK.2.1
      push_cast at hcast; rw [hwil] at hcast; linear_combination hcast
    calc (m.factorial : ZMod q) * ((q - m).factorial : ZMod q)
        = (K : ZMod q)⁻¹ * ((K : ZMod q) * ((m.factorial : ZMod q) * ((q - m).factorial : ZMod q))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hK_ne, one_mul]
      _ = (K : ZMod q)⁻¹ * (-1) := by rw [h1]
      _ = -(K : ZMod q)⁻¹ := by ring
  have htr_EF2_cast : ((Matrix.trace ((matE q m * matF q m) ^ 2) : ℤ) : ZMod q) =
      Matrix.trace ((E_q * F_q) ^ 2) := by
    have hmap : ((matE q m * matF q m) ^ 2).map (Int.castRingHom (ZMod q)) = (E_q * F_q) ^ 2 := by
      simp only [sq, Matrix.map_mul, E_q, F_q]
    rw [← hmap]; simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]; push_cast; rfl
  have htr_US4_cast : ((Matrix.trace ((matU q m * matS q m) ^ 4) : ℤ) : ZMod q) =
      Matrix.trace ((U_q * S_q) ^ 4) := by
    have hmap : ((matU q m * matS q m) ^ 4).map (Int.castRingHom (ZMod q)) = (U_q * S_q) ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul, Matrix.map_mul, U_q, S_q]
    rw [← hmap]; simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]; push_cast; rfl
  constructor
  · rw [h610.1, h611.2.2.2.2.1]
    push_cast
    rw [htr_EF2_cast, htr_EF2, hwil]
    calc (-1 : ZMod q) * (m.factorial : ZMod q) * ((q - m).factorial : ZMod q) *
          ((K : ZMod q) * ((K : ZMod q) * -1) ^ 2)
        = (-1 : ZMod q) * ((m.factorial : ZMod q) * ((q - m).factorial : ZMod q)) * (K : ZMod q) ^ 3 := by ring
      _ = (-1 : ZMod q) * (-(K : ZMod q)⁻¹) * (K : ZMod q) ^ 3 := by rw [hfac_prod]
      _ = ((K : ZMod q)⁻¹ * (K : ZMod q)) * (K : ZMod q) ^ 2 := by ring
      _ = (K : ZMod q) ^ 2 := by rw [inv_mul_cancel₀ hK_ne, one_mul]
      _ = ((m : ZMod q) ^ 2)⁻¹ := hK2_eq
  · rw [h611.2.2.2.2.2, htr_US4_cast, htr_US4, hwil]
    simp only [even_two, Even.neg_pow, one_pow, mul_one, show (-1 : ZMod q) ^ 4 = 1 by ring]
    exact hK2_eq

end Prop612Eval

section Theorem61TwoQ

/-! ### Theorem 6.1: Main `q = n / 2` Theorem -/

/-- **Theorem 6.1** (`thm_6_1_twoq`): For every odd prime `q`, `q^2 ∣ D_{2q}`, and for every
prime `q ≥ 5`, `q^3 ∣ D_{2q}`. -/
theorem thm_6_1_twoq (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧
    (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have h69 := prop_6_9_rankone q hq hodd
  refine ⟨h69.2.1, fun hq5 => ?_⟩
  -- Compute `(2 * NB q - NC q : ZMod q) = ∑_{x ≠ 0} x^2`
  have hsum_mod : ((2 * NB q - NC q : ℤ) : ZMod q) = ∑ x : ZMod q, x ^ 2 := by
    unfold NB NC
    push_cast
    have hterm : ∀ m ∈ Finset.Ioo 0 q,
        (2 * (mixedOrbitCountB q m : ZMod q) - (mixedOrbitCountC q m : ZMod q)) =
        ((m : ZMod q) ^ 2)⁻¹ := fun m hm => by
      have h12 := prop_6_12_zeval q m hq hodd (Finset.mem_Ioo.mp hm).1 (Finset.mem_Ioo.mp hm).2
      rw [h12.1, h12.2]; ring
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm]
    -- Re-index `m ∈ Ioo 0 q` to `x ∈ univ.erase 0` via `m ↦ (m : ZMod q)⁻¹`
    have hbij : (∑ m ∈ Finset.Ioo 0 q, ((m : ZMod q) ^ 2)⁻¹) =
        ∑ x ∈ (Finset.univ : Finset (ZMod q)).erase 0, x ^ 2 := by
      refine Finset.sum_bij (fun m _ => (m : ZMod q)⁻¹) ?_ ?_ ?_ ?_
      · intro m hm
        have hm0 := (Finset.mem_Ioo.mp hm).1; have hmq := (Finset.mem_Ioo.mp hm).2
        have hne : (m : ZMod q) ≠ 0 := fun h0 =>
          absurd (Nat.le_of_dvd hm0 ((ZMod.natCast_eq_zero_iff m q).mp h0)) (not_le_of_gt hmq)
        exact Finset.mem_erase.mpr ⟨inv_ne_zero hne, Finset.mem_univ _⟩
      · intro m₁ hm₁ m₂ hm₂ hEq
        have heq := inv_injective hEq
        have hval := congrArg ZMod.val heq
        rwa [ZMod.val_natCast_of_lt (Finset.mem_Ioo.mp hm₁).2,
          ZMod.val_natCast_of_lt (Finset.mem_Ioo.mp hm₂).2] at hval
      · intro x hx
        have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
        have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
        have hpos : 0 < x⁻¹.val := Nat.pos_of_ne_zero fun h => hinv0 ((ZMod.val_eq_zero _).mp h)
        refine ⟨x⁻¹.val, Finset.mem_Ioo.mpr ⟨hpos, x⁻¹.val_lt⟩, ?_⟩
        rw [ZMod.natCast_zmod_val, inv_inv]
      · intro m _; rw [inv_pow]
    rw [hbij, ← Finset.add_sum_erase (Finset.univ : Finset (ZMod q)) (fun x : ZMod q => x ^ 2)
      (Finset.mem_univ 0), zero_pow (by decide), zero_add]
  -- For `q ≥ 5`, `∑ x : ZMod q, x ^ 2 = 0` (scale by `2`, since `2^2 - 1 = 3 ≠ 0` in `ZMod q`!)
  have hsum0 : (∑ x : ZMod q, x ^ 2) = 0 := by
    have h2 : (2 : ZMod q) ≠ 0 := fun h0 => by
      have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h0)
      have := Nat.le_of_dvd (by decide) hdvd; omega
    have h3 : (3 : ZMod q) ≠ 0 := fun h0 => by
      have hdvd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp (by simpa using h0)
      have := Nat.le_of_dvd (by decide) hdvd; omega
    have hscale : (∑ x : ZMod q, ((2 : ZMod q) * x) ^ 2) = ∑ x : ZMod q, x ^ 2 :=
      Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod q) h2) (fun x : ZMod q => x ^ 2)
    have h4 : (4 : ZMod q) * (∑ x : ZMod q, x ^ 2) = ∑ x : ZMod q, x ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ x : ZMod q, (4 : ZMod q) * x ^ 2
          = ∑ x : ZMod q, ((2 : ZMod q) * x) ^ 2 := Finset.sum_congr rfl fun x _ => by ring
        _ = ∑ x : ZMod q, x ^ 2 := hscale
    have h3s : (3 : ZMod q) * (∑ x : ZMod q, x ^ 2) = 0 := by linear_combination h4
    exact (mul_eq_zero.mp h3s).resolve_left h3
  have hcong := (ZMod.intCast_eq_intCast_iff _ _ q).mpr h69.2.2
  rw [hsum_mod, hsum0] at hcong
  push_cast at hcong
  have h2ne : (2 : ZMod q) ≠ 0 := fun h0 => by
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h0)
    have := Nat.le_of_dvd (by decide) hdvd; omega
  have hq_dvd_quot : (q : ℤ) ∣ reducedDelta (2 * q) / (q : ℤ) ^ 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ((mul_eq_zero.mp hcong).resolve_left h2ne)
  rcases hq_dvd_quot with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hD := (Int.mul_ediv_cancel' h69.2.1).symm
  rw [hk] at hD
  calc reducedDelta (2 * q) = (q : ℤ) ^ 2 * ((q : ℤ) * k) := hD
    _ = (q : ℤ) ^ 3 * k := by ring

/-- Exact `q = 3` companion congruence: `D_6 / 9 ≡ 1 (mod 3)` and `¬ 27 ∣ D_6` (so `9 ‖ D_6`). -/
theorem D6_div_9_mod_3 : reducedDelta 6 / 9 ≡ 1 [ZMOD 3] ∧ ¬ ((27 : ℤ) ∣ reducedDelta 6) := by
  have h3 : Nat.Prime 3 := by decide
  have h69 := prop_6_9_rankone 3 h3 (by decide)
  have h1 := prop_6_12_zeval 3 1 h3 (by decide) (by decide) (by decide)
  have h2 := prop_6_12_zeval 3 2 h3 (by decide) (by decide) (by decide)
  have hinv_sum : ((1 : ZMod 3) ^ 2)⁻¹ + ((2 : ZMod 3) ^ 2)⁻¹ = 2 := by
    have h1s : (1 : ZMod 3) ^ 2 = 1 := by decide
    have h2s : (2 : ZMod 3) ^ 2 = 1 := by decide
    rw [h1s, h2s, inv_one]; decide
  have hNB : (NB 3 : ZMod 3) = 2 := by
    unfold NB
    have hI : Finset.Ioo 0 3 = {1, 2} := by decide
    rw [hI]; simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), Int.cast_add, h1.1, h2.1]
    exact hinv_sum
  have hNC : (NC 3 : ZMod 3) = 2 := by
    unfold NC
    have hI : Finset.Ioo 0 3 = {1, 2} := by decide
    rw [hI]; simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), Int.cast_add, h1.2, h2.2]
    exact hinv_sum
  have hcong := (ZMod.intCast_eq_intCast_iff _ _ 3).mpr h69.2.2
  push_cast at hcong
  rw [hNB, hNC] at hcong
  have hq : ((reducedDelta 6 / 9 : ℤ) : ZMod 3) = 1 := by
    have h2' : (2 : ZMod 3) * ((reducedDelta 6 / 9 : ℤ) : ZMod 3) = 2 := by
      rw [hcong]; decide
    have hmul := congrArg ((2 : ZMod 3) * ·) h2'
    have h22 : (2 : ZMod 3) * 2 = 1 := by decide
    rw [← mul_assoc, h22, one_mul] at hmul
    exact hmul
  have hmod : reducedDelta 6 / 9 ≡ 1 [ZMOD 3] :=
    (ZMod.intCast_eq_intCast_iff _ 1 3).mp (by simpa using hq)
  refine ⟨hmod, ?_⟩
  rintro ⟨k, hk⟩
  have hdiv : reducedDelta 6 / 9 = 3 * k := by
    rw [hk, show (27 : ℤ) * k = 9 * (3 * k) by ring, Int.mul_ediv_cancel_left _ (by decide)]
  rw [hdiv] at hq
  have h0 : ((3 * k : ℤ) : ZMod 3) = 0 := by
    push_cast
    have : (3 : ZMod 3) = 0 := by decide
    rw [this, zero_mul]
  rw [h0] at hq
  exact absurd hq (by decide)

end Theorem61TwoQ

end AlonTarsi.Proofs

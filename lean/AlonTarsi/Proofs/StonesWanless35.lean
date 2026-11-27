module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Defs.Basic
public import AlonTarsi.Proofs.LatinBasics
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Direct Proof of Stones–Wanless Theorem 3.5

Proves that for every even `n` and every prime `q` with `n / 2 < q ≤ n - 2`, `q ∣ D_n`,
directly from Lean's standard axioms via a Sylow `q`-subgroup `G ≅ (ZMod q)^3` of `S_n^3`
and a sign-reversing partial column switch on non-free orbits.
-/

namespace AlonTarsi.Proofs

open AlonTarsi

/-- Shift the first `q` indices of `Fin n` cyclically by `a : ZMod q`, fixing indices `≥ q`. -/
private def shiftPrefix {n q : ℕ} [NeZero q] (hqn : q ≤ n) (a : ZMod q) : Equiv.Perm (Fin n) where
  toFun i :=
    if h : i.val < q then
      ⟨(((i.val : ZMod q) + a).val), lt_of_lt_of_le (ZMod.val_lt _) hqn⟩
    else i
  invFun i :=
    if h : i.val < q then
      ⟨(((i.val : ZMod q) - a).val), lt_of_lt_of_le (ZMod.val_lt _) hqn⟩
    else i
  left_inv i := by
    by_cases h : i.val < q
    · have h1 : (((i.val : ZMod q) + a).val) < q := ZMod.val_lt _
      simp only [h, ↓reduceDIte, h1]
      apply Fin.ext
      dsimp
      rw [ZMod.natCast_zmod_val, add_sub_cancel_right, ZMod.val_natCast_of_lt h]
    · simp [h]
  right_inv i := by
    by_cases h : i.val < q
    · have h1 : (((i.val : ZMod q) - a).val) < q := ZMod.val_lt _
      simp only [h, ↓reduceDIte, h1]
      apply Fin.ext
      dsimp
      rw [ZMod.natCast_zmod_val, sub_add_cancel, ZMod.val_natCast_of_lt h]
    · simp [h]

private lemma shiftPrefix_zero {n q : ℕ} [NeZero q] (hqn : q ≤ n) :
    shiftPrefix hqn 0 = 1 := by
  apply Equiv.ext
  intro i
  by_cases h : i.val < q
  · simp only [shiftPrefix, Equiv.coe_fn_mk, h, ↓reduceDIte, add_zero, Equiv.Perm.coe_one, id_eq]
    exact Fin.ext (ZMod.val_natCast_of_lt h)
  · simp [shiftPrefix, h]

private lemma shiftPrefix_add {n q : ℕ} [NeZero q] (hqn : q ≤ n) (a b : ZMod q) :
    shiftPrefix hqn (a + b) = shiftPrefix hqn a * shiftPrefix hqn b := by
  apply Equiv.ext
  intro i
  by_cases h : i.val < q
  · have hb : (((i.val : ZMod q) + b).val) < q := ZMod.val_lt _
    simp only [shiftPrefix, Equiv.Perm.mul_apply, Equiv.coe_fn_mk, h, ↓reduceDIte, hb]
    apply Fin.ext
    dsimp
    rw [ZMod.natCast_zmod_val]
    congr 1
    ring
  · simp [shiftPrefix, h]

private lemma shiftPrefix_eq_one_iff {n q : ℕ} [NeZero q] (hqn : q ≤ n) (a : ZMod q) :
    shiftPrefix hqn a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have h0 : shiftPrefix hqn a ⟨0, lt_of_lt_of_le (NeZero.pos q) hqn⟩ =
        ⟨0, lt_of_lt_of_le (NeZero.pos q) hqn⟩ := by
      simpa using congrArg (fun p : Equiv.Perm (Fin n) =>
        p ⟨0, lt_of_lt_of_le (NeZero.pos q) hqn⟩) h
    simp only [shiftPrefix, Equiv.coe_fn_mk, NeZero.pos q, ↓reduceDIte, Nat.cast_zero, zero_add] at h0
    have hv : a.val = 0 := congrArg Fin.val h0
    exact (ZMod.val_eq_zero a).mp hv
  · rintro rfl; exact shiftPrefix_zero hqn

/-- Homomorphism `Multiplicative (ZMod q × ZMod q × ZMod q) →* Isotopy n`. -/
private def swHom {n q : ℕ} [NeZero q] (hqn : q ≤ n) :
    Multiplicative (ZMod q × ZMod q × ZMod q) →* Isotopy n where
  toFun g :=
    let v := Multiplicative.toAdd g
    (shiftPrefix hqn v.1, shiftPrefix hqn v.2.1, shiftPrefix hqn v.2.2)
  map_one' := by
    change (shiftPrefix hqn 0, shiftPrefix hqn 0, shiftPrefix hqn 0) = (1, 1, 1)
    simp [shiftPrefix_zero]
  map_mul' g₁ g₂ := by
    change (shiftPrefix hqn ((Multiplicative.toAdd g₁).1 + (Multiplicative.toAdd g₂).1),
            shiftPrefix hqn ((Multiplicative.toAdd g₁).2.1 + (Multiplicative.toAdd g₂).2.1),
            shiftPrefix hqn ((Multiplicative.toAdd g₁).2.2 + (Multiplicative.toAdd g₂).2.2)) = _
    simp [shiftPrefix_add, Prod.mk_mul_mk]

/-- Proof of Stones–Wanless Theorem 3.5 directly from Lean's standard axioms. -/
theorem stones_wanless_thm_3_5_proved (n q : ℕ) (heven : Even n) (hq : q.Prime)
    (hlo : n < 2 * q) (hhi : q ≤ n - 2) :
    (q : ℤ) ∣ reducedDelta n := by
  classical
  have hq2 : 2 ≤ q := hq.two_le
  have hqn : q + 2 ≤ n := by omega
  have hqn' : q ≤ n := by omega
  have hq_odd : q ≠ 2 := by
    intro h2; subst h2; omega
  have hq3 : 3 ≤ q := by omega
  have hq_odd' : Odd q := hq.odd_of_ne_two hq_odd
  have : Fact q.Prime := ⟨hq⟩
  let G := Multiplicative (ZMod q × ZMod q × ZMod q)
  letI : MulAction G (LatinSquare n) := MulAction.compHom (LatinSquare n) (swHom hqn')
  have hsmul_entry : ∀ (g : G) (L : LatinSquare n) (r c : Fin n),
      (g • L).entry r c =
        shiftPrefix hqn' (Multiplicative.toAdd g).2.2
          (L.entry ((shiftPrefix hqn' (Multiplicative.toAdd g).1).symm r)
            ((shiftPrefix hqn' (Multiplicative.toAdd g).2.1).symm c)) :=
    fun _ _ _ _ => rfl
  let j1 : Fin n := ⟨q, by omega⟩
  let j2 : Fin n := ⟨q + 1, by omega⟩
  have hj12 : j1 ≠ j2 := by
    intro h
    have hv : j1.val = j2.val := congrArg Fin.val h
    dsimp [j1, j2] at hv
    omega
  have hfix_j1 : ∀ a : ZMod q, shiftPrefix hqn' a j1 = j1 := fun a => by
    simp [shiftPrefix, j1]
  have hfix_j2 : ∀ a : ZMod q, shiftPrefix hqn' a j2 = j2 := fun a => by
    simp [shiftPrefix, j2]
  have hnonfree_maps_W : ∀ L : LatinSquare n, (∃ g : G, g ≠ 1 ∧ g • L = L) →
      (∀ r : Fin n, r.val < q → (L.entry r j1).val < q) ∧
      (∀ r : Fin n, r.val < q → (L.entry r j2).val < q) := by
    intro L ⟨g, hgne, hgfix⟩
    set u := (Multiplicative.toAdd g).1
    set v := (Multiplicative.toAdd g).2.1
    set w := (Multiplicative.toAdd g).2.2
    have hu_ne : u ≠ 0 := by
      intro hu0
      have hw0 : w = 0 := by
        by_contra hwne
        have hfix_all : ∀ s : Fin n, shiftPrefix hqn' w s = s := by
          intro s
          rcases (L.col_bijective j1).2 s with ⟨r, hr⟩
          have hentry := congrArg (fun M : LatinSquare n => M.entry r j1) hgfix
          rw [hsmul_entry] at hentry
          have hj1_symm : (shiftPrefix hqn' v).symm j1 = j1 := by
            apply (shiftPrefix hqn' v).injective
            rw [(shiftPrefix hqn' v).apply_symm_apply, hfix_j1]
          change shiftPrefix hqn' w
            (L.entry ((shiftPrefix hqn' u).symm r) ((shiftPrefix hqn' v).symm j1)) =
            L.entry r j1 at hentry
          simp only [hu0, shiftPrefix_zero, hj1_symm] at hentry
          have h1r : (1 : Equiv.Perm (Fin n)).symm r = r := rfl
          dsimp only at hr
          rw [h1r, hr] at hentry
          exact hentry
        exact hwne ((shiftPrefix_eq_one_iff hqn' w).mp (Equiv.ext hfix_all))
      have hv0 : v = 0 := by
        by_contra hvne
        have hfix_all : ∀ c : Fin n, (shiftPrefix hqn' v).symm c = c := by
          intro c
          let r0 : Fin n := ⟨0, by omega⟩
          have hentry := congrArg (fun M : LatinSquare n => M.entry r0 c) hgfix
          rw [hsmul_entry] at hentry
          change shiftPrefix hqn' w
            (L.entry ((shiftPrefix hqn' u).symm r0) ((shiftPrefix hqn' v).symm c)) =
            L.entry r0 c at hentry
          simp [hu0, hw0, shiftPrefix_zero] at hentry
          exact (L.row_bijective r0).1 hentry
        have hv1 : shiftPrefix hqn' v = 1 := by
          apply Equiv.symm_bijective.injective
          exact Equiv.ext hfix_all
        exact hvne ((shiftPrefix_eq_one_iff hqn' v).mp hv1)
      apply hgne
      apply Multiplicative.toAdd.injective
      exact Prod.ext hu0 (Prod.ext hv0 hw0)
    have hcol_W : ∀ j : Fin n, (∀ a : ZMod q, shiftPrefix hqn' a j = j) →
        ∀ r : Fin n, r.val < q → (L.entry r j).val < q := by
      intro j hfix_j r hr
      by_contra hge
      have hfix_s : shiftPrefix hqn' w (L.entry r j) = L.entry r j := by
        simp [shiftPrefix, hge]
      let r' : Fin n := shiftPrefix hqn' u r
      have hr'_ne : r' ≠ r := by
        intro heq
        have h1 : (((r.val : ZMod q) + u).val) = r.val := by
          have := congrArg Fin.val heq
          simpa [r', shiftPrefix, hr] using this
        have h2 : (r.val : ZMod q) + u = (r.val : ZMod q) := by
          apply ZMod.val_injective q
          rw [h1, ZMod.val_natCast_of_lt hr]
        exact hu_ne (add_left_cancel (a := (r.val : ZMod q)) (by simpa using h2))
      have hentry := congrArg (fun M : LatinSquare n => M.entry r' j) hgfix
      rw [hsmul_entry] at hentry
      change shiftPrefix hqn' w
        (L.entry ((shiftPrefix hqn' u).symm r') ((shiftPrefix hqn' v).symm j)) =
        L.entry r' j at hentry
      have hj_symm : (shiftPrefix hqn' v).symm j = j := by
        apply (shiftPrefix hqn' v).injective
        rw [(shiftPrefix hqn' v).apply_symm_apply, hfix_j]
      rw [hj_symm] at hentry
      have hr'_symm : (shiftPrefix hqn' u).symm r' = r := (shiftPrefix hqn' u).symm_apply_apply r
      rw [hr'_symm, hfix_s] at hentry
      exact hr'_ne ((L.col_bijective j).1 hentry.symm)
    exact ⟨hcol_W j1 hfix_j1, hcol_W j2 hfix_j2⟩
  let NonFree (L : LatinSquare n) : Prop := ∃ g : G, g ≠ 1 ∧ g • L = L
  have hcol_surj_W : ∀ (L : LatinSquare n) (j : Fin n),
      (∀ r : Fin n, r.val < q → (L.entry r j).val < q) →
      ∀ s : Fin n, s.val < q → ∃ r : Fin n, r.val < q ∧ L.entry r j = s := by
    intro L j hW s hs
    let U : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < q)
    have hsub : U.image (fun r => L.entry r j) ⊆ U := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW r (Finset.mem_filter.mp hr).2⟩
    have hcard_eq : (U.image (fun r => L.entry r j)).card = U.card :=
      Finset.card_image_of_injective U (L.col_bijective j).1
    have heq_set : U.image (fun r => L.entry r j) = U :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
    have hsU : s ∈ U.image (fun r => L.entry r j) := by
      rw [heq_set]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    rcases Finset.mem_image.mp hsU with ⟨r, hr, hrs⟩
    exact ⟨r, (Finset.mem_filter.mp hr).2, hrs⟩
  let switchEntry (L : LatinSquare n) (r c : Fin n) : Fin n :=
    if r.val < q then L.entry r (Equiv.swap j1 j2 c) else L.entry r c
  have hswitch_latin : ∀ L : LatinSquare n, NonFree L →
      (∀ r, Function.Bijective (fun c => switchEntry L r c)) ∧
      (∀ c, Function.Bijective (fun r => switchEntry L r c)) := by
    intro L hnf
    have hW := hnonfree_maps_W L hnf
    refine ⟨fun r => ?_, fun c => ?_⟩
    · by_cases hr : r.val < q
      · simpa [switchEntry, hr] using (L.row_bijective r).comp (Equiv.swap j1 j2).bijective
      · simpa [switchEntry, hr] using L.row_bijective r
    · rw [← Finite.injective_iff_bijective]
      intro r₁ r₂ heq
      by_cases hc1 : c = j1
      · subst hc1
        simp only [switchEntry, Equiv.swap_apply_left] at heq
        by_cases h1 : r₁.val < q <;> by_cases h2 : r₂.val < q
        · simp only [h1, h2, ↓reduceIte] at heq
          exact (L.col_bijective j2).1 heq
        · simp only [h1, h2, ↓reduceIte] at heq
          have hlt : (L.entry r₂ j1).val < q := heq ▸ hW.2 r₁ h1
          rcases hcol_surj_W L j1 hW.1 (L.entry r₂ j1) hlt with ⟨r', hr', hr'eq⟩
          have : r' = r₂ := (L.col_bijective j1).1 hr'eq
          exact absurd (this ▸ hr') h2
        · simp only [h1, h2, ↓reduceIte] at heq
          have hlt : (L.entry r₁ j1).val < q := heq.symm ▸ hW.2 r₂ h2
          rcases hcol_surj_W L j1 hW.1 (L.entry r₁ j1) hlt with ⟨r', hr', hr'eq⟩
          have : r' = r₁ := (L.col_bijective j1).1 hr'eq
          exact absurd (this ▸ hr') h1
        · simp only [h1, h2, ↓reduceIte] at heq
          exact (L.col_bijective j1).1 heq
      · by_cases hc2 : c = j2
        · subst hc2
          simp only [switchEntry, Equiv.swap_apply_right] at heq
          by_cases h1 : r₁.val < q <;> by_cases h2 : r₂.val < q
          · simp only [h1, h2, ↓reduceIte] at heq
            exact (L.col_bijective j1).1 heq
          · simp only [h1, h2, ↓reduceIte] at heq
            have hlt : (L.entry r₂ j2).val < q := heq ▸ hW.1 r₁ h1
            rcases hcol_surj_W L j2 hW.2 (L.entry r₂ j2) hlt with ⟨r', hr', hr'eq⟩
            have : r' = r₂ := (L.col_bijective j2).1 hr'eq
            exact absurd (this ▸ hr') h2
          · simp only [h1, h2, ↓reduceIte] at heq
            have hlt : (L.entry r₁ j2).val < q := heq.symm ▸ hW.1 r₂ h2
            rcases hcol_surj_W L j2 hW.2 (L.entry r₁ j2) hlt with ⟨r', hr', hr'eq⟩
            have : r' = r₁ := (L.col_bijective j2).1 hr'eq
            exact absurd (this ▸ hr') h1
          · simp only [h1, h2, ↓reduceIte] at heq
            exact (L.col_bijective j2).1 heq
        · simp only [switchEntry, Equiv.swap_apply_of_ne_of_ne hc1 hc2, ite_self] at heq
          exact (L.col_bijective c).1 heq
  let Φ (L : { L : LatinSquare n // NonFree L }) : LatinSquare n :=
    ⟨switchEntry L.1, (hswitch_latin L.1 L.2).1, (hswitch_latin L.1 L.2).2⟩
  have hΦ_comm : ∀ (g : G) (L : { L : LatinSquare n // NonFree L }),
      (g • Φ L).entry = switchEntry (g • L.1) := by
    intro g L
    set u := (Multiplicative.toAdd g).1
    set v := (Multiplicative.toAdd g).2.1
    set w := (Multiplicative.toAdd g).2.2
    funext r c
    rw [hsmul_entry]
    change shiftPrefix hqn' w
      (switchEntry L.1 ((shiftPrefix hqn' u).symm r) ((shiftPrefix hqn' v).symm c)) =
      switchEntry (g • L.1) r c
    have hlt_iff : ((shiftPrefix hqn' u).symm r).val < q ↔ r.val < q := by
      by_cases h : r.val < q
      · simp [shiftPrefix, h, ZMod.val_lt]
      · simp [shiftPrefix, h]
    have hswap_comm : (shiftPrefix hqn' v).symm (Equiv.swap j1 j2 c) =
        Equiv.swap j1 j2 ((shiftPrefix hqn' v).symm c) := by
      have hj1s : (shiftPrefix hqn' v).symm j1 = j1 := by
        apply (shiftPrefix hqn' v).injective; rw [(shiftPrefix hqn' v).apply_symm_apply, hfix_j1]
      have hj2s : (shiftPrefix hqn' v).symm j2 = j2 := by
        apply (shiftPrefix hqn' v).injective; rw [(shiftPrefix hqn' v).apply_symm_apply, hfix_j2]
      by_cases hc1 : c = j1
      · subst hc1; simp [hj1s, hj2s]
      · by_cases hc2 : c = j2
        · subst hc2; simp [hj1s, hj2s]
        · have hs1 : (shiftPrefix hqn' v).symm c ≠ j1 := fun h =>
            hc1 (by have := congrArg (shiftPrefix hqn' v) h; simpa [hfix_j1] using this)
          have hs2 : (shiftPrefix hqn' v).symm c ≠ j2 := fun h =>
            hc2 (by have := congrArg (shiftPrefix hqn' v) h; simpa [hfix_j2] using this)
          simp [Equiv.swap_apply_of_ne_of_ne hc1 hc2, Equiv.swap_apply_of_ne_of_ne hs1 hs2]
    dsimp only [switchEntry]
    by_cases hr : r.val < q
    · have hr' : ((shiftPrefix hqn' u).symm r).val < q := hlt_iff.mpr hr
      simp only [hr, hr', ↓reduceIte]
      rw [hsmul_entry]
      change shiftPrefix hqn' w
        (L.1.entry ((shiftPrefix hqn' u).symm r) (Equiv.swap j1 j2 ((shiftPrefix hqn' v).symm c))) =
        shiftPrefix hqn' w
        (L.1.entry ((shiftPrefix hqn' u).symm r) ((shiftPrefix hqn' v).symm (Equiv.swap j1 j2 c)))
      rw [hswap_comm]
    · have hr' : ¬ ((shiftPrefix hqn' u).symm r).val < q := fun h => hr (hlt_iff.mp h)
      simp only [hr, hr', ↓reduceIte]
      rw [hsmul_entry]
  have hΦ_nonfree : ∀ L : { L : LatinSquare n // NonFree L }, NonFree (Φ L) := by
    intro L
    rcases L.2 with ⟨g, hgne, hgfix⟩
    refine ⟨g, hgne, ?_⟩
    apply LatinSquare.ext
    rw [hΦ_comm, hgfix]
  have hΦ_inv : ∀ L : { L : LatinSquare n // NonFree L },
      Φ ⟨Φ L, hΦ_nonfree L⟩ = L.1 := by
    intro L
    apply LatinSquare.ext
    funext r c
    change switchEntry (Φ L) r c = L.1.entry r c
    by_cases hr : r.val < q
    · simp [switchEntry, Φ, hr]
    · simp [switchEntry, Φ, hr]
  have hΦ_sign : ∀ L : { L : LatinSquare n // NonFree L },
      squareSign (Φ L) = -squareSign L.1 := by
    intro L
    have hrow : rowSign (Φ L) = -rowSign L.1 := by
      unfold rowSign
      have hterm : ∀ r : Fin n, Equiv.Perm.sign (rowPerm (Φ L) r) =
          Equiv.Perm.sign (rowPerm L.1 r) * (if r.val < q then (-1 : ℤˣ) else 1) := by
        intro r
        by_cases hr : r.val < q
        · have heq : rowPerm (Φ L) r = rowPerm L.1 r * Equiv.swap j1 j2 := by
            apply Equiv.ext; intro c; simp [rowPerm, Φ, switchEntry, hr]
          simp [heq, Equiv.Perm.sign_swap hj12, hr]
        · have heq : rowPerm (Φ L) r = rowPerm L.1 r := by
            apply Equiv.ext; intro c; simp [rowPerm, Φ, switchEntry, hr]
          simp [heq, hr]
      simp_rw [hterm]
      rw [Finset.prod_mul_distrib]
      have hU : (Finset.univ.filter (fun r : Fin n => r.val < q)).card = q := by
        have hbi : (Finset.univ.filter (fun r : Fin n => r.val < q)).card = Fintype.card (Fin q) := by
          refine Finset.card_bij (fun r hr => (⟨r.val, (Finset.mem_filter.mp hr).2⟩ : Fin q)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro r₁ _ r₂ _ h
            have hv : r₁.val = r₂.val := congrArg (Fin.val (n := q)) h
            exact Fin.ext hv
          · intro i _; exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hqn'⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
        rw [hbi, Fintype.card_fin]
      have hprod_neg : (∏ r : Fin n, if r.val < q then (-1 : ℤˣ) else 1) = -1 := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hU]
        rcases hq_odd' with ⟨k, rfl⟩
        rw [pow_succ, pow_mul]; norm_num
      rw [hprod_neg]
      simp
    have hcol : colSign (Φ L) = colSign L.1 := by
      let π : Equiv.Perm (Fin n) := (colPerm L.1 j1)⁻¹ * colPerm (Φ L) j1
      have hcol1 : colPerm (Φ L) j1 = colPerm L.1 j1 * π := by
        simp [π]
      have hcol2 : colPerm (Φ L) j2 = colPerm L.1 j2 * π⁻¹ := by
        apply Equiv.ext
        intro r
        by_cases hr : r.val < q
        · have h1 : colPerm (Φ L) j2 r = L.1.entry r j1 := by
            simp [colPerm, Φ, switchEntry, hr]
          rw [h1]
          change L.1.entry r j1 = L.1.entry (π⁻¹ r) j2
          have hπir_eq : colPerm (Φ L) j1 (π⁻¹ r) = L.1.entry r j1 := by
            have : (colPerm (Φ L) j1 * π⁻¹) r = colPerm L.1 j1 r := by
              rw [hcol1, mul_assoc, mul_inv_cancel, mul_one]
            exact this
          have hr'eq : switchEntry L.1 (π⁻¹ r) j1 = L.1.entry r j1 := hπir_eq
          have hr'lt : (π⁻¹ r).val < q := by
            by_contra hge
            simp only [switchEntry, hge, ↓reduceIte] at hr'eq
            have heq_r : π⁻¹ r = r := (L.1.col_bijective j1).1 hr'eq
            rw [heq_r] at hge
            exact hge hr
          simp only [switchEntry, hr'lt, ↓reduceIte, Equiv.swap_apply_left] at hr'eq
          exact hr'eq.symm
        · have h1 : colPerm (Φ L) j2 r = L.1.entry r j2 := by
            simp [colPerm, Φ, switchEntry, hr]
          have hπr : π r = r := by
            change (colPerm L.1 j1).symm (switchEntry L.1 r j1) = r
            simp only [switchEntry, hr, ↓reduceIte]
            exact (colPerm L.1 j1).symm_apply_apply r
          have hπir : π⁻¹ r = r := by
            apply π.injective
            change (π * π⁻¹) r = π r
            rw [mul_inv_cancel, hπr]
            rfl
          rw [h1]
          change L.1.entry r j2 = L.1.entry (π⁻¹ r) j2
          rw [hπir]
      have hpair_sign :
          Equiv.Perm.sign (colPerm (Φ L) j1) * Equiv.Perm.sign (colPerm (Φ L) j2) =
          Equiv.Perm.sign (colPerm L.1 j1) * Equiv.Perm.sign (colPerm L.1 j2) := by
        have haux : ∀ a b p : Equiv.Perm (Fin n),
            Equiv.Perm.sign (a * p) * Equiv.Perm.sign (b * p⁻¹) =
            Equiv.Perm.sign a * Equiv.Perm.sign b := by
          intro a b p
          rw [map_mul, map_mul, map_inv, Int.units_inv_eq_self]
          rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
        exact (congrArg₂ (· * ·) (congrArg Equiv.Perm.sign hcol1)
          (congrArg Equiv.Perm.sign hcol2)).trans (haux _ _ π)
      have hother : ∀ c : Fin n, c ≠ j1 → c ≠ j2 → colPerm (Φ L) c = colPerm L.1 c := by
        intro c hc1 hc2
        apply Equiv.ext; intro r
        simp [colPerm, Φ, switchEntry, Equiv.swap_apply_of_ne_of_ne hc1 hc2]
      unfold colSign
      have hj12_mem : j1 ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j1
      have hj2_mem : j2 ∈ (Finset.univ : Finset (Fin n)).erase j1 :=
        Finset.mem_erase.mpr ⟨hj12.symm, Finset.mem_univ j2⟩
      rw [← Finset.mul_prod_erase _ _ hj12_mem, ← Finset.mul_prod_erase _ _ hj2_mem]
      conv_rhs =>
        rw [← Finset.mul_prod_erase _ _ hj12_mem, ← Finset.mul_prod_erase _ _ hj2_mem]
      have hrest :
          (∏ c ∈ ((Finset.univ : Finset (Fin n)).erase j1).erase j2,
            Equiv.Perm.sign (colPerm (Φ L) c)) =
          (∏ c ∈ ((Finset.univ : Finset (Fin n)).erase j1).erase j2,
            Equiv.Perm.sign (colPerm L.1 c)) := by
        refine Finset.prod_congr rfl fun c hc => ?_
        have hc2 : c ≠ j2 := (Finset.mem_erase.mp hc).1
        have hc1 : c ≠ j1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
        rw [hother c hc1 hc2]
      rw [hrest, ← mul_assoc, hpair_sign, mul_assoc]
    unfold squareSign
    rw [hrow, hcol]
    simp
  have hsum_nonfree :
      (∑ L ∈ Finset.univ.filter NonFree, (squareSign L : ℤ)) = 0 := by
    have hbij :
        (∑ L ∈ Finset.univ.filter NonFree, (squareSign L : ℤ)) =
        ∑ L ∈ Finset.univ.filter NonFree, -(squareSign L : ℤ) := by
      refine Finset.sum_bij (fun L hL => Φ ⟨L, (Finset.mem_filter.mp hL).2⟩) ?_ ?_ ?_ ?_
      · intro L hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hΦ_nonfree ⟨L, (Finset.mem_filter.mp hL).2⟩⟩
      · intro L₁ hL₁ L₂ hL₂ heq
        have h1 := congrArg (fun M : LatinSquare n => switchEntry M) heq
        have hinv1 := hΦ_inv ⟨L₁, (Finset.mem_filter.mp hL₁).2⟩
        have hinv2 := hΦ_inv ⟨L₂, (Finset.mem_filter.mp hL₂).2⟩
        calc L₁ = Φ ⟨Φ ⟨L₁, (Finset.mem_filter.mp hL₁).2⟩, hΦ_nonfree _⟩ := hinv1.symm
          _ = Φ ⟨Φ ⟨L₂, (Finset.mem_filter.mp hL₂).2⟩, hΦ_nonfree _⟩ := by
            apply LatinSquare.ext; exact h1
          _ = L₂ := hinv2
      · intro L hL
        refine ⟨Φ ⟨L, (Finset.mem_filter.mp hL).2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hΦ_nonfree _⟩,
          hΦ_inv ⟨L, (Finset.mem_filter.mp hL).2⟩⟩
      · intro L hL
        have hs := congrArg Units.val (hΦ_sign ⟨L, (Finset.mem_filter.mp hL).2⟩)
        change (squareSign (Φ ⟨L, (Finset.mem_filter.mp hL).2⟩) : ℤ) = -(squareSign L : ℤ) at hs
        linarith
    rw [Finset.sum_neg_distrib] at hbij
    linarith
  have hsum_free_dvd :
      ((q : ℤ) ^ 3) ∣ ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => ¬ NonFree L),
        (squareSign L : ℤ) := by
    let FreeSq := { L : LatinSquare n // ¬ NonFree L }
    have hsmul_free : ∀ (g : G) (L : FreeSq), ¬ NonFree (g • L.1) := by
      intro g L ⟨h, hne, hfix⟩
      apply L.2
      refine ⟨h, hne, ?_⟩
      have h1 : g • (h • L.1) = g • L.1 := by
        rw [← mul_smul, mul_comm g h, mul_smul, hfix]
      have h2 := congrArg (g⁻¹ • ·) h1
      simpa [inv_smul_smul] using h2
    letI : MulAction G FreeSq :=
      { smul := fun g L => ⟨g • L.1, hsmul_free g L⟩
        one_smul := fun L => Subtype.ext (one_smul G L.1)
        mul_smul := fun g₁ g₂ L => Subtype.ext (mul_smul g₁ g₂ L.1) }
    have hcardG : Fintype.card G = q ^ 3 := by
      change Fintype.card (Multiplicative (ZMod q × ZMod q × ZMod q)) = q ^ 3
      rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod, Fintype.card_prod, ZMod.card]
      ring
    let orbRel := MulAction.orbitRel G FreeSq
    have hsum_eq :
        (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => ¬ NonFree L), (squareSign L : ℤ)) =
        ∑ L : FreeSq, (squareSign L.1 : ℤ) := by
      let s := Finset.univ.filter (fun L : LatinSquare n => ¬ NonFree L)
      change (∑ L ∈ s, (squareSign L : ℤ)) = ∑ L : FreeSq, (squareSign L.1 : ℤ)
      rw [← Finset.sum_coe_sort s]
      let eF : { L : LatinSquare n // L ∈ s } ≃ FreeSq :=
        Equiv.subtypeEquivRight (fun L => by simp [s])
      exact Fintype.sum_equiv eF (fun L => (squareSign L.1 : ℤ))
        (fun L => (squareSign L.1 : ℤ)) (fun _ => rfl)
    rw [hsum_eq]
    have hpart :
        (∑ L : FreeSq, (squareSign L.1 : ℤ)) =
        ∑ o : Quotient orbRel,
          ∑ L ∈ Finset.univ.filter (fun L : FreeSq => Quotient.mk orbRel L = o),
            (squareSign L.1 : ℤ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk orbRel) (fun _ _ => Finset.mem_univ _)]
    rw [hpart]
    refine Finset.dvd_sum fun o _ => ?_
    let L₀ : FreeSq := Quotient.out o
    have hfib_card :
        (Finset.univ.filter (fun L : FreeSq => Quotient.mk orbRel L = o)).card = q ^ 3 := by
      rw [← hcardG]
      refine Finset.card_bij
        (fun L hL => Classical.choose (Quotient.exact
          (show Quotient.mk orbRel L = Quotient.mk orbRel L₀ by
            rw [Quotient.out_eq]; exact (Finset.mem_filter.mp hL).2))) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro L₁ hL₁ L₂ hL₂ h
        have h1 : Quotient.mk orbRel L₁ = Quotient.mk orbRel L₀ := by
          rw [Quotient.out_eq]; exact (Finset.mem_filter.mp hL₁).2
        have h2 : Quotient.mk orbRel L₂ = Quotient.mk orbRel L₀ := by
          rw [Quotient.out_eq]; exact (Finset.mem_filter.mp hL₂).2
        have hc1 : (Classical.choose (Quotient.exact h1)) • L₀ = L₁ :=
          Classical.choose_spec (Quotient.exact h1)
        have hc2 : (Classical.choose (Quotient.exact h2)) • L₀ = L₂ :=
          Classical.choose_spec (Quotient.exact h2)
        rw [← hc1, ← hc2, h]
      · intro g _
        refine ⟨g • L₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [← Quotient.out_eq o]
          exact Quotient.sound ⟨g, rfl⟩
        · have hm : Quotient.mk orbRel (g • L₀) = Quotient.mk orbRel L₀ :=
            Quotient.sound ⟨g, rfl⟩
          have hc : (Classical.choose (Quotient.exact hm)) • L₀ = g • L₀ :=
            Classical.choose_spec (Quotient.exact hm)
          have hval : (Classical.choose (Quotient.exact hm)) • L₀.1 = g • L₀.1 :=
            congrArg Subtype.val hc
          have heq1 : (g⁻¹ * Classical.choose (Quotient.exact hm)) • L₀.1 = L₀.1 := by
            rw [mul_smul, hval, inv_smul_smul]
          by_contra hne
          apply L₀.2
          refine ⟨g⁻¹ * Classical.choose (Quotient.exact hm), ?_, heq1⟩
          intro h1
          apply hne
          calc Classical.choose (Quotient.exact hm)
              = g * (g⁻¹ * Classical.choose (Quotient.exact hm)) := by simp
            _ = g := by rw [h1, mul_one]
    have hconst : ∀ L ∈ Finset.univ.filter (fun L : FreeSq => Quotient.mk orbRel L = o),
        (squareSign L.1 : ℤ) = (squareSign L₀.1 : ℤ) := by
      intro L hL
      have hm : Quotient.mk orbRel L = Quotient.mk orbRel L₀ := by
        rw [Quotient.out_eq]; exact (Finset.mem_filter.mp hL).2
      rcases Quotient.exact hm with ⟨g, hg⟩
      have hg1 : g • L₀.1 = L.1 := congrArg Subtype.val hg
      rw [← hg1]
      exact congrArg Units.val ((eq_isotopy_proved n (swHom hqn' g) L₀.1).2.2 heven)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hfib_card, nsmul_eq_mul]
    push_cast
    exact dvd_mul_right ((q : ℤ) ^ 3) _
  have hdelta_dvd : ((q : ℤ) ^ 3) ∣ delta n := by
    rw [delta_eq_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ NonFree,
      hsum_nonfree, zero_add]
    exact hsum_free_dvd
  rw [eq_normal_proved n heven] at hdelta_dvd
  have hlt_sq : n < q ^ 2 := by nlinarith
  have hval_fact : padicValNat q n.factorial = 1 := by
    rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by omega) hlt_sq)]
    have h1 : Finset.Ico 1 2 = {1} := by decide
    rw [h1, Finset.sum_singleton, pow_one]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hval_pred : padicValNat q (n - 1).factorial = 1 := by
    rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by omega) (by omega : n - 1 < q ^ 2))]
    have h1 : Finset.Ico 1 2 = {1} := by decide
    rw [h1, Finset.sum_singleton, pow_one]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hval_prod : padicValNat q (n.factorial * (n - 1).factorial) = 2 := by
    rw [padicValNat.mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1)),
      hval_fact, hval_pred]
  have hndvd3 : ¬ (q ^ 3 ∣ n.factorial * (n - 1).factorial) := by
    intro hd
    have hle := (padicValNat_dvd_iff_le
      (Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1)))).mp hd
    omega
  have h2dvd : q ^ 2 ∣ n.factorial * (n - 1).factorial := by
    rw [← hval_prod]; exact pow_padicValNat_dvd
  rcases h2dvd with ⟨k, hk⟩
  have hq_ndvd_k : ¬ (q ∣ k) := by
    rintro ⟨m, rfl⟩
    apply hndvd3
    exact ⟨m, by rw [hk]; ring⟩
  have hd_k : (q : ℤ) ∣ (k : ℤ) * reducedDelta n := by
    rw [hk] at hdelta_dvd
    push_cast at hdelta_dvd
    rcases hdelta_dvd with ⟨m, hm⟩
    have hq2_ne : ((q : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hq.ne_zero)
    refine ⟨m, ?_⟩
    apply mul_left_cancel₀ hq2_ne
    calc (q : ℤ) ^ 2 * ((k : ℤ) * reducedDelta n)
        = (q : ℤ) ^ 2 * (k : ℤ) * reducedDelta n := by ring
      _ = (q : ℤ) ^ 3 * m := hm
      _ = (q : ℤ) ^ 2 * ((q : ℤ) * m) := by ring
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  exact (hprime_int.dvd_or_dvd hd_k).resolve_left (fun h => hq_ndvd_k (Int.natCast_dvd_natCast.mp h))

end AlonTarsi.Proofs

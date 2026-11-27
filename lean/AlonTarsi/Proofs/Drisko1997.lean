/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Defs.Basic
import AlonTarsi.Defs.TwoQ
import AlonTarsi.Proofs.LatinBasics
import AlonTarsi.Proofs.SylowMid
import AlonTarsi.Proofs.TwoQMobius
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Self-Contained Proof of Drisko (1997)

Proves Drisko's congruence directly from Lean's standard axioms alone (using `lem_6_5_complete`
from `TwoQMobius.lean`):
For every odd prime `p`, `Δ_{p+1} ≡ (-1)^((p+1)/2) * p^2 [ZMOD p^3]`.
-/

namespace AlonTarsi.Proofs

open AlonTarsi
open scoped BigOperators

/-- Equivalence between `Fin (p + 1)` and `Option (ZMod p)` (`Fin.last p ↔ none`,
`Fin.castSucc i ↔ some i`). -/
private def finSuccEquivOption (p : ℕ) [NeZero p] : Fin (p + 1) ≃ Option (ZMod p) :=
  (finSuccEquivLast p).trans
    { toFun := fun s => match s with
        | Sum.inl i => some (ZMod.finEquiv p i)
        | Sum.inr () => none
      invFun := fun o => match o with
        | some x => Sum.inl ((ZMod.finEquiv p).symm x)
        | none => Sum.inr ()
      left_inv := fun s => by rcases s with i | ⟨⟩ <;> simp
      right_inv := fun o => by rcases o with _ | x <;> simp }
where
  finSuccEquivLast (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
    { toFun := fun i =>
        if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr ()
      invFun := fun s => match s with
        | Sum.inl j => ⟨j.val, by omega⟩
        | Sum.inr () => ⟨n, by omega⟩
      left_inv := fun i => by
        by_cases h : i.val < n
        · simp [h]
        · have hi : i.val = n := by have := i.isLt; omega
          simp [h]
          exact Fin.ext hi.symm
      right_inv := fun s => by
        rcases s with j | ⟨⟩
        · simp [j.isLt]
        · simp }

/-- Lift a permutation of `ZMod p` to `Fin (p + 1)` fixing the last element. -/
private def liftZModPerm (p : ℕ) [NeZero p] (π : Equiv.Perm (ZMod p)) :
    Equiv.Perm (Fin (p + 1)) :=
  (finSuccEquivOption p).symm.permCongr
    { toFun := fun o => o.map π
      invFun := fun o => o.map π.symm
      left_inv := fun o => by cases o <;> simp
      right_inv := fun o => by cases o <;> simp }

private lemma liftZModPerm_mul (p : ℕ) [NeZero p] (π₁ π₂ : Equiv.Perm (ZMod p)) :
    liftZModPerm p (π₁ * π₂) = liftZModPerm p π₁ * liftZModPerm p π₂ := by
  apply Equiv.ext; intro i
  unfold liftZModPerm
  simp only [Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.coe_fn_mk,
    Equiv.apply_symm_apply]
  cases finSuccEquivOption p i <;> rfl

private lemma liftZModPerm_one (p : ℕ) [NeZero p] :
    liftZModPerm p 1 = 1 := by
  apply Equiv.ext; intro i
  unfold liftZModPerm
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.coe_fn_mk, Equiv.Perm.coe_one]
  cases h : finSuccEquivOption p i with
  | none =>
    change (finSuccEquivOption p).symm none = i
    rw [← h, (finSuccEquivOption p).symm_apply_apply]
  | some x =>
    change (finSuccEquivOption p).symm (some x) = i
    rw [← h, (finSuccEquivOption p).symm_apply_apply]

private lemma sign_liftZModPerm (p : ℕ) [NeZero p] (π : Equiv.Perm (ZMod p)) :
    Equiv.Perm.sign (liftZModPerm p π) = Equiv.Perm.sign π := by
  unfold liftZModPerm
  rw [Equiv.Perm.sign_permCongr]
  let emb : ZMod p ↪ Option (ZMod p) := ⟨Option.some, Option.some_injective _⟩
  let e : ZMod p ≃ Set.range emb := Equiv.ofInjective emb emb.injective
  have heq :
      ({ toFun := fun o : Option (ZMod p) => o.map π
         invFun := fun o => o.map π.symm
         left_inv := fun o => by cases o <;> simp
         right_inv := fun o => by cases o <;> simp } : Equiv.Perm (Option (ZMod p))) =
      π.extendDomain e := by
    apply Equiv.ext; intro o
    cases o with
    | none =>
      have hnot : (none : Option (ZMod p)) ∉ Set.range emb := by
        rintro ⟨x, hx⟩; cases hx
      rw [Equiv.Perm.extendDomain_apply_not_subtype π e hnot]
      rfl
    | some x =>
      have h1 : π.extendDomain e (some x) = (e (π x)).1 :=
        Equiv.Perm.extendDomain_apply_image π e x
      rw [h1]; rfl
  rw [heq, Equiv.Perm.sign_extendDomain]

/-- Sign of `x ↦ -x` on `ZMod p` for odd prime `p` is `(-1)^((p - 1) / 2)`. -/
private lemma sign_neg_zmod (p : ℕ) [NeZero p] (hp : p.Prime) (hodd : p ≠ 2) :
    Equiv.Perm.sign (Equiv.neg (ZMod p)) = (-1 : ℤˣ) ^ ((p - 1) / 2) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let half : Finset (ZMod p) := Finset.univ.filter fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p
  have hneg_val : ∀ x : ZMod p, x ≠ 0 → (-x).val = p - x.val := by
    intro x hx
    have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h =>
      hx (by rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero])
    have hpos' : 0 < (-x).val := Nat.pos_of_ne_zero fun h =>
      (neg_ne_zero.mpr hx) (by rw [← ZMod.natCast_zmod_val (-x), h, Nat.cast_zero])
    have hsum : ((-x).val + x.val) % p = 0 := by
      rw [← ZMod.val_add, neg_add_cancel, ZMod.val_zero]
    have hlt1 : x.val < p := x.val_lt
    have hlt2 : (-x).val < p := (-x).val_lt
    rcases Nat.dvd_of_mod_eq_zero hsum with ⟨k, hk⟩
    rcases k with _ | _ | k
    · omega
    · omega
    · have : 2 * p ≤ p * (k + 1 + 1) := by nlinarith
      omega
  have hcard : half.card = (p - 1) / 2 := by
    have hbi : half.card = Fintype.card (Fin ((p - 1) / 2)) := by
      refine Finset.card_bij (fun x hx => ⟨x.val - 1, by
          have h := (Finset.mem_filter.mp hx).2; omega⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro x₁ hx₁ x₂ hx₂ heq
        have h1 := (Finset.mem_filter.mp hx₁).2
        have h2 := (Finset.mem_filter.mp hx₂).2
        have hv : x₁.val = x₂.val := by
          have := congrArg Fin.val heq; dsimp at this; omega
        exact ZMod.val_injective p hv
      · intro j _
        have hjlt : j.val + 1 < p := by have := j.isLt; omega
        refine ⟨((j.val + 1 : ℕ) : ZMod p), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]; omega
          · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]
            have := j.isLt
            rcases hp.odd_of_ne_two hodd with ⟨k, hk⟩
            omega
        · apply Fin.ext; dsimp
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]; omega
    rw [hbi, Fintype.card_fin]
  let swapOn : Finset (ZMod p) → Equiv.Perm (ZMod p) := fun s =>
    { toFun := fun x => if x ∈ s ∨ -x ∈ s then -x else x
      invFun := fun x => if x ∈ s ∨ -x ∈ s then -x else x
      left_inv := fun x => by dsimp; split_ifs with h1 h2 <;> simp_all [or_comm]
      right_inv := fun x => by dsimp; split_ifs with h1 h2 <;> simp_all [or_comm] }
  have hsub : ∀ s : Finset (ZMod p), s ⊆ half →
      Equiv.Perm.sign (swapOn s) = (-1 : ℤˣ) ^ s.card := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
      have h1 : swapOn ∅ = 1 := by apply Equiv.ext; intro x; simp [swapOn]
      rw [h1, map_one, Finset.card_empty, pow_zero]
    | @insert a s ha ih =>
      have hs' : s ⊆ half := fun x hx => hs (Finset.mem_insert_of_mem hx)
      have ha_mem : a ∈ half := hs (Finset.mem_insert_self a s)
      have ha_prop := (Finset.mem_filter.mp ha_mem).2
      have ha_ne0 : a ≠ 0 := fun h => by rw [h, ZMod.val_zero] at ha_prop; omega
      have ha_ne_neg : a ≠ -a := fun h => by
        have hv := hneg_val a ha_ne0
        have := congrArg ZMod.val h
        omega
      have hneg_not_half : -a ∉ half := by
        intro hm
        have h2 := (Finset.mem_filter.mp hm).2
        have hv := hneg_val a ha_ne0
        omega
      have hmul : swapOn (insert a s) = Equiv.swap a (-a) * swapOn s := by
        apply Equiv.ext; intro x
        change (if x ∈ insert a s ∨ -x ∈ insert a s then -x else x) =
          Equiv.swap a (-a) (if x ∈ s ∨ -x ∈ s then -x else x)
        by_cases hxa : x = a
        · subst hxa
          have hnot : ¬ (x ∈ s ∨ -x ∈ s) := by
            rintro (h | h)
            · exact ha h
            · exact hneg_not_half (hs' h)
          simp [hnot]
        · by_cases hxa' : x = -a
          · subst hxa'
            have hnot : ¬ (-a ∈ s ∨ a ∈ s) := by
              rintro (h | h)
              · exact hneg_not_half (hs' h)
              · exact ha h
            simp [hnot]
          · have hneg_ne1 : -x ≠ a := fun h => hxa' (by rw [← h, neg_neg])
            have hneg_ne2 : -x ≠ -a := fun h => hxa (neg_inj.mp h)
            by_cases hxs : x ∈ s ∨ -x ∈ s
            · have hmem : x ∈ insert a s ∨ -x ∈ insert a s :=
                hxs.imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
              rw [if_pos hmem, if_pos hxs, Equiv.swap_apply_of_ne_of_ne hneg_ne1 hneg_ne2]
            · have hnot : ¬ (x ∈ insert a s ∨ -x ∈ insert a s) := by
                rintro (h | h) <;> simp only [Finset.mem_insert] at h
                · rcases h with rfl | h
                  · exact hxa rfl
                  · exact hxs (Or.inl h)
                · rcases h with h | h
                  · exact hneg_ne1 h
                  · exact hxs (Or.inr h)
              rw [if_neg hnot, if_neg hxs, Equiv.swap_apply_of_ne_of_ne hxa hxa']
      rw [hmul, map_mul, Equiv.Perm.sign_swap ha_ne_neg, ih hs', Finset.card_insert_of_notMem ha,
        pow_succ, mul_comm]
  have heq : Equiv.neg (ZMod p) = swapOn half := by
    apply Equiv.ext; intro x
    change -x = if x ∈ half ∨ -x ∈ half then -x else x
    by_cases hx0 : x = 0
    · subst hx0
      have hnot : ¬ ((0 : ZMod p) ∈ half ∨ -(0 : ZMod p) ∈ half) := by
        simp [half]
      simp [hnot]
    · have hxpos : 0 < x.val := Nat.pos_of_ne_zero fun h =>
        hx0 (by rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero])
      have hvneg := hneg_val x hx0
      have hlt : x.val < p := x.val_lt
      have hmem : x ∈ half ∨ -x ∈ half := by
        by_cases h2 : 2 * x.val < p
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxpos, h2⟩)
        · refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, ?_⟩)
          rcases hp.odd_of_ne_two hodd with ⟨k, hk⟩
          omega
      simp [hmem]
  rw [heq, hsub half (Finset.Subset.refl _), hcard]

private abbrev DriskoG (p : ℕ) := Multiplicative (ZMod p × ZMod p × ZMod p)

/-- **Drisko (1997)**: For every odd prime `p`,
`Δ_{p+1} ≡ (-1)^((p+1)/2) * p^2 [ZMOD p^3]`. -/
theorem drisko_1997_proved (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    delta (p + 1) ≡ (-1 : ℤ) ^ ((p + 1) / 2) * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have heven : Even (p + 1) := by
    rcases hp.odd_of_ne_two hodd with ⟨k, rfl⟩
    exact ⟨k + 1, by omega⟩
  -- Define the translation group DriskoG p = Multiplicative ((ZMod p) × (ZMod p) × (ZMod p))
  let eOpt := finSuccEquivOption p
  let transPerm (a : ZMod p) : Equiv.Perm (Fin (p + 1)) :=
    liftZModPerm p (Equiv.addRight a)
  have htrans_one : transPerm 0 = 1 := by
    have h1 : Equiv.addRight (0 : ZMod p) = 1 := by ext x; simp
    simp [transPerm, h1, liftZModPerm_one]
  have htrans_add : ∀ a b : ZMod p, transPerm (a + b) = transPerm a * transPerm b := by
    intro a b
    have h1 : Equiv.addRight (a + b) = Equiv.addRight a * Equiv.addRight b := by
      ext x; simp only [Equiv.Perm.mul_apply, Equiv.coe_addRight]; ring
    simp [transPerm, h1, liftZModPerm_mul]
  let gHom : DriskoG p →* Isotopy (p + 1) :=
    { toFun := fun g =>
        let t := Multiplicative.toAdd g
        (transPerm t.1, transPerm t.2.1, transPerm t.2.2)
      map_one' := by
        change (transPerm 0, transPerm 0, transPerm 0) = (1, 1, 1)
        simp [htrans_one]
      map_mul' := fun g₁ g₂ => by
        change (transPerm (_ + _), transPerm (_ + _), transPerm (_ + _)) =
          (transPerm _ * transPerm _, transPerm _ * transPerm _, transPerm _ * transPerm _)
        simp [htrans_add] }
  have hgHom_inj : Function.Injective gHom := by
    intro g₁ g₂ h
    have htrans_inj : Function.Injective transPerm := by
      intro a b hab
      have h1 := congrArg (fun σ : Equiv.Perm (Fin (p + 1)) => eOpt (σ (eOpt.symm (some 0)))) hab
      simp [transPerm, liftZModPerm, eOpt] at h1
      exact h1
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x : Isotopy (p + 1) => x.2.1) h
    have h3 := congrArg (fun x : Isotopy (p + 1) => x.2.2) h
    have ha := htrans_inj h1
    have hb := htrans_inj h2
    have hc := htrans_inj h3
    apply Multiplicative.toAdd.injective
    exact Prod.ext ha (Prod.ext hb hc)
  letI : MulAction (DriskoG p) (LatinSquare (p + 1)) := MulAction.compHom (LatinSquare (p + 1)) gHom
  -- Action of DriskoG p on LatinSquare (p + 1) preserves squareSign since p + 1 is even
  have hsign_inv : ∀ (g : DriskoG p) (L : LatinSquare (p + 1)), squareSign (g • L) = squareSign L :=
    fun g L => (eq_isotopy_proved (p + 1) (gHom g) L).2.2 heven
  -- Helper: transPerm a on eOpt.symm none and eOpt.symm (some x)
  have htrans_none : ∀ a : ZMod p, transPerm a (eOpt.symm none) = eOpt.symm none := fun a => by
    simp [transPerm, liftZModPerm, eOpt]
  have htrans_some : ∀ a x : ZMod p, transPerm a (eOpt.symm (some x)) = eOpt.symm (some (x + a)) :=
    fun a x => by simp [transPerm, liftZModPerm, eOpt]
  have htrans_symm_none : ∀ a : ZMod p, (transPerm a).symm (eOpt.symm none) = eOpt.symm none :=
    fun a => by
      apply (transPerm a).injective; rw [(transPerm a).apply_symm_apply, htrans_none]
  have htrans_symm_some : ∀ a x : ZMod p,
      (transPerm a).symm (eOpt.symm (some x)) = eOpt.symm (some (x - a)) := fun a x => by
    apply (transPerm a).injective
    rw [(transPerm a).apply_symm_apply, htrans_some, sub_add_cancel]
  -- Entry formula for g • L = L
  have hfix_iff : ∀ (a b c : ZMod p) (L : LatinSquare (p + 1)),
      Multiplicative.ofAdd (a, b, c) • L = L ↔
        (∀ r c' : Fin (p + 1),
          transPerm c (L.entry r c') = L.entry (transPerm a r) (transPerm b c')) := by
    intro a b c L
    constructor
    · intro h r c'
      have h1 := congrArg (fun M : LatinSquare (p + 1) => M.entry (transPerm a r) (transPerm b c')) h
      change transPerm c (L.entry ((transPerm a).symm (transPerm a r))
        ((transPerm b).symm (transPerm b c'))) = L.entry (transPerm a r) (transPerm b c') at h1
      simpa using h1
    · intro h
      apply LatinSquare.ext; funext r c'
      change transPerm c (L.entry ((transPerm a).symm r) ((transPerm b).symm c')) = L.entry r c'
      have h1 := h ((transPerm a).symm r) ((transPerm b).symm c')
      simpa using h1
  -- Crucial structural lemma: ANY nontrivial stabilizer element (a, b, c) has a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0!
  have hstab_nonzero : ∀ (L : LatinSquare (p + 1)) (a b c : ZMod p),
      Multiplicative.ofAdd (a, b, c) • L = L → (a, b, c) ≠ (0, 0, 0) →
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
    intro L a b c hfix hne
    have hf := (hfix_iff a b c L).mp hfix
    have htrans_fix_only_none : ∀ (x : ZMod p) (u : Fin (p + 1)),
        x ≠ 0 → transPerm x u = u → u = eOpt.symm none := by
      intro x u hx hu
      cases ho : eOpt u with
      | none => rw [← ho, eOpt.symm_apply_apply]
      | some z =>
        exfalso
        have hu' : u = eOpt.symm (some z) := by rw [← ho, eOpt.symm_apply_apply]
        rw [hu', htrans_some] at hu
        have h2 := Option.some.inj (eOpt.symm.injective hu)
        exact hx (by simpa using h2)
    have ha0 : a ≠ 0 := by
      intro ha; subst ha
      by_cases hc0 : c = 0
      · subst hc0
        have hb0 : b ≠ 0 := fun hb => hne (by simp [hb])
        -- L(r, c + b) = L(r, c) for all r, c, contradicting row injectivity!
        have h1 := hf (eOpt.symm none) (eOpt.symm (some 0))
        rw [htrans_one, htrans_some, zero_add] at h1
        have h2 := (L.row_bijective (eOpt.symm none)).1 h1
        have h3 := Option.some.inj (eOpt.symm.injective h2)
        exact hb0 h3.symm
      · -- c ≠ 0, a = 0: for EVERY r, L(r, none) is fixed by transPerm c, so L(r, none) = none!
        -- Contradicts col_bijective at none since p + 1 ≥ 2!
        have hall : ∀ r : Fin (p + 1), L.entry r (eOpt.symm none) = eOpt.symm none := by
          intro r
          have h1 := hf r (eOpt.symm none)
          rw [htrans_one, htrans_none] at h1
          exact htrans_fix_only_none c _ hc0 h1
        have h01 := (L.col_bijective (eOpt.symm none)).1
          ((hall (eOpt.symm none)).trans (hall (eOpt.symm (some 0))).symm)
        have := eOpt.symm.injective h01
        cases this
    have hb0 : b ≠ 0 := by
      intro hb; subst hb
      by_cases hc0 : c = 0
      · subst hc0
        have h1 := hf (eOpt.symm (some 0)) (eOpt.symm none)
        rw [htrans_one, htrans_some, zero_add] at h1
        have h2 := (L.col_bijective (eOpt.symm none)).1 h1
        have h3 := Option.some.inj (eOpt.symm.injective h2)
        exact ha0 h3.symm
      · have hall : ∀ c' : Fin (p + 1), L.entry (eOpt.symm none) c' = eOpt.symm none := by
          intro c'
          have h1 := hf (eOpt.symm none) c'
          rw [htrans_one, htrans_none] at h1
          exact htrans_fix_only_none c _ hc0 h1
        have h01 := (L.row_bijective (eOpt.symm none)).1
          ((hall (eOpt.symm none)).trans (hall (eOpt.symm (some 0))).symm)
        have := eOpt.symm.injective h01
        cases this
    have hc0 : c ≠ 0 := by
      intro hc; subst hc
      -- a ≠ 0, b ≠ 0, c = 0: L(none, c + b) = L(none, c) contradicts row_bijective at none!
      have h1 := hf (eOpt.symm none) (eOpt.symm (some 0))
      rw [htrans_one, htrans_none, htrans_some, zero_add] at h1
      have h2 := (L.row_bijective (eOpt.symm none)).1 h1
      have h3 := Option.some.inj (eOpt.symm.injective h2)
      exact hb0 h3.symm
    exact ⟨ha0, hb0, hc0⟩
  -- For each pair (lam, mu) ∈ (ZMod p)ˣ × (ZMod p)ˣ, define the rank-1 subgroup line L_{lam, mu}
  let lineGen (lam mu : (ZMod p)ˣ) : DriskoG p := Multiplicative.ofAdd ((1 : ZMod p), lam.1, mu.1)
  let lineSub (lam mu : (ZMod p)ˣ) : Subgroup (DriskoG p) := Subgroup.zpowers (lineGen lam mu)
  let FixLine (lam mu : (ZMod p)ˣ) : Finset (LatinSquare (p + 1)) :=
    Finset.univ.filter fun L : LatinSquare (p + 1) => lineGen lam mu • L = L
  -- Every L with nontrivial stabilizer belongs to a UNIQUE FixLine lam mu!
  have hfix_unique : ∀ L : LatinSquare (p + 1),
      (∃ g : DriskoG p, g ≠ 1 ∧ g • L = L) →
      ∃! pair : (ZMod p)ˣ × (ZMod p)ˣ, L ∈ FixLine pair.1 pair.2 := by
    intro L ⟨g, hg1, hgf⟩
    rcases hgeq : Multiplicative.toAdd g with ⟨a, b, c⟩
    have hne : (a, b, c) ≠ (0, 0, 0) := fun h =>
      hg1 (Multiplicative.toAdd.injective (by rw [hgeq, h]; rfl))
    have hg_eq : g = Multiplicative.ofAdd (a, b, c) :=
      Multiplicative.toAdd.injective (by simpa using hgeq)
    rw [hg_eq] at hgf
    obtain ⟨ha, hb, hc⟩ := hstab_nonzero L a b c hgf hne
    let lam : (ZMod p)ˣ := Units.mk0 (b * a⁻¹) (mul_ne_zero hb (inv_ne_zero ha))
    let mu : (ZMod p)ˣ := Units.mk0 (c * a⁻¹) (mul_ne_zero hc (inv_ne_zero ha))
    have hpow_gen : ∀ (k : ℕ) (x y z : ZMod p),
        (Multiplicative.ofAdd (x, y, z) : DriskoG p) ^ k =
        Multiplicative.ofAdd ((k : ZMod p) * x, (k : ZMod p) * y, (k : ZMod p) * z) := by
      intro k x y z
      induction k with
      | zero => apply Multiplicative.toAdd.injective; simp; rfl
      | succ k ih =>
        rw [pow_succ, ih]
        apply Multiplicative.toAdd.injective
        simp [Prod.mk_add_mk, add_mul, one_mul]
    have hsmul_pow : ∀ (k : ℕ) (x : DriskoG p), x • L = L → (x ^ k) • L = L := by
      intro k x hx
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', mul_smul, ih, hx]
    have hmem : L ∈ FixLine lam mu := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h1 := hsmul_pow a⁻¹.val (Multiplicative.ofAdd (a, b, c)) hgf
      rw [hpow_gen, ZMod.natCast_zmod_val, inv_mul_cancel₀ ha] at h1
      simpa [lineGen, lam, mu, mul_comm] using h1
    refine ⟨(lam, mu), hmem, fun ⟨lam', mu'⟩ hmem' => ?_⟩
    have h1 : lineGen lam mu • L = L := (Finset.mem_filter.mp hmem).2
    have h2 : lineGen lam' mu' • L = L := (Finset.mem_filter.mp hmem').2
    have hdiff : (lineGen lam' mu' * (lineGen lam mu)⁻¹) • L = L := by
      rw [mul_smul]
      have hinv : (lineGen lam mu)⁻¹ • L = L := by
        rw [inv_smul_eq_iff]; exact h1.symm
      rw [hinv, h2]
    have hdiff_eq : lineGen lam' mu' * (lineGen lam mu)⁻¹ =
        Multiplicative.ofAdd ((0 : ZMod p), lam'.1 - lam.1, mu'.1 - mu.1) := by
      apply Multiplicative.toAdd.injective
      simp [lineGen, Prod.mk_add_mk, sub_eq_add_neg]
    rw [hdiff_eq] at hdiff
    by_contra hneq
    have htuple_ne : ((0 : ZMod p), lam'.1 - lam.1, mu'.1 - mu.1) ≠ (0, 0, 0) := by
      intro heq
      apply hneq
      have hlam : lam'.1 = lam.1 := sub_eq_zero.mp (congrArg (fun x => x.2.1) heq)
      have hmu : mu'.1 = mu.1 := sub_eq_zero.mp (congrArg (fun x => x.2.2) heq)
      exact Prod.ext (Units.ext hlam) (Units.ext hmu)
    exact (hstab_nonzero L 0 (lam'.1 - lam.1) (mu'.1 - mu.1) hdiff htuple_ne).1 rfl
  -- Step 1: Orbit congruence Δ_{p+1} ≡ ∑_{lam, mu} ∑_{L ∈ FixLine lam mu} squareSign L [ZMOD p^3]
  have hcong1 : delta (p + 1) ≡
      ∑ pair : (ZMod p)ˣ × (ZMod p)ˣ, ∑ L ∈ FixLine pair.1 pair.2, (squareSign L : ℤ)
      [ZMOD (p : ℤ) ^ 3] := by
    rw [delta_eq_sum]
    let NonTriv := Finset.univ.filter fun L : LatinSquare (p + 1) => ∃ g : DriskoG p, g ≠ 1 ∧ g • L = L
    let Triv := Finset.univ.filter fun L : LatinSquare (p + 1) => ¬ (∃ g : DriskoG p, g ≠ 1 ∧ g • L = L)
    have hsplit : (∑ L : LatinSquare (p + 1), (squareSign L : ℤ)) =
        (∑ L ∈ NonTriv, (squareSign L : ℤ)) + (∑ L ∈ Triv, (squareSign L : ℤ)) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
    have hcardG : Fintype.card (DriskoG p) = p ^ 3 := by
      rw [Fintype.card_of_bijective Multiplicative.toAdd.bijective, Fintype.card_prod, Fintype.card_prod,
        ZMod.card, pow_succ, pow_two]
      ring
    -- Sum over Triv is divisible by |DriskoG p| = p^3 (every orbit in Triv has size |DriskoG p|!)
    have htriv_dvd : (p : ℤ) ^ 3 ∣ ∑ L ∈ Triv, (squareSign L : ℤ) := by
      -- Group all of LatinSquare (p+1) into orbits, restrict to orbits with trivial stabilizer
      let f : LatinSquare (p + 1) → ℤ := fun L => if L ∈ Triv then (squareSign L : ℤ) else 0
      have hfinv : ∀ g : DriskoG p, ∀ L : LatinSquare (p + 1), f (g • L) = f L := by
        intro g L
        have hmem_iff : g • L ∈ Triv ↔ L ∈ Triv := by
          simp only [Triv, Finset.mem_filter, Finset.mem_univ, true_and]
          refine not_congr ⟨?_, ?_⟩
          · rintro ⟨h, hne, hfix⟩
            refine ⟨g⁻¹ * h * g, ?_, ?_⟩
            · intro h1; apply hne
              have := congrArg (fun x => g * x * g⁻¹) h1
              simpa [mul_assoc] using this
            · rw [mul_smul, mul_smul, hfix, inv_smul_smul]
          · rintro ⟨h, hne, hfix⟩
            refine ⟨g * h * g⁻¹, ?_, ?_⟩
            · intro h1; apply hne
              have := congrArg (fun x => g⁻¹ * x * g) h1
              simpa [mul_assoc] using this
            · rw [mul_smul, mul_smul, inv_smul_smul, hfix]
        dsimp only [f]
        by_cases hL : L ∈ Triv
        · rw [if_pos (hmem_iff.mpr hL), if_pos hL, hsign_inv]
        · rw [if_neg (fun h => hL (hmem_iff.mp h)), if_neg hL]
      have hsum_f : (∑ L ∈ Triv, (squareSign L : ℤ)) = ∑ L : LatinSquare (p + 1), f L := by
        simp only [f, Finset.sum_ite_mem, Finset.univ_inter]
      rw [hsum_f, sum_eq_sum_orbits f hfinv]
      refine Finset.dvd_sum fun ω _ => ?_
      set L := Quotient.out ω
      by_cases hL : L ∈ Triv
      · have hstab1 : Fintype.card (MulAction.stabilizer (DriskoG p) L) = 1 := by
          rw [Fintype.card_eq_one_iff]
          refine ⟨1, fun ⟨g, hg⟩ => Subtype.ext ?_⟩
          have hno : ¬ ∃ g : DriskoG p, g ≠ 1 ∧ g • L = L := (Finset.mem_filter.mp hL).2
          by_contra hne; exact hno ⟨g, hne, hg⟩
        have horb_eq : (Finset.univ.filter fun x : LatinSquare (p + 1) =>
            Quotient.mk (MulAction.orbitRel (DriskoG p) (LatinSquare (p + 1))) x = ω).card = p ^ 3 := by
          rw [card_orbit_fiber_eq ω]
          have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (DriskoG p) L
          rw [hstab1, mul_one, hcardG] at hmul
          exact hmul
        rw [horb_eq]
        exact dvd_mul_right _ _
      · dsimp only [f]; rw [if_neg hL, mul_zero]; exact dvd_zero _
    -- Sum over NonTriv equals ∑_{pair} ∑_{L ∈ FixLine pair} squareSign L
    have hnontriv_eq : (∑ L ∈ NonTriv, (squareSign L : ℤ)) =
        ∑ pair : (ZMod p)ˣ × (ZMod p)ˣ, ∑ L ∈ FixLine pair.1 pair.2, (squareSign L : ℤ) := by
      rw [← Finset.sum_biUnion]
      · congr 1; ext L
        simp only [NonTriv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          FixLine]
        constructor
        · intro h
          obtain ⟨pair, hpair, _⟩ := hfix_unique L h
          exact ⟨pair, (Finset.mem_filter.mp hpair).2⟩
        · rintro ⟨⟨lam, mu⟩, hL⟩
          refine ⟨lineGen lam mu, ?_, hL⟩
          intro h1
          have := congrArg (fun x => (Multiplicative.toAdd x).1) h1
          exact one_ne_zero this
      · intro p₁ _ p₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro L hL₁ hL₂
        have hex : ∃ g : DriskoG p, g ≠ 1 ∧ g • L = L :=
          ⟨lineGen p₁.1 p₁.2, fun h1 => one_ne_zero (congrArg (fun x => (Multiplicative.toAdd x).1) h1),
            (Finset.mem_filter.mp hL₁).2⟩
        obtain ⟨pair, _, huniq⟩ := hfix_unique L hex
        exact hne ((huniq p₁ hL₁).trans (huniq p₂ hL₂).symm)
    rw [hsplit, hnontriv_eq]
    have hmod : (∑ L ∈ Triv, (squareSign L : ℤ)) ≡ 0 [ZMOD (p : ℤ) ^ 3] :=
      Int.modEq_zero_iff_dvd.mpr htriv_dvd
    simpa using hmod.add_left
      (∑ pair : (ZMod p)ˣ × (ZMod p)ˣ, ∑ L ∈ FixLine pair.1 pair.2, (squareSign L : ℤ))
  -- Step 2: Rescaling shows every FixLine lam mu has the SAME signed sum as FixLine 1 1!
  have hscale_eq : ∀ lam mu : (ZMod p)ˣ,
      (∑ L ∈ FixLine lam mu, (squareSign L : ℤ)) =
      ∑ L ∈ FixLine 1 1, (squareSign L : ℤ) := by
    intro lam mu
    let scCol : Equiv.Perm (Fin (p + 1)) := liftZModPerm p (Equiv.mulLeft₀ lam.1 (Units.ne_zero lam))
    let scSym : Equiv.Perm (Fin (p + 1)) := liftZModPerm p (Equiv.mulLeft₀ mu.1 (Units.ne_zero mu))
    let ψ : Isotopy (p + 1) := (1, scCol, scSym)
    have hconj : ∀ (u : (ZMod p)ˣ) (a : ZMod p),
        liftZModPerm p (Equiv.mulLeft₀ u.1 (Units.ne_zero u)) * transPerm a *
          (liftZModPerm p (Equiv.mulLeft₀ u.1 (Units.ne_zero u)))⁻¹ =
        transPerm (u.1 * a) := by
      intro u a
      have hinv_eq : (liftZModPerm p (Equiv.mulLeft₀ u.1 (Units.ne_zero u)))⁻¹ =
          liftZModPerm p (Equiv.mulLeft₀ u.1 (Units.ne_zero u))⁻¹ := by
        apply inv_eq_of_mul_eq_one_right
        rw [← liftZModPerm_mul, mul_inv_cancel, liftZModPerm_one]
      rw [hinv_eq]
      change liftZModPerm p (Equiv.mulLeft₀ u.1 (Units.ne_zero u)) *
          liftZModPerm p (Equiv.addRight a) *
          liftZModPerm p (Equiv.mulLeft₀ u.1 (Units.ne_zero u))⁻¹ =
        liftZModPerm p (Equiv.addRight (u.1 * a))
      rw [← liftZModPerm_mul, ← liftZModPerm_mul]
      congr 1
      apply Equiv.ext; intro x
      simp only [Equiv.Perm.mul_apply, Equiv.mulLeft₀_apply, Equiv.coe_addRight]
      have hsymm : (Equiv.mulLeft₀ u.1 (Units.ne_zero u))⁻¹ x = u.1⁻¹ * x := by
        apply (Equiv.mulLeft₀ u.1 (Units.ne_zero u)).injective
        change (Equiv.mulLeft₀ u.1 (Units.ne_zero u)) ((Equiv.mulLeft₀ u.1 (Units.ne_zero u)).symm x) =
          u.1 * (u.1⁻¹ * x)
        rw [Equiv.apply_symm_apply, mul_inv_cancel_left₀ (Units.ne_zero u)]
      rw [hsymm, mul_add, mul_inv_cancel_left₀ (Units.ne_zero u)]
    have hbij : ∀ L : LatinSquare (p + 1), L ∈ FixLine 1 1 ↔ ψ • L ∈ FixLine lam mu := by
      intro L
      simp only [FixLine, Finset.mem_filter, Finset.mem_univ, true_and]
      change gHom (lineGen 1 1) • L = L ↔ gHom (lineGen lam mu) • (ψ • L) = ψ • L
      have hconj_iso : ψ * gHom (lineGen 1 1) * ψ⁻¹ = gHom (lineGen lam mu) := by
        apply Prod.ext
        · simp [ψ, gHom, lineGen]
        · apply Prod.ext
          · simpa [ψ, scCol, gHom, lineGen] using hconj lam 1
          · simpa [ψ, scSym, gHom, lineGen] using hconj mu 1
      constructor
      · intro hL
        rw [← hconj_iso, mul_smul, mul_smul, inv_smul_smul, hL]
      · intro hψL
        rw [← hconj_iso, mul_smul, mul_smul, inv_smul_smul] at hψL
        have := congrArg (ψ⁻¹ • ·) hψL
        simpa [inv_smul_smul] using this
    symm
    refine Finset.sum_bij (fun L _ => ψ • L) ?_ ?_ ?_ ?_
    · intro L hL; exact (hbij L).mp hL
    · intro L₁ _ L₂ _ h
      have := congrArg (ψ⁻¹ • ·) h
      simpa [inv_smul_smul] using this
    · intro L hL
      refine ⟨ψ⁻¹ • L, (hbij (ψ⁻¹ • L)).mpr (by simpa using hL), smul_inv_smul ψ L⟩
    · intro L _
      exact congrArg Units.val ((eq_isotopy_proved (p + 1) ψ L).2.2 heven).symm
  -- Step 3: Evaluate ∑_{L ∈ FixLine 1 1} squareSign L = p * (-1)^((p - 1)/2) * tauQ p!
  let Comp := { h : Equiv.Perm (ZMod p) // IsCompleteMap h }
  let buildLS (d₀ : ZMod p) (h : Comp) : LatinSquare (p + 1) :=
    let c₀ : ZMod p := h.1 d₀ - d₀
    let r₀ : ZMod p := h.1 d₀
    let fOpt (r c : Option (ZMod p)) : Option (ZMod p) :=
      match r, c with
      | none, none => none
      | none, some y => some (y + c₀)
      | some x, none => some (x + r₀)
      | some x, some y => if y - x = d₀ then none else some (x + h.1 (y - x))
    { entry := fun r c => eOpt.symm (fOpt (eOpt r) (eOpt c))
      row_bijective := fun r => by
        refine Finite.injective_iff_bijective.mp fun c₁ c₂ heq => ?_
        have hfeq : fOpt (eOpt r) (eOpt c₁) = fOpt (eOpt r) (eOpt c₂) := eOpt.symm.injective heq
        apply eOpt.injective
        cases hr : eOpt r with
        | none =>
          rw [hr] at hfeq
          cases hc1 : eOpt c₁ <;> cases hc2 : eOpt c₂ <;> simp [fOpt, hc1, hc2] at hfeq ⊢
          exact hfeq
        | some x =>
          rw [hr] at hfeq
          cases hc1 : eOpt c₁ with
          | none =>
            cases hc2 : eOpt c₂ with
            | none => rfl
            | some y₂ =>
              simp only [fOpt, hc1, hc2] at hfeq
              by_cases hd : y₂ - x = d₀
              · simp [hd] at hfeq
              · rw [if_neg hd] at hfeq
                have h1 := Option.some.inj hfeq
                have h2 : h.1 d₀ = h.1 (y₂ - x) := add_left_cancel h1
                exact absurd (h.1.injective h2).symm hd
          | some y₁ =>
            cases hc2 : eOpt c₂ with
            | none =>
              simp only [fOpt, hc1, hc2] at hfeq
              by_cases hd : y₁ - x = d₀
              · simp [hd] at hfeq
              · rw [if_neg hd] at hfeq
                have h1 := Option.some.inj hfeq
                have h2 : h.1 (y₁ - x) = h.1 d₀ := add_left_cancel h1
                exact absurd (h.1.injective h2) hd
            | some y₂ =>
              simp only [fOpt, hc1, hc2] at hfeq
              by_cases hd1 : y₁ - x = d₀ <;> by_cases hd2 : y₂ - x = d₀
              · congr 1; exact sub_left_inj.mp (hd1.trans hd2.symm)
              · simp [hd1, hd2] at hfeq
              · simp [hd1, hd2] at hfeq
              · rw [if_neg hd1, if_neg hd2] at hfeq
                have h1 : h.1 (y₁ - x) = h.1 (y₂ - x) := add_left_cancel (Option.some.inj hfeq)
                congr 1; exact sub_left_inj.mp (h.1.injective h1)
      col_bijective := fun c => by
        refine Finite.injective_iff_bijective.mp fun r₁ r₂ heq => ?_
        have hfeq : fOpt (eOpt r₁) (eOpt c) = fOpt (eOpt r₂) (eOpt c) := eOpt.symm.injective heq
        apply eOpt.injective
        cases hc : eOpt c with
        | none =>
          rw [hc] at hfeq
          cases hr1 : eOpt r₁ <;> cases hr2 : eOpt r₂ <;> simp [fOpt, hr1, hr2] at hfeq ⊢
          exact hfeq
        | some y =>
          rw [hc] at hfeq
          cases hr1 : eOpt r₁ with
          | none =>
            cases hr2 : eOpt r₂ with
            | none => rfl
            | some x₂ =>
              simp only [fOpt, hr1, hr2] at hfeq
              by_cases hd : y - x₂ = d₀
              · simp [hd] at hfeq
              · rw [if_neg hd] at hfeq
                have h1 := Option.some.inj hfeq
                have h2 : h.1 d₀ - d₀ = h.1 (y - x₂) - (y - x₂) := by
                  have : y + (h.1 d₀ - d₀) = y + (h.1 (y - x₂) - (y - x₂)) := by
                    calc y + (h.1 d₀ - d₀) = x₂ + h.1 (y - x₂) := h1
                      _ = y + (h.1 (y - x₂) - (y - x₂)) := by ring
                  exact add_left_cancel this
                exact absurd (h.2.1 h2).symm hd
          | some x₁ =>
            cases hr2 : eOpt r₂ with
            | none =>
              simp only [fOpt, hr1, hr2] at hfeq
              by_cases hd : y - x₁ = d₀
              · simp [hd] at hfeq
              · rw [if_neg hd] at hfeq
                have h1 := Option.some.inj hfeq
                have h2 : h.1 (y - x₁) - (y - x₁) = h.1 d₀ - d₀ := by
                  have : y + (h.1 (y - x₁) - (y - x₁)) = y + (h.1 d₀ - d₀) := by
                    calc y + (h.1 (y - x₁) - (y - x₁)) = x₁ + h.1 (y - x₁) := by ring
                      _ = y + (h.1 d₀ - d₀) := h1
                  exact add_left_cancel this
                exact absurd (h.2.1 h2) hd
            | some x₂ =>
              simp only [fOpt, hr1, hr2] at hfeq
              by_cases hd1 : y - x₁ = d₀ <;> by_cases hd2 : y - x₂ = d₀
              · congr 1
                have : y - x₁ = y - x₂ := hd1.trans hd2.symm
                exact sub_right_inj.mp this
              · simp [hd1, hd2] at hfeq
              · simp [hd1, hd2] at hfeq
              · rw [if_neg hd1, if_neg hd2] at hfeq
                have h1 := Option.some.inj hfeq
                have h2 : h.1 (y - x₁) - (y - x₁) = h.1 (y - x₂) - (y - x₂) := by
                  have : y + (h.1 (y - x₁) - (y - x₁)) = y + (h.1 (y - x₂) - (y - x₂)) := by
                    calc y + (h.1 (y - x₁) - (y - x₁)) = x₁ + h.1 (y - x₁) := by ring
                      _ = x₂ + h.1 (y - x₂) := h1
                      _ = y + (h.1 (y - x₂) - (y - x₂)) := by ring
                  exact add_left_cancel this
                congr 1; exact sub_right_inj.mp (h.2.1 h2) }
  have hbuild_mem : ∀ (d₀ : ZMod p) (h : Comp), buildLS d₀ h ∈ FixLine 1 1 := by
    intro d₀ h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [show lineGen 1 1 = Multiplicative.ofAdd ((1 : ZMod p), (1 : ZMod p), (1 : ZMod p)) from rfl,
      hfix_iff]
    intro r c
    cases hr : eOpt r with
    | none =>
      have hr' : r = eOpt.symm none := by rw [← hr, eOpt.symm_apply_apply]
      subst hr'
      cases hc : eOpt c with
      | none =>
        have hc' : c = eOpt.symm none := by rw [← hc, eOpt.symm_apply_apply]
        subst hc'; simp [buildLS, htrans_none, eOpt]
      | some y =>
        have hc' : c = eOpt.symm (some y) := by rw [← hc, eOpt.symm_apply_apply]
        subst hc'; simp [buildLS, htrans_none, htrans_some, eOpt]; ring
    | some x =>
      have hr' : r = eOpt.symm (some x) := by rw [← hr, eOpt.symm_apply_apply]
      subst hr'
      cases hc : eOpt c with
      | none =>
        have hc' : c = eOpt.symm none := by rw [← hc, eOpt.symm_apply_apply]
        subst hc'; simp [buildLS, htrans_none, htrans_some, eOpt]; ring
      | some y =>
        have hc' : c = eOpt.symm (some y) := by rw [← hc, eOpt.symm_apply_apply]
        subst hc'
        have hsub : y + 1 - (x + 1) = y - x := by ring
        simp only [buildLS, htrans_some, Equiv.apply_symm_apply, hsub]
        split_ifs with hd
        · exact htrans_none 1
        · rw [htrans_some]; congr 2; ring
  have hbuild_sign : ∀ (d₀ : ZMod p) (h : Comp),
      (squareSign (buildLS d₀ h) : ℤ) =
      (-1 : ℤ) ^ ((p - 1) / 2) * (Equiv.Perm.sign h.1 : ℤ) *
        (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ) := by
    intro d₀ h
    set L := buildLS d₀ h
    have hL_fix : lineGen 1 1 • L = L := (Finset.mem_filter.mp (hbuild_mem d₀ h)).2
    have hL_pow : ∀ k : ℕ, (lineGen 1 1 ^ k) • L = L := by
      intro k; induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', mul_smul, ih, hL_fix]
    have htrans_sign : ∀ a : ZMod p, Equiv.Perm.sign (transPerm a) = 1 := by
      intro a
      rw [show transPerm a = liftZModPerm p (Equiv.addRight a) from rfl, sign_liftZModPerm]
      exact (lem_6_4_signs p hodd).2.2.1 a
    have hgen_pow : ∀ x : ZMod p,
        gHom (lineGen 1 1 ^ x.val) = (transPerm x, transPerm x, transPerm x) := by
      intro x
      have h1 : ∀ k : ℕ, gHom (lineGen 1 1 ^ k) =
          (transPerm (k : ZMod p), transPerm (k : ZMod p), transPerm (k : ZMod p)) := by
        intro k; induction k with
        | zero =>
          rw [pow_zero, map_one, Nat.cast_zero, htrans_one]; rfl
        | succ k ih =>
          rw [pow_succ, map_mul, ih]
          change (transPerm (k : ZMod p) * transPerm 1, transPerm (k : ZMod p) * transPerm 1,
            transPerm (k : ZMod p) * transPerm 1) = _
          simp [← htrans_add]
      rw [h1 x.val, ZMod.natCast_zmod_val]
    -- All rows (some x) have the same sign as row (some 0)
    have hrow_const : ∀ x : ZMod p,
        Equiv.Perm.sign (rowPerm L (eOpt.symm (some x))) =
        Equiv.Perm.sign (rowPerm L (eOpt.symm (some 0))) := by
      intro x
      have h1 : rowPerm ((gHom (lineGen 1 1 ^ x.val)) • L) (transPerm x (eOpt.symm (some 0))) =
          transPerm x * rowPerm L (eOpt.symm (some 0)) * (transPerm x)⁻¹ := by
        have hsm := rowPerm_smul (gHom (lineGen 1 1 ^ x.val)) L (eOpt.symm (some 0))
        simpa [hgen_pow x] using hsm
      have hfix' : (gHom (lineGen 1 1 ^ x.val)) • L = L := hL_pow x.val
      rw [hfix', htrans_some, zero_add] at h1
      rw [h1, map_mul, map_mul, map_inv, htrans_sign, one_mul, inv_one, mul_one]
    -- Row (none) is a translation, so sign = 1
    have hrow_none : Equiv.Perm.sign (rowPerm L (eOpt.symm none)) = 1 := by
      have heq : rowPerm L (eOpt.symm none) = transPerm (h.1 d₀ - d₀) := by
        apply Equiv.ext; intro c
        cases hc : eOpt c with
        | none =>
          have hc' : c = eOpt.symm none := by rw [← hc, eOpt.symm_apply_apply]
          subst hc'; simp [rowPerm, L, buildLS, htrans_none, eOpt]
        | some y =>
          have hc' : c = eOpt.symm (some y) := by rw [← hc, eOpt.symm_apply_apply]
          subst hc'; simp [rowPerm, L, buildLS, htrans_some, eOpt]
      rw [heq, htrans_sign]
    -- Row (some 0) = swap none (some (h d₀)) * liftZModPerm p h.1
    have hrow_zero : Equiv.Perm.sign (rowPerm L (eOpt.symm (some 0))) = -Equiv.Perm.sign h.1 := by
      let sw : Equiv.Perm (Fin (p + 1)) := Equiv.swap (eOpt.symm none) (eOpt.symm (some (h.1 d₀)))
      have hne_sw : eOpt.symm none ≠ eOpt.symm (some (h.1 d₀)) := fun heq => by
        have := eOpt.symm.injective heq; cases this
      have heq : rowPerm L (eOpt.symm (some 0)) = sw * liftZModPerm p h.1 := by
        apply Equiv.ext; intro c
        cases hc : eOpt c with
        | none =>
          have hc' : c = eOpt.symm none := by rw [← hc, eOpt.symm_apply_apply]
          subst hc'
          simp only [rowPerm, Equiv.ofBijective_apply, L, buildLS, Equiv.apply_symm_apply,
            Equiv.Perm.mul_apply, liftZModPerm, Equiv.permCongr_apply, Equiv.symm_symm,
            Equiv.coe_fn_mk, Option.map_none, eOpt, zero_add]
          simp [sw, eOpt]
        | some y =>
          have hc' : c = eOpt.symm (some y) := by rw [← hc, eOpt.symm_apply_apply]
          subst hc'
          simp only [rowPerm, Equiv.ofBijective_apply, L, buildLS, Equiv.apply_symm_apply,
            Equiv.Perm.mul_apply, liftZModPerm, Equiv.permCongr_apply, Equiv.symm_symm,
            Equiv.coe_fn_mk, Option.map_some, eOpt, sub_zero, zero_add]
          by_cases hd : y = d₀
          · subst hd; simp [sw, eOpt]
          · have h1 : eOpt.symm (some (h.1 y)) ≠ eOpt.symm none := fun eq => by
              have := eOpt.symm.injective eq; cases this
            have h2 : eOpt.symm (some (h.1 y)) ≠ eOpt.symm (some (h.1 d₀)) := fun eq =>
              hd (h.1.injective (Option.some.inj (eOpt.symm.injective eq)))
            simp [hd, sw, eOpt, Equiv.swap_apply_of_ne_of_ne h1 h2]
      rw [heq, map_mul, Equiv.Perm.sign_swap hne_sw, sign_liftZModPerm, neg_one_mul]
    -- All columns (some y) have the same sign as column (some 0)
    have hcol_const : ∀ y : ZMod p,
        Equiv.Perm.sign (colPerm L (eOpt.symm (some y))) =
        Equiv.Perm.sign (colPerm L (eOpt.symm (some 0))) := by
      intro y
      have h1 : colPerm ((gHom (lineGen 1 1 ^ y.val)) • L) (transPerm y (eOpt.symm (some 0))) =
          transPerm y * colPerm L (eOpt.symm (some 0)) * (transPerm y)⁻¹ := by
        have hsm := colPerm_smul (gHom (lineGen 1 1 ^ y.val)) L (eOpt.symm (some 0))
        simpa [hgen_pow y] using hsm
      have hfix' : (gHom (lineGen 1 1 ^ y.val)) • L = L := hL_pow y.val
      rw [hfix', htrans_some, zero_add] at h1
      rw [h1, map_mul, map_mul, map_inv, htrans_sign, one_mul, inv_one, mul_one]
    -- Column (none) is a translation, so sign = 1
    have hcol_none : Equiv.Perm.sign (colPerm L (eOpt.symm none)) = 1 := by
      have heq : colPerm L (eOpt.symm none) = transPerm (h.1 d₀) := by
        apply Equiv.ext; intro r
        cases hr : eOpt r with
        | none =>
          have hr' : r = eOpt.symm none := by rw [← hr, eOpt.symm_apply_apply]
          subst hr'; simp [colPerm, L, buildLS, htrans_none, eOpt]
        | some x =>
          have hr' : r = eOpt.symm (some x) := by rw [← hr, eOpt.symm_apply_apply]
          subst hr'; simp [colPerm, L, buildLS, htrans_some, eOpt]
      rw [heq, htrans_sign]
    -- Column (some 0) = swap none (some (h d₀ - d₀)) * liftZModPerm p (h' * neg)
    let h' : Equiv.Perm (ZMod p) := Equiv.ofBijective (fun x => h.1 x - x) h.2
    have hcol_zero : Equiv.Perm.sign (colPerm L (eOpt.symm (some 0))) =
        -Equiv.Perm.sign h' * (-1 : ℤˣ) ^ ((p - 1) / 2) := by
      let sw : Equiv.Perm (Fin (p + 1)) := Equiv.swap (eOpt.symm none) (eOpt.symm (some (h' d₀)))
      have hne_sw : eOpt.symm none ≠ eOpt.symm (some (h' d₀)) := fun heq => by
        have := eOpt.symm.injective heq; cases this
      have heq : colPerm L (eOpt.symm (some 0)) = sw * liftZModPerm p (h' * Equiv.neg (ZMod p)) := by
        apply Equiv.ext; intro r
        cases hr : eOpt r with
        | none =>
          have hr' : r = eOpt.symm none := by rw [← hr, eOpt.symm_apply_apply]
          subst hr'
          simp only [colPerm, Equiv.ofBijective_apply, L, buildLS, Equiv.apply_symm_apply,
            Equiv.Perm.mul_apply, liftZModPerm, Equiv.permCongr_apply, Equiv.symm_symm,
            Equiv.coe_fn_mk, Option.map_none, eOpt, zero_add]
          simp only [sw, eOpt, Equiv.swap_apply_left, h']; rfl
        | some x =>
          have hr' : r = eOpt.symm (some x) := by rw [← hr, eOpt.symm_apply_apply]
          subst hr'
          simp only [colPerm, Equiv.ofBijective_apply, L, buildLS, Equiv.apply_symm_apply,
            Equiv.Perm.mul_apply, liftZModPerm, Equiv.permCongr_apply, Equiv.symm_symm,
            Equiv.coe_fn_mk, Option.map_some, Equiv.neg_apply, eOpt]
          have hsub0 : (0 : ZMod p) - x = -x := zero_sub x
          have hval : x + h.1 (-x) = h' (-x) := by
            change x + h.1 (-x) = h.1 (-x) - (-x); ring
          rw [hsub0, hval]
          by_cases hd : -x = d₀
          · rw [if_pos hd, hd]; simp [sw, eOpt]
          · have h1 : eOpt.symm (some (h' (-x))) ≠ eOpt.symm none := fun eq => by
              have := eOpt.symm.injective eq; cases this
            have h2 : eOpt.symm (some (h' (-x))) ≠ eOpt.symm (some (h' d₀)) := fun eq =>
              hd (h'.injective (Option.some.inj (eOpt.symm.injective eq)))
            rw [if_neg hd]
            simpa [sw, eOpt] using (Equiv.swap_apply_of_ne_of_ne h1 h2).symm
      rw [heq, map_mul, Equiv.Perm.sign_swap hne_sw, sign_liftZModPerm, map_mul,
        sign_neg_zmod p hp hodd, neg_one_mul, neg_mul]
    -- Multiply all row signs and column signs!
    have hunit_pow : ∀ u : ℤˣ, u ^ p = u := by
      intro u
      rcases hp.odd_of_ne_two hodd with ⟨k, hk⟩
      rw [hk, pow_succ, pow_mul]
      rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    have hrowSign : rowSign L = -Equiv.Perm.sign h.1 := by
      unfold rowSign
      rw [← Equiv.prod_comp eOpt.symm (fun r => Equiv.Perm.sign (rowPerm L r)),
        Fintype.prod_option, hrow_none, one_mul]
      simp_rw [hrow_const, Finset.prod_const, Finset.card_univ, ZMod.card, hrow_zero]
      exact hunit_pow _
    have hcolSign : colSign L = -Equiv.Perm.sign h' * (-1 : ℤˣ) ^ ((p - 1) / 2) := by
      unfold colSign
      rw [← Equiv.prod_comp eOpt.symm (fun c => Equiv.Perm.sign (colPerm L c)),
        Fintype.prod_option, hcol_none, one_mul]
      simp_rw [hcol_const, Finset.prod_const, Finset.card_univ, ZMod.card, hcol_zero]
      exact hunit_pow _
    unfold squareSign
    rw [hrowSign, hcolSign]
    push_cast
    ring
  -- Bijection ZMod p × Comp ≃ FixLine 1 1 via buildLS!
  have hsum_11 : (∑ L ∈ FixLine 1 1, (squareSign L : ℤ)) =
      (p : ℤ) * (-1 : ℤ) ^ ((p - 1) / 2) * tauQ p := by
    have hbij : (∑ L ∈ FixLine 1 1, (squareSign L : ℤ)) =
        ∑ x : ZMod p × Comp, (squareSign (buildLS x.1 x.2) : ℤ) := by
      symm
      refine Finset.sum_bij (fun x _ => buildLS x.1 x.2) ?_ ?_ ?_ ?_
      · intro x _; exact hbuild_mem x.1 x.2
      · intro ⟨d₁, h₁⟩ _ ⟨d₂, h₂⟩ _ heq
        have hd : d₁ = d₂ := by
          have h1 := congrArg (fun M : LatinSquare (p + 1) => eOpt (M.entry (eOpt.symm (some 0)) (eOpt.symm (some d₁)))) heq
          simp only [buildLS, Equiv.apply_symm_apply, sub_zero, ↓reduceIte] at h1
          by_contra hne
          rw [if_neg hne] at h1
          cases h1
        subst hd
        refine Prod.ext rfl (Subtype.ext (Equiv.ext fun d => ?_))
        by_cases hdd : d = d₁
        · subst hdd
          have h1 := congrArg (fun M : LatinSquare (p + 1) => eOpt (M.entry (eOpt.symm (some 0)) (eOpt.symm none))) heq
          simp only [buildLS, Equiv.apply_symm_apply, zero_add] at h1
          exact Option.some.inj h1
        · have h1 := congrArg (fun M : LatinSquare (p + 1) => eOpt (M.entry (eOpt.symm (some 0)) (eOpt.symm (some d)))) heq
          simp only [buildLS, Equiv.apply_symm_apply, sub_zero, if_neg hdd, zero_add] at h1
          exact Option.some.inj h1
      · intro L hL
        have hfix := (hfix_iff 1 1 1 L).mp (Finset.mem_filter.mp hL).2
        have hfix_t : ∀ t : ZMod p, ∀ r c : Fin (p + 1),
            transPerm t (L.entry r c) = L.entry (transPerm t r) (transPerm t c) := by
          intro t
          have h1 : ∀ k : ℕ, ∀ r c : Fin (p + 1),
              transPerm (k : ZMod p) (L.entry r c) =
              L.entry (transPerm (k : ZMod p) r) (transPerm (k : ZMod p) c) := by
            intro k; induction k with
            | zero => intro r c; simp [htrans_one]
            | succ k ih =>
              intro r c
              rw [Nat.cast_succ, htrans_add, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
                Equiv.Perm.mul_apply, hfix, ih]
          simpa [ZMod.natCast_zmod_val] using h1 t.val
        -- L(none, none) must be none (since fixed by transPerm 1)
        have hnn : L.entry (eOpt.symm none) (eOpt.symm none) = eOpt.symm none := by
          have h1 := hfix (eOpt.symm none) (eOpt.symm none)
          rw [htrans_none] at h1
          cases ho : eOpt (L.entry (eOpt.symm none) (eOpt.symm none)) with
          | none => exact eOpt.injective (ho.trans (eOpt.apply_symm_apply none).symm)
          | some z =>
            exfalso
            have hu : L.entry (eOpt.symm none) (eOpt.symm none) = eOpt.symm (some z) := by
              rw [← ho, eOpt.symm_apply_apply]
            rw [hu, htrans_some] at h1
            have := Option.some.inj (eOpt.symm.injective h1)
            simp at this
        -- Extract r₀, c₀, d₀
        have hr0_ne : eOpt (L.entry (eOpt.symm (some 0)) (eOpt.symm none)) ≠ none := by
          intro h0
          have heq' : L.entry (eOpt.symm (some 0)) (eOpt.symm none) = eOpt.symm none :=
            eOpt.injective (h0.trans (eOpt.apply_symm_apply none).symm)
          have := (L.col_bijective (eOpt.symm none)).1 (heq'.trans hnn.symm)
          have := eOpt.symm.injective this; cases this
        obtain ⟨r₀, hr₀⟩ := Option.ne_none_iff_exists'.mp hr0_ne
        have hc0_ne : eOpt (L.entry (eOpt.symm none) (eOpt.symm (some 0))) ≠ none := by
          intro h0
          have heq' : L.entry (eOpt.symm none) (eOpt.symm (some 0)) = eOpt.symm none :=
            eOpt.injective (h0.trans (eOpt.apply_symm_apply none).symm)
          have := (L.row_bijective (eOpt.symm none)).1 (heq'.trans hnn.symm)
          have := eOpt.symm.injective this; cases this
        obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.mp hc0_ne
        -- Find d₀ such that L(some 0, some d₀) = none
        obtain ⟨col_d, hcol_d⟩ := (L.row_bijective (eOpt.symm (some 0))).2 (eOpt.symm none)
        have hd_ne : eOpt col_d ≠ none := by
          intro h0
          have hc' : col_d = eOpt.symm none := by rw [← h0, eOpt.symm_apply_apply]
          rw [hc'] at hcol_d
          have := congrArg eOpt hcol_d
          rw [hr₀, eOpt.apply_symm_apply] at this; cases this
        obtain ⟨d₀, hd₀⟩ := Option.ne_none_iff_exists'.mp hd_ne
        have hL_d0 : L.entry (eOpt.symm (some 0)) (eOpt.symm (some d₀)) = eOpt.symm none := by
          have : col_d = eOpt.symm (some d₀) := by rw [← hd₀, eOpt.symm_apply_apply]
          rwa [← this]
        -- Define h : ZMod p → ZMod p by h(d₀) = r₀ and for d ≠ d₀, some (h d) = eOpt (L(some 0, some d))
        have hrow0_some : ∀ d : ZMod p, d ≠ d₀ →
            ∃ y : ZMod p, eOpt (L.entry (eOpt.symm (some 0)) (eOpt.symm (some d))) = some y := by
          intro d hd
          apply Option.ne_none_iff_exists'.mp
          intro h0
          have heq' : L.entry (eOpt.symm (some 0)) (eOpt.symm (some d)) = eOpt.symm none := by
            rw [← h0, eOpt.symm_apply_apply]
          have := (L.row_bijective (eOpt.symm (some 0))).1 (heq'.trans hL_d0.symm)
          exact hd (Option.some.inj (eOpt.symm.injective this))
        let hfun : ZMod p → ZMod p := fun d =>
          if hd : d = d₀ then r₀ else (hrow0_some d hd).choose
        have hhfun_spec : ∀ d : ZMod p, d ≠ d₀ →
            L.entry (eOpt.symm (some 0)) (eOpt.symm (some d)) = eOpt.symm (some (hfun d)) := by
          intro d hd
          have h1 := (hrow0_some d hd).choose_spec
          have h2 : hfun d = (hrow0_some d hd).choose := dif_neg hd
          rw [h2, ← h1, eOpt.symm_apply_apply]
        have hhfun_inj : Function.Injective hfun := by
          intro d₁ d₂ heq'
          by_cases h1 : d₁ = d₀ <;> by_cases h2 : d₂ = d₀
          · exact h1.trans h2.symm
          · exfalso
            have hr1 : L.entry (eOpt.symm (some 0)) (eOpt.symm none) = eOpt.symm (some r₀) := by
              rw [← hr₀, eOpt.symm_apply_apply]
            have hr2 := hhfun_spec d₂ h2
            have heq'' : r₀ = hfun d₂ := by rwa [show hfun d₁ = r₀ from dif_pos h1] at heq'
            rw [← heq'', ← hr1] at hr2
            have := (L.row_bijective (eOpt.symm (some 0))).1 hr2
            have := eOpt.symm.injective this; cases this
          · exfalso
            have hr1 : L.entry (eOpt.symm (some 0)) (eOpt.symm none) = eOpt.symm (some r₀) := by
              rw [← hr₀, eOpt.symm_apply_apply]
            have hr2 := hhfun_spec d₁ h1
            have heq'' : hfun d₁ = r₀ := by rwa [show hfun d₂ = r₀ from dif_pos h2] at heq'
            rw [heq'', ← hr1] at hr2
            have := (L.row_bijective (eOpt.symm (some 0))).1 hr2
            have := eOpt.symm.injective this; cases this
          · have hr1 := hhfun_spec d₁ h1
            have hr2 := hhfun_spec d₂ h2
            rw [heq', ← hr2] at hr1
            exact Option.some.inj (eOpt.symm.injective ((L.row_bijective (eOpt.symm (some 0))).1 hr1))
        let hPerm : Equiv.Perm (ZMod p) :=
          Equiv.ofBijective hfun (Finite.injective_iff_bijective.mp hhfun_inj)
        -- Check complete map property & c₀ = r₀ - d₀!
        have hcol0_val : ∀ d : ZMod p, d ≠ d₀ →
            L.entry (eOpt.symm (some (-d))) (eOpt.symm (some 0)) = eOpt.symm (some (hfun d - d)) := by
          intro d hd
          have h1 := hfix_t (-d) (eOpt.symm (some 0)) (eOpt.symm (some d))
          rw [hhfun_spec d hd, htrans_some, htrans_some, htrans_some, zero_add, add_neg_cancel] at h1
          simpa [sub_eq_add_neg] using h1.symm
        have hdiff_inj : Function.Injective (fun d : ZMod p => hfun d - d) := by
          have hdiff_ne : ∀ d₁ d₂ : ZMod p, d₁ ≠ d₀ → d₂ ≠ d₀ →
              hfun d₁ - d₁ = hfun d₂ - d₂ → d₁ = d₂ := by
            intro d₁ d₂ hd1 hd2 heq'
            have h1 := hcol0_val d₁ hd1
            have h2 := hcol0_val d₂ hd2
            rw [heq', ← h2] at h1
            have h3 := (L.col_bijective (eOpt.symm (some 0))).1 h1
            exact neg_inj.mp (Option.some.inj (eOpt.symm.injective h3))
          -- Sum of (hfun d - d) over all d ∈ ZMod p is 0, and over d ≠ d₀ is ∑_{y ≠ c₀} y = -c₀!
          have hsum_all : ∑ d : ZMod p, (hfun d - d) = 0 := by
            have h1 : ∑ d : ZMod p, hfun d = ∑ d : ZMod p, d :=
              Fintype.sum_equiv hPerm _ _ (fun _ => rfl)
            rw [Finset.sum_sub_distrib, h1, sub_self]
          have hmiss : ∀ d : ZMod p, d ≠ d₀ → hfun d - d ≠ c₀ := by
            intro d hd heq'
            have h1 := hcol0_val d hd
            have h2 : L.entry (eOpt.symm none) (eOpt.symm (some 0)) = eOpt.symm (some c₀) := by
              rw [← hc₀, eOpt.symm_apply_apply]
            rw [heq', ← h2] at h1
            have := (L.col_bijective (eOpt.symm (some 0))).1 h1
            have := eOpt.symm.injective this; cases this
          have hc0_eq : hfun d₀ - d₀ = c₀ := by
            have himg : (Finset.univ.erase d₀).image (fun d => hfun d - d) = Finset.univ.erase c₀ := by
              apply Finset.eq_of_subset_of_card_le
              · intro y hy
                rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
                exact Finset.mem_erase.mpr ⟨hmiss d (Finset.mem_erase.mp hd).1, Finset.mem_univ _⟩
              · rw [Finset.card_image_of_injOn (fun d₁ hd₁ d₂ hd₂ h =>
                    hdiff_ne d₁ d₂ (Finset.mem_erase.mp hd₁).1 (Finset.mem_erase.mp hd₂).1 h),
                  Finset.card_erase_of_mem (Finset.mem_univ d₀),
                  Finset.card_erase_of_mem (Finset.mem_univ c₀)]
            have hsum_erase : ∑ d ∈ Finset.univ.erase d₀, (hfun d - d) =
                ∑ y ∈ Finset.univ.erase c₀, y := by
              rw [← himg, Finset.sum_image (fun d₁ hd₁ d₂ hd₂ h =>
                hdiff_ne d₁ d₂ (Finset.mem_erase.mp hd₁).1 (Finset.mem_erase.mp hd₂).1 h)]
            have h1 := Finset.add_sum_erase Finset.univ (fun d : ZMod p => hfun d - d) (Finset.mem_univ d₀)
            have h2 := Finset.add_sum_erase Finset.univ (fun y : ZMod p => y) (Finset.mem_univ c₀)
            have hsum_zmod : ∑ y : ZMod p, y = 0 := by
              have hneg : ∑ y : ZMod p, (-y) = ∑ y : ZMod p, y :=
                Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun _ => rfl)
              rw [Finset.sum_neg_distrib] at hneg
              have h2s : (2 : ZMod p) * ∑ y : ZMod p, y = 0 := by
                calc (2 : ZMod p) * ∑ y : ZMod p, y
                    = (∑ y : ZMod p, y) + (∑ y : ZMod p, y) := two_mul _
                  _ = -(∑ y : ZMod p, y) + (∑ y : ZMod p, y) := by rw [hneg]
                  _ = 0 := neg_add_cancel _
              have h2ne : (2 : ZMod p) ≠ 0 := by
                intro h20
                have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h20)
                have hle := Nat.le_of_dvd (by norm_num) hdvd
                have := hp.two_le; omega
              exact (mul_eq_zero.mp h2s).resolve_left h2ne
            rw [hsum_all] at h1
            rw [hsum_zmod, ← hsum_erase] at h2
            linear_combination h1 - h2
          intro d₁ d₂ heq'
          dsimp only at heq'
          by_cases h1 : d₁ = d₀ <;> by_cases h2 : d₂ = d₀
          · exact h1.trans h2.symm
          · exfalso; rw [h1, hc0_eq] at heq'; exact hmiss d₂ h2 heq'.symm
          · exfalso; rw [h2, hc0_eq] at heq'; exact hmiss d₁ h1 heq'
          · exact hdiff_ne d₁ d₂ h1 h2 heq'
        have hcomp : IsCompleteMap hPerm := Finite.injective_iff_bijective.mp hdiff_inj
        refine ⟨(d₀, ⟨hPerm, hcomp⟩), Finset.mem_univ _, ?_⟩
        -- Verify buildLS d₀ ⟨hPerm, hcomp⟩ = L entrywise!
        have hc0_eq : hPerm d₀ - d₀ = c₀ := by
          -- Re-derive quickly: if hPerm d₀ - d₀ ≠ c₀, then c₀ = hPerm d - d for some d ≠ d₀, impossible!
          obtain ⟨d, hd⟩ := hcomp.2 c₀
          by_cases hdd : d = d₀
          · rwa [← hdd]
          · exfalso
            have h1 := hcol0_val d hdd
            have h2 : L.entry (eOpt.symm none) (eOpt.symm (some 0)) = eOpt.symm (some c₀) := by
              rw [← hc₀, eOpt.symm_apply_apply]
            have hd' : hfun d - d = c₀ := hd
            rw [hd', ← h2] at h1
            have := (L.col_bijective (eOpt.symm (some 0))).1 h1
            have := eOpt.symm.injective this; cases this
        apply LatinSquare.ext; funext r c
        cases hr : eOpt r with
        | none =>
          have hr' : r = eOpt.symm none := by rw [← hr, eOpt.symm_apply_apply]
          subst hr'
          cases hc : eOpt c with
          | none =>
            have hc' : c = eOpt.symm none := by rw [← hc, eOpt.symm_apply_apply]
            subst hc'; simpa [buildLS, eOpt] using hnn.symm
          | some y =>
            have hc' : c = eOpt.symm (some y) := by rw [← hc, eOpt.symm_apply_apply]
            subst hc'
            have h1 := hfix_t y (eOpt.symm none) (eOpt.symm (some 0))
            have h2 : L.entry (eOpt.symm none) (eOpt.symm (some 0)) = eOpt.symm (some c₀) := by
              rw [← hc₀, eOpt.symm_apply_apply]
            rw [h2, htrans_none, htrans_some, htrans_some, zero_add] at h1
            simp only [buildLS, Equiv.apply_symm_apply, hc0_eq]
            rw [← h1]; congr 2; ring
        | some x =>
          have hr' : r = eOpt.symm (some x) := by rw [← hr, eOpt.symm_apply_apply]
          subst hr'
          cases hc : eOpt c with
          | none =>
            have hc' : c = eOpt.symm none := by rw [← hc, eOpt.symm_apply_apply]
            subst hc'
            have h1 := hfix_t x (eOpt.symm (some 0)) (eOpt.symm none)
            have h2 : L.entry (eOpt.symm (some 0)) (eOpt.symm none) = eOpt.symm (some r₀) := by
              rw [← hr₀, eOpt.symm_apply_apply]
            rw [h2, htrans_none, htrans_some, htrans_some, zero_add] at h1
            have hr0_eq : hPerm d₀ = r₀ := dif_pos rfl
            simp only [buildLS, Equiv.apply_symm_apply, hr0_eq]
            rw [← h1]; congr 2; ring
          | some y =>
            have hc' : c = eOpt.symm (some y) := by rw [← hc, eOpt.symm_apply_apply]
            subst hc'
            have h1 := hfix_t x (eOpt.symm (some 0)) (eOpt.symm (some (y - x)))
            rw [htrans_some, htrans_some, zero_add, sub_add_cancel] at h1
            simp only [buildLS, Equiv.apply_symm_apply]
            by_cases hd : y - x = d₀
            · rw [if_pos hd, ← h1, hd, hL_d0, htrans_none]
            · rw [if_neg hd, ← h1, hhfun_spec (y - x) hd, htrans_some]
              change eOpt.symm (some (x + hfun (y - x))) = eOpt.symm (some (hfun (y - x) + x))
              congr 2; ring
      · intro _ _; rfl
    rw [hbij, Fintype.sum_prod_type]
    simp_rw [hbuild_sign]
    have hinner : ∀ d₀ : ZMod p,
        (∑ h : Comp, (-1 : ℤ) ^ ((p - 1) / 2) * (Equiv.Perm.sign h.1 : ℤ) *
          (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ)) =
        (-1 : ℤ) ^ ((p - 1) / 2) * tauQ p := by
      intro _
      unfold tauQ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have hsum_d : (∑ d₀ : ZMod p, ∑ h : Comp,
        (-1 : ℤ) ^ ((p - 1) / 2) * (Equiv.Perm.sign h.1 : ℤ) *
          (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ)) =
        ∑ _d₀ : ZMod p, (-1 : ℤ) ^ ((p - 1) / 2) * tauQ p :=
      Finset.sum_congr rfl fun d₀ _ => hinner d₀
    rw [hsum_d, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    ring
  -- Step 4: Combine everything with lem_6_5_complete (`tauQ p = p * tQ p`, `tQ p ≡ -1 [ZMOD p]`)!
  have hcomp65 := lem_6_5_complete p hp hodd
  have hsum_all : (∑ pair : (ZMod p)ˣ × (ZMod p)ˣ, ∑ L ∈ FixLine pair.1 pair.2, (squareSign L : ℤ)) =
      ((p - 1 : ℕ) : ℤ) ^ 2 * ((p : ℤ) * (-1 : ℤ) ^ ((p - 1) / 2) * tauQ p) := by
    simp_rw [hscale_eq, hsum_11, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      ZMod.card_units, nsmul_eq_mul]
    push_cast; ring
  rw [hsum_all, hcomp65.1] at hcong1
  have hmod_p : ((p - 1 : ℕ) : ℤ) ^ 2 * tQ p ≡ -1 [ZMOD (p : ℤ)] := by
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by have := hp.one_lt; omega
    have hsq : ((p - 1 : ℕ) : ℤ) ^ 2 ≡ 1 [ZMOD (p : ℤ)] := by
      rw [hp1]
      rw [Int.modEq_iff_dvd]
      refine ⟨2 - (p : ℤ), by ring⟩
    simpa using hsq.mul hcomp65.2.1
  have hmod_p3 :
      ((p - 1 : ℕ) : ℤ) ^ 2 * ((p : ℤ) * (-1 : ℤ) ^ ((p - 1) / 2) * ((p : ℤ) * tQ p)) ≡
      (-1 : ℤ) ^ ((p + 1) / 2) * (p : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
    rw [Int.modEq_iff_dvd] at hmod_p ⊢
    rcases hmod_p with ⟨k, hk⟩
    have hhalf : (p + 1) / 2 = (p - 1) / 2 + 1 := by
      rcases hp.odd_of_ne_two hodd with ⟨m, rfl⟩; omega
    refine ⟨(-1 : ℤ) ^ ((p - 1) / 2) * k, ?_⟩
    rw [hhalf, pow_succ]
    calc (-1 : ℤ) ^ ((p - 1) / 2) * (-1) * (p : ℤ) ^ 2 -
          ((p - 1 : ℕ) : ℤ) ^ 2 * ((p : ℤ) * (-1 : ℤ) ^ ((p - 1) / 2) * ((p : ℤ) * tQ p))
        = (-1 : ℤ) ^ ((p - 1) / 2) * (p : ℤ) ^ 2 * (-1 - ((p - 1 : ℕ) : ℤ) ^ 2 * tQ p) := by ring
      _ = (-1 : ℤ) ^ ((p - 1) / 2) * (p : ℤ) ^ 2 * ((p : ℤ) * k) := by rw [hk]
      _ = (p : ℤ) ^ 3 * ((-1 : ℤ) ^ ((p - 1) / 2) * k) := by ring
  exact hcong1.trans hmod_p3

end AlonTarsi.Proofs

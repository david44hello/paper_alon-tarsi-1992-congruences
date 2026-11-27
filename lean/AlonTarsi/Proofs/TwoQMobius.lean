/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Defs.TwoQ
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Möbius Reduction, Signs, and Complete Maps for `q = n / 2`

This file proves Lemmas 6.2–6.5 of Section 6 from Lean's standard axioms alone:
* `lem_6_2_mobius`: P. Hall's Möbius reduction for any finite `q`-group acting on a finite set
  with invariant sign.
* `lem_6_3_orbred`: Rank-at-most-3 stabilizer bound and Möbius congruence for `Δ_{2q}` mod `q^6`.
* `lem_6_4_signs`: Row/column orbit sign constancy, block-permutation signs, parity of
  translations, Zolotarev's lemma, and normalizer/transposition invariance of `S(H)`.
* `lem_6_5_complete`: `τ_q = q t_q`, `t_q ≡ -1 (mod q)`, and `δ`-scaling invariance of `τ_q`.
-/

namespace AlonTarsi.Proofs

open AlonTarsi
open scoped BigOperators

/-! ### Basic Latin Square Sign & Isotopy Helpers -/

lemma delta_eq_sum_squareSign (n : ℕ) :
    delta n = ∑ L : LatinSquare n, (squareSign L : ℤ) := by
  classical
  unfold delta evenCount oddCount
  have hpart :
      (Finset.univ : Finset (LatinSquare n)) =
        Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1) ∪
        Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1) := by
    ext L
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact Int.units_eq_one_or (squareSign L)
  have hdisj :
      Disjoint
        (Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1))
        (Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1)) := by
    rw [Finset.disjoint_filter]
    intro L _ h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  conv_rhs => rw [hpart, Finset.sum_union hdisj]
  have h1 :
      ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1), (squareSign L : ℤ) =
        ((Finset.univ.filter (fun L : LatinSquare n => squareSign L = 1)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun L hL => by rw [(Finset.mem_filter.mp hL).2])]
    simp
  have h2 :
      ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1), (squareSign L : ℤ) =
        -((Finset.univ.filter (fun L : LatinSquare n => squareSign L = -1)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun L hL => by rw [(Finset.mem_filter.mp hL).2])]
    simp
  rw [h1, h2]
  ring

lemma rowPerm_isotopyAct {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) (r : Fin n) :
    rowPerm (σ • L) r = σ.2.2 * rowPerm L (σ.1.symm r) * σ.2.1⁻¹ := by
  ext c
  rfl

lemma colPerm_isotopyAct {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) (c : Fin n) :
    colPerm (σ • L) c = σ.2.2 * colPerm L (σ.2.1.symm c) * σ.1⁻¹ := by
  ext r
  rfl

lemma rowSign_isotopyAct {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) :
    rowSign (σ • L) = rowSign L * (Equiv.Perm.sign σ.2.1 * Equiv.Perm.sign σ.2.2) ^ n := by
  unfold rowSign
  have h1 : ∀ r : Fin n, Equiv.Perm.sign (rowPerm (σ • L) r) =
      Equiv.Perm.sign (rowPerm L (σ.1.symm r)) *
        (Equiv.Perm.sign σ.2.1 * Equiv.Perm.sign σ.2.2) := by
    intro r
    rw [rowPerm_isotopyAct, map_mul, map_mul, map_inv, Int.units_inv_eq_self]
    ac_rfl
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact Equiv.prod_comp σ.1.symm (fun r => Equiv.Perm.sign (rowPerm L r))

lemma colSign_isotopyAct {n : ℕ} (σ : Isotopy n) (L : LatinSquare n) :
    colSign (σ • L) = colSign L * (Equiv.Perm.sign σ.1 * Equiv.Perm.sign σ.2.2) ^ n := by
  unfold colSign
  have h1 : ∀ c : Fin n, Equiv.Perm.sign (colPerm (σ • L) c) =
      Equiv.Perm.sign (colPerm L (σ.2.1.symm c)) *
        (Equiv.Perm.sign σ.1 * Equiv.Perm.sign σ.2.2) := by
    intro c
    rw [colPerm_isotopyAct, map_mul, map_mul, map_inv, Int.units_inv_eq_self]
    ac_rfl
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact Equiv.prod_comp σ.2.1.symm (fun c => Equiv.Perm.sign (colPerm L c))

lemma squareSign_isotopyAct_even {n : ℕ} (heven : Even n) (σ : Isotopy n) (L : LatinSquare n) :
    squareSign (σ • L) = squareSign L := by
  unfold squareSign
  rw [rowSign_isotopyAct, colSign_isotopyAct]
  rcases heven with ⟨k, rfl⟩
  have hsq : ∀ u : ℤˣ, u ^ (k + k) = 1 := by
    intro u
    rw [← two_mul, pow_mul]
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  rw [hsq, hsq, mul_one, mul_one]

lemma squareSign_transposeSquare {n : ℕ} (L : LatinSquare n) :
    squareSign (transposeSquare L) = squareSign L := by
  unfold squareSign rowSign colSign transposeSquare
  have hrow : ∀ r, rowPerm (transposeSquare L) r = colPerm L r := fun _ => by ext _; rfl
  have hcol : ∀ c, colPerm (transposeSquare L) c = rowPerm L c := fun _ => by ext _; rfl
  change (∏ r, Equiv.Perm.sign (rowPerm (transposeSquare L) r)) *
      (∏ c, Equiv.Perm.sign (colPerm (transposeSquare L) c)) = _
  simp_rw [hrow, hcol]
  exact mul_comm _ _

/-! ### Lemma 6.2: Möbius Reduction for Finite `q`-Groups -/

section Mobius

open scoped Classical

/-- An elementary abelian `q`-subgroup of a group has a commutative group structure. -/
@[instance_reducible]
private def commGroupOfElemAbelian {G : Type*} [Group G] {q : ℕ} {U : Subgroup G}
    (hU : IsElemAbelian q U) : CommGroup U :=
  { (inferInstance : Group U) with
    mul_comm := fun a b => Subtype.ext (hU.1 a.1 a.2 b.1 b.2) }

/-- `Additive U` carries a `ZMod q`-vector space structure when `U` is elementary abelian of
exponent dividing `q` (with `q` prime). -/
@[instance_reducible]
private def zmodModuleOfElemAbelian {G : Type*} [Group G] {q : ℕ} [Fact q.Prime]
    {U : Subgroup G} (hU : IsElemAbelian q U) :
    @Module (ZMod q) (Additive U) _
      (@Additive.addCommGroup U (commGroupOfElemAbelian hU)).toAddCommMonoid := by
  letI : CommGroup U := commGroupOfElemAbelian hU
  have hq0 : ∀ x : Additive U, q • x = 0 := by
    intro x
    change Additive.ofMul ((Additive.toMul x) ^ q) = Additive.ofMul 1
    congr 1
    exact Subtype.ext (hU.2 (Additive.toMul x).1 (Additive.toMul x).2)
  have hmod : ∀ (n : ℕ) (x : Additive U), (n % q) • x = n • x := by
    intro n x
    have hdiv := Nat.div_add_mod n q
    conv_rhs =>
      rw [← hdiv, add_nsmul, mul_comm q (n / q), mul_nsmul, hq0, zero_add]
  refine
    { smul := fun c x => c.val • x
      one_smul := fun x => by
        change (1 : ZMod q).val • x = x
        rw [ZMod.val_one, one_nsmul]
      mul_smul := fun a b x => by
        change (a * b).val • x = a.val • (b.val • x)
        rw [ZMod.val_mul, hmod, mul_comm a.val b.val, mul_nsmul]
      smul_zero := fun a => nsmul_zero a.val
      smul_add := fun a x y => nsmul_add x y a.val
      add_smul := fun a b x => by
        change (a + b).val • x = a.val • x + b.val • x
        rw [ZMod.val_add, hmod, add_nsmul]
      zero_smul := fun x => by
        change (0 : ZMod q).val • x = 0
        rw [ZMod.val_zero, zero_nsmul] }

/-- Order of an elementary abelian `q`-subgroup `U` equals `q ^ r` where `r = elemRank q U`. -/
lemma card_eq_pow_elemRank_of_elemAbelian {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {U : Subgroup G} (hU : IsElemAbelian q U) :
    Nat.card U = q ^ elemRank q U := by
  have : Fact q.Prime := ⟨hq⟩
  let _ : CommGroup U := commGroupOfElemAbelian hU
  let _ : Module (ZMod q) (Additive U) := zmodModuleOfElemAbelian hU
  have : Finite (Additive U) := inferInstanceAs (Finite U)
  let _ : Fintype (Additive U) := Fintype.ofFinite _
  have : Module.Finite (ZMod q) (Additive U) := Module.Finite.of_finite
  have hcard : Nat.card (Additive U) = q ^ Module.finrank (ZMod q) (Additive U) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q) (V := Additive U),
      ZMod.card]
  rw [Nat.card_congr Additive.toMul] at hcard
  have hlog : elemRank q U = Module.finrank (ZMod q) (Additive U) := by
    unfold elemRank
    rw [hcard, Nat.log_pow hq.one_lt]
  rw [hlog, hcard]

/-- For an elementary abelian `q`-subgroup `U` containing a subgroup `C` of order `q`, the fiber
`{H ≤ U | H ⊔ C = U}` has Möbius weight sum `0`. -/
private lemma fiber_mobius_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {U C : Subgroup G}
    (hU : IsElemAbelian q U) (hCU : C ≤ U) (hCcard : Nat.card C = q) :
    ∑ H ∈ (Finset.univ : Finset (Subgroup G)).filter (fun H => H ≤ U ∧ H ⊔ C = U),
      (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  let _ : CommGroup U := commGroupOfElemAbelian hU
  let _ : Module (ZMod q) (Additive U) := zmodModuleOfElemAbelian hU
  have : Finite (Additive U) := inferInstanceAs (Finite U)
  let _ : Fintype (Additive U) := Fintype.ofFinite _
  have : Module.Finite (ZMod q) (Additive U) := Module.Finite.of_finite
  -- Bijection between subgroups `H ≤ U` and `ZMod q`-submodules of `Additive U`.
  let toSubmod : { H : Subgroup G // H ≤ U } → Submodule (ZMod q) (Additive U) := fun H =>
    { carrier := { x : Additive U | (Additive.toMul x).1 ∈ H.1 }
      add_mem' := fun ha hb => H.1.mul_mem ha hb
      zero_mem' := H.1.one_mem
      smul_mem' := fun c x hx => by
        show (Additive.toMul (c.val • x)).1 ∈ H.1
        have hpow : (Additive.toMul (c.val • x)).1 = (Additive.toMul x).1 ^ c.val := rfl
        rw [hpow]
        exact H.1.pow_mem hx c.val }
  let ofSubmod : Submodule (ZMod q) (Additive U) → { H : Subgroup G // H ≤ U } := fun M =>
    ⟨{ carrier := { g : G | ∃ h : g ∈ U, Additive.ofMul (⟨g, h⟩ : U) ∈ M }
       mul_mem' := fun ⟨ha, hma⟩ ⟨hb, hmb⟩ => ⟨U.mul_mem ha hb, M.add_mem hma hmb⟩
       one_mem' := ⟨U.one_mem, M.zero_mem⟩
       inv_mem' := fun ⟨ha, hma⟩ => ⟨U.inv_mem ha, M.neg_mem hma⟩ },
     fun _ ⟨h, _⟩ => h⟩
  have hleft : Function.LeftInverse ofSubmod toSubmod := by
    intro H
    apply Subtype.ext
    ext g
    constructor
    · rintro ⟨_, hg⟩; exact hg
    · intro hg; exact ⟨H.2 hg, hg⟩
  have hright : Function.RightInverse ofSubmod toSubmod := by
    intro M
    ext x
    constructor
    · rintro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨(Additive.toMul x).2, hx⟩
  -- Monotonicity and sup preservation
  have hmono : ∀ H₁ H₂ : { H : Subgroup G // H ≤ U }, H₁.1 ≤ H₂.1 ↔ toSubmod H₁ ≤ toSubmod H₂ := by
    intro H₁ H₂
    constructor
    · intro h x hx; exact h hx
    · intro h g hg; exact h (x := Additive.ofMul ⟨g, H₁.2 hg⟩) hg
  have hsup : ∀ H₁ H₂ : { H : Subgroup G // H ≤ U },
      toSubmod ⟨H₁.1 ⊔ H₂.1, sup_le H₁.2 H₂.2⟩ = toSubmod H₁ ⊔ toSubmod H₂ := by
    intro H₁ H₂
    apply le_antisymm
    · have h1 : H₁.1 ≤ (ofSubmod (toSubmod H₁ ⊔ toSubmod H₂)).1 := by
        rw [hmono, hright]; exact le_sup_left
      have h2 : H₂.1 ≤ (ofSubmod (toSubmod H₁ ⊔ toSubmod H₂)).1 := by
        rw [hmono, hright]; exact le_sup_right
      have h12 : H₁.1 ⊔ H₂.1 ≤ (ofSubmod (toSubmod H₁ ⊔ toSubmod H₂)).1 := sup_le h1 h2
      have := (hmono ⟨H₁.1 ⊔ H₂.1, sup_le H₁.2 H₂.2⟩ (ofSubmod (toSubmod H₁ ⊔ toSubmod H₂))).mp h12
      rwa [hright] at this
    · refine sup_le ?_ ?_
      · exact (hmono H₁ ⟨H₁.1 ⊔ H₂.1, sup_le H₁.2 H₂.2⟩).mp le_sup_left
      · exact (hmono H₂ ⟨H₁.1 ⊔ H₂.1, sup_le H₁.2 H₂.2⟩).mp le_sup_right
  have htop : toSubmod ⟨U, le_rfl⟩ = ⊤ := by
    ext x
    simp [toSubmod]
  -- Card of `H` equals card of `toSubmod H`
  have hcard_eq : ∀ H : { H : Subgroup G // H ≤ U }, Nat.card H.1 = Nat.card (toSubmod H) := by
    intro H
    refine Nat.card_congr
      { toFun := fun g => ⟨Additive.ofMul ⟨g.1, H.2 g.2⟩, g.2⟩
        invFun := fun x => ⟨(Additive.toMul x.1).1, x.2⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
  -- Dimensions of `U` and `LC = toSubmod ⟨C, hCU⟩`
  let LC : Submodule (ZMod q) (Additive U) := toSubmod ⟨C, hCU⟩
  have hLC_card : Nat.card LC = q := by
    rw [← hcard_eq ⟨C, hCU⟩, hCcard]
  have hLC_rank : Module.finrank (ZMod q) LC = 1 := by
    let _ : Fintype LC := Fintype.ofFinite _
    have hc : Nat.card LC = q ^ Module.finrank (ZMod q) LC := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q) (V := LC), ZMod.card]
    rw [hLC_card] at hc
    have hlog := congrArg (Nat.log q) hc
    rw [Nat.log_pow hq.one_lt] at hlog
    have hlog1 : Nat.log q q = 1 := by
      simpa using Nat.log_pow hq.one_lt 1
    rw [hlog1] at hlog
    exact hlog.symm
  let r := Module.finrank (ZMod q) (Additive U)
  have hr_pos : 1 ≤ r := by
    rw [← hLC_rank]
    exact Submodule.finrank_le LC
  have hU_rank : elemRank q U = r := by
    unfold elemRank
    have hc : Nat.card (Additive U) = q ^ r := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q) (V := Additive U),
        ZMod.card]
    rw [Nat.card_congr Additive.toMul] at hc
    rw [hc, Nat.log_pow hq.one_lt]
  -- Pick a complement `W` of `LC` in `Additive U`
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl LC
  -- Split fiber into `{U}` and complements `{H ≤ U | H ⊔ C = U ∧ H ≠ U}`
  let F := (Finset.univ : Finset (Subgroup G)).filter (fun H => H ≤ U ∧ H ⊔ C = U)
  have hU_mem : U ∈ F := by
    simp [F, sup_eq_left.mpr hCU]
  rw [← Finset.add_sum_erase _ _ hU_mem]
  -- Every `H ∈ F.erase U` corresponds to a complement `M` of `LC` in `Additive U`
  have hcompl_iff : ∀ H : { H : Subgroup G // H ≤ U },
      (H.1 ⊔ C = U ∧ H.1 ≠ U) ↔ IsCompl (toSubmod H) LC := by
    intro H
    constructor
    · rintro ⟨hsupH, hne⟩
      have hsupM : toSubmod H ⊔ LC = ⊤ := by
        rw [← hsup H ⟨C, hCU⟩]
        have heq : (⟨H.1 ⊔ C, sup_le H.2 hCU⟩ : { K : Subgroup G // K ≤ U }) = ⟨U, le_rfl⟩ :=
          Subtype.ext hsupH
        rw [heq, htop]
      have hneM : toSubmod H ≠ ⊤ := by
        intro h
        apply hne
        have := congrArg ofSubmod (h.trans htop.symm)
        rw [hleft, hleft] at this
        exact congrArg Subtype.val this
      refine ⟨?_, by rw [codisjoint_iff]; exact hsupM⟩
      rw [disjoint_iff]
      by_contra hbot
      have hle : toSubmod H ⊓ LC ≤ LC := inf_le_right
      have hfin_pos : 0 < Module.finrank (ZMod q) ↥(toSubmod H ⊓ LC) := by
        rw [Module.finrank_pos_iff]
        rw [nontrivial_iff]
        obtain ⟨x, hxmem, hx0⟩ : ∃ x ∈ toSubmod H ⊓ LC, x ≠ 0 := by
          by_contra hall
          push Not at hall
          apply hbot
          rw [eq_bot_iff]
          exact fun x hx => hall x hx
        exact ⟨⟨x, hxmem⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩
      have hfin_le : Module.finrank (ZMod q) ↥(toSubmod H ⊓ LC) ≤ Module.finrank (ZMod q) LC :=
        Submodule.finrank_mono hle
      have hfin_eq : Module.finrank (ZMod q) ↥(toSubmod H ⊓ LC) = Module.finrank (ZMod q) LC := by
        omega
      have heqLC : toSubmod H ⊓ LC = LC :=
        Submodule.eq_of_le_of_finrank_eq hle hfin_eq
      have hLCle : LC ≤ toSubmod H := inf_eq_right.mp heqLC
      have : toSubmod H = ⊤ := by
        rw [← sup_eq_left.mpr hLCle, hsupM]
      exact hneM this
    · intro hcompl
      have hsupM : toSubmod H ⊔ LC = ⊤ := hcompl.codisjoint.eq_top
      have hsupH : H.1 ⊔ C = U := by
        have := congrArg ofSubmod ((hsup H ⟨C, hCU⟩).trans (hsupM.trans htop.symm))
        rw [hleft, hleft] at this
        exact congrArg Subtype.val this
      have hne : H.1 ≠ U := by
        intro h
        have hHtop : toSubmod H = ⊤ := by
          have : H = ⟨U, le_rfl⟩ := Subtype.ext h
          rw [this, htop]
        have hLCbot : LC = ⊥ := by
          have := hcompl.disjoint.eq_bot
          rw [hHtop, top_inf_eq] at this
          exact this
        have : Module.finrank (ZMod q) LC = 0 := by rw [hLCbot]; exact finrank_bot _ _
        omega
      exact ⟨hsupH, hne⟩
  -- Every `H ∈ F.erase U` has `elemRank q H = r - 1`
  have hrank_compl : ∀ H ∈ F.erase U, elemRank q H = r - 1 := by
    intro H hH
    have hHne : H ≠ U := (Finset.mem_erase.mp hH).1
    have hHmem := (Finset.mem_filter.mp (Finset.mem_erase.mp hH).2).2
    have hcompl : IsCompl (toSubmod ⟨H, hHmem.1⟩) LC := (hcompl_iff ⟨H, hHmem.1⟩).mp ⟨hHmem.2, hHne⟩
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have hfin : Module.finrank (ZMod q) (toSubmod ⟨H, hHmem.1⟩) = r - 1 := by omega
    let _ : Fintype (toSubmod ⟨H, hHmem.1⟩) := Fintype.ofFinite _
    unfold elemRank
    rw [hcard_eq ⟨H, hHmem.1⟩, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ZMod q), ZMod.card, hfin, Nat.log_pow hq.one_lt]
  -- Count `F.erase U` via bijection with `W →ₗ[ZMod q] LC`
  let graphSubmod : (W →ₗ[ZMod q] LC) → Submodule (ZMod q) (Additive U) := fun f =>
    LinearMap.range (W.subtype + LC.subtype.comp f)
  have hgraph_compl : ∀ f : W →ₗ[ZMod q] LC, IsCompl (graphSubmod f) LC := by
    intro f
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨⟨w, rfl⟩, hxC⟩
      change (w : Additive U) + (f w : Additive U) ∈ LC at hxC
      have hwC : (w : Additive U) ∈ LC := by
        have hsub := LC.sub_mem hxC (f w).2
        simpa using hsub
      have hw0 : (w : Additive U) = 0 := by
        have hmem : (w : Additive U) ∈ LC ⊓ W := ⟨hwC, w.2⟩
        rw [hW.disjoint.eq_bot] at hmem
        exact hmem
      have hw0' : w = 0 := Subtype.ext hw0
      simp [hw0']
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x ∈ LC ⊔ W := by rw [hW.codisjoint.eq_top]; trivial
      rcases Submodule.mem_sup.mp hx with ⟨c, hc, w, hw, rfl⟩
      have hdecomp : c + w = ((w : Additive U) + (f ⟨w, hw⟩ : Additive U)) +
          (c - (f ⟨w, hw⟩ : Additive U)) := by abel
      rw [hdecomp]
      exact Submodule.add_mem_sup ⟨⟨w, hw⟩, rfl⟩ (LC.sub_mem hc (f ⟨w, hw⟩).2)
  have hgraph_inj : Function.Injective graphSubmod := by
    intro f₁ f₂ hEq
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have hmem : (w : Additive U) + (f₁ w : Additive U) ∈ graphSubmod f₂ := by
      rw [← hEq]; exact ⟨w, rfl⟩
    rcases hmem with ⟨w', hw'⟩
    change (w' : Additive U) + (f₂ w' : Additive U) = (w : Additive U) + (f₁ w : Additive U) at hw'
    have hdiff : (w' : Additive U) - (w : Additive U) = (f₁ w : Additive U) - (f₂ w' : Additive U) :=
      eq_sub_of_add_eq (by rw [sub_add_eq_add_sub, hw']; abel)
    have hWmem : (w' : Additive U) - (w : Additive U) ∈ LC ⊓ W := by
      refine ⟨?_, W.sub_mem w'.2 w.2⟩
      rw [hdiff]
      exact LC.sub_mem (f₁ w).2 (f₂ w').2
    rw [hW.disjoint.eq_bot] at hWmem
    have hww' : w' = w := Subtype.ext (sub_eq_zero.mp hWmem)
    rw [hww'] at hw'
    have hfeq : (f₁ w : Additive U) = (f₂ w : Additive U) := by
      simpa using hw'.symm
    exact hfeq
  have hgraph_surj : ∀ M : Submodule (ZMod q) (Additive U), IsCompl M LC →
      ∃ f : W →ₗ[ZMod q] LC, graphSubmod f = M := by
    intro M hM
    have hex : ∀ w : W, ∃! c : LC, (w : Additive U) + (c : Additive U) ∈ M := by
      intro w
      have hw : (w : Additive U) ∈ M ⊔ LC := by rw [hM.codisjoint.eq_top]; trivial
      rcases Submodule.mem_sup.mp hw with ⟨m, hm, c, hc, hmc⟩
      refine ⟨⟨-c, LC.neg_mem hc⟩, ?_, ?_⟩
      · change (w : Additive U) + -c ∈ M
        rw [← hmc]; simpa using hm
      · intro c' hc'
        have hsub : (c' : Additive U) - (-c) ∈ M ⊓ LC := by
          refine ⟨?_, LC.sub_mem c'.2 (LC.neg_mem hc)⟩
          have h1 : ((w : Additive U) + (c' : Additive U)) - ((w : Additive U) + -c) ∈ M :=
            M.sub_mem hc' (by rw [← hmc]; simpa using hm)
          have h2 : (c' : Additive U) - (-c) =
              ((w : Additive U) + (c' : Additive U)) - ((w : Additive U) + -c) := by abel
          rw [h2]; exact h1
        rw [hM.disjoint.eq_bot] at hsub
        exact Subtype.ext (sub_eq_zero.mp hsub)
    choose f hf huniq using hex
    let flin : W →ₗ[ZMod q] LC :=
      { toFun := f
        map_add' := fun w₁ w₂ => by
          symm
          apply huniq (w₁ + w₂)
          have h1 := M.add_mem (hf w₁) (hf w₂)
          convert h1 using 1
          simp [add_left_comm, add_comm]
        map_smul' := fun a w => by
          symm
          apply huniq (a • w)
          have h1 := M.smul_mem a (hf w)
          convert h1 using 1
          simp [smul_add] }
    refine ⟨flin, le_antisymm ?_ ?_⟩
    · rintro _ ⟨w, rfl⟩
      exact hf w
    · intro m hm
      have hm' : m ∈ LC ⊔ W := by rw [hW.codisjoint.eq_top]; trivial
      rcases Submodule.mem_sup.mp hm' with ⟨c, hc, w, hw, rfl⟩
      have hcEq : (⟨c, hc⟩ : LC) = flin ⟨w, hw⟩ := by
        apply huniq ⟨w, hw⟩
        change w + c ∈ M
        rw [add_comm]
        exact hm
      refine ⟨⟨w, hw⟩, ?_⟩
      change w + (flin ⟨w, hw⟩ : Additive U) = c + w
      rw [← hcEq, add_comm]
  have hcard_erase : (F.erase U).card = q ^ (r - 1) := by
    have : Finite (W →ₗ[ZMod q] LC) :=
      Finite.of_injective (fun f : W →ₗ[ZMod q] LC => (f : W → LC)) DFunLike.coe_injective
    let _ : Fintype (W →ₗ[ZMod q] LC) := Fintype.ofFinite _
    have hbij : (F.erase U).card = Fintype.card (W →ₗ[ZMod q] LC) := by
      symm
      refine Finset.card_bij (fun (f : W →ₗ[ZMod q] LC) _ => (ofSubmod (graphSubmod f)).1) ?_ ?_ ?_
      · intro f _
        have hcomp : IsCompl (toSubmod (ofSubmod (graphSubmod f))) LC := by
          rw [hright]; exact hgraph_compl f
        have hpair := (hcompl_iff (ofSubmod (graphSubmod f))).mpr hcomp
        exact Finset.mem_erase.mpr ⟨hpair.2,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ofSubmod (graphSubmod f)).2, hpair.1⟩⟩
      · intro f₁ _ f₂ _ hEq
        have hsub : ofSubmod (graphSubmod f₁) = ofSubmod (graphSubmod f₂) := Subtype.ext hEq
        have := congrArg toSubmod hsub
        rw [hright, hright] at this
        exact hgraph_inj this
      · intro H hH
        have hHne : H ≠ U := (Finset.mem_erase.mp hH).1
        have hHmem := (Finset.mem_filter.mp (Finset.mem_erase.mp hH).2).2
        have hcomp : IsCompl (toSubmod ⟨H, hHmem.1⟩) LC :=
          (hcompl_iff ⟨H, hHmem.1⟩).mp ⟨hHmem.2, hHne⟩
        rcases hgraph_surj _ hcomp with ⟨f, hf⟩
        refine ⟨f, Finset.mem_univ _, ?_⟩
        rw [hf]
        exact congrArg Subtype.val (hleft ⟨H, hHmem.1⟩)
    rw [hbij]
    have hW_fin : Module.finrank (ZMod q) W = r - 1 := by
      have hsum := Submodule.finrank_add_eq_of_isCompl hW
      omega
    have hhom_fin : Module.finrank (ZMod q) (W →ₗ[ZMod q] LC) = r - 1 := by
      rw [Module.finrank_linearMap, hW_fin, hLC_rank, mul_one]
    have hcard_hom := Module.card_eq_pow_finrank (K := ZMod q) (V := W →ₗ[ZMod q] LC)
    rw [ZMod.card, hhom_fin] at hcard_hom
    exact hcard_hom
  -- Evaluate the sum!
  rw [Finset.sum_congr rfl (fun H hH => by rw [hrank_compl H hH])]
  rw [Finset.sum_const, hcard_erase, nsmul_eq_mul, hU_rank]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hr_pos
  rw [hk]
  simp only [Nat.add_sub_cancel]
  have hch : (k + 1).choose 2 = k.choose 2 + k := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  rw [hch, pow_add, pow_succ]
  push_cast
  ring

/-- Hall's Möbius sum identity: for any finite `q`-group `K ≤ G`,
`∑_{H ≤ K, elem. ab.} (-1)^{r(H)} q^{C(r(H), 2)} = [K = ⊥]`. -/
private lemma hall_mobius_sum {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : q.Prime) (hp : IsPGroup q G) (K : Subgroup G) :
    ∑ H ∈ (Finset.univ : Finset (Subgroup G)).filter (fun H => H ≤ K ∧ IsElemAbelian q H),
      (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 =
      if K = ⊥ then 1 else 0 := by
  split_ifs with hK
  · subst hK
    have hfilt :
        (Finset.univ : Finset (Subgroup G)).filter (fun H => H ≤ ⊥ ∧ IsElemAbelian q H) = {⊥} := by
      ext H
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, le_bot_iff]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, ⟨fun a ha b hb => by simp [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb],
          fun a ha => by simp [Subgroup.mem_bot.mp ha]⟩⟩
    rw [hfilt, Finset.sum_singleton]
    have hbot : elemRank q (⊥ : Subgroup G) = 0 := by
      unfold elemRank
      have : Nat.card (⊥ : Subgroup G) = 1 := by simp
      rw [this, Nat.log_one_right]
    simp [hbot]
  · -- `K` is a nontrivial finite `q`-group; pick a central element `c ∈ Z(K)` of order `q`.
    have : Fact q.Prime := ⟨hq⟩
    have hKp : IsPGroup q K := hp.to_subgroup K
    have : Nontrivial K := by
      rw [nontrivial_iff]
      obtain ⟨x, hxK, hx1⟩ : ∃ x ∈ K, x ≠ 1 := by
        by_contra hall
        push Not at hall
        apply hK
        ext x
        exact ⟨fun hx => hall x hx, fun hx => by rw [hx]; exact K.one_mem⟩
      exact ⟨⟨x, hxK⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩
    have : Nontrivial (Subgroup.center K) := hKp.center_nontrivial
    have hZp : IsPGroup q (Subgroup.center K) := hKp.to_subgroup (Subgroup.center K)
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center K)
    obtain ⟨m, hm⟩ := hZp z
    have hord_dvd : orderOf z ∣ q ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨e, _, hord_eq⟩ := (Nat.dvd_prime_pow hq).mp hord_dvd
    have he_pos : 0 < e := by
      by_contra h0
      have he0 : e = 0 := by omega
      subst he0
      rw [pow_zero] at hord_eq
      exact hz1 (orderOf_eq_one_iff.mp hord_eq)
    let c₀ : Subgroup.center K := z ^ (q ^ (e - 1))
    have hc₀_ord : orderOf c₀ = q := by
      dsimp only [c₀]
      rw [orderOf_pow, hord_eq]
      have hgcd : Nat.gcd (q ^ e) (q ^ (e - 1)) = q ^ (e - 1) :=
        Nat.gcd_eq_right (Nat.pow_dvd_pow q (Nat.sub_le e 1))
      rw [hgcd, Nat.pow_div (by omega) hq.pos, Nat.sub_sub_self he_pos, pow_one]
    let c : G := c₀.1.1
    have hcK : c ∈ K := c₀.1.2
    have hc_comm : ∀ g ∈ K, g * c = c * g := by
      intro g hg
      have h := c₀.2.comm ⟨g, hg⟩
      exact (congrArg Subtype.val h).symm
    have hc_ord : orderOf c = q := by
      have h1 : orderOf (c₀.1 : K) = orderOf c₀ := Subgroup.orderOf_coe c₀
      have h2 : orderOf (c₀.1.1 : G) = orderOf (c₀.1 : K) := Subgroup.orderOf_coe c₀.1
      exact h2.trans (h1.trans hc₀_ord)
    let C : Subgroup G := Subgroup.zpowers c
    have hCK : C ≤ K := Subgroup.zpowers_le.mpr hcK
    have hCcard : Nat.card C = q := by
      rw [Nat.card_zpowers, hc_ord]
    -- Group `SK` by `H ↦ H ⊔ C`
    let SK := (Finset.univ : Finset (Subgroup G)).filter (fun H => H ≤ K ∧ IsElemAbelian q H)
    let TK := SK.filter (fun U => C ≤ U)
    have hmaps : ∀ H ∈ SK, H ⊔ C ∈ TK := by
      intro H hH
      have ⟨hHK, hHab⟩ := (Finset.mem_filter.mp hH).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, sup_le hHK hCK, ?_⟩,
        le_sup_right⟩
      have hmem_sup : ∀ x ∈ H ⊔ C, ∃ h ∈ H, ∃ k : ℤ, x = h * c ^ k := by
        have hc_pow : ∀ k : ℤ, ∀ g ∈ K, g * c ^ k = c ^ k * g := fun k g hg =>
          Commute.zpow_right (hc_comm g hg) k
        let S : Subgroup G :=
          { carrier := { x : G | ∃ h ∈ H, ∃ k : ℤ, x = h * c ^ k }
            one_mem' := ⟨1, H.one_mem, 0, by simp⟩
            mul_mem' := by
              rintro _ _ ⟨h₁, hh₁, k₁, rfl⟩ ⟨h₂, hh₂, k₂, rfl⟩
              refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ + k₂, ?_⟩
              rw [zpow_add, mul_assoc, ← mul_assoc (c ^ k₁), ← hc_pow k₁ h₂ (hHK hh₂),
                mul_assoc, mul_assoc]
            inv_mem' := by
              rintro _ ⟨h, hh, k, rfl⟩
              refine ⟨h⁻¹, H.inv_mem hh, -k, ?_⟩
              rw [mul_inv_rev, ← zpow_neg, hc_pow (-k) h⁻¹ (hHK (H.inv_mem hh))] }
        have hle : H ⊔ C ≤ S := sup_le
          (fun h hh => ⟨h, hh, 0, by simp⟩)
          (fun _ ⟨k, hk⟩ => ⟨1, H.one_mem, k, by simp [← hk]⟩)
        exact fun x hx => hle hx
      constructor
      · intro a ha b hb
        rcases hmem_sup a ha with ⟨h₁, hh₁, k₁, rfl⟩
        rcases hmem_sup b hb with ⟨h₂, hh₂, k₂, rfl⟩
        have hc_pow : ∀ k : ℤ, ∀ g ∈ K, g * c ^ k = c ^ k * g := fun k g hg =>
          Commute.zpow_right (hc_comm g hg) k
        calc (h₁ * c ^ k₁) * (h₂ * c ^ k₂)
            = h₁ * (c ^ k₁ * h₂) * c ^ k₂ := by group
          _ = h₁ * (h₂ * c ^ k₁) * c ^ k₂ := by rw [hc_pow k₁ h₂ (hHK hh₂)]
          _ = (h₁ * h₂) * (c ^ k₁ * c ^ k₂) := by group
          _ = (h₂ * h₁) * (c ^ k₂ * c ^ k₁) := by
              rw [hHab.1 h₁ hh₁ h₂ hh₂, ← zpow_add, add_comm, zpow_add]
          _ = h₂ * (h₁ * c ^ k₂) * c ^ k₁ := by group
          _ = h₂ * (c ^ k₂ * h₁) * c ^ k₁ := by rw [hc_pow k₂ h₁ (hHK hh₁)]
          _ = (h₂ * c ^ k₂) * (h₁ * c ^ k₁) := by group
      · intro a ha
        rcases hmem_sup a ha with ⟨h, hh, k, rfl⟩
        have hcomm : Commute h (c ^ k) := Commute.zpow_right (hc_comm h (hHK hh)) k
        rw [hcomm.mul_pow, hHab.2 h hh, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
          zpow_mul, zpow_natCast, ← hc_ord, pow_orderOf_eq_one, one_zpow]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_eq_zero fun U hU => ?_
    have hUmem := Finset.mem_filter.mp hU
    have ⟨hUK, hUab⟩ := (Finset.mem_filter.mp hUmem.1).2
    have hCU : C ≤ U := hUmem.2
    have hfib : SK.filter (fun H => H ⊔ C = U) =
        (Finset.univ : Finset (Subgroup G)).filter (fun H => H ≤ U ∧ H ⊔ C = U) := by
      ext H
      simp only [SK, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, _⟩, hsup⟩
        exact ⟨hsup ▸ le_sup_left, hsup⟩
      · rintro ⟨hHU, hsup⟩
        exact ⟨⟨hHU.trans hUK,
          ⟨fun a ha b hb => hUab.1 a (hHU ha) b (hHU hb),
           fun a ha => hUab.2 a (hHU ha)⟩⟩, hsup⟩
    rw [hfib]
    exact fiber_mobius_sum_eq_zero hq hUab hCU hCcard

end Mobius

/-- **Lemma 6.2**: Möbius reduction for a finite `q`-group acting on a finite set with
invariant sign `ε : X → {±1}`. -/
theorem lem_6_2_mobius {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (q : ℕ) (hq : q.Prime) (hp : IsPGroup q G)
    (ε : X → ℤˣ) (hinv : ∀ g : G, ∀ x : X, ε (g • x) = ε x) :
    (∑ x : X, (ε x : ℤ)) ≡
      -(∑ H ∈ elemAbelianNontrivial (G := G) q,
        (-1 : ℤ) ^ (elemRank q H) * (q : ℤ) ^ ((elemRank q H).choose 2) *
          signedFixSum ε H) [ZMOD (Fintype.card G : ℤ)] := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  let w : Subgroup G → ℤ := fun H =>
    (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2
  have hw_bot : w ⊥ = 1 := by
    dsimp only [w, elemRank]
    have : Nat.card (⊥ : Subgroup G) = 1 := by simp
    rw [this, Nat.log_one_right]
    simp
  -- Double counting `∑_x ε(x) * ∑_{H ≤ Stab(x), elemAb} w(H)`
  have hdouble :
      (∑ x ∈ Finset.univ.filter (fun x : X => MulAction.stabilizer G x = ⊥), (ε x : ℤ)) =
      (∑ x : X, (ε x : ℤ)) +
        ∑ H ∈ elemAbelianNontrivial (G := G) q, w H * signedFixSum ε H := by
    have hL :
        (∑ x ∈ Finset.univ.filter (fun x : X => MulAction.stabilizer G x = ⊥), (ε x : ℤ)) =
        ∑ x : X, (ε x : ℤ) *
          ∑ H ∈ Finset.univ.filter
              (fun H : Subgroup G => H ≤ MulAction.stabilizer G x ∧ IsElemAbelian q H),
            w H := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hhall := hall_mobius_sum hq hp (MulAction.stabilizer G x)
      have hsum_eq :
          (∑ H ∈ Finset.univ.filter
              (fun H : Subgroup G => H ≤ MulAction.stabilizer G x ∧ IsElemAbelian q H), w H) =
          if MulAction.stabilizer G x = ⊥ then 1 else 0 := by
        convert hhall
      rw [hsum_eq]
      split_ifs <;> simp
    rw [hL]
    have hswap :
        (∑ x : X, (ε x : ℤ) *
          ∑ H ∈ Finset.univ.filter
              (fun H : Subgroup G => H ≤ MulAction.stabilizer G x ∧ IsElemAbelian q H),
            w H) =
        ∑ H ∈ Finset.univ.filter (fun H : Subgroup G => IsElemAbelian q H),
          w H * signedFixSum ε H := by
      simp_rw [Finset.mul_sum]
      trans (∑ x : X, ∑ H : Subgroup G,
          if H ≤ MulAction.stabilizer G x ∧ IsElemAbelian q H then (ε x : ℤ) * w H else 0)
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_filter _ _
      rw [Finset.sum_comm]
      trans (∑ H : Subgroup G, if IsElemAbelian q H then w H * signedFixSum ε H else 0)
      · refine Finset.sum_congr rfl fun H _ => ?_
        split_ifs with hHab
        · unfold signedFixSum
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          have hiff : H ≤ MulAction.stabilizer G x ↔ x ∈ fixSet H := Iff.rfl
          simp only [hHab, and_true, hiff]
          split_ifs <;> ring
        · simp [hHab]
      · exact (Finset.sum_filter _ _).symm
    rw [hswap]
    have hbot_mem :
        (⊥ : Subgroup G) ∈ Finset.univ.filter (fun H : Subgroup G => IsElemAbelian q H) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨fun a ha b hb => by simp [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb],
         fun a ha => by simp [Subgroup.mem_bot.mp ha]⟩⟩
    rw [← Finset.add_sum_erase _ _ hbot_mem]
    congr 1
    · rw [hw_bot, one_mul]
      simp only [signedFixSum, fixSet, Set.mem_ofPred_eq]
      have hfix_bot : ∀ x : X, ∀ g ∈ (⊥ : Subgroup G), g • x = x := by
        intro x g hg
        rw [Subgroup.mem_bot.mp hg, one_smul]
      simp [hfix_bot]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext H
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        elemAbelianNontrivial]
  -- Show `(Fintype.card G : ℤ)` divides the sum over free points `F = {x | Stab(x) = ⊥}`
  let F : Finset X := Finset.univ.filter (fun x : X => MulAction.stabilizer G x = ⊥)
  have hfree_dvd : (Fintype.card G : ℤ) ∣ ∑ x ∈ F, (ε x : ℤ) := by
    let FreeX := { x : X // MulAction.stabilizer G x = ⊥ }
    have hstab_smul : ∀ (g : G) (x : X),
        MulAction.stabilizer G x = ⊥ → MulAction.stabilizer G (g • x) = ⊥ := by
      intro g x hx
      ext k
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
      constructor
      · intro hk
        have h1 : (g⁻¹ * k * g) • x = x := by
          rw [mul_smul, mul_smul, hk, inv_smul_smul]
        have h2 : g⁻¹ * k * g ∈ MulAction.stabilizer G x := h1
        rw [hx, Subgroup.mem_bot] at h2
        calc k = g * (g⁻¹ * k * g) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [h2]
          _ = 1 := by group
      · rintro rfl; exact one_smul _ _
    let _ : MulAction G FreeX :=
      { smul := fun g x => ⟨g • x.1, hstab_smul g x.1 x.2⟩
        one_smul := fun x => Subtype.ext (one_smul G x.1)
        mul_smul := fun g₁ g₂ x => Subtype.ext (mul_smul g₁ g₂ x.1) }
    have hsum_eq : (∑ x ∈ F, (ε x : ℤ)) = ∑ x : FreeX, (ε x.1 : ℤ) := by
      rw [Finset.sum_subtype (p := fun x : X => MulAction.stabilizer G x = ⊥) F (fun x => by simp [F])]
    rw [hsum_eq]
    let orbRel := MulAction.orbitRel G FreeX
    have : Fintype (Quotient orbRel) := Fintype.ofFinite _
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Quotient orbRel)))
        (g := Quotient.mk orbRel) (fun _ _ => Finset.mem_univ _)]
    refine Finset.dvd_sum fun o _ => ?_
    obtain ⟨x₀, rfl⟩ := Quotient.exists_rep o
    have hconst : ∀ y ∈ Finset.univ.filter (fun y : FreeX => Quotient.mk orbRel y = Quotient.mk orbRel x₀),
        (ε y.1 : ℤ) = (ε x₀.1 : ℤ) := by
      intro y hy
      have hrel : orbRel.r y x₀ := Quotient.exact (Finset.mem_filter.mp hy).2
      rcases hrel with ⟨g, hg⟩
      have hg' : g • x₀.1 = y.1 := congrArg Subtype.val hg
      rw [← hg', hinv]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard_orb :
        (Finset.univ.filter (fun y : FreeX => Quotient.mk orbRel y = Quotient.mk orbRel x₀)).card =
        Fintype.card G := by
      symm
      refine Finset.card_bij (fun (g : G) _ => g • x₀) ?_ ?_ ?_
      · intro g _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.sound ⟨g, rfl⟩⟩
      · intro g₁ _ g₂ _ hEq
        have hEq' : g₁ • x₀.1 = g₂ • x₀.1 := congrArg Subtype.val hEq
        have h1 : (g₂⁻¹ * g₁) • x₀.1 = x₀.1 := by
          rw [mul_smul, hEq', inv_smul_smul]
        have h2 : g₂⁻¹ * g₁ ∈ MulAction.stabilizer G x₀.1 := h1
        rw [x₀.2, Subgroup.mem_bot] at h2
        calc g₁ = g₂ * (g₂⁻¹ * g₁) := by group
          _ = g₂ * 1 := by rw [h2]
          _ = g₂ := mul_one g₂
      · intro y hy
        have hrel : orbRel.r y x₀ := Quotient.exact (Finset.mem_filter.mp hy).2
        rcases hrel with ⟨g, hg⟩
        exact ⟨g, Finset.mem_univ _, hg⟩
    rw [hcard_orb]
    exact dvd_mul_right _ _
  -- Conclude congruence
  rw [Int.modEq_iff_dvd]
  have hdiff :
      -(∑ H ∈ elemAbelianNontrivial (G := G) q, w H * signedFixSum ε H) - ∑ x : X, (ε x : ℤ) =
        -(∑ x ∈ F, (ε x : ℤ)) := by
    linarith [hdouble]
  change (Fintype.card G : ℤ) ∣
    -(∑ H ∈ elemAbelianNontrivial (G := G) q, w H * signedFixSum ε H) - ∑ x : X, (ε x : ℤ)
  rw [hdiff]
  exact dvd_neg.mpr hfree_dvd

/-! ### Sylow `q`-Subgroup `P ≅ F_q^6` Helpers & Lemma 6.3 -/

lemma blockTransPerm_apply {q : ℕ} [NeZero q] (u : Fin 2 → ZMod q) (a : Fin 2) (x : ZMod q) :
    blockTransPerm q u (blockEquiv q (a, x)) = blockEquiv q (a, x + u a) := by
  simp [blockTransPerm]

lemma blockTransPerm_injective (q : ℕ) [NeZero q] :
    Function.Injective (blockTransPerm q) := by
  intro u v h
  ext a
  have h0 := congrArg (fun σ => σ (blockEquiv q (a, 0))) h
  rw [blockTransPerm_apply, blockTransPerm_apply] at h0
  have h1 := (blockEquiv q).injective h0
  simpa using congrArg Prod.snd h1

lemma sylowHom_injective (q : ℕ) [NeZero q] :
    Function.Injective (sylowHom q) := by
  intro g₁ g₂ h
  have h1 : (sylowHom q g₁).1 = (sylowHom q g₂).1 := congrArg Prod.fst h
  have h2 : (sylowHom q g₁).2.1 = (sylowHom q g₂).2.1 := congrArg (fun p => p.2.1) h
  have h3 : (sylowHom q g₁).2.2 = (sylowHom q g₂).2.2 := congrArg (fun p => p.2.2) h
  have e1 := blockTransPerm_injective q h1
  have e2 := blockTransPerm_injective q h2
  have e3 := blockTransPerm_injective q h3
  apply Multiplicative.toAdd.injective
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- Group isomorphism `Multiplicative (SylowVec q) ≃* sylowP q`. -/
noncomputable def sylowMulEquiv (q : ℕ) [NeZero q] :
    Multiplicative (SylowVec q) ≃* sylowP q :=
  MulEquiv.ofBijective (sylowHom q).rangeRestrict
    ⟨fun _ _ h => sylowHom_injective q (congrArg Subtype.val h),
     fun ⟨_, ⟨v, hv⟩⟩ => ⟨v, Subtype.ext hv⟩⟩

lemma natCard_sylowP (q : ℕ) [NeZero q] : Nat.card (sylowP q) = q ^ 6 := by
  rw [← Nat.card_congr (sylowMulEquiv q).toEquiv]
  change Nat.card ((Fin 2 → ZMod q) × (Fin 2 → ZMod q) × (Fin 2 → ZMod q)) = q ^ 6
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]
  ring

lemma nsmul_eq_zero_zmod {q : ℕ} [NeZero q] (x : ZMod q) : q • x = 0 := by
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

lemma isElemAbelian_sylowP_subgroup (q : ℕ) [NeZero q] (H : Subgroup (sylowP q)) :
    IsElemAbelian q H := by
  constructor
  · intro a _ b _
    obtain ⟨va, rfl⟩ := (sylowMulEquiv q).surjective a
    obtain ⟨vb, rfl⟩ := (sylowMulEquiv q).surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact mul_comm va vb
  · intro a _
    obtain ⟨va, rfl⟩ := (sylowMulEquiv q).surjective a
    rw [← map_pow, ← map_one (sylowMulEquiv q)]
    congr 1
    change Multiplicative.ofAdd (q • Multiplicative.toAdd va) = Multiplicative.ofAdd 0
    congr 1
    ext i <;> exact nsmul_eq_zero_zmod _

lemma isPGroup_sylowP (q : ℕ) [NeZero q] (hq : q.Prime) : IsPGroup q (sylowP q) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [IsPGroup.iff_card]
  exact ⟨6, natCard_sylowP q⟩

/-- For any Latin square `L` of positive order `n`, the autotopism group `Stab(L)` has order
dividing `n! * n`. -/
lemma card_stabilizer_isotopy_dvd {n : ℕ} (hn : 0 < n) (L : LatinSquare n) :
    Nat.card (MulAction.stabilizer (Isotopy n) L) ∣ n.factorial * n := by
  classical
  let A := MulAction.stabilizer (Isotopy n) L
  let π₁ : A →* Equiv.Perm (Fin n) :=
    { toFun := fun σ => σ.1.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let K := π₁.ker
  let _ : MulAction K (Fin n) :=
    { smul := fun σ c => σ.1.1.2.1 c
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have hfree : ∀ (σ : K) (c : Fin n), σ • c = c → σ = 1 := by
    intro σ c hc
    have hrow1 : σ.1.1.1 = 1 := σ.2
    have hfix : σ.1.1 • L = L := σ.1.2
    have hcol_eq : ∀ r : Fin n, σ.1.1.2.2 (L.entry r c) = L.entry r c := by
      intro r
      have h := congrArg (fun M => M.entry r c) hfix
      change σ.1.1.2.2 (L.entry (σ.1.1.1.symm r) (σ.1.1.2.1.symm c)) = L.entry r c at h
      have hcsym : σ.1.1.2.1.symm c = c := by
        apply σ.1.1.2.1.injective
        rw [Equiv.apply_symm_apply]
        exact hc.symm
      rw [hrow1, hcsym] at h
      exact h
    have hsym1 : σ.1.1.2.2 = 1 := by
      apply Equiv.Perm.ext
      intro s
      obtain ⟨r, hr⟩ := (L.col_bijective c).2 s
      rw [← hr]
      exact hcol_eq r
    have hcol1 : σ.1.1.2.1 = 1 := by
      apply Equiv.Perm.ext
      intro c'
      have h := congrArg (fun M => M.entry ⟨0, hn⟩ (σ.1.1.2.1 c')) hfix
      change σ.1.1.2.2 (L.entry (σ.1.1.1.symm ⟨0, hn⟩) (σ.1.1.2.1.symm (σ.1.1.2.1 c'))) =
        L.entry ⟨0, hn⟩ (σ.1.1.2.1 c') at h
      rw [hrow1, hsym1, Equiv.symm_apply_apply] at h
      exact ((L.row_bijective ⟨0, hn⟩).1 h).symm
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext hrow1 (Prod.ext hcol1 hsym1)
  have hKdvd : Nat.card K ∣ n := by
    rw [Nat.card_eq_fintype_card]
    let orbRel := MulAction.orbitRel K (Fin n)
    have : Fintype (Quotient orbRel) := Fintype.ofFinite _
    have hsum : n =
        ∑ o : Quotient orbRel,
          (Finset.univ.filter (fun c : Fin n => Quotient.mk orbRel c = o)).card := by
      trans (Fintype.card (Fin n))
      · exact (Fintype.card_fin n).symm
      · rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
          (f := Quotient.mk orbRel) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    conv_rhs => rw [hsum]
    refine Finset.dvd_sum fun o _ => ?_
    obtain ⟨c₀, rfl⟩ := Quotient.exists_rep o
    have hcard_orb :
        (Finset.univ.filter (fun c : Fin n => Quotient.mk orbRel c = Quotient.mk orbRel c₀)).card =
        Fintype.card K := by
      symm
      refine Finset.card_bij (fun (σ : K) _ => σ • c₀) ?_ ?_ ?_
      · intro σ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.sound ⟨σ, rfl⟩⟩
      · intro σ₁ _ σ₂ _ hEq
        have h1 : (σ₂⁻¹ * σ₁) • c₀ = c₀ := by rw [mul_smul, hEq, inv_smul_smul]
        have h2 := hfree _ c₀ h1
        calc σ₁ = σ₂ * (σ₂⁻¹ * σ₁) := by group
          _ = σ₂ := by rw [h2, mul_one]
      · intro c hc
        rcases Quotient.exact (Finset.mem_filter.mp hc).2 with ⟨σ, hσ⟩
        exact ⟨σ, Finset.mem_univ _, hσ⟩
    rw [hcard_orb]
  have hAcard : Nat.card A = Nat.card π₁.range * Nat.card K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have h2 : Nat.card (A ⧸ K) = Nat.card π₁.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange π₁).toEquiv
    rw [← h2]
    exact h1
  have hRdvd : Nat.card π₁.range ∣ n.factorial := by
    have hd := Subgroup.card_subgroup_dvd_card π₁.range
    rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
      Fintype.card_fin] at hd
  rw [hAcard]
  exact mul_dvd_mul hRdvd hKdvd

/-- **Lemma 6.3**: Every subgroup of `P ≅ F_q^6` fixing a Latin square of order `2q` has rank
at most `3`, and `Δ_{2q} ≡ ∑_{r=1} S(H) - q ∑_{r=2} S(H) + q^3 ∑_{r=3} S(H) (mod q^6)`. -/
theorem lem_6_3_orbred (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    (∀ H : Subgroup (sylowP q),
      (fixSet (H.map (sylowP q).subtype) : Set (LatinSquare (2 * q))).Nonempty →
        elemRank q H ≤ 3) ∧
    (delta (2 * q) ≡
      (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) -
      (q : ℤ) * (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) +
      (q : ℤ) ^ 3 * (∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H) [ZMOD (q : ℤ) ^ 6]) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by
    have := hq.two_le; omega
  -- Part 1: rank ≤ 3 for any subgroup fixing a Latin square
  have hrank_le : ∀ H : Subgroup (sylowP q),
      (fixSet (H.map (sylowP q).subtype) : Set (LatinSquare (2 * q))).Nonempty →
        elemRank q H ≤ 3 := by
    intro H ⟨L, hL⟩
    have hHcard : Nat.card H = q ^ elemRank q H :=
      card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H)
    let Hmap := H.map (sylowP q).subtype
    have hHle : Hmap ≤ MulAction.stabilizer (Isotopy (2 * q)) L := by
      intro σ hσ
      exact hL σ hσ
    have hcard_map : Nat.card Hmap = Nat.card H := by
      exact Nat.card_congr (Equiv.ofBijective (fun x : H => (⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩ : Hmap))
        ⟨fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : Hmap => z.1) h)),
         fun ⟨_, ⟨x, hx, hxe⟩⟩ => ⟨⟨x, hx⟩, Subtype.ext hxe⟩⟩).symm
    have hH_dvd_stab : Nat.card H ∣ Nat.card (MulAction.stabilizer (Isotopy (2 * q)) L) := by
      rw [← hcard_map]
      exact Subgroup.card_dvd_of_le hHle
    have hstab_dvd : Nat.card (MulAction.stabilizer (Isotopy (2 * q)) L) ∣
        (2 * q).factorial * (2 * q) :=
      card_stabilizer_isotopy_dvd (by omega) L
    have hpow_dvd : q ^ elemRank q H ∣ (2 * q).factorial * (2 * q) := by
      rw [← hHcard]
      exact hH_dvd_stab.trans hstab_dvd
    have hval_2q_fact : padicValNat q (2 * q).factorial = 2 := by
      have hlt : Nat.log q (2 * q) < 2 := by
        rw [Nat.log_lt_iff_lt_pow hq.one_lt (by omega)]
        calc 2 * q < q * q := by nlinarith
          _ = q ^ 2 := (sq q).symm
      have hleg := padicValNat_factorial (p := q) (n := 2 * q) (b := 2) hlt
      rw [hleg, Finset.sum_Ico_succ_top (by omega), Finset.Ico_self, Finset.sum_empty, zero_add]
      simp [Nat.mul_div_cancel _ hq.pos]
    have hval_2q : padicValNat q (2 * q) = 1 := by
      have hcop : ¬ (q ∣ 2) := by
        intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      rw [padicValNat.mul (by omega) hq.ne_zero, padicValNat.eq_zero_of_not_dvd hcop,
        padicValNat.self hq.one_lt, zero_add]
    have hval_prod : padicValNat q ((2 * q).factorial * (2 * q)) = 3 := by
      rw [padicValNat.mul (Nat.factorial_ne_zero _) (by omega), hval_2q_fact, hval_2q]
    have hle := (padicValNat_dvd_iff_le (p := q) (n := elemRank q H)
      (a := (2 * q).factorial * (2 * q))
      (mul_ne_zero (Nat.factorial_ne_zero _) (by omega))).mp hpow_dvd
    omega
  refine ⟨hrank_le, ?_⟩
  -- Part 2: Apply Lemma 6.2 to `G = sylowP q` acting on `X = LatinSquare (2 * q)`
  let _ : MulAction (sylowP q) (LatinSquare (2 * q)) :=
    { smul := fun g L => g.1 • L
      one_smul := fun L => one_smul _ L
      mul_smul := fun g₁ g₂ L => mul_smul g₁.1 g₂.1 L }
  have hinv : ∀ (g : sylowP q) (L : LatinSquare (2 * q)),
      squareSign (g • L) = squareSign L := fun g L =>
    squareSign_isotopyAct_even ⟨q, by ring⟩ g.1 L
  have hmob := lem_6_2_mobius (G := sylowP q) (X := LatinSquare (2 * q))
    q hq (isPGroup_sylowP q hq) squareSign hinv
  have hPcard : Fintype.card (sylowP q) = q ^ 6 := by
    rw [← Nat.card_eq_fintype_card, natCard_sylowP]
  rw [← delta_eq_sum_squareSign, hPcard] at hmob
  have hfix_eq : ∀ H : Subgroup (sylowP q),
      signedFixSum (G := sylowP q) (squareSign (n := 2 * q)) H = S_twoq q H := by
    intro H
    unfold S_twoq signedFixSum fixSet
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Subgroup.mem_map,
      Subgroup.coe_subtype]
    constructor
    · rintro h _ ⟨g, hg, rfl⟩; exact h g hg
    · intro h g hg; exact h g.1 ⟨g, hg, rfl⟩
  have hrank_pos : ∀ H : Subgroup (sylowP q), H ≠ ⊥ ↔ 1 ≤ elemRank q H := by
    intro H
    have hc := card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H)
    constructor
    · intro hne
      by_contra h0
      have hr0 : elemRank q H = 0 := by omega
      rw [hr0, pow_zero] at hc
      have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hc).1
      apply hne
      ext x
      simp only [Subgroup.mem_bot]
      exact ⟨fun hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : H) 1),
             fun hx => hx ▸ H.one_mem⟩
    · intro h1 hbot
      subst hbot
      have : elemRank q (⊥ : Subgroup (sylowP q)) = 0 := by
        unfold elemRank; simp
      omega
  have hzero_ge4 : ∀ H : Subgroup (sylowP q), 4 ≤ elemRank q H → S_twoq q H = 0 := by
    intro H h4
    unfold S_twoq signedFixSum
    refine Finset.sum_eq_zero fun L hL => ?_
    have hne : (fixSet (H.map (sylowP q).subtype) : Set (LatinSquare (2 * q))).Nonempty :=
      ⟨L, (Finset.mem_filter.mp hL).2⟩
    have := hrank_le H hne
    omega
  have hsum_split :
      -(∑ H ∈ elemAbelianNontrivial (G := sylowP q) q,
        (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 *
          signedFixSum (G := sylowP q) (squareSign (n := 2 * q)) H) =
      (∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) -
      (q : ℤ) * (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) +
      (q : ℤ) ^ 3 * (∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H) := by
    simp_rw [hfix_eq]
    have : Finite (Subgroup (sylowP q)) :=
      Finite.of_injective (fun H : Subgroup (sylowP q) => (H : Set (sylowP q))) SetLike.coe_injective
    let _ : Fintype (Subgroup (sylowP q)) := Fintype.ofFinite _
    have hdisj12 : Disjoint (sylowSubgroupsOfRank q 1) (sylowSubgroupsOfRank q 2) := by
      rw [Finset.disjoint_left]; intro H h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      omega
    have hdisj123 : Disjoint (sylowSubgroupsOfRank q 1 ∪ sylowSubgroupsOfRank q 2)
        (sylowSubgroupsOfRank q 3) := by
      rw [Finset.disjoint_left]; intro H h12 h3
      have e3 := (Finset.mem_filter.mp h3).2
      rcases Finset.mem_union.mp h12 with h1 | h2
      · have e1 := (Finset.mem_filter.mp h1).2; omega
      · have e2 := (Finset.mem_filter.mp h2).2; omega
    have hsub : (sylowSubgroupsOfRank q 1 ∪ sylowSubgroupsOfRank q 2) ∪ sylowSubgroupsOfRank q 3 ⊆
        elemAbelianNontrivial (G := sylowP q) q := by
      intro H hH
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, isElemAbelian_sylowP_subgroup q H⟩
      rw [hrank_pos]
      rcases Finset.mem_union.mp hH with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · have := (Finset.mem_filter.mp h1).2; omega
        · have := (Finset.mem_filter.mp h2).2; omega
      · have := (Finset.mem_filter.mp h3).2; omega
    have hrest :
        ∑ H ∈ elemAbelianNontrivial (G := sylowP q) q,
          (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 * S_twoq q H =
        ∑ H ∈ (sylowSubgroupsOfRank q 1 ∪ sylowSubgroupsOfRank q 2) ∪ sylowSubgroupsOfRank q 3,
          (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 * S_twoq q H := by
      symm
      refine Finset.sum_subset hsub fun H hH hnot => ?_
      have hne : H ≠ ⊥ := (Finset.mem_filter.mp hH).2.1
      have h1 : 1 ≤ elemRank q H := (hrank_pos H).mp hne
      have hne1 : elemRank q H ≠ 1 := fun h => hnot (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
      have hne2 : elemRank q H ≠ 2 := fun h => hnot (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
      have hne3 : elemRank q H ≠ 3 := fun h => hnot (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      rw [hzero_ge4 H (by omega), mul_zero]
    rw [hrest, Finset.sum_union hdisj123, Finset.sum_union hdisj12]
    have s1 :
        ∑ H ∈ sylowSubgroupsOfRank q 1,
          (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 * S_twoq q H =
        -(∑ H ∈ sylowSubgroupsOfRank q 1, S_twoq q H) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun H hH => ?_
      rw [(Finset.mem_filter.mp hH).2]
      norm_num
    have s2 :
        ∑ H ∈ sylowSubgroupsOfRank q 2,
          (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 * S_twoq q H =
        (q : ℤ) * (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun H hH => ?_
      rw [(Finset.mem_filter.mp hH).2]
      norm_num
    have s3 :
        ∑ H ∈ sylowSubgroupsOfRank q 3,
          (-1 : ℤ) ^ elemRank q H * (q : ℤ) ^ (elemRank q H).choose 2 * S_twoq q H =
        -((q : ℤ) ^ 3 * (∑ H ∈ sylowSubgroupsOfRank q 3, S_twoq q H)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun H hH => ?_
      rw [(Finset.mem_filter.mp hH).2]
      have hch3 : Nat.choose 3 2 = 3 := by decide
      rw [hch3]
      ring
    rw [s1, s2, s3]
    ring
  rw [← hsum_split]
  simpa using hmob

/-! ### Lemma 6.4: Signs, Block Permutations, and Zolotarev's Lemma -/

/-- A translation `x ↦ x + t` on `ZMod q` is an even permutation for odd `q`. -/
lemma sign_addRight_eq_one {q : ℕ} [NeZero q] (hodd : Odd q) (t : ZMod q) :
    Equiv.Perm.sign (Equiv.addRight t) = 1 := by
  have hpow : (Equiv.addRight t) ^ q = 1 := by
    ext x
    have hiter : ∀ k : ℕ, ((Equiv.addRight t) ^ k) x = x + k • t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih, succ_nsmul]
        change (x + k • t) + t = x + (k • t + t)
        rw [add_assoc]
    rw [hiter q, nsmul_eq_zero_zmod, add_zero]
    rfl
  have hs : (Equiv.Perm.sign (Equiv.addRight t)) ^ q = 1 := by
    rw [← map_pow, hpow, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.addRight t)) with h | h
  · exact h
  · rw [h, hodd.neg_one_pow] at hs
    exact absurd hs (by decide)

/-- Block permutation `(b, y) ↦ (ϖ b, φ b y)` on `Fin 2 × ZMod q` has sign
`(if ϖ = 1 then 1 else -1) * sgn(φ 0) * sgn(φ 1)` for odd `q`. -/
lemma sign_blockPerm {q : ℕ} [NeZero q] (hodd : Odd q)
    (ϖ : Equiv.Perm (Fin 2)) (φ : Fin 2 → Equiv.Perm (ZMod q)) :
    Equiv.Perm.sign
      ((blockEquiv q).symm.trans <|
        ({ toFun := fun p => (ϖ p.1, φ p.1 p.2)
           invFun := fun p => (ϖ.symm p.1, (φ (ϖ.symm p.1)).symm p.2)
           left_inv := fun p => by ext <;> simp
           right_inv := fun p => by ext <;> simp } : Equiv.Perm (Fin 2 × ZMod q)).trans
        (blockEquiv q)) =
      (if ϖ = 1 then 1 else -1) * Equiv.Perm.sign (φ 0) * Equiv.Perm.sign (φ 1) := by
  let P : Equiv.Perm (Fin 2 × ZMod q) :=
    { toFun := fun p => (ϖ p.1, φ p.1 p.2)
      invFun := fun p => (ϖ.symm p.1, (φ (ϖ.symm p.1)).symm p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  have hconj : Equiv.Perm.sign ((blockEquiv q).symm.trans (P.trans (blockEquiv q))) =
      Equiv.Perm.sign P :=
    Equiv.Perm.sign_permCongr (blockEquiv q) P
  rw [hconj]
  let Pswap : Equiv.Perm (Fin 2 × ZMod q) := Equiv.prodCongr ϖ (Equiv.refl (ZMod q))
  let P0 : Equiv.Perm (Fin 2 × ZMod q) :=
    { toFun := fun p => (p.1, if p.1 = 0 then φ 0 p.2 else p.2)
      invFun := fun p => (p.1, if p.1 = 0 then (φ 0).symm p.2 else p.2)
      left_inv := fun p => Prod.ext rfl (by dsimp; split_ifs <;> simp)
      right_inv := fun p => Prod.ext rfl (by dsimp; split_ifs <;> simp) }
  let P1 : Equiv.Perm (Fin 2 × ZMod q) :=
    { toFun := fun p => (p.1, if p.1 = 1 then φ 1 p.2 else p.2)
      invFun := fun p => (p.1, if p.1 = 1 then (φ 1).symm p.2 else p.2)
      left_inv := fun p => Prod.ext rfl (by dsimp; split_ifs <;> simp)
      right_inv := fun p => Prod.ext rfl (by dsimp; split_ifs <;> simp) }
  have hfac : P = Pswap * (P0 * P1) := by
    ext ⟨b, y⟩
    · simp [P, Pswap, P0, P1]
    · fin_cases b <;> simp [P, Pswap, P0, P1]
  rw [hfac, map_mul, map_mul]
  have hP0 : Equiv.Perm.sign P0 = Equiv.Perm.sign (φ 0) := by
    let e : ZMod q ⊕ ZMod q ≃ Fin 2 × ZMod q :=
      { toFun := Sum.elim (fun y => (0, y)) (fun y => (1, y))
        invFun := fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
        left_inv := fun x => by cases x <;> simp
        right_inv := fun ⟨b, y⟩ => by fin_cases b <;> simp }
    have hcongr : e.permCongr (Equiv.Perm.sumCongr (φ 0) 1) = P0 := by
      ext ⟨b, y⟩ <;> fin_cases b <;> simp [e, P0]
    rw [← hcongr, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, map_one, mul_one]
  have hP1 : Equiv.Perm.sign P1 = Equiv.Perm.sign (φ 1) := by
    let e : ZMod q ⊕ ZMod q ≃ Fin 2 × ZMod q :=
      { toFun := Sum.elim (fun y => (0, y)) (fun y => (1, y))
        invFun := fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
        left_inv := fun x => by cases x <;> simp
        right_inv := fun ⟨b, y⟩ => by fin_cases b <;> simp }
    have hcongr : e.permCongr (Equiv.Perm.sumCongr 1 (φ 1)) = P1 := by
      ext ⟨b, y⟩ <;> fin_cases b <;> simp [e, P1]
    rw [← hcongr, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, map_one, one_mul]
  have hPswap : Equiv.Perm.sign Pswap = if ϖ = 1 then 1 else -1 := by
    split_ifs with h1
    · subst h1
      have : Pswap = 1 := by ext ⟨b, y⟩ <;> rfl
      rw [this, map_one]
    · have hϖ : ϖ = Equiv.swap (0 : Fin 2) 1 := by
        have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
        have h0 : ϖ 0 = 1 := by
          rcases hfin2 (ϖ 0) with h00 | h01
          · exfalso
            have h11 : ϖ 1 = 1 := by
              rcases hfin2 (ϖ 1) with h10 | h11
              · exact absurd (ϖ.injective (h10.trans h00.symm)) (by decide)
              · exact h11
            apply h1; ext c; fin_cases c <;> simp [h00, h11]
          · exact h01
        have h1' : ϖ 1 = 0 := by
          rcases hfin2 (ϖ 1) with h10 | h11
          · exact h10
          · exact absurd (ϖ.injective (h11.trans h0.symm)) (by decide)
        ext b
        fin_cases b <;> simp [h0, h1']
      -- Express `Pswap` as a `List.prod` of `q` disjoint transpositions
      let sw : ZMod q → Equiv.Perm (Fin 2 × ZMod q) := fun y =>
        Equiv.swap ((0 : Fin 2), y) ((1 : Fin 2), y)
      have hL : ∀ (L : List (ZMod q)), L.Nodup → ∀ (b : Fin 2) (y : ZMod q),
          (L.map sw).prod (b, y) = if y ∈ L then (Equiv.swap (0 : Fin 2) 1 b, y) else (b, y) := by
        intro L
        induction L with
        | nil => simp
        | cons a tl ih =>
          intro hnd b y
          rw [List.nodup_cons] at hnd
          rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hnd.2]
          by_cases hy : y = a
          · subst hy
            simp only [hnd.1, ↓reduceIte, List.mem_cons, true_or]
            fin_cases b <;> simp [sw, Equiv.swap_apply_left, Equiv.swap_apply_right]
          · have hne0 : (b, y) ≠ ((0 : Fin 2), a) := fun h => hy (congrArg Prod.snd h)
            have hne1 : (b, y) ≠ ((1 : Fin 2), a) := fun h => hy (congrArg Prod.snd h)
            have hne0' : (Equiv.swap (0 : Fin 2) 1 b, y) ≠ ((0 : Fin 2), a) :=
              fun h => hy (congrArg Prod.snd h)
            have hne1' : (Equiv.swap (0 : Fin 2) 1 b, y) ≠ ((1 : Fin 2), a) :=
              fun h => hy (congrArg Prod.snd h)
            by_cases hytl : y ∈ tl
            · simp only [hytl, ↓reduceIte, List.mem_cons, hy, false_or]
              exact Equiv.swap_apply_of_ne_of_ne hne0' hne1'
            · simp only [hytl, ↓reduceIte, List.mem_cons, hy, or_self]
              exact Equiv.swap_apply_of_ne_of_ne hne0 hne1
      let L : List (ZMod q) := (Finset.univ : Finset (ZMod q)).toList
      have hprod : Pswap = (L.map sw).prod := by
        apply Equiv.Perm.ext
        rintro ⟨b, y⟩
        rw [hL L (Finset.nodup_toList _)]
        have hyL : y ∈ L := Finset.mem_toList.mpr (Finset.mem_univ y)
        simp [Pswap, hϖ, hyL]
      rw [hprod, map_list_prod]
      have hmap : (L.map sw).map Equiv.Perm.sign = List.replicate L.length (-1 : ℤˣ) := by
        rw [List.map_map]
        refine List.eq_replicate_iff.mpr ⟨by simp, fun u hu => ?_⟩
        rcases List.mem_map.mp hu with ⟨y, _, rfl⟩
        exact Equiv.Perm.sign_swap (fun h => Fin.zero_ne_one (congrArg Prod.fst h))
      rw [hmap, List.prod_replicate]
      have hlen : L.length = q := by
        simp [L, ZMod.card]
      rw [hlen, hodd.neg_one_pow]
  rw [hPswap, hP0, hP1, mul_assoc]

lemma sign_blockTransPerm {q : ℕ} [NeZero q] (hodd : Odd q) (u : Fin 2 → ZMod q) :
    Equiv.Perm.sign (blockTransPerm q u) = 1 := by
  have h := sign_blockPerm hodd 1 (fun a => Equiv.addRight (u a))
  simp only [↓reduceIte, sign_addRight_eq_one hodd, mul_one] at h
  convert h using 2
  ext k
  simp [blockTransPerm]

/-- Multiplicativity of `legendreSym q (x.val : ℤ)` on `ZMod q`. -/
lemma legendreSym_val_mul {q : ℕ} [Fact q.Prime] (a b : ZMod q) :
    legendreSym q ((a * b).val : ℤ) =
      legendreSym q (a.val : ℤ) * legendreSym q (b.val : ℤ) := by
  rw [← legendreSym.mul, legendreSym.mod q ((a * b).val : ℤ),
    legendreSym.mod q ((a.val : ℤ) * (b.val : ℤ))]
  congr 1
  rw [ZMod.val_mul, Int.natCast_emod, Nat.cast_mul, Int.emod_emod]

/-- **Zolotarev's Lemma**: for an odd prime `q` and `λ ∈ (ZMod q)ˣ`, the sign of `y ↦ λ * y` on
`ZMod q` equals the Legendre symbol `legendreSym q λ`. -/
lemma sign_mulLeft_eq_legendreSym {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) (lam : (ZMod q)ˣ) :
    (Equiv.Perm.sign (Equiv.mulLeft₀ lam.1 (Units.ne_zero lam)) : ℤ) =
      legendreSym q (lam.1.val : ℤ) := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  let φ₁ : (ZMod q)ˣ →* ℤˣ :=
    { toFun := fun u => Equiv.Perm.sign (Equiv.mulLeft₀ u.1 (Units.ne_zero u))
      map_one' := by
        have : Equiv.mulLeft₀ (1 : ZMod q) one_ne_zero = 1 := by ext x; simp
        change Equiv.Perm.sign (Equiv.mulLeft₀ (1 : ZMod q) _) = 1
        rw [this, map_one]
      map_mul' := fun u v => by
        rw [← map_mul]
        congr 1
        ext x
        simp [mul_assoc] }
  let φ₂ : (ZMod q)ˣ →* ℤˣ :=
    { toFun := fun u =>
        if legendreSym q (u.1.val : ℤ) = 1 then 1 else -1
      map_one' := by
        have h1 : legendreSym q ((1 : ZMod q).val : ℤ) = 1 := by
          rw [ZMod.val_one, Nat.cast_one, legendreSym.at_one]
        change (if legendreSym q ((1 : ZMod q).val : ℤ) = 1 then (1 : ℤˣ) else -1) = 1
        rw [h1]; rfl
      map_mul' := fun u v => by
        have hval : ∀ w : (ZMod q)ˣ, legendreSym q (w.1.val : ℤ) = 1 ∨
            legendreSym q (w.1.val : ℤ) = -1 := by
          intro w
          have hsq : legendreSym q (w.1.val : ℤ) ^ 2 = 1 :=
            legendreSym.sq_one q (by simp)
          exact sq_eq_one_iff.mp hsq
        change (if legendreSym q ((u.1 * v.1).val : ℤ) = 1 then (1 : ℤˣ) else -1) =
          (if legendreSym q (u.1.val : ℤ) = 1 then (1 : ℤˣ) else -1) *
          (if legendreSym q (v.1.val : ℤ) = 1 then (1 : ℤˣ) else -1)
        rw [legendreSym_val_mul]
        rcases hval u with hu | hu <;> rcases hval v with hv | hv <;>
          rw [hu, hv] <;> decide }
  have hφ₂_coe : ∀ u : (ZMod q)ˣ, (φ₂ u : ℤ) = legendreSym q (u.1.val : ℤ) := by
    intro u
    have hsq : legendreSym q (u.1.val : ℤ) ^ 2 = 1 :=
      legendreSym.sq_one q (by simp)
    dsimp only [φ₂, MonoidHom.coe_mk, OneHom.coe_mk]
    rcases sq_eq_one_iff.mp hsq with h | h <;> rw [h] <;> decide
  rw [← hφ₂_coe lam]
  suffices h : φ₁ = φ₂ by
    change (φ₁ lam : ℤ) = (φ₂ lam : ℤ)
    rw [h]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hord_g : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hφ₂_g : φ₂ g = -1 := by
    have hnsq : ¬ IsSquare ((g.1.val : ℤ) : ZMod q) := by
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
      rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        intro h0; subst h0; simp at hy
      let uy : (ZMod q)ˣ := Units.mk0 y hy0
      have hgu : g = uy ^ 2 := by ext; simp [uy, hy, sq]
      have hpow : g ^ ((q - 1) / 2) = 1 := by
        rw [hgu, ← pow_mul]
        have hev : 2 * ((q - 1) / 2) = q - 1 := by rcases hq_odd with ⟨k, rfl⟩; omega
        rw [hev, ← ZMod.card_units q]
        exact pow_card_eq_one
      have hdvd := orderOf_dvd_of_pow_eq_one hpow
      rw [hord_g] at hdvd
      have hpos : 0 < (q - 1) / 2 := by have := hq.two_le; omega
      have hle := Nat.le_of_dvd hpos hdvd
      omega
    have hleg : legendreSym q (g.1.val : ℤ) = -1 := (legendreSym.eq_neg_one_iff q).mpr hnsq
    change (if legendreSym q (g.1.val : ℤ) = 1 then (1 : ℤˣ) else -1) = -1
    rw [hleg]; decide
  have hφ₁_g : φ₁ g = -1 := by
    let σ : Equiv.Perm (ZMod q) := Equiv.mulLeft₀ g.1 (Units.ne_zero g)
    have hcyc : σ.IsCycle := by
      refine ⟨1, ?_, ?_⟩
      · change g.1 * 1 ≠ 1
        rw [mul_one]
        intro h1
        have hg1 : g = 1 := Units.ext h1
        rw [hg1, orderOf_one] at hord_g
        have := hq.two_le; omega
      · intro y hy
        have hy0 : y ≠ 0 := by intro h0; subst h0; simp [σ] at hy
        let uy : (ZMod q)ˣ := Units.mk0 y hy0
        obtain ⟨k, hk⟩ := hg uy
        have hk' : g ^ k = uy := hk
        refine ⟨k, ?_⟩
        have hiter : ∀ (m : ℤ) (z : ZMod q), (σ ^ m) z = (g ^ m).1 * z := by
          intro m
          induction m using Int.induction_on with
          | zero => intro z; simp
          | succ n ih =>
            intro z
            rw [zpow_add_one, Equiv.Perm.mul_apply, ih, zpow_add_one]
            simp [σ, mul_assoc]
          | pred n ih =>
            intro z
            rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, zpow_sub_one]
            change (g ^ (-(n : ℤ))).1 * (g.1⁻¹ * z) = _
            rw [← mul_assoc, Units.val_mul, Units.val_inv_eq_inv_val]
        rw [hiter, hk', mul_one]
        rfl
    have hsupp : σ.support = Finset.univ.erase 0 := by
      ext x
      simp only [Equiv.Perm.mem_support, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
      constructor
      · intro hx h0; subst h0; simp [σ] at hx
      · intro hx0 heq
        have hg1 : g.1 = 1 := mul_right_cancel₀ hx0 (by simpa [σ] using heq)
        have : g = 1 := Units.ext hg1
        rw [this, orderOf_one] at hord_g
        have := hq.two_le; omega
    rw [show φ₁ g = Equiv.Perm.sign σ from rfl, hcyc.sign, hsupp,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    rcases hq_odd with ⟨k, rfl⟩
    simp [pow_mul]
  ext u
  obtain ⟨k, rfl⟩ := hg u
  rw [map_zpow, map_zpow, hφ₁_g, hφ₂_g]

/-- Helper: conjugating a block translation by `blockSwapPerm` swaps the two shift components. -/
lemma blockSwapPerm_conj_blockTransPerm {q : ℕ} [NeZero q] (u : Fin 2 → ZMod q) :
    blockSwapPerm q * blockTransPerm q u * (blockSwapPerm q)⁻¹ =
      blockTransPerm q (fun a => u (1 - a)) := by
  apply Equiv.Perm.ext; intro k
  obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective k
  have h1 : (1 : Fin 2) - (1 - a) = a := by fin_cases a <;> rfl
  change blockSwapPerm q (blockTransPerm q u ((blockSwapPerm q).symm (blockEquiv q (a, x)))) = _
  simp only [blockSwapPerm, blockTransPerm, Equiv.symm_trans_apply, Equiv.trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  congr 1; exact Prod.ext h1 rfl

/-- Helper: conjugating a block translation by `blockScalePerm` scales the `a₀`-th shift by `lam`. -/
lemma blockScalePerm_conj_blockTransPerm {q : ℕ} [NeZero q] (a₀ : Fin 2) (lam : (ZMod q)ˣ)
    (u : Fin 2 → ZMod q) :
    blockScalePerm q a₀ lam * blockTransPerm q u * (blockScalePerm q a₀ lam)⁻¹ =
      blockTransPerm q (fun a => if a = a₀ then lam.1 * u a else u a) := by
  apply Equiv.Perm.ext; intro k
  obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective k
  change blockScalePerm q a₀ lam
      (blockTransPerm q u ((blockScalePerm q a₀ lam).symm (blockEquiv q (a, x)))) = _
  simp only [blockScalePerm, blockTransPerm, Equiv.symm_trans_apply, Equiv.trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  congr 1
  ext
  · rfl
  · by_cases ha : a = a₀
    · simp only [ha, ↓reduceIte, mul_add, ← mul_assoc, Units.mul_inv, one_mul]
    · simp only [ha, ↓reduceIte]

/-- Helper: for any subgroup `H ≤ sylowP q` acting on `Fin (2 * q)` via a coordinate projection
`proj` (rows or columns) that factors through `blockTransPerm`, every orbit has size `1` or `q`,
and the product of an `H`-invariant `ℤˣ`-valued function over `Fin (2 * q)` equals the product
over any complete set of orbit representatives. -/
private lemma orbit_size_and_rep_prod {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (H : Subgroup (sylowP q))
    (proj : Isotopy (2 * q) →* Equiv.Perm (Fin (2 * q)))
    (hproj : ∀ v : SylowVec q, ∃ u : Fin 2 → ZMod q,
      proj (sylowHom q (Multiplicative.ofAdd v)) = blockTransPerm q u) :
    (∀ i : Fin (2 * q),
      Nat.card { j : Fin (2 * q) // ∃ g ∈ H, proj g.1 i = j } = 1 ∨
      Nat.card { j : Fin (2 * q) // ∃ g ∈ H, proj g.1 i = j } = q) ∧
    (∀ (f : Fin (2 * q) → ℤˣ),
      (∀ g ∈ H, ∀ i, f (proj g.1 i) = f i) →
      ∀ (R : Finset (Fin (2 * q))),
        (∀ i : Fin (2 * q), ∃! r₀ ∈ R, ∃ g ∈ H, proj g.1 r₀ = i) →
        (∏ i : Fin (2 * q), f i) = ∏ r₀ ∈ R, f r₀) := by
  classical
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have hcoord : ∀ (g : sylowP q), ∃ u : Fin 2 → ZMod q, proj g.1 = blockTransPerm q u := by
    intro g
    rcases g.2 with ⟨v, hv⟩
    rw [← hv]
    exact hproj (Multiplicative.toAdd v)
  have horb_card : ∀ i : Fin (2 * q),
      Nat.card { j : Fin (2 * q) // ∃ g ∈ H, proj g.1 i = j } = 1 ∨
      Nat.card { j : Fin (2 * q) // ∃ g ∈ H, proj g.1 i = j } = q := by
    intro i
    obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective i
    -- Define hom `φ : H →* Multiplicative (ZMod q)` reading the shift on block `a`
    have hshift : ∀ g : H, ∃! t : ZMod q,
        proj g.1.1 (blockEquiv q (a, x)) = blockEquiv q (a, x + t) := by
      intro g
      obtain ⟨u, hu⟩ := hcoord g.1
      refine ⟨u a, by rw [hu, blockTransPerm_apply], fun t ht => ?_⟩
      rw [hu, blockTransPerm_apply] at ht
      have h2 : x + u a = x + t := congrArg Prod.snd ((blockEquiv q).injective ht)
      exact (add_left_cancel h2).symm
    let φ : H →* Multiplicative (ZMod q) :=
      { toFun := fun g => Multiplicative.ofAdd (hshift g).choose
        map_one' := by
          have h1 : (hshift 1).choose = 0 := by
            apply (hshift 1).unique (hshift 1).choose_spec.1
            simp
          change Multiplicative.ofAdd (hshift 1).choose = Multiplicative.ofAdd 0
          rw [h1]
        map_mul' := fun g₁ g₂ => by
          obtain ⟨u₁, hu₁⟩ := hcoord g₁.1
          obtain ⟨u₂, hu₂⟩ := hcoord g₂.1
          have ht1 : (hshift g₁).choose = u₁ a :=
            (hshift g₁).unique (hshift g₁).choose_spec.1 (by rw [hu₁, blockTransPerm_apply])
          have ht2 : (hshift g₂).choose = u₂ a :=
            (hshift g₂).unique (hshift g₂).choose_spec.1 (by rw [hu₂, blockTransPerm_apply])
          have ht12 : (hshift (g₁ * g₂)).choose = u₁ a + u₂ a := by
            apply (hshift (g₁ * g₂)).unique (hshift (g₁ * g₂)).choose_spec.1
            change proj (g₁.1.1 * g₂.1.1) (blockEquiv q (a, x)) = _
            rw [map_mul, Equiv.Perm.mul_apply, hu₂, hu₁, blockTransPerm_apply,
              blockTransPerm_apply]
            congr 1; exact Prod.ext rfl (by ring)
          change Multiplicative.ofAdd (hshift (g₁ * g₂)).choose =
            Multiplicative.ofAdd ((hshift g₁).choose + (hshift g₂).choose)
          rw [ht1, ht2, ht12] }
    have hbij : Nat.card { j : Fin (2 * q) // ∃ g ∈ H, proj g.1 (blockEquiv q (a, x)) = j } =
        Nat.card φ.range := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
        Fintype.card_subtype]
      symm
      refine Finset.card_bij (fun (t : Multiplicative (ZMod q)) _ =>
          blockEquiv q (a, x + Multiplicative.toAdd t)) ?_ ?_ ?_
      · intro t ht
        rcases (Finset.mem_filter.mp ht).2 with ⟨g, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, g.1, g.2, (hshift g).choose_spec.1⟩
      · intro t₁ _ t₂ _ hEq
        exact Multiplicative.toAdd.injective
          (add_left_cancel (show x + Multiplicative.toAdd t₁ = x + Multiplicative.toAdd t₂ from
            congrArg Prod.snd ((blockEquiv q).injective hEq)))
      · intro j hj
        rcases (Finset.mem_filter.mp hj).2 with ⟨g, hg, rfl⟩
        refine ⟨φ ⟨g, hg⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨g, hg⟩, rfl⟩⟩, ?_⟩
        exact ((hshift ⟨g, hg⟩).choose_spec.1).symm
    rw [hbij]
    have hdvd : Nat.card φ.range ∣ Nat.card (Multiplicative (ZMod q)) :=
      Subgroup.card_subgroup_dvd_card φ.range
    have hcard_z : Nat.card (Multiplicative (ZMod q)) = q := by
      rw [Nat.card_eq_fintype_card, Fintype.card_congr Multiplicative.toAdd, ZMod.card]
    rw [hcard_z] at hdvd
    exact (Nat.dvd_prime hq).mp hdvd
  refine ⟨horb_card, fun f hfinv R hR => ?_⟩
  have hR' : ∀ i : Fin (2 * q), ∃ r₀, r₀ ∈ R ∧ (∃ g ∈ H, proj g.1 r₀ = i) ∧
      ∀ r₁, r₁ ∈ R ∧ (∃ g ∈ H, proj g.1 r₁ = i) → r₁ = r₀ := fun i => by
    rcases hR i with ⟨r₀, ⟨hr₀R, hr₀orb⟩, huniq⟩
    exact ⟨r₀, hr₀R, hr₀orb, huniq⟩
  choose rep hrep_mem hrep_orb hrep_uniq using hR'
  rw [← Finset.prod_fiberwise_of_maps_to (t := R) (g := rep) (fun i _ => hrep_mem i)]
  refine Finset.prod_congr rfl fun r₀ hr₀ => ?_
  have hfib_eq :
      (Finset.univ.filter fun i : Fin (2 * q) => rep i = r₀) =
      (Finset.univ.filter fun i : Fin (2 * q) => ∃ g ∈ H, proj g.1 r₀ = i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [← h]; exact hrep_orb i
    · intro horb; exact (hrep_uniq i r₀ ⟨hr₀, horb⟩).symm
  rw [hfib_eq]
  have hconst : ∀ i ∈ Finset.univ.filter (fun i : Fin (2 * q) => ∃ g ∈ H, proj g.1 r₀ = i),
      f i = f r₀ := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with ⟨g, hg, rfl⟩
    exact hfinv g hg r₀
  rw [Finset.prod_congr rfl hconst, Finset.prod_const]
  have hcard_eq :
      (Finset.univ.filter fun i : Fin (2 * q) => ∃ g ∈ H, proj g.1 r₀ = i).card =
      Nat.card { j : Fin (2 * q) // ∃ g ∈ H, proj g.1 r₀ = j } := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard_eq]
  rcases horb_card r₀ with h1 | hq1
  · rw [h1, pow_one]
  · rw [hq1]
    rcases Int.units_eq_one_or (f r₀) with hu | hu
    · rw [hu, one_pow]
    · rw [hu, hq_odd.neg_one_pow]

/-- **Lemma 6.4**: Orbit sign constancy and orbit-representative product formula, block
permutation / Zolotarev signs, block-swap and block-scale normalizers of `P`, and
sign-preserving bijections on `Fix(H)` under normalizers and transposition. -/
theorem lem_6_4_signs (q : ℕ) [Fact q.Prime] (hodd : q ≠ 2) :
    (∀ (H : Subgroup (sylowP q)) (L : LatinSquare (2 * q)),
      L ∈ fixSet (H.map (sylowP q).subtype) →
        (∀ g ∈ H,
          (∀ r : Fin (2 * q), Equiv.Perm.sign (rowPerm L (g.1.1 r)) =
            Equiv.Perm.sign (rowPerm L r)) ∧
          (∀ c : Fin (2 * q), Equiv.Perm.sign (colPerm L (g.1.2.1 c)) =
            Equiv.Perm.sign (colPerm L c))) ∧
        (∀ r : Fin (2 * q),
          Nat.card { r' : Fin (2 * q) // ∃ g ∈ H, g.1.1 r = r' } = 1 ∨
          Nat.card { r' : Fin (2 * q) // ∃ g ∈ H, g.1.1 r = r' } = q) ∧
        (∀ c : Fin (2 * q),
          Nat.card { c' : Fin (2 * q) // ∃ g ∈ H, g.1.2.1 c = c' } = 1 ∨
          Nat.card { c' : Fin (2 * q) // ∃ g ∈ H, g.1.2.1 c = c' } = q) ∧
        (∀ (R C : Finset (Fin (2 * q))),
          (∀ r : Fin (2 * q), ∃! r₀ ∈ R, ∃ g ∈ H, g.1.1 r₀ = r) →
          (∀ c : Fin (2 * q), ∃! c₀ ∈ C, ∃ g ∈ H, g.1.2.1 c₀ = c) →
          squareSign L =
            (∏ r ∈ R, Equiv.Perm.sign (rowPerm L r)) *
            (∏ c ∈ C, Equiv.Perm.sign (colPerm L c)))) ∧
    (∀ (ϖ : Equiv.Perm (Fin 2)) (φ : Fin 2 → Equiv.Perm (ZMod q)),
      Equiv.Perm.sign
        ((blockEquiv q).symm.trans <|
          ({ toFun := fun p => (ϖ p.1, φ p.1 p.2)
             invFun := fun p => (ϖ.symm p.1, (φ (ϖ.symm p.1)).symm p.2)
             left_inv := fun p => by ext <;> simp
             right_inv := fun p => by ext <;> simp } : Equiv.Perm (Fin 2 × ZMod q)).trans
          (blockEquiv q)) =
        (if ϖ = 1 then 1 else -1) * Equiv.Perm.sign (φ 0) * Equiv.Perm.sign (φ 1)) ∧
    (∀ t : ZMod q, Equiv.Perm.sign (Equiv.addRight t) = 1) ∧
    (∀ lam : (ZMod q)ˣ,
      (Equiv.Perm.sign (Equiv.mulLeft₀ lam.1 (Units.ne_zero lam)) : ℤ) =
        (legendreSym q (lam.1.val : ℤ))) ∧
    ((∀ g ∈ sylowP q, (blockSwapPerm q, 1, 1) * g * (blockSwapPerm q, 1, 1)⁻¹ ∈ sylowP q) ∧
     (∀ g ∈ sylowP q, (1, blockSwapPerm q, 1) * g * (1, blockSwapPerm q, 1)⁻¹ ∈ sylowP q) ∧
     (∀ g ∈ sylowP q, (1, 1, blockSwapPerm q) * g * (1, 1, blockSwapPerm q)⁻¹ ∈ sylowP q) ∧
     (∀ (a₀ : Fin 2) (lam : (ZMod q)ˣ),
       (∀ g ∈ sylowP q,
         (blockScalePerm q a₀ lam, 1, 1) * g * (blockScalePerm q a₀ lam, 1, 1)⁻¹ ∈ sylowP q) ∧
       (∀ g ∈ sylowP q,
         (1, blockScalePerm q a₀ lam, 1) * g * (1, blockScalePerm q a₀ lam, 1)⁻¹ ∈ sylowP q) ∧
       (∀ g ∈ sylowP q,
         (1, 1, blockScalePerm q a₀ lam) * g * (1, 1, blockScalePerm q a₀ lam)⁻¹ ∈ sylowP q))) ∧
    (∀ ψ : Isotopy (2 * q),
      (∀ g ∈ sylowP q, ψ * g * ψ⁻¹ ∈ sylowP q) →
      (∀ L : LatinSquare (2 * q), squareSign (ψ • L) = squareSign L) ∧
      ∀ H : Subgroup (sylowP q),
        Set.BijOn (fun L : LatinSquare (2 * q) => ψ • L)
          (fixSet (H.map (sylowP q).subtype))
          (fixSet ((H.map (sylowP q).subtype).map (MulAut.conj ψ).toMonoidHom)) ∧
        signedFixSum (squareSign (n := 2 * q))
          ((H.map (sylowP q).subtype).map (MulAut.conj ψ).toMonoidHom) = S_twoq q H) ∧
    ((∀ L : LatinSquare (2 * q), squareSign (transposeSquare L) = squareSign L) ∧
     ∀ (H : Subgroup (sylowP q)),
      Set.BijOn (transposeSquare (n := 2 * q))
        (fixSet (H.map (sylowP q).subtype))
        (fixSet ((transposeSubgroup H).map (sylowP q).subtype)) ∧
      S_twoq q (transposeSubgroup H) = S_twoq q H) := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H L hL
    have hconst : ∀ g ∈ H,
        (∀ r : Fin (2 * q), Equiv.Perm.sign (rowPerm L (g.1.1 r)) =
          Equiv.Perm.sign (rowPerm L r)) ∧
        (∀ c : Fin (2 * q), Equiv.Perm.sign (colPerm L (g.1.2.1 c)) =
          Equiv.Perm.sign (colPerm L c)) := by
      intro g hg
      have hgfix : g.1 • L = L := hL g.1 ⟨g, hg, rfl⟩
      obtain ⟨v, hv⟩ := g.2
      have hsign_col : Equiv.Perm.sign g.1.2.1 = 1 := by
        rw [← hv]; exact sign_blockTransPerm hq_odd (Multiplicative.toAdd v).2.1
      have hsign_row : Equiv.Perm.sign g.1.1 = 1 := by
        rw [← hv]; exact sign_blockTransPerm hq_odd (Multiplicative.toAdd v).1
      have hsign_sym : Equiv.Perm.sign g.1.2.2 = 1 := by
        rw [← hv]; exact sign_blockTransPerm hq_odd (Multiplicative.toAdd v).2.2
      constructor
      · intro r
        have h := congrArg (fun M => rowPerm M (g.1.1 r)) hgfix
        rw [rowPerm_isotopyAct, Equiv.symm_apply_apply] at h
        rw [← h, map_mul, map_mul, map_inv, hsign_sym, hsign_col, inv_one, one_mul, mul_one]
      · intro c
        have h := congrArg (fun M => colPerm M (g.1.2.1 c)) hgfix
        rw [colPerm_isotopyAct, Equiv.symm_apply_apply] at h
        rw [← h, map_mul, map_mul, map_inv, hsign_sym, hsign_row, inv_one, one_mul, mul_one]
    let projRow : Isotopy (2 * q) →* Equiv.Perm (Fin (2 * q)) :=
      { toFun := fun σ => σ.1, map_one' := rfl, map_mul' := fun _ _ => rfl }
    let projCol : Isotopy (2 * q) →* Equiv.Perm (Fin (2 * q)) :=
      { toFun := fun σ => σ.2.1, map_one' := rfl, map_mul' := fun _ _ => rfl }
    have hrow := orbit_size_and_rep_prod hodd H projRow (fun v => ⟨v.1, rfl⟩)
    have hcol := orbit_size_and_rep_prod hodd H projCol (fun v => ⟨v.2.1, rfl⟩)
    refine ⟨hconst, hrow.1, hcol.1, fun R C hR hC => ?_⟩
    unfold squareSign rowSign colSign
    rw [hrow.2 (fun r => Equiv.Perm.sign (rowPerm L r)) (fun g hg r => (hconst g hg).1 r) R hR,
      hcol.2 (fun c => Equiv.Perm.sign (colPerm L c)) (fun g hg c => (hconst g hg).2 c) C hC]
  · exact sign_blockPerm hq_odd
  · exact sign_addRight_eq_one hq_odd
  · exact sign_mulLeft_eq_legendreSym hodd
  · refine ⟨?_, ?_, ?_, fun a₀ lam => ⟨?_, ?_, ?_⟩⟩
    · rintro _ ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd (fun a => (Multiplicative.toAdd v).1 (1 - a),
        (Multiplicative.toAdd v).2.1, (Multiplicative.toAdd v).2.2), ?_⟩
      refine Prod.ext (blockSwapPerm_conj_blockTransPerm _).symm (Prod.ext ?_ ?_) <;>
        simp [sylowHom]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd v).1,
        fun a => (Multiplicative.toAdd v).2.1 (1 - a), (Multiplicative.toAdd v).2.2), ?_⟩
      refine Prod.ext ?_ (Prod.ext (blockSwapPerm_conj_blockTransPerm _).symm ?_) <;>
        simp [sylowHom]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd v).1,
        (Multiplicative.toAdd v).2.1, fun a => (Multiplicative.toAdd v).2.2 (1 - a)), ?_⟩
      refine Prod.ext ?_ (Prod.ext ?_ (blockSwapPerm_conj_blockTransPerm _).symm) <;>
        simp [sylowHom]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd
        (fun a => if a = a₀ then lam.1 * (Multiplicative.toAdd v).1 a else (Multiplicative.toAdd v).1 a,
        (Multiplicative.toAdd v).2.1, (Multiplicative.toAdd v).2.2), ?_⟩
      refine Prod.ext (blockScalePerm_conj_blockTransPerm a₀ lam _).symm (Prod.ext ?_ ?_) <;>
        simp [sylowHom]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd v).1,
        fun a => if a = a₀ then lam.1 * (Multiplicative.toAdd v).2.1 a else (Multiplicative.toAdd v).2.1 a,
        (Multiplicative.toAdd v).2.2), ?_⟩
      refine Prod.ext ?_ (Prod.ext (blockScalePerm_conj_blockTransPerm a₀ lam _).symm ?_) <;>
        simp [sylowHom]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Multiplicative.ofAdd ((Multiplicative.toAdd v).1,
        (Multiplicative.toAdd v).2.1,
        fun a => if a = a₀ then lam.1 * (Multiplicative.toAdd v).2.2 a else (Multiplicative.toAdd v).2.2 a), ?_⟩
      refine Prod.ext ?_ (Prod.ext ?_ (blockScalePerm_conj_blockTransPerm a₀ lam _).symm) <;>
        simp [sylowHom]
  · intro ψ _
    refine ⟨fun L => squareSign_isotopyAct_even ⟨q, by ring⟩ ψ L, fun H => ?_⟩
    have hbij : Set.BijOn (fun L : LatinSquare (2 * q) => ψ • L)
        (fixSet (H.map (sylowP q).subtype))
        (fixSet ((H.map (sylowP q).subtype).map (MulAut.conj ψ).toMonoidHom)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro L hL
        rintro _ ⟨σ, hσ, rfl⟩
        change (ψ * σ * ψ⁻¹) • (ψ • L) = ψ • L
        rw [mul_smul, mul_smul, inv_smul_smul, hL σ hσ]
      · intro L₁ _ L₂ _ hEq
        have := congrArg (ψ⁻¹ • ·) hEq
        simpa using this
      · intro L hL
        refine ⟨ψ⁻¹ • L, ?_, smul_inv_smul ψ L⟩
        intro σ hσ
        have h1 := hL (ψ * σ * ψ⁻¹) ⟨σ, hσ, rfl⟩
        have h2 := congrArg (ψ⁻¹ • ·) h1
        rw [← mul_smul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_smul] at h2
        exact h2
    refine ⟨hbij, ?_⟩
    classical
    unfold S_twoq signedFixSum
    symm
    refine Finset.sum_bij (fun (L : LatinSquare (2 * q)) _ => ψ • L) ?_ ?_ ?_ ?_
    · intro L hL
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbij.mapsTo (Finset.mem_filter.mp hL).2⟩
    · intro L₁ h₁ L₂ h₂ hEq
      exact hbij.injOn (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2 hEq
    · intro L hL
      rcases hbij.surjOn (Finset.mem_filter.mp hL).2 with ⟨L₀, hL₀, rfl⟩
      exact ⟨L₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL₀⟩, rfl⟩
    · intro L _
      rw [squareSign_isotopyAct_even ⟨q, by ring⟩]
  · refine ⟨fun L => squareSign_transposeSquare L, fun H => ?_⟩
    have hbij : Set.BijOn (transposeSquare (n := 2 * q))
        (fixSet (H.map (sylowP q).subtype))
        (fixSet ((transposeSubgroup H).map (sylowP q).subtype)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro L hL
        rintro σ ⟨g', hg', rfl⟩
        rcases hg' with ⟨g, hg, hge⟩
        have hσ : g'.1 = (g.1.2.1, g.1.1, g.1.2.2) := (congrArg Subtype.val hge).symm
        have h1 := hL g.1 ⟨g, hg, rfl⟩
        apply LatinSquare.ext
        funext r c
        change (g'.1 • transposeSquare L).entry r c = (transposeSquare L).entry r c
        rw [hσ]
        exact congrArg (fun M => M.entry c r) h1
      · intro L₁ _ L₂ _ hEq
        apply LatinSquare.ext
        funext r c
        exact congrArg (fun M => M.entry c r) hEq
      · intro L hL
        refine ⟨transposeSquare L, ?_, LatinSquare.ext rfl⟩
        rintro _ ⟨g, hg, rfl⟩
        have h1 := hL (g.1.2.1, g.1.1, g.1.2.2) ⟨⟨(g.1.2.1, g.1.1, g.1.2.2), by
          rcases g.2 with ⟨v, hv⟩
          refine ⟨Multiplicative.ofAdd
            ((Multiplicative.toAdd v).2.1, (Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2.2),
            ?_⟩
          rw [← hv]; rfl⟩, ⟨g, hg, rfl⟩, rfl⟩
        apply LatinSquare.ext
        funext r c
        exact congrArg (fun M => M.entry c r) h1
    refine ⟨hbij, ?_⟩
    classical
    unfold S_twoq signedFixSum
    symm
    refine Finset.sum_bij (fun (L : LatinSquare (2 * q)) _ => transposeSquare L) ?_ ?_ ?_ ?_
    · intro L hL
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbij.mapsTo (Finset.mem_filter.mp hL).2⟩
    · intro L₁ h₁ L₂ h₂ hEq
      exact hbij.injOn (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2 hEq
    · intro L hL
      rcases hbij.surjOn (Finset.mem_filter.mp hL).2 with ⟨L₀, hL₀, rfl⟩
      exact ⟨L₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL₀⟩, rfl⟩
    · intro L _
      rw [squareSign_transposeSquare]

/-! ### Jacobsthal Identity & Lemma 6.5 (Complete Maps) -/

/-- Sum of Legendre symbols over `ZMod q` vanishes for odd prime `q`. -/
lemma sum_legendreSym_eq_zero {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ x : ZMod q, legendreSym q (x.val : ℤ) = 0 := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hord_g : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hleg_g : legendreSym q (g.1.val : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff q]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by intro h0; subst h0; simp at hy
    let uy : (ZMod q)ˣ := Units.mk0 y hy0
    have hgu : g = uy ^ 2 := by ext; simp [uy, hy, sq]
    have hpow : g ^ ((q - 1) / 2) = 1 := by
      rw [hgu, ← pow_mul]
      have hev : 2 * ((q - 1) / 2) = q - 1 := by rcases hq_odd with ⟨k, rfl⟩; omega
      rw [hev, ← ZMod.card_units q]
      exact pow_card_eq_one
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hord_g] at hdvd
    have hpos : 0 < (q - 1) / 2 := by have := hq.two_le; omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hmul : ∀ x : ZMod q,
      legendreSym q ((g.1 * x).val : ℤ) = -legendreSym q (x.val : ℤ) := by
    intro x
    rw [legendreSym_val_mul, hleg_g, neg_one_mul]
  have hsum := Equiv.sum_comp (Equiv.mulLeft₀ g.1 (Units.ne_zero g))
    (fun x : ZMod q => legendreSym q (x.val : ℤ))
  simp only [Equiv.mulLeft₀_apply, hmul, Finset.sum_neg_distrib] at hsum
  linarith

/-- Classical Jacobsthal identity: `∑_{x ∈ F_q} χ(x (x + c)) = -1` for `c ≠ 0`. -/
lemma jacobsthal_sum {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) {c : ZMod q} (hc : c ≠ 0) :
    ∑ x : ZMod q, legendreSym q ((x * (x + c)).val : ℤ) = -1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
  have h0 : legendreSym q (((0 : ZMod q) * (0 + c)).val : ℤ) = 0 := by
    simp [legendreSym.at_zero]
  rw [h0, zero_add]
  have hterm : ∀ x ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      legendreSym q ((x * (x + c)).val : ℤ) = legendreSym q ((1 + c * x⁻¹).val : ℤ) := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have heq : x * (x + c) = (x * x) * (1 + c * x⁻¹) := by
      field_simp [hx0]
    rw [heq, legendreSym_val_mul, legendreSym_val_mul]
    have hsq : legendreSym q (x.val : ℤ) * legendreSym q (x.val : ℤ) = 1 := by
      rw [← sq]
      exact legendreSym.sq_one q (by simpa using hx0)
    rw [hsq, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have hbij :
      ∑ x ∈ (Finset.univ : Finset (ZMod q)).erase 0, legendreSym q ((1 + c * x⁻¹).val : ℤ) =
      ∑ y ∈ (Finset.univ : Finset (ZMod q)).erase 1, legendreSym q (y.val : ℤ) := by
    refine Finset.sum_bij (fun x _ => 1 + c * x⁻¹) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro x hx
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h1
      have : c * x⁻¹ = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with hc0 | hxi
      · exact hc hc0
      · exact hx0 (inv_eq_zero.mp hxi)
    · intro x₁ _ x₂ _ hEq
      have h1 : c * x₁⁻¹ = c * x₂⁻¹ := by linear_combination hEq
      have h2 : x₁⁻¹ = x₂⁻¹ := mul_left_cancel₀ hc h1
      exact inv_injective h2
    · intro y hy
      have hy1 : y ≠ 1 := (Finset.mem_erase.mp hy).1
      have hsub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
      refine ⟨c * (y - 1)⁻¹, Finset.mem_erase.mpr ⟨mul_ne_zero hc (inv_ne_zero hsub),
        Finset.mem_univ _⟩, ?_⟩
      field_simp [hc, hsub]
      ring
  rw [hbij]
  have htot := sum_legendreSym_eq_zero (q := q) hodd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ZMod q))] at htot
  have h1 : legendreSym q ((1 : ZMod q).val : ℤ) = 1 := by
    rw [ZMod.val_one, Nat.cast_one, legendreSym.at_one]
  linarith

/-- **Lemma 6.5**: For odd prime `q`, `τ_q = q * t_q`, `t_q ≡ -1 (mod q)`, and the
`δ`-scaled complete-map signed sum equals `τ_q` for every `δ ≠ 0`. -/
theorem lem_6_5_complete (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    tauQ q = (q : ℤ) * tQ q ∧
    tQ q ≡ -1 [ZMOD (q : ℤ)] ∧
    ∀ δ : ZMod q, δ ≠ 0 →
      (∑ h : { h : Equiv.Perm (ZMod q) // Function.Bijective (fun x => h x - δ * x) },
        (Equiv.Perm.sign h.1 : ℤ) *
          (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - δ * x) h.2) : ℤ)) =
      tauQ q := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  let CM := { h : Equiv.Perm (ZMod q) // IsCompleteMap h }
  let wt : CM → ℤ := fun h =>
    (Equiv.Perm.sign h.1 : ℤ) *
      (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ)
  -- Action of `Multiplicative (ZMod q × ZMod q)` on `CM`: `(a, b) • h = x ↦ h (x - a) + b`
  let shiftCM (a b : ZMod q) (h : CM) : CM :=
    ⟨(Equiv.addRight (-a)).trans (h.1.trans (Equiv.addRight b)), by
      have hbij : (fun x : ZMod q => (h.1 (x + -a) + b) - x) =
          (fun y => y + (b - a)) ∘ (fun z => h.1 z - z) ∘ (fun x => x + -a) := by
        ext x; simp only [Function.comp_apply]; ring
      change Function.Bijective (fun x : ZMod q => (h.1 (x + -a) + b) - x)
      rw [hbij]
      exact (Equiv.addRight (b - a)).bijective.comp
        (h.2.comp (Equiv.addRight (-a)).bijective)⟩
  have hwt_shift : ∀ (a b : ZMod q) (h : CM), wt (shiftCM a b h) = wt h := by
    intro a b h
    dsimp only [wt]
    have h1 : Equiv.Perm.sign (shiftCM a b h).1 = Equiv.Perm.sign h.1 := by
      change Equiv.Perm.sign (Equiv.addRight b * (h.1 * Equiv.addRight (-a))) = _
      rw [map_mul, map_mul, sign_addRight_eq_one hq_odd, sign_addRight_eq_one hq_odd,
        one_mul, mul_one]
    have h2 : Equiv.ofBijective (fun x : ZMod q => (shiftCM a b h).1 x - x) (shiftCM a b h).2 =
        Equiv.addRight (b - a) *
          (Equiv.ofBijective (fun z => h.1 z - z) h.2 * Equiv.addRight (-a)) := by
      apply Equiv.Perm.ext
      intro x
      change (h.1 (x + -a) + b) - x = (h.1 (x + -a) - (x + -a)) + (b - a)
      ring
    rw [h1, h2, map_mul, map_mul, sign_addRight_eq_one hq_odd, sign_addRight_eq_one hq_odd,
      one_mul, mul_one]
  -- Part 1: `tauQ q = q * tQ q`
  have hpart1 : tauQ q = (q : ℤ) * tQ q := by
    change ∑ h : CM, wt h = (q : ℤ) * ∑ h ∈ Finset.univ.filter (fun h : CM => h.1 0 = 0), wt h
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (ZMod q)))
      (g := fun h : CM => h.1 0) (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ c : ZMod q,
        ∑ h ∈ Finset.univ.filter (fun h : CM => h.1 0 = c), wt h =
        ∑ h ∈ Finset.univ.filter (fun h : CM => h.1 0 = 0), wt h := by
      intro c
      refine Finset.sum_bij (fun h _ => shiftCM 0 (-c) h) ?_ ?_ ?_ ?_
      · intro h hh
        have hc := (Finset.mem_filter.mp hh).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change h.1 (0 + -0) + -c = 0
        rw [neg_zero, add_zero, hc, add_neg_cancel]
      · intro h₁ _ h₂ _ hEq
        apply Subtype.ext; ext x
        have hx := congrArg (fun k => k.1 x) hEq
        change h₁.1 (x + -0) + -c = h₂.1 (x + -0) + -c at hx
        simpa using hx
      · intro h hh
        have h0 := (Finset.mem_filter.mp hh).2
        refine ⟨shiftCM 0 c h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · change h.1 (0 + -0) + c = c; simp [h0]
        · apply Subtype.ext; ext x
          change (h.1 ((x + -0) + -0) + c) + -c = h.1 x
          simp
      · intro h _; exact (hwt_shift 0 (-c) h).symm
    simp_rw [hfib]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  -- Part 2: `tQ q ≡ -1 [ZMOD q]` via the `F_q^2` action
  have hpart2 : tQ q ≡ -1 [ZMOD (q : ℤ)] := by
    let G := Multiplicative (ZMod q × ZMod q)
    let _ : MulAction G CM :=
      { smul := fun g h => shiftCM (Multiplicative.toAdd g).1 (Multiplicative.toAdd g).2 h
        one_smul := fun h => by
          apply Subtype.ext; ext x; change h.1 (x + -0) + 0 = h.1 x; simp
        mul_smul := fun g₁ g₂ h => by
          apply Subtype.ext; ext x
          change h.1 (x + -((Multiplicative.toAdd g₁).1 + (Multiplicative.toAdd g₂).1)) +
            ((Multiplicative.toAdd g₁).2 + (Multiplicative.toAdd g₂).2) =
            h.1 ((x + -(Multiplicative.toAdd g₁).1) + -(Multiplicative.toAdd g₂).1) +
              (Multiplicative.toAdd g₂).2 + (Multiplicative.toAdd g₁).2
          have h1 : x + -((Multiplicative.toAdd g₁).1 + (Multiplicative.toAdd g₂).1) =
              (x + -(Multiplicative.toAdd g₁).1) + -(Multiplicative.toAdd g₂).1 := by ring
          rw [h1]; ring }
    let isAff : CM → Prop := fun h => ∃ (lam e : ZMod q), ∀ x, h.1 x = lam * x + e
    have hsplit : tauQ q =
        (∑ h ∈ Finset.univ.filter isAff, wt h) +
        (∑ h ∈ Finset.univ.filter (fun h => ¬ isAff h), wt h) := by
      change ∑ h : CM, wt h = _
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ isAff wt]
    have hnonaff_free : ∀ h : CM, ¬ isAff h → MulAction.stabilizer G h = ⊥ := by
      intro h hna
      ext g
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
      constructor
      · intro hg
        by_contra hg1
        let a := (Multiplicative.toAdd g).1
        let b := (Multiplicative.toAdd g).2
        have hstep : ∀ x : ZMod q, h.1 (x - a) + b = h.1 x := by
          intro x
          have hx : (g • h).1 x = h.1 x := congrArg (fun k => k.1 x) hg
          change h.1 (x + -a) + b = h.1 x at hx
          rwa [← sub_eq_add_neg] at hx
        have ha0 : a ≠ 0 := by
          intro ha
          have hb0 : b ≠ 0 := by
            intro hb
            apply hg1
            apply Multiplicative.toAdd.injective
            exact Prod.ext ha hb
          have h0 := hstep 0
          rw [ha, sub_zero] at h0
          have : b = 0 := by linear_combination h0
          exact hb0 this
        have hlin : ∀ k : ℕ, h.1 ((k : ZMod q) * a) = (k : ZMod q) * b + h.1 0 := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            have hs := hstep (((k : ZMod q) + 1) * a)
            have hsub : ((k : ZMod q) + 1) * a - a = (k : ZMod q) * a := by ring
            rw [hsub, ih] at hs
            push_cast
            linear_combination -hs
        apply hna
        refine ⟨b * a⁻¹, h.1 0, fun x => ?_⟩
        let y : ZMod q := x * a⁻¹
        have hy : ((y.val : ℕ) : ZMod q) = y := ZMod.natCast_zmod_val y
        have hxa : x = ((y.val : ℕ) : ZMod q) * a := by
          rw [hy]; dsimp only [y]; field_simp [ha0]
        rw [hxa, hlin y.val, hy]
        dsimp only [y]
        field_simp [ha0]
      · rintro rfl; exact one_smul _ _
    have hnonaff_dvd : (q : ℤ) ^ 2 ∣ ∑ h ∈ Finset.univ.filter (fun h => ¬ isAff h), wt h := by
      let NA := { h : CM // ¬ isAff h }
      have hna_smul : ∀ (g : G) (h : CM), ¬ isAff h → ¬ isAff (g • h) := by
        intro g h hna ⟨lam, e, hle⟩
        apply hna
        refine ⟨lam, e - (Multiplicative.toAdd g).2 + lam * (Multiplicative.toAdd g).1, fun x => ?_⟩
        have hx := hle (x + (Multiplicative.toAdd g).1)
        change h.1 ((x + (Multiplicative.toAdd g).1) + -(Multiplicative.toAdd g).1) +
            (Multiplicative.toAdd g).2 = _ at hx
        simp only [add_neg_cancel_right] at hx
        linear_combination hx
      let _ : MulAction G NA :=
        { smul := fun g h => ⟨g • h.1, hna_smul g h.1 h.2⟩
          one_smul := fun h => Subtype.ext (one_smul _ _)
          mul_smul := fun g₁ g₂ h => Subtype.ext (mul_smul _ _ _) }
      have hsum_na : (∑ h ∈ Finset.univ.filter (fun h => ¬ isAff h), wt h) =
          ∑ h : NA, wt h.1 := by
        rw [Finset.sum_subtype (p := fun h => ¬ isAff h)
          (Finset.univ.filter (fun h => ¬ isAff h)) (fun _ => by simp)]
      rw [hsum_na]
      let orbRel := MulAction.orbitRel G NA
      have : Fintype (Quotient orbRel) := Fintype.ofFinite _
      rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Quotient orbRel)))
        (g := Quotient.mk orbRel) (fun _ _ => Finset.mem_univ _)]
      refine Finset.dvd_sum fun o _ => ?_
      obtain ⟨h₀, rfl⟩ := Quotient.exists_rep o
      have hconst : ∀ y ∈ Finset.univ.filter (fun y : NA => Quotient.mk orbRel y = Quotient.mk orbRel h₀),
          wt y.1 = wt h₀.1 := by
        intro y hy
        rcases Quotient.exact (Finset.mem_filter.mp hy).2 with ⟨g, hg⟩
        have hg' : g • h₀.1 = y.1 := congrArg Subtype.val hg
        rw [← hg']
        exact hwt_shift _ _ _
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard_orb :
          (Finset.univ.filter (fun y : NA => Quotient.mk orbRel y = Quotient.mk orbRel h₀)).card =
          q ^ 2 := by
        have hGcard : Fintype.card G = q ^ 2 := by
          rw [Fintype.card_congr Multiplicative.toAdd]
          simp [ZMod.card, sq]
        rw [← hGcard]
        symm
        refine Finset.card_bij (fun (g : G) _ => g • h₀) ?_ ?_ ?_
        · intro g _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.sound ⟨g, rfl⟩⟩
        · intro g₁ _ g₂ _ hEq
          have hEq' : g₁ • h₀.1 = g₂ • h₀.1 := congrArg Subtype.val hEq
          have h1 : (g₂⁻¹ * g₁) • h₀.1 = h₀.1 := by
            rw [mul_smul, hEq', inv_smul_smul]
          have h2 : g₂⁻¹ * g₁ ∈ MulAction.stabilizer G h₀.1 := h1
          rw [hnonaff_free h₀.1 h₀.2, Subgroup.mem_bot] at h2
          calc g₁ = g₂ * (g₂⁻¹ * g₁) := (mul_inv_cancel_left g₂ g₁).symm
            _ = g₂ := by rw [h2, mul_one]
        · intro y hy
          rcases Quotient.exact (Finset.mem_filter.mp hy).2 with ⟨g, hg⟩
          exact ⟨g, Finset.mem_univ _, hg⟩
      rw [hcard_orb]
      exact dvd_mul_right _ _
    -- Affine complete maps sum to `-q`
    have haff_sum : (∑ h ∈ Finset.univ.filter isAff, wt h) = -(q : ℤ) := by
      let P := (Finset.univ : Finset (ZMod q × ZMod q)).filter (fun p => p.1 ≠ 0 ∧ p.1 ≠ 1)
      have hbij_aff : ∀ p : ZMod q × ZMod q, p.1 ≠ 1 →
          Function.Bijective (fun x : ZMod q => (p.1 * x + p.2) - x) := by
        intro p hne1
        have hsub : p.1 - 1 ≠ 0 := sub_ne_zero.mpr hne1
        have heq : (fun x : ZMod q => (p.1 * x + p.2) - x) =
            (fun y => y + p.2) ∘ (fun x => (p.1 - 1) * x) := by
          ext x; simp only [Function.comp_apply]; ring
        rw [heq]
        exact (Equiv.addRight p.2).bijective.comp (Equiv.mulLeft₀ (p.1 - 1) hsub).bijective
      have hbij : (∑ h ∈ Finset.univ.filter isAff, wt h) =
          ∑ p ∈ P, legendreSym q ((p.1 * (p.1 - 1)).val : ℤ) := by
        symm
        refine Finset.sum_bij
          (fun p hp =>
            let hne0 : p.1 ≠ 0 := (Finset.mem_filter.mp hp).2.1
            let hne1 : p.1 ≠ 1 := (Finset.mem_filter.mp hp).2.2
            ⟨(Equiv.mulLeft₀ p.1 hne0).trans (Equiv.addRight p.2), hbij_aff p hne1⟩)
          ?_ ?_ ?_ ?_
        · intro p _
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1, p.2, fun _ => rfl⟩
        · intro p₁ _ p₂ _ hEq
          have h0 := congrArg (fun k => k.1 0) hEq
          have h1 := congrArg (fun k => k.1 1) hEq
          change p₁.1 * 0 + p₁.2 = p₂.1 * 0 + p₂.2 at h0
          change p₁.1 * 1 + p₁.2 = p₂.1 * 1 + p₂.2 at h1
          simp only [mul_zero, zero_add, mul_one] at h0 h1
          exact Prod.ext (by linear_combination h1 - h0) h0
        · intro h hh
          rcases (Finset.mem_filter.mp hh).2 with ⟨lam, e, hle⟩
          have hne0 : lam ≠ 0 := by
            intro h0
            have h01 : (0 : ZMod q) = 1 :=
              h.1.injective (by rw [hle 0, hle 1, h0]; simp)
            exact zero_ne_one h01
          have hne1 : lam ≠ 1 := by
            intro h1
            have h01 : (0 : ZMod q) = 1 :=
              h.2.1 (by change h.1 0 - 0 = h.1 1 - 1; rw [hle 0, hle 1, h1]; ring)
            exact zero_ne_one h01
          refine ⟨(lam, e), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne0, hne1⟩, ?_⟩
          apply Subtype.ext; ext x
          exact (hle x).symm
        · intro p hp
          have hne0 : p.1 ≠ 0 := (Finset.mem_filter.mp hp).2.1
          have hne1 : p.1 ≠ 1 := (Finset.mem_filter.mp hp).2.2
          have hsub : p.1 - 1 ≠ 0 := sub_ne_zero.mpr hne1
          dsimp only [wt]
          have hs1 : (Equiv.Perm.sign ((Equiv.mulLeft₀ p.1 hne0).trans (Equiv.addRight p.2)) : ℤ) =
              legendreSym q (p.1.val : ℤ) := by
            change (Equiv.Perm.sign (Equiv.addRight p.2 * Equiv.mulLeft₀ p.1 hne0) : ℤ) = _
            rw [map_mul, sign_addRight_eq_one hq_odd, one_mul]
            exact sign_mulLeft_eq_legendreSym hodd (Units.mk0 p.1 hne0)
          have hs2 :
              (Equiv.Perm.sign (Equiv.ofBijective
                (fun x : ZMod q =>
                  ((Equiv.mulLeft₀ p.1 hne0).trans (Equiv.addRight p.2)) x - x)
                (hbij_aff p hne1)) : ℤ) =
              legendreSym q ((p.1 - 1).val : ℤ) := by
            have heq : Equiv.ofBijective
                (fun x : ZMod q =>
                  ((Equiv.mulLeft₀ p.1 hne0).trans (Equiv.addRight p.2)) x - x)
                (hbij_aff p hne1) =
                Equiv.addRight p.2 * Equiv.mulLeft₀ (p.1 - 1) hsub := by
              apply Equiv.Perm.ext
              intro x
              change (p.1 * x + p.2) - x = (p.1 - 1) * x + p.2
              ring
            rw [heq, map_mul, sign_addRight_eq_one hq_odd, one_mul]
            exact sign_mulLeft_eq_legendreSym hodd (Units.mk0 (p.1 - 1) hsub)
          rw [hs1, hs2, legendreSym_val_mul]
      rw [hbij]
      have hP : P = (Finset.univ.filter (fun lam : ZMod q => lam ≠ 0 ∧ lam ≠ 1)) ×ˢ
          (Finset.univ : Finset (ZMod q)) := by
        ext ⟨lam, e⟩; simp [P]
      rw [hP, Finset.sum_product]
      simp_rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← Finset.mul_sum]
      have hjac := jacobsthal_sum (q := q) hodd (c := -1) (by simp)
      have hfull :
          ∑ lam ∈ Finset.univ.filter (fun lam : ZMod q => lam ≠ 0 ∧ lam ≠ 1),
            legendreSym q ((lam * (lam - 1)).val : ℤ) =
          ∑ lam : ZMod q, legendreSym q ((lam * (lam + -1)).val : ℤ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun lam _ => ?_
        rw [sub_eq_add_neg]
        split_ifs with h
        · rfl
        · push Not at h
          by_cases h0 : lam = 0
          · subst h0
            have : ((0 : ZMod q) * (0 + -1)).val = 0 := by simp
            rw [this, Nat.cast_zero, legendreSym.at_zero]
          · have h1 := h h0; subst h1
            have : ((1 : ZMod q) * (1 + -1)).val = 0 := by simp
            rw [this, Nat.cast_zero, legendreSym.at_zero]
      rw [hfull, hjac]
      ring
    rw [hpart1, haff_sum] at hsplit
    rcases hnonaff_dvd with ⟨k, hk⟩
    rw [hk] at hsplit
    rw [Int.modEq_iff_dvd]
    refine ⟨-k, ?_⟩
    have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    apply mul_left_cancel₀ hq0
    linarith
  -- Part 3: `δ`-scaled sum equals `tauQ q`
  refine ⟨hpart1, hpart2, fun δ hδ => ?_⟩
  have hsqδ : (Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) : ℤ) *
      (Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ)) with h | h <;> simp [h]
  change _ = ∑ h : CM, wt h
  let scaleBij : { h : Equiv.Perm (ZMod q) // Function.Bijective (fun x => h x - δ * x) } → CM :=
    fun h =>
      ⟨h.1.trans (Equiv.mulLeft₀ δ hδ).symm, by
        have heq : (fun x : ZMod q => (h.1.trans (Equiv.mulLeft₀ δ hδ).symm) x - x) =
            (Equiv.mulLeft₀ δ hδ).symm ∘ (fun x => h.1 x - δ * x) := by
          ext x
          change δ⁻¹ * h.1 x - x = δ⁻¹ * (h.1 x - δ * x)
          rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
        change Function.Bijective (fun x : ZMod q => (h.1.trans (Equiv.mulLeft₀ δ hδ).symm) x - x)
        rw [heq]
        exact (Equiv.mulLeft₀ δ hδ).symm.bijective.comp h.2⟩
  refine Finset.sum_bij (fun h _ => scaleBij h) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro h₁ _ h₂ _ hEq
    apply Subtype.ext; ext x
    have hx := congrArg (fun k => k.1 x) hEq
    exact (Equiv.mulLeft₀ δ hδ).symm.injective hx
  · intro h₁ _
    refine ⟨⟨h₁.1.trans (Equiv.mulLeft₀ δ hδ), by
      change Function.Bijective (fun x : ZMod q => δ * h₁.1 x - δ * x)
      have heq : (fun x : ZMod q => δ * h₁.1 x - δ * x) =
          (Equiv.mulLeft₀ δ hδ) ∘ (fun x => h₁.1 x - x) := by
        ext x; simp [mul_sub]
      rw [heq]
      exact (Equiv.mulLeft₀ δ hδ).bijective.comp h₁.2⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext; ext x
    change δ⁻¹ * (δ * h₁.1 x) = h₁.1 x
    rw [← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
  · intro h _
    dsimp only [wt]
    have hs1 : Equiv.Perm.sign (scaleBij h).1 =
        Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) * Equiv.Perm.sign h.1 := by
      change Equiv.Perm.sign ((Equiv.mulLeft₀ δ hδ)⁻¹ * h.1) = _
      rw [map_mul, map_inv, Int.units_inv_eq_self]
    have heq2 : Equiv.ofBijective (fun x : ZMod q => (scaleBij h).1 x - x) (scaleBij h).2 =
        (Equiv.mulLeft₀ δ hδ)⁻¹ * Equiv.ofBijective (fun x => h.1 x - δ * x) h.2 := by
      apply Equiv.Perm.ext
      intro x
      change δ⁻¹ * h.1 x - x = δ⁻¹ * (h.1 x - δ * x)
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hδ, one_mul]
    rw [hs1, heq2, map_mul, map_inv, Int.units_inv_eq_self]
    push_cast
    calc (Equiv.Perm.sign h.1 : ℤ) *
          (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - δ * x) h.2) : ℤ)
        = ((Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) : ℤ) *
            (Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) : ℤ)) *
          ((Equiv.Perm.sign h.1 : ℤ) *
            (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - δ * x) h.2) : ℤ)) := by
          rw [hsqδ, one_mul]
      _ = ((Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) : ℤ) * (Equiv.Perm.sign h.1 : ℤ)) *
          ((Equiv.Perm.sign (Equiv.mulLeft₀ δ hδ) : ℤ) *
            (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - δ * x) h.2) : ℤ)) := by ring

end AlonTarsi.Proofs

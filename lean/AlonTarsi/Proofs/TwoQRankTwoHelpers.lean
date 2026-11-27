module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Proofs.TwoQMobius
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Wilson

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Helpers for Rank-Two and Rank-Three Subgroups in `q = n / 2`

This file proves:
* Coordinate helpers for `P ≅ F_q^6` and its normalizer (block swaps and rescalings).
* Part (i) of Lemma 6.6: any nontrivial `H ≤ P` fixing a column or row has `S(H) = 0`.
* Part (ii) of Lemma 6.6: any rank-3 `H ≤ P` has `Stab_P(L) = H` for `L ∈ Fix(H)` and `q^3 ∣ S(H)`.
* Fact 1 (vanishing when an element fixes all columns and a row).
* Unified Fact 2 (`S_twoq_four_affine`): exact closed-form `S(H)` when all four blocks are affine.
* The five normalized rank-2 subgroup family sums (`R_11`, `R_21`, `R_mon`, `R_one`, `R_full`).
-/

namespace AlonTarsi.Proofs

open AlonTarsi
open scoped BigOperators

private lemma fin2_ne_eq_one_sub {a b : Fin 2} (h : a ≠ b) : a = 1 - b := by
  fin_cases a <;> fin_cases b <;> simp_all

private lemma fin2_one_sub_one_sub (a : Fin 2) : 1 - (1 - a) = a := by
  fin_cases a <;> rfl

private lemma fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- Block permutation `(b, y) ↦ (ϖ b, φ b y)` transferred to `Fin (2 * q)`. -/
def blockPerm (q : ℕ) [NeZero q] (ϖ : Equiv.Perm (Fin 2)) (φ : Fin 2 → Equiv.Perm (ZMod q)) :
    Equiv.Perm (Fin (2 * q)) :=
  (blockEquiv q).symm.trans <|
    ({ toFun := fun p => (ϖ p.1, φ p.1 p.2)
       invFun := fun p => (ϖ.symm p.1, (φ (ϖ.symm p.1)).symm p.2)
       left_inv := fun p => by ext <;> simp
       right_inv := fun p => by ext <;> simp } : Equiv.Perm (Fin 2 × ZMod q)).trans
    (blockEquiv q)

@[simp]
lemma blockPerm_apply {q : ℕ} [NeZero q] (ϖ : Equiv.Perm (Fin 2))
    (φ : Fin 2 → Equiv.Perm (ZMod q)) (b : Fin 2) (y : ZMod q) :
    blockPerm q ϖ φ (blockEquiv q (b, y)) = blockEquiv q (ϖ b, φ b y) := by
  simp [blockPerm]

lemma sign_blockPerm_eq {q : ℕ} [NeZero q] (hodd : Odd q)
    (ϖ : Equiv.Perm (Fin 2)) (φ : Fin 2 → Equiv.Perm (ZMod q)) :
    Equiv.Perm.sign (blockPerm q ϖ φ) =
      (if ϖ = 1 then 1 else -1) * Equiv.Perm.sign (φ 0) * Equiv.Perm.sign (φ 1) :=
  sign_blockPerm hodd ϖ φ

/-! ### Coordinate Maps on `sylowP q` and Normalizer Conjugations -/

/-- Extract the coordinate vector `(u, v, w) ∈ F_q^6` of an element `g ∈ sylowP q`. -/
noncomputable def sylowToVec {q : ℕ} [NeZero q] (g : sylowP q) : SylowVec q :=
  Multiplicative.toAdd ((sylowMulEquiv q).symm g)

/-- Construct an element of `sylowP q` from its coordinate vector `(u, v, w) ∈ F_q^6`. -/
noncomputable def vecToSylow {q : ℕ} [NeZero q] (v : SylowVec q) : sylowP q :=
  sylowMulEquiv q (Multiplicative.ofAdd v)

@[simp]
lemma sylowToVec_vecToSylow {q : ℕ} [NeZero q] (v : SylowVec q) :
    sylowToVec (vecToSylow v) = v := by
  simp [sylowToVec, vecToSylow]

@[simp]
lemma vecToSylow_sylowToVec {q : ℕ} [NeZero q] (g : sylowP q) :
    vecToSylow (sylowToVec g) = g := by
  simp [sylowToVec, vecToSylow]

lemma vecToSylow_val {q : ℕ} [NeZero q] (v : SylowVec q) :
    (vecToSylow v).1 = (blockTransPerm q v.1, blockTransPerm q v.2.1, blockTransPerm q v.2.2) := by
  rfl

lemma sylowToVec_val {q : ℕ} [NeZero q] (g : sylowP q) :
    g.1 = (blockTransPerm q (sylowToVec g).1,
           blockTransPerm q (sylowToVec g).2.1,
           blockTransPerm q (sylowToVec g).2.2) := by
  conv_lhs => rw [← vecToSylow_sylowToVec g]
  rfl

@[simp]
lemma sylowToVec_one {q : ℕ} [NeZero q] : sylowToVec (1 : sylowP q) = 0 := by
  simp [sylowToVec]

@[simp]
lemma sylowToVec_mul {q : ℕ} [NeZero q] (g₁ g₂ : sylowP q) :
    sylowToVec (g₁ * g₂) = sylowToVec g₁ + sylowToVec g₂ := by
  simp [sylowToVec]

@[simp]
lemma sylowToVec_inv {q : ℕ} [NeZero q] (g : sylowP q) :
    sylowToVec g⁻¹ = -sylowToVec g := by
  simp [sylowToVec]

lemma sylowToVec_injective {q : ℕ} [NeZero q] : Function.Injective (sylowToVec (q := q)) := by
  intro g₁ g₂ h
  have := congrArg vecToSylow h
  simpa using this

lemma sylowToVec_sylowElem {q : ℕ} [NeZero q] (u₀ u₁ v₀ v₁ w₀ w₁ : ZMod q) :
    sylowToVec (sylowElem q u₀ u₁ v₀ v₁ w₀ w₁) =
      (fun a => if a = 0 then u₀ else u₁,
       fun b => if b = 0 then v₀ else v₁,
       fun c => if c = 0 then w₀ else w₁) := by
  have h : sylowElem q u₀ u₁ v₀ v₁ w₀ w₁ =
      vecToSylow (fun a => if a = 0 then u₀ else u₁,
        fun b => if b = 0 then v₀ else v₁,
        fun c => if c = 0 then w₀ else w₁) := Subtype.ext rfl
  rw [h, sylowToVec_vecToSylow]

/-- Characterization of `g.1 • L = L` in block coordinates `(a, x), (b, y)`. -/
lemma sylow_fix_entry_iff {q : ℕ} [NeZero q] (g : sylowP q) (L : LatinSquare (2 * q)) :
    g.1 • L = L ↔
      ∀ (a b : Fin 2) (x y : ZMod q),
        let p := (blockEquiv q).symm (L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)))
        L.entry (blockEquiv q (a, x + (sylowToVec g).1 a))
                (blockEquiv q (b, y + (sylowToVec g).2.1 b)) =
          blockEquiv q (p.1, p.2 + (sylowToVec g).2.2 p.1) := by
  let u := (sylowToVec g).1
  let v := (sylowToVec g).2.1
  let w := (sylowToVec g).2.2
  have hg : g.1 = (blockTransPerm q u, blockTransPerm q v, blockTransPerm q w) := sylowToVec_val g
  constructor
  · intro hfix a b x y
    have h := congrArg (fun M => M.entry (blockEquiv q (a, x + u a)) (blockEquiv q (b, y + v b))) hfix
    change (g.1 • L).entry (blockEquiv q (a, x + u a)) (blockEquiv q (b, y + v b)) = _ at h
    rw [hg] at h
    change blockTransPerm q w (L.entry ((blockTransPerm q u).symm (blockEquiv q (a, x + u a)))
      ((blockTransPerm q v).symm (blockEquiv q (b, y + v b)))) = _ at h
    have hu : (blockTransPerm q u).symm (blockEquiv q (a, x + u a)) = blockEquiv q (a, x) := by
      rw [← blockTransPerm_apply u a x, Equiv.symm_apply_apply]
    have hv : (blockTransPerm q v).symm (blockEquiv q (b, y + v b)) = blockEquiv q (b, y) := by
      rw [← blockTransPerm_apply v b y, Equiv.symm_apply_apply]
    rw [hu, hv] at h
    have hL := (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)))
    rw [← hL, blockTransPerm_apply] at h
    exact h.symm
  · intro h
    apply LatinSquare.ext
    funext r c
    obtain ⟨⟨a, x'⟩, rfl⟩ := (blockEquiv q).surjective r
    obtain ⟨⟨b, y'⟩, rfl⟩ := (blockEquiv q).surjective c
    let x := x' - u a
    let y := y' - v b
    have hx : x + u a = x' := sub_add_cancel x' (u a)
    have hy : y + v b = y' := sub_add_cancel y' (v b)
    have h0 := h a b x y
    rw [hx, hy] at h0
    change (g.1 • L).entry (blockEquiv q (a, x')) (blockEquiv q (b, y')) = _
    rw [hg]
    change blockTransPerm q w (L.entry ((blockTransPerm q u).symm (blockEquiv q (a, x')))
      ((blockTransPerm q v).symm (blockEquiv q (b, y')))) = _
    have hu : (blockTransPerm q u).symm (blockEquiv q (a, x')) = blockEquiv q (a, x) := by
      rw [← hx, ← blockTransPerm_apply u a x, Equiv.symm_apply_apply]
    have hv : (blockTransPerm q v).symm (blockEquiv q (b, y')) = blockEquiv q (b, y) := by
      rw [← hy, ← blockTransPerm_apply v b y, Equiv.symm_apply_apply]
    rw [hu, hv]
    have hL := (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)))
    conv_lhs => rw [← hL, blockTransPerm_apply]
    exact h0.symm

/-- Conjugating a subgroup `H ≤ sylowP q` by a normalizer element `ψ` preserves `S_twoq`. -/
noncomputable def conjSylowSub {q : ℕ} [NeZero q] (ψ : Isotopy (2 * q))
    (hψ : ∀ g ∈ sylowP q, ψ * g * ψ⁻¹ ∈ sylowP q) (H : Subgroup (sylowP q)) :
    Subgroup (sylowP q) :=
  H.map
    { toFun := fun g => ⟨ψ * g.1 * ψ⁻¹, hψ g.1 g.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => Subtype.ext (by
        change ψ * (a.1 * b.1) * ψ⁻¹ = (ψ * a.1 * ψ⁻¹) * (ψ * b.1 * ψ⁻¹); group) }

lemma S_twoq_conjSylowSub {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) (ψ : Isotopy (2 * q))
    (hψ : ∀ g ∈ sylowP q, ψ * g * ψ⁻¹ ∈ sylowP q) (H : Subgroup (sylowP q)) :
    S_twoq q (conjSylowSub ψ hψ H) = S_twoq q H := by
  have h5 := (((lem_6_4_signs q hodd).2.2.2.2.2.1 ψ hψ).2 H).2
  rw [← h5]
  unfold S_twoq
  congr 1
  ext σ
  simp only [conjSylowSub, Subgroup.mem_map, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g.1, ⟨g, hg, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨ψ * g.1 * ψ⁻¹, hψ g.1 g.2⟩, ⟨g, hg, rfl⟩, rfl⟩

/-! ### Part (i) of Lemma 6.6: Fixed Column or Row Gives `S(H) = 0` -/

/-- Fact 1: If some `g ≠ 1` in `H` fixes all columns and a row, then `Fix(H) = ∅`. -/
lemma fixSet_empty_of_fix_all_cols_and_row {q : ℕ} [NeZero q] (H : Subgroup (sylowP q))
    (g : sylowP q) (hgH : g ∈ H) (hg1 : g ≠ 1)
    (hcol : (sylowToVec g).2.1 = 0) (a₀ : Fin 2) (hrow : (sylowToVec g).1 a₀ = 0) :
    fixSet (H.map (sylowP q).subtype) = (∅ : Set (LatinSquare (2 * q))) := by
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hL
  have hgfix : g.1 • L = L := hL g.1 ⟨g, hgH, rfl⟩
  have hent := (sylow_fix_entry_iff g L).mp hgfix
  -- `g` fixes row `(a₀, 0)` and every column, so `w = 0`
  have hw0 : (sylowToVec g).2.2 = 0 := by
    ext c
    -- Find column `(b, y)` where `L((a₀, 0), (b, y)) = (c, 0)`
    obtain ⟨col, hcol_eq⟩ := (L.row_bijective (blockEquiv q (a₀, 0))).2 (blockEquiv q (c, 0))
    obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
    have hcol_eq' : L.entry (blockEquiv q (a₀, 0)) (blockEquiv q (b, y)) = blockEquiv q (c, 0) :=
      hcol_eq
    have h1 := hent a₀ b 0 y
    dsimp only at h1
    rw [hrow, hcol, Pi.zero_apply, add_zero, add_zero, hcol_eq', Equiv.symm_apply_apply] at h1
    have h2 := (blockEquiv q).injective h1
    have h3 : (0 : ZMod q) + (sylowToVec g).2.2 c = 0 := (congrArg Prod.snd h2).symm
    simpa using h3
  -- Now `g` fixes all columns and all symbols, so `u = 0`
  have hu0 : (sylowToVec g).1 = 0 := by
    ext a
    have h1 := hent a 0 0 0
    dsimp only at h1
    simp only [hcol, hw0, Pi.zero_apply, add_zero, zero_add] at h1
    rw [Prod.eta, Equiv.apply_symm_apply] at h1
    have h2 := (L.col_bijective (blockEquiv q (0, 0))).1 h1
    have h3 := (blockEquiv q).injective h2
    simpa using congrArg Prod.snd h3
  apply hg1
  apply sylowToVec_injective
  rw [sylowToVec_one]
  exact Prod.ext hu0 (Prod.ext hcol hw0)

/-- Lemma 6.6(i) for a fixed column: if `H ≠ ⊥` fixes a column `c₀`, then `S_twoq q H = 0`. -/
lemma S_twoq_eq_zero_of_fixed_col {q : ℕ} [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (H : Subgroup (sylowP q)) (hH : H ≠ ⊥)
    (c₀ : Fin (2 * q)) (hfix : ∀ g ∈ H, g.1.2.1 c₀ = c₀) :
    S_twoq q H = 0 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨⟨b₀, y₀⟩, rfl⟩ := (blockEquiv q).surjective c₀
  -- Every `g ∈ H` has `v_{b₀}(g) = 0`, hence fixes every column in block `b₀`
  have hv0 : ∀ g ∈ H, (sylowToVec g).2.1 b₀ = 0 := by
    intro g hg
    have h1 := hfix g hg
    rw [sylowToVec_val g, blockTransPerm_apply] at h1
    have h2 := congrArg Prod.snd ((blockEquiv q).injective h1)
    simpa using h2
  -- Case split: does `H` move some row block `a₀`?
  by_cases hmove : ∃ a₀ : Fin 2, ∃ g ∈ H, (sylowToVec g).1 a₀ ≠ 0
  · rcases hmove with ⟨a₀, g₀, hg₀H, hu₀⟩
    -- For any `L ∈ Fix(H)` and any `y : ZMod q`, all entries in block `(a₀, b₀)` column `y` lie in one symbol block!
    let symBlk (L : LatinSquare (2 * q)) (y : ZMod q) : Fin 2 :=
      ((blockEquiv q).symm (L.entry (blockEquiv q (a₀, 0)) (blockEquiv q (b₀, y)))).1
    have hsym_const : ∀ L ∈ fixSet (H.map (sylowP q).subtype), ∀ (x y : ZMod q),
        ((blockEquiv q).symm (L.entry (blockEquiv q (a₀, x)) (blockEquiv q (b₀, y)))).1 =
          symBlk L y := by
      intro L hL x y
      have hfix0 : g₀.1 • L = L := hL g₀.1 ⟨g₀, hg₀H, rfl⟩
      have hent := (sylow_fix_entry_iff g₀ L).mp hfix0
      have hv₀ := hv0 g₀ hg₀H
      -- By induction on `k`, `L((a₀, k * u₀), (b₀, y))` has the same symbol block as `L((a₀, 0), (b₀, y))`
      have hstep : ∀ k : ℕ,
          ((blockEquiv q).symm (L.entry (blockEquiv q (a₀, (k : ZMod q) * (sylowToVec g₀).1 a₀))
            (blockEquiv q (b₀, y)))).1 = symBlk L y := by
        intro k
        induction k with
        | zero => simp [symBlk]
        | succ k ih =>
          have h1 := hent a₀ b₀ ((k : ZMod q) * (sylowToVec g₀).1 a₀) y
          rw [hv₀, add_zero] at h1
          have hadd : ((k + 1 : ℕ) : ZMod q) * (sylowToVec g₀).1 a₀ =
              (k : ZMod q) * (sylowToVec g₀).1 a₀ + (sylowToVec g₀).1 a₀ := by
            push_cast; ring
          rw [hadd, h1, Equiv.symm_apply_apply]
          exact ih
      let t : ZMod q := x * ((sylowToVec g₀).1 a₀)⁻¹
      have hx : x = (t.val : ZMod q) * (sylowToVec g₀).1 a₀ := by
        rw [ZMod.natCast_zmod_val]; dsimp only [t]; field_simp [hu₀]
      rw [hx]
      exact hstep t.val
    -- Since `|ZMod q| = q ≥ 3 > 2 = |Fin 2|`, every `L` has a pair `y₁.val < y₂.val` with `symBlk L y₁ = symBlk L y₂`
    let pairs (L : LatinSquare (2 * q)) : Finset (ZMod q × ZMod q) :=
      Finset.univ.filter (fun p => p.1.val < p.2.val ∧ symBlk L p.1 = symBlk L p.2)
    have hpairs_ne : ∀ L : LatinSquare (2 * q), (pairs L).Nonempty := by
      intro L
      have hcard : Fintype.card (Fin 2) < Fintype.card (ZMod q) := by
        simp [ZMod.card]; omega
      obtain ⟨y₁, y₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (symBlk L) hcard
      rcases lt_or_gt_of_ne (fun h => hne (ZMod.val_injective q h)) with hlt | hgt
      · exact ⟨(y₁, y₂), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, heq⟩⟩
      · exact ⟨(y₂, y₁), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, heq.symm⟩⟩
    -- Pick the lexicographically smallest pair using `Prod.Lex ℕ ℕ`
    let _ : LinearOrder (ZMod q × ZMod q) :=
      LinearOrder.lift' (fun p : ZMod q × ZMod q => toLex (p.1.val, p.2.val))
        (fun a b h => by
          have h' : (a.1.val, a.2.val) = (b.1.val, b.2.val) := toLex.injective h
          exact Prod.ext (ZMod.val_injective q (congrArg Prod.fst h'))
            (ZMod.val_injective q (congrArg Prod.snd h')))
    let firstPair (L : LatinSquare (2 * q)) : ZMod q × ZMod q :=
      (pairs L).min' (hpairs_ne L)
    have hfp_mem : ∀ L, firstPair L ∈ pairs L := fun L => Finset.min'_mem _ (hpairs_ne L)
    have hfp_ne : ∀ L, (firstPair L).1 ≠ (firstPair L).2 := by
      intro L heq
      have hlt := (Finset.mem_filter.mp (hfp_mem L)).2.1
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    have hfp_blk : ∀ L, symBlk L (firstPair L).1 = symBlk L (firstPair L).2 := fun L =>
      (Finset.mem_filter.mp (hfp_mem L)).2.2
    -- Define the partial column-switch involution on `Fix(H)`
    let FixFin := (Finset.univ : Finset (LatinSquare (2 * q))).filter
      (fun L => L ∈ fixSet (H.map (sylowP q).subtype))
    -- Construct the swapped Latin square for any `L ∈ Fix(H)`
    have hcol_surj_blk : ∀ (L : LatinSquare (2 * q)),
        L ∈ fixSet (H.map (sylowP q).subtype) → ∀ (y : ZMod q),
        Function.Bijective (fun x : ZMod q =>
          ((blockEquiv q).symm (L.entry (blockEquiv q (a₀, x)) (blockEquiv q (b₀, y)))).2) := by
      intro L hL y
      rw [← Finite.injective_iff_bijective]
      intro x₁ x₂ hEq
      have hb1 := hsym_const L hL x₁ y
      have hb2 := hsym_const L hL x₂ y
      have hp : (blockEquiv q).symm (L.entry (blockEquiv q (a₀, x₁)) (blockEquiv q (b₀, y))) =
          (blockEquiv q).symm (L.entry (blockEquiv q (a₀, x₂)) (blockEquiv q (b₀, y))) :=
        Prod.ext (hb1.trans hb2.symm) hEq
      have he : L.entry (blockEquiv q (a₀, x₁)) (blockEquiv q (b₀, y)) =
          L.entry (blockEquiv q (a₀, x₂)) (blockEquiv q (b₀, y)) :=
        (blockEquiv q).symm.injective hp
      have hr := (L.col_bijective (blockEquiv q (b₀, y))).1 he
      exact congrArg Prod.snd ((blockEquiv q).injective hr)
    -- In the other row block `1 - a₀`, column `(b₀, y)` hits the OTHER symbol block `1 - symBlk L y`
    have hsym_other : ∀ (L : LatinSquare (2 * q)),
        L ∈ fixSet (H.map (sylowP q).subtype) → ∀ (a : Fin 2) (x y : ZMod q),
        a ≠ a₀ →
        ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) (blockEquiv q (b₀, y)))).1 ≠
          symBlk L y := by
      intro L hL a x y ha heq
      obtain ⟨x', hx'⟩ := (hcol_surj_blk L hL y).2
        ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) (blockEquiv q (b₀, y)))).2
      have hpair : (blockEquiv q).symm (L.entry (blockEquiv q (a₀, x')) (blockEquiv q (b₀, y))) =
          (blockEquiv q).symm (L.entry (blockEquiv q (a, x)) (blockEquiv q (b₀, y))) :=
        Prod.ext ((hsym_const L hL x' y).trans heq.symm) hx'
      have he := (blockEquiv q).symm.injective hpair
      have hr := (L.col_bijective (blockEquiv q (b₀, y))).1 he
      exact ha (congrArg Prod.fst ((blockEquiv q).injective hr)).symm
    let swEntry (L : LatinSquare (2 * q)) (r c : Fin (2 * q)) : Fin (2 * q) :=
      let p := firstPair L
      if ((blockEquiv q).symm r).1 = a₀ then
        L.entry r (Equiv.swap (blockEquiv q (b₀, p.1)) (blockEquiv q (b₀, p.2)) c)
      else
        L.entry r c
    let swSquare (L : LatinSquare (2 * q)) (hL : L ∈ fixSet (H.map (sylowP q).subtype)) :
        LatinSquare (2 * q) :=
      { entry := swEntry L
        row_bijective := fun r => by
          dsimp only [swEntry]
          split_ifs
          · exact (L.row_bijective r).comp (Equiv.swap _ _).bijective
          · exact L.row_bijective r
        col_bijective := fun c => by
          rw [← Finite.injective_iff_bijective]
          intro r₁ r₂ hEq
          dsimp only [swEntry] at hEq
          let p := firstPair L
          by_cases hc1 : c = blockEquiv q (b₀, p.1) ∨ c = blockEquiv q (b₀, p.2)
          · -- Column `c` is one of the two swapped columns; let `c'` be the other
            let c' := Equiv.swap (blockEquiv q (b₀, p.1)) (blockEquiv q (b₀, p.2)) c
            have hc_blk : ∃ y, c = blockEquiv q (b₀, y) ∧ symBlk L y = symBlk L p.1 := by
              rcases hc1 with rfl | rfl
              · exact ⟨p.1, rfl, rfl⟩
              · exact ⟨p.2, rfl, (hfp_blk L).symm⟩
            have hc'_blk : ∃ y', c' = blockEquiv q (b₀, y') ∧ symBlk L y' = symBlk L p.1 := by
              rcases hc1 with rfl | rfl
              · exact ⟨p.2, Equiv.swap_apply_left _ _, (hfp_blk L).symm⟩
              · exact ⟨p.1, Equiv.swap_apply_right _ _, rfl⟩
            rcases hc_blk with ⟨y, hyc, hyblk⟩
            rcases hc'_blk with ⟨y', hy'c, hy'blk⟩
            obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
            obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
            simp only [Equiv.symm_apply_apply] at hEq
            split_ifs at hEq with h1 h2 h2
            · subst h1; subst h2
              exact (L.col_bijective c').1 hEq
            · exfalso
              have hleft : ((blockEquiv q).symm (L.entry (blockEquiv q (a₀, x₁)) c')).1 = symBlk L p.1 := by
                rw [hy'c, hsym_const L hL, hy'blk]
              have hright : ((blockEquiv q).symm (L.entry (blockEquiv q (a₂, x₂)) c)).1 ≠ symBlk L p.1 := by
                rw [hyc, ← hyblk]; exact hsym_other L hL a₂ x₂ y h2
              rw [h1] at hEq
              exact hright (by rw [← hEq]; exact hleft)
            · exfalso
              have hleft : ((blockEquiv q).symm (L.entry (blockEquiv q (a₁, x₁)) c)).1 ≠ symBlk L p.1 := by
                rw [hyc, ← hyblk]; exact hsym_other L hL a₁ x₁ y h1
              have hright : ((blockEquiv q).symm (L.entry (blockEquiv q (a₀, x₂)) c')).1 = symBlk L p.1 := by
                rw [hy'c, hsym_const L hL, hy'blk]
              rw [h2] at hEq
              exact hleft (by rw [hEq]; exact hright)
            · exact (L.col_bijective c).1 hEq
          · push Not at hc1
            have hsw : Equiv.swap (blockEquiv q (b₀, (firstPair L).1))
                (blockEquiv q (b₀, (firstPair L).2)) c = c :=
              Equiv.swap_apply_of_ne_of_ne hc1.1 hc1.2
            simp only [hsw, ite_self] at hEq
            exact (L.col_bijective c).1 hEq }
    -- Show `swSquare L hL ∈ Fix(H)`
    have hsw_fix : ∀ L (hL : L ∈ fixSet (H.map (sylowP q).subtype)),
        swSquare L hL ∈ fixSet (H.map (sylowP q).subtype) := by
      intro L hL
      rintro _ ⟨g, hgH, rfl⟩
      change g.1 • swSquare L hL = swSquare L hL
      rw [sylow_fix_entry_iff]
      intro a b x y
      have hfixL := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩)
      have hvb := hv0 g hgH
      let p := firstPair L
      change swEntry L (blockEquiv q (a, x + (sylowToVec g).1 a))
          (blockEquiv q (b, y + (sylowToVec g).2.1 b)) =
        blockEquiv q (((blockEquiv q).symm (swEntry L (blockEquiv q (a, x)) (blockEquiv q (b, y)))).1,
          ((blockEquiv q).symm (swEntry L (blockEquiv q (a, x)) (blockEquiv q (b, y)))).2 +
            (sylowToVec g).2.2 ((blockEquiv q).symm (swEntry L (blockEquiv q (a, x)) (blockEquiv q (b, y)))).1)
      dsimp only [swEntry]
      simp only [Equiv.symm_apply_apply]
      split_ifs with ha
      · by_cases hby : (b = b₀ ∧ y = p.1) ∨ (b = b₀ ∧ y = p.2)
        · rcases hby with ⟨hb, hy⟩ | ⟨hb, hy⟩
          · rw [hb, hy, hvb, add_zero, Equiv.swap_apply_left]
            simpa [hvb] using hfixL a b₀ x p.2
          · rw [hb, hy, hvb, add_zero, Equiv.swap_apply_right]
            simpa [hvb] using hfixL a b₀ x p.1
        · push Not at hby
          have hne1 : blockEquiv q (b, y) ≠ blockEquiv q (b₀, p.1) := by
            intro h; have hp := (blockEquiv q).injective h
            exact hby.1 (congrArg Prod.fst hp) (congrArg Prod.snd hp)
          have hne2 : blockEquiv q (b, y) ≠ blockEquiv q (b₀, p.2) := by
            intro h; have hp := (blockEquiv q).injective h
            exact hby.2 (congrArg Prod.fst hp) (congrArg Prod.snd hp)
          have hne1' : blockEquiv q (b, y + (sylowToVec g).2.1 b) ≠ blockEquiv q (b₀, p.1) := by
            intro h; have hp := (blockEquiv q).injective h
            have hb : b = b₀ := congrArg Prod.fst hp
            subst hb; rw [hvb, add_zero] at hp
            exact hby.1 rfl (congrArg Prod.snd hp)
          have hne2' : blockEquiv q (b, y + (sylowToVec g).2.1 b) ≠ blockEquiv q (b₀, p.2) := by
            intro h; have hp := (blockEquiv q).injective h
            have hb : b = b₀ := congrArg Prod.fst hp
            subst hb; rw [hvb, add_zero] at hp
            exact hby.2 rfl (congrArg Prod.snd hp)
          change L.entry (blockEquiv q (a, x + (sylowToVec g).1 a))
              (Equiv.swap (blockEquiv q (b₀, p.1)) (blockEquiv q (b₀, p.2))
                (blockEquiv q (b, y + (sylowToVec g).2.1 b))) =
            blockEquiv q (((blockEquiv q).symm (L.entry (blockEquiv q (a, x))
                (Equiv.swap (blockEquiv q (b₀, p.1)) (blockEquiv q (b₀, p.2))
                  (blockEquiv q (b, y))))).1,
              ((blockEquiv q).symm (L.entry (blockEquiv q (a, x))
                (Equiv.swap (blockEquiv q (b₀, p.1)) (blockEquiv q (b₀, p.2))
                  (blockEquiv q (b, y))))).2 +
                (sylowToVec g).2.2 ((blockEquiv q).symm (L.entry (blockEquiv q (a, x))
                  (Equiv.swap (blockEquiv q (b₀, p.1)) (blockEquiv q (b₀, p.2))
                    (blockEquiv q (b, y))))).1)
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_of_ne_of_ne hne1' hne2']
          exact hfixL a b x y
      · exact hfixL a b x y
    -- Show `symBlk (swSquare L hL) = symBlk L`, hence `firstPair (swSquare L hL) = firstPair L`
    have hsw_symBlk : ∀ L (hL : L ∈ fixSet (H.map (sylowP q).subtype)),
        symBlk (swSquare L hL) = symBlk L := by
      intro L hL
      funext y
      change ((blockEquiv q).symm (swEntry L (blockEquiv q (a₀, 0)) (blockEquiv q (b₀, y)))).1 = _
      dsimp only [swEntry]
      simp only [Equiv.symm_apply_apply, ↓reduceIte]
      let p := firstPair L
      by_cases hy1 : y = p.1
      · subst hy1; rw [Equiv.swap_apply_left]; exact (hfp_blk L).symm
      · by_cases hy2 : y = p.2
        · subst hy2; rw [Equiv.swap_apply_right]; exact hfp_blk L
        · have hne1 : blockEquiv q (b₀, y) ≠ blockEquiv q (b₀, p.1) := fun h =>
            hy1 (congrArg Prod.snd ((blockEquiv q).injective h))
          have hne2 : blockEquiv q (b₀, y) ≠ blockEquiv q (b₀, p.2) := fun h =>
            hy2 (congrArg Prod.snd ((blockEquiv q).injective h))
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    have hsw_fp : ∀ L (hL : L ∈ fixSet (H.map (sylowP q).subtype)),
        firstPair (swSquare L hL) = firstPair L := by
      intro L hL
      have hpairs : pairs (swSquare L hL) = pairs L := by
        ext p; simp only [pairs, Finset.mem_filter, hsw_symBlk L hL]
      dsimp only [firstPair]
      simp_rw [hpairs]
    -- Show `swSquare` is an involution on `Fix(H)`
    have hsw_invol : ∀ L (hL : L ∈ fixSet (H.map (sylowP q).subtype)),
        swSquare (swSquare L hL) (hsw_fix L hL) = L := by
      intro L hL
      apply LatinSquare.ext
      funext r c
      change swEntry (swSquare L hL) r c = L.entry r c
      dsimp only [swEntry, swSquare]
      rw [hsw_fp L hL]
      split_ifs with hr
      · simp [Equiv.swap_apply_self]
      · rfl
    -- Show `squareSign (swSquare L hL) = -squareSign L`
    have hsw_sign : ∀ L (hL : L ∈ fixSet (H.map (sylowP q).subtype)),
        squareSign (swSquare L hL) = -squareSign L := by
      intro L hL
      let L' := swSquare L hL
      let p := firstPair L
      let c1 := blockEquiv q (b₀, p.1)
      let c2 := blockEquiv q (b₀, p.2)
      have hc12 : c1 ≠ c2 := fun h => hfp_ne L (congrArg Prod.snd ((blockEquiv q).injective h))
      -- Row signs: each of the `q` rows in block `a₀` flips sign; other `q` rows unchanged
      have hrow_sign : rowSign L' = -rowSign L := by
        unfold rowSign
        rw [← Equiv.prod_comp (blockEquiv q), ← Equiv.prod_comp (blockEquiv q)]
        rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
        have hblock : ∀ a : Fin 2,
            (∏ x : ZMod q, Equiv.Perm.sign (rowPerm L' (blockEquiv q (a, x)))) =
              (if a = a₀ then -1 else 1) *
                ∏ x : ZMod q, Equiv.Perm.sign (rowPerm L (blockEquiv q (a, x))) := by
          intro a
          split_ifs with ha
          · subst ha
            have heach : ∀ x : ZMod q,
                Equiv.Perm.sign (rowPerm L' (blockEquiv q (a, x))) =
                  -Equiv.Perm.sign (rowPerm L (blockEquiv q (a, x))) := by
              intro x
              have hperm : rowPerm L' (blockEquiv q (a, x)) =
                  rowPerm L (blockEquiv q (a, x)) * Equiv.swap c1 c2 := by
                apply Equiv.Perm.ext; intro c
                change swEntry L (blockEquiv q (a, x)) c =
                  L.entry (blockEquiv q (a, x)) (Equiv.swap c1 c2 c)
                simp [swEntry, c1, c2, p]
              rw [hperm, map_mul, Equiv.Perm.sign_swap hc12, mul_neg_one]
            simp_rw [heach]
            rw [Finset.prod_neg, Finset.card_univ, ZMod.card, hq_odd.neg_one_pow]
          · rw [one_mul]
            refine Finset.prod_congr rfl fun x _ => ?_
            have hperm : rowPerm L' (blockEquiv q (a, x)) = rowPerm L (blockEquiv q (a, x)) := by
              apply Equiv.Perm.ext; intro c
              change swEntry L (blockEquiv q (a, x)) c = L.entry (blockEquiv q (a, x)) c
              simp [swEntry, ha]
            rw [hperm]
        simp_rw [hblock]
        rw [Finset.prod_mul_distrib]
        have hprod_if : (∏ a : Fin 2, if a = a₀ then (-1 : ℤˣ) else 1) = -1 := by
          fin_cases a₀ <;> decide
        rw [hprod_if, neg_one_mul]
      -- Column signs: columns `c1, c2` compose on the left with mutually inverse permutations `τ, τ⁻¹`
      have hcol_sign : colSign L' = colSign L := by
        unfold colSign
        let f1 : Equiv.Perm (ZMod q) := Equiv.ofBijective _ (hcol_surj_blk L hL p.1)
        let f2 : Equiv.Perm (ZMod q) := Equiv.ofBijective _ (hcol_surj_blk L hL p.2)
        let cblk := symBlk L p.1
        let τ0 : Equiv.Perm (Fin 2 × ZMod q) :=
          { toFun := fun s => (s.1, if s.1 = cblk then f2 (f1.symm s.2) else s.2)
            invFun := fun s => (s.1, if s.1 = cblk then f1 (f2.symm s.2) else s.2)
            left_inv := fun s => Prod.ext rfl (by dsimp; split_ifs <;> simp)
            right_inv := fun s => Prod.ext rfl (by dsimp; split_ifs <;> simp) }
        let τ : Equiv.Perm (Fin (2 * q)) := (blockEquiv q).symm.trans (τ0.trans (blockEquiv q))
        have hc1_eq : colPerm L' c1 = τ * colPerm L c1 := by
          apply Equiv.Perm.ext; intro r
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          change swEntry L (blockEquiv q (a, x)) c1 = τ (L.entry (blockEquiv q (a, x)) c1)
          dsimp only [swEntry, τ, τ0, Equiv.trans_apply]
          simp only [Equiv.symm_apply_apply]
          split_ifs with ha
          · subst ha
            rw [Equiv.swap_apply_left]
            have h1 := hsym_const L hL x p.1
            have h2 := hsym_const L hL x p.2
            have h1' : ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).1 = cblk := h1
            have h2' : ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).1 = cblk :=
              h2.trans (hfp_blk L).symm
            have hf1x : f1 x = ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).2 := rfl
            have hf2x : f2 x = ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).2 := rfl
            change L.entry (blockEquiv q (a, x)) c2 =
              blockEquiv q (_, if ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).1 = cblk
                then f2 (f1.symm ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).2)
                else _)
            rw [if_pos h1', ← hf1x, Equiv.symm_apply_apply, hf2x, h1', ← h2']
            exact ((blockEquiv q).apply_symm_apply _).symm
          · have hne : ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).1 ≠ cblk :=
              hsym_other L hL a x p.1 ha
            change L.entry (blockEquiv q (a, x)) c1 =
              blockEquiv q (_, if ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).1 = cblk
                then _ else _)
            rw [if_neg hne]
            exact ((blockEquiv q).apply_symm_apply _).symm
        have hc2_eq : colPerm L' c2 = τ⁻¹ * colPerm L c2 := by
          apply Equiv.Perm.ext; intro r
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          change swEntry L (blockEquiv q (a, x)) c2 = τ⁻¹ (L.entry (blockEquiv q (a, x)) c2)
          dsimp only [swEntry, τ, τ0, Equiv.Perm.inv_def, Equiv.symm_trans_apply, Equiv.trans_apply]
          simp only [Equiv.symm_apply_apply]
          split_ifs with ha
          · subst ha
            rw [Equiv.swap_apply_right]
            have h1 := hsym_const L hL x p.1
            have h2 := hsym_const L hL x p.2
            have h1' : ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).1 = cblk := h1
            have h2' : ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).1 = cblk :=
              h2.trans (hfp_blk L).symm
            have hf1x : f1 x = ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c1)).2 := rfl
            have hf2x : f2 x = ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).2 := rfl
            change L.entry (blockEquiv q (a, x)) c1 =
              blockEquiv q (_, if ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).1 = cblk
                then f1 (f2.symm ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).2)
                else _)
            rw [if_pos h2', ← hf2x, Equiv.symm_apply_apply, hf1x, h2', ← h1']
            exact ((blockEquiv q).apply_symm_apply _).symm
          · have hne : ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).1 ≠ cblk := by
              rw [show cblk = symBlk L p.2 from hfp_blk L]
              exact hsym_other L hL a x p.2 ha
            change L.entry (blockEquiv q (a, x)) c2 =
              blockEquiv q (_, if ((blockEquiv q).symm (L.entry (blockEquiv q (a, x)) c2)).1 = cblk
                then _ else _)
            rw [if_neg hne]
            exact ((blockEquiv q).apply_symm_apply _).symm
        have hother_col : ∀ c, c ≠ c1 → c ≠ c2 → colPerm L' c = colPerm L c := by
          intro c h1 h2
          apply Equiv.Perm.ext; intro r
          change swEntry L r c = L.entry r c
          dsimp only [swEntry]
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
          split_ifs <;> rfl
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c1),
            ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hc12.symm, Finset.mem_univ c2⟩)]
        conv_rhs =>
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c1),
              ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hc12.symm, Finset.mem_univ c2⟩)]
        have hrest :
            ∏ c ∈ (Finset.univ.erase c1).erase c2, Equiv.Perm.sign (colPerm L' c) =
            ∏ c ∈ (Finset.univ.erase c1).erase c2, Equiv.Perm.sign (colPerm L c) := by
          refine Finset.prod_congr rfl fun c hc => ?_
          rw [hother_col c (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
            (Finset.mem_erase.mp hc).1]
        rw [hrest, hc1_eq, hc2_eq, map_mul, map_mul, map_inv]
        have hinv : Equiv.Perm.sign τ * (Equiv.Perm.sign τ)⁻¹ = 1 := mul_inv_cancel _
        calc Equiv.Perm.sign τ * Equiv.Perm.sign (colPerm L c1) *
              ((Equiv.Perm.sign τ)⁻¹ * Equiv.Perm.sign (colPerm L c2) *
                ∏ c ∈ (Finset.univ.erase c1).erase c2, Equiv.Perm.sign (colPerm L c))
            = (Equiv.Perm.sign τ * (Equiv.Perm.sign τ)⁻¹) *
              (Equiv.Perm.sign (colPerm L c1) * (Equiv.Perm.sign (colPerm L c2) *
                ∏ c ∈ (Finset.univ.erase c1).erase c2, Equiv.Perm.sign (colPerm L c))) := by ac_rfl
          _ = _ := by rw [hinv, one_mul]
      unfold squareSign
      rw [hrow_sign, hcol_sign, neg_mul]
    -- Sign-reversing involution on `FixFin` implies `S_twoq q H = 0`
    unfold S_twoq signedFixSum
    have hneg :
        (∑ L ∈ FixFin, (squareSign L : ℤ)) = -(∑ L ∈ FixFin, (squareSign L : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij (fun L hL => swSquare L (Finset.mem_filter.mp hL).2) ?_ ?_ ?_ ?_
      · intro L hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsw_fix L (Finset.mem_filter.mp hL).2⟩
      · intro L₁ hL₁ L₂ hL₂ hEq
        have h1 := hsw_invol L₁ (Finset.mem_filter.mp hL₁).2
        have h2 := hsw_invol L₂ (Finset.mem_filter.mp hL₂).2
        let SType := { M : LatinSquare (2 * q) // M ∈ fixSet (H.map (sylowP q).subtype) }
        have hsub : (⟨swSquare L₁ (Finset.mem_filter.mp hL₁).2,
            hsw_fix L₁ (Finset.mem_filter.mp hL₁).2⟩ : SType) =
          ⟨swSquare L₂ (Finset.mem_filter.mp hL₂).2,
            hsw_fix L₂ (Finset.mem_filter.mp hL₂).2⟩ := Subtype.ext hEq
        rw [← h1, ← h2]
        exact congrArg (fun M : SType => swSquare M.1 M.2) hsub
      · intro L hL
        refine ⟨swSquare L (Finset.mem_filter.mp hL).2,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsw_fix L (Finset.mem_filter.mp hL).2⟩,
          hsw_invol L (Finset.mem_filter.mp hL).2⟩
      · intro L hL
        rw [hsw_sign L (Finset.mem_filter.mp hL).2]
        simp
    change ∑ L ∈ FixFin, (squareSign L : ℤ) = 0
    linarith
  · -- Case A: `H` fixes all rows! Pick `g ∈ H, g ≠ 1`; then `Fix(H) = ∅`.
    push Not at hmove
    obtain ⟨g, hgH, hg1⟩ : ∃ g ∈ H, g ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hH
      ext x
      exact ⟨fun hx => hall x hx, fun hx => by rw [hx]; exact H.one_mem⟩
    have hu0 : (sylowToVec g).1 = 0 := by ext a; exact hmove a g hgH
    unfold S_twoq signedFixSum
    refine Finset.sum_eq_zero fun L hL => ?_
    exfalso
    have hgfix : g.1 • L = L := (Finset.mem_filter.mp hL).2 g.1 ⟨g, hgH, rfl⟩
    have hent := (sylow_fix_entry_iff g L).mp hgfix
    -- `g` fixes all rows and column `(b₀, y₀)`, so `w = 0`, then `v = 0`
    have hw0 : (sylowToVec g).2.2 = 0 := by
      ext c
      obtain ⟨row, hrow_eq⟩ := (L.col_bijective (blockEquiv q (b₀, y₀))).2 (blockEquiv q (c, 0))
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective row
      have hrow_eq' : L.entry (blockEquiv q (a, x)) (blockEquiv q (b₀, y₀)) = blockEquiv q (c, 0) :=
        hrow_eq
      have h1 := hent a b₀ x y₀
      dsimp only at h1
      rw [hu0, hv0 g hgH, Pi.zero_apply, add_zero, add_zero, hrow_eq', Equiv.symm_apply_apply] at h1
      have h2 := congrArg Prod.snd ((blockEquiv q).injective h1)
      simpa using h2.symm
    have hv_all : (sylowToVec g).2.1 = 0 := by
      ext b
      have h1 := hent 0 b 0 0
      dsimp only at h1
      simp only [hu0, hw0, Pi.zero_apply, add_zero, zero_add] at h1
      rw [Prod.eta, Equiv.apply_symm_apply] at h1
      have h2 := (L.row_bijective (blockEquiv q (0, 0))).1 h1
      have h3 := congrArg Prod.snd ((blockEquiv q).injective h2)
      simpa using h3
    apply hg1
    apply sylowToVec_injective
    rw [sylowToVec_one]
    exact Prod.ext hu0 (Prod.ext hv_all hw0)

/-- Lemma 6.6(i): fixed column or fixed row implies `S_twoq q H = 0`. -/
theorem lem_6_6_part1 {q : ℕ} [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (H : Subgroup (sylowP q)) (hH : H ≠ ⊥)
    (hfix : (∃ c : Fin (2 * q), ∀ g ∈ H, g.1.2.1 c = c) ∨
            (∃ r : Fin (2 * q), ∀ g ∈ H, g.1.1 r = r)) :
    S_twoq q H = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  rcases hfix with ⟨c, hc⟩ | ⟨r, hr⟩
  · exact S_twoq_eq_zero_of_fixed_col hq hodd H hH c hc
  · rw [← ((lem_6_4_signs q hodd).2.2.2.2.2.2.2 H).2]
    refine S_twoq_eq_zero_of_fixed_col hq hodd (transposeSubgroup H) ?_ r ?_
    · intro hbot
      apply hH
      ext g
      simp only [Subgroup.mem_bot]
      constructor
      · intro hg
        have hmem : (⟨(g.1.2.1, g.1.1, g.1.2.2), by
            rcases g.2 with ⟨v, hv⟩
            refine ⟨Multiplicative.ofAdd
              ((Multiplicative.toAdd v).2.1, (Multiplicative.toAdd v).1,
                (Multiplicative.toAdd v).2.2), ?_⟩
            rw [← hv]; rfl⟩ : sylowP q) ∈ transposeSubgroup H := ⟨g, hg, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        have h1 : g.1.2.1 = 1 := congrArg (fun x : sylowP q => x.1.1) hmem
        have h2 : g.1.1 = 1 := congrArg (fun x : sylowP q => x.1.2.1) hmem
        have h3 : g.1.2.2 = 1 := congrArg (fun x : sylowP q => x.1.2.2) hmem
        apply Subtype.ext
        exact Prod.ext h2 (Prod.ext h1 h3)
      · rintro rfl; exact H.one_mem
    · intro g' hg'
      rcases hg' with ⟨g, hg, hge⟩
      have h1 : g'.1.2.1 = g.1.1 := (congrArg (fun x : sylowP q => x.1.2.1) hge).symm
      rw [h1]
      exact hr g hg

/-! ### Part (ii) of Lemma 6.6: Rank 3 Subgroups -/

theorem lem_6_6_part2 {q : ℕ} [NeZero q] (hq : q.Prime) (hodd : q ≠ 2)
    (H : Subgroup (sylowP q)) (hH : elemRank q H = 3) :
    (∀ L : LatinSquare (2 * q), L ∈ fixSet (H.map (sylowP q).subtype) →
      ∀ g : sylowP q, g.1 • L = L → g ∈ H) ∧
    (q : ℤ) ^ 3 ∣ S_twoq q H := by
  classical
  have hstab : ∀ L : LatinSquare (2 * q), L ∈ fixSet (H.map (sylowP q).subtype) →
      ∀ g : sylowP q, g.1 • L = L → g ∈ H := by
    intro L hL g hg
    let K : Subgroup (sylowP q) := H ⊔ Subgroup.zpowers g
    have hKfix : L ∈ fixSet (K.map (sylowP q).subtype) := by
      rintro _ ⟨k, hk, rfl⟩
      have hle : K ≤ MulAction.stabilizer (sylowP q) L := by
        let _ : MulAction (sylowP q) (LatinSquare (2 * q)) :=
          { smul := fun x M => x.1 • M
            one_smul := fun M => one_smul _ M
            mul_smul := fun x y M => mul_smul x.1 y.1 M }
        refine sup_le (fun h hh => hL h.1 ⟨h, hh, rfl⟩) ?_
        rw [Subgroup.zpowers_le]
        exact hg
      exact hle hk
    have hKrank : elemRank q K ≤ 3 :=
      (lem_6_3_orbred q hq hodd).1 K ⟨L, hKfix⟩
    have hHcard : Nat.card H = q ^ 3 := by
      rw [card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H), hH]
    have hKcard : Nat.card K = q ^ elemRank q K :=
      card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q K)
    have hle_card : Nat.card K ≤ Nat.card H := by
      rw [hKcard, hHcard]
      exact Nat.pow_le_pow_right hq.pos hKrank
    have hHK_eq : H = K := by
      have hcard_eq : Nat.card H = Nat.card K :=
        le_antisymm (Nat.le_of_dvd (by rw [hKcard]; exact pow_pos hq.pos _)
          (Subgroup.card_dvd_of_le le_sup_left)) hle_card
      exact Subgroup.eq_of_le_of_card_ge le_sup_left hle_card
    rw [hHK_eq]
    exact (le_sup_right : Subgroup.zpowers g ≤ K) (Subgroup.mem_zpowers g)
  refine ⟨hstab, ?_⟩
  -- `sylowP q / H` (of order `q^3`) acts freely on `Fix(H)` preserving `squareSign`
  let FixT := { L : LatinSquare (2 * q) // L ∈ fixSet (H.map (sylowP q).subtype) }
  have hP_pres : ∀ (g : sylowP q) (L : LatinSquare (2 * q)),
      L ∈ fixSet (H.map (sylowP q).subtype) → g.1 • L ∈ fixSet (H.map (sylowP q).subtype) := by
    intro g L hL
    rintro _ ⟨h, hh, rfl⟩
    have hcomm : h * g = g * h :=
      (isElemAbelian_sylowP_subgroup q ⊤).1 h trivial g trivial
    have hcomm1 : h.1 * g.1 = g.1 * h.1 := congrArg Subtype.val hcomm
    change h.1 • (g.1 • L) = g.1 • L
    rw [← mul_smul, hcomm1, mul_smul, hL h.1 ⟨h, hh, rfl⟩]
  let _ : MulAction (sylowP q) FixT :=
    { smul := fun g L => ⟨g.1 • L.1, hP_pres g L.1 L.2⟩
      one_smul := fun L => Subtype.ext (one_smul _ _)
      mul_smul := fun g₁ g₂ L => Subtype.ext (mul_smul _ _ _) }
  unfold S_twoq signedFixSum
  have hsum :
      (∑ L ∈ Finset.univ.filter (fun L : LatinSquare (2 * q) => L ∈ fixSet (H.map (sylowP q).subtype)),
        (squareSign L : ℤ)) =
      ∑ L : FixT, (squareSign L.1 : ℤ) := by
    rw [Finset.sum_subtype (p := fun L => L ∈ fixSet (H.map (sylowP q).subtype)) _ (fun _ => by simp)]
  rw [hsum]
  let orbRel := MulAction.orbitRel (sylowP q) FixT
  have : Fintype (Quotient orbRel) := Fintype.ofFinite _
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Quotient orbRel)))
    (g := Quotient.mk orbRel) (fun _ _ => Finset.mem_univ _)]
  refine Finset.dvd_sum fun o _ => ?_
  obtain ⟨L₀, rfl⟩ := Quotient.exists_rep o
  have hconst : ∀ L ∈ Finset.univ.filter (fun L : FixT => Quotient.mk orbRel L = Quotient.mk orbRel L₀),
      (squareSign L.1 : ℤ) = (squareSign L₀.1 : ℤ) := by
    intro L hL
    rcases Quotient.exact (Finset.mem_filter.mp hL).2 with ⟨g, hg⟩
    have hg' : g.1 • L₀.1 = L.1 := congrArg Subtype.val hg
    rw [← hg', squareSign_isotopyAct_even ⟨q, by ring⟩]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- Orbit size equals `|sylowP q / H| = q^3`
  have hcard_orb :
      (Finset.univ.filter (fun L : FixT => Quotient.mk orbRel L = Quotient.mk orbRel L₀)).card =
      q ^ 3 := by
    have : H.Normal :=
      ⟨fun n hn g => by
        have hcomm := (isElemAbelian_sylowP_subgroup q ⊤).1 g trivial n trivial
        rw [hcomm, mul_inv_cancel_right]
        exact hn⟩
    have hqcard : Fintype.card (sylowP q ⧸ H) = q ^ 3 := by
      have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup H
      rw [natCard_sylowP, card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H),
        hH, Nat.card_eq_fintype_card] at hlag
      have hpow : q ^ 6 = q ^ 3 * q ^ 3 := by ring
      rw [hpow] at hlag
      exact (Nat.mul_right_cancel (pow_pos hq.pos 3) hlag).symm
    let rep : sylowP q ⧸ H → sylowP q := fun x => Classical.choose (QuotientGroup.mk_surjective x)
    have hrep : ∀ x : sylowP q ⧸ H, (rep x : sylowP q ⧸ H) = x := fun x =>
      Classical.choose_spec (QuotientGroup.mk_surjective x)
    rw [← hqcard]
    symm
    refine Finset.card_bij (fun (x : sylowP q ⧸ H) _ => rep x • L₀) ?_ ?_ ?_
    · intro x _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.sound ⟨rep x, rfl⟩⟩
    · intro x₁ _ x₂ _ hEq
      have hEq' : (rep x₁).1 • L₀.1 = (rep x₂).1 • L₀.1 := congrArg Subtype.val hEq
      have hfix1 : ((rep x₂)⁻¹ * rep x₁).1 • L₀.1 = L₀.1 := by
        change (rep x₂).1⁻¹ • (rep x₁).1 • L₀.1 = L₀.1
        rw [hEq', inv_smul_smul]
      have hmemH : (rep x₂)⁻¹ * rep x₁ ∈ H := hstab L₀.1 L₀.2 _ hfix1
      have hqeq : (rep x₁ : sylowP q ⧸ H) = (rep x₂ : sylowP q ⧸ H) := by
        rw [QuotientGroup.eq]
        have := H.inv_mem hmemH
        simpa [mul_inv_rev] using this
      rw [← hrep x₁, ← hrep x₂]
      exact hqeq
    · intro L hL
      rcases Quotient.exact (Finset.mem_filter.mp hL).2 with ⟨g, hg⟩
      refine ⟨(g : sylowP q ⧸ H), Finset.mem_univ _, ?_⟩
      have hrel : (rep (g : sylowP q ⧸ H))⁻¹ * g ∈ H := by
        rw [← QuotientGroup.eq]
        exact hrep (g : sylowP q ⧸ H)
      have hfix : ((rep (g : sylowP q ⧸ H))⁻¹ * g).1 • L₀.1 = L₀.1 :=
        L₀.2 _ ⟨_, hrel, rfl⟩
      apply Subtype.ext
      rw [← congrArg Subtype.val hg]
      change (rep (g : sylowP q ⧸ H)).1 • L₀.1 = g.1 • L₀.1
      have hmul : g.1 = (rep (g : sylowP q ⧸ H)).1 * ((rep (g : sylowP q ⧸ H))⁻¹ * g).1 := by
        change g.1 = (rep _).1 * ((rep _).1⁻¹ * g.1)
        group
      conv_rhs => rw [hmul, mul_smul, hfix]
  rw [hcard_orb]
  exact dvd_mul_right _ _

/-! ### Representative-Row/Column Sign Formula & Unified Fact 2 -/

/-- When `H` moves both row blocks and both column blocks, `ε(L)` is the product of the signs of
rows `(0, 0), (1, 0)` and columns `(0, 0), (1, 0)`. -/
lemma squareSign_of_all_moving {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (H : Subgroup (sylowP q)) (L : LatinSquare (2 * q))
    (hL : L ∈ fixSet (H.map (sylowP q).subtype))
    (hrow : ∀ a : Fin 2, ∃ g ∈ H, (sylowToVec g).1 a ≠ 0)
    (hcol : ∀ b : Fin 2, ∃ g ∈ H, (sylowToVec g).2.1 b ≠ 0) :
    squareSign L =
      Equiv.Perm.sign (rowPerm L (blockEquiv q (0, 0))) *
      Equiv.Perm.sign (rowPerm L (blockEquiv q (1, 0))) *
      Equiv.Perm.sign (colPerm L (blockEquiv q (0, 0))) *
      Equiv.Perm.sign (colPerm L (blockEquiv q (1, 0))) := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  have horb := ((lem_6_4_signs q hodd).1 H L hL).1
  have hrow_const : ∀ (a : Fin 2) (x : ZMod q),
      Equiv.Perm.sign (rowPerm L (blockEquiv q (a, x))) =
        Equiv.Perm.sign (rowPerm L (blockEquiv q (a, 0))) := by
    intro a x
    obtain ⟨g, hgH, hga⟩ := hrow a
    let t : ZMod q := x * ((sylowToVec g).1 a)⁻¹
    have hpow : g ^ t.val ∈ H := H.pow_mem hgH t.val
    have hstep : ∀ k : ℕ, (sylowToVec (g ^ k)).1 a = (k : ZMod q) * (sylowToVec g).1 a := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, sylowToVec_mul]
        change (sylowToVec (g ^ k)).1 a + (sylowToVec g).1 a = _
        rw [ih]; push_cast; ring
    have hact : (g ^ t.val).1.1 (blockEquiv q (a, 0)) = blockEquiv q (a, x) := by
      rw [sylowToVec_val, blockTransPerm_apply, zero_add, hstep, ZMod.natCast_zmod_val]
      congr 1; exact Prod.ext rfl (by dsimp only [t]; field_simp [hga])
    rw [← hact]
    exact (horb (g ^ t.val) hpow).1 (blockEquiv q (a, 0))
  have hcol_const : ∀ (b : Fin 2) (y : ZMod q),
      Equiv.Perm.sign (colPerm L (blockEquiv q (b, y))) =
        Equiv.Perm.sign (colPerm L (blockEquiv q (b, 0))) := by
    intro b y
    obtain ⟨g, hgH, hgb⟩ := hcol b
    let t : ZMod q := y * ((sylowToVec g).2.1 b)⁻¹
    have hpow : g ^ t.val ∈ H := H.pow_mem hgH t.val
    have hstep : ∀ k : ℕ, (sylowToVec (g ^ k)).2.1 b = (k : ZMod q) * (sylowToVec g).2.1 b := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, sylowToVec_mul]
        change (sylowToVec (g ^ k)).2.1 b + (sylowToVec g).2.1 b = _
        rw [ih]; push_cast; ring
    have hact : (g ^ t.val).1.2.1 (blockEquiv q (b, 0)) = blockEquiv q (b, y) := by
      rw [sylowToVec_val, blockTransPerm_apply, zero_add, hstep, ZMod.natCast_zmod_val]
      congr 1; exact Prod.ext rfl (by dsimp only [t]; field_simp [hgb])
    rw [← hact]
    exact (horb (g ^ t.val) hpow).2 (blockEquiv q (b, 0))
  have hodd_pow : ∀ u : ℤˣ, u ^ q = u := by
    intro u; rcases Int.units_eq_one_or u with rfl | rfl
    · simp
    · exact hq_odd.neg_one_pow
  have hR : rowSign L = Equiv.Perm.sign (rowPerm L (blockEquiv q (0, 0))) *
      Equiv.Perm.sign (rowPerm L (blockEquiv q (1, 0))) := by
    unfold rowSign
    rw [← Equiv.prod_comp (blockEquiv q), Fintype.prod_prod_type]
    simp_rw [hrow_const, Finset.prod_const, Finset.card_univ, ZMod.card, hodd_pow]
    exact Fin.prod_univ_two _
  have hC : colSign L = Equiv.Perm.sign (colPerm L (blockEquiv q (0, 0))) *
      Equiv.Perm.sign (colPerm L (blockEquiv q (1, 0))) := by
    unfold colSign
    rw [← Equiv.prod_comp (blockEquiv q), Fintype.prod_prod_type]
    simp_rw [hcol_const, Finset.prod_const, Finset.card_univ, ZMod.card, hodd_pow]
    exact Fin.prod_univ_two _
  unfold squareSign
  rw [hR, hC]
  ac_rfl

/-- Sign of an affine permutation `x ↦ lam * x + z` on `ZMod q` equals `legendreSym q lam`. -/
lemma sign_affine_zmod {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) {lam : ZMod q} (hlam : lam ≠ 0)
    (z : ZMod q) :
    (Equiv.Perm.sign ((Equiv.mulLeft₀ lam hlam).trans (Equiv.addRight z)) : ℤ) =
      legendreSym q (lam.val : ℤ) := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  change (Equiv.Perm.sign (Equiv.addRight z * Equiv.mulLeft₀ lam hlam) : ℤ) = _
  rw [map_mul, sign_addRight_eq_one hq_odd, one_mul]
  exact sign_mulLeft_eq_legendreSym hodd (Units.mk0 lam hlam)

/-- **Unified Fact 2**: If all four blocks `(a, b)` have surjective `(α_a, β_b) : H → F_q^2`
and `w_c = λ_{abc} u_a + μ_{abc} v_b` on `H`, then unconditionally:
`S(H) = q^4 * ∑_{c₀ : Fin 2} ∏_{a, b} χ(λ_{a,b,c₀+a+b} * μ_{a,b,c₀+a+b})`. -/
theorem S_twoq_four_affine {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (H : Subgroup (sylowP q))
    (lam mu : Fin 2 → Fin 2 → Fin 2 → ZMod q)
    (hsurj : ∀ a b : Fin 2, ∀ x y : ZMod q,
      ∃ g ∈ H, (sylowToVec g).1 a = x ∧ (sylowToVec g).2.1 b = y)
    (hslopes : ∀ a b c : Fin 2, ∀ g ∈ H,
      (sylowToVec g).2.2 c = lam a b c * (sylowToVec g).1 a + mu a b c * (sylowToVec g).2.1 b) :
    S_twoq q H =
      (q : ℤ) ^ 4 * ∑ c₀ : Fin 2,
        ∏ a : Fin 2, ∏ b : Fin 2,
          legendreSym q ((lam a b (c₀ + a + b) * mu a b (c₀ + a + b)).val : ℤ) := by
  classical
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  -- Moving hypotheses for `squareSign_of_all_moving`
  have hrow_mv : ∀ a : Fin 2, ∃ g ∈ H, (sylowToVec g).1 a ≠ 0 := fun a => by
    obtain ⟨g, hg, h1, _⟩ := hsurj a 0 1 0
    exact ⟨g, hg, by rw [h1]; exact one_ne_zero⟩
  have hcol_mv : ∀ b : Fin 2, ∃ g ∈ H, (sylowToVec g).2.1 b ≠ 0 := fun b => by
    obtain ⟨g, hg, _, h2⟩ := hsurj 0 b 0 1
    exact ⟨g, hg, by rw [h2]; exact one_ne_zero⟩
  -- For any `L ∈ Fix(H)`, each block `(a, b)` is affine of the form `(c_{ab}, z_{ab} + λ x + μ y)`
  have hblock_form : ∀ (L : LatinSquare (2 * q)), L ∈ fixSet (H.map (sylowP q).subtype) →
      ∀ a b : Fin 2,
      let p0 := (blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0)))
      (∀ x y : ZMod q, L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
        blockEquiv q (p0.1, p0.2 + lam a b p0.1 * x + mu a b p0.1 * y)) ∧
      lam a b p0.1 ≠ 0 ∧ mu a b p0.1 ≠ 0 := by
    intro L hL a b
    let p0 := (blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0)))
    have hform : ∀ x y : ZMod q, L.entry (blockEquiv q (a, x)) (blockEquiv q (b, y)) =
        blockEquiv q (p0.1, p0.2 + lam a b p0.1 * x + mu a b p0.1 * y) := by
      intro x y
      obtain ⟨g, hgH, hgx, hgy⟩ := hsurj a b x y
      have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) a b 0 0
      rw [hgx, hgy, zero_add, zero_add] at hent
      rw [hent, hslopes a b p0.1 g hgH, hgx, hgy, add_assoc]
    refine ⟨hform, ?_, ?_⟩
    · intro h0
      have h1 := hform 0 0
      have h2 := hform 1 0
      rw [h0, zero_mul] at h1 h2
      have hinj := (L.col_bijective (blockEquiv q (b, 0))).1 (h1.trans h2.symm)
      exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective hinj))
    · intro h0
      have h1 := hform 0 0
      have h2 := hform 0 1
      rw [h0, zero_mul] at h1 h2
      have hinj := (L.row_bijective (blockEquiv q (a, 0))).1 (h1.trans h2.symm)
      exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective hinj))
  -- Checkerboard: for `L ∈ Fix(H)`, `c(a, b) = c(0, 0) + a + b`
  have hchecker : ∀ (L : LatinSquare (2 * q)), L ∈ fixSet (H.map (sylowP q).subtype) →
      ∀ a b : Fin 2,
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0)))).1 =
        ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 + a + b := by
    intro L hL
    let cb (a b : Fin 2) : Fin 2 :=
      ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0)))).1
    have hrow_ne : ∀ a : Fin 2, cb a 0 ≠ cb a 1 := by
      intro a heq
      obtain ⟨hf0, _, hmu0⟩ := hblock_form L hL a 0
      obtain ⟨hf1, _, _⟩ := hblock_form L hL a 1
      let z0 := ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, 0)))).2
      let z1 := ((blockEquiv q).symm (L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, 0)))).2
      let y0 : ZMod q := (z1 - z0) * (mu a 0 (cb a 0))⁻¹
      have h0 := hf0 0 y0
      have h1 := hf1 0 0
      have he : L.entry (blockEquiv q (a, 0)) (blockEquiv q (0, y0)) =
          L.entry (blockEquiv q (a, 0)) (blockEquiv q (1, 0)) := by
        rw [h0, h1]
        congr 1
        refine Prod.ext heq ?_
        dsimp only [y0, z0, z1, cb]
        rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
        field_simp [hmu0]
        ring
      have hc := (L.row_bijective (blockEquiv q (a, 0))).1 he
      exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective hc))
    have hcol_ne : ∀ b : Fin 2, cb 0 b ≠ cb 1 b := by
      intro b heq
      obtain ⟨hf0, hlam0, _⟩ := hblock_form L hL 0 b
      obtain ⟨hf1, _, _⟩ := hblock_form L hL 1 b
      let z0 := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (b, 0)))).2
      let z1 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (b, 0)))).2
      let x0 : ZMod q := (z1 - z0) * (lam 0 b (cb 0 b))⁻¹
      have h0 := hf0 x0 0
      have h1 := hf1 0 0
      have he : L.entry (blockEquiv q (0, x0)) (blockEquiv q (b, 0)) =
          L.entry (blockEquiv q (1, 0)) (blockEquiv q (b, 0)) := by
        rw [h0, h1]
        congr 1
        refine Prod.ext heq ?_
        dsimp only [x0, z0, z1, cb]
        rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
        field_simp [hlam0]
        ring
      have hr := (L.col_bijective (blockEquiv q (b, 0))).1 he
      exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective hr))
    have h01 : cb 0 1 = 1 - cb 0 0 := fin2_ne_eq_one_sub (hrow_ne 0).symm
    have h10 : cb 1 0 = 1 - cb 0 0 := fin2_ne_eq_one_sub (hcol_ne 0).symm
    have h11 : cb 1 1 = cb 0 0 := by
      have := fin2_ne_eq_one_sub (hrow_ne 1).symm
      rw [h10, fin2_one_sub_one_sub] at this
      exact this
    intro a b
    have hfin : ∀ x : Fin 2, 1 - x = x + 1 := fun x => by fin_cases x <;> decide
    fin_cases a <;> fin_cases b
    · change cb 0 0 = cb 0 0 + 0 + 0; simp
    · change cb 0 1 = cb 0 0 + 0 + 1; rw [h01, hfin]; simp
    · change cb 1 0 = cb 0 0 + 1 + 0; rw [h10, hfin]; simp
    · change cb 1 1 = cb 0 0 + 1 + 1; rw [h11]; generalize cb 0 0 = d; fin_cases d <;> decide
  -- Split `S_twoq q H` by the layout `c₀ = c(0, 0) ∈ Fin 2`
  unfold S_twoq signedFixSum
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Fin 2)))
    (g := fun L : LatinSquare (2 * q) =>
      ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1)
    (fun _ _ => Finset.mem_univ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₀ _ => ?_
  by_cases hnz : ∀ a b : Fin 2, lam a b (c₀ + a + b) ≠ 0 ∧ mu a b (c₀ + a + b) ≠ 0
  · -- All 8 slopes for layout `c₀` are nonzero: bijection with `z : Fin 2 × Fin 2 → ZMod q`
    let build (z : Fin 2 × Fin 2 → ZMod q) : LatinSquare (2 * q) :=
      { entry := fun r c =>
          let pr := (blockEquiv q).symm r
          let pc := (blockEquiv q).symm c
          let cb := c₀ + pr.1 + pc.1
          blockEquiv q (cb, z (pr.1, pc.1) + lam pr.1 pc.1 cb * pr.2 + mu pr.1 pc.1 cb * pc.2)
        row_bijective := fun r => by
          rw [← Finite.injective_iff_bijective]
          intro c₁ c₂ hEq
          obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective c₁
          obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective c₂
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          simp only [Equiv.symm_apply_apply] at hEq
          have hp := (blockEquiv q).injective hEq
          have hb : b₁ = b₂ := by
            have h1 : c₀ + a + b₁ = c₀ + a + b₂ := congrArg Prod.fst hp
            exact add_left_cancel h1
          subst hb
          have h2 : mu a b₁ (c₀ + a + b₁) * y₁ = mu a b₁ (c₀ + a + b₁) * y₂ := by
            have := congrArg Prod.snd hp
            linear_combination this
          have hy := mul_left_cancel₀ (hnz a b₁).2 h2
          subst hy; rfl
        col_bijective := fun c => by
          rw [← Finite.injective_iff_bijective]
          intro r₁ r₂ hEq
          obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
          obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
          obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective c
          simp only [Equiv.symm_apply_apply] at hEq
          have hp := (blockEquiv q).injective hEq
          have ha : a₁ = a₂ := by
            have h1 : c₀ + a₁ + b = c₀ + a₂ + b := congrArg Prod.fst hp
            exact add_left_cancel (add_right_cancel h1)
          subst ha
          have h2 : lam a₁ b (c₀ + a₁ + b) * x₁ = lam a₁ b (c₀ + a₁ + b) * x₂ := by
            have := congrArg Prod.snd hp
            linear_combination this
          have hx := mul_left_cancel₀ (hnz a₁ b).1 h2
          subst hx; rfl }
    -- Sign of `build z`
    have hbuild_fix : ∀ z, build z ∈ fixSet (H.map (sylowP q).subtype) := by
      intro z
      rintro _ ⟨g, hgH, rfl⟩
      change g.1 • build z = build z
      rw [sylow_fix_entry_iff]
      intro a b x y
      dsimp only [build]
      simp only [Equiv.symm_apply_apply]
      congr 1
      refine Prod.ext rfl ?_
      rw [hslopes a b (c₀ + a + b) g hgH]
      ring
    have hbuild_sign : ∀ z,
        (squareSign (build z) : ℤ) =
          ∏ a : Fin 2, ∏ b : Fin 2,
            legendreSym q ((lam a b (c₀ + a + b) * mu a b (c₀ + a + b)).val : ℤ) := by
      intro z
      rw [squareSign_of_all_moving hodd H (build z) (hbuild_fix z) hrow_mv hcol_mv]
      -- Compute the 4 representative row/col signs via `sign_blockPerm`
      have hrow_s : ∀ a : Fin 2,
          (Equiv.Perm.sign (rowPerm (build z) (blockEquiv q (a, 0))) : ℤ) =
            (if c₀ + a = 0 then (1 : ℤ) else -1) *
              legendreSym q ((mu a 0 (c₀ + a + 0)).val : ℤ) *
              legendreSym q ((mu a 1 (c₀ + a + 1)).val : ℤ) := by
        intro a
        let ϖ : Equiv.Perm (Fin 2) := if c₀ + a = 0 then 1 else Equiv.swap 0 1
        let φ : Fin 2 → Equiv.Perm (ZMod q) := fun b =>
          (Equiv.mulLeft₀ (mu a b (c₀ + a + b)) (hnz a b).2).trans (Equiv.addRight (z (a, b)))
        have hperm : rowPerm (build z) (blockEquiv q (a, 0)) = blockPerm q ϖ φ := by
          apply Equiv.Perm.ext; intro k
          obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective k
          rw [blockPerm_apply]
          change (build z).entry (blockEquiv q (a, 0)) (blockEquiv q (b, y)) = _
          dsimp only [build]
          simp only [Equiv.symm_apply_apply]
          congr 1
          refine Prod.ext ?_ ?_
          · dsimp only [ϖ]; fin_cases c₀ <;> fin_cases a <;> fin_cases b <;> decide
          · dsimp only [φ]; change z (a, b) + lam a b (c₀ + a + b) * 0 + mu a b (c₀ + a + b) * y =
              mu a b (c₀ + a + b) * y + z (a, b); ring
        rw [hperm, sign_blockPerm_eq hq_odd]
        have hϖ : (((if ϖ = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) =
            if c₀ + a = 0 then 1 else -1 := by
          dsimp only [ϖ]; fin_cases c₀ <;> fin_cases a <;> decide
        dsimp only [φ]
        rw [Units.val_mul, Units.val_mul, hϖ, sign_affine_zmod hodd, sign_affine_zmod hodd]
      have hcol_s : ∀ b : Fin 2,
          (Equiv.Perm.sign (colPerm (build z) (blockEquiv q (b, 0))) : ℤ) =
            (if c₀ + b = 0 then (1 : ℤ) else -1) *
              legendreSym q ((lam 0 b (c₀ + 0 + b)).val : ℤ) *
              legendreSym q ((lam 1 b (c₀ + 1 + b)).val : ℤ) := by
        intro b
        let ϖ : Equiv.Perm (Fin 2) := if c₀ + b = 0 then 1 else Equiv.swap 0 1
        let φ : Fin 2 → Equiv.Perm (ZMod q) := fun a =>
          (Equiv.mulLeft₀ (lam a b (c₀ + a + b)) (hnz a b).1).trans (Equiv.addRight (z (a, b)))
        have hperm : colPerm (build z) (blockEquiv q (b, 0)) = blockPerm q ϖ φ := by
          apply Equiv.Perm.ext; intro k
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective k
          rw [blockPerm_apply]
          change (build z).entry (blockEquiv q (a, x)) (blockEquiv q (b, 0)) = _
          dsimp only [build]
          simp only [Equiv.symm_apply_apply]
          congr 1
          refine Prod.ext ?_ ?_
          · dsimp only [ϖ]; fin_cases c₀ <;> fin_cases a <;> fin_cases b <;> decide
          · dsimp only [φ]; change z (a, b) + lam a b (c₀ + a + b) * x + mu a b (c₀ + a + b) * 0 =
              lam a b (c₀ + a + b) * x + z (a, b); ring
        rw [hperm, sign_blockPerm_eq hq_odd]
        have hϖ : (((if ϖ = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) =
            if c₀ + b = 0 then 1 else -1 := by
          dsimp only [ϖ]; fin_cases c₀ <;> fin_cases b <;> decide
        dsimp only [φ]
        rw [Units.val_mul, Units.val_mul, hϖ, sign_affine_zmod hodd, sign_affine_zmod hodd]
      push_cast
      rw [hrow_s 0, hrow_s 1, hcol_s 0, hcol_s 1]
      simp_rw [Fin.prod_univ_two, legendreSym_val_mul]
      fin_cases c₀ <;> simp <;> ring
    -- Sum over `z : Fin 2 × Fin 2 → ZMod q` (`q^4` choices)
    have hbij :
        (∑ L ∈ (Finset.univ.filter (fun L : LatinSquare (2 * q) =>
              L ∈ fixSet (H.map (sylowP q).subtype))).filter
            (fun L => ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 = c₀),
          (squareSign L : ℤ)) =
        ∑ z : Fin 2 × Fin 2 → ZMod q, (squareSign (build z) : ℤ) := by
      symm
      refine Finset.sum_bij (fun z _ => build z) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro z _
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbuild_fix z⟩, ?_⟩
        simp [build]
      · intro z₁ _ z₂ _ hEq
        funext ⟨a, b⟩
        have h := congrArg (fun M => M.entry (blockEquiv q (a, 0)) (blockEquiv q (b, 0))) hEq
        dsimp only [build] at h
        simp only [Equiv.symm_apply_apply, mul_zero, add_zero] at h
        exact congrArg Prod.snd ((blockEquiv q).injective h)
      · intro L hL
        have hLfix := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
        have hLc0 := (Finset.mem_filter.mp hL).2
        let z : Fin 2 × Fin 2 → ZMod q := fun p =>
          ((blockEquiv q).symm (L.entry (blockEquiv q (p.1, 0)) (blockEquiv q (p.2, 0)))).2
        refine ⟨z, Finset.mem_univ _, ?_⟩
        apply LatinSquare.ext
        funext r c
        obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
        obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective c
        have hblk := hchecker L hLfix a b
        rw [hLc0] at hblk
        have hf := (hblock_form L hLfix a b).1 x y
        rw [hblk] at hf
        rw [hf]
        simp [build, z]
    rw [hbij]
    simp_rw [hbuild_sign]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      ZMod.card, nsmul_eq_mul]
    norm_num
  · -- Some slope is `0`: both sides vanish!
    push Not at hnz
    rcases hnz with ⟨a, b, hzero⟩
    have hrhs :
        ∏ a' : Fin 2, ∏ b' : Fin 2,
          legendreSym q ((lam a' b' (c₀ + a' + b') * mu a' b' (c₀ + a' + b')).val : ℤ) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      have hmul0 : lam a b (c₀ + a + b) * mu a b (c₀ + a + b) = 0 := by
        by_cases h1 : lam a b (c₀ + a + b) = 0
        · rw [h1, zero_mul]
        · rw [hzero h1, mul_zero]
      rw [hmul0]
      simp [legendreSym.at_zero]
    rw [hrhs, mul_zero]
    refine Finset.sum_eq_zero fun L hL => ?_
    exfalso
    have hLfix := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
    have hLc0 := (Finset.mem_filter.mp hL).2
    have hblk := hchecker L hLfix a b
    rw [hLc0] at hblk
    have ⟨_, hlam, hmu⟩ := hblock_form L hLfix a b
    rw [hblk] at hlam hmu
    exact hmu (hzero hlam)

/-! ### Explicit Rank-2 Subgroups and Normalized Family Sums -/

/-- Rank-2 subgroup `graphR11Sub r s ξ η` generated by `(1, r; 0, 0; ξ₀, ξ₁)` and
`(0, 0; 1, s; η₀, η₁)`. -/
def graphR11Sub {q : ℕ} [NeZero q] (r s : (ZMod q)ˣ) (ξ η : Fin 2 → ZMod q) :
    Subgroup (sylowP q) :=
  Subgroup.closure {sylowElem q 1 r.1 0 0 (ξ 0) (ξ 1), sylowElem q 0 0 1 s.1 (η 0) (η 1)}

/-- Rank-2 subgroup `graphRowSub k ξ η` generated by `(1, 0; k₀₀, k₁₀; ξ₀, ξ₁)` and
`(0, 1; k₀₁, k₁₁; η₀, η₁)`. -/
def graphRowSub {q : ℕ} [NeZero q] (k : Fin 2 → Fin 2 → ZMod q) (ξ η : Fin 2 → ZMod q) :
    Subgroup (sylowP q) :=
  Subgroup.closure
    {sylowElem q 1 0 (k 0 0) (k 1 0) (ξ 0) (ξ 1),
     sylowElem q 0 1 (k 0 1) (k 1 1) (η 0) (η 1)}

/-- Membership characterization for `graphR11Sub`. -/
lemma mem_graphR11Sub_iff {q : ℕ} [NeZero q] (r s : (ZMod q)ˣ) (ξ η : Fin 2 → ZMod q)
    (g : sylowP q) :
    g ∈ graphR11Sub r s ξ η ↔
      ∃ x y : ZMod q,
        sylowToVec g =
          (fun a => if a = 0 then x else r.1 * x,
           fun b => if b = 0 then y else s.1 * y,
           fun c => ξ c * x + η c * y) := by
  let S : Subgroup (sylowP q) :=
    { carrier := { g | ∃ x y : ZMod q, sylowToVec g =
        (fun a => if a = 0 then x else r.1 * x,
         fun b => if b = 0 then y else s.1 * y,
         fun c => ξ c * x + η c * y) }
      one_mem' := ⟨0, 0, by rw [sylowToVec_one]; ext a <;> fin_cases a <;> simp⟩
      mul_mem' := by
        rintro a b ⟨x₁, y₁, h₁⟩ ⟨x₂, y₂, h₂⟩
        refine ⟨x₁ + x₂, y₁ + y₂, ?_⟩
        rw [sylowToVec_mul, h₁, h₂]
        ext i <;> fin_cases i <;> simp <;> ring
      inv_mem' := by
        rintro a ⟨x, y, h⟩
        refine ⟨-x, -y, ?_⟩
        rw [sylowToVec_inv, h]
        ext i <;> fin_cases i <;> simp <;> ring }
  have hEq : graphR11Sub r s ξ η = S := by
    apply le_antisymm
    · rw [graphR11Sub, Subgroup.closure_le]
      rintro g (rfl | rfl)
      · refine ⟨1, 0, ?_⟩
        rw [sylowToVec_sylowElem]
        ext i <;> fin_cases i <;> simp
      · refine ⟨0, 1, ?_⟩
        rw [sylowToVec_sylowElem]
        ext i <;> fin_cases i <;> simp
    · rintro g ⟨x, y, hg⟩
      let g₁ := sylowElem q 1 r.1 0 0 (ξ 0) (ξ 1)
      let g₂ := sylowElem q 0 0 1 s.1 (η 0) (η 1)
      have hpow_vec : ∀ (h : sylowP q) (n : ℕ),
          sylowToVec (h ^ n) = (n : ZMod q) • sylowToVec h := by
        intro h n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, sylowToVec_mul, ih]
          ext i <;> simp [add_smul, one_smul]
      have hg_eq : g = g₁ ^ x.val * g₂ ^ y.val := by
        apply sylowToVec_injective
        rw [hg, sylowToVec_mul, hpow_vec, hpow_vec, sylowToVec_sylowElem, sylowToVec_sylowElem,
          ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        ext i <;> fin_cases i <;> simp [mul_comm]
      rw [hg_eq]
      exact (graphR11Sub r s ξ η).mul_mem
        ((graphR11Sub r s ξ η).pow_mem (Subgroup.subset_closure (Or.inl rfl)) _)
        ((graphR11Sub r s ξ η).pow_mem (Subgroup.subset_closure (Or.inr rfl)) _)
  rw [hEq]; rfl

/-- Membership characterization for `graphRowSub`. -/
lemma mem_graphRowSub_iff {q : ℕ} [NeZero q] (k : Fin 2 → Fin 2 → ZMod q)
    (ξ η : Fin 2 → ZMod q) (g : sylowP q) :
    g ∈ graphRowSub k ξ η ↔
      ∃ x y : ZMod q,
        sylowToVec g =
          (fun a => if a = 0 then x else y,
           fun b => k b 0 * x + k b 1 * y,
           fun c => ξ c * x + η c * y) := by
  let S : Subgroup (sylowP q) :=
    { carrier := { g | ∃ x y : ZMod q, sylowToVec g =
        (fun a => if a = 0 then x else y,
         fun b => k b 0 * x + k b 1 * y,
         fun c => ξ c * x + η c * y) }
      one_mem' := ⟨0, 0, by rw [sylowToVec_one]; ext a <;> fin_cases a <;> simp⟩
      mul_mem' := by
        rintro a b ⟨x₁, y₁, h₁⟩ ⟨x₂, y₂, h₂⟩
        refine ⟨x₁ + x₂, y₁ + y₂, ?_⟩
        rw [sylowToVec_mul, h₁, h₂]
        ext i <;> fin_cases i <;> simp <;> ring
      inv_mem' := by
        rintro a ⟨x, y, h⟩
        refine ⟨-x, -y, ?_⟩
        rw [sylowToVec_inv, h]
        ext i <;> fin_cases i <;> simp <;> ring }
  have hEq : graphRowSub k ξ η = S := by
    apply le_antisymm
    · rw [graphRowSub, Subgroup.closure_le]
      rintro g (rfl | rfl)
      · refine ⟨1, 0, ?_⟩
        rw [sylowToVec_sylowElem]
        ext i <;> fin_cases i <;> simp
      · refine ⟨0, 1, ?_⟩
        rw [sylowToVec_sylowElem]
        ext i <;> fin_cases i <;> simp
    · rintro g ⟨x, y, hg⟩
      let g₁ := sylowElem q 1 0 (k 0 0) (k 1 0) (ξ 0) (ξ 1)
      let g₂ := sylowElem q 0 1 (k 0 1) (k 1 1) (η 0) (η 1)
      have hpow_vec : ∀ (h : sylowP q) (n : ℕ),
          sylowToVec (h ^ n) = (n : ZMod q) • sylowToVec h := by
        intro h n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, sylowToVec_mul, ih]
          ext i <;> simp [add_smul, one_smul]
      have hg_eq : g = g₁ ^ x.val * g₂ ^ y.val := by
        apply sylowToVec_injective
        rw [hg, sylowToVec_mul, hpow_vec, hpow_vec, sylowToVec_sylowElem, sylowToVec_sylowElem,
          ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        ext i <;> fin_cases i <;> simp [mul_comm]
      rw [hg_eq]
      exact (graphRowSub k ξ η).mul_mem
        ((graphRowSub k ξ η).pow_mem (Subgroup.subset_closure (Or.inl rfl)) _)
        ((graphRowSub k ξ η).pow_mem (Subgroup.subset_closure (Or.inr rfl)) _)
  rw [hEq]; rfl

lemma elemRank_graphR11Sub {q : ℕ} [NeZero q] (hq : q.Prime) (r s : (ZMod q)ˣ)
    (ξ η : Fin 2 → ZMod q) : elemRank q (graphR11Sub r s ξ η) = 2 := by
  unfold elemRank
  have hcard : Nat.card (graphR11Sub r s ξ η) = q ^ 2 := by
    have heq : Nat.card (graphR11Sub r s ξ η) = Nat.card (ZMod q × ZMod q) := by
      refine Nat.card_congr
        { toFun := fun g => ((sylowToVec g.1).1 0, (sylowToVec g.1).2.1 0)
          invFun := fun p => ⟨vecToSylow (fun a => if a = 0 then p.1 else r.1 * p.1,
            fun b => if b = 0 then p.2 else s.1 * p.2,
            fun c => ξ c * p.1 + η c * p.2),
            (mem_graphR11Sub_iff r s ξ η _).mpr ⟨p.1, p.2, sylowToVec_vecToSylow _⟩⟩
          left_inv := fun g => by
            rcases (mem_graphR11Sub_iff r s ξ η g.1).mp g.2 with ⟨x, y, hxy⟩
            apply Subtype.ext; apply sylowToVec_injective
            rw [sylowToVec_vecToSylow]
            have h1 : (sylowToVec g.1).1 0 = x := by rw [hxy]; rfl
            have h2 : (sylowToVec g.1).2.1 0 = y := by rw [hxy]; rfl
            change (fun a => if a = 0 then (sylowToVec g.1).1 0 else r.1 * (sylowToVec g.1).1 0,
              fun b => if b = 0 then (sylowToVec g.1).2.1 0 else s.1 * (sylowToVec g.1).2.1 0,
              fun c => ξ c * (sylowToVec g.1).1 0 + η c * (sylowToVec g.1).2.1 0) = _
            rw [h1, h2, hxy]
          right_inv := fun ⟨x, y⟩ => by simp }
    rw [heq, Nat.card_eq_fintype_card]; simp [ZMod.card, sq]
  rw [hcard, Nat.log_pow hq.one_lt]

lemma elemRank_graphRowSub {q : ℕ} [NeZero q] (hq : q.Prime)
    (k : Fin 2 → Fin 2 → ZMod q) (ξ η : Fin 2 → ZMod q) :
    elemRank q (graphRowSub k ξ η) = 2 := by
  unfold elemRank
  have hcard : Nat.card (graphRowSub k ξ η) = q ^ 2 := by
    have heq : Nat.card (graphRowSub k ξ η) = Nat.card (ZMod q × ZMod q) := by
      refine Nat.card_congr
        { toFun := fun g => ((sylowToVec g.1).1 0, (sylowToVec g.1).1 1)
          invFun := fun p => ⟨vecToSylow (fun a => if a = 0 then p.1 else p.2,
            fun b => k b 0 * p.1 + k b 1 * p.2,
            fun c => ξ c * p.1 + η c * p.2),
            (mem_graphRowSub_iff k ξ η _).mpr ⟨p.1, p.2, sylowToVec_vecToSylow _⟩⟩
          left_inv := fun g => by
            rcases (mem_graphRowSub_iff k ξ η g.1).mp g.2 with ⟨x, y, hxy⟩
            apply Subtype.ext; apply sylowToVec_injective
            rw [sylowToVec_vecToSylow]
            have h1 : (sylowToVec g.1).1 0 = x := by rw [hxy]; rfl
            have h2 : (sylowToVec g.1).1 1 = y := by rw [hxy]; rfl
            change (fun a => if a = 0 then (sylowToVec g.1).1 0 else (sylowToVec g.1).1 1,
              fun b => k b 0 * (sylowToVec g.1).1 0 + k b 1 * (sylowToVec g.1).1 1,
              fun c => ξ c * (sylowToVec g.1).1 0 + η c * (sylowToVec g.1).1 1) = _
            rw [h1, h2, hxy]
          right_inv := fun ⟨x, y⟩ => by simp }
    rw [heq, Nat.card_eq_fintype_card]; simp [ZMod.card, sq]
  rw [hcard, Nat.log_pow hq.one_lt]

/-! ### Character-Sum Helpers for the Five Normalized Cases -/

/-- Sum of `χ(ξ * η)` over `ξ, η` with `ξ ≠ η` equals `-(q - 1)`. -/
lemma sum_chi_mul_ne {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ p : ZMod q × ZMod q,
      (if p.1 ≠ p.2 then legendreSym q ((p.1 * p.2).val : ℤ) else 0) = -((q : ℤ) - 1) := by
  have hsplit :
      (∑ p : ZMod q × ZMod q, legendreSym q ((p.1 * p.2).val : ℤ)) =
      (∑ p : ZMod q × ZMod q, if p.1 ≠ p.2 then legendreSym q ((p.1 * p.2).val : ℤ) else 0) +
      (∑ p : ZMod q × ZMod q, if p.1 = p.2 then legendreSym q ((p.1 * p.2).val : ℤ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1 = p.2 <;> simp [h]
  have htot : (∑ p : ZMod q × ZMod q, legendreSym q ((p.1 * p.2).val : ℤ)) = 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [legendreSym_val_mul, ← Finset.mul_sum, sum_legendreSym_eq_zero hodd, mul_zero,
      Finset.sum_const_zero]
  have hdiag :
      (∑ p : ZMod q × ZMod q, if p.1 = p.2 then legendreSym q ((p.1 * p.2).val : ℤ) else 0) =
      (q : ℤ) - 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
    have h0 : legendreSym q (((0 : ZMod q) * 0).val : ℤ) = 0 := by simp [legendreSym.at_zero]
    rw [h0, zero_add]
    have h1 : ∀ x ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        legendreSym q ((x * x).val : ℤ) = 1 := by
      intro x hx
      rw [legendreSym_val_mul, ← sq]
      exact legendreSym.sq_one q (by simpa using (Finset.mem_erase.mp hx).1)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    have hq1 : 1 ≤ q := (Fact.out : q.Prime).pos
    omega
  linarith

/-- Sum of `χ(ξ * (ξ - η))` over `ξ, η` with `η ≠ 0` equals `-(q - 1)`. -/
lemma sum_chi_xi_sub_eta {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ p : ZMod q × ZMod q,
      (if p.2 ≠ 0 then legendreSym q ((p.1 * (p.1 - p.2)).val : ℤ) else 0) = -((q : ℤ) - 1) := by
  have hbij :
      (∑ p : ZMod q × ZMod q,
        if p.2 ≠ 0 then legendreSym q ((p.1 * (p.1 - p.2)).val : ℤ) else 0) =
      (∑ p : ZMod q × ZMod q,
        if p.1 ≠ p.2 then legendreSym q ((p.1 * p.2).val : ℤ) else 0) := by
    refine Finset.sum_bij (fun p _ => (p.1, p.1 - p.2)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro p₁ _ p₂ _ hEq
      have h1 : p₁.1 = p₂.1 := (Prod.ext_iff.mp hEq).1
      have h2 : p₁.1 - p₁.2 = p₂.1 - p₂.2 := (Prod.ext_iff.mp hEq).2
      exact Prod.ext h1 (by linear_combination h1 - h2)
    · intro p _
      exact ⟨(p.1, p.1 - p.2), Finset.mem_univ _, Prod.ext rfl (by ring)⟩
    · intro p _
      have hiff : p.2 ≠ 0 ↔ p.1 ≠ p.1 - p.2 := by
        constructor <;> intro h h' <;> apply h <;> linear_combination h'
      simp [hiff]
  rw [hbij]
  exact sum_chi_mul_ne hodd

/-- Second moment of `ϱ(ν) = ∑_t χ(t(t-1)(t-ν))` over `ν ∉ {0, 1}` equals `q^2 - 2q - 3`. -/
lemma sum_rho_sq_ne_zero_one {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    let rho (ν : ZMod q) : ℤ :=
      ∑ t : ZMod q, legendreSym q ((t * (t - 1) * (t - ν)).val : ℤ)
    ∑ ν ∈ (Finset.univ : Finset (ZMod q)).filter (fun ν => ν ≠ 0 ∧ ν ≠ 1), (rho ν) ^ 2 =
      (q : ℤ) ^ 2 - 2 * (q : ℤ) - 3 := by
  intro rho
  have hq : q.Prime := Fact.out
  let chi (x : ZMod q) : ℤ := legendreSym q (x.val : ℤ)
  have hchi_mul : ∀ a b, chi (a * b) = chi a * chi b := fun a b => legendreSym_val_mul a b
  -- Full second moment `∑_ν rho(ν)^2 = q(q-2) - 1`
  have hfull : (∑ ν : ZMod q, (rho ν) ^ 2) = (q : ℤ) * ((q : ℤ) - 2) - 1 := by
    have hexp : ∀ ν : ZMod q, (rho ν) ^ 2 =
        ∑ t : ZMod q, ∑ s : ZMod q,
          chi (t * (t - 1)) * chi (s * (s - 1)) * chi ((t - ν) * (s - ν)) := by
      intro ν
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      dsimp only [chi]
      rw [legendreSym_val_mul (t * (t - 1)), legendreSym_val_mul (s * (s - 1)),
        legendreSym_val_mul (t - ν)]
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hinner : ∀ t : ZMod q,
        (∑ ν : ZMod q, ∑ s : ZMod q,
          chi (t * (t - 1)) * chi (s * (s - 1)) * chi ((t - ν) * (s - ν))) =
        ∑ s : ZMod q,
          chi (t * (t - 1)) * chi (s * (s - 1)) *
            (if t = s then ((q : ℤ) - 1) else -1) := by
      intro t
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      by_cases hts : t = s
      · subst hts
        rw [if_pos rfl]
        have hbij : (∑ ν : ZMod q, chi ((t - ν) * (t - ν))) = ∑ x : ZMod q, chi (x * x) := by
          refine Finset.sum_bij (fun ν _ => t - ν) (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => by linear_combination -h)
            (fun x _ => ⟨t - x, Finset.mem_univ _, by ring⟩) (fun _ _ => rfl)
        rw [hbij, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
        have h0 : chi (0 * 0) = 0 := by simp [chi, legendreSym.at_zero]
        rw [h0, zero_add]
        have h1 : ∀ x ∈ (Finset.univ : Finset (ZMod q)).erase 0, chi (x * x) = 1 := by
          intro x hx; rw [hchi_mul, ← sq]
          exact legendreSym.sq_one q (by simpa using (Finset.mem_erase.mp hx).1)
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
        have := hq.pos; omega
      · rw [if_neg hts]
        have hbij : (∑ ν : ZMod q, chi ((t - ν) * (s - ν))) =
            ∑ x : ZMod q, chi (x * (x + (s - t))) := by
          refine Finset.sum_bij (fun ν _ => t - ν) (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => by linear_combination -h)
            (fun x _ => ⟨t - x, Finset.mem_univ _, by ring⟩)
            (fun ν _ => by congr 2; ring)
        rw [hbij]
        exact jacobsthal_sum hodd (sub_ne_zero.mpr (Ne.symm hts))
    simp_rw [hinner]
    have hsplit : ∀ t s : ZMod q,
        chi (t * (t - 1)) * chi (s * (s - 1)) * (if t = s then ((q : ℤ) - 1) else -1) =
        (if t = s then (q : ℤ) * (chi (t * (t - 1))) ^ 2 else 0) -
          chi (t * (t - 1)) * chi (s * (s - 1)) := by
      intro t s; split_ifs with h
      · subst h; ring
      · ring
    simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hsum_chi : (∑ t : ZMod q, chi (t * (t - 1))) = -1 := by
      have h := jacobsthal_sum (q := q) hodd (c := -1) (by simp)
      convert h using 2 with t; rw [sub_eq_add_neg]
    have hsum_sq : (∑ t : ZMod q, (chi (t * (t - 1))) ^ 2) = (q : ℤ) - 2 := by
      have h01 : (0 : ZMod q) ≠ 1 := zero_ne_one
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : ZMod q)⟩)]
      have h0 : chi (0 * (0 - 1)) = 0 := by simp [chi, legendreSym.at_zero]
      have h1 : chi (1 * (1 - 1)) = 0 := by
        have : ((1 : ZMod q) * (1 - 1)).val = 0 := by simp
        simp [chi, this, legendreSym.at_zero]
      rw [h0, h1, zero_pow two_ne_zero, zero_add, zero_add]
      have hon : ∀ t ∈ ((Finset.univ : Finset (ZMod q)).erase 0).erase 1,
          (chi (t * (t - 1))) ^ 2 = 1 := by
        intro t ht
        have ht1 : t ≠ 1 := (Finset.mem_erase.mp ht).1
        have ht0 : t ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        exact legendreSym.sq_one q (by simpa using mul_ne_zero ht0 (sub_ne_zero.mpr ht1))
      rw [Finset.sum_congr rfl hon, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ 1⟩),
        Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card,
        nsmul_eq_mul, mul_one]
      have := hq.two_le; omega
    rw [hsum_sq, hsum_chi]
    ring
  -- Compute `rho 0 ^ 2 = 1` and `rho 1 ^ 2 = 1`
  have hrho0 : (rho 0) ^ 2 = 1 := by
    have heq : rho 0 = -chi (-1) := by
      dsimp only [rho]
      have hterm : ∀ t : ZMod q,
          legendreSym q ((t * (t - 1) * (t - 0)).val : ℤ) =
            if t = 0 then 0 else chi (t - 1) := by
        intro t
        split_ifs with ht
        · subst ht; simp [legendreSym.at_zero]
        · have : t * (t - 1) * (t - 0) = (t * t) * (t - 1) := by ring
          rw [this, legendreSym_val_mul, legendreSym_val_mul]
          have hsq : legendreSym q (t.val : ℤ) * legendreSym q (t.val : ℤ) = 1 := by
            rw [← sq]; exact legendreSym.sq_one q (by simpa using ht)
          rw [hsq, one_mul]
      simp_rw [hterm]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), if_pos rfl, zero_add]
      have htot : (∑ t : ZMod q, chi (t - 1)) = 0 := by
        have h := sum_legendreSym_eq_zero (q := q) hodd
        rw [← Equiv.sum_comp (Equiv.addRight (-1 : ZMod q))] at h
        convert h using 2 with t; change _ = chi (t + -1); rw [sub_eq_add_neg]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))] at htot
      have her :
          ∑ t ∈ (Finset.univ : Finset (ZMod q)).erase 0, (if t = 0 then (0 : ℤ) else chi (t - 1)) =
          ∑ t ∈ (Finset.univ : Finset (ZMod q)).erase 0, chi (t - 1) :=
        Finset.sum_congr rfl fun t ht => if_neg (Finset.mem_erase.mp ht).1
      rw [her]
      have h0m1 : (0 : ZMod q) - 1 = -1 := zero_sub 1
      rw [h0m1] at htot
      linarith
    rw [heq, neg_sq]
    exact legendreSym.sq_one q (by simp)
  have hrho1 : (rho 1) ^ 2 = 1 := by
    have heq : rho 1 = -1 := by
      dsimp only [rho]
      have hterm : ∀ t : ZMod q,
          legendreSym q ((t * (t - 1) * (t - 1)).val : ℤ) =
            if t = 1 then 0 else chi t := by
        intro t
        split_ifs with ht
        · subst ht
          have : ((1 : ZMod q) * (1 - 1) * (1 - 1)).val = 0 := by simp
          rw [this, Nat.cast_zero, legendreSym.at_zero]
        · have : t * (t - 1) * (t - 1) = ((t - 1) * (t - 1)) * t := by ring
          rw [this, legendreSym_val_mul, legendreSym_val_mul]
          have hsq : legendreSym q ((t - 1).val : ℤ) * legendreSym q ((t - 1).val : ℤ) = 1 := by
            rw [← sq]; exact legendreSym.sq_one q (by simpa using sub_ne_zero.mpr ht)
          rw [hsq, one_mul]
      simp_rw [hterm]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ZMod q)), if_pos rfl, zero_add]
      have htot := sum_legendreSym_eq_zero (q := q) hodd
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ZMod q))] at htot
      have her :
          ∑ t ∈ (Finset.univ : Finset (ZMod q)).erase 1, (if t = 1 then (0 : ℤ) else chi t) =
          ∑ t ∈ (Finset.univ : Finset (ZMod q)).erase 1, chi t :=
        Finset.sum_congr rfl fun t ht => if_neg (Finset.mem_erase.mp ht).1
      rw [her]
      have h1 : legendreSym q ((1 : ZMod q).val : ℤ) = 1 := by
        rw [ZMod.val_one, Nat.cast_one, legendreSym.at_one]
      linarith
    rw [heq]; norm_num
  have hfilt :
      (Finset.univ : Finset (ZMod q)).filter (fun ν => ν ≠ 0 ∧ ν ≠ 1) =
      ((Finset.univ : Finset (ZMod q)).erase 0).erase 1 := by
    ext ν; simp [and_comm]
  rw [hfilt]
  have h01 : (0 : ZMod q) ≠ 1 := zero_ne_one
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : ZMod q)⟩)] at hfull
  linarith [hfull, hrho0, hrho1]

/-! ### Normalized Representative Sums for `R_11`, `R_21`, `R_mon`, `R_one`, `R_full` -/

/-- Normalized `R_11` sum (for `r = s = 1`): `∑_{ξ, η} S(H) = 2 * q^4 * (q - 1)^4`. -/
lemma sum_R11_norm {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q,
      S_twoq q (graphR11Sub (1 : (ZMod q)ˣ) (1 : (ZMod q)ˣ) ξ η) =
    2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 4 := by
  have hq : q.Prime := Fact.out
  have hterm : ∀ ξ η : Fin 2 → ZMod q,
      S_twoq q (graphR11Sub (1 : (ZMod q)ˣ) (1 : (ZMod q)ˣ) ξ η) =
      if ξ 0 ≠ 0 ∧ ξ 1 ≠ 0 ∧ η 0 ≠ 0 ∧ η 1 ≠ 0 then 2 * (q : ℤ) ^ 4 else 0 := by
    intro ξ η
    let H := graphR11Sub (1 : (ZMod q)ˣ) (1 : (ZMod q)ˣ) ξ η
    have haff := S_twoq_four_affine hodd H (fun _ _ c => ξ c) (fun _ _ c => η c)
      (fun a b x y => ⟨vecToSylow (fun _ => x, fun _ => y, fun c => ξ c * x + η c * y),
        (mem_graphR11Sub_iff 1 1 ξ η _).mpr ⟨x, y, by
          rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp⟩,
        by simp, by simp⟩)
      (fun a b c g hg => by
        rcases (mem_graphR11Sub_iff 1 1 ξ η g).mp hg with ⟨x, y, hxy⟩
        rw [hxy]; fin_cases a <;> fin_cases b <;> simp)
    rw [haff]
    simp_rw [Fin.sum_univ_two, Fin.prod_univ_two, legendreSym_val_mul]
    by_cases hnz : ξ 0 ≠ 0 ∧ ξ 1 ≠ 0 ∧ η 0 ≠ 0 ∧ η 1 ≠ 0
    · rw [if_pos hnz]
      have hsq : ∀ z : ZMod q, z ≠ 0 → legendreSym q (z.val : ℤ) * legendreSym q (z.val : ℤ) = 1 :=
        fun z hz => by rw [← sq]; exact legendreSym.sq_one q (by simpa using hz)
      have h0 : legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ) *
          (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ)) *
          (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ) *
            (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ))) = 1 := by
        calc _ = (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((ξ 0).val : ℤ)) *
            (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((ξ 1).val : ℤ)) *
            (legendreSym q ((η 0).val : ℤ) * legendreSym q ((η 0).val : ℤ)) *
            (legendreSym q ((η 1).val : ℤ) * legendreSym q ((η 1).val : ℤ)) := by ring
          _ = 1 := by
            rw [hsq _ hnz.1, hsq _ hnz.2.1, hsq _ hnz.2.2.1, hsq _ hnz.2.2.2]; ring
      change (q : ℤ) ^ 4 * (
        legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ) *
          (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ)) *
          (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ) *
            (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ))) +
        legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ) *
          (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ)) *
          (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ) *
            (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ)))) = _
      have h1 : legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ) *
          (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ)) *
          (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ) *
            (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ))) = 1 := by
        linarith [h0]
      rw [h0, h1]; ring
    · rw [if_neg hnz]
      push Not at hnz
      change (q : ℤ) ^ 4 * (
        legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ) *
          (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ)) *
          (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ) *
            (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ))) +
        legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ) *
          (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ)) *
          (legendreSym q ((ξ 0).val : ℤ) * legendreSym q ((η 0).val : ℤ) *
            (legendreSym q ((ξ 1).val : ℤ) * legendreSym q ((η 1).val : ℤ)))) = 0
      have hz : legendreSym q ((ξ 0).val : ℤ) = 0 ∨ legendreSym q ((ξ 1).val : ℤ) = 0 ∨
          legendreSym q ((η 0).val : ℤ) = 0 ∨ legendreSym q ((η 1).val : ℤ) = 0 := by
        by_cases h1 : ξ 0 = 0
        · left; simp [h1, legendreSym.at_zero]
        · by_cases h2 : ξ 1 = 0
          · right; left; simp [h2, legendreSym.at_zero]
          · by_cases h3 : η 0 = 0
            · right; right; left; simp [h3, legendreSym.at_zero]
            · right; right; right; simp [hnz h1 h2 h3, legendreSym.at_zero]
      rcases hz with h | h | h | h <;> (rw [h]; ring)
  simp_rw [hterm]
  -- Count `{(ξ, η) | ξ 0, ξ 1, η 0, η 1 ≠ 0}` = `(q - 1)^4`
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((Finset.univ : Finset ((Fin 2 → ZMod q) × (Fin 2 → ZMod q))).filter
        (fun p => p.1 0 ≠ 0 ∧ p.1 1 ≠ 0 ∧ p.2 0 ≠ 0 ∧ p.2 1 ≠ 0)).card = (q - 1) ^ 4 := by
    let S := (Finset.univ : Finset (ZMod q)).erase 0
    have hS : S.card = q - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hbij :
        ((Finset.univ : Finset ((Fin 2 → ZMod q) × (Fin 2 → ZMod q))).filter
          (fun p => p.1 0 ≠ 0 ∧ p.1 1 ≠ 0 ∧ p.2 0 ≠ 0 ∧ p.2 1 ≠ 0)).card =
        (S ×ˢ (S ×ˢ (S ×ˢ S))).card := by
      refine Finset.card_bij (fun p _ => (p.1 0, p.1 1, p.2 0, p.2 1)) ?_ ?_ ?_
      · intro p hp
        have h := (Finset.mem_filter.mp hp).2
        simp [S, h]
      · intro p₁ _ p₂ _ hEq
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · fin_cases i
          · exact congrArg Prod.fst hEq
          · exact congrArg (fun x => x.2.1) hEq
        · fin_cases i
          · exact congrArg (fun x => x.2.2.1) hEq
          · exact congrArg (fun x => x.2.2.2) hEq
      · intro t ht
        simp only [Finset.mem_product, S, Finset.mem_erase, Finset.mem_univ, and_true] at ht
        refine ⟨(fun i => if i = 0 then t.1 else t.2.1,
                 fun i => if i = 0 then t.2.2.1 else t.2.2.2),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [ht]⟩, by simp⟩
    rw [hbij, Finset.card_product, Finset.card_product, Finset.card_product, hS]
    ring
  rw [hcard]
  have hq1 : 1 ≤ q := hq.pos
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  push_cast
  rw [hcast]
  ring

/-- Normalized `R_21` sum (for `k = [[1, 1], [1, 1]]`): `∑_{ξ, η} S(H) = 2 * q^4 * (q - 1)^2`. -/
lemma sum_R21_norm {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q,
      S_twoq q (graphRowSub (fun _ _ => (1 : ZMod q)) ξ η) =
    2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 := by
  have hterm : ∀ ξ η : Fin 2 → ZMod q,
      S_twoq q (graphRowSub (fun _ _ => (1 : ZMod q)) ξ η) =
      2 * (q : ℤ) ^ 4 *
        (if ξ 0 ≠ η 0 then legendreSym q ((ξ 0 * η 0).val : ℤ) else 0) *
        (if ξ 1 ≠ η 1 then legendreSym q ((ξ 1 * η 1).val : ℤ) else 0) := by
    intro ξ η
    let H := graphRowSub (fun _ _ => (1 : ZMod q)) ξ η
    let lam (a _ c : Fin 2) : ZMod q := if a = 0 then ξ c - η c else η c - ξ c
    let mu (a _ c : Fin 2) : ZMod q := if a = 0 then η c else ξ c
    have haff := S_twoq_four_affine hodd H lam mu
      (fun a b x y => by
        fin_cases a
        · refine ⟨vecToSylow (fun i => if i = 0 then x else y - x,
            fun _ => y, fun c => ξ c * x + η c * (y - x)),
            (mem_graphRowSub_iff _ ξ η _).mpr ⟨x, y - x, by
              rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp⟩,
            by simp, by simp⟩
        · refine ⟨vecToSylow (fun i => if i = 0 then y - x else x,
            fun _ => y, fun c => ξ c * (y - x) + η c * x),
            (mem_graphRowSub_iff _ ξ η _).mpr ⟨y - x, x, by
              rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp [add_comm]⟩,
            by simp, by simp⟩)
      (fun a b c g hg => by
        rcases (mem_graphRowSub_iff _ ξ η g).mp hg with ⟨x, y, hxy⟩
        rw [hxy]; dsimp only [lam, mu]; fin_cases a <;> simp <;> ring)
    rw [haff]
    simp_rw [Fin.sum_univ_two, Fin.prod_univ_two, lam, mu]
    -- Factor each symbol block `c`'s contribution
    have hsym : ∀ c : Fin 2,
        legendreSym q (((ξ c - η c) * η c).val : ℤ) *
          legendreSym q (((η c - ξ c) * ξ c).val : ℤ) =
        legendreSym q ((-1 : ZMod q).val : ℤ) *
          (if ξ c ≠ η c then legendreSym q ((ξ c * η c).val : ℤ) else 0) := by
      intro c
      split_ifs with hne
      · have hsub : ξ c - η c ≠ 0 := sub_ne_zero.mpr hne
        have heq : (ξ c - η c) * η c * ((η c - ξ c) * ξ c) =
            (-1 : ZMod q) * ((ξ c - η c) * (ξ c - η c)) * (ξ c * η c) := by ring
        rw [← legendreSym_val_mul, heq, legendreSym_val_mul, legendreSym_val_mul,
          legendreSym_val_mul (ξ c - η c)]
        have hsq : legendreSym q ((ξ c - η c).val : ℤ) * legendreSym q ((ξ c - η c).val : ℤ) = 1 := by
          rw [← sq]; exact legendreSym.sq_one q (by simpa using hsub)
        rw [hsq, mul_one]
      · push Not at hne
        rw [hne, sub_self, zero_mul]
        simp [legendreSym.at_zero]
    have hsq_m1 : legendreSym q ((-1 : ZMod q).val : ℤ) *
        legendreSym q ((-1 : ZMod q).val : ℤ) = 1 := by
      rw [← sq]; exact legendreSym.sq_one q (by simp)
    have hblk :
        legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
          legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
          (legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ) *
            legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ)) =
        (if ξ 0 ≠ η 0 then legendreSym q ((ξ 0 * η 0).val : ℤ) else 0) *
        (if ξ 1 ≠ η 1 then legendreSym q ((ξ 1 * η 1).val : ℤ) else 0) := by
      calc _ = (legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
              legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ)) *
            (legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
              legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ)) := by ring
        _ = (legendreSym q ((-1 : ZMod q).val : ℤ) * legendreSym q ((-1 : ZMod q).val : ℤ)) *
            ((if ξ 0 ≠ η 0 then legendreSym q ((ξ 0 * η 0).val : ℤ) else 0) *
             (if ξ 1 ≠ η 1 then legendreSym q ((ξ 1 * η 1).val : ℤ) else 0)) := by
            rw [hsym 0, hsym 1]; ring
        _ = _ := by rw [hsq_m1, one_mul]
    change (q : ℤ) ^ 4 * (
      legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
        legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
        (legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ) *
          legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ)) +
      legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
        legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
        (legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ) *
          legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ))) = _
    have hblk' :
        legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
          legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
          (legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ) *
            legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ)) =
        (if ξ 0 ≠ η 0 then legendreSym q ((ξ 0 * η 0).val : ℤ) else 0) *
        (if ξ 1 ≠ η 1 then legendreSym q ((ξ 1 * η 1).val : ℤ) else 0) := by
      linarith [hblk]
    rw [hblk, hblk']
    ring
  simp_rw [hterm]
  -- Factor the double sum over `(ξ 0, η 0)` and `(ξ 1, η 1)`
  let e : (Fin 2 → ZMod q) × (Fin 2 → ZMod q) ≃ (ZMod q × ZMod q) × (ZMod q × ZMod q) :=
    { toFun := fun p => ((p.1 0, p.2 0), (p.1 1, p.2 1))
      invFun := fun t => (fun i => if i = 0 then t.1.1 else t.2.1,
                          fun i => if i = 0 then t.1.2 else t.2.2)
      left_inv := fun p => Prod.ext (funext fun i => by fin_cases i <;> rfl)
        (funext fun i => by fin_cases i <;> rfl)
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  rw [← Fintype.sum_prod_type', ← Equiv.sum_comp e.symm]
  have hsim : ∀ t : (ZMod q × ZMod q) × (ZMod q × ZMod q),
      2 * (q : ℤ) ^ 4 *
        (if (e.symm t).1 0 ≠ (e.symm t).2 0 then legendreSym q (((e.symm t).1 0 * (e.symm t).2 0).val : ℤ) else 0) *
        (if (e.symm t).1 1 ≠ (e.symm t).2 1 then legendreSym q (((e.symm t).1 1 * (e.symm t).2 1).val : ℤ) else 0) =
      (2 * (q : ℤ) ^ 4 * (if t.1.1 ≠ t.1.2 then legendreSym q ((t.1.1 * t.1.2).val : ℤ) else 0)) *
        (if t.2.1 ≠ t.2.2 then legendreSym q ((t.2.1 * t.2.2).val : ℤ) else 0) :=
    fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  simp_rw [hsim]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_chi_mul_ne hodd, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_chi_mul_ne hodd]
  ring

/-- Normalized `R_full(ν)` sum (for `k = [[1, 1], [1, ν]]`, `ν ∉ {0, 1}`):
`∑_{ξ, η} S(H) = 2 * q^4 * (q - 1)^2 * ϱ(ν)^2`. -/
lemma sum_Rfull_norm {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) {ν : ZMod q}
    (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) :
    let k : Fin 2 → Fin 2 → ZMod q := fun b j =>
      if b = 0 then 1 else if j = 0 then 1 else ν
    let rho := ∑ t : ZMod q, legendreSym q ((t * (t - 1) * (t - ν)).val : ℤ)
    ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q, S_twoq q (graphRowSub k ξ η) =
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 * rho ^ 2 := by
  intro k rho
  have h1mν : 1 - ν ≠ 0 := sub_ne_zero.mpr (Ne.symm hν1)
  have hνm1 : ν - 1 ≠ 0 := sub_ne_zero.mpr hν1
  let κ (ξ η : ZMod q) : ℤ :=
    legendreSym q ((-(ξ * η * (ξ - η) * (ν * ξ - η))).val : ℤ)
  have hterm : ∀ ξ η : Fin 2 → ZMod q,
      S_twoq q (graphRowSub k ξ η) = 2 * (q : ℤ) ^ 4 * κ (ξ 0) (η 0) * κ (ξ 1) (η 1) := by
    intro ξ η
    let H := graphRowSub k ξ η
    let lam (a b c : Fin 2) : ZMod q :=
      if a = 0 then
        if b = 0 then ξ c - η c else (ν * ξ c - η c) * ν⁻¹
      else
        if b = 0 then η c - ξ c else η c - ν * ξ c
    let mu (a b c : Fin 2) : ZMod q :=
      if a = 0 then
        if b = 0 then η c else η c * ν⁻¹
      else
        ξ c
    have haff := S_twoq_four_affine hodd H lam mu
      (fun a b x y => by
        fin_cases a <;> fin_cases b
        · refine ⟨vecToSylow (fun i => if i = 0 then x else y - x,
            fun b => k b 0 * x + k b 1 * (y - x), fun c => ξ c * x + η c * (y - x)),
            (mem_graphRowSub_iff k ξ η _).mpr ⟨x, y - x, sylowToVec_vecToSylow _⟩,
            by simp, by simp [k]⟩
        · refine ⟨vecToSylow (fun i => if i = 0 then x else (y - x) * ν⁻¹,
            fun b => k b 0 * x + k b 1 * ((y - x) * ν⁻¹),
            fun c => ξ c * x + η c * ((y - x) * ν⁻¹)),
            (mem_graphRowSub_iff k ξ η _).mpr ⟨x, (y - x) * ν⁻¹, sylowToVec_vecToSylow _⟩,
            by simp, by simp [k]; field_simp [hν0]; ring⟩
        · refine ⟨vecToSylow (fun i => if i = 0 then y - x else x,
            fun b => k b 0 * (y - x) + k b 1 * x, fun c => ξ c * (y - x) + η c * x),
            (mem_graphRowSub_iff k ξ η _).mpr ⟨y - x, x, sylowToVec_vecToSylow _⟩,
            by simp, by simp [k]⟩
        · refine ⟨vecToSylow (fun i => if i = 0 then y - ν * x else x,
            fun b => k b 0 * (y - ν * x) + k b 1 * x, fun c => ξ c * (y - ν * x) + η c * x),
            (mem_graphRowSub_iff k ξ η _).mpr ⟨y - ν * x, x, sylowToVec_vecToSylow _⟩,
            by simp, by simp [k]⟩)
      (fun a b c g hg => by
        rcases (mem_graphRowSub_iff k ξ η g).mp hg with ⟨x, y, hxy⟩
        rw [hxy]; dsimp only [lam, mu, k]
        fin_cases a <;> fin_cases b <;> simp <;> field_simp [hν0] <;> ring)
    rw [haff]
    simp_rw [Fin.sum_univ_two, Fin.prod_univ_two, lam, mu]
    have hdiag : ∀ c : Fin 2,
        legendreSym q (((ξ c - η c) * η c).val : ℤ) *
          legendreSym q (((η c - ν * ξ c) * ξ c).val : ℤ) = κ (ξ c) (η c) := by
      intro c
      rw [← legendreSym_val_mul]
      dsimp only [κ]; congr 2; ring
    have hoff : ∀ c : Fin 2,
        legendreSym q (((ν * ξ c - η c) * ν⁻¹ * (η c * ν⁻¹)).val : ℤ) *
          legendreSym q (((η c - ξ c) * ξ c).val : ℤ) = κ (ξ c) (η c) := by
      intro c
      rw [← legendreSym_val_mul]
      have heq : (ν * ξ c - η c) * ν⁻¹ * (η c * ν⁻¹) * ((η c - ξ c) * ξ c) =
          (ν⁻¹ * ν⁻¹) * (-(ξ c * η c * (ξ c - η c) * (ν * ξ c - η c))) := by ring
      rw [heq, legendreSym_val_mul, legendreSym_val_mul ν⁻¹]
      have hsq : legendreSym q (ν⁻¹.val : ℤ) * legendreSym q (ν⁻¹.val : ℤ) = 1 := by
        rw [← sq]; exact legendreSym.sq_one q (by simpa using inv_ne_zero hν0)
      rw [hsq, one_mul]
    change (q : ℤ) ^ 4 * (
      legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
        legendreSym q (((ν * ξ 1 - η 1) * ν⁻¹ * (η 1 * ν⁻¹)).val : ℤ) *
        (legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ) *
          legendreSym q (((η 0 - ν * ξ 0) * ξ 0).val : ℤ)) +
      legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
        legendreSym q (((ν * ξ 0 - η 0) * ν⁻¹ * (η 0 * ν⁻¹)).val : ℤ) *
        (legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ) *
          legendreSym q (((η 1 - ν * ξ 1) * ξ 1).val : ℤ))) = _
    have h0 :
        legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
          legendreSym q (((ν * ξ 1 - η 1) * ν⁻¹ * (η 1 * ν⁻¹)).val : ℤ) *
          (legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ) *
            legendreSym q (((η 0 - ν * ξ 0) * ξ 0).val : ℤ)) =
        κ (ξ 0) (η 0) * κ (ξ 1) (η 1) := by
      calc _ = (legendreSym q (((ξ 0 - η 0) * η 0).val : ℤ) *
              legendreSym q (((η 0 - ν * ξ 0) * ξ 0).val : ℤ)) *
            (legendreSym q (((ν * ξ 1 - η 1) * ν⁻¹ * (η 1 * ν⁻¹)).val : ℤ) *
              legendreSym q (((η 1 - ξ 1) * ξ 1).val : ℤ)) := by ring
        _ = κ (ξ 0) (η 0) * κ (ξ 1) (η 1) := by rw [hdiag 0, hoff 1]
    have h1 :
        legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
          legendreSym q (((ν * ξ 0 - η 0) * ν⁻¹ * (η 0 * ν⁻¹)).val : ℤ) *
          (legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ) *
            legendreSym q (((η 1 - ν * ξ 1) * ξ 1).val : ℤ)) =
        κ (ξ 0) (η 0) * κ (ξ 1) (η 1) := by
      calc _ = (legendreSym q (((ν * ξ 0 - η 0) * ν⁻¹ * (η 0 * ν⁻¹)).val : ℤ) *
              legendreSym q (((η 0 - ξ 0) * ξ 0).val : ℤ)) *
            (legendreSym q (((ξ 1 - η 1) * η 1).val : ℤ) *
              legendreSym q (((η 1 - ν * ξ 1) * ξ 1).val : ℤ)) := by ring
        _ = κ (ξ 0) (η 0) * κ (ξ 1) (η 1) := by rw [hoff 0, hdiag 1]
    rw [h0, h1]
    ring
  -- Evaluate `∑_{ξ, η} κ(ξ, η) = χ(-1) * (q - 1) * rho`
  have hsum_k : (∑ p : ZMod q × ZMod q, κ p.1 p.2) =
      legendreSym q ((-1 : ZMod q).val : ℤ) * ((q : ℤ) - 1) * rho := by
    rw [Fintype.sum_prod_type]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
    have h0 : (∑ η : ZMod q, κ 0 η) = 0 := by
      refine Finset.sum_eq_zero fun η _ => ?_
      dsimp only [κ]; simp [legendreSym.at_zero]
    rw [h0, zero_add]
    have hxi : ∀ ξ ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        (∑ η : ZMod q, κ ξ η) = legendreSym q ((-1 : ZMod q).val : ℤ) * rho := by
      intro ξ hξ
      have hξ0 : ξ ≠ 0 := (Finset.mem_erase.mp hξ).1
      have hbij : (∑ η : ZMod q, κ ξ η) = ∑ t : ZMod q, κ ξ (t * ξ) := by
        refine Finset.sum_bij (fun η _ => η * ξ⁻¹) (fun _ _ => Finset.mem_univ _)
          (fun a _ b _ h => mul_right_cancel₀ (inv_ne_zero hξ0) h)
          (fun t _ => ⟨t * ξ, Finset.mem_univ _, by field_simp [hξ0]⟩)
          (fun η _ => by congr 1; field_simp [hξ0])
      rw [hbij]
      dsimp only [rho]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      dsimp only [κ]
      have heq : -(ξ * (t * ξ) * (ξ - t * ξ) * (ν * ξ - t * ξ)) =
          (-1 : ZMod q) * ((ξ * ξ) * (ξ * ξ)) * (t * (t - 1) * (t - ν)) := by ring
      rw [heq, legendreSym_val_mul, legendreSym_val_mul, legendreSym_val_mul,
        legendreSym_val_mul]
      have hsq : legendreSym q (ξ.val : ℤ) * legendreSym q (ξ.val : ℤ) = 1 := by
        rw [← sq]; exact legendreSym.sq_one q (by simpa using hξ0)
      rw [hsq, one_mul, mul_one]
    rw [Finset.sum_congr rfl hxi, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
      have := (Fact.out : q.Prime).pos; omega
    rw [hcast]; ring
  simp_rw [hterm]
  let e : (Fin 2 → ZMod q) × (Fin 2 → ZMod q) ≃ (ZMod q × ZMod q) × (ZMod q × ZMod q) :=
    { toFun := fun p => ((p.1 0, p.2 0), (p.1 1, p.2 1))
      invFun := fun t => (fun i => if i = 0 then t.1.1 else t.2.1,
                          fun i => if i = 0 then t.1.2 else t.2.2)
      left_inv := fun p => Prod.ext (funext fun i => by fin_cases i <;> rfl)
        (funext fun i => by fin_cases i <;> rfl)
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  rw [← Fintype.sum_prod_type', ← Equiv.sum_comp e.symm]
  have hsim : ∀ t : (ZMod q × ZMod q) × (ZMod q × ZMod q),
      2 * (q : ℤ) ^ 4 * κ ((e.symm t).1 0) ((e.symm t).2 0) * κ ((e.symm t).1 1) ((e.symm t).2 1) =
      (2 * (q : ℤ) ^ 4 * κ t.1.1 t.1.2) * κ t.2.1 t.2.2 :=
    fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  simp_rw [hsim]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hsum_k, ← Finset.sum_mul, ← Finset.mul_sum, hsum_k]
  have hsq_m1 : legendreSym q ((-1 : ZMod q).val : ℤ) *
      legendreSym q ((-1 : ZMod q).val : ℤ) = 1 := by
    rw [← sq]; exact legendreSym.sq_one q (by simp)
  calc 2 * (q : ℤ) ^ 4 * (legendreSym q ((-1 : ZMod q).val : ℤ) * ((q : ℤ) - 1) * rho) *
        (legendreSym q ((-1 : ZMod q).val : ℤ) * ((q : ℤ) - 1) * rho)
      = 2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 * rho ^ 2 *
          (legendreSym q ((-1 : ZMod q).val : ℤ) * legendreSym q ((-1 : ZMod q).val : ℤ)) := by ring
    _ = _ := by rw [hsq_m1, mul_one]

/-- Structure of Latin squares fixed by `graphRowSub I_2 ξ η`. -/
private lemma Rmon_L_prop {q : ℕ} [Fact q.Prime] (ξ η : Fin 2 → ZMod q)
    (L : LatinSquare (2 * q))
    (hL : L ∈ fixSet ((graphRowSub (fun b j : Fin 2 => if b = j then (1 : ZMod q) else 0) ξ η).map
      (sylowP q).subtype)) :
    let c' := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1
    let c := 1 - c'
    ξ c' = 0 ∧ η c' = 0 ∧ ξ c ≠ 0 ∧ η c ≠ 0 ∧
    (∀ x y, L.entry (blockEquiv q (0, x)) (blockEquiv q (1, y)) =
      blockEquiv q (c, ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).2 +
        ξ c * x + η c * y)) ∧
    (∀ x y, L.entry (blockEquiv q (1, x)) (blockEquiv q (0, y)) =
      blockEquiv q (c, ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).2 +
        η c * x + ξ c * y)) ∧
    (∀ x y, L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)) =
      blockEquiv q (c', ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y - x)))).2)) ∧
    (∀ x y, L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)) =
      blockEquiv q (c', ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y - x)))).2)) := by
      let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = j then 1 else 0
      let H := graphRowSub k ξ η
      have hL : L ∈ fixSet (H.map (sylowP q).subtype) := hL
      -- First, blocks `01` and `10` are affine via `(x, y) ∈ H`
      let c01 := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).1
      let z01 := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).2
      let c10 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).1
      let z10 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).2
      have h01_form : ∀ x y : ZMod q,
          L.entry (blockEquiv q (0, x)) (blockEquiv q (1, y)) =
            blockEquiv q (c01, z01 + ξ c01 * x + η c01 * y) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then x else y, fun b => k b 0 * x + k b 1 * y,
          fun c => ξ c * x + η c * y)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨x, y, sylowToVec_vecToSylow _⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 0 1 0 0
        simp only [g, sylowToVec_vecToSylow, k, Fin.isValue, zero_add] at hent
        simpa [c01, z01, add_assoc] using hent
      have h10_form : ∀ x y : ZMod q,
          L.entry (blockEquiv q (1, x)) (blockEquiv q (0, y)) =
            blockEquiv q (c10, z10 + η c10 * x + ξ c10 * y) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then y else x, fun b => k b 0 * y + k b 1 * x,
          fun c => ξ c * y + η c * x)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨y, x, sylowToVec_vecToSylow _⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 1 0 0 0
        simp only [g, sylowToVec_vecToSylow, k, Fin.isValue, zero_add] at hent
        have hcomm : ξ c10 * y + η c10 * x = η c10 * x + ξ c10 * y := add_comm _ _
        simpa [c10, z10, add_assoc, hcomm] using hent
      -- Slopes of `01` are nonzero
      have hξ01 : ξ c01 ≠ 0 := by
        intro h0
        have h1 := h01_form 0 0; have h2 := h01_form 1 0
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.col_bijective (blockEquiv q (1, 0))).1 (h1.trans h2.symm))))
      have hη01 : η c01 ≠ 0 := by
        intro h0
        have h1 := h01_form 0 0; have h2 := h01_form 0 1
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.row_bijective (blockEquiv q (0, 0))).1 (h1.trans h2.symm))))
      -- Slopes of `10` are nonzero
      have hξ10 : ξ c10 ≠ 0 := by
        intro h0
        have h1 := h10_form 0 0; have h2 := h10_form 0 1
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.row_bijective (blockEquiv q (1, 0))).1 (h1.trans h2.symm))))
      have hη10 : η c10 ≠ 0 := by
        intro h0
        have h1 := h10_form 0 0; have h2 := h10_form 1 0
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.col_bijective (blockEquiv q (0, 0))).1 (h1.trans h2.symm))))
      -- Row `(0, x)` meets `01` in ALL of `Σ_{c01}`, so every cell in `00` avoids `Σ_{c01}`, hence lies in `Σ_{1 - c01}`!
      have h00_blk : ∀ x y : ZMod q,
          ((blockEquiv q).symm (L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)))).1 = 1 - c01 := by
        intro x y
        let p := (blockEquiv q).symm (L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)))
        have hne : p.1 ≠ c01 := by
          intro heq
          let y1 : ZMod q := (p.2 - z01 - ξ c01 * x) * (η c01)⁻¹
          have h1 := h01_form x y1
          have hEq : L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)) =
              L.entry (blockEquiv q (0, x)) (blockEquiv q (1, y1)) := by
            rw [h1, ← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)))]
            congr 1; refine Prod.ext heq ?_
            dsimp only [y1, z01, p]; field_simp [hη01]; ring
          have hc := (L.row_bijective (blockEquiv q (0, x))).1 hEq
          exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective hc))
        exact fin2_ne_eq_one_sub hne
      -- Similarly col `(0, y)` meets `10` in ALL of `Σ_{c10}`, so `(0, 0)` avoids `Σ_{c10}`, hence `c10 = c01`!
      have hc10_eq : c10 = c01 := by
        have hne : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 ≠ c10 := by
          intro heq
          let p := (blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))
          let x1 : ZMod q := (p.2 - z10) * (η c10)⁻¹
          have h1 := h10_form x1 0
          have hEq : L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)) =
              L.entry (blockEquiv q (1, x1)) (blockEquiv q (0, 0)) := by
            rw [h1, ← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))]
            congr 1; refine Prod.ext heq ?_
            dsimp only [x1, z10, p]; rw [mul_zero, add_zero]; field_simp [hη10]; ring
          have hr := (L.col_bijective (blockEquiv q (0, 0))).1 hEq
          exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective hr))
        rw [h00_blk 0 0] at hne
        have := fin2_ne_eq_one_sub hne.symm
        rw [fin2_one_sub_one_sub] at this
        exact this
      -- Row `(1, x)` meets `10` in all of `Σ_{c01}`, so `11` lies in `Σ_{1 - c01}`
      have h11_blk : ∀ x y : ZMod q,
          ((blockEquiv q).symm (L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)))).1 = 1 - c01 := by
        intro x y
        let p := (blockEquiv q).symm (L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)))
        have hne : p.1 ≠ c10 := by
          intro heq
          let y1 : ZMod q := (p.2 - z10 - η c10 * x) * (ξ c10)⁻¹
          have h1 := h10_form x y1
          have hEq : L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)) =
              L.entry (blockEquiv q (1, x)) (blockEquiv q (0, y1)) := by
            rw [h1, ← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)))]
            congr 1; refine Prod.ext heq ?_
            dsimp only [y1, z10, p]; field_simp [hξ10]; ring
          have hc := (L.row_bijective (blockEquiv q (1, x))).1 hEq
          exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective hc)).symm
        rw [hc10_eq] at hne
        exact fin2_ne_eq_one_sub hne
      -- Now `g₂ = (0, 1; 0, 1; η₀, η₁)` fixes cell `(0, 0), (0, 0)` -> `η (1 - c01) = 0`!
      have hη' : η (1 - c01) = 0 := by
        let g₂ := sylowElem q 0 1 0 1 (η 0) (η 1)
        have hg₂ : g₂ ∈ H := (mem_graphRowSub_iff k ξ η g₂).mpr ⟨0, 1, by
          rw [sylowToVec_sylowElem]; ext i <;> fin_cases i <;> simp [k]⟩
        have hent := (sylow_fix_entry_iff g₂ L).mp (hL g₂.1 ⟨g₂, hg₂, rfl⟩) 0 0 0 0
        rw [sylowToVec_sylowElem] at hent
        simp only [Fin.isValue, ↓reduceIte, add_zero] at hent
        rw [h00_blk 0 0] at hent
        have h1 := congrArg Prod.snd ((blockEquiv q).injective
          (((blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).trans hent))
        have h3 : (if 1 - c01 = 0 then η 0 else η 1) = η (1 - c01) := by
          generalize 1 - c01 = d; fin_cases d <;> rfl
        rw [h3] at h1
        simpa using h1.symm
      -- And `g₁ = (1, 0; 1, 0; ξ₀, ξ₁)` fixes cell `(1, 0), (1, 0)` -> `ξ (1 - c01) = 0`!
      have hξ' : ξ (1 - c01) = 0 := by
        let g₁ := sylowElem q 1 0 1 0 (ξ 0) (ξ 1)
        have hg₁ : g₁ ∈ H := (mem_graphRowSub_iff k ξ η g₁).mpr ⟨1, 0, by
          rw [sylowToVec_sylowElem]; ext i <;> fin_cases i <;> simp [k]⟩
        have hent := (sylow_fix_entry_iff g₁ L).mp (hL g₁.1 ⟨g₁, hg₁, rfl⟩) 1 1 0 0
        rw [sylowToVec_sylowElem] at hent
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero] at hent
        rw [h11_blk 0 0] at hent
        have h1 := congrArg Prod.snd ((blockEquiv q).injective
          (((blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)))).trans hent))
        have h3 : (if 1 - c01 = 0 then ξ 0 else ξ 1) = ξ (1 - c01) := by
          generalize 1 - c01 = d; fin_cases d <;> rfl
        rw [h3] at h1
        simpa using h1.symm
      -- Diagonal invariance on `00` and `11`
      have h00_diag : ∀ x y : ZMod q, L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)) =
          blockEquiv q (1 - c01,
            ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y - x)))).2) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then x else 0, fun b => k b 0 * x,
          fun c => ξ c * x)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨x, 0, by
          rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp [k]⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 0 0 0 (y - x)
        simp only [g, sylowToVec_vecToSylow, k, Fin.isValue, ↓reduceIte, one_mul, zero_add,
          sub_add_cancel] at hent
        rw [h00_blk 0 (y - x), hξ', zero_mul, add_zero] at hent
        exact hent
      have h11_diag : ∀ x y : ZMod q, L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)) =
          blockEquiv q (1 - c01,
            ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y - x)))).2) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then 0 else x, fun b => k b 1 * x,
          fun c => η c * x)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨0, x, by
          rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp [k]⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 1 1 0 (y - x)
        simp only [g, sylowToVec_vecToSylow, k, Fin.isValue, one_ne_zero, ↓reduceIte, one_mul,
          zero_add, sub_add_cancel] at hent
        rw [h11_blk 0 (y - x), hη', zero_mul, add_zero] at hent
        exact hent
      have hc' : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 = 1 - c01 :=
        h00_blk 0 0
      have hc1 : 1 - (1 - c01) = c01 := fin2_one_sub_one_sub c01
      refine ⟨by rw [hc']; exact hξ', by rw [hc']; exact hη',
        by rw [hc', hc1]; exact hξ01, by rw [hc', hc1]; exact hη01,
        by rw [hc', hc1]; exact h01_form,
        by rw [hc', hc1]; intro x y; have h := h10_form x y; rw [hc10_eq] at h; exact h,
        by rw [hc']; exact h00_diag, by rw [hc']; exact h11_diag⟩

/-- Explicit Latin square builder for the `R_mon` branch. -/
private def Rmon_build {q : ℕ} [Fact q.Prime] (ξ η : Fin 2 → ZMod q) (c' : Fin 2)
    (hξc : ξ (1 - c') ≠ 0) (hηc : η (1 - c') ≠ 0)
    (t : Equiv.Perm (ZMod q) × Equiv.Perm (ZMod q) × ZMod q × ZMod q) :
    LatinSquare (2 * q) :=
  let c := 1 - c'
  { entry := fun r col =>
      let pr := (blockEquiv q).symm r
      let pc := (blockEquiv q).symm col
      if pr.1 = 0 ∧ pc.1 = 0 then blockEquiv q (c', t.1 (pc.2 - pr.2))
      else if pr.1 = 1 ∧ pc.1 = 1 then blockEquiv q (c', t.2.1 (pc.2 - pr.2))
      else if pr.1 = 0 ∧ pc.1 = 1 then blockEquiv q (c, t.2.2.1 + ξ c * pr.2 + η c * pc.2)
      else blockEquiv q (c, t.2.2.2 + η c * pr.2 + ξ c * pc.2)
    row_bijective := fun r => by
      rw [← Finite.injective_iff_bijective]
      intro col₁ col₂ hEq
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective col₁
      obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective col₂
      simp only [Equiv.symm_apply_apply] at hEq
      have hcne : c' ≠ c := by dsimp only [c]; fin_cases c' <;> decide
      fin_cases a <;> fin_cases b₁ <;> fin_cases b₂ <;>
        simp [c, hcne, hcne.symm, hηc, hξc] at hEq
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl
    col_bijective := fun col => by
      rw [← Finite.injective_iff_bijective]
      intro r₁ r₂ hEq
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
      obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
      simp only [Equiv.symm_apply_apply] at hEq
      have hcne : c' ≠ c := by dsimp only [c]; fin_cases c' <;> decide
      fin_cases b <;> fin_cases a₁ <;> fin_cases a₂ <;>
        simp [c, hcne, hcne.symm, hηc, hξc] at hEq
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl }

private lemma Rmon_build_fix {q : ℕ} [Fact q.Prime] (ξ η : Fin 2 → ZMod q) (c' : Fin 2)
    (hξ' : ξ c' = 0) (hη' : η c' = 0) (hξc : ξ (1 - c') ≠ 0) (hηc : η (1 - c') ≠ 0)
    (t : Equiv.Perm (ZMod q) × Equiv.Perm (ZMod q) × ZMod q × ZMod q) :
    Rmon_build ξ η c' hξc hηc t ∈
      fixSet ((graphRowSub (fun b j : Fin 2 => if b = j then (1 : ZMod q) else 0) ξ η).map
        (sylowP q).subtype) := by
  let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = j then 1 else 0
  rintro _ ⟨g, hgH, rfl⟩
  change g.1 • Rmon_build ξ η c' hξc hηc t = Rmon_build ξ η c' hξc hηc t
  rw [sylow_fix_entry_iff]
  intro a b x y
  rcases (mem_graphRowSub_iff k ξ η g).mp hgH with ⟨gx, gy, hg⟩
  dsimp only [Rmon_build]; rw [hg]; simp only [Equiv.symm_apply_apply, k]
  fin_cases a <;> fin_cases b <;> simp [hξ', hη'] <;> ring

private lemma Rmon_build_sign {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) (ξ η : Fin 2 → ZMod q) (c' : Fin 2)
    (hξ' : ξ c' = 0) (hη' : η c' = 0) (hξc : ξ (1 - c') ≠ 0) (hηc : η (1 - c') ≠ 0)
    (t : Equiv.Perm (ZMod q) × Equiv.Perm (ZMod q) × ZMod q × ZMod q) :
    squareSign (Rmon_build ξ η c' hξc hηc t) = 1 := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = j then 1 else 0
  let H := graphRowSub k ξ η
  let c := 1 - c'
  have hrow_mv : ∀ a : Fin 2, ∃ g ∈ H, (sylowToVec g).1 a ≠ 0 := fun a => by
    fin_cases a
    · exact ⟨vecToSylow (fun i => if i = 0 then 1 else 0, fun b => k b 0, fun c => ξ c),
        (mem_graphRowSub_iff k ξ η _).mpr ⟨1, 0, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
        by simp⟩
    · exact ⟨vecToSylow (fun i => if i = 0 then 0 else 1, fun b => k b 1, fun c => η c),
        (mem_graphRowSub_iff k ξ η _).mpr ⟨0, 1, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
        by simp⟩
  have hcol_mv : ∀ b : Fin 2, ∃ g ∈ H, (sylowToVec g).2.1 b ≠ 0 := fun b => by
    fin_cases b
    · exact ⟨vecToSylow (fun i => if i = 0 then 1 else 0, fun b => k b 0, fun c => ξ c),
        (mem_graphRowSub_iff k ξ η _).mpr ⟨1, 0, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
        by simp [k]⟩
    · exact ⟨vecToSylow (fun i => if i = 0 then 0 else 1, fun b => k b 1, fun c => η c),
        (mem_graphRowSub_iff k ξ η _).mpr ⟨0, 1, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
        by simp [k]⟩
  let B := Rmon_build ξ η c' hξc hηc t
  rw [squareSign_of_all_moving hodd H B (Rmon_build_fix ξ η c' hξ' hη' hξc hηc t) hrow_mv hcol_mv]
  let negP : Equiv.Perm (ZMod q) := Equiv.neg (ZMod q)
  have hfin2_c' : c' = 0 ∨ c' = 1 := fin2_cases c'
  have hr0 : Equiv.Perm.sign (rowPerm B (blockEquiv q (0, 0))) =
      (if c' = 0 then 1 else -1) * Equiv.Perm.sign t.1 *
        Equiv.Perm.sign ((Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.2.1)) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then 1 else Equiv.swap 0 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun b =>
      if b = 0 then t.1 else (Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.2.1)
    have hp : rowPerm B (blockEquiv q (0, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro col
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (0, 0)) (blockEquiv q (b, y)) = _
      dsimp only [B, Rmon_build, ϖ, φ, c]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases b with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, sub_zero];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (if ϖ = 1 then (1 : ℤˣ) else -1) = if c' = 0 then 1 else -1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [hϖ]; rfl
  have hr1 : Equiv.Perm.sign (rowPerm B (blockEquiv q (1, 0))) =
      (if c' = 0 then -1 else 1) *
        Equiv.Perm.sign ((Equiv.mulLeft₀ (ξ c) hξc).trans (Equiv.addRight t.2.2.2)) *
        Equiv.Perm.sign t.2.1 := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then Equiv.swap 0 1 else 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun b =>
      if b = 0 then (Equiv.mulLeft₀ (ξ c) hξc).trans (Equiv.addRight t.2.2.2) else t.2.1
    have hp : rowPerm B (blockEquiv q (1, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro col
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (1, 0)) (blockEquiv q (b, y)) = _
      dsimp only [B, Rmon_build, ϖ, φ, c]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases b with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, sub_zero];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (if ϖ = 1 then (1 : ℤˣ) else -1) = if c' = 0 then -1 else 1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [hϖ]; rfl
  have hc0 : Equiv.Perm.sign (colPerm B (blockEquiv q (0, 0))) =
      (if c' = 0 then 1 else -1) *
        Equiv.Perm.sign (negP.trans t.1) *
        Equiv.Perm.sign ((Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.2.2)) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then 1 else Equiv.swap 0 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun a =>
      if a = 0 then negP.trans t.1
      else (Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.2.2)
    have hp : colPerm B (blockEquiv q (0, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro r
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (a, x)) (blockEquiv q (0, 0)) = _
      dsimp only [B, Rmon_build, ϖ, φ, negP, c]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases a with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, Equiv.neg_apply, zero_sub];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (if ϖ = 1 then (1 : ℤˣ) else -1) = if c' = 0 then 1 else -1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [hϖ]; rfl
  have hc1 : Equiv.Perm.sign (colPerm B (blockEquiv q (1, 0))) =
      (if c' = 0 then -1 else 1) *
        Equiv.Perm.sign ((Equiv.mulLeft₀ (ξ c) hξc).trans (Equiv.addRight t.2.2.1)) *
        Equiv.Perm.sign (negP.trans t.2.1) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then Equiv.swap 0 1 else 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun a =>
      if a = 0 then (Equiv.mulLeft₀ (ξ c) hξc).trans (Equiv.addRight t.2.2.1)
      else negP.trans t.2.1
    have hp : colPerm B (blockEquiv q (1, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro r
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (a, x)) (blockEquiv q (1, 0)) = _
      dsimp only [B, Rmon_build, ϖ, φ, negP, c]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases a with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, Equiv.neg_apply, zero_sub];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (if ϖ = 1 then (1 : ℤˣ) else -1) = if c' = 0 then -1 else 1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [hϖ]; rfl
  rw [hr0, hr1, hc0, hc1]
  have haff_s : ∀ (a : ZMod q) (ha : a ≠ 0) (z : ZMod q),
      Equiv.Perm.sign ((Equiv.mulLeft₀ a ha).trans (Equiv.addRight z)) =
        Equiv.Perm.sign (Equiv.mulLeft₀ a ha) := fun a ha z => by
    change Equiv.Perm.sign (Equiv.addRight z * Equiv.mulLeft₀ a ha) = _
    rw [map_mul, sign_addRight_eq_one hq_odd, one_mul]
  have hneg_t : ∀ φ : Equiv.Perm (ZMod q),
      Equiv.Perm.sign (negP.trans φ) = Equiv.Perm.sign φ * Equiv.Perm.sign negP := fun φ => by
    change Equiv.Perm.sign (φ * negP) = _; exact map_mul _ _ _
  simp_rw [haff_s, hneg_t]
  have hsq : ∀ u : ℤˣ, u * u = 1 := fun u => by
    rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  have hite :
      (if c' = 0 then (1 : ℤˣ) else -1) * (if c' = 0 then (-1 : ℤˣ) else 1) *
      (if c' = 0 then (1 : ℤˣ) else -1) * (if c' = 0 then (-1 : ℤˣ) else 1) = 1 := by
    rcases hfin2_c' with hc' | hc' <;> simp [hc']
  calc _ = ((if c' = 0 then (1 : ℤˣ) else -1) * (if c' = 0 then (-1 : ℤˣ) else 1) *
        (if c' = 0 then (1 : ℤˣ) else -1) * (if c' = 0 then (-1 : ℤˣ) else 1)) *
        (Equiv.Perm.sign t.1 * Equiv.Perm.sign t.1) *
        (Equiv.Perm.sign t.2.1 * Equiv.Perm.sign t.2.1) *
        (Equiv.Perm.sign negP * Equiv.Perm.sign negP) *
        (Equiv.Perm.sign (Equiv.mulLeft₀ (η c) hηc) *
          Equiv.Perm.sign (Equiv.mulLeft₀ (η c) hηc)) *
        (Equiv.Perm.sign (Equiv.mulLeft₀ (ξ c) hξc) *
          Equiv.Perm.sign (Equiv.mulLeft₀ (ξ c) hξc)) := by ac_rfl
    _ = 1 := by rw [hite]; simp [hsq]

/-- Normalized `R_mon` sum (for `k = I_2`): `∑_{ξ, η} S(H) = 2 * q^2 * (q - 1)^2 * (q!)^2`. -/
lemma sum_Rmon_norm {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = j then 1 else 0
    ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q, S_twoq q (graphRowSub k ξ η) =
      2 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 * (q.factorial : ℤ) ^ 2 := by
  classical
  intro k
  have hq : q.Prime := Fact.out
  have hS : ∀ ξ η : Fin 2 → ZMod q,
      S_twoq q (graphRowSub k ξ η) =
      (if ξ 0 = 0 ∧ η 0 = 0 ∧ ξ 1 ≠ 0 ∧ η 1 ≠ 0 then (q : ℤ) ^ 2 * (q.factorial : ℤ) ^ 2 else 0) +
      (if ξ 1 = 0 ∧ η 1 = 0 ∧ ξ 0 ≠ 0 ∧ η 0 ≠ 0 then (q : ℤ) ^ 2 * (q.factorial : ℤ) ^ 2 else 0) := by
    intro ξ η
    let H := graphRowSub k ξ η
    have hL_prop := Rmon_L_prop ξ η
    -- Now count `Fix(H)` directly: split by `c' ∈ Fin 2`
    unfold S_twoq signedFixSum
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Fin 2)))
      (g := fun L : LatinSquare (2 * q) =>
        ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1)
      (fun _ _ => Finset.mem_univ _)]
    rw [Fin.sum_univ_two]
    have hbranch : ∀ c' : Fin 2,
        (∑ L ∈ (Finset.univ.filter (fun L : LatinSquare (2 * q) =>
            L ∈ fixSet (H.map (sylowP q).subtype))).filter
            (fun L => ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 = c'),
          (squareSign L : ℤ)) =
        if ξ c' = 0 ∧ η c' = 0 ∧ ξ (1 - c') ≠ 0 ∧ η (1 - c') ≠ 0
        then (q : ℤ) ^ 2 * (q.factorial : ℤ) ^ 2 else 0 := by
      intro c'
      split_ifs with hcond
      · rcases hcond with ⟨hξ', hη', hξc, hηc⟩
        let build := Rmon_build ξ η c' hξc hηc
        have hbuild_fix : ∀ t, build t ∈ fixSet (H.map (sylowP q).subtype) :=
          Rmon_build_fix ξ η c' hξ' hη' hξc hηc
        have hbuild_sign : ∀ t, squareSign (build t) = 1 :=
          Rmon_build_sign hodd ξ η c' hξ' hη' hξc hηc
        -- Bijection between the fiber and `Perm (ZMod q) × Perm (ZMod q) × ZMod q × ZMod q`
        have hbij :
            (∑ L ∈ (Finset.univ.filter (fun L : LatinSquare (2 * q) =>
                L ∈ fixSet (H.map (sylowP q).subtype))).filter
                (fun L => ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 = c'),
              (squareSign L : ℤ)) =
            ∑ t : Equiv.Perm (ZMod q) × Equiv.Perm (ZMod q) × ZMod q × ZMod q, (1 : ℤ) := by
          symm
          refine Finset.sum_bij (fun t _ => build t) ?_ ?_ ?_ (fun t _ => by rw [hbuild_sign]; rfl)
          · intro t _
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbuild_fix t⟩, ?_⟩
            simp [build, Rmon_build]
          · intro t₁ _ t₂ _ hEq
            have h00 : t₁.1 = t₂.1 := by
              apply Equiv.Perm.ext; intro y
              have h := congrArg (fun M => M.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y))) hEq
              simp only [build, Rmon_build, Equiv.symm_apply_apply, ↓reduceIte, sub_zero] at h
              exact (Prod.mk.inj ((blockEquiv q).injective h)).2
            have h11 : t₁.2.1 = t₂.2.1 := by
              apply Equiv.Perm.ext; intro y
              have h := congrArg (fun M => M.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y))) hEq
              simp only [build, Rmon_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, and_self,
                ↓reduceIte, sub_zero] at h
              exact (Prod.mk.inj ((blockEquiv q).injective h)).2
            have h01 : t₁.2.2.1 = t₂.2.2.1 := by
              have h := congrArg (fun M => M.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0))) hEq
              simp only [build, Rmon_build, Equiv.symm_apply_apply, Fin.isValue, zero_ne_one, and_false,
                ↓reduceIte, false_and, and_self, mul_zero, add_zero] at h
              exact (Prod.mk.inj ((blockEquiv q).injective h)).2
            have h10 : t₁.2.2.2 = t₂.2.2.2 := by
              have h := congrArg (fun M => M.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0))) hEq
              simp only [build, Rmon_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, false_and,
                ↓reduceIte, and_false, mul_zero, add_zero] at h
              exact (Prod.mk.inj ((blockEquiv q).injective h)).2
            exact Prod.ext h00 (Prod.ext h11 (Prod.ext h01 h10))
          · intro L hL
            have hLfix := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
            have hLc' := (Finset.mem_filter.mp hL).2
            have hp := hL_prop L hLfix
            rw [hLc'] at hp
            -- Extract `φ₀, φ₁ : Equiv.Perm (ZMod q)` from row `(0, 0)` on `00` and row `(1, 0)` on `11`
            have hφ0_bij : Function.Bijective (fun y : ZMod q =>
                ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y)))).2) := by
              rw [← Finite.injective_iff_bijective]
              intro y₁ y₂ hEq
              have hb1 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₁)))).1 = c' := by
                have := hp.2.2.2.2.2.2.1 0 y₁; rw [this, Equiv.symm_apply_apply]
              have hb2 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₂)))).1 = c' := by
                have := hp.2.2.2.2.2.2.1 0 y₂; rw [this, Equiv.symm_apply_apply]
              have he : L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₁)) =
                  L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₂)) :=
                (blockEquiv q).symm.injective (Prod.ext (hb1.trans hb2.symm) hEq)
              exact congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 he))
            have hφ1_bij : Function.Bijective (fun y : ZMod q =>
                ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y)))).2) := by
              rw [← Finite.injective_iff_bijective]
              intro y₁ y₂ hEq
              have hb1 : ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y₁)))).1 = c' := by
                have := hp.2.2.2.2.2.2.2 0 y₁; rw [this, Equiv.symm_apply_apply]
              have hb2 : ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y₂)))).1 = c' := by
                have := hp.2.2.2.2.2.2.2 0 y₂; rw [this, Equiv.symm_apply_apply]
              have he : L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y₁)) =
                  L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, y₂)) :=
                (blockEquiv q).symm.injective (Prod.ext (hb1.trans hb2.symm) hEq)
              exact congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 he))
            let t : Equiv.Perm (ZMod q) × Equiv.Perm (ZMod q) × ZMod q × ZMod q :=
              (Equiv.ofBijective _ hφ0_bij, Equiv.ofBijective _ hφ1_bij,
               ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).2,
               ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).2)
            refine ⟨t, Finset.mem_univ _, ?_⟩
            apply LatinSquare.ext; funext r col
            obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
            obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
            fin_cases a <;> fin_cases b
            · simp only [build, Rmon_build, Equiv.symm_apply_apply, ↓reduceIte, t, Equiv.ofBijective_apply]
              exact (hp.2.2.2.2.2.2.1 x y).symm
            · simp only [build, Rmon_build, Equiv.symm_apply_apply, Fin.isValue, zero_ne_one, and_false,
                ↓reduceIte, false_and, and_self, t]
              exact (hp.2.2.2.2.1 x y).symm
            · simp only [build, Rmon_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, false_and,
                ↓reduceIte, and_false, t]
              exact (hp.2.2.2.2.2.1 x y).symm
            · simp only [build, Rmon_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, and_self,
                ↓reduceIte, t, Equiv.ofBijective_apply]
              exact (hp.2.2.2.2.2.2.2 x y).symm
        rw [hbij, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_perm, ZMod.card, nsmul_eq_mul, mul_one]
        push_cast; ring
      · refine Finset.sum_eq_zero fun L hL => ?_
        exfalso
        have hLfix := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
        have hLc' := (Finset.mem_filter.mp hL).2
        have hp := hL_prop L hLfix
        rw [hLc'] at hp
        exact hcond ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
    rw [hbranch 0, hbranch 1]
    rfl
  simp_rw [hS, Finset.sum_add_distrib]
  -- Count each of the two identical sums: `(q - 1)^2 * (q^2 * (q!)^2)`
  have hcount : ∀ c' : Fin 2,
      (∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q,
        if ξ c' = 0 ∧ η c' = 0 ∧ ξ (1 - c') ≠ 0 ∧ η (1 - c') ≠ 0
        then (q : ℤ) ^ 2 * (q.factorial : ℤ) ^ 2 else 0) =
      (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 * (q.factorial : ℤ) ^ 2 := by
    intro c'
    rw [← Fintype.sum_prod_type', ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    let S := (Finset.univ : Finset (ZMod q)).erase 0
    have hS : S.card = q - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hbij :
        ((Finset.univ : Finset ((Fin 2 → ZMod q) × (Fin 2 → ZMod q))).filter
          (fun p => p.1 c' = 0 ∧ p.2 c' = 0 ∧ p.1 (1 - c') ≠ 0 ∧ p.2 (1 - c') ≠ 0)).card =
        (S ×ˢ S).card := by
      refine Finset.card_bij (fun p _ => (p.1 (1 - c'), p.2 (1 - c'))) ?_ ?_ ?_
      · intro p hp
        have h := (Finset.mem_filter.mp hp).2
        simp [S, h]
      · intro p₁ hp₁ p₂ hp₂ hEq
        have h1 := (Finset.mem_filter.mp hp₁).2
        have h2 := (Finset.mem_filter.mp hp₂).2
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · fin_cases c' <;> fin_cases i
          · exact h1.1.trans h2.1.symm
          · exact congrArg Prod.fst hEq
          · exact congrArg Prod.fst hEq
          · exact h1.1.trans h2.1.symm
        · fin_cases c' <;> fin_cases i
          · exact h1.2.1.trans h2.2.1.symm
          · exact congrArg Prod.snd hEq
          · exact congrArg Prod.snd hEq
          · exact h1.2.1.trans h2.2.1.symm
      · intro t ht
        simp only [Finset.mem_product, S, Finset.mem_erase, Finset.mem_univ, and_true] at ht
        refine ⟨(fun i => if i = c' then 0 else t.1, fun i => if i = c' then 0 else t.2),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · fin_cases c' <;> simp [ht]
        · fin_cases c' <;> simp
    rw [hbij, Finset.card_product, hS]
    have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := hq.pos; omega
    push_cast; rw [hcast]; ring
  have h0 := hcount 0
  have h1 := hcount 1
  have h10 : (1 : Fin 2) - 0 = 1 := rfl
  have h11 : (1 : Fin 2) - 1 = 0 := rfl
  rw [h10] at h0; rw [h11] at h1
  rw [h0, h1]
  ring

/-- Structure of Latin squares fixed by `graphRowSub [[1, 0], [1, 1]] ξ η`. -/
private lemma Rone_L_prop {q : ℕ} [Fact q.Prime] (ξ η : Fin 2 → ZMod q)
    (L : LatinSquare (2 * q))
    (hL : L ∈ fixSet ((graphRowSub (fun b j : Fin 2 => if b = 0 ∧ j = 1 then (0 : ZMod q) else 1) ξ η).map
      (sylowP q).subtype)) :
    let c' := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1
    let c := 1 - c'
    η c' = 0 ∧ ξ c' ≠ 0 ∧ ξ c ≠ 0 ∧ η c ≠ 0 ∧ ξ c ≠ η c ∧
    (∀ x y, L.entry (blockEquiv q (0, x)) (blockEquiv q (1, y)) =
      blockEquiv q (c, ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).2 +
        (ξ c - η c) * x + η c * y)) ∧
    (∀ x y, L.entry (blockEquiv q (1, x)) (blockEquiv q (0, y)) =
      blockEquiv q (c, ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).2 +
        η c * x + ξ c * y)) ∧
    (∀ x y, L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)) =
      blockEquiv q (c', ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)))).2 +
        (-ξ c') * x + ξ c' * y)) ∧
    (∀ x y, L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)) =
      blockEquiv q (c', ξ c' * x +
        ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y - x)))).2)) := by
      let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 ∧ j = 1 then 0 else 1
      let H := graphRowSub k ξ η
      have hL : L ∈ fixSet (H.map (sylowP q).subtype) := hL
      let c01 := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).1
      let z01 := ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).2
      let c10 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).1
      let z10 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).2
      let c11 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)))).1
      let z11 := ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)))).2
      have h01_form : ∀ x y : ZMod q,
          L.entry (blockEquiv q (0, x)) (blockEquiv q (1, y)) =
            blockEquiv q (c01, z01 + (ξ c01 - η c01) * x + η c01 * y) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then x else y - x,
          fun b => k b 0 * x + k b 1 * (y - x), fun c => ξ c * x + η c * (y - x))
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨x, y - x, sylowToVec_vecToSylow _⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 0 1 0 0
        simp only [g, sylowToVec_vecToSylow, k, Fin.isValue, ↓reduceIte, zero_add, one_mul,
          one_ne_zero, false_and, add_sub_cancel] at hent
        rw [hent]; congr 1; refine Prod.ext rfl ?_; dsimp only [c01, z01]; ring
      have h10_form : ∀ x y : ZMod q,
          L.entry (blockEquiv q (1, x)) (blockEquiv q (0, y)) =
            blockEquiv q (c10, z10 + η c10 * x + ξ c10 * y) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then y else x,
          fun b => k b 0 * y + k b 1 * x, fun c => ξ c * y + η c * x)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨y, x, sylowToVec_vecToSylow _⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 1 0 0 0
        have hk00 : k 0 0 = 1 := by simp [k]
        have hk01 : k 0 1 = 0 := by simp [k]
        simp only [g, sylowToVec_vecToSylow, hk00, hk01, Fin.isValue, one_ne_zero, ↓reduceIte,
          zero_add, zero_mul, add_zero, one_mul] at hent
        rw [hent]; congr 1; refine Prod.ext rfl ?_; dsimp only [c10, z10]; ring
      have h11_form : ∀ x y : ZMod q,
          L.entry (blockEquiv q (1, x)) (blockEquiv q (1, y)) =
            blockEquiv q (c11, z11 + (η c11 - ξ c11) * x + ξ c11 * y) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then y - x else x,
          fun b => k b 0 * (y - x) + k b 1 * x, fun c => ξ c * (y - x) + η c * x)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨y - x, x, sylowToVec_vecToSylow _⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 1 1 0 0
        simp only [g, sylowToVec_vecToSylow, k, Fin.isValue, one_ne_zero, ↓reduceIte, zero_add,
          false_and, one_mul, sub_add_cancel] at hent
        rw [hent]; congr 1; refine Prod.ext rfl ?_; dsimp only [c11, z11]; ring
      -- Slopes of `01`, `10`, `11` are all nonzero
      have h01_x : ξ c01 - η c01 ≠ 0 := by
        intro h0; have h1 := h01_form 0 0; have h2 := h01_form 1 0
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.col_bijective _).1 (h1.trans h2.symm))))
      have h01_y : η c01 ≠ 0 := by
        intro h0; have h1 := h01_form 0 0; have h2 := h01_form 0 1
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.row_bijective _).1 (h1.trans h2.symm))))
      have h10_x : η c10 ≠ 0 := by
        intro h0; have h1 := h10_form 0 0; have h2 := h10_form 1 0
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.col_bijective _).1 (h1.trans h2.symm))))
      have h10_y : ξ c10 ≠ 0 := by
        intro h0; have h1 := h10_form 0 0; have h2 := h10_form 0 1
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.row_bijective _).1 (h1.trans h2.symm))))
      have h11_x : η c11 - ξ c11 ≠ 0 := by
        intro h0; have h1 := h11_form 0 0; have h2 := h11_form 1 0
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.col_bijective _).1 (h1.trans h2.symm))))
      have h11_y : ξ c11 ≠ 0 := by
        intro h0; have h1 := h11_form 0 0; have h2 := h11_form 0 1
        rw [h0, zero_mul] at h1 h2
        exact zero_ne_one (congrArg Prod.snd ((blockEquiv q).injective
          ((L.row_bijective _).1 (h1.trans h2.symm))))
      -- `11` avoids `10` (same row block 1) and `01` (same col block 1), so `c01 = c10 = 1 - c11`
      have h11_ne_10 : c11 ≠ c10 := by
        intro heq
        let y0 : ZMod q := (z11 - z10) * (ξ c10)⁻¹
        have hEq : L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, y0)) =
            L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)) := by
          rw [h10_form 0 y0, h11_form 0 0]
          congr 1; refine Prod.ext heq.symm ?_
          dsimp only [y0, z10, z11]; rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
          field_simp [h10_y]; ring
        exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective ((L.row_bijective _).1 hEq)))
      have h11_ne_01 : c11 ≠ c01 := by
        intro heq
        let x0 : ZMod q := (z11 - z01) * (ξ c01 - η c01)⁻¹
        have hEq : L.entry (blockEquiv q (0, x0)) (blockEquiv q (1, 0)) =
            L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)) := by
          rw [h01_form x0 0, h11_form 0 0]
          congr 1; refine Prod.ext heq.symm ?_
          dsimp only [x0, z01, z11]; rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
          field_simp [h01_x]; ring
        exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective ((L.col_bijective _).1 hEq)))
      have hc01_eq : c01 = 1 - c11 := fin2_ne_eq_one_sub h11_ne_01.symm
      have hc10_eq : c10 = 1 - c11 := fin2_ne_eq_one_sub h11_ne_10.symm
      -- Block `00` avoids `01`, hence lies in `Σ_{c11}`!
      have h00_blk : ∀ x y : ZMod q,
          ((blockEquiv q).symm (L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)))).1 = c11 := by
        intro x y
        let p := (blockEquiv q).symm (L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)))
        have hne : p.1 ≠ c01 := by
          intro heq
          let y1 : ZMod q := (p.2 - z01 - (ξ c01 - η c01) * x) * (η c01)⁻¹
          have hEq : L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)) =
              L.entry (blockEquiv q (0, x)) (blockEquiv q (1, y1)) := by
            rw [h01_form x y1, ← (blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)))]
            congr 1; refine Prod.ext heq ?_
            dsimp only [y1, z01, p]; field_simp [h01_y]; ring
          exact Fin.zero_ne_one (congrArg Prod.fst ((blockEquiv q).injective ((L.row_bijective _).1 hEq)))
        rw [hc01_eq] at hne
        have := fin2_ne_eq_one_sub hne
        rwa [fin2_one_sub_one_sub] at this
      -- `g₂ = (0, 1; 0, 1; η₀, η₁)` fixes cell `(0, 0), (0, 0)` -> `η c11 = 0`!
      have hη' : η c11 = 0 := by
        let g₂ := sylowElem q 0 1 0 1 (η 0) (η 1)
        have hg₂ : g₂ ∈ H := (mem_graphRowSub_iff k ξ η g₂).mpr ⟨0, 1, by
          rw [sylowToVec_sylowElem]; ext i <;> fin_cases i <;> simp [k]⟩
        have hent := (sylow_fix_entry_iff g₂ L).mp (hL g₂.1 ⟨g₂, hg₂, rfl⟩) 0 0 0 0
        rw [sylowToVec_sylowElem] at hent
        simp only [Fin.isValue, ↓reduceIte, add_zero] at hent
        rw [h00_blk 0 0] at hent
        have h1 := congrArg Prod.snd ((blockEquiv q).injective
          (((blockEquiv q).apply_symm_apply (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).trans hent))
        have h2 : (if c11 = 0 then η 0 else η 1) = η c11 := by
          generalize c11 = d; fin_cases d <;> rfl
        rw [h2] at h1
        simpa using h1.symm
      -- `00` shifts by `g₁^x = (x, 0; x, x; ξ₀ x, ξ₁ x)`: `L((0, x), (0, y)) = (c11, ξ c11 * x + h(y - x))`
      have h00_form : ∀ x y : ZMod q, L.entry (blockEquiv q (0, x)) (blockEquiv q (0, y)) =
          blockEquiv q (c11, ξ c11 * x +
            ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y - x)))).2) := by
        intro x y
        let g := vecToSylow (fun a => if a = 0 then x else 0, fun b => k b 0 * x, fun c => ξ c * x)
        have hgH : g ∈ H := (mem_graphRowSub_iff k ξ η g).mpr ⟨x, 0, by
          rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp [k]⟩
        have hent := (sylow_fix_entry_iff g L).mp (hL g.1 ⟨g, hgH, rfl⟩) 0 0 0 (y - x)
        have hk00 : k 0 0 = 1 := by simp [k]
        simp only [g, sylowToVec_vecToSylow, hk00, Fin.isValue, ↓reduceIte, one_mul, zero_add,
          sub_add_cancel] at hent
        rw [h00_blk 0 (y - x)] at hent
        rw [hent]; congr 1; refine Prod.ext rfl ?_; ring
      have hc' : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 = c11 :=
        h00_blk 0 0
      refine ⟨by rw [hc']; exact hη', by rw [hc']; exact h11_y,
        by rw [hc', ← hc10_eq]; exact h10_y, by rw [hc', ← hc01_eq]; exact h01_y,
        by rw [hc', ← hc01_eq]; exact sub_ne_zero.mp h01_x,
        by rw [hc', ← hc01_eq]; exact h01_form,
        by rw [hc', ← hc10_eq]; exact h10_form,
        by rw [hc']; intro x y; have h := h11_form x y; rw [hη', zero_sub] at h; exact h,
        by rw [hc']; exact h00_form⟩

/-- Explicit Latin square builder for the `R_one` branch. -/
private def Rone_build {q : ℕ} [Fact q.Prime] (ξ η : Fin 2 → ZMod q) (c' : Fin 2)
    (hδ : ξ c' ≠ 0) (hξc : ξ (1 - c') ≠ 0) (hηc : η (1 - c') ≠ 0) (hne : ξ (1 - c') ≠ η (1 - c'))
    (t : { h : Equiv.Perm (ZMod q) // Function.Bijective (fun x => h x - ξ c' * x) } ×
      ZMod q × ZMod q × ZMod q) : LatinSquare (2 * q) :=
  let c := 1 - c'
  let δ := ξ c'
  have hξmη : ξ c - η c ≠ 0 := sub_ne_zero.mpr hne
  { entry := fun r col =>
      let pr := (blockEquiv q).symm r
      let pc := (blockEquiv q).symm col
      if pr.1 = 0 ∧ pc.1 = 0 then blockEquiv q (c', δ * pr.2 + t.1.1 (pc.2 - pr.2))
      else if pr.1 = 0 ∧ pc.1 = 1 then blockEquiv q (c, t.2.1 + (ξ c - η c) * pr.2 + η c * pc.2)
      else if pr.1 = 1 ∧ pc.1 = 0 then blockEquiv q (c, t.2.2.1 + η c * pr.2 + ξ c * pc.2)
      else blockEquiv q (c', t.2.2.2 + (-δ) * pr.2 + δ * pc.2)
    row_bijective := fun r => by
      rw [← Finite.injective_iff_bijective]
      intro col₁ col₂ hEq
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      obtain ⟨⟨b₁, y₁⟩, rfl⟩ := (blockEquiv q).surjective col₁
      obtain ⟨⟨b₂, y₂⟩, rfl⟩ := (blockEquiv q).surjective col₂
      simp only [Equiv.symm_apply_apply] at hEq
      have hcne : c' ≠ c := by dsimp only [c]; fin_cases c' <;> decide
      fin_cases a <;> fin_cases b₁ <;> fin_cases b₂ <;>
        simp [c, δ, hcne, hcne.symm, hηc, hξc, hδ] at hEq
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl
    col_bijective := fun col => by
      rw [← Finite.injective_iff_bijective]
      intro r₁ r₂ hEq
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      obtain ⟨⟨a₁, x₁⟩, rfl⟩ := (blockEquiv q).surjective r₁
      obtain ⟨⟨a₂, x₂⟩, rfl⟩ := (blockEquiv q).surjective r₂
      simp only [Equiv.symm_apply_apply] at hEq
      have hcne : c' ≠ c := by dsimp only [c]; fin_cases c' <;> decide
      fin_cases b <;> fin_cases a₁ <;> fin_cases a₂ <;>
        simp [c, δ, hcne, hcne.symm, hηc, hξmη, hδ] at hEq
      · have heq' : t.1.1 (y - x₁) - δ * (y - x₁) = t.1.1 (y - x₂) - δ * (y - x₂) := by
          linear_combination hEq
        have := t.1.2.1 heq'
        congr 1; exact Prod.ext rfl (by linear_combination -this)
      · subst hEq; rfl
      · subst hEq; rfl
      · subst hEq; rfl }

private lemma Rone_build_fix {q : ℕ} [Fact q.Prime] (ξ η : Fin 2 → ZMod q) (c' : Fin 2)
    (hη' : η c' = 0) (hδ : ξ c' ≠ 0) (hξc : ξ (1 - c') ≠ 0) (hηc : η (1 - c') ≠ 0)
    (hne : ξ (1 - c') ≠ η (1 - c'))
    (t : { h : Equiv.Perm (ZMod q) // Function.Bijective (fun x => h x - ξ c' * x) } ×
      ZMod q × ZMod q × ZMod q) :
    Rone_build ξ η c' hδ hξc hηc hne t ∈
      fixSet ((graphRowSub (fun b j : Fin 2 => if b = 0 ∧ j = 1 then (0 : ZMod q) else 1) ξ η).map
        (sylowP q).subtype) := by
  let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 ∧ j = 1 then 0 else 1
  rintro _ ⟨g, hgH, rfl⟩
  change g.1 • Rone_build ξ η c' hδ hξc hηc hne t = Rone_build ξ η c' hδ hξc hηc hne t
  rw [sylow_fix_entry_iff]
  intro a b x y
  rcases (mem_graphRowSub_iff k ξ η g).mp hgH with ⟨gx, gy, hg⟩
  dsimp only [Rone_build]; rw [hg]; simp only [Equiv.symm_apply_apply, k]
  fin_cases a <;> fin_cases b <;> simp [hη'] <;> ring

private lemma Rone_build_sign {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) (ξ η : Fin 2 → ZMod q) (c' : Fin 2)
    (hη' : η c' = 0) (hδ : ξ c' ≠ 0) (hξc : ξ (1 - c') ≠ 0) (hηc : η (1 - c') ≠ 0)
    (hne : ξ (1 - c') ≠ η (1 - c'))
    (t : { h : Equiv.Perm (ZMod q) // Function.Bijective (fun x => h x - ξ c' * x) } ×
      ZMod q × ZMod q × ZMod q) :
    (squareSign (Rone_build ξ η c' hδ hξc hηc hne t) : ℤ) =
      (Equiv.Perm.sign t.1.1 : ℤ) *
      (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.1.1 x - ξ c' * x) t.1.2) : ℤ) *
      legendreSym q ((ξ (1 - c') * (ξ (1 - c') - η (1 - c'))).val : ℤ) := by
  have hq : q.Prime := Fact.out
  have hq_odd : Odd q := hq.odd_of_ne_two hodd
  let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 ∧ j = 1 then 0 else 1
  let H := graphRowSub k ξ η
  let c := 1 - c'
  let δ := ξ c'
  have hξmη : ξ c - η c ≠ 0 := sub_ne_zero.mpr hne
  have hmd : -δ ≠ 0 := neg_ne_zero.mpr hδ
  have hrow_mv : ∀ a : Fin 2, ∃ g ∈ H, (sylowToVec g).1 a ≠ 0 := fun a => by
    fin_cases a
    · exact ⟨vecToSylow (fun i => if i = 0 then 1 else 0, fun b => k b 0, fun c => ξ c),
        (mem_graphRowSub_iff k ξ η _).mpr ⟨1, 0, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
        by simp⟩
    · exact ⟨vecToSylow (fun i => if i = 0 then 0 else 1, fun b => k b 1, fun c => η c),
        (mem_graphRowSub_iff k ξ η _).mpr ⟨0, 1, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
        by simp⟩
  have hcol_mv : ∀ b : Fin 2, ∃ g ∈ H, (sylowToVec g).2.1 b ≠ 0 := fun b =>
    ⟨vecToSylow (fun i => if i = 0 then 1 else 0, fun b => k b 0, fun c => ξ c),
      (mem_graphRowSub_iff k ξ η _).mpr ⟨1, 0, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩,
      by fin_cases b <;> simp [k]⟩
  let B := Rone_build ξ η c' hδ hξc hηc hne t
  rw [squareSign_of_all_moving hodd H B (Rone_build_fix ξ η c' hη' hδ hξc hηc hne t) hrow_mv hcol_mv]
  let negP : Equiv.Perm (ZMod q) := Equiv.neg (ZMod q)
  let hδP : Equiv.Perm (ZMod q) := Equiv.ofBijective (fun x => t.1.1 x - δ * x) t.1.2
  have hfin2_c' : c' = 0 ∨ c' = 1 := fin2_cases c'
  have hr0 : (Equiv.Perm.sign (rowPerm B (blockEquiv q (0, 0))) : ℤ) =
      (if c' = 0 then (1 : ℤ) else -1) * (Equiv.Perm.sign t.1.1 : ℤ) *
        legendreSym q ((η c).val : ℤ) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then 1 else Equiv.swap 0 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun b =>
      if b = 0 then t.1.1 else (Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.1)
    have hp : rowPerm B (blockEquiv q (0, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro col
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (0, 0)) (blockEquiv q (b, y)) = _
      dsimp only [B, Rone_build, ϖ, φ, c]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases b with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, sub_zero, mul_zero, zero_add];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (((if ϖ = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = if c' = 0 then 1 else -1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [Units.val_mul, Units.val_mul, hϖ, show φ 0 = t.1.1 from rfl,
      show φ 1 = (Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.1) from rfl,
      sign_affine_zmod hodd]
  have hr1 : (Equiv.Perm.sign (rowPerm B (blockEquiv q (1, 0))) : ℤ) =
      (if c' = 0 then (-1 : ℤ) else 1) *
        legendreSym q ((ξ c).val : ℤ) * legendreSym q (δ.val : ℤ) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then Equiv.swap 0 1 else 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun b =>
      if b = 0 then (Equiv.mulLeft₀ (ξ c) hξc).trans (Equiv.addRight t.2.2.1)
      else (Equiv.mulLeft₀ δ hδ).trans (Equiv.addRight t.2.2.2)
    have hp : rowPerm B (blockEquiv q (1, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro col
      obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (1, 0)) (blockEquiv q (b, y)) = _
      dsimp only [B, Rone_build, ϖ, φ, c, δ]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases b with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, sub_zero, mul_zero, zero_add];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (((if ϖ = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = if c' = 0 then -1 else 1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [Units.val_mul, Units.val_mul, hϖ,
      show φ 0 = (Equiv.mulLeft₀ (ξ c) hξc).trans (Equiv.addRight t.2.2.1) from rfl,
      show φ 1 = (Equiv.mulLeft₀ δ hδ).trans (Equiv.addRight t.2.2.2) from rfl,
      sign_affine_zmod hodd, sign_affine_zmod hodd]
  have hc0 : (Equiv.Perm.sign (colPerm B (blockEquiv q (0, 0))) : ℤ) =
      (if c' = 0 then (1 : ℤ) else -1) *
        (Equiv.Perm.sign hδP : ℤ) * legendreSym q ((-1 : ZMod q).val : ℤ) *
        legendreSym q ((η c).val : ℤ) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then 1 else Equiv.swap 0 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun a =>
      if a = 0 then negP.trans hδP
      else (Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.2.1)
    have hp : colPerm B (blockEquiv q (0, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro r
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (a, x)) (blockEquiv q (0, 0)) = _
      dsimp only [B, Rone_build, ϖ, φ, negP, hδP, c, δ]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases a with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, Equiv.neg_apply,
          Equiv.ofBijective_apply, zero_sub];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (((if ϖ = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = if c' = 0 then 1 else -1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    have hneg_sign : (Equiv.Perm.sign negP : ℤ) = legendreSym q ((-1 : ZMod q).val : ℤ) := by
      have heq : negP = Equiv.mulLeft₀ (-1 : ZMod q) (by simp) := by ext x; simp [negP]
      rw [heq]; exact sign_mulLeft_eq_legendreSym hodd (Units.mk0 (-1) (by simp))
    have hφ0 : (Equiv.Perm.sign (φ 0) : ℤ) =
        (Equiv.Perm.sign hδP : ℤ) * legendreSym q ((-1 : ZMod q).val : ℤ) := by
      change (Equiv.Perm.sign (hδP * negP) : ℤ) = _
      rw [map_mul]; push_cast; rw [hneg_sign]
    rw [Units.val_mul, Units.val_mul, hϖ, hφ0,
      show φ 1 = (Equiv.mulLeft₀ (η c) hηc).trans (Equiv.addRight t.2.2.1) from rfl,
      sign_affine_zmod hodd]
    ring
  have hc1 : (Equiv.Perm.sign (colPerm B (blockEquiv q (1, 0))) : ℤ) =
      (if c' = 0 then (-1 : ℤ) else 1) *
        legendreSym q ((ξ c - η c).val : ℤ) * legendreSym q ((-δ).val : ℤ) := by
    let ϖ : Equiv.Perm (Fin 2) := if c' = 0 then Equiv.swap 0 1 else 1
    let φ : Fin 2 → Equiv.Perm (ZMod q) := fun a =>
      if a = 0 then (Equiv.mulLeft₀ (ξ c - η c) hξmη).trans (Equiv.addRight t.2.1)
      else (Equiv.mulLeft₀ (-δ) hmd).trans (Equiv.addRight t.2.2.2)
    have hp : colPerm B (blockEquiv q (1, 0)) = blockPerm q ϖ φ := by
      apply Equiv.Perm.ext; intro r
      obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
      rw [blockPerm_apply]
      change B.entry (blockEquiv q (a, x)) (blockEquiv q (1, 0)) = _
      dsimp only [B, Rone_build, ϖ, φ, c, δ]; simp only [Equiv.symm_apply_apply]
      rcases hfin2_c' with hc' | hc' <;> rcases fin2_cases a with rfl | rfl <;>
        (simp only [hc', Fin.isValue, and_true, and_false,
          ite_true, ite_false, one_ne_zero, zero_ne_one, Equiv.Perm.one_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.trans_apply,
          Equiv.mulLeft₀_apply, Equiv.coe_addRight, mul_zero];
         try exact congrArg (blockEquiv q) (Prod.ext rfl (by ring)))
    rw [hp, sign_blockPerm_eq hq_odd]
    have hϖ : (((if ϖ = 1 then (1 : ℤˣ) else -1) : ℤˣ) : ℤ) = if c' = 0 then -1 else 1 := by
      dsimp only [ϖ]; rcases hfin2_c' with hc' | hc' <;> (simp [hc']; try decide)
    rw [Units.val_mul, Units.val_mul, hϖ,
      show φ 0 = (Equiv.mulLeft₀ (ξ c - η c) hξmη).trans (Equiv.addRight t.2.1) from rfl,
      show φ 1 = (Equiv.mulLeft₀ (-δ) hmd).trans (Equiv.addRight t.2.2.2) from rfl,
      sign_affine_zmod hodd, sign_affine_zmod hodd]
  push_cast
  rw [hr0, hr1, hc0, hc1]
  have hsq_η : legendreSym q ((η c).val : ℤ) * legendreSym q ((η c).val : ℤ) = 1 := by
    rw [← sq]; exact legendreSym.sq_one q (by simpa using hηc)
  have hsq_δ : legendreSym q (δ.val : ℤ) * legendreSym q ((-1 : ZMod q).val : ℤ) *
      legendreSym q ((-δ).val : ℤ) = 1 := by
    rw [← legendreSym_val_mul, ← legendreSym_val_mul]
    have : δ * (-1) * (-δ) = δ * δ := by ring
    rw [this, legendreSym_val_mul, ← sq]
    exact legendreSym.sq_one q (by simpa using hδ)
  rw [legendreSym_val_mul (ξ c) (ξ c - η c)]
  have hite_prod :
      (if c' = 0 then (1 : ℤ) else -1) * (if c' = 0 then (-1 : ℤ) else 1) *
      (if c' = 0 then (1 : ℤ) else -1) * (if c' = 0 then (-1 : ℤ) else 1) = 1 := by
    rcases hfin2_c' with hc' | hc' <;> simp [hc']
  calc _ = ((if c' = 0 then (1 : ℤ) else -1) * (if c' = 0 then (-1 : ℤ) else 1) *
        (if c' = 0 then (1 : ℤ) else -1) * (if c' = 0 then (-1 : ℤ) else 1)) *
        (Equiv.Perm.sign t.1.1 : ℤ) * (Equiv.Perm.sign hδP : ℤ) *
        (legendreSym q ((ξ c).val : ℤ) * legendreSym q ((ξ c - η c).val : ℤ)) *
        (legendreSym q ((η c).val : ℤ) * legendreSym q ((η c).val : ℤ)) *
        (legendreSym q (δ.val : ℤ) * legendreSym q ((-1 : ZMod q).val : ℤ) *
          legendreSym q ((-δ).val : ℤ)) := by ring
    _ = _ := by rw [hite_prod, hsq_η, hsq_δ]; ring

/-- Normalized `R_one` sum (for `k = [[1, 0], [1, 1]]`):
`∑_{ξ, η} S(H) = -2 * q^3 * (q - 1)^2 * tauQ q`. -/
lemma sum_Rone_norm {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    let k : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 ∧ j = 1 then 0 else 1
    ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q, S_twoq q (graphRowSub k ξ η) =
      -2 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 2 * tauQ q := by
  classical
  intro k
  have hq : q.Prime := Fact.out
  have hS : ∀ ξ η : Fin 2 → ZMod q,
      S_twoq q (graphRowSub k ξ η) =
      ∑ c' : Fin 2,
        let c := 1 - c'
        if η c' = 0 ∧ ξ c' ≠ 0 ∧ ξ c ≠ 0 ∧ η c ≠ 0 ∧ ξ c ≠ η c then
          (q : ℤ) ^ 3 * tauQ q * legendreSym q ((ξ c * (ξ c - η c)).val : ℤ)
        else 0 := by
    intro ξ η
    let H := graphRowSub k ξ η
    have hL_prop := Rone_L_prop ξ η
    -- Split `S_twoq q H` by `c' ∈ Fin 2`
    unfold S_twoq signedFixSum
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Fin 2)))
      (g := fun L : LatinSquare (2 * q) =>
        ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c' _ => ?_
    dsimp only
    let c := 1 - c'
    change _ = if η c' = 0 ∧ ξ c' ≠ 0 ∧ ξ c ≠ 0 ∧ η c ≠ 0 ∧ ξ c ≠ η c then
      (q : ℤ) ^ 3 * tauQ q * legendreSym q ((ξ c * (ξ c - η c)).val : ℤ) else 0
    split_ifs with hcond
    · rcases hcond with ⟨hη', hδ, hξc, hηc, hne⟩
      let δ := ξ c'
      let H00 := { h : Equiv.Perm (ZMod q) // Function.Bijective (fun x => h x - δ * x) }
      let build := Rone_build ξ η c' hδ hξc hηc hne
      have hbuild_fix : ∀ t, build t ∈ fixSet (H.map (sylowP q).subtype) :=
        Rone_build_fix ξ η c' hη' hδ hξc hηc hne
      have hbuild_sign : ∀ t,
          (squareSign (build t) : ℤ) =
            (Equiv.Perm.sign t.1.1 : ℤ) *
            (Equiv.Perm.sign (Equiv.ofBijective (fun x => t.1.1 x - δ * x) t.1.2) : ℤ) *
            legendreSym q ((ξ c * (ξ c - η c)).val : ℤ) :=
        Rone_build_sign hodd ξ η c' hη' hδ hξc hηc hne
      -- Bijection between fiber and `H00 × ZMod q × ZMod q × ZMod q`
      have hbij :
          (∑ L ∈ (Finset.univ.filter (fun L : LatinSquare (2 * q) =>
              L ∈ fixSet (H.map (sylowP q).subtype))).filter
              (fun L => ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, 0)))).1 = c'),
            (squareSign L : ℤ)) =
          ∑ t : H00 × ZMod q × ZMod q × ZMod q, (squareSign (build t) : ℤ) := by
        symm
        refine Finset.sum_bij (fun t _ => build t) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro t _
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbuild_fix t⟩, ?_⟩
          simp [build, Rone_build]
        · intro t₁ _ t₂ _ hEq
          have hh : t₁.1 = t₂.1 := by
            apply Subtype.ext; apply Equiv.Perm.ext; intro y
            have h := congrArg (fun M => M.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y))) hEq
            simp only [build, Rone_build, Equiv.symm_apply_apply, ↓reduceIte, mul_zero, zero_add,
              sub_zero] at h
            exact congrArg Prod.snd ((blockEquiv q).injective h)
          have h01 : t₁.2.1 = t₂.2.1 := by
            have h := congrArg (fun M => M.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0))) hEq
            simp only [build, Rone_build, Equiv.symm_apply_apply, Fin.isValue, zero_ne_one, and_false,
              ↓reduceIte, and_self, mul_zero, add_zero] at h
            exact congrArg Prod.snd ((blockEquiv q).injective h)
          have h10 : t₁.2.2.1 = t₂.2.2.1 := by
            have h := congrArg (fun M => M.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0))) hEq
            simp only [build, Rone_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, false_and,
              ↓reduceIte, and_self, mul_zero, add_zero] at h
            exact congrArg Prod.snd ((blockEquiv q).injective h)
          have h11 : t₁.2.2.2 = t₂.2.2.2 := by
            have h := congrArg (fun M => M.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0))) hEq
            simp only [build, Rone_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, false_and,
              ↓reduceIte, and_false, mul_zero, add_zero] at h
            exact (Prod.mk.inj ((blockEquiv q).injective h)).2
          exact Prod.ext hh (Prod.ext h01 (Prod.ext h10 h11))
        · intro L hL
          have hLfix := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
          have hLc' := (Finset.mem_filter.mp hL).2
          have hp := hL_prop L hLfix
          rw [hLc'] at hp
          let hfun : ZMod q → ZMod q := fun d =>
            ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)))).2
          have hh_bij : Function.Bijective hfun := by
            rw [← Finite.injective_iff_bijective]
            intro y₁ y₂ hEq
            have hb1 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₁)))).1 = c' := by
              have := hp.2.2.2.2.2.2.2.2 0 y₁; rw [this, Equiv.symm_apply_apply]
            have hb2 : ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₂)))).1 = c' := by
              have := hp.2.2.2.2.2.2.2.2 0 y₂; rw [this, Equiv.symm_apply_apply]
            have he : L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₁)) =
                L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, y₂)) :=
              (blockEquiv q).symm.injective (Prod.ext (hb1.trans hb2.symm) hEq)
            exact congrArg Prod.snd ((blockEquiv q).injective ((L.row_bijective _).1 he))
          have hhδ_bij : Function.Bijective (fun d => Equiv.ofBijective hfun hh_bij d - δ * d) := by
            rw [← Finite.injective_iff_bijective]
            intro d₁ d₂ hEq
            have he1 := hp.2.2.2.2.2.2.2.2 (-d₁) 0
            have he2 := hp.2.2.2.2.2.2.2.2 (-d₂) 0
            have hsub1 : (0 : ZMod q) - -d₁ = d₁ := by ring
            have hsub2 : (0 : ZMod q) - -d₂ = d₂ := by ring
            rw [hsub1] at he1; rw [hsub2] at he2
            have he : L.entry (blockEquiv q (0, -d₁)) (blockEquiv q (0, 0)) =
                L.entry (blockEquiv q (0, -d₂)) (blockEquiv q (0, 0)) := by
              rw [he1, he2]; congr 1; refine Prod.ext rfl ?_
              simp only [Equiv.ofBijective_apply] at hEq
              change δ * -d₁ + hfun d₁ = δ * -d₂ + hfun d₂
              linear_combination hEq
            have hneg := congrArg Prod.snd ((blockEquiv q).injective ((L.col_bijective _).1 he))
            exact neg_injective hneg
          let t : H00 × ZMod q × ZMod q × ZMod q :=
            (⟨Equiv.ofBijective hfun hh_bij, hhδ_bij⟩,
             ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (1, 0)))).2,
             ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (0, 0)))).2,
             ((blockEquiv q).symm (L.entry (blockEquiv q (1, 0)) (blockEquiv q (1, 0)))).2)
          refine ⟨t, Finset.mem_univ _, ?_⟩
          apply LatinSquare.ext; funext r col
          obtain ⟨⟨a, x⟩, rfl⟩ := (blockEquiv q).surjective r
          obtain ⟨⟨b, y⟩, rfl⟩ := (blockEquiv q).surjective col
          fin_cases a <;> fin_cases b
          · simp only [build, Rone_build, Equiv.symm_apply_apply, ↓reduceIte, t,
              Equiv.ofBijective_apply, hfun, δ]
            exact (hp.2.2.2.2.2.2.2.2 x y).symm
          · simp only [build, Rone_build, Equiv.symm_apply_apply, Fin.isValue, zero_ne_one, and_false,
              ↓reduceIte, and_self, t]
            exact (hp.2.2.2.2.2.1 x y).symm
          · simp only [build, Rone_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, false_and,
              ↓reduceIte, and_self, t]
            exact (hp.2.2.2.2.2.2.1 x y).symm
          · simp only [build, Rone_build, Equiv.symm_apply_apply, Fin.isValue, one_ne_zero, false_and,
              ↓reduceIte, and_false, t, δ]
            exact (hp.2.2.2.2.2.2.2.1 x y).symm
      rw [hbij]
      simp_rw [hbuild_sign]
      rw [Fintype.sum_prod_type]
      have hinner_t : ∀ h : H00,
          (∑ _x : ZMod q × ZMod q × ZMod q,
            (Equiv.Perm.sign h.1 : ℤ) *
              (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - δ * x) h.2) : ℤ) *
              legendreSym q ((ξ c * (ξ c - η c)).val : ℤ)) =
          ((q * (q * q) : ℕ) : ℤ) *
            ((Equiv.Perm.sign h.1 : ℤ) *
              (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - δ * x) h.2) : ℤ) *
              legendreSym q ((ξ c * (ξ c - η c)).val : ℤ)) := fun h => by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card,
          nsmul_eq_mul]
      simp_rw [hinner_t, ← Finset.mul_sum, ← Finset.sum_mul]
      have htau := (lem_6_5_complete q hq hodd).2.2 δ hδ
      rw [htau]
      push_cast; ring
    · refine Finset.sum_eq_zero fun L hL => ?_
      exfalso
      have hLfix := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2
      have hLc' := (Finset.mem_filter.mp hL).2
      have hp := hL_prop L hLfix
      rw [hLc'] at hp
      exact hcond ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩
  simp_rw [hS]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 2 → ZMod q)))
    (t := (Finset.univ : Finset (Fin 2)))]
  -- Each of the 2 choices of `c' ∈ Fin 2` contributes `-(q - 1)^2 * q^3 * tauQ q`
  have hbranch_sum : ∀ c' : Fin 2,
      (∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q,
        if η c' = 0 ∧ ξ c' ≠ 0 ∧ ξ (1 - c') ≠ 0 ∧ η (1 - c') ≠ 0 ∧ ξ (1 - c') ≠ η (1 - c')
        then (q : ℤ) ^ 3 * tauQ q * legendreSym q ((ξ (1 - c') * (ξ (1 - c') - η (1 - c'))).val : ℤ)
        else 0) =
      -((q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 2 * tauQ q) := by
    intro c'
    let c := 1 - c'
    let e : (Fin 2 → ZMod q) × (Fin 2 → ZMod q) ≃ (ZMod q × ZMod q) × (ZMod q × ZMod q) :=
      { toFun := fun p => ((p.1 c', p.2 c'), (p.1 c, p.2 c))
        invFun := fun t => (fun i => if i = c' then t.1.1 else t.2.1,
                            fun i => if i = c' then t.1.2 else t.2.2)
        left_inv := fun p => Prod.ext (funext fun i => by fin_cases c' <;> fin_cases i <;> rfl)
          (funext fun i => by fin_cases c' <;> fin_cases i <;> rfl)
        right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => by fin_cases c' <;> rfl }
    rw [← Fintype.sum_prod_type', ← Equiv.sum_comp e.symm]
    have hsim : ∀ t : (ZMod q × ZMod q) × (ZMod q × ZMod q),
        (if (e.symm t).2 c' = 0 ∧ (e.symm t).1 c' ≠ 0 ∧ (e.symm t).1 (1 - c') ≠ 0 ∧
            (e.symm t).2 (1 - c') ≠ 0 ∧ (e.symm t).1 (1 - c') ≠ (e.symm t).2 (1 - c')
         then (q : ℤ) ^ 3 * tauQ q *
            legendreSym q (((e.symm t).1 (1 - c') * ((e.symm t).1 (1 - c') - (e.symm t).2 (1 - c'))).val : ℤ)
         else 0) =
        (if t.1.2 = 0 ∧ t.1.1 ≠ 0 then (q : ℤ) ^ 3 * tauQ q else 0) *
        (if t.2.2 ≠ 0 then legendreSym q ((t.2.1 * (t.2.1 - t.2.2)).val : ℤ) else 0) := by
      intro ⟨⟨a, b⟩, ⟨u, v⟩⟩
      have he1 : (e.symm ((a, b), (u, v))).1 c' = a := by fin_cases c' <;> rfl
      have he2 : (e.symm ((a, b), (u, v))).2 c' = b := by fin_cases c' <;> rfl
      have he3 : (e.symm ((a, b), (u, v))).1 (1 - c') = u := by fin_cases c' <;> rfl
      have he4 : (e.symm ((a, b), (u, v))).2 (1 - c') = v := by fin_cases c' <;> rfl
      rw [he1, he2, he3, he4]
      by_cases h1 : b = 0 ∧ a ≠ 0
      · by_cases hv : v ≠ 0
        · by_cases hu : u = 0
          · subst hu
            rw [if_neg (by simp), if_pos h1, if_pos hv]
            have hz : ((0 : ZMod q) * (0 - v)).val = 0 := by simp
            rw [hz, Nat.cast_zero, legendreSym.at_zero, mul_zero]
          · by_cases huv : u = v
            · subst huv
              rw [if_neg (by simp), if_pos h1, if_pos hv]
              have hz : (u * (u - u)).val = 0 := by simp
              rw [hz, Nat.cast_zero, legendreSym.at_zero, mul_zero]
            · rw [if_pos ⟨h1.1, h1.2, hu, hv, huv⟩, if_pos h1, if_pos hv]
        · rw [if_neg (fun h => hv h.2.2.2.1), if_neg hv, mul_zero]
      · rw [if_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg h1, zero_mul]
    simp_rw [hsim]
    rw [Fintype.sum_prod_type]
    have hinner_sum : ∀ p : ZMod q × ZMod q,
        (∑ r : ZMod q × ZMod q,
          (if p.2 = 0 ∧ p.1 ≠ 0 then (q : ℤ) ^ 3 * tauQ q else 0) *
          (if r.2 ≠ 0 then legendreSym q ((r.1 * (r.1 - r.2)).val : ℤ) else 0)) =
        (if p.2 = 0 ∧ p.1 ≠ 0 then (q : ℤ) ^ 3 * tauQ q else 0) * -((q : ℤ) - 1) := fun p => by
      rw [← Finset.mul_sum, sum_chi_xi_sub_eta hodd]
    simp_rw [hinner_sum, ← Finset.sum_mul]
    have hfirst :
        (∑ p : ZMod q × ZMod q, if p.2 = 0 ∧ p.1 ≠ 0 then (q : ℤ) ^ 3 * tauQ q else 0) =
        ((q : ℤ) - 1) * ((q : ℤ) ^ 3 * tauQ q) := by
      rw [Fintype.sum_prod_type]
      have hrow : ∀ a : ZMod q,
          (∑ b : ZMod q, if b = 0 ∧ a ≠ 0 then (q : ℤ) ^ 3 * tauQ q else 0) =
          if a ≠ 0 then (q : ℤ) ^ 3 * tauQ q else 0 := by
        intro a
        by_cases ha : a ≠ 0
        · simp [ha]
        · rw [if_neg ha]
          refine Finset.sum_eq_zero fun b _ => if_neg (fun h => ha h.2)
      simp_rw [hrow, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.univ : Finset (ZMod q)).filter (fun a => a ≠ 0)).card = q - 1 := by
        have : (Finset.univ : Finset (ZMod q)).filter (fun a => a ≠ 0) = Finset.univ.erase 0 := by
          ext x; simp
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
      rw [hcard]
      have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := hq.pos; omega
      rw [hcast]
    rw [hfirst]
    ring
  rw [Finset.sum_congr rfl fun c' _ => hbranch_sum c']
  rw [Fin.sum_univ_two]
  ring

end AlonTarsi.Proofs

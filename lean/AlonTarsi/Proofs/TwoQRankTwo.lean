/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Proofs.TwoQRankTwoHelpers
import Mathlib.NumberTheory.Wilson

/-!
# Section 6 (Lemma 6.6): Rank-2 Classification and Divisibility by `q^5`

This file classifies all rank-2 subgroups of `sylowP q`, reduces every non-vanishing family
to the five normalized representatives computed in `TwoQRankTwoHelpers.lean`, proves the
exact formula for `∑_{r(H)=2} S(H)` and its divisibility by `q^5`, and assembles
`AlonTarsi.Proofs.lem_6_6_vanish`.
-/

namespace AlonTarsi.Proofs

open scoped BigOperators
open AlonTarsi

section RankTwoClassification

/-! ### Normalizer Isotopies and `sumGraphRow` Invariance -/

/-- Row block rescaling isotopy. -/
private def rowScaleIso (q : ℕ) [NeZero q] (a₀ : Fin 2) (lam : (ZMod q)ˣ) : Isotopy (2 * q) :=
  (blockScalePerm q a₀ lam, 1, 1)

/-- Column block rescaling isotopy. -/
private def colScaleIso (q : ℕ) [NeZero q] (b₀ : Fin 2) (lam : (ZMod q)ˣ) : Isotopy (2 * q) :=
  (1, blockScalePerm q b₀ lam, 1)

/-- Row block swap isotopy. -/
private def rowSwapIso (q : ℕ) [NeZero q] : Isotopy (2 * q) :=
  (blockSwapPerm q, 1, 1)

/-- Column block swap isotopy. -/
private def colSwapIso (q : ℕ) [NeZero q] : Isotopy (2 * q) :=
  (1, blockSwapPerm q, 1)

private lemma rowScaleIso_conj_mem {q : ℕ} [NeZero q] (a₀ : Fin 2) (lam : (ZMod q)ˣ)
    (g : Isotopy (2 * q)) (hg : g ∈ sylowP q) :
    rowScaleIso q a₀ lam * g * (rowScaleIso q a₀ lam)⁻¹ ∈ sylowP q := by
  rcases hg with ⟨v, rfl⟩
  let w := Multiplicative.toAdd v
  refine ⟨Multiplicative.ofAdd (fun a => if a = a₀ then lam.1 * w.1 a else w.1 a, w.2.1, w.2.2), ?_⟩
  change (blockTransPerm q (fun a => if a = a₀ then lam.1 * w.1 a else w.1 a),
      blockTransPerm q w.2.1, blockTransPerm q w.2.2) =
    (blockScalePerm q a₀ lam * blockTransPerm q w.1 * (blockScalePerm q a₀ lam)⁻¹,
     1 * blockTransPerm q w.2.1 * 1⁻¹, 1 * blockTransPerm q w.2.2 * 1⁻¹)
  simp [blockScalePerm_conj_blockTransPerm]

private lemma colScaleIso_conj_mem {q : ℕ} [NeZero q] (b₀ : Fin 2) (lam : (ZMod q)ˣ)
    (g : Isotopy (2 * q)) (hg : g ∈ sylowP q) :
    colScaleIso q b₀ lam * g * (colScaleIso q b₀ lam)⁻¹ ∈ sylowP q := by
  rcases hg with ⟨v, rfl⟩
  let w := Multiplicative.toAdd v
  refine ⟨Multiplicative.ofAdd (w.1, fun b => if b = b₀ then lam.1 * w.2.1 b else w.2.1 b, w.2.2), ?_⟩
  change (blockTransPerm q w.1,
      blockTransPerm q (fun b => if b = b₀ then lam.1 * w.2.1 b else w.2.1 b),
      blockTransPerm q w.2.2) =
    (1 * blockTransPerm q w.1 * 1⁻¹,
     blockScalePerm q b₀ lam * blockTransPerm q w.2.1 * (blockScalePerm q b₀ lam)⁻¹,
     1 * blockTransPerm q w.2.2 * 1⁻¹)
  simp [blockScalePerm_conj_blockTransPerm]

private lemma rowSwapIso_conj_mem {q : ℕ} [NeZero q]
    (g : Isotopy (2 * q)) (hg : g ∈ sylowP q) :
    rowSwapIso q * g * (rowSwapIso q)⁻¹ ∈ sylowP q := by
  rcases hg with ⟨v, rfl⟩
  let w := Multiplicative.toAdd v
  refine ⟨Multiplicative.ofAdd (fun a => w.1 (1 - a), w.2.1, w.2.2), ?_⟩
  change (blockTransPerm q (fun a => w.1 (1 - a)), blockTransPerm q w.2.1, blockTransPerm q w.2.2) =
    (blockSwapPerm q * blockTransPerm q w.1 * (blockSwapPerm q)⁻¹,
     1 * blockTransPerm q w.2.1 * 1⁻¹, 1 * blockTransPerm q w.2.2 * 1⁻¹)
  simp [blockSwapPerm_conj_blockTransPerm]

private lemma colSwapIso_conj_mem {q : ℕ} [NeZero q]
    (g : Isotopy (2 * q)) (hg : g ∈ sylowP q) :
    colSwapIso q * g * (colSwapIso q)⁻¹ ∈ sylowP q := by
  rcases hg with ⟨v, rfl⟩
  let w := Multiplicative.toAdd v
  refine ⟨Multiplicative.ofAdd (w.1, fun b => w.2.1 (1 - b), w.2.2), ?_⟩
  change (blockTransPerm q w.1, blockTransPerm q (fun b => w.2.1 (1 - b)), blockTransPerm q w.2.2) =
    (1 * blockTransPerm q w.1 * 1⁻¹,
     blockSwapPerm q * blockTransPerm q w.2.1 * (blockSwapPerm q)⁻¹,
     1 * blockTransPerm q w.2.2 * 1⁻¹)
  simp [blockSwapPerm_conj_blockTransPerm]

private lemma sylowToVec_conj_rowScaleIso {q : ℕ} [NeZero q] (a₀ : Fin 2) (lam : (ZMod q)ˣ)
    (g : sylowP q) :
    sylowToVec ⟨rowScaleIso q a₀ lam * g.1 * (rowScaleIso q a₀ lam)⁻¹,
      rowScaleIso_conj_mem a₀ lam g.1 g.2⟩ =
    (fun a => if a = a₀ then lam.1 * (sylowToVec g).1 a else (sylowToVec g).1 a,
     (sylowToVec g).2.1, (sylowToVec g).2.2) := by
  refine Eq.trans ?_ (sylowToVec_vecToSylow _)
  congr 1
  have hv := sylowToVec_val g
  apply Subtype.ext
  change rowScaleIso q a₀ lam * g.1 * (rowScaleIso q a₀ lam)⁻¹ =
    (vecToSylow (fun a => if a = a₀ then lam.1 * (sylowToVec g).1 a else (sylowToVec g).1 a,
      (sylowToVec g).2.1, (sylowToVec g).2.2)).1
  rw [vecToSylow_val, hv]
  change (blockScalePerm q a₀ lam * blockTransPerm q (sylowToVec g).1 * (blockScalePerm q a₀ lam)⁻¹,
      1 * blockTransPerm q (sylowToVec g).2.1 * 1⁻¹,
      1 * blockTransPerm q (sylowToVec g).2.2 * 1⁻¹) = _
  simp [sylowHom, blockScalePerm_conj_blockTransPerm]

private lemma sylowToVec_conj_colScaleIso {q : ℕ} [NeZero q] (b₀ : Fin 2) (lam : (ZMod q)ˣ)
    (g : sylowP q) :
    sylowToVec ⟨colScaleIso q b₀ lam * g.1 * (colScaleIso q b₀ lam)⁻¹,
      colScaleIso_conj_mem b₀ lam g.1 g.2⟩ =
    ((sylowToVec g).1,
     fun b => if b = b₀ then lam.1 * (sylowToVec g).2.1 b else (sylowToVec g).2.1 b,
     (sylowToVec g).2.2) := by
  refine Eq.trans ?_ (sylowToVec_vecToSylow _)
  congr 1
  have hv := sylowToVec_val g
  apply Subtype.ext
  change colScaleIso q b₀ lam * g.1 * (colScaleIso q b₀ lam)⁻¹ =
    (vecToSylow ((sylowToVec g).1,
      fun b => if b = b₀ then lam.1 * (sylowToVec g).2.1 b else (sylowToVec g).2.1 b,
      (sylowToVec g).2.2)).1
  rw [vecToSylow_val, hv]
  change (1 * blockTransPerm q (sylowToVec g).1 * 1⁻¹,
      blockScalePerm q b₀ lam * blockTransPerm q (sylowToVec g).2.1 * (blockScalePerm q b₀ lam)⁻¹,
      1 * blockTransPerm q (sylowToVec g).2.2 * 1⁻¹) = _
  simp [sylowHom, blockScalePerm_conj_blockTransPerm]

private lemma sylowToVec_conj_rowSwapIso {q : ℕ} [NeZero q] (g : sylowP q) :
    sylowToVec ⟨rowSwapIso q * g.1 * (rowSwapIso q)⁻¹, rowSwapIso_conj_mem g.1 g.2⟩ =
    (fun a => (sylowToVec g).1 (1 - a), (sylowToVec g).2.1, (sylowToVec g).2.2) := by
  refine Eq.trans ?_ (sylowToVec_vecToSylow _)
  congr 1
  have hv := sylowToVec_val g
  apply Subtype.ext
  change rowSwapIso q * g.1 * (rowSwapIso q)⁻¹ =
    (vecToSylow (fun a => (sylowToVec g).1 (1 - a), (sylowToVec g).2.1, (sylowToVec g).2.2)).1
  rw [vecToSylow_val, hv]
  change (blockSwapPerm q * blockTransPerm q (sylowToVec g).1 * (blockSwapPerm q)⁻¹,
      1 * blockTransPerm q (sylowToVec g).2.1 * 1⁻¹,
      1 * blockTransPerm q (sylowToVec g).2.2 * 1⁻¹) = _
  simp [sylowHom, blockSwapPerm_conj_blockTransPerm]

private lemma sylowToVec_conj_colSwapIso {q : ℕ} [NeZero q] (g : sylowP q) :
    sylowToVec ⟨colSwapIso q * g.1 * (colSwapIso q)⁻¹, colSwapIso_conj_mem g.1 g.2⟩ =
    ((sylowToVec g).1, fun b => (sylowToVec g).2.1 (1 - b), (sylowToVec g).2.2) := by
  refine Eq.trans ?_ (sylowToVec_vecToSylow _)
  congr 1
  have hv := sylowToVec_val g
  apply Subtype.ext
  change colSwapIso q * g.1 * (colSwapIso q)⁻¹ =
    (vecToSylow ((sylowToVec g).1, fun b => (sylowToVec g).2.1 (1 - b), (sylowToVec g).2.2)).1
  rw [vecToSylow_val, hv]
  change (1 * blockTransPerm q (sylowToVec g).1 * 1⁻¹,
      blockSwapPerm q * blockTransPerm q (sylowToVec g).2.1 * (blockSwapPerm q)⁻¹,
      1 * blockTransPerm q (sylowToVec g).2.2 * 1⁻¹) = _
  simp [sylowHom, blockSwapPerm_conj_blockTransPerm]

/-- Every `graphR11Sub r s ξ η` has the same `S_twoq` as `graphR11Sub 1 1 ξ η`. -/
private lemma S_twoq_graphR11Sub_eq_norm {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (r s : (ZMod q)ˣ) (ξ η : Fin 2 → ZMod q) :
    S_twoq q (graphR11Sub r s ξ η) = S_twoq q (graphR11Sub 1 1 ξ η) := by
  have h1 : conjSylowSub (rowScaleIso q 1 r⁻¹) (rowScaleIso_conj_mem 1 r⁻¹)
      (graphR11Sub r s ξ η) = graphR11Sub 1 s ξ η := by
    ext g
    simp only [conjSylowSub, Subgroup.mem_map, MonoidHom.coe_mk, OneHom.coe_mk,
      mem_graphR11Sub_iff]
    constructor
    · rintro ⟨h, ⟨x, y, hv⟩, rfl⟩
      refine ⟨x, y, ?_⟩
      rw [sylowToVec_conj_rowScaleIso, hv]
      refine Prod.ext (funext fun i => by
        fin_cases i
        · simp
        · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Units.val_one, one_mul]
          rw [← mul_assoc, Units.inv_mul, one_mul]) rfl
    · rintro ⟨x, y, hv⟩
      refine ⟨vecToSylow (fun a => if a = 0 then x else r.1 * x,
          fun b => if b = 0 then y else s.1 * y, fun c => ξ c * x + η c * y),
        ⟨x, y, sylowToVec_vecToSylow _⟩, ?_⟩
      apply sylowToVec_injective
      rw [sylowToVec_conj_rowScaleIso, sylowToVec_vecToSylow, hv]
      refine Prod.ext (funext fun i => by
        fin_cases i
        · simp
        · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Units.val_one, one_mul]
          rw [← mul_assoc, Units.inv_mul, one_mul]) rfl
  have h2 : conjSylowSub (colScaleIso q 1 s⁻¹) (colScaleIso_conj_mem 1 s⁻¹)
      (graphR11Sub 1 s ξ η) = graphR11Sub 1 1 ξ η := by
    ext g
    simp only [conjSylowSub, Subgroup.mem_map, MonoidHom.coe_mk, OneHom.coe_mk,
      mem_graphR11Sub_iff]
    constructor
    · rintro ⟨h, ⟨x, y, hv⟩, rfl⟩
      refine ⟨x, y, ?_⟩
      rw [sylowToVec_conj_colScaleIso, hv]
      refine Prod.ext rfl (Prod.ext (funext fun i => by
        fin_cases i
        · simp
        · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Units.val_one, one_mul]
          rw [← mul_assoc, Units.inv_mul, one_mul]) rfl)
    · rintro ⟨x, y, hv⟩
      refine ⟨vecToSylow (fun a => if a = 0 then x else (1 : (ZMod q)ˣ).1 * x,
          fun b => if b = 0 then y else s.1 * y, fun c => ξ c * x + η c * y),
        ⟨x, y, sylowToVec_vecToSylow _⟩, ?_⟩
      apply sylowToVec_injective
      rw [sylowToVec_conj_colScaleIso, sylowToVec_vecToSylow, hv]
      refine Prod.ext rfl (Prod.ext (funext fun i => by
        fin_cases i
        · simp
        · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Units.val_one, one_mul]
          rw [← mul_assoc, Units.inv_mul, one_mul]) rfl)
  rw [← S_twoq_conjSylowSub hodd (rowScaleIso q 1 r⁻¹) (rowScaleIso_conj_mem 1 r⁻¹), h1,
      ← S_twoq_conjSylowSub hodd (colScaleIso q 1 s⁻¹) (colScaleIso_conj_mem 1 s⁻¹), h2]

/-- Sum of `S(graphRowSub k ξ η)` over all symbol characters `(ξ, η)`. -/
private noncomputable def sumGraphRow (q : ℕ) [NeZero q] (k : Fin 2 → Fin 2 → ZMod q) : ℤ :=
  ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q, S_twoq q (graphRowSub k ξ η)

private lemma sumGraphRow_scale_row {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q) (b₀ : Fin 2) (u : (ZMod q)ˣ) :
    sumGraphRow q (fun b j => if b = b₀ then u.1 * k b j else k b j) = sumGraphRow q k := by
  unfold sumGraphRow
  refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
  symm
  rw [← S_twoq_conjSylowSub hodd (colScaleIso q b₀ u) (colScaleIso_conj_mem b₀ u)]
  congr 1
  ext g
  simp only [conjSylowSub, Subgroup.mem_map, MonoidHom.coe_mk, OneHom.coe_mk,
    mem_graphRowSub_iff]
  constructor
  · rintro ⟨h, ⟨x, y, hv⟩, rfl⟩
    refine ⟨x, y, ?_⟩
    rw [sylowToVec_conj_colScaleIso, hv]
    refine Prod.ext rfl (Prod.ext (funext fun b => ?_) rfl)
    dsimp only; split_ifs <;> ring
  · rintro ⟨x, y, hv⟩
    refine ⟨vecToSylow (fun a => if a = 0 then x else y,
        fun b => k b 0 * x + k b 1 * y, fun c => ξ c * x + η c * y),
      ⟨x, y, sylowToVec_vecToSylow _⟩, ?_⟩
    apply sylowToVec_injective
    rw [sylowToVec_conj_colScaleIso, sylowToVec_vecToSylow, hv]
    refine Prod.ext rfl (Prod.ext (funext fun b => ?_) rfl)
    dsimp only; split_ifs <;> ring

private lemma sumGraphRow_swap_row {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q) :
    sumGraphRow q (fun b j => k (1 - b) j) = sumGraphRow q k := by
  unfold sumGraphRow
  refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
  symm
  rw [← S_twoq_conjSylowSub hodd (colSwapIso q) colSwapIso_conj_mem]
  congr 1
  ext g
  simp only [conjSylowSub, Subgroup.mem_map, MonoidHom.coe_mk, OneHom.coe_mk,
    mem_graphRowSub_iff]
  constructor
  · rintro ⟨h, ⟨x, y, hv⟩, rfl⟩
    refine ⟨x, y, ?_⟩
    rw [sylowToVec_conj_colSwapIso, hv]
  · rintro ⟨x, y, hv⟩
    refine ⟨vecToSylow (fun a => if a = 0 then x else y,
        fun b => k b 0 * x + k b 1 * y, fun c => ξ c * x + η c * y),
      ⟨x, y, sylowToVec_vecToSylow _⟩, ?_⟩
    apply sylowToVec_injective
    rw [sylowToVec_conj_colSwapIso, sylowToVec_vecToSylow, hv]

private lemma sumGraphRow_scale_col {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q) (j₀ : Fin 2) (u : (ZMod q)ˣ) :
    sumGraphRow q (fun b j => if j = j₀ then u.1 * k b j else k b j) = sumGraphRow q k := by
  unfold sumGraphRow
  have hconj : ∀ ξ η : Fin 2 → ZMod q,
      conjSylowSub (rowScaleIso q j₀ u⁻¹) (rowScaleIso_conj_mem j₀ u⁻¹) (graphRowSub k ξ η) =
      graphRowSub (fun b j => if j = j₀ then u.1 * k b j else k b j)
        (if j₀ = 0 then fun c => u.1 * ξ c else ξ)
        (if j₀ = 1 then fun c => u.1 * η c else η) := by
    intro ξ η
    ext g
    simp only [conjSylowSub, Subgroup.mem_map, MonoidHom.coe_mk, OneHom.coe_mk,
      mem_graphRowSub_iff]
    constructor
    · rintro ⟨h, ⟨x, y, hv⟩, rfl⟩
      rcases (by fin_cases j₀ <;> simp : j₀ = 0 ∨ j₀ = 1) with rfl | rfl
      · refine ⟨(u⁻¹).1 * x, y, ?_⟩
        rw [sylowToVec_conj_rowScaleIso, hv]
        refine Prod.ext (funext fun a => by
            fin_cases a <;> simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero])
          (Prod.ext (funext fun b => by
            simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
            have : u.1 * k b 0 * ((u⁻¹).1 * x) = (u.1 * (u⁻¹).1) * (k b 0 * x) := by ring
            rw [this, Units.mul_inv, one_mul])
            (funext fun c => by
              simp only [Fin.isValue, ↓reduceIte, zero_ne_one]
              have : u.1 * ξ c * ((u⁻¹).1 * x) = (u.1 * (u⁻¹).1) * (ξ c * x) := by ring
              rw [this, Units.mul_inv, one_mul]))
      · refine ⟨x, (u⁻¹).1 * y, ?_⟩
        rw [sylowToVec_conj_rowScaleIso, hv]
        refine Prod.ext (funext fun a => by
            fin_cases a <;> simp only [Fin.mk_zero, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero])
          (Prod.ext (funext fun b => by
            simp only [Fin.isValue, ↓reduceIte, zero_ne_one]
            have : u.1 * k b 1 * ((u⁻¹).1 * y) = (u.1 * (u⁻¹).1) * (k b 1 * y) := by ring
            rw [this, Units.mul_inv, one_mul])
            (funext fun c => by
              simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
              have : u.1 * η c * ((u⁻¹).1 * y) = (u.1 * (u⁻¹).1) * (η c * y) := by ring
              rw [this, Units.mul_inv, one_mul]))
    · rintro ⟨x, y, hv⟩
      rcases (by fin_cases j₀ <;> simp : j₀ = 0 ∨ j₀ = 1) with rfl | rfl
      · refine ⟨vecToSylow (fun a => if a = 0 then u.1 * x else y,
            fun b => k b 0 * (u.1 * x) + k b 1 * y,
            fun c => ξ c * (u.1 * x) + η c * y),
          ⟨u.1 * x, y, sylowToVec_vecToSylow _⟩, ?_⟩
        apply sylowToVec_injective
        rw [sylowToVec_conj_rowScaleIso, sylowToVec_vecToSylow, hv]
        refine Prod.ext (funext fun a => by
          fin_cases a
          · simp only [Fin.mk_zero, Fin.isValue, ↓reduceIte]; rw [← mul_assoc, Units.inv_mul, one_mul]
          · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero])
          (Prod.ext (funext fun b => by simp only [Fin.isValue, ↓reduceIte, one_ne_zero]; ring)
            (funext fun c => by simp only [Fin.isValue, ↓reduceIte, zero_ne_one]; ring))
      · refine ⟨vecToSylow (fun a => if a = 0 then x else u.1 * y,
            fun b => k b 0 * x + k b 1 * (u.1 * y),
            fun c => ξ c * x + η c * (u.1 * y)),
          ⟨x, u.1 * y, sylowToVec_vecToSylow _⟩, ?_⟩
        apply sylowToVec_injective
        rw [sylowToVec_conj_rowScaleIso, sylowToVec_vecToSylow, hv]
        refine Prod.ext (funext fun a => by
          fin_cases a
          · simp only [Fin.mk_zero, Fin.isValue, ↓reduceIte, zero_ne_one]
          · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero]; rw [← mul_assoc, Units.inv_mul, one_mul])
          (Prod.ext (funext fun b => by simp only [Fin.isValue, ↓reduceIte, zero_ne_one]; ring)
            (funext fun c => by simp only [Fin.isValue, ↓reduceIte, one_ne_zero]; ring))
  let e : (Fin 2 → ZMod q) ≃ (Fin 2 → ZMod q) :=
    { toFun := fun f c => u.1 * f c
      invFun := fun f c => (u⁻¹).1 * f c
      left_inv := fun f => funext fun c => by dsimp; rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun f => funext fun c => by dsimp; rw [← mul_assoc, Units.mul_inv, one_mul] }
  rcases (by fin_cases j₀ <;> simp : j₀ = 0 ∨ j₀ = 1) with rfl | rfl
  · rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
    symm
    rw [← S_twoq_conjSylowSub hodd (rowScaleIso q 0 u⁻¹) (rowScaleIso_conj_mem 0 u⁻¹),
      hconj ξ η]
    rfl
  · refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun η _ => ?_
    symm
    rw [← S_twoq_conjSylowSub hodd (rowScaleIso q 1 u⁻¹) (rowScaleIso_conj_mem 1 u⁻¹),
      hconj ξ η]
    rfl

private lemma sumGraphRow_swap_col {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q) :
    sumGraphRow q (fun b j => k b (1 - j)) = sumGraphRow q k := by
  unfold sumGraphRow
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ξ _ => ?_
  symm
  rw [← S_twoq_conjSylowSub hodd (rowSwapIso q) rowSwapIso_conj_mem]
  congr 1
  ext g
  simp only [conjSylowSub, Subgroup.mem_map, MonoidHom.coe_mk, OneHom.coe_mk,
    mem_graphRowSub_iff]
  constructor
  · rintro ⟨h, ⟨y, x, hv⟩, rfl⟩
    refine ⟨x, y, ?_⟩
    rw [sylowToVec_conj_rowSwapIso, hv]
    refine Prod.ext (funext fun a => by fin_cases a <;> rfl)
      (Prod.ext (funext fun b => by dsimp; ring) (funext fun c => by dsimp; ring))
  · rintro ⟨x, y, hv⟩
    refine ⟨vecToSylow (fun a => if a = 0 then y else x,
        fun b => k b 0 * y + k b 1 * x, fun c => η c * y + ξ c * x),
      ⟨y, x, sylowToVec_vecToSylow _⟩, ?_⟩
    apply sylowToVec_injective
    rw [sylowToVec_conj_rowSwapIso, sylowToVec_vecToSylow, hv]
    refine Prod.ext (funext fun a => by fin_cases a <;> rfl)
      (Prod.ext (funext fun b => by dsimp; ring) (funext fun c => by dsimp; ring))

/-! ### Evaluating `sumGraphRow` on Every Matrix Class -/

private lemma sumGraphRow_R21 {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q)
    (h00 : k 0 0 ≠ 0) (h01 : k 0 1 ≠ 0) (h10 : k 1 0 ≠ 0)
    (hdet : k 0 0 * k 1 1 = k 0 1 * k 1 0) :
    sumGraphRow q k = 2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 := by
  let u0 : (ZMod q)ˣ := Units.mk0 (k 0 0)⁻¹ (inv_ne_zero h00)
  let u1 : (ZMod q)ˣ := Units.mk0 (k 0 1)⁻¹ (inv_ne_zero h01)
  let s : (ZMod q)ˣ := Units.mk0 (k 0 0 * (k 1 0)⁻¹) (mul_ne_zero h00 (inv_ne_zero h10))
  let k1 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 1 then s.1 * k b j else k b j
  let k2 : Fin 2 → Fin 2 → ZMod q := fun b j => if j = 0 then u0.1 * k1 b j else k1 b j
  let k3 : Fin 2 → Fin 2 → ZMod q := fun b j => if j = 1 then u1.1 * k2 b j else k2 b j
  have hnorm : k3 = fun _ _ => (1 : ZMod q) := by
    ext b j
    fin_cases b <;> fin_cases j <;> simp [k3, k2, k1, u0, u1, s]
    · exact inv_mul_cancel₀ h00
    · exact inv_mul_cancel₀ h01
    · calc (k 0 0)⁻¹ * (k 0 0 * (k 1 0)⁻¹ * k 1 0)
          = ((k 0 0)⁻¹ * k 0 0) * ((k 1 0)⁻¹ * k 1 0) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ h00, inv_mul_cancel₀ h10, mul_one]
    · calc (k 0 1)⁻¹ * (k 0 0 * (k 1 0)⁻¹ * k 1 1)
          = (k 0 1)⁻¹ * ((k 1 0)⁻¹ * (k 0 0 * k 1 1)) := by ring
        _ = (k 0 1)⁻¹ * ((k 1 0)⁻¹ * (k 0 1 * k 1 0)) := by rw [hdet]
        _ = ((k 0 1)⁻¹ * k 0 1) * ((k 1 0)⁻¹ * k 1 0) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ h01, inv_mul_cancel₀ h10, mul_one]
  rw [← sumGraphRow_scale_row hodd k 1 s, ← sumGraphRow_scale_col hodd k1 0 u0,
      ← sumGraphRow_scale_col hodd k2 1 u1]
  change sumGraphRow q k3 = _
  rw [hnorm]
  exact sum_R21_norm hodd

private lemma sumGraphRow_Rmon {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q)
    (hmon : (k 0 0 ≠ 0 ∧ k 1 1 ≠ 0 ∧ k 0 1 = 0 ∧ k 1 0 = 0) ∨
            (k 0 1 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 0 0 = 0 ∧ k 1 1 = 0)) :
    sumGraphRow q k = 2 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 * (q.factorial : ℤ) ^ 2 := by
  have hdiag : ∀ k' : Fin 2 → Fin 2 → ZMod q,
      k' 0 0 ≠ 0 → k' 1 1 ≠ 0 → k' 0 1 = 0 → k' 1 0 = 0 →
      sumGraphRow q k' = 2 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 * (q.factorial : ℤ) ^ 2 := by
    intro k' h00 h11 h01 h10
    let u0 : (ZMod q)ˣ := Units.mk0 (k' 0 0)⁻¹ (inv_ne_zero h00)
    let u1 : (ZMod q)ˣ := Units.mk0 (k' 1 1)⁻¹ (inv_ne_zero h11)
    let k1 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 then u0.1 * k' b j else k' b j
    let k2 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 1 then u1.1 * k1 b j else k1 b j
    have hnorm : k2 = fun b j => if b = j then (1 : ZMod q) else 0 := by
      ext b j; fin_cases b <;> fin_cases j <;> simp [k2, k1, u0, u1, h01, h10, inv_mul_cancel₀ h00,
        inv_mul_cancel₀ h11]
    rw [← sumGraphRow_scale_row hodd k' 0 u0, ← sumGraphRow_scale_row hodd k1 1 u1]
    change sumGraphRow q k2 = _
    rw [hnorm]
    exact sum_Rmon_norm hodd
  rcases hmon with ⟨h00, h11, h01, h10⟩ | ⟨h01, h10, h00, h11⟩
  · exact hdiag k h00 h11 h01 h10
  · rw [← sumGraphRow_swap_row hodd k]
    exact hdiag _ h10 h01 h11 h00

private lemma sumGraphRow_Rone_base {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q)
    (h01 : k 0 1 = 0) (h00 : k 0 0 ≠ 0) (h10 : k 1 0 ≠ 0) (h11 : k 1 1 ≠ 0) :
    sumGraphRow q k = -2 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 2 * tauQ q := by
  let u0 : (ZMod q)ˣ := Units.mk0 (k 0 0)⁻¹ (inv_ne_zero h00)
  let u1 : (ZMod q)ˣ := Units.mk0 (k 1 0)⁻¹ (inv_ne_zero h10)
  let v1 : (ZMod q)ˣ := Units.mk0 (k 1 0 * (k 1 1)⁻¹) (mul_ne_zero h10 (inv_ne_zero h11))
  let k1 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 then u0.1 * k b j else k b j
  let k2 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 1 then u1.1 * k1 b j else k1 b j
  let k3 : Fin 2 → Fin 2 → ZMod q := fun b j => if j = 1 then v1.1 * k2 b j else k2 b j
  have hnorm : k3 = fun b j => if b = 0 ∧ j = 1 then (0 : ZMod q) else 1 := by
    ext b j; fin_cases b <;> fin_cases j <;> simp [k3, k2, k1, u0, u1, v1, h01]
    · exact inv_mul_cancel₀ h00
    · exact inv_mul_cancel₀ h10
    · calc k 1 0 * (k 1 1)⁻¹ * ((k 1 0)⁻¹ * k 1 1)
          = (k 1 0 * (k 1 0)⁻¹) * ((k 1 1)⁻¹ * k 1 1) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ h10, inv_mul_cancel₀ h11, mul_one]
  rw [← sumGraphRow_scale_row hodd k 0 u0, ← sumGraphRow_scale_row hodd k1 1 u1,
      ← sumGraphRow_scale_col hodd k2 1 v1]
  change sumGraphRow q k3 = _
  rw [hnorm]
  exact sum_Rone_norm hodd

private lemma sumGraphRow_Rone {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q)
    (hone : (k 0 1 = 0 ∧ k 0 0 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 1 1 ≠ 0) ∨
            (k 0 0 = 0 ∧ k 0 1 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 1 1 ≠ 0) ∨
            (k 1 1 = 0 ∧ k 0 0 ≠ 0 ∧ k 0 1 ≠ 0 ∧ k 1 0 ≠ 0) ∨
            (k 1 0 = 0 ∧ k 0 0 ≠ 0 ∧ k 0 1 ≠ 0 ∧ k 1 1 ≠ 0)) :
    sumGraphRow q k = -2 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 2 * tauQ q := by
  rcases hone with ⟨h01, h00, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ |
      ⟨h11, h00, h01, h10⟩ | ⟨h10, h00, h01, h11⟩
  · exact sumGraphRow_Rone_base hodd k h01 h00 h10 h11
  · rw [← sumGraphRow_swap_col hodd k]
    exact sumGraphRow_Rone_base hodd _ h00 h01 h11 h10
  · rw [← sumGraphRow_swap_row hodd k]
    exact sumGraphRow_Rone_base hodd _ h11 h10 h00 h01
  · rw [← sumGraphRow_swap_row hodd k, ← sumGraphRow_swap_col hodd _]
    exact sumGraphRow_Rone_base hodd _ h10 h11 h01 h00

private lemma sumGraphRow_Rfull {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q)
    (h00 : k 0 0 ≠ 0) (h01 : k 0 1 ≠ 0) (h10 : k 1 0 ≠ 0) (h11 : k 1 1 ≠ 0)
    (hdet : k 0 0 * k 1 1 ≠ k 0 1 * k 1 0) :
    let ν := k 0 0 * k 1 1 * (k 0 1 * k 1 0)⁻¹
    sumGraphRow q k =
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 *
        (∑ t : ZMod q, legendreSym q ((t * (t - 1) * (t - ν)).val : ℤ)) ^ 2 := by
  intro ν
  have hν0 : ν ≠ 0 := mul_ne_zero (mul_ne_zero h00 h11) (inv_ne_zero (mul_ne_zero h01 h10))
  have hν1 : ν ≠ 1 := by
    intro h
    apply hdet
    have hmul := congrArg (· * (k 0 1 * k 1 0)) h
    dsimp [ν] at hmul
    rwa [mul_assoc, inv_mul_cancel₀ (mul_ne_zero h01 h10), mul_one, one_mul] at hmul
  let u0 : (ZMod q)ˣ := Units.mk0 (k 0 0)⁻¹ (inv_ne_zero h00)
  let u1 : (ZMod q)ˣ := Units.mk0 (k 1 0)⁻¹ (inv_ne_zero h10)
  let v1 : (ZMod q)ˣ := Units.mk0 (k 0 0 * (k 0 1)⁻¹) (mul_ne_zero h00 (inv_ne_zero h01))
  let k1 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 0 then u0.1 * k b j else k b j
  let k2 : Fin 2 → Fin 2 → ZMod q := fun b j => if b = 1 then u1.1 * k1 b j else k1 b j
  let k3 : Fin 2 → Fin 2 → ZMod q := fun b j => if j = 1 then v1.1 * k2 b j else k2 b j
  have hnorm : k3 = fun b j => if b = 0 then (1 : ZMod q) else if j = 0 then 1 else ν := by
    ext b j; fin_cases b <;> fin_cases j <;> simp [k3, k2, k1, u0, u1, v1, ν]
    · exact inv_mul_cancel₀ h00
    · calc k 0 0 * (k 0 1)⁻¹ * ((k 0 0)⁻¹ * k 0 1)
          = (k 0 0 * (k 0 0)⁻¹) * ((k 0 1)⁻¹ * k 0 1) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ h00, inv_mul_cancel₀ h01, mul_one]
    · exact inv_mul_cancel₀ h10
    · ring
  rw [← sumGraphRow_scale_row hodd k 0 u0, ← sumGraphRow_scale_row hodd k1 1 u1,
      ← sumGraphRow_scale_col hodd k2 1 v1]
  change sumGraphRow q k3 = _
  rw [hnorm]
  exact sum_Rfull_norm hodd hν0 hν1

private lemma sumGraphRow_deg_zero {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (k : Fin 2 → Fin 2 → ZMod q)
    (hdet : k 0 0 * k 1 1 = k 0 1 * k 1 0)
    (hz : k 0 0 = 0 ∨ k 0 1 = 0 ∨ k 1 0 = 0 ∨ k 1 1 = 0) :
    sumGraphRow q k = 0 := by
  have hq : q.Prime := Fact.out
  unfold sumGraphRow
  refine Finset.sum_eq_zero fun ξ _ => Finset.sum_eq_zero fun η _ => ?_
  let H := graphRowSub k ξ η
  have hne : H ≠ ⊥ := by
    intro hbot
    have hr : elemRank q H = 2 := elemRank_graphRowSub hq k ξ η
    rw [hbot] at hr
    simp [elemRank, Nat.log_one_right] at hr
  -- Check if a column block is fixed by `H`
  by_cases hrow0 : k 0 0 = 0 ∧ k 0 1 = 0
  · refine lem_6_6_part1 hq hodd H hne (Or.inl ⟨blockEquiv q (0, 0), fun g hg => ?_⟩)
    rcases (mem_graphRowSub_iff k ξ η g).mp hg with ⟨x, y, hv⟩
    have hv' := congrArg (fun p => p.2.1 0) hv
    dsimp at hv'
    rw [hrow0.1, hrow0.2, zero_mul, zero_mul, add_zero] at hv'
    have hgval := sylowToVec_val g
    have hcol : g.1.2.1 = blockTransPerm q (sylowToVec g).2.1 := by rw [hgval]
    rw [hcol, blockTransPerm_apply, hv', add_zero]
  by_cases hrow1 : k 1 0 = 0 ∧ k 1 1 = 0
  · refine lem_6_6_part1 hq hodd H hne (Or.inl ⟨blockEquiv q (1, 0), fun g hg => ?_⟩)
    rcases (mem_graphRowSub_iff k ξ η g).mp hg with ⟨x, y, hv⟩
    have hv' := congrArg (fun p => p.2.1 1) hv
    dsimp at hv'
    rw [hrow1.1, hrow1.2, zero_mul, zero_mul, add_zero] at hv'
    have hgval := sylowToVec_val g
    have hcol : g.1.2.1 = blockTransPerm q (sylowToVec g).2.1 := by rw [hgval]
    rw [hcol, blockTransPerm_apply, hv', add_zero]
  -- Otherwise either col 0 of `k` is zero, or col 1 of `k` is zero -> Fact 1!
  have hcolz : (k 0 0 = 0 ∧ k 1 0 = 0) ∨ (k 0 1 = 0 ∧ k 1 1 = 0) := by
    rcases hz with h | h | h | h
    · have h01 : k 0 1 ≠ 0 := fun h' => hrow0 ⟨h, h'⟩
      rw [h, zero_mul] at hdet
      exact Or.inl ⟨h, (mul_eq_zero.mp hdet.symm).resolve_left h01⟩
    · have h00 : k 0 0 ≠ 0 := fun h' => hrow0 ⟨h', h⟩
      rw [h, zero_mul] at hdet
      exact Or.inr ⟨h, (mul_eq_zero.mp hdet).resolve_left h00⟩
    · have h11 : k 1 1 ≠ 0 := fun h' => hrow1 ⟨h, h'⟩
      rw [h, mul_zero] at hdet
      exact Or.inl ⟨(mul_eq_zero.mp hdet).resolve_right h11, h⟩
    · have h10 : k 1 0 ≠ 0 := fun h' => hrow1 ⟨h', h⟩
      rw [h, mul_zero] at hdet
      exact Or.inr ⟨(mul_eq_zero.mp hdet.symm).resolve_right h10, h⟩
  have hempty : fixSet (H.map (sylowP q).subtype) = (∅ : Set (LatinSquare (2 * q))) := by
    rcases hcolz with ⟨h00, h10⟩ | ⟨h01, h11⟩
    · let g := vecToSylow (fun a => if a = 0 then (1 : ZMod q) else 0,
        fun b => k b 0, fun c => ξ c)
      refine fixSet_empty_of_fix_all_cols_and_row H g
        ((mem_graphRowSub_iff k ξ η g).mpr ⟨1, 0, by
          rw [sylowToVec_vecToSylow]; ext i <;> simp⟩)
        (fun h1 => by
          have := congrArg (fun x => (sylowToVec x).1 0) h1
          rw [sylowToVec_vecToSylow, sylowToVec_one] at this
          exact one_ne_zero this)
        (by rw [sylowToVec_vecToSylow]; ext b; fin_cases b <;> simp [h00, h10])
        1 (by rw [sylowToVec_vecToSylow]; simp)
    · let g := vecToSylow (fun a => if a = 0 then (0 : ZMod q) else 1,
        fun b => k b 1, fun c => η c)
      refine fixSet_empty_of_fix_all_cols_and_row H g
        ((mem_graphRowSub_iff k ξ η g).mpr ⟨0, 1, by
          rw [sylowToVec_vecToSylow]; ext i <;> simp⟩)
        (fun h1 => by
          have := congrArg (fun x => (sylowToVec x).1 1) h1
          rw [sylowToVec_vecToSylow, sylowToVec_one] at this
          exact one_ne_zero this)
        (by rw [sylowToVec_vecToSylow]; ext b; fin_cases b <;> simp [h01, h11])
        0 (by rw [sylowToVec_vecToSylow]; simp)
  unfold S_twoq signedFixSum
  rw [hempty]
  simp

/-! ### Summing `sumGraphRow` Over Singular and Invertible Matrices `k` -/

private lemma card_units_zmod (q : ℕ) [Fact q.Prime] :
    Fintype.card (ZMod q)ˣ = q - 1 := by
  have hq : q.Prime := Fact.out
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]

private lemma sum_sumGraphRow_det_eq_zero {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q => k 0 0 * k 1 1 = k 0 1 * k 1 0),
      sumGraphRow q k =
    2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 := by
  classical
  have hq : q.Prime := Fact.out
  let S := Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q =>
    k 0 0 * k 1 1 = k 0 1 * k 1 0 ∧ k 0 0 ≠ 0 ∧ k 0 1 ≠ 0 ∧ k 1 0 ≠ 0)
  have hsub :
      ∑ k ∈ Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q => k 0 0 * k 1 1 = k 0 1 * k 1 0),
        sumGraphRow q k =
      ∑ k ∈ S, sumGraphRow q k := by
    symm
    refine Finset.sum_subset (fun k hk => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; exact hk.1) ?_
    intro k hk hkS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hkS
    have hz : k 0 0 = 0 ∨ k 0 1 = 0 ∨ k 1 0 = 0 ∨ k 1 1 = 0 := by
      by_cases h00 : k 0 0 = 0; · exact Or.inl h00
      by_cases h01 : k 0 1 = 0; · exact Or.inr (Or.inl h01)
      exact Or.inr (Or.inr (Or.inl (hkS hk h00 h01)))
    exact sumGraphRow_deg_zero hodd k hk hz
  rw [hsub]
  have hconst : ∀ k ∈ S, sumGraphRow q k = 2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 := by
    intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact sumGraphRow_R21 hodd k hk.2.1 hk.2.2.1 hk.2.2.2 hk.1
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- Count `|S| = (q - 1)^3`
  have hcard : S.card = (q - 1) ^ 3 := by
    let f : (ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ → (Fin 2 → Fin 2 → ZMod q) :=
      fun p b j =>
        if b = 0 then (if j = 0 then p.1.1 else p.2.1.1)
        else (if j = 0 then p.2.2.1 else p.2.1.1 * p.2.2.1 * (p.1⁻¹).1)
    have hbij : S.card = Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ) := by
      symm
      refine Finset.card_bij (fun p _ => f p) ?_ ?_ ?_
      · intro p _
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, f]
        refine ⟨?_, p.1.ne_zero, p.2.1.ne_zero, p.2.2.ne_zero⟩
        calc p.1.1 * (p.2.1.1 * p.2.2.1 * (p.1⁻¹).1)
            = p.2.1.1 * p.2.2.1 * (p.1.1 * (p.1⁻¹).1) := by ring
          _ = p.2.1.1 * p.2.2.1 := by rw [Units.mul_inv, mul_one]
      · intro p₁ _ p₂ _ hEq
        have h00 := congrFun (congrFun hEq 0) 0
        have h01 := congrFun (congrFun hEq 0) 1
        have h10 := congrFun (congrFun hEq 1) 0
        simp only [f, ↓reduceIte, one_ne_zero] at h00 h01 h10
        exact Prod.ext (Units.ext h00) (Prod.ext (Units.ext h01) (Units.ext h10))
      · intro k hk
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨(Units.mk0 (k 0 0) hk.2.1, Units.mk0 (k 0 1) hk.2.2.1, Units.mk0 (k 1 0) hk.2.2.2),
          Finset.mem_univ _, ?_⟩
        ext b j
        fin_cases b <;> fin_cases j <;>
          simp only [f, Fin.mk_zero, Fin.mk_one, ↓reduceIte, one_ne_zero, Units.val_mk0,
            Units.val_inv_eq_inv_val]
        calc k 0 1 * k 1 0 * (k 0 0)⁻¹
            = k 0 0 * k 1 1 * (k 0 0)⁻¹ := by rw [hk.1]
          _ = k 1 1 * (k 0 0 * (k 0 0)⁻¹) := by ring
          _ = k 1 1 := by rw [mul_inv_cancel₀ hk.2.1, mul_one]
    rw [hbij, Fintype.card_prod, Fintype.card_prod, card_units_zmod]
    ring
  rw [hcard]
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := hq.two_le; omega
  push_cast
  rw [hcast]
  ring

private lemma sum_sumGraphRow_det_ne_zero {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q => k 0 0 * k 1 1 ≠ k 0 1 * k 1 0),
      sumGraphRow q k =
    4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2 -
    8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q +
    2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) ^ 2 - 2 * (q : ℤ) - 3) := by
  classical
  have hq : q.Prime := Fact.out
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := hq.two_le; omega
  let Sinv := Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q => k 0 0 * k 1 1 ≠ k 0 1 * k 1 0)
  let Smon := Sinv.filter (fun k =>
    (k 0 0 ≠ 0 ∧ k 1 1 ≠ 0 ∧ k 0 1 = 0 ∧ k 1 0 = 0) ∨
    (k 0 1 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 0 0 = 0 ∧ k 1 1 = 0))
  let Sone := Sinv.filter (fun k =>
    (k 0 1 = 0 ∧ k 0 0 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 1 1 ≠ 0) ∨
    (k 0 0 = 0 ∧ k 0 1 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 1 1 ≠ 0) ∨
    (k 1 1 = 0 ∧ k 0 0 ≠ 0 ∧ k 0 1 ≠ 0 ∧ k 1 0 ≠ 0) ∨
    (k 1 0 = 0 ∧ k 0 0 ≠ 0 ∧ k 0 1 ≠ 0 ∧ k 1 1 ≠ 0))
  let Sfull := Sinv.filter (fun k => k 0 0 ≠ 0 ∧ k 0 1 ≠ 0 ∧ k 1 0 ≠ 0 ∧ k 1 1 ≠ 0)
  -- Partition `Sinv = Smon ∪ Sone ∪ Sfull`
  have hdisj1 : Disjoint Smon Sone := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Smon, Sone, Finset.mem_filter] at h1 h2
    rcases h1.2 with ⟨_, _, h01, h10⟩ | ⟨_, _, h00, h11⟩ <;>
      rcases h2.2 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
      contradiction
  have hdisj2 : Disjoint (Smon ∪ Sone) Sfull := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_union, Smon, Sone, Sfull, Finset.mem_filter] at h1 h2
    rcases h2.2 with ⟨h00, h01, h10, h11⟩
    rcases h1 with ⟨_, h⟩ | ⟨_, h⟩
    · rcases h with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> contradiction
    · rcases h with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> contradiction
  have hunion : Sinv = (Smon ∪ Sone) ∪ Sfull := by
    ext k
    simp only [Finset.mem_union, Smon, Sone, Sfull, Sinv, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hdet
      by_cases h00 : k 0 0 = 0 <;> by_cases h01 : k 0 1 = 0 <;>
        by_cases h10 : k 1 0 = 0 <;> by_cases h11 : k 1 1 = 0
      · exfalso; exact hdet (by simp [h00, h01])
      · exfalso; exact hdet (by simp [h00, h01])
      · exfalso; exact hdet (by simp [h00, h01])
      · exfalso; exact hdet (by simp [h00, h01])
      · exfalso; exact hdet (by simp [h00, h10])
      · exfalso; exact hdet (by simp [h00, h10])
      · exact Or.inl (Or.inl ⟨hdet, Or.inr ⟨h01, h10, h00, h11⟩⟩)
      · exact Or.inl (Or.inr ⟨hdet, Or.inr (Or.inl ⟨h00, h01, h10, h11⟩)⟩)
      · exfalso; exact hdet (by simp [h01, h11])
      · exact Or.inl (Or.inl ⟨hdet, Or.inl ⟨h00, h11, h01, h10⟩⟩)
      · exfalso; exact hdet (by simp [h01, h11])
      · exact Or.inl (Or.inr ⟨hdet, Or.inl ⟨h01, h00, h10, h11⟩⟩)
      · exfalso; exact hdet (by simp [h10, h11])
      · exact Or.inl (Or.inr ⟨hdet, Or.inr (Or.inr (Or.inr ⟨h10, h00, h01, h11⟩))⟩)
      · exact Or.inl (Or.inr ⟨hdet, Or.inr (Or.inr (Or.inl ⟨h11, h00, h01, h10⟩))⟩)
      · exact Or.inr ⟨hdet, h00, h01, h10, h11⟩
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  change ∑ k ∈ Sinv, sumGraphRow q k = _
  rw [hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
  -- 1. `Smon` sum
  have hSmon : ∑ k ∈ Smon, sumGraphRow q k =
      4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2 := by
    rw [Finset.sum_congr rfl fun k hk => sumGraphRow_Rmon hodd k (Finset.mem_filter.mp hk).2,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : Smon.card = 2 * (q - 1) ^ 2 := by
      let f : Bool × (ZMod q)ˣ × (ZMod q)ˣ → (Fin 2 → Fin 2 → ZMod q) := fun p b j =>
        if p.1 then (if b = 0 ∧ j = 0 then p.2.1.1 else if b = 1 ∧ j = 1 then p.2.2.1 else 0)
        else (if b = 0 ∧ j = 1 then p.2.1.1 else if b = 1 ∧ j = 0 then p.2.2.1 else 0)
      have hbij : Smon.card = Fintype.card (Bool × (ZMod q)ˣ × (ZMod q)ˣ) := by
        symm
        refine Finset.card_bij (fun p _ => f p) ?_ ?_ ?_
        · intro p _
          simp only [Smon, Sinv, Finset.mem_filter, Finset.mem_univ, true_and, f]
          cases p.1 <;> simp [mul_ne_zero p.2.1.ne_zero p.2.2.ne_zero,
            (mul_ne_zero p.2.1.ne_zero p.2.2.ne_zero).symm, p.2.1.ne_zero, p.2.2.ne_zero]
        · intro p₁ _ p₂ _ hEq
          have h00 := congrFun (congrFun hEq 0) 0
          have h01 := congrFun (congrFun hEq 0) 1
          have h10 := congrFun (congrFun hEq 1) 0
          have h11 := congrFun (congrFun hEq 1) 1
          rcases p₁ with ⟨b₁, u₁, v₁⟩; rcases p₂ with ⟨b₂, u₂, v₂⟩
          cases b₁ <;> cases b₂ <;> simp [f] at h00 h01 h10 h11
          · exact Prod.ext rfl (Prod.ext (Units.ext h01) (Units.ext h10))
          · exact Prod.ext rfl (Prod.ext (Units.ext h00) (Units.ext h11))
        · intro k hk
          simp only [Smon, Sinv, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rcases hk.2 with ⟨h00, h11, h01, h10⟩ | ⟨h01, h10, h00, h11⟩
          · refine ⟨(true, Units.mk0 (k 0 0) h00, Units.mk0 (k 1 1) h11), Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;> simp [f, h01, h10]
          · refine ⟨(false, Units.mk0 (k 0 1) h01, Units.mk0 (k 1 0) h10), Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;> simp [f, h00, h11]
      rw [hbij, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, card_units_zmod]
      ring
    rw [hcard]; push_cast; rw [hcast]; ring
  -- 2. `Sone` sum
  have hSone : ∑ k ∈ Sone, sumGraphRow q k = -8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q := by
    rw [Finset.sum_congr rfl fun k hk => sumGraphRow_Rone hodd k (Finset.mem_filter.mp hk).2,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : Sone.card = 4 * (q - 1) ^ 3 := by
      let f : (Fin 2 × Fin 2) × (ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ → (Fin 2 → Fin 2 → ZMod q) :=
        fun p b j =>
          match p.1 with
          | (0, 1) => if b = 0 ∧ j = 1 then 0 else if b = 0 ∧ j = 0 then p.2.1.1
              else if b = 1 ∧ j = 0 then p.2.2.1.1 else p.2.2.2.1
          | (0, 0) => if b = 0 ∧ j = 0 then 0 else if b = 0 ∧ j = 1 then p.2.1.1
              else if b = 1 ∧ j = 0 then p.2.2.1.1 else p.2.2.2.1
          | (1, 1) => if b = 1 ∧ j = 1 then 0 else if b = 0 ∧ j = 0 then p.2.1.1
              else if b = 0 ∧ j = 1 then p.2.2.1.1 else p.2.2.2.1
          | (1, 0) => if b = 1 ∧ j = 0 then 0 else if b = 0 ∧ j = 0 then p.2.1.1
              else if b = 0 ∧ j = 1 then p.2.2.1.1 else p.2.2.2.1
      have hbij : Sone.card =
          Fintype.card ((Fin 2 × Fin 2) × (ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ) := by
        symm
        refine Finset.card_bij (fun p _ => f p) ?_ ?_ ?_
        · rintro ⟨⟨a, b⟩, u, v, w⟩ _
          simp only [Sone, Sinv, Finset.mem_filter, Finset.mem_univ, true_and]
          fin_cases a <;> fin_cases b <;>
            simp [f, u.ne_zero, v.ne_zero, w.ne_zero, mul_ne_zero u.ne_zero w.ne_zero,
              (mul_ne_zero u.ne_zero v.ne_zero).symm, (mul_ne_zero v.ne_zero w.ne_zero).symm]
        · rintro ⟨⟨a₁, b₁⟩, u₁, v₁, w₁⟩ _ ⟨⟨a₂, b₂⟩, u₂, v₂, w₂⟩ _ hEq
          have h00 := congrFun (congrFun hEq 0) 0
          have h01 := congrFun (congrFun hEq 0) 1
          have h10 := congrFun (congrFun hEq 1) 0
          have h11 := congrFun (congrFun hEq 1) 1
          fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂ <;>
            simp [f] at h00 h01 h10 h11
          all_goals try exact Prod.ext rfl (Prod.ext (Units.ext h01) (Prod.ext (Units.ext h10) (Units.ext h11)))
          all_goals try exact Prod.ext rfl (Prod.ext (Units.ext h00) (Prod.ext (Units.ext h10) (Units.ext h11)))
          all_goals try exact Prod.ext rfl (Prod.ext (Units.ext h00) (Prod.ext (Units.ext h01) (Units.ext h11)))
          all_goals try exact Prod.ext rfl (Prod.ext (Units.ext h00) (Prod.ext (Units.ext h01) (Units.ext h10)))
        · intro k hk
          simp only [Sone, Sinv, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rcases hk.2 with ⟨h01, h00, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ |
              ⟨h11, h00, h01, h10⟩ | ⟨h10, h00, h01, h11⟩
          · refine ⟨((0, 1), Units.mk0 (k 0 0) h00, Units.mk0 (k 1 0) h10, Units.mk0 (k 1 1) h11),
              Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;> simp [f, h01]
          · refine ⟨((0, 0), Units.mk0 (k 0 1) h01, Units.mk0 (k 1 0) h10, Units.mk0 (k 1 1) h11),
              Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;> simp [f, h00]
          · refine ⟨((1, 1), Units.mk0 (k 0 0) h00, Units.mk0 (k 0 1) h01, Units.mk0 (k 1 0) h10),
              Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;> simp [f, h11]
          · refine ⟨((1, 0), Units.mk0 (k 0 0) h00, Units.mk0 (k 0 1) h01, Units.mk0 (k 1 1) h11),
              Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;> simp [f, h10]
      rw [hbij, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
        Fintype.card_fin, card_units_zmod]
      ring
    rw [hcard]; push_cast; rw [hcast]; ring
  -- 3. `Sfull` sum via fiber over `ν = (k 0 0 * k 1 1) * (k 0 1 * k 1 0)⁻¹`
  have hSfull : ∑ k ∈ Sfull, sumGraphRow q k =
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) ^ 2 - 2 * (q : ℤ) - 3) := by
    let T := Finset.univ.filter (fun ν : ZMod q => ν ≠ 0 ∧ ν ≠ 1)
    let φ : (Fin 2 → Fin 2 → ZMod q) → ZMod q := fun k =>
      k 0 0 * k 1 1 * (k 0 1 * k 1 0)⁻¹
    have hmap : ∀ k ∈ Sfull, φ k ∈ T := by
      intro k hk
      simp only [Sfull, Sinv, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases hk with ⟨hdet, h00, h01, h10, h11⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, φ]
      refine ⟨mul_ne_zero (mul_ne_zero h00 h11) (inv_ne_zero (mul_ne_zero h01 h10)), fun h1 => hdet ?_⟩
      have hmul := congrArg (· * (k 0 1 * k 1 0)) h1
      rwa [mul_assoc, inv_mul_cancel₀ (mul_ne_zero h01 h10), mul_one, one_mul] at hmul
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    have hfiber : ∀ ν ∈ T,
        ∑ k ∈ Sfull.filter (fun k => φ k = ν), sumGraphRow q k =
        2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 *
          (∑ t : ZMod q, legendreSym q ((t * (t - 1) * (t - ν)).val : ℤ)) ^ 2 := by
      intro ν hν
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hν
      have hconst : ∀ k ∈ Sfull.filter (fun k => φ k = ν),
          sumGraphRow q k =
          2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 2 *
            (∑ t : ZMod q, legendreSym q ((t * (t - 1) * (t - ν)).val : ℤ)) ^ 2 := by
        intro k hk
        simp only [Sfull, Sinv, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rcases hk with ⟨⟨hdet, h00, h01, h10, h11⟩, hφ⟩
        have h := sumGraphRow_Rfull hodd k h00 h01 h10 h11 hdet
        dsimp only [φ] at hφ
        dsimp only at h
        rw [hφ] at h
        exact h
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Sfull.filter (fun k => φ k = ν)).card = (q - 1) ^ 3 := by
        let g : (ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ → (Fin 2 → Fin 2 → ZMod q) := fun p b j =>
          if b = 0 then (if j = 0 then p.1.1 else p.2.1.1)
          else (if j = 0 then p.2.2.1 else ν * p.2.1.1 * p.2.2.1 * (p.1⁻¹).1)
        have hbij : (Sfull.filter (fun k => φ k = ν)).card =
            Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ × (ZMod q)ˣ) := by
          symm
          refine Finset.card_bij (fun p _ => g p) ?_ ?_ ?_
          · intro p _
            simp only [Sfull, Sinv, Finset.mem_filter, Finset.mem_univ, true_and, g, φ,
              ↓reduceIte, one_ne_zero]
            have h11 : ν * p.2.1.1 * p.2.2.1 * (p.1⁻¹).1 ≠ 0 :=
              mul_ne_zero (mul_ne_zero (mul_ne_zero hν.1 p.2.1.ne_zero) p.2.2.ne_zero)
                p.1⁻¹.ne_zero
            have hprod : p.1.1 * (ν * p.2.1.1 * p.2.2.1 * (p.1⁻¹).1) =
                ν * (p.2.1.1 * p.2.2.1) := by
              calc p.1.1 * (ν * p.2.1.1 * p.2.2.1 * (p.1⁻¹).1)
                  = ν * (p.2.1.1 * p.2.2.1) * (p.1.1 * (p.1⁻¹).1) := by ring
                _ = ν * (p.2.1.1 * p.2.2.1) := by rw [Units.mul_inv, mul_one]
            refine ⟨⟨?_, p.1.ne_zero, p.2.1.ne_zero, p.2.2.ne_zero, h11⟩, ?_⟩
            · rw [hprod]
              intro heq
              apply hν.2
              have hcancel := mul_right_cancel₀ (mul_ne_zero p.2.1.ne_zero p.2.2.ne_zero)
                (by simpa [one_mul] using heq)
              exact hcancel
            · rw [hprod, mul_assoc, mul_inv_cancel₀ (mul_ne_zero p.2.1.ne_zero p.2.2.ne_zero),
                mul_one]
          · intro p₁ _ p₂ _ hEq
            have h00 := congrFun (congrFun hEq 0) 0
            have h01 := congrFun (congrFun hEq 0) 1
            have h10 := congrFun (congrFun hEq 1) 0
            simp only [g, ↓reduceIte, one_ne_zero] at h00 h01 h10
            exact Prod.ext (Units.ext h00) (Prod.ext (Units.ext h01) (Units.ext h10))
          · intro k hk
            simp only [Sfull, Sinv, Finset.mem_filter, Finset.mem_univ, true_and, φ] at hk
            rcases hk with ⟨⟨_, h00, h01, h10, _⟩, hφ⟩
            refine ⟨(Units.mk0 (k 0 0) h00, Units.mk0 (k 0 1) h01, Units.mk0 (k 1 0) h10),
              Finset.mem_univ _, ?_⟩
            ext b j; fin_cases b <;> fin_cases j <;>
              simp only [g, Fin.mk_zero, Fin.mk_one, ↓reduceIte, one_ne_zero,
                Units.val_mk0, Units.val_inv_eq_inv_val]
            rw [← hφ]
            calc k 0 0 * k 1 1 * (k 0 1 * k 1 0)⁻¹ * k 0 1 * k 1 0 * (k 0 0)⁻¹
                = k 1 1 * (k 0 0 * (k 0 0)⁻¹) * ((k 0 1 * k 1 0)⁻¹ * (k 0 1 * k 1 0)) := by ring
              _ = k 1 1 := by
                rw [mul_inv_cancel₀ h00, inv_mul_cancel₀ (mul_ne_zero h01 h10), mul_one, mul_one]
        rw [hbij, Fintype.card_prod, Fintype.card_prod, card_units_zmod]; ring
      rw [hcard]; push_cast; rw [hcast]; ring
    rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum, sum_rho_sq_ne_zero_one hodd]
  rw [hSmon, hSone, hSfull]
  ring

/-! ### Classifying All Rank-2 Subgroups of `sylowP q` -/

private def rowFull {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) : Prop :=
  ∀ x y : ZMod q, ∃ g ∈ H, (sylowToVec g).1 0 = x ∧ (sylowToVec g).1 1 = y

private def colFull {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) : Prop :=
  ∀ x y : ZMod q, ∃ g ∈ H, (sylowToVec g).2.1 0 = x ∧ (sylowToVec g).2.1 1 = y

private lemma sylowToVec_zpow_smul {q : ℕ} [NeZero q] (g : sylowP q) (n : ℕ) :
    sylowToVec (g ^ n) =
      (fun a => (n : ZMod q) * (sylowToVec g).1 a,
       fun b => (n : ZMod q) * (sylowToVec g).2.1 b,
       fun c => (n : ZMod q) * (sylowToVec g).2.2 c) := by
  induction n with
  | zero =>
    simp [sylowToVec_one]; rfl
  | succ n ih =>
    rw [pow_succ, sylowToVec_mul, ih]
    refine Prod.ext (funext fun a => ?_) (Prod.ext (funext fun b => ?_) (funext fun c => ?_)) <;>
      · change (n : ZMod q) * _ + _ = ((n + 1 : ℕ) : ZMod q) * _
        push_cast; ring

private lemma mem_scale_sylow {q : ℕ} [NeZero q] (H : Subgroup (sylowP q))
    {g : sylowP q} (hg : g ∈ H) (t : ZMod q) :
    vecToSylow (fun a => t * (sylowToVec g).1 a,
                fun b => t * (sylowToVec g).2.1 b,
                fun c => t * (sylowToVec g).2.2 c) ∈ H := by
  have hpow : g ^ t.val ∈ H := H.pow_mem hg t.val
  have heq : vecToSylow (fun a => t * (sylowToVec g).1 a,
      fun b => t * (sylowToVec g).2.1 b,
      fun c => t * (sylowToVec g).2.2 c) = g ^ t.val := by
    apply sylowToVec_injective
    rw [sylowToVec_vecToSylow, sylowToVec_zpow_smul, ZMod.natCast_zmod_val]
  rw [heq]; exact hpow

private lemma rowFull_eq_graphRowSub {q : ℕ} [Fact q.Prime]
    (H : Subgroup (sylowP q)) (hrank : elemRank q H = 2) (hfull : rowFull H) :
    ∃ k ξ η, H = graphRowSub k ξ η := by
  have hq : q.Prime := Fact.out
  let _ : Fintype (sylowP q) := Fintype.ofFinite _
  -- `|H| = q^2`
  have hcardH : Nat.card H = q ^ 2 := by
    rw [card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H), hrank]
  -- Projection `H → ZMod q × ZMod q` onto row vector is surjective, hence bijective
  let π : H → ZMod q × ZMod q := fun g => ((sylowToVec g.1).1 0, (sylowToVec g.1).1 1)
  have hsurj : Function.Surjective π := fun ⟨x, y⟩ => by
    rcases hfull x y with ⟨g, hg, h0, h1⟩
    exact ⟨⟨g, hg⟩, Prod.ext h0 h1⟩
  have hbij : Function.Bijective π := by
    let _ : Fintype H := Fintype.ofFinite H
    have hcard_eq : Fintype.card H = Fintype.card (ZMod q × ZMod q) := by
      rw [← Nat.card_eq_fintype_card, hcardH, Fintype.card_prod, ZMod.card, sq]
    exact (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hsurj, hcard_eq⟩
  obtain ⟨⟨g0, hg0⟩, hπ0⟩ := hsurj (1, 0)
  obtain ⟨⟨g1, hg1⟩, hπ1⟩ := hsurj (0, 1)
  let k : Fin 2 → Fin 2 → ZMod q := fun b j =>
    if j = 0 then (sylowToVec g0).2.1 b else (sylowToVec g1).2.1 b
  let ξ : Fin 2 → ZMod q := (sylowToVec g0).2.2
  let η : Fin 2 → ZMod q := (sylowToVec g1).2.2
  refine ⟨k, ξ, η, ?_⟩
  ext g
  rw [mem_graphRowSub_iff]
  constructor
  · intro hgH
    let x := (sylowToVec g).1 0
    let y := (sylowToVec g).1 1
    let g0' := vecToSylow (fun a => x * (sylowToVec g0).1 a,
      fun b => x * (sylowToVec g0).2.1 b, fun c => x * (sylowToVec g0).2.2 c)
    let g1' := vecToSylow (fun a => y * (sylowToVec g1).1 a,
      fun b => y * (sylowToVec g1).2.1 b, fun c => y * (sylowToVec g1).2.2 c)
    have hg0' : g0' ∈ H := mem_scale_sylow H hg0 x
    have hg1' : g1' ∈ H := mem_scale_sylow H hg1 y
    have hmulH : g0' * g1' ∈ H := H.mul_mem hg0' hg1'
    have h00 : (sylowToVec g0).1 0 = 1 := congrArg Prod.fst hπ0
    have h01 : (sylowToVec g0).1 1 = 0 := congrArg Prod.snd hπ0
    have h10 : (sylowToVec g1).1 0 = 0 := congrArg Prod.fst hπ1
    have h11 : (sylowToVec g1).1 1 = 1 := congrArg Prod.snd hπ1
    have hπeq : π ⟨g0' * g1', hmulH⟩ = π ⟨g, hgH⟩ := by
      apply Prod.ext
      · change (sylowToVec (g0' * g1')).1 0 = x
        rw [sylowToVec_mul]
        change (sylowToVec g0').1 0 + (sylowToVec g1').1 0 = x
        simp [g0', g1', h00, h10]
      · change (sylowToVec (g0' * g1')).1 1 = y
        rw [sylowToVec_mul]
        change (sylowToVec g0').1 1 + (sylowToVec g1').1 1 = y
        simp [g0', g1', h01, h11]
    have hgeq : g = g0' * g1' := (congrArg Subtype.val (hbij.1 hπeq)).symm
    refine ⟨x, y, ?_⟩
    rw [hgeq, sylowToVec_mul]
    refine Prod.ext (funext fun a => by fin_cases a <;> simp [g0', g1', h00, h01, h10, h11])
      (Prod.ext (funext fun b => by simp [g0', g1', k]; ring)
        (funext fun c => by simp [g0', g1', ξ, η]; ring))
  · rintro ⟨x, y, hv⟩
    let g0' := vecToSylow (fun a => x * (sylowToVec g0).1 a,
      fun b => x * (sylowToVec g0).2.1 b, fun c => x * (sylowToVec g0).2.2 c)
    let g1' := vecToSylow (fun a => y * (sylowToVec g1).1 a,
      fun b => y * (sylowToVec g1).2.1 b, fun c => y * (sylowToVec g1).2.2 c)
    have h00 : (sylowToVec g0).1 0 = 1 := congrArg Prod.fst hπ0
    have h01 : (sylowToVec g0).1 1 = 0 := congrArg Prod.snd hπ0
    have h10 : (sylowToVec g1).1 0 = 0 := congrArg Prod.fst hπ1
    have h11 : (sylowToVec g1).1 1 = 1 := congrArg Prod.snd hπ1
    have hgeq : g = g0' * g1' := by
      apply sylowToVec_injective
      rw [hv, sylowToVec_mul]
      refine Prod.ext (funext fun a => by fin_cases a <;> simp [g0', g1', h00, h01, h10, h11])
        (Prod.ext (funext fun b => by simp [g0', g1', k]; ring)
          (funext fun c => by simp [g0', g1', ξ, η]; ring))
    rw [hgeq]
    exact H.mul_mem (mem_scale_sylow H hg0 x) (mem_scale_sylow H hg1 y)

private lemma graphRowSub_injective {q : ℕ} [NeZero q] :
    Function.Injective (fun p : (Fin 2 → Fin 2 → ZMod q) × (Fin 2 → ZMod q) × (Fin 2 → ZMod q) =>
      graphRowSub p.1 p.2.1 p.2.2) := by
  rintro ⟨k₁, ξ₁, η₁⟩ ⟨k₂, ξ₂, η₂⟩ hEq
  dsimp only at hEq
  have h1 : vecToSylow (fun a => if a = 0 then (1 : ZMod q) else 0,
      fun b => k₁ b 0, fun c => ξ₁ c) ∈ graphRowSub k₂ ξ₂ η₂ := by
    rw [← hEq, mem_graphRowSub_iff]
    exact ⟨1, 0, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩
  have h2 : vecToSylow (fun a => if a = 0 then (0 : ZMod q) else 1,
      fun b => k₁ b 1, fun c => η₁ c) ∈ graphRowSub k₂ ξ₂ η₂ := by
    rw [← hEq, mem_graphRowSub_iff]
    exact ⟨0, 1, by rw [sylowToVec_vecToSylow]; ext i <;> simp⟩
  rcases (mem_graphRowSub_iff k₂ ξ₂ η₂ _).mp h1 with ⟨x₁, y₁, hv₁⟩
  rcases (mem_graphRowSub_iff k₂ ξ₂ η₂ _).mp h2 with ⟨x₂, y₂, hv₂⟩
  rw [sylowToVec_vecToSylow] at hv₁ hv₂
  have hx₁ : x₁ = 1 := (congrArg (fun p => p.1 0) hv₁).symm
  have hy₁ : y₁ = 0 := (congrArg (fun p => p.1 1) hv₁).symm
  have hx₂ : x₂ = 0 := (congrArg (fun p => p.1 0) hv₂).symm
  have hy₂ : y₂ = 1 := (congrArg (fun p => p.1 1) hv₂).symm
  subst hx₁ hy₁ hx₂ hy₂
  refine Prod.ext (funext fun b => funext fun j => ?_)
    (Prod.ext (funext fun c => ?_) (funext fun c => ?_))
  · fin_cases j
    · simpa using congrArg (fun p => p.2.1 b) hv₁
    · simpa using congrArg (fun p => p.2.1 b) hv₂
  · simpa using congrArg (fun p => p.2.2 c) hv₁
  · simpa using congrArg (fun p => p.2.2 c) hv₂

private lemma rowFull_graphRowSub {q : ℕ} [NeZero q]
    (k : Fin 2 → Fin 2 → ZMod q) (ξ η : Fin 2 → ZMod q) :
    rowFull (graphRowSub k ξ η) := fun x y =>
  ⟨vecToSylow (fun a => if a = 0 then x else y,
      fun b => k b 0 * x + k b 1 * y, fun c => ξ c * x + η c * y),
    (mem_graphRowSub_iff k ξ η _).mpr ⟨x, y, sylowToVec_vecToSylow _⟩,
    by simp, by simp⟩

private lemma colFull_graphRowSub_iff {q : ℕ} [Fact q.Prime]
    (k : Fin 2 → Fin 2 → ZMod q) (ξ η : Fin 2 → ZMod q) :
    colFull (graphRowSub k ξ η) ↔ k 0 0 * k 1 1 ≠ k 0 1 * k 1 0 := by
  constructor
  · intro hfull hdet
    let f : ZMod q × ZMod q → ZMod q × ZMod q := fun p =>
      (k 0 0 * p.1 + k 0 1 * p.2, k 1 0 * p.1 + k 1 1 * p.2)
    have hsurj : Function.Surjective f := fun ⟨u, v⟩ => by
      rcases hfull u v with ⟨g, hg, h0, h1⟩
      rcases (mem_graphRowSub_iff k ξ η g).mp hg with ⟨x, y, hv⟩
      rw [hv] at h0 h1
      exact ⟨(x, y), Prod.ext h0 h1⟩
    have hinj : Function.Injective f := (Finite.injective_iff_surjective).mpr hsurj
    by_cases h0 : k 0 0 = 0 ∧ k 0 1 = 0
    · rcases hsurj (1, 0) with ⟨p, hp⟩
      have h1 := congrArg Prod.fst hp
      simp [f, h0.1, h0.2] at h1
    · have hnz : (k 0 1, -k 0 0) ≠ (0, 0) := by
        intro h; apply h0
        exact ⟨neg_eq_zero.mp (congrArg Prod.snd h), congrArg Prod.fst h⟩
      have hf : f (k 0 1, -k 0 0) = f (0, 0) := by
        dsimp [f]
        apply Prod.ext
        · ring
        · linear_combination -hdet
      exact hnz (hinj hf)
  · intro hdet u v
    let d := k 0 0 * k 1 1 - k 0 1 * k 1 0
    have hd : d ≠ 0 := sub_ne_zero.mpr hdet
    let x := (k 1 1 * u - k 0 1 * v) * d⁻¹
    let y := (-k 1 0 * u + k 0 0 * v) * d⁻¹
    refine ⟨vecToSylow (fun a => if a = 0 then x else y,
        fun b => k b 0 * x + k b 1 * y, fun c => ξ c * x + η c * y),
      (mem_graphRowSub_iff k ξ η _).mpr ⟨x, y, sylowToVec_vecToSylow _⟩, ?_, ?_⟩
    · rw [sylowToVec_vecToSylow]; dsimp [x, y]
      calc k 0 0 * ((k 1 1 * u - k 0 1 * v) * d⁻¹) + k 0 1 * ((-k 1 0 * u + k 0 0 * v) * d⁻¹)
          = u * (d * d⁻¹) := by dsimp [d]; ring
        _ = u := by rw [mul_inv_cancel₀ hd, mul_one]
    · rw [sylowToVec_vecToSylow]; dsimp [x, y]
      calc k 1 0 * ((k 1 1 * u - k 0 1 * v) * d⁻¹) + k 1 1 * ((-k 1 0 * u + k 0 0 * v) * d⁻¹)
          = v * (d * d⁻¹) := by dsimp [d]; ring
        _ = v := by rw [mul_inv_cancel₀ hd, mul_one]

private lemma sylowToVec_transpose {q : ℕ} [NeZero q] (g : sylowP q) :
    ∃ g' : sylowP q, g' ∈ transposeSubgroup (Subgroup.closure {g}) ∧
      sylowToVec g' = ((sylowToVec g).2.1, (sylowToVec g).1, (sylowToVec g).2.2) := by
  let g' := vecToSylow ((sylowToVec g).2.1, (sylowToVec g).1, (sylowToVec g).2.2)
  refine ⟨g', ?_, sylowToVec_vecToSylow _⟩
  refine ⟨g, Subgroup.subset_closure (Set.mem_singleton g), ?_⟩
  apply Subtype.ext
  have hg := sylowToVec_val g
  rw [vecToSylow_val]
  change (g.1.2.1, g.1.1, g.1.2.2) = _
  rw [hg]

private lemma mem_transposeSubgroup_iff {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) (g : sylowP q) :
    g ∈ transposeSubgroup H ↔
      vecToSylow ((sylowToVec g).2.1, (sylowToVec g).1, (sylowToVec g).2.2) ∈ H := by
  let sw : sylowP q → sylowP q := fun h =>
    vecToSylow ((sylowToVec h).2.1, (sylowToVec h).1, (sylowToVec h).2.2)
  have hsw_val : ∀ h : sylowP q, (sw h).1 = (h.1.2.1, h.1.1, h.1.2.2) := fun h => by
    dsimp [sw]; rw [vecToSylow_val, sylowToVec_val h]
  have hsw_invol : ∀ h : sylowP q, sw (sw h) = h := fun h => by
    apply sylowToVec_injective; simp [sw]
  constructor
  · rintro ⟨h, hh, hEq⟩
    have hswg : sw g = h := by
      apply Subtype.ext
      rw [hsw_val]
      have h1 := congrArg Subtype.val hEq
      change (h.1.2.1, h.1.1, h.1.2.2) = g.1 at h1
      rw [← h1]
    simpa [sw, hswg] using hh
  · intro hg
    refine ⟨sw g, hg, ?_⟩
    apply Subtype.ext
    change ((sw g).1.2.1, (sw g).1.1, (sw g).1.2.2) = g.1
    rw [hsw_val]

private lemma transposeSubgroup_invol {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) :
    transposeSubgroup (transposeSubgroup H) = H := by
  ext g
  rw [mem_transposeSubgroup_iff, mem_transposeSubgroup_iff]
  simp only [sylowToVec_vecToSylow]
  have hvec : vecToSylow ((sylowToVec g).1, (sylowToVec g).2.1, (sylowToVec g).2.2) = g :=
    vecToSylow_sylowToVec g
  rw [hvec]

private lemma elemRank_transposeSubgroup {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) :
    elemRank q (transposeSubgroup H) = elemRank q H := by
  unfold elemRank
  congr 1
  refine Nat.card_congr
    { toFun := fun g => ⟨vecToSylow ((sylowToVec g.1).2.1, (sylowToVec g.1).1, (sylowToVec g.1).2.2),
        (mem_transposeSubgroup_iff H g.1).mp g.2⟩
      invFun := fun g => ⟨vecToSylow ((sylowToVec g.1).2.1, (sylowToVec g.1).1, (sylowToVec g.1).2.2),
        (mem_transposeSubgroup_iff H _).mpr (by simpa using g.2)⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }

private lemma rowFull_transposeSubgroup {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) :
    rowFull (transposeSubgroup H) ↔ colFull H := by
  constructor
  · intro h x y
    rcases h x y with ⟨g, hg, h0, h1⟩
    refine ⟨vecToSylow ((sylowToVec g).2.1, (sylowToVec g).1, (sylowToVec g).2.2),
      (mem_transposeSubgroup_iff H g).mp hg, by simpa using h0, by simpa using h1⟩
  · intro h x y
    rcases h x y with ⟨g, hg, h0, h1⟩
    refine ⟨vecToSylow ((sylowToVec g).2.1, (sylowToVec g).1, (sylowToVec g).2.2),
      (mem_transposeSubgroup_iff H _).mpr (by simpa using hg),
      by simpa using h0, by simpa using h1⟩

private lemma colFull_transposeSubgroup {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) :
    colFull (transposeSubgroup H) ↔ rowFull H := by
  rw [← rowFull_transposeSubgroup, transposeSubgroup_invol]

private lemma not_rowFull_not_colFull_cases {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (H : Subgroup (sylowP q)) (hrank : elemRank q H = 2)
    (hR : ¬ rowFull H) (hC : ¬ colFull H) :
    S_twoq q H = 0 ∨ ∃ r s : (ZMod q)ˣ, ∃ ξ η : Fin 2 → ZMod q, H = graphR11Sub r s ξ η := by
  have hq : q.Prime := Fact.out
  have hne : H ≠ ⊥ := by
    intro hbot; rw [hbot] at hrank; simp [elemRank, Nat.log_one_right] at hrank
  -- If any row or col block is fixed by `H`, then `S_twoq q H = 0`
  by_cases hr0 : ∀ g ∈ H, (sylowToVec g).1 0 = 0
  · left; refine lem_6_6_part1 hq hodd H hne (Or.inr ⟨blockEquiv q (0, 0), fun g hg => ?_⟩)
    have hv := sylowToVec_val g
    have hrow : g.1.1 = blockTransPerm q (sylowToVec g).1 := by rw [hv]
    rw [hrow, blockTransPerm_apply, hr0 g hg, add_zero]
  by_cases hr1 : ∀ g ∈ H, (sylowToVec g).1 1 = 0
  · left; refine lem_6_6_part1 hq hodd H hne (Or.inr ⟨blockEquiv q (1, 0), fun g hg => ?_⟩)
    have hv := sylowToVec_val g
    have hrow : g.1.1 = blockTransPerm q (sylowToVec g).1 := by rw [hv]
    rw [hrow, blockTransPerm_apply, hr1 g hg, add_zero]
  by_cases hc0 : ∀ g ∈ H, (sylowToVec g).2.1 0 = 0
  · left; refine lem_6_6_part1 hq hodd H hne (Or.inl ⟨blockEquiv q (0, 0), fun g hg => ?_⟩)
    have hv := sylowToVec_val g
    have hcol : g.1.2.1 = blockTransPerm q (sylowToVec g).2.1 := by rw [hv]
    rw [hcol, blockTransPerm_apply, hc0 g hg, add_zero]
  by_cases hc1 : ∀ g ∈ H, (sylowToVec g).2.1 1 = 0
  · left; refine lem_6_6_part1 hq hodd H hne (Or.inl ⟨blockEquiv q (1, 0), fun g hg => ?_⟩)
    have hv := sylowToVec_val g
    have hcol : g.1.2.1 = blockTransPerm q (sylowToVec g).2.1 := by rw [hv]
    rw [hcol, blockTransPerm_apply, hc1 g hg, add_zero]
  push Not at hr0 hr1 hc0 hc1
  -- Extract unique proportionality `u 1 = r * u 0` (with `r ≠ 0`) and `v 1 = s * v 0` (with `s ≠ 0`)
  rcases hr0 with ⟨gr, hgr, hgr0⟩
  let gr1 := vecToSylow (fun a => ((sylowToVec gr).1 0)⁻¹ * (sylowToVec gr).1 a,
    fun b => ((sylowToVec gr).1 0)⁻¹ * (sylowToVec gr).2.1 b,
    fun c => ((sylowToVec gr).1 0)⁻¹ * (sylowToVec gr).2.2 c)
  have hgr1H : gr1 ∈ H := mem_scale_sylow H hgr _
  have hgr1_0 : (sylowToVec gr1).1 0 = 1 := by
    rw [sylowToVec_vecToSylow]; exact inv_mul_cancel₀ hgr0
  let r0 : ZMod q := (sylowToVec gr1).1 1
  have hpropR : ∀ g ∈ H, (sylowToVec g).1 1 = r0 * (sylowToVec g).1 0 := by
    intro g hg
    by_contra hne_r
    let x := (sylowToVec g).1 0
    let gdiff := g * (vecToSylow (fun a => (-x) * (sylowToVec gr1).1 a,
      fun b => (-x) * (sylowToVec gr1).2.1 b, fun c => (-x) * (sylowToVec gr1).2.2 c))
    have hgdiffH : gdiff ∈ H := H.mul_mem hg (mem_scale_sylow H hgr1H (-x))
    have hd0 : (sylowToVec gdiff).1 0 = 0 := by
      dsimp only [gdiff]; rw [sylowToVec_mul, sylowToVec_vecToSylow]
      change x + (-x) * (sylowToVec gr1).1 0 = 0; rw [hgr1_0]; ring
    have hd1 : (sylowToVec gdiff).1 1 ≠ 0 := by
      dsimp only [gdiff]; rw [sylowToVec_mul, sylowToVec_vecToSylow]
      change (sylowToVec g).1 1 + (-x) * r0 ≠ 0
      intro h0; apply hne_r; linear_combination h0
    let g01 := vecToSylow (fun a => ((sylowToVec gdiff).1 1)⁻¹ * (sylowToVec gdiff).1 a,
      fun b => ((sylowToVec gdiff).1 1)⁻¹ * (sylowToVec gdiff).2.1 b,
      fun c => ((sylowToVec gdiff).1 1)⁻¹ * (sylowToVec gdiff).2.2 c)
    have hg01H : g01 ∈ H := mem_scale_sylow H hgdiffH _
    apply hR
    intro u v
    let g1a := vecToSylow (fun a => u * (sylowToVec gr1).1 a,
        fun b => u * (sylowToVec gr1).2.1 b, fun c => u * (sylowToVec gr1).2.2 c)
    let g1b := vecToSylow (fun a => (v - u * r0) * (sylowToVec g01).1 a,
        fun b => (v - u * r0) * (sylowToVec g01).2.1 b,
        fun c => (v - u * r0) * (sylowToVec g01).2.2 c)
    have hg1a : sylowToVec g1a = (fun a => u * (sylowToVec gr1).1 a,
        fun b => u * (sylowToVec gr1).2.1 b, fun c => u * (sylowToVec gr1).2.2 c) :=
      sylowToVec_vecToSylow _
    have hg1b : sylowToVec g1b = (fun a => (v - u * r0) * (sylowToVec g01).1 a,
        fun b => (v - u * r0) * (sylowToVec g01).2.1 b,
        fun c => (v - u * r0) * (sylowToVec g01).2.2 c) :=
      sylowToVec_vecToSylow _
    refine ⟨g1a * g1b, H.mul_mem (mem_scale_sylow H hgr1H u) (mem_scale_sylow H hg01H _), ?_, ?_⟩
    · rw [sylowToVec_mul, hg1a, hg1b]
      change u * (sylowToVec gr1).1 0 + (v - u * r0) * (sylowToVec g01).1 0 = u
      rw [hgr1_0]; simp [g01, hd0]
    · rw [sylowToVec_mul, hg1a, hg1b]
      change u * r0 + (v - u * r0) * (sylowToVec g01).1 1 = v
      have h11 : (sylowToVec g01).1 1 = 1 := by
        rw [sylowToVec_vecToSylow]; exact inv_mul_cancel₀ hd1
      rw [h11]; ring
  have hr0_ne : r0 ≠ 0 := by
    intro h0; rcases hr1 with ⟨g, hg, hg1⟩
    have := hpropR g hg; rw [h0, zero_mul] at this; exact hg1 this
  -- Same for columns
  rcases hc0 with ⟨gc, hgc, hgc0⟩
  let gc1 := vecToSylow (fun a => ((sylowToVec gc).2.1 0)⁻¹ * (sylowToVec gc).1 a,
    fun b => ((sylowToVec gc).2.1 0)⁻¹ * (sylowToVec gc).2.1 b,
    fun c => ((sylowToVec gc).2.1 0)⁻¹ * (sylowToVec gc).2.2 c)
  have hgc1H : gc1 ∈ H := mem_scale_sylow H hgc _
  have hgc1_0 : (sylowToVec gc1).2.1 0 = 1 := by
    rw [sylowToVec_vecToSylow]; exact inv_mul_cancel₀ hgc0
  let s0 : ZMod q := (sylowToVec gc1).2.1 1
  have hpropC : ∀ g ∈ H, (sylowToVec g).2.1 1 = s0 * (sylowToVec g).2.1 0 := by
    intro g hg
    by_contra hne_s
    let y := (sylowToVec g).2.1 0
    let gdiff := g * (vecToSylow (fun a => (-y) * (sylowToVec gc1).1 a,
      fun b => (-y) * (sylowToVec gc1).2.1 b, fun c => (-y) * (sylowToVec gc1).2.2 c))
    have hgdiffH : gdiff ∈ H := H.mul_mem hg (mem_scale_sylow H hgc1H (-y))
    have hd0 : (sylowToVec gdiff).2.1 0 = 0 := by
      dsimp only [gdiff]; rw [sylowToVec_mul, sylowToVec_vecToSylow]
      change y + (-y) * (sylowToVec gc1).2.1 0 = 0; rw [hgc1_0]; ring
    have hd1 : (sylowToVec gdiff).2.1 1 ≠ 0 := by
      dsimp only [gdiff]; rw [sylowToVec_mul, sylowToVec_vecToSylow]
      change (sylowToVec g).2.1 1 + (-y) * s0 ≠ 0
      intro h0; apply hne_s; linear_combination h0
    let g01 := vecToSylow (fun a => ((sylowToVec gdiff).2.1 1)⁻¹ * (sylowToVec gdiff).1 a,
      fun b => ((sylowToVec gdiff).2.1 1)⁻¹ * (sylowToVec gdiff).2.1 b,
      fun c => ((sylowToVec gdiff).2.1 1)⁻¹ * (sylowToVec gdiff).2.2 c)
    have hg01H : g01 ∈ H := mem_scale_sylow H hgdiffH _
    apply hC
    intro u v
    let g1a := vecToSylow (fun a => u * (sylowToVec gc1).1 a,
        fun b => u * (sylowToVec gc1).2.1 b, fun c => u * (sylowToVec gc1).2.2 c)
    let g1b := vecToSylow (fun a => (v - u * s0) * (sylowToVec g01).1 a,
        fun b => (v - u * s0) * (sylowToVec g01).2.1 b,
        fun c => (v - u * s0) * (sylowToVec g01).2.2 c)
    have hg1a : sylowToVec g1a = (fun a => u * (sylowToVec gc1).1 a,
        fun b => u * (sylowToVec gc1).2.1 b, fun c => u * (sylowToVec gc1).2.2 c) :=
      sylowToVec_vecToSylow _
    have hg1b : sylowToVec g1b = (fun a => (v - u * s0) * (sylowToVec g01).1 a,
        fun b => (v - u * s0) * (sylowToVec g01).2.1 b,
        fun c => (v - u * s0) * (sylowToVec g01).2.2 c) :=
      sylowToVec_vecToSylow _
    refine ⟨g1a * g1b, H.mul_mem (mem_scale_sylow H hgc1H u) (mem_scale_sylow H hg01H _), ?_, ?_⟩
    · rw [sylowToVec_mul, hg1a, hg1b]
      change u * (sylowToVec gc1).2.1 0 + (v - u * s0) * (sylowToVec g01).2.1 0 = u
      rw [hgc1_0]; simp [g01, hd0]
    · rw [sylowToVec_mul, hg1a, hg1b]
      change u * s0 + (v - u * s0) * (sylowToVec g01).2.1 1 = v
      have h11 : (sylowToVec g01).2.1 1 = 1 := by
        rw [sylowToVec_vecToSylow]; exact inv_mul_cancel₀ hd1
      rw [h11]; ring
  have hs0_ne : s0 ≠ 0 := by
    intro h0; rcases hc1 with ⟨g, hg, hg1⟩
    have := hpropC g hg; rw [h0, zero_mul] at this; exact hg1 this
  -- Now test whether `π₀ : H → ZMod q × ZMod q`, `g ↦ (u 0, v 0)` is injective
  let π₀ : H → ZMod q × ZMod q := fun g => ((sylowToVec g.1).1 0, (sylowToVec g.1).2.1 0)
  by_cases hinj : Function.Injective π₀
  · right
    let _ : Fintype (sylowP q) := Fintype.ofFinite _
    have hcardH : Nat.card H = q ^ 2 := by
      rw [card_eq_pow_elemRank_of_elemAbelian hq (isElemAbelian_sylowP_subgroup q H), hrank]
    have hbij : Function.Bijective π₀ := by
      let _ : Fintype H := Fintype.ofFinite H
      have hcard_eq : Fintype.card H = Fintype.card (ZMod q × ZMod q) := by
        rw [← Nat.card_eq_fintype_card, hcardH, Fintype.card_prod, ZMod.card, sq]
      exact (Fintype.bijective_iff_injective_and_card π₀).mpr ⟨hinj, hcard_eq⟩
    obtain ⟨⟨e0, he0⟩, hπe0⟩ := hbij.2 (1, 0)
    obtain ⟨⟨e1, he1⟩, hπe1⟩ := hbij.2 (0, 1)
    let r : (ZMod q)ˣ := Units.mk0 r0 hr0_ne
    let s : (ZMod q)ˣ := Units.mk0 s0 hs0_ne
    let ξ : Fin 2 → ZMod q := (sylowToVec e0).2.2
    let η : Fin 2 → ZMod q := (sylowToVec e1).2.2
    refine ⟨r, s, ξ, η, ?_⟩
    have he0_r0 : (sylowToVec e0).1 0 = 1 := congrArg Prod.fst hπe0
    have he0_c0 : (sylowToVec e0).2.1 0 = 0 := congrArg Prod.snd hπe0
    have he1_r0 : (sylowToVec e1).1 0 = 0 := congrArg Prod.fst hπe1
    have he1_c0 : (sylowToVec e1).2.1 0 = 1 := congrArg Prod.snd hπe1
    have he0_r1 : (sylowToVec e0).1 1 = r0 := by rw [hpropR e0 he0, he0_r0, mul_one]
    have he0_c1 : (sylowToVec e0).2.1 1 = 0 := by rw [hpropC e0 he0, he0_c0, mul_zero]
    have he1_r1 : (sylowToVec e1).1 1 = 0 := by rw [hpropR e1 he1, he1_r0, mul_zero]
    have he1_c1 : (sylowToVec e1).2.1 1 = s0 := by rw [hpropC e1 he1, he1_c0, mul_one]
    ext g
    rw [mem_graphR11Sub_iff]
    constructor
    · intro hgH
      let x := (sylowToVec g).1 0
      let y := (sylowToVec g).2.1 0
      let g0' := vecToSylow (fun a => x * (sylowToVec e0).1 a,
        fun b => x * (sylowToVec e0).2.1 b, fun c => x * (sylowToVec e0).2.2 c)
      let g1' := vecToSylow (fun a => y * (sylowToVec e1).1 a,
        fun b => y * (sylowToVec e1).2.1 b, fun c => y * (sylowToVec e1).2.2 c)
      have hmulH : g0' * g1' ∈ H := H.mul_mem (mem_scale_sylow H he0 x) (mem_scale_sylow H he1 y)
      have hπeq : π₀ ⟨g0' * g1', hmulH⟩ = π₀ ⟨g, hgH⟩ := by
        apply Prod.ext
        · change (sylowToVec (g0' * g1')).1 0 = x
          rw [sylowToVec_mul]; dsimp only [g0', g1']; rw [sylowToVec_vecToSylow, sylowToVec_vecToSylow]
          change x * (sylowToVec e0).1 0 + y * (sylowToVec e1).1 0 = x
          rw [he0_r0, he1_r0]; ring
        · change (sylowToVec (g0' * g1')).2.1 0 = y
          rw [sylowToVec_mul]; dsimp only [g0', g1']; rw [sylowToVec_vecToSylow, sylowToVec_vecToSylow]
          change x * (sylowToVec e0).2.1 0 + y * (sylowToVec e1).2.1 0 = y
          rw [he0_c0, he1_c0]; ring
      have hgeq : g = g0' * g1' := (congrArg Subtype.val (hinj hπeq)).symm
      refine ⟨x, y, ?_⟩
      rw [hgeq, sylowToVec_mul]
      refine Prod.ext (funext fun a => by fin_cases a <;>
          simp [g0', g1', he0_r0, he0_r1, he1_r0, he1_r1, r]; ring)
        (Prod.ext (funext fun b => by fin_cases b <;>
            simp [g0', g1', he0_c0, he0_c1, he1_c0, he1_c1, s]; ring)
          (funext fun c => by simp [g0', g1', ξ, η]; ring))
    · rintro ⟨x, y, hv⟩
      let g0' := vecToSylow (fun a => x * (sylowToVec e0).1 a,
        fun b => x * (sylowToVec e0).2.1 b, fun c => x * (sylowToVec e0).2.2 c)
      let g1' := vecToSylow (fun a => y * (sylowToVec e1).1 a,
        fun b => y * (sylowToVec e1).2.1 b, fun c => y * (sylowToVec e1).2.2 c)
      have hgeq : g = g0' * g1' := by
        apply sylowToVec_injective
        rw [hv, sylowToVec_mul]
        refine Prod.ext (funext fun a => by fin_cases a <;>
            simp [g0', g1', he0_r0, he0_r1, he1_r0, he1_r1, r]; ring)
          (Prod.ext (funext fun b => by fin_cases b <;>
              simp [g0', g1', he0_c0, he0_c1, he1_c0, he1_c1, s]; ring)
            (funext fun c => by simp [g0', g1', ξ, η]; ring))
      rw [hgeq]
      exact H.mul_mem (mem_scale_sylow H he0 x) (mem_scale_sylow H he1 y)
  · -- Not injective -> nonzero element fixing all rows and columns -> Fact 1 -> `S(H) = 0`
    left
    unfold Function.Injective at hinj
    push Not at hinj
    rcases hinj with ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩, hπeq, hne12⟩
    let gd := g₁ * g₂⁻¹
    have hgdH : gd ∈ H := H.mul_mem hg₁ (H.inv_mem hg₂)
    have hgd1 : gd ≠ 1 := fun h1 => hne12 (Subtype.ext (mul_inv_eq_one.mp h1))
    have hgd_r0 : (sylowToVec gd).1 0 = 0 := by
      rw [sylowToVec_mul, sylowToVec_inv]
      change (sylowToVec g₁).1 0 + -(sylowToVec g₂).1 0 = 0
      have hp1 : (sylowToVec g₁).1 0 = (sylowToVec g₂).1 0 := congrArg Prod.fst hπeq
      rw [hp1, add_neg_cancel]
    have hgd_c0 : (sylowToVec gd).2.1 0 = 0 := by
      rw [sylowToVec_mul, sylowToVec_inv]
      change (sylowToVec g₁).2.1 0 + -(sylowToVec g₂).2.1 0 = 0
      have hp2 : (sylowToVec g₁).2.1 0 = (sylowToVec g₂).2.1 0 := congrArg Prod.snd hπeq
      rw [hp2, add_neg_cancel]
    have hgd_c : (sylowToVec gd).2.1 = 0 := by
      ext b
      rcases (by fin_cases b <;> simp : b = 0 ∨ b = 1) with rfl | rfl
      · exact hgd_c0
      · rw [hpropC gd hgdH, hgd_c0, mul_zero]; rfl
    have hempty := fixSet_empty_of_fix_all_cols_and_row H gd hgdH hgd1 hgd_c 0 hgd_r0
    unfold S_twoq signedFixSum
    rw [hempty]; simp

private lemma graphR11Sub_injective {q : ℕ} [NeZero q] :
    Function.Injective (fun p : (ZMod q)ˣ × (ZMod q)ˣ × (Fin 2 → ZMod q) × (Fin 2 → ZMod q) =>
      graphR11Sub p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rintro ⟨r₁, s₁, ξ₁, η₁⟩ ⟨r₂, s₂, ξ₂, η₂⟩ hEq
  dsimp only at hEq
  have h1 : vecToSylow (fun a => if a = 0 then (1 : ZMod q) else r₁.1,
      fun _ => 0, fun c => ξ₁ c) ∈ graphR11Sub r₂ s₂ ξ₂ η₂ := by
    rw [← hEq, mem_graphR11Sub_iff]
    exact ⟨1, 0, by rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp⟩
  have h2 : vecToSylow (fun _ => 0,
      fun b => if b = 0 then (1 : ZMod q) else s₁.1, fun c => η₁ c) ∈ graphR11Sub r₂ s₂ ξ₂ η₂ := by
    rw [← hEq, mem_graphR11Sub_iff]
    exact ⟨0, 1, by rw [sylowToVec_vecToSylow]; ext i <;> fin_cases i <;> simp⟩
  rcases (mem_graphR11Sub_iff r₂ s₂ ξ₂ η₂ _).mp h1 with ⟨x₁, y₁, hv₁⟩
  rcases (mem_graphR11Sub_iff r₂ s₂ ξ₂ η₂ _).mp h2 with ⟨x₂, y₂, hv₂⟩
  rw [sylowToVec_vecToSylow] at hv₁ hv₂
  have hx₁ : x₁ = 1 := (congrArg (fun p => p.1 0) hv₁).symm
  have hy₁ : y₁ = 0 := (congrArg (fun p => p.2.1 0) hv₁).symm
  have hx₂ : x₂ = 0 := (congrArg (fun p => p.1 0) hv₂).symm
  have hy₂ : y₂ = 1 := (congrArg (fun p => p.2.1 0) hv₂).symm
  subst hx₁ hy₁ hx₂ hy₂
  refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_)
    (Prod.ext (funext fun c => ?_) (funext fun c => ?_)))
  · simpa using congrArg (fun p => p.1 1) hv₁
  · simpa using congrArg (fun p => p.2.1 1) hv₂
  · simpa using congrArg (fun p => p.2.2 c) hv₁
  · simpa using congrArg (fun p => p.2.2 c) hv₂

private lemma not_rowFull_graphR11Sub {q : ℕ} [Fact q.Prime]
    (r s : (ZMod q)ˣ) (ξ η : Fin 2 → ZMod q) :
    ¬ rowFull (graphR11Sub r s ξ η) := by
  intro h
  rcases h 0 1 with ⟨g, hg, h0, h1⟩
  rcases (mem_graphR11Sub_iff r s ξ η g).mp hg with ⟨x, y, hv⟩
  rw [hv] at h0 h1
  simp only [↓reduceIte, one_ne_zero] at h0 h1
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

private lemma not_colFull_graphR11Sub {q : ℕ} [Fact q.Prime]
    (r s : (ZMod q)ˣ) (ξ η : Fin 2 → ZMod q) :
    ¬ colFull (graphR11Sub r s ξ η) := by
  intro h
  rcases h 0 1 with ⟨g, hg, h0, h1⟩
  rcases (mem_graphR11Sub_iff r s ξ η g).mp hg with ⟨x, y, hv⟩
  rw [hv] at h0 h1
  simp only [↓reduceIte, one_ne_zero] at h0 h1
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

/-! ### Exact Formula for `∑_{r(H)=2} S(H)` and Divisibility by `q^5` -/

/-- Exact formula for the rank-2 sum `∑_{r(H)=2} S(H)`. -/
theorem sum_rank_two_formula (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) =
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) - 2) * ((q : ℤ) + 1) -
      8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q +
      4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by have := hq.two_le; omega
  let R2 := sylowSubgroupsOfRank q 2
  let P_RF_CF := R2.filter (fun H => rowFull H ∧ colFull H)
  let P_RF_nCF := R2.filter (fun H => rowFull H ∧ ¬ colFull H)
  let P_nRF_CF := R2.filter (fun H => ¬ rowFull H ∧ colFull H)
  let P_nRF_nCF := R2.filter (fun H => ¬ rowFull H ∧ ¬ colFull H)
  have hpart :
      ∑ H ∈ R2, S_twoq q H =
      (∑ H ∈ P_RF_CF, S_twoq q H) + (∑ H ∈ P_RF_nCF, S_twoq q H) +
      (∑ H ∈ P_nRF_CF, S_twoq q H) + (∑ H ∈ P_nRF_nCF, S_twoq q H) := by
    have h1 := (Finset.sum_filter_add_sum_filter_not R2 (fun H => rowFull H) (S_twoq q)).symm
    have h2 := (Finset.sum_filter_add_sum_filter_not
      (R2.filter (fun H => rowFull H)) (fun H => colFull H) (S_twoq q)).symm
    have h3 := (Finset.sum_filter_add_sum_filter_not
      (R2.filter (fun H => ¬ rowFull H)) (fun H => colFull H) (S_twoq q)).symm
    simp only [Finset.filter_filter] at h2 h3
    rw [h1, h2, h3]
    change _ = _ + _ + _ + _
    ring
  rw [hpart]
  -- 1. `P_RF_CF` sum
  have h1 : ∑ H ∈ P_RF_CF, S_twoq q H =
      4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2 -
      8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q +
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) ^ 2 - 2 * (q : ℤ) - 3) := by
    let dom := (Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q =>
        k 0 0 * k 1 1 ≠ k 0 1 * k 1 0)) ×ˢ
      ((Finset.univ : Finset (Fin 2 → ZMod q)) ×ˢ (Finset.univ : Finset (Fin 2 → ZMod q)))
    have hbij : ∑ H ∈ P_RF_CF, S_twoq q H =
        ∑ p ∈ dom, S_twoq q (graphRowSub p.1 p.2.1 p.2.2) := by
      symm
      refine Finset.sum_bij (fun p _ => graphRowSub p.1 p.2.1 p.2.2) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro p hp
        simp only [dom, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [P_RF_CF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨elemRank_graphRowSub hq p.1 p.2.1 p.2.2, rowFull_graphRowSub p.1 p.2.1 p.2.2,
          (colFull_graphRowSub_iff p.1 p.2.1 p.2.2).mpr hp.1⟩
      · intro p₁ _ p₂ _ hEq; exact graphRowSub_injective hEq
      · intro H hH
        simp only [P_RF_CF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ, true_and]
          at hH
        rcases rowFull_eq_graphRowSub H hH.1 hH.2.1 with ⟨k, ξ, η, rfl⟩
        refine ⟨(k, ξ, η), ?_, rfl⟩
        simp only [dom, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(colFull_graphRowSub_iff k ξ η).mp hH.2.2, trivial⟩
    rw [hbij]
    simp only [dom, Finset.sum_product]
    exact sum_sumGraphRow_det_ne_zero hodd
  -- 2. `P_RF_nCF` sum
  have h2 : ∑ H ∈ P_RF_nCF, S_twoq q H = 2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 := by
    let dom := (Finset.univ.filter (fun k : Fin 2 → Fin 2 → ZMod q =>
        k 0 0 * k 1 1 = k 0 1 * k 1 0)) ×ˢ
      ((Finset.univ : Finset (Fin 2 → ZMod q)) ×ˢ (Finset.univ : Finset (Fin 2 → ZMod q)))
    have hbij : ∑ H ∈ P_RF_nCF, S_twoq q H =
        ∑ p ∈ dom, S_twoq q (graphRowSub p.1 p.2.1 p.2.2) := by
      symm
      refine Finset.sum_bij (fun p _ => graphRowSub p.1 p.2.1 p.2.2) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro p hp
        simp only [dom, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [P_RF_nCF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨elemRank_graphRowSub hq p.1 p.2.1 p.2.2, rowFull_graphRowSub p.1 p.2.1 p.2.2,
          fun hc => (colFull_graphRowSub_iff p.1 p.2.1 p.2.2).mp hc hp.1⟩
      · intro p₁ _ p₂ _ hEq; exact graphRowSub_injective hEq
      · intro H hH
        simp only [P_RF_nCF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ, true_and]
          at hH
        rcases rowFull_eq_graphRowSub H hH.1 hH.2.1 with ⟨k, ξ, η, rfl⟩
        refine ⟨(k, ξ, η), ?_, rfl⟩
        simp only [dom, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
        have hdet : k 0 0 * k 1 1 = k 0 1 * k 1 0 :=
          by_contra fun hne => hH.2.2 ((colFull_graphRowSub_iff k ξ η).mpr hne)
        exact ⟨hdet, trivial⟩
    rw [hbij]
    simp only [dom, Finset.sum_product]
    exact sum_sumGraphRow_det_eq_zero hodd
  -- 3. `P_nRF_CF` sum = `P_RF_nCF` sum via `transposeSubgroup`
  have h3 : ∑ H ∈ P_nRF_CF, S_twoq q H = 2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 := by
    rw [← h2]
    refine Finset.sum_bij (fun H _ => transposeSubgroup H) ?_ ?_ ?_ ?_
    · intro H hH
      simp only [P_nRF_CF, P_RF_nCF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ,
        true_and] at hH ⊢
      exact ⟨by rw [elemRank_transposeSubgroup]; exact hH.1,
        (rowFull_transposeSubgroup H).mpr hH.2.2,
        fun hc => hH.2.1 ((colFull_transposeSubgroup H).mp hc)⟩
    · intro H₁ _ H₂ _ hEq
      have := congrArg transposeSubgroup hEq
      rwa [transposeSubgroup_invol, transposeSubgroup_invol] at this
    · intro H hH
      refine ⟨transposeSubgroup H, ?_, transposeSubgroup_invol H⟩
      simp only [P_nRF_CF, P_RF_nCF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ,
        true_and] at hH ⊢
      exact ⟨by rw [elemRank_transposeSubgroup]; exact hH.1,
        fun hr => hH.2.2 ((rowFull_transposeSubgroup H).mp hr),
        (colFull_transposeSubgroup H).mpr hH.2.1⟩
    · intro H _
      exact ((lem_6_4_signs q hodd).2.2.2.2.2.2.2 H).2.symm
  -- 4. `P_nRF_nCF` sum = `R_11 = 2 * q^4 * (q - 1)^6`
  have h4 : ∑ H ∈ P_nRF_nCF, S_twoq q H = 2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 6 := by
    let S11 := P_nRF_nCF.filter (fun H =>
      ∃ r s : (ZMod q)ˣ, ∃ ξ η : Fin 2 → ZMod q, H = graphR11Sub r s ξ η)
    have hsub : ∑ H ∈ P_nRF_nCF, S_twoq q H = ∑ H ∈ S11, S_twoq q H := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro H hH hnot
      have hH_mem : H ∈ P_nRF_nCF := hH
      simp only [S11, Finset.mem_filter, not_and] at hnot
      simp only [P_nRF_nCF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ, true_and]
        at hH
      rcases not_rowFull_not_colFull_cases hodd H hH.1 hH.2.1 hH.2.2 with hzero | hex
      · exact hzero
      · exact (hnot hH_mem hex).elim
    rw [hsub]
    have hbij : ∑ H ∈ S11, S_twoq q H =
        ∑ p : (ZMod q)ˣ × (ZMod q)ˣ × (Fin 2 → ZMod q) × (Fin 2 → ZMod q),
          S_twoq q (graphR11Sub p.1 p.2.1 p.2.2.1 p.2.2.2) := by
      symm
      refine Finset.sum_bij (fun p _ => graphR11Sub p.1 p.2.1 p.2.2.1 p.2.2.2) ?_ ?_ ?_
        (fun _ _ => rfl)
      · intro p _
        simp only [S11, P_nRF_nCF, R2, sylowSubgroupsOfRank, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨⟨elemRank_graphR11Sub hq p.1 p.2.1 p.2.2.1 p.2.2.2,
          not_rowFull_graphR11Sub p.1 p.2.1 p.2.2.1 p.2.2.2,
          not_colFull_graphR11Sub p.1 p.2.1 p.2.2.1 p.2.2.2⟩,
          p.1, p.2.1, p.2.2.1, p.2.2.2, rfl⟩
      · intro p₁ _ p₂ _ hEq; exact graphR11Sub_injective hEq
      · intro H hH
        simp only [S11, Finset.mem_filter] at hH
        rcases hH.2 with ⟨r, s, ξ, η, rfl⟩
        exact ⟨(r, s, ξ, η), Finset.mem_univ _, rfl⟩
    rw [hbij]
    simp_rw [Fintype.sum_prod_type]
    have hinner : ∀ r s : (ZMod q)ˣ,
        ∑ ξ : Fin 2 → ZMod q, ∑ η : Fin 2 → ZMod q, S_twoq q (graphR11Sub r s ξ η) =
        2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 4 := fun r s => by
      simp_rw [S_twoq_graphR11Sub_eq_norm hodd r s]
      exact sum_R11_norm hodd
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, card_units_zmod, nsmul_eq_mul,
      Finset.sum_const, Finset.card_univ, card_units_zmod, nsmul_eq_mul]
    rw [hcast]; ring
  rw [h1, h2, h3, h4]
  ring

/-- **Lemma 6.6** (`lem_6_6_vanish`):
(i) Fixed row or column gives `S(H) = 0`;
(ii) rank 3 gives trivial extra stabilizer and `q^3 ∣ S(H)`;
(iii) exact formula for `∑_{r(H)=2} S(H)` and divisibility by `q^5`. -/
theorem lem_6_6_vanish (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : q ≠ 2) :
    (∀ H : Subgroup (sylowP q), H ≠ ⊥ →
      ((∃ c : Fin (2 * q), ∀ g ∈ H, g.1.2.1 c = c) ∨
       (∃ r : Fin (2 * q), ∀ g ∈ H, g.1.1 r = r)) →
        S_twoq q H = 0) ∧
    (∀ H : Subgroup (sylowP q), elemRank q H = 3 →
      (∀ L : LatinSquare (2 * q), L ∈ fixSet (H.map (sylowP q).subtype) →
        ∀ g : sylowP q, g.1 • L = L → g ∈ H) ∧
      (q : ℤ) ^ 3 ∣ S_twoq q H) ∧
    ((∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) =
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) - 2) * ((q : ℤ) + 1) -
      8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q +
      4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2) ∧
    ((q : ℤ) ^ 5 ∣ ∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) := by
  have : Fact q.Prime := ⟨hq⟩
  have hform := sum_rank_two_formula q hq hodd
  refine ⟨lem_6_6_part1 hq hodd, lem_6_6_part2 hq hodd, hform, ?_⟩
  rw [hform]
  rcases lem_6_5_complete q hq hodd with ⟨htau, htq, _⟩
  have hfac : (q.factorial : ℤ) = (q : ℤ) * ((q - 1).factorial : ℤ) := by
    have hnat : q.factorial = q * (q - 1).factorial := (Nat.mul_factorial_pred hq.ne_zero).symm
    exact_mod_cast hnat
  let C : ℤ :=
    2 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) - 2) * ((q : ℤ) + 1) -
    8 * ((q : ℤ) - 1) ^ 5 * tQ q +
    4 * ((q : ℤ) - 1) ^ 4 * ((q - 1).factorial : ℤ) ^ 2
  have hfactor :
      2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) - 2) * ((q : ℤ) + 1) -
      8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q +
      4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2 =
      (q : ℤ) ^ 4 * C := by
    rw [htau, hfac]; dsimp [C]; ring
  rw [hfactor]
  have hC : (q : ℤ) ∣ C := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have htq' : (tQ q : ZMod q) = -1 := by
      have h := (ZMod.intCast_eq_intCast_iff (tQ q) (-1) q).mpr htq
      simpa using h
    have hwil : (((q - 1).factorial : ℕ) : ZMod q) = -1 := ZMod.wilsons_lemma q
    dsimp [C]
    push_cast
    rw [htq', hwil]
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    rw [hq0]
    ring
  rcases hC with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  rw [hm]; ring

end RankTwoClassification

end AlonTarsi.Proofs

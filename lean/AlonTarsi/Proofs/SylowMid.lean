/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Defs.Circuit
import AlonTarsi.Proofs.CircuitPoly
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Section 5: Odd Primes `q` with `n / 3 < q < n / 2`

This file proves all remaining formal blocks of Section 5 directly from Lean's standard axioms:
- `rem_5_2_aut_proved`: automorphism invariance of `cyc_T` and `j(H_{π_T}; x)` on orbits, and
  explicit induced automorphism `inducedAutSplit` of `H_{π_T}` when `g π_T = π_T`.
- `lem_5_3_three_proved`: `v_q(j(M)) ≥ 3` for `n > 2q` and `|V| ≥ 2` with all `M_{uv} ≥ 1`.
- `lem_5_4_quad_S_proved`: `v_q(j(M)) ≥ 4` on `S₀ ⊔ S₁` with a `q`-cycle automorphism on `S₁`.
- `thm_5_5_quad_P_proved`: `q^2 ∣ D_n`, `v_q(n!) = 2`, `q ∤ n`, and `M_q(n) ∣ D_n` for odd prime
  `q` and even `n` with `2q < n < 3q`.
-/

namespace AlonTarsi.Proofs

open AlonTarsi
open scoped BigOperators Matrix

/-! ### Part 1: Remark 5.2 (`rem_5_2_aut`) and Group Action on Partial Transitions -/

/-- `autActPartial` respects `1` and multiplication of `S`-preserving automorphisms. -/
lemma autActPartial_one {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (hS : ∀ v, v ∈ S ↔ (1 : MultidigraphAut H).vPerm v ∈ S) (πT : PartialTransition H S) :
    autActPartial (1 : MultidigraphAut H) hS πT = πT := by
  funext w; apply Equiv.ext; intro e; apply Subtype.ext; rfl

lemma autActPartial_mul {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g₁ g₂ : MultidigraphAut H)
    (hS₁ : ∀ v, v ∈ S ↔ g₁.vPerm v ∈ S)
    (hS₂ : ∀ v, v ∈ S ↔ g₂.vPerm v ∈ S)
    (hS₁₂ : ∀ v, v ∈ S ↔ (g₁ * g₂).vPerm v ∈ S)
    (πT : PartialTransition H S) :
    autActPartial (g₁ * g₂) hS₁₂ πT = autActPartial g₁ hS₁ (autActPartial g₂ hS₂ πT) := by
  funext w; apply Equiv.ext; intro e; apply Subtype.ext
  change g₁.aPerm (g₂.aPerm (πT ⟨g₂.vPerm.symm (g₁.vPerm.symm w.1), _⟩
    ⟨g₂.aPerm.symm (g₁.aPerm.symm e.1), _⟩).1) =
    g₁.aPerm (g₂.aPerm (πT ⟨g₂.vPerm.symm (g₁.vPerm.symm w.1), _⟩
      ⟨g₂.aPerm.symm (g₁.aPerm.symm e.1), _⟩).1)
  rfl

/-- `partialStep` commutes with an `S`-preserving automorphism `g`. -/
lemma partialStep_autActPartial {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S) (a : H.Arc) :
    partialStep H S (autActPartial g hS πT) (g.aPerm a) =
      g.aPerm (partialStep H S πT a) := by
  by_cases ha : H.head a ∉ S
  · have hga : H.head (g.aPerm a) ∉ S := by
      rw [g.map_head]; intro hmem; exact ha ((hS (H.head a)).mpr hmem)
    simp only [partialStep, hga, ha, ↓reduceDIte]
    change g.aPerm (πT ⟨g.vPerm.symm (H.head (g.aPerm a)), _⟩
      ⟨g.aPerm.symm (g.aPerm a), _⟩).1 = g.aPerm (πT ⟨H.head a, ha⟩ ⟨a, rfl⟩).1
    congr 1
    have hv : g.vPerm.symm (H.head (g.aPerm a)) = H.head a := by
      rw [g.map_head, g.vPerm.symm_apply_apply]
    have hsub : ∀ {v : V} (h : v = H.head a) (hmem : v ∉ S) (a' : H.Arc)
        (ha' : a' = a) (hhead : H.head a' = v),
        (πT ⟨v, hmem⟩ ⟨a', hhead⟩).1 = (πT ⟨H.head a, ha⟩ ⟨a, rfl⟩).1 := by
      intro v h _ a' ha' _; subst h; subst ha'; rfl
    exact hsub hv _ (g.aPerm.symm (g.aPerm a)) (g.aPerm.symm_apply_apply a) _
  · have hga : ¬ (H.head (g.aPerm a) ∉ S) := by
      rw [g.map_head, not_not]; exact (hS (H.head a)).mp (not_not.mp ha)
    simp [partialStep, ha, hga]

lemma partialStep_iterate_autActPartial {V : Type} [DecidableEq V] {H : Multidigraph V}
    {S : Finset V} (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S) (n : ℕ) (a : H.Arc) :
    (partialStep H S (autActPartial g hS πT))^[n] (g.aPerm a) =
      g.aPerm ((partialStep H S πT)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      partialStep_autActPartial]

/-- `walkEnd` commutes with an `S`-preserving automorphism `g`. -/
lemma walkEnd_autActPartial {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S)
    (e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S }) :
    let ge : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } :=
      ⟨g.aPerm e.1, by rw [g.map_tail]; exact (hS _).mp e.2.1,
        by rw [g.map_head]; intro hm; exact e.2.2 ((hS _).mpr hm)⟩
    (walkEnd H S (autActPartial g hS πT) ge).1 = g.aPerm (walkEnd H S πT e).1 := by
  classical
  dsimp only
  unfold walkEnd
  have hiff : ∀ k : ℕ,
      H.head ((partialStep H S (autActPartial g hS πT))^[k] (g.aPerm e.1)) ∈ S ↔
      H.head ((partialStep H S πT)^[k] e.1) ∈ S := by
    intro k
    rw [partialStep_iterate_autActPartial, g.map_head]
    exact (hS _).symm
  have hfind : Nat.find (exit_reaches_S H S (autActPartial g hS πT) (g.aPerm e.1)
      (by rw [g.map_tail]; exact (hS _).mp e.2.1)
      (by rw [g.map_head]; intro hm; exact e.2.2 ((hS _).mpr hm))) =
      Nat.find (exit_reaches_S H S πT e.1 e.2.1 e.2.2) := by
    simp_rw [hiff]
  dsimp only
  rw [hfind, partialStep_iterate_autActPartial]

/-- Explicit induced automorphism of `splitDigraph H S πT` when `autActPartial g hS πT = πT`. -/
noncomputable def inducedAutSplit {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S) (hfix : autActPartial g hS πT = πT) :
    MultidigraphAut (splitDigraph H S πT) where
  vPerm :=
    { toFun := fun u => ⟨g.vPerm u.1, (hS u.1).mp u.2⟩
      invFun := fun u => ⟨g.vPerm.symm u.1, by
        have := (hS (g.vPerm.symm u.1)).mpr (by rw [g.vPerm.apply_symm_apply]; exact u.2)
        exact this⟩
      left_inv := fun u => by apply Subtype.ext; simp
      right_inv := fun u => by apply Subtype.ext; simp }
  aPerm :=
    { toFun := fun b => match b with
        | Sum.inl a => Sum.inl ⟨g.aPerm a.1,
            by rw [g.map_tail]; exact (hS _).mp a.2.1,
            by rw [g.map_head]; exact (hS _).mp a.2.2⟩
        | Sum.inr e => Sum.inr ⟨g.aPerm e.1,
            by rw [g.map_tail]; exact (hS _).mp e.2.1,
            by rw [g.map_head]; intro hm; exact e.2.2 ((hS _).mpr hm)⟩
      invFun := fun b => match b with
        | Sum.inl a => Sum.inl ⟨g.aPerm.symm a.1,
            by
              have h1 := g.map_tail (g.aPerm.symm a.1)
              rw [g.aPerm.apply_symm_apply] at h1
              exact (hS _).mpr (h1 ▸ a.2.1),
            by
              have h1 := g.map_head (g.aPerm.symm a.1)
              rw [g.aPerm.apply_symm_apply] at h1
              exact (hS _).mpr (h1 ▸ a.2.2)⟩
        | Sum.inr e => Sum.inr ⟨g.aPerm.symm e.1,
            by
              have h1 := g.map_tail (g.aPerm.symm e.1)
              rw [g.aPerm.apply_symm_apply] at h1
              exact (hS _).mpr (h1 ▸ e.2.1),
            by
              have h1 := g.map_head (g.aPerm.symm e.1)
              rw [g.aPerm.apply_symm_apply] at h1
              intro hm; exact e.2.2 (h1 ▸ (hS _).mp hm)⟩
      left_inv := fun b => by rcases b with a | e <;> (dsimp only; congr 1; apply Subtype.ext; simp)
      right_inv := fun b => by rcases b with a | e <;> (dsimp only; congr 1; apply Subtype.ext; simp) }
  map_tail := fun b => by
    rcases b with a | e <;> (apply Subtype.ext; exact g.map_tail _)
  map_head := fun b => by
    rcases b with a | e
    · apply Subtype.ext; exact g.map_head a.1
    · apply Subtype.ext
      change H.head (walkEnd H S πT ⟨g.aPerm e.1,
        by rw [g.map_tail]; exact (hS _).mp e.2.1,
        by rw [g.map_head]; intro hm; exact e.2.2 ((hS _).mpr hm)⟩).1 =
        g.vPerm (H.head (walkEnd H S πT e).1)
      have h1 := walkEnd_autActPartial g hS πT e
      dsimp only at h1
      rw [hfix] at h1
      rw [h1, g.map_head]

/-- Power of `inducedAutSplit` matches `g ^ k` on vertices and arcs. -/
lemma inducedAutSplit_pow_vPerm {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S) (hfix : autActPartial g hS πT = πT) (k : ℕ)
    (u : { v : V // v ∈ S }) :
    (((inducedAutSplit g hS πT hfix) ^ k).vPerm u).1 = ((g ^ k).vPerm u.1) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    change (((inducedAutSplit g hS πT hfix) ^ k).vPerm ((inducedAutSplit g hS πT hfix).vPerm u)).1 =
      ((g ^ k).vPerm (g.vPerm u.1))
    rw [ih]
    rfl

lemma inducedAutSplit_pow_eq_one {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S) (hfix : autActPartial g hS πT = πT) {k : ℕ}
    (hk : g ^ k = 1) :
    (inducedAutSplit g hS πT hfix) ^ k = 1 := by
  have ha_pow : ∀ (m : ℕ) (b : (splitDigraph H S πT).Arc),
      match b with
      | Sum.inl a => ∃ h1 h2, ((inducedAutSplit g hS πT hfix) ^ m).aPerm (Sum.inl a) =
          Sum.inl ⟨(g ^ m).aPerm a.1, h1, h2⟩
      | Sum.inr e => ∃ h1 h2, ((inducedAutSplit g hS πT hfix) ^ m).aPerm (Sum.inr e) =
          Sum.inr ⟨(g ^ m).aPerm e.1, h1, h2⟩ := by
    intro m
    induction m with
    | zero =>
      intro b; rcases b with a | e
      · exact ⟨a.2.1, a.2.2, rfl⟩
      · exact ⟨e.2.1, e.2.2, rfl⟩
    | succ m ih =>
      intro b; rcases b with a | e
      · rcases ih (Sum.inl a) with ⟨h1, h2, hm⟩
        have h1' : H.tail ((g ^ (m + 1)).aPerm a.1) ∈ S := by
          rw [pow_succ']; change H.tail (g.aPerm ((g ^ m).aPerm a.1)) ∈ S
          rw [g.map_tail]; exact (hS _).mp h1
        have h2' : H.head ((g ^ (m + 1)).aPerm a.1) ∈ S := by
          rw [pow_succ']; change H.head (g.aPerm ((g ^ m).aPerm a.1)) ∈ S
          rw [g.map_head]; exact (hS _).mp h2
        refine ⟨h1', h2', ?_⟩
        rw [pow_succ']
        change (inducedAutSplit g hS πT hfix).aPerm (((inducedAutSplit g hS πT hfix) ^ m).aPerm (Sum.inl a)) = _
        rw [hm]; dsimp only [inducedAutSplit, Equiv.coe_fn_mk]; congr 1; apply Subtype.ext
        change g.aPerm ((g ^ m).aPerm a.1) = (g ^ (m + 1)).aPerm a.1; rw [pow_succ']; rfl
      · rcases ih (Sum.inr e) with ⟨h1, h2, hm⟩
        have h1' : H.tail ((g ^ (m + 1)).aPerm e.1) ∈ S := by
          rw [pow_succ']; change H.tail (g.aPerm ((g ^ m).aPerm e.1)) ∈ S
          rw [g.map_tail]; exact (hS _).mp h1
        have h2' : H.head ((g ^ (m + 1)).aPerm e.1) ∉ S := by
          rw [pow_succ']; change H.head (g.aPerm ((g ^ m).aPerm e.1)) ∉ S
          rw [g.map_head]; intro hmem; exact h2 ((hS _).mpr hmem)
        refine ⟨h1', h2', ?_⟩
        rw [pow_succ']
        change (inducedAutSplit g hS πT hfix).aPerm (((inducedAutSplit g hS πT hfix) ^ m).aPerm (Sum.inr e)) = _
        rw [hm]; dsimp only [inducedAutSplit, Equiv.coe_fn_mk]; congr 1; apply Subtype.ext
        change g.aPerm ((g ^ m).aPerm e.1) = (g ^ (m + 1)).aPerm e.1; rw [pow_succ']; rfl
  apply MultidigraphAut.ext
  · apply Equiv.ext; intro u; apply Subtype.ext
    rw [inducedAutSplit_pow_vPerm, hk]; rfl
  · apply Equiv.ext; intro b
    rcases b with a | e
    · rcases ha_pow k (Sum.inl a) with ⟨h1, h2, hm⟩
      rw [hm]; congr 1; apply Subtype.ext
      change (g ^ k).aPerm a.1 = a.1; rw [hk]; rfl
    · rcases ha_pow k (Sum.inr e) with ⟨h1, h2, hm⟩
      rw [hm]; congr 1; apply Subtype.ext
      change (g ^ k).aPerm e.1 = e.1; rw [hk]; rfl

/-- **Remark 5.2**: Automorphism invariance of `cyc_T` and `j(H_{π_T}; x)` on orbits, and
induced automorphism of `H_{π_T}` when `g π_T = π_T`. -/
theorem rem_5_2_aut_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (S : Finset V) (g : MultidigraphAut H)
    (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S) (πT : PartialTransition H S) :
    cycInsideT H S (autActPartial g hS πT) = cycInsideT H S πT ∧
    circuitPoly (splitDigraph H S (autActPartial g hS πT)) = circuitPoly (splitDigraph H S πT) ∧
    (autActPartial g hS πT = πT →
      ∃ gS : MultidigraphAut (splitDigraph H S πT),
        ∀ u : { v : V // v ∈ S }, (gS.vPerm u).1 = g.vPerm u.1) := by
  classical
  -- Part 1: cycInsideT invariance via closedTArcs equivalence
  have hclosed_iff : ∀ a : H.Arc,
      (∀ n : ℕ, H.head ((partialStep H S (autActPartial g hS πT))^[n] (g.aPerm a)) ∉ S) ↔
      (∀ n : ℕ, H.head ((partialStep H S πT)^[n] a) ∉ S) := by
    intro a
    refine forall_congr' fun n => ?_
    rw [partialStep_iterate_autActPartial, g.map_head]
    exact not_congr (hS _).symm
  let eC : closedTArcs H S πT ≃ closedTArcs H S (autActPartial g hS πT) :=
    { toFun := fun a => ⟨g.aPerm a.1, (hclosed_iff a.1).mpr a.2⟩
      invFun := fun b => ⟨g.aPerm.symm b.1, (hclosed_iff (g.aPerm.symm b.1)).mp (by simpa using b.2)⟩
      left_inv := fun a => by apply Subtype.ext; simp
      right_inv := fun b => by apply Subtype.ext; simp }
  have hcyc : cycInsideT H S (autActPartial g hS πT) = cycInsideT H S πT := by
    unfold cycInsideT
    rw [← permCycleCount_equivCongr eC (closedTPerm H S πT)]
    congr 1
    apply Equiv.ext; intro b; apply Subtype.ext
    change partialStep H S (autActPartial g hS πT) b.1 = g.aPerm (partialStep H S πT (g.aPerm.symm b.1))
    rw [← partialStep_autActPartial g hS πT (g.aPerm.symm b.1), g.aPerm.apply_symm_apply]
  -- Part 2: circuitPoly invariance via multidigraph isomorphism
  let eV : { v : V // v ∈ S } ≃ { v : V // v ∈ S } :=
    { toFun := fun u => ⟨g.vPerm u.1, (hS u.1).mp u.2⟩
      invFun := fun u => ⟨g.vPerm.symm u.1,
        (hS (g.vPerm.symm u.1)).mpr (by rw [g.vPerm.apply_symm_apply]; exact u.2)⟩
      left_inv := fun u => by apply Subtype.ext; simp
      right_inv := fun u => by apply Subtype.ext; simp }
  let eA : (splitDigraph H S πT).Arc ≃ (splitDigraph H S (autActPartial g hS πT)).Arc :=
    { toFun := fun b => match b with
        | Sum.inl a => Sum.inl ⟨g.aPerm a.1,
            by rw [g.map_tail]; exact (hS _).mp a.2.1,
            by rw [g.map_head]; exact (hS _).mp a.2.2⟩
        | Sum.inr e => Sum.inr ⟨g.aPerm e.1,
            by rw [g.map_tail]; exact (hS _).mp e.2.1,
            by rw [g.map_head]; intro hm; exact e.2.2 ((hS _).mpr hm)⟩
      invFun := fun b => match b with
        | Sum.inl a => Sum.inl ⟨g.aPerm.symm a.1,
            by
              have h1 := g.map_tail (g.aPerm.symm a.1)
              rw [g.aPerm.apply_symm_apply] at h1
              exact (hS _).mpr (h1 ▸ a.2.1),
            by
              have h1 := g.map_head (g.aPerm.symm a.1)
              rw [g.aPerm.apply_symm_apply] at h1
              exact (hS _).mpr (h1 ▸ a.2.2)⟩
        | Sum.inr e => Sum.inr ⟨g.aPerm.symm e.1,
            by
              have h1 := g.map_tail (g.aPerm.symm e.1)
              rw [g.aPerm.apply_symm_apply] at h1
              exact (hS _).mpr (h1 ▸ e.2.1),
            by
              have h1 := g.map_head (g.aPerm.symm e.1)
              rw [g.aPerm.apply_symm_apply] at h1
              intro hm; exact e.2.2 (h1 ▸ (hS _).mp hm)⟩
      left_inv := fun b => by rcases b with a | e <;> (dsimp only; congr 1; apply Subtype.ext; simp)
      right_inv := fun b => by rcases b with a | e <;> (dsimp only; congr 1; apply Subtype.ext; simp) }
  have hpoly : circuitPoly (splitDigraph H S (autActPartial g hS πT)) =
      circuitPoly (splitDigraph H S πT) :=
    (circuitPoly_eq_of_equiv (splitDigraph H S πT) (splitDigraph H S (autActPartial g hS πT))
      eV eA
      (fun b => by rcases b with a | e <;> (apply Subtype.ext; exact g.map_tail _))
      (fun b => by
        rcases b with a | e
        · apply Subtype.ext; exact g.map_head a.1
        · apply Subtype.ext
          change H.head (walkEnd H S (autActPartial g hS πT) ⟨g.aPerm e.1,
            by rw [g.map_tail]; exact (hS _).mp e.2.1,
            by rw [g.map_head]; intro hm; exact e.2.2 ((hS _).mpr hm)⟩).1 =
            g.vPerm (H.head (walkEnd H S πT e).1)
          have h1 := walkEnd_autActPartial g hS πT e
          dsimp only at h1
          rw [h1, g.map_head])).symm
  -- Part 3: induced automorphism when g fixes πT
  refine ⟨hcyc, hpoly, fun hfix => ⟨inducedAutSplit g hS πT hfix, fun _ => rfl⟩⟩

/-! ### Part 2: Lemma 5.3 (`lem_5_3_three`) and Lemma 5.4 (`lem_5_4_quad_S`) -/

/-- **Lemma 5.3**: For prime `q` and `n > 2q`, if `H` is `n`-regular on at least 2 vertices
with all `M_{uv} ≥ 1`, then `v_q(j(M)) ≥ 3`. -/
theorem lem_5_3_three_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (q n : ℕ) (hq : q.Prime) (hn : 2 * q < n)
    (hreg : IsRegular H n) (hV : 2 ≤ Fintype.card V)
    (hpos : ∀ u v : V, 1 ≤ adjMatrix H u v) :
    (3 : ℕ∞) ≤ qVal q (circuitEval (adjMatrix H) n) := by
  have hind := prop_3_5_quad_ind_proved H n q hreg (by omega) hpos hq
  have hf1 : 2 ≤ fVal q n 1 := by
    rw [fVal_one (by have := hq.pos; omega)]
    have hdiv := div_le_padicValNat_factorial hq n
    have h2 : 2 ≤ n / q := (Nat.le_div_iff_mul_le hq.pos).mpr (by omega)
    omega
  have hf2 : 1 ≤ fVal q n 2 := by
    have hlin := linear_lower_bound_fVal (n := n) hq (by norm_num : 1 ≤ 2) (by have := hq.two_le; omega)
    have hstrict : 0 < q * fVal q n 2 := by have := hq.two_le; omega
    exact Nat.pos_of_mul_pos_left hstrict
  have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 (Fintype.card V) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]; omega
  have hsum3 : 3 ≤ ∑ N' ∈ Finset.Icc 1 (Fintype.card V), fVal q n N' := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fVal q n) (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h1
    omega
  have hcast : ((3 : ℕ) : ℕ∞) ≤ ∑ N' ∈ Finset.Icc 1 (Fintype.card V), (fVal q n N' : ℕ∞) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr hsum3
  exact le_trans hcast hind

/-- Helper: `qVal q` of a finite sum is at least any lower bound `b` that bounds every term. -/
lemma le_qVal_sum {ι : Type*} {q : ℕ} (hq : q.Prime) (s : Finset ι) (f : ι → ℤ) (b : ℕ∞)
    (hf : ∀ i ∈ s, b ≤ qVal q (f i)) :
    b ≤ qVal q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qVal_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))) (min_le_qVal_add hq _ _)

open scoped Classical in
/-- Helper: group a sum over `X` into `G`-orbits when `f` is `G`-invariant. -/
lemma sum_eq_sum_orbits {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    [Fintype (Quotient (MulAction.orbitRel G X))]
    (f : X → ℤ) (hinv : ∀ g : G, ∀ x : X, f (g • x) = f x) :
    ∑ x : X, f x =
      ∑ ω : Quotient (MulAction.orbitRel G X),
        ((Finset.univ.filter fun x : X => Quotient.mk (MulAction.orbitRel G X) x = ω).card : ℤ) *
          f (Quotient.out ω) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk (MulAction.orbitRel G X))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hconst : ∑ x ∈ Finset.univ.filter (fun x : X => Quotient.mk (MulAction.orbitRel G X) x = ω),
      f x =
      ∑ _x ∈ Finset.univ.filter (fun x : X => Quotient.mk (MulAction.orbitRel G X) x = ω),
        f (Quotient.out ω) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hrel : (MulAction.orbitRel G X) x (Quotient.out ω) := by
      apply Quotient.exact
      rw [(Finset.mem_filter.mp hx).2, Quotient.out_eq]
    rcases MulAction.mem_orbit_iff.mp hrel with ⟨g, rfl⟩
    exact hinv g (Quotient.out ω)
  rw [hconst, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
/-- The cardinality of the orbit of `x` in `sum_eq_sum_orbits` equals `Fintype.card (MulAction.orbit G x)`. -/
lemma card_orbit_fiber_eq {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X]
    (ω : Quotient (MulAction.orbitRel G X)) [Fintype (MulAction.orbit G (Quotient.out ω))] :
    (Finset.univ.filter fun x : X => Quotient.mk (MulAction.orbitRel G X) x = ω).card =
      Fintype.card (MulAction.orbit G (Quotient.out ω)) := by
  classical
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun x => ⟨x.1, by
        have hrel : (MulAction.orbitRel G X) x.1 (Quotient.out ω) :=
          Quotient.exact (x.2.trans (Quotient.out_eq ω).symm)
        exact hrel⟩
      invFun := fun y => ⟨y.1, by
        have h1 : Quotient.mk (MulAction.orbitRel G X) y.1 =
            Quotient.mk (MulAction.orbitRel G X) (Quotient.out ω) := Quotient.sound y.2
        rw [h1, Quotient.out_eq]⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun y => by apply Subtype.ext; rfl }

/-- Helper: `S`-preserving subgroup of `MultidigraphAut H` acts on `PartialTransition H S`. -/
def StabAut {V : Type} (H : Multidigraph V) (S : Finset V) : Subgroup (MultidigraphAut H) where
  carrier := { g | ∀ v, v ∈ S ↔ g.vPerm v ∈ S }
  mul_mem' := fun {a b} ha hb v => (hb v).trans (ha (b.vPerm v))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {a} ha v => by
    have h1 := ha (a.vPerm.symm v)
    change v ∈ S ↔ a.vPerm.symm v ∈ S
    rw [a.vPerm.apply_symm_apply] at h1
    exact h1.symm

instance {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V) :
    MulAction (StabAut H S) (PartialTransition H S) where
  smul g πT := autActPartial g.1 g.2 πT
  one_smul πT := autActPartial_one (fun _ => Iff.rfl) πT
  mul_smul g₁ g₂ πT := autActPartial_mul g₁.1 g₂.1 g₁.2 g₂.2 (g₁ * g₂).2 πT

set_option maxHeartbeats 800000 in
/-- **Lemma 5.4**: For odd prime `q` and `n > 2q`, if `H` is `n`-regular on `S₀ ⊔ S₁` with
`|S₀| = |S₁| = q`, all `M_{uv} ≥ 1`, `M_{ab} = 1` for `a ∈ S₀, b ∈ S₁`, and `g` is an
automorphism of order `q` fixing `S₀` pointwise and acting transitively on `S₁`, then
`v_q(j(M)) ≥ 4`. -/
theorem lem_5_4_quad_S_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (q n : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (hn : 2 * q < n)
    (hreg : IsRegular H n) (S₀ S₁ : Finset V)
    (hdisj : Disjoint S₀ S₁) (hcov : S₀ ∪ S₁ = Finset.univ)
    (hcard0 : S₀.card = q) (hcard1 : S₁.card = q)
    (hpos : ∀ u v : V, 1 ≤ adjMatrix H u v)
    (h1 : ∀ a ∈ S₀, ∀ b ∈ S₁, adjMatrix H a b = 1)
    (g : MultidigraphAut H) (hord : orderOf g = q)
    (hfix : ∀ a ∈ S₀, g.vPerm a = a)
    (htrans : ∀ b₁ ∈ S₁, ∀ b₂ ∈ S₁, ∃ k : ℕ, (g.vPerm ^ k) b₁ = b₂) :
    (4 : ℕ∞) ≤ qVal q (circuitEval (adjMatrix H) n) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp (by omega)
  have hS₁_ne : S₁.Nonempty := Finset.card_pos.mp (by omega)
  have hmem_S₁ : ∀ v : V, v ∉ S₀ ↔ v ∈ S₁ := by
    intro v
    constructor
    · intro hv
      have : v ∈ S₀ ∪ S₁ := hcov ▸ Finset.mem_univ v
      rcases Finset.mem_union.mp this with h0 | h1'
      · exact absurd h0 hv
      · exact h1'
    · intro hv h0
      exact Finset.disjoint_left.mp hdisj h0 hv
  have hS_pres : ∀ v : V, v ∈ S₀ ↔ g.vPerm v ∈ S₀ := by
    intro v
    constructor
    · intro hv; rw [hfix v hv]; exact hv
    · intro hgv
      by_contra hv
      have hv1 : v ∈ S₁ := (hmem_S₁ v).mp hv
      -- g.vPerm fixes S₀ pointwise, so g.vPerm (g.vPerm v) = g.vPerm v ⇒ v = g.vPerm v ∈ S₀, contradiction!
      have h2 := hfix (g.vPerm v) hgv
      have hv_eq := g.vPerm.injective h2
      exact hv (hv_eq ▸ hgv)
  -- Apply Lemma 5.1 with S = S₀ and evaluate at x = -n
  have hsplit := lem_5_1_quad_split_proved H n hreg S₀ hS₀_ne
  have heval := congrArg (Polynomial.eval (-(n : ℤ))) hsplit.1
  rw [circuitPoly_eval_eq_circuitEval H n, Polynomial.eval_finset_sum] at heval
  rw [heval]
  -- Subgroup G = zpowers ⟨g, hS_pres⟩ ≤ StabAut H S₀ of order q acting on PartialTransition H S₀
  let gStab : StabAut H S₀ := ⟨g, hS_pres⟩
  let G := Subgroup.zpowers gStab
  haveI : Finite (MultidigraphAut H) :=
    Finite.of_injective (fun x : MultidigraphAut H => (x.vPerm, x.aPerm))
      (fun _ _ h => MultidigraphAut.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2)
  let _ : Fintype G := Fintype.ofFinite _
  have hord_gStab : orderOf gStab = q := by
    have h1' : orderOf (gStab : MultidigraphAut H) = orderOf gStab := Subgroup.orderOf_coe gStab
    rw [← h1', hord]
  have hcardG : Fintype.card G = q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hord_gStab]
  -- Term function is G-invariant by Remark 5.2
  let term (πT : PartialTransition H S₀) : ℤ :=
    (Polynomial.X ^ cycInsideT H S₀ πT * circuitPoly (splitDigraph H S₀ πT)).eval (-(n : ℤ))
  have hinv : ∀ h : G, ∀ πT : PartialTransition H S₀, term (h • πT) = term πT := by
    intro h πT
    have hrem := rem_5_2_aut_proved H S₀ h.1.1 h.1.2 πT
    change (Polynomial.X ^ cycInsideT H S₀ (autActPartial h.1.1 h.1.2 πT) *
      circuitPoly (splitDigraph H S₀ (autActPartial h.1.1 h.1.2 πT))).eval (-(n : ℤ)) =
      (Polynomial.X ^ cycInsideT H S₀ πT * circuitPoly (splitDigraph H S₀ πT)).eval (-(n : ℤ))
    rw [hrem.1, hrem.2.1]
  let _ : Fintype (Quotient (MulAction.orbitRel G (PartialTransition H S₀))) := Fintype.ofFinite _
  rw [sum_eq_sum_orbits term hinv]
  refine le_qVal_sum hq Finset.univ _ (4 : ℕ∞) fun ω _ => ?_
  set πT := Quotient.out ω
  let _ : Fintype (MulAction.orbit G πT) := Fintype.ofFinite _
  have horb_dvd : (Finset.univ.filter fun x : PartialTransition H S₀ =>
      Quotient.mk (MulAction.orbitRel G (PartialTransition H S₀)) x = ω).card ∣ q := by
    rw [card_orbit_fiber_eq ω, ← hcardG]
    exact ⟨Fintype.card (MulAction.stabilizer G πT),
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group G πT).symm⟩
  have hsplit_πT := hsplit.2 πT
  have hreg_S₀ : IsRegular (splitDigraph H S₀ πT) n := hsplit_πT.1
  have hpos_S₀ : ∀ u v : { v : V // v ∈ S₀ }, 1 ≤ adjMatrix (splitDigraph H S₀ πT) u v := by
    rcases hsplit_πT.2 with ⟨R, hMR, _, _⟩
    intro u v
    rw [hMR]
    have := hpos u.1 v.1
    change 1 ≤ adjMatrix H u.1 v.1 + R u v
    omega
  have hcard_S₀ : Fintype.card { v : V // v ∈ S₀ } = q := by
    rw [Fintype.card_coe, hcard0]
  have hterm_val : qVal q (term πT) ≥ qVal q (circuitEval (adjMatrix (splitDigraph H S₀ πT)) n) := by
    dsimp only [term]
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      circuitPoly_eval_eq_circuitEval, qVal_mul hq]
    exact le_add_self
  rcases hq.eq_one_or_self_of_dvd _ horb_dvd with hcard1' | hcardq
  · -- Fixed point: orbit size 1, so g fixes πT!
    rw [hcard1', Nat.cast_one, one_mul]
    have hfix_πT : autActPartial g hS_pres πT = πT := by
      have horb1 : Fintype.card (MulAction.orbit G πT) = 1 := by
        rw [← card_orbit_fiber_eq ω]; exact hcard1'
      have hmem1 : (⟨gStab, Subgroup.mem_zpowers gStab⟩ : G) • πT ∈ MulAction.orbit G πT :=
        ⟨⟨gStab, Subgroup.mem_zpowers gStab⟩, rfl⟩
      have hmem2 : πT ∈ MulAction.orbit G πT := ⟨1, one_smul G πT⟩
      have heq := (Fintype.card_eq_one_iff.mp horb1)
      rcases heq with ⟨z, hz⟩
      have h1' : (⟨_, hmem1⟩ : MulAction.orbit G πT) = z := hz _
      have h2' : (⟨_, hmem2⟩ : MulAction.orbit G πT) = z := hz _
      exact congrArg Subtype.val (h1'.trans h2'.symm)
    -- Pick a ∈ S₀ and b₀ ∈ S₁; all q exit arcs a → b (b ∈ S₁) end at the SAME vertex w ∈ S₀!
    obtain ⟨a, ha⟩ := hS₀_ne
    obtain ⟨b₀, hb₀⟩ := hS₁_ne
    have hex_arc : ∀ b ∈ S₁, ∃! e : H.Arc, H.tail e = a ∧ H.head e = b := by
      intro b hb
      rcases Finset.card_eq_one.mp (h1 a ha b hb) with ⟨e, he⟩
      refine ⟨e, ?_, fun e' he' => ?_⟩
      · have : e ∈ Finset.univ.filter (fun x : H.Arc => H.tail x = a ∧ H.head x = b) := by
          rw [he]; simp
        exact (Finset.mem_filter.mp this).2
      · have : e' ∈ ({e} : Finset H.Arc) := by
          rw [← he]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩
        exact Finset.mem_singleton.mp this
    let e₀ : { x : H.Arc // H.tail x ∈ S₀ ∧ H.head x ∉ S₀ } :=
      ⟨(hex_arc b₀ hb₀).choose,
        (hex_arc b₀ hb₀).choose_spec.1.1.symm ▸ ha,
        (hmem_S₁ _).mpr ((hex_arc b₀ hb₀).choose_spec.1.2.symm ▸ hb₀)⟩
    let w : { v : V // v ∈ S₀ } := ⟨H.head (walkEnd H S₀ πT e₀).1, (walkEnd H S₀ πT e₀).2⟩
    -- For every k : ℕ, g^k fixes πT and maps e₀ to the unique arc a → (g.vPerm^k) b₀,
    -- whose walkEnd has head = (g.vPerm^k) w.1 = w.1!
    have hpow_S : ∀ (k : ℕ) (v : V), v ∈ S₀ ↔ (g ^ k).vPerm v ∈ S₀ := by
      intro k v
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ']
        change v ∈ S₀ ↔ g.vPerm ((g ^ k).vPerm v) ∈ S₀
        exact ih.trans (hS_pres _)
    have hfix_pow : ∀ k : ℕ, autActPartial (g ^ k) (hpow_S k) πT = πT := by
      intro k
      induction k with
      | zero => exact autActPartial_one _ πT
      | succ k ih =>
        have h1' := autActPartial_mul g (g ^ k) hS_pres (hpow_S k) (by
          intro v; change v ∈ S₀ ↔ g.vPerm ((g ^ k).vPerm v) ∈ S₀
          exact (hpow_S k v).trans (hS_pres _)) πT
        have heq : autActPartial (g ^ (k + 1)) (hpow_S (k + 1)) πT =
            autActPartial (g * g ^ k) (by
              intro v; change v ∈ S₀ ↔ g.vPerm ((g ^ k).vPerm v) ∈ S₀
              exact (hpow_S k v).trans (hS_pres _)) πT := by
          congr 1; exact pow_succ' g k
        rw [heq, h1', ih, hfix_πT]
    have hpow_fix_S₀ : ∀ (k : ℕ) (v : V), v ∈ S₀ → ((g ^ k).vPerm v) = v := by
      intro k v hv
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ']
        change g.vPerm ((g ^ k).vPerm v) = v
        rw [ih, hfix v hv]
    have hpow_vPerm : ∀ k : ℕ, (g ^ k).vPerm = g.vPerm ^ k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', pow_succ']
        change g.vPerm * (g ^ k).vPerm = g.vPerm * g.vPerm ^ k
        rw [ih]
    have hall_end_w : ∀ (b : V) (hb : b ∈ S₁),
        H.head (walkEnd H S₀ πT ⟨(hex_arc b hb).choose,
          (hex_arc b hb).choose_spec.1.1.symm ▸ ha,
          (hmem_S₁ _).mpr ((hex_arc b hb).choose_spec.1.2.symm ▸ hb)⟩).1 = w.1 := by
      intro b hb
      obtain ⟨k, hk⟩ := htrans b₀ hb₀ b hb
      have hgk_S : ∀ v, v ∈ S₀ ↔ (g ^ k).vPerm v ∈ S₀ := fun v => by
        clear hk
        rw [hpow_vPerm]; induction k with
        | zero => rfl
        | succ k ih => rw [pow_succ']; exact ih.trans (hS_pres _)
      have hgk_e₀ : (g ^ k).aPerm e₀.1 = (hex_arc b hb).choose := by
        apply (hex_arc b hb).choose_spec.2
        constructor
        · rw [(g ^ k).map_tail, (hex_arc b₀ hb₀).choose_spec.1.1, hpow_fix_S₀ k a ha]
        · rw [(g ^ k).map_head, (hex_arc b₀ hb₀).choose_spec.1.2, hpow_vPerm, hk]
      have hwalk := walkEnd_autActPartial (g ^ k) hgk_S πT e₀
      dsimp only at hwalk
      have hfixk : autActPartial (g ^ k) hgk_S πT = πT := hfix_pow k
      rw [hfixk] at hwalk
      have he_eq : (⟨(g ^ k).aPerm e₀.1,
          by rw [(g ^ k).map_tail]; exact (hgk_S _).mp e₀.2.1,
          by rw [(g ^ k).map_head]; intro hm; exact e₀.2.2 ((hgk_S _).mpr hm)⟩ :
          { x : H.Arc // H.tail x ∈ S₀ ∧ H.head x ∉ S₀ }) =
          ⟨(hex_arc b hb).choose,
            (hex_arc b hb).choose_spec.1.1.symm ▸ ha,
            (hmem_S₁ _).mpr ((hex_arc b hb).choose_spec.1.2.symm ▸ hb)⟩ :=
        Subtype.ext hgk_e₀
      rw [← he_eq, hwalk, (g ^ k).map_head, hpow_fix_S₀ k w.1 w.2]
    -- Hence adjMatrix (splitDigraph H S₀ πT) ⟨a, ha⟩ w ≥ q + 1 (at least 1 internal arc + q virtual arcs)!
    have hM_aw_ge : q ≤ adjMatrix (splitDigraph H S₀ πT) ⟨a, ha⟩ w := by
      let f : { b : V // b ∈ S₁ } → (splitDigraph H S₀ πT).Arc := fun b =>
        Sum.inr ⟨(hex_arc b.1 b.2).choose,
          (hex_arc b.1 b.2).choose_spec.1.1.symm ▸ ha,
          (hmem_S₁ _).mpr ((hex_arc b.1 b.2).choose_spec.1.2.symm ▸ b.2)⟩
      have hinj : Function.Injective f := by
        intro b₁ b₂ heq
        have hval : (hex_arc b₁.1 b₁.2).choose = (hex_arc b₂.1 b₂.2).choose :=
          congrArg Subtype.val (Sum.inr.inj heq)
        apply Subtype.ext
        have h1' := (hex_arc b₁.1 b₁.2).choose_spec.1.2
        have h2' := (hex_arc b₂.1 b₂.2).choose_spec.1.2
        rw [hval] at h1'
        exact h1'.symm.trans h2'
      unfold adjMatrix; dsimp only [Matrix.of_apply]
      calc q = (Finset.univ : Finset { b : V // b ∈ S₁ }).card := by
              rw [Finset.card_univ, Fintype.card_coe, hcard1]
        _ = ((Finset.univ : Finset { b : V // b ∈ S₁ }).image f).card :=
              (Finset.card_image_of_injective _ hinj).symm
        _ ≤ _ := Finset.card_le_card (by
              intro e he
              rcases Finset.mem_image.mp he with ⟨b, _, rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨Subtype.ext (hex_arc b.1 b.2).choose_spec.1.1,
                Subtype.ext (hall_end_w b.1 b.2)⟩)
    -- Apply Corollary 3.4 at w to splitDigraph H S₀ πT!
    have hcor := cor_3_4_quad_elim_proved (splitDigraph H S₀ πT) n q hreg_S₀ (by omega) w hq
    dsimp only at hcor
    have hcol_ge1 : 1 ≤ padicValNat q (∏ u : { v : V // v ∈ S₀ },
        (adjMatrix (splitDigraph H S₀ πT) u w).factorial) := by
      have hdvd1 : q ∣ (adjMatrix (splitDigraph H S₀ πT) ⟨a, ha⟩ w).factorial :=
        Nat.dvd_factorial hq.pos hM_aw_ge
      have hdvd2 : (adjMatrix (splitDigraph H S₀ πT) ⟨a, ha⟩ w).factorial ∣
          ∏ u : { v : V // v ∈ S₀ }, (adjMatrix (splitDigraph H S₀ πT) u w).factorial :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨a, ha⟩ : { v : V // v ∈ S₀ }))
      exact one_le_padicValNat_of_dvd
        (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _) (dvd_trans hdvd1 hdvd2)
    have hR_ge3 : ∀ R : { R : Matrix { v : { v : V // v ∈ S₀ } // v ≠ w }
        { v : { v : V // v ∈ S₀ } // v ≠ w } ℕ // ValidProfile (adjMatrix (splitDigraph H S₀ πT)) w R },
        (3 : ℕ∞) ≤ qVal q (circuitEval (subMatrix (adjMatrix (splitDigraph H S₀ πT)) w + R.1) n) := by
      intro R
      let M' := subMatrix (adjMatrix (splitDigraph H S₀ πT)) w + R.1
      let G' := ofMatrix M'
      have hM'_eq : adjMatrix G' = M' := adjMatrix_ofMatrix M'
      have hcard' : Fintype.card { v : { v : V // v ∈ S₀ } // v ≠ w } = q - 1 := by
        have h1' := Fintype.card_subtype_compl (fun v : { v : V // v ∈ S₀ } => v = w)
        have h2' : Fintype.card { v : { v : V // v ∈ S₀ } // v = w } = 1 := Fintype.card_unique
        rw [h2', hcard_S₀] at h1'
        exact h1'
      have hreg' : IsRegular G' n := by
        rw [isRegular_iff_adjMatrix, hM'_eq]
        have hregM := (isRegular_iff_adjMatrix (splitDigraph H S₀ πT) n).mp hreg_S₀
        constructor
        · intro v
          simp only [M', Matrix.add_apply, subMatrix, Matrix.of_apply, Finset.sum_add_distrib]
          rw [R.2.2 v]
          have hcol := hregM.1 v.1
          rw [← Finset.add_sum_erase Finset.univ (fun u => adjMatrix (splitDigraph H S₀ πT) u v.1)
            (Finset.mem_univ w)] at hcol
          have hsub_sum : ∑ u : { u : { v : V // v ∈ S₀ } // u ≠ w },
              adjMatrix (splitDigraph H S₀ πT) u.1 v.1 =
              ∑ u ∈ Finset.univ.erase w, adjMatrix (splitDigraph H S₀ πT) u v.1 := by
            refine Finset.sum_bij (fun u _ => u.1) ?_ ?_ ?_ ?_
            · intro u _; exact Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩
            · intro u₁ _ u₂ _ h; exact Subtype.ext h
            · intro u hu; exact ⟨⟨u, (Finset.mem_erase.mp hu).1⟩, Finset.mem_univ _, rfl⟩
            · intro _ _; rfl
          rw [hsub_sum]; omega
        · intro u
          simp only [M', Matrix.add_apply, subMatrix, Matrix.of_apply, Finset.sum_add_distrib]
          rw [R.2.1 u]
          have hrow := hregM.2 u.1
          rw [← Finset.add_sum_erase Finset.univ (fun v => adjMatrix (splitDigraph H S₀ πT) u.1 v)
            (Finset.mem_univ w)] at hrow
          have hsub_sum : ∑ v : { v : { v : V // v ∈ S₀ } // v ≠ w },
              adjMatrix (splitDigraph H S₀ πT) u.1 v.1 =
              ∑ v ∈ Finset.univ.erase w, adjMatrix (splitDigraph H S₀ πT) u.1 v := by
            refine Finset.sum_bij (fun v _ => v.1) ?_ ?_ ?_ ?_
            · intro v _; exact Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩
            · intro v₁ _ v₂ _ h; exact Subtype.ext h
            · intro v hv; exact ⟨⟨v, (Finset.mem_erase.mp hv).1⟩, Finset.mem_univ _, rfl⟩
            · intro _ _; rfl
          rw [hsub_sum]; omega
      have hpos' : ∀ u v, 1 ≤ adjMatrix G' u v := by
        intro u v; rw [hM'_eq]
        have := hpos_S₀ u.1 v.1
        change 1 ≤ adjMatrix (splitDigraph H S₀ πT) u.1 v.1 + R.1 u v
        omega
      have h3 := lem_5_3_three_proved G' q n hq hn hreg' (by omega) hpos'
      rwa [hM'_eq] at h3
    have hiInf : (3 : ℕ∞) ≤
        ⨅ R : { R : Matrix { v : { v : V // v ∈ S₀ } // v ≠ w }
            { v : { v : V // v ∈ S₀ } // v ≠ w } ℕ // ValidProfile (adjMatrix (splitDigraph H S₀ πT)) w R },
          qVal q (circuitEval (subMatrix (adjMatrix (splitDigraph H S₀ πT)) w + R.1) n) :=
      le_iInf hR_ge3
    calc (4 : ℕ∞) = (1 : ℕ∞) + (3 : ℕ∞) := by norm_num
      _ ≤ (padicValNat q (∏ u : { v : V // v ∈ S₀ },
            (adjMatrix (splitDigraph H S₀ πT) u w).factorial) : ℕ∞) +
            ⨅ R : { R : Matrix { v : { v : V // v ∈ S₀ } // v ≠ w }
                { v : { v : V // v ∈ S₀ } // v ≠ w } ℕ // ValidProfile (adjMatrix (splitDigraph H S₀ πT)) w R },
              qVal q (circuitEval (subMatrix (adjMatrix (splitDigraph H S₀ πT)) w + R.1) n) :=
          add_le_add (by exact_mod_cast hcol_ge1) hiInf
      _ ≤ qVal q (circuitEval (adjMatrix (splitDigraph H S₀ πT)) n) := hcor
      _ ≤ qVal q (term πT) := hterm_val
  · -- Orbit of size q: factor q times lem_5_3_three (v_q ≥ 3) gives v_q ≥ 4!
    rw [hcardq, qVal_mul hq, qVal_natCast hq.ne_zero, padicValNat.self hq.one_lt]
    have h3 := lem_5_3_three_proved (splitDigraph H S₀ πT) q n hq hn hreg_S₀ (by omega) hpos_S₀
    calc (4 : ℕ∞) = (1 : ℕ∞) + (3 : ℕ∞) := by norm_num
      _ ≤ (1 : ℕ∞) + qVal q (term πT) := add_le_add (le_refl _) (le_trans h3 hterm_val)

/-! ### Part 3: Theorem 5.5 (`thm_5_5_quad_P`) -/

/-- Construct a concrete `q`-cycle on the upper half `{q, ..., 2q - 1}` of `Fin (2 * q)`. -/
private def halfCycle (q : ℕ) [NeZero q] (b : Fin 2) : Equiv.Perm (Fin (2 * q)) where
  toFun i :=
    if h : i.val / q = b.val then
      ⟨b.val * q + (i.val % q + 1) % q, by
        have hq : 0 < q := NeZero.pos q
        have hmod : (i.val % q + 1) % q < q := Nat.mod_lt _ hq
        have hb : b.val ≤ 1 := by omega
        nlinarith⟩
    else i
  invFun i :=
    if h : i.val / q = b.val then
      ⟨b.val * q + (i.val % q + q - 1) % q, by
        have hq : 0 < q := NeZero.pos q
        have hmod : (i.val % q + q - 1) % q < q := Nat.mod_lt _ hq
        have hb : b.val ≤ 1 := by omega
        nlinarith⟩
    else i
  left_inv i := by
    have hq : 0 < q := NeZero.pos q
    by_cases h : i.val / q = b.val
    · simp only [h, ↓reduceDIte]
      have hdiv : (b.val * q + (i.val % q + 1) % q) / q = b.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq,
          Nat.div_eq_of_lt (Nat.mod_lt _ hq), zero_add]
      have hmod1 : (b.val * q + (i.val % q + 1) % q) % q = (i.val % q + 1) % q := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_mod]
      simp only [hdiv, ↓reduceDIte, hmod1]
      apply Fin.ext; dsimp only
      have hstep : ((i.val % q + 1) % q + q - 1) % q = i.val % q := by
        have hlt : i.val % q < q := Nat.mod_lt _ hq
        by_cases hlast : i.val % q + 1 = q
        · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (show q - 1 < q by omega)]; omega
        · rw [Nat.mod_eq_of_lt (show i.val % q + 1 < q by omega)]
          have : i.val % q + 1 + q - 1 = i.val % q + q := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      rw [hstep, ← h, Nat.mul_comm, Nat.div_add_mod]
    · simp [h]
  right_inv i := by
    have hq : 0 < q := NeZero.pos q
    by_cases h : i.val / q = b.val
    · simp only [h, ↓reduceDIte]
      have hdiv : (b.val * q + (i.val % q + q - 1) % q) / q = b.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq,
          Nat.div_eq_of_lt (Nat.mod_lt _ hq), zero_add]
      have hmod1 : (b.val * q + (i.val % q + q - 1) % q) % q = (i.val % q + q - 1) % q := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_mod]
      simp only [hdiv, ↓reduceDIte, hmod1]
      apply Fin.ext; dsimp only
      have hstep : ((i.val % q + q - 1) % q + 1) % q = i.val % q := by
        have hlt : i.val % q < q := Nat.mod_lt _ hq
        by_cases h0 : i.val % q = 0
        · rw [h0, zero_add, Nat.mod_eq_of_lt (show q - 1 < q by omega),
            Nat.sub_add_cancel hq, Nat.mod_self]
        · have : i.val % q + q - 1 = (i.val % q - 1) + q := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (show i.val % q - 1 < q by omega),
            Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hlt]
      rw [hstep, ← h, Nat.mul_comm, Nat.div_add_mod]
    · simp [h]

private lemma halfCycle_pow_apply (q : ℕ) [NeZero q] (b : Fin 2) (k : ℕ) (i : Fin (2 * q)) :
    (halfCycle q b ^ k) i =
      if i.val / q = b.val then
        ⟨b.val * q + (i.val % q + k) % q, by
          have hq : 0 < q := NeZero.pos q
          have hmod : (i.val % q + k) % q < q := Nat.mod_lt _ hq
          have hb : b.val ≤ 1 := by omega
          nlinarith⟩
      else i := by
  have hq : 0 < q := NeZero.pos q
  induction k with
  | zero =>
    simp only [pow_zero, Equiv.Perm.coe_one, id_eq, add_zero]
    split_ifs with h
    · apply Fin.ext; dsimp only
      rw [Nat.mod_mod, ← h, Nat.div_add_mod']
    · rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    by_cases h : i.val / q = b.val
    · simp only [h, ↓reduceIte]
      have hdiv : (b.val * q + (i.val % q + k) % q) / q = b.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq,
          Nat.div_eq_of_lt (Nat.mod_lt _ hq), zero_add]
      have hmod1 : (b.val * q + (i.val % q + k) % q) % q = (i.val % q + k) % q := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_mod]
      simp only [halfCycle, Equiv.coe_fn_mk, hdiv, ↓reduceDIte, hmod1]
      apply Fin.ext; dsimp only
      rw [Nat.mod_add_mod, add_assoc]
    · simp [h, halfCycle]

private lemma halfCycle_pow_q (q : ℕ) [NeZero q] (b : Fin 2) : halfCycle q b ^ q = 1 := by
  apply Equiv.ext; intro i
  rw [halfCycle_pow_apply]
  split_ifs with h
  · apply Fin.ext; dsimp only
    rw [Nat.add_mod_right, Nat.mod_mod, ← h, Nat.div_add_mod']; rfl
  · rfl

private lemma halfCycle_comm (q : ℕ) [NeZero q] :
    halfCycle q 0 * halfCycle q 1 = halfCycle q 1 * halfCycle q 0 := by
  have hq : 0 < q := NeZero.pos q
  apply Equiv.ext; intro i
  change halfCycle q 0 (halfCycle q 1 i) = halfCycle q 1 (halfCycle q 0 i)
  by_cases h0 : i.val / q = 0
  · have h1 : i.val / q ≠ 1 := by omega
    have hdiv0 : (0 * q + (i.val % q + 1) % q) / q = 0 := by
      simp [Nat.div_eq_of_lt (Nat.mod_lt _ hq)]
    have hdiv0_ne1 : (0 * q + (i.val % q + 1) % q) / q ≠ 1 := by rw [hdiv0]; omega
    simp only [halfCycle, Equiv.coe_fn_mk, Fin.val_zero, Fin.val_one, h0, h1, Nat.zero_ne_one,
      ↓reduceDIte, hdiv0_ne1]
  · have hdiv_lt : i.val / q < 2 := Nat.div_lt_of_lt_mul (by linarith [i.isLt])
    have h1 : i.val / q = 1 := by
      cases hd : i.val / q with
      | zero => exact absurd hd h0
      | succ k => cases k with
        | zero => rfl
        | succ k => rw [hd] at hdiv_lt; omega
    have hdiv1 : (1 * q + (i.val % q + 1) % q) / q = 1 := by
      rw [one_mul, Nat.add_comm, Nat.add_div_right _ hq, Nat.div_eq_of_lt (Nat.mod_lt _ hq)]
    have hdiv1_ne0 : (1 * q + (i.val % q + 1) % q) / q ≠ 0 := by rw [hdiv1]; omega
    simp only [halfCycle, Equiv.coe_fn_mk, Fin.val_zero, Fin.val_one, h0, h1, Nat.one_ne_zero,
      ↓reduceDIte, hdiv1_ne0]

set_option maxHeartbeats 800000 in
/-- **Theorem 5.5**: For odd prime `q` and even `n` with `2q < n < 3q`, `q^2 ∣ D_n`,
`v_q(n!) = 2`, `q ∤ n`, and `M_q(n) ∣ D_n`. -/
theorem thm_5_5_quad_P_proved (q n : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (heven : Even n)
    (hlo : 2 * q < n) (hhi : n < 3 * q) :
    (q : ℤ) ^ 2 ∣ reducedDelta n ∧
    padicValNat q n.factorial = 2 ∧
    ¬ (q ∣ n) ∧
    (naturalModulus q n : ℤ) ∣ reducedDelta n := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hlt_sq : n < q ^ 2 := by nlinarith
  have hv_nfact : padicValNat q n.factorial = 2 := by
    rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by omega) hlt_sq)]
    have h1 : Finset.Ico 1 2 = {1} := by decide
    rw [h1, Finset.sum_singleton, pow_one]
    have : 2 * q ≤ n ∧ n < 3 * q := ⟨by omega, hhi⟩
    have hdiv_ge : 2 ≤ n / q := (Nat.le_div_iff_mul_le hq.pos).mpr (by omega)
    have hdiv_lt : n / q < 3 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hndvd_n : ¬ (q ∣ n) := by
    rintro ⟨k, rfl⟩
    have hk_gt : 2 < k := by nlinarith
    have hk_lt : k < 3 := by nlinarith
    omega
  have hv_n : padicValNat q n = 0 := padicValNat.eq_zero_of_not_dvd hndvd_n
  have hnatMod : naturalModulus q n = q ^ 2 := by
    unfold naturalModulus
    rw [hv_nfact, hv_n, add_zero]
  -- Helper: from q^6 ∣ delta n, deduce q^2 ∣ reducedDelta n!
  have hdvd_from_6 : (6 : ℕ∞) ≤ qVal q (delta n) → (q : ℤ) ^ 2 ∣ reducedDelta n := by
    intro h6
    have hdvd6 : (q : ℤ) ^ 6 ∣ delta n := (natCast_le_qVal_iff_dvd hq 6 (delta n)).mp h6
    rw [eq_normal_proved n heven] at hdvd6
    have hv_pred : padicValNat q (n - 1).factorial = 2 := by
      have h1 : n.factorial = n * (n - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
      rw [h1, padicValNat.mul (by omega) (Nat.factorial_ne_zero (n - 1)), hv_n, zero_add] at hv_nfact
      exact hv_nfact
    have hv_prod : padicValNat q (n.factorial * (n - 1).factorial) = 4 := by
      rw [padicValNat.mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1)),
        hv_nfact, hv_pred]
    have h4dvd : q ^ 4 ∣ n.factorial * (n - 1).factorial := by
      rw [← hv_prod]; exact pow_padicValNat_dvd
    rcases h4dvd with ⟨k, hk⟩
    have hndvd_k : ¬ (q ∣ k) := by
      rintro ⟨m, rfl⟩
      have hd5 : q ^ 5 ∣ n.factorial * (n - 1).factorial := ⟨m, by rw [hk]; ring⟩
      have hle := (padicValNat_dvd_iff_le
        (Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1)))).mp hd5
      omega
    rw [hk] at hdvd6
    push_cast at hdvd6
    rcases hdvd6 with ⟨m, hm⟩
    have hq4_ne : ((q : ℤ) ^ 4) ≠ 0 := pow_ne_zero 4 (Nat.cast_ne_zero.mpr hq.ne_zero)
    have hd_k : (q : ℤ) ^ 2 ∣ (k : ℤ) * reducedDelta n := by
      refine ⟨m, ?_⟩
      apply mul_left_cancel₀ hq4_ne
      calc (q : ℤ) ^ 4 * ((k : ℤ) * reducedDelta n)
          = (q : ℤ) ^ 4 * (k : ℤ) * reducedDelta n := by ring
        _ = (q : ℤ) ^ 6 * m := hm
        _ = (q : ℤ) ^ 4 * ((q : ℤ) ^ 2 * m) := by ring
    have hcop : IsCoprime ((q : ℤ) ^ 2) (k : ℤ) := by
      have hcop1 : Nat.Coprime (q ^ 2) k := (hq.coprime_iff_not_dvd.mpr hndvd_k).pow_left 2
      exact_mod_cast hcop1.isCoprime
    exact hcop.dvd_of_dvd_mul_left hd_k
  suffices hq2 : (q : ℤ) ^ 2 ∣ reducedDelta n by
    exact ⟨hq2, hv_nfact, hndvd_n, by rw [hnatMod]; exact_mod_cast hq2⟩
  apply hdvd_from_6
  -- Split into boundary case n = 3q - 1 (already covered by Quadratic!) vs 2q < n ≤ 3q - 3
  by_cases htop : n = 3 * q - 1
  · subst htop
    have h41a : ∀ m p : ℕ, Even m → 2 ≤ m → p.Prime →
        qVal p (delta m) ≥
          (padicValNat p (m - 1).factorial : ℕ∞) +
            (∑ N ∈ Finset.Icc 1 (m - 1), fVal p m N : ℕ∞) := fun m p hm hm2 hp =>
      (thm_4_1_quadratic_of prop_3_5_quad_ind_proved prop_3_6_identity_proved m hm hm2).1 p hp
    exact le_trans (by norm_num : (6 : ℕ∞) ≤ 7) (sec5_three_q_minus_one_of h41a q hq hodd)
  · -- Main case: 2q < n < 3q - 1, so n ≤ 3q - 3 (as n is even and 3q - 2 is odd)
    have hn_le : n ≤ 3 * q - 3 := by
      rcases heven with ⟨a, ha⟩
      rcases hq.odd_of_ne_two hodd with ⟨r, hr⟩
      omega
    have hq5 : 5 ≤ q := by
      rcases hq.odd_of_ne_two hodd with ⟨r, hr⟩
      omega
    have hn2 : 2 ≤ n := by omega
    -- Use Proposition 3.6: delta n = ± (n-1)! * j(J_{n-1} + I_{n-1})
    have hv_pred : padicValNat q (n - 1).factorial = 2 := by
      have h1 : n.factorial = n * (n - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
      rw [h1, padicValNat.mul (by omega) (Nat.factorial_ne_zero (n - 1)), hv_n, zero_add] at hv_nfact
      exact hv_nfact
    rw [prop_3_6_identity_proved n heven hn2, mul_assoc, qVal_neg_one_pow_mul hq, qVal_mul hq,
      qVal_natCast (Nat.factorial_ne_zero (n - 1)), hv_pred]
    suffices h4 : (4 : ℕ∞) ≤
        qVal q (circuitEval (allOnesMatrix (Fin (n - 1)) +
          (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)) n) by
      calc (6 : ℕ∞) = (2 : ℕ∞) + (4 : ℕ∞) := by norm_num
        _ ≤ (2 : ℕ∞) + qVal q (circuitEval _ n) := add_le_add (le_refl _) h4
    -- Let H = ofMatrix (J_{n-1} + I_{n-1}) on Fin (n - 1), split into S (first 2q vertices) and T (rest)
    let M : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ :=
      allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)
    let H := ofMatrix M
    have hM_eq : adjMatrix H = M := adjMatrix_ofMatrix M
    have hregH : IsRegular H n := by
      rw [isRegular_iff_adjMatrix, hM_eq]
      constructor
      · intro v; simp [M, allOnesMatrix, Matrix.one_apply, Finset.sum_add_distrib]; omega
      · intro u; simp [M, allOnesMatrix, Matrix.one_apply, Finset.sum_add_distrib]; omega
    let S : Finset (Fin (n - 1)) := Finset.univ.filter fun i : Fin (n - 1) => i.val < 2 * q
    have hcardS : S.card = 2 * q := by
      have hbi : S.card = Fintype.card (Fin (2 * q)) := by
        refine Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin (2 * q))) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro i₁ _ i₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin (2 * q) → ℕ) h)
        · intro j _
          exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, Fin.ext rfl⟩
      rw [hbi, Fintype.card_fin]
    have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
    have ht_lt_q : (Finset.univ.filter fun i : Fin (n - 1) => ¬ (i ∈ S)).card < q := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (n - 1))))
        (p := fun i => i ∈ S)
      have h2 : (Finset.univ.filter fun i : Fin (n - 1) => i ∈ S) = S := by ext i; simp
      rw [h2, hcardS, Finset.card_univ, Fintype.card_fin] at h1
      omega
    -- Apply Lemma 5.1 to H and S at -n
    have hsplit := lem_5_1_quad_split_proved H n hregH S hS_ne
    have heval := congrArg (Polynomial.eval (-(n : ℤ))) hsplit.1
    rw [circuitPoly_eval_eq_circuitEval H n, hM_eq, Polynomial.eval_finset_sum] at heval
    rw [heval]
    -- Embed G = Equiv.Perm { v // v ∈ S } into StabAut H S (fixing T pointwise!)
    let G := Equiv.Perm { v : Fin (n - 1) // v ∈ S }
    let extPerm (σ : G) : Equiv.Perm (Fin (n - 1)) :=
      { toFun := fun v => if hv : v ∈ S then (σ ⟨v, hv⟩).1 else v
        invFun := fun v => if hv : v ∈ S then (σ.symm ⟨v, hv⟩).1 else v
        left_inv := fun v => by
          by_cases hv : v ∈ S
          · simp only [hv, ↓reduceDIte, (σ ⟨v, hv⟩).2, Subtype.coe_eta]
            exact congrArg Subtype.val (σ.symm_apply_apply ⟨v, hv⟩)
          · simp [hv]
        right_inv := fun v => by
          by_cases hv : v ∈ S
          · simp only [hv, ↓reduceDIte, (σ.symm ⟨v, hv⟩).2, Subtype.coe_eta]
            exact congrArg Subtype.val (σ.apply_symm_apply ⟨v, hv⟩)
          · simp [hv] }
    have hext_M : ∀ (σ : G) (u v : Fin (n - 1)), M (extPerm σ u) (extPerm σ v) = M u v := by
      intro σ u v
      simp only [M, Matrix.add_apply, allOnesMatrix, Matrix.of_apply, Matrix.one_apply]
      congr 1
      by_cases h : u = v
      · subst h; simp
      · have hne : extPerm σ u ≠ extPerm σ v := fun heq => h ((extPerm σ).injective heq)
        simp [h, hne]
    have harc_ext : ∀ (a b : H.Arc), a.1 = b.1 → a.2.1 = b.2.1 → a.2.2.val = b.2.2.val → a = b := by
      rintro ⟨u₁, v₁, k₁⟩ ⟨u₂, v₂, k₂⟩ rfl rfl hk
      exact congrArg (fun k => (⟨u₁, v₁, k⟩ : H.Arc)) (Fin.ext hk)
    have hcast_val : ∀ {a b : ℕ} (h : a = b) (k : Fin a), (h ▸ k).val = k.val := by
      rintro _ _ rfl _; rfl
    let toAut (σ : G) : MultidigraphAut H :=
      { vPerm := extPerm σ
        aPerm :=
          { toFun := fun a => ⟨extPerm σ a.1, extPerm σ a.2.1,
              (hext_M σ a.1 a.2.1).symm ▸ a.2.2⟩
            invFun := fun a => ⟨(extPerm σ).symm a.1, (extPerm σ).symm a.2.1,
              (by
                have := hext_M σ ((extPerm σ).symm a.1) ((extPerm σ).symm a.2.1)
                simpa using this) ▸ a.2.2⟩
            left_inv := fun ⟨u, v, k⟩ => harc_ext _ _
              ((extPerm σ).symm_apply_apply u) ((extPerm σ).symm_apply_apply v)
              (by dsimp only; rw [hcast_val, hcast_val])
            right_inv := fun ⟨u, v, k⟩ => harc_ext _ _
              ((extPerm σ).apply_symm_apply u) ((extPerm σ).apply_symm_apply v)
              (by dsimp only; rw [hcast_val, hcast_val]) }
        map_tail := fun _ => rfl
        map_head := fun _ => rfl }
    have htoAut_S : ∀ (σ : G) (v : Fin (n - 1)), v ∈ S ↔ (toAut σ).vPerm v ∈ S := by
      intro σ v
      change v ∈ S ↔ extPerm σ v ∈ S
      by_cases hv : v ∈ S
      · simp [extPerm, hv, (σ ⟨v, hv⟩).2]
      · simp [extPerm, hv]
    let toStab : G →* StabAut H S :=
      { toFun := fun σ => ⟨toAut σ, htoAut_S σ⟩
        map_one' := by
          have hext1 : ∀ v, extPerm 1 v = v := fun v => by
            by_cases hv : v ∈ S
            · simp only [extPerm, Equiv.coe_fn_mk, hv, ↓reduceDIte]; rfl
            · simp [extPerm, hv]
          apply Subtype.ext; apply MultidigraphAut.ext
          · apply Equiv.ext; exact hext1
          · apply Equiv.ext; rintro ⟨u, v, k⟩
            exact harc_ext _ _ (hext1 u) (hext1 v)
              (by change ((hext_M 1 u v).symm ▸ k).val = k.val; exact hcast_val _ _)
        map_mul' := fun σ₁ σ₂ => by
          have hextm : ∀ v, extPerm (σ₁ * σ₂) v = extPerm σ₁ (extPerm σ₂ v) := fun v => by
            by_cases hv : v ∈ S
            · simp only [extPerm, Equiv.coe_fn_mk, hv, ↓reduceDIte, (σ₂ ⟨v, hv⟩).2,
                Subtype.coe_eta]; rfl
            · simp [extPerm, hv]
          apply Subtype.ext; apply MultidigraphAut.ext
          · apply Equiv.ext; exact hextm
          · apply Equiv.ext; rintro ⟨u, v, k⟩
            exact harc_ext _ _ (hextm u) (hextm v)
              (by
                change ((hext_M (σ₁ * σ₂) u v).symm ▸ k).val =
                  ((hext_M σ₁ (extPerm σ₂ u) (extPerm σ₂ v)).symm ▸
                    (hext_M σ₂ u v).symm ▸ k).val
                rw [hcast_val, hcast_val, hcast_val]) }
    -- Action of G on PartialTransition H S via toStab
    letI : MulAction G (PartialTransition H S) := MulAction.compHom (PartialTransition H S) toStab
    let term (πT : PartialTransition H S) : ℤ :=
      (Polynomial.X ^ cycInsideT H S πT * circuitPoly (splitDigraph H S πT)).eval (-(n : ℤ))
    have hinv : ∀ σ : G, ∀ πT : PartialTransition H S, term (σ • πT) = term πT := by
      intro σ πT
      have hrem := rem_5_2_aut_proved H S (toAut σ) (htoAut_S σ) πT
      change (Polynomial.X ^ cycInsideT H S (autActPartial (toAut σ) (htoAut_S σ) πT) *
        circuitPoly (splitDigraph H S (autActPartial (toAut σ) (htoAut_S σ) πT))).eval (-(n : ℤ)) =
        (Polynomial.X ^ cycInsideT H S πT * circuitPoly (splitDigraph H S πT)).eval (-(n : ℤ))
      rw [hrem.1, hrem.2.1]
    let _ : Fintype (Quotient (MulAction.orbitRel G (PartialTransition H S))) := Fintype.ofFinite _
    rw [sum_eq_sum_orbits term hinv]
    refine le_qVal_sum hq Finset.univ _ (4 : ℕ∞) fun ω _ => ?_
    set πT := Quotient.out ω
    let _ : Fintype (MulAction.orbit G πT) := Fintype.ofFinite _
    have hsplit_πT := hsplit.2 πT
    have hreg_S : IsRegular (splitDigraph H S πT) n := hsplit_πT.1
    have hpos_S : ∀ u v : { v : Fin (n - 1) // v ∈ S }, 1 ≤ adjMatrix (splitDigraph H S πT) u v := by
      rcases hsplit_πT.2 with ⟨R, hMR, _, _⟩
      intro u v; rw [hMR, hM_eq]
      change 1 ≤ (allOnesMatrix (Fin (n - 1)) u.1 v.1 + (1 : Matrix _ _ ℕ) u.1 v.1) + R u v
      have : allOnesMatrix (Fin (n - 1)) u.1 v.1 = 1 := rfl
      omega
    have hcard_S_ty : Fintype.card { v : Fin (n - 1) // v ∈ S } = 2 * q := by
      rw [Fintype.card_coe, hcardS]
    have hterm_val : qVal q (term πT) ≥ qVal q (circuitEval (adjMatrix (splitDigraph H S πT)) n) := by
      dsimp only [term]
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        circuitPoly_eval_eq_circuitEval, qVal_mul hq]
      exact le_add_self
    set orbCard := (Finset.univ.filter fun x : PartialTransition H S =>
      Quotient.mk (MulAction.orbitRel G (PartialTransition H S)) x = ω).card
    by_cases hqdvd : q ∣ orbCard
    · -- Case 1: q divides the orbit size!
      have horb_pos : 0 < orbCard := by
        rw [show orbCard = Fintype.card (MulAction.orbit G πT) from card_orbit_fiber_eq ω]
        exact Fintype.card_pos_iff.mpr ⟨⟨πT, ⟨1, one_smul G πT⟩⟩⟩
      have hv_orb : 1 ≤ padicValNat q orbCard :=
        one_le_padicValNat_of_dvd (Nat.ne_of_gt horb_pos) hqdvd
      have h3 := lem_5_3_three_proved (splitDigraph H S πT) q n hq hlo hreg_S (by omega) hpos_S
      rw [qVal_mul hq, qVal_natCast (Nat.ne_of_gt horb_pos)]
      calc (4 : ℕ∞) = (1 : ℕ∞) + (3 : ℕ∞) := by norm_num
        _ ≤ (padicValNat q orbCard : ℕ∞) + qVal q (term πT) :=
            add_le_add (by exact_mod_cast hv_orb) (le_trans h3 hterm_val)
    · -- Case 2: q ∤ orbCard, so Stab_G(πT) contains a Sylow q-subgroup of G, hence a q-cycle on S₁ fixing S₀!
      have horb_pos : 0 < orbCard := by
        rw [show orbCard = Fintype.card (MulAction.orbit G πT) from card_orbit_fiber_eq ω]
        exact Fintype.card_pos_iff.mpr ⟨⟨πT, ⟨1, one_smul G πT⟩⟩⟩
      have horb_eq : orbCard * Nat.card (MulAction.stabilizer G πT) = Nat.card G := by
        rw [show orbCard = Fintype.card (MulAction.orbit G πT) from card_orbit_fiber_eq ω,
          Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G πT
      have hcardG : Nat.card G = (2 * q).factorial := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcard_S_ty]
      have hv_G : padicValNat q (Nat.card G) = 2 := by
        rw [hcardG]
        have hlt2q : 2 * q < q ^ 2 := by nlinarith
        rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by omega) hlt2q)]
        have h1 : Finset.Ico 1 2 = {1} := by decide
        rw [h1, Finset.sum_singleton, pow_one, Nat.mul_div_cancel _ hq.pos]
      have hq2_dvd_stab : q ^ 2 ∣ Nat.card (MulAction.stabilizer G πT) := by
        have hq2_G : q ^ 2 ∣ Nat.card G := by rw [← hv_G]; exact pow_padicValNat_dvd
        rw [← horb_eq] at hq2_G
        exact ((hq.coprime_iff_not_dvd.mpr hqdvd).pow_left 2).dvd_of_dvd_mul_left hq2_G
      -- Take a Sylow q-subgroup Q of Stab_G(πT), push it to G, and compare with our concrete P₀ = ⟨c₀, c₁⟩!
      let eS : Fin (2 * q) ≃ { v : Fin (n - 1) // v ∈ S } :=
        (Fintype.equivFinOfCardEq hcard_S_ty).symm
      let c0 : G := Equiv.permCongrHom eS (halfCycle q 0)
      let c1 : G := Equiv.permCongrHom eS (halfCycle q 1)
      let P0 : Subgroup G := Subgroup.closure {c0, c1}
      have hc0_q : c0 ^ q = 1 := by
        dsimp only [c0]; rw [← map_pow, halfCycle_pow_q, map_one]
      have hc1_q : c1 ^ q = 1 := by
        dsimp only [c1]; rw [← map_pow, halfCycle_pow_q, map_one]
      have hcomm : c0 * c1 = c1 * c0 := by
        dsimp only [c0, c1]; rw [← map_mul, ← map_mul, halfCycle_comm]
      have hcard_P0 : Nat.card P0 = q ^ 2 := by
        -- Explicit bijection Fin q × Fin q ≃ P0 via (a, b) ↦ c0^a * c1^b
        let f : ZMod q × ZMod q → P0 := fun p =>
          ⟨c0 ^ p.1.val * c1 ^ p.2.val,
            Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
              (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩
        have hf_inj : Function.Injective f := by
          intro p₁ p₂ heq
          have hval : c0 ^ p₁.1.val * c1 ^ p₁.2.val = c0 ^ p₂.1.val * c1 ^ p₂.2.val :=
            congrArg Subtype.val heq
          have hval' : halfCycle q 0 ^ p₁.1.val * halfCycle q 1 ^ p₁.2.val =
              halfCycle q 0 ^ p₂.1.val * halfCycle q 1 ^ p₂.2.val := by
            have hhom : Equiv.permCongrHom eS (halfCycle q 0 ^ p₁.1.val * halfCycle q 1 ^ p₁.2.val) =
                Equiv.permCongrHom eS (halfCycle q 0 ^ p₂.1.val * halfCycle q 1 ^ p₂.2.val) := by
              simpa only [map_mul, map_pow] using hval
            exact (Equiv.permCongr eS).injective hhom
          have h0_eq := congrArg (fun σ : Equiv.Perm (Fin (2 * q)) => σ ⟨0, by omega⟩) hval'
          have h1_eq := congrArg (fun σ : Equiv.Perm (Fin (2 * q)) => σ ⟨q, by omega⟩) hval'
          have hv1 : p₁.1.val = p₂.1.val := by
            simp only [Equiv.Perm.mul_apply, halfCycle_pow_apply, Fin.val_zero, Fin.val_one] at h0_eq
            have hdiv0 : (0 : ℕ) / q = 0 := Nat.zero_div q
            have hne01 : (0 : ℕ) / q ≠ 1 := by omega
            simp only [hdiv0, Nat.zero_ne_one, ↓reduceIte, zero_mul, Nat.zero_mod, zero_add] at h0_eq
            have hmod : p₁.1.val % q = p₂.1.val % q := congrArg Fin.val h0_eq
            rwa [Nat.mod_eq_of_lt p₁.1.val_lt, Nat.mod_eq_of_lt p₂.1.val_lt] at hmod
          have hv2 : p₁.2.val = p₂.2.val := by
            simp only [Equiv.Perm.mul_apply, halfCycle_pow_apply, Fin.val_zero, Fin.val_one] at h1_eq
            have hdivq : q / q = 1 := Nat.div_self hq.pos
            have hmodq : q % q = 0 := Nat.mod_self q
            have hdiv_res : ∀ k : ℕ, (1 * q + k % q) / q ≠ 0 := fun k => by
              rw [one_mul, Nat.add_comm, Nat.add_div_right _ hq.pos,
                Nat.div_eq_of_lt (Nat.mod_lt k hq.pos)]; omega
            simp only [hdivq, hmodq, zero_add, ↓reduceIte, hdiv_res] at h1_eq
            have hmod := congrArg Fin.val h1_eq
            dsimp only at hmod
            rw [Nat.mod_eq_of_lt p₁.2.val_lt, Nat.mod_eq_of_lt p₂.2.val_lt] at hmod
            omega
          exact Prod.ext (ZMod.val_injective q hv1) (ZMod.val_injective q hv2)
        have hsub_le : Subgroup.closure {c0, c1} ≤
            { carrier := { x : G | ∃ a b : ℕ, x = c0 ^ a * c1 ^ b }
              mul_mem' := by
                rintro _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
                refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
                have hcomm_pow : c1 ^ b₁ * c0 ^ a₂ = c0 ^ a₂ * c1 ^ b₁ :=
                  (Commute.pow_left (Commute.pow_right hcomm.symm a₂) b₁)
                rw [pow_add, pow_add, mul_assoc, ← mul_assoc (c1 ^ b₁), hcomm_pow, mul_assoc,
                  ← mul_assoc]
              one_mem' := ⟨0, 0, by simp⟩
              inv_mem' := by
                rintro _ ⟨a, b, rfl⟩
                refine ⟨(q - a % q) % q, (q - b % q) % q, ?_⟩
                have hinv0 : (c0 ^ a)⁻¹ = c0 ^ ((q - a % q) % q) := by
                  have h1 : c0 ^ a = c0 ^ (a % q) := by
                    conv_lhs => rw [← Nat.div_add_mod a q, pow_add, pow_mul, hc0_q, one_pow, one_mul]
                  rw [h1, inv_eq_iff_mul_eq_one, ← pow_add]
                  have hdvd : q ∣ a % q + (q - a % q) % q := by
                    by_cases ha0 : a % q = 0
                    · rw [ha0, Nat.sub_zero, Nat.mod_self, add_zero]; exact dvd_zero q
                    · rw [Nat.mod_eq_of_lt (show q - a % q < q by have := Nat.mod_lt a hq.pos; omega),
                        Nat.add_sub_cancel' (le_of_lt (Nat.mod_lt a hq.pos))]
                  rcases hdvd with ⟨t, ht⟩
                  rw [ht, pow_mul, hc0_q, one_pow]
                have hinv1 : (c1 ^ b)⁻¹ = c1 ^ ((q - b % q) % q) := by
                  have h1 : c1 ^ b = c1 ^ (b % q) := by
                    conv_lhs => rw [← Nat.div_add_mod b q, pow_add, pow_mul, hc1_q, one_pow, one_mul]
                  rw [h1, inv_eq_iff_mul_eq_one, ← pow_add]
                  have hdvd : q ∣ b % q + (q - b % q) % q := by
                    by_cases hb0 : b % q = 0
                    · rw [hb0, Nat.sub_zero, Nat.mod_self, add_zero]; exact dvd_zero q
                    · rw [Nat.mod_eq_of_lt (show q - b % q < q by have := Nat.mod_lt b hq.pos; omega),
                        Nat.add_sub_cancel' (le_of_lt (Nat.mod_lt b hq.pos))]
                  rcases hdvd with ⟨t, ht⟩
                  rw [ht, pow_mul, hc1_q, one_pow]
                rw [mul_inv_rev, hinv0, hinv1]
                exact (Commute.pow_left (Commute.pow_right hcomm.symm _) _) } := by
          rw [Subgroup.closure_le]
          intro x hx
          rcases hx with rfl | rfl
          · exact ⟨1, 0, by simp⟩
          · exact ⟨0, 1, by simp⟩
        have hf_surj : Function.Surjective f := by
          rintro ⟨x, hx⟩
          rcases hsub_le hx with ⟨a, b, rfl⟩
          refine ⟨((a : ZMod q), (b : ZMod q)), Subtype.ext ?_⟩
          change c0 ^ (a : ZMod q).val * c1 ^ (b : ZMod q).val = c0 ^ a * c1 ^ b
          rw [ZMod.val_natCast, ZMod.val_natCast]
          have h1 : c0 ^ a = c0 ^ (a % q) := by
            conv_lhs => rw [← Nat.div_add_mod a q, pow_add, pow_mul, hc0_q, one_pow, one_mul]
          have h2 : c1 ^ b = c1 ^ (b % q) := by
            conv_lhs => rw [← Nat.div_add_mod b q, pow_add, pow_mul, hc1_q, one_pow, one_mul]
          rw [h1, h2]
        rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩),
          Fintype.card_prod, ZMod.card, sq]
      -- Both P0 and a Sylow q-subgroup Q of Stab_G(πT) have order q^2 = q^(v_q |G|), hence are Sylow q-subgroups of G!
      have hP0_isP : IsPGroup q P0 := by
        rw [IsPGroup.iff_card]; exact ⟨2, hcard_P0⟩
      obtain ⟨Q_stab⟩ : Nonempty (Sylow q (MulAction.stabilizer G πT)) := inferInstance
      let Q : Subgroup G := Q_stab.toSubgroup.map (MulAction.stabilizer G πT).subtype
      have hQ_sub : Q ≤ MulAction.stabilizer G πT := by
        rintro x ⟨y, _, rfl⟩; exact y.2
      have hQ_card : Nat.card Q = q ^ 2 := by
        have hcard_Qstab : Nat.card Q_stab = q ^ (Nat.factorization (Nat.card (MulAction.stabilizer G πT)) q) :=
          Q_stab.card_eq_multiplicity
        have hfac_ge : 2 ≤ Nat.factorization (Nat.card (MulAction.stabilizer G πT)) q := by
          rw [Nat.factorization_def _ hq]
          exact (padicValNat_dvd_iff_le (Nat.card_pos.ne')).mp hq2_dvd_stab
        have hfac_le : Nat.factorization (Nat.card (MulAction.stabilizer G πT)) q ≤ 2 := by
          have hdvd_G : Nat.card (MulAction.stabilizer G πT) ∣ Nat.card G :=
            Subgroup.card_subgroup_dvd_card _
          have hle := (padicValNat_dvd_iff_le (p := q) (Nat.card_pos.ne')).mp
            (dvd_trans (pow_padicValNat_dvd (p := q)) hdvd_G)
          rw [Nat.factorization_def _ hq]; omega
        have hfac_eq : Nat.factorization (Nat.card (MulAction.stabilizer G πT)) q = 2 := by omega
        have hmap_card : Nat.card Q = Nat.card Q_stab := by
          refine (Nat.card_congr (Equiv.ofBijective
            (fun y : Q_stab => (⟨y.1.1, ⟨y.1, y.2, rfl⟩⟩ : Q))
            ⟨fun y₁ y₂ h => Subtype.ext (Subtype.ext (congrArg (Subtype.val : Q → G) h)),
             fun ⟨_, ⟨y, hy, rfl⟩⟩ => ⟨⟨y, hy⟩, rfl⟩⟩)).symm
        rw [hmap_card, hcard_Qstab, hfac_eq]
      have hQ_isP : IsPGroup q Q := by rw [IsPGroup.iff_card]; exact ⟨2, hQ_card⟩
      -- Lift P0 and Q to Sylow q G and apply Sylow conjugacy!
      have hP0_max : ∀ K : Subgroup G, IsPGroup q K → P0 ≤ K → K = P0 := by
        intro K hK hle
        rcases IsPGroup.iff_card.mp hK with ⟨r, hr⟩
        have hr_le : r ≤ 2 := by
          have hdvd : q ^ r ∣ Nat.card G := hr ▸ Subgroup.card_subgroup_dvd_card K
          have := (padicValNat_dvd_iff_le (Nat.card_pos.ne')).mp hdvd
          omega
        have hr_ge : 2 ≤ r := by
          have hdvd : q ^ 2 ∣ q ^ r := hcard_P0 ▸ hr ▸ Subgroup.card_dvd_of_le hle
          exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvd
        have hcard_eq : Nat.card P0 = Nat.card K := by rw [hcard_P0, hr, show r = 2 by omega]
        exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm)).symm
      have hQ_max : ∀ K : Subgroup G, IsPGroup q K → Q ≤ K → K = Q := by
        intro K hK hle
        rcases IsPGroup.iff_card.mp hK with ⟨r, hr⟩
        have hr_le : r ≤ 2 := by
          have hdvd : q ^ r ∣ Nat.card G := hr ▸ Subgroup.card_subgroup_dvd_card K
          have := (padicValNat_dvd_iff_le (Nat.card_pos.ne')).mp hdvd
          omega
        have hr_ge : 2 ≤ r := by
          have hdvd : q ^ 2 ∣ q ^ r := hQ_card ▸ hr ▸ Subgroup.card_dvd_of_le hle
          exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvd
        have hcard_eq : Nat.card Q = Nat.card K := by rw [hQ_card, hr, show r = 2 by omega]
        exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard_eq.symm)).symm
      let SP0 : Sylow q G := ⟨P0, hP0_isP, fun {K} hK hle => hP0_max K hK hle⟩
      let SQ : Sylow q G := ⟨Q, hQ_isP, fun {K} hK hle => hQ_max K hK hle⟩
      obtain ⟨hconj, hhconj⟩ := MulAction.exists_smul_eq G SP0 SQ
      -- Let σ = hconj * c1 * hconj⁻¹ ∈ Q ≤ Stab_G(πT)!
      let σ : G := hconj * c1 * hconj⁻¹
      have hσ_mem_Q : σ ∈ Q := by
        have hc1_mem : c1 ∈ SP0 := Subgroup.subset_closure (by simp)
        change σ ∈ SQ.toSubgroup
        rw [← hhconj]
        exact ⟨c1, hc1_mem, rfl⟩
      have hσ_stab : σ • πT = πT := hQ_sub hσ_mem_Q
      -- Induce automorphism gS of splitDigraph H S πT from toAut σ!
      let gS : MultidigraphAut (splitDigraph H S πT) :=
        inducedAutSplit (toAut σ) (htoAut_S σ) πT hσ_stab
      have hσ_pow_q : σ ^ q = 1 := by
        dsimp only [σ]
        rw [conj_pow, hc1_q, mul_one, mul_inv_cancel]
      have htoAut_pow_q : (toAut σ) ^ q = 1 := by
        have : toStab (σ ^ q) = 1 := by rw [hσ_pow_q, map_one]
        rw [map_pow] at this
        have h1 : ((toStab σ) ^ q).1 = (1 : MultidigraphAut H) := congrArg Subtype.val this
        exact h1
      have hgS_pow_q : gS ^ q = 1 := inducedAutSplit_pow_eq_one _ _ _ _ htoAut_pow_q
      have hgS_vPerm : ∀ u : { v : Fin (n - 1) // v ∈ S }, gS.vPerm u = σ u := by
        intro u; apply Subtype.ext
        change extPerm σ u.1 = (σ u).1
        simp [extPerm, u.2]
      -- Partition { v // v ∈ S } into S₀ = image of {0..q-1} and S₁ = image of {q..2q-1} under hconj ∘ eS!
      let eP : Fin (2 * q) ≃ { v : Fin (n - 1) // v ∈ S } := eS.trans hconj
      let S₀ : Finset { v : Fin (n - 1) // v ∈ S } :=
        (Finset.univ.filter fun i : Fin (2 * q) => i.val < q).image eP
      let S₁ : Finset { v : Fin (n - 1) // v ∈ S } :=
        (Finset.univ.filter fun i : Fin (2 * q) => q ≤ i.val).image eP
      have hdisj_S : Disjoint S₀ S₁ := by
        rw [Finset.disjoint_left]
        intro u hu0 hu1
        rcases Finset.mem_image.mp hu0 with ⟨i, hi, rfl⟩
        rcases Finset.mem_image.mp hu1 with ⟨j, hj, hij⟩
        have := eP.injective hij
        subst this
        have h1' := (Finset.mem_filter.mp hi).2
        have h2' := (Finset.mem_filter.mp hj).2
        omega
      have hcov_S : S₀ ∪ S₁ = Finset.univ := by
        ext u
        simp only [Finset.mem_union, Finset.mem_univ, iff_true, S₀, S₁, Finset.mem_image,
          Finset.mem_filter, true_and]
        by_cases h : (eP.symm u).val < q
        · exact Or.inl ⟨eP.symm u, h, eP.apply_symm_apply u⟩
        · exact Or.inr ⟨eP.symm u, by omega, eP.apply_symm_apply u⟩
      have hcard_S₀ : S₀.card = q := by
        rw [Finset.card_image_of_injective _ eP.injective]
        have hbi : (Finset.univ.filter fun i : Fin (2 * q) => i.val < q).card =
            Fintype.card (Fin q) := by
          refine Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin q)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro i₁ _ i₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin q → ℕ) h)
          · intro j _
            exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, Fin.ext rfl⟩
        rw [hbi, Fintype.card_fin]
      have hcard_S₁ : S₁.card = q := by
        rw [Finset.card_image_of_injective _ eP.injective]
        have hbi : (Finset.univ.filter fun i : Fin (2 * q) => q ≤ i.val).card =
            Fintype.card (Fin q) := by
          refine Finset.card_bij (fun i hi => (⟨i.val - q, by
              have := (Finset.mem_filter.mp hi).2; have := i.isLt; omega⟩ : Fin q)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro i₁ hi₁ i₂ hi₂ h
            have h1' := (Finset.mem_filter.mp hi₁).2
            have h2' := (Finset.mem_filter.mp hi₂).2
            have hv := congrArg (Fin.val : Fin q → ℕ) h
            dsimp at hv; exact Fin.ext (by omega)
          · intro j _
            exact ⟨⟨j.val + q, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩,
              Fin.ext (by simp)⟩
        rw [hbi, Fintype.card_fin]
      have hgS_act : ∀ i : Fin (2 * q), gS.vPerm (eP i) = eP (halfCycle q 1 i) := by
        intro i
        rw [hgS_vPerm]
        change hconj (eS.permCongr (halfCycle q 1) (hconj.symm (hconj (eS i)))) =
          hconj (eS (halfCycle q 1 i))
        rw [hconj.symm_apply_apply, Equiv.permCongr_apply, eS.symm_apply_apply]
      have hgS_pow_act : ∀ (k : ℕ) (i : Fin (2 * q)),
          (gS.vPerm ^ k) (eP i) = eP ((halfCycle q 1 ^ k) i) := by
        intro k i
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, hgS_act]
      have hgS_fix : ∀ a ∈ S₀, gS.vPerm a = a := by
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
        rw [hgS_act]
        have hlt : i.val < q := (Finset.mem_filter.mp hi).2
        have hdiv : i.val / q ≠ 1 := by rw [Nat.div_eq_of_lt hlt]; norm_num
        simp [halfCycle, hdiv]
      have hgS_trans : ∀ b₁ ∈ S₁, ∀ b₂ ∈ S₁, ∃ k : ℕ, (gS.vPerm ^ k) b₁ = b₂ := by
        intro b₁ hb₁ b₂ hb₂
        rcases Finset.mem_image.mp hb₁ with ⟨i₁, hi₁, rfl⟩
        rcases Finset.mem_image.mp hb₂ with ⟨i₂, hi₂, rfl⟩
        have h1' : q ≤ i₁.val := (Finset.mem_filter.mp hi₁).2
        have h2' : q ≤ i₂.val := (Finset.mem_filter.mp hi₂).2
        refine ⟨(i₂.val % q + q - i₁.val % q) % q, ?_⟩
        rw [hgS_pow_act]
        congr 1
        rw [halfCycle_pow_apply]
        have hdiv1 : i₁.val / q = 1 := by
          have hlt1 : i₁.val / q < 2 := Nat.div_lt_of_lt_mul (by linarith [i₁.isLt])
          have hge1 : 1 ≤ i₁.val / q := (Nat.le_div_iff_mul_le hq.pos).mpr (by omega)
          omega
        simp only [hdiv1, Fin.val_one, ↓reduceIte]
        apply Fin.ext; dsimp only
        have hmod_eq : (i₁.val % q + (i₂.val % q + q - i₁.val % q) % q) % q = i₂.val % q := by
          have hm1 : i₁.val % q < q := Nat.mod_lt _ hq.pos
          have hm2 : i₂.val % q < q := Nat.mod_lt _ hq.pos
          rw [Nat.add_mod_mod]
          have : i₁.val % q + (i₂.val % q + q - i₁.val % q) = i₂.val % q + q := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hm2]
        rw [hmod_eq]
        have hdiv2 : i₂.val / q = 1 := by
          have hlt2 : i₂.val / q < 2 := Nat.div_lt_of_lt_mul (by linarith [i₂.isLt])
          have hge2 : 1 ≤ i₂.val / q := (Nat.le_div_iff_mul_le hq.pos).mpr (by omega)
          omega
        have hdm := Nat.div_add_mod i₂.val q
        rw [hdiv2, mul_one] at hdm
        omega
      have hgS_ne_one : gS ≠ 1 := by
        intro heq
        have h1' := hgS_act ⟨q, by omega⟩
        rw [heq] at h1'
        have h2' := eP.injective h1'.symm
        have hdivq : q / q = 1 := Nat.div_self hq.pos
        have hmodq : q % q = 0 := Nat.mod_self q
        have hv := congrArg Fin.val h2'
        simp [halfCycle, hdivq, hmodq, Nat.mod_eq_of_lt hq.one_lt] at hv
      have hord_gS : orderOf gS = q := by
        have hdvd : orderOf gS ∣ q := orderOf_dvd_of_pow_eq_one hgS_pow_q
        rcases hq.eq_one_or_self_of_dvd _ hdvd with h1' | hq'
        · exact absurd (orderOf_eq_one_iff.mp h1') hgS_ne_one
        · exact hq'
      -- Show adjMatrix (splitDigraph H S πT) a b = 1 for all a ∈ S₀, b ∈ S₁!
      have hadj_one : ∀ a ∈ S₀, ∀ b ∈ S₁, adjMatrix (splitDigraph H S πT) a b = 1 := by
        rcases hsplit_πT.2 with ⟨R, hMR, hrowR, _⟩
        -- Automorphism gS preserves adjMatrix (splitDigraph H S πT)!
        have hadj_inv : ∀ (u v : { v : Fin (n - 1) // v ∈ S }),
            adjMatrix (splitDigraph H S πT) (gS.vPerm u) (gS.vPerm v) =
            adjMatrix (splitDigraph H S πT) u v := by
          intro u v
          change (Finset.univ.filter fun e => (splitDigraph H S πT).tail e = gS.vPerm u ∧
              (splitDigraph H S πT).head e = gS.vPerm v).card =
            (Finset.univ.filter fun e => (splitDigraph H S πT).tail e = u ∧
              (splitDigraph H S πT).head e = v).card
          refine Finset.card_bij (fun e _ => gS.aPerm.symm e) ?_ ?_ ?_
          · intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
            constructor
            · apply gS.vPerm.injective; rw [← gS.map_tail, gS.aPerm.apply_symm_apply, he.1]
            · apply gS.vPerm.injective; rw [← gS.map_head, gS.aPerm.apply_symm_apply, he.2]
          · intro e₁ _ e₂ _ h; exact gS.aPerm.symm.injective h
          · intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
            refine ⟨gS.aPerm e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
              gS.aPerm.symm_apply_apply e⟩
            · rw [gS.map_tail, he.1]
            · rw [gS.map_head, he.2]
        have hadj_inv_pow : ∀ (k : ℕ) (u v : { v : Fin (n - 1) // v ∈ S }),
            adjMatrix (splitDigraph H S πT) ((gS.vPerm ^ k) u) ((gS.vPerm ^ k) v) =
            adjMatrix (splitDigraph H S πT) u v := by
          intro k u v
          induction k with
          | zero => rfl
          | succ k ih =>
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hadj_inv, ih]
        intro a ha b hb
        have hM_ab : ∀ b' ∈ S₁, adjMatrix (splitDigraph H S πT) a b' = 1 + R a b' := by
          intro b' hb'
          have hne : a.1 ≠ b'.1 := fun h =>
            Finset.disjoint_left.mp hdisj_S ha (Subtype.ext h ▸ hb')
          rw [hMR, hM_eq]
          change (allOnesMatrix (Fin (n - 1)) a.1 b'.1 + (1 : Matrix _ _ ℕ) a.1 b'.1) + R a b' = _
          simp [allOnesMatrix, Matrix.one_apply, hne]
        have hR_const : ∀ b' ∈ S₁, R a b' = R a b := by
          intro b' hb'
          obtain ⟨k, hk⟩ := hgS_trans b hb b' hb'
          have hfix_k : (gS.vPerm ^ k) a = a := by
            clear hk
            induction k with
            | zero => rfl
            | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hgS_fix a ha]
          have h1' := hadj_inv_pow k a b
          rw [hfix_k, hk, hM_ab b' hb', hM_ab b hb] at h1'
          omega
        have hrow_lt : ∑ v : { v : Fin (n - 1) // v ∈ S }, R a v < q := by
          rw [hrowR a]
          have hcard_ex : (Finset.univ.filter fun e : H.Arc => H.tail e = a.1 ∧ H.head e ∉ S).card =
              (Finset.univ.filter fun i : Fin (n - 1) => ¬ (i ∈ S)).card := by
            refine Finset.card_bij (fun e _ => H.head e) ?_ ?_ ?_
            · intro e he; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.2⟩
            · intro e₁ he₁ e₂ he₂ hhead
              have h1' := (Finset.mem_filter.mp he₁).2
              have h2' := (Finset.mem_filter.mp he₂).2
              rcases e₁ with ⟨u₁, v₁, k₁⟩
              rcases e₂ with ⟨u₂, v₂, k₂⟩
              dsimp [H, ofMatrix] at h1' h2' hhead
              rcases h1' with ⟨rfl, hv1⟩
              rcases h2' with ⟨rfl, hv2⟩
              subst hhead
              have hne : a.1 ≠ v₁ := fun h => hv1 (h ▸ a.2)
              have hM1 : M a.1 v₁ = 1 := by simp [M, allOnesMatrix, Matrix.one_apply, hne]
              have hk : k₁ = k₂ := Fin.ext (by have := k₁.isLt; have := k₂.isLt; omega)
              rw [hk]
            · intro i hi
              have hi_out : i ∉ S := (Finset.mem_filter.mp hi).2
              have hne : a.1 ≠ i := fun h => hi_out (h ▸ a.2)
              have hM1 : M a.1 i = 1 := by simp [M, allOnesMatrix, Matrix.one_apply, hne]
              exact ⟨⟨a.1, i, ⟨0, by omega⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hi_out⟩, rfl⟩
          rw [hcard_ex]; exact ht_lt_q
        have hqR_lt : q * R a b < q := by
          calc q * R a b = ∑ _b' ∈ S₁, R a b := by rw [Finset.sum_const, hcard_S₁, smul_eq_mul]
            _ = ∑ b' ∈ S₁, R a b' := Finset.sum_congr rfl fun b' hb' => (hR_const b' hb').symm
            _ ≤ ∑ v : { v : Fin (n - 1) // v ∈ S }, R a v :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S₁) (fun _ _ _ => Nat.zero_le _)
            _ < q := hrow_lt
        have hRab0 : R a b = 0 := by nlinarith
        rw [hM_ab b hb, hRab0]
      -- Apply Lemma 5.4 to splitDigraph H S πT!
      have h4_S := lem_5_4_quad_S_proved (splitDigraph H S πT) q n hq hodd hlo hreg_S S₀ S₁
        hdisj_S hcov_S hcard_S₀ hcard_S₁ hpos_S hadj_one gS hord_gS hgS_fix hgS_trans
      rw [qVal_mul hq]
      calc (4 : ℕ∞) ≤ qVal q (circuitEval (adjMatrix (splitDigraph H S πT)) n) := h4_S
        _ ≤ qVal q (term πT) := hterm_val
        _ ≤ qVal q (orbCard : ℤ) + qVal q (term πT) := le_add_self

end AlonTarsi.Proofs

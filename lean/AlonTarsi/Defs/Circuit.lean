/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Defs.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.Sigma

/-!
# Multidigraphs, Circuit Partition Polynomials, and Vertex Removal

This file defines finite multidigraphs, `d`-regularity, transition systems, closed-trail
counts, the circuit partition polynomial `j(H; x)`, its evaluation `j(M) = j(H; -d)`,
the complete digraph with loops `K_n^∘`, single-vertex removal `H_σ`, subset elimination
`H_{π_T}`, and multidigraph automorphisms.
-/

namespace AlonTarsi

/-- A finite multidigraph on vertex set `V` with labeled arcs. -/
structure Multidigraph (V : Type) where
  Arc : Type
  [arcFintype : Fintype Arc]
  [arcDecEq : DecidableEq Arc]
  tail : Arc → V
  head : Arc → V

attribute [instance] Multidigraph.arcFintype Multidigraph.arcDecEq

/-- Adjacency matrix `M(H)` whose `(u, v)` entry is the number of arcs from `u` to `v`. -/
def adjMatrix {V : Type} [DecidableEq V] (H : Multidigraph V) : Matrix V V ℕ :=
  Matrix.of fun u v => (Finset.univ.filter fun a : H.Arc => H.tail a = u ∧ H.head a = v).card

/-- A multidigraph `H` is `d`-regular if every vertex has in-degree `d` and out-degree `d`. -/
def IsRegular {V : Type} [DecidableEq V] (H : Multidigraph V) (d : ℕ) : Prop :=
  (∀ v : V, (Finset.univ.filter fun a : H.Arc => H.head a = v).card = d) ∧
  (∀ v : V, (Finset.univ.filter fun a : H.Arc => H.tail a = v).card = d)

/-- Arcs entering vertex `v`. -/
abbrev inArcs {V : Type} (H : Multidigraph V) (v : V) := { a : H.Arc // H.head a = v }

/-- Arcs leaving vertex `v`. -/
abbrev outArcs {V : Type} (H : Multidigraph V) (v : V) := { a : H.Arc // H.tail a = v }

/-- A transition system assigns at each vertex `v` a bijection from incoming arcs to outgoing arcs. -/
abbrev TransitionSystem {V : Type} (H : Multidigraph V) :=
  ∀ v : V, inArcs H v ≃ outArcs H v

/-- The permutation of arcs induced by a transition system: `a ↦ π_{head(a)}(a)`. -/
def arcPerm {V : Type} (H : Multidigraph V) (π : TransitionSystem H) : Equiv.Perm H.Arc where
  toFun a := (π (H.head a) ⟨a, rfl⟩).1
  invFun b := ((π (H.tail b)).symm ⟨b, rfl⟩).1
  left_inv a := by
    let b := π (H.head a) ⟨a, rfl⟩
    have hb : H.tail b.1 = H.head a := b.2
    change ((π (H.tail b.1)).symm ⟨b.1, rfl⟩).1 = a
    have hsub : ∀ {v : V} (hv : H.tail b.1 = v),
        ((π v).symm ⟨b.1, hv⟩).1 = ((π (H.tail b.1)).symm ⟨b.1, rfl⟩).1 := by
      intro v hv; subst hv; rfl
    rw [← hsub hb]
    have hb_eq : (⟨b.1, hb⟩ : outArcs H (H.head a)) = b := rfl
    rw [hb_eq]
    exact congrArg Subtype.val ((π (H.head a)).symm_apply_apply ⟨a, rfl⟩)
  right_inv b := by
    let a := (π (H.tail b)).symm ⟨b, rfl⟩
    have ha : H.head a.1 = H.tail b := a.2
    change (π (H.head a.1) ⟨a.1, rfl⟩).1 = b
    have hsub : ∀ {v : V} (hv : H.head a.1 = v),
        (π v ⟨a.1, hv⟩).1 = (π (H.head a.1) ⟨a.1, rfl⟩).1 := by
      intro v hv; subst hv; rfl
    rw [← hsub ha]
    have ha_eq : (⟨a.1, ha⟩ : inArcs H (H.tail b)) = a := rfl
    rw [ha_eq]
    exact congrArg Subtype.val ((π (H.tail b)).apply_symm_apply ⟨b, rfl⟩)

/-- Number of cycles (including fixed points / 1-cycles) of a permutation of a finite type. -/
noncomputable def permCycleCount {α : Type*} [Fintype α] (p : Equiv.Perm α) : ℕ := by
  classical
  exact Fintype.card (Quotient (MulAction.orbitRel (Subgroup.zpowers p) α))

/-- Number `cyc(π)` of closed trails in the transition system `π`. -/
noncomputable def cycCount {V : Type} (H : Multidigraph V) (π : TransitionSystem H) : ℕ :=
  permCycleCount (arcPerm H π)

/-- The circuit partition polynomial `j(H; x) = ∑_π x^{cyc(π)}`. -/
noncomputable def circuitPoly {V : Type} [Fintype V] (H : Multidigraph V) : Polynomial ℤ := by
  classical
  exact ∑ π : TransitionSystem H, Polynomial.X ^ (cycCount H π)

/-- Canonical multidigraph constructed from an adjacency matrix `M`. -/
def ofMatrix {V : Type} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ) : Multidigraph V where
  Arc := Σ u : V, Σ v : V, Fin (M u v)
  arcFintype :=
    letI : ∀ u : V, Fintype (Σ v : V, Fin (M u v)) := fun _ => Sigma.instFintype
    Sigma.instFintype
  tail a := a.1
  head a := a.2.1

/-- Evaluation `j(M) = j(H; -d)` for a `d`-regular matrix `M`. -/
noncomputable def circuitEval {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (d : ℕ) : ℤ :=
  (circuitPoly (ofMatrix M)).eval (-(d : ℤ))

/-- The all-ones matrix `J` on vertex set `V`. -/
def allOnesMatrix (V : Type) : Matrix V V ℕ :=
  Matrix.of fun _ _ => 1

/-- The complete digraph with one loop at each vertex, `K_n^∘`. -/
def completeLoopDigraph (n : ℕ) : Multidigraph (Fin n) :=
  ofMatrix (allOnesMatrix (Fin n))

/-- The generic `V × V` matrix `X = (x_{uv})` of independent indeterminates over `ℤ`. -/
noncomputable def genericMatrix (V : Type) [Fintype V] [DecidableEq V] :
    Matrix V V (MvPolynomial (V × V) ℤ) :=
  Matrix.of fun u v => MvPolynomial.X (u, v)

/-- Monomial exponent `x^M` corresponding to a matrix `M : Matrix V V ℕ`. -/
noncomputable def matMonomial {V : Type} [Fintype V] (M : Matrix V V ℕ) : (V × V) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => M p.1 p.2

/-- The coefficient `[x^M] det(X)^d`. -/
noncomputable def detPowCoeff {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (d : ℕ) : ℤ :=
  ((genericMatrix V).det ^ d).coeff (matMonomial M)

/-- Non-loop arcs entering vertex `w`. -/
abbrev nonLoopIn {V : Type} (H : Multidigraph V) (w : V) :=
  { a : H.Arc // H.head a = w ∧ H.tail a ≠ w }

/-- Non-loop arcs leaving vertex `w`. -/
abbrev nonLoopOut {V : Type} (H : Multidigraph V) (w : V) :=
  { a : H.Arc // H.tail a = w ∧ H.head a ≠ w }

/-- The multidigraph `H_σ` on `V \ {w}` obtained by removing `w` along a bijection `σ`
from non-loop arcs into `w` to non-loop arcs out of `w`. -/
def elimDigraph {V : Type} [DecidableEq V] (H : Multidigraph V) (w : V)
    (σ : nonLoopIn H w ≃ nonLoopOut H w) : Multidigraph { v : V // v ≠ w } where
  Arc := { a : H.Arc // H.tail a ≠ w ∧ H.head a ≠ w } ⊕ nonLoopIn H w
  tail
    | Sum.inl a => ⟨H.tail a.1, a.2.1⟩
    | Sum.inr e => ⟨H.tail e.1, e.2.2⟩
  head
    | Sum.inl a => ⟨H.head a.1, a.2.2⟩
    | Sum.inr e => ⟨H.head (σ e).1, (σ e).2.2⟩

/-- Restriction of a matrix `M` to `V \ {w}`. -/
def subMatrix {V : Type} (M : Matrix V V ℕ) (w : V) :
    Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ :=
  Matrix.of fun u v => M u.1 v.1

/-- Valid profile matrices `R` on `(V \ {w})²` with row sums `M_{uw}` and column sums `M_{wv}`. -/
def ValidProfile {V : Type} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ) (w : V)
    (R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ) : Prop :=
  (∀ u : { v : V // v ≠ w }, ∑ v, R u v = M u.1 w) ∧
  (∀ v : { v : V // v ≠ w }, ∑ u, R u v = M w v.1)

/-- The set of valid profiles for `(M, w)` is finite because each entry `R u v ≤ M u.1 w`. -/
noncomputable instance validProfileFintype {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (w : V) :
    Fintype { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R } := by
  classical
  let f : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R } →
      (u : { v : V // v ≠ w }) → { v : V // v ≠ w } → Fin (M u.1 w + 1) :=
    fun R u v => ⟨R.1 u v, Nat.lt_succ_of_le <| by
      calc R.1 u v ≤ ∑ v', R.1 u v' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        _ = M u.1 w := R.2.1 u⟩
  have hf : Function.Injective f := by
    intro R₁ R₂ h
    apply Subtype.ext
    ext u v
    exact congrArg Fin.val (congrFun (congrFun h u) v)
  have : Finite { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R } :=
    Finite.of_injective f hf
  exact Fintype.ofFinite _

/-- The profile multiplicity `count(R)` from vertex removal (E'). -/
def profileCount {V : Type} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ) (w : V)
    (R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ) : ℕ :=
  ((∏ u : { v : V // v ≠ w }, (M u.1 w).factorial) *
    (∏ v : { v : V // v ≠ w }, (M w v.1).factorial)) /
  (∏ u : { v : V // v ≠ w }, ∏ v : { v : V // v ≠ w }, (R u v).factorial)

/-- Families of transitions `π_T` at the vertices outside a subset `S ⊆ V`. -/
abbrev PartialTransition {V : Type} (H : Multidigraph V) (S : Finset V) :=
  ∀ w : { v : V // v ∉ S }, inArcs H w.1 ≃ outArcs H w.1

/-- One transition step inside `T = Sᶜ`: if `head(a) ∉ S`, advance along `π_T`; otherwise stay. -/
def partialStep {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) (a : H.Arc) : H.Arc :=
  if h : H.head a ∉ S then (πT ⟨H.head a, h⟩ ⟨a, rfl⟩).1 else a

/-- Injectivity of `partialStep` on arcs whose head lies outside `S`. -/
lemma partialStep_inj_on_outside {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) {a b : H.Arc} (ha : H.head a ∉ S) (hb : H.head b ∉ S)
    (hstep : partialStep H S πT a = partialStep H S πT b) : a = b := by
  simp [partialStep, ha, hb] at hstep
  have h1 : H.tail (πT ⟨H.head a, ha⟩ ⟨a, rfl⟩).1 = H.head a := (πT ⟨H.head a, ha⟩ ⟨a, rfl⟩).2
  have h2 : H.tail (πT ⟨H.head b, hb⟩ ⟨b, rfl⟩).1 = H.head b := (πT ⟨H.head b, hb⟩ ⟨b, rfl⟩).2
  have hhead : H.head a = H.head b := by rw [← h1, hstep, h2]
  have hsub : ∀ {v : V} (hv : H.head a = v) (hmem : v ∉ S),
      (πT ⟨v, hmem⟩ ⟨a, hv⟩).1 = (πT ⟨H.head a, ha⟩ ⟨a, rfl⟩).1 := by
    intro v hv hmem; subst hv; rfl
  have hval : (πT ⟨H.head b, hb⟩ ⟨a, hhead⟩).1 = (πT ⟨H.head b, hb⟩ ⟨b, rfl⟩).1 := by
    rw [hsub hhead hb, hstep]
  have hinj := (πT ⟨H.head b, hb⟩).injective (Subtype.ext hval)
  exact congrArg Subtype.val hinj

/-- Every exit from `S` to `T` eventually reaches an entry back into `S` under `partialStep`. -/
lemma exit_reaches_S {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) (e : H.Arc) (htail : H.tail e ∈ S) (_hhead : H.head e ∉ S) :
    ∃ k : ℕ, H.head ((partialStep H S πT)^[k] e) ∈ S := by
  by_contra hno
  push Not at hno
  have htail_succ : ∀ n, H.tail ((partialStep H S πT)^[n + 1] e) ∉ S := by
    intro n
    rw [Function.iterate_succ_apply']
    simp [partialStep, hno n]
    have h1 := (πT ⟨H.head ((partialStep H S πT)^[n] e), hno n⟩
      ⟨(partialStep H S πT)^[n] e, rfl⟩).2
    simpa [h1] using hno n
  have hinj : Function.Injective (fun n : ℕ => (partialStep H S πT)^[n] e) := by
    intro i j hij
    dsimp only at hij
    wlog hlt : i ≤ j generalizing i j
    · exact (this hij.symm (le_of_not_ge hlt)).symm
    induction i generalizing j with
    | zero =>
      cases j with
      | zero => rfl
      | succ k =>
        exfalso
        have h0 : e = (partialStep H S πT)^[k + 1] e := hij
        exact htail_succ k (h0 ▸ htail)
    | succ m ih =>
      cases j with
      | zero => omega
      | succ k =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hij
        have hprev := partialStep_inj_on_outside H S πT (hno m) (hno k) hij
        exact congrArg Nat.succ (ih hprev (Nat.le_of_succ_le_succ hlt))
  have : Finite ℕ := Finite.of_injective _ hinj
  exact not_finite ℕ

/-- The entry arc ending the walk through `T` from an exit arc `e`. -/
noncomputable def walkEnd {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S)
    (e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S }) :
    { a : H.Arc // H.head a ∈ S } := by
  classical
  let k := Nat.find (exit_reaches_S H S πT e.1 e.2.1 e.2.2)
  exact ⟨(partialStep H S πT)^[k] e.1, Nat.find_spec (exit_reaches_S H S πT e.1 e.2.1 e.2.2)⟩

/-- Arcs trapped in closed trails strictly inside `T = Sᶜ` under `π_T`. -/
abbrev closedTArcs {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) :=
  { a : H.Arc // ∀ n : ℕ, H.head ((partialStep H S πT)^[n] a) ∉ S }

/-- `partialStep` induces a permutation on `closedTArcs H S πT`. -/
noncomputable def closedTPerm {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) : Equiv.Perm (closedTArcs H S πT) := by
  classical
  let f : closedTArcs H S πT → closedTArcs H S πT := fun a =>
    ⟨partialStep H S πT a.1, fun n => by
      have := a.2 (n + 1)
      rwa [Function.iterate_succ_apply] at this⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact partialStep_inj_on_outside H S πT (a.2 0) (b.2 0) (congrArg Subtype.val hab)
  exact Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)

/-- Number `cyc_T(π_T)` of closed trails strictly inside `T = Sᶜ`. -/
noncomputable def cycInsideT {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) : ℕ := by
  classical
  exact permCycleCount (closedTPerm H S πT)

/-- The reduced multidigraph `H_{π_T}` on `S` obtained by contracting walks through `T = Sᶜ`. -/
noncomputable def splitDigraph {V : Type} [DecidableEq V] (H : Multidigraph V) (S : Finset V)
    (πT : PartialTransition H S) : Multidigraph { v : V // v ∈ S } where
  Arc := { a : H.Arc // H.tail a ∈ S ∧ H.head a ∈ S } ⊕
    { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S }
  tail
    | Sum.inl a => ⟨H.tail a.1, a.2.1⟩
    | Sum.inr e => ⟨H.tail e.1, e.2.1⟩
  head
    | Sum.inl a => ⟨H.head a.1, a.2.2⟩
    | Sum.inr e => ⟨H.head (walkEnd H S πT e).1, (walkEnd H S πT e).2⟩

/-- An automorphism of a multidigraph `H`: a vertex permutation and an arc permutation
preserving tails and heads. -/
structure MultidigraphAut {V : Type} (H : Multidigraph V) where
  vPerm : Equiv.Perm V
  aPerm : Equiv.Perm H.Arc
  map_tail : ∀ a : H.Arc, H.tail (aPerm a) = vPerm (H.tail a)
  map_head : ∀ a : H.Arc, H.head (aPerm a) = vPerm (H.head a)

@[ext]
theorem MultidigraphAut.ext {V : Type} {H : Multidigraph V}
    {g₁ g₂ : MultidigraphAut H} (hv : g₁.vPerm = g₂.vPerm) (ha : g₁.aPerm = g₂.aPerm) :
    g₁ = g₂ := by
  cases g₁; cases g₂; cases hv; cases ha; rfl

instance {V : Type} (H : Multidigraph V) : Group (MultidigraphAut H) where
  mul g₁ g₂ :=
    { vPerm := g₁.vPerm * g₂.vPerm
      aPerm := g₁.aPerm * g₂.aPerm
      map_tail := fun a => by simp [g₁.map_tail, g₂.map_tail]
      map_head := fun a => by simp [g₁.map_head, g₂.map_head] }
  one :=
    { vPerm := 1
      aPerm := 1
      map_tail := fun _ => rfl
      map_head := fun _ => rfl }
  inv g :=
    { vPerm := g.vPerm⁻¹
      aPerm := g.aPerm⁻¹
      map_tail := fun a => by
        apply g.vPerm.injective
        rw [← g.map_tail]
        change H.tail (g.aPerm (g.aPerm.symm a)) = g.vPerm (g.vPerm.symm (H.tail a))
        rw [g.aPerm.apply_symm_apply, g.vPerm.apply_symm_apply]
      map_head := fun a => by
        apply g.vPerm.injective
        rw [← g.map_head]
        change H.head (g.aPerm (g.aPerm.symm a)) = g.vPerm (g.vPerm.symm (H.head a))
        rw [g.aPerm.apply_symm_apply, g.vPerm.apply_symm_apply] }
  mul_assoc _ _ _ := by apply MultidigraphAut.ext <;> exact mul_assoc _ _ _
  one_mul _ := by apply MultidigraphAut.ext <;> exact one_mul _
  mul_one _ := by apply MultidigraphAut.ext <;> exact mul_one _
  inv_mul_cancel _ := by apply MultidigraphAut.ext <;> exact inv_mul_cancel _

/-- Action of a multidigraph automorphism `g` preserving `T = Sᶜ` on `PartialTransition H S`. -/
def autActPartial {V : Type} [DecidableEq V] {H : Multidigraph V} {S : Finset V}
    (g : MultidigraphAut H) (hS : ∀ v, v ∈ S ↔ g.vPerm v ∈ S)
    (πT : PartialTransition H S) : PartialTransition H S :=
  fun w =>
    let w' : { v : V // v ∉ S } := ⟨g.vPerm.symm w.1, by
      intro hmem
      have := (hS (g.vPerm.symm w.1)).mp hmem
      rw [g.vPerm.apply_symm_apply] at this
      exact w.2 this⟩
    { toFun := fun e =>
        let e' : inArcs H w'.1 := ⟨g.aPerm.symm e.1, by
          apply g.vPerm.injective
          rw [← g.map_head, g.aPerm.apply_symm_apply, e.2, g.vPerm.apply_symm_apply]⟩
        ⟨g.aPerm (πT w' e').1, by
          rw [g.map_tail, (πT w' e').2, g.vPerm.apply_symm_apply]⟩
      invFun := fun f =>
        let f' : outArcs H w'.1 := ⟨g.aPerm.symm f.1, by
          apply g.vPerm.injective
          rw [← g.map_tail, g.aPerm.apply_symm_apply, f.2, g.vPerm.apply_symm_apply]⟩
        ⟨g.aPerm ((πT w').symm f').1, by
          rw [g.map_head, ((πT w').symm f').2, g.vPerm.apply_symm_apply]⟩
      left_inv := fun e => by
        apply Subtype.ext
        simp
      right_inv := fun f => by
        apply Subtype.ext
        simp }

end AlonTarsi

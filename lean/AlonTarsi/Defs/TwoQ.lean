/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import AlonTarsi.Defs.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Definitions for the Prime `q = n / 2` Case

This file defines the Sylow `q`-subgroup `P ≅ F_q^6` of `S_{2q}^3`, elementary abelian
subgroups and their ranks, fixed-square sums `S(H)`, ordered-subset signs `θ(I)`, complete
maps and `τ_q, t_q`, rank-one generators `ℓ_0, ℓ_B, ℓ_C`, patterns, layers, centered layers
`Ω(E)`, mixed-orbit counts `N_{B,m}, N_{C,m}`, and the trace matrices
`A_X, B_X, E, F, U, S` built from minors of the generic circulant matrix `Γ(x)`.
-/

namespace AlonTarsi

/-- Bijection `{0, 1} × ZMod q ≃ Fin (2 * q)` ordering `ZMod q` by `0 < 1 < ... < q - 1`. -/
def blockEquiv (q : ℕ) [NeZero q] : Fin 2 × ZMod q ≃ Fin (2 * q) where
  toFun p := ⟨p.1.val * q + p.2.val, by
    have hq : 0 < q := NeZero.pos q
    have h1 : p.1.val = 0 ∨ p.1.val = 1 := by omega
    have h2 : p.2.val < q := p.2.val_lt
    rcases h1 with h1 | h1 <;> simp [h1] <;> omega⟩
  invFun k := (⟨k.val / q, by
    have hq : 0 < q := NeZero.pos q
    exact Nat.div_lt_of_lt_mul (by linarith [k.isLt])⟩, (k.val % q : ℕ))
  left_inv p := by
    have hq : 0 < q := NeZero.pos q
    have h2 : p.2.val < q := p.2.val_lt
    ext
    · change (p.1.val * q + p.2.val) / q = p.1.val
      rw [Nat.mul_comm, Nat.mul_add_div hq, Nat.div_eq_of_lt h2, add_zero]
    · apply ZMod.val_injective q
      change (((p.1.val * q + p.2.val) % q : ℕ) : ZMod q).val = p.2.val
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h2, ZMod.val_natCast_of_lt h2]
  right_inv k := by
    have hq : 0 < q := NeZero.pos q
    apply Fin.ext
    change k.val / q * q + ((k.val % q : ℕ) : ZMod q).val = k.val
    rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hq), Nat.mul_comm, Nat.div_add_mod]

/-- Translation within the two blocks `{0, 1} × ZMod q` by `(u₀, u₁)`. -/
def blockTransPerm (q : ℕ) [NeZero q] (u : Fin 2 → ZMod q) : Equiv.Perm (Fin (2 * q)) :=
  (blockEquiv q).symm.trans <|
    ({ toFun := fun p => (p.1, p.2 + u p.1)
       invFun := fun p => (p.1, p.2 - u p.1)
       left_inv := fun p => by ext <;> simp
       right_inv := fun p => by ext <;> simp } : Equiv.Perm (Fin 2 × ZMod q)).trans
    (blockEquiv q)

/-- Parameter space `(u₀, u₁; v₀, v₁; w₀, w₁) ∈ F_q^6` for the Sylow `q`-subgroup `P`. -/
abbrev SylowVec (q : ℕ) := (Fin 2 → ZMod q) × (Fin 2 → ZMod q) × (Fin 2 → ZMod q)

/-- Group homomorphism `Multiplicative (F_q^6) →* Isotopy (2 * q)` defining `P`. -/
def sylowHom (q : ℕ) [NeZero q] : Multiplicative (SylowVec q) →* Isotopy (2 * q) where
  toFun g :=
    let v := Multiplicative.toAdd g
    (blockTransPerm q v.1, blockTransPerm q v.2.1, blockTransPerm q v.2.2)
  map_one' := by
    have h0 : blockTransPerm q (0 : Fin 2 → ZMod q) = 1 := by
      ext k
      simp [blockTransPerm]
    change (blockTransPerm q 0, blockTransPerm q 0, blockTransPerm q 0) = (1, 1, 1)
    simp [h0]
  map_mul' g₁ g₂ := by
    have hmul : ∀ a b : Fin 2 → ZMod q,
        blockTransPerm q (a + b) = blockTransPerm q a * blockTransPerm q b := by
      intro a b
      ext k
      simp only [blockTransPerm, Equiv.Perm.mul_apply, Equiv.trans_apply,
        Equiv.coe_fn_mk, Equiv.symm_apply_apply, Pi.add_apply]
      have hadd :
          ((blockEquiv q).symm k).2 + (a ((blockEquiv q).symm k).1 + b ((blockEquiv q).symm k).1) =
          ((blockEquiv q).symm k).2 + b ((blockEquiv q).symm k).1 + a ((blockEquiv q).symm k).1 := by
        ring
      rw [hadd]
    change (blockTransPerm q ((Multiplicative.toAdd g₁).1 + (Multiplicative.toAdd g₂).1),
            blockTransPerm q ((Multiplicative.toAdd g₁).2.1 + (Multiplicative.toAdd g₂).2.1),
            blockTransPerm q ((Multiplicative.toAdd g₁).2.2 + (Multiplicative.toAdd g₂).2.2)) = _
    simp [hmul, Prod.mk_mul_mk]

/-- The Sylow `q`-subgroup `P ≅ F_q^6` of `Isotopy (2 * q)`. -/
def sylowP (q : ℕ) [NeZero q] : Subgroup (Isotopy (2 * q)) :=
  (sylowHom q).range

/-- Fixed-point set `Fix(H)` of a subgroup `H` acting on `X`. -/
def fixSet {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) : Set X :=
  { x : X | ∀ g ∈ H, g • x = x }

/-- Signed fixed-point sum `S_X(H) = ∑_{x ∈ Fix(H)} ε(x)`. -/
noncomputable def signedFixSum {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (ε : X → ℤˣ) (H : Subgroup G) : ℤ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x : X => x ∈ fixSet H), (ε x : ℤ)

/-- Signed count `S(H)` of Latin squares of order `2q` fixed by `H ≤ P`. -/
noncomputable def S_twoq (q : ℕ) [NeZero q] (H : Subgroup (sylowP q)) : ℤ :=
  signedFixSum (squareSign (n := 2 * q)) (H.map (sylowP q).subtype)

/-- A subgroup `H` is an elementary abelian `q`-group if it is abelian and of exponent dividing `q`. -/
def IsElemAbelian {G : Type*} [Group G] (q : ℕ) (H : Subgroup G) : Prop :=
  (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧ (∀ a ∈ H, a ^ q = 1)

/-- Rank `r(H) = log_q |H|` of a finite elementary abelian `q`-group `H`. -/
noncomputable def elemRank {G : Type*} [Group G] (q : ℕ) (H : Subgroup G) : ℕ :=
  Nat.log q (Nat.card H)

/-- Finset of nontrivial elementary abelian `q`-subgroups of a finite group `G`. -/
noncomputable def elemAbelianNontrivial {G : Type*} [Group G] [Fintype G] (q : ℕ) :
    Finset (Subgroup G) := by
  classical
  have : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  exact Finset.univ.filter fun H : Subgroup G => H ≠ ⊥ ∧ IsElemAbelian q H

/-- Finset of subgroups of `P = sylowP q` of rank `r`. -/
noncomputable def sylowSubgroupsOfRank (q r : ℕ) [NeZero q] :
    Finset (Subgroup (sylowP q)) := by
  classical
  have : Finite (Subgroup (sylowP q)) :=
    Finite.of_injective (fun H : Subgroup (sylowP q) => (H : Set (sylowP q))) SetLike.coe_injective
  letI : Fintype (Subgroup (sylowP q)) := Fintype.ofFinite _
  exact Finset.univ.filter fun H : Subgroup (sylowP q) => elemRank q H = r

/-- Standard linear order `0 < 1 < ... < q - 1` on `ZMod q`. -/
@[instance_reducible]
def zmodLinearOrder (q : ℕ) [NeZero q] : LinearOrder (ZMod q) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective q)

/-- Sign of a bijection `f : A ≃ B` between equal-sized subsets of `ZMod q`,
using the increasing order `0 < 1 < ... < q - 1` on both subsets. -/
noncomputable def orderedSign {q : ℕ} [NeZero q] {A B : Finset (ZMod q)}
    (hcard : A.card = B.card) (f : A ≃ B) : ℤˣ := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  let eA : Fin A.card ≃o A := A.orderIsoOfFin rfl
  let eB : Fin A.card ≃o B := B.orderIsoOfFin hcard.symm
  exact Equiv.Perm.sign (eA.toEquiv.trans (f.trans eB.toEquiv.symm))

/-- Shuffle sign `θ(I) = (-1)^(ι(I) - C(|I|, 2))` of listing `I` before `Iᶜ` in `ZMod q`. -/
def thetaSign {q : ℕ} [NeZero q] (I : Finset (ZMod q)) : ℤˣ :=
  (-1 : ℤˣ) ^ ((∑ x ∈ I, x.val) - I.card.choose 2)

/-- A complete map (orthomorphism) of `ZMod q`: both `h` and `h - id` are bijections. -/
def IsCompleteMap {q : ℕ} (h : Equiv.Perm (ZMod q)) : Prop :=
  Function.Bijective (fun x : ZMod q => h x - x)

/-- Signed sum `τ_q = ∑_h sgn(h) sgn(h - id)` over all complete maps of `ZMod q`. -/
noncomputable def tauQ (q : ℕ) [NeZero q] : ℤ := by
  classical
  exact ∑ h : { h : Equiv.Perm (ZMod q) // IsCompleteMap h },
    ((Equiv.Perm.sign h.1 : ℤ) *
      (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ))

/-- Normalized signed sum `t_q` over complete maps with `h(0) = 0`. -/
noncomputable def tQ (q : ℕ) [NeZero q] : ℤ := by
  classical
  exact ∑ h ∈ Finset.univ.filter
      (fun h : { h : Equiv.Perm (ZMod q) // IsCompleteMap h } => h.1 0 = 0),
    ((Equiv.Perm.sign h.1 : ℤ) *
      (Equiv.Perm.sign (Equiv.ofBijective (fun x => h.1 x - x) h.2) : ℤ))

/-- Element of `P` specified by row, column, and symbol block shifts. -/
def sylowElem (q : ℕ) [NeZero q] (u₀ u₁ v₀ v₁ w₀ w₁ : ZMod q) : sylowP q :=
  ⟨sylowHom q (Multiplicative.ofAdd
      (fun a => if a = 0 then u₀ else u₁,
       fun b => if b = 0 then v₀ else v₁,
       fun c => if c = 0 then w₀ else w₁)),
    ⟨_, rfl⟩⟩

/-- Rank-one representative `ℓ_0 = (1,1; 1,1; 0,0)`. -/
def ell0 (q : ℕ) [NeZero q] : sylowP q := sylowElem q 1 1 1 1 0 0

/-- Rank-one representative `ℓ_B = (1,1; 1,1; 0,1)`. -/
def ellB (q : ℕ) [NeZero q] : sylowP q := sylowElem q 1 1 1 1 0 1

/-- Rank-one representative `ℓ_C = (1,1; 1,1; 1,1)`. -/
def ellC (q : ℕ) [NeZero q] : sylowP q := sylowElem q 1 1 1 1 1 1

/-- Stratum `m` of a Latin square `L` of order `2q`: number of offsets `d ∈ ZMod q`
for which `L((0,0), (0,d))` lies in the first symbol block `Σ_0`. -/
def stratumOf (q : ℕ) [NeZero q] (L : LatinSquare (2 * q)) : ℕ :=
  (Finset.univ.filter fun d : ZMod q =>
    ((blockEquiv q).symm (L.entry (blockEquiv q (0, 0)) (blockEquiv q (0, d)))).1 = 0).card

/-- A pattern `O = (O_{00}, O_{01}; O_{10}, O_{11})` of size `m` in `ZMod q`. -/
structure Pattern (q m : ℕ) [NeZero q] where
  O : Fin 2 → Fin 2 → Finset (ZMod q)
  card_00 : (O 0 0).card = m
  card_11 : (O 1 1).card = m
  card_01 : (O 0 1).card = q - m
  card_10 : (O 1 0).card = q - m

@[ext]
theorem Pattern.ext {q m : ℕ} [NeZero q] {P₁ P₂ : Pattern q m} (h : P₁.O = P₂.O) : P₁ = P₂ := by
  cases P₁; cases P₂; cases h; rfl

noncomputable instance {q m : ℕ} [NeZero q] : Fintype (Pattern q m) := by
  classical
  let e : Pattern q m ≃
      { O : Fin 2 → Fin 2 → Finset (ZMod q) //
        (O 0 0).card = m ∧ (O 1 1).card = m ∧ (O 0 1).card = q - m ∧ (O 1 0).card = q - m } :=
    { toFun := fun P => ⟨P.O, P.card_00, P.card_11, P.card_01, P.card_10⟩
      invFun := fun f => ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Complement `O^c` of a pattern of size `m`, forming a pattern of size `q - m`. -/
def Pattern.compl {q m : ℕ} [NeZero q] (hm : m ≤ q) (P : Pattern q m) : Pattern q (q - m) where
  O a b := (P.O a b)ᶜ
  card_00 := by simp [Finset.card_compl, ZMod.card, P.card_00]
  card_11 := by simp [Finset.card_compl, ZMod.card, P.card_11]
  card_01 := by simp [Finset.card_compl, ZMod.card, P.card_01, Nat.sub_sub_self hm]
  card_10 := by simp [Finset.card_compl, ZMod.card, P.card_10, Nat.sub_sub_self hm]

/-- A pattern `O` is centered if every `O_{ab}` has element sum `0` in `ZMod q`. -/
def Pattern.IsCentered {q m : ℕ} [NeZero q] (P : Pattern q m) : Prop :=
  ∀ a b : Fin 2, ∑ d ∈ P.O a b, d = 0

/-- Finset of all centered patterns of size `m` in `ZMod q`. -/
noncomputable def centeredPatterns (q m : ℕ) [NeZero q] : Finset (Pattern q m) := by
  classical
  exact Finset.univ.filter Pattern.IsCentered

/-- A moving layer `h = (h_{ab})` on a pattern `E`, satisfying (L1) and (L2). -/
structure Layer {q m : ℕ} [NeZero q] (E : Pattern q m) where
  h : ∀ a b : Fin 2, E.O a b → ZMod q
  L1 : ∀ a : Fin 2,
    Function.Bijective (fun x : E.O a 0 ⊕ E.O a 1 => Sum.elim (h a 0) (h a 1) x)
  L2 : ∀ b : Fin 2,
    Function.Bijective (fun x : E.O 0 b ⊕ E.O 1 b =>
      Sum.elim (fun d => h 0 b d - d.1) (fun d => h 1 b d - d.1) x)

@[ext]
theorem Layer.ext {q m : ℕ} [NeZero q] {E : Pattern q m} {h₁ h₂ : Layer E}
    (heq : h₁.h = h₂.h) : h₁ = h₂ := by
  cases h₁; cases h₂; cases heq; rfl

noncomputable instance {q m : ℕ} [NeZero q] (E : Pattern q m) : Fintype (Layer E) := by
  classical
  let e : Layer E ≃
      { h : ∀ a b : Fin 2, E.O a b → ZMod q //
        (∀ a, Function.Bijective (fun x : E.O a 0 ⊕ E.O a 1 => Sum.elim (h a 0) (h a 1) x)) ∧
        (∀ b, Function.Bijective (fun x : E.O 0 b ⊕ E.O 1 b =>
          Sum.elim (fun d => h 0 b d - d.1) (fun d => h 1 b d - d.1) x)) } :=
    { toFun := fun L => ⟨L.h, L.L1, L.L2⟩
      invFun := fun f => ⟨f.1, f.2.1, f.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Sign of a bijection `f : A ⊕ B ≃ ZMod q` relative to `A` before `B` and `0 < ... < q - 1`. -/
noncomputable def sumBijectionSign {q : ℕ} [NeZero q] {A B : Finset (ZMod q)}
    (f : (A ⊕ B) ≃ ZMod q) : ℤˣ := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  letI : LinearOrder A := Subtype.instLinearOrder _
  letI : LinearOrder B := Subtype.instLinearOrder _
  have hcard : Fintype.card (A ⊕ₗ B) = q := by
    have h1 : Fintype.card (A ⊕ₗ B) = Fintype.card (A ⊕ B) :=
      Fintype.card_congr ofLex
    rw [h1]
    simpa [ZMod.card] using Fintype.card_congr f
  let eDom : Fin q ≃o (A ⊕ₗ B) := Fintype.orderIsoFinOfCardEq (α := A ⊕ₗ B) hcard
  let eCod : Fin q ≃o ZMod q := Fintype.orderIsoFinOfCardEq (α := ZMod q) (ZMod.card q)
  exact Equiv.Perm.sign
    (eDom.toEquiv.trans (ofLex.trans (f.trans eCod.toEquiv.symm)))

/-- Sign `ω(h)` of a layer `h`: product of its two (L1) signs and two (L2) signs. -/
noncomputable def layerSign {q m : ℕ} [NeZero q] {E : Pattern q m} (L : Layer E) : ℤˣ :=
  (∏ a : Fin 2, sumBijectionSign (Equiv.ofBijective _ (L.L1 a))) *
  (∏ b : Fin 2, sumBijectionSign (Equiv.ofBijective _ (L.L2 b)))

/-- A layer `h` is centered if all four phase sums `Φ_{ab}(h) = ∑_{d ∈ E_{ab}} h_{ab}(d)` vanish. -/
def Layer.IsCentered {q m : ℕ} [NeZero q] {E : Pattern q m} (L : Layer E) : Prop :=
  ∀ a b : Fin 2, ∑ d : E.O a b, L.h a b d = 0

/-- Signed count `Ω(E) = ∑_{h centered} ω(h)` of centered layers on `E`. -/
noncomputable def OmegaSum {q m : ℕ} [NeZero q] (E : Pattern q m) : ℤ := by
  classical
  exact ∑ L ∈ Finset.univ.filter (fun L : Layer E => L.IsCentered), (layerSign L : ℤ)

/-- Subtype of Latin squares of order `2q` fixed by `ℓ` in stratum `m`. -/
abbrev StratumFix (q : ℕ) [NeZero q] (ℓ : sylowP q) (m : ℕ) :=
  { L : LatinSquare (2 * q) // L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) ∧
      stratumOf q L = m }

/-- `sylowP q` preserves `StratumFix q ℓ m` (because `P` is abelian and block translations
preserve membership in `Σ_0` and permute offsets). -/
noncomputable def mixedOrbitCount (q : ℕ) [NeZero q] (ℓ : sylowP q) (m : ℕ) : ℤ := by
  classical
  let R : Setoid (StratumFix q ℓ m) :=
    { r := fun L₁ L₂ => ∃ g : sylowP q, g.1 • L₁.1 = L₂.1
      iseqv :=
        ⟨fun L => ⟨1, one_smul _ _⟩,
         fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg]; simp⟩,
         fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ => ⟨g₂ * g₁, by rw [← h₂, ← h₁]; exact mul_smul _ _ _⟩⟩ }
  exact ∑ o : Quotient R, (squareSign (Quotient.out o).1 : ℤ)

/-- Signed sum of squares fixed by `ℓ` in the homogeneous strata `m = 0` and `m = q`. -/
noncomputable def homogStrataSum (q : ℕ) [NeZero q] (ℓ : sylowP q) : ℤ := by
  classical
  exact ∑ L ∈ (Finset.univ : Finset (LatinSquare (2 * q))).filter
      (fun L => L ∈ fixSet ((Subgroup.zpowers ℓ).map (sylowP q).subtype) ∧
        (stratumOf q L = 0 ∨ stratumOf q L = q)),
    (squareSign L : ℤ)

/-- `N_{B, m}`: signed number of `P`-orbits of mixed stratum `m` fixed by `ℓ_B`. -/
noncomputable def mixedOrbitCountB (q m : ℕ) [NeZero q] : ℤ :=
  mixedOrbitCount q (ellB q) m

/-- `N_{C, m}`: signed number of `P`-orbits of mixed stratum `m` fixed by `ℓ_C`. -/
noncomputable def mixedOrbitCountC (q m : ℕ) [NeZero q] : ℤ :=
  mixedOrbitCount q (ellC q) m

/-- `N_B = ∑_{0 < m < q} N_{B, m}`. -/
noncomputable def NB (q : ℕ) [NeZero q] : ℤ :=
  ∑ m ∈ Finset.Ioo 0 q, mixedOrbitCountB q m

/-- `N_C = ∑_{0 < m < q} N_{C, m}`. -/
noncomputable def NC (q : ℕ) [NeZero q] : ℤ :=
  ∑ m ∈ Finset.Ioo 0 q, mixedOrbitCountC q m

/-- `Z_Y(I, J)`: sum of `sgn(h) sgn(h - id)` over bijections `h : Y ≃ I` such that
`d ↦ h(d) - d` is a bijection `Y → J`. -/
noncomputable def ZY {q : ℕ} [NeZero q] (Y I J : Finset (ZMod q)) : ℤ := by
  classical
  exact if hYI : Y.card = I.card then
    if hYJ : Y.card = J.card then
      ∑ h : Y ≃ I,
        if hmem : ∀ d : Y, (h d).1 - d.1 ∈ J then
          if hbij : Function.Bijective (fun d : Y => (⟨(h d).1 - d.1, hmem d⟩ : J)) then
            (orderedSign hYI h : ℤ) *
              (orderedSign hYJ (Equiv.ofBijective _ hbij) : ℤ)
          else 0
        else 0
    else 0
  else 0

/-- The generic `q × q` circulant matrix `Γ(x) = ∑_d x_d T_d` with `(Γ(x))_{ij} = x_{i - j}`. -/
noncomputable def genericCirculant (q : ℕ) [NeZero q] :
    Matrix (ZMod q) (ZMod q) (MvPolynomial (ZMod q) ℤ) :=
  Matrix.of fun i j => MvPolynomial.X (i - j)

/-- Submatrix `Γ(x)[I, J]` for equal-sized subsets `I, J ⊆ ZMod q`, ordered by `0 < ... < q - 1`. -/
noncomputable def circulantSubmatrix {q : ℕ} [NeZero q] {I J : Finset (ZMod q)}
    (hIJ : I.card = J.card) :
    Matrix (Fin I.card) (Fin I.card) (MvPolynomial (ZMod q) ℤ) := by
  letI : LinearOrder (ZMod q) := zmodLinearOrder q
  let eI : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let eJ : Fin I.card ≃o J := J.orderIsoOfFin hIJ.symm
  exact Matrix.of fun r c => genericCirculant q (eI r).1 (eJ c).1

/-- Indicator monomial `x^Y = ∏_{d ∈ Y} x_d`. -/
noncomputable def subsetMonomial {q : ℕ} [NeZero q] (Y : Finset (ZMod q)) : ZMod q →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm fun d => if d ∈ Y then 1 else 0

/-- Set `C_m` of centered `m`-subsets of `ZMod q`. -/
def centeredSubsets (q m : ℕ) [NeZero q] : Finset (Finset (ZMod q)) :=
  Finset.univ.filter fun X : Finset (ZMod q) => X.card = m ∧ ∑ d ∈ X, d = 0

/-- Index type for `C_m`. -/
abbrev CenteredIdx (q m : ℕ) [NeZero q] := { X : Finset (ZMod q) // X ∈ centeredSubsets q m }

/-- For odd `q`, the sum of all elements of `ZMod q` is `0`. -/
lemma sum_univ_zmod_odd {q : ℕ} [NeZero q] (hodd : Odd q) :
    (∑ x : ZMod q, x) = 0 := by
  have h2 : (2 : ZMod q) * (∑ x : ZMod q, x) = 0 := by
    have hneg : (∑ x : ZMod q, -x) = ∑ x : ZMod q, x :=
      Equiv.sum_comp (Equiv.neg (ZMod q)) (fun x => x)
    rw [Finset.sum_neg_distrib] at hneg
    calc (2 : ZMod q) * (∑ x : ZMod q, x)
        = (∑ x : ZMod q, x) + (∑ x : ZMod q, x) := two_mul _
      _ = (∑ x : ZMod q, x) + -(∑ x : ZMod q, x) := congrArg ((∑ x : ZMod q, x) + ·) hneg.symm
      _ = 0 := add_neg_cancel _
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr hcop
  exact hunit.mul_right_eq_zero.mp h2

/-- Complement of a centered `(q - m)`-subset gives a centered `m`-subset when `q` is odd. -/
def complCentered {q m : ℕ} [NeZero q] (hodd : Odd q) (hm : m ≤ q)
    (X : Finset (ZMod q)) (hcard : X.card = q - m) (hsum : ∑ d ∈ X, d = 0) :
    CenteredIdx q m :=
  ⟨Xᶜ, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    by simp [Finset.card_compl, ZMod.card, hcard, Nat.sub_sub_self hm],
    by
      have htot := Finset.sum_add_sum_compl X (fun d : ZMod q => d)
      rw [hsum, zero_add, sum_univ_zmod_odd hodd] at htot
      exact htot⟩⟩

/-- Negation `-X` of a centered `m`-subset of `ZMod q`. -/
def negCentered {q m : ℕ} [NeZero q] (X : CenteredIdx q m) : CenteredIdx q m :=
  ⟨X.1.image (fun d => -d), by
    have hX := Finset.mem_filter.mp X.2
    dsimp only [centeredSubsets]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ neg_injective, hX.2.1]
    · rw [Finset.sum_image (fun _ _ _ _ h => neg_injective h), Finset.sum_neg_distrib, hX.2.2,
        neg_zero]⟩

/-- Matrix `A_X(I, J) = Z_X(I, J)` indexed by `C_m`. -/
noncomputable def matA (q m : ℕ) [NeZero q] (X : CenteredIdx q m) :
    Matrix (CenteredIdx q m) (CenteredIdx q m) ℤ :=
  Matrix.of fun I J => ZY X.1 I.1 J.1

/-- Matrix `B_X(I, J) = θ(I) θ(J) Z_{Xᶜ}(Iᶜ, Jᶜ)` indexed by `C_m`. -/
noncomputable def matB (q m : ℕ) [NeZero q] (X : CenteredIdx q m) :
    Matrix (CenteredIdx q m) (CenteredIdx q m) ℤ :=
  Matrix.of fun I J => (thetaSign I.1 : ℤ) * (thetaSign J.1 : ℤ) * ZY X.1ᶜ I.1ᶜ J.1ᶜ

/-- Sum matrix `E = ∑_{X ∈ C_m} A_X`. -/
noncomputable def matE (q m : ℕ) [NeZero q] : Matrix (CenteredIdx q m) (CenteredIdx q m) ℤ :=
  ∑ X : CenteredIdx q m, matA q m X

/-- Sum matrix `F = ∑_{X ∈ C_m} B_X`. -/
noncomputable def matF (q m : ℕ) [NeZero q] : Matrix (CenteredIdx q m) (CenteredIdx q m) ℤ :=
  ∑ X : CenteredIdx q m, matB q m X

/-- Kronecker product `A ⊗ B` of square matrices. -/
def kronMat {α β R : Type*} [Mul R] (A : Matrix α α R) (B : Matrix β β R) :
    Matrix (α × β) (α × β) R :=
  Matrix.of fun p r => A p.1 r.1 * B p.2 r.2

/-- Tensor-sum matrix `U = ∑_{X ∈ C_m} A_X ⊗ B_X` indexed by `C_m × C_m`. -/
noncomputable def matU (q m : ℕ) [NeZero q] :
    Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) ℤ :=
  ∑ X : CenteredIdx q m, kronMat (matA q m X) (matB q m X)

/-- Swap matrix `S` on `C_m × C_m`: `S((I, J), (I', J')) = [I = J' ∧ J = I']`. -/
def matS (q m : ℕ) [NeZero q] :
    Matrix (CenteredIdx q m × CenteredIdx q m) (CenteredIdx q m × CenteredIdx q m) ℤ :=
  Matrix.of fun p r => if p.1 = r.2 ∧ p.2 = r.1 then 1 else 0

/-- Transpose of a subgroup `H ≤ P` (exchanging row and column coordinates). -/
def transposeSubgroup {q : ℕ} [NeZero q] (H : Subgroup (sylowP q)) : Subgroup (sylowP q) :=
  let swap : Isotopy (2 * q) ≃* Isotopy (2 * q) :=
    { toFun := fun σ => (σ.2.1, σ.1, σ.2.2)
      invFun := fun σ => (σ.2.1, σ.1, σ.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  H.map
    { toFun := fun g => ⟨swap g.1, by
        rcases g.2 with ⟨v, hv⟩
        refine ⟨Multiplicative.ofAdd
          ((Multiplicative.toAdd v).2.1, (Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2.2),
          ?_⟩
        rw [← hv]; rfl⟩
      map_one' := by ext <;> rfl
      map_mul' := fun _ _ => by ext <;> rfl }

/-- Helper: given a `1`-variable or `2`-variable block rescaling or interchange on `{0, 1} × ZMod q`. -/
def blockSwapPerm (q : ℕ) [NeZero q] : Equiv.Perm (Fin (2 * q)) :=
  (blockEquiv q).symm.trans <|
    ({ toFun := fun p => (1 - p.1, p.2)
       invFun := fun p => (1 - p.1, p.2)
       left_inv := fun p => by
         rcases p with ⟨⟨i, hi⟩, x⟩
         have h : i = 0 ∨ i = 1 := by omega
         rcases h with rfl | rfl <;> rfl
       right_inv := fun p => by
         rcases p with ⟨⟨i, hi⟩, x⟩
         have h : i = 0 ∨ i = 1 := by omega
         rcases h with rfl | rfl <;> rfl } : Equiv.Perm (Fin 2 × ZMod q)).trans
    (blockEquiv q)

/-- Rescaling of a single block `a₀ ∈ Fin 2` by `λ : (ZMod q)ˣ`. -/
def blockScalePerm (q : ℕ) [NeZero q] (a₀ : Fin 2) (lam : (ZMod q)ˣ) : Equiv.Perm (Fin (2 * q)) :=
  (blockEquiv q).symm.trans <|
    ({ toFun := fun p => (p.1, if p.1 = a₀ then lam.1 * p.2 else p.2)
       invFun := fun p => (p.1, if p.1 = a₀ then (lam⁻¹).1 * p.2 else p.2)
       left_inv := fun p => by
         ext
         · rfl
         · dsimp; split_ifs <;> simp [← mul_assoc]
       right_inv := fun p => by
         ext
         · rfl
         · dsimp; split_ifs <;> simp [← mul_assoc] } : Equiv.Perm (Fin 2 × ZMod q)).trans
    (blockEquiv q)

end AlonTarsi

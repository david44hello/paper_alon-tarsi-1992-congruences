module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Defs.Circuit
public import AlonTarsi.Proofs.LatinBasics
public import AlonTarsi.Proofs.Quadratic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fintype.Perm

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Section 3: Circuit Partition Polynomial and Vertex Removal

This file proves all results of Section 3 (plus the general permutation cycle-count and
subset-contraction machinery reused in Section 5) directly from Lean's standard axioms:
- `permCycleCount_equivCongr`, `neg_one_pow_card_add_permCycleCount`, `permCycleCount_firstReturn`.
- `circuitPoly_eq_of_equiv`, `circuitPoly_eq_ofMatrix`, `circuitPoly_eval_eq_circuitEval`.
- `lem_3_1_quad_fact_proved`: `j(H; -d) = (-1)^(Nd) (∏ M_{uv}!) [x^M] det(X)^d`.
- `lem_3_2_quad_latin_proved`: `j(K_n^∘; -n) = [x^J] det(X)^n = (-1)^(n/2) Δ_n`.
- `lem_5_1_quad_split_proved`: general subset elimination `V = S ⊔ T`.
- `lem_3_3_quad_elim_proved`: single-vertex removal (regularity, (E), and (E')).
- `cor_3_4_quad_elim_proved`: `q`-adic valuation lower bound from single-vertex removal.
- `prop_3_5_quad_ind_proved`: inductive `q`-adic valuation bound `v_q(j(M)) ≥ ∑_{N'=1}^N f_q(n, N')`.
- `prop_3_6_identity_proved`: `Δ_n = (-1)^(n/2 + 1) (n - 1)! j(J_{n-1} + I_{n-1})`.
-/

namespace AlonTarsi.Proofs

open AlonTarsi
open scoped BigOperators Matrix

/-! ### Part 1: Permutation Cycle Count, Sign Identity, and First-Return Bijection -/

/-- Conjugation by an equivalence preserves `permCycleCount`. -/
lemma permCycleCount_equivCongr {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : Equiv.Perm α) :
    permCycleCount (e.permCongr p) = permCycleCount p := by
  classical
  unfold permCycleCount
  refine Fintype.card_congr ?_
  have hrel : ∀ x y : α,
      (MulAction.orbitRel (Subgroup.zpowers (e.permCongr p)) β) (e x) (e y) ↔
      (MulAction.orbitRel (Subgroup.zpowers p) α) x y := by
    intro x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨g, hg⟩, hxy⟩
      rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
      refine ⟨⟨p ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩, ?_⟩
      change (p ^ k) y = x
      have h1 : ((Equiv.permCongrHom e p) ^ k) (e y) = e x := hxy
      rw [← map_zpow (Equiv.permCongrHom e) p k] at h1
      change e ((p ^ k) (e.symm (e y))) = e x at h1
      rw [e.symm_apply_apply] at h1
      exact e.injective h1
    · rintro ⟨⟨g, hg⟩, hxy⟩
      rcases Subgroup.mem_zpowers_iff.mp hg with ⟨k, rfl⟩
      refine ⟨⟨(e.permCongr p) ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩, ?_⟩
      change ((Equiv.permCongrHom e p) ^ k) (e y) = e x
      rw [← map_zpow (Equiv.permCongrHom e) p k]
      change e ((p ^ k) (e.symm (e y))) = e x
      rw [e.symm_apply_apply]
      have h1 : (p ^ k) y = x := hxy
      rw [h1]
  refine
    { toFun := Quotient.lift (fun b => Quotient.mk _ (e.symm b)) fun b₁ b₂ h => by
        apply Quotient.sound
        have h' : (MulAction.orbitRel (Subgroup.zpowers (e.permCongr p)) β)
            (e (e.symm b₁)) (e (e.symm b₂)) := by simpa using h
        exact (hrel _ _).mp h'
      invFun := Quotient.lift (fun a => Quotient.mk _ (e a)) fun a₁ a₂ h => by
        apply Quotient.sound
        exact (hrel _ _).mpr h
      left_inv := fun q => Quotient.inductionOn q fun b => by simp
      right_inv := fun q => Quotient.inductionOn q fun a => by simp }

/-- In a finite type, every element `x` returns to `x` after finitely many positive steps of `p`. -/
lemma exists_pos_iterate_eq_self {α : Type*} [Fintype α] (p : Equiv.Perm α) (x : α) :
    ∃ k : ℕ, 0 < k ∧ p^[k] x = x := by
  have hfin : ¬ Function.Injective (fun n : ℕ => p^[n] x) := fun hinj => by
    have : Finite ℕ := Finite.of_injective _ hinj
    exact not_finite ℕ
  unfold Function.Injective at hfin
  push Not at hfin
  rcases hfin with ⟨i, j, hij, hne⟩
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hne.symm (by omega)
  refine ⟨j - i, by omega, ?_⟩
  have h1 : p^[i] (p^[j - i] x) = p^[i] x := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' (le_of_lt hlt), hij]
  exact (p.injective.iterate i) h1

/-- Orbit equivalence in a finite type is witnessed by a nonnegative iterate. -/
lemma orbitRel_iff_exists_iterate {α : Type*} [Fintype α] (p : Equiv.Perm α) (x y : α) :
    (MulAction.orbitRel (Subgroup.zpowers p) α) x y ↔ ∃ k : ℕ, p^[k] y = x := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, hxy⟩
    rcases Subgroup.mem_zpowers_iff.mp hg with ⟨z, rfl⟩
    change (p ^ z) y = x at hxy
    obtain ⟨m, hmpos, hm⟩ := exists_pos_iterate_eq_self p y
    have hpow_m : (p ^ (m : ℤ)) y = y := by
      rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hm
    have hpow_mul : ∀ t : ℕ, (p ^ ((t * m : ℕ) : ℤ)) y = y := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Nat.succ_mul, Nat.cast_add, zpow_add, Equiv.Perm.mul_apply, hpow_m, ih]
    have hpos_ex : ∃ n : ℕ, (p ^ (n : ℤ)) y = x := by
      rcases le_or_gt 0 z with hz | hz
      · exact ⟨z.toNat, by rw [Int.toNat_of_nonneg hz]; exact hxy⟩
      · let t := (-z).toNat
        have htm : 0 ≤ z + ((t * m : ℕ) : ℤ) := by
          have ht : (t : ℤ) = -z := Int.toNat_of_nonneg (by omega)
          have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hmpos
          push_cast
          nlinarith
        refine ⟨(z + ((t * m : ℕ) : ℤ)).toNat, ?_⟩
        rw [Int.toNat_of_nonneg htm, zpow_add, Equiv.Perm.mul_apply, hpow_mul t, hxy]
    rcases hpos_ex with ⟨n, hn⟩
    exact ⟨n, by rwa [zpow_natCast, Equiv.Perm.coe_pow] at hn⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨p ^ (k : ℤ), Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), rfl⟩⟩, ?_⟩
    change (p ^ (k : ℤ)) y = x
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    exact hk

/-- Multiplying on the left by `Equiv.swap x y` when `x ≠ y` are in the same `p`-orbit
splits their cycle into two, increasing `permCycleCount` by `1`. -/
private lemma permCycleCount_swap_mul_of_same_orbit {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) {x y : α} (hne : x ≠ y)
    (hsame : (MulAction.orbitRel (Subgroup.zpowers p) α) x y) :
    permCycleCount (Equiv.swap x y * p) = permCycleCount p + 1 := by
  classical
  set q : Equiv.Perm α := Equiv.swap x y * p
  have hy_ex : ∃ k : ℕ, p^[k] x = y := by
    have hsym := (MulAction.orbitRel (Subgroup.zpowers p) α).symm hsame
    exact (orbitRel_iff_exists_iterate p y x).mp hsym
  let m := Nat.find hy_ex
  have hm_eq : p^[m] x = y := Nat.find_spec hy_ex
  have hm_pos : 0 < m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    rw [hm0] at hm_eq
    exact hne hm_eq
  have hm_min : ∀ i < m, p^[i] x ≠ y := fun i hi => Nat.find_min hy_ex hi
  have hx_ex := exists_pos_iterate_eq_self p x
  let k := Nat.find hx_ex
  have hk_spec := Nat.find_spec hx_ex
  have hk_pos : 0 < k := hk_spec.1
  have hk_eq : p^[k] x = x := hk_spec.2
  have hk_min : ∀ i, 0 < i → i < k → p^[i] x ≠ x := fun i hi0 hik h =>
    Nat.find_min hx_ex hik ⟨hi0, h⟩
  have hmk : m < k := by
    by_contra hge
    have hkm : k ≤ m := by omega
    have hlt : m - k < m := by omega
    have heq : p^[m - k] x = y := by
      have : p^[m - k] (p^[k] x) = p^[m] x := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hkm]
      rw [hk_eq, hm_eq] at this
      exact this
    exact hm_min (m - k) hlt heq
  have hdistinct : ∀ i j, i < k → j < k → p^[i] x = p^[j] x → i = j := by
    intro i j hi hj hij
    wlog hle : i ≤ j generalizing i j
    · exact (this j i hj hi hij.symm (by omega)).symm
    by_cases heq : i = j
    · exact heq
    · exfalso
      have hdiff : p^[j - i] x = x := by
        apply p.injective.iterate i
        rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hle, hij.symm]
      exact hk_min (j - i) (by omega) (by omega) hdiff
  have hq_A : ∀ i, i < m - 1 → q (p^[i] x) = p^[i + 1] x := by
    intro i hi
    change Equiv.swap x y (p (p^[i] x)) = p^[i + 1] x
    rw [← Function.iterate_succ_apply' p i x]
    have h1 : p^[i + 1] x ≠ x := hk_min (i + 1) (by omega) (by omega)
    have h2 : p^[i + 1] x ≠ y := hm_min (i + 1) (by omega)
    exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hq_A_end : q (p^[m - 1] x) = x := by
    change Equiv.swap x y (p (p^[m - 1] x)) = x
    rw [← Function.iterate_succ_apply' p (m - 1) x, Nat.succ_eq_add_one, Nat.sub_add_cancel hm_pos,
      hm_eq, Equiv.swap_apply_right]
  have hq_B : ∀ i, m ≤ i → i < k - 1 → q (p^[i] x) = p^[i + 1] x := by
    intro i him hi
    change Equiv.swap x y (p (p^[i] x)) = p^[i + 1] x
    rw [← Function.iterate_succ_apply' p i x]
    have h1 : p^[i + 1] x ≠ x := hk_min (i + 1) (by omega) (by omega)
    have h2 : p^[i + 1] x ≠ y := fun h => by
      have := hdistinct (i + 1) m (by omega) hmk (h.trans hm_eq.symm)
      omega
    exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hq_B_end : q (p^[k - 1] x) = y := by
    change Equiv.swap x y (p (p^[k - 1] x)) = y
    rw [← Function.iterate_succ_apply' p (k - 1) x, Nat.succ_eq_add_one, Nat.sub_add_cancel hk_pos,
      hk_eq, Equiv.swap_apply_left]
  have hq_iter_x : ∀ n : ℕ, q^[n] x = p^[n % m] x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have hmod_lt : n % m < m := Nat.mod_lt n hm_pos
      by_cases hlast : n % m = m - 1
      · rw [hlast, hq_A_end]
        have hdiv : (n + 1) % m = 0 := by
          rw [Nat.add_mod, hlast]
          by_cases hm1 : m = 1
          · rw [hm1]
          · rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.sub_add_cancel hm_pos, Nat.mod_self]
        rw [hdiv]; rfl
      · rw [hq_A (n % m) (by omega)]
        have hmod1 : (n + 1) % m = n % m + 1 := by
          have h1 : (n + 1) % m = (n % m + 1 % m) % m := Nat.add_mod n 1 m
          have h2 : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
        rw [hmod1]
  have hq_iter_y : ∀ n : ℕ, q^[n] y = p^[m + n % (k - m)] x := by
    intro n
    induction n with
    | zero => simp [hm_eq]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have hkm_pos : 0 < k - m := by omega
      have hmod_lt : n % (k - m) < k - m := Nat.mod_lt n hkm_pos
      by_cases hlast : n % (k - m) = k - m - 1
      · have heq : m + n % (k - m) = k - 1 := by omega
        rw [heq, hq_B_end]
        have hdiv : (n + 1) % (k - m) = 0 := by
          rw [Nat.add_mod, hlast]
          by_cases hkm1 : k - m = 1
          · rw [hkm1]
          · rw [Nat.mod_eq_of_lt (by omega : 1 < k - m), Nat.sub_add_cancel hkm_pos, Nat.mod_self]
        rw [hdiv, add_zero, hm_eq]
      · rw [hq_B (m + n % (k - m)) (by omega) (by omega)]
        have hmod1 : (n + 1) % (k - m) = n % (k - m) + 1 := by
          have h1 : (n + 1) % (k - m) = (n % (k - m) + 1 % (k - m)) % (k - m) :=
            Nat.add_mod n 1 (k - m)
          have h2 : 1 % (k - m) = 1 := Nat.mod_eq_of_lt (by omega)
          rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
        rw [hmod1, add_assoc]
  have hxy_diff_q : ¬ (MulAction.orbitRel (Subgroup.zpowers q) α) y x := by
    rw [orbitRel_iff_exists_iterate]
    rintro ⟨n, hn⟩
    rw [hq_iter_x] at hn
    exact hm_min (n % m) (Nat.mod_lt n hm_pos) hn
  have horb_x_p : ∀ z : α, (MulAction.orbitRel (Subgroup.zpowers p) α) z x ↔
      ∃ i < k, p^[i] x = z := by
    intro z
    rw [orbitRel_iff_exists_iterate]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n % k, Nat.mod_lt n hk_pos, ?_⟩
      have hper : ∀ t : ℕ, p^[t * k] x = x := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [Nat.succ_mul, Function.iterate_add_apply, hk_eq, ih]
      have hdiv : n = n % k + n / k * k := by
        have := Nat.div_add_mod n k; rw [mul_comm] at this; omega
      conv_rhs => rw [hdiv, Function.iterate_add_apply, hper (n / k)]
    · rintro ⟨i, _, hi⟩; exact ⟨i, hi⟩
  have hq_outside : ∀ z : α, ¬ (MulAction.orbitRel (Subgroup.zpowers p) α) z x → q z = p z := by
    intro z hz
    change Equiv.swap x y (p z) = p z
    have h1 : p z ≠ x := by
      intro hpx
      apply hz
      have hsym : (MulAction.orbitRel (Subgroup.zpowers p) α) x z :=
        (orbitRel_iff_exists_iterate p x z).mpr ⟨1, hpx⟩
      exact (MulAction.orbitRel (Subgroup.zpowers p) α).symm hsym
    have h2 : p z ≠ y := by
      intro hpy
      apply hz
      have h1' : (MulAction.orbitRel (Subgroup.zpowers p) α) y z :=
        (orbitRel_iff_exists_iterate p y z).mpr ⟨1, hpy⟩
      have h2' := (MulAction.orbitRel (Subgroup.zpowers p) α).symm h1'
      have h3' := (MulAction.orbitRel (Subgroup.zpowers p) α).symm hsame
      exact (MulAction.orbitRel (Subgroup.zpowers p) α).trans h2' h3'
    exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hq_iter_outside : ∀ z : α, ¬ (MulAction.orbitRel (Subgroup.zpowers p) α) z x →
      ∀ n : ℕ, q^[n] z = p^[n] z := by
    intro z hz n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      apply hq_outside
      intro hmem
      apply hz
      have hstep : (MulAction.orbitRel (Subgroup.zpowers p) α) (p^[n] z) z :=
        (orbitRel_iff_exists_iterate p _ _).mpr ⟨n, rfl⟩
      exact (MulAction.orbitRel (Subgroup.zpowers p) α).trans
        ((MulAction.orbitRel (Subgroup.zpowers p) α).symm hstep) hmem
  have hq_sub_p : ∀ a b : α,
      (MulAction.orbitRel (Subgroup.zpowers q) α) a b →
      (MulAction.orbitRel (Subgroup.zpowers p) α) a b := by
    intro a b hab
    rw [orbitRel_iff_exists_iterate] at hab
    rcases hab with ⟨n, rfl⟩
    by_cases hb : (MulAction.orbitRel (Subgroup.zpowers p) α) b x
    · rcases (horb_x_p b).mp hb with ⟨i, hik, rfl⟩
      have hmem_a : (MulAction.orbitRel (Subgroup.zpowers p) α) (q^[n] (p^[i] x)) x := by
        by_cases him : i < m
        · have hi_eq : p^[i] x = q^[i] x := by rw [hq_iter_x, Nat.mod_eq_of_lt him]
          rw [hi_eq, ← Function.iterate_add_apply, hq_iter_x]
          exact (horb_x_p _).mpr ⟨(n + i) % m, lt_trans (Nat.mod_lt _ hm_pos) hmk, rfl⟩
        · have hi_eq : p^[i] x = q^[i - m] y := by
            rw [hq_iter_y, Nat.mod_eq_of_lt (by omega : i - m < k - m),
              Nat.add_sub_cancel' (by omega)]
          rw [hi_eq, ← Function.iterate_add_apply, hq_iter_y]
          exact (horb_x_p _).mpr
            ⟨m + (n + (i - m)) % (k - m),
              by have := Nat.mod_lt (n + (i - m)) (by omega : 0 < k - m); omega, rfl⟩
      exact (MulAction.orbitRel (Subgroup.zpowers p) α).trans hmem_a
        ((MulAction.orbitRel (Subgroup.zpowers p) α).symm hb)
    · rw [hq_iter_outside b hb n]
      exact (orbitRel_iff_exists_iterate p _ _).mpr ⟨n, rfl⟩
  let Qq := Quotient (MulAction.orbitRel (Subgroup.zpowers q) α)
  let Qp := Quotient (MulAction.orbitRel (Subgroup.zpowers p) α)
  let π : Qq → Qp := Quotient.lift (fun a => Quotient.mk _ a) fun a b h =>
    Quotient.sound (hq_sub_p a b h)
  let qy : Qq := Quotient.mk _ y
  have hbi : Fintype.card { u : Qq // u ≠ qy } = Fintype.card Qp := by
    refine Fintype.card_congr (Equiv.ofBijective (fun u : { u : Qq // u ≠ qy } => π u.1) ⟨?_, ?_⟩)
    · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ heq
      apply Subtype.ext
      dsimp only at heq ⊢
      revert hu₁ hu₂ heq
      refine Quotient.inductionOn₂ u₁ u₂ fun a b hu₁ hu₂ hab => ?_
      have hab_p : (MulAction.orbitRel (Subgroup.zpowers p) α) a b := Quotient.exact hab
      by_cases ha : (MulAction.orbitRel (Subgroup.zpowers p) α) a x
      · have hb : (MulAction.orbitRel (Subgroup.zpowers p) α) b x :=
          (MulAction.orbitRel (Subgroup.zpowers p) α).trans
            ((MulAction.orbitRel (Subgroup.zpowers p) α).symm hab_p) ha
        have hax : (MulAction.orbitRel (Subgroup.zpowers q) α) a x := by
          rcases (horb_x_p a).mp ha with ⟨i, hik, rfl⟩
          by_cases him : i < m
          · exact (orbitRel_iff_exists_iterate q _ _).mpr
              ⟨i, by rw [hq_iter_x, Nat.mod_eq_of_lt him]⟩
          · exfalso
            apply hu₁
            apply Quotient.sound
            exact (orbitRel_iff_exists_iterate q _ _).mpr
              ⟨i - m, by rw [hq_iter_y, Nat.mod_eq_of_lt (by omega : i - m < k - m),
                Nat.add_sub_cancel' (by omega)]⟩
        have hbx : (MulAction.orbitRel (Subgroup.zpowers q) α) b x := by
          rcases (horb_x_p b).mp hb with ⟨i, hik, rfl⟩
          by_cases him : i < m
          · exact (orbitRel_iff_exists_iterate q _ _).mpr
              ⟨i, by rw [hq_iter_x, Nat.mod_eq_of_lt him]⟩
          · exfalso
            apply hu₂
            apply Quotient.sound
            exact (orbitRel_iff_exists_iterate q _ _).mpr
              ⟨i - m, by rw [hq_iter_y, Nat.mod_eq_of_lt (by omega : i - m < k - m),
                Nat.add_sub_cancel' (by omega)]⟩
        exact Quotient.sound ((MulAction.orbitRel (Subgroup.zpowers q) α).trans hax
          ((MulAction.orbitRel (Subgroup.zpowers q) α).symm hbx))
      · have hb : ¬ (MulAction.orbitRel (Subgroup.zpowers p) α) b x := fun hbx =>
          ha ((MulAction.orbitRel (Subgroup.zpowers p) α).trans hab_p hbx)
        rcases (orbitRel_iff_exists_iterate p a b).mp hab_p with ⟨n, rfl⟩
        apply Quotient.sound
        exact (orbitRel_iff_exists_iterate q _ _).mpr ⟨n, hq_iter_outside b hb n⟩
    · intro v
      refine Quotient.inductionOn v fun a => ?_
      by_cases ha : (MulAction.orbitRel (Subgroup.zpowers p) α) a x
      · refine ⟨⟨Quotient.mk _ x, ?_⟩, ?_⟩
        · intro heq
          exact hxy_diff_q ((MulAction.orbitRel (Subgroup.zpowers q) α).symm (Quotient.exact heq))
        · exact Quotient.sound ((MulAction.orbitRel (Subgroup.zpowers p) α).symm ha)
      · refine ⟨⟨Quotient.mk _ a, ?_⟩, rfl⟩
        intro heq
        have hay_q : (MulAction.orbitRel (Subgroup.zpowers q) α) a y := Quotient.exact heq
        have hay_p := hq_sub_p a y hay_q
        exact ha ((MulAction.orbitRel (Subgroup.zpowers p) α).trans hay_p
          ((MulAction.orbitRel (Subgroup.zpowers p) α).symm hsame))
  unfold permCycleCount
  have hcard : Fintype.card Qq = Fintype.card { u : Qq // u ≠ qy } + 1 := by
    have hcomp := Fintype.card_subtype_compl (fun u : Qq => u = qy)
    have h1 : Fintype.card { u : Qq // u = qy } = 1 := Fintype.card_unique
    have h2 : Fintype.card { u : Qq // ¬ u = qy } = Fintype.card { u : Qq // u ≠ qy } := rfl
    have hpos : 1 ≤ Fintype.card Qq := Fintype.card_pos_iff.mpr ⟨qy⟩
    omega
  rw [hcard, hbi]

/-- Multiplying on the left by `Equiv.swap x y` when `x, y` are in different `p`-orbits
merges their cycles into one, decreasing `permCycleCount` by `1`. -/
private lemma permCycleCount_swap_mul_of_diff_orbit {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) {x y : α} (hne : x ≠ y)
    (hdiff : ¬ (MulAction.orbitRel (Subgroup.zpowers p) α) x y) :
    permCycleCount (Equiv.swap x y * p) + 1 = permCycleCount p := by
  classical
  set q : Equiv.Perm α := Equiv.swap x y * p
  have hx_ex := exists_pos_iterate_eq_self p x
  let k := Nat.find hx_ex
  have hk_pos : 0 < k := (Nat.find_spec hx_ex).1
  have hk_eq : p^[k] x = x := (Nat.find_spec hx_ex).2
  have hk_min : ∀ i, 0 < i → i < k → p^[i] x ≠ x := fun i hi0 hik h =>
    Nat.find_min hx_ex hik ⟨hi0, h⟩
  have hiter : ∀ i ≤ k - 1, q^[i] x = p^[i] x := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      change Equiv.swap x y (p (p^[i] x)) = p (p^[i] x)
      rw [← Function.iterate_succ_apply' p i x]
      have h1 : p^[i + 1] x ≠ x := hk_min (i + 1) (by omega) (by omega)
      have h2 : p^[i + 1] x ≠ y := by
        intro hy
        apply hdiff
        have hsym : (MulAction.orbitRel (Subgroup.zpowers p) α) y x :=
          (orbitRel_iff_exists_iterate p y x).mpr ⟨i + 1, hy⟩
        exact (MulAction.orbitRel (Subgroup.zpowers p) α).symm hsym
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hqk : q^[k] x = y := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, Function.iterate_succ_apply', hiter (k - 1) (le_refl _)]
    change Equiv.swap x y (p (p^[k - 1] x)) = y
    rw [← Function.iterate_succ_apply' p (k - 1) x, Nat.succ_eq_add_one, Nat.sub_add_cancel hk_pos,
      hk_eq, Equiv.swap_apply_left]
  have hsame_q : (MulAction.orbitRel (Subgroup.zpowers q) α) x y :=
    (MulAction.orbitRel (Subgroup.zpowers q) α).symm
      ((orbitRel_iff_exists_iterate q y x).mpr ⟨k, hqk⟩)
  have hsq : Equiv.swap x y * q = p := by
    simp [q, ← mul_assoc]
  have := permCycleCount_swap_mul_of_same_orbit q hne hsame_q
  rw [hsq] at this
  exact this.symm

/-- Fundamental parity relation: `(-1)^(card α + permCycleCount p) = sign p`. -/
lemma neg_one_pow_card_add_permCycleCount {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) :
    (-1 : ℤ) ^ (Fintype.card α + permCycleCount p) = (Equiv.Perm.sign p : ℤ) := by
  induction p using Equiv.Perm.swap_induction_on with
  | one =>
    have h1 : permCycleCount (1 : Equiv.Perm α) = Fintype.card α := by
      classical
      unfold permCycleCount
      refine Fintype.card_congr
        { toFun := Quotient.lift id fun a b h => by
            rcases (orbitRel_iff_exists_iterate (1 : Equiv.Perm α) a b).mp h with ⟨k, hk⟩
            simpa using hk.symm
          invFun := Quotient.mk _
          left_inv := fun q => Quotient.inductionOn q fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, map_one, Units.val_one, ← two_mul, pow_mul]
    norm_num
  | swap_mul p x y hne ih =>
    rw [map_mul, Equiv.Perm.sign_swap hne, Units.val_mul, Units.val_neg, Units.val_one,
      neg_one_mul, ← ih]
    by_cases hsame : (MulAction.orbitRel (Subgroup.zpowers p) α) x y
    · rw [permCycleCount_swap_mul_of_same_orbit p hne hsame, ← add_assoc, pow_succ]
      ring
    · have hdec := permCycleCount_swap_mul_of_diff_orbit p hne hsame
      rw [← hdec, ← add_assoc, pow_succ]
      ring

/-- Number of `p`-invariant colorings `α → Fin d` is `d ^ permCycleCount p`. -/
lemma card_invariant_colorings {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (d : ℕ) :
    (Finset.univ.filter fun c : α → Fin d => ∀ a, c (p a) = c a).card =
      d ^ permCycleCount p := by
  classical
  have hbi : Fintype.card { c : α → Fin d // ∀ a, c (p a) = c a } =
      Fintype.card (Quotient (MulAction.orbitRel (Subgroup.zpowers p) α) → Fin d) := by
    refine Fintype.card_congr
      { toFun := fun c => Quotient.lift c.1 fun a b hab => by
          rcases (orbitRel_iff_exists_iterate p a b).mp hab with ⟨k, rfl⟩
          have hiter : ∀ n : ℕ, c.1 (p^[n] b) = c.1 b := by
            intro n; induction n with
            | zero => rfl
            | succ n ih => rw [Function.iterate_succ_apply', c.2, ih]
          exact hiter k
        invFun := fun f => ⟨fun a => f (Quotient.mk _ a), fun a => by
          apply congrArg f
          apply Quotient.sound
          exact (orbitRel_iff_exists_iterate p (p a) a).mpr ⟨1, rfl⟩⟩
        left_inv := fun c => by ext a; rfl
        right_inv := fun f => by ext q; refine Quotient.inductionOn q fun _ => rfl }
  rw [← Fintype.card_subtype, hbi, Fintype.card_fun, Fintype.card_fin]
  rfl

/-- Cycle count of a permutation on a disjoint sum of two invariant sets equals the sum
of the cycle counts on each part. -/
lemma permCycleCount_sumCongr {α β : Type*} [Fintype α] [Fintype β]
    (p : Equiv.Perm α) (q : Equiv.Perm β) :
    permCycleCount (Equiv.sumCongr p q) = permCycleCount p + permCycleCount q := by
  classical
  unfold permCycleCount
  rw [← Fintype.card_sum]
  have hiter : ∀ (n : ℕ) (x : α), (Equiv.sumCongr p q)^[n] (Sum.inl x) = Sum.inl (p^[n] x) := by
    intro n x; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
  have hiterR : ∀ (n : ℕ) (y : β), (Equiv.sumCongr p q)^[n] (Sum.inr y) = Sum.inr (q^[n] y) := by
    intro n y; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
  refine Fintype.card_congr
    { toFun := Quotient.lift
        (fun s : α ⊕ β => match s with
          | Sum.inl a => Sum.inl (Quotient.mk _ a)
          | Sum.inr b => Sum.inr (Quotient.mk _ b))
        (fun s₁ s₂ h => by
          rcases (orbitRel_iff_exists_iterate _ _ _).mp h with ⟨n, hn⟩
          cases s₁ <;> cases s₂
          · rw [hiter] at hn
            have hinj := Sum.inl.inj hn
            exact congrArg Sum.inl (Quotient.sound ((orbitRel_iff_exists_iterate p _ _).mpr ⟨n, hinj⟩))
          · rw [hiterR] at hn; cases hn
          · rw [hiter] at hn; cases hn
          · rw [hiterR] at hn
            have hinj := Sum.inr.inj hn
            exact congrArg Sum.inr (Quotient.sound ((orbitRel_iff_exists_iterate q _ _).mpr ⟨n, hinj⟩)))
      invFun := fun s => match s with
        | Sum.inl u => Quotient.lift (fun a => Quotient.mk _ (Sum.inl a))
            (fun a₁ a₂ h => by
              rcases (orbitRel_iff_exists_iterate p _ _).mp h with ⟨n, rfl⟩
              exact Quotient.sound ((orbitRel_iff_exists_iterate _ _ _).mpr ⟨n, hiter n a₂⟩)) u
        | Sum.inr v => Quotient.lift (fun b => Quotient.mk _ (Sum.inr b))
            (fun b₁ b₂ h => by
              rcases (orbitRel_iff_exists_iterate q _ _).mp h with ⟨n, rfl⟩
              exact Quotient.sound ((orbitRel_iff_exists_iterate _ _ _).mpr ⟨n, hiterR n b₂⟩)) v
      left_inv := fun u => Quotient.inductionOn u fun s => by cases s <;> rfl
      right_inv := fun s => by
        cases s with
        | inl u => refine Quotient.inductionOn u fun _ => rfl
        | inr v => refine Quotient.inductionOn v fun _ => rfl }

/-- First-return permutation cycle count: if `p : Equiv.Perm α` on a finite type and every orbit
meets `{x // P x}`, and `q : Equiv.Perm {x // P x}` is the first-return map of `p` on `{x // P x}`,
then `permCycleCount q = permCycleCount p`. -/
lemma permCycleCount_firstReturn {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (P : α → Prop) [DecidablePred P]
    (hmeet : ∀ x : α, ∃ k : ℕ, P (p^[k] x))
    (q : Equiv.Perm { x : α // P x })
    (hq : ∀ a : { x : α // P x }, ∃ r : ℕ, 0 < r ∧ (q a).1 = p^[r] a.1 ∧
      ∀ j, 0 < j → j < r → ¬ P (p^[j] a.1)) :
    permCycleCount q = permCycleCount p := by
  classical
  have hstep_p : ∀ a : { x : α // P x },
      (MulAction.orbitRel (Subgroup.zpowers p) α) (q a).1 a.1 := by
    intro a
    rcases hq a with ⟨r, _, hr, _⟩
    exact (orbitRel_iff_exists_iterate p _ _).mpr ⟨r, hr.symm⟩
  have hq_to_p : ∀ a b : { x : α // P x },
      (MulAction.orbitRel (Subgroup.zpowers q) _) a b →
      (MulAction.orbitRel (Subgroup.zpowers p) α) a.1 b.1 := by
    intro a b hab
    rcases (orbitRel_iff_exists_iterate q a b).mp hab with ⟨n, rfl⟩
    have hiter : ∀ k : ℕ, (MulAction.orbitRel (Subgroup.zpowers p) α) (q^[k] b).1 b.1 := by
      intro k
      induction k with
      | zero => exact (MulAction.orbitRel (Subgroup.zpowers p) α).refl b.1
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (MulAction.orbitRel (Subgroup.zpowers p) α).trans (hstep_p (q^[k] b)) ih
    exact hiter n
  have hp_to_q : ∀ (n : ℕ) (a b : { x : α // P x }),
      p^[n] b.1 = a.1 → (MulAction.orbitRel (Subgroup.zpowers q) _) a b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b hn
      by_cases hn0 : n = 0
      · subst hn0
        have heq : b = a := Subtype.ext hn
        subst heq
        exact (MulAction.orbitRel (Subgroup.zpowers q) _).refl b
      · rcases hq b with ⟨r, hr0, hr_eq, hr_min⟩
        have hrle : r ≤ n := by
          by_contra hgt
          exact hr_min n (by omega) (by omega) (hn ▸ a.2)
        have hrem : p^[n - r] (q b).1 = a.1 := by
          rw [hr_eq, ← Function.iterate_add_apply, Nat.sub_add_cancel hrle, hn]
        have h1 := ih (n - r) (by omega) a (q b) hrem
        have h2 : (MulAction.orbitRel (Subgroup.zpowers q) _) (q b) b :=
          (orbitRel_iff_exists_iterate q _ _).mpr ⟨1, rfl⟩
        exact (MulAction.orbitRel (Subgroup.zpowers q) _).trans h1 h2
  let f : Quotient (MulAction.orbitRel (Subgroup.zpowers q) _) →
      Quotient (MulAction.orbitRel (Subgroup.zpowers p) α) :=
    Quotient.lift (fun a => Quotient.mk _ a.1) fun a b h => Quotient.sound (hq_to_p a b h)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro u₁ u₂ heq
      refine Quotient.inductionOn₂ u₁ u₂ (fun a b h => ?_) heq
      rcases (orbitRel_iff_exists_iterate p a.1 b.1).mp (Quotient.exact h) with ⟨n, hn⟩
      exact Quotient.sound (hp_to_q n a b hn)
    · intro v
      refine Quotient.inductionOn v fun x => ?_
      rcases hmeet x with ⟨k, hk⟩
      refine ⟨Quotient.mk _ ⟨p^[k] x, hk⟩, ?_⟩
      exact Quotient.sound ((orbitRel_iff_exists_iterate p _ _).mpr ⟨k, rfl⟩)
  unfold permCycleCount
  exact Fintype.card_congr (Equiv.ofBijective f hf_bij)

/-! ### Part 2: Multidigraph Isomorphism & Regularity Basics -/

/-- Number of arcs of a `d`-regular multidigraph is `|V| * d`. -/
lemma card_arcs_of_isRegular {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) (hreg : IsRegular H d) :
    Fintype.card H.Arc = Fintype.card V * d := by
  have hpart : (Finset.univ : Finset H.Arc).card =
      ∑ v : V, (Finset.univ.filter fun a : H.Arc => H.head a = v).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext a; simp
    · intro u _ v _ hne
      exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
        hne ((Finset.mem_filter.mp ha₁).2.symm.trans (Finset.mem_filter.mp ha₂).2)
  rw [← Finset.card_univ, hpart]
  simp_rw [hreg.1, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- An isomorphism of multidigraphs preserves the circuit partition polynomial. -/
lemma circuitPoly_eq_of_equiv {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    (H₁ : Multidigraph V₁) (H₂ : Multidigraph V₂)
    (eV : V₁ ≃ V₂) (eA : H₁.Arc ≃ H₂.Arc)
    (htail : ∀ a, H₂.tail (eA a) = eV (H₁.tail a))
    (hhead : ∀ a, H₂.head (eA a) = eV (H₁.head a)) :
    circuitPoly H₁ = circuitPoly H₂ := by
  classical
  let eTS : TransitionSystem H₁ ≃ TransitionSystem H₂ :=
    { toFun := fun π v₂ =>
        { toFun := fun b =>
            let a : inArcs H₁ (eV.symm v₂) := ⟨eA.symm b.1, by
              apply eV.injective; rw [← hhead, eA.apply_symm_apply, b.2, eV.apply_symm_apply]⟩
            ⟨eA (π (eV.symm v₂) a).1, by rw [htail, (π (eV.symm v₂) a).2, eV.apply_symm_apply]⟩
          invFun := fun b =>
            let a : outArcs H₁ (eV.symm v₂) := ⟨eA.symm b.1, by
              apply eV.injective; rw [← htail, eA.apply_symm_apply, b.2, eV.apply_symm_apply]⟩
            ⟨eA ((π (eV.symm v₂)).symm a).1, by
              rw [hhead, ((π (eV.symm v₂)).symm a).2, eV.apply_symm_apply]⟩
          left_inv := fun b => by apply Subtype.ext; simp
          right_inv := fun b => by apply Subtype.ext; simp }
      invFun := fun π₂ v₁ =>
        { toFun := fun a =>
            let b : inArcs H₂ (eV v₁) := ⟨eA a.1, by rw [hhead, a.2]⟩
            ⟨eA.symm (π₂ (eV v₁) b).1, by
              apply eV.injective; rw [← htail, eA.apply_symm_apply, (π₂ (eV v₁) b).2]⟩
          invFun := fun a =>
            let b : outArcs H₂ (eV v₁) := ⟨eA a.1, by rw [htail, a.2]⟩
            ⟨eA.symm ((π₂ (eV v₁)).symm b).1, by
              apply eV.injective; rw [← hhead, eA.apply_symm_apply, ((π₂ (eV v₁)).symm b).2]⟩
          left_inv := fun a => by apply Subtype.ext; simp
          right_inv := fun a => by apply Subtype.ext; simp }
      left_inv := fun π => by
        funext v₁; apply Equiv.ext; intro a; apply Subtype.ext
        have hsub : ∀ {u : V₁} (hu : eV.symm (eV v₁) = u) (ha : H₁.head a.1 = u),
            (π u ⟨a.1, ha⟩).1 = (π (eV.symm (eV v₁)) ⟨a.1, by rw [hu]; exact ha⟩).1 := by
          intro u hu ha; subst hu; rfl
        simp only [Equiv.coe_fn_mk, Equiv.symm_apply_apply]
        exact (hsub (eV.symm_apply_apply v₁) a.2).symm
      right_inv := fun π₂ => by
        funext v₂; apply Equiv.ext; intro b; apply Subtype.ext
        have hsub : ∀ {u : V₂} (hu : eV (eV.symm v₂) = u) (hb : H₂.head b.1 = u),
            (π₂ u ⟨b.1, hb⟩).1 = (π₂ (eV (eV.symm v₂)) ⟨b.1, by rw [hu]; exact hb⟩).1 := by
          intro u hu hb; subst hu; rfl
        simp only [Equiv.coe_fn_mk, Equiv.apply_symm_apply]
        exact (hsub (eV.apply_symm_apply v₂) b.2).symm }
  have hcyc : ∀ π : TransitionSystem H₁, cycCount H₂ (eTS π) = cycCount H₁ π := by
    intro π
    unfold cycCount
    have hperm : arcPerm H₂ (eTS π) = eA.permCongr (arcPerm H₁ π) := by
      apply Equiv.ext; intro b
      change eA (π (eV.symm (H₂.head b)) ⟨eA.symm b, _⟩).1 =
        eA (π (H₁.head (eA.symm b)) ⟨eA.symm b, rfl⟩).1
      congr 1
      have hv : eV.symm (H₂.head b) = H₁.head (eA.symm b) := by
        apply eV.injective; rw [eV.apply_symm_apply, ← hhead, eA.apply_symm_apply]
      have hsub : ∀ {u : V₁} (hu : eV.symm (H₂.head b) = u) (hb' : H₁.head (eA.symm b) = u),
          (π (eV.symm (H₂.head b)) ⟨eA.symm b, by rw [hu]; exact hb'⟩).1 =
          (π u ⟨eA.symm b, hb'⟩).1 := by
        intro u hu hb'; subst hu; rfl
      exact hsub hv rfl
    rw [hperm, permCycleCount_equivCongr]
  unfold circuitPoly
  refine Fintype.sum_equiv eTS _ _ fun π => ?_
  rw [hcyc π]

/-- `ofMatrix M` has adjacency matrix `M`. -/
lemma adjMatrix_ofMatrix {V : Type} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ) :
    adjMatrix (ofMatrix M) = M := by
  ext u v
  change (Finset.univ.filter fun a : (ofMatrix M).Arc =>
    (ofMatrix M).tail a = u ∧ (ofMatrix M).head a = v).card = M u v
  have hbi : (Finset.univ.filter fun a : (ofMatrix M).Arc =>
      (ofMatrix M).tail a = u ∧ (ofMatrix M).head a = v).card =
      Fintype.card (Fin (M u v)) := by
    refine Finset.card_bij
      (fun a ha => by
        have h1 := (Finset.mem_filter.mp ha).2
        exact h1.1 ▸ h1.2 ▸ a.2.2) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ ha₁ a₂ ha₂ heq
      rcases a₁ with ⟨u₁, v₁, k₁⟩
      rcases a₂ with ⟨u₂, v₂, k₂⟩
      have h1 := (Finset.mem_filter.mp ha₁).2
      have h2 := (Finset.mem_filter.mp ha₂).2
      dsimp [ofMatrix] at h1 h2 heq
      rcases h1 with ⟨rfl, rfl⟩
      rcases h2 with ⟨rfl, rfl⟩
      have hk : k₁ = k₂ := heq
      rw [hk]
    · intro k _
      exact ⟨⟨u, v, k⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩, rfl⟩
  rw [hbi, Fintype.card_fin]

/-- Any multidigraph `H` is isomorphic to `ofMatrix (adjMatrix H)`, hence has the same
circuit partition polynomial. -/
lemma circuitPoly_eq_ofMatrix {V : Type} [Fintype V] [DecidableEq V] (H : Multidigraph V) :
    circuitPoly H = circuitPoly (ofMatrix (adjMatrix H)) := by
  classical
  have eFiber : ∀ u v : V, { a : H.Arc // H.tail a = u ∧ H.head a = v } ≃ Fin (adjMatrix H u v) :=
    fun u v => Fintype.equivFinOfCardEq (by
      rw [Fintype.card_subtype]; rfl)
  let eA : H.Arc ≃ (ofMatrix (adjMatrix H)).Arc :=
    { toFun := fun a => ⟨H.tail a, H.head a, eFiber (H.tail a) (H.head a) ⟨a, rfl, rfl⟩⟩
      invFun := fun b => ((eFiber b.1 b.2.1).symm b.2.2).1
      left_inv := fun a => by
        dsimp
        exact congrArg Subtype.val ((eFiber (H.tail a) (H.head a)).symm_apply_apply ⟨a, rfl, rfl⟩)
      right_inv := fun ⟨u, v, k⟩ => by
        dsimp
        have hspec := ((eFiber u v).symm k).2
        have hsub : ∀ {u' v' : V} (hu : u' = u) (hv : v' = v)
            (a : { a : H.Arc // H.tail a = u' ∧ H.head a = v' }),
            (⟨u', v', eFiber u' v' a⟩ : (ofMatrix (adjMatrix H)).Arc) =
              ⟨u, v, eFiber u v ⟨a.1, hu ▸ a.2.1, hv ▸ a.2.2⟩⟩ := by
          intro u' v' hu hv a; subst hu; subst hv; rfl
        rw [hsub hspec.1 hspec.2 ⟨((eFiber u v).symm k).1, rfl, rfl⟩]
        exact congrArg (fun x => (⟨u, v, x⟩ : (ofMatrix (adjMatrix H)).Arc))
          ((eFiber u v).apply_symm_apply k) }
  exact circuitPoly_eq_of_equiv H (ofMatrix (adjMatrix H)) (Equiv.refl V) eA
    (fun _ => rfl) (fun _ => rfl)

/-- Unfolding `circuitPoly H` with any `Fintype (TransitionSystem H)` instance without `whnf` blowup. -/
lemma circuitPoly_eq_sum {V : Type} [Fintype V] (H : Multidigraph V)
    [Fintype (TransitionSystem H)] :
    circuitPoly H = ∑ π : TransitionSystem H, Polynomial.X ^ (cycCount H π) := by
  unfold circuitPoly
  convert rfl

/-- Evaluating `circuitPoly H` at `-d` equals `circuitEval (adjMatrix H) d`. -/
lemma circuitPoly_eval_eq_circuitEval {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) :
    (circuitPoly H).eval (-(d : ℤ)) = circuitEval (adjMatrix H) d := by
  unfold circuitEval
  rw [circuitPoly_eq_ofMatrix]

/-- `IsRegular` depends only on the adjacency matrix (column sums and row sums equal `d`). -/
lemma isRegular_iff_adjMatrix {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) :
    IsRegular H d ↔
      (∀ v : V, ∑ u : V, adjMatrix H u v = d) ∧ (∀ u : V, ∑ v : V, adjMatrix H u v = d) := by
  have hin : ∀ v : V, (Finset.univ.filter fun a : H.Arc => H.head a = v).card =
      ∑ u : V, adjMatrix H u v := by
    intro v
    simp only [adjMatrix, Matrix.of_apply]
    rw [← Finset.card_biUnion]
    · congr 1; ext a; simp
    · intro u₁ _ u₂ _ hne
      exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
        hne ((Finset.mem_filter.mp ha₁).2.1.symm.trans (Finset.mem_filter.mp ha₂).2.1)
  have hout : ∀ u : V, (Finset.univ.filter fun a : H.Arc => H.tail a = u).card =
      ∑ v : V, adjMatrix H u v := by
    intro u
    simp only [adjMatrix, Matrix.of_apply]
    rw [← Finset.card_biUnion]
    · congr 1; ext a; simp
    · intro v₁ _ v₂ _ hne
      exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
        hne ((Finset.mem_filter.mp ha₁).2.2.symm.trans (Finset.mem_filter.mp ha₂).2.2)
  simp only [IsRegular, hin, hout]

/-! ### Part 3: Lemma 3.1 (`lem_3_1_quad_fact`) and Lemma 3.2 (`lem_3_2_quad_latin`) -/

/-- Monomial `(u, σ u) ↦ 1` corresponding to a permutation `σ : Equiv.Perm V`. -/
private noncomputable def permMonomial {V : Type} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) : (V × V) →₀ ℕ :=
  ∑ u : V, Finsupp.single (u, σ u) 1

private lemma permMonomial_apply {V : Type} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) (u v : V) :
    permMonomial σ (u, v) = if σ u = v then 1 else 0 := by
  unfold permMonomial
  rw [Finsupp.finsetSum_apply]
  have h1 : ∀ u' : V, (Finsupp.single (u', σ u') 1 : (V × V) →₀ ℕ) (u, v) =
      if u' = u then (if σ u' = v then 1 else 0) else 0 := by
    intro u'
    rw [Finsupp.single_apply]
    by_cases hu : u' = u
    · subst hu
      by_cases hv : σ u' = v
      · subst hv; simp
      · have hne : (u', σ u') ≠ (u', v) := fun h => hv (Prod.mk.inj h).2
        simp [hne, hv]
    · have hne : (u', σ u') ≠ (u, v) := fun h => hu (Prod.mk.inj h).1
      simp [hne, hu]
  simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

section
open Classical

/-- Explicit expansion of `detPowCoeff M d` as a signed sum over `d`-tuples of permutations
whose multiplicity matrix equals `M`. -/
lemma detPowCoeff_eq_sum {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (d : ℕ) :
    detPowCoeff M d =
      ∑ σ : Fin d → Equiv.Perm V,
        if (∀ u v : V, (Finset.univ.filter fun k : Fin d => σ k u = v).card = M u v)
        then ∏ k : Fin d, (Equiv.Perm.sign (σ k) : ℤ) else 0 := by
  classical
  unfold detPowCoeff
  have hdet : (genericMatrix V).det =
      ∑ τ : Equiv.Perm V,
        MvPolynomial.monomial (permMonomial τ) (Equiv.Perm.sign τ : ℤ) := by
    rw [Matrix.det_apply]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm V)) _ _ fun τ => ?_
    have hsign : Equiv.Perm.sign τ⁻¹ = Equiv.Perm.sign τ := by
      rw [map_inv, Int.units_inv_eq_self]
    have hprod : (∏ u : V, (genericMatrix V) (τ u) u) =
        MvPolynomial.monomial (permMonomial τ⁻¹) (1 : ℤ) := by
      have hreindex : (∏ u : V, (genericMatrix V) (τ u) u) =
          ∏ u : V, MvPolynomial.monomial (Finsupp.single (u, τ⁻¹ u) 1) (1 : ℤ) := by
        refine Fintype.prod_equiv τ _ _ fun u => ?_
        simp [genericMatrix, MvPolynomial.X]
      rw [hreindex]
      have hmon_prod : ∀ (s : Finset V) (f : V → (V × V) →₀ ℕ),
          ∏ u ∈ s, MvPolynomial.monomial (f u) (1 : ℤ) =
            MvPolynomial.monomial (∑ u ∈ s, f u) (1 : ℤ) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.monomial_mul, one_mul]
      exact hmon_prod Finset.univ (fun u => Finsupp.single (u, τ⁻¹ u) 1)
    change (Equiv.Perm.sign τ : ℤ) • (∏ u : V, (genericMatrix V) (τ u) u) =
      MvPolynomial.monomial (permMonomial τ⁻¹) (Equiv.Perm.sign τ⁻¹ : ℤ)
    rw [hprod, hsign, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hpow : (genericMatrix V).det ^ d =
      ∑ σ : Fin d → Equiv.Perm V,
        MvPolynomial.monomial (∑ k : Fin d, permMonomial (σ k))
          (∏ k : Fin d, (Equiv.Perm.sign (σ k) : ℤ)) := by
    have hprod_const : (genericMatrix V).det ^ d = ∏ _k : Fin d, (genericMatrix V).det := by
      simp
    rw [hprod_const, hdet, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hmon_prod : ∀ (s : Finset (Fin d)) (f : Fin d → (V × V) →₀ ℕ) (c : Fin d → ℤ),
        ∏ k ∈ s, MvPolynomial.monomial (f k) (c k) =
          MvPolynomial.monomial (∑ k ∈ s, f k) (∏ k ∈ s, c k) := by
      intro s f c
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ih,
          MvPolynomial.monomial_mul]
    exact hmon_prod Finset.univ (fun k => permMonomial (σ k))
      (fun k => (Equiv.Perm.sign (σ k) : ℤ))
  rw [hpow, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  have heq_iff : (∑ k : Fin d, permMonomial (σ k)) = matMonomial M ↔
      ∀ u v : V, (Finset.univ.filter fun k : Fin d => σ k u = v).card = M u v := by
    constructor
    · intro h u v
      have h1 := congrArg (fun f : (V × V) →₀ ℕ => f (u, v)) h
      rw [Finsupp.finset_sum_apply] at h1
      simp_rw [permMonomial_apply] at h1
      rw [Finset.sum_boole] at h1
      simpa [matMonomial] using h1
    · intro h
      ext ⟨u, v⟩
      rw [Finsupp.finset_sum_apply]
      simp_rw [permMonomial_apply]
      rw [Finset.sum_boole]
      simpa [matMonomial] using h u v
  by_cases hc : (∑ k : Fin d, permMonomial (σ k)) = matMonomial M
  · rw [if_pos hc, if_pos (heq_iff.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (heq_iff.mpr h))]

end

/-- **Lemma 3.1**: For any `d`-regular multidigraph `H` on `V`,
`j(H; -d) = (-1)^(N d) (∏_{u, v} M_{uv}!) [x^M] det(X)^d`. -/
theorem lem_3_1_quad_fact_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) (hreg : IsRegular H d) :
    (circuitPoly H).eval (-(d : ℤ)) =
      (-1 : ℤ) ^ (Fintype.card V * d) *
        (∏ u : V, ∏ v : V, ((adjMatrix H u v).factorial : ℤ)) *
        detPowCoeff (adjMatrix H) d := by
  classical
  have hcards : Fintype.card H.Arc = Fintype.card V * d := card_arcs_of_isRegular H d hreg
  have hsign_sq : (-1 : ℤ) ^ (Fintype.card V * d) * (-1 : ℤ) ^ (Fintype.card V * d) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  -- Multiply both sides by (-1)^(N * d) and show equality
  suffices hmain :
      (-1 : ℤ) ^ (Fintype.card V * d) * (circuitPoly H).eval (-(d : ℤ)) =
        (∏ u : V, ∏ v : V, ((adjMatrix H u v).factorial : ℤ)) * detPowCoeff (adjMatrix H) d by
    calc (circuitPoly H).eval (-(d : ℤ))
        = ((-1 : ℤ) ^ (Fintype.card V * d) * (-1 : ℤ) ^ (Fintype.card V * d)) *
            (circuitPoly H).eval (-(d : ℤ)) := by rw [hsign_sq, one_mul]
      _ = (-1 : ℤ) ^ (Fintype.card V * d) *
            ((-1 : ℤ) ^ (Fintype.card V * d) * (circuitPoly H).eval (-(d : ℤ))) := by ring
      _ = (-1 : ℤ) ^ (Fintype.card V * d) *
            ((∏ u : V, ∏ v : V, ((adjMatrix H u v).factorial : ℤ)) *
              detPowCoeff (adjMatrix H) d) := by rw [hmain]
      _ = (-1 : ℤ) ^ (Fintype.card V * d) *
            (∏ u : V, ∏ v : V, ((adjMatrix H u v).factorial : ℤ)) *
            detPowCoeff (adjMatrix H) d := by ring
  -- Step 1: Expand LHS as double sum over (π, c) and swap sums
  have hLHS :
      (-1 : ℤ) ^ (Fintype.card V * d) * (circuitPoly H).eval (-(d : ℤ)) =
        ∑ c : H.Arc → Fin d,
          ∑ π : TransitionSystem H,
            if (∀ a : H.Arc, c (arcPerm H π a) = c a) then
              (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0 := by
    rw [circuitPoly_eq_sum H, Polynomial.eval_finsetSum, Finset.mul_sum]
    have hterm : ∀ π : TransitionSystem H,
        (-1 : ℤ) ^ (Fintype.card V * d) * (Polynomial.X ^ cycCount H π).eval (-(d : ℤ)) =
          ∑ c : H.Arc → Fin d,
            if (∀ a : H.Arc, c (arcPerm H π a) = c a) then
              (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0 := by
      intro π
      rw [Polynomial.eval_pow, Polynomial.eval_X,
        show -(d : ℤ) = (-1 : ℤ) * (d : ℤ) by ring, mul_pow, ← mul_assoc,
        ← pow_add, ← hcards, cycCount, neg_one_pow_card_add_permCycleCount]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        card_invariant_colorings (arcPerm H π) d, Nat.cast_pow, mul_comm]
    rw [Finset.sum_congr rfl fun π _ => hterm π]
    exact Finset.sum_comm
  rw [hLHS]
  -- Step 2: Define proper colorings (every vertex has exactly 1 in-arc and 1 out-arc of each color)
  let IsProper (c : H.Arc → Fin d) : Prop :=
    ∀ v : V, ∀ k : Fin d,
      (Finset.univ.filter fun a : inArcs H v => c a.1 = k).card = 1 ∧
      (Finset.univ.filter fun a : outArcs H v => c a.1 = k).card = 1
  -- Step 3: Improper colorings cancel to 0 via transposition involution
  have himproper_zero : ∀ c : H.Arc → Fin d, ¬ IsProper c →
      (∑ π : TransitionSystem H,
        if (∀ a : H.Arc, c (arcPerm H π a) = c a) then
          (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0) = 0 := by
    intro c hnot
    by_cases hex : ∃ π₀ : TransitionSystem H, ∀ a : H.Arc, c (arcPerm H π₀ a) = c a
    · rcases hex with ⟨π₀, hπ₀⟩
      have hcinv_iff : ∀ π : TransitionSystem H,
          (∀ a : H.Arc, c (arcPerm H π a) = c a) ↔
          (∀ (v : V) (e : inArcs H v), c (π v e).1 = c e.1) := by
        intro π
        constructor
        · intro h v ⟨a, ha⟩
          subst ha; exact h a
        · intro h a
          exact h (H.head a) ⟨a, rfl⟩
      have hcard_eq : ∀ (v : V) (k : Fin d),
          (Finset.univ.filter fun a : inArcs H v => c a.1 = k).card =
          (Finset.univ.filter fun a : outArcs H v => c a.1 = k).card := by
        intro v k
        refine Finset.card_bij (fun e _ => π₀ v e) ?_ ?_ ?_
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          rw [(hcinv_iff π₀).mp hπ₀ v e, he]
        · intro e₁ _ e₂ _ h; exact (π₀ v).injective h
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          refine ⟨(π₀ v).symm b, ?_, (π₀ v).apply_symm_apply b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have := (hcinv_iff π₀).mp hπ₀ v ((π₀ v).symm b)
          rw [(π₀ v).apply_symm_apply, hb] at this
          exact this.symm
      -- Find (v₀, k₀) with at least 2 outgoing arcs of color k₀
      have hex_ge2 : ∃ v₀ : V, ∃ k₀ : Fin d,
          2 ≤ (Finset.univ.filter fun a : outArcs H v₀ => c a.1 = k₀).card := by
        by_contra hle1
        push_neg at hle1
        apply hnot
        intro v k
        have hsum_d : ∑ j : Fin d,
            (Finset.univ.filter fun a : outArcs H v => c a.1 = j).card = d := by
          have hpart : (Finset.univ : Finset (outArcs H v)).card =
              ∑ j : Fin d, (Finset.univ.filter fun a : outArcs H v => c a.1 = j).card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext a; simp
            · intro j₁ _ j₂ _ hne
              exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
                hne ((Finset.mem_filter.mp ha₁).2.symm.trans (Finset.mem_filter.mp ha₂).2)
          rw [← hpart, Finset.card_univ, Fintype.card_subtype]
          exact hreg.2 v
        have hle_each : ∀ j : Fin d,
            (Finset.univ.filter fun a : outArcs H v => c a.1 = j).card ≤ 1 :=
          fun j => Nat.lt_succ_iff.mp (hle1 v j)
        have heq_one : (Finset.univ.filter fun a : outArcs H v => c a.1 = k).card = 1 := by
          by_contra hne1
          have h0 : (Finset.univ.filter fun a : outArcs H v => c a.1 = k).card = 0 := by
            have := hle_each k; omega
          have hsum_lt : ∑ j : Fin d,
              (Finset.univ.filter fun a : outArcs H v => c a.1 = j).card <
              ∑ _j : Fin d, 1 := by
            refine Finset.sum_lt_sum (fun j _ => hle_each j) ⟨k, Finset.mem_univ k, by omega⟩
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
            mul_one] at hsum_lt
          omega
        exact ⟨by rw [hcard_eq v k, heq_one], heq_one⟩
      rcases hex_ge2 with ⟨v₀, k₀, hge2⟩
      obtain ⟨b₁, hb₁, b₂, hb₂, hne⟩ :=
        Finset.one_lt_card.mp (Nat.lt_of_lt_of_le (by decide : 1 < 2) hge2)
      have hcb₁ : c b₁.1 = k₀ := (Finset.mem_filter.mp hb₁).2
      have hcb₂ : c b₂.1 = k₀ := (Finset.mem_filter.mp hb₂).2
      have hne_val : b₁.1 ≠ b₂.1 := fun h => hne (Subtype.ext h)
      let Φ : TransitionSystem H ≃ TransitionSystem H :=
        { toFun := fun π v => if hv : v = v₀ then (π v).trans (Equiv.swap (hv ▸ b₁) (hv ▸ b₂)) else π v
          invFun := fun π v => if hv : v = v₀ then (π v).trans (Equiv.swap (hv ▸ b₁) (hv ▸ b₂)) else π v
          left_inv := fun π => by
            funext v; by_cases hv : v = v₀
            · subst hv; apply Equiv.ext; intro e; simp
            · simp [hv]
          right_inv := fun π => by
            funext v; by_cases hv : v = v₀
            · subst hv; apply Equiv.ext; intro e; simp
            · simp [hv] }
      have hΦ_arc : ∀ π : TransitionSystem H,
          arcPerm H (Φ π) = Equiv.swap b₁.1 b₂.1 * arcPerm H π := by
        intro π
        apply Equiv.ext; intro a
        change ((if hv : H.head a = v₀ then
          (π (H.head a)).trans (Equiv.swap (hv ▸ b₁) (hv ▸ b₂)) else π (H.head a)) ⟨a, rfl⟩).1 =
          Equiv.swap b₁.1 b₂.1 (π (H.head a) ⟨a, rfl⟩).1
        by_cases hv : H.head a = v₀
        · subst hv
          simp only [↓reduceDIte, Equiv.trans_apply]
          have hswap_val : ∀ x : outArcs H (H.head a),
              (Equiv.swap b₁ b₂ x).1 = Equiv.swap b₁.1 b₂.1 x.1 := by
            intro x
            by_cases h1 : x = b₁
            · subst h1; simp
            · by_cases h2 : x = b₂
              · subst h2; simp
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
                  Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Subtype.ext h))
                    (fun h => h2 (Subtype.ext h))]
          exact hswap_val (π (H.head a) ⟨a, rfl⟩)
        · simp only [hv, ↓reduceDIte]
          have h1 : (π (H.head a) ⟨a, rfl⟩).1 ≠ b₁.1 := fun h => by
            have := (π (H.head a) ⟨a, rfl⟩).2
            rw [h, b₁.2] at this; exact hv this.symm
          have h2 : (π (H.head a) ⟨a, rfl⟩).1 ≠ b₂.1 := fun h => by
            have := (π (H.head a) ⟨a, rfl⟩).2
            rw [h, b₂.2] at this; exact hv this.symm
          exact (Equiv.swap_apply_of_ne_of_ne h1 h2).symm
      have hΦ_inv : ∀ π : TransitionSystem H,
          (∀ a, c (arcPerm H (Φ π) a) = c a) ↔ (∀ a, c (arcPerm H π a) = c a) := by
        intro π
        have hswap_c : ∀ x : H.Arc, c (Equiv.swap b₁.1 b₂.1 x) = c x := by
          intro x
          by_cases h1 : x = b₁.1
          · subst h1; simp [hcb₁, hcb₂]
          · by_cases h2 : x = b₂.1
            · subst h2; simp [hcb₁, hcb₂]
            · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        simp_rw [hΦ_arc, Equiv.Perm.mul_apply, hswap_c]
      set S := ∑ π : TransitionSystem H,
        if (∀ a : H.Arc, c (arcPerm H π a) = c a) then
          (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0
      have hneg : S = -S := by
        calc S = ∑ π : TransitionSystem H,
              if (∀ a : H.Arc, c (arcPerm H (Φ π) a) = c a) then
                (Equiv.Perm.sign (arcPerm H (Φ π)) : ℤ) else 0 :=
              (Fintype.sum_equiv Φ _ _ (fun _ => rfl)).symm
          _ = ∑ π : TransitionSystem H,
              -(if (∀ a : H.Arc, c (arcPerm H π a) = c a) then
                (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0) := by
              refine Finset.sum_congr rfl fun π _ => ?_
              by_cases hc : ∀ a : H.Arc, c (arcPerm H π a) = c a
              · rw [if_pos ((hΦ_inv π).mpr hc), if_pos hc, hΦ_arc, map_mul,
                  Equiv.Perm.sign_swap hne_val]
                simp
              · rw [if_neg (fun h => hc ((hΦ_inv π).mp h)), if_neg hc]
                simp
          _ = -S := by rw [Finset.sum_neg_distrib]
      omega
    · push_neg at hex
      exact Finset.sum_eq_zero fun π _ => if_neg (fun h => by
        rcases hex π with ⟨a, ha⟩; exact ha (h a))
  -- Step 4: Collapse the sum over c to proper colorings
  have hproper_sum :
      (∑ c : H.Arc → Fin d,
        ∑ π : TransitionSystem H,
          if (∀ a : H.Arc, c (arcPerm H π a) = c a) then
            (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0) =
      ∑ c : { c : H.Arc → Fin d // IsProper c },
        ∑ π : TransitionSystem H,
          if (∀ a : H.Arc, c.1 (arcPerm H π a) = c.1 a) then
            (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0 := by
    rw [← Fintype.sum_subtype_add_sum_subtype IsProper]
    have hzero : (∑ c : { c : H.Arc → Fin d // ¬ IsProper c },
        ∑ π : TransitionSystem H,
          if (∀ a : H.Arc, c.1 (arcPerm H π a) = c.1 a) then
            (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0) = 0 :=
      Finset.sum_eq_zero fun c _ => himproper_zero c.1 c.2
    rw [hzero, add_zero]
  rw [hproper_sum]
  -- Step 5: For each proper coloring c, extract unique π_c and tuple of permutations σ_c
  have hunique_out : ∀ (c : { c : H.Arc → Fin d // IsProper c }) (v : V) (k : Fin d),
      ∃! a : outArcs H v, c.1 a.1 = k := by
    intro c v k
    rcases Finset.card_eq_one.mp (c.2 v k).2 with ⟨a, ha⟩
    refine ⟨a, ?_, fun b hb => ?_⟩
    · have : a ∈ Finset.univ.filter (fun x : outArcs H v => c.1 x.1 = k) := by rw [ha]; simp
      exact (Finset.mem_filter.mp this).2
    · have : b ∈ ({a} : Finset (outArcs H v)) := by
        rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
      exact Finset.mem_singleton.mp this
  have hunique_in : ∀ (c : { c : H.Arc → Fin d // IsProper c }) (v : V) (k : Fin d),
      ∃! a : inArcs H v, c.1 a.1 = k := by
    intro c v k
    rcases Finset.card_eq_one.mp (c.2 v k).1 with ⟨a, ha⟩
    refine ⟨a, ?_, fun b hb => ?_⟩
    · have : a ∈ Finset.univ.filter (fun x : inArcs H v => c.1 x.1 = k) := by rw [ha]; simp
      exact (Finset.mem_filter.mp this).2
    · have : b ∈ ({a} : Finset (inArcs H v)) := by
        rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
      exact Finset.mem_singleton.mp this
  let outOf (c : { c : H.Arc → Fin d // IsProper c }) (v : V) (k : Fin d) : outArcs H v :=
    (hunique_out c v k).choose
  have houtOf_c : ∀ (c : { c : H.Arc → Fin d // IsProper c }) v k, c.1 (outOf c v k).1 = k :=
    fun c v k => (hunique_out c v k).choose_spec.1
  have houtOf_uniq : ∀ (c : { c : H.Arc → Fin d // IsProper c }) v k (a : outArcs H v),
      c.1 a.1 = k → a = outOf c v k := fun c v k a ha =>
    (hunique_out c v k).choose_spec.2 a ha
  let inOf (c : { c : H.Arc → Fin d // IsProper c }) (v : V) (k : Fin d) : inArcs H v :=
    (hunique_in c v k).choose
  have hinOf_c : ∀ (c : { c : H.Arc → Fin d // IsProper c }) v k, c.1 (inOf c v k).1 = k :=
    fun c v k => (hunique_in c v k).choose_spec.1
  have hinOf_uniq : ∀ (c : { c : H.Arc → Fin d // IsProper c }) v k (a : inArcs H v),
      c.1 a.1 = k → a = inOf c v k := fun c v k a ha =>
    (hunique_in c v k).choose_spec.2 a ha
  let σOf (c : { c : H.Arc → Fin d // IsProper c }) (k : Fin d) : Equiv.Perm V :=
    { toFun := fun u => H.head (outOf c u k).1
      invFun := fun v => H.tail (inOf c v k).1
      left_inv := fun u => by
        dsimp only
        have h1 : (⟨(outOf c u k).1, rfl⟩ : inArcs H (H.head (outOf c u k).1)) =
            inOf c (H.head (outOf c u k).1) k :=
          hinOf_uniq c (H.head (outOf c u k).1) k ⟨(outOf c u k).1, rfl⟩ (houtOf_c c u k)
        rw [← congrArg Subtype.val h1]
        exact (outOf c u k).2
      right_inv := fun v => by
        dsimp only
        have h1 : (⟨(inOf c v k).1, rfl⟩ : outArcs H (H.tail (inOf c v k).1)) =
            outOf c (H.tail (inOf c v k).1) k :=
          houtOf_uniq c (H.tail (inOf c v k).1) k ⟨(inOf c v k).1, rfl⟩ (hinOf_c c v k)
        rw [← congrArg Subtype.val h1]
        exact (inOf c v k).2 }
  have hinner_proper : ∀ c : { c : H.Arc → Fin d // IsProper c },
      (∑ π : TransitionSystem H,
        if (∀ a : H.Arc, c.1 (arcPerm H π a) = c.1 a) then
          (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0) =
      ∏ k : Fin d, (Equiv.Perm.sign (σOf c k) : ℤ) := by
    intro c
    let πc : TransitionSystem H := fun v =>
      { toFun := fun e => outOf c v (c.1 e.1)
        invFun := fun b => inOf c v (c.1 b.1)
        left_inv := fun e => by
          dsimp only; rw [houtOf_c]; exact (hinOf_uniq c v (c.1 e.1) e rfl).symm
        right_inv := fun b => by
          dsimp only; rw [hinOf_c]; exact (houtOf_uniq c v (c.1 b.1) b rfl).symm }
    have hπc_inv : ∀ a : H.Arc, c.1 (arcPerm H πc a) = c.1 a := fun a =>
      houtOf_c c (H.head a) (c.1 a)
    have hπc_uniq : ∀ π : TransitionSystem H,
        (∀ a : H.Arc, c.1 (arcPerm H π a) = c.1 a) → π = πc := by
      intro π hπ
      funext v; apply Equiv.ext; intro e
      have h1 : c.1 (π v e).1 = c.1 e.1 := by
        rcases e with ⟨a, rfl⟩; exact hπ a
      exact houtOf_uniq c v (c.1 e.1) (π v e) h1
    have hsum1 :
        (∑ π : TransitionSystem H,
          if (∀ a : H.Arc, c.1 (arcPerm H π a) = c.1 a) then
            (Equiv.Perm.sign (arcPerm H π) : ℤ) else 0) =
        (Equiv.Perm.sign (arcPerm H πc) : ℤ) := by
      rw [Finset.sum_eq_single πc]
      · exact if_pos hπc_inv
      · intro π _ hne
        exact if_neg (fun h => hne (hπc_uniq π h))
      · intro h; exact absurd (Finset.mem_univ πc) h
    rw [hsum1]
    -- Conjugate arcPerm H πc to fiberwise (k, u) ↦ (k, σOf c k u) via a ↦ (c a, tail a)
    let eArc : H.Arc ≃ Fin d × V :=
      { toFun := fun a => (c.1 a, H.tail a)
        invFun := fun p => (outOf c p.2 p.1).1
        left_inv := fun a => by
          have := houtOf_uniq c (H.tail a) (c.1 a) ⟨a, rfl⟩ rfl
          exact (congrArg Subtype.val this).symm
        right_inv := fun ⟨k, u⟩ => Prod.ext (houtOf_c c u k) (outOf c u k).2 }
    let fiberP : Equiv.Perm (Fin d × V) :=
      { toFun := fun p => (p.1, σOf c p.1 p.2)
        invFun := fun p => (p.1, (σOf c p.1).symm p.2)
        left_inv := fun p => by ext <;> simp
        right_inv := fun p => by ext <;> simp }
    have hconj : eArc.permCongr (arcPerm H πc) = fiberP := by
      apply Equiv.ext; rintro ⟨k, u⟩
      apply Prod.ext
      · change c.1 (arcPerm H πc (outOf c u k).1) = k
        rw [hπc_inv, houtOf_c]
      · change H.tail (arcPerm H πc (outOf c u k).1) = H.head (outOf c u k).1
        exact (outOf c (H.head (outOf c u k).1) (c.1 (outOf c u k).1)).2
    have hsign_eq : Equiv.Perm.sign (arcPerm H πc) = Equiv.Perm.sign fiberP := by
      rw [← hconj, Equiv.Perm.sign_permCongr]
    rw [hsign_eq, sign_fiberwise (σOf c)]
    push_cast; rfl
  simp_rw [hinner_proper]
  -- Step 6: Group proper colorings by σOf c and count each fiber = ∏ u v, (M u v)!
  rw [detPowCoeff_eq_sum (adjMatrix H) d, Finset.mul_sum]
  let IsValidTuple (σ : Fin d → Equiv.Perm V) : Prop :=
    ∀ u v : V, (Finset.univ.filter fun k : Fin d => σ k u = v).card = adjMatrix H u v
  have hσ_valid : ∀ c : { c : H.Arc → Fin d // IsProper c }, IsValidTuple (σOf c) := by
    intro c u v
    refine Finset.card_bij (fun k _ => (outOf c u k).1) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨(outOf c u k).2, hk⟩
    · intro k₁ _ k₂ _ heq
      have h1 := houtOf_c c u k₁
      have h2 := houtOf_c c u k₂
      rw [heq] at h1; exact h1.symm.trans h2
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      refine ⟨c.1 a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : (⟨a, ha.1⟩ : outArcs H u) = outOf c u (c.1 a) :=
          houtOf_uniq c u (c.1 a) ⟨a, ha.1⟩ rfl
        change H.head (outOf c u (c.1 a)).1 = v
        rw [← congrArg Subtype.val h1]; exact ha.2
      · have h1 : (⟨a, ha.1⟩ : outArcs H u) = outOf c u (c.1 a) :=
          houtOf_uniq c u (c.1 a) ⟨a, ha.1⟩ rfl
        exact (congrArg Subtype.val h1).symm
  have hfiber_card : ∀ σ : Fin d → Equiv.Perm V, IsValidTuple σ →
      (Finset.univ.filter fun c : { c : H.Arc → Fin d // IsProper c } => σOf c = σ).card =
        ∏ u : V, ∏ v : V, (adjMatrix H u v).factorial := by
    intro σ hσ
    -- Bijection with ∀ u v, {a // tail a = u ∧ head a = v} ≃ {k // σ k u = v}
    let Fiber := ∀ u v : V,
      { a : H.Arc // H.tail a = u ∧ H.head a = v } ≃ { k : Fin d // σ k u = v }
    have hcard_F : Fintype.card Fiber = ∏ u : V, ∏ v : V, (adjMatrix H u v).factorial := by
      simp only [Fiber, Fintype.card_pi]
      refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => ?_
      have h1 : Fintype.card { a : H.Arc // H.tail a = u ∧ H.head a = v } = adjMatrix H u v := by
        rw [Fintype.card_subtype]; rfl
      have h2 : Fintype.card { k : Fin d // σ k u = v } = adjMatrix H u v := by
        rw [Fintype.card_subtype]; exact hσ u v
      have e1 := Fintype.equivFinOfCardEq h1
      have e2 := Fintype.equivFinOfCardEq h2
      have hcard_equiv : Fintype.card
          ({ a : H.Arc // H.tail a = u ∧ H.head a = v } ≃ { k : Fin d // σ k u = v }) =
          Fintype.card (Equiv.Perm (Fin (adjMatrix H u v))) :=
        Fintype.card_congr (Equiv.equivCongr e1 e2)
      rw [hcard_equiv, Fintype.card_perm, Fintype.card_fin]
    rw [← hcard_F, ← Fintype.card_subtype]
    refine Fintype.card_congr
      { toFun := fun ⟨c, hc⟩ u v =>
          { toFun := fun a => ⟨c.1 a.1, by
              have h1 : (⟨a.1, a.2.1⟩ : outArcs H u) = outOf c u (c.1 a.1) :=
                houtOf_uniq c u (c.1 a.1) ⟨a.1, a.2.1⟩ rfl
              rw [← hc]
              change H.head (outOf c u (c.1 a.1)).1 = v
              rw [← congrArg Subtype.val h1]; exact a.2.2⟩
            invFun := fun k => ⟨(outOf c u k.1).1, (outOf c u k.1).2, by
              have : H.head (outOf c u k.1).1 = σOf c k.1 u := rfl
              rw [this, hc]; exact k.2⟩
            left_inv := fun a => by
              apply Subtype.ext
              exact (congrArg Subtype.val (houtOf_uniq c u (c.1 a.1) ⟨a.1, a.2.1⟩ rfl)).symm
            right_inv := fun k => by apply Subtype.ext; exact houtOf_c c u k.1 }
        invFun := fun f =>
          let cfun : H.Arc → Fin d := fun a => (f (H.tail a) (H.head a) ⟨a, rfl, rfl⟩).1
          have hprop : IsProper cfun := by
            intro v k
            constructor
            · rw [Finset.card_eq_one]
              let u := (σ k).symm v
              let a0 := (f u v).symm ⟨k, (σ k).apply_symm_apply v⟩
              refine ⟨⟨a0.1, a0.2.2⟩, ?_⟩
              ext ⟨a, ha⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
              constructor
              · intro hca
                have hu : H.tail a = u := by
                  have hspec := (f (H.tail a) v ⟨a, rfl, ha⟩).2
                  have h1 : σ k (H.tail a) = v := by
                    have hck : (f (H.tail a) v ⟨a, rfl, ha⟩).1 = k := by
                      have hsub : ∀ {v' : V} (hv' : H.head a = v'),
                          (f (H.tail a) v' ⟨a, rfl, hv'⟩).1 = cfun a := by
                        intro v' hv'; subst hv'; rfl
                      rw [hsub ha]; exact hca
                    rw [← hck]; exact hspec
                  exact (σ k).injective (h1.trans ((σ k).apply_symm_apply v).symm)
                apply Subtype.ext
                have h2 : (⟨a, hu, ha⟩ : { a : H.Arc // H.tail a = u ∧ H.head a = v }) = a0 := by
                  apply (f u v).injective
                  rw [(f u v).apply_symm_apply]
                  apply Subtype.ext
                  have hsub : ∀ {u' v' : V} (hu' : H.tail a = u') (hv' : H.head a = v'),
                      (f u' v' ⟨a, hu', hv'⟩).1 = cfun a := by
                    intro u' v' hu' hv'; subst hu'; subst hv'; rfl
                  rw [hsub hu ha]; exact hca
                exact congrArg (fun x : { a : H.Arc // H.tail a = u ∧ H.head a = v } => x.1) h2
              · intro heq
                have hval : a = a0.1 := congrArg Subtype.val heq
                subst hval
                have hsub : ∀ {u' v' : V} (hu' : H.tail a0.1 = u') (hv' : H.head a0.1 = v'),
                    (f u' v' ⟨a0.1, hu', hv'⟩).1 = cfun a0.1 := by
                  intro u' v' hu' hv'; subst hu'; subst hv'; rfl
                rw [← hsub a0.2.1 a0.2.2]
                exact congrArg Subtype.val ((f u v).apply_symm_apply ⟨k, (σ k).apply_symm_apply v⟩)
            · rw [Finset.card_eq_one]
              let w := σ k v
              let a0 := (f v w).symm ⟨k, rfl⟩
              refine ⟨⟨a0.1, a0.2.1⟩, ?_⟩
              ext ⟨a, ha⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
              constructor
              · intro hca
                have hw : H.head a = w := by
                  have hspec := (f v (H.head a) ⟨a, ha, rfl⟩).2
                  have hck : (f v (H.head a) ⟨a, ha, rfl⟩).1 = k := by
                    have hsub : ∀ {u' : V} (hu' : H.tail a = u'),
                        (f u' (H.head a) ⟨a, hu', rfl⟩).1 = cfun a := by
                      intro u' hu'; subst hu'; rfl
                    rw [hsub ha]; exact hca
                  exact hspec.symm.trans (congrArg (fun j => σ j v) hck)
                apply Subtype.ext
                have h2 : (⟨a, ha, hw⟩ : { a : H.Arc // H.tail a = v ∧ H.head a = w }) = a0 := by
                  apply (f v w).injective
                  rw [(f v w).apply_symm_apply]
                  apply Subtype.ext
                  have hsub : ∀ {u' v' : V} (hu' : H.tail a = u') (hv' : H.head a = v'),
                      (f u' v' ⟨a, hu', hv'⟩).1 = cfun a := by
                    intro u' v' hu' hv'; subst hu'; subst hv'; rfl
                  rw [hsub ha hw]; exact hca
                exact congrArg (fun x : { a : H.Arc // H.tail a = v ∧ H.head a = w } => x.1) h2
              · intro heq
                have hval : a = a0.1 := congrArg Subtype.val heq
                subst hval
                have hsub : ∀ {u' v' : V} (hu' : H.tail a0.1 = u') (hv' : H.head a0.1 = v'),
                    (f u' v' ⟨a0.1, hu', hv'⟩).1 = cfun a0.1 := by
                  intro u' v' hu' hv'; subst hu'; subst hv'; rfl
                rw [← hsub a0.2.1 a0.2.2]
                exact congrArg Subtype.val ((f v w).apply_symm_apply ⟨k, rfl⟩)
          ⟨⟨cfun, hprop⟩, by
            funext k; apply Equiv.ext; intro u
            let a0 := (f u (σ k u)).symm ⟨k, rfl⟩
            have hca0 : cfun a0.1 = k := by
              have hsub : ∀ {u' v' : V} (hu' : H.tail a0.1 = u') (hv' : H.head a0.1 = v'),
                  (f u' v' ⟨a0.1, hu', hv'⟩).1 = cfun a0.1 := by
                intro u' v' hu' hv'; subst hu'; subst hv'; rfl
              rw [← hsub a0.2.1 a0.2.2]
              exact congrArg Subtype.val ((f u (σ k u)).apply_symm_apply ⟨k, rfl⟩)
            have h1 : (⟨a0.1, a0.2.1⟩ : outArcs H u) = outOf ⟨cfun, hprop⟩ u k :=
              houtOf_uniq ⟨cfun, hprop⟩ u k ⟨a0.1, a0.2.1⟩ hca0
            change H.head (outOf ⟨cfun, hprop⟩ u k).1 = σ k u
            rw [← congrArg Subtype.val h1]; exact a0.2.2⟩
        left_inv := fun ⟨⟨c, hprop⟩, hc⟩ => by
          apply Subtype.ext; apply Subtype.ext; funext a; rfl
        right_inv := fun f => by
          funext u v; apply Equiv.ext; intro a; apply Subtype.ext
          have hsub : ∀ {u' v' : V} (hu' : H.tail a.1 = u') (hv' : H.head a.1 = v'),
              (f u' v' ⟨a.1, hu', hv'⟩).1 = (f (H.tail a.1) (H.head a.1) ⟨a.1, rfl, rfl⟩).1 := by
            intro u' v' hu' hv'; subst hu'; subst hv'; rfl
          exact (hsub a.2.1 a.2.2).symm }
  rw [← Finset.sum_fiberwise_of_maps_to (g := σOf) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : IsValidTuple σ
  · rw [if_pos hσ]
    have hconst : ∑ c ∈ Finset.univ.filter (fun c : { c : H.Arc → Fin d // IsProper c } => σOf c = σ),
        ∏ k : Fin d, (Equiv.Perm.sign (σOf c k) : ℤ) =
        ∑ _c ∈ Finset.univ.filter (fun c : { c : H.Arc → Fin d // IsProper c } => σOf c = σ),
          ∏ k : Fin d, (Equiv.Perm.sign (σ k) : ℤ) :=
      Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.mp hc).2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, hfiber_card σ hσ]
    push_cast; rfl
  · rw [if_neg hσ, mul_zero]
    refine Finset.sum_eq_zero fun c hc => ?_
    exfalso
    have h1 := hσ_valid c
    rw [(Finset.mem_filter.mp hc).2] at h1
    exact hσ h1

/-- **Lemma 3.2**: For even `n`, `j(K_n^∘; -n) = [x^J] det(X)^n = (-1)^(n/2) Δ_n`. -/
theorem lem_3_2_quad_latin_proved (n : ℕ) (heven : Even n) :
    (circuitPoly (completeLoopDigraph n)).eval (-(n : ℤ)) =
      detPowCoeff (allOnesMatrix (Fin n)) n ∧
    detPowCoeff (allOnesMatrix (Fin n)) n = (-1 : ℤ) ^ (n / 2) * delta n := by
  classical
  have hM : adjMatrix (completeLoopDigraph n) = allOnesMatrix (Fin n) :=
    adjMatrix_ofMatrix (allOnesMatrix (Fin n))
  have hreg : IsRegular (completeLoopDigraph n) n := by
    rw [isRegular_iff_adjMatrix, hM]
    simp [allOnesMatrix]
  have hpart1 : (circuitPoly (completeLoopDigraph n)).eval (-(n : ℤ)) =
      detPowCoeff (allOnesMatrix (Fin n)) n := by
    have h1 := lem_3_1_quad_fact_proved (completeLoopDigraph n) n hreg
    rw [hM, Fintype.card_fin] at h1
    have hsign : (-1 : ℤ) ^ (n * n) = 1 := by
      rcases heven with ⟨k, rfl⟩
      have : (k + k) * (k + k) = 2 * (2 * k * k) := by ring
      rw [this, pow_mul]; norm_num
    have hprod : (∏ u : Fin n, ∏ v : Fin n, ((allOnesMatrix (Fin n) u v).factorial : ℤ)) = 1 := by
      simp [allOnesMatrix]
    rw [h1, hsign, hprod, mul_one, one_mul]
  refine ⟨hpart1, ?_⟩
  rw [detPowCoeff_eq_sum (allOnesMatrix (Fin n)) n, delta_eq_sum]
  -- Bijection between LatinSquare n and valid n-tuples σ : Fin n → Equiv.Perm (Fin n)
  let IsValid (σ : Fin n → Equiv.Perm (Fin n)) : Prop :=
    ∀ u v : Fin n, (Finset.univ.filter fun k : Fin n => σ k u = v).card = 1
  trans (∑ σ : { σ : Fin n → Equiv.Perm (Fin n) // IsValid σ },
      ∏ k : Fin n, (Equiv.Perm.sign (σ.1 k) : ℤ))
  · have hfilt_eq :
        (∑ σ : Fin n → Equiv.Perm (Fin n),
          if (∀ u v : Fin n, (Finset.univ.filter fun k : Fin n => σ k u = v).card =
              allOnesMatrix (Fin n) u v)
          then ∏ k : Fin n, (Equiv.Perm.sign (σ k) : ℤ) else 0) =
        ∑ σ ∈ Finset.univ.filter IsValid, ∏ k : Fin n, (Equiv.Perm.sign (σ k) : ℤ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : IsValid σ
      · have h' : ∀ u v : Fin n, (Finset.univ.filter fun k : Fin n => σ k u = v).card =
            allOnesMatrix (Fin n) u v := h
        rw [if_pos h', if_pos h]
      · have h' : ¬ (∀ u v : Fin n, (Finset.univ.filter fun k : Fin n => σ k u = v).card =
            allOnesMatrix (Fin n) u v) := h
        rw [if_neg h', if_neg h]
    trans (∑ σ ∈ Finset.univ.filter IsValid, ∏ k : Fin n, (Equiv.Perm.sign (σ k) : ℤ))
    · convert hfilt_eq
    · exact Finset.sum_subtype (Finset.univ.filter IsValid) (fun _ => by simp)
        (fun σ => ∏ k : Fin n, (Equiv.Perm.sign (σ k) : ℤ))
  have huniq : ∀ (σ : { σ : Fin n → Equiv.Perm (Fin n) // IsValid σ }) (u v : Fin n),
      ∃! k : Fin n, σ.1 k u = v := by
    intro σ u v
    rcases Finset.card_eq_one.mp (σ.2 u v) with ⟨k, hk⟩
    refine ⟨k, ?_, fun k' hk' => ?_⟩
    · have : k ∈ Finset.univ.filter (fun j : Fin n => σ.1 j u = v) := by rw [hk]; simp
      exact (Finset.mem_filter.mp this).2
    · have : k' ∈ ({k} : Finset (Fin n)) := by
        rw [← hk]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩
      exact Finset.mem_singleton.mp this
  let eLS : LatinSquare n ≃ { σ : Fin n → Equiv.Perm (Fin n) // IsValid σ } :=
    { toFun := fun L => ⟨symPerm L, fun u v => by
        rw [Finset.card_eq_one]
        refine ⟨L.entry u v, ?_⟩
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hk
          have h1 : L.entry u (symPerm L k u) = k := (rowPerm L u).apply_symm_apply k
          rw [hk] at h1; exact h1.symm
        · rintro rfl
          exact (rowPerm L u).symm_apply_apply v⟩
      invFun := fun σ =>
        { entry := fun u v => (huniq σ u v).choose
          row_bijective := fun u => by
            refine Finite.injective_iff_bijective.mp fun v₁ v₂ hv => ?_
            have h1 := (huniq σ u v₁).choose_spec.1
            have h2 := (huniq σ u v₂).choose_spec.1
            rw [hv] at h1; exact h1.symm.trans h2
          col_bijective := fun v => by
            refine Finite.injective_iff_bijective.mp fun u₁ u₂ hu => ?_
            have h1 := (huniq σ u₁ v).choose_spec.1
            have h2 := (huniq σ u₂ v).choose_spec.1
            rw [hu] at h1; exact (σ.1 _).injective (h1.trans h2.symm) }
      left_inv := fun L => by
        apply LatinSquare.ext; funext u v
        exact ((huniq ⟨symPerm L, _⟩ u v).choose_spec.2 (L.entry u v)
          ((rowPerm L u).symm_apply_apply v)).symm
      right_inv := fun σ => by
        apply Subtype.ext; funext k; apply Equiv.ext; intro u
        let Lσ : LatinSquare n :=
          { entry := fun u v => (huniq σ u v).choose
            row_bijective := fun u => by
              refine Finite.injective_iff_bijective.mp fun v₁ v₂ hv => ?_
              have h1' := (huniq σ u v₁).choose_spec.1
              have h2' := (huniq σ u v₂).choose_spec.1
              rw [hv] at h1'; exact h1'.symm.trans h2'
            col_bijective := fun v => by
              refine Finite.injective_iff_bijective.mp fun u₁ u₂ hu => ?_
              have h1' := (huniq σ u₁ v).choose_spec.1
              have h2' := (huniq σ u₂ v).choose_spec.1
              rw [hu] at h1'; exact (σ.1 _).injective (h1'.trans h2'.symm) }
        have h1 : (huniq σ u (σ.1 k u)).choose = k :=
          ((huniq σ u (σ.1 k u)).choose_spec.2 k rfl).symm
        change (rowPerm Lσ u).symm k = σ.1 k u
        apply (rowPerm Lσ u).injective
        rw [(rowPerm Lσ u).apply_symm_apply]
        exact h1.symm }
  rw [← Fintype.sum_equiv eLS (fun L => ∏ k : Fin n, (Equiv.Perm.sign ((eLS L).1 k) : ℤ))
    (fun σ => ∏ k : Fin n, (Equiv.Perm.sign (σ.1 k) : ℤ)) (fun _ => rfl), Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  have hprod_sym : (∏ k : Fin n, (Equiv.Perm.sign ((eLS L).1 k) : ℤ)) = (symSign L : ℤ) := by
    change (∏ k : Fin n, (Equiv.Perm.sign (symPerm L k) : ℤ)) = (symSign L : ℤ)
    unfold symSign; push_cast; rfl
  have hjan := eq_janssen_proved n L
  have hsq : squareSign L * squareSign L = 1 := by
    rcases Int.units_eq_one_or (squareSign L) with h | h <;> simp [h]
  have hsym : symSign L = (-1 : ℤˣ) ^ (n * (n - 1) / 2) * squareSign L := by
    unfold squareSign at hsq ⊢
    calc symSign L = (rowSign L * colSign L) * (rowSign L * colSign L * symSign L) := by
            have : (rowSign L * colSign L) * (rowSign L * colSign L) = 1 := hsq
            calc symSign L = 1 * symSign L := (one_mul _).symm
              _ = ((rowSign L * colSign L) * (rowSign L * colSign L)) * symSign L := by rw [this]
              _ = (rowSign L * colSign L) * (rowSign L * colSign L * symSign L) := by ac_rfl
      _ = (rowSign L * colSign L) * (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by rw [hjan]
      _ = (-1 : ℤˣ) ^ (n * (n - 1) / 2) * (rowSign L * colSign L) := by ac_rfl
  have hpar : (-1 : ℤ) ^ (n * (n - 1) / 2) = (-1 : ℤ) ^ (n / 2) := by
    rcases heven with ⟨k, rfl⟩
    cases k with
    | zero => simp
    | succ m =>
      have h1 : (m + 1 + (m + 1)) * (m + 1 + (m + 1) - 1) / 2 = (m + 1) * (2 * m + 1) := by
        have hsub : m + 1 + (m + 1) - 1 = 2 * m + 1 := by omega
        rw [hsub]
        have : (m + 1 + (m + 1)) * (2 * m + 1) = 2 * ((m + 1) * (2 * m + 1)) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
      have h2 : (m + 1 + (m + 1)) / 2 = m + 1 := by omega
      rw [h1, h2]
      have h3 : (m + 1) * (2 * m + 1) = (m + 1) + 2 * (m * (m + 1)) := by ring
      rw [h3, pow_add, pow_mul]; norm_num
  have hsymZ : (symSign L : ℤ) = (-1 : ℤ) ^ (n / 2) * (squareSign L : ℤ) := by
    rw [hsym, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hpar]
  have h1 : eLS.symm (eLS L) = L := eLS.symm_apply_apply L
  simpa [hprod_sym, hsymZ, eLS] using (hprod_sym.trans hsymZ)

/-! ### Part 4: Lemma 5.1 (`lem_5_1_quad_split`) — General Subset Elimination -/

/-- For a `d`-regular digraph `H` and subset `S`, `walkEnd` induces a bijection from exit arcs
(`S → T`) to entry arcs (`T → S`). -/
lemma walkEnd_bijective {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) (hreg : IsRegular H d) (S : Finset V)
    (πT : PartialTransition H S) :
    let Ex := { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S }
    let En := { a : H.Arc // H.tail a ∉ S ∧ H.head a ∈ S }
    ∃ f : Ex ≃ En, ∀ e : Ex, (f e).1 = (walkEnd H S πT e).1 := by
  classical
  let Ex := { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S }
  let En := { a : H.Arc // H.tail a ∉ S ∧ H.head a ∈ S }
  have hwalk_tail : ∀ e : Ex, H.tail (walkEnd H S πT e).1 ∉ S := by
    intro e
    unfold walkEnd
    dsimp only
    set k := Nat.find (exit_reaches_S H S πT e.1 e.2.1 e.2.2)
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      have hspec : H.head ((partialStep H S πT)^[k] e.1) ∈ S :=
        Nat.find_spec (exit_reaches_S H S πT e.1 e.2.1 e.2.2)
      rw [hk0] at hspec
      exact e.2.2 hspec
    have hprev : H.head ((partialStep H S πT)^[k - 1] e.1) ∉ S :=
      Nat.find_min (exit_reaches_S H S πT e.1 e.2.1 e.2.2) (by omega)
    have hstep : (partialStep H S πT)^[k] e.1 =
        partialStep H S πT ((partialStep H S πT)^[k - 1] e.1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk_pos, Function.iterate_succ_apply']
    change H.tail ((partialStep H S πT)^[k] e.1) ∉ S
    rw [hstep]
    simp only [partialStep, dif_pos hprev]
    have ht := (πT ⟨H.head ((partialStep H S πT)^[k - 1] e.1), hprev⟩
      ⟨(partialStep H S πT)^[k - 1] e.1, rfl⟩).2
    rw [ht]; exact hprev
  let toEn : Ex → En := fun e => ⟨(walkEnd H S πT e).1, hwalk_tail e, (walkEnd H S πT e).2⟩
  have hinj : Function.Injective toEn := by
    intro e₁ e₂ heq
    have hval : (walkEnd H S πT e₁).1 = (walkEnd H S πT e₂).1 :=
      congrArg (fun x : En => x.1) heq
    unfold walkEnd at hval
    dsimp only at hval
    set k₁ := Nat.find (exit_reaches_S H S πT e₁.1 e₁.2.1 e₁.2.2)
    set k₂ := Nat.find (exit_reaches_S H S πT e₂.1 e₂.2.1 e₂.2.2)
    have hmin₁ : ∀ i < k₁, H.head ((partialStep H S πT)^[i] e₁.1) ∉ S := fun i hi =>
      Nat.find_min (exit_reaches_S H S πT e₁.1 e₁.2.1 e₁.2.2) hi
    have hmin₂ : ∀ i < k₂, H.head ((partialStep H S πT)^[i] e₂.1) ∉ S := fun i hi =>
      Nat.find_min (exit_reaches_S H S πT e₂.1 e₂.2.1 e₂.2.2) hi
    have hback : ∀ t, t ≤ k₁ → t ≤ k₂ →
        (partialStep H S πT)^[k₁ - t] e₁.1 = (partialStep H S πT)^[k₂ - t] e₂.1 := by
      intro t
      induction t with
      | zero => intro _ _; simpa using hval
      | succ t ih =>
        intro ht₁ ht₂
        have hprev := ih (by omega) (by omega)
        have h1 : k₁ - t = (k₁ - (t + 1)) + 1 := by omega
        have h2 : k₂ - t = (k₂ - (t + 1)) + 1 := by omega
        rw [h1, h2, Function.iterate_succ_apply', Function.iterate_succ_apply'] at hprev
        exact partialStep_inj_on_outside H S πT (hmin₁ _ (by omega)) (hmin₂ _ (by omega)) hprev
    have hno_lt : ∀ (a b : Ex) (ka kb : ℕ),
        (∀ i < kb, H.head ((partialStep H S πT)^[i] b.1) ∉ S) →
        (partialStep H S πT)^[0] a.1 = (partialStep H S πT)^[kb - ka] b.1 →
        ka < kb → False := by
      intro a b ka kb hminb h0 hlt
      have hpos : 0 < kb - ka := by omega
      have hprev_out : H.head ((partialStep H S πT)^[kb - ka - 1] b.1) ∉ S :=
        hminb (kb - ka - 1) (by omega)
      have hstep : (partialStep H S πT)^[kb - ka] b.1 =
          partialStep H S πT ((partialStep H S πT)^[kb - ka - 1] b.1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hpos, Function.iterate_succ_apply']
      rw [hstep, Function.iterate_zero_apply, partialStep, dif_pos hprev_out] at h0
      have ht : H.tail ((πT ⟨H.head ((partialStep H S πT)^[kb - ka - 1] b.1), hprev_out⟩
        ⟨(partialStep H S πT)^[kb - ka - 1] b.1, rfl⟩).1) =
        H.head ((partialStep H S πT)^[kb - ka - 1] b.1) :=
        (πT ⟨H.head ((partialStep H S πT)^[kb - ka - 1] b.1), hprev_out⟩
          ⟨(partialStep H S πT)^[kb - ka - 1] b.1, rfl⟩).2
      rw [← h0] at ht
      exact hprev_out (by rw [← ht]; exact a.2.1)
    have hk_eq : k₁ = k₂ := by
      rcases lt_trichotomy k₁ k₂ with hlt | heq' | hgt
      · exfalso
        have h0 := hback k₁ (le_refl k₁) (le_of_lt hlt)
        rw [Nat.sub_self] at h0
        exact hno_lt e₁ e₂ k₁ k₂ hmin₂ h0 hlt
      · exact heq'
      · exfalso
        have h0 := (hback k₂ (le_of_lt hgt) (le_refl k₂)).symm
        rw [Nat.sub_self] at h0
        exact hno_lt e₂ e₁ k₂ k₁ hmin₁ h0 hgt
    have h0 := hback k₁ (le_refl k₁) (hk_eq ▸ le_refl k₁)
    rw [Nat.sub_self, ← hk_eq, Nat.sub_self] at h0
    exact Subtype.ext h0
  -- Compare cardinalities of Ex and En using d-regularity
  have hcard_eq : Fintype.card Ex = Fintype.card En := by
    have h1 : ∑ v ∈ S, (Finset.univ.filter fun a : H.Arc => H.tail a = v).card =
        (Finset.univ.filter fun a : H.Arc => H.tail a ∈ S ∧ H.head a ∈ S).card +
        (Finset.univ.filter fun a : H.Arc => H.tail a ∈ S ∧ H.head a ∉ S).card := by
      have hbi : (Finset.univ.filter fun a : H.Arc => H.tail a ∈ S).card =
          ∑ v ∈ S, (Finset.univ.filter fun a : H.Arc => H.tail a = v).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext a; simp
        · intro u _ v _ hne
          exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
            hne ((Finset.mem_filter.mp ha₁).2.symm.trans (Finset.mem_filter.mp ha₂).2)
      rw [← hbi, ← Finset.card_union_of_disjoint]
      · congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        tauto
      · exact Finset.disjoint_filter.mpr fun a _ h₁ h₂ => h₂.2 h₁.2
    have h2 : ∑ v ∈ S, (Finset.univ.filter fun a : H.Arc => H.head a = v).card =
        (Finset.univ.filter fun a : H.Arc => H.tail a ∈ S ∧ H.head a ∈ S).card +
        (Finset.univ.filter fun a : H.Arc => H.tail a ∉ S ∧ H.head a ∈ S).card := by
      have hbi : (Finset.univ.filter fun a : H.Arc => H.head a ∈ S).card =
          ∑ v ∈ S, (Finset.univ.filter fun a : H.Arc => H.head a = v).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext a; simp
        · intro u _ v _ hne
          exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
            hne ((Finset.mem_filter.mp ha₁).2.symm.trans (Finset.mem_filter.mp ha₂).2)
      rw [← hbi, ← Finset.card_union_of_disjoint]
      · congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        tauto
      · exact Finset.disjoint_filter.mpr fun a _ h₁ h₂ => h₂.1 h₁.1
    simp_rw [hreg.2, Finset.sum_const, smul_eq_mul] at h1
    simp_rw [hreg.1, Finset.sum_const, smul_eq_mul] at h2
    rw [Fintype.card_subtype, Fintype.card_subtype]
    omega
  exact ⟨Equiv.ofBijective toEn ((Fintype.bijective_iff_injective_and_card toEn).mpr ⟨hinj, hcard_eq⟩),
    fun _ => rfl⟩

/-- **Lemma 5.1**: Subset elimination `V = S ⊔ T` (`S ≠ ∅`):
`j(H; x) = ∑_{π_T} x^{cyc_T} j(H_{π_T}; x)`, and each `H_{π_T}` is `d`-regular on `S`
with matrix `M_S + R` whose row/column sums equal exit/entry counts. -/
theorem lem_5_1_quad_split_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) (hreg : IsRegular H d) (S : Finset V) (_hS : S.Nonempty) :
    circuitPoly H =
      ∑ πT : PartialTransition H S,
        Polynomial.X ^ cycInsideT H S πT * circuitPoly (splitDigraph H S πT) ∧
    ∀ πT : PartialTransition H S,
      IsRegular (splitDigraph H S πT) d ∧
      ∃ R : Matrix { v : V // v ∈ S } { v : V // v ∈ S } ℕ,
        adjMatrix (splitDigraph H S πT) =
          Matrix.of (fun u v => adjMatrix H u.1 v.1) + R ∧
        (∀ u : { v : V // v ∈ S },
          ∑ v, R u v = (Finset.univ.filter fun a : H.Arc => H.tail a = u.1 ∧ H.head a ∉ S).card) ∧
        (∀ v : { v : V // v ∈ S },
          ∑ u, R u v = (Finset.univ.filter fun a : H.Arc => H.tail a ∉ S ∧ H.head a = v.1).card) := by
  classical
  -- Helper: for any πT, construct in/out bijections between splitDigraph H S πT and H at each v ∈ S
  let fWalkOf (πT : PartialTransition H S) :
      { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } ≃ { a : H.Arc // H.tail a ∉ S ∧ H.head a ∈ S } :=
    (walkEnd_bijective H d hreg S πT).choose
  have hfWalkOf : ∀ (πT : PartialTransition H S) (e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S }),
      (fWalkOf πT e).1 = (walkEnd H S πT e).1 :=
    fun πT => (walkEnd_bijective H d hreg S πT).choose_spec
  let eInOf (πT : PartialTransition H S) (v : { v : V // v ∈ S }) :
      inArcs (splitDigraph H S πT) v ≃ inArcs H v.1 :=
    { toFun := fun b => match b with
        | ⟨Sum.inl a, hb⟩ => ⟨a.1, congrArg Subtype.val hb⟩
        | ⟨Sum.inr e, hb⟩ => ⟨(fWalkOf πT e).1, by rw [hfWalkOf]; exact congrArg Subtype.val hb⟩
      invFun := fun a =>
        if ht : H.tail a.1 ∈ S then
          ⟨Sum.inl ⟨a.1, ht, a.2.symm ▸ v.2⟩, Subtype.ext a.2⟩
        else
          let e := (fWalkOf πT).symm ⟨a.1, ht, a.2.symm ▸ v.2⟩
          ⟨Sum.inr e, Subtype.ext (by
            change H.head (walkEnd H S πT e).1 = v.1
            have h1 : (walkEnd H S πT e).1 = a.1 := by
              rw [← hfWalkOf πT e, (fWalkOf πT).apply_symm_apply]
            rw [h1]; exact a.2)⟩
      left_inv := fun b => by
        rcases b with ⟨⟨a, ha1, ha2⟩ | e, hb⟩
        · apply Subtype.ext; dsimp only; rw [dif_pos ha1]
        · apply Subtype.ext; dsimp only
          have hnt : H.tail (fWalkOf πT e).1 ∉ S := (fWalkOf πT e).2.1
          rw [dif_neg hnt]
          exact congrArg Sum.inr ((fWalkOf πT).symm_apply_apply e)
      right_inv := fun a => by
        apply Subtype.ext; dsimp only
        by_cases ht : H.tail a.1 ∈ S
        · rw [dif_pos ht]
        · rw [dif_neg ht]
          change (fWalkOf πT ((fWalkOf πT).symm ⟨a.1, ht, a.2.symm ▸ v.2⟩)).1 = a.1
          exact congrArg Subtype.val ((fWalkOf πT).apply_symm_apply ⟨a.1, ht, a.2.symm ▸ v.2⟩) }
  let eOutOf (πT : PartialTransition H S) (v : { v : V // v ∈ S }) :
      outArcs (splitDigraph H S πT) v ≃ outArcs H v.1 :=
    { toFun := fun b => match b with
        | ⟨Sum.inl a, hb⟩ => ⟨a.1, congrArg Subtype.val hb⟩
        | ⟨Sum.inr e, hb⟩ => ⟨e.1, congrArg Subtype.val hb⟩
      invFun := fun a =>
        if hh : H.head a.1 ∈ S then
          ⟨Sum.inl ⟨a.1, a.2.symm ▸ v.2, hh⟩, Subtype.ext a.2⟩
        else
          ⟨Sum.inr ⟨a.1, a.2.symm ▸ v.2, hh⟩, Subtype.ext a.2⟩
      left_inv := fun b => by
        rcases b with ⟨⟨a, ha1, ha2⟩ | ⟨e, he1, he2⟩, hb⟩
        · apply Subtype.ext; dsimp only; rw [dif_pos ha2]
        · apply Subtype.ext; dsimp only; rw [dif_neg he2]
      right_inv := fun a => by
        apply Subtype.ext; dsimp only
        by_cases hh : H.head a.1 ∈ S
        · rw [dif_pos hh]
        · rw [dif_neg hh] }
  have hsplit_prop : ∀ πT : PartialTransition H S,
      IsRegular (splitDigraph H S πT) d ∧
      ∃ R : Matrix { v : V // v ∈ S } { v : V // v ∈ S } ℕ,
        adjMatrix (splitDigraph H S πT) =
          Matrix.of (fun u v => adjMatrix H u.1 v.1) + R ∧
        (∀ u : { v : V // v ∈ S },
          ∑ v, R u v = (Finset.univ.filter fun a : H.Arc => H.tail a = u.1 ∧ H.head a ∉ S).card) ∧
        (∀ v : { v : V // v ∈ S },
          ∑ u, R u v = (Finset.univ.filter fun a : H.Arc => H.tail a ∉ S ∧ H.head a = v.1).card) := by
    intro πT
    let fWalk := fWalkOf πT
    have hfWalk := hfWalkOf πT
    let eIn := eInOf πT
    let eOut := eOutOf πT
    have hregS : IsRegular (splitDigraph H S πT) d := by
      constructor
      · intro v
        rw [← Fintype.card_subtype, Fintype.card_congr (eIn v), Fintype.card_subtype]
        exact hreg.1 v.1
      · intro v
        rw [← Fintype.card_subtype, Fintype.card_congr (eOut v), Fintype.card_subtype]
        exact hreg.2 v.1
    let R : Matrix { v : V // v ∈ S } { v : V // v ∈ S } ℕ :=
      Matrix.of fun u v =>
        (Finset.univ.filter fun e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } =>
          H.tail e.1 = u.1 ∧ H.head (walkEnd H S πT e).1 = v.1).card
    have hM_eq : adjMatrix (splitDigraph H S πT) =
        Matrix.of (fun u v => adjMatrix H u.1 v.1) + R := by
      ext u v
      change (Finset.univ.filter fun b : (splitDigraph H S πT).Arc =>
        (splitDigraph H S πT).tail b = u ∧ (splitDigraph H S πT).head b = v).card =
        adjMatrix H u.1 v.1 + R u v
      let A1 := Finset.univ.filter fun a : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∈ S } =>
        H.tail a.1 = u.1 ∧ H.head a.1 = v.1
      let A2 := Finset.univ.filter fun e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } =>
        H.tail e.1 = u.1 ∧ H.head (walkEnd H S πT e).1 = v.1
      have hcard_sum :
          (Finset.univ.filter fun b : (splitDigraph H S πT).Arc =>
            (splitDigraph H S πT).tail b = u ∧ (splitDigraph H S πT).head b = v).card =
          A1.card + A2.card := by
        rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_subtype,
          ← Fintype.card_sum]
        refine Fintype.card_congr
          { toFun := fun b => match b with
              | ⟨Sum.inl a, hb⟩ => Sum.inl ⟨a, congrArg Subtype.val hb.1, congrArg Subtype.val hb.2⟩
              | ⟨Sum.inr e, hb⟩ => Sum.inr ⟨e, congrArg Subtype.val hb.1, congrArg Subtype.val hb.2⟩
            invFun := fun s => match s with
              | Sum.inl ⟨a, ha⟩ => ⟨Sum.inl a, Subtype.ext ha.1, Subtype.ext ha.2⟩
              | Sum.inr ⟨e, he⟩ => ⟨Sum.inr e, Subtype.ext he.1, Subtype.ext he.2⟩
            left_inv := fun b => by rcases b with ⟨_ | _, _⟩ <;> rfl
            right_inv := fun s => by rcases s with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl }
      rw [hcard_sum]
      congr 1
      refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
      · intro a ha
        simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha
      · intro a₁ _ a₂ _ h; exact Subtype.ext h
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ⟨⟨a, ha.1.symm ▸ u.2, ha.2.symm ▸ v.2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
    have hrowR : ∀ u : { v : V // v ∈ S },
        ∑ v, R u v = (Finset.univ.filter fun a : H.Arc => H.tail a = u.1 ∧ H.head a ∉ S).card := by
      intro u
      have h1 : ∑ v : { v : V // v ∈ S }, R u v =
          (Finset.univ.filter fun e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } =>
            H.tail e.1 = u.1).card := by
        simp only [R, Matrix.of_apply]
        rw [← Finset.card_biUnion]
        · congr 1; ext e
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨⟨H.head (walkEnd H S πT e).1, (walkEnd H S πT e).2⟩, h, rfl⟩⟩
        · intro v₁ _ v₂ _ hne
          exact Finset.disjoint_left.mpr fun e he₁ he₂ =>
            hne (Subtype.ext ((Finset.mem_filter.mp he₁).2.2.symm.trans (Finset.mem_filter.mp he₂).2.2))
      rw [h1]
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2, e.2.2⟩
      · intro e₁ _ e₂ _ h; exact Subtype.ext h
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ⟨⟨a, ha.1.symm ▸ u.2, ha.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1⟩, rfl⟩
    have hcolR : ∀ v : { v : V // v ∈ S },
        ∑ u, R u v = (Finset.univ.filter fun a : H.Arc => H.tail a ∉ S ∧ H.head a = v.1).card := by
      intro v
      have h1 : ∑ u : { v : V // v ∈ S }, R u v =
          (Finset.univ.filter fun e : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } =>
            H.head (walkEnd H S πT e).1 = v.1).card := by
        simp only [R, Matrix.of_apply]
        rw [← Finset.card_biUnion]
        · congr 1; ext e
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨_, h⟩ => h.2, fun h => ⟨⟨H.tail e.1, e.2.1⟩, rfl, h⟩⟩
        · intro u₁ _ u₂ _ hne
          exact Finset.disjoint_left.mpr fun e he₁ he₂ =>
            hne (Subtype.ext ((Finset.mem_filter.mp he₁).2.1.symm.trans (Finset.mem_filter.mp he₂).2.1))
      rw [h1]
      refine Finset.card_bij (fun e _ => (fWalk e).1) ?_ ?_ ?_
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact ⟨(fWalk e).2.1, by rw [hfWalk]; exact he⟩
      · intro e₁ _ e₂ _ h; exact fWalk.injective (Subtype.ext h)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        let e := fWalk.symm ⟨a, ha.1, ha.2.symm ▸ v.2⟩
        refine ⟨e, ?_, congrArg Subtype.val (fWalk.apply_symm_apply ⟨a, ha.1, ha.2.symm ▸ v.2⟩)⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1' : (walkEnd H S πT e).1 = a := by
          rw [← hfWalk, fWalk.apply_symm_apply]
        rw [h1']; exact ha.2
    exact ⟨hregS, R, hM_eq, hrowR, hcolR⟩
  refine ⟨?_, hsplit_prop⟩
  -- Now prove the polynomial identity j(H; x) = ∑ πT, X^(cyc_T πT) * j(H_{πT}; x)
  let eSplit : TransitionSystem H ≃ Σ πT : PartialTransition H S, TransitionSystem (splitDigraph H S πT) :=
    { toFun := fun π =>
        let πT : PartialTransition H S := fun w => π w.1
        ⟨πT, fun v => ((eInOf πT v).trans (π v.1)).trans (eOutOf πT v).symm⟩
      invFun := fun ⟨πT, πS⟩ v =>
        if hv : v ∈ S then
          ((eInOf πT ⟨v, hv⟩).symm.trans (πS ⟨v, hv⟩)).trans (eOutOf πT ⟨v, hv⟩)
        else πT ⟨v, hv⟩
      left_inv := fun π => by
        funext v; by_cases hv : v ∈ S
        · simp only [hv, ↓reduceDIte]
          apply Equiv.ext; intro a; simp
        · simp only [hv, ↓reduceDIte]
      right_inv := fun ⟨πT, πS⟩ => by
        have hT : (fun w : { v : V // v ∉ S } =>
            if hv : w.1 ∈ S then
              (((eInOf πT ⟨w.1, hv⟩).symm.trans (πS ⟨w.1, hv⟩)).trans (eOutOf πT ⟨w.1, hv⟩))
            else πT ⟨w.1, hv⟩) = πT := by
          funext w; simp [w.2]
        refine Sigma.ext hT ?_
        have h1 : ∀ {πT' : PartialTransition H S} (h : πT' = πT),
            HEq (fun v : { v : V // v ∈ S } => ((eInOf πT' v).trans
              (if hv : v.1 ∈ S then
                (((eInOf πT ⟨v.1, hv⟩).symm.trans (πS ⟨v.1, hv⟩)).trans (eOutOf πT ⟨v.1, hv⟩))
              else πT ⟨v.1, hv⟩)).trans (eOutOf πT' v).symm) πS := by
          intro πT' h; subst h
          apply heq_of_eq
          funext v; apply Equiv.ext; intro a; simp [v.2]
        exact h1 hT }
  -- Core cycle count identity: cycCount H (eSplit.symm ⟨πT, πS⟩) = cycInsideT H S πT + cycCount (splitDigraph H S πT) πS
  have hcyc_split : ∀ (πT : PartialTransition H S) (πS : TransitionSystem (splitDigraph H S πT)),
      cycCount H (eSplit.symm ⟨πT, πS⟩) =
        cycInsideT H S πT + cycCount (splitDigraph H S πT) πS := by
    intro πT πS
    let π := eSplit.symm ⟨πT, πS⟩
    let p := arcPerm H π
    let CPred (a : H.Arc) : Prop := ∀ n : ℕ, H.head ((partialStep H S πT)^[n] a) ∉ S
    -- Action of p on arcs with head ∉ S agrees with partialStep
    have hp_out : ∀ a : H.Arc, H.head a ∉ S → p a = partialStep H S πT a := by
      intro a ha
      change (π (H.head a) ⟨a, rfl⟩).1 = partialStep H S πT a
      rw [partialStep, dif_pos ha]
      simp only [π, eSplit, Equiv.coe_fn_symm_mk, dif_neg ha]
    -- Action of p on arcs with head ∈ S
    have hp_in_tail : ∀ a : H.Arc, H.head a ∈ S → H.tail (p a) ∈ S := by
      intro a ha
      have : H.tail (p a) = H.head a := (π (H.head a) ⟨a, rfl⟩).2
      rw [this]; exact ha
    -- Any arc with tail ∈ S satisfies ¬ CPred
    have hnotC_of_tail : ∀ a : H.Arc, H.tail a ∈ S → ¬ CPred a := by
      intro a hta hC
      have hha : H.head a ∉ S := hC 0
      rcases exit_reaches_S H S πT a hta hha with ⟨k, hk⟩
      exact hC k hk
    -- CPred is p-invariant
    have hC_inv : ∀ a : H.Arc, CPred (p a) ↔ CPred a := by
      intro a
      constructor
      · intro hpa
        by_cases hha : H.head a ∈ S
        · exfalso; exact hnotC_of_tail (p a) (hp_in_tail a hha) hpa
        · intro n
          cases n with
          | zero => exact hha
          | succ n =>
            have h1 := hpa n
            rwa [hp_out a hha, ← Function.iterate_succ_apply] at h1
      · intro ha n
        have hha : H.head a ∉ S := ha 0
        rw [hp_out a hha, ← Function.iterate_succ_apply]
        exact ha (n + 1)
    -- Split p into pC on {a // CPred a} = closedTArcs and pU on U = {a // ¬ CPred a}
    let U := { a : H.Arc // ¬ CPred a }
    let pU : Equiv.Perm U :=
      { toFun := fun a => ⟨p a.1, fun h => a.2 ((hC_inv a.1).mp h)⟩
        invFun := fun a => ⟨p.symm a.1, fun h => a.2 (by
          have := (hC_inv (p.symm a.1)).mpr h; simpa using this)⟩
        left_inv := fun a => by apply Subtype.ext; simp
        right_inv := fun a => by apply Subtype.ext; simp }
    let eSum : closedTArcs H S πT ⊕ U ≃ H.Arc :=
      { toFun := fun s => match s with | Sum.inl a => a.1 | Sum.inr a => a.1
        invFun := fun a => if h : CPred a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
        left_inv := fun s => by
          rcases s with ⟨a, ha⟩ | ⟨a, ha⟩
          · dsimp only; rw [dif_pos ha]
          · dsimp only; rw [dif_neg ha]
        right_inv := fun a => by
          dsimp only; by_cases h : CPred a
          · rw [dif_pos h]
          · rw [dif_neg h] }
    have hconj_sum : eSum.permCongr (Equiv.sumCongr (closedTPerm H S πT) pU) = p := by
      apply Equiv.ext; intro a
      by_cases h : CPred a
      · simp only [Equiv.permCongr_apply, eSum, Equiv.coe_fn_symm_mk, h, ↓reduceDIte,
          Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_fn_mk]
        exact (hp_out a (h 0)).symm
      · simp only [Equiv.permCongr_apply, eSum, Equiv.coe_fn_symm_mk, h, ↓reduceDIte,
          Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_fn_mk, pU]
    have hsplit_cyc : permCycleCount p = permCycleCount (closedTPerm H S πT) + permCycleCount pU := by
      rw [← hconj_sum, permCycleCount_equivCongr, permCycleCount_sumCongr]
    -- Now relate pU to arcPerm (splitDigraph H S πT) πS via first-return on A_S = {u : U // tail u ∈ S}
    let PS (u : U) : Prop := H.tail u.1 ∈ S
    have hpU_iter : ∀ (k : ℕ) (u : U), (pU^[k] u).1 = p^[k] u.1 := by
      intro k u; induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
    have hmeet : ∀ u : U, ∃ k : ℕ, PS (pU^[k] u) := by
      intro u
      have hex : ∃ n : ℕ, H.head ((partialStep H S πT)^[n] u.1) ∈ S := by
        have := u.2; simp only [CPred, not_forall, Classical.not_not] at this; exact this
      let m := Nat.find hex
      have hm_in : H.head ((partialStep H S πT)^[m] u.1) ∈ S := Nat.find_spec hex
      have hagree : ∀ i ≤ m, p^[i] u.1 = (partialStep H S πT)^[i] u.1 := by
        intro i hi
        induction i with
        | zero => rfl
        | succ i ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
          exact hp_out _ (Nat.find_min hex (by omega))
      refine ⟨m + 1, ?_⟩
      change H.tail (pU^[m + 1] u).1 ∈ S
      rw [hpU_iter, Function.iterate_succ_apply', hagree m (le_refl m)]
      exact hp_in_tail _ hm_in
    -- Bijection eAS : { u : U // PS u } ≃ (splitDigraph H S πT).Arc
    let eAS : { u : U // PS u } ≃ (splitDigraph H S πT).Arc :=
      { toFun := fun u =>
          if hh : H.head u.1.1 ∈ S then Sum.inl ⟨u.1.1, u.2, hh⟩
          else Sum.inr ⟨u.1.1, u.2, hh⟩
        invFun := fun b => match b with
          | Sum.inl a => ⟨⟨a.1, hnotC_of_tail a.1 a.2.1⟩, a.2.1⟩
          | Sum.inr e => ⟨⟨e.1, hnotC_of_tail e.1 e.2.1⟩, e.2.1⟩
        left_inv := fun ⟨⟨a, ha⟩, hta⟩ => by
          apply Subtype.ext; apply Subtype.ext; dsimp only
          by_cases hh : H.head a ∈ S
          · simp only [hh, ↓reduceDIte]
          · simp only [hh, ↓reduceDIte]
        right_inv := fun b => by
          rcases b with ⟨a, ha1, ha2⟩ | ⟨e, he1, he2⟩
          · dsimp only; exact dif_pos ha2
          · dsimp only; exact dif_neg he2 }
    let qS : Equiv.Perm { u : U // PS u } := eAS.symm.permCongr (arcPerm (splitDigraph H S πT) πS)
    have hqS_first : ∀ a : { u : U // PS u }, ∃ r : ℕ, 0 < r ∧ (qS a).1 = pU^[r] a.1 ∧
        ∀ j, 0 < j → j < r → ¬ PS (pU^[j] a.1) := by
      intro a
      by_cases hh : H.head a.1.1 ∈ S
      · refine ⟨1, by omega, ?_, fun j hj1 hj2 => by omega⟩
        apply Subtype.ext
        rw [hpU_iter, Function.iterate_one]
        change (eAS.symm (arcPerm (splitDigraph H S πT) πS (eAS a))).1.1 = p a.1.1
        have hstep_S : ∀ b : (splitDigraph H S πT).Arc, (eAS.symm b).1.1 =
            (eOutOf πT ((splitDigraph H S πT).tail b) ⟨b, rfl⟩).1 := by
          intro b; rcases b with x | x <;> rfl
        rw [hstep_S]
        have hhead_b : (splitDigraph H S πT).head (eAS a) = ⟨H.head a.1.1, hh⟩ := by
          have heAS_a : eAS a = Sum.inl ⟨a.1.1, a.2, hh⟩ := by
            change (if h : H.head a.1.1 ∈ S then _ else _) = _; exact dif_pos hh
          rw [heAS_a]; rfl
        have htail_res : (splitDigraph H S πT).tail (arcPerm (splitDigraph H S πT) πS (eAS a)) =
            ⟨H.head a.1.1, hh⟩ := by
          have := (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).2
          simpa [arcPerm, hhead_b] using this
        have h1 : (eOutOf πT ((splitDigraph H S πT).tail
            (arcPerm (splitDigraph H S πT) πS (eAS a)))
            ⟨arcPerm (splitDigraph H S πT) πS (eAS a), rfl⟩).1 =
            (eOutOf πT ⟨H.head a.1.1, hh⟩
              (πS ⟨H.head a.1.1, hh⟩ ⟨eAS a, hhead_b⟩)).1 := by
          have hsub : ∀ {v : { v : V // v ∈ S }} (hv : (splitDigraph H S πT).head (eAS a) = v),
              (eOutOf πT ((splitDigraph H S πT).tail
                (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1)
                ⟨(πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1, rfl⟩).1 =
              (eOutOf πT v (πS v ⟨eAS a, hv⟩)).1 := by
            intro v hv; subst hv
            have hsub2 : ∀ {w : { v : V // v ∈ S }}
                (hw : (splitDigraph H S πT).tail (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1 = w),
                (eOutOf πT ((splitDigraph H S πT).tail
                  (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1)
                  ⟨(πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1, rfl⟩).1 =
                (eOutOf πT w ⟨(πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1, hw⟩).1 := by
              intro w hw; subst hw; rfl
            exact hsub2 (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).2
          exact hsub hhead_b
        rw [h1]
        have h2 : eInOf πT ⟨H.head a.1.1, hh⟩ ⟨eAS a, hhead_b⟩ = ⟨a.1.1, rfl⟩ := by
          apply Subtype.ext; simp [eAS, hh, eInOf]
        change (eOutOf πT ⟨H.head a.1.1, hh⟩ (πS ⟨H.head a.1.1, hh⟩ ⟨eAS a, hhead_b⟩)).1 =
          (π (H.head a.1.1) ⟨a.1.1, rfl⟩).1
        simp only [π, eSplit, Equiv.coe_fn_symm_mk, hh, ↓reduceDIte, Equiv.trans_apply]
        rw [← h2, Equiv.symm_apply_apply]
      · -- Exit arc: walk through T takes k = Nat.find (exit_reaches_S ...) steps to walkEnd, then 1 step into S!
        let e : { b : H.Arc // H.tail b ∈ S ∧ H.head b ∉ S } := ⟨a.1.1, a.2, hh⟩
        let k := Nat.find (exit_reaches_S H S πT e.1 e.2.1 e.2.2)
        have hk_pos : 0 < k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          have hspec : H.head ((partialStep H S πT)^[k] e.1) ∈ S :=
            Nat.find_spec (exit_reaches_S H S πT e.1 e.2.1 e.2.2)
          rw [hk0] at hspec; exact hh hspec
        have hagree : ∀ j ≤ k, p^[j] a.1.1 = (partialStep H S πT)^[j] a.1.1 := by
          intro j hj
          induction j with
          | zero => rfl
          | succ j ih =>
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
            exact hp_out _ (Nat.find_min (exit_reaches_S H S πT e.1 e.2.1 e.2.2) (by omega))
        refine ⟨k + 1, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [hpU_iter, Function.iterate_succ_apply', hagree k (le_refl k)]
          have hwe_eq : (partialStep H S πT)^[k] a.1.1 = (walkEnd H S πT e).1 := rfl
          rw [hwe_eq]
          let w := walkEnd H S πT e
          have hstep_S : ∀ b : (splitDigraph H S πT).Arc, (eAS.symm b).1.1 =
              (eOutOf πT ((splitDigraph H S πT).tail b) ⟨b, rfl⟩).1 := by
            intro b; rcases b with x | x <;> rfl
          change (eAS.symm (arcPerm (splitDigraph H S πT) πS (eAS a))).1.1 = p w.1
          rw [hstep_S]
          have hhead_b : (splitDigraph H S πT).head (eAS a) = ⟨H.head w.1, w.2⟩ := by
            have heAS_a : eAS a = Sum.inr e := by
              change (if h : H.head a.1.1 ∈ S then _ else _) = _; exact dif_neg hh
            rw [heAS_a]; rfl
          have h1 : (eOutOf πT ((splitDigraph H S πT).tail
              (arcPerm (splitDigraph H S πT) πS (eAS a)))
              ⟨arcPerm (splitDigraph H S πT) πS (eAS a), rfl⟩).1 =
              (eOutOf πT ⟨H.head w.1, w.2⟩
                (πS ⟨H.head w.1, w.2⟩ ⟨eAS a, hhead_b⟩)).1 := by
            have hsub : ∀ {v : { v : V // v ∈ S }} (hv : (splitDigraph H S πT).head (eAS a) = v),
                (eOutOf πT ((splitDigraph H S πT).tail
                  (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1)
                  ⟨(πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1, rfl⟩).1 =
                (eOutOf πT v (πS v ⟨eAS a, hv⟩)).1 := by
              intro v hv; subst hv
              have hsub2 : ∀ {v' : { v : V // v ∈ S }}
                  (hv' : (splitDigraph H S πT).tail (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1 = v'),
                  (eOutOf πT ((splitDigraph H S πT).tail
                    (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1)
                    ⟨(πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1, rfl⟩).1 =
                  (eOutOf πT v' ⟨(πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).1, hv'⟩).1 := by
                intro v' hv'; subst hv'; rfl
              exact hsub2 (πS ((splitDigraph H S πT).head (eAS a)) ⟨eAS a, rfl⟩).2
            exact hsub hhead_b
          rw [h1]
          have h2 : eInOf πT ⟨H.head w.1, w.2⟩ ⟨eAS a, hhead_b⟩ = ⟨w.1, rfl⟩ := by
            apply Subtype.ext
            have heAS_a : eAS a = Sum.inr e := by
              change (if h : H.head a.1.1 ∈ S then _ else _) = _; exact dif_neg hh
            have hsub_e : (eInOf πT ⟨H.head w.1, w.2⟩ ⟨eAS a, hhead_b⟩).1 =
                (eInOf πT ⟨H.head w.1, w.2⟩ ⟨Sum.inr e, by rwa [← heAS_a]⟩).1 :=
              congrArg (fun x => (eInOf πT ⟨H.head w.1, w.2⟩ x).1) (Subtype.ext heAS_a)
            rw [hsub_e]
            exact hfWalkOf πT e
          change (eOutOf πT ⟨H.head w.1, w.2⟩ (πS ⟨H.head w.1, w.2⟩ ⟨eAS a, hhead_b⟩)).1 =
            (π (H.head w.1) ⟨w.1, rfl⟩).1
          simp only [π, eSplit, Equiv.coe_fn_symm_mk, w.2, ↓reduceDIte, Equiv.trans_apply]
          rw [← h2, Equiv.symm_apply_apply]
        · intro j hj1 hj2
          change H.tail (pU^[j] a.1).1 ∉ S
          rw [hpU_iter, hagree j (by omega)]
          have hjm : j - 1 < k := by omega
          have hprev : H.head ((partialStep H S πT)^[j - 1] a.1.1) ∉ S :=
            Nat.find_min (exit_reaches_S H S πT e.1 e.2.1 e.2.2) hjm
          have hstep : (partialStep H S πT)^[j] a.1.1 =
              partialStep H S πT ((partialStep H S πT)^[j - 1] a.1.1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hj1, Function.iterate_succ_apply']
          rw [hstep, partialStep, dif_pos hprev]
          have ht := (πT ⟨H.head ((partialStep H S πT)^[j - 1] a.1.1), hprev⟩
            ⟨(partialStep H S πT)^[j - 1] a.1.1, rfl⟩).2
          rw [ht]; exact hprev
    have hfirst := permCycleCount_firstReturn pU PS hmeet qS hqS_first
    have hqS_cyc : permCycleCount qS = permCycleCount (arcPerm (splitDigraph H S πT) πS) :=
      permCycleCount_equivCongr eAS.symm (arcPerm (splitDigraph H S πT) πS)
    unfold cycCount cycInsideT
    rw [hsplit_cyc, ← hfirst, hqS_cyc]
  rw [circuitPoly_eq_sum H]
  rw [← Fintype.sum_equiv eSplit.symm _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun πT _ => ?_
  rw [circuitPoly_eq_sum (splitDigraph H S πT), Finset.mul_sum]
  refine Finset.sum_congr rfl fun πS _ => ?_
  rw [hcyc_split πT πS, pow_add]

/-! ### Part 5: Loop Insertion & Single-Vertex Removal (Lemma 3.3, Cor 3.4, Prop 3.5, Prop 3.6) -/

section
open scoped Classical

private def loopStep {α β : Type} {k : ℕ} (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k))
    (x : α ⊕ Fin k) : α ⊕ Fin k :=
  match π x with | Sum.inl _ => x | Sum.inr l => Sum.inr l

private lemma loopStrand_fin {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (a : α) :
    ∃ n : ℕ, (π ((loopStep π)^[n] (Sum.inl a))).isLeft := by
  by_contra hno
  push Not at hno
  have hval : ∀ n, ∃ l : Fin k, π ((loopStep π)^[n] (Sum.inl a)) = Sum.inr l := by
    intro n
    cases h : π ((loopStep π)^[n] (Sum.inl a)) with
    | inl b => exact absurd (by simp [h]) (hno n)
    | inr l => exact ⟨l, rfl⟩
  have hstep_of_inr : ∀ (x : α ⊕ Fin k) (l : Fin k), π x = Sum.inr l →
      loopStep π x = Sum.inr l := fun x l hx => by dsimp only [loopStep]; rw [hx]
  have hstep_inr : ∀ n, (loopStep π)^[n + 1] (Sum.inl a) = Sum.inr (hval n).choose := by
    intro n
    rw [Function.iterate_succ_apply']
    exact hstep_of_inr _ _ (hval n).choose_spec
  have hinj : Function.Injective (fun n : ℕ => (loopStep π)^[n] (Sum.inl a)) := by
    intro i j hij
    dsimp only at hij
    wlog hle : i ≤ j generalizing i j
    · exact (this hij.symm (by omega)).symm
    induction i generalizing j with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        exfalso
        rw [Function.iterate_zero_apply, hstep_inr j] at hij
        cases hij
    | succ i ih =>
      cases j with
      | zero => omega
      | succ j =>
        rw [hstep_inr i, hstep_inr j] at hij
        have hch : (hval i).choose = (hval j).choose := Sum.inr.inj hij
        have hπeq : π ((loopStep π)^[i] (Sum.inl a)) = π ((loopStep π)^[j] (Sum.inl a)) := by
          rw [(hval i).choose_spec, (hval j).choose_spec, hch]
        exact congrArg Nat.succ (ih (π.injective hπeq) (by omega))
  have : Finite ℕ := Finite.of_injective _ hinj
  exact not_finite ℕ

private noncomputable def loopStrandEnd {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (a : α) : β :=
  match h : π ((loopStep π)^[Nat.find (loopStrand_fin π a)] (Sum.inl a)) with
  | Sum.inl b => b
  | Sum.inr _ => False.elim (by have := Nat.find_spec (loopStrand_fin π a); rw [h] at this; cases this)

private lemma loopStrandEnd_eq_of {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (a : α) (n : ℕ) (b : β)
    (hreach : π ((loopStep π)^[n] (Sum.inl a)) = Sum.inl b)
    (hmin : ∀ j < n, (π ((loopStep π)^[j] (Sum.inl a))).isRight) :
    loopStrandEnd π a = b := by
  have hfind : Nat.find (loopStrand_fin π a) = n := by
    refine le_antisymm (Nat.find_min' (loopStrand_fin π a) (by rw [hreach]; rfl)) ?_
    by_contra hlt
    have hspec := Nat.find_spec (loopStrand_fin π a)
    have hr := hmin (Nat.find (loopStrand_fin π a)) (by omega)
    cases h : π ((loopStep π)^[Nat.find (loopStrand_fin π a)] (Sum.inl a)) with
    | inl _ => rw [h] at hr; cases hr
    | inr _ => rw [h] at hspec; cases hspec
  have hval : π ((loopStep π)^[Nat.find (loopStrand_fin π a)] (Sum.inl a)) = Sum.inl b := by
    rw [hfind]; exact hreach
  unfold loopStrandEnd
  split
  · rename_i b' hb'; exact Sum.inl.inj (hb'.symm.trans hval)
  · rename_i l hl; rw [hval] at hl; cases hl

private abbrev loopClosedSet {α β : Type} {k : ℕ} (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) :=
  { l : Fin k // ∀ n : ℕ, (π ((loopStep π)^[n] (Sum.inr l))).isRight }

private def loopClosedFun {α β : Type} {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (l : loopClosedSet π) : loopClosedSet π :=
  match h : π (Sum.inr l.1) with
  | Sum.inr l' => ⟨l', fun n => by
      have h1 := l.2 (n + 1)
      have hst : loopStep π (Sum.inr l.1) = Sum.inr l' := by dsimp only [loopStep]; rw [h]
      rwa [Function.iterate_succ_apply, hst] at h1⟩
  | Sum.inl _ => False.elim (by have := l.2 0; rw [Function.iterate_zero_apply, h] at this; cases this)

private lemma loopClosedFun_spec {α β : Type} {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (l : loopClosedSet π) :
    π (Sum.inr l.1) = Sum.inr (loopClosedFun π l).1 := by
  unfold loopClosedFun
  split
  · rename_i l' hl'; exact hl'
  · rename_i b hb; exfalso; have := l.2 0; rw [Function.iterate_zero_apply, hb] at this; cases this

private noncomputable def loopClosedPerm {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) : Equiv.Perm (loopClosedSet π) :=
  Equiv.ofBijective (loopClosedFun π) (Finite.injective_iff_bijective.mp fun l₁ l₂ heq => by
    have h1 := loopClosedFun_spec π l₁
    have h2 := loopClosedFun_spec π l₂
    rw [heq] at h1
    exact Subtype.ext (Sum.inr.inj (π.injective (h1.trans h2.symm))))

private lemma loopClosedPerm_spec {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (l : loopClosedSet π) :
    π (Sum.inr l.1) = Sum.inr (loopClosedPerm π l).1 :=
  loopClosedFun_spec π l

private noncomputable def loopCycleCount {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) : ℕ :=
  permCycleCount (loopClosedPerm π)

set_option maxHeartbeats 800000 in
/-- Abstract strand-contraction and loop-insertion polynomial identity:
for finite `α, β` of size `m` and `k` loops (`Fin k`), for any fixed `σ : α ≃ β`,
the sum of `X^(loop cycles)` over all `π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)` whose induced strand
bijection is `σ` equals `∏_{i=0}^{k-1} (X + (m + i))`. -/
private lemma loop_insertion_poly {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (m : ℕ) (hα : Fintype.card α = m) (k : ℕ) :
    ∀ (σ : α ≃ β),
      (∑ π : (α ⊕ Fin k) ≃ (β ⊕ Fin k),
        @ite (Polynomial ℤ) (∀ a : α, loopStrandEnd π a = σ a) (Classical.propDecidable _)
          (Polynomial.X ^ (loopCycleCount π)) 0) =
      ∏ i ∈ Finset.range k, (Polynomial.X + Polynomial.C ((m + i : ℕ) : ℤ)) := by
  classical
  induction k with
  | zero =>
    intro σ
    rw [Finset.prod_range_zero]
    let π0 : (α ⊕ Fin 0) ≃ (β ⊕ Fin 0) := Equiv.sumCongr σ (Equiv.refl (Fin 0))
    have huniq : ∀ π : (α ⊕ Fin 0) ≃ (β ⊕ Fin 0),
        (∀ a : α, loopStrandEnd π a = σ a) → π = π0 := by
      intro π hπ
      apply Equiv.ext; rintro (a | l)
      · rcases h : π (Sum.inl a) with b | l
        · have heq : loopStrandEnd π a = b := loopStrandEnd_eq_of π a 0 b h (fun _ hj => by omega)
          have hb : b = σ a := heq.symm.trans (hπ a)
          simp [π0, hb]
        · exact Fin.elim0 l
      · exact Fin.elim0 l
    rw [Finset.sum_eq_single π0]
    · have hcond : ∀ a : α, loopStrandEnd π0 a = σ a := fun a =>
        loopStrandEnd_eq_of π0 a 0 (σ a) rfl (fun _ hj => by omega)
      rw [if_pos hcond]
      have hcyc0 : loopCycleCount π0 = 0 := by
        unfold loopCycleCount permCycleCount
        haveI : IsEmpty (loopClosedSet π0) := ⟨fun l => Fin.elim0 l.1⟩
        exact Fintype.card_eq_zero
      simp [hcyc0]
    · intro π _ hne
      exact if_neg (fun hcond => hne (huniq π hcond))
    · intro h; exact absurd (Finset.mem_univ π0) h
  | succ k ih =>
    intro σ
    rw [Finset.prod_range_succ, ← ih σ, mul_comm, add_mul, Finset.mul_sum, Finset.mul_sum]
    -- Split π' : (α ⊕ Fin (k+1)) ≃ (β ⊕ Fin (k+1)) by whether π' (inr last) = inr last or not!
    let last : Fin (k + 1) := Fin.last k
    let emb : Fin k ↪ Fin (k + 1) := ⟨Fin.castSucc, Fin.castSucc_injective k⟩
    let castIn : α ⊕ Fin k → α ⊕ Fin (k + 1) := Sum.map id Fin.castSucc
    let castOut : β ⊕ Fin k → β ⊕ Fin (k + 1) := Sum.map id Fin.castSucc
    have hcastIn_inj : Function.Injective castIn := fun x y h => by
      cases x <;> cases y <;> simp [castIn] at h ⊢ <;> exact h
    have hcastOut_inj : Function.Injective castOut := fun x y h => by
      cases x <;> cases y <;> simp [castOut] at h ⊢ <;> exact h
    have hcastIn_ne_last : ∀ x : α ⊕ Fin k, castIn x ≠ Sum.inr last := by
      rintro (a | l) h <;> simp [castIn, last] at h
    have hcastOut_ne_last : ∀ y : β ⊕ Fin k, castOut y ≠ Sum.inr last := by
      rintro (b | l) h <;> simp [castOut, last] at h
    -- Helper: lift/unlift Fin (k+1) ≠ last to Fin k
    let uncastIn (x : α ⊕ Fin (k + 1)) (hx : x ≠ Sum.inr last) : α ⊕ Fin k :=
      match x with
      | Sum.inl a => Sum.inl a
      | Sum.inr l => Sum.inr (l.castPred (fun h => hx (congrArg Sum.inr h)))
    let uncastOut (y : β ⊕ Fin (k + 1)) (hy : y ≠ Sum.inr last) : β ⊕ Fin k :=
      match y with
      | Sum.inl b => Sum.inl b
      | Sum.inr l => Sum.inr (l.castPred (fun h => hy (congrArg Sum.inr h)))
    have hcastIn_uncast : ∀ x hx, castIn (uncastIn x hx) = x := by
      rintro (a | l) hx
      · rfl
      · simp [castIn, uncastIn, Fin.castSucc_castPred]
    have huncastIn_cast : ∀ x, uncastIn (castIn x) (hcastIn_ne_last x) = x := by
      rintro (a | l)
      · rfl
      · simp [castIn, uncastIn]
    have hcastOut_uncast : ∀ y hy, castOut (uncastOut y hy) = y := by
      rintro (b | l) hy
      · rfl
      · simp [castOut, uncastOut, Fin.castSucc_castPred]
    have huncastOut_cast : ∀ y, uncastOut (castOut y) (hcastOut_ne_last y) = y := by
      rintro (b | l)
      · rfl
      · simp [castOut, uncastOut]
    -- Map 1 (self-loop): π ↦ insertSelfLoop π (maps inr last ↦ inr last)
    let insSelf (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) : (α ⊕ Fin (k + 1)) ≃ (β ⊕ Fin (k + 1)) :=
      { toFun := fun x => if hx : x = Sum.inr last then Sum.inr last else castOut (π (uncastIn x hx))
        invFun := fun y => if hy : y = Sum.inr last then Sum.inr last else castIn (π.symm (uncastOut y hy))
        left_inv := fun x => by
          by_cases hx : x = Sum.inr last
          · simp [hx]
          · simp [hx, hcastOut_ne_last, huncastOut_cast, hcastIn_uncast]
        right_inv := fun y => by
          by_cases hy : y = Sum.inr last
          · simp [hy]
          · simp [hy, hcastIn_ne_last, huncastIn_cast, hcastOut_uncast] }
    -- Map 2 (insert after x₀ ∈ α ⊕ Fin k): (π, x₀) ↦ insAfter π x₀
    let insAfter (π : (α ⊕ Fin k) ≃ (β ⊕ Fin k)) (x₀ : α ⊕ Fin k) :
        (α ⊕ Fin (k + 1)) ≃ (β ⊕ Fin (k + 1)) :=
      { toFun := fun x =>
          if hx : x = Sum.inr last then castOut (π x₀)
          else if uncastIn x hx = x₀ then Sum.inr last
          else castOut (π (uncastIn x hx))
        invFun := fun y =>
          if hy : y = Sum.inr last then castIn x₀
          else if π.symm (uncastOut y hy) = x₀ then Sum.inr last
          else castIn (π.symm (uncastOut y hy))
        left_inv := fun x => by
          dsimp only
          by_cases hx : x = Sum.inr last
          · subst hx
            simp [hcastOut_ne_last, huncastOut_cast]
          · by_cases hx0 : uncastIn x hx = x₀
            · rw [dif_neg hx, if_pos hx0, dif_pos rfl, ← hx0, hcastIn_uncast]
            · simp [hx, hx0, hcastOut_ne_last, huncastOut_cast, hcastIn_uncast]
        right_inv := fun y => by
          dsimp only
          by_cases hy : y = Sum.inr last
          · subst hy
            simp [hcastIn_ne_last, huncastIn_cast]
          · by_cases hy0 : π.symm (uncastOut y hy) = x₀
            · have hy_eq : uncastOut y hy = π x₀ := (Equiv.symm_apply_eq π).mp hy0
              rw [dif_neg hy, if_pos hy0, dif_pos rfl, ← hy_eq, hcastOut_uncast]
            · simp [hy, hy0, hcastIn_ne_last, huncastIn_cast, hcastOut_uncast] }
    -- Equivalence between ((α ⊕ Fin k) ≃ (β ⊕ Fin k)) ⊕ (((α ⊕ Fin k) ≃ (β ⊕ Fin k)) × (α ⊕ Fin k))
    -- and (α ⊕ Fin (k+1)) ≃ (β ⊕ Fin (k+1))
    let eIns : ((α ⊕ Fin k) ≃ (β ⊕ Fin k)) ⊕ (((α ⊕ Fin k) ≃ (β ⊕ Fin k)) × (α ⊕ Fin k)) ≃
        ((α ⊕ Fin (k + 1)) ≃ (β ⊕ Fin (k + 1))) :=
      { toFun := fun s => match s with
          | Sum.inl π => insSelf π
          | Sum.inr (π, x₀) => insAfter π x₀
        invFun := fun π' =>
          if hfix : π' (Sum.inr last) = Sum.inr last then
            Sum.inl
              { toFun := fun x => uncastOut (π' (castIn x)) (fun h =>
                  hcastIn_ne_last x (π'.injective (h.trans hfix.symm)))
                invFun := fun y => uncastIn (π'.symm (castOut y)) (fun h =>
                  hcastOut_ne_last y (by
                    have := congrArg π' h; rw [π'.apply_symm_apply, hfix] at this; exact this))
                left_inv := fun x => by simp [hcastOut_uncast, huncastIn_cast]
                right_inv := fun y => by simp [hcastIn_uncast, huncastOut_cast] }
          else
            let hne_symm : π'.symm (Sum.inr last) ≠ Sum.inr last := fun h =>
              hfix (by have := congrArg π' h; rw [π'.apply_symm_apply] at this; exact this.symm)
            let x₀ : α ⊕ Fin k := uncastIn (π'.symm (Sum.inr last)) hne_symm
            let y₀ : β ⊕ Fin k := uncastOut (π' (Sum.inr last)) hfix
            have hne_out : ∀ x : α ⊕ Fin k, x ≠ x₀ → π' (castIn x) ≠ Sum.inr last := fun x hx h => by
              apply hx
              have h1 : castIn x = π'.symm (Sum.inr last) :=
                π'.injective (h.trans (π'.apply_symm_apply _).symm)
              apply hcastIn_inj
              rw [h1, hcastIn_uncast]
            have hne_in : ∀ y : β ⊕ Fin k, y ≠ y₀ → π'.symm (castOut y) ≠ Sum.inr last := fun y hy h => by
              apply hy
              have h1 : castOut y = π' (Sum.inr last) := by
                have := congrArg π' h; rwa [π'.apply_symm_apply] at this
              apply hcastOut_inj
              rw [h1, hcastOut_uncast]
            Sum.inr (
              ({ toFun := fun (x : α ⊕ Fin k) =>
                  @dite _ (x = x₀) (Classical.propDecidable _) (fun _ => y₀)
                    (fun hx => uncastOut (π' (castIn x)) (hne_out x hx))
                 invFun := fun (y : β ⊕ Fin k) =>
                  @dite _ (y = y₀) (Classical.propDecidable _) (fun _ => x₀)
                    (fun hy => uncastIn (π'.symm (castOut y)) (hne_in y hy))
                 left_inv := fun x => by
                  by_cases hx : x = x₀
                  · subst hx; simp
                  · have hne : uncastOut (π' (castIn x)) (hne_out x hx) ≠ y₀ := by
                      intro heq
                      have h1 : π' (castIn x) = π' (Sum.inr last) := by
                        rw [← hcastOut_uncast (π' (castIn x)) (hne_out x hx), heq, hcastOut_uncast]
                      exact hcastIn_ne_last x (π'.injective h1)
                    simp [hx, hne, hcastOut_uncast, huncastIn_cast]
                 right_inv := fun y => by
                  by_cases hy : y = y₀
                  · subst hy; simp
                  · have hne : uncastIn (π'.symm (castOut y)) (hne_in y hy) ≠ x₀ := by
                      intro heq
                      have h1 : π'.symm (castOut y) = π'.symm (Sum.inr last) := by
                        rw [← hcastIn_uncast (π'.symm (castOut y)) (hne_in y hy), heq, hcastIn_uncast]
                      exact hcastOut_ne_last y (π'.symm.injective h1)
                    simp [hy, hne, hcastIn_uncast, huncastOut_cast] } : (α ⊕ Fin k) ≃ (β ⊕ Fin k)),
              x₀)
        left_inv := fun s => by
          rcases s with π | ⟨π, x₀⟩
          · have hfix : insSelf π (Sum.inr last) = Sum.inr last := by simp [insSelf]
            simp only [hfix, ↓reduceDIte, Sum.inl.injEq]
            apply Equiv.ext; intro x
            simp [insSelf, hcastIn_ne_last, huncastIn_cast, huncastOut_cast]
          · have hfix : insAfter π x₀ (Sum.inr last) ≠ Sum.inr last := by
              simp [insAfter, hcastOut_ne_last]
            have hx0_eq : uncastIn ((insAfter π x₀).symm (Sum.inr last)) (fun h =>
                hfix (by have := congrArg (insAfter π x₀) h; rw [(insAfter π x₀).apply_symm_apply] at this; exact this.symm)) = x₀ := by
              simp [insAfter, huncastIn_cast]
            simp only [hfix, ↓reduceDIte, Sum.inr.injEq, Prod.mk.injEq]
            refine ⟨?_, hx0_eq⟩
            apply Equiv.ext; intro x
            dsimp only [Equiv.coe_fn_mk]
            by_cases hx : x = x₀
            · subst hx
              rw [dif_pos hx0_eq.symm]
              simp [insAfter, huncastOut_cast]
            · rw [dif_neg (by rw [hx0_eq]; exact hx)]
              simp [hx, insAfter, hcastIn_ne_last, huncastIn_cast, huncastOut_cast]
        right_inv := fun π' => by
          by_cases hfix : π' (Sum.inr last) = Sum.inr last
          · simp only [hfix, ↓reduceDIte]
            apply Equiv.ext; intro x
            by_cases hx : x = Sum.inr last
            · subst hx; simp [insSelf, hfix]
            · simp [insSelf, hx, hcastIn_uncast, hcastOut_uncast]
          · simp only [hfix, ↓reduceDIte]
            apply Equiv.ext; intro x
            by_cases hx : x = Sum.inr last
            · subst hx; simp [insAfter, hcastOut_uncast]
            · by_cases hx0 : uncastIn x hx = uncastIn (π'.symm (Sum.inr last))
                  (fun h => hfix (by rw [← h, Equiv.apply_symm_apply]))
              · have hx_eq : x = π'.symm (Sum.inr last) := by
                  rw [← hcastIn_uncast x hx, hx0, hcastIn_uncast]
                simp only [insAfter, Equiv.coe_fn_mk, hx, ↓reduceDIte, hx0, ↓reduceIte]
                rw [hx_eq, Equiv.apply_symm_apply]
              · simp [insAfter, hx, hx0, hcastIn_uncast, hcastOut_uncast] }
    -- Helper properties for insSelf and insAfter: strandEnd preserved, loopCycleCount shifts by +1 / +0!
    -- Let's prove both cleanly via step iteration and permCycleCount_firstReturn / permCycleCount_sumCongr!
    have hcard_dom : (Fintype.card (α ⊕ Fin k) : ℤ) = ((m + k : ℕ) : ℤ) := by
      rw [Fintype.card_sum, hα, Fintype.card_fin]
    rw [← Fintype.sum_equiv eIns _ _ (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_prod_type]
    congr 1
    · -- Self-loop branch: ∑ π, (if strandEnd (insSelf π) = σ then X^(cyc+1) else 0)
      refine Finset.sum_congr rfl fun π _ => ?_
      have hstep_self : ∀ (n : ℕ) (x : α ⊕ Fin k),
          (loopStep (insSelf π))^[n] (castIn x) = castIn ((loopStep π)^[n] x) := by
        intro n x
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          dsimp only [loopStep]
          simp only [insSelf, Equiv.coe_fn_mk, hcastIn_ne_last, ↓reduceDIte, huncastIn_cast]
          cases π ((loopStep π)^[n] x) <;> rfl
      have hstrand_self : ∀ a : α, loopStrandEnd (insSelf π) a = loopStrandEnd π a := by
        intro a
        set n0 := Nat.find (loopStrand_fin π a)
        have hspec0 := Nat.find_spec (loopStrand_fin π a)
        have hmin0 : ∀ j < n0, (π ((loopStep π)^[j] (Sum.inl a))).isRight := fun j hj => by
          have := Nat.find_min (loopStrand_fin π a) hj
          cases h : π ((loopStep π)^[j] (Sum.inl a)) with | inl _ => simp [h] at this | inr _ => simp
        rcases hπ0 : π ((loopStep π)^[n0] (Sum.inl a)) with b0 | l0
        · have hR : loopStrandEnd π a = b0 := loopStrandEnd_eq_of π a n0 b0 hπ0 hmin0
          rw [hR]
          refine loopStrandEnd_eq_of (insSelf π) a n0 b0 ?_ fun j hj => ?_
          · change insSelf π ((loopStep (insSelf π))^[n0] (castIn (Sum.inl a))) = Sum.inl b0
            rw [hstep_self, show insSelf π (castIn ((loopStep π)^[n0] (Sum.inl a))) =
              castOut (π ((loopStep π)^[n0] (Sum.inl a))) by
              simp only [insSelf, Equiv.coe_fn_mk, hcastIn_ne_last, ↓reduceDIte, huncastIn_cast]]
            rw [hπ0]; rfl
          · change (insSelf π ((loopStep (insSelf π))^[j] (castIn (Sum.inl a)))).isRight
            rw [hstep_self, show insSelf π (castIn ((loopStep π)^[j] (Sum.inl a))) =
              castOut (π ((loopStep π)^[j] (Sum.inl a))) by
              simp only [insSelf, Equiv.coe_fn_mk, hcastIn_ne_last, ↓reduceDIte, huncastIn_cast]]
            have hjr := hmin0 j hj
            cases h : π ((loopStep π)^[j] (Sum.inl a)) with
            | inl _ => rw [h] at hjr; cases hjr
            | inr _ => rfl
        · rw [hπ0] at hspec0; cases hspec0
      have hcyc_self : loopCycleCount (insSelf π) = loopCycleCount π + 1 := by
        unfold loopCycleCount
        have hlast_mem : ∀ n, (insSelf π ((loopStep (insSelf π))^[n] (Sum.inr last))).isRight := by
          intro n
          have hiter : (loopStep (insSelf π))^[n] (Sum.inr last) = Sum.inr last := by
            induction n with
            | zero => rfl
            | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [loopStep, insSelf]
          rw [hiter]; simp [insSelf]
        have hcast_iff : ∀ l : Fin k,
            (∀ n, (insSelf π ((loopStep (insSelf π))^[n] (Sum.inr l.castSucc))).isRight) ↔
            (∀ n, (π ((loopStep π)^[n] (Sum.inr l))).isRight) := by
          intro l
          refine forall_congr' fun n => ?_
          have h1 := hstep_self n (Sum.inr l)
          change (insSelf π ((loopStep (insSelf π))^[n] (castIn (Sum.inr l)))).isRight ↔ _
          rw [h1]
          simp only [insSelf, Equiv.coe_fn_mk, hcastIn_ne_last, ↓reduceDIte, huncastIn_cast]
          cases π ((loopStep π)^[n] (Sum.inr l)) <;> simp [castOut]
        let eC : loopClosedSet π ⊕ Unit ≃ loopClosedSet (insSelf π) :=
          { toFun := fun s => match s with
              | Sum.inl l => ⟨l.1.castSucc, (hcast_iff l.1).mpr l.2⟩
              | Sum.inr () => ⟨last, hlast_mem⟩
            invFun := fun l =>
              if hl : l.1 = last then Sum.inr ()
              else Sum.inl ⟨l.1.castPred hl, (hcast_iff _).mp (by simpa [Fin.castSucc_castPred] using l.2)⟩
            left_inv := fun s => by
              rcases s with ⟨l, hl⟩ | ⟨⟩
              · simp [last, Fin.castSucc_ne_last]
              · simp
            right_inv := fun ⟨l, hl⟩ => by
              by_cases h : l = last
              · subst h; simp
              · simp [h, Fin.castSucc_castPred] }
        have hconj : eC.permCongr (Equiv.sumCongr (loopClosedPerm π) (1 : Equiv.Perm Unit)) =
            loopClosedPerm (insSelf π) := by
          apply Equiv.ext; rintro ⟨l, hl⟩
          apply Subtype.ext
          by_cases h : l = last
          · subst h
            have h1 := loopClosedPerm_spec (insSelf π) ⟨last, hl⟩
            simp only [insSelf, Equiv.coe_fn_mk, ↓reduceDIte, Sum.inr.injEq] at h1
            simp only [Equiv.permCongr_apply, eC, Equiv.coe_fn_symm_mk, ↓reduceDIte,
              Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_fn_mk]
            exact h1
          · simp only [Equiv.permCongr_apply, eC, Equiv.coe_fn_symm_mk, h, ↓reduceDIte,
              Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_fn_mk]
            have h1 := loopClosedPerm_spec (insSelf π) ⟨l, hl⟩
            have h2 := loopClosedPerm_spec π ⟨l.castPred h, (hcast_iff _).mp (by simpa [Fin.castSucc_castPred] using hl)⟩
            have hlne : (Sum.inr l : α ⊕ Fin (k + 1)) ≠ Sum.inr last := fun eq => h (Sum.inr.inj eq)
            simp only [insSelf, Equiv.coe_fn_mk, hlne, ↓reduceDIte, uncastIn] at h1
            rw [h2] at h1
            exact Sum.inr.inj h1
        rw [← hconj, permCycleCount_equivCongr, permCycleCount_sumCongr]
        have hunit : permCycleCount (1 : Equiv.Perm Unit) = 1 := by
          unfold permCycleCount
          exact Fintype.card_unique
        rw [hunit]
      dsimp only [eIns, Equiv.coe_fn_mk]
      simp_rw [hstrand_self]
      split_ifs with hcond
      · rw [hcyc_self, pow_succ, mul_comm]
      · simp
    · -- Non-self-loop branch: ∑ π, ∑ x₀, ... = ∑ π, C (m + k) * ...
      have hconst_one : ∀ p : Polynomial ℤ,
          Polynomial.C ((m + k : ℕ) : ℤ) * p = ∑ _x₀ : α ⊕ Fin k, p := fun p => by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_sum, hα, Fintype.card_fin]
        simp [Polynomial.C_eq_natCast]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [hconst_one]
      refine Finset.sum_congr rfl fun x₀ _ => ?_
      -- Show insAfter π x₀ has the exact same loopStrandEnd and loopCycleCount as π!
      let step0 := loopStep π
      let step1 := loopStep (insAfter π x₀)
      -- Clean simulation: for every x : α ⊕ Fin k, if (π ((step0)^[n] x)) reaches Sum.inl b at first n,
      -- then insAfter π x₀ reaches Sum.inl b at some n' with all intermediate steps inr!
      have hreach_inl : ∀ (n : ℕ) (x : α ⊕ Fin k) (b : β),
          π (step0^[n] x) = Sum.inl b →
          (∀ j < n, (π (step0^[j] x)).isRight) →
          ∃ n' : ℕ, insAfter π x₀ (step1^[n'] (castIn x)) = Sum.inl b ∧
            ∀ j < n', (insAfter π x₀ (step1^[j] (castIn x))).isRight := by
        intro n
        induction n with
        | zero =>
          intro x b hπx _
          rw [Function.iterate_zero_apply] at hπx
          by_cases hx : x = x₀
          · subst hx
            refine ⟨1, ?_, fun j hj => ?_⟩
            · have h1 : insAfter π x (castIn x) = Sum.inr last := by
                simp [insAfter, hcastIn_ne_last, huncastIn_cast]
              have h2 : step1 (castIn x) = Sum.inr last := by simp [step1, loopStep, h1]
              simp [h2, insAfter, hπx, castOut]
            · have hj0 : j = 0 := by omega
              subst hj0
              simp [insAfter, hcastIn_ne_last, huncastIn_cast]
          · refine ⟨0, ?_, fun j hj => by omega⟩
            simp [insAfter, hcastIn_ne_last, huncastIn_cast, hx, hπx, castOut]
        | succ n ih =>
          intro x b hπn hmin
          have h0_right := hmin 0 (by omega)
          rcases hπx : π x with b0 | l0
          · simp [hπx] at h0_right
          · have hst0 : step0 x = Sum.inr l0 := by simp [step0, loopStep, hπx]
            have hπn' : π (step0^[n] (Sum.inr l0)) = Sum.inl b := by
              rwa [← hst0, ← Function.iterate_succ_apply]
            have hmin' : ∀ j < n, (π (step0^[j] (Sum.inr l0))).isRight := fun j hj => by
              have := hmin (j + 1) (by omega)
              rwa [Function.iterate_succ_apply, hst0] at this
            obtain ⟨m', hm'_eq, hm'_min⟩ := ih (Sum.inr l0) b hπn' hmin'
            by_cases hx : x = x₀
            · subst hx
              have h1 : insAfter π x (castIn x) = Sum.inr last := by
                simp [insAfter, hcastIn_ne_last, huncastIn_cast]
              have hs1 : step1 (castIn x) = Sum.inr last := by simp [step1, loopStep, h1]
              have h2 : insAfter π x (Sum.inr last) = Sum.inr l0.castSucc := by
                simp [insAfter, hπx, castOut]
              have hs2 : step1 (Sum.inr last) = castIn (Sum.inr l0) := by
                simp [step1, loopStep, h2, castIn]
              refine ⟨m' + 2, ?_, fun j hj => ?_⟩
              · rw [show m' + 2 = m' + 1 + 1 from rfl, Function.iterate_succ_apply, hs1,
                  Function.iterate_succ_apply, hs2]
                exact hm'_eq
              · cases j with
                | zero => simp [h1]
                | succ j =>
                  cases j with
                  | zero => simp [hs1, h2]
                  | succ j =>
                    rw [Function.iterate_succ_apply, hs1, Function.iterate_succ_apply, hs2]
                    exact hm'_min j (by omega)
            · have h1 : insAfter π x₀ (castIn x) = Sum.inr l0.castSucc := by
                simp [insAfter, hcastIn_ne_last, huncastIn_cast, hx, hπx, castOut]
              have hs1 : step1 (castIn x) = castIn (Sum.inr l0) := by
                simp [step1, loopStep, h1, castIn]
              refine ⟨m' + 1, ?_, fun j hj => ?_⟩
              · rw [Function.iterate_succ_apply, hs1]; exact hm'_eq
              · cases j with
                | zero => simp [h1]
                | succ j => rw [Function.iterate_succ_apply, hs1]; exact hm'_min j (by omega)
      have hstrand_after : ∀ a : α, loopStrandEnd (insAfter π x₀) a = loopStrandEnd π a := by
        intro a
        set n0 := Nat.find (loopStrand_fin π a)
        have hspec0 := Nat.find_spec (loopStrand_fin π a)
        have hmin0 : ∀ j < n0, (π (step0^[j] (Sum.inl a))).isRight := fun j hj => by
          have hnot : ¬ (π (step0^[j] (Sum.inl a))).isLeft := Nat.find_min (loopStrand_fin π a) hj
          cases h : π (step0^[j] (Sum.inl a)) with
          | inl _ => rw [h] at hnot; exact absurd rfl hnot
          | inr _ => rfl
        rcases hπ0 : π (step0^[n0] (Sum.inl a)) with b0 | l0
        · have hR : loopStrandEnd π a = b0 := loopStrandEnd_eq_of π a n0 b0 hπ0 hmin0
          rw [hR]
          obtain ⟨n1, hn1_eq, hn1_min⟩ := hreach_inl n0 (Sum.inl a) b0 hπ0 hmin0
          exact loopStrandEnd_eq_of (insAfter π x₀) a n1 b0 hn1_eq hn1_min
        · rw [hπ0] at hspec0; cases hspec0
      -- Now prove loopCycleCount (insAfter π x₀) = loopCycleCount π via permCycleCount_firstReturn!
      have hcyc_after : loopCycleCount (insAfter π x₀) = loopCycleCount π := by
        unfold loopCycleCount
        set p1 := loopClosedPerm (insAfter π x₀)
        set p0 := loopClosedPerm π
        have hp1 : ∀ l, insAfter π x₀ (Sum.inr l.1) = Sum.inr (p1 l).1 := loopClosedPerm_spec _
        have hp0 : ∀ l, π (Sum.inr l.1) = Sum.inr (p0 l).1 := loopClosedPerm_spec _
        -- Show P1 (l.castSucc) ↔ P0 l for all l : Fin k
        have hP_iff : ∀ l : Fin k,
            (∀ n, (insAfter π x₀ (step1^[n] (Sum.inr l.castSucc))).isRight) ↔
            (∀ n, (π (step0^[n] (Sum.inr l))).isRight) := by
          intro l
          constructor
          · intro h1
            by_contra hnot
            push Not at hnot
            have hex : ∃ n, (π (step0^[n] (Sum.inr l))).isLeft := by
              rcases hnot with ⟨n, hn⟩
              exact ⟨n, by cases h : π (step0^[n] (Sum.inr l)) with | inl _ => rfl | inr _ => rw [h] at hn; exact absurd rfl hn⟩
            let m := Nat.find hex
            have hspec : (π (step0^[m] (Sum.inr l))).isLeft := Nat.find_spec hex
            have hmin : ∀ j < m, (π (step0^[j] (Sum.inr l))).isRight := fun j hj => by
              have := Nat.find_min hex hj
              cases h : π (step0^[j] (Sum.inr l)) with | inl _ => rw [h] at this; exact absurd rfl this | inr _ => rfl
            rcases hπm : π (step0^[m] (Sum.inr l)) with b | l'
            · obtain ⟨n1, hn1_eq, _⟩ := hreach_inl m (Sum.inr l) b hπm hmin
              have h1n : (insAfter π x₀ (step1^[n1] (castIn (Sum.inr l)))).isRight := h1 n1
              rw [hn1_eq] at h1n; cases h1n
            · rw [hπm] at hspec; cases hspec
          · intro h0
            -- All iterates from inr l stay in {inr l'.castSucc | P0 l'} ∪ {inr last}
            have hclosed_step : ∀ x : Fin k, (∀ n, (π (step0^[n] (Sum.inr x))).isRight) →
                ∃ y : Fin k, (∀ n, (π (step0^[n] (Sum.inr y))).isRight) ∧
                  π (Sum.inr x) = Sum.inr y := by
              intro x hx
              rcases h : π (Sum.inr x) with b | y
              · exfalso; have := hx 0; simp [h] at this
              · refine ⟨y, fun n => ?_, rfl⟩
                have h1 := hx (n + 1)
                have hst : step0 (Sum.inr x) = Sum.inr y := by simp [step0, loopStep, h]
                rwa [Function.iterate_succ_apply, hst] at h1
            have hinv : ∀ n : ℕ,
                (∃ y : Fin k, (∀ r, (π (step0^[r] (Sum.inr y))).isRight) ∧
                  step1^[n] (Sum.inr l.castSucc) = Sum.inr y.castSucc) ∨
                (step1^[n] (Sum.inr l.castSucc) = Sum.inr last ∧
                  ∃ y : Fin k, (∀ r, (π (step0^[r] (Sum.inr y))).isRight) ∧
                    insAfter π x₀ (Sum.inr last) = Sum.inr y.castSucc) := by
              intro n
              induction n with
              | zero => exact Or.inl ⟨l, h0, rfl⟩
              | succ n ih =>
                rw [Function.iterate_succ_apply']
                rcases ih with ⟨y, hy, heq⟩ | ⟨heq, y, hy, hlast⟩
                · rw [heq]
                  obtain ⟨y', hy', hπy⟩ := hclosed_step y hy
                  by_cases hyx : (Sum.inr y : α ⊕ Fin k) = x₀
                  · refine Or.inr ⟨?_, y', hy', ?_⟩
                    · have h1 : insAfter π x₀ (Sum.inr y.castSucc) = Sum.inr last := by
                        change insAfter π x₀ (castIn (Sum.inr y)) = Sum.inr last
                        simp [insAfter, hcastIn_ne_last, huncastIn_cast, hyx]
                      simp [step1, loopStep, h1]
                    · simp [insAfter, ← hyx, hπy, castOut]
                  · refine Or.inl ⟨y', hy', ?_⟩
                    have h1 : insAfter π x₀ (Sum.inr y.castSucc) = Sum.inr y'.castSucc := by
                      change insAfter π x₀ (castIn (Sum.inr y)) = Sum.inr y'.castSucc
                      simp [insAfter, hcastIn_ne_last, huncastIn_cast, hyx, hπy, castOut]
                    simp [step1, loopStep, h1]
                · rw [heq]
                  refine Or.inl ⟨y, hy, ?_⟩
                  simp [step1, loopStep, hlast]
            intro n
            rcases hinv n with ⟨y, hy, heq⟩ | ⟨heq, y, _, hlast⟩
            · rw [heq]
              obtain ⟨y', _, hπy⟩ := hclosed_step y hy
              by_cases hyx : (Sum.inr y : α ⊕ Fin k) = x₀
              · have h1 : insAfter π x₀ (Sum.inr y.castSucc) = Sum.inr last := by
                  change insAfter π x₀ (castIn (Sum.inr y)) = Sum.inr last
                  simp [insAfter, hcastIn_ne_last, huncastIn_cast, hyx]
                simp [h1]
              · have h1 : insAfter π x₀ (Sum.inr y.castSucc) = Sum.inr y'.castSucc := by
                  change insAfter π x₀ (castIn (Sum.inr y)) = Sum.inr y'.castSucc
                  simp [insAfter, hcastIn_ne_last, huncastIn_cast, hyx, hπy, castOut]
                simp [h1]
            · rw [heq, hlast]; simp
        -- Apply permCycleCount_firstReturn to p1 with predicate Q l := l.1 ≠ last!
        let Q (l : loopClosedSet (insAfter π x₀)) : Prop := l.1 ≠ last
        have hmeetQ : ∀ l : loopClosedSet (insAfter π x₀), ∃ r : ℕ, Q (p1^[r] l) := by
          intro l
          by_cases hl : l.1 = last
          · refine ⟨1, ?_⟩
            change (p1 l).1 ≠ last
            intro heq
            have h1 := hp1 l
            rw [hl, heq] at h1
            exact hcastOut_ne_last (π x₀) (by simpa [insAfter] using h1)
          · exact ⟨0, hl⟩
        let eQ : { l : loopClosedSet (insAfter π x₀) // Q l } ≃ loopClosedSet π :=
          { toFun := fun l => ⟨l.1.1.castPred l.2, (hP_iff _).mp (by simpa [Fin.castSucc_castPred] using l.1.2)⟩
            invFun := fun l => ⟨⟨l.1.castSucc, (hP_iff l.1).mpr l.2⟩, Fin.castSucc_ne_last l.1⟩
            left_inv := fun ⟨⟨l, hl⟩, hne⟩ => by apply Subtype.ext; apply Subtype.ext; simp [Fin.castSucc_castPred]
            right_inv := fun ⟨l, hl⟩ => by apply Subtype.ext; simp }
        let q0 : Equiv.Perm { l : loopClosedSet (insAfter π x₀) // Q l } := eQ.symm.permCongr p0
        have hq0_first : ∀ a : { l : loopClosedSet (insAfter π x₀) // Q l },
            ∃ r : ℕ, 0 < r ∧ (q0 a).1 = p1^[r] a.1 ∧ ∀ j, 0 < j → j < r → ¬ Q (p1^[j] a.1) := by
          intro ⟨⟨l, hl⟩, hne⟩
          let x : Fin k := l.castPred hne
          have hx_cast : x.castSucc = l := Fin.castSucc_castPred l hne
          have hx_mem : ∀ n, (π (step0^[n] (Sum.inr x))).isRight :=
            (hP_iff x).mp (by simpa [hx_cast] using hl)
          have h0 := hp0 ⟨x, hx_mem⟩
          by_cases hx0 : (Sum.inr x : α ⊕ Fin k) = x₀
          · -- Takes 2 steps: l ↦ last ↦ (p0 x).castSucc
            refine ⟨2, by omega, ?_, fun j hj1 hj2 => ?_⟩
            · have hj_eq : (p1 ⟨l, hl⟩).1 = last := by
                have h1 := hp1 ⟨l, hl⟩
                have h2 : insAfter π x₀ (Sum.inr l) = Sum.inr last := by
                  rw [← hx_cast]
                  change insAfter π x₀ (castIn (Sum.inr x)) = Sum.inr last
                  simp [insAfter, hcastIn_ne_last, huncastIn_cast, hx0]
                rw [h2] at h1; exact (Sum.inr.inj h1).symm
              have hstep2 : (p1 (p1 ⟨l, hl⟩)).1 = (p0 ⟨x, hx_mem⟩).1.castSucc := by
                have h1 := hp1 (p1 ⟨l, hl⟩)
                rw [hj_eq] at h1
                have h2 : insAfter π x₀ (Sum.inr last) = Sum.inr (p0 ⟨x, hx_mem⟩).1.castSucc := by
                  simp [insAfter, ← hx0, h0, castOut]
                rw [h2] at h1; exact (Sum.inr.inj h1).symm
              apply Subtype.ext
              change (p0 ⟨x, hx_mem⟩).1.castSucc = (p1 (p1 ⟨l, hl⟩)).1
              exact hstep2.symm
            · have hj1' : j = 1 := by omega
              subst hj1'
              change ¬ ((p1 ⟨l, hl⟩).1 ≠ last)
              rw [not_not]
              have h1 := hp1 ⟨l, hl⟩
              have h2 : insAfter π x₀ (Sum.inr l) = Sum.inr last := by
                rw [← hx_cast]
                change insAfter π x₀ (castIn (Sum.inr x)) = Sum.inr last
                simp [insAfter, hcastIn_ne_last, huncastIn_cast, hx0]
              rw [h2] at h1; exact (Sum.inr.inj h1).symm
          · -- Takes 1 step: l ↦ (p0 x).castSucc
            refine ⟨1, by omega, ?_, fun j hj1 hj2 => by omega⟩
            apply Subtype.ext
            change (p0 ⟨x, hx_mem⟩).1.castSucc = (p1 ⟨l, hl⟩).1
            have h1 := hp1 ⟨l, hl⟩
            have h2 : insAfter π x₀ (Sum.inr l) = Sum.inr (p0 ⟨x, hx_mem⟩).1.castSucc := by
              rw [← hx_cast]
              change insAfter π x₀ (castIn (Sum.inr x)) = Sum.inr (p0 ⟨x, hx_mem⟩).1.castSucc
              simp [insAfter, hcastIn_ne_last, huncastIn_cast, hx0, h0, castOut]
            rw [h2] at h1; exact Sum.inr.inj h1
        have hfirst := permCycleCount_firstReturn p1 Q hmeetQ q0 hq0_first
        have hq0_cyc : permCycleCount q0 = permCycleCount p0 := permCycleCount_equivCongr eQ.symm p0
        rw [← hfirst, hq0_cyc]
      dsimp only [eIns, Equiv.coe_fn_mk]
      simp_rw [hstrand_after]
      split_ifs with hcond
      · rw [hcyc_after]
      · rfl

end

/-- Multinomial divisibility: if `∑ i ∈ s, f i = N`, then `∏ i ∈ s, (f i)! ∣ N!`. -/
lemma prod_factorial_dvd_factorial_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ s, (f i).factorial) ∣ (∑ i ∈ s, f i).factorial := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hmul : (f a).factorial * (∑ i ∈ s, f i).factorial ∣ (f a + ∑ i ∈ s, f i).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add (f a) (∑ i ∈ s, f i)
    exact dvd_trans (Nat.mul_dvd_mul_left (f a).factorial ih) hmul

/-- **Lemma 3.3**: Single-vertex removal (regularity, polynomial identity (E), and (E')). -/
theorem lem_3_3_quad_elim_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d : ℕ) (hreg : IsRegular H d) (hV : 2 ≤ Fintype.card V) (w : V) :
    (∀ σ : nonLoopIn H w ≃ nonLoopOut H w, IsRegular (elimDigraph H w σ) d) ∧
    (circuitPoly H =
      (∏ i ∈ Finset.range (adjMatrix H w w),
        (Polynomial.X + Polynomial.C (((d - adjMatrix H w w + i : ℕ) : ℤ)))) *
      (∑ σ : nonLoopIn H w ≃ nonLoopOut H w, circuitPoly (elimDigraph H w σ))) ∧
    (let M := adjMatrix H
     circuitEval M d =
      (-1 : ℤ) ^ (M w w) * ((M w w).factorial : ℤ) *
        ∑ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
          (profileCount M w R.1 : ℤ) * circuitEval (subMatrix M w + R.1) d) := by
  classical
  -- Step 1: Apply Lemma 5.1 with S = Finset.univ.erase w (nonempty since |V| ≥ 2)
  let S : Finset V := Finset.univ.erase w
  have hS_ne : S.Nonempty := by
    have hcard : S.card = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
    exact Finset.card_pos.mp (by omega)
  have hsplit := lem_5_1_quad_split_proved H d hreg S hS_ne
  -- Note: {v : V // v ∈ S} ≃ {v : V // v ≠ w}, and {v : V // v ∉ S} ≃ Unit (just w!)
  have hmemS : ∀ v : V, v ∈ S ↔ v ≠ w := fun v => by simp [S]
  let eVS : { v : V // v ∈ S } ≃ { v : V // v ≠ w } :=
    Equiv.subtypeEquivRight hmemS
  -- Identify PartialTransition H S with inArcs H w ≃ outArcs H w
  let ePT : PartialTransition H S ≃ (inArcs H w ≃ outArcs H w) :=
    { toFun := fun πT => πT ⟨w, by simp [S]⟩
      invFun := fun πw u =>
        have hu : u.1 = w := by have := u.2; simp [S] at this; exact this
        hu ▸ πw
      left_inv := fun πT => by
        funext u
        have hu : u.1 = w := by have := u.2; simp [S] at this; exact this
        rcases u with ⟨v, hv⟩
        dsimp at hu; subst hu; rfl
      right_inv := fun πw => rfl }
  -- Identify inArcs H w ≃ nonLoopIn H w ⊕ Fin k and outArcs H w ≃ nonLoopOut H w ⊕ Fin k
  set k := adjMatrix H w w
  let Loops := { a : H.Arc // H.tail a = w ∧ H.head a = w }
  have hcard_loops : Fintype.card Loops = k := by
    rw [Fintype.card_subtype]; rfl
  let eL : Loops ≃ Fin k := Fintype.equivFinOfCardEq hcard_loops
  let eInW : inArcs H w ≃ nonLoopIn H w ⊕ Fin k :=
    { toFun := fun a =>
        if ht : H.tail a.1 = w then Sum.inr (eL ⟨a.1, ht, a.2⟩)
        else Sum.inl ⟨a.1, a.2, ht⟩
      invFun := fun s => match s with
        | Sum.inl a => ⟨a.1, a.2.1⟩
        | Sum.inr i => ⟨(eL.symm i).1, (eL.symm i).2.2⟩
      left_inv := fun a => by
        by_cases ht : H.tail a.1 = w
        · simp [ht]
        · simp [ht]
      right_inv := fun s => by
        rcases s with a | i
        · simp [a.2.2]
        · simp [(eL.symm i).2.1] }
  let eOutW : outArcs H w ≃ nonLoopOut H w ⊕ Fin k :=
    { toFun := fun a =>
        if hh : H.head a.1 = w then Sum.inr (eL ⟨a.1, a.2, hh⟩)
        else Sum.inl ⟨a.1, a.2, hh⟩
      invFun := fun s => match s with
        | Sum.inl a => ⟨a.1, a.2.1⟩
        | Sum.inr i => ⟨(eL.symm i).1, (eL.symm i).2.1⟩
      left_inv := fun a => by
        by_cases hh : H.head a.1 = w
        · simp [hh]
        · simp [hh]
      right_inv := fun s => by
        rcases s with a | i
        · simp [a.2.2]
        · simp [(eL.symm i).2.2] }
  have hcard_nli : Fintype.card (nonLoopIn H w) = d - k := by
    have h1 : Fintype.card (inArcs H w) = Fintype.card (nonLoopIn H w) + k := by
      rw [Fintype.card_congr eInW, Fintype.card_sum, Fintype.card_fin]
    have h2 : Fintype.card (inArcs H w) = d := by rw [Fintype.card_subtype]; exact hreg.1 w
    omega
  -- Check regularity of elimDigraph H w σ directly via in/out bijections
  have hreg_elim : ∀ σ : nonLoopIn H w ≃ nonLoopOut H w, IsRegular (elimDigraph H w σ) d := by
    intro σ
    constructor
    · intro v
      let eIn : inArcs (elimDigraph H w σ) v ≃ inArcs H v.1 :=
        { toFun := fun b => match b with
            | ⟨Sum.inl a, hb⟩ => ⟨a.1, congrArg Subtype.val hb⟩
            | ⟨Sum.inr e, hb⟩ => ⟨(σ e).1, congrArg Subtype.val hb⟩
          invFun := fun a =>
            if ht : H.tail a.1 = w then
              let e := σ.symm ⟨a.1, ht, a.2.symm ▸ v.2⟩
              ⟨Sum.inr e, Subtype.ext (by
                change H.head (σ e).1 = v.1
                have h1 : (σ e).1 = a.1 := congrArg Subtype.val (σ.apply_symm_apply _)
                rw [h1]; exact a.2)⟩
            else
              ⟨Sum.inl ⟨a.1, ht, a.2.symm ▸ v.2⟩, Subtype.ext a.2⟩
          left_inv := fun b => by
            rcases b with ⟨⟨a, ha1, ha2⟩ | e, hb⟩
            · apply Subtype.ext; dsimp only; rw [dif_neg ha1]
            · apply Subtype.ext; dsimp only; rw [dif_pos (σ e).2.1]
              exact congrArg Sum.inr (σ.symm_apply_apply e)
          right_inv := fun a => by
            apply Subtype.ext; dsimp only
            by_cases ht : H.tail a.1 = w
            · rw [dif_pos ht]
              change (σ (σ.symm ⟨a.1, ht, a.2.symm ▸ v.2⟩)).1 = a.1
              exact congrArg Subtype.val (σ.apply_symm_apply ⟨a.1, ht, a.2.symm ▸ v.2⟩)
            · rw [dif_neg ht] }
      rw [← Fintype.card_subtype, Fintype.card_congr eIn, Fintype.card_subtype]
      exact hreg.1 v.1
    · intro v
      let eOut : outArcs (elimDigraph H w σ) v ≃ outArcs H v.1 :=
        { toFun := fun b => match b with
            | ⟨Sum.inl a, hb⟩ => ⟨a.1, congrArg Subtype.val hb⟩
            | ⟨Sum.inr e, hb⟩ => ⟨e.1, congrArg Subtype.val hb⟩
          invFun := fun a =>
            if hh : H.head a.1 = w then
              ⟨Sum.inr ⟨a.1, hh, a.2.symm ▸ v.2⟩, Subtype.ext a.2⟩
            else
              ⟨Sum.inl ⟨a.1, a.2.symm ▸ v.2, hh⟩, Subtype.ext a.2⟩
          left_inv := fun b => by
            rcases b with ⟨⟨a, ha1, ha2⟩ | ⟨e, he1, he2⟩, hb⟩
            · apply Subtype.ext; dsimp only; rw [dif_neg ha2]
            · apply Subtype.ext; dsimp only; rw [dif_pos he1]
          right_inv := fun a => by
            apply Subtype.ext; dsimp only
            by_cases hh : H.head a.1 = w
            · rw [dif_pos hh]
            · rw [dif_neg hh] }
      rw [← Fintype.card_subtype, Fintype.card_congr eOut, Fintype.card_subtype]
      exact hreg.2 v.1
  -- Part 2: Prove polynomial identity (E) by rewriting Lemma 5.1's sum over πT via loop_insertion_poly
  have hpolyE : circuitPoly H =
      (∏ i ∈ Finset.range k, (Polynomial.X + Polynomial.C (((d - k + i : ℕ) : ℤ)))) *
      (∑ σ : nonLoopIn H w ≃ nonLoopOut H w, circuitPoly (elimDigraph H w σ)) := by
    rw [hsplit.1]
    -- Map PartialTransition H S ≃ ((nonLoopIn H w ⊕ Fin k) ≃ (nonLoopOut H w ⊕ Fin k))
    let eComb : PartialTransition H S ≃ ((nonLoopIn H w ⊕ Fin k) ≃ (nonLoopOut H w ⊕ Fin k)) :=
      ePT.trans (Equiv.equivCongr eInW eOutW)
    -- For each πT, let σOf πT : nonLoopIn H w ≃ nonLoopOut H w be induced by walkEnd!
    have hwalk_eq : ∀ πT : PartialTransition H S,
        ∃ σ : nonLoopIn H w ≃ nonLoopOut H w,
          circuitPoly (splitDigraph H S πT) = circuitPoly (elimDigraph H w σ) ∧
          (∀ e : nonLoopIn H w, (σ e).1 = (walkEnd H S πT ⟨e.1, (hmemS _).mpr e.2.2, by simp [S, e.2.1]⟩).1) := by
      intro πT
      obtain ⟨fWalk, hfWalk⟩ := walkEnd_bijective H d hreg S πT
      let eEx : nonLoopIn H w ≃ { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } :=
        Equiv.subtypeEquivRight fun a => by simp [S, and_comm]
      let eEn : { a : H.Arc // H.tail a ∉ S ∧ H.head a ∈ S } ≃ nonLoopOut H w :=
        Equiv.subtypeEquivRight fun a => by simp [S]
      let σ : nonLoopIn H w ≃ nonLoopOut H w := (eEx.trans fWalk).trans eEn
      refine ⟨σ, ?_, fun e => hfWalk (eEx e)⟩
      let eA : (splitDigraph H S πT).Arc ≃ (elimDigraph H w σ).Arc :=
        Equiv.sumCongr
          (Equiv.subtypeEquivRight fun a => by simp [S])
          eEx.symm
      exact circuitPoly_eq_of_equiv (splitDigraph H S πT) (elimDigraph H w σ) eVS eA
        (fun b => by rcases b with a | e <;> rfl)
        (fun b => by
          rcases b with a | e
          · rfl
          · apply Subtype.ext
            change H.head (σ (eEx.symm e)).1 = H.head (walkEnd H S πT e).1
            have h1 : (σ (eEx.symm e)).1 = (walkEnd H S πT e).1 := by
              change (fWalk (eEx (eEx.symm e))).1 = (walkEnd H S πT e).1
              rw [eEx.apply_symm_apply]
              exact hfWalk e
            rw [h1])
    let σOf (πT : PartialTransition H S) : nonLoopIn H w ≃ nonLoopOut H w :=
      (hwalk_eq πT).choose
    have hσ_poly : ∀ πT, circuitPoly (splitDigraph H S πT) = circuitPoly (elimDigraph H w (σOf πT)) :=
      fun πT => (hwalk_eq πT).choose_spec.1
    have hσ_walk : ∀ πT (e : nonLoopIn H w),
        (σOf πT e).1 = (walkEnd H S πT ⟨e.1, (hmemS _).mpr e.2.2, by simp [S, e.2.1]⟩).1 :=
      fun πT => (hwalk_eq πT).choose_spec.2
    -- Group sum over πT by σOf πT
    rw [← Finset.sum_fiberwise_of_maps_to (g := σOf) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hpull :
        (∑ πT ∈ Finset.univ.filter (fun πT => σOf πT = σ),
          Polynomial.X ^ cycInsideT H S πT * circuitPoly (splitDigraph H S πT)) =
        (∑ πT : PartialTransition H S,
          if σOf πT = σ then Polynomial.X ^ cycInsideT H S πT else 0) *
          circuitPoly (elimDigraph H w σ) := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun πT _ => ?_
      split_ifs with h
      · rw [hσ_poly, h]
      · simp
    rw [hpull]
    congr 1
    -- Translate sum over πT to sum over π = eComb πT and match loop_insertion_poly!
    have hmatch := loop_insertion_poly (α := nonLoopIn H w) (β := nonLoopOut H w) (d - k) hcard_nli k σ
    rw [← hmatch]
    refine Fintype.sum_equiv eComb _ _ fun πT => ?_
    -- Show: (σOf πT = σ ↔ ∀ a, loopStrandEnd (eComb πT) a = σ a) and cycInsideT H S πT = loopCycleCount (eComb πT)
    let π := eComb πT
    let stepπ := loopStep π
    have hstep_agree : ∀ (n : ℕ) (x : inArcs H w),
        (hhn : H.head ((partialStep H S πT)^[n] x.1) = w) →
        (∀ j < n, H.head ((partialStep H S πT)^[j] x.1) = w) →
        (stepπ^[n] (eInW x)) = eInW ⟨(partialStep H S πT)^[n] x.1, hhn⟩ := by
      intro n
      induction n with
      | zero => intro x _ _; rfl
      | succ n ih =>
        intro x hhn hmin
        have hn_w : H.head ((partialStep H S πT)^[n] x.1) = w := hmin n (by omega)
        have hprev := ih x hn_w (fun j hj => hmin j (by omega))
        rw [Function.iterate_succ_apply', hprev]
        have hstep_val : (partialStep H S πT)^[n + 1] x.1 =
            (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] x.1, hn_w⟩).1 := by
          rw [Function.iterate_succ_apply']
          have hns : H.head ((partialStep H S πT)^[n] x.1) ∉ S := by simp [S, hn_w]
          simp only [partialStep, hns, ↓reduceDIte]
          have hsub : ∀ {v : V} (hv : H.head ((partialStep H S πT)^[n] x.1) = v) (hvs : v ∉ S),
              (πT ⟨H.head ((partialStep H S πT)^[n] x.1), hns⟩
                ⟨(partialStep H S πT)^[n] x.1, rfl⟩).1 =
              (πT ⟨v, hvs⟩ ⟨(partialStep H S πT)^[n] x.1, hv⟩).1 := by
            intro v hv hvs; subst hv; rfl
          exact hsub hn_w (by simp [S])
        have hhead_next : H.head (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] x.1, hn_w⟩).1 = w := by
          rw [← hstep_val]; exact hhn
        have hπ_val : π (eInW ⟨(partialStep H S πT)^[n] x.1, hn_w⟩) =
            eOutW (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] x.1, hn_w⟩) := by
          simp [π, eComb, ePT]
        have htail_next : H.tail (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] x.1, hn_w⟩).1 = w :=
          (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] x.1, hn_w⟩).2
        simp only [stepπ, loopStep, hπ_val, eOutW, Equiv.coe_fn_mk, hhead_next, ↓reduceDIte]
        simp only [eInW, Equiv.coe_fn_mk]
        have ht2 : H.tail ((partialStep H S πT)^[n + 1] x.1) = w := by rw [hstep_val]; exact htail_next
        simp only [ht2, ↓reduceDIte, Sum.inr.injEq]
        congr 1; apply Subtype.ext; exact hstep_val.symm
    have hstrand_eq : ∀ (e : nonLoopIn H w), loopStrandEnd π e = σOf πT e := by
      intro e
      let ex : { a : H.Arc // H.tail a ∈ S ∧ H.head a ∉ S } :=
        ⟨e.1, (hmemS _).mpr e.2.2, by simp [S, e.2.1]⟩
      let m := Nat.find (exit_reaches_S H S πT ex.1 ex.2.1 ex.2.2)
      have hm_pos : 0 < m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        have hspec : H.head ((partialStep H S πT)^[m] ex.1) ∈ S :=
          Nat.find_spec (exit_reaches_S H S πT ex.1 ex.2.1 ex.2.2)
        rw [hm0] at hspec; exact ex.2.2 hspec
      have hmin_w : ∀ j < m, H.head ((partialStep H S πT)^[j] e.1) = w := fun j hj => by
        have := Nat.find_min (exit_reaches_S H S πT ex.1 ex.2.1 ex.2.2) hj
        simp [S] at this; exact this
      have hspec_ne : H.head ((partialStep H S πT)^[m] e.1) ≠ w := by
        have := Nat.find_spec (exit_reaches_S H S πT ex.1 ex.2.1 ex.2.2)
        exact (hmemS _).mp this
      have hwalk_last : (partialStep H S πT)^[m] e.1 =
          (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[m - 1] e.1, hmin_w (m - 1) (by omega)⟩).1 := by
        conv_lhs => rw [← Nat.sub_add_cancel hm_pos, Function.iterate_succ_apply']
        have hns : H.head ((partialStep H S πT)^[m - 1] e.1) ∉ S := by
          simp [S, hmin_w (m - 1) (by omega)]
        simp only [partialStep, hns, ↓reduceDIte]
        have hsub : ∀ {v : V} (hv : H.head ((partialStep H S πT)^[m - 1] e.1) = v) (hvs : v ∉ S),
            (πT ⟨H.head ((partialStep H S πT)^[m - 1] e.1), hns⟩
              ⟨(partialStep H S πT)^[m - 1] e.1, rfl⟩).1 =
            (πT ⟨v, hvs⟩ ⟨(partialStep H S πT)^[m - 1] e.1, hv⟩).1 := by
          intro v hv hvs; subst hv; rfl
        exact hsub (hmin_w (m - 1) (by omega)) (by simp [S])
      have heIn_e : eInW ⟨e.1, e.2.1⟩ = Sum.inl e := by simp [eInW, e.2.2]
      refine loopStrandEnd_eq_of π e (m - 1) (σOf πT e) ?_ fun j hj => ?_
      · rw [show (loopStep π)^[m - 1] (Sum.inl e) = stepπ^[m - 1] (eInW ⟨e.1, e.2.1⟩) by rw [heIn_e],
          hstep_agree (m - 1) ⟨e.1, e.2.1⟩ (hmin_w (m - 1) (by omega))
            (fun j hj => hmin_w j (by omega))]
        have hπ_val : π (eInW ⟨(partialStep H S πT)^[m - 1] e.1, hmin_w (m - 1) (by omega)⟩) =
            eOutW (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[m - 1] e.1, hmin_w (m - 1) (by omega)⟩) := by
          simp [π, eComb, ePT]
        rw [hπ_val]
        have hhne : H.head (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[m - 1] e.1, hmin_w (m - 1) (by omega)⟩).1 ≠ w := by
          rw [← hwalk_last]; exact hspec_ne
        simp only [eOutW, Equiv.coe_fn_mk, hhne, ↓reduceDIte, Sum.inl.injEq]
        apply Subtype.ext
        rw [hσ_walk πT e]
        exact hwalk_last.symm
      · rw [show (loopStep π)^[j] (Sum.inl e) = stepπ^[j] (eInW ⟨e.1, e.2.1⟩) by rw [heIn_e],
          hstep_agree j ⟨e.1, e.2.1⟩ (hmin_w j (by omega))
            (fun r hr => hmin_w r (by omega))]
        have hπ_val : π (eInW ⟨(partialStep H S πT)^[j] e.1, hmin_w j (by omega)⟩) =
            eOutW (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[j] e.1, hmin_w j (by omega)⟩) := by
          simp [π, eComb, ePT]
        rw [hπ_val]
        have hstep_j : (partialStep H S πT)^[j + 1] e.1 =
            (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[j] e.1, hmin_w j (by omega)⟩).1 := by
          rw [Function.iterate_succ_apply']
          have hns : H.head ((partialStep H S πT)^[j] e.1) ∉ S := by simp [S, hmin_w j (by omega)]
          simp only [partialStep, hns, ↓reduceDIte]
          have hsub : ∀ {v : V} (hv : H.head ((partialStep H S πT)^[j] e.1) = v) (hvs : v ∉ S),
              (πT ⟨H.head ((partialStep H S πT)^[j] e.1), hns⟩
                ⟨(partialStep H S πT)^[j] e.1, rfl⟩).1 =
              (πT ⟨v, hvs⟩ ⟨(partialStep H S πT)^[j] e.1, hv⟩).1 := by
            intro v hv hvs; subst hv; rfl
          exact hsub (hmin_w j (by omega)) (by simp [S])
        have hhw : H.head (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[j] e.1, hmin_w j (by omega)⟩).1 = w := by
          rw [← hstep_j]; exact hmin_w (j + 1) (by omega)
        simp [eOutW, hhw]
    change (if σOf πT = σ then Polynomial.X ^ cycInsideT H S πT else 0) =
      (@ite (Polynomial ℤ) (∀ e : nonLoopIn H w, loopStrandEnd π e = σ e) (Classical.propDecidable _) (Polynomial.X ^ loopCycleCount π) 0)
    simp_rw [hstrand_eq]
    by_cases hc : σOf πT = σ
    · rw [if_pos hc, if_pos (fun e => by rw [hc])]
      congr 1
      -- Show cycInsideT H S πT = loopCycleCount (eComb πT) via permCycleCount_equivCongr
      have hclosed_loop : ∀ a : H.Arc,
          (∀ n : ℕ, H.head ((partialStep H S πT)^[n] a) ∉ S) →
          H.tail a = w ∧ H.head a = w := by
        intro a ha
        have hha : H.head a = w := by have := ha 0; simp [S] at this; exact this
        have hta : H.tail a = w := by
          by_contra hne
          rcases exit_reaches_S H S πT a ((hmemS _).mpr hne) (by simp [S, hha]) with ⟨n, hn⟩
          exact ha n hn
        exact ⟨hta, hha⟩
      have hclosed_iff : ∀ l : Fin k,
          (∀ n : ℕ, (π (stepπ^[n] (Sum.inr l))).isRight) ↔
          (∀ n : ℕ, H.head ((partialStep H S πT)^[n] (eL.symm l).1) ∉ S) := by
        intro l
        have heIn_l : eInW ⟨(eL.symm l).1, (eL.symm l).2.2⟩ = Sum.inr l := by
          simp [eInW, (eL.symm l).2.1]
        constructor
        · intro hr
          have hall : ∀ n : ℕ, H.head ((partialStep H S πT)^[n] (eL.symm l).1) = w := by
            intro n
            induction n using Nat.strongRecOn with
            | ind n ih =>
              cases n with
              | zero => exact (eL.symm l).2.2
              | succ m =>
                have hmin : ∀ j ≤ m, H.head ((partialStep H S πT)^[j] (eL.symm l).1) = w :=
                  fun j hj => ih j (by omega)
                have hstep_m : (partialStep H S πT)^[m + 1] (eL.symm l).1 =
                    (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[m] (eL.symm l).1, hmin m (le_refl m)⟩).1 := by
                  rw [Function.iterate_succ_apply']
                  have hns : H.head ((partialStep H S πT)^[m] (eL.symm l).1) ∉ S := by
                    simp [S, hmin m (le_refl m)]
                  simp only [partialStep, hns, ↓reduceDIte]
                  have hsub : ∀ {v : V} (hv : H.head ((partialStep H S πT)^[m] (eL.symm l).1) = v) (hvs : v ∉ S),
                      (πT ⟨H.head ((partialStep H S πT)^[m] (eL.symm l).1), hns⟩
                        ⟨(partialStep H S πT)^[m] (eL.symm l).1, rfl⟩).1 =
                      (πT ⟨v, hvs⟩ ⟨(partialStep H S πT)^[m] (eL.symm l).1, hv⟩).1 := by
                    intro v hv hvs; subst hv; rfl
                  exact hsub (hmin m (le_refl m)) (by simp [S])
                have hrm := hr m
                rw [← heIn_l, hstep_agree m ⟨(eL.symm l).1, (eL.symm l).2.2⟩ (hmin m (le_refl m))
                  (fun j hj => hmin j (le_of_lt hj))] at hrm
                have hπ_val : π (eInW ⟨(partialStep H S πT)^[m] (eL.symm l).1, hmin m (le_refl m)⟩) =
                    eOutW (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[m] (eL.symm l).1, hmin m (le_refl m)⟩) := by
                  simp [π, eComb, ePT]
                rw [hπ_val] at hrm
                rw [hstep_m]
                by_contra hne
                simp [eOutW, hne] at hrm
          intro n; simp [S, hall n]
        · intro ha n
          have hmin : ∀ j ≤ n, H.head ((partialStep H S πT)^[j] (eL.symm l).1) = w := fun j _ => by
            have := ha j; simp [S] at this; exact this
          rw [← heIn_l, hstep_agree n ⟨(eL.symm l).1, (eL.symm l).2.2⟩ (hmin n (le_refl n))
            (fun j hj => hmin j (le_of_lt hj))]
          have hπ_val : π (eInW ⟨(partialStep H S πT)^[n] (eL.symm l).1, hmin n (le_refl n)⟩) =
              eOutW (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] (eL.symm l).1, hmin n (le_refl n)⟩) := by
            simp [π, eComb, ePT]
          rw [hπ_val]
          have hstep_n : (partialStep H S πT)^[n + 1] (eL.symm l).1 =
              (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] (eL.symm l).1, hmin n (le_refl n)⟩).1 := by
            rw [Function.iterate_succ_apply']
            have hns : H.head ((partialStep H S πT)^[n] (eL.symm l).1) ∉ S := ha n
            simp only [partialStep, hns, ↓reduceDIte]
            have hsub : ∀ {v : V} (hv : H.head ((partialStep H S πT)^[n] (eL.symm l).1) = v) (hvs : v ∉ S),
                (πT ⟨H.head ((partialStep H S πT)^[n] (eL.symm l).1), hns⟩
                  ⟨(partialStep H S πT)^[n] (eL.symm l).1, rfl⟩).1 =
                (πT ⟨v, hvs⟩ ⟨(partialStep H S πT)^[n] (eL.symm l).1, hv⟩).1 := by
              intro v hv hvs; subst hv; rfl
            exact hsub (hmin n (le_refl n)) (by simp [S])
          have hhw : H.head (πT ⟨w, by simp [S]⟩ ⟨(partialStep H S πT)^[n] (eL.symm l).1, hmin n (le_refl n)⟩).1 = w := by
            rw [← hstep_n]; have := ha (n + 1); simp [S] at this; exact this
          simp [eOutW, hhw]
      -- Equivalence between closedTArcs H S πT and { l : Fin k // ∀ n, (π (stepπ^[n] (Sum.inr l))).isRight }
      let eClosed : closedTArcs H S πT ≃ { l : Fin k // ∀ n : ℕ, (π (stepπ^[n] (Sum.inr l))).isRight } :=
        { toFun := fun a =>
            ⟨eL ⟨a.1, hclosed_loop a.1 a.2⟩, (hclosed_iff _).mpr (by simpa using a.2)⟩
          invFun := fun l => ⟨(eL.symm l.1).1, (hclosed_iff l.1).mp l.2⟩
          left_inv := fun a => by apply Subtype.ext; simp
          right_inv := fun l => by apply Subtype.ext; simp }
      unfold cycInsideT loopCycleCount
      rw [← permCycleCount_equivCongr eClosed (closedTPerm H S πT)]
      congr 1
      apply Equiv.ext
      intro l
      apply Subtype.ext
      have hπl : π (Sum.inr l.1) = eOutW (πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩) := by
        have heIn_l : eInW ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩ = Sum.inr l.1 := by
          simp [eInW, (eL.symm l.1).2.1]
        rw [← heIn_l]; simp [π, eComb, ePT]
      have hha : H.head (πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩).1 = w := by
        have h1 := ((hclosed_iff l.1).mp l.2) 1
        have hns : H.head (eL.symm l.1).1 ∉ S := by simp [S, (eL.symm l.1).2.2]
        have hstep1 : partialStep H S πT (eL.symm l.1).1 =
            (πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩).1 := by
          simp only [partialStep, hns, ↓reduceDIte]
          have hsub : ∀ {v : V} (hv : H.head (eL.symm l.1).1 = v) (hvs : v ∉ S),
              (πT ⟨H.head (eL.symm l.1).1, hns⟩ ⟨(eL.symm l.1).1, rfl⟩).1 =
              (πT ⟨v, hvs⟩ ⟨(eL.symm l.1).1, hv⟩).1 := by
            intro v hv hvs; subst hv; rfl
          exact hsub (eL.symm l.1).2.2 (by simp [S])
        simp only [Function.iterate_one, hstep1] at h1
        simp [S] at h1; exact h1
      have hπl_inr : π (Sum.inr l.1) =
          Sum.inr (eL ⟨(πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩).1,
            (πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩).2, hha⟩) := by
        rw [hπl]; simp [eOutW, hha]
      have hLHS : (eClosed.permCongr (closedTPerm H S πT) l).1 =
          eL ⟨(πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩).1,
            (πT ⟨w, by simp [S]⟩ ⟨(eL.symm l.1).1, (eL.symm l.1).2.2⟩).2, hha⟩ := by
        change eL ⟨partialStep H S πT (eL.symm l.1).1, _⟩ = _
        congr 1; apply Subtype.ext
        have hns : H.head (eL.symm l.1).1 ∉ S := by simp [S, (eL.symm l.1).2.2]
        simp only [partialStep, hns, ↓reduceDIte]
        have hsub : ∀ {v : V} (hv : H.head (eL.symm l.1).1 = v) (hvs : v ∉ S),
            (πT ⟨H.head (eL.symm l.1).1, hns⟩ ⟨(eL.symm l.1).1, rfl⟩).1 =
            (πT ⟨v, hvs⟩ ⟨(eL.symm l.1).1, hv⟩).1 := by
          intro v hv hvs; subst hv; rfl
        exact hsub (eL.symm l.1).2.2 (by simp [S])
      rw [hLHS]
      exact Sum.inr.inj (hπl_inr.symm.trans (loopClosedPerm_spec π l))
    · rw [if_neg hc, if_neg (fun h => hc (Equiv.ext h))]
  refine ⟨hreg_elim, hpolyE, ?_⟩
  -- Part 3: Evaluate (E) at x = -d and group σ by profile R!
  dsimp only
  set M := adjMatrix H
  have heval_poly := congrArg (Polynomial.eval (-(d : ℤ))) hpolyE
  rw [circuitPoly_eval_eq_circuitEval H d, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_finset_sum] at heval_poly
  have hk_le_d : k ≤ d := by
    have h1 : k = (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a = w).card := rfl
    have h2 : (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a = w) ⊆
        (Finset.univ.filter fun a : H.Arc => H.head a = w) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.2
    calc k ≤ (Finset.univ.filter fun a : H.Arc => H.head a = w).card := Finset.card_le_card h2
      _ = d := hreg.1 w
  have hpref :
      (∏ i ∈ Finset.range k,
        (Polynomial.X + Polynomial.C (((d - k + i : ℕ) : ℤ))).eval (-(d : ℤ))) =
      (-1 : ℤ) ^ k * (k.factorial : ℤ) := by
    have hterm : ∀ i ∈ Finset.range k,
        (Polynomial.X + Polynomial.C (((d - k + i : ℕ) : ℤ))).eval (-(d : ℤ)) =
        (-1 : ℤ) * ((k - i : ℕ) : ℤ) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      omega
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    have hrev : ∏ i ∈ Finset.range k, ((k - i : ℕ) : ℤ) = (k.factorial : ℤ) := by
      rw [← Nat.cast_prod]
      congr 1
      clear hterm heval_poly hpolyE hreg_elim
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.prod_range_succ']
        simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub, Nat.factorial_succ]
        rw [ih, mul_comm]
    exact hrev
  rw [hpref] at heval_poly
  rw [heval_poly]
  congr 1
  -- Define profile R(σ) for each σ : nonLoopIn H w ≃ nonLoopOut H w
  let prof (σ : nonLoopIn H w ≃ nonLoopOut H w) :
      Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ :=
    Matrix.of fun u v =>
      (Finset.univ.filter fun e : nonLoopIn H w => H.tail e.1 = u.1 ∧ H.head (σ e).1 = v.1).card
  have hprof_valid : ∀ σ, ValidProfile M w (prof σ) := by
    intro σ
    constructor
    · intro u
      have hbi : ∑ v : { v : V // v ≠ w }, prof σ u v =
          (Finset.univ.filter fun e : nonLoopIn H w => H.tail e.1 = u.1).card := by
        simp only [prof, Matrix.of_apply]
        rw [← Finset.card_biUnion]
        · congr 1; ext e
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨⟨H.head (σ e).1, (σ e).2.2⟩, h, rfl⟩⟩
        · intro v₁ _ v₂ _ hne
          exact Finset.disjoint_left.mpr fun e he₁ he₂ =>
            hne (Subtype.ext ((Finset.mem_filter.mp he₁).2.2.symm.trans (Finset.mem_filter.mp he₂).2.2))
      rw [hbi]
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2, e.2.1⟩
      · intro e₁ _ e₂ _ h; exact Subtype.ext h
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ⟨⟨a, ha.2, ha.1.symm ▸ u.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1⟩, rfl⟩
    · intro v
      have hbi : ∑ u : { v : V // v ≠ w }, prof σ u v =
          (Finset.univ.filter fun e : nonLoopIn H w => H.head (σ e).1 = v.1).card := by
        simp only [prof, Matrix.of_apply]
        rw [← Finset.card_biUnion]
        · congr 1; ext e
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun ⟨_, h⟩ => h.2, fun h => ⟨⟨H.tail e.1, e.2.2⟩, rfl, h⟩⟩
        · intro u₁ _ u₂ _ hne
          exact Finset.disjoint_left.mpr fun e he₁ he₂ =>
            hne (Subtype.ext ((Finset.mem_filter.mp he₁).2.1.symm.trans (Finset.mem_filter.mp he₂).2.1))
      rw [hbi]
      refine Finset.card_bij (fun e _ => (σ e).1) ?_ ?_ ?_
      · intro e he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (σ e).2.1, (Finset.mem_filter.mp he).2⟩
      · intro e₁ _ e₂ _ h; exact σ.injective (Subtype.ext h)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        let e := σ.symm ⟨a, ha.1, ha.2.symm ▸ v.2⟩
        refine ⟨e, ?_, congrArg Subtype.val (σ.apply_symm_apply ⟨a, ha.1, ha.2.symm ▸ v.2⟩)⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : (σ e).1 = a := congrArg Subtype.val (σ.apply_symm_apply _)
        rw [h1]; exact ha.2
  have hadj_elim : ∀ σ, adjMatrix (elimDigraph H w σ) = subMatrix M w + prof σ := by
    intro σ
    ext u v
    change (Finset.univ.filter fun b : (elimDigraph H w σ).Arc =>
      (elimDigraph H w σ).tail b = u ∧ (elimDigraph H w σ).head b = v).card =
      M u.1 v.1 + prof σ u v
    let A1 := Finset.univ.filter fun a : { a : H.Arc // H.tail a ≠ w ∧ H.head a ≠ w } =>
      H.tail a.1 = u.1 ∧ H.head a.1 = v.1
    let A2 := Finset.univ.filter fun e : nonLoopIn H w =>
      H.tail e.1 = u.1 ∧ H.head (σ e).1 = v.1
    have hcard_sum :
        (Finset.univ.filter fun b : (elimDigraph H w σ).Arc =>
          (elimDigraph H w σ).tail b = u ∧ (elimDigraph H w σ).head b = v).card =
        A1.card + A2.card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_subtype,
        ← Fintype.card_sum]
      refine Fintype.card_congr
        { toFun := fun b => match b with
            | ⟨Sum.inl a, hb⟩ => Sum.inl ⟨a, congrArg Subtype.val hb.1, congrArg Subtype.val hb.2⟩
            | ⟨Sum.inr e, hb⟩ => Sum.inr ⟨e, congrArg Subtype.val hb.1, congrArg Subtype.val hb.2⟩
          invFun := fun s => match s with
            | Sum.inl ⟨a, ha⟩ => ⟨Sum.inl a, Subtype.ext ha.1, Subtype.ext ha.2⟩
            | Sum.inr ⟨e, he⟩ => ⟨Sum.inr e, Subtype.ext he.1, Subtype.ext he.2⟩
          left_inv := fun b => by rcases b with ⟨_ | _, _⟩ <;> rfl
          right_inv := fun s => by rcases s with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl }
    rw [hcard_sum]
    congr 1
    refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
    · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · intro a₁ _ a₂ _ h; exact Subtype.ext h
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ⟨⟨a, ha.1.symm ▸ u.2, ha.2.symm ▸ v.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  -- Count the fiber {σ | prof σ = R} = profileCount M w R via flat non-dependent Index subtype!
  have hfiber_count : ∀ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
      (Finset.univ.filter fun σ : nonLoopIn H w ≃ nonLoopOut H w => prof σ = R.1).card =
        profileCount M w R.1 := by
    intro R
    let C := (Finset.univ.filter fun σ : nonLoopIn H w ≃ nonLoopOut H w => prof σ = R.1).card
    let D := ∏ u : { v : V // v ≠ w }, ∏ v : { v : V // v ≠ w }, (R.1 u v).factorial
    have hD_pos : 0 < D := Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => Nat.factorial_pos _
    have hR_le_d : ∀ u v : { v : V // v ≠ w }, R.1 u v ≤ d := by
      intro u v
      have h1 : R.1 u v ≤ M u.1 w := by
        calc R.1 u v ≤ ∑ v', R.1 u v' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
          _ = M u.1 w := R.2.1 u
      have h2 : M u.1 w ≤ d := by
        have := ((isRegular_iff_adjMatrix H d).mp hreg).1 w
        calc M u.1 w ≤ ∑ u' : V, M u' w :=
            Finset.single_le_sum (f := fun u' : V => M u' w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u.1)
          _ = d := this
      omega
    -- Flat non-dependent index type of triples (u, v, i) with i < R u v!
    let Idx := { t : { v : V // v ≠ w } × { v : V // v ≠ w } × Fin (d + 1) // t.2.2.val < R.1 t.1 t.2.1 }
    letI : DecidableEq Idx := inferInstanceAs
      (DecidableEq { t : { v : V // v ≠ w } × { v : V // v ≠ w } × Fin (d + 1) // t.2.2.val < R.1 t.1 t.2.1 })
    letI : Fintype Idx := inferInstanceAs
      (Fintype { t : { v : V // v ≠ w } × { v : V // v ≠ w } × Fin (d + 1) // t.2.2.val < R.1 t.1 t.2.1 })
    let InBij := { f : nonLoopIn H w ≃ Idx // ∀ e : nonLoopIn H w, (f e).1.1.1 = H.tail e.1 }
    let OutBij := { f : nonLoopOut H w ≃ Idx // ∀ e : nonLoopOut H w, (f e).1.2.1.1 = H.head e.1 }
    letI : Fintype InBij := inferInstanceAs
      (Fintype { f : nonLoopIn H w ≃ Idx // ∀ e : nonLoopIn H w, (f e).1.1.1 = H.tail e.1 })
    letI : Fintype OutBij := inferInstanceAs
      (Fintype { f : nonLoopOut H w ≃ Idx // ∀ e : nonLoopOut H w, (f e).1.2.1.1 = H.head e.1 })
    have hcard_Idx_uv : ∀ u v : { v : V // v ≠ w },
        Fintype.card { t : Idx // t.1.1 = u ∧ t.1.2.1 = v } = R.1 u v := by
      intro u v
      rw [Fintype.card_subtype, ← Fintype.card_fin (R.1 u v)]
      refine Finset.card_bij (fun t ht => ⟨t.1.2.2.val, by
          have h := t.2; have hp := (Finset.mem_filter.mp ht).2; rw [hp.1, hp.2] at h; exact h⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro t₁ ht₁ t₂ ht₂ heq
        have h1 := (Finset.mem_filter.mp ht₁).2
        have h2 := (Finset.mem_filter.mp ht₂).2
        apply Subtype.ext; apply Prod.ext (h1.1.trans h2.1.symm)
        apply Prod.ext (h1.2.trans h2.2.symm)
        exact Fin.ext (congrArg (fun x : Fin (R.1 u v) => x.val) heq)
      · intro i _
        have hlt : i.val < d + 1 := Nat.lt_succ_of_le (le_trans (le_of_lt i.isLt) (hR_le_d u v))
        exact ⟨⟨(u, v, ⟨i.val, hlt⟩), i.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩, Fin.ext rfl⟩
    have hcard_Idx_u : ∀ u : { v : V // v ≠ w },
        Fintype.card { t : Idx // t.1.1 = u } = M u.1 w := by
      intro u
      rw [Fintype.card_subtype, ← R.2.1 u]
      have hbi : (Finset.univ.filter fun t : Idx => t.1.1 = u).card =
          ∑ v : { v : V // v ≠ w }, (Finset.univ.filter fun t : Idx => t.1.1 = u ∧ t.1.2.1 = v).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext t; simp
        · intro v₁ _ v₂ _ hne
          exact Finset.disjoint_left.mpr fun t ht₁ ht₂ =>
            hne ((Finset.mem_filter.mp ht₁).2.2.symm.trans (Finset.mem_filter.mp ht₂).2.2)
      rw [hbi]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Fintype.card_subtype, hcard_Idx_uv u v]
    have hcard_Idx_v : ∀ v : { v : V // v ≠ w },
        Fintype.card { t : Idx // t.1.2.1 = v } = M w v.1 := by
      intro v
      rw [Fintype.card_subtype, ← R.2.2 v]
      have hbi : (Finset.univ.filter fun t : Idx => t.1.2.1 = v).card =
          ∑ u : { v : V // v ≠ w }, (Finset.univ.filter fun t : Idx => t.1.1 = u ∧ t.1.2.1 = v).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext t; simp
        · intro u₁ _ u₂ _ hne
          exact Finset.disjoint_left.mpr fun t ht₁ ht₂ =>
            hne ((Finset.mem_filter.mp ht₁).2.1.symm.trans (Finset.mem_filter.mp ht₂).2.1)
      rw [hbi]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Fintype.card_subtype, hcard_Idx_uv u v]
    have hcard_In : Fintype.card InBij = ∏ u : { v : V // v ≠ w }, (M u.1 w).factorial := by
      have hcard_Pi : Fintype.card (∀ u : { v : V // v ≠ w },
          { e : nonLoopIn H w // H.tail e.1 = u.1 } ≃ { t : Idx // t.1.1 = u }) =
          ∏ u : { v : V // v ≠ w }, (M u.1 w).factorial := by
        rw [Fintype.card_pi]
        refine Finset.prod_congr rfl fun u _ => ?_
        have h1 : Fintype.card { e : nonLoopIn H w // H.tail e.1 = u.1 } = M u.1 w := by
          rw [Fintype.card_subtype]
          refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
          · intro e he; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2, e.2.1⟩
          · intro e₁ _ e₂ _ h; exact Subtype.ext h
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
            exact ⟨⟨a, ha.2, ha.1.symm ▸ u.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1⟩, rfl⟩
        rw [Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq h1)
          (Fintype.equivFinOfCardEq (hcard_Idx_u u))), Fintype.card_perm, Fintype.card_fin]
      rw [← hcard_Pi]
      refine Fintype.card_congr
        { toFun := fun f u =>
            { toFun := fun e => ⟨f.1 e.1, Subtype.ext ((f.2 e.1).trans e.2)⟩
              invFun := fun t => ⟨f.1.symm t.1, by
                have h1 := f.2 (f.1.symm t.1)
                rw [f.1.apply_symm_apply, t.2] at h1; exact h1.symm⟩
              left_inv := fun e => by apply Subtype.ext; exact f.1.symm_apply_apply e.1
              right_inv := fun t => by apply Subtype.ext; exact f.1.apply_symm_apply t.1 }
          invFun := fun F =>
            ⟨{ toFun := fun e => (F ⟨H.tail e.1, e.2.2⟩ ⟨e, rfl⟩).1
               invFun := fun t => ((F t.1.1).symm ⟨t, rfl⟩).1
               left_inv := fun e => by
                 dsimp only
                 have hu : (F ⟨H.tail e.1, e.2.2⟩ ⟨e, rfl⟩).1.1.1 = ⟨H.tail e.1, e.2.2⟩ :=
                   (F ⟨H.tail e.1, e.2.2⟩ ⟨e, rfl⟩).2
                 have hsub : ∀ {u' : { v : V // v ≠ w }} (hu' : u' = ⟨H.tail e.1, e.2.2⟩)
                     (t : { t : Idx // t.1.1 = u' }),
                     ((F u').symm t).1 = ((F ⟨H.tail e.1, e.2.2⟩).symm ⟨t.1, hu' ▸ t.2⟩).1 := by
                   intro u' hu' t; subst hu'; rfl
                 rw [hsub hu]
                 exact congrArg Subtype.val ((F ⟨H.tail e.1, e.2.2⟩).symm_apply_apply ⟨e, rfl⟩)
               right_inv := fun t => by
                 dsimp only
                 have hu : (⟨H.tail ((F t.1.1).symm ⟨t, rfl⟩).1.1, ((F t.1.1).symm ⟨t, rfl⟩).1.2.2⟩ :
                     { v : V // v ≠ w }) = t.1.1 := Subtype.ext ((F t.1.1).symm ⟨t, rfl⟩).2
                 have hsub : ∀ {u' : { v : V // v ≠ w }} (hu' : u' = t.1.1)
                     (a : { e : nonLoopIn H w // H.tail e.1 = u'.1 }),
                     (F u' a).1 = (F t.1.1 ⟨a.1, hu' ▸ a.2⟩).1 := by
                   intro u' hu' a; subst hu'; rfl
                 rw [hsub hu]
                 exact congrArg Subtype.val ((F t.1.1).apply_symm_apply ⟨t, rfl⟩) },
             fun e => congrArg Subtype.val (F ⟨H.tail e.1, e.2.2⟩ ⟨e, rfl⟩).2⟩
          left_inv := fun f => by apply Subtype.ext; apply Equiv.ext; intro e; rfl
          right_inv := fun F => by
            funext u; apply Equiv.ext; intro ⟨e, he⟩; apply Subtype.ext; dsimp only
            have hu : (⟨H.tail e.1, e.2.2⟩ : { v : V // v ≠ w }) = u := Subtype.ext he
            have hsub : ∀ {u' : { v : V // v ≠ w }} (hu' : u' = u)
                (a : { e : nonLoopIn H w // H.tail e.1 = u'.1 }),
                (F u' a).1 = (F u ⟨a.1, hu' ▸ a.2⟩).1 := by
              intro u' hu' a; subst hu'; rfl
            exact hsub hu ⟨e, rfl⟩ }
    have hcard_Out : Fintype.card OutBij = ∏ v : { v : V // v ≠ w }, (M w v.1).factorial := by
      have hcard_Pi : Fintype.card (∀ v : { v : V // v ≠ w },
          { f : nonLoopOut H w // H.head f.1 = v.1 } ≃ { t : Idx // t.1.2.1 = v }) =
          ∏ v : { v : V // v ≠ w }, (M w v.1).factorial := by
        rw [Fintype.card_pi]
        refine Finset.prod_congr rfl fun v _ => ?_
        have h1 : Fintype.card { f : nonLoopOut H w // H.head f.1 = v.1 } = M w v.1 := by
          rw [Fintype.card_subtype]
          refine Finset.card_bij (fun f _ => f.1) ?_ ?_ ?_
          · intro f hf; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.2.1, (Finset.mem_filter.mp hf).2⟩
          · intro f₁ _ f₂ _ h; exact Subtype.ext h
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
            exact ⟨⟨a, ha.1, ha.2.symm ▸ v.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.2⟩, rfl⟩
        rw [Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq h1)
          (Fintype.equivFinOfCardEq (hcard_Idx_v v))), Fintype.card_perm, Fintype.card_fin]
      rw [← hcard_Pi]
      refine Fintype.card_congr
        { toFun := fun f v =>
            { toFun := fun e => ⟨f.1 e.1, Subtype.ext ((f.2 e.1).trans e.2)⟩
              invFun := fun t => ⟨f.1.symm t.1, by
                have h1 := f.2 (f.1.symm t.1)
                rw [f.1.apply_symm_apply, t.2] at h1; exact h1.symm⟩
              left_inv := fun e => by apply Subtype.ext; exact f.1.symm_apply_apply e.1
              right_inv := fun t => by apply Subtype.ext; exact f.1.apply_symm_apply t.1 }
          invFun := fun F =>
            ⟨{ toFun := fun e => (F ⟨H.head e.1, e.2.2⟩ ⟨e, rfl⟩).1
               invFun := fun t => ((F t.1.2.1).symm ⟨t, rfl⟩).1
               left_inv := fun e => by
                 dsimp only
                 have hv : (F ⟨H.head e.1, e.2.2⟩ ⟨e, rfl⟩).1.1.2.1 = ⟨H.head e.1, e.2.2⟩ :=
                   (F ⟨H.head e.1, e.2.2⟩ ⟨e, rfl⟩).2
                 have hsub : ∀ {v' : { v : V // v ≠ w }} (hv' : v' = ⟨H.head e.1, e.2.2⟩)
                     (t : { t : Idx // t.1.2.1 = v' }),
                     ((F v').symm t).1 = ((F ⟨H.head e.1, e.2.2⟩).symm ⟨t.1, hv' ▸ t.2⟩).1 := by
                   intro v' hv' t; subst hv'; rfl
                 rw [hsub hv]
                 exact congrArg Subtype.val ((F ⟨H.head e.1, e.2.2⟩).symm_apply_apply ⟨e, rfl⟩)
               right_inv := fun t => by
                 dsimp only
                 have hv : (⟨H.head ((F t.1.2.1).symm ⟨t, rfl⟩).1.1, ((F t.1.2.1).symm ⟨t, rfl⟩).1.2.2⟩ :
                     { v : V // v ≠ w }) = t.1.2.1 := Subtype.ext ((F t.1.2.1).symm ⟨t, rfl⟩).2
                 have hsub : ∀ {v' : { v : V // v ≠ w }} (hv' : v' = t.1.2.1)
                     (a : { f : nonLoopOut H w // H.head f.1 = v'.1 }),
                     (F v' a).1 = (F t.1.2.1 ⟨a.1, hv' ▸ a.2⟩).1 := by
                   intro v' hv' a; subst hv'; rfl
                 rw [hsub hv]
                 exact congrArg Subtype.val ((F t.1.2.1).apply_symm_apply ⟨t, rfl⟩) },
             fun e => congrArg Subtype.val (F ⟨H.head e.1, e.2.2⟩ ⟨e, rfl⟩).2⟩
          left_inv := fun f => by apply Subtype.ext; apply Equiv.ext; intro e; rfl
          right_inv := fun F => by
            funext v; apply Equiv.ext; intro ⟨e, he⟩; apply Subtype.ext; dsimp only
            have hv : (⟨H.head e.1, e.2.2⟩ : { v : V // v ≠ w }) = v := Subtype.ext he
            have hsub : ∀ {v' : { v : V // v ≠ w }} (hv' : v' = v)
                (a : { f : nonLoopOut H w // H.head f.1 = v'.1 }),
                (F v' a).1 = (F v ⟨a.1, hv' ▸ a.2⟩).1 := by
              intro v' hv' a; subst hv'; rfl
            exact hsub hv ⟨e, rfl⟩ }
    -- Map (fIn, fOut) ↦ fIn.trans fOut.symm has every fiber over {σ | prof σ = R} of size D!
    let proj : InBij × OutBij → nonLoopIn H w ≃ nonLoopOut H w :=
      fun p => p.1.1.trans p.2.1.symm
    have hproj_mem : ∀ p : InBij × OutBij,
        proj p ∈ Finset.univ.filter (fun σ : nonLoopIn H w ≃ nonLoopOut H w => prof σ = R.1) := by
      intro ⟨fIn, fOut⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      ext u v
      change (Finset.univ.filter fun e : nonLoopIn H w =>
        H.tail e.1 = u.1 ∧ H.head (fOut.1.symm (fIn.1 e)).1 = v.1).card = R.1 u v
      rw [← Fintype.card_subtype, ← hcard_Idx_uv u v]
      refine Fintype.card_congr
        { toFun := fun e => ⟨fIn.1 e.1, Subtype.ext ((fIn.2 e.1).trans e.2.1), by
            have h1 := fOut.2 (fOut.1.symm (fIn.1 e.1))
            rw [fOut.1.apply_symm_apply] at h1
            exact Subtype.ext (h1.trans e.2.2)⟩
          invFun := fun t => ⟨fIn.1.symm t.1, by
            have h1 := fIn.2 (fIn.1.symm t.1); rw [fIn.1.apply_symm_apply, t.2.1] at h1; exact h1.symm, by
            rw [fIn.1.apply_symm_apply]
            have h1 := fOut.2 (fOut.1.symm t.1); rw [fOut.1.apply_symm_apply, t.2.2] at h1; exact h1.symm⟩
          left_inv := fun e => by apply Subtype.ext; exact fIn.1.symm_apply_apply e.1
          right_inv := fun t => by apply Subtype.ext; exact fIn.1.apply_symm_apply t.1 }
    have hfiber_D : ∀ σ ∈ Finset.univ.filter (fun σ : nonLoopIn H w ≃ nonLoopOut H w => prof σ = R.1),
        (Finset.univ.filter fun p : InBij × OutBij => proj p = σ).card = D := by
      intro σ hσ
      have hprofσ : prof σ = R.1 := (Finset.mem_filter.mp hσ).2
      have hcard_Fib : Fintype.card (∀ u v : { v : V // v ≠ w },
          { e : nonLoopIn H w // H.tail e.1 = u.1 ∧ H.head (σ e).1 = v.1 } ≃
          { t : Idx // t.1.1 = u ∧ t.1.2.1 = v }) = D := by
        simp only [Fintype.card_pi, D]
        refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => ?_
        have h1 : Fintype.card { e : nonLoopIn H w // H.tail e.1 = u.1 ∧ H.head (σ e).1 = v.1 } = R.1 u v := by
          rw [Fintype.card_subtype, ← hprofσ]; rfl
        rw [Fintype.card_congr (Equiv.equivCongr (Fintype.equivFinOfCardEq h1)
          (Fintype.equivFinOfCardEq (hcard_Idx_uv u v))), Fintype.card_perm, Fintype.card_fin]
      rw [← hcard_Fib, ← Fintype.card_subtype]
      refine Fintype.card_congr
        { toFun := fun p u v =>
            have hp_eq : ∀ x, σ x = p.1.2.1.symm (p.1.1.1 x) := fun x =>
              congrArg (fun f => f x) p.2.symm
            { toFun := fun e => ⟨p.1.1.1 e.1, Subtype.ext ((p.1.1.2 e.1).trans e.2.1), by
                have h1 : p.1.2.1 (σ e.1) = p.1.1.1 e.1 := by
                  rw [hp_eq, p.1.2.1.apply_symm_apply]
                rw [← h1]; exact Subtype.ext ((p.1.2.2 (σ e.1)).trans e.2.2)⟩
              invFun := fun t => ⟨p.1.1.1.symm t.1, by
                have h1 := p.1.1.2 (p.1.1.1.symm t.1); rw [p.1.1.1.apply_symm_apply, t.2.1] at h1; exact h1.symm, by
                have h1 : p.1.2.1 (σ (p.1.1.1.symm t.1)) = t.1 := by
                  rw [hp_eq, p.1.2.1.apply_symm_apply, p.1.1.1.apply_symm_apply]
                have h2 := p.1.2.2 (σ (p.1.1.1.symm t.1)); rw [h1, t.2.2] at h2; exact h2.symm⟩
              left_inv := fun e => by apply Subtype.ext; exact p.1.1.1.symm_apply_apply e.1
              right_inv := fun t => by apply Subtype.ext; exact p.1.1.1.apply_symm_apply t.1 }
          invFun := fun g =>
            let fInEquiv : nonLoopIn H w ≃ Idx :=
              { toFun := fun e => (g ⟨H.tail e.1, e.2.2⟩ ⟨H.head (σ e).1, (σ e).2.2⟩ ⟨e, rfl, rfl⟩).1
                invFun := fun t => ((g t.1.1 t.1.2.1).symm ⟨t, rfl, rfl⟩).1
                left_inv := fun e => by
                  dsimp only
                  have hspec := (g ⟨H.tail e.1, e.2.2⟩ ⟨H.head (σ e).1, (σ e).2.2⟩ ⟨e, rfl, rfl⟩).2
                  have hsub : ∀ {u' v' : { v : V // v ≠ w }}
                      (hu' : u' = ⟨H.tail e.1, e.2.2⟩) (hv' : v' = ⟨H.head (σ e).1, (σ e).2.2⟩)
                      (t : { t : Idx // t.1.1 = u' ∧ t.1.2.1 = v' }),
                      ((g u' v').symm t).1 =
                      ((g ⟨H.tail e.1, e.2.2⟩ ⟨H.head (σ e).1, (σ e).2.2⟩).symm ⟨t.1, hu' ▸ t.2.1, hv' ▸ t.2.2⟩).1 := by
                    intro u' v' hu' hv' t; subst hu'; subst hv'; rfl
                  rw [hsub hspec.1 hspec.2]
                  exact congrArg Subtype.val ((g ⟨H.tail e.1, e.2.2⟩ ⟨H.head (σ e).1, (σ e).2.2⟩).symm_apply_apply ⟨e, rfl, rfl⟩)
                right_inv := fun t => by
                  dsimp only
                  have hspec := ((g t.1.1 t.1.2.1).symm ⟨t, rfl, rfl⟩).2
                  have hu : (⟨H.tail ((g t.1.1 t.1.2.1).symm ⟨t, rfl, rfl⟩).1.1,
                      ((g t.1.1 t.1.2.1).symm ⟨t, rfl, rfl⟩).1.2.2⟩ : { v : V // v ≠ w }) = t.1.1 :=
                    Subtype.ext hspec.1
                  have hv : (⟨H.head (σ ((g t.1.1 t.1.2.1).symm ⟨t, rfl, rfl⟩).1).1,
                      (σ ((g t.1.1 t.1.2.1).symm ⟨t, rfl, rfl⟩).1).2.2⟩ : { v : V // v ≠ w }) = t.1.2.1 :=
                    Subtype.ext hspec.2
                  have hsub : ∀ {u' v' : { v : V // v ≠ w }} (hu' : u' = t.1.1) (hv' : v' = t.1.2.1)
                      (a : { e : nonLoopIn H w // H.tail e.1 = u'.1 ∧ H.head (σ e).1 = v'.1 }),
                      (g u' v' a).1 = (g t.1.1 t.1.2.1 ⟨a.1, hu' ▸ a.2.1, hv' ▸ a.2.2⟩).1 := by
                    intro u' v' hu' hv' a; subst hu'; subst hv'; rfl
                  rw [hsub hu hv]
                  exact congrArg Subtype.val ((g t.1.1 t.1.2.1).apply_symm_apply ⟨t, rfl, rfl⟩) }
            let fIn : InBij := ⟨fInEquiv, fun e =>
              congrArg Subtype.val (g ⟨H.tail e.1, e.2.2⟩ ⟨H.head (σ e).1, (σ e).2.2⟩ ⟨e, rfl, rfl⟩).2.1⟩
            let fOut : OutBij := ⟨σ.symm.trans fInEquiv, fun f => by
              have h1 := (g ⟨H.tail (σ.symm f).1, (σ.symm f).2.2⟩
                ⟨H.head (σ (σ.symm f)).1, (σ (σ.symm f)).2.2⟩ ⟨σ.symm f, rfl, rfl⟩).2.2
              have h2 : H.head (σ (σ.symm f)).1 = H.head f.1 := by rw [σ.apply_symm_apply]
              exact (congrArg Subtype.val h1).trans h2⟩
            ⟨(fIn, fOut), by
              apply Equiv.ext; intro e
              change σ (fInEquiv.symm (fInEquiv e)) = σ e
              rw [fInEquiv.symm_apply_apply]⟩
          left_inv := fun ⟨⟨fIn, fOut⟩, hp⟩ => by
            apply Subtype.ext; apply Prod.ext
            · apply Subtype.ext; apply Equiv.ext; intro e; rfl
            · apply Subtype.ext; apply Equiv.ext; intro f
              change fIn.1 (σ.symm f) = fOut.1 f
              have := congrArg (fun e => fOut.1 (e (σ.symm f))) hp
              dsimp [proj] at this
              rw [fOut.1.apply_symm_apply, σ.apply_symm_apply] at this
              exact this
          right_inv := fun g => by
            funext u v; apply Equiv.ext; intro ⟨e, he1, he2⟩; apply Subtype.ext; dsimp only
            have hu : (⟨H.tail e.1, e.2.2⟩ : { v : V // v ≠ w }) = u := Subtype.ext he1
            have hv : (⟨H.head (σ e).1, (σ e).2.2⟩ : { v : V // v ≠ w }) = v := Subtype.ext he2
            have hsub : ∀ {u' v' : { v : V // v ≠ w }} (hu' : u' = u) (hv' : v' = v)
                (a : { e : nonLoopIn H w // H.tail e.1 = u'.1 ∧ H.head (σ e).1 = v'.1 }),
                (g u' v' a).1 = (g u v ⟨a.1, hu' ▸ a.2.1, hv' ▸ a.2.2⟩).1 := by
              intro u' v' hu' hv' a; subst hu'; subst hv'; rfl
            exact hsub hu hv ⟨e, rfl, rfl⟩ }
    have hbij : C * D =
        (∏ u : { v : V // v ≠ w }, (M u.1 w).factorial) *
        (∏ v : { v : V // v ≠ w }, (M w v.1).factorial) := by
      have htot : (Finset.univ : Finset (InBij × OutBij)).card =
          ∑ σ ∈ Finset.univ.filter (fun σ : nonLoopIn H w ≃ nonLoopOut H w => prof σ = R.1),
            (Finset.univ.filter fun p : InBij × OutBij => proj p = σ).card :=
        Finset.card_eq_sum_card_fiberwise (fun p _ => hproj_mem p)
      rw [Finset.card_univ, Fintype.card_prod, hcard_In, hcard_Out] at htot
      rw [Finset.sum_congr rfl hfiber_D, Finset.sum_const, smul_eq_mul] at htot
      exact htot.symm
    unfold profileCount
    exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt hD_pos) hbij
  -- Group sum over σ by ⟨prof σ, hprof_valid σ⟩
  let profSub (σ : nonLoopIn H w ≃ nonLoopOut H w) :
      { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R } :=
    ⟨prof σ, hprof_valid σ⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := profSub) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun R _ => ?_
  have hconst : ∑ σ ∈ Finset.univ.filter (fun σ => profSub σ = R),
      (circuitPoly (elimDigraph H w σ)).eval (-(d : ℤ)) =
      ∑ _σ ∈ Finset.univ.filter (fun σ => profSub σ = R),
        circuitEval (subMatrix M w + R.1) d := by
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hR : prof σ = R.1 := congrArg Subtype.val (Finset.mem_filter.mp hσ).2
    rw [circuitPoly_eval_eq_circuitEval, hadj_elim, hR]
  rw [hconst, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hfilt : (Finset.univ.filter fun σ : nonLoopIn H w ≃ nonLoopOut H w => profSub σ = R) =
      (Finset.univ.filter fun σ : nonLoopIn H w ≃ nonLoopOut H w => prof σ = R.1) := by
    ext σ; simp [profSub, Subtype.ext_iff]
  rw [hfilt, hfiber_count R]

/-- **Corollary 3.4**: In Lemma 3.3, for every prime `q`,
`v_q(j(M)) ≥ v_q(∏_{u ∈ V} M_{uw}!) + min_R v_q(j(M' + R))`. -/
theorem cor_3_4_quad_elim_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (d q : ℕ) (hreg : IsRegular H d) (hV : 2 ≤ Fintype.card V)
    (w : V) (hq : q.Prime) :
    let M := adjMatrix H
    qVal q (circuitEval M d) ≥
      (padicValNat q (∏ u : V, (M u w).factorial) : ℕ∞) +
        ⨅ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
          qVal q (circuitEval (subMatrix M w + R.1) d) := by
  classical
  dsimp only
  set M := adjMatrix H
  have hE' := (lem_3_3_quad_elim_proved H d hreg hV w).2.2
  dsimp only at hE'
  -- For each valid profile R, ∏_{u ≠ w} (M u w)! divides profileCount M w R
  have hdvd_prof : ∀ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
      (∏ u : { v : V // v ≠ w }, (M u.1 w).factorial) ∣ profileCount M w R.1 := by
    intro R
    have hcol : ∀ v : { v : V // v ≠ w },
        (∏ u : { v : V // v ≠ w }, (R.1 u v).factorial) ∣ (M w v.1).factorial := by
      intro v
      rw [← R.2.2 v]
      exact prod_factorial_dvd_factorial_sum Finset.univ (fun u => R.1 u v)
    have hprod_dvd : (∏ v : { v : V // v ≠ w }, ∏ u : { v : V // v ≠ w }, (R.1 u v).factorial) ∣
        (∏ v : { v : V // v ≠ w }, (M w v.1).factorial) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun v _ => hcol v)
    rw [Finset.prod_comm] at hprod_dvd
    rcases hprod_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    unfold profileCount
    have hD_pos : 0 < ∏ u : { v : V // v ≠ w }, ∏ v : { v : V // v ≠ w }, (R.1 u v).factorial :=
      Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => Nat.factorial_pos _
    rw [hc, ← mul_assoc, mul_comm (∏ u : { v : V // v ≠ w }, (M u.1 w).factorial), mul_assoc,
      Nat.mul_div_cancel_left _ hD_pos]
  -- Pull out ∏_{u : V} (M u w)! from the entire RHS of (E')
  have hcol_split : (∏ u : V, (M u w).factorial) =
      (M w w).factorial * ∏ u : { v : V // v ≠ w }, (M u.1 w).factorial := by
    rw [← Finset.mul_prod_erase Finset.univ (fun u => (M u w).factorial) (Finset.mem_univ w)]
    congr 1
    refine Finset.prod_bij (fun u hu => ⟨u, (Finset.mem_erase.mp hu).1⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro u₁ _ u₂ _ h; exact congrArg Subtype.val h
    · intro u _
      exact ⟨u.1, Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩, Subtype.ext rfl⟩
    · intro _ _; rfl
  let coeff (R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R }) : ℕ :=
    (hdvd_prof R).choose
  have hcoeff_eq : ∀ R, profileCount M w R.1 =
      (∏ u : { v : V // v ≠ w }, (M u.1 w).factorial) * coeff R :=
    fun R => (hdvd_prof R).choose_spec
  have hfactor : circuitEval M d =
      (-1 : ℤ) ^ (M w w) * ((∏ u : V, (M u w).factorial : ℕ) : ℤ) *
        ∑ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
          (coeff R : ℤ) * circuitEval (subMatrix M w + R.1) d := by
    rw [hE', hcol_split, Nat.cast_mul]
    have hsum_eq :
        (∑ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
          (profileCount M w R.1 : ℤ) * circuitEval (subMatrix M w + R.1) d) =
        ((∏ u : { v : V // v ≠ w }, (M u.1 w).factorial : ℕ) : ℤ) *
          ∑ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
            (coeff R : ℤ) * circuitEval (subMatrix M w + R.1) d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun R _ => ?_
      rw [hcoeff_eq R, Nat.cast_mul, mul_assoc]
    rw [hsum_eq]; ring
  rw [hfactor, mul_assoc, qVal_neg_one_pow_mul hq, qVal_mul hq,
    qVal_natCast (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)]
  refine add_le_add (le_refl _) ?_
  -- Show qVal q (∑ R, coeff R * j(M' + R)) ≥ ⨅ R, qVal q (j(M' + R))
  have hterm_ge : ∀ R : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
      (⨅ R' : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
        qVal q (circuitEval (subMatrix M w + R'.1) d)) ≤
      qVal q ((coeff R : ℤ) * circuitEval (subMatrix M w + R.1) d) := by
    intro R
    rw [qVal_mul hq]
    calc ⨅ R' : { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R },
          qVal q (circuitEval (subMatrix M w + R'.1) d)
        ≤ qVal q (circuitEval (subMatrix M w + R.1) d) := iInf_le _ R
      _ ≤ qVal q (coeff R : ℤ) + qVal q (circuitEval (subMatrix M w + R.1) d) := le_add_self
  -- General Finset sum valuation lower bound
  have hsum_ge : ∀ (s : Finset { R : Matrix { v : V // v ≠ w } { v : V // v ≠ w } ℕ // ValidProfile M w R })
      (b : ℕ∞), (∀ R ∈ s, b ≤ qVal q ((coeff R : ℤ) * circuitEval (subMatrix M w + R.1) d)) →
      b ≤ qVal q (∑ R ∈ s, (coeff R : ℤ) * circuitEval (subMatrix M w + R.1) d) := by
    intro s b hb
    induction s using Finset.induction_on with
    | empty => simp [qVal_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact le_trans (le_min (hb a (Finset.mem_insert_self a s))
        (ih fun R hR => hb R (Finset.mem_insert_of_mem hR))) (min_le_qVal_add hq _ _)
  exact hsum_ge Finset.univ _ (fun R _ => hterm_ge R)

/-- **Proposition 3.5**: If `H` is `n`-regular on `N ≥ 1` vertices with all `M_{uv} ≥ 1`, then
`v_q(j(M)) ≥ ∑_{N'=1}^N f_q(n, N')` for every prime `q`. -/
theorem prop_3_5_quad_ind_proved {V : Type} [Fintype V] [DecidableEq V]
    (H : Multidigraph V) (n q : ℕ) (hreg : IsRegular H n) (hV : 1 ≤ Fintype.card V)
    (hpos : ∀ u v : V, 1 ≤ adjMatrix H u v) (hq : q.Prime) :
    qVal q (circuitEval (adjMatrix H) n) ≥
      (∑ N' ∈ Finset.Icc 1 (Fintype.card V), fVal q n N' : ℕ∞) := by
  classical
  -- Induct on N = Fintype.card V, generalizing V and H!
  suffices hgen : ∀ (N : ℕ), 1 ≤ N →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (G : Multidigraph W),
        Fintype.card W = N → IsRegular G n → (∀ u v : W, 1 ≤ adjMatrix G u v) →
        qVal q (circuitEval (adjMatrix G) n) ≥
          (∑ N' ∈ Finset.Icc 1 N, fVal q n N' : ℕ∞) by
    exact hgen (Fintype.card V) hV V H rfl hreg hpos
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    intro W _ _ G hcard hregG hposG
    by_cases hN0 : N = 0
    · -- Base case: |W| = 1
      subst hN0
      have hW1 : Fintype.card W = 1 := hcard
      obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp hW1
      have hMww : adjMatrix G w w = n := by
        have h1 := ((isRegular_iff_adjMatrix G n).mp hregG).1 w
        have huniv : (Finset.univ : Finset W) = {w} := by ext x; simp [hw x]
        rw [huniv, Finset.sum_singleton] at h1
        exact h1
      have h1 := lem_3_1_quad_fact_proved G n hregG
      rw [circuitPoly_eval_eq_circuitEval, hW1, one_mul] at h1
      have huniv : (Finset.univ : Finset W) = {w} := by ext x; simp [hw x]
      have hprod : (∏ u : W, ∏ v : W, ((adjMatrix G u v).factorial : ℤ)) = (n.factorial : ℤ) := by
        rw [huniv, Finset.prod_singleton, Finset.prod_singleton, hMww]
      have hdet : detPowCoeff (adjMatrix G) n = 1 := by
        rw [detPowCoeff_eq_sum]
        let idTup : Fin n → Equiv.Perm W := fun _ => 1
        have huniq : ∀ σ : Fin n → Equiv.Perm W, σ = idTup := fun σ => by
          funext k; apply Equiv.ext; intro x; rw [hw (σ k x), hw x]; rfl
        rw [Finset.sum_eq_single idTup]
        · have hcond : ∀ u v : W, (Finset.univ.filter fun k : Fin n => idTup k u = v).card = adjMatrix G u v := by
            intro u v
            rw [hw u, hw v, hMww]
            simp [idTup]
          rw [if_pos hcond]; simp [idTup]
        · intro σ _ hne; exact absurd (huniq σ) hne
        · intro h; exact absurd (Finset.mem_univ idTup) h
      rw [h1, hprod, hdet, mul_one, qVal_neg_one_pow_mul hq, qVal_natCast (Nat.factorial_ne_zero n)]
      have hn1 : 1 ≤ n := by rw [← hMww]; exact hposG w w
      have hIcc : Finset.Icc 1 1 = {1} := by decide
      rw [hIcc, Finset.sum_singleton, fVal_one hn1]
    · -- Inductive step: |W| = N + 1 ≥ 2
      have hN1 : 1 ≤ N := by omega
      have hW2 : 2 ≤ Fintype.card W := by omega
      have hne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
      let w : W := Classical.arbitrary W
      have hcor := cor_3_4_quad_elim_proved G n q hregG hW2 w hq
      dsimp only at hcor
      -- Column w has N + 1 positive entries summing to n, so v_q(∏_u M_{uw}!) ≥ f_q(n, N + 1)
      have hcol_bound : fVal q n (N + 1) ≤ padicValNat q (∏ u : W, (adjMatrix G u w).factorial) := by
        let eW : Fin (N + 1) ≃ W := (Fintype.equivFinOfCardEq hcard).symm
        let m : Fin (N + 1) → ℕ := fun i => adjMatrix G (eW i) w
        have hm_pos : ∀ i, 0 < m i := fun i => hposG (eW i) w
        have hm_sum : ∑ i, m i = n := by
          rw [Fintype.sum_equiv eW _ (fun u => adjMatrix G u w) (fun _ => rfl)]
          exact ((isRegular_iff_adjMatrix G n).mp hregG).1 w
        have hprod_eq : (∏ i : Fin (N + 1), (m i).factorial) = ∏ u : W, (adjMatrix G u w).factorial :=
          Fintype.prod_equiv eW _ (fun u => (adjMatrix G u w).factorial) (fun _ => rfl)
        rw [← hprod_eq]
        exact fVal_le_of_comp m hm_pos hm_sum
      -- Every valid profile R gives an n-regular digraph on {v // v ≠ w} (card N) with entries ≥ 1
      have hR_bound : ∀ R : { R : Matrix { v : W // v ≠ w } { v : W // v ≠ w } ℕ // ValidProfile (adjMatrix G) w R },
          (∑ N' ∈ Finset.Icc 1 N, fVal q n N' : ℕ∞) ≤
            qVal q (circuitEval (subMatrix (adjMatrix G) w + R.1) n) := by
        intro R
        let M' := subMatrix (adjMatrix G) w + R.1
        let G' := ofMatrix M'
        have hcard' : Fintype.card { v : W // v ≠ w } = N := by
          have h1 := Fintype.card_subtype_compl (fun v : W => v = w)
          have h2 : Fintype.card { v : W // v = w } = 1 := Fintype.card_unique
          have h3 : Fintype.card { v : W // ¬ v = w } = Fintype.card { v : W // v ≠ w } := rfl
          omega
        have hM'_eq : adjMatrix G' = M' := adjMatrix_ofMatrix M'
        have hregG' : IsRegular G' n := by
          rw [isRegular_iff_adjMatrix, hM'_eq]
          have hregM := (isRegular_iff_adjMatrix G n).mp hregG
          constructor
          · intro v
            simp only [M', Matrix.add_apply, subMatrix, Matrix.of_apply, Finset.sum_add_distrib]
            rw [R.2.2 v]
            have hcolG := hregM.1 v.1
            rw [← Finset.add_sum_erase Finset.univ (fun u => adjMatrix G u v.1) (Finset.mem_univ w)] at hcolG
            have hsub_sum : ∑ u : { u : W // u ≠ w }, adjMatrix G u.1 v.1 =
                ∑ u ∈ Finset.univ.erase w, adjMatrix G u v.1 := by
              refine Finset.sum_bij (fun u _ => u.1) ?_ ?_ ?_ ?_
              · intro u _; exact Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩
              · intro u₁ _ u₂ _ h; exact Subtype.ext h
              · intro u hu; exact ⟨⟨u, (Finset.mem_erase.mp hu).1⟩, Finset.mem_univ _, rfl⟩
              · intro _ _; rfl
            rw [hsub_sum]; omega
          · intro u
            simp only [M', Matrix.add_apply, subMatrix, Matrix.of_apply, Finset.sum_add_distrib]
            rw [R.2.1 u]
            have hrowG := hregM.2 u.1
            rw [← Finset.add_sum_erase Finset.univ (fun v => adjMatrix G u.1 v) (Finset.mem_univ w)] at hrowG
            have hsub_sum : ∑ v : { v : W // v ≠ w }, adjMatrix G u.1 v.1 =
                ∑ v ∈ Finset.univ.erase w, adjMatrix G u.1 v := by
              refine Finset.sum_bij (fun v _ => v.1) ?_ ?_ ?_ ?_
              · intro v _; exact Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩
              · intro v₁ _ v₂ _ h; exact Subtype.ext h
              · intro v hv; exact ⟨⟨v, (Finset.mem_erase.mp hv).1⟩, Finset.mem_univ _, rfl⟩
              · intro _ _; rfl
            rw [hsub_sum]; omega
        have hposG' : ∀ u v : { v : W // v ≠ w }, 1 ≤ adjMatrix G' u v := by
          intro u v
          rw [hM'_eq]
          have := hposG u.1 v.1
          change 1 ≤ adjMatrix G u.1 v.1 + R.1 u v
          omega
        have hih := ih hN1 { v : W // v ≠ w } G' hcard' hregG' hposG'
        rwa [hM'_eq] at hih
      have hIcc_split : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnotmem : N + 1 ∉ Finset.Icc 1 N := by simp
      calc (∑ N' ∈ Finset.Icc 1 (N + 1), (fVal q n N' : ℕ∞))
          = (fVal q n (N + 1) : ℕ∞) + ∑ N' ∈ Finset.Icc 1 N, (fVal q n N' : ℕ∞) := by
            rw [hIcc_split, Finset.sum_insert hnotmem]
        _ ≤ (padicValNat q (∏ u : W, (adjMatrix G u w).factorial) : ℕ∞) +
              ⨅ R : { R : Matrix { v : W // v ≠ w } { v : W // v ≠ w } ℕ // ValidProfile (adjMatrix G) w R },
                qVal q (circuitEval (subMatrix (adjMatrix G) w + R.1) n) :=
            add_le_add (Nat.cast_le.mpr hcol_bound) (le_iInf hR_bound)
        _ ≤ qVal q (circuitEval (adjMatrix G) n) := hcor

/-- **Proposition 3.6**: For positive even `n`,
`Δ_n = (-1)^(n/2 + 1) (n - 1)! j(J_{n-1} + I_{n-1})`. -/
theorem prop_3_6_identity_proved (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    delta n =
      (-1 : ℤ) ^ (n / 2 + 1) * ((n - 1).factorial : ℤ) *
        circuitEval (allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)) n := by
  classical
  have hlat := lem_3_2_quad_latin_proved n heven
  have hM : adjMatrix (completeLoopDigraph n) = allOnesMatrix (Fin n) :=
    adjMatrix_ofMatrix (allOnesMatrix (Fin n))
  have hreg : IsRegular (completeLoopDigraph n) n := by
    rw [isRegular_iff_adjMatrix, hM]; simp [allOnesMatrix]
  have hcard : 2 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  let w : Fin n := ⟨n - 1, by omega⟩
  have hE' := (lem_3_3_quad_elim_proved (completeLoopDigraph n) n hreg hcard w).2.2
  dsimp only at hE'
  rw [hM] at hE'
  have hMw : allOnesMatrix (Fin n) w w = 1 := rfl
  -- Identify { v : Fin n // v ≠ w } ≃ Fin (n - 1)
  let eW : { v : Fin n // v ≠ w } ≃ Fin (n - 1) :=
    { toFun := fun v => ⟨v.1.val, by
        have hv1 := v.1.isLt
        have hne : v.1.val ≠ n - 1 := fun h => v.2 (Fin.ext h)
        omega⟩
      invFun := fun i => ⟨⟨i.val, by omega⟩, fun h => by
        have : i.val = n - 1 := congrArg Fin.val h
        omega⟩
      left_inv := fun v => by apply Subtype.ext; apply Fin.ext; rfl
      right_inv := fun i => by apply Fin.ext; rfl }
  -- Every ValidProfile (allOnesMatrix (Fin n)) w R is a permutation matrix on {v // v ≠ w}
  have hprof_perm : ∀ R : { R : Matrix { v : Fin n // v ≠ w } { v : Fin n // v ≠ w } ℕ //
      ValidProfile (allOnesMatrix (Fin n)) w R },
      ∃ p : Equiv.Perm { v : Fin n // v ≠ w }, ∀ u v, R.1 u v = if p u = v then 1 else 0 := by
    intro R
    have huniq_row : ∀ u, ∃! v, R.1 u v = 1 := by
      intro u
      have hsum : ∑ v, R.1 u v = 1 := R.2.1 u
      have hex : ∃ v, R.1 u v ≠ 0 := by
        by_contra h0; push_neg at h0
        simp [h0] at hsum
      rcases hex with ⟨v, hv⟩
      have hle : R.1 u v ≤ 1 := by
        have := Finset.single_le_sum (f := fun v' => R.1 u v') (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        omega
      have hv1 : R.1 u v = 1 := by omega
      refine ⟨v, hv1, fun v' hv' => ?_⟩
      by_contra hne
      have hsum2 : R.1 u v + R.1 u v' ≤ ∑ x, R.1 u x := by
        have hsub : ({v, v'} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun x => R.1 u x) (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair (Ne.symm hne)] at this
        exact this
      omega
    let f : { v : Fin n // v ≠ w } → { v : Fin n // v ≠ w } := fun u => (huniq_row u).choose
    have hf_one : ∀ u, R.1 u (f u) = 1 := fun u => (huniq_row u).choose_spec.1
    have hf_inj : Function.Injective f := by
      intro u₁ u₂ heq
      by_contra hne
      have hcol : ∑ u, R.1 u (f u₁) = 1 := R.2.2 (f u₁)
      have hsum2 : R.1 u₁ (f u₁) + R.1 u₂ (f u₁) ≤ ∑ u, R.1 u (f u₁) := by
        have hsub : ({u₁, u₂} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun u => R.1 u (f u₁)) (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair hne] at this
        exact this
      have h1 := hf_one u₁
      have h2 : R.1 u₂ (f u₁) = 1 := by rw [heq]; exact hf_one u₂
      omega
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj), fun u v => ?_⟩
    by_cases hv : f u = v
    · subst hv; simp [hf_one u]
    · simp only [Equiv.ofBijective_apply, hv, ↓reduceIte]
      by_contra hne0
      have hsum : ∑ x, R.1 u x = 1 := R.2.1 u
      have hsum2 : R.1 u (f u) + R.1 u v ≤ ∑ x, R.1 u x := by
        have hsub : ({f u, v} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun x => R.1 u x) (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair hv] at this
        exact this
      have := hf_one u
      omega
  -- Bijection between ValidProfile and Equiv.Perm (Fin (n - 1))
  let permMat (p : Equiv.Perm { v : Fin n // v ≠ w }) :
      Matrix { v : Fin n // v ≠ w } { v : Fin n // v ≠ w } ℕ :=
    Matrix.of fun u v => if p u = v then 1 else 0
  have hpermMat_valid : ∀ p : Equiv.Perm { v : Fin n // v ≠ w },
      ValidProfile (allOnesMatrix (Fin n)) w (permMat p) := by
    intro p
    constructor
    · intro u; simp [permMat, allOnesMatrix]
    · intro v
      have h1 : ∀ u, (if p u = v then (1 : ℕ) else 0) = if u = p.symm v then 1 else 0 := by
        intro u; by_cases h : u = p.symm v
        · subst h; simp
        · have hne : p u ≠ v := fun hp => h (p.injective (hp.trans (p.apply_symm_apply v).symm))
          simp [h, hne]
      simp [permMat, allOnesMatrix, h1]
  let eProf : Equiv.Perm { v : Fin n // v ≠ w } ≃
      { R : Matrix { v : Fin n // v ≠ w } { v : Fin n // v ≠ w } ℕ // ValidProfile (allOnesMatrix (Fin n)) w R } :=
    { toFun := fun p => ⟨permMat p, hpermMat_valid p⟩
      invFun := fun R => (hprof_perm R).choose
      left_inv := fun p => by
        apply Equiv.ext; intro u
        have hspec := (hprof_perm ⟨permMat p, hpermMat_valid p⟩).choose_spec u (p u)
        change (if p u = p u then 1 else 0) = if _ = p u then 1 else 0 at hspec
        simp only [↓reduceIte] at hspec
        by_contra hne
        rw [if_neg hne] at hspec
        omega
      right_inv := fun R => by
        apply Subtype.ext; ext u v
        exact ((hprof_perm R).choose_spec u v).symm }
  -- Every permutation profile has profileCount = 1 and circuitEval (J + P) = circuitEval (J + I)!
  have hterm_eq : ∀ p : Equiv.Perm { v : Fin n // v ≠ w },
      (profileCount (allOnesMatrix (Fin n)) w (permMat p) : ℤ) *
        circuitEval (subMatrix (allOnesMatrix (Fin n)) w + permMat p) n =
      circuitEval (allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)) n := by
    intro p
    have hpc : profileCount (allOnesMatrix (Fin n)) w (permMat p) = 1 := by
      unfold profileCount
      have hnum : (∏ u : { v : Fin n // v ≠ w }, (allOnesMatrix (Fin n) u.1 w).factorial) *
          (∏ v : { v : Fin n // v ≠ w }, (allOnesMatrix (Fin n) w v.1).factorial) = 1 := by
        simp [allOnesMatrix]
      have hden : (∏ u : { v : Fin n // v ≠ w }, ∏ v : { v : Fin n // v ≠ w }, (permMat p u v).factorial) = 1 := by
        refine Finset.prod_eq_one fun u _ => Finset.prod_eq_one fun v _ => ?_
        simp only [permMat, Matrix.of_apply]
        split_ifs <;> simp
      rw [hnum, hden]
    rw [hpc, Nat.cast_one, one_mul]
    -- Show circuitEval (subMatrix J w + permMat p) n = circuitEval (J_{n-1} + I_{n-1}) n via Lemma 3.1!
    let M₁ := subMatrix (allOnesMatrix (Fin n)) w + permMat p
    let M₂ := allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)
    have hcardW : Fintype.card { v : Fin n // v ≠ w } = n - 1 := by
      rw [Fintype.card_congr eW, Fintype.card_fin]
    have hreg1 : IsRegular (ofMatrix M₁) n := by
      rw [isRegular_iff_adjMatrix, adjMatrix_ofMatrix]
      constructor
      · intro v
        simp only [M₁, Matrix.add_apply, subMatrix, allOnesMatrix, permMat, Matrix.of_apply,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcardW]
        have h1 : ∑ u : { v : Fin n // v ≠ w }, (if p u = v then 1 else 0) = 1 := by
          have h2 : ∀ u, (if p u = v then (1 : ℕ) else 0) = if u = p.symm v then 1 else 0 := fun u => by
            by_cases h : u = p.symm v
            · subst h; simp
            · have hne : p u ≠ v := fun hp => h (p.injective (hp.trans (p.apply_symm_apply v).symm))
              simp [h, hne]
          simp [h2]
        rw [h1]; omega
      · intro u
        simp only [M₁, Matrix.add_apply, subMatrix, allOnesMatrix, permMat, Matrix.of_apply,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcardW]
        simp; omega
    have hreg2 : IsRegular (ofMatrix M₂) n := by
      rw [isRegular_iff_adjMatrix, adjMatrix_ofMatrix]
      constructor
      · intro v
        simp [M₂, allOnesMatrix, Matrix.one_apply, Finset.sum_add_distrib]
        omega
      · intro u
        simp [M₂, allOnesMatrix, Matrix.one_apply, Finset.sum_add_distrib]
        omega
    have hL1 := lem_3_1_quad_fact_proved (ofMatrix M₁) n hreg1
    have hL2 := lem_3_1_quad_fact_proved (ofMatrix M₂) n hreg2
    rw [adjMatrix_ofMatrix] at hL1 hL2
    change (circuitPoly (ofMatrix M₁)).eval (-(n : ℤ)) = (circuitPoly (ofMatrix M₂)).eval (-(n : ℤ))
    rw [hL1, hL2, hcardW, Fintype.card_fin]
    have hprod1 : (∏ u : { v : Fin n // v ≠ w }, ∏ v : { v : Fin n // v ≠ w }, ((M₁ u v).factorial : ℤ)) =
        (∏ u : Fin (n - 1), ∏ v : Fin (n - 1), ((M₂ u v).factorial : ℤ)) := by
      refine Fintype.prod_equiv eW _ _ fun u => ?_
      refine Fintype.prod_equiv (p.symm.trans eW) _ _ fun v => ?_
      have hcond : (p u = v) ↔ (eW u = eW (p.symm v)) := by
        constructor
        · intro h; rw [← h, p.symm_apply_apply]
        · intro h; have := eW.injective h; rw [this, p.apply_symm_apply]
      simp only [M₁, M₂, Matrix.add_apply, subMatrix, allOnesMatrix, permMat, Matrix.of_apply,
        Matrix.one_apply, Equiv.trans_apply]
      by_cases h : p u = v
      · rw [if_pos h, if_pos (hcond.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hcond.mpr h'))]
    rw [hprod1]
    congr 1
    -- detPowCoeff M₁ n = detPowCoeff M₂ n by τ ↦ (fun k => eW.permCongr (p⁻¹ * τ k))
    rw [detPowCoeff_eq_sum M₁ n, detPowCoeff_eq_sum M₂ n]
    let eTup : (Fin n → Equiv.Perm { v : Fin n // v ≠ w }) ≃ (Fin n → Equiv.Perm (Fin (n - 1))) :=
      Equiv.piCongrRight fun _ => (Equiv.mulLeft p⁻¹).trans (Equiv.permCongr eW)
    refine Fintype.sum_equiv eTup _ _ fun τ => ?_
    have hcond_iff :
        (∀ u v : { v : Fin n // v ≠ w }, (Finset.univ.filter fun k : Fin n => τ k u = v).card = M₁ u v) ↔
        (∀ u v : Fin (n - 1), (Finset.univ.filter fun k : Fin n => eTup τ k u = v).card = M₂ u v) := by
      have hstep : ∀ u v : { v : Fin n // v ≠ w },
          (Finset.univ.filter fun k : Fin n => τ k u = v).card =
          (Finset.univ.filter fun k : Fin n => eTup τ k (eW u) = eW (p⁻¹ v)).card := by
        intro u v
        congr 1; ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have heval_k : eTup τ k (eW u) = eW (p⁻¹ (τ k u)) := by
          change eW ((p⁻¹ * τ k) (eW.symm (eW u))) = eW (p⁻¹ (τ k u))
          rw [eW.symm_apply_apply]; rfl
        rw [heval_k]
        constructor
        · intro h; rw [h]
        · intro h
          exact p⁻¹.injective (eW.injective h)
      have hMeq : ∀ u v : { v : Fin n // v ≠ w }, M₁ u v = M₂ (eW u) (eW (p⁻¹ v)) := by
        intro u v
        have hcond : (p u = v) ↔ (eW u = eW (p⁻¹ v)) := by
          constructor
          · intro h; rw [← h]; simp
          · intro h; have := eW.injective h; rw [this]; simp
        simp only [M₁, M₂, Matrix.add_apply, subMatrix, allOnesMatrix, permMat, Matrix.of_apply,
          Matrix.one_apply]
        by_cases h : p u = v
        · rw [if_pos h, if_pos (hcond.mp h)]
        · rw [if_neg h, if_neg (fun hh => h (hcond.mpr hh))]
      constructor
      · intro h u' v'
        let u := eW.symm u'
        let v := p (eW.symm v')
        have hu : eW u = u' := eW.apply_symm_apply u'
        have hv : eW (p⁻¹ v) = v' := by simp [v]
        rw [← hu, ← hv, ← hstep u v, ← hMeq u v]
        exact h u v
      · intro h u v
        rw [hstep u v, hMeq u v]
        exact h (eW u) (eW (p⁻¹ v))
    have hsign_eq :
        (∏ k : Fin n, (Equiv.Perm.sign (τ k) : ℤ)) =
        ∏ k : Fin n, (Equiv.Perm.sign (eTup τ k) : ℤ) := by
      have h1 : ∀ k : Fin n, (Equiv.Perm.sign (eTup τ k) : ℤ) =
          (Equiv.Perm.sign p : ℤ) * (Equiv.Perm.sign (τ k) : ℤ) := by
        intro k
        have heq_k : eTup τ k = eW.permCongr (p⁻¹ * τ k) := rfl
        rw [heq_k, Equiv.Perm.sign_permCongr, map_mul, map_inv, Int.units_inv_eq_self, Units.val_mul]
      simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hpeven_gen : ∀ (k : ℕ), Even k → (Equiv.Perm.sign p : ℤ) ^ k = 1 := fun k ⟨m, hm⟩ => by
        rw [hm, ← two_mul, pow_mul]
        rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
      rw [hpeven_gen n heven, one_mul]
    by_cases hc : ∀ u v : { v : Fin n // v ≠ w },
        (Finset.univ.filter fun k : Fin n => τ k u = v).card = M₁ u v
    · rw [if_pos hc, if_pos (hcond_iff.mp hc), hsign_eq]
    · rw [if_neg hc, if_neg (fun h => hc (hcond_iff.mpr h))]
  -- Assemble the final identity!
  have hsum_eval :
      (∑ R : { R : Matrix { v : Fin n // v ≠ w } { v : Fin n // v ≠ w } ℕ //
        ValidProfile (allOnesMatrix (Fin n)) w R },
        (profileCount (allOnesMatrix (Fin n)) w R.1 : ℤ) *
          circuitEval (subMatrix (allOnesMatrix (Fin n)) w + R.1) n) =
      ((n - 1).factorial : ℤ) *
        circuitEval (allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)) n := by
    rw [← Fintype.sum_equiv eProf _ _ (fun _ => rfl)]
    simp_rw [eProf, Equiv.coe_fn_mk, hterm_eq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_congr eW,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hMw, pow_one, Nat.factorial_one, Nat.cast_one, mul_one, hsum_eval] at hE'
  have hdelta_j : delta n = (-1 : ℤ) ^ (n / 2) * circuitEval (allOnesMatrix (Fin n)) n := by
    have hsq : (-1 : ℤ) ^ (n / 2) * (-1 : ℤ) ^ (n / 2) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hlat' : circuitEval (allOnesMatrix (Fin n)) n = (-1 : ℤ) ^ (n / 2) * delta n := by
      unfold circuitEval
      exact hlat.1.trans hlat.2
    calc delta n = ((-1 : ℤ) ^ (n / 2) * (-1 : ℤ) ^ (n / 2)) * delta n := by rw [hsq, one_mul]
      _ = (-1 : ℤ) ^ (n / 2) * ((-1 : ℤ) ^ (n / 2) * delta n) := by ring
      _ = (-1 : ℤ) ^ (n / 2) * circuitEval (allOnesMatrix (Fin n)) n := by rw [← hlat']
  rw [hdelta_j, hE', pow_succ]
  ring

end AlonTarsi.Proofs

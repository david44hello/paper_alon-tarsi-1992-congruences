module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Defs.Basic
public import AlonTarsi.Defs.Circuit
public import AlonTarsi.Proofs.LatinBasics
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Quadratic Valuation Bounds (Section 4)

Proves the pure arithmetic and valuation lemmas of Section 4:
- Valuation helper lemmas for `qVal : ℕ → ℤ → ℕ∞` (`qVal_zero`, `qVal_mul`, `natCast_le_qVal_iff_dvd`).
- Lower bounds on `f_q(n, N)` and the sum `Q = ∑_{N=2}^{n-1} f_q(n, N)`.
- Theorem 4.1 (`thm_4_1_quadratic_of`), Corollary 4.2 (`cor_4_2_floor_of`),
  the `n = 3q - 1` bound (`sec5_three_q_minus_one_of`), and exact DP evaluation
  of `f_2(n, N)` for `n = 2, 4, 6, 8, 10, 26`.
-/

namespace AlonTarsi.Proofs

open AlonTarsi

/-! ### `qVal` basic properties -/

lemma qVal_zero (q : ℕ) : qVal q 0 = ⊤ := if_pos rfl

lemma qVal_of_ne_zero (q : ℕ) {x : ℤ} (hx : x ≠ 0) :
    qVal q x = (padicValInt q x : ℕ∞) := if_neg hx

lemma natCast_le_qVal_iff_dvd {q : ℕ} (hq : q.Prime) (k : ℕ) (x : ℤ) :
    (k : ℕ∞) ≤ qVal q x ↔ ((q : ℤ) ^ k ∣ x) := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hx : x = 0
  · subst hx; simp [qVal_zero]
  · rw [qVal_of_ne_zero q hx, Nat.cast_le, padicValInt_dvd_iff]
    simp [hx]

lemma qVal_natCast {q n : ℕ} (hn : n ≠ 0) :
    qVal q (n : ℤ) = (padicValNat q n : ℕ∞) := by
  rw [qVal_of_ne_zero q (Nat.cast_ne_zero.mpr hn)]
  rfl

lemma qVal_mul {q : ℕ} (hq : q.Prime) (x y : ℤ) :
    qVal q (x * y) = qVal q x + qVal q y := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hx : x = 0
  · subst hx; simp [qVal_zero]
  · by_cases hy : y = 0
    · subst hy; simp [qVal_zero]
    · rw [qVal_of_ne_zero q (mul_ne_zero hx hy), qVal_of_ne_zero q hx, qVal_of_ne_zero q hy,
        padicValInt.mul hx hy, Nat.cast_add]

lemma qVal_neg (q : ℕ) (x : ℤ) : qVal q (-x) = qVal q x := by
  by_cases hx : x = 0
  · subst hx; simp [qVal_zero]
  · rw [qVal_of_ne_zero q (neg_ne_zero.mpr hx), qVal_of_ne_zero q hx]
    simp [padicValInt]

lemma qVal_neg_one_pow_mul {q : ℕ} (hq : q.Prime) (k : ℕ) (x : ℤ) :
    qVal q ((-1 : ℤ) ^ k * x) = qVal q x := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have : (-1 : ℤ) ^ (m + m) = 1 := by rw [← two_mul, pow_mul]; norm_num
    rw [this, one_mul]
  · have : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [this, neg_one_mul, qVal_neg]

lemma min_le_qVal_add {q : ℕ} (hq : q.Prime) (x y : ℤ) :
    min (qVal q x) (qVal q y) ≤ qVal q (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, qVal_zero]; exact le_top
  · by_cases hx : x = 0
    · subst hx; simp [qVal_zero]
    · by_cases hy : y = 0
      · subst hy; simp [qVal_zero]
      · rw [qVal_of_ne_zero q hx, qVal_of_ne_zero q hy]
        have hmin : min (padicValInt q x : ℕ∞) (padicValInt q y : ℕ∞) =
            ((min (padicValInt q x) (padicValInt q y) : ℕ) : ℕ∞) := by
          rcases le_total (padicValInt q x) (padicValInt q y) with h | h
          · rw [min_eq_left h, min_eq_left (Nat.cast_le.mpr h)]
          · rw [min_eq_right h, min_eq_right (Nat.cast_le.mpr h)]
        rw [hmin, natCast_le_qVal_iff_dvd hq]
        have h1 : (q : ℤ) ^ min (padicValInt q x) (padicValInt q y) ∣ x :=
          (natCast_le_qVal_iff_dvd hq _ _).mp
            (by rw [qVal_of_ne_zero q hx, Nat.cast_le]; exact min_le_left _ _)
        have h2 : (q : ℤ) ^ min (padicValInt q x) (padicValInt q y) ∣ y :=
          (natCast_le_qVal_iff_dvd hq _ _).mp
            (by rw [qVal_of_ne_zero q hy, Nat.cast_le]; exact min_le_right _ _)
        exact dvd_add h1 h2

lemma iInf_le_qVal_sum {ι : Type*} {q : ℕ} (hq : q.Prime) (s : Finset ι) (f : ι → ℤ) :
    (⨅ i ∈ s, qVal q (f i)) ≤ qVal q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qVal_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.iInf_insert]
    exact le_trans (min_le_min_left _ ih) (min_le_qVal_add hq _ _)

lemma padicValNat_finset_prod {ι : Type*} {q : ℕ} [Fact q.Prime] (s : Finset ι)
    (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat q (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-! ### Elementary `fVal` bounds -/

lemma fVal_one {q n : ℕ} (hn : 0 < n) : fVal q n 1 = padicValNat q n.factorial := by
  unfold fVal
  have hset : { k : ℕ | ∃ m : Fin 1 → ℕ, (∀ i, 0 < m i) ∧ (∑ i, m i = n) ∧
      k = padicValNat q (∏ i, (m i).factorial) } = {padicValNat q n.factorial} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, _, hsum, rfl⟩
      simp only [Fin.sum_univ_one, Fin.prod_univ_one] at hsum ⊢
      rw [hsum]
    · rintro rfl
      exact ⟨fun _ => n, fun _ => hn, by simp, by simp⟩
  rw [hset, csInf_singleton]

lemma fVal_le_of_comp {q n N : ℕ} (m : Fin N → ℕ) (hpos : ∀ i, 0 < m i)
    (hsum : ∑ i, m i = n) :
    fVal q n N ≤ padicValNat q (∏ i, (m i).factorial) :=
  Nat.sInf_le ⟨m, hpos, hsum, rfl⟩

lemma comp_set_nonempty {q n N : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    { k : ℕ | ∃ m : Fin N → ℕ, (∀ i, 0 < m i) ∧ (∑ i, m i = n) ∧
      k = padicValNat q (∏ i, (m i).factorial) }.Nonempty := by
  let m : Fin N → ℕ := fun i => if i.val = 0 then n - N + 1 else 1
  refine ⟨padicValNat q (∏ i, (m i).factorial), m, ?_, ?_, rfl⟩
  · intro i; dsimp [m]; split_ifs <;> omega
  · have h0 : (⟨0, hN1⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ h0]
    have hrest : ∑ i ∈ Finset.univ.erase (⟨0, hN1⟩ : Fin N), m i = N - 1 := by
      have h1 : ∀ i ∈ Finset.univ.erase (⟨0, hN1⟩ : Fin N), m i = 1 := by
        intro i hi
        have hv : i.val ≠ 0 := fun hv => (Finset.mem_erase.mp hi).1 (Fin.ext hv)
        simp [m, hv]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem h0,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [hrest]
    simp only [m, ↓reduceIte]
    omega

lemma le_fVal_of_forall {q n N b : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ n)
    (h : ∀ m : Fin N → ℕ, (∀ i, 0 < m i) → (∑ i, m i = n) →
      b ≤ padicValNat q (∏ i, (m i).factorial)) :
    b ≤ fVal q n N := by
  obtain ⟨m, hpos, hsum, heq⟩ := Nat.sInf_mem (comp_set_nonempty (q := q) hN1 hNn)
  rw [fVal, heq]
  exact h m hpos hsum

/-- `v_q(m!) ≥ m / q` for every prime `q` and every `m : ℕ`. -/
lemma div_le_padicValNat_factorial {q : ℕ} (hq : q.Prime) (m : ℕ) :
    m / q ≤ padicValNat q m.factorial := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hm : m < q
  · rw [Nat.div_eq_of_lt hm]; exact Nat.zero_le _
  · have hlog : 1 ≤ Nat.log q m := Nat.le_log_of_pow_le hq.one_lt (by simpa using not_lt.mp hm)
    rw [padicValNat_factorial (Nat.lt_succ_self (Nat.log q m))]
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log q m + 1) :=
      Finset.mem_Ico.mpr ⟨le_refl 1, Nat.lt_succ_of_le hlog⟩
    calc m / q = m / q ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log q m + 1), m / q ^ i :=
        Finset.single_le_sum (f := fun i => m / q ^ i) (fun _ _ => Nat.zero_le _) hmem

/-- Core lower bound: `q * f_q(n, N) + N * (q - 1) ≥ n` for `1 ≤ N ≤ n`. -/
lemma linear_lower_bound_fVal {q n N : ℕ} (hq : q.Prime) (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    n ≤ q * fVal q n N + N * (q - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, _, hsum, heq⟩ := Nat.sInf_mem (comp_set_nonempty (q := q) hN1 hNn)
  rw [fVal, heq]
  have hprod : padicValNat q (∏ i : Fin N, (m i).factorial) =
      ∑ i : Fin N, padicValNat q (m i).factorial :=
    padicValNat_finset_prod Finset.univ (fun i => (m i).factorial)
      (fun i _ => Nat.factorial_ne_zero (m i))
  rw [hprod, Finset.mul_sum]
  have hterm : ∀ i : Fin N, m i ≤ q * padicValNat q (m i).factorial + (q - 1) := by
    intro i
    have hdiv := div_le_padicValNat_factorial hq (m i)
    have hmod : m i % q ≤ q - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt (m i) hq.pos)
    have heucl := Nat.div_add_mod (m i) q
    nlinarith
  calc n = ∑ i : Fin N, m i := hsum.symm
    _ ≤ ∑ i : Fin N, (q * padicValNat q (m i).factorial + (q - 1)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i : Fin N, q * padicValNat q (m i).factorial) + N * (q - 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- For `q = 2` and `1 ≤ N ≤ n`, `f_2(n, N) ≥ (n - N + 1) / 2` (i.e. `⌈(n - N)/2⌉`). -/
lemma fVal_two_ge {n N : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    (n - N + 1) / 2 ≤ fVal 2 n N := by
  have h := linear_lower_bound_fVal Nat.prime_two hN1 hNn
  omega

/-- Exact identity `∑_{N=1}^{n-1} ⌈(n - N)/2⌉ = n^2 / 4` for even `n`. -/
lemma sum_ceil_half_eq_sq_div_four {n : ℕ} (heven : Even n) :
    (∑ N ∈ Finset.Icc 1 (n - 1), (n - N + 1) / 2) = n ^ 2 / 4 := by
  rcases heven with ⟨k, rfl⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum_shift :
        (∑ N ∈ Finset.Icc 1 (k + 1 + (k + 1) - 1), (k + 1 + (k + 1) - N + 1) / 2) =
        (∑ i ∈ Finset.Icc 1 (2 * k + 1), (i + 1) / 2) := by
      refine Finset.sum_bij (fun N _ => 2 * k + 2 - N) ?_ ?_ ?_ ?_
      · intro N hN; simp only [Finset.mem_Icc] at hN ⊢; omega
      · intro N₁ hN₁ N₂ hN₂ h; simp only [Finset.mem_Icc] at hN₁ hN₂; omega
      · intro i hi; refine ⟨2 * k + 2 - i, ?_, ?_⟩ <;> (simp only [Finset.mem_Icc] at hi ⊢; omega)
      · intro N hN; simp only [Finset.mem_Icc] at hN; congr 1; omega
    have hsum_prev :
        (∑ N ∈ Finset.Icc 1 (k + k - 1), (k + k - N + 1) / 2) =
        (∑ i ∈ Finset.Icc 1 (2 * k - 1), (i + 1) / 2) := by
      refine Finset.sum_bij (fun N _ => 2 * k - N) ?_ ?_ ?_ ?_
      · intro N hN; simp only [Finset.mem_Icc] at hN ⊢; omega
      · intro N₁ hN₁ N₂ hN₂ h; simp only [Finset.mem_Icc] at hN₁ hN₂; omega
      · intro i hi; refine ⟨2 * k - i, ?_, ?_⟩ <;> (simp only [Finset.mem_Icc] at hi ⊢; omega)
      · intro N hN; simp only [Finset.mem_Icc] at hN; congr 1; omega
    rw [hsum_prev] at ih
    rw [hsum_shift]
    cases k with
    | zero => decide
    | succ m =>
      have hsplit : Finset.Icc 1 (2 * (m + 1) + 1) =
          insert (2 * (m + 1) + 1) (insert (2 * (m + 1)) (Finset.Icc 1 (2 * (m + 1) - 1))) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot1 : (2 * (m + 1) + 1) ∉ insert (2 * (m + 1)) (Finset.Icc 1 (2 * (m + 1) - 1)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hnot2 : (2 * (m + 1)) ∉ Finset.Icc 1 (2 * (m + 1) - 1) := by
        simp only [Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert hnot1, Finset.sum_insert hnot2, ih]
      have h1 : (2 * (m + 1) + 1 + 1) / 2 = m + 2 := by omega
      have h2 : (2 * (m + 1) + 1) / 2 = m + 1 := by omega
      have h3 : (m + 1 + (m + 1)) ^ 2 / 4 = (m + 1) ^ 2 := by
        have : (m + 1 + (m + 1)) ^ 2 = 4 * (m + 1) ^ 2 := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
      have h4 : (m + 1 + 1 + (m + 1 + 1)) ^ 2 / 4 = (m + 2) ^ 2 := by
        have : (m + 1 + 1 + (m + 1 + 1)) ^ 2 = 4 * (m + 2) ^ 2 := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [h1, h2, h3, h4]
      ring

/-- Triangular sum identity `∑_{N=2}^a (a - N + 1) = a (a - 1) / 2` for `a ≥ 2`. -/
lemma sum_Icc_sub_eq_triangular {a : ℕ} (ha : 2 ≤ a) :
    ∑ N ∈ Finset.Icc 2 a, (a - N + 1) = a * (a - 1) / 2 := by
  have h1 : ∑ N ∈ Finset.Icc 2 a, (a - N + 1) = ∑ i ∈ Finset.range (a - 1), (i + 1) := by
    refine Finset.sum_bij (fun N _ => a - N) ?_ ?_ ?_ ?_
    · intro N hN; simp only [Finset.mem_Icc, Finset.mem_range] at hN ⊢; omega
    · intro N₁ hN₁ N₂ hN₂ h; simp only [Finset.mem_Icc] at hN₁ hN₂; omega
    · intro i hi; refine ⟨a - i, ?_, ?_⟩ <;> (simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega)
    · intro _ _; rfl
  rw [h1]
  have h2 : ∑ i ∈ Finset.range (a - 1), (i + 1) =
      (∑ i ∈ Finset.range (a - 1), i) + (a - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [h2, Finset.sum_range_id]
  rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hA : (k + k - 1) * (k + k - 1 - 1) = 2 * ((2 * k - 1) * (k - 1)) := by
      have : k + k - 1 - 1 = 2 * (k - 1) := by omega
      have h1' : k + k - 1 = 2 * k - 1 := by omega
      rw [this, h1']; ring
    have hB : (k + k) * (k + k - 1) = 2 * (k * (2 * k - 1)) := by
      have : k + k = 2 * k := by omega
      rw [this]; ring
    rw [hA, hB, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
    have hk1 : 1 ≤ k := by omega
    have h2k1 : 1 ≤ 2 * k := by omega
    have hsub1 : k + k - 1 = 2 * k - 1 := by omega
    rw [hsub1]
    zify [hk1, h2k1]; ring
  · have hA : (2 * k + 1 - 1) * (2 * k + 1 - 1 - 1) = 2 * (k * (2 * k - 1)) := by
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]; ring
    have hB : (2 * k + 1) * (2 * k + 1 - 1) = 2 * ((2 * k + 1) * k) := by
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]; ring
    rw [hA, hB, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
    have hk1 : 1 ≤ k := by omega
    have h2k1 : 1 ≤ 2 * k := by omega
    have hsub1 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hsub1]
    zify [hk1, h2k1]; ring

/-- General quadratic lower bound on `Q = ∑_{N=2}^{n-1} f_q(n, N)`:
`Q ≥ a * (a - 1) / 2` where `a = n / q`, for every prime `q` and every `n : ℕ`. -/
lemma sum_fVal_tail_ge_triangular {q n : ℕ} (hq : q.Prime) :
    (n / q) * (n / q - 1) / 2 ≤ ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N := by
  set a := n / q
  by_cases ha : a ≤ 1
  · have : a * (a - 1) / 2 = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h <;> simp [h]
    rw [this]; exact Nat.zero_le _
  · have ha2 : 2 ≤ a := by omega
    have hqa : q * a ≤ n := Nat.mul_div_le n q
    have hq2 : 2 ≤ q := hq.two_le
    have h2a : 2 * a ≤ n := le_trans (Nat.mul_le_mul_right a hq2) hqa
    have hsub : Finset.Icc 2 a ⊆ Finset.Icc 2 (n - 1) := by
      intro N hN
      simp only [Finset.mem_Icc] at hN ⊢
      exact ⟨hN.1, by omega⟩
    have hterm : ∀ N ∈ Finset.Icc 2 a, a - N + 1 ≤ fVal q n N := by
      intro N hN
      simp only [Finset.mem_Icc] at hN
      have hNn : N ≤ n := by omega
      have hlin := linear_lower_bound_fVal hq (by omega : 1 ≤ N) hNn
      have hstrict : q * (a - N) < q * fVal q n N := by
        have h1 : N + N * (q - 1) = q * N := by zify [hq.one_le]; ring
        have h2 : q * (a - N) + q * N = q * a := by
          rw [← mul_add, Nat.sub_add_cancel hN.2]
        omega
      have hlt : a - N < fVal q n N := Nat.lt_of_mul_lt_mul_left hstrict
      omega
    calc a * (a - 1) / 2
        = ∑ N ∈ Finset.Icc 2 a, (a - N + 1) := (sum_Icc_sub_eq_triangular ha2).symm
      _ ≤ ∑ N ∈ Finset.Icc 2 a, fVal q n N := Finset.sum_le_sum hterm
      _ ≤ ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- If `m < q`, then `v_q(m!) = 0`. -/
lemma padicValNat_factorial_eq_zero_of_lt {q m : ℕ} (hq : q.Prime) (hm : m < q) :
    padicValNat q m.factorial = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  have hlog : Nat.log q m < 1 := by
    rw [Nat.log_eq_zero_iff.mpr (Or.inl hm)]
    norm_num
  rw [padicValNat_factorial hlog]
  simp

/-- Legendre recursion `v_q(m!) = m / q + v_q((m / q)!)`. -/
lemma padicValNat_factorial_rec {q : ℕ} (hq : q.Prime) (m : ℕ) :
    padicValNat q m.factorial = m / q + padicValNat q (m / q).factorial := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hm : m < q
  · have hdiv0 : m / q = 0 := Nat.div_eq_of_lt hm
    have hz := padicValNat_factorial_eq_zero_of_lt hq hm
    simp [hdiv0, hz]
  · rw [padicValNat_factorial (Nat.lt_succ_self (Nat.log q m)),
      padicValNat_factorial (Nat.lt_succ_self (Nat.log q (m / q)))]
    have hlog_eq : Nat.log q m = Nat.log q (m / q) + 1 := by
      rw [Nat.log_div_base]
      have : 1 ≤ Nat.log q m := Nat.le_log_of_pow_le hq.one_lt (by simpa using not_lt.mp hm)
      omega
    have hshift :
        Finset.Ico 1 (Nat.log q m + 1) =
        insert 1 ((Finset.Ico 1 (Nat.log q (m / q) + 1)).image (· + 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro ⟨hx1, hxu⟩
        by_cases h1 : x = 1
        · exact Or.inl h1
        · exact Or.inr ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro (rfl | ⟨y, ⟨hy1, hyu⟩, rfl⟩)
        · exact ⟨le_refl 1, by omega⟩
        · exact ⟨by omega, by omega⟩
    have hnot1 : 1 ∉ (Finset.Ico 1 (Nat.log q (m / q) + 1)).image (· + 1) := by
      simp only [Finset.mem_image, Finset.mem_Ico]; omega
    rw [hshift, Finset.sum_insert hnot1,
      Finset.sum_image (fun _ _ _ _ h => Nat.add_right_cancel h), pow_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', Nat.div_div_eq_div_mul]

/-- Upper bound `v_q(m!) * (q - 1) ≤ m` (Legendre's formula). -/
lemma padicValNat_factorial_mul_le {q : ℕ} (hq : q.Prime) (m : ℕ) :
    (q - 1) * padicValNat q m.factorial ≤ m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m < q
    · rw [padicValNat_factorial_eq_zero_of_lt hq hm, mul_zero]; exact Nat.zero_le _
    · have hm_pos : 0 < m := lt_of_lt_of_le hq.pos (not_lt.mp hm)
      have hih := ih (m / q) (Nat.div_lt_self hm_pos hq.one_lt)
      have hmul : q * (m / q) ≤ m := Nat.mul_div_le m q
      have hq1 : 1 ≤ q := hq.one_le
      have hsplit : (q - 1) * (m / q) + m / q = q * (m / q) := by zify [hq1]; ring
      rw [padicValNat_factorial_rec hq m, mul_add]
      omega

/-- Strict upper bound `v_q(m!) * (q - 1) < m` when `m ≥ 1`. -/
lemma padicValNat_factorial_mul_lt {q : ℕ} (hq : q.Prime) {m : ℕ} (hm : 1 ≤ m) :
    (q - 1) * padicValNat q m.factorial < m := by
  by_cases hlt : m < q
  · rw [padicValNat_factorial_eq_zero_of_lt hq hlt, mul_zero]; exact hm
  · have ha1 : 1 ≤ m / q := Nat.div_pos (not_lt.mp hlt) hq.pos
    have hlt_a := padicValNat_factorial_mul_lt hq ha1
    have hmul : q * (m / q) ≤ m := Nat.mul_div_le m q
    have hq1 : 1 ≤ q := hq.one_le
    have hsplit : (q - 1) * (m / q) + m / q = q * (m / q) := by zify [hq1]; ring
    rw [padicValNat_factorial_rec hq m, mul_add]
    omega
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) hq.one_lt

/-- Core arithmetic inequality (4.1) for Theorem 4.1(c):
`Q = ∑_{N=2}^{n-1} f_q(n, N) ≥ v_q(n!) + v_q(n)` when (`q = 2, n ≥ 8`) or (`q` odd, `3q ≤ n`),
for even `n`. -/
lemma sum_fVal_tail_ge_natMod_exp {n q : ℕ} (heven : Even n) (hq : q.Prime)
    (hcase : (q = 2 ∧ 8 ≤ n) ∨ (q ≠ 2 ∧ 3 * q ≤ n)) :
    padicValNat q n.factorial + padicValNat q n ≤ ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N := by
  have : Fact q.Prime := ⟨hq⟩
  rcases hcase with ⟨rfl, hn8⟩ | ⟨hodd, h3q⟩
  · -- Case q = 2, n ≥ 8 even
    have hsum1 : ∑ N ∈ Finset.Icc 1 (n - 1), (n - N + 1) / 2 =
        n / 2 + ∑ N ∈ Finset.Icc 2 (n - 1), (n - N + 1) / 2 := by
      have hsplit : Finset.Icc 1 (n - 1) = insert 1 (Finset.Icc 2 (n - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      congr 1; omega
    have hQ : n ^ 2 / 4 - n / 2 ≤ ∑ N ∈ Finset.Icc 2 (n - 1), fVal 2 n N := by
      have htot := sum_ceil_half_eq_sq_div_four heven
      have hle : ∑ N ∈ Finset.Icc 2 (n - 1), (n - N + 1) / 2 ≤
          ∑ N ∈ Finset.Icc 2 (n - 1), fVal 2 n N :=
        Finset.sum_le_sum fun N hN => by
          simp only [Finset.mem_Icc] at hN
          exact fVal_two_ge (by omega) (by omega)
      omega
    have hvfact : padicValNat 2 n.factorial ≤ n - 1 := by
      have := padicValNat_factorial_mul_lt Nat.prime_two (by omega : 1 ≤ n)
      omega
    have hvn : padicValNat 2 n ≤ n / 2 := by
      have hpow : 2 ^ padicValNat 2 n ≤ n :=
        Nat.le_of_dvd (by omega) pow_padicValNat_dvd
      by_cases h0 : padicValNat 2 n = 0
      · omega
      · have h2k' : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ 2 ^ k := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ih =>
            cases k with
            | zero => simp
            | succ m =>
              have := ih (by omega)
              rw [pow_succ]; omega
        have := h2k' (padicValNat 2 n) (by omega)
        omega
    rcases heven with ⟨k, rfl⟩
    have hsq : (k + k) ^ 2 / 4 = k ^ 2 := by
      have : (k + k) ^ 2 = 4 * k ^ 2 := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    have hhalf : (k + k) / 2 = k := by omega
    rw [hsq] at hQ
    rw [hhalf] at hQ hvn
    have hk4 : 4 ≤ k := by omega
    have h4k : 4 * k ≤ k ^ 2 := by nlinarith
    omega
  · -- Case q odd prime, 3q ≤ n, n even
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    set a := n / q
    have ha3 : 3 ≤ a := Nat.le_div_iff_mul_le hq.pos |>.mpr (by linarith)
    have hQtri : a * (a - 1) / 2 ≤ ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N :=
      sum_fVal_tail_ge_triangular hq
    by_cases ha_lt : a < q
    · -- Subcase 1: a < q, so n < q^2, v_q(n!) = a, v_q(n) ≤ 1
      have hlt_sq : n < q ^ 2 := by
        have hmod : n % q < q := Nat.mod_lt n hq.pos
        have heucl : q * a + n % q = n := Nat.div_add_mod n q
        have h1 : q * a ≤ q * (q - 1) := Nat.mul_le_mul_left q (by omega)
        have h2 : q * (q - 1) + q = q ^ 2 := by zify [hq.one_le]; ring
        omega
      have hvfact : padicValNat q n.factorial = a := by
        rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by omega) hlt_sq)]
        have h1 : Finset.Ico 1 2 = {1} := by decide
        rw [h1, Finset.sum_singleton, pow_one]
      have hvn_le : padicValNat q n ≤ 1 := by
        by_contra h2
        have hge2 : 2 ≤ padicValNat q n := by omega
        have hd : q ^ 2 ∣ n := dvd_trans (pow_dvd_pow q hge2) pow_padicValNat_dvd
        have hle := Nat.le_of_dvd (by omega) hd
        omega
      by_cases ha4 : 4 ≤ a
      · have htri_ge : a + 1 ≤ a * (a - 1) / 2 := by
          have : 2 * (a + 1) ≤ a * (a - 1) := by
            zify [show 1 ≤ a by omega]; nlinarith
          omega
        omega
      · have ha_eq : a = 3 := by omega
        have hndvd : ¬ (q ∣ n) := by
          rintro ⟨m, hm⟩
          have hm3 : m = 3 := by
            have := congrArg (· / q) hm
            rw [Nat.mul_div_cancel_left m hq.pos] at this
            omega
          rw [hm3] at hm
          rcases hq.odd_of_ne_two hodd with ⟨r, rfl⟩
          rcases heven with ⟨s, hs⟩
          omega
        have hvn0 : padicValNat q n = 0 := padicValNat.eq_zero_of_not_dvd hndvd
        rw [hvfact, hvn0, ha_eq]
        rw [ha_eq] at hQtri
        omega
    · have ha_ge : q ≤ a := not_lt.mp ha_lt
      by_cases ha5 : 5 ≤ a
      · -- Subcase 2: a ≥ 5.
        have hvfact_rec : padicValNat q n.factorial = a + padicValNat q a.factorial :=
          padicValNat_factorial_rec hq n
        have hva_le : 2 * padicValNat q a.factorial ≤ a - 1 := by
          have h1 := padicValNat_factorial_mul_lt hq (by omega : 1 ≤ a)
          have h2 : 2 ≤ q - 1 := by omega
          have h3 : 2 * padicValNat q a.factorial ≤ (q - 1) * padicValNat q a.factorial :=
            Nat.mul_le_mul_right _ h2
          omega
        have hvn_pow : q ^ padicValNat q n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
        have hn_lt : n < (a + 1) * q := by
          have h1 : q * a + n % q = n := Nat.div_add_mod n q
          have h2 : n % q < q := Nat.mod_lt n hq.pos
          have h3 : (a + 1) * q = q * a + q := by ring
          omega
        set d := a * (a - 1) / 2 - a - (a - 1) / 2
        have h3pow : ∀ m : ℕ, 5 ≤ m → m < 3 ^ (m * (m - 1) / 2 - m - (m - 1) / 2) := by
          intro m hm
          induction m with
          | zero => omega
          | succ m ih =>
            by_cases hm5 : m < 5
            · have hm_eq : m = 4 := by omega
              subst hm_eq; decide
            · have hih := ih (by omega)
              have hstep : m * (m - 1) / 2 - m - (m - 1) / 2 + 1 ≤
                  (m + 1) * m / 2 - (m + 1) - m / 2 := by
                have h1 : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
                  have hA : (m + 1) * m = m * (m - 1) + 2 * m := by
                    zify [show 1 ≤ m by omega]; ring
                  rw [hA, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
                have hm_ge : 2 * (m + (m - 1) / 2 + 1) ≤ m * (m - 1) := by
                  have hdiv : 2 * ((m - 1) / 2) ≤ m - 1 := Nat.mul_div_le (m - 1) 2
                  have hm5' : 5 ≤ m := by omega
                  have hquad : 2 * m + (m - 1) + 2 ≤ m * (m - 1) := by
                    zify [show 1 ≤ m by omega]; nlinarith
                  omega
                omega
              calc m + 1 < 3 * m := by omega
                _ < 3 * 3 ^ (m * (m - 1) / 2 - m - (m - 1) / 2) := by omega
                _ = 3 ^ (m * (m - 1) / 2 - m - (m - 1) / 2 + 1) := by rw [pow_succ']
                _ ≤ 3 ^ ((m + 1) * m / 2 - (m + 1) - m / 2) := Nat.pow_le_pow_right (by norm_num) hstep
        have ha_lt_3d : a < 3 ^ d := h3pow a ha5
        have hvn_le_d : padicValNat q n ≤ d := by
          by_contra hgt
          have hd1 : d + 1 ≤ padicValNat q n := by omega
          have hpow_ge : q ^ (d + 1) ≤ q ^ padicValNat q n := Nat.pow_le_pow_right hq.pos hd1
          have h3_le_q : 3 ^ d ≤ q ^ d := Nat.pow_le_pow_left hq3 d
          have hbig : (a + 1) * q ≤ q ^ (d + 1) := by
            rw [pow_succ]
            exact Nat.mul_le_mul_right q (by omega)
          omega
        have hsum_le : a + (a - 1) / 2 ≤ a * (a - 1) / 2 := by
          have hdiv : 2 * ((a - 1) / 2) ≤ a - 1 := Nat.mul_div_le (a - 1) 2
          have hquad : 2 * a + (a - 1) ≤ a * (a - 1) := by
            zify [show 1 ≤ a by omega]; nlinarith
          omega
        have htri_split : a + (a - 1) / 2 + d = a * (a - 1) / 2 := by omega
        omega
      · -- Subcase 3: q ≤ a ≤ 4, q ≥ 3 odd ⇒ q = 3, a ∈ {3, 4}, n ∈ {10, 12, 14}
        have hq_eq : q = 3 := by
          rcases hq.odd_of_ne_two hodd with ⟨r, hr⟩
          omega
        subst hq_eq
        have hn_cases : n = 10 ∨ n = 12 ∨ n = 14 := by
          have hdiv : 3 * a + n % 3 = n := Nat.div_add_mod n 3
          have hmod : n % 3 < 3 := Nat.mod_lt n (by norm_num)
          rcases heven with ⟨k, rfl⟩
          omega
        have hbound_N : ∀ m N, 10 ≤ m → 2 ≤ N → N ≤ m - 1 →
            (m - 2 * N + 2) / 3 ≤ fVal 3 m N := by
          intro m N hm hN2 hNm
          have hlin := linear_lower_bound_fVal (by decide : Nat.Prime 3) (by omega) (by omega : N ≤ m)
          omega
        rcases hn_cases with rfl | rfl | rfl
        · have hf2 : 2 ≤ fVal 3 10 2 := hbound_N 10 2 (by norm_num) (by norm_num) (by norm_num)
          have hf3 : 2 ≤ fVal 3 10 3 := hbound_N 10 3 (by norm_num) (by norm_num) (by norm_num)
          have hf4 : 1 ≤ fVal 3 10 4 := hbound_N 10 4 (by norm_num) (by norm_num) (by norm_num)
          have hsub : ({2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 2 9 := by decide
          have hsum_ge : fVal 3 10 2 + fVal 3 10 3 + fVal 3 10 4 ≤
              ∑ N ∈ Finset.Icc 2 9, fVal 3 10 N := by
            have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fVal 3 10) (fun _ _ _ => Nat.zero_le _)
            rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h1
            omega
          have hv1 : padicValNat 3 (Nat.factorial 10) = 4 := by
            rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num : 10 < 3 ^ 3))]
            decide
          have hv2 : padicValNat 3 10 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
          show padicValNat 3 (Nat.factorial 10) + padicValNat 3 10 ≤ ∑ N ∈ Finset.Icc 2 9, fVal 3 10 N
          omega
        · have hf2 : 3 ≤ fVal 3 12 2 := hbound_N 12 2 (by norm_num) (by norm_num) (by norm_num)
          have hf3 : 2 ≤ fVal 3 12 3 := hbound_N 12 3 (by norm_num) (by norm_num) (by norm_num)
          have hf4 : 2 ≤ fVal 3 12 4 := hbound_N 12 4 (by norm_num) (by norm_num) (by norm_num)
          have hf5 : 1 ≤ fVal 3 12 5 := hbound_N 12 5 (by norm_num) (by norm_num) (by norm_num)
          have hsub : ({2, 3, 4, 5} : Finset ℕ) ⊆ Finset.Icc 2 11 := by decide
          have hsum_ge : fVal 3 12 2 + fVal 3 12 3 + fVal 3 12 4 + fVal 3 12 5 ≤
              ∑ N ∈ Finset.Icc 2 11, fVal 3 12 N := by
            have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fVal 3 12) (fun _ _ _ => Nat.zero_le _)
            rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton] at h1
            omega
          have hv1 : padicValNat 3 (Nat.factorial 12) = 5 := by
            rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num : 12 < 3 ^ 3))]
            decide
          have hv2 : padicValNat 3 12 = 1 := by
            have h12 : (12 : ℕ) = 3 * 4 := by norm_num
            rw [h12, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
              padicValNat.eq_zero_of_not_dvd (by decide)]
          show padicValNat 3 (Nat.factorial 12) + padicValNat 3 12 ≤ ∑ N ∈ Finset.Icc 2 11, fVal 3 12 N
          omega
        · have hf2 : 4 ≤ fVal 3 14 2 := hbound_N 14 2 (by norm_num) (by norm_num) (by norm_num)
          have hf3 : 3 ≤ fVal 3 14 3 := hbound_N 14 3 (by norm_num) (by norm_num) (by norm_num)
          have hf4 : 2 ≤ fVal 3 14 4 := hbound_N 14 4 (by norm_num) (by norm_num) (by norm_num)
          have hf5 : 2 ≤ fVal 3 14 5 := hbound_N 14 5 (by norm_num) (by norm_num) (by norm_num)
          have hf6 : 1 ≤ fVal 3 14 6 := hbound_N 14 6 (by norm_num) (by norm_num) (by norm_num)
          have hsub : ({2, 3, 4, 5, 6} : Finset ℕ) ⊆ Finset.Icc 2 13 := by decide
          have hsum_ge : fVal 3 14 2 + fVal 3 14 3 + fVal 3 14 4 + fVal 3 14 5 + fVal 3 14 6 ≤
              ∑ N ∈ Finset.Icc 2 13, fVal 3 14 N := by
            have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fVal 3 14) (fun _ _ _ => Nat.zero_le _)
            rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_singleton] at h1
            omega
          have hv1 : padicValNat 3 (Nat.factorial 14) = 5 := by
            rw [padicValNat_factorial (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num : 14 < 3 ^ 3))]
            decide
          have hv2 : padicValNat 3 14 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
          show padicValNat 3 (Nat.factorial 14) + padicValNat 3 14 ≤ ∑ N ∈ Finset.Icc 2 13, fVal 3 14 N
          omega

/-! ### Exact DP evaluation of `f_2(n, N)` for small even orders -/

/-- Structurally recursive fuel-based `v_2(m!)` for fast kernel reduction. -/
def v2FactFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => m / 2 + v2FactFuel fuel (m / 2)

/-- Exact 2-adic valuation of `m!`. -/
def v2Fact (m : ℕ) : ℕ := v2FactFuel m m

private lemma v2FactFuel_eq (fuel m : ℕ) (h : m ≤ fuel) :
    v2FactFuel fuel m = padicValNat 2 m.factorial := by
  induction fuel generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0; simp [v2FactFuel]
  | succ k ih =>
    rw [v2FactFuel, padicValNat_factorial_rec Nat.prime_two m]
    congr 1
    exact ih (m / 2) (by omega)

lemma v2Fact_eq_padicValNat (m : ℕ) : v2Fact m = padicValNat 2 m.factorial :=
  v2FactFuel_eq m m (le_refl m)

/-- Exact DP table for `f_2(s, N)` returning a list of length `n + 1` (indexed by `s = 0..n`). -/
def f2DPRow (n : ℕ) : ℕ → List ℕ
  | 0 => 0 :: List.replicate n (n + 1)
  | N + 1 =>
    let prev := f2DPRow n N
    (List.range (n + 1)).map fun s =>
      ((List.range s).map fun t => prev.getD t (n + 1) + v2Fact (s - t)).foldl min (n + 1)

def f2DP (n N : ℕ) : ℕ := (f2DPRow n N).getD n (n + 1)

private lemma foldl_min_le_init (l : List ℕ) (a : ℕ) : l.foldl min a ≤ a := by
  induction l generalizing a with
  | nil => exact le_refl a
  | cons x xs ih => exact le_trans (ih (min a x)) (min_le_left a x)

private lemma foldl_min_le_mem (l : List ℕ) (a : ℕ) {x : ℕ} (hx : x ∈ l) :
    l.foldl min a ≤ x := by
  induction l generalizing a with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_trans (foldl_min_le_init ys (min a x)) (min_le_right a x)
    · exact ih (min a y) hx

private lemma exists_foldl_min (l : List ℕ) (a : ℕ) :
    l.foldl min a = a ∨ ∃ x ∈ l, l.foldl min a = x := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
    change ys.foldl min (min a y) = a ∨ ∃ x ∈ y :: ys, ys.foldl min (min a y) = x
    rcases ih (min a y) with h | ⟨x, hx, h⟩
    · rcases min_cases a y with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact Or.inl (by rw [h, hm])
      · exact Or.inr ⟨y, List.mem_cons_self, by rw [h, hm]⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem y hx, h⟩

/-- Exactness of `f2DP` for every `1 ≤ N ≤ n`: `fVal 2 n N = f2DP n N`. -/
lemma fVal_two_eq_f2DP {n N : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    fVal 2 n N = f2DP n N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrow : ∀ k : ℕ, ∀ s ≤ n,
      (∀ m : Fin k → ℕ, (∀ i, 0 < m i) → (∑ i, m i = s) →
        (f2DPRow n k).getD s (n + 1) ≤ padicValNat 2 (∏ i, (m i).factorial)) ∧
      ((k = 0 ∧ s = 0) ∨ (1 ≤ k ∧ k ≤ s) →
        ∃ m : Fin k → ℕ, (∀ i, 0 < m i) ∧ (∑ i, m i = s) ∧
          padicValNat 2 (∏ i, (m i).factorial) = (f2DPRow n k).getD s (n + 1)) := by
    intro k
    induction k with
    | zero =>
      intro s hs
      constructor
      · intro m _ hsum
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
        subst hsum; simp [f2DPRow]
      · rintro (⟨_, rfl⟩ | ⟨h1, _⟩)
        · exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp, by simp [f2DPRow]⟩
        · omega
    | succ k ih =>
      intro s hs
      have hget : (f2DPRow n (k + 1)).getD s (n + 1) =
          ((List.range s).map fun t => (f2DPRow n k).getD t (n + 1) + v2Fact (s - t)).foldl min (n + 1) := by
        simp [f2DPRow, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (Nat.lt_succ_of_le hs)]
      constructor
      · intro m hpos hsum
        rw [hget]
        let t := ∑ i : Fin k, m i.castSucc
        have hlast : m (Fin.last k) = s - t := by
          have := Fin.sum_univ_castSucc m
          omega
        have ht_lt : t < s := by
          have := hpos (Fin.last k)
          omega
        have hmem : (f2DPRow n k).getD t (n + 1) + v2Fact (s - t) ∈
            (List.range s).map (fun t => (f2DPRow n k).getD t (n + 1) + v2Fact (s - t)) :=
          List.mem_map.mpr ⟨t, List.mem_range.mpr ht_lt, rfl⟩
        have hle1 := foldl_min_le_mem _ (n + 1) hmem
        have hih := (ih t (by omega)).1 (fun i => m i.castSucc) (fun i => hpos i.castSucc) rfl
        have hprod : padicValNat 2 (∏ i : Fin (k + 1), (m i).factorial) =
            padicValNat 2 (∏ i : Fin k, (m i.castSucc).factorial) +
            padicValNat 2 (m (Fin.last k)).factorial := by
          rw [Fin.prod_univ_castSucc, padicValNat.mul
            (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)
            (Nat.factorial_ne_zero _)]
        rw [hprod, hlast, ← v2Fact_eq_padicValNat]
        omega
      · rintro (⟨h0, _⟩ | ⟨_, hks⟩)
        · omega
        · rw [hget]
          set L := (List.range s).map fun t => (f2DPRow n k).getD t (n + 1) + v2Fact (s - t)
          have hvalid_ex : ∃ t < s, (f2DPRow n k).getD t (n + 1) + v2Fact (s - t) ≤ n := by
            refine ⟨k, by omega, ?_⟩
            have hcond : (k = 0 ∧ k = 0) ∨ (1 ≤ k ∧ k ≤ k) := by
              by_cases hk0 : k = 0
              · exact Or.inl ⟨hk0, hk0⟩
              · exact Or.inr ⟨by omega, le_refl k⟩
            obtain ⟨m0, hpos0, hsum0, heq0⟩ := (ih k (by omega)).2 hcond
            have hv0 : padicValNat 2 (∏ i : Fin k, (m0 i).factorial) ≤ k := by
              rw [padicValNat_finset_prod Finset.univ (fun i => (m0 i).factorial)
                (fun i _ => Nat.factorial_ne_zero _)]
              calc ∑ i : Fin k, padicValNat 2 (m0 i).factorial
                  ≤ ∑ i : Fin k, m0 i := Finset.sum_le_sum fun i _ => by
                    have := padicValNat_factorial_mul_le Nat.prime_two (m0 i); omega
                _ = k := hsum0
            have hv1 : v2Fact (s - k) ≤ s - k := by
              rw [v2Fact_eq_padicValNat]
              have := padicValNat_factorial_mul_le Nat.prime_two (s - k); omega
            omega
          obtain ⟨t0, ht0_lt, ht0_le⟩ := hvalid_ex
          have hmin_le : L.foldl min (n + 1) ≤ n :=
            le_trans (foldl_min_le_mem L (n + 1) (List.mem_map.mpr ⟨t0, List.mem_range.mpr ht0_lt, rfl⟩)) ht0_le
          rcases exists_foldl_min L (n + 1) with hbad | ⟨x, hx, hmin_eq⟩
          · omega
          · rcases List.mem_map.mp hx with ⟨t, ht_mem, rfl⟩
            have ht_lt : t < s := List.mem_range.mp ht_mem
            have hget_lt : (f2DPRow n k).getD t (n + 1) ≤ n := by omega
            have ht_valid : (k = 0 ∧ t = 0) ∨ (1 ≤ k ∧ k ≤ t) := by
              have hbad_ge : ∀ r : ℕ, ∀ u ≤ n,
                  ¬ ((r = 0 ∧ u = 0) ∨ (1 ≤ r ∧ r ≤ u)) → (f2DPRow n r).getD u (n + 1) = n + 1 := by
                intro r
                induction r with
                | zero =>
                  intro u hu hnot
                  have hu0 : u ≠ 0 := fun h => hnot (Or.inl ⟨rfl, h⟩)
                  cases u with
                  | zero => exact absurd rfl hu0
                  | succ u' =>
                    have hu'lt : u' < n := by omega
                    simp [f2DPRow, List.getD_eq_getElem?_getD, hu'lt]
                | succ r ihr =>
                  intro u hu hnot
                  have hur : u < r + 1 := by omega
                  have hget' : (f2DPRow n (r + 1)).getD u (n + 1) =
                      ((List.range u).map fun w => (f2DPRow n r).getD w (n + 1) + v2Fact (u - w)).foldl min (n + 1) := by
                    simp [f2DPRow, List.getD_eq_getElem?_getD, List.getElem?_map,
                      List.getElem?_range (Nat.lt_succ_of_le hu)]
                  rw [hget']
                  rcases exists_foldl_min _ (n + 1) with heq | ⟨y, hy, heq⟩
                  · exact heq
                  · rcases List.mem_map.mp hy with ⟨w, hw, rfl⟩
                    have hw_lt : w < u := List.mem_range.mp hw
                    have hw_bad : ¬ ((r = 0 ∧ w = 0) ∨ (1 ≤ r ∧ r ≤ w)) := by omega
                    have hprev_eq := ihr w (by omega) hw_bad
                    have hle := foldl_min_le_init
                      ((List.range u).map fun w => (f2DPRow n r).getD w (n + 1) + v2Fact (u - w)) (n + 1)
                    omega
              by_contra hnot
              have := hbad_ge k t (by omega) hnot
              omega
            obtain ⟨m0, hpos0, hsum0, heq0⟩ := (ih t (by omega)).2 ht_valid
            let m : Fin (k + 1) → ℕ := Fin.snoc m0 (s - t)
            refine ⟨m, ?_, ?_, ?_⟩
            · intro i
              refine Fin.lastCases ?_ ?_ i
              · simp [m]; omega
              · intro j; simp [m, hpos0 j]
            · rw [Fin.sum_univ_castSucc]
              simp only [m, Fin.snoc_castSucc, Fin.snoc_last, hsum0]
              omega
            · rw [Fin.prod_univ_castSucc]
              simp only [m, Fin.snoc_castSucc, Fin.snoc_last]
              rw [padicValNat.mul (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)
                (Nat.factorial_ne_zero _), heq0, ← v2Fact_eq_padicValNat, ← hmin_eq]
  apply le_antisymm
  · obtain ⟨m, hpos, hsum, heq⟩ := (hrow N n (le_refl n)).2 (Or.inr ⟨hN1, hNn⟩)
    change fVal 2 n N ≤ (f2DPRow n N).getD n (n + 1)
    rw [← heq]
    exact fVal_le_of_comp m hpos hsum
  · exact le_fVal_of_forall hN1 hNn (hrow N n (le_refl n)).1

/-- Concrete DP evaluations of `∑_{N=1}^{n-1} f_2(n, N)` at `n = 2, 4, 6, 8, 10, 26`. -/
lemma sum_fVal_two_small :
    (∑ N ∈ Finset.Icc 1 1, fVal 2 2 N = 1) ∧
    (∑ N ∈ Finset.Icc 1 3, fVal 2 4 N = 5) ∧
    (∑ N ∈ Finset.Icc 1 5, fVal 2 6 N = 10) ∧
    (∑ N ∈ Finset.Icc 1 7, fVal 2 8 N = 20) ∧
    (∑ N ∈ Finset.Icc 1 9, fVal 2 10 N = 30) ∧
    (∑ N ∈ Finset.Icc 1 25, fVal 2 26 N = 204) := by
  have heval : ∀ n : ℕ, (∑ N ∈ Finset.Icc 1 (n - 1), fVal 2 n N) =
      ∑ N ∈ Finset.Icc 1 (n - 1), f2DP n N := fun n =>
    Finset.sum_congr rfl fun N hN => by
      simp only [Finset.mem_Icc] at hN
      exact fVal_two_eq_f2DP hN.1 (by omega)
  rw [heval 2, heval 4, heval 6, heval 8, heval 10, heval 26]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### Theorem 4.1, Corollary 4.2, and `n = 3q - 1` (hypothesis-parametrized on Section 3) -/

/-- Theorem 4.1 proved from Propositions 3.5 and 3.6. -/
theorem thm_4_1_quadratic_of
    (h_ind : ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Multidigraph V) (n q : ℕ),
      IsRegular H n → 1 ≤ Fintype.card V → (∀ u v : V, 1 ≤ adjMatrix H u v) → q.Prime →
      qVal q (circuitEval (adjMatrix H) n) ≥
        (∑ N' ∈ Finset.Icc 1 (Fintype.card V), fVal q n N' : ℕ∞))
    (h_id : ∀ n : ℕ, Even n → 2 ≤ n →
      delta n = (-1 : ℤ) ^ (n / 2 + 1) * ((n - 1).factorial : ℤ) *
        circuitEval (allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)) n)
    (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    (∀ q : ℕ, q.Prime →
      qVal q (delta n) ≥
        (padicValNat q (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞)) ∧
    (qVal 2 (delta n) ≥
      (padicValNat 2 (n - 1).factorial : ℕ∞) + ((n ^ 2 / 4 : ℕ) : ℕ∞)) ∧
    (∀ q : ℕ, q.Prime →
      ((q = 2 ∧ 8 ≤ n) ∨ (q ≠ 2 ∧ 3 * q ≤ n)) →
        qVal q (delta n) ≥ (3 * padicValNat q n.factorial : ℕ∞) ∧
        (naturalModulus q n : ℤ) ∣ reducedDelta n) := by
  have hpartA : ∀ q : ℕ, q.Prime →
      qVal q (delta n) ≥
        (padicValNat q (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞) := by
    intro q hq
    let M : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ :=
      allOnesMatrix (Fin (n - 1)) + (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ)
    let H := ofMatrix M
    have hM_eq : adjMatrix H = M := by
      ext u v
      change (Finset.univ.filter fun a : H.Arc => H.tail a = u ∧ H.head a = v).card = M u v
      have hbi : (Finset.univ.filter fun a : H.Arc => H.tail a = u ∧ H.head a = v).card =
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
          dsimp [H, ofMatrix] at h1 h2 heq
          rcases h1 with ⟨rfl, rfl⟩
          rcases h2 with ⟨rfl, rfl⟩
          have hk : k₁ = k₂ := heq
          rw [hk]
        · intro k _
          exact ⟨⟨u, v, k⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩, rfl⟩
      rw [hbi, Fintype.card_fin]
    have hreg : IsRegular H n := by
      have hcard_in : ∀ v : Fin (n - 1),
          (Finset.univ.filter fun a : H.Arc => H.head a = v).card = ∑ u : Fin (n - 1), M u v := by
        intro v
        have hpart : (Finset.univ.filter fun a : H.Arc => H.head a = v).card =
            ∑ u : Fin (n - 1), (Finset.univ.filter fun a : H.Arc => H.tail a = u ∧ H.head a = v).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext a; simp
          · intro u₁ _ u₂ _ hne
            exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
              hne ((Finset.mem_filter.mp ha₁).2.1.symm.trans (Finset.mem_filter.mp ha₂).2.1)
        rw [hpart]
        refine Finset.sum_congr rfl fun u _ => ?_
        exact congrFun (congrFun hM_eq u) v
      have hcard_out : ∀ u : Fin (n - 1),
          (Finset.univ.filter fun a : H.Arc => H.tail a = u).card = ∑ v : Fin (n - 1), M u v := by
        intro u
        have hpart : (Finset.univ.filter fun a : H.Arc => H.tail a = u).card =
            ∑ v : Fin (n - 1), (Finset.univ.filter fun a : H.Arc => H.tail a = u ∧ H.head a = v).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext a; simp
          · intro v₁ _ v₂ _ hne
            exact Finset.disjoint_left.mpr fun a ha₁ ha₂ =>
              hne ((Finset.mem_filter.mp ha₁).2.2.symm.trans (Finset.mem_filter.mp ha₂).2.2)
        rw [hpart]
        refine Finset.sum_congr rfl fun v _ => ?_
        exact congrFun (congrFun hM_eq u) v
      refine ⟨fun v => ?_, fun u => ?_⟩
      · rw [hcard_in v]
        simp only [M, Matrix.add_apply, allOnesMatrix, Matrix.of_apply, Matrix.one_apply,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        omega
      · rw [hcard_out u]
        simp only [M, Matrix.add_apply, allOnesMatrix, Matrix.of_apply, Matrix.one_apply,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        omega
    have hpos : ∀ u v : Fin (n - 1), 1 ≤ adjMatrix H u v := by
      intro u v; rw [hM_eq]; simp [M, allOnesMatrix]
    have hV : 1 ≤ Fintype.card (Fin (n - 1)) := by rw [Fintype.card_fin]; omega
    have hj := h_ind H n q hreg hV hpos hq
    rw [hM_eq, Fintype.card_fin] at hj
    rw [h_id n heven hn, mul_assoc, qVal_neg_one_pow_mul hq, qVal_mul hq,
      qVal_natCast (Nat.factorial_ne_zero (n - 1))]
    exact add_le_add (le_refl _) hj
  have hpartB : qVal 2 (delta n) ≥
      (padicValNat 2 (n - 1).factorial : ℕ∞) + ((n ^ 2 / 4 : ℕ) : ℕ∞) := by
    have hA := hpartA 2 Nat.prime_two
    have hsum : n ^ 2 / 4 ≤ ∑ N ∈ Finset.Icc 1 (n - 1), fVal 2 n N := by
      rw [← sum_ceil_half_eq_sq_div_four heven]
      exact Finset.sum_le_sum fun N hN => by
        simp only [Finset.mem_Icc] at hN
        exact fVal_two_ge hN.1 (by omega)
    have hle : ((n ^ 2 / 4 : ℕ) : ℕ∞) ≤ ∑ N ∈ Finset.Icc 1 (n - 1), (fVal 2 n N : ℕ∞) := by
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr hsum
    exact le_trans (add_le_add (le_refl _) hle) hA
  have hpartC : ∀ q : ℕ, q.Prime →
      ((q = 2 ∧ 8 ≤ n) ∨ (q ≠ 2 ∧ 3 * q ≤ n)) →
        qVal q (delta n) ≥ (3 * padicValNat q n.factorial : ℕ∞) ∧
        (naturalModulus q n : ℤ) ∣ reducedDelta n := by
    intro q hq hcase
    have : Fact q.Prime := ⟨hq⟩
    have hA := hpartA q hq
    have hsplit : Finset.Icc 1 (n - 1) = insert 1 (Finset.Icc 2 (n - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsum_split : ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N =
        padicValNat q n.factorial + ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N := by
      rw [hsplit, Finset.sum_insert (by simp), fVal_one (by omega)]
    have hQ := sum_fVal_tail_ge_natMod_exp heven hq hcase
    have hv_pred : padicValNat q n.factorial = padicValNat q n + padicValNat q (n - 1).factorial := by
      have h1 : n.factorial = n * (n - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
      rw [h1, padicValNat.mul (by omega) (Nat.factorial_ne_zero (n - 1))]
    have hge_3 : 3 * padicValNat q n.factorial ≤
        padicValNat q (n - 1).factorial + ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N := by
      rw [hsum_split]; omega
    have hdelta_ge : ((3 * padicValNat q n.factorial : ℕ) : ℕ∞) ≤ qVal q (delta n) := by
      have hcast : ((padicValNat q (n - 1).factorial + ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ) : ℕ∞) =
          (padicValNat q (n - 1).factorial : ℕ∞) + ∑ N ∈ Finset.Icc 1 (n - 1), (fVal q n N : ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_sum]
      exact le_trans (Nat.cast_le.mpr hge_3) (hcast ▸ hA)
    have hdelta_ge' : (3 * padicValNat q n.factorial : ℕ∞) ≤ qVal q (delta n) := by
      simpa [Nat.cast_mul] using hdelta_ge
    refine ⟨hdelta_ge', ?_⟩
    have hdvd : (q : ℤ) ^ (3 * padicValNat q n.factorial) ∣ delta n :=
      (natCast_le_qVal_iff_dvd hq _ _).mp hdelta_ge
    rw [eq_normal_proved n heven] at hdvd
    have hprod_val : padicValNat q (n.factorial * (n - 1).factorial) =
        padicValNat q n.factorial + padicValNat q (n - 1).factorial :=
      padicValNat.mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1))
    set e := padicValNat q n.factorial + padicValNat q (n - 1).factorial
    have he_dvd : q ^ e ∣ n.factorial * (n - 1).factorial := by
      rw [← hprod_val]; exact pow_padicValNat_dvd
    rcases he_dvd with ⟨k, hk⟩
    have hndvd_k : ¬ (q ∣ k) := by
      rintro ⟨m, rfl⟩
      have hd1 : q ^ (e + 1) ∣ n.factorial * (n - 1).factorial := ⟨m, by rw [hk]; ring⟩
      have hle := (padicValNat_dvd_iff_le
        (Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1)))).mp hd1
      omega
    have hexp_eq : 3 * padicValNat q n.factorial = e + (padicValNat q n.factorial + padicValNat q n) := by
      omega
    rw [hexp_eq, pow_add, hk] at hdvd
    push_cast at hdvd
    rcases hdvd with ⟨m, hm⟩
    have hqe_ne : ((q : ℤ) ^ e) ≠ 0 := pow_ne_zero e (Nat.cast_ne_zero.mpr hq.ne_zero)
    have hd_k : (q : ℤ) ^ (padicValNat q n.factorial + padicValNat q n) ∣ (k : ℤ) * reducedDelta n := by
      refine ⟨m, ?_⟩
      apply mul_left_cancel₀ hqe_ne
      calc (q : ℤ) ^ e * ((k : ℤ) * reducedDelta n)
          = (q : ℤ) ^ e * (k : ℤ) * reducedDelta n := by ring
        _ = (q : ℤ) ^ e * (q : ℤ) ^ (padicValNat q n.factorial + padicValNat q n) * m := hm
        _ = (q : ℤ) ^ e * ((q : ℤ) ^ (padicValNat q n.factorial + padicValNat q n) * m) := by ring
    have hcop : IsCoprime ((q : ℤ) ^ (padicValNat q n.factorial + padicValNat q n)) (k : ℤ) := by
      have hcop1 : Nat.Coprime (q ^ (padicValNat q n.factorial + padicValNat q n)) k :=
        (hq.coprime_iff_not_dvd.mpr hndvd_k).pow_left _
      exact_mod_cast hcop1.isCoprime
    unfold naturalModulus
    push_cast
    exact hcop.dvd_of_dvd_mul_left hd_k
  exact ⟨hpartA, hpartB, hpartC⟩

/-- Corollary 4.2 proved from Theorem 4.1(a). -/
theorem cor_4_2_floor_of
    (h_4_1a : ∀ n q : ℕ, Even n → 2 ≤ n → q.Prime →
      qVal q (delta n) ≥
        (padicValNat q (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞))
    (n q : ℕ) (heven : Even n) (hq : q.Prime) :
    qVal q (delta n) ≥
      (padicValNat q (n.factorial * (n - 1).factorial) : ℕ∞) +
        (((n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hn0 : n = 0
  · subst hn0; simp [padicValNat]
  · have hn2 : 2 ≤ n := by rcases heven with ⟨k, rfl⟩; omega
    have hA := h_4_1a n q heven hn2 hq
    have hsplit : Finset.Icc 1 (n - 1) = insert 1 (Finset.Icc 2 (n - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsum_split : ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N =
        padicValNat q n.factorial + ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N := by
      rw [hsplit, Finset.sum_insert (by simp), fVal_one (by omega)]
    have htri : (n / q) * (n / q - 1) / 2 ≤ ∑ N ∈ Finset.Icc 2 (n - 1), fVal q n N :=
      sum_fVal_tail_ge_triangular hq
    have hmul : padicValNat q (n.factorial * (n - 1).factorial) =
        padicValNat q n.factorial + padicValNat q (n - 1).factorial :=
      padicValNat.mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1))
    have hle : padicValNat q (n.factorial * (n - 1).factorial) + (n / q) * (n / q - 1) / 2 ≤
        padicValNat q (n - 1).factorial + ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N := by
      rw [hmul, hsum_split]; omega
    have hcast : ((padicValNat q (n - 1).factorial + ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ) : ℕ∞) =
        (padicValNat q (n - 1).factorial : ℕ∞) + ∑ N ∈ Finset.Icc 1 (n - 1), (fVal q n N : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_sum]
    have hcast2 : ((padicValNat q (n.factorial * (n - 1).factorial) + (n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) =
        (padicValNat q (n.factorial * (n - 1).factorial) : ℕ∞) + (((n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) :=
      Nat.cast_add _ _
    exact le_trans (hcast2 ▸ Nat.cast_le.mpr hle) (hcast ▸ hA)

/-- Section 5 boundary case `n = 3q - 1`: `v_q(Δ_{3q - 1}) ≥ 7`. -/
theorem sec5_three_q_minus_one_of
    (h_4_1a : ∀ n q : ℕ, Even n → 2 ≤ n → q.Prime →
      qVal q (delta n) ≥
        (padicValNat q (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞))
    (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    (7 : ℕ∞) ≤ qVal q (delta (3 * q - 1)) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have heven : Even (3 * q - 1) := by
    rcases hq.odd_of_ne_two hodd with ⟨k, rfl⟩
    exact ⟨3 * k + 1, by omega⟩
  have hA := h_4_1a (3 * q - 1) q heven (by omega) hq
  have hv_pred : 2 ≤ padicValNat q (3 * q - 1 - 1).factorial := by
    have := div_le_padicValNat_factorial hq (3 * q - 1 - 1)
    have h2 : 2 ≤ (3 * q - 1 - 1) / q := Nat.le_div_iff_mul_le hq.pos |>.mpr (by omega)
    omega
  have hf1 : 2 ≤ fVal q (3 * q - 1) 1 := by
    rw [fVal_one (by omega)]
    have := div_le_padicValNat_factorial hq (3 * q - 1)
    have h2 : 2 ≤ (3 * q - 1) / q := Nat.le_div_iff_mul_le hq.pos |>.mpr (by omega)
    omega
  have hf2 : 2 ≤ fVal q (3 * q - 1) 2 := by
    have hlin := linear_lower_bound_fVal hq (by norm_num : 1 ≤ 2) (by omega : 2 ≤ 3 * q - 1)
    have hstrict : q * 1 < q * fVal q (3 * q - 1) 2 := by omega
    have := Nat.lt_of_mul_lt_mul_left hstrict
    omega
  have hf3 : 1 ≤ fVal q (3 * q - 1) 3 := by
    have hlin := linear_lower_bound_fVal hq (by norm_num : 1 ≤ 3) (by omega : 3 ≤ 3 * q - 1)
    have hstrict : 0 < q * fVal q (3 * q - 1) 3 := by omega
    exact Nat.pos_of_mul_pos_left hstrict
  have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 (3 * q - 1 - 1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]; omega
  have hsum5 : 5 ≤ ∑ N ∈ Finset.Icc 1 (3 * q - 1 - 1), fVal q (3 * q - 1) N := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fVal q (3 * q - 1))
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h1
    omega
  have h7 : ((7 : ℕ) : ℕ∞) ≤ (padicValNat q (3 * q - 1 - 1).factorial : ℕ∞) +
      ∑ N ∈ Finset.Icc 1 (3 * q - 1 - 1), (fVal q (3 * q - 1) N : ℕ∞) := by
    rw [← Nat.cast_sum, ← Nat.cast_add]
    exact Nat.cast_le.mpr (by omega)
  exact le_trans h7 hA

end AlonTarsi.Proofs

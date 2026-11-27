module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import AlonTarsi.Proofs.LatinBasics
public import AlonTarsi.Proofs.CircuitPoly
public import AlonTarsi.Proofs.Quadratic
public import AlonTarsi.Proofs.StonesWanless35
public import AlonTarsi.Proofs.SylowMid
public import AlonTarsi.Proofs.Drisko1997
public import AlonTarsi.Proofs.TwoQMobius

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Main Assembly and Coverage Links

This file wires Section 3 (`CircuitPoly`), Section 4 (`Quadratic`), Section 5 (`SylowMid`),
Stones–Wanless Theorem 3.5 (`StonesWanless35`), and Drisko (1997) (`Drisko1997`) into:
* Unconditional proofs of `thm_4_1_quadratic_proved`, `cor_4_2_floor_proved`,
  `sec5_three_q_minus_one_proved`, and `thm_C_proved`.
* Unconditional proofs of the coverage links `eq_orbit_proved`, `sec3_fig4_elim_n4_proved`,
  `sec1_fig1_small_counts_proved`, `cVal_two`, `cVal_four`, `centeredSubsets_card`, and
  `tauQ_three`.
* Assembly of `thm_B_of`, `thm_A_of`, `sec7_uniform_divisor_of`, `sec4_numeric_bounds_of`,
  `sec1_small_orders_and_headline_of`, and `sec6_concrete_in_text_of` from Section 6.
-/

namespace AlonTarsi.Proofs

open AlonTarsi
open scoped BigOperators

/-! ### Unconditional Section 4, Boundary, and Theorem C Proofs -/

theorem thm_4_1_quadratic_proved (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    (∀ q : ℕ, q.Prime →
      qVal q (delta n) ≥
        (padicValNat q (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞)) ∧
    (qVal 2 (delta n) ≥
      (padicValNat 2 (n - 1).factorial : ℕ∞) + ((n ^ 2 / 4 : ℕ) : ℕ∞)) ∧
    (∀ q : ℕ, q.Prime →
      ((q = 2 ∧ 8 ≤ n) ∨ (q ≠ 2 ∧ 3 * q ≤ n)) →
        qVal q (delta n) ≥ (3 * padicValNat q n.factorial : ℕ∞) ∧
        (naturalModulus q n : ℤ) ∣ reducedDelta n) :=
  thm_4_1_quadratic_of
    (fun H m q hreg hV hpos hq => prop_3_5_quad_ind_proved H m q hreg hV hpos hq)
    prop_3_6_identity_proved n heven hn

theorem cor_4_2_floor_proved (n q : ℕ) (heven : Even n) (hq : q.Prime) :
    qVal q (delta n) ≥
      (padicValNat q (n.factorial * (n - 1).factorial) : ℕ∞) +
        (((n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) :=
  cor_4_2_floor_of (fun m r hm h2 hr => (thm_4_1_quadratic_proved m hm h2).1 r hr) n q heven hq

theorem sec5_three_q_minus_one_proved (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    (7 : ℕ∞) ≤ qVal q (delta (3 * q - 1)) :=
  sec5_three_q_minus_one_of
    (fun m r hm h2 hr => (thm_4_1_quadratic_proved m hm h2).1 r hr) q hq hodd

theorem thm_C_proved (n q : ℕ) (heven : Even n) (hq : q.Prime) :
    qVal q (delta n) ≥
      (padicValNat q (n - 1).factorial : ℕ∞) +
        (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞) ∧
    (padicValNat q (n - 1).factorial : ℕ∞) +
        (∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ∞) ≥
      (padicValNat q (n.factorial * (n - 1).factorial) : ℕ∞) +
        (((n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) ∧
    (q = 2 →
      (padicValNat 2 (n - 1).factorial : ℕ∞) +
          (∑ N ∈ Finset.Icc 1 (n - 1), fVal 2 n N : ℕ∞) ≥
        (padicValNat 2 (n - 1).factorial : ℕ∞) + ((n ^ 2 / 4 : ℕ) : ℕ∞)) := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨by simp [padicValNat], by simp [padicValNat], fun _ => by simp⟩
  · have hn2 : 2 ≤ n := by rcases heven with ⟨k, rfl⟩; omega
    refine ⟨(thm_4_1_quadratic_proved n heven hn2).1 q hq, ?_, ?_⟩
    · have hsplit : Finset.Icc 1 (n - 1) = insert 1 (Finset.Icc 2 (n - 1)) := by
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
      have hcast1 : ((padicValNat q (n - 1).factorial + ∑ N ∈ Finset.Icc 1 (n - 1), fVal q n N : ℕ) : ℕ∞) =
          (padicValNat q (n - 1).factorial : ℕ∞) + ∑ N ∈ Finset.Icc 1 (n - 1), (fVal q n N : ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_sum]
      have hcast2 : ((padicValNat q (n.factorial * (n - 1).factorial) + (n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) =
          (padicValNat q (n.factorial * (n - 1).factorial) : ℕ∞) + (((n / q) * (n / q - 1) / 2 : ℕ) : ℕ∞) :=
        Nat.cast_add _ _
      exact hcast1 ▸ hcast2 ▸ Nat.cast_le.mpr hle
    · rintro rfl
      have hsum : n ^ 2 / 4 ≤ ∑ N ∈ Finset.Icc 1 (n - 1), fVal 2 n N := by
        rw [← sum_ceil_half_eq_sq_div_four heven]
        exact Finset.sum_le_sum fun N hN => by
          simp only [Finset.mem_Icc] at hN
          exact fVal_two_ge hN.1 (by omega)
      have hle : ((n ^ 2 / 4 : ℕ) : ℕ∞) ≤ ∑ N ∈ Finset.Icc 1 (n - 1), (fVal 2 n N : ℕ∞) := by
        rw [← Nat.cast_sum]; exact Nat.cast_le.mpr hsum
      exact add_le_add (le_refl _) hle

/-! ### Coverage Links: Orbit Congruence, Fig 4, Fig 1, Small Orders, `|C_m|`, `τ_3` -/

open scoped Classical in
theorem eq_orbit_proved (n q : ℕ) (heven : Even n) (_hq : q.Prime)
    (G : Subgroup (Isotopy n)) (_hp : IsPGroup q G) :
    delta n ≡
      ∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => ∃ g ∈ G, g ≠ 1 ∧ g • L = L),
        (squareSign L : ℤ) [ZMOD (Nat.card G : ℤ)] := by
  classical
  let P : LatinSquare n → Prop := fun L => ∃ g ∈ G, g ≠ 1 ∧ g • L = L
  rw [delta_eq_sum_squareSign]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun L => (squareSign L : ℤ))]
  rw [Int.modEq_iff_dvd]
  have hdiff :
      (∑ L ∈ Finset.univ.filter P, (squareSign L : ℤ)) -
        ((∑ L ∈ Finset.univ.filter P, (squareSign L : ℤ)) +
          ∑ L ∈ Finset.univ.filter (fun L => ¬ P L), (squareSign L : ℤ)) =
      -(∑ L ∈ Finset.univ.filter (fun L => ¬ P L), (squareSign L : ℤ)) := by ring
  rw [hdiff]
  apply dvd_neg.mpr
  let Free := { L : LatinSquare n // ¬ P L }
  have hsmul_free : ∀ (g : G) (L : LatinSquare n), ¬ P L → ¬ P (g.1 • L) := by
    intro g L hL ⟨h, hhG, hh1, hfix⟩
    apply hL
    refine ⟨g.1⁻¹ * h * g.1, G.mul_mem (G.mul_mem (G.inv_mem g.2) hhG) g.2, ?_, ?_⟩
    · intro h1
      apply hh1
      calc h = g.1 * (g.1⁻¹ * h * g.1) * g.1⁻¹ := by group
        _ = g.1 * 1 * g.1⁻¹ := by rw [h1]
        _ = 1 := by group
    · rw [mul_smul, mul_smul, hfix, inv_smul_smul]
  let _ : MulAction G Free :=
    { smul := fun g L => ⟨g.1 • L.1, hsmul_free g L.1 L.2⟩
      one_smul := fun L => Subtype.ext (one_smul _ L.1)
      mul_smul := fun g₁ g₂ L => Subtype.ext (mul_smul g₁.1 g₂.1 L.1) }
  have hsum_sub :
      (∑ L ∈ Finset.univ.filter (fun L : LatinSquare n => ¬ P L), (squareSign L : ℤ)) =
      ∑ L : Free, (squareSign L.1 : ℤ) := by
    rw [Finset.sum_subtype (p := fun L => ¬ P L) (Finset.univ.filter (fun L => ¬ P L))
      (fun _ => by simp)]
  rw [hsum_sub]
  let orbRel := MulAction.orbitRel G Free
  have : Fintype (Quotient orbRel) := Fintype.ofFinite _
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Quotient orbRel)))
      (g := Quotient.mk orbRel) (fun _ _ => Finset.mem_univ _)]
  refine Finset.dvd_sum fun o _ => ?_
  obtain ⟨L₀, rfl⟩ := Quotient.exists_rep o
  have hconst : ∀ y ∈ Finset.univ.filter (fun y : Free => Quotient.mk orbRel y = Quotient.mk orbRel L₀),
      (squareSign y.1 : ℤ) = (squareSign L₀.1 : ℤ) := by
    intro y hy
    rcases Quotient.exact (Finset.mem_filter.mp hy).2 with ⟨g, hg⟩
    have hg' : g.1 • L₀.1 = y.1 := congrArg Subtype.val hg
    rw [← hg', squareSign_isotopyAct_even heven]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard_orb :
      (Finset.univ.filter (fun y : Free => Quotient.mk orbRel y = Quotient.mk orbRel L₀)).card =
      Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    symm
    refine Finset.card_bij (fun (g : G) _ => g • L₀) ?_ ?_ ?_
    · intro g _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Quotient.sound ⟨g, rfl⟩⟩
    · intro g₁ _ g₂ _ hEq
      have hEq' : g₁.1 • L₀.1 = g₂.1 • L₀.1 := congrArg Subtype.val hEq
      have hfix : (g₂.1⁻¹ * g₁.1) • L₀.1 = L₀.1 := by rw [mul_smul, hEq', inv_smul_smul]
      by_contra hne
      apply L₀.2
      refine ⟨g₂.1⁻¹ * g₁.1, G.mul_mem (G.inv_mem g₂.2) g₁.2, ?_, hfix⟩
      intro h1
      apply hne
      apply Subtype.ext
      calc g₁.1 = g₂.1 * (g₂.1⁻¹ * g₁.1) := by group
        _ = g₂.1 * 1 := by rw [h1]
        _ = g₂.1 := mul_one _
    · intro y hy
      rcases Quotient.exact (Finset.mem_filter.mp hy).2 with ⟨g, hg⟩
      exact ⟨g, Finset.mem_univ _, hg⟩
  rw [hcard_orb]
  exact dvd_mul_right _ _

theorem sec3_fig4_elim_n4_proved {H : Multidigraph (Fin 3)}
    (hM : adjMatrix H = allOnesMatrix (Fin 3) + (1 : Matrix (Fin 3) (Fin 3) ℕ))
    (w : Fin 3) :
    Fintype.card (nonLoopIn H w ≃ nonLoopOut H w) = 2 ∧
    circuitPoly H =
      (Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 3) *
        ∑ σ : nonLoopIn H w ≃ nonLoopOut H w, circuitPoly (elimDigraph H w σ) := by
  have hM_at : ∀ u v : Fin 3, adjMatrix H u v = (if u = v then 2 else 1) := by
    intro u v
    have h := congrFun (congrFun hM u) v
    simp only [Matrix.add_apply, allOnesMatrix, Matrix.of_apply, Matrix.one_apply] at h
    split_ifs at h ⊢ <;> omega
  have hreg : IsRegular H 4 := by
    rw [isRegular_iff_adjMatrix]
    exact ⟨fun v => by simp_rw [hM_at]; fin_cases v <;> decide,
           fun u => by simp_rw [hM_at]; fin_cases u <;> decide⟩
  have hww : adjMatrix H w w = 2 := by rw [hM_at]; simp
  have hcard_nli : Fintype.card (nonLoopIn H w) = 2 := by
    rw [Fintype.card_subtype]
    have hpart :
        (Finset.univ.filter fun a : H.Arc => H.head a = w).card =
        (Finset.univ.filter fun a : H.Arc => H.head a = w ∧ H.tail a ≠ w).card +
        (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a = w).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        tauto
      · rw [Finset.disjoint_filter]; intro a _ h1 h2; exact h1.2 h2.1
    have h1 := hreg.1 w
    have h2 : (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a = w).card = 2 := hww
    omega
  have hcard_nlo : Fintype.card (nonLoopOut H w) = 2 := by
    rw [Fintype.card_subtype]
    have hpart :
        (Finset.univ.filter fun a : H.Arc => H.tail a = w).card =
        (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a ≠ w).card +
        (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a = w).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        tauto
      · rw [Finset.disjoint_filter]; intro a _ h1 h2; exact h1.2 h2.2
    have h1 := hreg.2 w
    have h2 : (Finset.univ.filter fun a : H.Arc => H.tail a = w ∧ H.head a = w).card = 2 := hww
    omega
  have hcard_eq : Fintype.card (nonLoopIn H w ≃ nonLoopOut H w) = 2 := by
    have e1 := Fintype.equivFinOfCardEq hcard_nli
    have e2 := Fintype.equivFinOfCardEq hcard_nlo
    have e3 : (nonLoopIn H w ≃ nonLoopOut H w) ≃ Equiv.Perm (Fin 2) :=
      { toFun := fun σ => e1.symm.trans (σ.trans e2)
        invFun := fun τ => e1.trans (τ.trans e2.symm)
        left_inv := fun σ => by ext x; simp
        right_inv := fun τ => by ext x; simp }
    rw [Fintype.card_congr e3, Fintype.card_perm, Fintype.card_fin]
    decide
  refine ⟨hcard_eq, ?_⟩
  have hE := (lem_3_3_quad_elim_proved H 4 hreg (by decide) w).2.1
  rw [hww] at hE
  rw [hE]
  congr 1
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num

/-! ### Small Orders (`n = 2, 4, 6`): Figure 1, `cVal 2 = 4`, `cVal 4 = 24` -/

/-- Every Latin square of positive order can be reduced by an isotopy. -/
private lemma exists_reduced_isotopy {n : ℕ} (hn : 0 < n) (L : LatinSquare n) :
    ∃ σ : Isotopy n, IsReduced (σ • L) := by
  let σA : Isotopy n := (1, 1, (rowPerm L ⟨0, hn⟩)⁻¹)
  let L₁ : LatinSquare n := σA • L
  have hL1_row0 : ∀ c : Fin n, L₁.entry ⟨0, hn⟩ c = c := by
    intro c
    change (rowPerm L ⟨0, hn⟩).symm (L.entry ⟨0, hn⟩ c) = c
    exact Equiv.symm_apply_apply (rowPerm L ⟨0, hn⟩) c
  have hL1_col0_zero : colPerm L₁ ⟨0, hn⟩ ⟨0, hn⟩ = ⟨0, hn⟩ := hL1_row0 ⟨0, hn⟩
  let σB : Isotopy n := (colPerm L₁ ⟨0, hn⟩, 1, 1)
  refine ⟨σB * σA, fun _ => ⟨fun c => ?_, fun r => ?_⟩⟩
  · change ((σB • L₁).entry ⟨0, hn⟩ c) = c
    change L₁.entry ((colPerm L₁ ⟨0, hn⟩).symm ⟨0, hn⟩) c = c
    have h0 : (colPerm L₁ ⟨0, hn⟩).symm ⟨0, hn⟩ = ⟨0, hn⟩ := by
      apply (colPerm L₁ ⟨0, hn⟩).injective
      rw [Equiv.apply_symm_apply, hL1_col0_zero]
    rw [h0]
    exact hL1_row0 c
  · change ((σB • L₁).entry r ⟨0, hn⟩) = r
    change colPerm L₁ ⟨0, hn⟩ ((colPerm L₁ ⟨0, hn⟩).symm r) = r
    exact Equiv.apply_symm_apply _ r

/-- Explicit reduced Latin square of order 2. -/
private def redLS2 : LatinSquare 2 where
  entry r c := ⟨(r.val + c.val) % 2, Nat.mod_lt _ (by omega)⟩
  row_bijective r := Finite.injective_iff_bijective.mp fun c₁ c₂ h => by
    fin_cases r <;> fin_cases c₁ <;> fin_cases c₂ <;> simp at h ⊢
  col_bijective c := Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
    fin_cases c <;> fin_cases r₁ <;> fin_cases r₂ <;> simp at h ⊢

private lemma isReduced_redLS2 : IsReduced redLS2 := by
  intro _; constructor <;> intro x <;> fin_cases x <;> rfl

private lemma eq_redLS2_of_isReduced (L : LatinSquare 2) (hL : IsReduced L) : L = redLS2 := by
  have hr := (hL (by omega)).1
  have hc := (hL (by omega)).2
  apply LatinSquare.ext; funext r c
  fin_cases r <;> fin_cases c
  · exact hr 0
  · exact hr 1
  · exact hc 1
  · have h10 : L.entry 1 0 = 1 := hc 1
    have hne : L.entry 1 1 ≠ L.entry 1 0 := fun h =>
      absurd ((L.row_bijective 1).1 h) (by decide)
    rw [h10] at hne
    have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
    rcases hfin2 (L.entry 1 1) with h | h
    · exact h
    · exact absurd h hne

private lemma squareSign_redLS2 : squareSign redLS2 = 1 := by
  have hr0 : rowPerm redLS2 0 = 1 := by ext c; fin_cases c <;> rfl
  have hr1 : rowPerm redLS2 1 = Equiv.swap 0 1 := by ext c; fin_cases c <;> rfl
  have hc0 : colPerm redLS2 0 = 1 := by ext r; fin_cases r <;> rfl
  have hc1 : colPerm redLS2 1 = Equiv.swap 0 1 := by ext r; fin_cases r <;> rfl
  unfold squareSign rowSign colSign
  rw [Fin.prod_univ_two, Fin.prod_univ_two, hr0, hr1, hc0, hc1, map_one,
    Equiv.Perm.sign_swap (by decide)]
  rfl

/-- The four reduced Latin squares of order 4. -/
private def redLS4_0 : LatinSquare 4 where
  entry r c :=
    match r.val, c.val with
    | 0, _ => c
    | _, 0 => r
    | 1, 1 => 0 | 1, 2 => 3 | 1, 3 => 2
    | 2, 1 => 3 | 2, 2 => 0 | 2, 3 => 1
    | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0
    | _, _ => 0
  row_bijective r := Finite.injective_iff_bijective.mp fun c₁ c₂ h => by
    fin_cases r <;> fin_cases c₁ <;> fin_cases c₂ <;> simp at h ⊢
  col_bijective c := Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
    fin_cases c <;> fin_cases r₁ <;> fin_cases r₂ <;> simp at h ⊢

private def redLS4_1 : LatinSquare 4 where
  entry r c :=
    match r.val, c.val with
    | 0, _ => c
    | _, 0 => r
    | 1, 1 => 0 | 1, 2 => 3 | 1, 3 => 2
    | 2, 1 => 3 | 2, 2 => 1 | 2, 3 => 0
    | 3, 1 => 2 | 3, 2 => 0 | 3, 3 => 1
    | _, _ => 0
  row_bijective r := Finite.injective_iff_bijective.mp fun c₁ c₂ h => by
    fin_cases r <;> fin_cases c₁ <;> fin_cases c₂ <;> simp at h ⊢
  col_bijective c := Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
    fin_cases c <;> fin_cases r₁ <;> fin_cases r₂ <;> simp at h ⊢

private def redLS4_2 : LatinSquare 4 where
  entry r c :=
    match r.val, c.val with
    | 0, _ => c
    | _, 0 => r
    | 1, 1 => 2 | 1, 2 => 3 | 1, 3 => 0
    | 2, 1 => 3 | 2, 2 => 0 | 2, 3 => 1
    | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 2
    | _, _ => 0
  row_bijective r := Finite.injective_iff_bijective.mp fun c₁ c₂ h => by
    fin_cases r <;> fin_cases c₁ <;> fin_cases c₂ <;> simp at h ⊢
  col_bijective c := Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
    fin_cases c <;> fin_cases r₁ <;> fin_cases r₂ <;> simp at h ⊢

private def redLS4_3 : LatinSquare 4 where
  entry r c :=
    match r.val, c.val with
    | 0, _ => c
    | _, 0 => r
    | 1, 1 => 3 | 1, 2 => 0 | 1, 3 => 2
    | 2, 1 => 0 | 2, 2 => 3 | 2, 3 => 1
    | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0
    | _, _ => 0
  row_bijective r := Finite.injective_iff_bijective.mp fun c₁ c₂ h => by
    fin_cases r <;> fin_cases c₁ <;> fin_cases c₂ <;> simp at h ⊢
  col_bijective c := Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
    fin_cases c <;> fin_cases r₁ <;> fin_cases r₂ <;> simp at h ⊢

/-- Every one of our four reduced Latin squares of order 4 is symmetric (`L = L^T`),
so `colPerm = rowPerm` and therefore `squareSign = rowSign^2 = 1`. -/
private lemma squareSign_redLS4_all :
    squareSign redLS4_0 = 1 ∧ squareSign redLS4_1 = 1 ∧
    squareSign redLS4_2 = 1 ∧ squareSign redLS4_3 = 1 := by
  have hsym_sign : ∀ L : LatinSquare 4, (∀ i : Fin 4, colPerm L i = rowPerm L i) →
      squareSign L = 1 := by
    intro L hsym
    unfold squareSign rowSign colSign
    simp_rw [hsym]
    rcases Int.units_eq_one_or (∏ r : Fin 4, Equiv.Perm.sign (rowPerm L r)) with h | h <;>
      simp [h]
  exact ⟨hsym_sign redLS4_0 (fun i => by ext j; fin_cases i <;> fin_cases j <;> rfl),
         hsym_sign redLS4_1 (fun i => by ext j; fin_cases i <;> fin_cases j <;> rfl),
         hsym_sign redLS4_2 (fun i => by ext j; fin_cases i <;> fin_cases j <;> rfl),
         hsym_sign redLS4_3 (fun i => by ext j; fin_cases i <;> fin_cases j <;> rfl)⟩

/-- Every reduced Latin square of order 4 is symmetric (`L(r, c) = L(c, r)`) and belongs to
`{redLS4_0, redLS4_1, redLS4_2, redLS4_3}`! -/
private lemma eq_redLS4_of_isReduced (L : LatinSquare 4) (hL : IsReduced L) :
    L = redLS4_0 ∨ L = redLS4_1 ∨ L = redLS4_2 ∨ L = redLS4_3 := by
  have hr := (hL (by omega)).1
  have hc := (hL (by omega)).2
  have hfin4 : ∀ x : Fin 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := fun x => by fin_cases x <;> simp
  have hfin4_3 : ∀ (x a b c d : Fin 4),
      (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) → x ≠ a → x ≠ b → x ≠ c → x = d := by
    decide
  have hrow : ∀ r c₁ c₂ : Fin 4, c₁ ≠ c₂ → L.entry r c₁ ≠ L.entry r c₂ :=
    fun r c₁ c₂ hne h => hne ((L.row_bijective r).1 h)
  have hcol : ∀ c r₁ r₂ : Fin 4, r₁ ≠ r₂ → L.entry r₁ c ≠ L.entry r₂ c :=
    fun c r₁ r₂ hne h => hne ((L.col_bijective c).1 h)
  -- Helper: conclude `L = M` once all 9 inner entries match
  have hmk : ∀ M : LatinSquare 4,
      (∀ c, M.entry 0 c = c) → (∀ r, M.entry r 0 = r) →
      L.entry 1 1 = M.entry 1 1 → L.entry 1 2 = M.entry 1 2 → L.entry 1 3 = M.entry 1 3 →
      L.entry 2 1 = M.entry 2 1 → L.entry 2 2 = M.entry 2 2 → L.entry 2 3 = M.entry 2 3 →
      L.entry 3 1 = M.entry 3 1 → L.entry 3 2 = M.entry 3 2 → L.entry 3 3 = M.entry 3 3 →
      L = M := by
    intro M hM0 hM0c e11 e12 e13 e21 e22 e23 e31 e32 e33
    apply LatinSquare.ext; funext r c
    fin_cases r <;> fin_cases c <;> first | exact (hr _).trans (hM0 _).symm | exact (hc _).trans (hM0c _).symm | assumption
  -- Case split on `L.entry 1 1`, then `L.entry 1 2`, `L.entry 1 3`, `L.entry 2 1`, etc.
  have h01 : L.entry 0 1 = 1 := hr 1
  have h02 : L.entry 0 2 = 2 := hr 2
  have h03 : L.entry 0 3 = 3 := hr 3
  have h10 : L.entry 1 0 = 1 := hc 1
  have h20 : L.entry 2 0 = 2 := hc 2
  have h30 : L.entry 3 0 = 3 := hc 3
  have hne_11_1 : L.entry 1 1 ≠ 1 := fun h => hrow 1 1 0 (by decide) (h.trans h10.symm)
  have hne_12_2 : L.entry 1 2 ≠ 2 := fun h => hcol 2 1 0 (by decide) (h.trans h02.symm)
  have hne_12_1 : L.entry 1 2 ≠ 1 := fun h => hrow 1 2 0 (by decide) (h.trans h10.symm)
  have hne_13_3 : L.entry 1 3 ≠ 3 := fun h => hcol 3 1 0 (by decide) (h.trans h03.symm)
  have hne_13_1 : L.entry 1 3 ≠ 1 := fun h => hrow 1 3 0 (by decide) (h.trans h10.symm)
  have hne_21_1 : L.entry 2 1 ≠ 1 := fun h => hcol 1 2 0 (by decide) (h.trans h01.symm)
  have hne_21_2 : L.entry 2 1 ≠ 2 := fun h => hrow 2 1 0 (by decide) (h.trans h20.symm)
  have hne_31_1 : L.entry 3 1 ≠ 1 := fun h => hcol 1 3 0 (by decide) (h.trans h01.symm)
  have hne_31_3 : L.entry 3 1 ≠ 3 := fun h => hrow 3 1 0 (by decide) (h.trans h30.symm)
  have hne_22_2 : L.entry 2 2 ≠ 2 := fun h => hcol 2 2 0 (by decide) (h.trans h02.symm)
  have hne_23_2 : L.entry 2 3 ≠ 2 := fun h => hrow 2 3 0 (by decide) (h.trans h20.symm)
  have hne_23_3 : L.entry 2 3 ≠ 3 := fun h => hcol 3 2 0 (by decide) (h.trans h03.symm)
  have hne_32_2 : L.entry 3 2 ≠ 2 := fun h => hcol 2 3 0 (by decide) (h.trans h02.symm)
  have hne_32_3 : L.entry 3 2 ≠ 3 := fun h => hrow 3 2 0 (by decide) (h.trans h30.symm)
  have hne_33_3 : L.entry 3 3 ≠ 3 := fun h => hcol 3 3 0 (by decide) (h.trans h03.symm)
  rcases hfin4 (L.entry 1 1) with e11 | e11 | e11 | e11
  · -- L(1,1) = 0 -> L(1,2) = 3, L(1,3) = 2, L(2,1) = 3, L(3,1) = 2
    have e12 : L.entry 1 2 = 3 :=
      hfin4_3 _ 0 1 2 3 (by decide) (fun h => hrow 1 2 1 (by decide) (h.trans e11.symm)) hne_12_1 hne_12_2
    have e13 : L.entry 1 3 = 2 :=
      hfin4_3 _ 0 1 3 2 (by decide) (fun h => hrow 1 3 1 (by decide) (h.trans e11.symm)) hne_13_1
        (fun h => hrow 1 3 2 (by decide) (h.trans e12.symm))
    have e21 : L.entry 2 1 = 3 :=
      hfin4_3 _ 0 1 2 3 (by decide) (fun h => hcol 1 2 1 (by decide) (h.trans e11.symm)) hne_21_1 hne_21_2
    have e31 : L.entry 3 1 = 2 :=
      hfin4_3 _ 0 1 3 2 (by decide) (fun h => hcol 1 3 1 (by decide) (h.trans e11.symm)) hne_31_1
        (fun h => hcol 1 3 2 (by decide) (h.trans e21.symm))
    rcases hfin4 (L.entry 2 2) with e22 | e22 | e22 | e22
    · -- L(2,2) = 0 -> redLS4_0
      have e23 : L.entry 2 3 = 1 :=
        hfin4_3 _ 0 2 3 1 (by decide) (fun h => hrow 2 3 2 (by decide) (h.trans e22.symm)) hne_23_2
          (fun h => hrow 2 3 1 (by decide) (h.trans e21.symm))
      have e32 : L.entry 3 2 = 1 :=
        hfin4_3 _ 0 2 3 1 (by decide) (fun h => hcol 2 3 2 (by decide) (h.trans e22.symm)) hne_32_2
          (fun h => hcol 2 3 1 (by decide) (h.trans e12.symm))
      have e33 : L.entry 3 3 = 0 :=
        hfin4_3 _ 1 2 3 0 (by decide) (fun h => hrow 3 3 2 (by decide) (h.trans e32.symm))
          (fun h => hrow 3 3 1 (by decide) (h.trans e31.symm)) hne_33_3
      exact Or.inl (hmk redLS4_0 (fun c => by fin_cases c <;> rfl) (fun r => by fin_cases r <;> rfl)
        e11 e12 e13 e21 e22 e23 e31 e32 e33)
    · -- L(2,2) = 1 -> redLS4_1
      have e23 : L.entry 2 3 = 0 :=
        hfin4_3 _ 1 2 3 0 (by decide) (fun h => hrow 2 3 2 (by decide) (h.trans e22.symm)) hne_23_2
          (fun h => hrow 2 3 1 (by decide) (h.trans e21.symm))
      have e32 : L.entry 3 2 = 0 :=
        hfin4_3 _ 1 2 3 0 (by decide) (fun h => hcol 2 3 2 (by decide) (h.trans e22.symm)) hne_32_2
          (fun h => hcol 2 3 1 (by decide) (h.trans e12.symm))
      have e33 : L.entry 3 3 = 1 :=
        hfin4_3 _ 0 2 3 1 (by decide) (fun h => hrow 3 3 2 (by decide) (h.trans e32.symm))
          (fun h => hrow 3 3 1 (by decide) (h.trans e31.symm)) hne_33_3
      exact Or.inr (Or.inl (hmk redLS4_1 (fun c => by fin_cases c <;> rfl) (fun r => by fin_cases r <;> rfl)
        e11 e12 e13 e21 e22 e23 e31 e32 e33))
    · exact absurd e22 hne_22_2
    · exact absurd (e22.trans e21.symm) (hrow 2 2 1 (by decide))
  · exact absurd e11 hne_11_1
  · -- L(1,1) = 2 -> redLS4_2
    have e13 : L.entry 1 3 = 0 :=
      hfin4_3 _ 1 2 3 0 (by decide) hne_13_1 (fun h => hrow 1 3 1 (by decide) (h.trans e11.symm)) hne_13_3
    have e12 : L.entry 1 2 = 3 :=
      hfin4_3 _ 0 1 2 3 (by decide) (fun h => hrow 1 2 3 (by decide) (h.trans e13.symm)) hne_12_1 hne_12_2
    have e31 : L.entry 3 1 = 0 :=
      hfin4_3 _ 1 2 3 0 (by decide) hne_31_1 (fun h => hcol 1 3 1 (by decide) (h.trans e11.symm)) hne_31_3
    have e21 : L.entry 2 1 = 3 :=
      hfin4_3 _ 0 1 2 3 (by decide) (fun h => hcol 1 2 3 (by decide) (h.trans e31.symm)) hne_21_1 hne_21_2
    have e23 : L.entry 2 3 = 1 :=
      hfin4_3 _ 0 2 3 1 (by decide) (fun h => hcol 3 2 1 (by decide) (h.trans e13.symm)) hne_23_2 hne_23_3
    have e22 : L.entry 2 2 = 0 :=
      hfin4_3 _ 1 2 3 0 (by decide) (fun h => hrow 2 2 3 (by decide) (h.trans e23.symm)) hne_22_2
        (fun h => hrow 2 2 1 (by decide) (h.trans e21.symm))
    have e32 : L.entry 3 2 = 1 :=
      hfin4_3 _ 0 2 3 1 (by decide) (fun h => hcol 2 3 2 (by decide) (h.trans e22.symm)) hne_32_2
        (fun h => hcol 2 3 1 (by decide) (h.trans e12.symm))
    have e33 : L.entry 3 3 = 2 :=
      hfin4_3 _ 0 1 3 2 (by decide) (fun h => hrow 3 3 1 (by decide) (h.trans e31.symm))
        (fun h => hrow 3 3 2 (by decide) (h.trans e32.symm)) hne_33_3
    exact Or.inr (Or.inr (Or.inl (hmk redLS4_2 (fun c => by fin_cases c <;> rfl) (fun r => by fin_cases r <;> rfl)
      e11 e12 e13 e21 e22 e23 e31 e32 e33)))
  · -- L(1,1) = 3 -> redLS4_3
    have e12 : L.entry 1 2 = 0 :=
      hfin4_3 _ 1 2 3 0 (by decide) hne_12_1 hne_12_2 (fun h => hrow 1 2 1 (by decide) (h.trans e11.symm))
    have e13 : L.entry 1 3 = 2 :=
      hfin4_3 _ 0 1 3 2 (by decide) (fun h => hrow 1 3 2 (by decide) (h.trans e12.symm)) hne_13_1 hne_13_3
    have e21 : L.entry 2 1 = 0 :=
      hfin4_3 _ 1 2 3 0 (by decide) hne_21_1 hne_21_2 (fun h => hcol 1 2 1 (by decide) (h.trans e11.symm))
    have e31 : L.entry 3 1 = 2 :=
      hfin4_3 _ 0 1 3 2 (by decide) (fun h => hcol 1 3 2 (by decide) (h.trans e21.symm)) hne_31_1 hne_31_3
    have e23 : L.entry 2 3 = 1 :=
      hfin4_3 _ 0 2 3 1 (by decide) (fun h => hrow 2 3 1 (by decide) (h.trans e21.symm)) hne_23_2 hne_23_3
    have e22 : L.entry 2 2 = 3 :=
      hfin4_3 _ 0 1 2 3 (by decide) (fun h => hrow 2 2 1 (by decide) (h.trans e21.symm))
        (fun h => hrow 2 2 3 (by decide) (h.trans e23.symm)) hne_22_2
    have e32 : L.entry 3 2 = 1 :=
      hfin4_3 _ 0 2 3 1 (by decide) (fun h => hcol 2 3 1 (by decide) (h.trans e12.symm)) hne_32_2
        (fun h => hcol 2 3 2 (by decide) (h.trans e22.symm))
    have e33 : L.entry 3 3 = 0 :=
      hfin4_3 _ 1 2 3 0 (by decide) (fun h => hrow 3 3 2 (by decide) (h.trans e32.symm))
        (fun h => hrow 3 3 1 (by decide) (h.trans e31.symm)) hne_33_3
    exact Or.inr (Or.inr (Or.inr (hmk redLS4_3 (fun c => by fin_cases c <;> rfl) (fun r => by fin_cases r <;> rfl)
      e11 e12 e13 e21 e22 e23 e31 e32 e33)))

private lemma squareSign_eq_one_two (L : LatinSquare 2) : squareSign L = 1 := by
  obtain ⟨σ, hred⟩ := exists_reduced_isotopy (by omega) L
  have h1 := squareSign_isotopyAct_even ⟨1, rfl⟩ σ L
  rw [eq_redLS2_of_isReduced _ hred, squareSign_redLS2] at h1
  exact h1.symm

private lemma squareSign_eq_one_four (L : LatinSquare 4) : squareSign L = 1 := by
  obtain ⟨σ, hred⟩ := exists_reduced_isotopy (by omega) L
  have h1 := squareSign_isotopyAct_even ⟨2, rfl⟩ σ L
  rcases eq_redLS4_of_isReduced _ hred with h | h | h | h
  · rw [h, squareSign_redLS4_all.1] at h1; exact h1.symm
  · rw [h, squareSign_redLS4_all.2.1] at h1; exact h1.symm
  · rw [h, squareSign_redLS4_all.2.2.1] at h1; exact h1.symm
  · rw [h, squareSign_redLS4_all.2.2.2] at h1; exact h1.symm

lemma reducedDelta_two : reducedDelta 2 = 1 := by
  classical
  unfold reducedDelta
  have hfilt : (Finset.univ.filter fun L : LatinSquare 2 => IsReduced L) = {redLS2} := by
    ext L; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨eq_redLS2_of_isReduced L, fun h => h ▸ isReduced_redLS2⟩
  rw [hfilt, Finset.sum_singleton, squareSign_redLS2]
  rfl

lemma reducedDelta_four : reducedDelta 4 = 4 := by
  classical
  unfold reducedDelta
  have hred0 : IsReduced redLS4_0 := fun _ =>
    ⟨fun c => by fin_cases c <;> rfl, fun r => by fin_cases r <;> rfl⟩
  have hred1 : IsReduced redLS4_1 := fun _ =>
    ⟨fun c => by fin_cases c <;> rfl, fun r => by fin_cases r <;> rfl⟩
  have hred2 : IsReduced redLS4_2 := fun _ =>
    ⟨fun c => by fin_cases c <;> rfl, fun r => by fin_cases r <;> rfl⟩
  have hred3 : IsReduced redLS4_3 := fun _ =>
    ⟨fun c => by fin_cases c <;> rfl, fun r => by fin_cases r <;> rfl⟩
  have hfilt : (Finset.univ.filter fun L : LatinSquare 4 => IsReduced L) =
      {redLS4_0, redLS4_1, redLS4_2, redLS4_3} := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact ⟨eq_redLS4_of_isReduced L, fun h => by rcases h with rfl | rfl | rfl | rfl <;> assumption⟩
  have h01 : redLS4_0 ≠ redLS4_1 := fun h => by
    have := congrArg (fun M => M.entry 2 2) h; exact absurd this (by decide)
  have h02 : redLS4_0 ≠ redLS4_2 := fun h => by
    have := congrArg (fun M => M.entry 1 1) h; exact absurd this (by decide)
  have h03 : redLS4_0 ≠ redLS4_3 := fun h => by
    have := congrArg (fun M => M.entry 1 1) h; exact absurd this (by decide)
  have h12 : redLS4_1 ≠ redLS4_2 := fun h => by
    have := congrArg (fun M => M.entry 1 1) h; exact absurd this (by decide)
  have h13 : redLS4_1 ≠ redLS4_3 := fun h => by
    have := congrArg (fun M => M.entry 1 1) h; exact absurd this (by decide)
  have h23 : redLS4_2 ≠ redLS4_3 := fun h => by
    have := congrArg (fun M => M.entry 1 1) h; exact absurd this (by decide)
  rw [hfilt, Finset.sum_insert (by simp [h01, h02, h03]),
    Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton, squareSign_redLS4_all.1, squareSign_redLS4_all.2.1,
    squareSign_redLS4_all.2.2.1, squareSign_redLS4_all.2.2.2]
  rfl

lemma cVal_two : cVal 2 = 4 := by
  have h1 := (eq_cn_reduced_proved 2 ⟨1, rfl⟩ (by omega)).1
  rw [h1, reducedDelta_two]
  decide

lemma cVal_four : cVal 4 = 24 := by
  have h1 := (eq_cn_reduced_proved 4 ⟨2, rfl⟩ (by omega)).1
  rw [h1, reducedDelta_four]
  decide

/-- Explicit even Latin square of order 6 (cyclic addition mod 6). -/
private def evenLS6 : LatinSquare 6 where
  entry r c := ⟨(r.val + c.val) % 6, Nat.mod_lt _ (by omega)⟩
  row_bijective r := Finite.injective_iff_bijective.mp fun c₁ c₂ h => by
    fin_cases r <;> fin_cases c₁ <;> fin_cases c₂ <;> simp at h ⊢
  col_bijective c := Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
    fin_cases c <;> fin_cases r₁ <;> fin_cases r₂ <;> simp at h ⊢

private lemma squareSign_evenLS6 : squareSign evenLS6 = 1 := by
  have hsym : ∀ i : Fin 6, colPerm evenLS6 i = rowPerm evenLS6 i := by
    intro i; ext j; fin_cases i <;> fin_cases j <;> rfl
  unfold squareSign rowSign colSign
  simp_rw [hsym]
  rcases Int.units_eq_one_or (∏ r : Fin 6, Equiv.Perm.sign (rowPerm evenLS6 r)) with h | h <;>
    simp [h]

/-- Entry table for an explicit odd Latin square of order 6 (2×3 trade on `ZMod 2 × ZMod 3`). -/
private def oddLS6Entry : Fin 6 → Fin 6 → Fin 6 :=
  ![![1, 2, 0, 3, 4, 5],
    ![0, 1, 2, 4, 5, 3],
    ![2, 0, 1, 5, 3, 4],
    ![3, 4, 5, 0, 1, 2],
    ![4, 5, 3, 1, 2, 0],
    ![5, 3, 4, 2, 0, 1]]

private lemma oddLS6Entry_row_inj : ∀ r c₁ c₂ : Fin 6, oddLS6Entry r c₁ = oddLS6Entry r c₂ → c₁ = c₂ := by
  decide

private lemma oddLS6Entry_col_inj : ∀ c r₁ r₂ : Fin 6, oddLS6Entry r₁ c = oddLS6Entry r₂ c → r₁ = r₂ := by
  decide

/-- Explicit odd Latin square of order 6 (2×3 trade on `ZMod 2 × ZMod 3`). -/
private def oddLS6 : LatinSquare 6 where
  entry := oddLS6Entry
  row_bijective r := Finite.injective_iff_bijective.mp (oddLS6Entry_row_inj r)
  col_bijective c := Finite.injective_iff_bijective.mp (oddLS6Entry_col_inj c)

private lemma squareSign_oddLS6 : squareSign oddLS6 = -1 := by
  -- Express each row and column of `oddLS6` as an explicit product of swaps!
  let s (a b : Fin 6) : Equiv.Perm (Fin 6) := Equiv.swap a b
  have hsw : ∀ a b : Fin 6, a ≠ b → Equiv.Perm.sign (s a b) = -1 :=
    fun a b h => Equiv.Perm.sign_swap h
  have hr0 : rowPerm oddLS6 0 = s 0 2 * s 0 1 := by ext c; fin_cases c <;> rfl
  have hr1 : rowPerm oddLS6 1 = s 3 5 * s 3 4 := by ext c; fin_cases c <;> rfl
  have hr2 : rowPerm oddLS6 2 = s 0 1 * s 0 2 * (s 3 4 * s 3 5) := by ext c; fin_cases c <;> rfl
  have hr3 : rowPerm oddLS6 3 = s 0 3 * s 1 4 * s 2 5 := by ext c; fin_cases c <;> rfl
  have hr4 : rowPerm oddLS6 4 = s 0 5 * s 0 1 * s 0 3 * s 0 2 * s 0 4 := by ext c; fin_cases c <;> rfl
  have hr5 : rowPerm oddLS6 5 = s 0 4 * s 0 2 * s 0 3 * s 0 1 * s 0 5 := by ext c; fin_cases c <;> rfl
  have hc0 : colPerm oddLS6 0 = s 0 1 := by ext r; fin_cases r <;> rfl
  have hc1 : colPerm oddLS6 1 = s 0 2 * (s 3 5 * s 3 4) := by ext r; fin_cases r <;> rfl
  have hc2 : colPerm oddLS6 2 = s 1 2 * (s 3 4 * s 3 5) := by ext r; fin_cases r <;> rfl
  have hc3 : colPerm oddLS6 3 = s 0 3 * s 1 4 * s 2 5 := by ext r; fin_cases r <;> rfl
  have hc4 : colPerm oddLS6 4 = s 0 5 * s 0 1 * s 0 3 * s 0 2 * s 0 4 := by ext r; fin_cases r <;> rfl
  have hc5 : colPerm oddLS6 5 = s 0 4 * s 0 2 * s 0 3 * s 0 1 * s 0 5 := by ext r; fin_cases r <;> rfl
  unfold squareSign rowSign colSign
  rw [Fin.prod_univ_six, Fin.prod_univ_six,
    hr0, hr1, hr2, hr3, hr4, hr5, hc0, hc1, hc2, hc3, hc4, hc5]
  simp only [map_mul,
    hsw 0 1 (by decide), hsw 0 2 (by decide), hsw 1 2 (by decide),
    hsw 3 4 (by decide), hsw 3 5 (by decide),
    hsw 0 3 (by decide), hsw 1 4 (by decide), hsw 2 5 (by decide),
    hsw 0 4 (by decide), hsw 0 5 (by decide)]
  rfl

theorem sec1_fig1_small_counts_proved :
    oddCount 2 = 0 ∧ oddCount 4 = 0 ∧ 0 < evenCount 6 ∧ 0 < oddCount 6 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold oddCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro L _; rw [squareSign_eq_one_two L]; decide
  · unfold oddCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro L _; rw [squareSign_eq_one_four L]; decide
  · unfold evenCount
    exact Finset.card_pos.mpr ⟨evenLS6, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact squareSign_evenLS6⟩
  · unfold oddCount
    exact Finset.card_pos.mpr ⟨oddLS6, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact squareSign_oddLS6⟩

/-! ### Section 6 Concrete In-Text Lemmas (`|C_m| = C(q, m) / q` and `τ_3 = -3`) -/

theorem centeredSubsets_card (q m : ℕ) [NeZero q] (hq : q.Prime) (_hodd : q ≠ 2)
    (hm0 : 0 < m) (hmq : m < q) :
    (centeredSubsets q m).card = q.choose m / q := by
  have : Fact q.Prime := ⟨hq⟩
  have hm_ne0 : (m : ZMod q) ≠ 0 := by
    intro h
    have hdvd : q ∣ m := (ZMod.natCast_eq_zero_iff m q).mp h
    have := Nat.le_of_dvd hm0 hdvd
    omega
  -- Bijection between `centeredSubsets q m × ZMod q` and `Finset.powersetCard m Finset.univ`
  let S := Finset.powersetCard m (Finset.univ : Finset (ZMod q))
  have hS_card : S.card = q.choose m := by
    rw [Finset.card_powersetCard, Finset.card_univ, ZMod.card]
  have hbij : (centeredSubsets q m).card * q = S.card := by
    have hprod : (centeredSubsets q m).card * q =
        (centeredSubsets q m ×ˢ (Finset.univ : Finset (ZMod q))).card := by
      rw [Finset.card_product, Finset.card_univ, ZMod.card]
    rw [hprod]
    refine Finset.card_bij (fun p _ => p.1.image (fun x => x + p.2)) ?_ ?_ ?_
    · intro ⟨X, t⟩ hXt
      have hX := (Finset.mem_filter.mp (Finset.mem_product.mp hXt).1).2
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_image_of_injective _ (add_left_injective t), hX.1]
    · intro ⟨X₁, t₁⟩ h₁ ⟨X₂, t₂⟩ h₂ hEq
      have hX1 := (Finset.mem_filter.mp (Finset.mem_product.mp h₁).1).2
      have hX2 := (Finset.mem_filter.mp (Finset.mem_product.mp h₂).1).2
      have hsum := congrArg (fun A : Finset (ZMod q) => ∑ d ∈ A, d) hEq
      rw [Finset.sum_image (fun _ _ _ _ h => add_left_injective t₁ h),
          Finset.sum_image (fun _ _ _ _ h => add_left_injective t₂ h),
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          hX1.2, hX2.2, zero_add, zero_add,
          Finset.sum_const, Finset.sum_const, hX1.1, hX2.1,
          nsmul_eq_mul, nsmul_eq_mul] at hsum
      have ht : t₁ = t₂ := mul_left_cancel₀ hm_ne0 hsum
      subst ht
      refine Prod.ext ?_ rfl
      ext x
      have hx := Finset.ext_iff.mp hEq (x + t₁)
      simp only [Finset.mem_image] at hx
      constructor
      · intro hx1
        rcases hx.mp ⟨x, hx1, rfl⟩ with ⟨y, hy2, hyx⟩
        rwa [add_right_cancel hyx] at hy2
      · intro hx2
        rcases hx.mpr ⟨x, hx2, rfl⟩ with ⟨y, hy1, hyx⟩
        rwa [add_right_cancel hyx] at hy1
    · intro A hA
      have hAcard : A.card = m := (Finset.mem_powersetCard.mp hA).2
      let t : ZMod q := (m : ZMod q)⁻¹ * (∑ d ∈ A, d)
      let X : Finset (ZMod q) := A.image (fun d => d - t)
      have hX_mem : X ∈ centeredSubsets q m := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [Finset.card_image_of_injective _ (sub_left_injective), hAcard]
        · rw [Finset.sum_image (fun _ _ _ _ h => sub_left_injective h),
              Finset.sum_sub_distrib, Finset.sum_const, hAcard, nsmul_eq_mul]
          dsimp only [t]
          rw [← mul_assoc, mul_inv_cancel₀ hm_ne0, one_mul, sub_self]
      refine ⟨(X, t), Finset.mem_product.mpr ⟨hX_mem, Finset.mem_univ _⟩, ?_⟩
      ext y
      simp only [X, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; simpa using ha
      · intro hy; exact ⟨y - t, ⟨y, hy, rfl⟩, by ring⟩
  rw [← hS_card, ← hbij, Nat.mul_div_cancel _ hq.pos]

theorem tauQ_three : tauQ 3 = -3 := by
  have h1 := (lem_6_5_complete 3 Nat.prime_three (by decide)).1
  rw [h1]
  suffices ht : tQ 3 = -1 by rw [ht]; ring
  classical
  unfold tQ
  -- Only one complete map of `ZMod 3` satisfies `h(0) = 0`: `x ↦ 2 * x`!
  let h2 : Equiv.Perm (ZMod 3) := Equiv.mulLeft₀ (2 : ZMod 3) (by decide)
  have hh2_cm : IsCompleteMap h2 := by
    refine Finite.injective_iff_bijective.mp fun x y h => ?_
    fin_cases x <;> fin_cases y <;> first | rfl | exact absurd h (by decide)
  let elem : { h : Equiv.Perm (ZMod 3) // IsCompleteMap h } := ⟨h2, hh2_cm⟩
  have hfin3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hfilt :
      Finset.univ.filter
        (fun h : { h : Equiv.Perm (ZMod 3) // IsCompleteMap h } => h.1 0 = 0) = {elem} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h0
      have h1ne0 : h.1 1 ≠ 0 := fun e => absurd (h.1.injective (e.trans h0.symm)) (by decide)
      have h1ne1 : h.1 1 ≠ 1 := fun e => by
        have hdiff : h.1 1 - 1 = h.1 0 - 0 := by rw [e, h0]; decide
        exact absurd (h.2.1 hdiff) (by decide)
      have h1eq : h.1 1 = 2 := by
        rcases hfin3 (h.1 1) with hv | hv | hv <;> simp_all
      have h2ne0 : h.1 2 ≠ 0 := fun e => absurd (h.1.injective (e.trans h0.symm)) (by decide)
      have h2ne2 : h.1 2 ≠ 2 := fun e => absurd (h.1.injective (e.trans h1eq.symm)) (by decide)
      have h2eq : h.1 2 = 1 := by
        rcases hfin3 (h.1 2) with hv | hv | hv <;> simp_all
      apply Subtype.ext; ext x
      fin_cases x
      · exact h0
      · exact h1eq
      · exact h2eq
    · rintro rfl; change h2 0 = 0; decide
  rw [hfilt, Finset.sum_singleton]
  have hs1 : Equiv.Perm.sign elem.1 = -1 := by
    have : elem.1 = Equiv.swap (1 : ZMod 3) 2 := by
      ext x; change h2 x = Equiv.swap (1 : ZMod 3) 2 x; fin_cases x <;> decide
    rw [this, Equiv.Perm.sign_swap (by decide)]
  have hs2 : Equiv.Perm.sign (Equiv.ofBijective (fun x : ZMod 3 => elem.1 x - x) elem.2) = 1 := by
    have : Equiv.ofBijective (fun x : ZMod 3 => elem.1 x - x) elem.2 = 1 := by
      ext x; change h2 x - x = x; simp only [h2, Equiv.mulLeft₀_apply]; ring
    rw [this, map_one]
  rw [hs1, hs2]
  rfl

/-! ### Assembly of Theorems B, A, Section 7 Uniform Divisor, Numeric & Small-Order Claims -/

private lemma prime_dvd_factorial_iff {p m : ℕ} (hp : p.Prime) : p ∣ m.factorial ↔ p ≤ m := by
  induction m with
  | zero => exact ⟨fun h => absurd h hp.not_dvd_one, fun h => by have := hp.pos; omega⟩
  | succ m ih =>
    rw [Nat.factorial_succ, hp.dvd_mul, ih]
    constructor
    · rintro (h | h)
      · exact Nat.le_of_dvd (Nat.succ_pos m) h
      · omega
    · intro hle
      by_cases heq : p = m + 1
      · exact Or.inl (heq ▸ dvd_refl _)
      · exact Or.inr (by omega)

theorem thm_B_of
    (h_6_1 : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧ (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q)))
    (n q : ℕ) (heven : Even n) (hn : 8 ≤ n) (hq : q.Prime) (hqle : q ≤ n - 2) :
    (naturalModulus q n : ℤ) ∣ reducedDelta n := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hq2 : q = 2
  · subst hq2
    exact ((thm_4_1_quadratic_proved n heven (by omega)).2.2 2 hq (Or.inl ⟨rfl, hn⟩)).2
  · by_cases h3q : 3 * q ≤ n
    · exact ((thm_4_1_quadratic_proved n heven (by omega)).2.2 q hq (Or.inr ⟨hq2, h3q⟩)).2
    · by_cases h2q : 2 * q < n
      · exact (thm_5_5_quad_P_proved q n hq hq2 heven h2q (by omega)).2.2.2
      · by_cases heq : n = 2 * q
        · subst heq
          have hq4 : q ≠ 4 := fun h => by rw [h] at hq; exact absurd hq (by decide)
          have hq5 : 5 ≤ q := by have := hq.two_le; omega
          have hval_fact : padicValNat q (2 * q).factorial = 2 := by
            have hlt : Nat.log q (2 * q) < 2 := by
              rw [Nat.log_lt_iff_lt_pow hq.one_lt (by omega)]
              calc 2 * q < q * q := by nlinarith
                _ = q ^ 2 := (sq q).symm
            have hleg := padicValNat_factorial (p := q) (n := 2 * q) (b := 2) hlt
            rw [hleg, Finset.sum_Ico_succ_top (by omega), Finset.Ico_self, Finset.sum_empty, zero_add]
            simp [Nat.mul_div_cancel _ hq.pos]
          have hval_n : padicValNat q (2 * q) = 1 := by
            have hcop : ¬ (q ∣ 2) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
            rw [padicValNat.mul (by omega) hq.ne_zero, padicValNat.eq_zero_of_not_dvd hcop,
              padicValNat.self hq.one_lt, zero_add]
          unfold naturalModulus
          rw [hval_fact, hval_n]
          exact (h_6_1 q hq hq2).2 hq5
        · have hlt : n < 2 * q := by omega
          have hval_fact : padicValNat q n.factorial = 1 := by
            have hlt2 : Nat.log q n < 2 := by
              rw [Nat.log_lt_iff_lt_pow hq.one_lt (by omega)]
              have := hq.two_le
              calc n < 2 * q := hlt
                _ < q * q := by nlinarith
                _ = q ^ 2 := (sq q).symm
            have hleg := padicValNat_factorial (p := q) (n := n) (b := 2) hlt2
            rw [hleg, Finset.sum_Ico_succ_top (by omega), Finset.Ico_self, Finset.sum_empty, zero_add]
            simp only [pow_one]
            exact Nat.div_eq_of_lt_le (by omega) (by omega)
          have hval_n : padicValNat q n = 0 := by
            apply padicValNat.eq_zero_of_not_dvd
            intro h
            rcases h with ⟨k, hk⟩
            have : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
            rcases this with rfl | rfl | hk2
            · omega
            · omega
            · nlinarith
          unfold naturalModulus
          rw [hval_fact, hval_n, add_zero, pow_one]
          exact stones_wanless_thm_3_5_proved n q heven hq hlt hqle

theorem thm_A_of
    (h_6_1 : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧ (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q)))
    (n : ℕ) (heven : Even n) (hn : 8 ≤ n) :
    cVal n = (if (n - 1).Prime then n - 1 else 1) ∧
    (¬ (n - 1).Prime → ((n.factorial : ℤ) ^ 3 ∣ delta n)) ∧
    ((n - 1).Prime →
      (((n.factorial ^ 3 / (n - 1) : ℕ) : ℤ) ∣ delta n) ∧
      ¬ ((n.factorial : ℤ) ^ 3 ∣ delta n)) := by
  have hB := thm_B_of h_6_1 n
  have hcn := eq_cn_reduced_proved n heven (by omega)
  have hcn_pos : 0 < cVal n := by
    rw [hcn.1]
    exact Nat.div_pos (Nat.gcd_le_right _ (mul_pos (Nat.factorial_pos n) (by omega)))
      (Nat.gcd_pos_of_pos_right _ (mul_pos (Nat.factorial_pos n) (by omega)))
  have hcn_dvd : cVal n ∣ n.factorial * n := by
    rw [hcn.1]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  -- Any prime `q ∣ cVal n` must satisfy `q = n - 1`
  have hprime_eq : ∀ q : ℕ, q.Prime → q ∣ cVal n → q = n - 1 := by
    intro q hq hq_dvd
    have hq_dvd_nn : q ∣ n.factorial * n := hq_dvd.trans hcn_dvd
    have hq_le_n : q ≤ n := by
      rcases hq.dvd_mul.mp hq_dvd_nn with h1 | h2
      · exact (prime_dvd_factorial_iff hq).mp h1
      · exact Nat.le_of_dvd (by omega) h2
    have hq_ne_n : q ≠ n := by
      intro h; subst h
      rcases heven with ⟨k, hk⟩
      have h2dvd : 2 ∣ q := ⟨k, by omega⟩
      rcases (Nat.dvd_prime hq).mp h2dvd with h1 | h2 <;> omega
    have hq_gt : ¬ (q ≤ n - 2) := fun hle =>
      ((hcn.2 q hq).mpr (hB q heven hn hq hle)) hq_dvd
    omega
  have hcVal_eq : cVal n = if (n - 1).Prime then n - 1 else 1 := by
    split_ifs with hp
    · -- `p = n - 1` is an odd prime
      set p := n - 1
      have : Fact p.Prime := ⟨hp⟩
      have hp_odd : p ≠ 2 := by omega
      have hn_eq : n = p + 1 := by omega
      -- Show `p ∣ cVal n` via Drisko (1997)
      have hp_ndvd_D : ¬ ((naturalModulus p n : ℤ) ∣ reducedDelta n) := by
        intro hdvd
        have hdr := drisko_1997_proved p hp hp_odd
        rw [← hn_eq] at hdr
        have hnorm := eq_normal_proved n heven
        -- `p ∣ reducedDelta n` since `naturalModulus p n ≥ p`
        have hp_dvd_M : (p : ℤ) ∣ (naturalModulus p n : ℤ) := by
          unfold naturalModulus
          have h1 : 1 ≤ padicValNat p n.factorial + padicValNat p n := by
            have : 1 ≤ padicValNat p n.factorial :=
              one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n)
                ((prime_dvd_factorial_iff hp).mpr (by omega))
            omega
          exact_mod_cast dvd_pow_self p (by omega : padicValNat p n.factorial + padicValNat p n ≠ 0)
        have hp_dvd_D : (p : ℤ) ∣ reducedDelta n := hp_dvd_M.trans hdvd
        have hp_dvd_fact : (p : ℤ) ∣ (n.factorial : ℤ) := by
          exact_mod_cast (prime_dvd_factorial_iff hp).mpr (by omega)
        have hp_dvd_fact1 : (p : ℤ) ∣ ((n - 1).factorial : ℤ) := by
          exact_mod_cast (prime_dvd_factorial_iff hp).mpr (by omega)
        have hp3_dvd : (p : ℤ) ^ 3 ∣ delta n := by
          rw [hnorm, Nat.cast_mul]
          have : (p : ℤ) * (p : ℤ) * (p : ℤ) ∣
              (n.factorial : ℤ) * ((n - 1).factorial : ℤ) * reducedDelta n :=
            mul_dvd_mul (mul_dvd_mul hp_dvd_fact hp_dvd_fact1) hp_dvd_D
          simpa [pow_three, mul_assoc] using this
        have hcong : (p : ℤ) ^ 3 ∣ (-1 : ℤ) ^ ((p + 1) / 2) * (p : ℤ) ^ 2 := by
          have hsub := Int.modEq_iff_dvd.mp hdr
          have := dvd_add hsub hp3_dvd
          simpa [hn_eq] using this
        have hpm : ((-1 : ℤ) ^ ((p + 1) / 2) * (p : ℤ) ^ 2).natAbs = p ^ 2 := by
          rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
            Int.natAbs_pow, Int.natAbs_natCast]
        have hnat : p ^ 3 ∣ p ^ 2 := by
          have := Int.natCast_dvd.mp hcong
          rwa [hpm] at this
        have hle := Nat.le_of_dvd (pow_pos hp.pos 2) hnat
        have := hp.two_le
        have : p ^ 2 * p ≤ p ^ 2 * 1 := by simpa [pow_succ] using hle
        nlinarith
      have hp_dvd_c : p ∣ cVal n := by
        by_contra hnot
        exact hp_ndvd_D ((hcn.2 p hp).mp hnot)
      -- Moreover `v_p(n! * n) = 1`, so `¬ (p^2 ∣ cVal n)`
      have hv_nn : padicValNat p (n.factorial * n) = 1 := by
        have hv_n : padicValNat p n = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro h
          have : p ∣ 1 := by
            have := Nat.dvd_sub h (dvd_refl p)
            rwa [show n - p = 1 by omega] at this
          exact hp.not_dvd_one this
        have hv_f : padicValNat p n.factorial = 1 := by
          have hlt : Nat.log p n < 2 := by
            rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega)]
            have := hp.two_le
            calc n = p + 1 := hn_eq
              _ < p * p := by nlinarith
              _ = p ^ 2 := (sq p).symm
          have hleg := padicValNat_factorial (p := p) (n := n) (b := 2) hlt
          rw [hleg, Finset.sum_Ico_succ_top (by omega), Finset.Ico_self, Finset.sum_empty, zero_add]
          simp only [pow_one]
          exact Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [padicValNat.mul (Nat.factorial_ne_zero n) (by omega), hv_f, hv_n, add_zero]
      have hnp2 : ¬ (p ^ 2 ∣ cVal n) := by
        intro h2
        have h2' : p ^ 2 ∣ n.factorial * n := h2.trans hcn_dvd
        have hle := (padicValNat_dvd_iff_le (p := p) (n := 2)
          (mul_ne_zero (Nat.factorial_ne_zero n) (by omega))).mp h2'
        omega
      rcases hp_dvd_c with ⟨k, hk⟩
      have hk1 : k = 1 := by
        by_contra hne
        have hk_pos : 0 < k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          rw [hk0, mul_zero] at hk
          omega
        obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
        have hr_c : r ∣ cVal n := by rw [hk]; exact dvd_mul_of_dvd_right hr_dvd p
        have hr_eq : r = p := hprime_eq r hr_prime hr_c
        subst hr_eq
        apply hnp2
        rcases hr_dvd with ⟨m, hm⟩
        exact ⟨m, by rw [hk, hm]; ring⟩
      rw [hk, hk1, mul_one]
    · -- `n - 1` is not prime, so `cVal n` has no prime factors -> `cVal n = 1`
      by_contra hne
      obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
      have := hprime_eq q hq_prime hq_dvd
      rw [this] at hq_prime
      exact hp hq_prime
  -- Deduce the divisibility equivalences directly from `cVal n = (n!)^3 / gcd(|Δ_n|, (n!)^3)`
  have hg_dvd_delta : (Nat.gcd (delta n).natAbs (n.factorial ^ 3) : ℤ) ∣ delta n :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hg_mul_c : Nat.gcd (delta n).natAbs (n.factorial ^ 3) * cVal n = n.factorial ^ 3 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  refine ⟨hcVal_eq, fun hnp => ?_, fun hp => ?_⟩
  · have hc1 : cVal n = 1 := by rw [hcVal_eq, if_neg hnp]
    rw [hc1, mul_one] at hg_mul_c
    rw [← Nat.cast_pow, ← hg_mul_c]
    exact hg_dvd_delta
  · have hcp : cVal n = n - 1 := by rw [hcVal_eq, if_pos hp]
    rw [hcp] at hg_mul_c
    have hdiv_eq : n.factorial ^ 3 / (n - 1) = Nat.gcd (delta n).natAbs (n.factorial ^ 3) := by
      conv_lhs => rw [← hg_mul_c]
      exact Nat.mul_div_cancel _ (by omega)
    refine ⟨by rw [hdiv_eq]; exact hg_dvd_delta, fun hdvd => ?_⟩
    have hdvd_nat : n.factorial ^ 3 ∣ (delta n).natAbs := by
      have hdvd' : ((n.factorial ^ 3 : ℕ) : ℤ) ∣ delta n := by rwa [Nat.cast_pow]
      exact Int.natCast_dvd.mp hdvd'
    have hgcd_eq : Nat.gcd (delta n).natAbs (n.factorial ^ 3) = n.factorial ^ 3 :=
      Nat.gcd_eq_right hdvd_nat
    rw [hgcd_eq] at hg_mul_c
    have : n.factorial ^ 3 * (n - 1) = n.factorial ^ 3 * 1 := by simpa using hg_mul_c
    have hpos : 0 < n.factorial ^ 3 := by positivity
    have := Nat.eq_of_mul_eq_mul_left hpos this
    omega

theorem sec7_uniform_divisor_of
    (h_6_1 : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧ (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q)))
    (n : ℕ) (heven : Even n) (hn : 8 ≤ n) :
    ((n ^ 2 * (n - 2).factorial : ℕ) : ℤ) ∣ reducedDelta n := by
  have hB := thm_B_of h_6_1 n
  by_cases hD0 : reducedDelta n = 0
  · rw [hD0]; exact dvd_zero _
  · rw [Int.natCast_dvd]
    have hDabs : (reducedDelta n).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
    have hne : n ^ 2 * (n - 2).factorial ≠ 0 :=
      mul_ne_zero (by positivity) (Nat.factorial_ne_zero _)
    rw [← Nat.factorization_le_iff_dvd hne hDabs]
    intro q
    by_cases hq : q.Prime
    · have : Fact q.Prime := ⟨hq⟩
      rw [Nat.factorization_def _ hq, Nat.factorization_def _ hq]
      by_cases hqle : q ≤ n - 2
      · have hdvd_B : naturalModulus q n ∣ (reducedDelta n).natAbs :=
          Int.natCast_dvd.mp (hB q heven hn hq hqle)
        have hM_le : padicValNat q n.factorial + padicValNat q n ≤
            padicValNat q (reducedDelta n).natAbs :=
          (padicValNat_dvd_iff_le hDabs).mp hdvd_B
        have hsub : n ^ 2 * (n - 2).factorial ∣ n.factorial * n := by
          have hfact : n.factorial = n * (n - 1) * (n - 2).factorial := by
            have h1 : n = (n - 1) + 1 := by omega
            have h2 : n - 1 = (n - 2) + 1 := by omega
            conv_lhs => rw [h1, Nat.factorial_succ, ← h1]
            conv_lhs => rw [h2, Nat.factorial_succ, ← h2]
            ring
          exact ⟨n - 1, by rw [hfact]; ring⟩
        have hle1 : padicValNat q (n ^ 2 * (n - 2).factorial) ≤
            padicValNat q (n.factorial * n) := by
          have hlt := (Nat.factorization_le_iff_dvd hne
            (mul_ne_zero (Nat.factorial_ne_zero n) (by omega))).mpr hsub q
          rwa [Nat.factorization_def _ hq, Nat.factorization_def _ hq] at hlt
        rw [padicValNat.mul (Nat.factorial_ne_zero n) (by omega)] at hle1
        exact hle1.trans hM_le
      · -- `q > n - 2` cannot divide `n^2 * (n - 2)!` since `n ≥ 8` is even!
        have hndvd : ¬ (q ∣ n ^ 2 * (n - 2).factorial) := by
          intro h
          rcases hq.dvd_mul.mp h with h1 | h2
          · have hqn : q ∣ n := hq.dvd_of_dvd_pow h1
            rcases heven with ⟨k, hk⟩
            have h2dvd : 2 ∣ n := ⟨k, by omega⟩
            rcases hqn with ⟨m, hm⟩
            have hm1 : m ≠ 1 := by
              intro hm1; rw [hm1, mul_one] at hm; subst hm
              rcases (Nat.dvd_prime hq).mp h2dvd with h1 | h2 <;> omega
            have hm2 : 2 ≤ m := by
              by_contra hlt
              have hm0 : m = 0 := by omega
              rw [hm0, mul_zero] at hm
              omega
            have hqge : n ≤ q + 1 := by omega
            nlinarith
          · exact hqle ((prime_dvd_factorial_iff hq).mp h2)
        rw [padicValNat.eq_zero_of_not_dvd hndvd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq]; exact Nat.zero_le _

private lemma two_pow_dvd_reducedDelta_of_qVal (n k e : ℕ) (heven : Even n)
    (hqval : qVal 2 (delta n) ≥ (k : ℕ∞))
    (hle : e + v2Fact n + v2Fact (n - 1) ≤ k) :
    ((2 : ℤ) ^ e ∣ reducedDelta n) := by
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have hv : ∀ m : ℕ, padicValNat 2 m.factorial = v2Fact m := fun m => (v2Fact_eq_padicValNat m).symm
  have hnorm := eq_normal_proved n heven
  rw [hnorm] at hqval
  by_cases hD0 : reducedDelta n = 0
  · rw [hD0]; exact dvd_zero _
  · rw [qVal_mul Nat.prime_two,
      qVal_natCast (mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1))),
      padicValNat.mul (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (n - 1)), hv, hv,
      qVal, if_neg hD0] at hqval
    have hcast : ((v2Fact n + v2Fact (n - 1) : ℕ) : ℕ∞) + (padicValInt 2 (reducedDelta n) : ℕ∞) =
        ((v2Fact n + v2Fact (n - 1) + padicValInt 2 (reducedDelta n) : ℕ) : ℕ∞) :=
      (Nat.cast_add _ _).symm
    rw [hcast] at hqval
    have hnat : k ≤ v2Fact n + v2Fact (n - 1) + padicValInt 2 (reducedDelta n) :=
      Nat.cast_le.mp hqval
    have he_le : e ≤ padicValInt 2 (reducedDelta n) := by omega
    have he_nat : 2 ^ e ∣ (reducedDelta n).natAbs :=
      (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hD0)).mpr he_le
    exact_mod_cast Int.natCast_dvd.mpr he_nat

private lemma prime_not_dvd_reducedDelta_succ (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    ¬ ((p : ℤ) ∣ reducedDelta (p + 1)) := by
  intro hpD
  have heven : Even (p + 1) := by
    rcases hp.odd_of_ne_two hodd with ⟨k, rfl⟩
    exact ⟨k + 1, by omega⟩
  have hdr := drisko_1997_proved p hp hodd
  have hnorm := eq_normal_proved (p + 1) heven
  have hp3 : (p : ℤ) ^ 3 ∣ delta (p + 1) := by
    rw [hnorm, Nat.cast_mul]
    have h1 : (p : ℤ) ∣ ((p + 1).factorial : ℤ) := by
      exact_mod_cast (prime_dvd_factorial_iff hp).mpr (by omega)
    have h2 : (p : ℤ) ∣ (((p + 1) - 1).factorial : ℤ) := by
      exact_mod_cast (prime_dvd_factorial_iff hp).mpr (by omega)
    have := mul_dvd_mul (mul_dvd_mul h1 h2) hpD
    simpa [pow_three, mul_assoc] using this
  have hsub := Int.modEq_iff_dvd.mp hdr
  have hcong : (p : ℤ) ^ 3 ∣ (-1 : ℤ) ^ ((p + 1) / 2) * (p : ℤ) ^ 2 := by
    simpa using dvd_add hsub hp3
  have hpm : ((-1 : ℤ) ^ ((p + 1) / 2) * (p : ℤ) ^ 2).natAbs = p ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
      Int.natAbs_pow, Int.natAbs_natCast]
  have hnat : p ^ 3 ∣ p ^ 2 := by
    have := Int.natCast_dvd.mp hcong
    rwa [hpm] at this
  have hle := Nat.le_of_dvd (pow_pos hp.pos 2) hnat
  have := hp.two_le
  have : p ^ 2 * p ≤ p ^ 2 * 1 := by simpa [pow_succ] using hle
  nlinarith

theorem sec4_numeric_bounds_of
    (h_6_1 : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧ (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q))) :
    ((2 : ℤ) ^ 13 ∣ reducedDelta 8) ∧
    naturalModulus 2 8 = 2 ^ 10 ∧
    ((2 : ℤ) ^ 181 ∣ reducedDelta 26) ∧
    ((2 : ℤ) ^ 146 ∣ reducedDelta 26) ∧
    naturalModulus 2 26 = 2 ^ 24 ∧
    cVal 26 = 1 ∧
    padicValNat 2 1 + ∑ N ∈ Finset.Icc 1 1, fVal 2 2 N = 1 ∧
    padicValNat 2 (Nat.factorial 3) + ∑ N ∈ Finset.Icc 1 3, fVal 2 4 N = 6 ∧
    padicValNat 2 (Nat.factorial 5) + ∑ N ∈ Finset.Icc 1 5, fVal 2 6 N = 13 ∧
    padicValNat 2 (Nat.factorial 7) + ∑ N ∈ Finset.Icc 1 7, fVal 2 8 N = 24 ∧
    padicValNat 2 (Nat.factorial 9) + ∑ N ∈ Finset.Icc 1 9, fVal 2 10 N = 37 := by
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have htab := sum_fVal_two_small
  have hv : ∀ m : ℕ, padicValNat 2 m.factorial = v2Fact m := fun m => (v2Fact_eq_padicValNat m).symm
  have h8_val : qVal 2 (delta 8) ≥ (24 : ℕ∞) := by
    have h := (thm_4_1_quadratic_proved 8 ⟨4, rfl⟩ (by omega)).1 2 Nat.prime_two
    have hsum : padicValNat 2 (Nat.factorial 7) + ∑ N ∈ Finset.Icc 1 7, fVal 2 8 N = 24 := by
      rw [hv 7, htab.2.2.2.1]; decide
    have hcast : ((padicValNat 2 (Nat.factorial 7) + ∑ N ∈ Finset.Icc 1 7, fVal 2 8 N : ℕ) : ℕ∞) =
        (padicValNat 2 (Nat.factorial 7) : ℕ∞) + ∑ N ∈ Finset.Icc 1 7, (fVal 2 8 N : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_sum]
    simpa [← hcast, hsum] using h
  have h26_val : qVal 2 (delta 26) ≥ (226 : ℕ∞) := by
    have h := (thm_4_1_quadratic_proved 26 ⟨13, rfl⟩ (by omega)).1 2 Nat.prime_two
    have hsum : padicValNat 2 (Nat.factorial 25) + ∑ N ∈ Finset.Icc 1 25, fVal 2 26 N = 226 := by
      rw [hv 25, htab.2.2.2.2.2]; decide
    have hcast : ((padicValNat 2 (Nat.factorial 25) + ∑ N ∈ Finset.Icc 1 25, fVal 2 26 N : ℕ) : ℕ∞) =
        (padicValNat 2 (Nat.factorial 25) : ℕ∞) + ∑ N ∈ Finset.Icc 1 25, (fVal 2 26 N : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_sum]
    simpa [← hcast, hsum] using h
  have h26_181 : (2 : ℤ) ^ 181 ∣ reducedDelta 26 :=
    two_pow_dvd_reducedDelta_of_qVal 26 226 181 ⟨13, rfl⟩ h26_val (by decide)
  have hM2_8 : naturalModulus 2 8 = 2 ^ 10 := by
    unfold naturalModulus; rw [hv 8]
    have h8 : padicValNat 2 8 = 3 := by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, padicValNat.prime_pow]
    rw [h8]; decide
  have hM2_26 : naturalModulus 2 26 = 2 ^ 24 := by
    unfold naturalModulus; rw [hv 26]
    have h26 : padicValNat 2 26 = 1 := by
      rw [show (26 : ℕ) = 2 * 13 by decide, padicValNat.mul (by decide) (by decide),
        padicValNat.self (by decide), padicValNat.eq_zero_of_not_dvd (by decide)]
    rw [h26]; decide
  have hc26 : cVal 26 = 1 := by
    have hA := (thm_A_of h_6_1 26 ⟨13, rfl⟩ (by omega)).1
    have hnp : ¬ Nat.Prime 25 := by decide
    simpa [hnp] using hA
  refine ⟨two_pow_dvd_reducedDelta_of_qVal 8 24 13 ⟨4, rfl⟩ h8_val (by decide), hM2_8, h26_181,
    (pow_dvd_pow (2 : ℤ) (by omega : 146 ≤ 181)).trans h26_181, hM2_26, hc26, ?_, ?_, ?_, ?_, ?_⟩
  · rw [padicValNat.eq_zero_of_not_dvd (by decide), htab.1]
  · rw [hv 3, htab.2.1]; decide
  · rw [hv 5, htab.2.2.1]; decide
  · rw [hv 7, htab.2.2.2.1]; decide
  · rw [hv 9, htab.2.2.2.2.1]; decide

private lemma fact6_mul6_eq : Nat.factorial 6 * 6 = 288 * 15 := by
  have hf4 : Nat.factorial 4 = 24 := rfl
  have hf5 : Nat.factorial 5 = 5 * 24 := by rw [Nat.factorial_succ, hf4]
  have hf6 : Nat.factorial 6 = 6 * (5 * 24) := by rw [Nat.factorial_succ, hf5]
  have h1 : 12 * 24 = 288 := by norm_num
  have h2 : 3 * 5 = 15 := by norm_num
  calc Nat.factorial 6 * 6 = (6 * (5 * 24)) * 6 := by rw [hf6]
    _ = (12 * 24) * (3 * 5) := by ring
    _ = 288 * 15 := by rw [h1, h2]

private lemma two_pow_five_dvd_reducedDelta_six : (2 : ℤ) ^ 5 ∣ reducedDelta 6 := by
  have h6_val : qVal 2 (delta 6) ≥ (13 : ℕ∞) := by
    have h := (thm_4_1_quadratic_proved 6 ⟨3, rfl⟩ (by omega)).1 2 Nat.prime_two
    have hv5 : padicValNat 2 (Nat.factorial 5) = v2Fact 5 := (v2Fact_eq_padicValNat 5).symm
    have hsum : padicValNat 2 (Nat.factorial 5) + ∑ N ∈ Finset.Icc 1 5, fVal 2 6 N = 13 := by
      rw [hv5, sum_fVal_two_small.2.2.1]; decide
    have hcast : ((padicValNat 2 (Nat.factorial 5) + ∑ N ∈ Finset.Icc 1 5, fVal 2 6 N : ℕ) : ℕ∞) =
        (padicValNat 2 (Nat.factorial 5) : ℕ∞) + ∑ N ∈ Finset.Icc 1 5, (fVal 2 6 N : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_sum]
    simpa [← hcast, hsum] using h
  exact two_pow_dvd_reducedDelta_of_qVal 6 13 5 ⟨3, rfl⟩ h6_val (by decide)

private lemma gcd_288_15_eq_288 (d : ℕ) (h32 : 32 ∣ d) (h9 : 9 ∣ d)
    (h27 : ¬ (27 ∣ d)) (h5 : ¬ (5 ∣ d)) :
    Nat.gcd d (288 * 15) = 288 := by
  have h288_dvd : 288 ∣ Nat.gcd d (288 * 15) := by
    apply Nat.dvd_gcd _ (dvd_mul_right 288 15)
    have hcop : Nat.Coprime 32 9 := by norm_num
    have hmul : 32 * 9 ∣ d := hcop.mul_dvd_of_dvd_of_dvd h32 h9
    rwa [show (32 : ℕ) * 9 = 288 by norm_num] at hmul
  rcases h288_dvd with ⟨m, hm⟩
  have hm_dvd15 : m ∣ 15 := by
    have h1 : 288 * m ∣ 288 * 15 := hm ▸ Nat.gcd_dvd_right _ _
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 288)).mp h1
  have h3_ndvd_m : ¬ (3 ∣ m) := by
    intro h3m
    apply h27
    have h1 : 288 * m ∣ d := hm ▸ Nat.gcd_dvd_left _ _
    have h27' : 27 ∣ 288 * m := by
      rcases h3m with ⟨t, rfl⟩
      refine ⟨32 * t, ?_⟩
      rw [show (288 : ℕ) = 9 * 32 by norm_num, show (27 : ℕ) = 9 * 3 by norm_num]
      ring
    exact h27'.trans h1
  have h5_ndvd_m : ¬ (5 ∣ m) := by
    intro h5m
    apply h5
    have h1 : 288 * m ∣ d := hm ▸ Nat.gcd_dvd_left _ _
    exact (dvd_mul_of_dvd_right h5m 288).trans h1
  have hm1 : m = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hne
    have hq15 : q ∣ 3 * 5 := by
      rw [show (3 : ℕ) * 5 = 15 by norm_num]
      exact hqm.trans hm_dvd15
    rcases hq.dvd_mul.mp hq15 with hq3 | hq5
    · rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hq3 with rfl | rfl
      · exact hq.ne_one rfl
      · exact h3_ndvd_m hqm
    · rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hq5 with rfl | rfl
      · exact hq.ne_one rfl
      · exact h5_ndvd_m hqm
  rw [hm, hm1, mul_one]

private lemma cVal_six_of
    (h_6_1 : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧ (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q)))
    (h_6_nine : reducedDelta 6 / 9 ≡ 1 [ZMOD 3] ∧ ¬ ((27 : ℤ) ∣ reducedDelta 6)) :
    cVal 6 = 15 := by
  have hcn := (eq_cn_reduced_proved 6 ⟨3, rfl⟩ (by omega)).1
  have h32 : 32 ∣ (reducedDelta 6).natAbs := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
    exact_mod_cast Int.natCast_dvd.mp two_pow_five_dvd_reducedDelta_six
  have h9 : 9 ∣ (reducedDelta 6).natAbs := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact_mod_cast Int.natCast_dvd.mp (h_6_1 3 Nat.prime_three (by decide)).1
  have h27 : ¬ (27 ∣ (reducedDelta 6).natAbs) := fun h => h_6_nine.2 (Int.natCast_dvd.mpr h)
  have h5 : ¬ (5 ∣ (reducedDelta 6).natAbs) := fun h =>
    prime_not_dvd_reducedDelta_succ 5 (by decide) (by decide) (Int.natCast_dvd.mpr h)
  have hgcd_eq := gcd_288_15_eq_288 (reducedDelta 6).natAbs h32 h9 h27 h5
  rw [hcn, fact6_mul6_eq, hgcd_eq, Nat.mul_div_cancel_left 15 (by norm_num)]

theorem sec1_small_orders_and_headline_of
    (h_6_1 : ∀ q : ℕ, q.Prime → q ≠ 2 →
      ((q : ℤ) ^ 2 ∣ reducedDelta (2 * q)) ∧ (5 ≤ q → (q : ℤ) ^ 3 ∣ reducedDelta (2 * q)))
    (h_6_nine : reducedDelta 6 / 9 ≡ 1 [ZMOD 3] ∧ ¬ ((27 : ℤ) ∣ reducedDelta 6)) :
    cVal 2 = 4 ∧ cVal 4 = 24 ∧ cVal 6 = 15 ∧
    ∀ n : ℕ, Even n → 2 < n → (1 < cVal n ↔ (n - 1).Prime) := by
  have hc6 : cVal 6 = 15 := cVal_six_of h_6_1 h_6_nine
  refine ⟨cVal_two, cVal_four, hc6, fun n heven hn => ?_⟩
  rcases heven with ⟨k, rfl⟩
  have hk2 : 2 ≤ k := by omega
  by_cases hk2_eq : k = 2
  · subst hk2_eq
    rw [show 2 + 2 = 4 from rfl, cVal_four]
    exact iff_of_true (by norm_num) (by decide)
  · by_cases hk3_eq : k = 3
    · subst hk3_eq
      rw [show 3 + 3 = 6 from rfl, hc6]
      exact iff_of_true (by norm_num) (by decide)
    · have h8 : 8 ≤ k + k := by omega
      have hA := (thm_A_of h_6_1 (k + k) ⟨k, rfl⟩ h8).1
      rw [hA]
      split_ifs with hp
      · simp only [hp, iff_true]; omega
      · simp [hp]

theorem sec6_concrete_in_text_of
    (h_6_6 : ∀ q : ℕ, [NeZero q] → q.Prime → q ≠ 2 →
      (∑ H ∈ sylowSubgroupsOfRank q 2, S_twoq q H) =
        2 * (q : ℤ) ^ 4 * ((q : ℤ) - 1) ^ 5 * ((q : ℤ) - 2) * ((q : ℤ) + 1) -
        8 * (q : ℤ) ^ 3 * ((q : ℤ) - 1) ^ 5 * tauQ q +
        4 * (q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 4 * (q.factorial : ℤ) ^ 2)
    (h_6_nine : reducedDelta 6 / 9 ≡ 1 [ZMOD 3] ∧ ¬ ((27 : ℤ) ∣ reducedDelta 6)) :
    (reducedDelta 6 / 9 ≡ 1 [ZMOD 3] ∧ ¬ ((27 : ℤ) ∣ reducedDelta 6)) ∧
    tauQ 3 = -3 ∧
    (∑ H ∈ sylowSubgroupsOfRank 3 2, S_twoq 3 H) = 62208 ∧
    ∀ (q m : ℕ) [NeZero q], q.Prime → q ≠ 2 → 0 < m → m < q →
      (centeredSubsets q m).card = q.choose m / q := by
  refine ⟨h_6_nine, tauQ_three, ?_, fun q m _ hq hodd hm0 hmq =>
    centeredSubsets_card q m hq hodd hm0 hmq⟩
  rw [h_6_6 3 Nat.prime_three (by decide), tauQ_three]
  norm_num [Nat.factorial]

end AlonTarsi.Proofs

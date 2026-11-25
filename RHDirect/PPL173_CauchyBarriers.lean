/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# PPL 173 (Erdős #711): Unconditional Lean 4 Formalization of All Four Cauchy–Schwarz Minimax Barriers

This standalone pure-Mathlib file formally proves the four minimax barrier theorems complementing
`RHDirect/PPL173_WorldRecordHalf.lean` (`F(n) ≤ n^{4/3} exp(O((log n / log log n)^{1/2}))`):

1. **Barrier Theorem 1 (`barrier1_unabsorbed_two_thirds`):**
   Without Bad-Difference Absorption, every set-theoretic cover `D = (N/2, N] ⊆ ⋃_{α ∈ idx} S α`
   satisfies
   ```
   ∑ α ∈ idx, κ(S α, ⌊N^(4/3)⌋)^(2/3) * |S α|^(1/3)
     ≥ N^(1/3) * exp(c * (log N / log log N)^(2/3)).
   ```
2. **Barrier Theorem 2a (`barrier2a_absorbed_half`):**
   Even with Bad-Difference Absorption (even setting `K₁ ≡ 1`), every set-theoretic cover
   `D = (N/2, N] ⊆ ⋃_{α ∈ idx} S α` satisfies
   ```
   ∑ α ∈ idx, κ(S α, ⌊N^(4/3)⌋)^(1/3) * |S α|^(1/3)
     ≥ N^(1/3) * exp(c * (log N / log log N)^(1/2)).
   ```
3. **Barrier Theorem 2b (`barrier2b_single_slice_avg_half`):**
   Replacing worst-case `ℓ^∞` multiplicity `κ` by the `ℓ^2` average over `U × U`,
   `κ_bar(S, U) = |U|⁻² ∑_{z₁ ≠ z₂ ∈ U} r_S(|z₁ - z₂|)`, still stalls at exponent `1/2` on a
   single prime-count slice `S_k ⊆ (N/2, N]` with an explicit set `U ⊆ [1, ⌊N^(4/3)⌋]` of size
   `|U| = |S_k|`.
4. **Barrier Theorem 2c (`barrier2c_deterministic_U0_all_partitions`):**
   A single deterministic primorial progression `U₀ = {P * j : 1 ≤ j ≤ N} ⊆ [1, ⌊N^(4/3)⌋]`
   simultaneously forces
   ```
   ∑ α ∈ idx, κ_bar(S α, U₀)^(1/3) * |S α|^(1/3)
     ≥ N^(1/3) * exp(c * (log N)^(1/2) / log log N)
   ```
   across every set-theoretic cover `D = (N/2, N] ⊆ ⋃_{α ∈ idx} S α`.

## Honest Scope
All four theorems are proved unconditionally in pure Mathlib with explicit positive constants `c > 0`
using completely elementary Chebyshev dyadic prime counting and finite `Finset.powerset` Markov
arguments. Refinement of the leading constants to the exact PNT values `18^(-1/3)` and `2/(3√3)` is
carried out in `REPORT.md`.
-/

namespace PPL173Barriers

/-! ### Section 1: Elementary Real & Partition-Elimination Inequalities -/

/-- Elementary lower bound `1 / 2 ≤ log 2`. -/
private lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h1 : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
    have := Real.add_one_le_exp (-(1 : ℝ) / 2); linarith
  have hexp_le : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
    have hinv : Real.exp (-(1 : ℝ) / 2) = (Real.exp ((1 : ℝ) / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hinv] at h1
    have hpos : 0 < Real.exp ((1 : ℝ) / 2) := Real.exp_pos _
    have hmul : (1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2) ≤ 1 := by
      calc (1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2)
          ≤ (Real.exp ((1 : ℝ) / 2))⁻¹ * Real.exp ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hexp_le
  rwa [Real.log_exp] at hlog

/-- Elementary upper bound `log 2 ≤ 1`. -/
private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- For `0 ≤ x ≤ 1`, `exp (x / 2) ≤ 1 + x`. -/
private lemma exp_half_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (x / 2) ≤ 1 + x := by
  have h1 : Real.exp (-(x / 2)) ≥ 1 - x / 2 := by
    have := Real.add_one_le_exp (-(x / 2)); linarith
  have hpos : 0 < Real.exp (x / 2) := Real.exp_pos _
  have hinv : Real.exp (-(x / 2)) = (Real.exp (x / 2))⁻¹ := Real.exp_neg (x / 2)
  rw [hinv] at h1
  have hmul : (1 - x / 2) * Real.exp (x / 2) ≤ 1 := by
    calc (1 - x / 2) * Real.exp (x / 2)
        ≤ (Real.exp (x / 2))⁻¹ * Real.exp (x / 2) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hden : 0 < 1 - x / 2 := by linarith
  have hprod : 1 ≤ (1 - x / 2) * (1 + x) := by nlinarith
  nlinarith

/-- Young's inequality for `(3/2, 3)`: `x^(2/3) * y^(1/3) ≤ (2/3) * x + (1/3) * y`. -/
private lemma rpow_two_thirds_mul_one_third_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ ((2 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) / 3 * x + (1 : ℝ) / 3 * y := by
  let u := x ^ ((1 : ℝ) / 3)
  let v := y ^ ((1 : ℝ) / 3)
  have hu : 0 ≤ u := Real.rpow_nonneg hx _
  have hv : 0 ≤ v := Real.rpow_nonneg hy _
  have hu2 : x ^ ((2 : ℝ) / 3) = u ^ 2 := by
    dsimp [u]; rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hx]; norm_num
  have hu3 : u ^ 3 = x := by
    dsimp [u]; rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hx]; norm_num
  have hv3 : v ^ 3 = y := by
    dsimp [v]; rw [← Real.rpow_natCast (y ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hy]; norm_num
  rw [hu2]
  have hident : 2 * u ^ 3 + v ^ 3 - 3 * (u ^ 2 * v) = (u - v) ^ 2 * (2 * u + v) := by ring
  have hnn : 0 ≤ (u - v) ^ 2 * (2 * u + v) := mul_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- Hölder `(3/2, 3)` on a finset: `∑ x ∈ S, f x ^ (2/3) ≤ (∑ x ∈ S, f x)^(2/3) * |S|^(1/3)`. -/
private lemma sum_rpow_two_thirds_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    ∑ x ∈ S, (f x) ^ ((2 : ℝ) / 3) ≤ (∑ x ∈ S, f x) ^ ((2 : ℝ) / 3) * (S.card : ℝ) ^ ((1 : ℝ) / 3) := by
  set A := ∑ x ∈ S, f x
  have hA_nn : 0 ≤ A := Finset.sum_nonneg hf
  by_cases hA0 : A = 0
  · have hzero : ∀ x ∈ S, f x = 0 := (Finset.sum_eq_zero_iff_of_nonneg hf).mp hA0
    have hL : ∑ x ∈ S, (f x) ^ ((2 : ℝ) / 3) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [hzero x hx, Real.zero_rpow (by norm_num)]
    rw [hL]; positivity
  by_cases hS0 : S.card = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
    subst hSe; simp
  have hA_pos : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA0)
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hS0
  have hstep : ∑ x ∈ S, (f x / A) ^ ((2 : ℝ) / 3) * ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 3) ≤ 1 := by
    calc ∑ x ∈ S, (f x / A) ^ ((2 : ℝ) / 3) * ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 3)
        ≤ ∑ x ∈ S, ((2 : ℝ) / 3 * (f x / A) + (1 : ℝ) / 3 * ((1 : ℝ) / (S.card : ℝ))) :=
          Finset.sum_le_sum fun x hx =>
            rpow_two_thirds_mul_one_third_le (div_nonneg (hf x hx) (le_of_lt hA_pos)) (by positivity)
      _ = (2 : ℝ) / 3 * (A / A) + (1 : ℝ) / 3 * ((S.card : ℝ) / (S.card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ = 1 := by rw [div_self (ne_of_gt hA_pos), div_self (ne_of_gt hS_pos)]; ring
  have hrew : ∑ x ∈ S, (f x / A) ^ ((2 : ℝ) / 3) * ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 3) =
      (∑ x ∈ S, (f x) ^ ((2 : ℝ) / 3)) / (A ^ ((2 : ℝ) / 3) * (S.card : ℝ) ^ ((1 : ℝ) / 3)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Real.div_rpow (hf x hx) (le_of_lt hA_pos),
      Real.div_rpow (by norm_num) (le_of_lt hS_pos), Real.one_rpow]
    ring
  rw [hrew, div_le_one (by positivity)] at hstep
  exact hstep

/-- Cauchy–Schwarz on a finset: `∑ x ∈ S, f x ^ (1/2) ≤ (∑ x ∈ S, f x)^(1/2) * |S|^(1/2)`. -/
private lemma sum_rpow_half_le {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    ∑ x ∈ S, (f x) ^ ((1 : ℝ) / 2) ≤ (∑ x ∈ S, f x) ^ ((1 : ℝ) / 2) * (S.card : ℝ) ^ ((1 : ℝ) / 2) := by
  set A := ∑ x ∈ S, f x
  have hA_nn : 0 ≤ A := Finset.sum_nonneg hf
  by_cases hA0 : A = 0
  · have hzero : ∀ x ∈ S, f x = 0 := (Finset.sum_eq_zero_iff_of_nonneg hf).mp hA0
    have hL : ∑ x ∈ S, (f x) ^ ((1 : ℝ) / 2) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [hzero x hx, Real.zero_rpow (by norm_num)]
    rw [hL]; positivity
  by_cases hS0 : S.card = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
    subst hSe; simp
  have hA_pos : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA0)
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hS0
  have hstep : ∑ x ∈ S, (f x / A) ^ ((1 : ℝ) / 2) * ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 2) ≤ 1 := by
    calc ∑ x ∈ S, (f x / A) ^ ((1 : ℝ) / 2) * ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ ∑ x ∈ S, ((1 : ℝ) / 2 * (f x / A) + (1 : ℝ) / 2 * ((1 : ℝ) / (S.card : ℝ))) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have h1 : 0 ≤ (f x / A) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (div_nonneg (hf x hx) (le_of_lt hA_pos)) _
          have h2 : 0 ≤ ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
          have hsq1 : ((f x / A) ^ ((1 : ℝ) / 2)) ^ 2 = f x / A := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (div_nonneg (hf x hx) (le_of_lt hA_pos))]; norm_num
          have hsq2 : (((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 = 1 / (S.card : ℝ) := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
          nlinarith [sq_nonneg ((f x / A) ^ ((1 : ℝ) / 2) - ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 2))]
      _ = (1 : ℝ) / 2 * (A / A) + (1 : ℝ) / 2 * ((S.card : ℝ) / (S.card : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ = 1 := by rw [div_self (ne_of_gt hA_pos), div_self (ne_of_gt hS_pos)]; ring
  have hrew : ∑ x ∈ S, (f x / A) ^ ((1 : ℝ) / 2) * ((1 : ℝ) / (S.card : ℝ)) ^ ((1 : ℝ) / 2) =
      (∑ x ∈ S, (f x) ^ ((1 : ℝ) / 2)) / (A ^ ((1 : ℝ) / 2) * (S.card : ℝ) ^ ((1 : ℝ) / 2)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Real.div_rpow (hf x hx) (le_of_lt hA_pos),
      Real.div_rpow (by norm_num) (le_of_lt hS_pos), Real.one_rpow]
    ring
  rw [hrew, div_le_one (by positivity)] at hstep
  exact hstep

/-- `ℓ^{3/2} ≤ ℓ^1` monotonicity: `∑ x_i^{3/2} ≤ (∑ x_i)^{3/2}` for `x_i ≥ 0`. -/
private lemma sum_rpow_three_halves_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i) ^ ((3 : ℝ) / 2) ≤ (∑ i ∈ s, f i) ^ ((3 : ℝ) / 2) := by
  set S : ℝ := ∑ i ∈ s, f i
  have hS : 0 ≤ S := Finset.sum_nonneg hf
  have hpt : ∀ i ∈ s, (f i) ^ ((3 : ℝ) / 2) ≤ f i * S ^ ((1 : ℝ) / 2) := by
    intro i hi
    have hfi : 0 ≤ f i := hf i hi
    have hfi_le : f i ≤ S := Finset.single_le_sum hf hi
    have hsplit : (f i) ^ ((3 : ℝ) / 2) = f i * (f i) ^ ((1 : ℝ) / 2) := by
      by_cases h0 : f i = 0
      · rw [h0, Real.zero_rpow (by norm_num), zero_mul]
      · have hpos : 0 < f i := lt_of_le_of_ne hfi (Ne.symm h0)
        rw [show ((3 : ℝ) / 2) = 1 + ((1 : ℝ) / 2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfi hfi_le (by norm_num)) hfi
  calc ∑ i ∈ s, (f i) ^ ((3 : ℝ) / 2)
      ≤ ∑ i ∈ s, f i * S ^ ((1 : ℝ) / 2) := Finset.sum_le_sum hpt
    _ = S * S ^ ((1 : ℝ) / 2) := by rw [← Finset.sum_mul]
    _ = S ^ ((3 : ℝ) / 2) := by
        by_cases h0 : S = 0
        · rw [h0, zero_mul, Real.zero_rpow (by norm_num)]
        · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm h0)
          rw [show ((3 : ℝ) / 2) = 1 + ((1 : ℝ) / 2) by norm_num, Real.rpow_add hpos, Real.rpow_one]

/-- Subadditivity of nonnegative sums over `Finset.biUnion`. -/
private lemma finset_sum_biUnion_le {ι α : Type*} [DecidableEq α] (idx : Finset ι)
    (S : ι → Finset α) (f : α → ℝ) (hf : ∀ x ∈ idx.biUnion S, 0 ≤ f x) :
    ∑ x ∈ idx.biUnion S, f x ≤ ∑ i ∈ idx, ∑ x ∈ S i, f x := by
  classical
  induction idx using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hf_a : ∀ x ∈ S a, 0 ≤ f x := fun x hx =>
      hf x (Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self a s, hx⟩)
    have hf_s : ∀ x ∈ s.biUnion S, 0 ≤ f x := fun x hx => by
      rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
      exact hf x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_insert_of_mem hi, hxi⟩)
    have hunion : ∑ x ∈ S a ∪ s.biUnion S, f x ≤ ∑ x ∈ S a, f x + ∑ x ∈ s.biUnion S, f x := by
      have h := Finset.sum_union_inter (s₁ := S a) (s₂ := s.biUnion S) (f := f)
      have hinter_nn : 0 ≤ ∑ x ∈ S a ∩ s.biUnion S, f x :=
        Finset.sum_nonneg fun x hx => hf_a x (Finset.mem_inter.mp hx).1
      linarith
    exact le_trans hunion (add_le_add (le_refl _) (ih hf_s))

/-- Abstract Partition-Elimination for Barrier 1 (`2/3`): for any sub-probability weight `w` on
`Icc 1 H` and any cover `D ⊆ idx.biUnion S`,
`∑ d ∈ D, p_w(d)^(2/3) ≤ ∑ α ∈ idx, κ(S α, H)^(2/3) * |S α|^(1/3)`. -/
private lemma partition_lower_two_thirds {ι : Type*} (D : Finset ℕ) (H : ℕ)
    (w : ℕ → ℝ) (hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t) (hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1)
    (idx : Finset ι) (S : ι → Finset ℕ) (hcover : D ⊆ idx.biUnion S) :
    let p_w : ℕ → ℝ := fun d => ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t
    ∑ d ∈ D, (p_w d) ^ ((2 : ℝ) / 3) ≤
      ∑ α ∈ idx,
        (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
          ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  intro p_w
  have hp_nn : ∀ d, 0 ≤ p_w d := fun d =>
    Finset.sum_nonneg fun t ht => hw_nn t (Finset.mem_filter.mp ht).1
  have hsum_le_κ : ∀ α ∈ idx, ∑ d ∈ S α, p_w d ≤
      (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) := by
    intro α _
    have hswap : ∑ d ∈ S α, p_w d =
        ∑ t ∈ Finset.Icc 1 H, (((S α).filter (fun d => d ∣ t)).card : ℝ) * w t := by
      have h1 : ∀ d ∈ S α, p_w d = ∑ t ∈ Finset.Icc 1 H, if d ∣ t then w t else 0 := fun d _ => by
        dsimp [p_w]; rw [Finset.sum_filter]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hswap]
    set κ := (Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card)
    calc ∑ t ∈ Finset.Icc 1 H, (((S α).filter (fun d => d ∣ t)).card : ℝ) * w t
        ≤ ∑ t ∈ Finset.Icc 1 H, (κ : ℝ) * w t := by
          refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right ?_ (hw_nn t ht)
          exact_mod_cast Finset.le_sup (f := fun t => ((S α).filter (fun d => d ∣ t)).card) ht
      _ = (κ : ℝ) * ∑ t ∈ Finset.Icc 1 H, w t := by rw [← Finset.mul_sum]
      _ ≤ (κ : ℝ) * 1 := mul_le_mul_of_nonneg_left hw_sum (Nat.cast_nonneg _)
      _ = (κ : ℝ) := mul_one _
  calc ∑ d ∈ D, (p_w d) ^ ((2 : ℝ) / 3)
      ≤ ∑ d ∈ idx.biUnion S, (p_w d) ^ ((2 : ℝ) / 3) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ => Real.rpow_nonneg (hp_nn d) _
    _ ≤ ∑ α ∈ idx, ∑ d ∈ S α, (p_w d) ^ ((2 : ℝ) / 3) :=
        finset_sum_biUnion_le idx S (fun d => (p_w d) ^ ((2 : ℝ) / 3)) (fun d _ => Real.rpow_nonneg (hp_nn d) _)
    _ ≤ ∑ α ∈ idx,
          (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
            ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
        refine Finset.sum_le_sum fun α hα => ?_
        have h1 := sum_rpow_two_thirds_le (S α) p_w (fun d _ => hp_nn d)
        have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => hp_nn d) (hsum_le_κ α hα) (by norm_num : (0 : ℝ) ≤ 2 / 3)
        exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))

/-- Abstract Partition-Elimination for Barrier 2a (`1/2`): for any sub-probability weight `w` on
`Icc 1 H` and any cover `D ⊆ idx.biUnion S`,
`(∑ d ∈ D, p_w(d)^(1/2))^(2/3) ≤ ∑ α ∈ idx, κ(S α, H)^(1/3) * |S α|^(1/3)`. -/
private lemma partition_lower_half {ι : Type*} (D : Finset ℕ) (H : ℕ)
    (w : ℕ → ℝ) (hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t) (hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1)
    (idx : Finset ι) (S : ι → Finset ℕ) (hcover : D ⊆ idx.biUnion S) :
    let p_w : ℕ → ℝ := fun d => ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t
    (∑ d ∈ D, (p_w d) ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3) ≤
      ∑ α ∈ idx,
        (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
          ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  intro p_w
  have hp_nn : ∀ d, 0 ≤ p_w d := fun d =>
    Finset.sum_nonneg fun t ht => hw_nn t (Finset.mem_filter.mp ht).1
  let a : ι → ℝ := fun α =>
    (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
      ((S α).card : ℝ) ^ ((1 : ℝ) / 3)
  have ha_nn : ∀ α ∈ idx, 0 ≤ a α := fun _ _ => by dsimp [a]; positivity
  have hsum_le_κ : ∀ α ∈ idx, ∑ d ∈ S α, p_w d ≤
      (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) := by
    intro α _
    have hswap : ∑ d ∈ S α, p_w d =
        ∑ t ∈ Finset.Icc 1 H, (((S α).filter (fun d => d ∣ t)).card : ℝ) * w t := by
      have h1 : ∀ d ∈ S α, p_w d = ∑ t ∈ Finset.Icc 1 H, if d ∣ t then w t else 0 := fun d _ => by
        dsimp [p_w]; rw [Finset.sum_filter]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hswap]
    set κ := (Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card)
    calc ∑ t ∈ Finset.Icc 1 H, (((S α).filter (fun d => d ∣ t)).card : ℝ) * w t
        ≤ ∑ t ∈ Finset.Icc 1 H, (κ : ℝ) * w t := by
          refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right ?_ (hw_nn t ht)
          exact_mod_cast Finset.le_sup (f := fun t => ((S α).filter (fun d => d ∣ t)).card) ht
      _ = (κ : ℝ) * ∑ t ∈ Finset.Icc 1 H, w t := by rw [← Finset.mul_sum]
      _ ≤ (κ : ℝ) * 1 := mul_le_mul_of_nonneg_left hw_sum (Nat.cast_nonneg _)
      _ = (κ : ℝ) := mul_one _
  have h32 : ∑ d ∈ D, (p_w d) ^ ((1 : ℝ) / 2) ≤ (∑ α ∈ idx, a α) ^ ((3 : ℝ) / 2) := by
    calc ∑ d ∈ D, (p_w d) ^ ((1 : ℝ) / 2)
        ≤ ∑ d ∈ idx.biUnion S, (p_w d) ^ ((1 : ℝ) / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ => Real.rpow_nonneg (hp_nn d) _
      _ ≤ ∑ α ∈ idx, ∑ d ∈ S α, (p_w d) ^ ((1 : ℝ) / 2) :=
          finset_sum_biUnion_le idx S (fun d => (p_w d) ^ ((1 : ℝ) / 2)) (fun d _ => Real.rpow_nonneg (hp_nn d) _)
      _ ≤ ∑ α ∈ idx, (a α) ^ ((3 : ℝ) / 2) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have h1 := sum_rpow_half_le (S α) p_w (fun d _ => hp_nn d)
          have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => hp_nn d) (hsum_le_κ α hα) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          have ha32 : (a α) ^ ((3 : ℝ) / 2) =
              (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                ((S α).card : ℝ) ^ ((1 : ℝ) / 2) := by
            dsimp [a]
            rw [Real.mul_rpow (by positivity) (by positivity),
              ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_mul (Nat.cast_nonneg _)]
            norm_num
          rw [ha32]
          exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ ≤ (∑ α ∈ idx, a α) ^ ((3 : ℝ) / 2) := sum_rpow_three_halves_le idx a ha_nn
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => Real.rpow_nonneg (hp_nn d) _) h32 (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul (Finset.sum_nonneg ha_nn)] at hpow
  norm_num at hpow
  exact hpow

/-- Abstract Partition-Elimination for Barrier 2c (`κ_bar` average over `U × U`):
`(∑ d ∈ D, q_U(d)^(1/2))^(2/3) ≤ ∑ α ∈ idx, κ_bar(S α, U)^(1/3) * |S α|^(1/3)`. -/
private lemma partition_lower_half_avg {ι : Type*} (D U : Finset ℕ)
    (idx : Finset ι) (S : ι → Finset ℕ) (hcover : D ⊆ idx.biUnion S) :
    let q_U : ℕ → ℝ := fun d =>
      (∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ ∧ d ∣ (if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂) then (1 : ℝ) else 0) /
        (U.card : ℝ) ^ 2
    (∑ d ∈ D, (q_U d) ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3) ≤
      ∑ α ∈ idx,
        ((∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
            (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
          else 0) / (U.card : ℝ) ^ 2) ^ ((1 : ℝ) / 3) *
          ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  intro q_U
  have hq_nn : ∀ d, 0 ≤ q_U d := fun d => by
    dsimp [q_U]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) (sq_nonneg _)
  have hsum_eq : ∀ α, ∑ d ∈ S α, q_U d =
      (∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
          (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
        else 0) / (U.card : ℝ) ^ 2 := by
    intro α
    dsimp [q_U]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z₂ _ => ?_
    by_cases hne : z₁ = z₂
    · simp [hne]
    · simp [hne]
  let a : ι → ℝ := fun α =>
    ((∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
        (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
      else 0) / (U.card : ℝ) ^ 2) ^ ((1 : ℝ) / 3) *
      ((S α).card : ℝ) ^ ((1 : ℝ) / 3)
  have hκ_nn : ∀ α, 0 ≤ (∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
        (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
      else 0) / (U.card : ℝ) ^ 2 := fun α =>
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) (sq_nonneg _)
  have ha_nn : ∀ α ∈ idx, 0 ≤ a α := fun α _ => mul_nonneg (Real.rpow_nonneg (hκ_nn α) _) (by positivity)
  have h32 : ∑ d ∈ D, (q_U d) ^ ((1 : ℝ) / 2) ≤ (∑ α ∈ idx, a α) ^ ((3 : ℝ) / 2) := by
    calc ∑ d ∈ D, (q_U d) ^ ((1 : ℝ) / 2)
        ≤ ∑ d ∈ idx.biUnion S, (q_U d) ^ ((1 : ℝ) / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ => Real.rpow_nonneg (hq_nn d) _
      _ ≤ ∑ α ∈ idx, ∑ d ∈ S α, (q_U d) ^ ((1 : ℝ) / 2) :=
          finset_sum_biUnion_le idx S (fun d => (q_U d) ^ ((1 : ℝ) / 2)) (fun d _ => Real.rpow_nonneg (hq_nn d) _)
      _ ≤ ∑ α ∈ idx, (a α) ^ ((3 : ℝ) / 2) := by
          refine Finset.sum_le_sum fun α _ => ?_
          have h1 := sum_rpow_half_le (S α) q_U (fun d _ => hq_nn d)
          rw [hsum_eq α] at h1
          have ha32 : (a α) ^ ((3 : ℝ) / 2) =
              ((∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
                  (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
                else 0) / (U.card : ℝ) ^ 2) ^ ((1 : ℝ) / 2) *
                ((S α).card : ℝ) ^ ((1 : ℝ) / 2) := by
            dsimp [a]
            rw [Real.mul_rpow (Real.rpow_nonneg (hκ_nn α) _) (by positivity),
              ← Real.rpow_mul (hκ_nn α), ← Real.rpow_mul (Nat.cast_nonneg _)]
            norm_num
          rwa [ha32]
      _ ≤ (∑ α ∈ idx, a α) ^ ((3 : ℝ) / 2) := sum_rpow_three_halves_le idx a ha_nn
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun d _ => Real.rpow_nonneg (hq_nn d) _) h32 (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul (Finset.sum_nonneg ha_nn)] at hpow
  norm_num at hpow
  exact hpow

/-! ### Section 2: Elementary Chebyshev Primorial Upper Bound & Dyadic Prime Lower Bound -/

private lemma nat_prod_dvd_of_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ) (n : ℕ)
    (hcop : (s : Set ι).Pairwise fun i j => Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ n) :
    ∏ i ∈ s, f i ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_s : (s : Set ι).Pairwise fun i j => Nat.Coprime (f i) (f j) :=
      hcop.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have h1 : f a ∣ n := hdvd a (Finset.mem_insert_self a s)
    have h2 : ∏ i ∈ s, f i ∣ n := ih hcop_s fun i hi => hdvd i (Finset.mem_insert_of_mem hi)
    have hca : Nat.Coprime (f a) (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    exact hca.mul_dvd_of_dvd_of_dvd h1 h2

/-- Erdős's 1932 elementary primorial bound: `∏_{p ≤ N} p ≤ 4 ^ N` for all `N : ℕ`. -/
private lemma prod_primes_le_four_pow (N : ℕ) :
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ≤ 4 ^ N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN2 : N ≤ 2
    · interval_cases N <;> decide
    · rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hN_not_prime : ¬ Nat.Prime N := by
          intro hp
          have h2dvd : 2 ∣ N := ⟨m, by omega⟩
          have h2eq : 2 = N := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd
          omega
        have hEq : (Finset.Icc 1 N).filter Nat.Prime = (Finset.Icc 1 (N - 1)).filter Nat.Prime := by
          ext p; simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨h1, h2⟩, hp⟩; refine ⟨⟨h1, ?_⟩, hp⟩
            by_contra hgt; have : p = N := by omega
            subst this; exact hN_not_prime hp
          · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨h1, by omega⟩, hp⟩
        rw [hEq]
        exact le_trans (ih (N - 1) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
      · have hm1 : 1 ≤ m := by omega
        let P1 := (Finset.Icc 1 (m + 1)).filter Nat.Prime
        let P2 := (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime
        have hdisj : Disjoint P1 P2 := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
          have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1
          omega
        have hunion : (Finset.Icc 1 N).filter Nat.Prime = P1 ∪ P2 := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, P1, P2]
          constructor
          · rintro ⟨⟨h1, h2⟩, hp⟩
            by_cases hle : p ≤ m + 1
            · exact Or.inl ⟨⟨h1, hle⟩, hp⟩
            · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
          · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
            · exact ⟨⟨h1, by omega⟩, hp⟩
            · exact ⟨⟨by omega, by omega⟩, hp⟩
        rw [hunion, Finset.prod_union hdisj]
        have hP1 : ∏ p ∈ P1, p ≤ 4 ^ (m + 1) := ih (m + 1) (by omega)
        have hdvd_each : ∀ p ∈ P2, p ∣ Nat.choose (2 * m + 1) m := by
          intro p hp
          have hp_Ioc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
          have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m + 1)
          rw [show 2 * m + 1 - m = m + 1 by omega] at hfac
          have hp_dvd_top : p ∣ (2 * m + 1).factorial := (Nat.Prime.dvd_factorial hp_prime).mpr hp_Ioc.2
          rw [← hfac] at hp_dvd_top
          have hp_not_m1 : ¬ p ∣ (m + 1).factorial := by rw [Nat.Prime.dvd_factorial hp_prime]; omega
          have hp_not_m : ¬ p ∣ m.factorial := by rw [Nat.Prime.dvd_factorial hp_prime]; omega
          rcases hp_prime.dvd_mul.mp hp_dvd_top with h1 | h2
          · rcases hp_prime.dvd_mul.mp h1 with h11 | h12
            · exact h11
            · exact (hp_not_m h12).elim
          · exact (hp_not_m1 h2).elim
        have hcop : (P2 : Set ℕ).Pairwise (fun p q => Nat.Coprime p q) := fun p hp q hq hpq =>
          (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
        have hP2_le_ch : ∏ p ∈ P2, p ≤ Nat.choose (2 * m + 1) m :=
          Nat.le_of_dvd (Nat.choose_pos (by omega)) (nat_prod_dvd_of_coprime P2 id _ hcop hdvd_each)
        have hch_le : Nat.choose (2 * m + 1) m ≤ 4 ^ m := by
          have hsum := Nat.sum_range_choose (2 * m + 1)
          have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
            simpa [show 2 * m + 1 - m = m + 1 by omega] using Nat.choose_symm (by omega : m ≤ 2 * m + 1)
          have hpair : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (2 * m + 2) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
          have hle_sum : Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) ≤
              ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k := by
            simpa [Finset.sum_pair (by omega : m ≠ m + 1)] using
              Finset.sum_le_sum_of_subset (f := fun k => Nat.choose (2 * m + 1) k) hpair
          rw [hsum, hsymm] at hle_sum
          have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; norm_num; ring
          omega
        calc (∏ p ∈ P1, p) * (∏ p ∈ P2, p)
            ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul hP1 (le_trans hP2_le_ch hch_le)
          _ = 4 ^ (2 * m + 1) := by rw [← pow_add]; congr 1; omega
          _ = 4 ^ N := by rw [hm]

/-- Dyadic prime reciprocal sum upper bound: for `r ≥ 1`, `∑_{2^r < p ≤ 2^(r+1)} 1/p ≤ 4 / r`. -/
private lemma sum_inv_primes_dyadic_le (r : ℕ) (hr : 1 ≤ r) :
    ∑ p ∈ (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 4 / (r : ℝ) := by
  let S := (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hsub : S ⊆ (Finset.Icc 1 (2 ^ (r + 1))).filter Nat.Prime := fun p hp => by
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, (Finset.mem_filter.mp hp).2⟩
  have hpow_le : 2 ^ (r * S.card) ≤ 2 ^ (4 * 2 ^ r) := by
    calc 2 ^ (r * S.card) = (2 ^ r) ^ S.card := by rw [pow_mul]
      _ = ∏ _p ∈ S, 2 ^ r := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' fun p hp => le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      _ ≤ ∏ p ∈ (Finset.Icc 1 (2 ^ (r + 1))).filter Nat.Prime, p :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ => (Finset.mem_filter.mp hp).2.one_le
      _ ≤ 4 ^ (2 ^ (r + 1)) := prod_primes_le_four_pow (2 ^ (r + 1))
      _ = 2 ^ (4 * 2 ^ r) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]; congr 1; ring
  have hcard : r * S.card ≤ 4 * 2 ^ r := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h2r_pos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
  have hcard_r : (r : ℝ) * (S.card : ℝ) ≤ 4 * ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hcard
  calc ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _p ∈ S, (1 : ℝ) / ((2 ^ r : ℕ) : ℝ) := Finset.sum_le_sum fun p hp =>
        one_div_le_one_div_of_le h2r_pos (by exact_mod_cast le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1)
    _ = (S.card : ℝ) / ((2 ^ r : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ 4 / (r : ℝ) := by rw [div_le_div_iff₀ h2r_pos hr_pos]; linarith

/-- Elementary Legendre formula for `n!.factorization p`. -/
private lemma factorization_factorial_eq (p E n : ℕ) (hp : p.Prime) (hn : n < p ^ (E + 1)) :
    n.factorial.factorization p = ∑ k ∈ Finset.Icc 1 E, n / p ^ k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hm_lt : m < p ^ (E + 1) := by omega
    rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero m),
      Finsupp.add_apply, ih hm_lt]
    have hdiff : ∀ k ∈ Finset.Icc 1 E, (m + 1) / p ^ k = m / p ^ k + (if p ^ k ∣ m + 1 then 1 else 0) := by
      intro k _
      have hd : 0 < p ^ k := pow_pos hp.pos k
      have hmod := Nat.div_add_mod m (p ^ k)
      have hlt := Nat.mod_lt m hd
      split_ifs with hdvd
      · rcases hdvd with ⟨q, hq⟩
        have hq_pos : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with rfl | h
          · simp at hq
          · exact h
        have hm_eq : m = p ^ k * (q - 1) + (p ^ k - 1) := by
          have : p ^ k * (q - 1) + p ^ k = p ^ k * q := by
            calc p ^ k * (q - 1) + p ^ k = p ^ k * (q - 1 + 1) := by ring
              _ = p ^ k * q := by rw [Nat.sub_add_cancel hq_pos]
          omega
        have hdiv1 : (m + 1) / p ^ k = q := by rw [hq, Nat.mul_div_cancel_left q hd]
        have hdiv2 : m / p ^ k = q - 1 := by
          rw [hm_eq, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega : p ^ k - 1 < p ^ k), add_zero]
        omega
      · have hne : m % p ^ k + 1 < p ^ k := by
          by_contra hge; push Not at hge
          have : m % p ^ k + 1 = p ^ k := by omega
          exact hdvd ⟨m / p ^ k + 1, by linarith⟩
        have hm1 : m + 1 = p ^ k * (m / p ^ k) + (m % p ^ k + 1) := by omega
        rw [hm1, Nat.mul_add_div hd, Nat.div_eq_of_lt hne, add_zero]
    rw [Finset.sum_congr rfl hdiff, Finset.sum_add_distrib, add_comm]
    congr 1
    rw [← Finset.card_filter]
    have hfac_le : (m + 1).factorization p ≤ E := by
      have hpow : p ^ ((m + 1).factorization p) ≤ m + 1 := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (m + 1) p)
      have hlt : p ^ ((m + 1).factorization p) < p ^ (E + 1) := lt_of_le_of_lt hpow hn
      have : (m + 1).factorization p < E + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
      omega
    have hEq : (Finset.Icc 1 E).filter (fun k => p ^ k ∣ m + 1) = Finset.Icc 1 ((m + 1).factorization p) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc, hp.pow_dvd_iff_le_factorization (by omega : m + 1 ≠ 0)]
      omega
    rw [hEq]; simp

/-- Prime-power bound in central binomial coefficient: `p ^ (v_p(choose (2m) m)) ≤ 2 * m`,
and `v_p(choose (2m) m) = 0` for `2 * m / 3 < p ≤ m` (`m ≥ 5`). -/
private lemma central_choose_factorization_bounds (m p : ℕ) (hm : 5 ≤ m) (hp : p.Prime) :
    p ^ ((Nat.choose (2 * m) m).factorization p) ≤ 2 * m ∧
    (2 * m / 3 < p → p ≤ m → (Nat.choose (2 * m) m).factorization p = 0) := by
  let E := Nat.log p (2 * m)
  have h2m_lt : 2 * m < p ^ (E + 1) := Nat.lt_pow_succ_log_self hp.one_lt (2 * m)
  have hm_lt : m < p ^ (E + 1) := by omega
  have hfac_id := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
  rw [show 2 * m - m = m by omega] at hfac_id
  have hch_ne : Nat.choose (2 * m) m ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hm_ne : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hv_eq : (Nat.choose (2 * m) m).factorization p + 2 * (m.factorial.factorization p) =
      (2 * m).factorial.factorization p := by
    have h := congrArg (fun x => x.factorization p) hfac_id
    rw [Nat.factorization_mul (Nat.mul_ne_zero hch_ne hm_ne) hm_ne,
      Nat.factorization_mul hch_ne hm_ne] at h
    simp only [Finsupp.add_apply] at h
    omega
  rw [factorization_factorial_eq p E (2 * m) hp h2m_lt,
    factorization_factorial_eq p E m hp hm_lt] at hv_eq
  have hterm : ∀ k ∈ Finset.Icc 1 E, 2 * (m / p ^ k) ≤ (2 * m) / p ^ k ∧ (2 * m) / p ^ k ≤ 2 * (m / p ^ k) + 1 := by
    intro k _
    have hd : 0 < p ^ k := pow_pos hp.pos k
    have hmod := Nat.div_add_mod m (p ^ k)
    have hlt := Nat.mod_lt m hd
    have hmod2 := Nat.div_add_mod (2 * m) (p ^ k)
    have hlt2 := Nat.mod_lt (2 * m) hd
    have h2m : 2 * m = 2 * (p ^ k * (m / p ^ k)) + 2 * (m % p ^ k) := by omega
    constructor
    · by_contra hgt; push Not at hgt
      have h1 : p ^ k * ((2 * m) / p ^ k + 1) ≤ p ^ k * (2 * (m / p ^ k)) := Nat.mul_le_mul_left _ (by omega)
      have h2 : p ^ k * ((2 * m) / p ^ k + 1) = p ^ k * ((2 * m) / p ^ k) + p ^ k := by ring
      have h3 : p ^ k * (2 * (m / p ^ k)) = 2 * (p ^ k * (m / p ^ k)) := by ring
      omega
    · by_contra hgt; push Not at hgt
      have h1 : p ^ k * (2 * (m / p ^ k) + 2) ≤ p ^ k * ((2 * m) / p ^ k) := Nat.mul_le_mul_left _ (by omega)
      have h2 : p ^ k * (2 * (m / p ^ k) + 2) = 2 * (p ^ k * (m / p ^ k)) + 2 * p ^ k := by ring
      have hle_mul : 2 * (p ^ k * (m / p ^ k)) + 2 * p ^ k ≤ 2 * m := by
        calc 2 * (p ^ k * (m / p ^ k)) + 2 * p ^ k
            = p ^ k * (2 * (m / p ^ k) + 2) := h2.symm
          _ ≤ p ^ k * ((2 * m) / p ^ k) := h1
          _ ≤ p ^ k * ((2 * m) / p ^ k) + (2 * m) % p ^ k := Nat.le_add_right _ _
          _ = 2 * m := hmod2
      omega
  have hv_le_E : (Nat.choose (2 * m) m).factorization p ≤ E := by
    have hsum_le : ∑ k ∈ Finset.Icc 1 E, (2 * m) / p ^ k ≤
        2 * (∑ k ∈ Finset.Icc 1 E, m / p ^ k) + E := by
      have h1 : ∑ k ∈ Finset.Icc 1 E, (2 * m) / p ^ k ≤ ∑ k ∈ Finset.Icc 1 E, (2 * (m / p ^ k) + 1) :=
        Finset.sum_le_sum fun k hk => (hterm k hk).2
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc] at h1
      simpa using h1
    omega
  constructor
  · exact le_trans (Nat.pow_le_pow_right hp.pos hv_le_E) (Nat.pow_log_le_self p (by omega))
  · intro hp_lo hp_hi
    have h2m_lt_p2 : 2 * m < p ^ 2 := by
      have h3p : 2 * m < 3 * p := by omega
      have hp3 : 3 ≤ p := by omega
      have : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp3
      rw [sq]; omega
    have hE_eq : E = 1 := by
      have h1 : 1 ≤ E := Nat.le_log_of_pow_le hp.one_lt (by rw [pow_one]; omega)
      have h2 : E < 2 := by
        by_contra hge; push Not at hge
        have : p ^ 2 ≤ p ^ E := Nat.pow_le_pow_right hp.pos hge
        have : p ^ E ≤ 2 * m := Nat.pow_log_le_self p (by omega)
        omega
      omega
    rw [hE_eq] at hv_eq
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one] at hv_eq
    have hdiv1 : m / p = 1 := by
      have hmod := Nat.div_add_mod m p; have hlt := Nat.mod_lt m hp.pos
      have h2p : m < 2 * p := by omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with h0 | h2
      · have : m / p = 0 := by omega
        rw [this, mul_zero, zero_add] at hmod; omega
      · have : 2 * p ≤ p * (m / p) := by nlinarith
        omega
    have hdiv2 : (2 * m) / p = 2 := by
      have hmod := Nat.div_add_mod (2 * m) p; have hlt := Nat.mod_lt (2 * m) hp.pos
      have h3p : 2 * m < 3 * p := by omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt2 | hgt2
      · have : p * ((2 * m) / p) ≤ p * 1 := Nat.mul_le_mul_left p (by omega)
        omega
      · have : 3 * p ≤ p * ((2 * m) / p) := by nlinarith
        omega
    rw [hdiv1, hdiv2] at hv_eq
    omega

/-- Elementary Chebyshev dyadic prime lower bound: for `m ≥ 10^9`,
`#{p ∈ (m, 2*m] | p.Prime} ≥ m / (4 * log (2 * m))`. -/
private lemma prime_dyadic_card_lower (m : ℕ) (hm : 10 ^ 9 ≤ m) :
    (m : ℝ) / (4 * Real.log (2 * (m : ℝ))) ≤
      (((Finset.Ioc m (2 * m)).filter Nat.Prime).card : ℝ) := by
  let P_all := (Finset.Icc 1 (2 * m)).filter Nat.Prime
  let P_sq := (Finset.Icc 1 (Nat.sqrt (2 * m))).filter Nat.Prime
  let P_mid := (Finset.Ioc (Nat.sqrt (2 * m)) (2 * m / 3)).filter Nat.Prime
  let P_hi := (Finset.Ioc m (2 * m)).filter Nat.Prime
  have hch_pos : 0 < Nat.choose (2 * m) m := Nat.choose_pos (by omega)
  have hch_prod : Nat.choose (2 * m) m = ∏ p ∈ P_all, p ^ ((Nat.choose (2 * m) m).factorization p) := by
    have hsub : (Nat.choose (2 * m) m).primeFactors ⊆ P_all := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      have hp_le : p ≤ 2 * m := by
        have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
        have htop : p ∣ (2 * m).factorial := dvd_trans hdvd ⟨m.factorial * (2 * m - m).factorial, by linarith⟩
        exact (Nat.Prime.dvd_factorial hpr).mp htop
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.one_le, hp_le⟩, hpr⟩
    have h1 : ∏ p ∈ P_all, p ^ ((Nat.choose (2 * m) m).factorization p) =
        ∏ p ∈ (Nat.choose (2 * m) m).primeFactors, p ^ ((Nat.choose (2 * m) m).factorization p) := by
      symm; refine Finset.prod_subset hsub fun p _ hp_not => ?_
      rw [Finsupp.notMem_support_iff.mp hp_not, pow_zero]
    rw [h1]; exact (Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hch_pos)).symm
  -- Split P_all into P_sq, P_mid, (2m/3, m] (exponent 0), and P_hi
  have hsub_union : (Nat.choose (2 * m) m).primeFactors ⊆ P_sq ∪ P_mid ∪ P_hi := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hp_le : p ≤ 2 * m := by
      have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
      have htop : p ∣ (2 * m).factorial := dvd_trans hdvd ⟨m.factorial * (2 * m - m).factorial, by linarith⟩
      exact (Nat.Prime.dvd_factorial hpr).mp htop
    by_cases h1 : p ≤ Nat.sqrt (2 * m)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.one_le, h1⟩, hpr⟩))
    · by_cases h2 : p ≤ 2 * m / 3
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h2⟩, hpr⟩))
      · by_cases h3 : p ≤ m
        · exfalso
          have hv0 := (central_choose_factorization_bounds m p (by omega) hpr).2 (by omega) h3
          exact Finsupp.mem_support_iff.mp hp hv0
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hp_le⟩, hpr⟩)
  have hch_le : Nat.choose (2 * m) m ≤
      (2 * m) ^ (Nat.sqrt (2 * m)) * 4 ^ (2 * m / 3) * (2 * m) ^ P_hi.card := by
    have hdisj1 : Disjoint P_sq P_mid := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1; omega
    have hdisj2 : Disjoint (P_sq ∪ P_mid) P_hi := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      have hhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1
      rcases Finset.mem_union.mp hp1 with ha | hb
      · have hle := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
        have hsq : Nat.sqrt (2 * m) * Nat.sqrt (2 * m) ≤ 2 * m := Nat.sqrt_le (2 * m)
        nlinarith
      · have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).2; omega
    have hprod_eq : Nat.choose (2 * m) m =
        (∏ p ∈ P_sq, p ^ ((Nat.choose (2 * m) m).factorization p)) *
        (∏ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p)) *
        (∏ p ∈ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p)) := by
      rw [← Finset.prod_union hdisj1, ← Finset.prod_union hdisj2]
      symm
      calc ∏ p ∈ P_sq ∪ P_mid ∪ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p)
          = ∏ p ∈ (Nat.choose (2 * m) m).primeFactors, p ^ ((Nat.choose (2 * m) m).factorization p) := by
            symm; refine Finset.prod_subset hsub_union fun p _ hp_not => ?_
            rw [Finsupp.notMem_support_iff.mp hp_not, pow_zero]
        _ = Nat.choose (2 * m) m := Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hch_pos)
    rw [hprod_eq]
    have hB1 : ∏ p ∈ P_sq, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ (2 * m) ^ (Nat.sqrt (2 * m)) := by
      calc ∏ p ∈ P_sq, p ^ ((Nat.choose (2 * m) m).factorization p)
          ≤ ∏ _p ∈ P_sq, (2 * m) := Finset.prod_le_prod' fun p hp =>
            (central_choose_factorization_bounds m p (by omega) (Finset.mem_filter.mp hp).2).1
        _ = (2 * m) ^ P_sq.card := by simp
        _ ≤ (2 * m) ^ (Nat.sqrt (2 * m)) := Nat.pow_le_pow_right (by omega) (by
            calc P_sq.card ≤ (Finset.Icc 1 (Nat.sqrt (2 * m))).card := Finset.card_filter_le _ _
              _ = Nat.sqrt (2 * m) := by simp)
    have hB2 : ∏ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ 4 ^ (2 * m / 3) := by
      have hpt : ∀ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ p := by
        intro p hp
        have hpr := (Finset.mem_filter.mp hp).2
        have hp_gt : Nat.sqrt (2 * m) < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        have hp2 : 2 * m < p ^ 2 := by
          have := Nat.lt_succ_sqrt (2 * m)
          rw [sq]; nlinarith
        have hle := (central_choose_factorization_bounds m p (by omega) hpr).1
        have hv1 : (Nat.choose (2 * m) m).factorization p ≤ 1 := by
          by_contra hgt; push Not at hgt
          have : p ^ 2 ≤ p ^ ((Nat.choose (2 * m) m).factorization p) := Nat.pow_le_pow_right hpr.pos hgt
          omega
        calc p ^ ((Nat.choose (2 * m) m).factorization p) ≤ p ^ 1 := Nat.pow_le_pow_right hpr.pos hv1
          _ = p := pow_one p
      have hsub2 : P_mid ⊆ (Finset.Icc 1 (2 * m / 3)).filter Nat.Prime := fun p hp =>
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_le,
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩, (Finset.mem_filter.mp hp).2⟩
      calc ∏ p ∈ P_mid, p ^ ((Nat.choose (2 * m) m).factorization p)
          ≤ ∏ p ∈ P_mid, p := Finset.prod_le_prod' hpt
        _ ≤ ∏ p ∈ (Finset.Icc 1 (2 * m / 3)).filter Nat.Prime, p :=
            Finset.prod_le_prod_of_subset_of_one_le' hsub2 fun p hp _ => (Finset.mem_filter.mp hp).2.one_le
        _ ≤ 4 ^ (2 * m / 3) := prod_primes_le_four_pow (2 * m / 3)
    have hB3 : ∏ p ∈ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p) ≤ (2 * m) ^ P_hi.card := by
      calc ∏ p ∈ P_hi, p ^ ((Nat.choose (2 * m) m).factorization p)
          ≤ ∏ _p ∈ P_hi, (2 * m) := Finset.prod_le_prod' fun p hp =>
            (central_choose_factorization_bounds m p (by omega) (Finset.mem_filter.mp hp).2).1
        _ = (2 * m) ^ P_hi.card := by simp
    exact Nat.mul_le_mul (Nat.mul_le_mul hB1 hB2) hB3
  -- Combine with 4 ^ m ≤ (2 * m + 1) * Nat.choose (2 * m) m
  have h4m_le : 4 ^ m ≤ (2 * m + 1) * Nat.choose (2 * m) m := by
    have hsum := Nat.sum_range_choose (2 * m)
    have h4 : 4 ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    rw [h4, ← hsum]
    calc ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k
        ≤ ∑ _k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) m :=
          Finset.sum_le_sum fun k _ => by simpa [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using Nat.choose_le_middle k (2 * m)
      _ = (2 * m + 1) * Nat.choose (2 * m) m := by simp
  have hcomb : 4 ^ m ≤ (2 * m + 1) * ((2 * m) ^ (Nat.sqrt (2 * m)) * 4 ^ (2 * m / 3) * (2 * m) ^ P_hi.card) :=
    le_trans h4m_le (Nat.mul_le_mul_left _ hch_le)
  -- Take logs in ℝ
  have hm_ge_r : (10 ^ 9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hlog2m_pos : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by linarith)
  have hcomb_r : (4 : ℝ) ^ m ≤ ((2 * (m : ℝ) + 1) * ((2 * (m : ℝ)) ^ (Nat.sqrt (2 * m)) *
      (4 : ℝ) ^ (2 * m / 3) * (2 * (m : ℝ)) ^ P_hi.card)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcomb
    push_cast at this; exact this
  have hlg := Real.log_le_log (pow_pos (by norm_num) m) hcomb_r
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlg
  have hlog4_ge1 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith [half_le_log_two]
  have h2m3_le : ((2 * m / 3 : ℕ) : ℝ) ≤ (2 : ℝ) / 3 * (m : ℝ) := by
    have : 3 * (2 * m / 3) ≤ 2 * m := Nat.mul_div_le (2 * m) 3
    have : (3 : ℝ) * ((2 * m / 3 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast this
    linarith
  have hlog2m1 : Real.log (2 * (m : ℝ) + 1) ≤ 2 * Real.log (2 * (m : ℝ)) := by
    have h1 : 2 * (m : ℝ) + 1 ≤ (2 * (m : ℝ)) ^ (2 : ℕ) := by nlinarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at this; push_cast at this; exact this
  -- Bound (√(2m) + 2) * log (2m) ≤ m / 12 for m ≥ 10^9 using log(2m) ≤ 4 * (2m)^(1/4)
  have hsqrt_le : ((Nat.sqrt (2 * m) : ℝ) + 2) * Real.log (2 * (m : ℝ)) ≤ (m : ℝ) / 12 := by
    have hlog_rpow : Real.log (2 * (m : ℝ)) ≤ 4 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 4) := by
      have h1 : Real.log ((2 * (m : ℝ)) ^ ((1 : ℝ) / 4)) ≤ (2 * (m : ℝ)) ^ ((1 : ℝ) / 4) := by
        linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h2m_pos ((1 : ℝ) / 4))]
      rw [Real.log_rpow h2m_pos] at h1; linarith
    have hsq_le : (Nat.sqrt (2 * m) : ℝ) + 2 ≤ 2 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
      have hsq : (Nat.sqrt (2 * m) : ℝ) ≤ (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (Nat.cast_nonneg _) (le_of_lt h2m_pos)]
        have : Nat.sqrt (2 * m) * Nat.sqrt (2 * m) ≤ 2 * m := Nat.sqrt_le (2 * m)
        have : (Nat.sqrt (2 * m) : ℝ) * (Nat.sqrt (2 * m) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast this
        nlinarith
      have h2_le : (2 : ℝ) ≤ (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (le_of_lt h2m_pos)]
        have : (10 ^ 9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      linarith
    have hprod_rpow : (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) * (2 * (m : ℝ)) ^ ((1 : ℝ) / 4) =
        (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add h2m_pos]; norm_num
    have h34_le : 8 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) / 12 := by
      have hpow4 : (96 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) ≤ (m : ℝ) ^ (4 : ℕ) := by
        rw [mul_pow, ← Real.rpow_natCast ((2 * (m : ℝ)) ^ ((3 : ℝ) / 4)) 4,
          ← Real.rpow_mul (le_of_lt h2m_pos)]
        have h3 : ((3 : ℝ) / 4) * ((4 : ℕ) : ℝ) = (3 : ℝ) := by push_cast; norm_num
        rw [h3, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hm_r : (10 ^ 9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have h96 : (96 : ℝ) ^ 4 * 8 ≤ (m : ℝ) := by linarith
        have hm3_nn : 0 ≤ (m : ℝ) ^ 3 := by positivity
        calc (96 : ℝ) ^ 4 * (2 * (m : ℝ)) ^ 3
            = ((96 : ℝ) ^ 4 * 8) * (m : ℝ) ^ 3 := by ring
          _ ≤ (m : ℝ) * (m : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h96 hm3_nn
          _ = (m : ℝ) ^ 4 := by ring
      have h96_le : 96 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) := by
        by_contra hgt; push Not at hgt
        have : (m : ℝ) ^ (4 : ℕ) < (96 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) :=
          pow_lt_pow_left₀ hgt (le_of_lt hm_pos) (by norm_num)
        linarith
      linarith
    calc ((Nat.sqrt (2 * m) : ℝ) + 2) * Real.log (2 * (m : ℝ))
        ≤ (2 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 2)) * (4 * (2 * (m : ℝ)) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul hsq_le hlog_rpow (le_of_lt hlog2m_pos) (by positivity)
      _ = 8 * (2 * (m : ℝ)) ^ ((3 : ℝ) / 4) := by rw [← hprod_rpow]; ring
      _ ≤ (m : ℝ) / 12 := h34_le
  have h1 : (m : ℝ) / 4 ≤ (P_hi.card : ℝ) * Real.log (2 * (m : ℝ)) := by
    have hdiff : (m : ℝ) / 3 * Real.log 4 ≤ (m : ℝ) * Real.log 4 - ((2 * m / 3 : ℕ) : ℝ) * Real.log 4 := by
      have : 0 ≤ Real.log 4 := by linarith
      nlinarith
    have hthird : (m : ℝ) / 3 ≤ (m : ℝ) / 3 * Real.log 4 := by nlinarith
    nlinarith
  exact (div_le_iff₀ (by positivity)).mpr (by linarith)

/-- Dyadic prime lower bound on `(N / (2 * d), N / d]` for `2 * 10^9 ≤ N / d`. -/
private lemma prime_dyadic_div_lower (N d : ℕ) (hd : 1 ≤ d) (hbig : 2 * 10 ^ 9 ≤ N / d) :
    (N : ℝ) / (16 * (d : ℝ) * Real.log (N : ℝ)) ≤
      (((Finset.Ioc (N / (2 * d)) (N / d)).filter Nat.Prime).card : ℝ) := by
  let m := N / (2 * d)
  have hm_ge : 10 ^ 9 ≤ m := by
    have hdiv : N / (2 * d) = (N / d) / 2 := by rw [mul_comm, ← Nat.div_div_eq_div_mul]
    omega
  have h2m_le : 2 * m ≤ N / d := by
    have hdiv : N / (2 * d) = (N / d) / 2 := by rw [mul_comm, ← Nat.div_div_eq_div_mul]
    have := Nat.mul_div_le (N / d) 2
    omega
  have hsub : (Finset.Ioc m (2 * m)).filter Nat.Prime ⊆ (Finset.Ioc (N / (2 * d)) (N / d)).filter Nat.Prime := by
    intro p hp
    have hI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hI.1, le_trans hI.2 h2m_le⟩, (Finset.mem_filter.mp hp).2⟩
  have hcard : (((Finset.Ioc m (2 * m)).filter Nat.Prime).card : ℝ) ≤
      (((Finset.Ioc (N / (2 * d)) (N / d)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcheb := prime_dyadic_card_lower m hm_ge
  have hN_ge : 2 * 10 ^ 9 ≤ N := le_trans hbig (Nat.div_le_self N d)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have h2m_le_N : 2 * (m : ℝ) ≤ (N : ℝ) := by
    have : 2 * m ≤ N := le_trans h2m_le (Nat.div_le_self N d)
    exact_mod_cast this
  have hlog_le : Real.log (2 * (m : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * m)) h2m_le_N
  have hm_lb : (N : ℝ) / (4 * (d : ℝ)) ≤ (m : ℝ) := by
    have hmod := Nat.div_add_mod N (2 * d)
    have hlt := Nat.mod_lt N (by omega : 0 < 2 * d)
    have h2 : N < 2 * d * (m + 1) := by dsimp [m]; nlinarith
    have h3 : N ≤ 4 * d * m := by
      have : m + 1 ≤ 2 * m := by omega
      nlinarith
    have h4 : (N : ℝ) ≤ (m : ℝ) * (4 * (d : ℝ)) := by
      have := (Nat.cast_le (α := ℝ)).mpr h3
      push_cast at this; linarith
    exact (div_le_iff₀ (by positivity)).mpr h4
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog2m_pos : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * m))
  calc (N : ℝ) / (16 * (d : ℝ) * Real.log (N : ℝ))
      = ((N : ℝ) / (4 * (d : ℝ))) / (4 * Real.log (N : ℝ)) := by ring
    _ ≤ (m : ℝ) / (4 * Real.log (2 * (m : ℝ))) :=
        div_le_div₀ (by positivity) hm_lb (by positivity) (by linarith)
    _ ≤ (((Finset.Ioc m (2 * m)).filter Nat.Prime).card : ℝ) := hcheb
    _ ≤ (((Finset.Ioc (N / (2 * d)) (N / d)).filter Nat.Prime).card : ℝ) := hcard

/-! ### Section 3: Super-Dyadic Prime Window `P_win J = {p ∈ (2^J, 2^(2J)] | p.Prime}` -/

private def P_win (J : ℕ) : Finset ℕ := (Finset.Ioc (2 ^ J) (2 ^ (2 * J))).filter Nat.Prime

/-- Exact upper & lower bounds on `∑_{p ∈ P_win J} 1 / p` for `J ≥ 30`:
`1 / 16 ≤ ∑ p ∈ P_win J, 1 / p ≤ 4`. -/
private lemma sum_inv_primes_win_bounds (J : ℕ) (hJ : 30 ≤ J) :
    (1 : ℝ) / 16 ≤ ∑ p ∈ P_win J, (1 : ℝ) / (p : ℝ) ∧
    ∑ p ∈ P_win J, (1 : ℝ) / (p : ℝ) ≤ 4 := by
  let I := Finset.Ico J (2 * J)
  let F : ℕ → Finset ℕ := fun r => (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) F := by
    intro r₁ _ r₂ _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p hp1 hp2
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1
    have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (r₁ + 1) ≤ 2 ^ r₂ := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (r₂ + 1) ≤ 2 ^ r₁ := Nat.pow_le_pow_right (by norm_num) hgt
      omega
  have hEq : P_win J = I.biUnion F := by
    ext p
    simp only [P_win, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_biUnion, I, F, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      let r := Nat.log 2 (p - 1)
      have hp_ge2 : 2 ≤ p := hp.two_le
      have hr_le : 2 ^ r ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
      have hr_lt : p - 1 < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
      have hr_ge : J ≤ r := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hr_ub : r < 2 * J := by
        by_contra hge; push Not at hge
        have : 2 ^ (2 * J) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hge
        omega
      exact ⟨r, ⟨hr_ge, hr_ub⟩, ⟨by omega, by omega⟩, hp⟩
    · rintro ⟨r, ⟨hr1, hr2⟩, ⟨h1, h2⟩, hp⟩
      have hlo : 2 ^ J ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
      have hhi : 2 ^ (r + 1) ≤ 2 ^ (2 * J) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact ⟨⟨by omega, by omega⟩, hp⟩
  rw [hEq, Finset.sum_biUnion hdisj]
  have hJ_pos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
  have hIcard : I.card = J := by dsimp [I]; rw [Nat.card_Ico]; omega
  constructor
  · -- Lower bound: each r ∈ [J, 2J) contributes ≥ 1 / (8 * (r + 1)) ≥ 1 / (16 * J)
    have hper : ∀ r ∈ I, (1 : ℝ) / (16 * (J : ℝ)) ≤ ∑ p ∈ F r, (1 : ℝ) / (p : ℝ) := by
      intro r hr
      have hr_ge : J ≤ r := (Finset.mem_Ico.mp hr).1
      have hr_lt : r < 2 * J := (Finset.mem_Ico.mp hr).2
      have h2r_ge : 10 ^ 9 ≤ 2 ^ r := by
        calc 10 ^ 9 ≤ 2 ^ 30 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcheb := prime_dyadic_card_lower (2 ^ r) h2r_ge
      have hFr_eq : F r = (Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime := by
        dsimp [F]; rw [pow_succ, mul_comm]
      rw [hFr_eq]
      have h2r1_pos : (0 : ℝ) < (2 * ((2 ^ r : ℕ) : ℝ)) := by positivity
      have hlog_le : Real.log (2 * ((2 ^ r : ℕ) : ℝ)) ≤ ((r + 1 : ℕ) : ℝ) := by
        have heq : 2 * ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ (r + 1) := by push_cast; rw [pow_succ]; ring
        rw [heq, Real.log_pow]
        have h1 := log_two_le_one
        nlinarith [Nat.cast_nonneg (α := ℝ) (r + 1)]
      have hlog_pos : 0 < Real.log (2 * ((2 ^ r : ℕ) : ℝ)) := Real.log_pos (by
        have : (1 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 ^ r)
        linarith)
      have hr1_le : ((r + 1 : ℕ) : ℝ) ≤ 2 * (J : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ 2 * J)
      calc (1 : ℝ) / (16 * (J : ℝ))
          ≤ (((2 ^ r : ℕ) : ℝ) / (4 * Real.log (2 * ((2 ^ r : ℕ) : ℝ)))) / (2 * ((2 ^ r : ℕ) : ℝ)) := by
            have h1 : (((2 ^ r : ℕ) : ℝ) / (4 * Real.log (2 * ((2 ^ r : ℕ) : ℝ)))) / (2 * ((2 ^ r : ℕ) : ℝ)) =
                1 / (8 * Real.log (2 * ((2 ^ r : ℕ) : ℝ))) := by
              have h2r_ne : ((2 ^ r : ℕ) : ℝ) ≠ 0 := by positivity
              field_simp [h2r_ne, ne_of_gt hlog_pos]; ring
            rw [h1]
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
        _ ≤ (((Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime).card : ℝ) / (2 * ((2 ^ r : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right hcheb (le_of_lt h2r1_pos)
        _ = ∑ _p ∈ (Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime, (1 : ℝ) / (2 * ((2 ^ r : ℕ) : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ ∑ p ∈ (Finset.Ioc (2 ^ r) (2 * 2 ^ r)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le
              (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
              (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)
    calc (1 : ℝ) / 16 = (I.card : ℝ) * ((1 : ℝ) / (16 * (J : ℝ))) := by
          rw [hIcard]; field_simp [ne_of_gt hJ_pos]
      _ = ∑ _r ∈ I, (1 : ℝ) / (16 * (J : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ I, ∑ p ∈ F r, (1 : ℝ) / (p : ℝ) := Finset.sum_le_sum hper
  · -- Upper bound: each r ∈ [J, 2J) contributes ≤ 4 / r ≤ 4 / J
    calc ∑ r ∈ I, ∑ p ∈ F r, (1 : ℝ) / (p : ℝ)
        ≤ ∑ r ∈ I, (4 : ℝ) / (r : ℝ) :=
          Finset.sum_le_sum fun r hr => sum_inv_primes_dyadic_le r (by have := (Finset.mem_Ico.mp hr).1; omega)
      _ ≤ ∑ _r ∈ I, (4 : ℝ) / (J : ℝ) := Finset.sum_le_sum fun r hr =>
          div_le_div_of_nonneg_left (by norm_num) hJ_pos (by exact_mod_cast (Finset.mem_Ico.mp hr).1)
      _ = (I.card : ℝ) * ((4 : ℝ) / (J : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 4 := by rw [hIcard]; field_simp [ne_of_gt hJ_pos]

/-! ### Section 4: `Finset.powerset` Product Measure, Markov Truncation, and Barrier Theorems 1 & 2a -/

/-- Exact product-measure normalization on `P.powerset`:
`∑ S ∈ P.powerset, (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p)) = 1`. -/
private lemma powerset_prod_bernoulli_sum_eq_one (P : Finset ℕ) (q : ℕ → ℝ) :
    ∑ S ∈ P.powerset, (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p)) = 1 := by
  classical
  have h := Finset.prod_add (s := P) (f := fun p => q p) (g := fun p => 1 - q p)
  have h1 : ∏ p ∈ P, (q p + (1 - q p)) = 1 := Finset.prod_eq_one fun p _ => by ring
  rw [h1] at h
  exact h.symm

/-- Exact subset-conditioning identity on `P.powerset`: for `S₀ ⊆ P`,
`∑ S ∈ P.powerset.filter (S₀ ⊆ ·), μ(S) = ∏ p ∈ S₀, q p`. -/
private lemma powerset_prod_bernoulli_filter_subset (P S₀ : Finset ℕ) (hS₀ : S₀ ⊆ P) (q : ℕ → ℝ) :
    ∑ S ∈ P.powerset.filter (fun S => S₀ ⊆ S), (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p)) =
      ∏ p ∈ S₀, q p := by
  classical
  let R := P \ S₀
  have hdisj : ∀ T ∈ R.powerset, Disjoint S₀ T := fun T hT =>
    Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp hT)
  have himg : P.powerset.filter (fun S => S₀ ⊆ S) = R.powerset.image (fun T => S₀ ∪ T) := by
    ext S; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, R]
    constructor
    · rintro ⟨hSP, hS₀S⟩
      refine ⟨S \ S₀, Finset.sdiff_subset_sdiff hSP (Finset.Subset.refl _), Finset.union_sdiff_of_subset hS₀S⟩
    · rintro ⟨T, hTR, rfl⟩
      exact ⟨Finset.union_subset hS₀ (Finset.Subset.trans hTR Finset.sdiff_subset), Finset.subset_union_left⟩
  have hinj : Set.InjOn (fun T => S₀ ∪ T) (R.powerset : Set (Finset ℕ)) := by
    intro T₁ hT₁ T₂ hT₂ hEq
    have hd1 := hdisj T₁ hT₁
    have hd2 := hdisj T₂ hT₂
    calc T₁ = (S₀ ∪ T₁) \ S₀ := (Finset.union_sdiff_cancel_left hd1).symm
      _ = (S₀ ∪ T₂) \ S₀ := by dsimp only at hEq; rw [hEq]
      _ = T₂ := Finset.union_sdiff_cancel_left hd2
  rw [himg, Finset.sum_image (fun T₁ hT₁ T₂ hT₂ hEq => hinj hT₁ hT₂ hEq)]
  have hterm : ∀ T ∈ R.powerset,
      (∏ p ∈ S₀ ∪ T, q p) * (∏ p ∈ P \ (S₀ ∪ T), (1 - q p)) =
        (∏ p ∈ S₀, q p) * ((∏ p ∈ T, q p) * (∏ p ∈ R \ T, (1 - q p))) := by
    intro T hT
    have h1 : ∏ p ∈ S₀ ∪ T, q p = (∏ p ∈ S₀, q p) * (∏ p ∈ T, q p) :=
      Finset.prod_union (hdisj T hT)
    have h2 : P \ (S₀ ∪ T) = R \ T := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, R]; tauto
    rw [h1, h2]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, powerset_prod_bernoulli_sum_eq_one, mul_one]

/-- Exact expectation of additive weight `∑ p ∈ S, f p` under product Bernoulli measure on `P.powerset`. -/
private lemma powerset_prod_bernoulli_expect (P : Finset ℕ) (q f : ℕ → ℝ) :
    ∑ S ∈ P.powerset, ((∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))) * (∑ p ∈ S, f p) =
      ∑ p ∈ P, q p * f p := by
  classical
  have h1 : ∀ S ∈ P.powerset,
      ((∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))) * (∑ p ∈ S, f p) =
        ∑ p ∈ P, if p ∈ S then ((∏ x ∈ S, q x) * (∏ x ∈ P \ S, (1 - q x))) * f p else 0 := by
    intro S hS
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hEq : P.filter (fun p => p ∈ S) = S := by
      ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_powerset.mp hS h, h⟩⟩
    rw [hEq]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have hfilt : P.powerset.filter (fun S => p ∈ S) = P.powerset.filter (fun S => {p} ⊆ S) := by
    ext S; simp only [Finset.mem_filter, Finset.singleton_subset_iff]
  rw [hfilt, powerset_prod_bernoulli_filter_subset P {p} (Finset.singleton_subset_iff.mpr hp) q,
    Finset.prod_singleton]

/-- Markov truncation lemma on `P.powerset`: if `0 ≤ q p ≤ 1`, `0 ≤ f p`, `0 < B`, and
`∑ p ∈ P, q p * f p ≤ B / 2`, then the subset `{S ⊆ P | ∑ p ∈ S, f p ≤ B}` has total
measure `≥ 1 / 2`. -/
private lemma powerset_prod_bernoulli_markov (P : Finset ℕ) (q f : ℕ → ℝ) (B : ℝ)
    (hq0 : ∀ p ∈ P, 0 ≤ q p) (hq1 : ∀ p ∈ P, q p ≤ 1)
    (hf : ∀ p ∈ P, 0 ≤ f p) (hB : 0 < B)
    (hexp : ∑ p ∈ P, q p * f p ≤ B / 2) :
    (1 : ℝ) / 2 ≤ ∑ S ∈ P.powerset.filter (fun S => ∑ p ∈ S, f p ≤ B),
      (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p)) := by
  classical
  let μ : Finset ℕ → ℝ := fun S => (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))
  have hμ_nn : ∀ S ∈ P.powerset, 0 ≤ μ S := fun S hS =>
    mul_nonneg (Finset.prod_nonneg fun p hp => hq0 p (Finset.mem_powerset.mp hS hp))
      (Finset.prod_nonneg fun p hp => by linarith [hq1 p (Finset.mem_sdiff.mp hp).1])
  let Bad := P.powerset.filter (fun S => ¬ ∑ p ∈ S, f p ≤ B)
  have hbad : (∑ S ∈ Bad, μ S) * B ≤ ∑ p ∈ P, q p * f p := by
    calc (∑ S ∈ Bad, μ S) * B = ∑ S ∈ Bad, μ S * B := by rw [Finset.sum_mul]
      _ ≤ ∑ S ∈ Bad, μ S * (∑ p ∈ S, f p) :=
          Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left
            (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hS).2)) (hμ_nn S (Finset.mem_filter.mp hS).1)
      _ ≤ ∑ S ∈ P.powerset, μ S * (∑ p ∈ S, f p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S hS _ =>
            mul_nonneg (hμ_nn S hS) (Finset.sum_nonneg fun p hp => hf p (Finset.mem_powerset.mp hS hp))
      _ = ∑ p ∈ P, q p * f p := powerset_prod_bernoulli_expect P q f
  have hbad_half : ∑ S ∈ Bad, μ S ≤ 1 / 2 := by nlinarith
  have hsplit := Finset.sum_filter_add_sum_filter_not P.powerset (fun S => ∑ p ∈ S, f p ≤ B) μ
  rw [powerset_prod_bernoulli_sum_eq_one P q] at hsplit
  dsimp [Bad] at hbad_half
  linarith

/-- Truncated Euler sum lower bound via powerset Markov: if `0 ≤ r p ≤ 1` for `p ∈ P` and
`∑ p ∈ P, r p * log p ≤ B / 2` (`B > 0`), then
`∑ S ∈ P.powerset.filter (fun S => ∑ p ∈ S, log p ≤ B), ∏ p ∈ S, r p ≥ (1/2) * exp ((1/2) * ∑ p ∈ P, r p)`. -/
private lemma truncated_euler_sum_lower (P : Finset ℕ) (r : ℕ → ℝ) (B : ℝ)
    (hP : ∀ p ∈ P, 2 ≤ p)
    (hr0 : ∀ p ∈ P, 0 ≤ r p) (hr1 : ∀ p ∈ P, r p ≤ 1)
    (hB : 0 < B)
    (hlog_sum : ∑ p ∈ P, r p * Real.log (p : ℝ) ≤ B / 2) :
    (1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p) ≤
      ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B), ∏ p ∈ S, r p := by
  classical
  let q : ℕ → ℝ := fun p => r p / (1 + r p)
  have h1r_pos : ∀ p ∈ P, 0 < 1 + r p := fun p hp => by linarith [hr0 p hp]
  have hq0 : ∀ p ∈ P, 0 ≤ q p := fun p hp => div_nonneg (hr0 p hp) (le_of_lt (h1r_pos p hp))
  have hq1 : ∀ p ∈ P, q p ≤ 1 := fun p hp => (div_le_one (h1r_pos p hp)).mpr (by linarith [hr0 p hp])
  have hq_le_r : ∀ p ∈ P, q p ≤ r p := fun p hp => by
    dsimp [q]; rw [div_le_iff₀ (h1r_pos p hp)]; nlinarith [hr0 p hp]
  have hlog_nn : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (by have := hP p hp; omega : 1 ≤ p))
  have hexp : ∑ p ∈ P, q p * Real.log (p : ℝ) ≤ B / 2 :=
    le_trans (Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hq_le_r p hp) (hlog_nn p hp)) hlog_sum
  have hmarkov := powerset_prod_bernoulli_markov P q (fun p => Real.log (p : ℝ)) B hq0 hq1 hlog_nn hB hexp
  have hZ_eq : ∀ S ∈ P.powerset,
      ((∏ p ∈ P, (1 + r p)) * ((∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p)))) = ∏ p ∈ S, r p := by
    intro S hS
    have hsplit' : ∏ p ∈ P, (1 + r p) = (∏ p ∈ S, (1 + r p)) * (∏ p ∈ P \ S, (1 + r p)) := by
      rw [← Finset.prod_sdiff (Finset.mem_powerset.mp hS), mul_comm]
    rw [hsplit']
    have hA : (∏ p ∈ S, (1 + r p)) * (∏ p ∈ S, q p) = ∏ p ∈ S, r p := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      dsimp [q]; exact mul_div_cancel₀ _ (ne_of_gt (h1r_pos p (Finset.mem_powerset.mp hS hp)))
    have hB' : (∏ p ∈ P \ S, (1 + r p)) * (∏ p ∈ P \ S, (1 - q p)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun p hp => ?_
      have hpP := (Finset.mem_sdiff.mp hp).1
      dsimp [q]; field_simp [ne_of_gt (h1r_pos p hpP)]; ring
    calc ((∏ p ∈ S, (1 + r p)) * (∏ p ∈ P \ S, (1 + r p))) * ((∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p)))
        = ((∏ p ∈ S, (1 + r p)) * (∏ p ∈ S, q p)) * ((∏ p ∈ P \ S, (1 + r p)) * (∏ p ∈ P \ S, (1 - q p))) := by ring
      _ = (∏ p ∈ S, r p) * 1 := by rw [hA, hB']
      _ = ∏ p ∈ S, r p := mul_one _
  have hZ_ge : Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p) ≤ ∏ p ∈ P, (1 + r p) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => le_of_lt (Real.exp_pos _)) fun p hp => ?_
    rw [show (1 : ℝ) / 2 * r p = r p / 2 by ring]
    exact exp_half_le_one_add (hr0 p hp) (hr1 p hp)
  have hZ_nn : 0 ≤ ∏ p ∈ P, (1 + r p) := Finset.prod_nonneg fun p hp => le_of_lt (h1r_pos p hp)
  calc (1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p)
      ≤ (1 : ℝ) / 2 * ∏ p ∈ P, (1 + r p) := mul_le_mul_of_nonneg_left hZ_ge (by norm_num)
    _ ≤ (∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B),
          (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))) * ∏ p ∈ P, (1 + r p) :=
        mul_le_mul_of_nonneg_right hmarkov hZ_nn
    _ = ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B),
          (∏ p ∈ P, (1 + r p)) * ((∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))) := by
        rw [mul_comm, Finset.mul_sum]
    _ = ∑ S ∈ P.powerset.filter (fun S : Finset ℕ => ∑ p ∈ S, Real.log (p : ℝ) ≤ B), ∏ p ∈ S, r p :=
        Finset.sum_congr rfl fun S hS => hZ_eq S (Finset.mem_filter.mp hS).1

/-- Unique recovery of `(S₀, p₀)` from `(∏ p ∈ S₀, p) * p₀` when `S₀` consists of primes `≤ M`
and `p₀ > M` is prime. -/
private lemma prod_primes_mul_large_prime_inj (M : ℕ)
    {S₁ S₂ : Finset ℕ} {p₁ p₂ : ℕ}
    (hS₁ : ∀ p ∈ S₁, p.Prime ∧ p ≤ M) (hS₂ : ∀ p ∈ S₂, p.Prime ∧ p ≤ M)
    (hp₁ : p₁.Prime ∧ M < p₁) (hp₂ : p₂.Prime ∧ M < p₂)
    (hEq : (∏ p ∈ S₁, p) * p₁ = (∏ p ∈ S₂, p) * p₂) :
    S₁ = S₂ ∧ p₁ = p₂ := by
  have hp1_not_S2 : ∀ q ∈ S₂, ¬ p₁ ∣ q := fun q hq hdvd => by
    have hq_pr := (hS₂ q hq).1
    have := (Nat.prime_dvd_prime_iff_eq hp₁.1 hq_pr).mp hdvd
    have := (hS₂ q hq).2; omega
  have hp1_not_prod2 : ¬ p₁ ∣ ∏ q ∈ S₂, q := by
    intro hdvd
    rcases (Prime.dvd_finsetProd_iff hp₁.1.prime id).mp hdvd with ⟨q, hq, hq_dvd⟩
    exact hp1_not_S2 q hq hq_dvd
  have hp1_dvd : p₁ ∣ (∏ q ∈ S₂, q) * p₂ := ⟨∏ q ∈ S₁, q, by rw [← hEq, mul_comm]⟩
  have hp1_eq_p2 : p₁ = p₂ := by
    rcases hp₁.1.dvd_mul.mp hp1_dvd with h1 | h2
    · exact (hp1_not_prod2 h1).elim
    · exact (Nat.prime_dvd_prime_iff_eq hp₁.1 hp₂.1).mp h2
  subst hp1_eq_p2
  have hprod_eq : ∏ p ∈ S₁, p = ∏ p ∈ S₂, p := Nat.eq_of_mul_eq_mul_right hp₁.1.pos hEq
  have hS_eq : S₁ = S₂ := by
    ext q; constructor <;> intro hq
    · have hq_pr := (hS₁ q hq).1
      have hq_dvd : q ∣ ∏ p ∈ S₂, p := by rw [← hprod_eq]; exact Finset.dvd_prod_of_mem id hq
      rcases (Prime.dvd_finsetProd_iff hq_pr.prime id).mp hq_dvd with ⟨r, hr, hqr⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hq_pr (hS₂ r hr).1).mp hqr]
    · have hq_pr := (hS₂ q hq).1
      have hq_dvd : q ∣ ∏ p ∈ S₁, p := by rw [hprod_eq]; exact Finset.dvd_prod_of_mem id hq
      rcases (Prime.dvd_finsetProd_iff hq_pr.prime id).mp hq_dvd with ⟨r, hr, hqr⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hq_pr (hS₁ r hr).1).mp hqr]
  exact ⟨hS_eq, rfl⟩

/-- Unified random-tilt lower bound on `∑ d ∈ Ioc (N/2) N, p_w(d)^α` for any `α ∈ (0, 1)`
using `P_win J` and `q_p = 2^J / p` (simultaneously proving Barrier 1 at `α = 2/3` and
Barrier 2a at `α = 1/2`). -/
private lemma unified_random_tilt_lower (N J : ℕ) (α : ℝ)
    (hα0 : 0 < α) (hα34 : α ≤ 3 / 4)
    (hJ30 : 30 ≤ J)
    (hY_budget : 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ) ≤ (1 : ℝ) / 10 * Real.log (N : ℝ))
    (hY_sq_small : ((2 ^ (2 * J) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2))
    (hN_big : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10))
    (hlogN_ge : 100 ≤ Real.log (N : ℝ)) :
    let H := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
    ∃ w : ℕ → ℝ,
      (∀ t ∈ Finset.Icc 1 H, 0 ≤ w t) ∧
      (∑ t ∈ Finset.Icc 1 H, w t ≤ 1) ∧
      ((N : ℝ) ^ (1 - α) / (128 * Real.log (N : ℝ))) *
          Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ α) ≤
        ∑ d ∈ Finset.Ioc (N / 2) N,
          (∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t) ^ α := by
  classical
  intro H
  have hα1 : α < 1 := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 1 < (N : ℝ) := by
      have := Real.exp_lt_exp.mpr (show (0 : ℝ) < Real.log (N : ℝ) by linarith)
      rw [Real.exp_zero] at this
      by_contra hle; push Not at hle
      have : Real.log (N : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg N) hle
      linarith
    linarith
  have hN_ge2 : 2 ≤ N := by
    have h1 : (2 : ℝ) ≤ (N : ℝ) := by
      have : (2 : ℝ) < Real.exp (Real.log (N : ℝ)) := by linarith [Real.add_one_le_exp (Real.log (N : ℝ))]
      rw [Real.exp_log hN_pos] at this; exact le_of_lt this
    exact_mod_cast h1
  let P := P_win J
  let Y : ℝ := ((2 ^ J : ℕ) : ℝ)
  let q : ℕ → ℝ := fun p => Y / (p : ℝ)
  have hP_prop : ∀ p ∈ P, p.Prime ∧ 2 ^ J < p ∧ p ≤ 2 ^ (2 * J) := fun p hp =>
    ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1,
     (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩
  have hq0 : ∀ p ∈ P, 0 ≤ q p := fun p _ => by dsimp [q, Y]; positivity
  have hq1 : ∀ p ∈ P, q p ≤ 1 := fun p hp => by
    dsimp [q, Y]
    exact (div_le_one (by exact_mod_cast (hP_prop p hp).1.pos)).mpr (by exact_mod_cast le_of_lt (hP_prop p hp).2.1)
  let μ : Finset ℕ → ℝ := fun S => (∏ p ∈ S, q p) * (∏ p ∈ P \ S, (1 - q p))
  have hμ_nn : ∀ S ∈ P.powerset, 0 ≤ μ S := fun S hS =>
    mul_nonneg (Finset.prod_nonneg fun p hp => hq0 p (Finset.mem_powerset.mp hS hp))
      (Finset.prod_nonneg fun p hp => by linarith [hq1 p (Finset.mem_sdiff.mp hp).1])
  let Tmax := Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 3))
  let GoodS := P.powerset.filter (fun S => ∏ p ∈ S, p ≤ Tmax)
  -- Sub-probability weight w(t) = (1/N) * ∑_{S ∈ GoodS, (∏ S) ∣ t, t / (∏ S) ≤ N} μ(S)
  let w : ℕ → ℝ := fun t =>
    ((N : ℝ))⁻¹ * ∑ S ∈ GoodS.filter (fun S => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N), μ S
  have hw_nn : ∀ t ∈ Finset.Icc 1 H, 0 ≤ w t := fun t _ =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun S hS =>
      hμ_nn S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)
  have hTmax_mul : Tmax * N ≤ H := by
    have h1 : (Tmax : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
    have h2 : ((Tmax * N : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Nat.cast_mul, show ((4 : ℝ) / 3) = ((1 : ℝ) / 3) + 1 by norm_num, Real.rpow_add hN_pos, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hN_pos)
    exact Nat.le_floor h2
  have hw_sum : ∑ t ∈ Finset.Icc 1 H, w t ≤ 1 := by
    have hswap : ∑ t ∈ Finset.Icc 1 H, w t =
        ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
          (((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ) * μ S := by
      dsimp only [w]
      rw [← Finset.mul_sum]
      congr 1
      have h1 : ∀ t ∈ Finset.Icc 1 H,
          ∑ S ∈ GoodS.filter (fun S => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N), μ S =
          ∑ S ∈ GoodS, if (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N then μ S else 0 :=
        fun _ _ => Finset.sum_filter _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hswap]
    have hcard_le : ∀ S ∈ GoodS,
        ((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card ≤ N := by
      intro S hS
      have hprod_pos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp =>
        (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hp)).1.pos
      have hmaps : ∀ t ∈ (Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N),
          t / (∏ p ∈ S, p) ∈ Finset.Icc 1 N := by
        intro t ht
        have ht1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
        have hdvd := (Finset.mem_filter.mp ht).2.1
        have hle := (Finset.mem_filter.mp ht).2.2
        have hpos : 1 ≤ t / (∏ p ∈ S, p) := by
          have hmul := Nat.mul_div_cancel' hdvd
          by_contra h0; push Not at h0
          have : t / (∏ p ∈ S, p) = 0 := Nat.lt_one_iff.mp h0
          rw [this, mul_zero] at hmul; omega
        exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
      have hinj : Set.InjOn (fun t => t / (∏ p ∈ S, p))
          (((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)) : Set ℕ) := by
        intro t₁ ht₁ t₂ ht₂ hEq; dsimp only at hEq
        calc t₁ = (∏ p ∈ S, p) * (t₁ / (∏ p ∈ S, p)) := (Nat.mul_div_cancel' (Finset.mem_filter.mp ht₁).2.1).symm
          _ = (∏ p ∈ S, p) * (t₂ / (∏ p ∈ S, p)) := by rw [hEq]
          _ = t₂ := Nat.mul_div_cancel' (Finset.mem_filter.mp ht₂).2.1
      calc ((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card
          ≤ (Finset.Icc 1 N).card := Finset.card_le_card_of_injOn _ hmaps hinj
        _ = N := by simp
    calc ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
            (((Finset.Icc 1 H).filter (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ) * μ S
        ≤ ((N : ℝ))⁻¹ * ∑ S ∈ GoodS, (N : ℝ) * μ S := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S hS => ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le S hS) (hμ_nn S (Finset.mem_filter.mp hS).1)
      _ = ∑ S ∈ GoodS, μ S := by rw [← Finset.mul_sum, inv_mul_cancel_left₀ (ne_of_gt hN_pos)]
      _ ≤ ∑ S ∈ P.powerset, μ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S hS _ => hμ_nn S hS
      _ = 1 := powerset_prod_bernoulli_sum_eq_one P q
  -- Now bound ∑_{d ∈ Ioc (N/2) N} p_w(d)^α from below!
  refine ⟨w, hw_nn, hw_sum, ?_⟩
  let L := Real.log (N : ℝ)
  have hsum_inv := sum_inv_primes_win_bounds J hJ30
  have hlogp_le : ∀ p ∈ P, Real.log (p : ℝ) ≤ 2 * (J : ℝ) := fun p hp => by
    have h1 : (p : ℝ) ≤ (2 : ℝ) ^ (2 * J) := by exact_mod_cast (hP_prop p hp).2.2
    have h2 := Real.log_le_log (by exact_mod_cast (hP_prop p hp).1.pos) h1
    rw [Real.log_pow] at h2; push_cast at h2
    have := log_two_le_one
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hlogp_nn : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hP_prop p hp).1.one_le)
  have hqlog_sum : ∑ p ∈ P, q p * Real.log (p : ℝ) ≤ L / 10 := by
    calc ∑ p ∈ P, q p * Real.log (p : ℝ)
        ≤ ∑ p ∈ P, (Y / (p : ℝ)) * (2 * (J : ℝ)) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hlogp_le p hp) (hq0 p hp)
      _ = 2 * Y * (J : ℝ) * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ 2 * Y * (J : ℝ) * 4 := mul_le_mul_of_nonneg_left hsum_inv.2 (by positivity)
      _ = 8 * Y * (J : ℝ) := by ring
      _ ≤ L / 10 := by linarith [hY_budget]
  -- Define SmallS₀ = {S₀ ⊆ P | ∑ p ∈ S₀, log p ≤ L / 10}
  let SmallS₀ := P.powerset.filter (fun S₀ : Finset ℕ => ∑ p ∈ S₀, Real.log (p : ℝ) ≤ L / 10)
  -- For any S₀ ∈ SmallS₀, ∏ p ∈ S₀, p ≤ N^(1/10) and ∑_{S ∈ GoodS, S₀ ⊆ S} μ(S) ≥ (1/2) * ∏_{p ∈ S₀} q p
  have hS₀_prod_le : ∀ S₀ ∈ SmallS₀, ((∏ p ∈ S₀, p : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := by
    intro S₀ hS₀
    have hsum_le : ∑ p ∈ S₀, Real.log (p : ℝ) ≤ L / 10 := (Finset.mem_filter.mp hS₀).2
    have hprod_pos : (0 : ℝ) < ((∏ p ∈ S₀, p : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun p hp => (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos
    have hlog_eq : Real.log ((∏ p ∈ S₀, p : ℕ) : ℝ) = ∑ p ∈ S₀, Real.log (p : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      intro p hp; exact ne_of_gt (by exact_mod_cast (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos)
    calc ((∏ p ∈ S₀, p : ℕ) : ℝ) = Real.exp (Real.log ((∏ p ∈ S₀, p : ℕ) : ℝ)) := (Real.exp_log hprod_pos).symm
      _ ≤ Real.exp (L / 10) := Real.exp_le_exp.mpr (by linarith)
      _ = (N : ℝ) ^ ((1 : ℝ) / 10) := by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring
  have hcond_good : ∀ S₀ ∈ SmallS₀,
      (1 : ℝ) / 2 * (∏ p ∈ S₀, q p) ≤ ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), μ S := by
    intro S₀ hS₀
    have hS₀P : S₀ ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1
    let R := P \ S₀
    have hqlog_R : ∑ p ∈ R, q p * Real.log (p : ℝ) ≤ (L / 5) / 2 := by
      calc ∑ p ∈ R, q p * Real.log (p : ℝ)
          ≤ ∑ p ∈ P, q p * Real.log (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
            fun p hp _ => mul_nonneg (hq0 p hp) (hlogp_nn p hp)
        _ ≤ L / 10 := hqlog_sum
        _ = (L / 5) / 2 := by ring
    have hmk := powerset_prod_bernoulli_markov R q (fun p => Real.log (p : ℝ)) (L / 5)
      (fun p hp => hq0 p (Finset.mem_sdiff.mp hp).1) (fun p hp => hq1 p (Finset.mem_sdiff.mp hp).1)
      (fun p hp => hlogp_nn p (Finset.mem_sdiff.mp hp).1) (by linarith) hqlog_R
    let GoodT := R.powerset.filter (fun T : Finset ℕ => ∑ p ∈ T, Real.log (p : ℝ) ≤ L / 5)
    -- Every T ∈ GoodT maps via T ↦ S₀ ∪ T into GoodS.filter (S₀ ⊆ ·)
    have hmaps : ∀ T ∈ GoodT, S₀ ∪ T ∈ GoodS.filter (fun S => S₀ ⊆ S) := by
      intro T hT
      have hTR : T ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hdisj : Disjoint S₀ T := Finset.disjoint_sdiff.mono_right hTR
      have hSP : S₀ ∪ T ⊆ P := Finset.union_subset hS₀P (Finset.Subset.trans hTR Finset.sdiff_subset)
      have hlog_sum : ∑ p ∈ S₀ ∪ T, Real.log (p : ℝ) ≤ (3 : ℝ) / 10 * L := by
        rw [Finset.sum_union hdisj]
        linarith [(Finset.mem_filter.mp hS₀).2, (Finset.mem_filter.mp hT).2]
      have hprod_le : ((∏ p ∈ S₀ ∪ T, p : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
        have hpos : (0 : ℝ) < ((∏ p ∈ S₀ ∪ T, p : ℕ) : ℝ) := by
          exact_mod_cast Finset.prod_pos fun p hp => (hP_prop p (hSP hp)).1.pos
        have hlog_eq : Real.log ((∏ p ∈ S₀ ∪ T, p : ℕ) : ℝ) = ∑ p ∈ S₀ ∪ T, Real.log (p : ℝ) := by
          rw [Nat.cast_prod, Real.log_prod]
          intro p hp; exact ne_of_gt (by exact_mod_cast (hP_prop p (hSP hp)).1.pos)
        calc ((∏ p ∈ S₀ ∪ T, p : ℕ) : ℝ) = Real.exp (Real.log ((∏ p ∈ S₀ ∪ T, p : ℕ) : ℝ)) := (Real.exp_log hpos).symm
          _ ≤ Real.exp ((1 : ℝ) / 3 * L) := Real.exp_le_exp.mpr (by linarith)
          _ = (N : ℝ) ^ ((1 : ℝ) / 3) := by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSP, Nat.le_floor hprod_le⟩,
        Finset.subset_union_left⟩
    have hinj : Set.InjOn (fun T => S₀ ∪ T) (GoodT : Set (Finset ℕ)) := by
      intro T₁ hT₁ T₂ hT₂ hEq
      have hd1 : Disjoint S₀ T₁ := Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp (Finset.mem_filter.mp hT₁).1)
      have hd2 : Disjoint S₀ T₂ := Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp (Finset.mem_filter.mp hT₂).1)
      calc T₁ = (S₀ ∪ T₁) \ S₀ := (Finset.union_sdiff_cancel_left hd1).symm
        _ = (S₀ ∪ T₂) \ S₀ := by dsimp only at hEq; rw [hEq]
        _ = T₂ := Finset.union_sdiff_cancel_left hd2
    have hsub_img : GoodT.image (fun T => S₀ ∪ T) ⊆ GoodS.filter (fun S => S₀ ⊆ S) := by
      intro S hS; rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩; exact hmaps T hT
    calc (1 : ℝ) / 2 * (∏ p ∈ S₀, q p)
        ≤ (∏ p ∈ S₀, q p) * ∑ T ∈ GoodT, (∏ p ∈ T, q p) * (∏ p ∈ R \ T, (1 - q p)) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmk (Finset.prod_nonneg fun p hp => hq0 p (hS₀P hp))
      _ = ∑ T ∈ GoodT, μ (S₀ ∪ T) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun T hT => ?_
          have hTR : T ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
          have hdisj : Disjoint S₀ T := Finset.disjoint_sdiff.mono_right hTR
          have hsdiff : P \ (S₀ ∪ T) = R \ T := by ext x; simp only [Finset.mem_sdiff, Finset.mem_union, R]; tauto
          dsimp [μ]; rw [Finset.prod_union hdisj, hsdiff]; ring
      _ = ∑ S ∈ GoodT.image (fun T => S₀ ∪ T), μ S :=
          (Finset.sum_image (fun T₁ hT₁ T₂ hT₂ hEq => hinj hT₁ hT₂ hEq)).symm
      _ ≤ ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), μ S :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun S hS _ =>
            hμ_nn S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  -- Lower bound on p_w(d₁ * p₀) for S₀ ∈ SmallS₀ and prime p₀ ∈ (N/(2*d₁), N/d₁]
  have hp_w_lb : ∀ S₀ ∈ SmallS₀, ∀ p₀ ∈ (Finset.Ioc (N / (2 * ∏ p ∈ S₀, p)) (N / ∏ p ∈ S₀, p)).filter Nat.Prime,
      (((∏ p ∈ S₀, p : ℕ) : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p) ≤
        ∑ t ∈ (Finset.Icc 1 H).filter (fun t => (∏ p ∈ S₀, p) * p₀ ∣ t), w t := by
    intro S₀ hS₀ p₀ hp₀
    set d₁ := ∏ p ∈ S₀, p
    have hd₁_pos : 1 ≤ d₁ := Finset.one_le_prod' fun p hp =>
      (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.one_le
    have hp₀_I := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1
    have hp₀_pr : p₀.Prime := (Finset.mem_filter.mp hp₀).2
    have hp₀_le_N : p₀ ≤ N := le_trans hp₀_I.2 (Nat.div_le_self N d₁)
    -- Swap sums on RHS
    have hswap : ∑ t ∈ (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t), w t =
        ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
          (((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ) * μ S := by
      dsimp only [w]; rw [← Finset.mul_sum]; congr 1
      have h1 : ∀ t ∈ (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t),
          ∑ S ∈ GoodS.filter (fun S => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N), μ S =
          ∑ S ∈ GoodS, if (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N then μ S else 0 := fun _ _ => Finset.sum_filter _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hf_eq : ((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t)).filter
            (fun t => (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N) =
          (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N) := by
        ext t; simp only [Finset.mem_filter]; tauto
      rw [hf_eq]
    rw [hswap]
    have hcount : ∀ S ∈ GoodS.filter (fun S => S₀ ⊆ S),
        N / p₀ ≤ ((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card := by
      intro S hS
      have hS_good := (Finset.mem_filter.mp hS).1
      have hS₀S : S₀ ⊆ S := (Finset.mem_filter.mp hS).2
      set T₁ := ∏ p ∈ S, p
      have hT₁_pos : 1 ≤ T₁ := Finset.one_le_prod' fun p hp =>
        (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS_good).1 hp)).1.one_le
      have hT₁_le : T₁ ≤ Tmax := (Finset.mem_filter.mp hS_good).2
      have hd₁_dvd_T₁ : d₁ ∣ T₁ := Finset.prod_dvd_prod_of_subset S₀ S id hS₀S
      have hmaps : ∀ k ∈ Finset.Icc 1 (N / p₀),
          T₁ * (k * p₀) ∈ (Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ T₁ ∣ t ∧ t / T₁ ≤ N) := by
        intro k hk
        have hk_I := Finset.mem_Icc.mp hk
        have hkp₀_le : k * p₀ ≤ N := le_trans (Nat.mul_le_mul_right p₀ hk_I.2) (Nat.div_mul_le_self N p₀)
        have ht_le : T₁ * (k * p₀) ≤ H := le_trans (Nat.mul_le_mul hT₁_le hkp₀_le) hTmax_mul
        have ht_ge1 : 1 ≤ T₁ * (k * p₀) := Nat.mul_pos hT₁_pos (Nat.mul_pos hk_I.1 hp₀_pr.pos)
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht_ge1, ht_le⟩, ?_, dvd_mul_right T₁ _, ?_⟩
        · rcases hd₁_dvd_T₁ with ⟨c, hc⟩
          exact ⟨c * k, by rw [hc]; ring⟩
        · rwa [Nat.mul_div_cancel_left _ hT₁_pos]
      have hinj : Set.InjOn (fun k => T₁ * (k * p₀)) (Finset.Icc 1 (N / p₀) : Set ℕ) := by
        intro k₁ _ k₂ _ hEq; dsimp only at hEq
        exact Nat.eq_of_mul_eq_mul_right hp₀_pr.pos (Nat.eq_of_mul_eq_mul_left hT₁_pos hEq)
      calc N / p₀ = (Finset.Icc 1 (N / p₀)).card := by simp
        _ ≤ _ := Finset.card_le_card_of_injOn _ hmaps hinj
    have hdiv_ge : (d₁ : ℝ) / 2 ≤ ((N / p₀ : ℕ) : ℝ) := by
      have h1 : d₁ ≤ N / p₀ + N / p₀ := by
        have hq_ge1 : 1 ≤ N / p₀ := (Nat.le_div_iff_mul_le hp₀_pr.pos).mpr (by simpa using hp₀_le_N)
        have hmod := Nat.div_add_mod N p₀; have hlt := Nat.mod_lt N hp₀_pr.pos
        have h2 : N < p₀ * (N / p₀ + 1) := by nlinarith
        have h3 : p₀ * d₁ ≤ N := by
          have := Nat.div_mul_le_self N d₁; have := Nat.mul_le_mul_right d₁ hp₀_I.2; omega
        have h4 : d₁ ≤ N / p₀ + 1 := by
          by_contra hgt; push Not at hgt
          have : p₀ * (N / p₀ + 1) < p₀ * d₁ := Nat.mul_lt_mul_of_pos_left (by omega) hp₀_pr.pos
          omega
        omega
      have h2 : (d₁ : ℝ) ≤ 2 * ((N / p₀ : ℕ) : ℝ) := by exact_mod_cast (by omega : d₁ ≤ 2 * (N / p₀))
      linarith
    calc ((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)
        = ((N : ℝ))⁻¹ * ((d₁ : ℝ) / 2) * ((1 : ℝ) / 2 * (∏ p ∈ S₀, q p)) := by ring
      _ ≤ ((N : ℝ))⁻¹ * ((N / p₀ : ℕ) : ℝ) * ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), μ S :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdiv_ge (by positivity)) (hcond_good S₀ hS₀)
            (by positivity) (by positivity)
      _ = ((N : ℝ))⁻¹ * ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S), ((N / p₀ : ℕ) : ℝ) * μ S := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ ((N : ℝ))⁻¹ * ∑ S ∈ GoodS.filter (fun S => S₀ ⊆ S),
            (((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ) * μ S :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S hS =>
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcount S hS)
              (hμ_nn S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)) (by positivity)
      _ ≤ ((N : ℝ))⁻¹ * ∑ S ∈ GoodS,
            (((Finset.Icc 1 H).filter (fun t => d₁ * p₀ ∣ t ∧ (∏ p ∈ S, p) ∣ t ∧ t / (∏ p ∈ S, p) ≤ N)).card : ℝ) * μ S :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S hS _ =>
            mul_nonneg (Nat.cast_nonneg _) (hμ_nn S (Finset.mem_filter.mp hS).1)) (by positivity)
  -- Sum over disjoint pairs (S₀, p₀) mapping injectively into Finset.Ioc (N/2) N
  let P₀ : Finset ℕ → Finset ℕ := fun S₀ =>
    (Finset.Ioc (N / (2 * ∏ p ∈ S₀, p)) (N / ∏ p ∈ S₀, p)).filter Nat.Prime
  let Pairs := SmallS₀.sigma P₀
  let φ : (Σ _ : Finset ℕ, ℕ) → ℕ := fun x => (∏ p ∈ x.1, p) * x.2
  have hmaps_D : ∀ x ∈ Pairs, φ x ∈ Finset.Ioc (N / 2) N := by
    intro x hx
    have hS₀ : x.1 ∈ SmallS₀ := (Finset.mem_sigma.mp hx).1
    have hp₀ : x.2 ∈ P₀ x.1 := (Finset.mem_sigma.mp hx).2
    have hI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1
    set d₁ := ∏ p ∈ x.1, p
    have hd₁_pos : 1 ≤ d₁ := Finset.one_le_prod' fun p hp =>
      (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.one_le
    have hhi : d₁ * x.2 ≤ N := le_trans (Nat.mul_le_mul_left d₁ hI.2) (by rw [mul_comm]; exact Nat.div_mul_le_self N d₁)
    have hlo : N / 2 < d₁ * x.2 := by
      have hdiv : N / (2 * d₁) = (N / 2) / d₁ := (Nat.div_div_eq_div_mul N 2 d₁).symm
      have hmod := Nat.div_add_mod (N / 2) d₁
      have hlt := Nat.mod_lt (N / 2) hd₁_pos
      have : d₁ * (N / (2 * d₁) + 1) ≤ d₁ * x.2 := Nat.mul_le_mul_left d₁ (by omega)
      rw [hdiv] at this; nlinarith
    exact Finset.mem_Ioc.mpr ⟨hlo, hhi⟩
  have hp₀_gt_M : ∀ S₀ ∈ SmallS₀, ∀ p₀ ∈ P₀ S₀, 2 ^ (2 * J) < p₀ := by
    intro S₀ hS₀ p₀ hp₀
    set d₁ := ∏ p ∈ S₀, p
    have hd₁_le : (d₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := hS₀_prod_le S₀ hS₀
    have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by
      exact_mod_cast Finset.prod_pos fun p hp =>
        (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos
    have hdiv_ge : (N : ℝ) ^ ((9 : ℝ) / 10) ≤ (N : ℝ) / (d₁ : ℝ) := by
      rw [le_div_iff₀ hd₁_pos]
      calc (N : ℝ) ^ ((9 : ℝ) / 10) * (d₁ : ℝ)
          ≤ (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) :=
            mul_le_mul_of_nonneg_left hd₁_le (by positivity)
        _ = (N : ℝ) := by rw [← Real.rpow_add hN_pos]; norm_num
    have hN2d_ge : (N : ℝ) ^ ((1 : ℝ) / 2) < ((N / (2 * d₁) + 1 : ℕ) : ℝ) := by
      have h1 : (N : ℝ) / (2 * (d₁ : ℝ)) < ((N / (2 * d₁) + 1 : ℕ) : ℝ) := by
        have hd₁_pos_nat : 0 < d₁ := by exact_mod_cast hd₁_pos
        have hmod := Nat.div_add_mod N (2 * d₁)
        have hlt := Nat.mod_lt N (by omega : 0 < 2 * d₁)
        have : N < (2 * d₁) * (N / (2 * d₁) + 1) := by nlinarith
        have hcast : (N : ℝ) < (2 * (d₁ : ℝ)) * ((N / (2 * d₁) + 1 : ℕ) : ℝ) := by exact_mod_cast this
        exact (div_lt_iff₀' (by positivity)).mpr hcast
      have hhalf : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) / (2 * (d₁ : ℝ)) := by
        have h4 : (2 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by
          have : (2 : ℝ) ≤ Real.exp (2 / 5 * L) := by linarith [Real.add_one_le_exp (2 / 5 * L)]
          rwa [show Real.exp (2 / 5 * L) = (N : ℝ) ^ ((2 : ℝ) / 5) by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring] at this
        have hprod : (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((2 : ℝ) / 5) = (N : ℝ) ^ ((9 : ℝ) / 10) := by
          rw [← Real.rpow_add hN_pos]; norm_num
        have hmul : 2 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((9 : ℝ) / 10) := by
          calc 2 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
                mul_le_mul_of_nonneg_right h4 (by positivity)
            _ = (N : ℝ) ^ ((9 : ℝ) / 10) := by rw [mul_comm, hprod]
        have : (N : ℝ) / (2 * (d₁ : ℝ)) = ((N : ℝ) / (d₁ : ℝ)) / 2 := by ring
        linarith
      linarith
    have hp₀_ge : N / (2 * d₁) + 1 ≤ p₀ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1).1
    have hlt_r : ((2 ^ (2 * J) : ℕ) : ℝ) < (p₀ : ℝ) :=
      lt_of_le_of_lt hY_sq_small (lt_of_lt_of_le hN2d_ge (by exact_mod_cast hp₀_ge))
    exact_mod_cast hlt_r
  have hinj_D : Set.InjOn φ (Pairs : Set _) := by
    intro x₁ hx₁ x₂ hx₂ hEq
    have h1 := Finset.mem_sigma.mp hx₁
    have h2 := Finset.mem_sigma.mp hx₂
    have hres := prod_primes_mul_large_prime_inj (2 ^ (2 * J))
      (fun p hp => ⟨(hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h1.1).1 hp)).1,
        (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h1.1).1 hp)).2.2⟩)
      (fun p hp => ⟨(hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h2.1).1 hp)).1,
        (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp h2.1).1 hp)).2.2⟩)
      ⟨(Finset.mem_filter.mp h1.2).2, hp₀_gt_M x₁.1 h1.1 x₁.2 h1.2⟩
      ⟨(Finset.mem_filter.mp h2.2).2, hp₀_gt_M x₂.1 h2.1 x₂.2 h2.2⟩ hEq
    rcases x₁ with ⟨S₁, p₁⟩; rcases x₂ with ⟨S₂, p₂⟩
    simp only at hres; rcases hres with ⟨rfl, rfl⟩; rfl
  let f_obj : ℕ → ℝ := fun d => (∑ t ∈ (Finset.Icc 1 H).filter (fun t => d ∣ t), w t) ^ α
  have hf_nn : ∀ d, 0 ≤ f_obj d := fun d =>
    Real.rpow_nonneg (Finset.sum_nonneg fun t ht => hw_nn t (Finset.mem_filter.mp ht).1) _
  have hsub_D : Pairs.image φ ⊆ Finset.Ioc (N / 2) N := by
    intro d hd; rcases Finset.mem_image.mp hd with ⟨x, hx, rfl⟩; exact hmaps_D x hx
  -- Evaluate sum over Pairs
  let r : ℕ → ℝ := fun p => Y ^ α / (p : ℝ)
  have hS₀_inner : ∀ S₀ ∈ SmallS₀,
      ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p) ≤ ∑ p₀ ∈ P₀ S₀, f_obj ((∏ p ∈ S₀, p) * p₀) := by
    intro S₀ hS₀
    set d₁ := ∏ p ∈ S₀, p
    have hd₁_pos : 1 ≤ d₁ := Finset.one_le_prod' fun p hp =>
      (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.one_le
    have hd₁_pos_r : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast hd₁_pos
    have hN_div_big : 2 * 10 ^ 9 ≤ N / d₁ := by
      have hd₁_le := hS₀_prod_le S₀ hS₀
      have hdiv_ge : (N : ℝ) ^ ((9 : ℝ) / 10) ≤ (N : ℝ) / (d₁ : ℝ) := by
        rw [le_div_iff₀ hd₁_pos_r]
        calc (N : ℝ) ^ ((9 : ℝ) / 10) * (d₁ : ℝ) ≤ (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) :=
              mul_le_mul_of_nonneg_left hd₁_le (by positivity)
          _ = (N : ℝ) := by rw [← Real.rpow_add hN_pos]; norm_num
      have h2e9 : (2 * 10 ^ 9 : ℝ) ≤ (N : ℝ) / (d₁ : ℝ) := by linarith
      have hmul : (2 * 10 ^ 9 : ℝ) * (d₁ : ℝ) ≤ (N : ℝ) := (le_div_iff₀ hd₁_pos_r).mp h2e9
      have hnat : 2 * 10 ^ 9 * d₁ ≤ N := by exact_mod_cast hmul
      exact (Nat.le_div_iff_mul_le hd₁_pos).mpr hnat
    have hP₀_card := prime_dyadic_div_lower N d₁ hd₁_pos hN_div_big
    have hpt : ∀ p₀ ∈ P₀ S₀,
        (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α ≤ f_obj (d₁ * p₀) := fun p₀ hp₀ =>
      Real.rpow_le_rpow (mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp =>
        hq0 p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)))
        (hp_w_lb S₀ hS₀ p₀ hp₀) (le_of_lt hα0)
    have h4α : (4 : ℝ) ^ α ≤ 4 := by
      calc (4 : ℝ) ^ α ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hα1)
        _ = 4 := Real.rpow_one 4
    have hprod_id : ((d₁ : ℝ) / (4 * (N : ℝ)) * (∏ p ∈ S₀, q p)) ^ α * ((N : ℝ) / (16 * (d₁ : ℝ) * L)) ≥
        ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p) := by
      have hq_prod_nn : 0 ≤ ∏ p ∈ S₀, q p := Finset.prod_nonneg fun p hp =>
        hq0 p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)
      have hsplit : ((d₁ : ℝ) / (4 * (N : ℝ)) * (∏ p ∈ S₀, q p)) ^ α =
          (d₁ : ℝ) ^ α / ((4 : ℝ) ^ α * (N : ℝ) ^ α) * (∏ p ∈ S₀, (q p) ^ α) := by
        rw [Real.mul_rpow (by positivity) hq_prod_nn, Real.div_rpow (le_of_lt hd₁_pos_r) (by positivity),
          Real.mul_rpow (by norm_num) (le_of_lt hN_pos),
          ← Real.finsetProd_rpow S₀ q (fun p hp => hq0 p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)) α]
      have hd₁_comb : (d₁ : ℝ) ^ α / (d₁ : ℝ) * (∏ p ∈ S₀, (q p) ^ α) = ∏ p ∈ S₀, r p := by
        have hd1_rpow : (d₁ : ℝ) ^ α / (d₁ : ℝ) = ∏ p ∈ S₀, ((p : ℝ) ^ α / (p : ℝ)) := by
          have h1 : (d₁ : ℝ) = ∏ p ∈ S₀, (p : ℝ) := by dsimp [d₁]; push_cast; rfl
          rw [h1, ← Real.finsetProd_rpow S₀ (fun p => (p : ℝ)) (fun _ _ => Nat.cast_nonneg _) α,
            ← Finset.prod_div_distrib]
        rw [hd1_rpow, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp_pos : (0 : ℝ) < (p : ℝ) := by
          exact_mod_cast (hP_prop p (Finset.mem_powerset.mp (Finset.mem_filter.mp hS₀).1 hp)).1.pos
        dsimp [q, r]
        rw [Real.div_rpow (by positivity) (le_of_lt hp_pos)]
        have hpα_ne : (p : ℝ) ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp_pos α)
        field_simp [hpα_ne, ne_of_gt hp_pos]
      have hN_comb : (N : ℝ) / (N : ℝ) ^ α = (N : ℝ) ^ (1 - α) := by
        rw [Real.rpow_sub hN_pos, Real.rpow_one]
      rw [hsplit]
      have hrew : ((d₁ : ℝ) ^ α / ((4 : ℝ) ^ α * (N : ℝ) ^ α) * ∏ p ∈ S₀, q p ^ α) *
            ((N : ℝ) / (16 * (d₁ : ℝ) * L)) =
          ((N : ℝ) / (N : ℝ) ^ α) / (16 * (4 : ℝ) ^ α * L) *
            ((d₁ : ℝ) ^ α / (d₁ : ℝ) * ∏ p ∈ S₀, q p ^ α) := by ring
      rw [hrew, hN_comb, hd₁_comb]
      refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by dsimp [r]; positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    calc ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p)
        ≤ (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α * ((N : ℝ) / (16 * (d₁ : ℝ) * L)) := hprod_id
      _ ≤ (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α * ((P₀ S₀).card : ℝ) :=
          mul_le_mul_of_nonneg_left hP₀_card (by positivity)
      _ = ∑ _p₀ ∈ P₀ S₀, (((d₁ : ℝ) / (4 * (N : ℝ))) * (∏ p ∈ S₀, q p)) ^ α := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ p₀ ∈ P₀ S₀, f_obj (d₁ * p₀) := Finset.sum_le_sum hpt
  -- Apply truncated_euler_sum_lower to r(p) = Y^α / p on P
  have hr0 : ∀ p ∈ P, 0 ≤ r p := fun p _ => by dsimp [r]; positivity
  have hr1 : ∀ p ∈ P, r p ≤ 1 := fun p hp => by
    dsimp [r]
    have hY_ge1 : (1 : ℝ) ≤ Y := by dsimp [Y]; exact_mod_cast (Nat.one_le_two_pow (n := J))
    have hYa_le : Y ^ α ≤ Y := by
      calc Y ^ α ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY_ge1 (le_of_lt hα1)
        _ = Y := Real.rpow_one Y
    have hp_ge : Y ≤ (p : ℝ) := by dsimp [Y]; exact_mod_cast le_of_lt (hP_prop p hp).2.1
    exact (div_le_one (by exact_mod_cast (hP_prop p hp).1.pos)).mpr (le_trans hYa_le hp_ge)
  have hrlog : ∑ p ∈ P, r p * Real.log (p : ℝ) ≤ (L / 10) / 2 := by
    have hY_ge1 : (1 : ℝ) ≤ Y := by dsimp [Y]; exact_mod_cast (Nat.one_le_two_pow (n := J))
    have hr_le_q : ∀ p ∈ P, r p ≤ q p / 2 := fun p hp => by
      dsimp [r, q]
      have hY_pos : 0 < Y := by dsimp [Y]; positivity
      have h2Y : 2 * Y ^ α ≤ Y := by
        have hY_ge : (16 : ℝ) ≤ Y := by
          dsimp [Y]
          have : 16 ≤ 2 ^ J := le_trans (by norm_num : 16 ≤ 2 ^ 30) (Nat.pow_le_pow_right (by norm_num) hJ30)
          exact_mod_cast this
        have h2_le : (2 : ℝ) ≤ Y ^ ((1 : ℝ) / 4) := by
          have hpow4 : (2 : ℝ) ^ (4 : ℕ) ≤ (Y ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := by
            rw [← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul (le_of_lt hY_pos)]
            norm_num; exact hY_ge
          by_contra hgt; push Not at hgt
          have : (Y ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) < (2 : ℝ) ^ (4 : ℕ) :=
            pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
          linarith
        have hsplit : Y = Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_add hY_pos]; norm_num
        have hYα : Y ^ α ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hY_ge1 hα34
        calc 2 * Y ^ α ≤ Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) :=
              mul_le_mul h2_le hYα (by positivity) (by positivity)
          _ = Y := hsplit.symm
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hP_prop p hp).1.pos
      rw [div_div, div_le_div_iff₀ hp_pos (by positivity)]
      nlinarith
    calc ∑ p ∈ P, r p * Real.log (p : ℝ)
        ≤ ∑ p ∈ P, (q p / 2) * Real.log (p : ℝ) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hr_le_q p hp) (hlogp_nn p hp)
      _ = (∑ p ∈ P, q p * Real.log (p : ℝ)) / 2 := by rw [Finset.sum_div]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ (L / 10) / 2 := by linarith
  have heuler := truncated_euler_sum_lower P r (L / 10) (fun p hp => (hP_prop p hp).1.two_le) hr0 hr1 (by linarith) hrlog
  have hsum_r_lb : (1 : ℝ) / 16 * Y ^ α ≤ ∑ p ∈ P, r p := by
    have hrew : ∑ p ∈ P, r p = Y ^ α * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by dsimp [r]; ring
    rw [hrew]
    have := hsum_inv.1
    nlinarith [Real.rpow_nonneg (show 0 ≤ Y by positivity) α]
  calc ((N : ℝ) ^ (1 - α) / (128 * L)) * Real.exp ((1 : ℝ) / 32 * Y ^ α)
      = ((N : ℝ) ^ (1 - α) / (64 * L)) * ((1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ((1 : ℝ) / 16 * Y ^ α))) := by
        rw [show (1 : ℝ) / 32 * Y ^ α = (1 : ℝ) / 2 * ((1 : ℝ) / 16 * Y ^ α) by ring]; ring
    _ ≤ ((N : ℝ) ^ (1 - α) / (64 * L)) * ((1 : ℝ) / 2 * Real.exp ((1 : ℝ) / 2 * ∑ p ∈ P, r p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)) (by positivity)
    _ ≤ ((N : ℝ) ^ (1 - α) / (64 * L)) * ∑ S₀ ∈ SmallS₀, ∏ p ∈ S₀, r p :=
        mul_le_mul_of_nonneg_left heuler (by positivity)
    _ = ∑ S₀ ∈ SmallS₀, ((N : ℝ) ^ (1 - α) / (64 * L)) * (∏ p ∈ S₀, r p) := by rw [Finset.mul_sum]
    _ ≤ ∑ S₀ ∈ SmallS₀, ∑ p₀ ∈ P₀ S₀, f_obj ((∏ p ∈ S₀, p) * p₀) := Finset.sum_le_sum hS₀_inner
    _ = ∑ x ∈ Pairs, f_obj (φ x) := (Finset.sum_sigma SmallS₀ P₀ (fun x => f_obj (φ x))).symm
    _ = ∑ d ∈ Pairs.image φ, f_obj d := (Finset.sum_image (fun x₁ hx₁ x₂ hx₂ hEq => hinj_D hx₁ hx₂ hEq)).symm
    _ ≤ ∑ d ∈ Finset.Ioc (N / 2) N, f_obj d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_D fun d _ _ => hf_nn d

/-! ### Section 5: Shared Elementary Helpers & All Four Headline Barrier Theorems -/

/-- Auxiliary asymptotic inequalities for `N ≥ Nat.ceil (Real.exp (Real.exp 200))`. -/
private lemma large_N_barrier_bounds (N : ℕ)
    (hN : Nat.ceil (Real.exp (Real.exp 200)) ≤ N) :
    let L := Real.log (N : ℝ)
    let LL := Real.log L
    200 ≤ LL ∧ LL ^ 8 ≤ L / 160 ∧ (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10) ∧
    (4 : ℝ) * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) ∧ LL ^ 2 ≤ (L / LL) ^ ((1 : ℝ) / 2) := by
  intro L LL
  have hN_ge_exp : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN_ge_exp
  have hL_ge_exp : Real.exp 200 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hN_ge_exp
    rwa [Real.log_exp] at this
  have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL_ge_exp
  have hLL : 200 ≤ LL := by
    have := Real.log_le_log (Real.exp_pos _) hL_ge_exp
    rwa [Real.log_exp] at this
  have hexp_LL : Real.exp LL = L := Real.exp_log hL_pos
  have hexp_L : Real.exp L = (N : ℝ) := Real.exp_log hN_pos
  -- LL^11 / 11! ≤ exp LL = L ⟹ LL^8 ≤ L / 160 (since 200^3 / 11! = 8e6 / 39916800 ... wait: use LL^12 / 12! or LL^10 / 10! * 160!)
  -- Check: 160 * 10! = 580,608,000; 200^4 = 1,600,000,000 > 580,608,000! Wait: 10 + 4 = 14? No: 160 * 10! vs LL^2:
  -- Check 12! = 479,001,600; LL^4 ≥ 200^4 = 1.6e9; 160 * 12! = 7.66e10; LL^5 ≥ 200^5 = 3.2e11 > 7.66e10!
  -- Actually LL^13 / 13! ≤ L: 13! = 6,227,020,800; 160 * 13! = 9.96e11; 200^5 = 3.2e11 < 9.96e11.
  -- Just use LL^10 / 10! ≤ L? No: (LL/2)^9 / 9! ≤ exp(LL/2), so LL^8 ≤ L / 160 is EASY via (LL^8) * 160 ≤ LL^12 / 12! * ...
  -- Check k = 12: LL^12 / 12! ≤ L, and 160 * 12! = 76,640,256,000, while LL^4 = 1.6e9 < 7.66e10.
  -- Check k = 14: 14! = 8.7178e10, 160 * 14! = 1.3948e13, while 200^6 = 6.4e13 > 1.3948e13!! YES!!
  have hLL8 : LL ^ 8 ≤ L / 160 := by
    have hsum := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ LL) 15
    have h14 : LL ^ 14 / ((14 : ℕ).factorial : ℝ) ≤
        ∑ i ∈ Finset.range 15, LL ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => LL ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
    have hfac14 : ((14 : ℕ).factorial : ℝ) = 87178291200 := by norm_num
    rw [hfac14] at h14
    have hle : LL ^ 14 / 87178291200 ≤ L := by linarith
    have hLL6 : (160 : ℝ) * 87178291200 ≤ LL ^ 6 := by
      have : (200 : ℝ) ^ 6 ≤ LL ^ 6 := pow_le_pow_left₀ (by norm_num) hLL 6
      linarith
    have hLL8_nn : 0 ≤ LL ^ 8 := by positivity
    have h14_eq : LL ^ 14 = LL ^ 8 * LL ^ 6 := by ring
    nlinarith
  have hL_ge : (10 : ℝ) ^ 18 ≤ L := by
    have : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
    linarith
  have hN910 : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [Real.rpow_def_of_pos hN_pos]
    have h1 : (2 : ℝ) * 10 ^ 9 ≤ 1 + L * ((9 : ℝ) / 10) := by linarith
    linarith [Real.add_one_le_exp (L * ((9 : ℝ) / 10))]
  have h4L2 : (4 : ℝ) * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hN_pos]
    have hsum := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ L * ((1 : ℝ) / 2)) 4
    have h3 : (L * ((1 : ℝ) / 2)) ^ 3 / ((3 : ℕ).factorial : ℝ) ≤
        ∑ i ∈ Finset.range 4, (L * ((1 : ℝ) / 2)) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (L * ((1 : ℝ) / 2)) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
    have hfac3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfac3] at h3
    nlinarith [sq_nonneg L]
  have hLL2_sq : LL ^ 2 ≤ (L / LL) ^ ((1 : ℝ) / 2) := by
    have hLL5 : LL ^ 5 ≤ L := by
      have hLL3 : (1 : ℝ) ≤ LL ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hLL 3]
      have hLL5_nn : 0 ≤ LL ^ 5 := by positivity
      have : LL ^ 8 = LL ^ 5 * LL ^ 3 := by ring
      nlinarith
    have hpow2 : (LL ^ 2) ^ (2 : ℕ) ≤ ((L / LL) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((L / LL) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [le_div_iff₀ (by linarith)]
      nlinarith [show (LL ^ 2) ^ 2 * LL = LL ^ 5 by ring]
    by_contra hgt; push Not at hgt
    have : ((L / LL) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) < (LL ^ 2) ^ (2 : ℕ) :=
      pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
    linarith
  exact ⟨hLL, hLL8, hN910, h4L2, hLL2_sq⟩

/-- Elementary binomial lower bound: for `2 * k ≤ n`, `((n : ℝ) / (2 * (k : ℝ))) ^ k ≤ Nat.choose n k`
(with `1 ≤ k`). -/
private lemma nat_choose_lower (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((n : ℝ) / (2 * (k : ℝ))) ^ k ≤ (Nat.choose n k : ℝ) := by
  have hnat : (n - k) ^ k ≤ Nat.choose n k * k.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    have haux : ∀ r : ℕ, r ≤ n → (n - r) ^ r ≤ n.descFactorial r := by
      intro r hr; induction r with
      | zero => simp
      | succ m ih =>
        rw [Nat.descFactorial_succ, pow_succ]
        have h1 : (n - (m + 1)) ^ m ≤ (n - m) ^ m := Nat.pow_le_pow_left (by omega) m
        calc (n - (m + 1)) ^ m * (n - (m + 1))
            ≤ (n - m) ^ m * (n - m) := Nat.mul_le_mul h1 (by omega)
          _ ≤ n.descFactorial m * (n - m) := Nat.mul_le_mul_right _ (ih (by omega))
          _ = (n - m) * n.descFactorial m := mul_comm _ _
    exact haux k (by omega)
  have hfac_le : k.factorial ≤ k ^ k := by
    have haux : ∀ m : ℕ, m ≤ k → m.factorial ≤ k ^ m := by
      intro m hm; induction m with
      | zero => simp
      | succ r ih =>
        rw [Nat.factorial_succ, pow_succ]
        calc (r + 1) * r.factorial ≤ k * k ^ r := Nat.mul_le_mul (by omega) (ih (by omega))
          _ = k ^ r * k := mul_comm _ _
    exact haux k (le_refl k)
  have h2nk : n ≤ 2 * (n - k) := by omega
  have hnat2 : n ^ k ≤ (2 * k) ^ k * Nat.choose n k := by
    calc n ^ k ≤ (2 * (n - k)) ^ k := Nat.pow_le_pow_left h2nk k
      _ = 2 ^ k * (n - k) ^ k := mul_pow 2 (n - k) k
      _ ≤ 2 ^ k * (Nat.choose n k * k.factorial) := Nat.mul_le_mul_left _ hnat
      _ ≤ 2 ^ k * (Nat.choose n k * k ^ k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfac_le)
      _ = (2 * k) ^ k * Nat.choose n k := by rw [mul_pow]; ring
  have hr : (n : ℝ) ^ k ≤ (2 * (k : ℝ)) ^ k * (Nat.choose n k : ℝ) := by exact_mod_cast hnat2
  have hden_pos : (0 : ℝ) < (2 * (k : ℝ)) ^ k := by positivity
  rw [div_pow, div_le_iff₀ hden_pos]
  linarith

/-- **BARRIER THEOREM 1 (Exact `2/3` Unabsorbed Minimax Wall):**
There exist `c > 0` and `N₀ : ℕ` such that for every `N ≥ N₀`, setting `H := ⌊N^(4/3)⌋`,
every set-theoretic cover `Finset.Ioc (N / 2) N ⊆ idx.biUnion S` satisfies
```
∑ α ∈ idx, κ(S α, H)^(2/3) * |S α|^(1/3) ≥ N^(1/3) * exp (c * (log N / log log N)^(2/3)).
``` -/
theorem barrier1_unabsorbed_two_thirds :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
        Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
        (N : ℝ) ^ ((1 : ℝ) / 3) *
          Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((2 : ℝ) / 3)) ≤
          ∑ α ∈ idx,
            (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
              ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  refine ⟨(1 : ℝ) / 4000, by norm_num, Nat.ceil (Real.exp (Real.exp 200)), fun N hN => ?_⟩
  intro H ι idx S hcover
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  obtain ⟨hLL, hLL8, hN910, h4L2, hLL2_sq⟩ := large_N_barrier_bounds N hN
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  change 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) at h4L2
  change LL ^ 2 ≤ (L / LL) ^ ((1 : ℝ) / 2) at hLL2_sq
  have hL_pos : 0 < L := by
    have : (1 : ℝ) ≤ LL ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) hLL 8]
    linarith
  have hLL_pos : 0 < LL := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    exact lt_of_lt_of_le (Real.exp_pos _) this
  let X_fl := Nat.floor (L / (160 * LL))
  have hX_ge : 2 ^ 30 ≤ X_fl := by
    have h1 : ((2 ^ 30 : ℕ) : ℝ) ≤ L / (160 * LL) := by
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      have hdiv : LL ^ 7 ≤ L / (160 * LL) := by
        rw [le_div_iff₀ (by positivity)]
        have : LL ^ 8 = LL ^ 7 * LL := by ring
        nlinarith
      push_cast; linarith
    exact Nat.le_floor h1
  let J := Nat.log 2 X_fl
  have hJ30 : 30 ≤ J := Nat.le_log_of_pow_le (by norm_num) hX_ge
  have h2J_le : ((2 ^ J : ℕ) : ℝ) ≤ L / (160 * LL) := by
    have h1 : 2 ^ J ≤ X_fl := Nat.pow_log_le_self 2 (by omega)
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
  have hJ_le : (J : ℝ) ≤ 2 * LL := by
    have h1 : (2 : ℝ) ^ J ≤ L := le_trans (by simpa using h2J_le)
      (by rw [div_le_iff₀ (by positivity)]; nlinarith)
    have hlg := Real.log_le_log (pow_pos (by norm_num) J) h1
    rw [Real.log_pow] at hlg
    nlinarith [half_le_log_two]
  have hY_budget : 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ) ≤ (1 : ℝ) / 10 * L := by
    calc 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ)
        ≤ 8 * (L / (160 * LL)) * (2 * LL) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2J_le (by norm_num)) hJ_le (Nat.cast_nonneg _) (by positivity)
      _ = (1 : ℝ) / 10 * L := by field_simp [ne_of_gt hLL_pos]; ring
  have hY_sq : ((2 ^ (2 * J) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : ((2 ^ (2 * J) : ℕ) : ℝ) = ((2 ^ J : ℕ) : ℝ) ^ 2 := by
      rw [mul_comm, pow_mul]; push_cast; ring
    have h2J_le_L : ((2 ^ J : ℕ) : ℝ) ≤ L := le_trans h2J_le (by rw [div_le_iff₀ (by positivity)]; nlinarith)
    rw [h1]
    calc ((2 ^ J : ℕ) : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) h2J_le_L 2
      _ ≤ (4 : ℝ) * L ^ 2 := by nlinarith [sq_nonneg L]
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := h4L2
  have hlogN100 : 100 ≤ L := by
    have : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
    linarith
  obtain ⟨w, hw_nn, hw_sum, hw_lb⟩ := unified_random_tilt_lower N J ((2 : ℝ) / 3)
    (by norm_num) (by norm_num) hJ30 hY_budget hY_sq hN910 hlogN100
  have hpart := partition_lower_two_thirds (Finset.Ioc (N / 2) N) H w hw_nn hw_sum idx S hcover
  refine le_trans ?_ (le_trans hw_lb hpart)
  -- Show (N^(1/3) / (128 * L)) * exp ((1/32) * (2^J)^(2/3)) ≥ N^(1/3) * exp ((1/4000) * (L/LL)^(2/3))
  have h2J_ge : (L / LL) / 640 ≤ ((2 ^ J : ℕ) : ℝ) := by
    have hlt : X_fl < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) X_fl
    have hfl : L / (160 * LL) - 1 < (X_fl : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have h1 : L / (320 * LL) ≤ L / (160 * LL) - 1 := by
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      have : LL ^ 7 ≤ L / (160 * LL) := by rw [le_div_iff₀ (by positivity)]; nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
      have : L / (320 * LL) = (L / (160 * LL)) / 2 := by ring
      linarith
    have h2 : ((2 ^ (J + 1) : ℕ) : ℝ) = 2 * ((2 ^ J : ℕ) : ℝ) := by rw [pow_succ]; push_cast; ring
    have h3 : (X_fl : ℝ) < 2 * ((2 ^ J : ℕ) : ℝ) := by rw [← h2]; exact_mod_cast hlt
    have : (L / LL) / 640 = (L / (320 * LL)) / 2 := by ring
    linarith
  have h2J_23 : (1 : ℝ) / 75 * (L / LL) ^ ((2 : ℝ) / 3) ≤ ((2 ^ J : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
    have h1 := Real.rpow_le_rpow (by positivity) h2J_ge (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [Real.div_rpow (by positivity) (by norm_num)] at h1
    have h640 : (640 : ℝ) ^ ((2 : ℝ) / 3) ≤ 75 := by
      have hpow3 : ((640 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) ≤ (75 : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast ((640 : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]; norm_num
      by_contra hgt; push Not at hgt
      have : (75 : ℝ) ^ (3 : ℕ) < ((640 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) :=
        pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
      linarith
    have hdiv : (L / LL) ^ ((2 : ℝ) / 3) / 75 ≤ (L / LL) ^ ((2 : ℝ) / 3) / (640 : ℝ) ^ ((2 : ℝ) / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h640
    linarith
  have h128L : (128 * L : ℝ) ≤ Real.exp (2 * LL) := by
    have h128 : (128 : ℝ) ≤ Real.exp LL := by linarith [Real.add_one_le_exp LL]
    calc 128 * L = 128 * Real.exp LL := by rw [Real.exp_log hL_pos]
      _ ≤ Real.exp LL * Real.exp LL := mul_le_mul_of_nonneg_right h128 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (2 * LL) := by rw [← Real.exp_add]; congr 1; ring
  have hE23_ge : LL ^ 3 ≤ (L / LL) ^ ((2 : ℝ) / 3) := by
    have hLL3 : LL ^ 3 ≤ (L / LL) ^ ((1 : ℝ) / 2) := by
      have hsq : (LL ^ 3) ^ 2 ≤ L / LL := by
        rw [le_div_iff₀ hLL_pos]
        have h1 : (LL ^ 3) ^ 2 * LL = LL ^ 7 := by ring
        have h2 : LL ^ 8 = LL ^ 7 * LL := by ring
        nlinarith [pow_nonneg (le_of_lt hLL_pos) 7]
      have h1 := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_natCast (LL ^ 3) 2, ← Real.rpow_mul (by positivity)] at h1
      norm_num at h1; exact h1
    have hratio : 1 ≤ L / LL := by rw [one_le_div hLL_pos]; nlinarith [pow_le_pow_left₀ (by norm_num) hLL 7]
    exact le_trans hLL3 (Real.rpow_le_rpow_of_exponent_le hratio (by norm_num))
  have h2LL_le : 2 * LL ≤ (1 : ℝ) / 20000 * (L / LL) ^ ((2 : ℝ) / 3) := by
    have hLL2 : (200 : ℝ) ^ 2 ≤ LL ^ 2 := pow_le_pow_left₀ (by norm_num) hLL 2
    have h3 : LL ^ 3 = LL * LL ^ 2 := by ring
    nlinarith
  have hexp_diff : 2 * LL + (1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3) ≤
      (1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
    nlinarith
  have h1m : (1 : ℝ) - (2 : ℝ) / 3 = (1 : ℝ) / 3 := by norm_num
  rw [h1m]
  rw [div_mul_eq_mul_div (a := (N : ℝ) ^ ((1 : ℝ) / 3)), le_div_iff₀ (by positivity)]
  calc (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp ((1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3)) * (128 * L)
      ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp ((1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3)) * Real.exp (2 * LL) :=
        mul_le_mul_of_nonneg_left h128L (by positivity)
    _ = (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp (2 * LL + (1 : ℝ) / 4000 * (L / LL) ^ ((2 : ℝ) / 3)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)

/-- **BARRIER THEOREM 2a (Exact `1/2` Absorbed Minimax Wall, Even With `K₁ ≡ 1`):**
There exist `c > 0` and `N₀ : ℕ` such that for every `N ≥ N₀`, setting `H := ⌊N^(4/3)⌋`,
every set-theoretic cover `Finset.Ioc (N / 2) N ⊆ idx.biUnion S` satisfies
```
∑ α ∈ idx, κ(S α, H)^(1/3) * |S α|^(1/3) ≥ N^(1/3) * exp (c * (log N / log log N)^(1/2)).
``` -/
theorem barrier2a_absorbed_half :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
        Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
        (N : ℝ) ^ ((1 : ℝ) / 3) *
          Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 2)) ≤
          ∑ α ∈ idx,
            (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
              ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  refine ⟨(1 : ℝ) / 2000, by norm_num, Nat.ceil (Real.exp (Real.exp 200)), fun N hN => ?_⟩
  intro H ι idx S hcover
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  obtain ⟨hLL, hLL8, hN910, h4L2, hLL2_sq⟩ := large_N_barrier_bounds N hN
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  change 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) at h4L2
  change LL ^ 2 ≤ (L / LL) ^ ((1 : ℝ) / 2) at hLL2_sq
  have hL_pos : 0 < L := by
    have : (1 : ℝ) ≤ LL ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) hLL 8]
    linarith
  have hLL_pos : 0 < LL := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    exact lt_of_lt_of_le (Real.exp_pos _) this
  let X_fl := Nat.floor (L / (160 * LL))
  have hX_ge : 2 ^ 30 ≤ X_fl := by
    have h1 : ((2 ^ 30 : ℕ) : ℝ) ≤ L / (160 * LL) := by
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      have hdiv : LL ^ 7 ≤ L / (160 * LL) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
      push_cast; linarith
    exact Nat.le_floor h1
  let J := Nat.log 2 X_fl
  have hJ30 : 30 ≤ J := Nat.le_log_of_pow_le (by norm_num) hX_ge
  have h2J_le : ((2 ^ J : ℕ) : ℝ) ≤ L / (160 * LL) := by
    have h1 : 2 ^ J ≤ X_fl := Nat.pow_log_le_self 2 (by omega)
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
  have hJ_le : (J : ℝ) ≤ 2 * LL := by
    have h1 : (2 : ℝ) ^ J ≤ L := le_trans (by simpa using h2J_le)
      (by rw [div_le_iff₀ (by positivity)]; nlinarith)
    have hlg := Real.log_le_log (pow_pos (by norm_num) J) h1
    rw [Real.log_pow] at hlg
    nlinarith [half_le_log_two]
  have hY_budget : 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ) ≤ (1 : ℝ) / 10 * L := by
    calc 8 * ((2 ^ J : ℕ) : ℝ) * (J : ℝ)
        ≤ 8 * (L / (160 * LL)) * (2 * LL) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2J_le (by norm_num)) hJ_le (Nat.cast_nonneg _) (by positivity)
      _ = (1 : ℝ) / 10 * L := by field_simp [ne_of_gt hLL_pos]; ring
  have hY_sq : ((2 ^ (2 * J) : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : ((2 ^ (2 * J) : ℕ) : ℝ) = ((2 ^ J : ℕ) : ℝ) ^ 2 := by
      rw [mul_comm, pow_mul]; push_cast; ring
    have h2J_le_L : ((2 ^ J : ℕ) : ℝ) ≤ L := le_trans h2J_le (by rw [div_le_iff₀ (by positivity)]; nlinarith)
    rw [h1]
    calc ((2 ^ J : ℕ) : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) h2J_le_L 2
      _ ≤ (4 : ℝ) * L ^ 2 := by nlinarith [sq_nonneg L]
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := h4L2
  have hlogN100 : 100 ≤ L := by
    have : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
    linarith
  obtain ⟨w, hw_nn, hw_sum, hw_lb⟩ := unified_random_tilt_lower N J ((1 : ℝ) / 2)
    (by norm_num) (by norm_num) hJ30 hY_budget hY_sq hN910 hlogN100
  have hpart := partition_lower_half (Finset.Ioc (N / 2) N) H w hw_nn hw_sum idx S hcover
  have hw_lb23 := Real.rpow_le_rpow (by positivity) hw_lb (by norm_num : (0 : ℝ) ≤ 2 / 3)
  refine le_trans ?_ (le_trans hw_lb23 hpart)
  have h2J_ge : (L / LL) / 640 ≤ ((2 ^ J : ℕ) : ℝ) := by
    have hlt : X_fl < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) X_fl
    have hfl : L / (160 * LL) - 1 < (X_fl : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have h1 : L / (320 * LL) ≤ L / (160 * LL) - 1 := by
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      have : LL ^ 7 ≤ L / (160 * LL) := by rw [le_div_iff₀ (by positivity)]; nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
      have : L / (320 * LL) = (L / (160 * LL)) / 2 := by ring
      linarith
    have h2 : ((2 ^ (J + 1) : ℕ) : ℝ) = 2 * ((2 ^ J : ℕ) : ℝ) := by rw [pow_succ]; push_cast; ring
    have h3 : (X_fl : ℝ) < 2 * ((2 ^ J : ℕ) : ℝ) := by rw [← h2]; exact_mod_cast hlt
    have : (L / LL) / 640 = (L / (320 * LL)) / 2 := by ring
    linarith
  have h2J_12 : (1 : ℝ) / 26 * (L / LL) ^ ((1 : ℝ) / 2) ≤ ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 := Real.rpow_le_rpow (by positivity) h2J_ge (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.div_rpow (by positivity) (by norm_num)] at h1
    have h640 : (640 : ℝ) ^ ((1 : ℝ) / 2) ≤ 26 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
    have hdiv : (L / LL) ^ ((1 : ℝ) / 2) / 26 ≤ (L / LL) ^ ((1 : ℝ) / 2) / (640 : ℝ) ^ ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h640
    linarith
  have h128L : (128 * L : ℝ) ≤ Real.exp (2 * LL) := by
    have h128 : (128 : ℝ) ≤ Real.exp LL := by linarith [Real.add_one_le_exp LL]
    calc 128 * L = 128 * Real.exp LL := by rw [Real.exp_log hL_pos]
      _ ≤ Real.exp LL * Real.exp LL := mul_le_mul_of_nonneg_right h128 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (2 * LL) := by rw [← Real.exp_add]; congr 1; ring
  have h1m : (1 : ℝ) - (1 : ℝ) / 2 = (1 : ℝ) / 2 := by norm_num
  rw [h1m]
  have hstep : (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) ≤
      (N : ℝ) ^ ((1 : ℝ) / 2) / (128 * L) * Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) := by
    rw [div_mul_eq_mul_div (a := (N : ℝ) ^ ((1 : ℝ) / 2)), le_div_iff₀ (by positivity)]
    have hexp_diff : 2 * LL + (3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2) ≤
        (1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      have hLL3 : LL ^ 3 ≤ (L / LL) ^ ((1 : ℝ) / 2) := by
        have hsq : (LL ^ 3) ^ 2 ≤ L / LL := by
          rw [le_div_iff₀ hLL_pos]
          have h1 : (LL ^ 3) ^ 2 * LL = LL ^ 7 := by ring
          have h2 : LL ^ 8 = LL ^ 7 * LL := by ring
          nlinarith [pow_nonneg (le_of_lt hLL_pos) 7]
        have h1 := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [← Real.rpow_natCast (LL ^ 3) 2, ← Real.rpow_mul (by positivity)] at h1
        norm_num at h1; exact h1
      have hLL2 : (200 : ℝ) ^ 2 ≤ LL ^ 2 := pow_le_pow_left₀ (by norm_num) hLL 2
      have h3 : LL ^ 3 = LL * LL ^ 2 := by ring
      have h2LL_le : 2 * LL ≤ (1 : ℝ) / 20000 * (L / LL) ^ ((1 : ℝ) / 2) := by nlinarith
      nlinarith
    calc (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) * (128 * L)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) * Real.exp (2 * LL) :=
          mul_le_mul_of_nonneg_left h128L (by positivity)
      _ = (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp (2 * LL + (3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 32 * ((2 ^ J : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)
  have hpow := Real.rpow_le_rpow (by positivity) hstep (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [Real.mul_rpow (by positivity) (le_of_lt (Real.exp_pos _)),
    ← Real.rpow_mul (le_of_lt hN_pos), ← Real.exp_mul] at hpow
  have h13 : (1 : ℝ) / 2 * ((2 : ℝ) / 3) = (1 : ℝ) / 3 := by norm_num
  have h2000 : (3 : ℝ) / 4000 * (L / LL) ^ ((1 : ℝ) / 2) * ((2 : ℝ) / 3) =
      (1 : ℝ) / 2000 * (L / LL) ^ ((1 : ℝ) / 2) := by ring
  rw [h13, h2000] at hpow
  exact hpow

/-- Elementary symmetric reciprocal sum lower bound:
`∑ S ∈ B.powersetCard k, ∏ p ∈ S, (1 / p) ≥ (μ - k / p_min)^k / k!`
when every `p ∈ B` satisfies `p_min ≤ p` (`p_min > 0`) and `μ := ∑ p ∈ B, 1/p ≥ k / p_min`. -/
private lemma elem_symm_inv_lower (B : Finset ℕ) (p_min : ℝ) (hp_min : 0 < p_min)
    (hB : ∀ p ∈ B, p_min ≤ (p : ℝ)) (k : ℕ)
    (hμ_ge : (k : ℝ) / p_min ≤ ∑ p ∈ B, (1 : ℝ) / (p : ℝ)) :
    ((∑ p ∈ B, (1 : ℝ) / (p : ℝ)) - (k : ℝ) / p_min) ^ k / (k.factorial : ℝ) ≤
      ∑ S ∈ B.powersetCard k, ∏ p ∈ S, (1 : ℝ) / (p : ℝ) := by
  classical
  set μ := ∑ p ∈ B, (1 : ℝ) / (p : ℝ)
  induction k with
  | zero => simp
  | succ m ih =>
    have hμ_m : (m : ℝ) / p_min ≤ μ := by
      have : (m : ℝ) / p_min ≤ ((m + 1 : ℕ) : ℝ) / p_min :=
        div_le_div_of_nonneg_right (by push_cast; linarith) (le_of_lt hp_min)
      linarith
    have hih := ih hμ_m
    -- Double count pairs (S, p) with S ∈ B.powersetCard m and p ∈ B \ S
    have hdouble : ((m + 1 : ℕ) : ℝ) * ∑ T ∈ B.powersetCard (m + 1), ∏ q ∈ T, (1 : ℝ) / (q : ℝ) =
        ∑ S ∈ B.powersetCard m, (∏ q ∈ S, (1 : ℝ) / (q : ℝ)) * ∑ p ∈ B \ S, (1 : ℝ) / (p : ℝ) := by
      have hL : ((m + 1 : ℕ) : ℝ) * ∑ T ∈ B.powersetCard (m + 1), ∏ q ∈ T, (1 : ℝ) / (q : ℝ) =
          ∑ T ∈ B.powersetCard (m + 1), ∑ p ∈ T, ∏ q ∈ T, (1 : ℝ) / (q : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun T hT => ?_
        rw [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hT).2]
      rw [hL]
      have hR : ∑ S ∈ B.powersetCard m, (∏ q ∈ S, (1 : ℝ) / (q : ℝ)) * ∑ p ∈ B \ S, (1 : ℝ) / (p : ℝ) =
          ∑ S ∈ B.powersetCard m, ∑ p ∈ B \ S, ∏ q ∈ insert p S, (1 : ℝ) / (q : ℝ) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.prod_insert (Finset.mem_sdiff.mp hp).2, mul_comm]
      rw [hR]
      -- Bijection between {(T, p) | T ∈ powersetCard (m+1), p ∈ T} and {(S, p) | S ∈ powersetCard m, p ∈ B \ S}
      calc ∑ T ∈ B.powersetCard (m + 1), ∑ _p ∈ T, ∏ q ∈ T, (1 : ℝ) / (q : ℝ)
          = ∑ x ∈ (B.powersetCard (m + 1)).sigma id, ∏ q ∈ x.1, (1 : ℝ) / (q : ℝ) :=
            (Finset.sum_sigma (B.powersetCard (m + 1)) id (fun x => ∏ q ∈ x.1, (1 : ℝ) / (q : ℝ))).symm
        _ = ∑ y ∈ (B.powersetCard m).sigma (fun S => B \ S), ∏ q ∈ insert y.2 y.1, (1 : ℝ) / (q : ℝ) := by
            refine Finset.sum_bij (fun x _ => ⟨x.1.erase x.2, x.2⟩) ?_ ?_ ?_ ?_
            · intro x hx
              have hT := Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hx).1
              have hpT : x.2 ∈ x.1 := (Finset.mem_sigma.mp hx).2
              refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans (Finset.erase_subset _ _) hT.1, ?_⟩,
                Finset.mem_sdiff.mpr ⟨hT.1 hpT, Finset.notMem_erase _ _⟩⟩
              dsimp only; rw [Finset.card_erase_of_mem hpT, hT.2]; omega
            · intro ⟨T₁, p₁⟩ hx₁ ⟨T₂, p₂⟩ hx₂ hEq
              simp only [Sigma.mk.inj_iff, heq_eq_eq] at hEq
              rcases hEq with ⟨her, rfl⟩
              have h1 : p₁ ∈ T₁ := (Finset.mem_sigma.mp hx₁).2
              have h2 : p₁ ∈ T₂ := (Finset.mem_sigma.mp hx₂).2
              have hT_eq : T₁ = T₂ := by
                rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, her]
              subst hT_eq; rfl
            · intro y hy
              have hS := Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hy).1
              have hpBS := Finset.mem_sdiff.mp (Finset.mem_sigma.mp hy).2
              refine ⟨⟨insert y.2 y.1, y.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr
                ⟨Finset.insert_subset hpBS.1 hS.1, by rw [Finset.card_insert_of_notMem hpBS.2, hS.2]⟩,
                Finset.mem_insert_self _ _⟩, ?_⟩
              simp only [Finset.erase_insert hpBS.2]
            · intro x hx
              have hpT : x.2 ∈ x.1 := (Finset.mem_sigma.mp hx).2
              dsimp only; rw [Finset.insert_erase hpT]
        _ = ∑ S ∈ B.powersetCard m, ∑ p ∈ B \ S, ∏ q ∈ insert p S, (1 : ℝ) / (q : ℝ) :=
            Finset.sum_sigma (B.powersetCard m) (fun S => B \ S) (fun y => ∏ q ∈ insert y.2 y.1, (1 : ℝ) / (q : ℝ))
    have hrem_lb : ∀ S ∈ B.powersetCard m, μ - ((m + 1 : ℕ) : ℝ) / p_min ≤ ∑ p ∈ B \ S, (1 : ℝ) / (p : ℝ) := by
      intro S hS
      have hSB := (Finset.mem_powersetCard.mp hS).1
      have hScard := (Finset.mem_powersetCard.mp hS).2
      have hsplit : ∑ p ∈ B \ S, (1 : ℝ) / (p : ℝ) + ∑ p ∈ S, (1 : ℝ) / (p : ℝ) = μ :=
        Finset.sum_sdiff hSB
      have hS_ub : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ (m : ℝ) / p_min := by
        calc ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
            ≤ ∑ _p ∈ S, (1 : ℝ) / p_min := Finset.sum_le_sum fun p hp =>
              one_div_le_one_div_of_le hp_min (hB p (hSB hp))
          _ = (m : ℝ) / p_min := by rw [Finset.sum_const, hScard, nsmul_eq_mul, mul_one_div]
      have hm1 : (m : ℝ) / p_min ≤ ((m + 1 : ℕ) : ℝ) / p_min :=
        div_le_div_of_nonneg_right (by push_cast; linarith) (le_of_lt hp_min)
      linarith
    have hbase_nn : 0 ≤ μ - ((m + 1 : ℕ) : ℝ) / p_min := by linarith
    have hbase_le : μ - ((m + 1 : ℕ) : ℝ) / p_min ≤ μ - (m : ℝ) / p_min := by
      have : (m : ℝ) / p_min ≤ ((m + 1 : ℕ) : ℝ) / p_min :=
        div_le_div_of_nonneg_right (by push_cast; linarith) (le_of_lt hp_min)
      linarith
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hfac_eq : (((m + 1).factorial : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; rfl
    rw [hfac_eq, div_le_iff₀ (by positivity)]
    calc (μ - ((m + 1 : ℕ) : ℝ) / p_min) ^ (m + 1)
        = (μ - ((m + 1 : ℕ) : ℝ) / p_min) ^ m * (μ - ((m + 1 : ℕ) : ℝ) / p_min) := pow_succ _ m
      _ ≤ (μ - (m : ℝ) / p_min) ^ m * (μ - ((m + 1 : ℕ) : ℝ) / p_min) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase_nn hbase_le m) hbase_nn
      _ ≤ ((∑ S ∈ B.powersetCard m, ∏ p ∈ S, (1 : ℝ) / (p : ℝ)) * (m.factorial : ℝ)) *
            (μ - ((m + 1 : ℕ) : ℝ) / p_min) := by
          have := (div_le_iff₀ (by positivity : (0 : ℝ) < (m.factorial : ℝ))).mp hih
          exact mul_le_mul_of_nonneg_right this hbase_nn
      _ = (m.factorial : ℝ) * ∑ S ∈ B.powersetCard m,
            (∏ p ∈ S, (1 : ℝ) / (p : ℝ)) * (μ - ((m + 1 : ℕ) : ℝ) / p_min) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ (m.factorial : ℝ) * ∑ S ∈ B.powersetCard m,
            (∏ p ∈ S, (1 : ℝ) / (p : ℝ)) * ∑ p ∈ B \ S, (1 : ℝ) / (p : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S hS =>
            mul_le_mul_of_nonneg_left (hrem_lb S hS) (Finset.prod_nonneg fun _ _ => by positivity)) (by positivity)
      _ = (∑ T ∈ B.powersetCard (m + 1), ∏ q ∈ T, (1 : ℝ) / (q : ℝ)) * (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)) := by
          rw [← hdouble]; ring

/-- Lower bound on `q_U(d₁ * q)` for an arithmetic progression `U = {T₁ * j : 1 ≤ j ≤ M}`
when `d₁ ∣ T₁`, `T₁ ≥ 1`, `q ≥ 1`, and `2 * q ≤ M` (`M ≥ 2`):
`1 / (18 * q) ≤ q_U(d₁ * q)`. -/
private lemma qU_prog_lower (T₁ M d₁ q : ℕ) (hT₁ : 1 ≤ T₁) (hM : 2 ≤ M)
    (hd₁ : d₁ ∣ T₁) (hq1 : 1 ≤ q) (h2q : 2 * q ≤ M) :
    let U := (Finset.Icc 1 M).image (fun j => T₁ * j)
    (1 : ℝ) / (18 * (q : ℝ)) ≤
      (∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ ∧ d₁ * q ∣ (if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂) then (1 : ℝ) else 0) /
        (U.card : ℝ) ^ 2 := by
  intro U
  have hinj_T : Function.Injective (fun j => T₁ * j) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hT₁ h
  have hU_card : U.card = M := by
    dsimp [U]; rw [Finset.card_image_of_injective _ hinj_T]; simp
  rw [hU_card]
  have hrew : ∑ z₁ ∈ U, ∑ z₂ ∈ U,
        (if z₁ ≠ z₂ ∧ d₁ * q ∣ (if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂) then (1 : ℝ) else 0) =
      ∑ j₁ ∈ Finset.Icc 1 M, ∑ j₂ ∈ Finset.Icc 1 M,
        (if j₁ ≠ j₂ ∧ d₁ * q ∣ (if j₁ ≤ j₂ then T₁ * (j₂ - j₁) else T₁ * (j₁ - j₂)) then (1 : ℝ) else 0) := by
    dsimp only [U]
    rw [Finset.sum_image (fun _ _ _ _ h => hinj_T h)]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_image (fun _ _ _ _ h => hinj_T h)]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    have hne_iff : T₁ * j₁ ≠ T₁ * j₂ ↔ j₁ ≠ j₂ := ⟨fun h heq => h (congrArg _ heq), fun h heq => h (hinj_T heq)⟩
    have hle_iff : T₁ * j₁ ≤ T₁ * j₂ ↔ j₁ ≤ j₂ := Nat.mul_le_mul_left_iff hT₁
    by_cases hle : j₁ ≤ j₂
    · have hle' : T₁ * j₁ ≤ T₁ * j₂ := hle_iff.mpr hle
      simp only [hne_iff, hle, hle', ↓reduceIte, Nat.mul_sub_left_distrib]
    · have hle' : ¬ T₁ * j₁ ≤ T₁ * j₂ := fun h => hle (hle_iff.mp h)
      simp only [hne_iff, hle, hle', ↓reduceIte, Nat.mul_sub_left_distrib]
  rw [hrew]
  -- Count ordered pairs (j₁, j₂) with 1 ≤ j₁ ≤ M/2 and j₂ = j₁ + k * q for 1 ≤ k ≤ (M/2)/q
  let A := Finset.Icc 1 (M / 2)
  let K := Finset.Icc 1 ((M / 2) / q)
  have hmaps : ∀ p ∈ A ×ˢ K,
      (p.1, p.1 + p.2 * q) ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun x => x.1 ≠ x.2 ∧ d₁ * q ∣ (if x.1 ≤ x.2 then T₁ * (x.2 - x.1) else T₁ * (x.1 - x.2))) := by
    intro ⟨j₁, k⟩ hp
    have hj₁ := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
    have hk := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
    have hkq_le : k * q ≤ M / 2 := le_trans (Nat.mul_le_mul_right q hk.2) (Nat.div_mul_le_self (M / 2) q)
    have hj₂_le : j₁ + k * q ≤ M := by omega
    have hle : j₁ ≤ j₁ + k * q := Nat.le_add_right _ _
    have hne : j₁ ≠ j₁ + k * q := by have : 1 ≤ k * q := Nat.mul_pos hk.1 hq1; omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hj₁.1, by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega, hj₂_le⟩⟩, hne, ?_⟩
    rw [if_pos hle, Nat.add_sub_cancel_left]
    rcases hd₁ with ⟨c, hc⟩
    exact ⟨c * k, by rw [hc]; ring⟩
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1, p.1 + p.2 * q)) ((A ×ˢ K : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro ⟨a₁, k₁⟩ _ ⟨a₂, k₂⟩ _ hEq
    rcases Prod.mk.inj hEq with ⟨rfl, h2⟩
    dsimp only at h2
    have : k₁ * q = k₂ * q := by omega
    have := Nat.eq_of_mul_eq_mul_right hq1 this
    subst this; rfl
  have hcard_lb : A.card * K.card ≤
      (((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun x => x.1 ≠ x.2 ∧ d₁ * q ∣ (if x.1 ≤ x.2 then T₁ * (x.2 - x.1) else T₁ * (x.1 - x.2)))).card := by
    rw [← Finset.card_product]
    exact Finset.card_le_card_of_injOn _ hmaps hinj
  have hsum_eq_card :
      ∑ j₁ ∈ Finset.Icc 1 M, ∑ j₂ ∈ Finset.Icc 1 M,
        (if j₁ ≠ j₂ ∧ d₁ * q ∣ (if j₁ ≤ j₂ then T₁ * (j₂ - j₁) else T₁ * (j₁ - j₂)) then (1 : ℝ) else 0) =
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun x => x.1 ≠ x.2 ∧ d₁ * q ∣ (if x.1 ≤ x.2 then T₁ * (x.2 - x.1) else T₁ * (x.1 - x.2)))).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => by split_ifs <;> simp
  rw [hsum_eq_card]
  have hA_ge : (M : ℝ) / 3 ≤ (A.card : ℝ) := by
    have h1 : A.card = M / 2 := by simp [A]
    rw [h1]
    have : M ≤ 3 * (M / 2) := by omega
    have : (M : ℝ) ≤ 3 * ((M / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hK_ge : (M : ℝ) / (6 * (q : ℝ)) ≤ (K.card : ℝ) := by
    have h1 : K.card = (M / 2) / q := by simp [K]
    rw [h1]
    have hq_le : q ≤ M / 2 := by omega
    have hK1 : 1 ≤ (M / 2) / q := (Nat.le_div_iff_mul_le hq1).mpr (by simpa using hq_le)
    have hmod := Nat.div_add_mod (M / 2) q; have hlt := Nat.mod_lt (M / 2) hq1
    have h2 : M / 2 ≤ 2 * q * ((M / 2) / q) := by nlinarith
    have h3 : M ≤ 3 * (M / 2) := by omega
    have h4 : M ≤ 6 * q * ((M / 2) / q) := by nlinarith
    have h5 : (M : ℝ) ≤ (6 * (q : ℝ)) * (((M / 2) / q : ℕ) : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h4; push_cast at this; linarith
    exact (div_le_iff₀' (by positivity)).mpr h5
  have hAK_r : (A.card : ℝ) * (K.card : ℝ) ≤
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun x => x.1 ≠ x.2 ∧ d₁ * q ∣ (if x.1 ≤ x.2 then T₁ * (x.2 - x.1) else T₁ * (x.1 - x.2)))).card : ℝ) := by
    exact_mod_cast hcard_lb
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : (M : ℝ) ^ 2 / (18 * (q : ℝ)) ≤ (A.card : ℝ) * (K.card : ℝ) := by
    calc (M : ℝ) ^ 2 / (18 * (q : ℝ)) = ((M : ℝ) / 3) * ((M : ℝ) / (6 * (q : ℝ))) := by ring
      _ ≤ (A.card : ℝ) * (K.card : ℝ) := mul_le_mul hA_ge hK_ge (by positivity) (by positivity)
  have hle_tot := le_trans hprod hAK_r
  have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 18 * (q : ℝ))).mp hle_tot
  linarith

/-- Prime-factorization count in `B₀` for a squarefree product `(∏ r ∈ S₀, r) * q` where
`S₀ ⊆ B₀` consists of primes and `q ∉ B₀` is prime. -/
private lemma sum_factorization_prod_primes_mul_prime (B₀ S₀ : Finset ℕ) (q : ℕ)
    (hB₀ : ∀ p ∈ B₀, p.Prime) (hS₀ : S₀ ⊆ B₀) (hq : q.Prime) (hq_not : q ∉ B₀) :
    ∑ p ∈ B₀, ((∏ r ∈ S₀, r) * q).factorization p = S₀.card := by
  classical
  have hprod_ne : (∏ r ∈ S₀, r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r hr => (hB₀ r (hS₀ hr)).ne_zero
  have hq_ne : q ≠ 0 := hq.ne_zero
  have hterm : ∀ p ∈ B₀, ((∏ r ∈ S₀, r) * q).factorization p = if p ∈ S₀ then 1 else 0 := by
    intro p hp
    rw [Nat.factorization_mul hprod_ne hq_ne, Finsupp.coe_add, Pi.add_apply]
    have hq_zero : q.factorization p = 0 := by
      rw [hq.factorization, Finsupp.single_apply]
      have hne : q ≠ p := fun h => hq_not (h ▸ hp)
      simp [hne]
    rw [hq_zero, add_zero]
    rw [Nat.factorization_prod (fun r hr => (hB₀ r (hS₀ hr)).ne_zero), Finsupp.coe_finsetSum,
      Finset.sum_apply]
    have hinner : ∀ r ∈ S₀, r.factorization p = if r = p then 1 else 0 := fun r hr => by
      rw [(hB₀ r (hS₀ hr)).factorization, Finsupp.single_apply]
    rw [Finset.sum_congr rfl hinner]
    by_cases hpS : p ∈ S₀
    · simp [hpS]
    · simp [hpS]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hfilt : B₀.filter (fun p => p ∈ S₀) = S₀ := by
    ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hS₀ h, h⟩⟩
  rw [hfilt, Finset.sum_const, smul_eq_mul, mul_one]

/-- Exact double-counting identity relating `κ_bar(S, U)` to `∑ d ∈ S, q_U(d)`. -/
private lemma sum_qU_eq_kappa_bar (S U : Finset ℕ) :
    ∑ d ∈ S,
      ((∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ ∧ d ∣ (if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂) then (1 : ℝ) else 0) /
        (U.card : ℝ) ^ 2) =
    (∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
        ((S.filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
      else 0) / (U.card : ℝ) ^ 2 := by
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z₂ _ => ?_
  by_cases hne : z₁ = z₂
  · simp [hne]
  · simp [hne]

/-- **BARRIER THEOREM 2b (Single Prime-Count Slice `ℓ²`-Average `1/2` Wall):**
There exist `c > 0` and `N₀ : ℕ` such that for every `N ≥ N₀`, setting `H := ⌊N^(4/3)⌋`,
there exist a finite set of primes `B₀`, a prime-count `k : ℕ`, and a subset `U ⊆ [1, H]`
with `|U| = |S_k|` (where `S_k = {d ∈ (N/2, N] : ∑_{p ∈ B₀} v_p(d) = k}`), such that
```
κ_bar(S_k, U)^(1/3) * |S_k|^(1/3) ≥ N^(1/3) * exp (c * (log N / log log N)^(1/2)).
``` -/
theorem barrier2b_single_slice_avg_half :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∃ B₀ : Finset ℕ, (∀ p ∈ B₀, p.Prime) ∧ ∃ k : ℕ,
        let S := (Finset.Ioc (N / 2) N).filter (fun d => ∑ p ∈ B₀, d.factorization p = k)
        ∃ U : Finset ℕ,
          U ⊆ Finset.Icc 1 H ∧
          U.Nonempty ∧
          U.card = S.card ∧
          (N : ℝ) ^ ((1 : ℝ) / 3) *
            Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 2)) ≤
            ((∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
                ((S.filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
              else 0) / (U.card : ℝ) ^ 2) ^ ((1 : ℝ) / 3) *
              (S.card : ℝ) ^ ((1 : ℝ) / 3) := by
  classical
  refine ⟨(1 : ℝ) / 1500, by norm_num, Nat.ceil (Real.exp (Real.exp 200)), fun N hN => ?_⟩
  intro H
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  obtain ⟨hLL, hLL8, hN910, h4L2, hLL2_sq⟩ := large_N_barrier_bounds N hN
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  change 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) at h4L2
  change LL ^ 2 ≤ (L / LL) ^ ((1 : ℝ) / 2) at hLL2_sq
  have hN_ge_exp : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by linarith [Real.add_one_le_exp (Real.exp 200), Real.exp_pos (200 : ℝ)]
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN_ge_exp
  have hLL_pos : 0 < LL := by linarith
  have hLL8_ge : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
  have hL_ge : (160 : ℝ) * (200 : ℝ) ^ 8 ≤ L := by linarith
  have hL_pos : 0 < L := by linarith
  have h1000LL : 10000 * LL ≤ (L / LL) ^ ((1 : ℝ) / 2) := by
    have hsq : (10000 * LL) ^ 2 ≤ L / LL := by
      rw [le_div_iff₀ hLL_pos]
      have hLL5 : (200 : ℝ) ^ 5 ≤ LL ^ 5 := pow_le_pow_left₀ (by norm_num) hLL 5
      have h1 : (10000 * LL) ^ 2 * LL = 10 ^ 8 * LL ^ 3 := by ring
      have h2 : LL ^ 8 = LL ^ 3 * LL ^ 5 := by ring
      nlinarith [pow_nonneg (le_of_lt hLL_pos) 3]
    have h1 := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_natCast (10000 * LL) 2, ← Real.rpow_mul (by positivity)] at h1
    norm_num at h1; exact h1
  -- Set J_lo = Nat.log 2 ⌊L⌋ + 1 so L < 2^J_lo ≤ 2 * L and 2^(2 * J_lo) ≤ 4 * L^2 ≤ N^(1/2)
  let J_lo := Nat.log 2 (Nat.floor L) + 1
  have hL_fl_ge : 2 ^ 30 ≤ Nat.floor L := Nat.le_floor (by push_cast; linarith)
  have hJ_lo30 : 30 ≤ J_lo := by
    have := Nat.le_log_of_pow_le (by norm_num) hL_fl_ge
    omega
  have h2Jlo_gt_L : L < ((2 ^ J_lo : ℕ) : ℝ) := by
    have h1 : Nat.floor L < 2 ^ J_lo := Nat.lt_pow_succ_log_self (by norm_num) (Nat.floor L)
    have h2 : Nat.floor L + 1 ≤ 2 ^ J_lo := by omega
    have h3 : L < (Nat.floor L : ℝ) + 1 := Nat.lt_floor_add_one L
    have h4 : (Nat.floor L : ℝ) + 1 ≤ ((2 ^ J_lo : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have h2Jlo_le_2L : ((2 ^ J_lo : ℕ) : ℝ) ≤ 2 * L := by
    have h1 : 2 ^ (Nat.log 2 (Nat.floor L)) ≤ Nat.floor L := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ J_lo : ℕ) : ℝ) = 2 * ((2 ^ (Nat.log 2 (Nat.floor L)) : ℕ) : ℝ) := by
      dsimp [J_lo]; rw [pow_succ]; push_cast; ring
    have h3 : ((2 ^ (Nat.log 2 (Nat.floor L)) : ℕ) : ℝ) ≤ L := le_trans (by exact_mod_cast h1) (Nat.floor_le (le_of_lt hL_pos))
    linarith
  have h2_2Jlo_le : ((2 ^ (2 * J_lo) : ℕ) : ℝ) ≤ 4 * L ^ 2 := by
    have h1 : ((2 ^ (2 * J_lo) : ℕ) : ℝ) = ((2 ^ J_lo : ℕ) : ℝ) ^ 2 := by
      rw [mul_comm, pow_mul]; push_cast; ring
    rw [h1]
    have h2 := pow_le_pow_left₀ (by positivity) h2Jlo_le_2L 2
    linarith
  let B₀ := P_win J_lo
  have hB₀_pr : ∀ p ∈ B₀, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hμ₀ := sum_inv_primes_win_bounds J_lo hJ_lo30
  -- Choose A ⊆ A_pool = (2^J_lo, 2 * 2^J_lo] ∩ Primes of cardinality R₀ = ⌊L / (16 * LL)⌋
  let A_pool := (Finset.Ioc (2 ^ J_lo) (2 * 2 ^ J_lo)).filter Nat.Prime
  have hApool_sub : A_pool ⊆ B₀ := by
    intro p hp
    have hI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have h2le : 2 * 2 ^ J_lo ≤ 2 ^ (2 * J_lo) := by
      rw [show 2 * 2 ^ J_lo = 2 ^ (J_lo + 1) by rw [pow_succ]; ring]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hI.1, le_trans hI.2 h2le⟩, (Finset.mem_filter.mp hp).2⟩
  have h2Jlo_ge109 : 10 ^ 9 ≤ 2 ^ J_lo := le_trans (by norm_num : 10 ^ 9 ≤ 2 ^ 30) (Nat.pow_le_pow_right (by norm_num) hJ_lo30)
  have hApool_card : L / (8 * LL) ≤ (A_pool.card : ℝ) := by
    have hcheb := prime_dyadic_card_lower (2 ^ J_lo) h2Jlo_ge109
    have hlog_le : Real.log (2 * ((2 ^ J_lo : ℕ) : ℝ)) ≤ 2 * LL := by
      have hle : 2 * ((2 ^ J_lo : ℕ) : ℝ) ≤ 4 * L := by linarith
      have h1 := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (ne_of_gt hL_pos)] at h1
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith [log_two_le_one]
      linarith
    have hlog_pos : 0 < Real.log (2 * ((2 ^ J_lo : ℕ) : ℝ)) :=
      Real.log_pos (by linarith [h2Jlo_gt_L, hL_ge])
    calc L / (8 * LL) = L / (4 * (2 * LL)) := by ring
      _ ≤ ((2 ^ J_lo : ℕ) : ℝ) / (4 * Real.log (2 * ((2 ^ J_lo : ℕ) : ℝ))) :=
          div_le_div₀ (by positivity) (le_of_lt h2Jlo_gt_L) (by positivity) (by linarith)
      _ ≤ (A_pool.card : ℝ) := hcheb
  let R₀ := Nat.floor (L / (16 * LL))
  have hR₀_le_real : (R₀ : ℝ) ≤ L / (16 * LL) := Nat.floor_le (by positivity)
  have hR₀_ge_real : L / (32 * LL) ≤ (R₀ : ℝ) := by
    have hfl : L / (16 * LL) - 1 < (R₀ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have hbig : 1 ≤ L / (32 * LL) := by
      rw [one_le_div (by positivity)]
      have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
      nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
    have : L / (16 * LL) = 2 * (L / (32 * LL)) := by ring
    linarith
  have hR₀_le_Apool : R₀ ≤ A_pool.card := by
    have : (R₀ : ℝ) ≤ (A_pool.card : ℝ) := by
      calc (R₀ : ℝ) ≤ L / (16 * LL) := hR₀_le_real
        _ ≤ L / (8 * LL) := by
            have : 0 ≤ L / (16 * LL) := by positivity
            have : L / (8 * LL) = 2 * (L / (16 * LL)) := by ring
            linarith
        _ ≤ (A_pool.card : ℝ) := hApool_card
    exact_mod_cast this
  obtain ⟨A, hA_sub_pool, hA_card⟩ := Finset.exists_subset_card_eq hR₀_le_Apool
  have hA_sub_B₀ : A ⊆ B₀ := Finset.Subset.trans hA_sub_pool hApool_sub
  let T₁ := ∏ p ∈ A, p
  have hT₁_pos : 1 ≤ T₁ := Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => (hB₀_pr p (hA_sub_B₀ hp)).ne_zero)
  have hT₁_le_N18 : (T₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
    have hlogT : Real.log (T₁ : ℝ) ≤ L / 8 := by
      rw [Nat.cast_prod, Real.log_prod (fun p hp => ne_of_gt (by exact_mod_cast (hB₀_pr p (hA_sub_B₀ hp)).pos))]
      have hper : ∀ p ∈ A, Real.log (p : ℝ) ≤ 2 * LL := fun p hp => by
        have hp_le : (p : ℝ) ≤ 4 * L := by
          have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hA_sub_pool hp)).1).2
          have : (p : ℝ) ≤ 2 * ((2 ^ J_lo : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        have h1 := Real.log_le_log (by exact_mod_cast (hB₀_pr p (hA_sub_B₀ hp)).pos) hp_le
        rw [Real.log_mul (by norm_num) (ne_of_gt hL_pos)] at h1
        have hlog4 : Real.log 4 ≤ 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith [log_two_le_one]
        linarith
      calc ∑ p ∈ A, Real.log (p : ℝ)
          ≤ ∑ _p ∈ A, (2 * LL) := Finset.sum_le_sum hper
        _ = (R₀ : ℝ) * (2 * LL) := by rw [Finset.sum_const, hA_card, nsmul_eq_mul]
        _ ≤ (L / (16 * LL)) * (2 * LL) := mul_le_mul_of_nonneg_right hR₀_le_real (by positivity)
        _ = L / 8 := by field_simp [ne_of_gt hLL_pos]; ring
    have hT_pos_r : (0 : ℝ) < (T₁ : ℝ) := by exact_mod_cast hT₁_pos
    calc (T₁ : ℝ) = Real.exp (Real.log (T₁ : ℝ)) := (Real.exp_log hT_pos_r).symm
      _ ≤ Real.exp (L / 8) := Real.exp_le_exp.mpr hlogT
      _ = (N : ℝ) ^ ((1 : ℝ) / 8) := by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring
  -- Choose k = ⌊(1/12) * R₀^(1/2)⌋
  let k := Nat.floor ((1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2))
  have hR₀_sq_ge : (1 : ℝ) / 6 * (L / LL) ^ ((1 : ℝ) / 2) ≤ (R₀ : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 := Real.rpow_le_rpow (by positivity) hR₀_ge_real (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hrew : L / (32 * LL) = (L / LL) / 32 := by ring
    rw [hrew, Real.div_rpow (by positivity) (by norm_num)] at h1
    have h32 : (32 : ℝ) ^ ((1 : ℝ) / 2) ≤ 6 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
    have hdiv : (L / LL) ^ ((1 : ℝ) / 2) / 6 ≤ (L / LL) ^ ((1 : ℝ) / 2) / (32 : ℝ) ^ ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h32
    linarith
  have hk_le : (k : ℝ) ≤ (1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2) := Nat.floor_le (by positivity)
  have hk_ge : (1 / 144 : ℝ) * (L / LL) ^ ((1 : ℝ) / 2) ≤ (k : ℝ) := by
    have hfl : (1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2) - 1 < (k : ℝ) :=
      sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have h1 : (1 / 72 : ℝ) * (L / LL) ^ ((1 : ℝ) / 2) ≤ (1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2) := by linarith
    have h2 : 1 ≤ (1 / 144 : ℝ) * (L / LL) ^ ((1 : ℝ) / 2) := by linarith
    linarith
  have hk_ge_6LL : 6 * LL ≤ (k : ℝ) := by linarith
  have hk_pos : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have h2k_le_R₀ : 2 * k ≤ R₀ := by
    have hsq : (R₀ : ℝ) ^ ((1 : ℝ) / 2) ≤ (R₀ : ℝ) := by
      have hR1 : (1 : ℝ) ≤ (R₀ : ℝ) := by
        have : (1 : ℝ) ≤ L / (32 * LL) := by
          rw [one_le_div (by positivity)]
          have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
          nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
        linarith
      calc (R₀ : ℝ) ^ ((1 : ℝ) / 2) ≤ (R₀ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
        _ = (R₀ : ℝ) := Real.rpow_one _
    have : (2 * k : ℝ) ≤ (R₀ : ℝ) := by linarith
    exact_mod_cast this
  have h32k_le_halfL : 32 * (k : ℝ) ≤ L / 2 := by
    have hsq : (64 * (k : ℝ)) ^ 2 ≤ L ^ 2 := by
      have hk2 : (k : ℝ) ^ 2 ≤ (R₀ : ℝ) := by
        have h1 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le 2
        have h2 : ((R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (R₀ : ℝ) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
        nlinarith [show ((1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (1 / 144) * ((R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 by ring]
      have hR_le_L : (R₀ : ℝ) ≤ L := le_trans hR₀_le_real (by rw [div_le_iff₀ (by positivity)]; nlinarith)
      nlinarith
    nlinarith
  have hk_div_2Jlo : (k : ℝ) / ((2 ^ J_lo : ℕ) : ℝ) ≤ 1 / 32 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- Define S := S_k = {d ∈ (N/2, N] | ∑ p ∈ B₀, v_p(d) = k}
  refine ⟨B₀, hB₀_pr, k, ?_⟩
  intro S
  -- Key property for ANY S₀ ∈ B₀.powersetCard k: d₁ = ∏ S₀ ≤ N^(1/10), and every q ∈ P₀ S₀ gives d₁ * q ∈ S
  let P₀ : Finset ℕ → Finset ℕ := fun S₀ =>
    let d₁ := ∏ p ∈ S₀, p
    (Finset.Ioc (N / (2 * d₁)) (N / d₁)).filter Nat.Prime
  have hS₀_d₁_bounds : ∀ S₀ ∈ B₀.powersetCard k,
      let d₁ := ∏ p ∈ S₀, p
      1 ≤ d₁ ∧ (d₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) ∧ 2 * 10 ^ 9 ≤ N / d₁ := by
    intro S₀ hS₀ d₁
    have hS₀B := (Finset.mem_powersetCard.mp hS₀).1
    have hS₀c := (Finset.mem_powersetCard.mp hS₀).2
    have hd₁_pos : 1 ≤ d₁ := Nat.one_le_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun p hp => (hB₀_pr p (hS₀B hp)).ne_zero)
    have hlog_d₁ : Real.log (d₁ : ℝ) ≤ L / 10 := by
      dsimp [d₁]
      rw [Nat.cast_prod, Real.log_prod (fun p hp => ne_of_gt (by exact_mod_cast (hB₀_pr p (hS₀B hp)).pos))]
      have hper : ∀ p ∈ S₀, Real.log (p : ℝ) ≤ 3 * LL := fun p hp => by
        have hp_le : (p : ℝ) ≤ 4 * L ^ 2 := by
          have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hS₀B hp)).1).2
          exact le_trans (by exact_mod_cast this) h2_2Jlo_le
        have h1 := Real.log_le_log (by exact_mod_cast (hB₀_pr p (hS₀B hp)).pos) hp_le
        rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hL_pos 2)), Real.log_pow] at h1
        push_cast at h1
        have hlog4 : Real.log 4 ≤ 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith [log_two_le_one]
        linarith
      have h30LL : (30 * LL * (k : ℝ)) ^ 2 ≤ L ^ 2 := by
        have hk2 : (k : ℝ) ^ 2 ≤ (R₀ : ℝ) := by
          have h1 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le 2
          have h2 : ((R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (R₀ : ℝ) := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
          nlinarith [show ((1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (1 / 144) * ((R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 by ring]
        have hstep : 900 * LL ^ 2 * (R₀ : ℝ) ≤ L ^ 2 := by
          have h1 : 900 * LL ^ 2 * (R₀ : ℝ) ≤ 900 * LL ^ 2 * (L / (16 * LL)) :=
            mul_le_mul_of_nonneg_left hR₀_le_real (by positivity)
          have h2 : 900 * LL ^ 2 * (L / (16 * LL)) = (900 / 16 : ℝ) * LL * L := by
            field_simp [ne_of_gt hLL_pos]
          have h3 : (900 / 16 : ℝ) * LL ≤ L := by
            have hLL7 : (200 : ℝ) ^ 7 ≤ LL ^ 7 := pow_le_pow_left₀ (by norm_num) hLL 7
            nlinarith [show LL ^ 8 = LL ^ 7 * LL by ring]
          nlinarith
        have : (30 * LL * (k : ℝ)) ^ 2 = 900 * LL ^ 2 * (k : ℝ) ^ 2 := by ring
        nlinarith
      have h3LLk : (k : ℝ) * (3 * LL) ≤ L / 10 := by nlinarith
      calc ∑ p ∈ S₀, Real.log (p : ℝ)
          ≤ ∑ _p ∈ S₀, (3 * LL) := Finset.sum_le_sum hper
        _ = (k : ℝ) * (3 * LL) := by rw [Finset.sum_const, hS₀c, nsmul_eq_mul]
        _ ≤ L / 10 := h3LLk
    have hd₁_le : (d₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := by
      have hd₁_pos_r : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast hd₁_pos
      calc (d₁ : ℝ) = Real.exp (Real.log (d₁ : ℝ)) := (Real.exp_log hd₁_pos_r).symm
        _ ≤ Real.exp (L / 10) := Real.exp_le_exp.mpr hlog_d₁
        _ = (N : ℝ) ^ ((1 : ℝ) / 10) := by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring
    have hdiv_ge : 2 * 10 ^ 9 ≤ N / d₁ := by
      have hdiv_r : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) / (d₁ : ℝ) := by
        have hsplit : (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) = (N : ℝ) := by
          rw [← Real.rpow_add hN_pos]; norm_num
        rw [le_div_iff₀ (by exact_mod_cast hd₁_pos)]
        calc (2 : ℝ) * 10 ^ 9 * (d₁ : ℝ)
            ≤ (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) :=
              mul_le_mul hN910 hd₁_le (by positivity) (by positivity)
          _ = (N : ℝ) := hsplit
      have hnat_mul : 2 * 10 ^ 9 * d₁ ≤ N := by
        have := (le_div_iff₀ (by exact_mod_cast hd₁_pos : (0 : ℝ) < (d₁ : ℝ))).mp hdiv_r
        exact_mod_cast this
      exact (Nat.le_div_iff_mul_le hd₁_pos).mpr hnat_mul
    exact ⟨hd₁_pos, hd₁_le, hdiv_ge⟩
  have hmem_S : ∀ S₀ ∈ B₀.powersetCard k, ∀ q ∈ P₀ S₀,
      2 ^ (2 * J_lo) < q ∧ (∏ p ∈ S₀, p) * q ∈ S := by
    intro S₀ hS₀ q hq
    obtain ⟨hd₁_pos, hd₁_le, hdiv_ge⟩ := hS₀_d₁_bounds S₀ hS₀
    set d₁ := ∏ p ∈ S₀, p
    have hqI : N / (2 * d₁) < q ∧ q ≤ N / d₁ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2
    have hq_gt_win : 2 ^ (2 * J_lo) < q := by
      have hN12_lt : (N : ℝ) ^ ((1 : ℝ) / 2) < (N : ℝ) / (2 * (d₁ : ℝ)) - 1 := by
        have hN_gt : (4 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by
          have h1 : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) ^ ((9 : ℝ) / 10) := hN910
          have hpow9 : (4 : ℝ) ^ (9 : ℕ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 5)) ^ (9 : ℕ) := by
            rw [← Real.rpow_natCast ((N : ℝ) ^ ((2 : ℝ) / 5)) 9, ← Real.rpow_mul (le_of_lt hN_pos)]
            have h2 : (2 : ℝ) / 5 * (9 : ℕ) = ((9 : ℝ) / 10) * (4 : ℕ) := by norm_num
            rw [h2, Real.rpow_mul (le_of_lt hN_pos), Real.rpow_natCast]
            calc (4 : ℝ) ^ (9 : ℕ) ≤ ((2 : ℝ) * 10 ^ 9) ^ (4 : ℕ) := by norm_num
              _ ≤ ((N : ℝ) ^ ((9 : ℝ) / 10)) ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) h1 4
          by_contra hlt; push Not at hlt
          have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 9 ≠ 0)
          linarith
        have hN12_ge4 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          have : (4 : ℝ) * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := h4L2
          nlinarith [sq_nonneg (L - 1)]
        have hdiv : (N : ℝ) ^ ((9 : ℝ) / 10) ≤ (N : ℝ) / (d₁ : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast hd₁_pos)]
          have hsplit : (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) = (N : ℝ) := by
            rw [← Real.rpow_add hN_pos]; norm_num
          calc (N : ℝ) ^ ((9 : ℝ) / 10) * (d₁ : ℝ)
              ≤ (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) :=
                mul_le_mul_of_nonneg_left hd₁_le (by positivity)
            _ = (N : ℝ) := hsplit
        have hprod : (N : ℝ) ^ ((9 : ℝ) / 10) = (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((2 : ℝ) / 5) := by
          rw [← Real.rpow_add hN_pos]; norm_num
        have : (N : ℝ) / (2 * (d₁ : ℝ)) = ((N : ℝ) / (d₁ : ℝ)) / 2 := by ring
        nlinarith
      have hdiv_floor : (N : ℝ) / (2 * (d₁ : ℝ)) - 1 < ((N / (2 * d₁) : ℕ) : ℝ) := by
        have hmod := Nat.div_add_mod N (2 * d₁)
        have hlt := Nat.mod_lt N (by omega : 0 < 2 * d₁)
        have hnat : N < 2 * d₁ * (N / (2 * d₁) + 1) := by nlinarith
        have hr : (N : ℝ) < (2 * (d₁ : ℝ)) * (((N / (2 * d₁) : ℕ) : ℝ) + 1) := by
          have := (Nat.cast_lt (α := ℝ)).mpr hnat; push_cast at this; linarith
        have := (div_lt_iff₀' (by exact_mod_cast (by omega : 0 < 2 * d₁) : (0 : ℝ) < 2 * (d₁ : ℝ))).mpr hr
        linarith
      have hwin_lt : ((2 ^ (2 * J_lo) : ℕ) : ℝ) < ((N / (2 * d₁) : ℕ) : ℝ) :=
        lt_of_le_of_lt (le_trans h2_2Jlo_le h4L2) (lt_trans hN12_lt hdiv_floor)
      have hwin_nat : 2 ^ (2 * J_lo) < N / (2 * d₁) := by exact_mod_cast hwin_lt
      omega
    have hq_not_B₀ : q ∉ B₀ := fun hmem => by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem).1).2; omega
    have hIoc : d₁ * q ∈ Finset.Ioc (N / 2) N := by
      refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
      · have h1 : N / (2 * d₁) + 1 ≤ q := hqI.1
        have hmod := Nat.div_add_mod N (2 * d₁)
        have hlt := Nat.mod_lt N (by omega : 0 < 2 * d₁)
        have hmul : N < 2 * (d₁ * q) := by nlinarith
        omega
      · exact le_trans (Nat.mul_le_mul_left d₁ hqI.2) (Nat.mul_div_le N d₁)
    have hfac : ∑ p ∈ B₀, (d₁ * q).factorization p = k := by
      rw [sum_factorization_prod_primes_mul_prime B₀ S₀ q hB₀_pr (Finset.mem_powersetCard.mp hS₀).1 hq_pr hq_not_B₀,
        (Finset.mem_powersetCard.mp hS₀).2]
    exact ⟨hq_gt_win, Finset.mem_filter.mpr ⟨hIoc, hfac⟩⟩
  -- Lower bound |S| ≥ (N / (16 * L)) * ((1 / 32)^k / k!)
  let PairsB := (B₀.powersetCard k).sigma P₀
  let φ : (Σ _ : Finset ℕ, ℕ) → ℕ := fun x => (∏ p ∈ x.1, p) * x.2
  have hPairsB_sub : PairsB.image φ ⊆ S := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨⟨S₀, q⟩, hx, rfl⟩
    exact (hmem_S S₀ (Finset.mem_sigma.mp hx).1 q (Finset.mem_sigma.mp hx).2).2
  have hPairsB_inj : Set.InjOn φ (PairsB : Set (Σ _ : Finset ℕ, ℕ)) := by
    intro ⟨S₁, q₁⟩ hx₁ ⟨S₂, q₂⟩ hx₂ hEq
    have h1 := Finset.mem_sigma.mp hx₁
    have h2 := Finset.mem_sigma.mp hx₂
    have hS₁ : ∀ p ∈ S₁, p.Prime ∧ p ≤ 2 ^ (2 * J_lo) := fun p hp =>
      have hpB := (Finset.mem_powersetCard.mp h1.1).1 hp
      ⟨(Finset.mem_filter.mp hpB).2, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpB).1).2⟩
    have hS₂ : ∀ p ∈ S₂, p.Prime ∧ p ≤ 2 ^ (2 * J_lo) := fun p hp =>
      have hpB := (Finset.mem_powersetCard.mp h2.1).1 hp
      ⟨(Finset.mem_filter.mp hpB).2, (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpB).1).2⟩
    have hq₁ : q₁.Prime ∧ 2 ^ (2 * J_lo) < q₁ := ⟨(Finset.mem_filter.mp h1.2).2, (hmem_S S₁ h1.1 q₁ h1.2).1⟩
    have hq₂ : q₂.Prime ∧ 2 ^ (2 * J_lo) < q₂ := ⟨(Finset.mem_filter.mp h2.2).2, (hmem_S S₂ h2.1 q₂ h2.2).1⟩
    obtain ⟨rfl, rfl⟩ := prod_primes_mul_large_prime_inj (2 ^ (2 * J_lo)) hS₁ hS₂ hq₁ hq₂ hEq
    rfl
  have hS_card_lb : ((N : ℝ) / (16 * L)) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ)) ≤ (S.card : ℝ) := by
    have hcard_nat : ∑ S₀ ∈ B₀.powersetCard k, (P₀ S₀).card ≤ S.card := by
      calc ∑ S₀ ∈ B₀.powersetCard k, (P₀ S₀).card = PairsB.card := (Finset.card_sigma _ _).symm
        _ = (PairsB.image φ).card := (Finset.card_image_of_injOn hPairsB_inj).symm
        _ ≤ S.card := Finset.card_le_card hPairsB_sub
    have hcard_r : ∑ S₀ ∈ B₀.powersetCard k, ((P₀ S₀).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hcard_nat
    have helem := elem_symm_inv_lower B₀ ((2 ^ J_lo : ℕ) : ℝ) (by positivity)
      (fun p hp => by exact_mod_cast le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1)
      k (by linarith [hμ₀.1])
    have h32_le : ((1 : ℝ) / 32) ^ k / (k.factorial : ℝ) ≤
        ∑ S₀ ∈ B₀.powersetCard k, ∏ p ∈ S₀, (1 : ℝ) / (p : ℝ) := by
      refine le_trans ?_ helem
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by linarith [hμ₀.1]) k) (by positivity)
    calc ((N : ℝ) / (16 * L)) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ))
        ≤ ((N : ℝ) / (16 * L)) * ∑ S₀ ∈ B₀.powersetCard k, ∏ p ∈ S₀, (1 : ℝ) / (p : ℝ) :=
          mul_le_mul_of_nonneg_left h32_le (by positivity)
      _ = ∑ S₀ ∈ B₀.powersetCard k, (N : ℝ) / (16 * ((∏ p ∈ S₀, p : ℕ) : ℝ) * L) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S₀ _ => ?_
          rw [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]; ring
      _ ≤ ∑ S₀ ∈ B₀.powersetCard k, ((P₀ S₀).card : ℝ) := by
          refine Finset.sum_le_sum fun S₀ hS₀ => ?_
          obtain ⟨hd₁_pos, _, hdiv_ge⟩ := hS₀_d₁_bounds S₀ hS₀
          exact prime_dyadic_div_lower N (∏ p ∈ S₀, p) hd₁_pos hdiv_ge
      _ ≤ (S.card : ℝ) := hcard_r
  -- Construct U := {T₁ * j : 1 ≤ j ≤ S.card}
  let U := (Finset.Icc 1 S.card).image (fun j => T₁ * j)
  -- First show 2 * q ≤ S.card for every S₀ ∈ A.powersetCard k and q ∈ P₀ S₀ (also implies 2 ≤ S.card!)
  have h2q_le_S : ∀ S₀ ∈ A.powersetCard k, ∀ q ∈ P₀ S₀, 2 * q ≤ S.card := by
    intro S₀ hS₀ q hq
    have hS₀A := (Finset.mem_powersetCard.mp hS₀).1
    have hS₀c := (Finset.mem_powersetCard.mp hS₀).2
    have hS₀B : S₀ ∈ B₀.powersetCard k := Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans hS₀A hA_sub_B₀, hS₀c⟩
    obtain ⟨hd₁_pos, _, _⟩ := hS₀_d₁_bounds S₀ hS₀B
    set d₁ := ∏ p ∈ S₀, p
    have hd₁_ge_Lk : L ^ k ≤ (d₁ : ℝ) := by
      dsimp [d₁]; rw [Nat.cast_prod]
      calc L ^ k = ∏ _p ∈ S₀, L := by rw [Finset.prod_const, hS₀c]
        _ ≤ ∏ p ∈ S₀, (p : ℝ) := Finset.prod_le_prod (fun _ _ => le_of_lt hL_pos) fun p hp => by
            have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hA_sub_B₀ (hS₀A hp))).1).1
            exact le_trans (le_of_lt h2Jlo_gt_L) (by exact_mod_cast le_of_lt h1)
    have h2k_ge_32L : 32 * L ≤ (2 : ℝ) ^ k := by
      have h32L : 32 * L ≤ Real.exp (3 * LL) := by
        have h32 : (32 : ℝ) ≤ Real.exp (2 * LL) := by linarith [Real.add_one_le_exp (2 * LL)]
        calc 32 * L = 32 * Real.exp LL := by rw [Real.exp_log hL_pos]
          _ ≤ Real.exp (2 * LL) * Real.exp LL := mul_le_mul_of_nonneg_right h32 (le_of_lt (Real.exp_pos _))
          _ = Real.exp (3 * LL) := by rw [← Real.exp_add]; congr 1; ring
      have h2k : Real.exp ((k : ℝ) / 2) ≤ (2 : ℝ) ^ k := by
        have h1 : Real.exp ((k : ℝ) / 2) = (Real.exp ((1 : ℝ) / 2)) ^ k := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        have h2 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
          have := Real.exp_le_exp.mpr half_le_log_two
          rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
        rw [h1]; exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h2 k
      exact le_trans h32L (le_trans (Real.exp_le_exp.mpr (by linarith)) h2k)
    have hfac_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      have hnat : k.factorial ≤ k ^ k := by
        have haux : ∀ m ≤ k, m.factorial ≤ k ^ m := by
          intro m hm; induction m with
          | zero => simp
          | succ r ihr =>
            rw [Nat.factorial_succ, pow_succ]
            calc (r + 1) * r.factorial ≤ k * k ^ r := Nat.mul_le_mul hm (ihr (by omega))
              _ = k ^ r * k := mul_comm _ _
        exact haux k (le_refl k)
      exact_mod_cast hnat
    have hden_le : 32 * L * (32 : ℝ) ^ k * (k.factorial : ℝ) ≤ L ^ k := by
      calc 32 * L * (32 : ℝ) ^ k * (k.factorial : ℝ)
          ≤ (2 : ℝ) ^ k * (32 : ℝ) ^ k * (k : ℝ) ^ k :=
            mul_le_mul (mul_le_mul_of_nonneg_right h2k_ge_32L (by positivity)) hfac_le (by positivity) (by positivity)
        _ = (2 * (32 * (k : ℝ))) ^ k := by rw [← mul_pow, ← mul_pow]; congr 1; ring
        _ ≤ (2 * (L / 2)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
        _ = L ^ k := by ring
    have hq_le_div : (q : ℝ) ≤ (N : ℝ) / (d₁ : ℝ) := by
      have h1 : d₁ * q ≤ N := le_trans (Nat.mul_le_mul_left d₁ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2) (Nat.mul_div_le N d₁)
      have h2 : (d₁ : ℝ) * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      exact (le_div_iff₀' (by exact_mod_cast hd₁_pos)).mpr h2
    have h2q_r : (2 * q : ℝ) ≤ (S.card : ℝ) := by
      refine le_trans ?_ hS_card_lb
      have hstep : 2 * ((N : ℝ) / (d₁ : ℝ)) ≤ ((N : ℝ) / (16 * L)) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ)) := by
        rw [one_div_pow]
        have hrew : ((N : ℝ) / (16 * L)) * ((1 : ℝ) / (32 : ℝ) ^ k / (k.factorial : ℝ)) =
            (2 * (N : ℝ)) / (32 * L * (32 : ℝ) ^ k * (k.factorial : ℝ)) := by
          field_simp [ne_of_gt hL_pos]; ring
        rw [hrew, show 2 * ((N : ℝ) / (d₁ : ℝ)) = (2 * (N : ℝ)) / (d₁ : ℝ) by ring]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (le_trans hden_le hd₁_ge_Lk)
      linarith
    exact_mod_cast h2q_r
  have hS_ge2 : 2 ≤ S.card := by
    have hA_ne : (A.powersetCard k).Nonempty := by
      rw [← Finset.card_pos, Finset.card_powersetCard, hA_card]
      exact Nat.choose_pos (by omega)
    rcases hA_ne with ⟨S₀, hS₀⟩
    have hS₀B : S₀ ∈ B₀.powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans (Finset.mem_powersetCard.mp hS₀).1 hA_sub_B₀, (Finset.mem_powersetCard.mp hS₀).2⟩
    obtain ⟨hd₁_pos, _, hdiv_ge⟩ := hS₀_d₁_bounds S₀ hS₀B
    have hP₀_pos : 0 < (P₀ S₀).card := by
      have hlb := prime_dyadic_div_lower N (∏ p ∈ S₀, p) hd₁_pos hdiv_ge
      have : (0 : ℝ) < ((P₀ S₀).card : ℝ) := lt_of_lt_of_le (by positivity) hlb
      exact_mod_cast this
    rcases Finset.card_pos.mp hP₀_pos with ⟨q, hq⟩
    have hq2 : 1 ≤ q := (Finset.mem_filter.mp hq).2.one_le
    have := h2q_le_S S₀ hS₀ q hq
    omega
  have hinj_T₁ : Function.Injective (fun j => T₁ * j) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hT₁_pos h
  have hU_card : U.card = S.card := by
    dsimp [U]; rw [Finset.card_image_of_injective _ hinj_T₁]; simp
  have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hU_sub : U ⊆ Finset.Icc 1 H := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨j, hj, rfl⟩
    have hjI := Finset.mem_Icc.mp hj
    have hS_le_N : S.card ≤ N := by
      calc S.card ≤ (Finset.Ioc (N / 2) N).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = N - N / 2 := Nat.card_Ioc _ _
        _ ≤ N := Nat.sub_le _ _
    have hj_le_N : j ≤ N := le_trans hjI.2 hS_le_N
    have hprod_le : ((T₁ * j : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
      push_cast
      have hN18 : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      have hsplit : (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) = (N : ℝ) ^ ((4 : ℝ) / 3) := by
        calc (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ)
            = (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (((1 : ℝ) / 3) + 1) := (Real.rpow_add hN_pos _ _).symm
          _ = (N : ℝ) ^ ((4 : ℝ) / 3) := by norm_num
      calc (T₁ : ℝ) * (j : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) :=
            mul_le_mul hT₁_le_N18 (by exact_mod_cast hj_le_N) (Nat.cast_nonneg _) (by positivity)
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) := mul_le_mul_of_nonneg_right hN18 (le_of_lt hN_pos)
        _ = (N : ℝ) ^ ((4 : ℝ) / 3) := hsplit
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hT₁_pos hjI.1, Nat.le_floor hprod_le⟩
  refine ⟨U, hU_sub, hU_ne, hU_card, ?_⟩
  -- Lower bound κ_bar(S, U) ≥ Nat.choose R₀ k / (288 * L)
  let q_U : ℕ → ℝ := fun d =>
    (∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ ∧ d ∣ (if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂) then (1 : ℝ) else 0) /
      (U.card : ℝ) ^ 2
  have hqU_nn : ∀ d, 0 ≤ q_U d := fun d =>
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) (sq_nonneg _)
  let PairsA := (A.powersetCard k).sigma P₀
  have hPairsA_sub_B : PairsA ⊆ PairsB := by
    intro ⟨S₀, q⟩ hx
    have h1 := Finset.mem_sigma.mp hx
    exact Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans (Finset.mem_powersetCard.mp h1.1).1 hA_sub_B₀,
      (Finset.mem_powersetCard.mp h1.1).2⟩, h1.2⟩
  have hPairsA_img_sub : PairsA.image φ ⊆ S := Finset.Subset.trans (Finset.image_subset_image hPairsA_sub_B) hPairsB_sub
  have hPairsA_inj : Set.InjOn φ (PairsA : Set (Σ _ : Finset ℕ, ℕ)) :=
    hPairsB_inj.mono (by exact_mod_cast hPairsA_sub_B)
  have hκ_lb : (Nat.choose R₀ k : ℝ) / (288 * L) ≤ ∑ d ∈ S, q_U d := by
    have hinner : ∀ S₀ ∈ A.powersetCard k, (1 : ℝ) / (288 * L) ≤ ∑ q ∈ P₀ S₀, q_U ((∏ p ∈ S₀, p) * q) := by
      intro S₀ hS₀
      have hS₀A := (Finset.mem_powersetCard.mp hS₀).1
      have hS₀B : S₀ ∈ B₀.powersetCard k := Finset.mem_powersetCard.mpr ⟨Finset.Subset.trans hS₀A hA_sub_B₀, (Finset.mem_powersetCard.mp hS₀).2⟩
      obtain ⟨hd₁_pos, _, hdiv_ge⟩ := hS₀_d₁_bounds S₀ hS₀B
      set d₁ := ∏ p ∈ S₀, p
      have hd₁_dvd_T₁ : d₁ ∣ T₁ := Finset.prod_dvd_prod_of_subset S₀ A id hS₀A
      have hpt : ∀ q ∈ P₀ S₀, (d₁ : ℝ) / (18 * (N : ℝ)) ≤ q_U (d₁ * q) := fun q hq => by
        have hq1 : 1 ≤ q := (Finset.mem_filter.mp hq).2.one_le
        have hq_lb := qU_prog_lower T₁ S.card d₁ q hT₁_pos hS_ge2 hd₁_dvd_T₁ hq1 (h2q_le_S S₀ hS₀ q hq)
        have hdq_le : (d₁ : ℝ) * (q : ℝ) ≤ (N : ℝ) := by
          have : d₁ * q ≤ N := le_trans (Nat.mul_le_mul_left d₁ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2) (Nat.mul_div_le N d₁)
          exact_mod_cast this
        have h1 : (d₁ : ℝ) / (18 * (N : ℝ)) ≤ (1 : ℝ) / (18 * (q : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast (by omega : 0 < 18 * q))]
          nlinarith
        exact le_trans h1 hq_lb
      have hP₀_lb := prime_dyadic_div_lower N d₁ hd₁_pos hdiv_ge
      calc (1 : ℝ) / (288 * L)
          = ((N : ℝ) / (16 * (d₁ : ℝ) * L)) * ((d₁ : ℝ) / (18 * (N : ℝ))) := by
            have hd₁_ne : (d₁ : ℝ) ≠ 0 := by exact_mod_cast (by omega : d₁ ≠ 0)
            field_simp [hd₁_ne, ne_of_gt hN_pos, ne_of_gt hL_pos]; ring
        _ ≤ ((P₀ S₀).card : ℝ) * ((d₁ : ℝ) / (18 * (N : ℝ))) := mul_le_mul_of_nonneg_right hP₀_lb (by positivity)
        _ = ∑ _q ∈ P₀ S₀, (d₁ : ℝ) / (18 * (N : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ q ∈ P₀ S₀, q_U (d₁ * q) := Finset.sum_le_sum hpt
    calc (Nat.choose R₀ k : ℝ) / (288 * L)
        = ((A.powersetCard k).card : ℝ) * ((1 : ℝ) / (288 * L)) := by
          rw [Finset.card_powersetCard, hA_card, mul_one_div]
      _ = ∑ _S₀ ∈ A.powersetCard k, (1 : ℝ) / (288 * L) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S₀ ∈ A.powersetCard k, ∑ q ∈ P₀ S₀, q_U ((∏ p ∈ S₀, p) * q) := Finset.sum_le_sum hinner
      _ = ∑ x ∈ PairsA, q_U (φ x) := (Finset.sum_sigma (A.powersetCard k) P₀ (fun x => q_U (φ x))).symm
      _ = ∑ d ∈ PairsA.image φ, q_U d := (Finset.sum_image (fun x₁ hx₁ x₂ hx₂ hEq => hPairsA_inj hx₁ hx₂ hEq)).symm
      _ ≤ ∑ d ∈ S, q_U d := Finset.sum_le_sum_of_subset_of_nonneg hPairsA_img_sub fun d _ _ => hqU_nn d
  -- Combine κ_bar(S, U) * |S| and take ^(1/3)
  rw [← sum_qU_eq_kappa_bar S U]
  have hκ_nn : 0 ≤ ∑ d ∈ S, q_U d := Finset.sum_nonneg fun d _ => hqU_nn d
  rw [← Real.mul_rpow hκ_nn (Nat.cast_nonneg S.card)]
  have hch_ratio : (2 : ℝ) ^ k ≤ (Nat.choose R₀ k : ℝ) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ)) := by
    have hch := nat_choose_lower R₀ k hk_pos h2k_le_R₀
    have hfac_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      have hnat : k.factorial ≤ k ^ k := by
        have haux : ∀ m ≤ k, m.factorial ≤ k ^ m := by
          intro m hm; induction m with
          | zero => simp
          | succ r ihr =>
            rw [Nat.factorial_succ, pow_succ]
            calc (r + 1) * r.factorial ≤ k * k ^ r := Nat.mul_le_mul hm (ihr (by omega))
              _ = k ^ r * k := mul_comm _ _
        exact haux k (le_refl k)
      exact_mod_cast hnat
    have h64k2 : 64 * (k : ℝ) ^ 2 ≤ (R₀ : ℝ) / 2 := by
      have h1 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le 2
      have h2 : ((R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = (R₀ : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      nlinarith [show ((1 / 12 : ℝ) * (R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (1 / 144) * ((R₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 by ring]
    have hbase : (2 : ℝ) ≤ (R₀ : ℝ) / (64 * (k : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hpow := pow_le_pow_left₀ (by norm_num) hbase k
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hrew : ((R₀ : ℝ) / (64 * (k : ℝ) ^ 2)) ^ k = ((R₀ : ℝ) / (2 * (k : ℝ))) ^ k * (((1 : ℝ) / 32) ^ k / (k : ℝ) ^ k) := by
      rw [← div_pow, ← mul_pow]; congr 1; field_simp [hk_ne]; ring
    rw [hrew] at hpow
    calc (2 : ℝ) ^ k ≤ ((R₀ : ℝ) / (2 * (k : ℝ))) ^ k * (((1 : ℝ) / 32) ^ k / (k : ℝ) ^ k) := hpow
      _ ≤ (Nat.choose R₀ k : ℝ) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ)) :=
          mul_le_mul hch (div_le_div_of_nonneg_left (by positivity) (by positivity) hfac_le) (by positivity) (by positivity)
  have h2k_exp : Real.exp ((k : ℝ) / 2) ≤ (2 : ℝ) ^ k := by
    have h1 : Real.exp ((k : ℝ) / 2) = (Real.exp ((1 : ℝ) / 2)) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
      have := Real.exp_le_exp.mpr half_le_log_two
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
    rw [h1]; exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h2 k
  have hprod_lb : (N : ℝ) * Real.exp ((1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2)) ≤
      (∑ d ∈ S, q_U d) * (S.card : ℝ) := by
    have h4608 : 4608 * L ^ 2 ≤ Real.exp (3 * LL) := by
      have h4608_le : (4608 : ℝ) ≤ Real.exp LL := by
        have hsum := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ LL) 3
        have h2 : LL ^ 2 / ((2 : ℕ).factorial : ℝ) ≤ ∑ i ∈ Finset.range 3, LL ^ i / (i.factorial : ℝ) :=
          Finset.single_le_sum (f := fun i => LL ^ i / (i.factorial : ℝ)) (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
        norm_num at h2
        nlinarith
      calc 4608 * L ^ 2 = 4608 * (Real.exp LL) ^ 2 := by rw [Real.exp_log hL_pos]
        _ ≤ Real.exp LL * (Real.exp LL) ^ 2 := mul_le_mul_of_nonneg_right h4608_le (sq_nonneg _)
        _ = Real.exp (3 * LL) := by rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hexp_diff : 3 * LL + (1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2) ≤ (k : ℝ) / 2 := by linarith
    have hstep1 : (N : ℝ) * Real.exp ((1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2)) ≤
        ((N : ℝ) / (4608 * L ^ 2)) * Real.exp ((k : ℝ) / 2) := by
      rw [div_mul_eq_mul_div (a := (N : ℝ)), le_div_iff₀ (by positivity)]
      calc (N : ℝ) * Real.exp ((1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2)) * (4608 * L ^ 2)
          ≤ (N : ℝ) * Real.exp ((1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2)) * Real.exp (3 * LL) :=
            mul_le_mul_of_nonneg_left h4608 (by positivity)
        _ = (N : ℝ) * Real.exp (3 * LL + (1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2)) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ (N : ℝ) * Real.exp ((k : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)
    calc (N : ℝ) * Real.exp ((1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2))
        ≤ ((N : ℝ) / (4608 * L ^ 2)) * Real.exp ((k : ℝ) / 2) := hstep1
      _ ≤ ((N : ℝ) / (4608 * L ^ 2)) * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_left h2k_exp (by positivity)
      _ ≤ ((N : ℝ) / (4608 * L ^ 2)) * ((Nat.choose R₀ k : ℝ) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hch_ratio (by positivity)
      _ = ((Nat.choose R₀ k : ℝ) / (288 * L)) * (((N : ℝ) / (16 * L)) * (((1 : ℝ) / 32) ^ k / (k.factorial : ℝ))) := by ring
      _ ≤ (∑ d ∈ S, q_U d) * (S.card : ℝ) := mul_le_mul hκ_lb hS_card_lb (by positivity) hκ_nn
  have hpow := Real.rpow_le_rpow (by positivity) hprod_lb (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [Real.mul_rpow (le_of_lt hN_pos) (le_of_lt (Real.exp_pos _)), ← Real.exp_mul] at hpow
  have h1500 : (1 : ℝ) / 500 * (L / LL) ^ ((1 : ℝ) / 2) * ((1 : ℝ) / 3) =
      (1 : ℝ) / 1500 * (L / LL) ^ ((1 : ℝ) / 2) := by ring
  rw [h1500] at hpow
  exact hpow

/-- **BARRIER THEOREM 2c (Deterministic Single-Adversary `U₀` Across ALL Partitions):**
There exist `c > 0` and `N₀ : ℕ` such that for every `N ≥ N₀`, setting `H := ⌊N^(4/3)⌋`,
there exists a single explicit arithmetic progression `U₀ ⊆ [1, H]` of cardinality `N`
(namely `U₀ = {P * j : 1 ≤ j ≤ N}` for a primorial `P ≤ N^(1/4)`) that simultaneously forces
```
∑ α ∈ idx, κ_bar(S α, U₀)^(1/3) * |S α|^(1/3) ≥ N^(1/3) * exp (c * (log N)^(1/2) / log log N)
```
across EVERY set-theoretic cover `Finset.Ioc (N / 2) N ⊆ idx.biUnion S`. -/
theorem barrier2c_deterministic_U0_all_partitions :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∃ U₀ : Finset ℕ,
        U₀ ⊆ Finset.Icc 1 H ∧
        U₀.Nonempty ∧
        U₀.card = N ∧
        ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
          Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
          (N : ℝ) ^ ((1 : ℝ) / 3) *
            Real.exp (c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 2) / Real.log (Real.log (N : ℝ))) ≤
            ∑ α ∈ idx,
              ((∑ z₁ ∈ U₀, ∑ z₂ ∈ U₀, if z₁ ≠ z₂ then
                  (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
                else 0) / (U₀.card : ℝ) ^ 2) ^ ((1 : ℝ) / 3) *
                ((S α).card : ℝ) ^ ((1 : ℝ) / 3) := by
  classical
  refine ⟨(1 : ℝ) / 12000, by norm_num, Nat.ceil (Real.exp (Real.exp 200)), fun N hN => ?_⟩
  intro H
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  obtain ⟨hLL, hLL8, hN910, h4L2, hLL2_sq⟩ := large_N_barrier_bounds N hN
  change 200 ≤ LL at hLL
  change LL ^ 8 ≤ L / 160 at hLL8
  change 4 * L ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) at h4L2
  change LL ^ 2 ≤ (L / LL) ^ ((1 : ℝ) / 2) at hLL2_sq
  have hN_ge_exp : Real.exp (Real.exp 200) ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by linarith [Real.add_one_le_exp (Real.exp 200), Real.exp_pos (200 : ℝ)]
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hN_ge_exp
  have hN_ge2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ (N : ℝ) := by linarith [Real.add_one_le_exp (Real.exp 200), Real.add_one_le_exp (200 : ℝ)]
    exact_mod_cast this
  have hLL_pos : 0 < LL := by linarith
  have hLL8_ge : (200 : ℝ) ^ 8 ≤ LL ^ 8 := pow_le_pow_left₀ (by norm_num) hLL 8
  have hL_ge : (160 : ℝ) * (200 : ℝ) ^ 8 ≤ L := by linarith
  have hL_pos : 0 < L := by linarith
  have hL12_ge_12LL4 : 12 * LL ^ 4 ≤ L ^ ((1 : ℝ) / 2) := by
    have hsq : (12 * LL ^ 4) ^ 2 ≤ L := by
      have : (12 * LL ^ 4) ^ 2 = 144 * LL ^ 8 := by ring
      linarith
    have h1 := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_natCast (12 * LL ^ 4) 2, ← Real.rpow_mul (by positivity)] at h1
    norm_num at h1; exact h1
  -- Set Y = 2^(J_Y) with L/32 ≤ Y ≤ L/8 and m = Y / 2 ≥ 10^9
  let Y_fl := Nat.floor (L / 8)
  have hYfl_ge : 2 ^ 31 ≤ Y_fl := Nat.le_floor (by push_cast; linarith)
  let J_Y := Nat.log 2 Y_fl
  have hJY_ge31 : 31 ≤ J_Y := Nat.le_log_of_pow_le (by norm_num) hYfl_ge
  let Y := 2 ^ J_Y
  have hY_le : (Y : ℝ) ≤ L / 8 :=
    le_trans (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : Y_fl ≠ 0)) (Nat.floor_le (by positivity))
  have hY_ge : L / 32 ≤ (Y : ℝ) := by
    have hlt : Y_fl < 2 ^ (J_Y + 1) := Nat.lt_pow_succ_log_self (by norm_num) Y_fl
    have hfl : L / 8 - 1 < (Y_fl : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have h2Y : ((2 ^ (J_Y + 1) : ℕ) : ℝ) = 2 * (Y : ℝ) := by dsimp [Y]; rw [pow_succ]; push_cast; ring
    have : (Y_fl : ℝ) < 2 * (Y : ℝ) := by rw [← h2Y]; exact_mod_cast hlt
    linarith
  let m := 2 ^ (J_Y - 1)
  have h2m_eq_Y : 2 * m = Y := by
    calc 2 * m = 2 ^ (J_Y - 1) * 2 := by dsimp [m]; ring
      _ = 2 ^ ((J_Y - 1) + 1) := (pow_succ 2 (J_Y - 1)).symm
      _ = Y := by dsimp [Y]; congr 1; omega
  have hm_ge109 : 10 ^ 9 ≤ m :=
    le_trans (by norm_num : 10 ^ 9 ≤ 2 ^ 30) (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- Primorial P = ∏_{p ≤ Y} p ≤ 4^Y ≤ N^(1/4), U₀ = {P * j : 1 ≤ j ≤ N}
  let P := ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, p
  have hP_pos : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun p hp => (Finset.mem_filter.mp hp).2.ne_zero)
  have hP_le_N14 : (P : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have h4Y : (P : ℝ) ≤ (4 : ℝ) ^ Y := by exact_mod_cast prod_primes_le_four_pow Y
    have h4_exp : (4 : ℝ) ^ Y ≤ Real.exp (2 * (Y : ℝ)) := by
      have h1 : (4 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_le_exp.mpr (show Real.log 4 ≤ 2 by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith [log_two_le_one])
        rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at this
      calc (4 : ℝ) ^ Y ≤ (Real.exp 2) ^ Y := pow_le_pow_left₀ (by norm_num) h1 Y
        _ = Real.exp (2 * (Y : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    calc (P : ℝ) ≤ Real.exp (2 * (Y : ℝ)) := le_trans h4Y h4_exp
      _ ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by linarith)
      _ = (N : ℝ) ^ ((1 : ℝ) / 4) := by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring
  let U₀ := (Finset.Icc 1 N).image (fun j => P * j)
  have hinj_P : Function.Injective (fun j => P * j) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hP_pos h
  have hU₀_card : U₀.card = N := by dsimp [U₀]; rw [Finset.card_image_of_injective _ hinj_P]; simp
  have hU₀_ne : U₀.Nonempty := Finset.card_pos.mp (by omega)
  have hU₀_sub : U₀ ⊆ Finset.Icc 1 H := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨j, hj, rfl⟩
    have hjI := Finset.mem_Icc.mp hj
    have hprod_le : ((P * j : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 3) := by
      push_cast
      have hN14 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      have hsplit : (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) = (N : ℝ) ^ ((4 : ℝ) / 3) := by
        calc (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ)
            = (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (((1 : ℝ) / 3) + 1) := (Real.rpow_add hN_pos _ _).symm
          _ = (N : ℝ) ^ ((4 : ℝ) / 3) := by norm_num
      calc (P : ℝ) * (j : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) :=
            mul_le_mul hP_le_N14 (by exact_mod_cast hjI.2) (Nat.cast_nonneg _) (by positivity)
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) := mul_le_mul_of_nonneg_right hN14 (le_of_lt hN_pos)
        _ = (N : ℝ) ^ ((4 : ℝ) / 3) := hsplit
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hP_pos hjI.1, Nat.le_floor hprod_le⟩
  refine ⟨U₀, hU₀_sub, hU₀_ne, hU₀_card, ?_⟩
  intro ι idx S hcover
  -- Apply partition_lower_half_avg
  have hpart := partition_lower_half_avg (Finset.Ioc (N / 2) N) U₀ idx S hcover
  let q_U : ℕ → ℝ := fun d =>
    (∑ z₁ ∈ U₀, ∑ z₂ ∈ U₀, if z₁ ≠ z₂ ∧ d ∣ (if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂) then (1 : ℝ) else 0) /
      (U₀.card : ℝ) ^ 2
  have hqU_nn : ∀ d, 0 ≤ q_U d := fun d =>
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) (sq_nonneg _)
  -- Dyadic prime block B = (m, Y] ∩ Primes
  let B := (Finset.Ioc m (2 * m)).filter Nat.Prime
  have hB_card_lb : L / (256 * LL) ≤ (B.card : ℝ) := by
    have hcheb := prime_dyadic_card_lower m hm_ge109
    have hm_ge_r : L / 64 ≤ (m : ℝ) := by
      have : 2 * (m : ℝ) = (Y : ℝ) := by exact_mod_cast h2m_eq_Y
      linarith
    have hlog_le : Real.log (2 * (m : ℝ)) ≤ LL := by
      have : 2 * (m : ℝ) ≤ L := by
        have : 2 * (m : ℝ) = (Y : ℝ) := by exact_mod_cast h2m_eq_Y
        linarith
      exact Real.log_le_log (by positivity) this
    have hlog_pos : 0 < Real.log (2 * (m : ℝ)) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * m))
    calc L / (256 * LL) = (L / 64) / (4 * LL) := by ring
      _ ≤ (m : ℝ) / (4 * Real.log (2 * (m : ℝ))) :=
          div_le_div₀ (by positivity) hm_ge_r (by positivity) (by linarith)
      _ ≤ (B.card : ℝ) := hcheb
  have hB_card_le_Y : (B.card : ℝ) ≤ (Y : ℝ) := by
    have h1 : B.card ≤ Y := by
      calc B.card ≤ (Finset.Ioc m (2 * m)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 * m - m := Nat.card_Ioc _ _
        _ ≤ Y := by omega
    exact_mod_cast h1
  let k := Nat.floor ((B.card : ℝ) / (4 * (Y : ℝ) ^ ((1 : ℝ) / 2)))
  have hY12_pos : 0 < (Y : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hY12_le_L12 : (Y : ℝ) ^ ((1 : ℝ) / 2) ≤ L ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hk_le : (k : ℝ) ≤ (B.card : ℝ) / (4 * (Y : ℝ) ^ ((1 : ℝ) / 2)) := Nat.floor_le (by positivity)
  have hk_ge : L ^ ((1 : ℝ) / 2) / (2048 * LL) ≤ (k : ℝ) := by
    have hfl : (B.card : ℝ) / (4 * (Y : ℝ) ^ ((1 : ℝ) / 2)) - 1 < (k : ℝ) :=
      sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    have h1 : L ^ ((1 : ℝ) / 2) / (1024 * LL) ≤ (B.card : ℝ) / (4 * (Y : ℝ) ^ ((1 : ℝ) / 2)) := by
      have hLsplit : L / (256 * LL) / (4 * L ^ ((1 : ℝ) / 2)) = L ^ ((1 : ℝ) / 2) / (1024 * LL) := by
        have hsq : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
          rw [← Real.rpow_add hL_pos]; norm_num
        field_simp [ne_of_gt hLL_pos, ne_of_gt (Real.rpow_pos_of_pos hL_pos ((1 : ℝ) / 2))]
        nlinarith
      rw [← hLsplit]
      exact div_le_div₀ (by positivity) hB_card_lb (by positivity) (by linarith)
    have h2 : 1 ≤ L ^ ((1 : ℝ) / 2) / (2048 * LL) := by
      rw [one_le_div (by positivity)]
      have hLL3 : (200 : ℝ) ^ 3 ≤ LL ^ 3 := pow_le_pow_left₀ (by norm_num) hLL 3
      nlinarith [show LL ^ 4 = LL ^ 3 * LL by ring]
    have hhalf : L ^ ((1 : ℝ) / 2) / (1024 * LL) = 2 * (L ^ ((1 : ℝ) / 2) / (2048 * LL)) := by ring
    linarith
  have hk_pos : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by
      have h2 : 1 ≤ L ^ ((1 : ℝ) / 2) / (2048 * LL) := by
        rw [one_le_div (by positivity)]
        have hLL3 : (200 : ℝ) ^ 3 ≤ LL ^ 3 := pow_le_pow_left₀ (by norm_num) hLL 3
        nlinarith [show LL ^ 4 = LL ^ 3 * LL by ring]
      linarith
    exact_mod_cast this
  have h2k_le_B : 2 * k ≤ B.card := by
    have hY12_ge1 : (1 : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have : (2 * k : ℝ) ≤ (B.card : ℝ) := by
      have h1 : (k : ℝ) ≤ (B.card : ℝ) / 4 := le_trans hk_le
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith))
      linarith
    exact_mod_cast this
  have hk_le_L12 : (k : ℝ) ≤ L ^ ((1 : ℝ) / 2) := by
    have h1 : (B.card : ℝ) / (4 * (Y : ℝ) ^ ((1 : ℝ) / 2)) ≤ (Y : ℝ) ^ ((1 : ℝ) / 2) / 4 := by
      have hsq : (Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ ((1 : ℝ) / 2) = (Y : ℝ) := by
        rw [← Real.rpow_add (by positivity)]; norm_num
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  -- Construct injective family (S₀, p₀) ↦ (∏ S₀) * p₀ into (N/2, N]
  let P₀ : Finset ℕ → Finset ℕ := fun S₀ =>
    let d₁ := ∏ p ∈ S₀, p
    (Finset.Ioc (N / (2 * d₁)) (N / d₁)).filter Nat.Prime
  have hS₀_props : ∀ S₀ ∈ B.powersetCard k,
      let d₁ := ∏ p ∈ S₀, p
      2 ≤ d₁ ∧ d₁ ∣ P ∧ (d₁ : ℝ) ≤ (Y : ℝ) ^ k ∧ (d₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) ∧ 2 * 10 ^ 9 ≤ N / d₁ := by
    intro S₀ hS₀ d₁
    have hS₀B := (Finset.mem_powersetCard.mp hS₀).1
    have hS₀c := (Finset.mem_powersetCard.mp hS₀).2
    have hS₀_pr : ∀ p ∈ S₀, p.Prime ∧ p ≤ Y := fun p hp => by
      have hB := hS₀B hp
      exact ⟨(Finset.mem_filter.mp hB).2, by rw [← h2m_eq_Y]; exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hB).1).2⟩
    have hd₁_ge2 : 2 ≤ d₁ := by
      have hne : S₀.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨p, hp⟩
      have h2p : 2 ≤ p := (hS₀_pr p hp).1.two_le
      have hp_dvd : p ∣ d₁ := Finset.dvd_prod_of_mem id hp
      have hd₁_pos : 0 < d₁ := Finset.prod_pos fun q hq => (hS₀_pr q hq).1.pos
      exact le_trans h2p (Nat.le_of_dvd hd₁_pos hp_dvd)
    have hd₁_dvd_P : d₁ ∣ P := by
      refine Finset.prod_dvd_prod_of_subset S₀ ((Finset.Icc 1 Y).filter Nat.Prime) id ?_
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hS₀_pr p hp).1.one_le, (hS₀_pr p hp).2⟩, (hS₀_pr p hp).1⟩
    have hd₁_le_Yk : (d₁ : ℝ) ≤ (Y : ℝ) ^ k := by
      dsimp [d₁]; rw [Nat.cast_prod]
      calc ∏ p ∈ S₀, (p : ℝ) ≤ ∏ _p ∈ S₀, (Y : ℝ) :=
            Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun p hp => by exact_mod_cast (hS₀_pr p hp).2
        _ = (Y : ℝ) ^ k := by rw [Finset.prod_const, hS₀c]
    have hd₁_le_N10 : (d₁ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := by
      have hlogY : Real.log (Y : ℝ) ≤ LL := Real.log_le_log (by positivity) (by linarith)
      have h10LL : 10 * (k : ℝ) * LL ≤ L := by
        have hsq : (10 * L ^ ((1 : ℝ) / 2) * LL) ^ 2 ≤ L ^ 2 := by
          have hLsq : (L ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = L := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (le_of_lt hL_pos)]; norm_num
          have hrew : (10 * L ^ ((1 : ℝ) / 2) * LL) ^ 2 = 100 * LL ^ 2 * (L ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by ring
          rw [hrew, hLsq]
          have hLL6 : (200 : ℝ) ^ 6 ≤ LL ^ 6 := pow_le_pow_left₀ (by norm_num) hLL 6
          have h100 : 100 * LL ^ 2 ≤ L := by nlinarith [show LL ^ 8 = LL ^ 2 * LL ^ 6 by ring]
          nlinarith
        have h1 : 10 * L ^ ((1 : ℝ) / 2) * LL ≤ L := by nlinarith
        nlinarith
      have hYk_exp : (Y : ℝ) ^ k ≤ Real.exp (L / 10) := by
        calc (Y : ℝ) ^ k = (Real.exp (Real.log (Y : ℝ))) ^ k := by rw [Real.exp_log (by positivity)]
          _ = Real.exp ((k : ℝ) * Real.log (Y : ℝ)) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (L / 10) := Real.exp_le_exp.mpr (by nlinarith)
      calc (d₁ : ℝ) ≤ (Y : ℝ) ^ k := hd₁_le_Yk
        _ ≤ Real.exp (L / 10) := hYk_exp
        _ = (N : ℝ) ^ ((1 : ℝ) / 10) := by rw [Real.rpow_def_of_pos hN_pos]; congr 1; dsimp [L]; ring
    have hdiv_ge : 2 * 10 ^ 9 ≤ N / d₁ := by
      have hd₁_pos : 1 ≤ d₁ := by omega
      have hdiv_r : (2 : ℝ) * 10 ^ 9 ≤ (N : ℝ) / (d₁ : ℝ) := by
        have hsplit : (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) = (N : ℝ) := by
          rw [← Real.rpow_add hN_pos]; norm_num
        rw [le_div_iff₀ (by exact_mod_cast hd₁_pos)]
        calc (2 : ℝ) * 10 ^ 9 * (d₁ : ℝ)
            ≤ (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) :=
              mul_le_mul hN910 hd₁_le_N10 (by positivity) (by positivity)
          _ = (N : ℝ) := hsplit
      have hnat_mul : 2 * 10 ^ 9 * d₁ ≤ N := by
        have := (le_div_iff₀ (by exact_mod_cast hd₁_pos : (0 : ℝ) < (d₁ : ℝ))).mp hdiv_r
        exact_mod_cast this
      exact (Nat.le_div_iff_mul_le hd₁_pos).mpr hnat_mul
    exact ⟨hd₁_ge2, hd₁_dvd_P, hd₁_le_Yk, hd₁_le_N10, hdiv_ge⟩
  let Pairs := (B.powersetCard k).sigma P₀
  let φ : (Σ _ : Finset ℕ, ℕ) → ℕ := fun x => (∏ p ∈ x.1, p) * x.2
  have hPairs_gt_Y : ∀ S₀ ∈ B.powersetCard k, ∀ p₀ ∈ P₀ S₀, Y < p₀ := by
    intro S₀ hS₀ p₀ hp₀
    obtain ⟨hd₁_ge2, _, _, hd₁_le_N10, _⟩ := hS₀_props S₀ hS₀
    set d₁ := ∏ p ∈ S₀, p
    have hd₁_pos : 1 ≤ d₁ := by omega
    have hN12_lt : (N : ℝ) ^ ((1 : ℝ) / 2) < (N : ℝ) / (2 * (d₁ : ℝ)) - 1 := by
      have hN_gt : (4 : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by
        have hpow9 : (4 : ℝ) ^ (9 : ℕ) ≤ ((N : ℝ) ^ ((2 : ℝ) / 5)) ^ (9 : ℕ) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ ((2 : ℝ) / 5)) 9, ← Real.rpow_mul (le_of_lt hN_pos)]
          have h2 : (2 : ℝ) / 5 * (9 : ℕ) = ((9 : ℝ) / 10) * (4 : ℕ) := by norm_num
          rw [h2, Real.rpow_mul (le_of_lt hN_pos), Real.rpow_natCast]
          calc (4 : ℝ) ^ (9 : ℕ) ≤ ((2 : ℝ) * 10 ^ 9) ^ (4 : ℕ) := by norm_num
            _ ≤ ((N : ℝ) ^ ((9 : ℝ) / 10)) ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) hN910 4
        by_contra hlt; push Not at hlt
        have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 9 ≠ 0)
        linarith
      have hN12_ge4 : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith [sq_nonneg (L - 1)]
      have hdiv : (N : ℝ) ^ ((9 : ℝ) / 10) ≤ (N : ℝ) / (d₁ : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hd₁_pos)]
        have hsplit : (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) = (N : ℝ) := by
          rw [← Real.rpow_add hN_pos]; norm_num
        calc (N : ℝ) ^ ((9 : ℝ) / 10) * (d₁ : ℝ)
            ≤ (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) :=
              mul_le_mul_of_nonneg_left hd₁_le_N10 (by positivity)
          _ = (N : ℝ) := hsplit
      have hprod : (N : ℝ) ^ ((9 : ℝ) / 10) = (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((2 : ℝ) / 5) := by
        rw [← Real.rpow_add hN_pos]; norm_num
      have : (N : ℝ) / (2 * (d₁ : ℝ)) = ((N : ℝ) / (d₁ : ℝ)) / 2 := by ring
      nlinarith
    have hdiv_floor : (N : ℝ) / (2 * (d₁ : ℝ)) - 1 < ((N / (2 * d₁) : ℕ) : ℝ) := by
      have hmod := Nat.div_add_mod N (2 * d₁)
      have hlt := Nat.mod_lt N (by omega : 0 < 2 * d₁)
      have hnat : N < 2 * d₁ * (N / (2 * d₁) + 1) := by nlinarith
      have hr : (N : ℝ) < (2 * (d₁ : ℝ)) * (((N / (2 * d₁) : ℕ) : ℝ) + 1) := by
        have := (Nat.cast_lt (α := ℝ)).mpr hnat; push_cast at this; linarith
      have := (div_lt_iff₀' (by exact_mod_cast (by omega : 0 < 2 * d₁) : (0 : ℝ) < 2 * (d₁ : ℝ))).mpr hr
      linarith
    have hY_lt_N12 : (Y : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by nlinarith [sq_nonneg (L - 1)]
    have hY_lt_div : (Y : ℝ) < ((N / (2 * d₁) : ℕ) : ℝ) := lt_of_le_of_lt hY_lt_N12 (lt_trans hN12_lt hdiv_floor)
    have hY_nat : Y < N / (2 * d₁) := by exact_mod_cast hY_lt_div
    have hp₀I : N / (2 * d₁) < p₀ ∧ p₀ ≤ N / d₁ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1
    omega
  have hPairs_sub : Pairs.image φ ⊆ Finset.Ioc (N / 2) N := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨⟨S₀, p₀⟩, hx, rfl⟩
    have h1 := Finset.mem_sigma.mp hx
    obtain ⟨hd₁_ge2, _, _, _, _⟩ := hS₀_props S₀ h1.1
    set d₁ := ∏ p ∈ S₀, p
    have hp₀I : N / (2 * d₁) < p₀ ∧ p₀ ≤ N / d₁ := Finset.mem_Ioc.mp (Finset.mem_filter.mp h1.2).1
    refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
    · have hmod := Nat.div_add_mod N (2 * d₁)
      have hlt := Nat.mod_lt N (by omega : 0 < 2 * d₁)
      have hmul : N < 2 * (d₁ * p₀) := by nlinarith
      change N / 2 < d₁ * p₀
      omega
    · exact le_trans (Nat.mul_le_mul_left d₁ hp₀I.2) (Nat.mul_div_le N d₁)
  have hPairs_inj : Set.InjOn φ (Pairs : Set (Σ _ : Finset ℕ, ℕ)) := by
    intro ⟨S₁, p₁⟩ hx₁ ⟨S₂, p₂⟩ hx₂ hEq
    have h1 := Finset.mem_sigma.mp hx₁
    have h2 := Finset.mem_sigma.mp hx₂
    have hS₁ : ∀ p ∈ S₁, p.Prime ∧ p ≤ Y := fun p hp =>
      have hB := (Finset.mem_powersetCard.mp h1.1).1 hp
      ⟨(Finset.mem_filter.mp hB).2, by rw [← h2m_eq_Y]; exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hB).1).2⟩
    have hS₂ : ∀ p ∈ S₂, p.Prime ∧ p ≤ Y := fun p hp =>
      have hB := (Finset.mem_powersetCard.mp h2.1).1 hp
      ⟨(Finset.mem_filter.mp hB).2, by rw [← h2m_eq_Y]; exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hB).1).2⟩
    have hp₁ : p₁.Prime ∧ Y < p₁ := ⟨(Finset.mem_filter.mp h1.2).2, hPairs_gt_Y S₁ h1.1 p₁ h1.2⟩
    have hp₂ : p₂.Prime ∧ Y < p₂ := ⟨(Finset.mem_filter.mp h2.2).2, hPairs_gt_Y S₂ h2.1 p₂ h2.2⟩
    obtain ⟨rfl, rfl⟩ := prod_primes_mul_large_prime_inj Y hS₁ hS₂ hp₁ hp₂ hEq
    rfl
  -- Lower bound ∑_{d ∈ (N/2, N]} q_{U₀}(d)^(1/2)
  have hsum_lb : ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (2 : ℝ) ^ k ≤
      ∑ d ∈ Finset.Ioc (N / 2) N, (q_U d) ^ ((1 : ℝ) / 2) := by
    have hinner : ∀ S₀ ∈ B.powersetCard k,
        ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k) ≤
          ∑ p₀ ∈ P₀ S₀, (q_U ((∏ p ∈ S₀, p) * p₀)) ^ ((1 : ℝ) / 2) := by
      intro S₀ hS₀
      obtain ⟨hd₁_ge2, hd₁_dvd_P, hd₁_le_Yk, _, hdiv_ge⟩ := hS₀_props S₀ hS₀
      set d₁ := ∏ p ∈ S₀, p
      have hd₁_pos : 1 ≤ d₁ := by omega
      have hpt : ∀ p₀ ∈ P₀ S₀,
          (d₁ : ℝ) ^ ((1 : ℝ) / 2) / (5 * (N : ℝ) ^ ((1 : ℝ) / 2)) ≤ (q_U (d₁ * p₀)) ^ ((1 : ℝ) / 2) := fun p₀ hp₀ => by
        have hp₀1 : 1 ≤ p₀ := (Finset.mem_filter.mp hp₀).2.one_le
        have h2p₀_le_N : 2 * p₀ ≤ N := by
          have h1 : d₁ * p₀ ≤ N := le_trans (Nat.mul_le_mul_left d₁ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1).2) (Nat.mul_div_le N d₁)
          nlinarith
        have hq_lb := qU_prog_lower P N d₁ p₀ hP_pos hN_ge2 hd₁_dvd_P hp₀1 h2p₀_le_N
        have hdp_le : (d₁ : ℝ) * (p₀ : ℝ) ≤ (N : ℝ) := by
          have : d₁ * p₀ ≤ N := le_trans (Nat.mul_le_mul_left d₁ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp₀).1).2) (Nat.mul_div_le N d₁)
          exact_mod_cast this
        have hq_ge : (d₁ : ℝ) / (25 * (N : ℝ)) ≤ q_U (d₁ * p₀) := by
          refine le_trans ?_ hq_lb
          rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast (by omega : 0 < 18 * p₀))]
          nlinarith
        have hrpow := Real.rpow_le_rpow (by positivity) hq_ge (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have h25 : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 := by
          rw [← Real.sqrt_eq_rpow]; norm_num
        rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity), Real.mul_rpow (by norm_num) (le_of_lt hN_pos), h25] at hrpow
        exact hrpow
      have hP₀_lb := prime_dyadic_div_lower N d₁ hd₁_pos hdiv_ge
      have hd₁_12_le : (d₁ : ℝ) ^ ((1 : ℝ) / 2) ≤ ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k := by
        have h1 := Real.rpow_le_rpow (Nat.cast_nonneg d₁) hd₁_le_Yk (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have h2 : ((Y : ℝ) ^ k) ^ ((1 : ℝ) / 2) = ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k := by
          rw [← Real.rpow_natCast (Y : ℝ) k, ← Real.rpow_mul (by positivity),
            ← Real.rpow_natCast ((Y : ℝ) ^ ((1 : ℝ) / 2)) k, ← Real.rpow_mul (by positivity)]
          congr 1; ring
        rwa [h2] at h1
      have hN_split : (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1 : (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) := by
          rw [← Real.rpow_add hN_pos]; norm_num
        rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hN_pos _))]; exact h1.symm
      have hd₁_split : (d₁ : ℝ) ^ ((1 : ℝ) / 2) / (d₁ : ℝ) = 1 / (d₁ : ℝ) ^ ((1 : ℝ) / 2) := by
        have hd₁_pos_r : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast hd₁_pos
        have h1 : (d₁ : ℝ) ^ ((1 : ℝ) / 2) * (d₁ : ℝ) ^ ((1 : ℝ) / 2) = (d₁ : ℝ) := by
          rw [← Real.rpow_add hd₁_pos_r]; norm_num
        rw [div_eq_div_iff (ne_of_gt hd₁_pos_r) (ne_of_gt (Real.rpow_pos_of_pos hd₁_pos_r _)), one_mul]
        exact h1
      have hcomb : ((N : ℝ) / (16 * (d₁ : ℝ) * L)) * ((d₁ : ℝ) ^ ((1 : ℝ) / 2) / (5 * (N : ℝ) ^ ((1 : ℝ) / 2))) =
          ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (1 / (d₁ : ℝ) ^ ((1 : ℝ) / 2)) := by
        have hrew : ((N : ℝ) / (16 * (d₁ : ℝ) * L)) * ((d₁ : ℝ) ^ ((1 : ℝ) / 2) / (5 * (N : ℝ) ^ ((1 : ℝ) / 2))) =
            ((N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 2)) / (80 * L) * ((d₁ : ℝ) ^ ((1 : ℝ) / 2) / (d₁ : ℝ)) := by ring
        rw [hrew, hN_split, hd₁_split]
      calc ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k)
          ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (1 / (d₁ : ℝ) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hd₁_pos) _) hd₁_12_le) (by positivity)
        _ = ((N : ℝ) / (16 * (d₁ : ℝ) * L)) * ((d₁ : ℝ) ^ ((1 : ℝ) / 2) / (5 * (N : ℝ) ^ ((1 : ℝ) / 2))) := hcomb.symm
        _ ≤ ((P₀ S₀).card : ℝ) * ((d₁ : ℝ) ^ ((1 : ℝ) / 2) / (5 * (N : ℝ) ^ ((1 : ℝ) / 2))) :=
            mul_le_mul_of_nonneg_right hP₀_lb (by positivity)
        _ = ∑ _p₀ ∈ P₀ S₀, (d₁ : ℝ) ^ ((1 : ℝ) / 2) / (5 * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p₀ ∈ P₀ S₀, (q_U (d₁ * p₀)) ^ ((1 : ℝ) / 2) := Finset.sum_le_sum hpt
    have hch_ratio : (2 : ℝ) ^ k ≤ (Nat.choose B.card k : ℝ) * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k) := by
      have hch := nat_choose_lower B.card k hk_pos h2k_le_B
      have hbase : (2 : ℝ) ≤ (B.card : ℝ) / (2 * (k : ℝ) * (Y : ℝ) ^ ((1 : ℝ) / 2)) := by
        rw [le_div_iff₀ (by positivity)]
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Y : ℝ) ^ ((1 : ℝ) / 2))).mp hk_le
        linarith
      have hpow := pow_le_pow_left₀ (by norm_num) hbase k
      have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have hrew : ((B.card : ℝ) / (2 * (k : ℝ) * (Y : ℝ) ^ ((1 : ℝ) / 2))) ^ k =
          ((B.card : ℝ) / (2 * (k : ℝ))) ^ k * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k) := by
        rw [← one_div_pow, ← mul_pow]; congr 1; field_simp [hk_ne, ne_of_gt hY12_pos]
      rw [hrew] at hpow
      exact le_trans hpow (mul_le_mul_of_nonneg_right hch (by positivity))
    calc ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (2 : ℝ) ^ k
        ≤ ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * ((Nat.choose B.card k : ℝ) * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k)) :=
          mul_le_mul_of_nonneg_left hch_ratio (by positivity)
      _ = ((B.powersetCard k).card : ℝ) * (((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k)) := by
          rw [Finset.card_powersetCard]; ring
      _ = ∑ _S₀ ∈ B.powersetCard k, ((N : ℝ) ^ ((1 : ℝ) / 2) / (80 * L)) * (1 / ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S₀ ∈ B.powersetCard k, ∑ p₀ ∈ P₀ S₀, (q_U ((∏ p ∈ S₀, p) * p₀)) ^ ((1 : ℝ) / 2) :=
          Finset.sum_le_sum hinner
      _ = ∑ x ∈ Pairs, (q_U (φ x)) ^ ((1 : ℝ) / 2) :=
          (Finset.sum_sigma (B.powersetCard k) P₀ (fun x => (q_U (φ x)) ^ ((1 : ℝ) / 2))).symm
      _ = ∑ d ∈ Pairs.image φ, (q_U d) ^ ((1 : ℝ) / 2) :=
          (Finset.sum_image (f := fun d => (q_U d) ^ ((1 : ℝ) / 2)) (fun x₁ hx₁ x₂ hx₂ hEq => hPairs_inj hx₁ hx₂ hEq)).symm
      _ ≤ ∑ d ∈ Finset.Ioc (N / 2) N, (q_U d) ^ ((1 : ℝ) / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPairs_sub fun d _ _ => Real.rpow_nonneg (hqU_nn d) _
  -- Finish via partition_lower_half_avg: raise hsum_lb to ^(2/3)
  have h2k_exp : Real.exp ((k : ℝ) / 2) ≤ (2 : ℝ) ^ k := by
    have h1 : Real.exp ((k : ℝ) / 2) = (Real.exp ((1 : ℝ) / 2)) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
      have := Real.exp_le_exp.mpr half_le_log_two
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
    rw [h1]; exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h2 k
  have h80L : 80 * L ≤ Real.exp (2 * LL) := by
    have h80 : (80 : ℝ) ≤ Real.exp LL := by linarith [Real.add_one_le_exp LL]
    calc 80 * L = 80 * Real.exp LL := by rw [Real.exp_log hL_pos]
      _ ≤ Real.exp LL * Real.exp LL := mul_le_mul_of_nonneg_right h80 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (2 * LL) := by rw [← Real.exp_add]; congr 1; ring
  have h2LL_le : 2 * LL ≤ L ^ ((1 : ℝ) / 2) / (10000 * LL) := by
    rw [le_div_iff₀ (by positivity)]
    have hLL2 : (200 : ℝ) ^ 2 ≤ LL ^ 2 := pow_le_pow_left₀ (by norm_num) hLL 2
    nlinarith [show LL ^ 4 = LL ^ 2 * LL ^ 2 by ring]
  have hexp_diff : 2 * LL + (1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL ≤ (k : ℝ) / 2 := by
    have h1 : (1 : ℝ) / 4096 * (L ^ ((1 : ℝ) / 2) / LL) ≤ (k : ℝ) / 2 := by
      have : L ^ ((1 : ℝ) / 2) / (2048 * LL) / 2 = (1 : ℝ) / 4096 * (L ^ ((1 : ℝ) / 2) / LL) := by ring
      linarith
    have h2 : (1 : ℝ) / 10000 * (L ^ ((1 : ℝ) / 2) / LL) = L ^ ((1 : ℝ) / 2) / (10000 * LL) := by ring
    have h3 : (1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL = (1 : ℝ) / 8000 * (L ^ ((1 : ℝ) / 2) / LL) := by ring
    have hpos : 0 ≤ L ^ ((1 : ℝ) / 2) / LL := by positivity
    nlinarith
  have hstep : (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL) ≤
      ∑ d ∈ Finset.Ioc (N / 2) N, (q_U d) ^ ((1 : ℝ) / 2) := by
    refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left h2k_exp (by positivity)) hsum_lb)
    rw [div_mul_eq_mul_div (a := (N : ℝ) ^ ((1 : ℝ) / 2)), le_div_iff₀ (by positivity)]
    calc (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL) * (80 * L)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL) * Real.exp (2 * LL) :=
          mul_le_mul_of_nonneg_left h80L (by positivity)
      _ = (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp (2 * LL + (1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * Real.exp ((k : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)
  have hpow := Real.rpow_le_rpow (by positivity) hstep (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [Real.mul_rpow (by positivity) (le_of_lt (Real.exp_pos _)),
    ← Real.rpow_mul (le_of_lt hN_pos), ← Real.exp_mul] at hpow
  have h13 : (1 : ℝ) / 2 * ((2 : ℝ) / 3) = (1 : ℝ) / 3 := by norm_num
  have h12000 : (1 : ℝ) / 8000 * L ^ ((1 : ℝ) / 2) / LL * ((2 : ℝ) / 3) =
      (1 : ℝ) / 12000 * L ^ ((1 : ℝ) / 2) / LL := by ring
  rw [h13, h12000] at hpow
  exact le_trans hpow hpart

end PPL173Barriers



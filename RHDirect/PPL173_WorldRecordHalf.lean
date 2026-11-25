/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# PPL 173 (Erdős #711): Minimax-Sharp World-Record Bound `F(n) ≤ n^{4/3} exp(O((log n / log log n)^{1/2}))`

## Scope & Honest Labeling
This file formally proves a **new unconditional world-record subpolynomial upper bound** for
Erdős Problem #711 (`F(n) = sup_m f(n, m)`), achieving the **minimax-sharp `1/2` exponent** for
the 3-path modular reflection framework via Bad-Difference Absorption:

> **Headline World-Record Theorems (`ppl173_world_record_half_closed_iSup`,
> `ppl173_world_record_half_iSup`):**
> There exists an absolute constant `C > 0` such that for all `n ≥ 16`,
> ```
> sup_{m : ℕ} f(n, m) ≤ n ^ (4/3) * exp (C * (log n / log (log n)) ^ (1/2)).
> ```

- **Status vs. Literature:**
  - Strictly improves our prior Lean-verified world record `PPL173_WorldRecordFourThirds.lean`,
    which achieved `F(n) ≤ n^{4/3} exp(O((log n / log log n)^{2/3}))`, by cutting the subpolynomial
    error exponent from `2/3` down to the minimax-sharp `1/2`.
  - Strictly improves Chen–Korsky (`arXiv:2607.26450`, Aug 2026), which achieved
    `F(n) ≤ n^{4/3} exp(O(log n / log log n))`, by a super-exponential factor in the subpolynomial
    error term.
- **Honest Scope (NOT Erdős #711 Part A `n^{1+o(1)}`):**
  Erdős #711 Part A (`F(n) ≤ n^{1+o(1)}`) remains **open**. This theorem unconditionally
  establishes the minimax-sharp 3-path reflection bound `n^{4/3} exp(O((log n / log log n)^{1/2}))`.

## Proof Overview (100% Pure Mathlib, Elementary, Zero `sorry`)
1. **Lemma A'0 (`lemma_A_prime_0`):** Elementary dyadic harmonic average divisor-multiplicity bound
   `∑_{c=1}^{ℓ-1} r_D(c * e) ≤ (ℓ - 1) * τ(e)` for `D ⊆ (X/2, X]`.
2. **Lemma A' (`lemma_A_prime`, `lemma_A_prime_nodiv`):** Absorbed Superset 3-Path Modular
   Reflection Inequality with Bad-Difference Absorption, replacing worst-case `κ^2 |U|^2` by
   `K₁ * κ * |U|^2` where `K₁ = 4 * max_{e ∈ D} τ(e)`.
3. **Lemma B' (`lemma_B_prime`, `lemma_B_prime_single`):** Uniform `|U|`-Elimination Principle
   cutting the `κ`-exponent from `2/3` down to `1/3` (`(K₁ * κ * M)^{1/3} / ℓ`).
4. **Elementary Chebyshev, Prime Reciprocal & Joint Euler–Rankin Bounds:** Self-contained
   primorial bound `∏_{p ≤ N} p ≤ 4^N`, exact divisor-count bound Lemma C1/C2a, Constant-1
   Joint Euler-Product Rankin Trick Lemma C2b, and `τ(e)` factorization on Regime 2 slices.
5. **Headline Pure-Mathlib `sInf`/`⨆` Theorems (`ppl173_world_record_half_closed_iSup`,
   `ppl173_world_record_half_iSup`):** Explicit nonemptiness (`sInf`) and `BddAbove` (`⨆`)
   verification with zero custom masking definitions.
-/

namespace PPL173Half

/-! ### Section 1: Elementary Inequalities, Cauchy–Schwarz, and `ZMod` Fiber Bounds -/

/-- Elementary Cauchy–Schwarz inequality for `ℕ`-valued functions on a `Finset`. -/
private lemma sq_sum_le_card_mul_sum_sq_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ x ∈ s, f x) ^ 2 ≤ s.card * ∑ x ∈ s, (f x) ^ 2 := by
  have hZ : (0 : ℤ) ≤ ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp :
      ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        2 * (s.card : ℤ) * (∑ x ∈ s, (f x : ℤ) ^ 2) - 2 * (∑ x ∈ s, (f x : ℤ)) ^ 2 := by
    have h1 : ∀ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        (s.card : ℤ) * (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (∑ y ∈ s, (f y : ℤ)) +
          ∑ y ∈ s, (f y : ℤ) ^ 2 := by
      intro x _
      have hsub : ∀ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
          (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (f y : ℤ) + (f y : ℤ) ^ 2 := by
        intro y _; ring
      rw [Finset.sum_congr rfl hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ s, 2 * (f x : ℤ) = 2 * ∑ x ∈ s, (f x : ℤ) := by
      rw [← Finset.mul_sum]
    rw [h2]
    ring
  rw [hexp] at hZ
  have hle : (∑ x ∈ s, (f x : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ x ∈ s, (f x : ℤ) ^ 2 := by linarith
  exact_mod_cast hle

/-- In `ZMod d` (`d ≥ 1`), the map `c ↦ 2 * c - a` is at most `2`-to-`1`. -/
private lemma zmod_two_mul_sub_fiber_le_two (d : ℕ) [NeZero d] (a r : ZMod d) :
    (Finset.univ.filter (fun c : ZMod d => 2 * c - a = r)).card ≤ 2 := by
  by_cases hne : (Finset.univ.filter (fun c : ZMod d => 2 * c - a = r)).Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hc₀_eq : 2 * c₀ - a = r := (Finset.mem_filter.mp hc₀).2
    -- Any c in the fiber satisfies 2 * (c - c₀) = 0 in ZMod d.
    have hd_pos : 0 < d := NeZero.pos d
    let s : Finset (ZMod d) := {c₀, c₀ + ((d / 2 : ℕ) : ZMod d)}
    have hsub : Finset.univ.filter (fun c : ZMod d => 2 * c - a = r) ⊆ s := by
      intro c hc
      have hc_eq : 2 * c - a = r := (Finset.mem_filter.mp hc).2
      have h2 : (2 : ZMod d) * (c - c₀) = 0 := by
        linear_combination hc_eq - hc₀_eq
      set x : ZMod d := c - c₀
      have hx_val_lt : x.val < d := ZMod.val_lt x
      have hx_zero : ((2 * x.val : ℕ) : ZMod d) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        exact h2
      have hdvd : d ∣ 2 * x.val := (ZMod.natCast_eq_zero_iff (2 * x.val) d).mp hx_zero
      rcases hdvd with ⟨q, hq⟩
      have hq_lt : q < 2 := by nlinarith
      have hq_cases : q = 0 ∨ q = 1 := by omega
      rcases hq_cases with rfl | rfl
      · have hx0 : x.val = 0 := by omega
        have hx_eq : x = 0 := by
          rw [← ZMod.natCast_zmod_val x, hx0, Nat.cast_zero]
        have : c = c₀ := sub_eq_zero.mp hx_eq
        simp [s, this]
      · have hx_half : x.val = d / 2 := by omega
        have hx_eq : x = ((d / 2 : ℕ) : ZMod d) := by
          rw [← ZMod.natCast_zmod_val x, hx_half]
        have : c = c₀ + ((d / 2 : ℕ) : ZMod d) := eq_add_of_sub_eq' hx_eq
        simp [s, this]
    calc (Finset.univ.filter (fun c : ZMod d => 2 * c - a = r)).card
        ≤ s.card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- For `x, A, B ≥ 0`, `x^2 ≤ A * x + B → x ≤ A + √B`. -/
private lemma quad_le_imp_le_add_sqrt {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : x ^ 2 ≤ A * x + B) : x ≤ A + Real.sqrt B := by
  by_contra hgt
  push Not at hgt
  have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hx_pos : 0 < x := by linarith
  have h1 : (A + Real.sqrt B) * x < x ^ 2 := by nlinarith
  have h2 : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
  nlinarith

/-- Elementary inequality `min X (a + b + c) ≤ a + min X b + min X c` for `X, a, b, c ≥ 0`. -/
private lemma min_add_three_le {X a b c : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    min X (a + b + c) ≤ a + min X b + min X c := by
  by_cases h1 : X ≤ b
  · have hmin1 : min X b = X := min_eq_left h1
    have hmin2 : 0 ≤ min X c := le_min hX hc
    have hlhs : min X (a + b + c) ≤ X := min_le_left _ _
    linarith
  · by_cases h2 : X ≤ c
    · have hmin2 : min X c = X := min_eq_left h2
      have hmin1 : 0 ≤ min X b := le_min hX hb
      have hlhs : min X (a + b + c) ≤ X := min_le_left _ _
      linarith
    · push Not at h1 h2
      rw [min_eq_right (le_of_lt h1), min_eq_right (le_of_lt h2)]
      exact min_le_right _ _

/-- Weighted geometric mean bound `min X Y ≤ X ^ p * Y ^ q` for `p, q ≥ 0`, `p + q = 1`. -/
private lemma min_le_rpow_mul_rpow {X Y p q : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    min X Y ≤ X ^ p * Y ^ q := by
  have hm_nonneg : 0 ≤ min X Y := le_min hX hY
  have h1 : (min X Y) ^ p ≤ X ^ p := Real.rpow_le_rpow hm_nonneg (min_le_left X Y) hp
  have h2 : (min X Y) ^ q ≤ Y ^ q := Real.rpow_le_rpow hm_nonneg (min_le_right X Y) hq
  calc min X Y = (min X Y) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ = (min X Y) ^ (p + q) := by rw [hpq]
    _ = (min X Y) ^ p * (min X Y) ^ q := by
        by_cases hm : min X Y = 0
        · rw [hm, Real.zero_rpow (by linarith)]
          by_cases hp0 : p = 0
          · have hq1 : q = 1 := by linarith
            rw [hp0, hq1, Real.rpow_zero, Real.rpow_one, mul_zero]
          · rw [Real.zero_rpow hp0, zero_mul]
        · exact Real.rpow_add (lt_of_le_of_ne hm_nonneg (Ne.symm hm)) p q
    _ ≤ X ^ p * Y ^ q := mul_le_mul h1 h2 (Real.rpow_nonneg hm_nonneg q) (Real.rpow_nonneg hX p)

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
        have h32 : ((3 : ℝ) / 2) = 1 + ((1 : ℝ) / 2) := by norm_num
        rw [h32, Real.rpow_add hpos, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hfi hfi_le (by norm_num)) hfi
  calc ∑ i ∈ s, (f i) ^ ((3 : ℝ) / 2)
      ≤ ∑ i ∈ s, f i * S ^ ((1 : ℝ) / 2) := Finset.sum_le_sum hpt
    _ = S * S ^ ((1 : ℝ) / 2) := by rw [← Finset.sum_mul]
    _ = S ^ ((3 : ℝ) / 2) := by
        by_cases h0 : S = 0
        · rw [h0, zero_mul, Real.zero_rpow (by norm_num)]
        · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm h0)
          have h32 : ((3 : ℝ) / 2) = 1 + ((1 : ℝ) / 2) := by norm_num
          rw [h32, Real.rpow_add hpos, Real.rpow_one]

/-- Every integer `k ∈ [1, M]` has a multiple in `(x, x + M]`. -/
private lemma exists_multiple_in_block (x M k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ∃ a : ℕ, x < a ∧ a ≤ x + M ∧ k ∣ a := by
  refine ⟨(x / k + 1) * k, ?_, ?_, dvd_mul_left k _⟩
  · have hmod := Nat.div_add_mod x k
    have hlt : x % k < k := Nat.mod_lt x (by omega)
    nlinarith
  · have hle : (x / k) * k ≤ x := Nat.div_mul_le_self x k
    nlinarith

/-! ### Section 2: Lemma A — Refined Superset 3-Path Modular Reflection Inequality -/

/-- Half-progression of length `ℓ` starting at `a d` (`b = false`) or `a d + ℓ * d` (`b = true`). -/
private def apHalf (a : ℕ → ℕ) (ℓ d : ℕ) (b : Bool) : Finset ℕ :=
  (Finset.range ℓ).image (fun j => a d + (if b then ℓ + j else j) * d)

private lemma apHalf_card (a : ℕ → ℕ) (ℓ d : ℕ) (hd : 1 ≤ d) (b : Bool) :
    (apHalf a ℓ d b).card = ℓ := by
  rw [apHalf, Finset.card_image_of_injOn, Finset.card_range]
  intro j₁ _ j₂ _ hEq
  dsimp only at hEq
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hEq
  · have : j₁ * d = j₂ * d := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) this
  · have : (ℓ + j₁) * d = (ℓ + j₂) * d := by omega
    have : ℓ + j₁ = ℓ + j₂ := Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) this
    omega

private lemma apHalf_disjoint (a : ℕ → ℕ) (ℓ d : ℕ) (hd : 1 ≤ d) :
    Disjoint (apHalf a ℓ d false) (apHalf a ℓ d true) := by
  rw [Finset.disjoint_left]
  intro x hx0 hx1
  rcases Finset.mem_image.mp hx0 with ⟨j₀, hj₀, rfl⟩
  rcases Finset.mem_image.mp hx1 with ⟨j₁, hj₁, hEq⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hEq
  have hj₀_lt : j₀ < ℓ := Finset.mem_range.mp hj₀
  have : (ℓ + j₁) * d = j₀ * d := by omega
  have : ℓ + j₁ = j₀ := Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) this
  omega

private lemma apHalf_subset_of_ap (a : ℕ → ℕ) (ℓ d : ℕ) (U : Finset ℕ)
    (hU : ∀ j < 2 * ℓ, a d + j * d ∈ U) (b : Bool) :
    apHalf a ℓ d b ⊆ U := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  have hj_lt : j < ℓ := Finset.mem_range.mp hj
  cases b
  · exact hU j (by omega)
  · exact hU (ℓ + j) (by omega)

/-- Absolute difference of two natural numbers. -/
private def natDiff (u w : ℕ) : ℕ := if u ≤ w then w - u else u - w

/-- Elementary dyadic harmonic sum bound: for any `X > 0` and any finite set `A ⊆ ℕ`
contained in `(X / 2, X]`, `∑ d ∈ A, (1 : ℝ) / d ≤ 1`. -/
private lemma dyadic_harmonic_le_one (X : ℝ) (hX : 0 < X) (A : Finset ℕ)
    (hA : ∀ d ∈ A, X / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X) :
    ∑ d ∈ A, (1 : ℝ) / (d : ℝ) ≤ 1 := by
  by_cases hAne : A.Nonempty
  · let a : ℕ := Nat.floor (X / 2) + 1
    let b : ℕ := Nat.floor X
    have ha_pos : 1 ≤ a := by omega
    have ha_pos_r : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
    have hA_sub : A ⊆ Finset.Icc a b := by
      intro d hd
      obtain ⟨hlo, hhi⟩ := hA d hd
      have hfloor_lo : (Nat.floor (X / 2) : ℝ) ≤ X / 2 := Nat.floor_le (by linarith)
      have hd_gt : Nat.floor (X / 2) < d := by
        have : (Nat.floor (X / 2) : ℝ) < (d : ℝ) := lt_of_le_of_lt hfloor_lo hlo
        exact_mod_cast this
      have hd_le : d ≤ Nat.floor X := Nat.le_floor hhi
      exact Finset.mem_Icc.mpr ⟨by omega, hd_le⟩
    have hX_lt_2a : X < 2 * (a : ℝ) := by
      have hlt : X / 2 < (Nat.floor (X / 2) : ℝ) + 1 := Nat.lt_floor_add_one (X / 2)
      have ha_eq : (a : ℝ) = (Nat.floor (X / 2) : ℝ) + 1 := by push_cast [a]; rfl
      linarith
    have hb_lt_2a : b < 2 * a := by
      have hb_le : (b : ℝ) ≤ X := Nat.floor_le (le_of_lt hX)
      have : (b : ℝ) < ((2 * a : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hA_card : A.card ≤ a := by
      calc A.card ≤ (Finset.Icc a b).card := Finset.card_le_card hA_sub
        _ = b + 1 - a := Nat.card_Icc a b
        _ ≤ a := by omega
    have hpt : ∀ d ∈ A, (1 : ℝ) / (d : ℝ) ≤ (1 : ℝ) / (a : ℝ) := by
      intro d hd
      have hd_ge : a ≤ d := (Finset.mem_Icc.mp (hA_sub hd)).1
      exact one_div_le_one_div_of_le ha_pos_r (by exact_mod_cast hd_ge)
    calc ∑ d ∈ A, (1 : ℝ) / (d : ℝ)
        ≤ ∑ _d ∈ A, (1 : ℝ) / (a : ℝ) := Finset.sum_le_sum hpt
      _ = (A.card : ℝ) / (a : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ (a : ℝ) / (a : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hA_card) (le_of_lt ha_pos_r)
      _ = 1 := div_self (ne_of_gt ha_pos_r)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.sum_empty]
    norm_num

/-- **Lemma A'0 (Dyadic Average Divisor-Multiplicity Bound):**
For any real `X > 0`, any finite set `D ⊆ (X / 2, X] ∩ ℕ`, any `ℓ : ℕ`, and any `e ≥ 1`,
```
∑ c ∈ Icc 1 (ℓ - 1), #{d ∈ D : d ∣ c * e} ≤ (ℓ - 1) * τ(e).
``` -/
theorem lemma_A_prime_0
    (D : Finset ℕ) (X : ℝ) (ℓ e : ℕ)
    (hX : 0 < X)
    (hD_dyad : ∀ d ∈ D, X / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X)
    (he : 1 ≤ e) :
    ∑ c ∈ Finset.Icc 1 (ℓ - 1), (D.filter (fun d => d ∣ c * e)).card ≤
      (ℓ - 1) * e.divisors.card := by
  classical
  have hswap : ∑ c ∈ Finset.Icc 1 (ℓ - 1), (D.filter (fun d => d ∣ c * e)).card =
      ∑ d ∈ D, ((Finset.Icc 1 (ℓ - 1)).filter (fun c => d ∣ c * e)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hinner : ∀ d ∈ D,
      (((Finset.Icc 1 (ℓ - 1)).filter (fun c => d ∣ c * e)).card : ℝ) ≤
        ((ℓ - 1 : ℕ) : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) := by
    intro d hd
    have hd_pos : 0 < d := by
      have hlo := (hD_dyad d hd).1
      have : (0 : ℝ) < (d : ℝ) := by linarith
      exact_mod_cast this
    let g := Nat.gcd d e
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left e hd_pos
    let d' := d / g
    let e' := e / g
    have hd_eq : d = g * d' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)).symm
    have he_eq : e = g * e' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
    have hd'_pos : 0 < d' :=
      Nat.div_pos (Nat.le_of_dvd hd_pos (Nat.gcd_dvd_left d e)) hg_pos
    have hcop : Nat.Coprime d' e' := Nat.coprime_div_gcd_div_gcd hg_pos
    have hdvd_iff : ∀ c : ℕ, d ∣ c * e → d' ∣ c := by
      intro c hc
      have h1 : g * d' ∣ g * (c * e') := by
        rw [← hd_eq, show g * (c * e') = c * (g * e') by ring, ← he_eq]
        exact hc
      have h2 : d' ∣ c * e' := (mul_dvd_mul_iff_left (by omega : g ≠ 0)).mp h1
      exact hcop.dvd_of_dvd_mul_right h2
    let F := (Finset.Icc 1 (ℓ - 1)).filter (fun c => d ∣ c * e)
    have hmaps : ∀ c ∈ F, c / d' ∈ Finset.Icc 1 ((ℓ - 1) / d') := by
      intro c hc
      have hcIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1
      have hc_dvd : d' ∣ c := hdvd_iff c (Finset.mem_filter.mp hc).2
      have hq1 : 1 ≤ c / d' :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hc_dvd) hd'_pos
      exact Finset.mem_Icc.mpr ⟨hq1, Nat.div_le_div_right hcIcc.2⟩
    have hinj : Set.InjOn (fun c => c / d') (F : Set ℕ) := by
      intro c₁ hc₁ c₂ hc₂ hEq
      dsimp only at hEq
      have h1 : d' * (c₁ / d') = c₁ := Nat.mul_div_cancel' (hdvd_iff c₁ (Finset.mem_filter.mp hc₁).2)
      have h2 : d' * (c₂ / d') = c₂ := Nat.mul_div_cancel' (hdvd_iff c₂ (Finset.mem_filter.mp hc₂).2)
      rw [← h1, ← h2, hEq]
    have hcard_le : F.card ≤ (ℓ - 1) / d' := by
      calc F.card ≤ (Finset.Icc 1 ((ℓ - 1) / d')).card := Finset.card_le_card_of_injOn _ hmaps hinj
        _ = (ℓ - 1) / d' := by simp
    have hd'_pos_r : (0 : ℝ) < (d' : ℝ) := by exact_mod_cast hd'_pos
    have hdiv_le : (((ℓ - 1) / d' : ℕ) : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) / (d' : ℝ) := by
      rw [le_div_iff₀ hd'_pos_r]
      exact_mod_cast Nat.div_mul_le_self (ℓ - 1) d'
    exact le_trans (by exact_mod_cast hcard_le) hdiv_le
  suffices hR : (∑ d ∈ D, (((Finset.Icc 1 (ℓ - 1)).filter (fun c => d ∣ c * e)).card : ℝ)) ≤
      ((ℓ - 1 : ℕ) : ℝ) * (e.divisors.card : ℝ) by
    exact_mod_cast hR
  have hmaps_g : ∀ d ∈ D, Nat.gcd d e ∈ e.divisors := fun d _ =>
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d e, by omega⟩
  have hfib : ∑ d ∈ D, (1 : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) =
      ∑ g ∈ e.divisors, ∑ d ∈ D.filter (fun d => Nat.gcd d e = g), (1 : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) :=
    (Finset.sum_fiberwise_of_maps_to hmaps_g _).symm
  have hper_g : ∀ g ∈ e.divisors,
      ∑ d ∈ D.filter (fun d => Nat.gcd d e = g), (1 : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) ≤ 1 := by
    intro g hg
    have hg_pos : 0 < g := Nat.pos_of_mem_divisors hg
    have hg_pos_r : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
    let Dg := D.filter (fun d => Nat.gcd d e = g)
    have hcongr : ∑ d ∈ Dg, (1 : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) =
        ∑ d ∈ Dg, (1 : ℝ) / ((d / g : ℕ) : ℝ) :=
      Finset.sum_congr rfl fun d hd => by rw [(Finset.mem_filter.mp hd).2]
    rw [hcongr]
    have hinj : Set.InjOn (fun d => d / g) (Dg : Set ℕ) := by
      intro d₁ hd₁ d₂ hd₂ hEq
      dsimp only at hEq
      have h1 : g ∣ d₁ := by rw [← (Finset.mem_filter.mp hd₁).2]; exact Nat.gcd_dvd_left d₁ e
      have h2 : g ∣ d₂ := by rw [← (Finset.mem_filter.mp hd₂).2]; exact Nat.gcd_dvd_left d₂ e
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, hEq]
    have hsum_img : ∑ d ∈ Dg, (1 : ℝ) / ((d / g : ℕ) : ℝ) =
        ∑ d' ∈ Dg.image (fun d => d / g), (1 : ℝ) / (d' : ℝ) :=
      (Finset.sum_image (f := fun d' : ℕ => (1 : ℝ) / (d' : ℝ))
        (fun d₁ hd₁ d₂ hd₂ hEq => hinj hd₁ hd₂ hEq)).symm
    rw [hsum_img]
    refine dyadic_harmonic_le_one (X / (g : ℝ)) (div_pos hX hg_pos_r) (Dg.image (fun d => d / g)) ?_
    intro d' hd'
    rcases Finset.mem_image.mp hd' with ⟨d, hd, rfl⟩
    have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
    have hg_dvd : g ∣ d := by rw [← (Finset.mem_filter.mp hd).2]; exact Nat.gcd_dvd_left d e
    have hcast : ((d / g : ℕ) : ℝ) = (d : ℝ) / (g : ℝ) := by
      rw [eq_div_iff (ne_of_gt hg_pos_r)]
      exact_mod_cast Nat.div_mul_cancel hg_dvd
    obtain ⟨hlo, hhi⟩ := hD_dyad d hdD
    rw [hcast]
    constructor
    · rw [div_div, mul_comm (g : ℝ) 2, ← div_div]
      exact div_lt_div_of_pos_right hlo hg_pos_r
    · exact div_le_div_of_nonneg_right hhi (le_of_lt hg_pos_r)
  calc ∑ d ∈ D, (((Finset.Icc 1 (ℓ - 1)).filter (fun c => d ∣ c * e)).card : ℝ)
      ≤ ∑ d ∈ D, ((ℓ - 1 : ℕ) : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) := Finset.sum_le_sum hinner
    _ = ((ℓ - 1 : ℕ) : ℝ) * ∑ d ∈ D, (1 : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => (mul_one_div _ _).symm
    _ = ((ℓ - 1 : ℕ) : ℝ) * ∑ g ∈ e.divisors,
          ∑ d ∈ D.filter (fun d => Nat.gcd d e = g), (1 : ℝ) / ((d / Nat.gcd d e : ℕ) : ℝ) := by
        rw [hfib]
    _ ≤ ((ℓ - 1 : ℕ) : ℝ) * ∑ _g ∈ e.divisors, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper_g) (Nat.cast_nonneg _)
    _ = ((ℓ - 1 : ℕ) : ℝ) * (e.divisors.card : ℝ) := by simp

/-- **Lemma A' (Absorbed Superset 3-Path Modular Reflection Inequality, Exact `1 + √2` Form):**
Let `D ⊆ (X / 2, X] ∩ ℕ` be a finite dyadic set (`X > 0`), `ℓ ≥ 2`, `a : ℕ → ℕ`, and `U` any
finite set of natural numbers of diameter `≤ H` containing `{a d + j * d : 0 ≤ j < 2ℓ}` for every
`d ∈ D`. If every `1 ≤ t ≤ H` has at most `κ` divisors in `D` and every `e ∈ D` satisfies
`4 * τ(e) ≤ K₁`, then Bad-Difference Absorption replaces `κ^2 |U|^2` by `K₁ * κ * |U|^2`:
```
((ℓ - 1) / 2) * (4 * |D|^2 * ℓ^2 - 2 * |D| * ℓ * |U|)
  ≤ (1 + √2) * K₁ * |U| * (|D| * |U| + κ * |U|^2).
``` -/
theorem lemma_A_prime_nodiv
    (D U : Finset ℕ) (a : ℕ → ℕ) (X : ℝ) (ℓ H κ K₁ : ℕ)
    (hX : 0 < X)
    (hD_dyad : ∀ d ∈ D, X / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X)
    (hℓ : 2 ≤ ℓ)
    (hSU : ∀ d ∈ D, ∀ j < 2 * ℓ, a d + j * d ∈ U)
    (hU_diam : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → v - u ≤ H)
    (hκ : ∀ t : ℕ, 1 ≤ t → t ≤ H → (D.filter (fun d => d ∣ t)).card ≤ κ)
    (hK₁ : ∀ e ∈ D, 4 * e.divisors.card ≤ K₁) :
    (((ℓ - 1 : ℕ) : ℝ) / 2) * (4 * (D.card : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 - 2 * (D.card : ℝ) * (ℓ : ℝ) * (U.card : ℝ))
      ≤ (1 + Real.sqrt 2) * (K₁ : ℝ) * (U.card : ℝ) *
          ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) := by
  classical
  have hD_pos : ∀ d ∈ D, 1 ≤ d := by
    intro d hd
    have hlo := (hD_dyad d hd).1
    have : (0 : ℝ) < (d : ℝ) := by linarith
    have : 0 < d := by exact_mod_cast this
    omega
  -- Degenerate case D = ∅
  by_cases hD_empty : D.card = 0
  · simp [hD_empty]
    positivity
  have hU_pos : 0 < U.card := by
    obtain ⟨d₀, hd₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hD_empty)
    exact Finset.card_pos.mpr ⟨a d₀ + 0 * d₀, hSU d₀ hd₀ 0 (by omega)⟩
  let B2 : Finset Bool := {false, true}
  let P : Finset (ℕ × Bool) := D ×ˢ B2
  have hP_card : P.card = 2 * D.card := by
    rw [Finset.card_product]
    have hB2 : B2.card = 2 := by decide
    rw [hB2, mul_comm]
  let deg : ℕ → ℕ := fun u => (P.filter (fun p => u ∈ apHalf a ℓ p.1 p.2)).card
  -- Step 1: ∑ u ∈ U, deg u = 2 * D.card * ℓ
  have hsum_deg : ∑ u ∈ U, deg u = 2 * D.card * ℓ := by
    have h1 : ∑ u ∈ U, deg u = ∑ p ∈ P, (U.filter (fun u => u ∈ apHalf a ℓ p.1 p.2)).card := by
      simp_rw [deg, Finset.card_filter]
      exact Finset.sum_comm
    rw [h1]
    have h2 : ∀ p ∈ P, (U.filter (fun u => u ∈ apHalf a ℓ p.1 p.2)).card = ℓ := by
      intro p hp
      have hd : p.1 ∈ D := (Finset.mem_product.mp hp).1
      have hsub : apHalf a ℓ p.1 p.2 ⊆ U := apHalf_subset_of_ap a ℓ p.1 U (hSU p.1 hd) p.2
      have hEq : U.filter (fun u => u ∈ apHalf a ℓ p.1 p.2) = apHalf a ℓ p.1 p.2 := by
        ext u
        exact ⟨fun hu => (Finset.mem_filter.mp hu).2, fun hu => Finset.mem_filter.mpr ⟨hsub hu, hu⟩⟩
      rw [hEq]
      exact apHalf_card a ℓ p.1 (hD_pos p.1 hd) p.2
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, hP_card]
  -- Step 2: Define the good directed 3-path set T_good (r_D(|w - u|) ≤ K₁)
  let T : Finset (((ℕ × Bool) × (ℕ × Bool)) × (ℕ × ℕ)) :=
    ((P ×ˢ P) ×ˢ (U ×ˢ U)).filter fun x =>
      x.1.1 ≠ x.1.2 ∧
      x.2.1 ∈ apHalf a ℓ x.1.1.1 x.1.1.2 ∧
      x.2.1 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 ∧
      x.2.2 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 ∧
      x.2.2 ≠ x.2.1
  let T_good : Finset (((ℕ × Bool) × (ℕ × Bool)) × (ℕ × ℕ)) :=
    T.filter fun x => (D.filter (fun d => d ∣ natDiff x.2.1 x.2.2)).card ≤ K₁
  -- Bad-Difference Absorption lower bound: (ℓ - 1) * ∑ u ∈ U, deg u * (deg u - 1) ≤ 2 * T_good.card
  have hT_good_card : (ℓ - 1) * ∑ u ∈ U, deg u * (deg u - 1) ≤ 2 * T_good.card := by
    -- Express T_good.card by summing over u ∈ U, then pq ∈ P × P, then w ∈ U
    have hT_good_sum : T_good.card =
        ∑ u ∈ U, ∑ pq ∈ P ×ˢ P,
          (if pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧ u ∈ apHalf a ℓ pq.2.1 pq.2.2 then
            ((apHalf a ℓ pq.2.1 pq.2.2).erase u |>.filter
              (fun w => (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁)).card
          else 0) := by
      have hT_good_eq : T_good =
          ((P ×ˢ P) ×ˢ (U ×ˢ U)).filter fun x =>
            x.1.1 ≠ x.1.2 ∧
            x.2.1 ∈ apHalf a ℓ x.1.1.1 x.1.1.2 ∧
            x.2.1 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 ∧
            x.2.2 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 ∧
            x.2.2 ≠ x.2.1 ∧
            (D.filter (fun d => d ∣ natDiff x.2.1 x.2.2)).card ≤ K₁ := by
        ext x
        simp only [T_good, T, Finset.mem_filter]
        tauto
      rw [hT_good_eq, Finset.card_filter, Finset.sum_product, Finset.sum_comm, Finset.sum_product]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun pq hpq => ?_
      by_cases hcond : pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧ u ∈ apHalf a ℓ pq.2.1 pq.2.2
      · rw [if_pos hcond]
        have hcond_w : ∀ w ∈ U,
            (if pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧ u ∈ apHalf a ℓ pq.2.1 pq.2.2 ∧
                w ∈ apHalf a ℓ pq.2.1 pq.2.2 ∧ w ≠ u ∧
                (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁
              then (1 : ℕ) else 0) =
            (if w ∈ apHalf a ℓ pq.2.1 pq.2.2 ∧ w ≠ u ∧
                (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁
              then (1 : ℕ) else 0) := by
          intro w _
          by_cases hw : w ∈ apHalf a ℓ pq.2.1 pq.2.2 ∧ w ≠ u ∧
              (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁
          · rw [if_pos ⟨hcond.1, hcond.2.1, hcond.2.2, hw.1, hw.2.1, hw.2.2⟩, if_pos hw]
          · rw [if_neg (fun h => hw ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩), if_neg hw]
        rw [Finset.sum_congr rfl hcond_w, ← Finset.card_filter]
        have hd2 : pq.2.1 ∈ D := (Finset.mem_product.mp (Finset.mem_product.mp hpq).2).1
        have hsub : apHalf a ℓ pq.2.1 pq.2.2 ⊆ U :=
          apHalf_subset_of_ap a ℓ pq.2.1 U (hSU pq.2.1 hd2) pq.2.2
        congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨_, hw, hne, hgood⟩ => ⟨⟨hne, hw⟩, hgood⟩,
          fun ⟨⟨hne, hw⟩, hgood⟩ => ⟨hsub hw, hw, hne, hgood⟩⟩
      · rw [if_neg hcond]
        have hfalse : ∀ w, ¬(pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧
            u ∈ apHalf a ℓ pq.2.1 pq.2.2 ∧ w ∈ apHalf a ℓ pq.2.1 pq.2.2 ∧ w ≠ u ∧
            (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁) :=
          fun _ h => hcond ⟨h.1, h.2.1, h.2.2.1⟩
        simp only [hfalse, ite_false, Finset.sum_const_zero]
    -- For every e ∈ D, δ : Bool, u ∈ apHalf a ℓ e δ, Markov + Lemma A'0 gives
    -- ℓ - 1 ≤ 2 * ((apHalf a ℓ e δ).erase u |>.filter good).card
    have hgood_per : ∀ e ∈ D, ∀ δ : Bool, ∀ u ∈ apHalf a ℓ e δ,
        ℓ - 1 ≤ 2 * (((apHalf a ℓ e δ).erase u).filter
          (fun w => (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁)).card := by
      intro e he δ u hu
      have he_pos : 1 ≤ e := hD_pos e he
      let G := (apHalf a ℓ e δ).erase u
      let G_good := G.filter (fun w => (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁)
      let G_bad := G.filter (fun w => ¬ (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁)
      have hG_card : G.card = ℓ - 1 := by
        dsimp only [G]
        rw [Finset.card_erase_of_mem hu, apHalf_card a ℓ e he_pos δ]
      have hG_split : G_good.card + G_bad.card = ℓ - 1 := by
        rw [← hG_card]
        dsimp only [G_good, G_bad]
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        have h1 : ∀ w ∈ G, (if (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁ then (1 : ℕ) else 0) +
            (if ¬ (D.filter (fun d => d ∣ natDiff u w)).card ≤ K₁ then (1 : ℕ) else 0) = 1 := by
          intro w _; split_ifs <;> omega
        rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
      -- Define bad multiplier set B_e = {c ∈ Icc 1 (ℓ - 1) | K₁ < r_D(c * e)}
      let Be := (Finset.Icc 1 (ℓ - 1)).filter (fun c => K₁ < (D.filter (fun d => d ∣ c * e)).card)
      -- Markov's inequality + Lemma A'0: 4 * Be.card ≤ ℓ - 1
      have hBe_le : 4 * Be.card ≤ ℓ - 1 := by
        have hK₁_ge : 4 * e.divisors.card ≤ K₁ := hK₁ e he
        have htau_pos : 1 ≤ e.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
        have hK₁_pos : 0 < K₁ := by omega
        have hmarkov : K₁ * Be.card ≤ ∑ c ∈ Finset.Icc 1 (ℓ - 1), (D.filter (fun d => d ∣ c * e)).card := by
          calc K₁ * Be.card = ∑ _c ∈ Be, K₁ := by simp [mul_comm]
            _ ≤ ∑ c ∈ Be, (D.filter (fun d => d ∣ c * e)).card :=
                Finset.sum_le_sum fun c hc => le_of_lt (Finset.mem_filter.mp hc).2
            _ ≤ ∑ c ∈ Finset.Icc 1 (ℓ - 1), (D.filter (fun d => d ∣ c * e)).card :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _
        have hA0 := lemma_A_prime_0 D X ℓ e hX hD_dyad he_pos
        have h4 : K₁ * (4 * Be.card) ≤ K₁ * (ℓ - 1) := by
          calc K₁ * (4 * Be.card) = 4 * (K₁ * Be.card) := by ring
            _ ≤ 4 * ((ℓ - 1) * e.divisors.card) := Nat.mul_le_mul_left 4 (le_trans hmarkov hA0)
            _ = (4 * e.divisors.card) * (ℓ - 1) := by ring
            _ ≤ K₁ * (ℓ - 1) := Nat.mul_le_mul_right (ℓ - 1) hK₁_ge
        exact Nat.le_of_mul_le_mul_left h4 hK₁_pos
      -- Map w ∈ G_bad to c = natDiff u w / e ∈ Be with fibers of size ≤ 2
      have hmaps_bad : ∀ w ∈ G_bad, natDiff u w / e ∈ Be := by
        intro w hw
        have hwG : w ∈ G := (Finset.mem_filter.mp hw).1
        have hw_bad : K₁ < (D.filter (fun d => d ∣ natDiff u w)).card := by
          have := (Finset.mem_filter.mp hw).2; omega
        have hw_ne : w ≠ u := (Finset.mem_erase.mp hwG).1
        have hw_ap : w ∈ apHalf a ℓ e δ := (Finset.mem_erase.mp hwG).2
        rcases Finset.mem_image.mp hu with ⟨ju, hju, hju_eq⟩
        rcases Finset.mem_image.mp hw_ap with ⟨jw, hjw, hjw_eq⟩
        have hju_lt : ju < ℓ := Finset.mem_range.mp hju
        have hjw_lt : jw < ℓ := Finset.mem_range.mp hjw
        have hdiff_eq : natDiff u w = natDiff ju jw * e := by
          dsimp only [natDiff]
          cases δ <;> simp only [Bool.false_eq_true, ↓reduceIte] at hju_eq hjw_eq
          · by_cases hle : ju ≤ jw
            · have huw : u ≤ w := by rw [← hju_eq, ← hjw_eq]; exact Nat.add_le_add_left (Nat.mul_le_mul_right e hle) _
              rw [if_pos huw, if_pos hle, ← hju_eq, ← hjw_eq, Nat.sub_mul]
              omega
            · have huw : ¬ u ≤ w := by
                have hlt : jw < ju := by omega
                have : w < u := by
                  rw [← hju_eq, ← hjw_eq]
                  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hlt (by omega)) _
                omega
              rw [if_neg huw, if_neg hle, ← hju_eq, ← hjw_eq, Nat.sub_mul]
              omega
          · by_cases hle : ju ≤ jw
            · have huw : u ≤ w := by
                rw [← hju_eq, ← hjw_eq]
                exact Nat.add_le_add_left (Nat.mul_le_mul_right e (by omega)) _
              rw [if_pos huw, if_pos hle, ← hju_eq, ← hjw_eq]
              have hsub : (ℓ + jw) * e - (ℓ + ju) * e = (jw - ju) * e := by
                rw [← Nat.sub_mul]; congr 1; omega
              omega
            · have huw : ¬ u ≤ w := by
                have hlt : jw < ju := by omega
                have : w < u := by
                  rw [← hju_eq, ← hjw_eq]
                  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (by omega : ℓ + jw < ℓ + ju) (by omega)) _
                omega
              rw [if_neg huw, if_neg hle, ← hju_eq, ← hjw_eq]
              have hsub : (ℓ + ju) * e - (ℓ + jw) * e = (ju - jw) * e := by
                rw [← Nat.sub_mul]; congr 1; omega
              omega
        have hdiv_eq : natDiff u w / e = natDiff ju jw := by
          rw [hdiff_eq, Nat.mul_div_cancel _ (by omega)]
        have hj_ne : ju ≠ jw := by
          intro hEq; apply hw_ne; rw [← hju_eq, ← hjw_eq, hEq]
        have hc_Icc : natDiff ju jw ∈ Finset.Icc 1 (ℓ - 1) := by
          refine Finset.mem_Icc.mpr ?_
          dsimp only [natDiff]; split_ifs <;> omega
        refine Finset.mem_filter.mpr ⟨by rwa [hdiv_eq], ?_⟩
        rw [hdiv_eq, ← hdiff_eq]
        exact hw_bad
      have hfib_bad : ∀ c ∈ Be, (G_bad.filter (fun w => natDiff u w / e = c)).card ≤ 2 := by
        intro c _
        have hsub : G_bad.filter (fun w => natDiff u w / e = c) ⊆ {u + c * e, u - c * e} := by
          intro w hw
          have hwG : w ∈ G := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
          have hwc : natDiff u w / e = c := (Finset.mem_filter.mp hw).2
          have hw_ap : w ∈ apHalf a ℓ e δ := (Finset.mem_erase.mp hwG).2
          rcases Finset.mem_image.mp hu with ⟨ju, _, hju_eq⟩
          rcases Finset.mem_image.mp hw_ap with ⟨jw, _, hjw_eq⟩
          have hdvd : e ∣ natDiff u w := by
            dsimp only [natDiff]
            split_ifs with hle
            · refine ⟨(if δ then ℓ + jw else jw) - (if δ then ℓ + ju else ju), ?_⟩
              rw [mul_comm, Nat.sub_mul, ← hju_eq, ← hjw_eq]; omega
            · refine ⟨(if δ then ℓ + ju else ju) - (if δ then ℓ + jw else jw), ?_⟩
              rw [mul_comm, Nat.sub_mul, ← hju_eq, ← hjw_eq]; omega
          have hmul : natDiff u w = c * e := by
            rw [← hwc, Nat.div_mul_cancel hdvd]
          dsimp only [natDiff] at hmul
          simp only [Finset.mem_insert, Finset.mem_singleton]
          split_ifs at hmul with hle
          · left; omega
          · right; omega
        exact le_trans (Finset.card_le_card hsub) Finset.card_le_two
      have hGbad_le : G_bad.card ≤ 2 * Be.card := by
        rw [Finset.card_eq_sum_card_fiberwise hmaps_bad]
        calc ∑ c ∈ Be, (G_bad.filter (fun w => natDiff u w / e = c)).card
            ≤ ∑ _c ∈ Be, 2 := Finset.sum_le_sum hfib_bad
          _ = 2 * Be.card := by simp [mul_comm]
      change ℓ - 1 ≤ 2 * G_good.card
      omega
    -- Combine hgood_per over all u ∈ U and pq ∈ P × P
    rw [hT_good_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Finset.mul_sum]
    let Pu : Finset (ℕ × Bool) := P.filter (fun p => u ∈ apHalf a ℓ p.1 p.2)
    have hdeg_eq : Pu.card = deg u := rfl
    have hsum_pq : (ℓ - 1) * (deg u * (deg u - 1)) =
        ∑ pq ∈ P ×ˢ P,
          (if pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧ u ∈ apHalf a ℓ pq.2.1 pq.2.2
            then ℓ - 1 else 0) := by
      have h1 : ∑ pq ∈ P ×ˢ P,
          (if pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧ u ∈ apHalf a ℓ pq.2.1 pq.2.2
            then ℓ - 1 else 0) =
          (ℓ - 1) * ((Pu ×ˢ Pu).filter (fun pq => pq.1 ≠ pq.2)).card := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
          mul_comm]
        congr 1; congr 1
        ext pq
        simp only [Finset.mem_filter, Finset.mem_product, Pu]
        tauto
      have hoff : ((Pu ×ˢ Pu).filter (fun pq => pq.1 ≠ pq.2)).card = Pu.card * (Pu.card - 1) := by
        rw [Finset.card_filter, Finset.sum_product]
        have hrow : ∀ p ∈ Pu, ∑ q ∈ Pu, (if p ≠ q then (1 : ℕ) else 0) = Pu.card - 1 := by
          intro p hp
          rw [← Finset.card_filter]
          have hEq : Pu.filter (fun q => p ≠ q) = Pu.erase p := by
            ext q; simp only [Finset.mem_filter, Finset.mem_erase, ne_comm]; tauto
          rw [hEq, Finset.card_erase_of_mem hp]
        rw [Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]
      rw [h1, hoff, hdeg_eq]
    rw [hsum_pq]
    refine Finset.sum_le_sum fun pq hpq => ?_
    by_cases hcond : pq.1 ≠ pq.2 ∧ u ∈ apHalf a ℓ pq.1.1 pq.1.2 ∧ u ∈ apHalf a ℓ pq.2.1 pq.2.2
    · rw [if_pos hcond, if_pos hcond]
      have he : pq.2.1 ∈ D := (Finset.mem_product.mp (Finset.mem_product.mp hpq).2).1
      exact hgood_per pq.2.1 he pq.2.2 u hcond.2.2
    · rw [if_neg hcond, if_neg hcond, mul_zero]
  -- Step 3: Cauchy–Schwarz lower bound on 2 * T_good.card (in ℕ!)
  have hT_lower_nat :
      (ℓ - 1) * (4 * D.card ^ 2 * ℓ ^ 2) ≤
        U.card * (2 * T_good.card + (ℓ - 1) * (2 * D.card * ℓ)) := by
    have hcs := sq_sum_le_card_mul_sum_sq_nat U deg
    rw [hsum_deg] at hcs
    have hsq_split : ∑ u ∈ U, (deg u) ^ 2 = (∑ u ∈ U, deg u * (deg u - 1)) + ∑ u ∈ U, deg u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      cases hdu : deg u with
      | zero => simp
      | succ k => simp; ring
    rw [hsq_split, hsum_deg] at hcs
    have h4 : (2 * D.card * ℓ) ^ 2 = 4 * D.card ^ 2 * ℓ ^ 2 := by ring
    rw [h4] at hcs
    have hmul := Nat.mul_le_mul_left (ℓ - 1) hcs
    calc (ℓ - 1) * (4 * D.card ^ 2 * ℓ ^ 2)
        ≤ (ℓ - 1) * (U.card * ((∑ u ∈ U, deg u * (deg u - 1)) + 2 * D.card * ℓ)) := hmul
      _ = U.card * ((ℓ - 1) * (∑ u ∈ U, deg u * (deg u - 1)) + (ℓ - 1) * (2 * D.card * ℓ)) := by ring
      _ ≤ U.card * (2 * T_good.card + (ℓ - 1) * (2 * D.card * ℓ)) :=
          Nat.mul_le_mul_left U.card (Nat.add_le_add_right hT_good_card _)
  -- Step 4: Partition T_good into T1 and T2
  let T1 := T_good.filter fun x =>
    (x.1.2.2 = false ∧ x.2.2 < x.2.1) ∨ (x.1.2.2 = true ∧ x.2.1 < x.2.2)
  let T2 := T_good.filter fun x =>
    (x.1.2.2 = false ∧ x.2.1 < x.2.2) ∨ (x.1.2.2 = true ∧ x.2.2 < x.2.1)
  have hT_split : T_good.card ≤ T1.card + T2.card := by
    have hsub : T_good ⊆ T1 ∪ T2 := by
      intro x hx
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      have hne : x.2.2 ≠ x.2.1 := (Finset.mem_filter.mp hxT).2.2.2.2.2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · cases hb : x.1.2.2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, Or.inl ⟨hb, hlt⟩⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, Or.inr ⟨hb, hlt⟩⟩)
      · cases hb : x.1.2.2
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, Or.inl ⟨hb, hgt⟩⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, Or.inr ⟨hb, hgt⟩⟩)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le T1 T2)
  -- Helper: residue multiplicity m d c = #{x ∈ U | (x : ZMod d) = c}
  let m : (d : ℕ) → ZMod d → ℕ := fun d c => (U.filter (fun x : ℕ => (x : ZMod d) = c)).card
  -- Helper: S_mod d = ∑ c : ZMod d, (m d c)^2
  -- Step 5: Bound T1.card ≤ K₁ * ∑ d ∈ D, #{(z₁, z₂) ∈ U × U | z₁ ≡ z₂ (mod d)}
  have hT1_bound :
      T1.card ≤ K₁ * ∑ d ∈ D, ((U ×ˢ U).filter
        (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card := by
    -- We'll bound T1.card via fibers of Φ₁ x = (d, w, 2 * u - w)
    let Φ₁ : (((ℕ × Bool) × (ℕ × Bool)) × (ℕ × ℕ)) → ℕ × (ℕ × ℕ) :=
      fun x => (x.1.1.1, (x.2.2, 2 * x.2.1 - x.2.2))
    let B₁ : Finset (ℕ × (ℕ × ℕ)) :=
      (D ×ˢ (U ×ˢ U)).filter fun y =>
        (y.2.2 : ZMod y.1) = 2 * (a y.1 : ZMod y.1) - (y.2.1 : ZMod y.1)
    -- Every x ∈ T1 maps into B₁
    have hΦ₁_maps : ∀ x ∈ T1, Φ₁ x ∈ B₁ := by
      intro x hx
      have hxT_good : x ∈ T_good := (Finset.mem_filter.mp hx).1
      have hxT : x ∈ T := (Finset.mem_filter.mp hxT_good).1
      have hcase := (Finset.mem_filter.mp hx).2
      have hx_mem := Finset.mem_filter.mp hxT
      have hprod := Finset.mem_product.mp hx_mem.1
      have hd : x.1.1.1 ∈ D := (Finset.mem_product.mp (Finset.mem_product.mp hprod.1).1).1
      have he : x.1.2.1 ∈ D := (Finset.mem_product.mp (Finset.mem_product.mp hprod.1).2).1
      have he_pos : 1 ≤ x.1.2.1 := hD_pos _ he
      have hwU : x.2.2 ∈ U := (Finset.mem_product.mp hprod.2).2
      have hu_Sd : x.2.1 ∈ apHalf a ℓ x.1.1.1 x.1.1.2 := hx_mem.2.2.1
      have hu_Se : x.2.1 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := hx_mem.2.2.2.1
      have hw_Se : x.2.2 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := hx_mem.2.2.2.2.1
      -- Show 2 * u - w ∈ U and w ≤ 2 * u
      have hz_U_and_le : x.2.2 ≤ 2 * x.2.1 ∧ 2 * x.2.1 - x.2.2 ∈ U := by
        rcases Finset.mem_image.mp hu_Se with ⟨ju, hju, hju_eq⟩
        rcases Finset.mem_image.mp hw_Se with ⟨jw, hjw, hjw_eq⟩
        have hju_lt : ju < ℓ := Finset.mem_range.mp hju
        have hjw_lt : jw < ℓ := Finset.mem_range.mp hjw
        rcases hcase with ⟨hδ, hwu⟩ | ⟨hδ, huw⟩
        · rw [hδ] at hju_eq hjw_eq
          simp only [Bool.false_eq_true, ↓reduceIte] at hju_eq hjw_eq
          have hj_lt : jw < ju := by
            by_contra hge
            push Not at hge
            have : x.2.1 ≤ x.2.2 := by
              rw [← hju_eq, ← hjw_eq]
              exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hge) _
            omega
          refine ⟨by omega, ?_⟩
          have hz_eq : 2 * x.2.1 - x.2.2 = a x.1.2.1 + (2 * ju - jw) * x.1.2.1 := by
            rw [← hju_eq, ← hjw_eq]
            have hadd_mul : (2 * ju - jw) * x.1.2.1 + jw * x.1.2.1 = 2 * (ju * x.1.2.1) := by
              rw [← Nat.add_mul]; have : 2 * ju - jw + jw = 2 * ju := by omega
              rw [this]; ring
            exact Nat.sub_eq_of_eq_add (by linarith)
          rw [hz_eq]
          exact hSU x.1.2.1 he (2 * ju - jw) (by omega)
        · rw [hδ] at hju_eq hjw_eq
          simp only [↓reduceIte] at hju_eq hjw_eq
          have hj_lt : ju < jw := by
            by_contra hge
            push Not at hge
            have : x.2.2 ≤ x.2.1 := by
              rw [← hju_eq, ← hjw_eq]
              exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
            omega
          have h2u_gt : x.2.2 < 2 * x.2.1 := by
            rw [← hju_eq, ← hjw_eq]
            have : ℓ + jw < 2 * (ℓ + ju) := by omega
            have hmul : (ℓ + jw) * x.1.2.1 < (2 * (ℓ + ju)) * x.1.2.1 :=
              Nat.mul_lt_mul_of_pos_right this (by omega)
            linarith
          refine ⟨by omega, ?_⟩
          have hz_eq : 2 * x.2.1 - x.2.2 = a x.1.2.1 + (ℓ + 2 * ju - jw) * x.1.2.1 := by
            rw [← hju_eq, ← hjw_eq]
            have hadd_mul : (ℓ + 2 * ju - jw) * x.1.2.1 + (ℓ + jw) * x.1.2.1 =
                2 * ((ℓ + ju) * x.1.2.1) := by
              rw [← Nat.add_mul]; have : ℓ + 2 * ju - jw + (ℓ + jw) = 2 * (ℓ + ju) := by omega
              rw [this]; ring
            exact Nat.sub_eq_of_eq_add (by linarith)
          rw [hz_eq]
          exact hSU x.1.2.1 he (ℓ + 2 * ju - jw) (by omega)
      -- Show congruence mod d: (z : ZMod d) = 2 * a d - w
      have hcong : ((2 * x.2.1 - x.2.2 : ℕ) : ZMod x.1.1.1) =
          2 * (a x.1.1.1 : ZMod x.1.1.1) - (x.2.2 : ZMod x.1.1.1) := by
        have hu_mod : (x.2.1 : ZMod x.1.1.1) = (a x.1.1.1 : ZMod x.1.1.1) := by
          rcases Finset.mem_image.mp hu_Sd with ⟨j, _, hj_eq⟩
          rw [← hj_eq]
          push_cast
          simp
        have hadd : x.2.2 + (2 * x.2.1 - x.2.2) = 2 * x.2.1 :=
          Nat.add_sub_of_le hz_U_and_le.1
        have hadd_z : (x.2.2 : ZMod x.1.1.1) + ((2 * x.2.1 - x.2.2 : ℕ) : ZMod x.1.1.1) =
            2 * (x.2.1 : ZMod x.1.1.1) := by
          have := congrArg (fun n : ℕ => (n : ZMod x.1.1.1)) hadd
          simpa [Nat.cast_add, Nat.cast_mul] using this
        rw [hu_mod] at hadd_z
        linear_combination hadd_z
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hd, Finset.mem_product.mpr ⟨hwU, hz_U_and_le.2⟩⟩, hcong⟩
    -- Every fiber of Φ₁ over y ∈ B₁ has card ≤ K₁
    have hΦ₁_fiber : ∀ y ∈ B₁, (T1.filter (fun x => Φ₁ x = y)).card ≤ K₁ := by
      intro y _
      by_cases hfne : (T1.filter (fun x => Φ₁ x = y)).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hfne
        have hx₀_T1 : x₀ ∈ T1 := (Finset.mem_filter.mp hx₀).1
        have hx₀_Φ : Φ₁ x₀ = y := (Finset.mem_filter.mp hx₀).2
        -- Extract u₀ and w₀ from y
        let u₀ := x₀.2.1
        let w₀ := x₀.2.2
        have hx₀_Tgood : x₀ ∈ T_good := (Finset.mem_filter.mp hx₀_T1).1
        have hx₀_good : (D.filter (fun d => d ∣ natDiff u₀ w₀)).card ≤ K₁ :=
          (Finset.mem_filter.mp hx₀_Tgood).2
        let diff : ℕ := natDiff u₀ w₀
        -- Map fiber into D.filter (fun e => e ∣ diff) via x ↦ x.1.2.1
        have hinj : Set.InjOn (fun x : ((ℕ × Bool) × (ℕ × Bool)) × (ℕ × ℕ) => x.1.2.1)
            (T1.filter (fun x => Φ₁ x = y) : Set _) := by
          intro x₁ hx₁ x₂ hx₂ he_eq
          dsimp only at he_eq
          have h1T1 := (Finset.mem_filter.mp hx₁).1
          have h2T1 := (Finset.mem_filter.mp hx₂).1
          have h1Φ : Φ₁ x₁ = Φ₁ x₂ := by
            rw [(Finset.mem_filter.mp hx₁).2, (Finset.mem_filter.mp hx₂).2]
          have hd_eq : x₁.1.1.1 = x₂.1.1.1 := congrArg (fun p => p.1) h1Φ
          have hw_eq : x₁.2.2 = x₂.2.2 := congrArg (fun p => p.2.1) h1Φ
          have hz_eq : 2 * x₁.2.1 - x₁.2.2 = 2 * x₂.2.1 - x₂.2.2 := congrArg (fun p => p.2.2) h1Φ
          -- Need x.2.2 ≤ 2 * x.2.1 for both x₁ and x₂ to conclude x₁.2.1 = x₂.2.1
          have hle_2u : ∀ x ∈ T1, x.2.2 ≤ 2 * x.2.1 := by
            intro x hx
            have hxT := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
            have hcase := (Finset.mem_filter.mp hx).2
            have hxm := Finset.mem_filter.mp hxT
            have heD : x.1.2.1 ∈ D :=
              (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hxm.1).1).2).1
            have heP : 1 ≤ x.1.2.1 := hD_pos _ heD
            rcases hcase with ⟨_, hlt⟩ | ⟨hδ, _⟩
            · omega
            · rcases Finset.mem_image.mp hxm.2.2.2.1 with ⟨ju, hju, hju_eq⟩
              rcases Finset.mem_image.mp hxm.2.2.2.2.1 with ⟨jw, hjw, hjw_eq⟩
              rw [hδ] at hju_eq hjw_eq
              simp only [↓reduceIte] at hju_eq hjw_eq
              have hjw_lt : jw < ℓ := Finset.mem_range.mp hjw
              rw [← hju_eq, ← hjw_eq]
              have : (ℓ + jw) * x.1.2.1 ≤ (2 * (ℓ + ju)) * x.1.2.1 :=
                Nat.mul_le_mul_right _ (by omega)
              linarith
          have h1le := hle_2u x₁ h1T1
          have h2le := hle_2u x₂ h2T1
          have hu_eq : x₁.2.1 = x₂.2.1 := by omega
          have h1T := (Finset.mem_filter.mp (Finset.mem_filter.mp h1T1).1).1
          have h2T := (Finset.mem_filter.mp (Finset.mem_filter.mp h2T1).1).1
          have h1m := Finset.mem_filter.mp h1T
          have h2m := Finset.mem_filter.mp h2T
          have hd1D : x₁.1.1.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp h1m.1).1).1).1
          have he1D : x₁.1.2.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp h1m.1).1).2).1
          have hε_eq : x₁.1.1.2 = x₂.1.1.2 := by
            have h1u : x₁.2.1 ∈ apHalf a ℓ x₁.1.1.1 x₁.1.1.2 := h1m.2.2.1
            have h2u : x₁.2.1 ∈ apHalf a ℓ x₁.1.1.1 x₂.1.1.2 := by
              rw [hd_eq, hu_eq]; exact h2m.2.2.1
            have hdisj := apHalf_disjoint a ℓ x₁.1.1.1 (hD_pos _ hd1D)
            cases b1 : x₁.1.1.2 <;> cases b2 : x₂.1.1.2 <;> simp_all [Finset.disjoint_left]
          have hδ_eq : x₁.1.2.2 = x₂.1.2.2 := by
            have h1u : x₁.2.1 ∈ apHalf a ℓ x₁.1.2.1 x₁.1.2.2 := h1m.2.2.2.1
            have h2u : x₁.2.1 ∈ apHalf a ℓ x₁.1.2.1 x₂.1.2.2 := by
              rw [he_eq, hu_eq]; exact h2m.2.2.2.1
            have hdisj := apHalf_disjoint a ℓ x₁.1.2.1 (hD_pos _ he1D)
            cases b1 : x₁.1.2.2 <;> cases b2 : x₂.1.2.2 <;> simp_all [Finset.disjoint_left]
          rcases x₁ with ⟨⟨⟨d1, ε1⟩, ⟨e1, δ1⟩⟩, ⟨u1, w1⟩⟩
          rcases x₂ with ⟨⟨⟨d2, ε2⟩, ⟨e2, δ2⟩⟩, ⟨u2, w2⟩⟩
          simp only at hd_eq he_eq hε_eq hδ_eq hu_eq hw_eq
          subst hd_eq; subst he_eq; subst hε_eq; subst hδ_eq; subst hu_eq; subst hw_eq
          rfl
        have hmaps : ∀ x ∈ T1.filter (fun x => Φ₁ x = y),
            x.1.2.1 ∈ D.filter (fun e => e ∣ diff) := by
          intro x hx
          have hxT1 := (Finset.mem_filter.mp hx).1
          have hxΦ : Φ₁ x = Φ₁ x₀ := by rw [(Finset.mem_filter.mp hx).2, hx₀_Φ]
          have hxT := (Finset.mem_filter.mp (Finset.mem_filter.mp hxT1).1).1
          have hxm := Finset.mem_filter.mp hxT
          have heD : x.1.2.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hxm.1).1).2).1
          have hw_eq : x.2.2 = w₀ := congrArg (fun p => p.2.1) hxΦ
          have hz_eq : 2 * x.2.1 - x.2.2 = 2 * u₀ - w₀ := congrArg (fun p => p.2.2) hxΦ
          have hle_2u : ∀ z ∈ T1, z.2.2 ≤ 2 * z.2.1 := by
            intro z hz
            have hzT := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
            have hcase := (Finset.mem_filter.mp hz).2
            have hzm := Finset.mem_filter.mp hzT
            have heDz : z.1.2.1 ∈ D :=
              (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hzm.1).1).2).1
            have hePz : 1 ≤ z.1.2.1 := hD_pos _ heDz
            rcases hcase with ⟨_, hlt⟩ | ⟨hδ, _⟩
            · omega
            · rcases Finset.mem_image.mp hzm.2.2.2.1 with ⟨ju, _, hju_eq⟩
              rcases Finset.mem_image.mp hzm.2.2.2.2.1 with ⟨jw, hjw, hjw_eq⟩
              rw [hδ] at hju_eq hjw_eq
              simp only [↓reduceIte] at hju_eq hjw_eq
              have hjw_lt : jw < ℓ := Finset.mem_range.mp hjw
              rw [← hju_eq, ← hjw_eq]
              have : (ℓ + jw) * z.1.2.1 ≤ (2 * (ℓ + ju)) * z.1.2.1 :=
                Nat.mul_le_mul_right _ (by omega)
              linarith
          have hu_eq : x.2.1 = u₀ := by
            have := hle_2u x hxT1
            have := hle_2u x₀ hx₀_T1
            omega
          -- u₀, w₀ ∈ apHalf a ℓ e δ ⟹ e ∣ diff
          have he_dvd : x.1.2.1 ∣ diff := by
            have hu_Se : u₀ ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := by rw [← hu_eq]; exact hxm.2.2.2.1
            have hw_Se : w₀ ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := by rw [← hw_eq]; exact hxm.2.2.2.2.1
            rcases Finset.mem_image.mp hu_Se with ⟨ju, _, hju_eq⟩
            rcases Finset.mem_image.mp hw_Se with ⟨jw, _, hjw_eq⟩
            dsimp [diff, natDiff]
            split_ifs with hle
            · refine ⟨(if x.1.2.2 then ℓ + jw else jw) - (if x.1.2.2 then ℓ + ju else ju), ?_⟩
              rw [mul_comm, Nat.sub_mul, ← hju_eq, ← hjw_eq]
              omega
            · refine ⟨(if x.1.2.2 then ℓ + ju else ju) - (if x.1.2.2 then ℓ + jw else jw), ?_⟩
              rw [mul_comm, Nat.sub_mul, ← hju_eq, ← hjw_eq]
              omega
          exact Finset.mem_filter.mpr ⟨heD, he_dvd⟩
        calc (T1.filter (fun x => Φ₁ x = y)).card
            ≤ (D.filter (fun e => e ∣ diff)).card :=
              Finset.card_le_card_of_injOn _ hmaps hinj
          _ ≤ K₁ := hx₀_good
      · rw [Finset.not_nonempty_iff_eq_empty.mp hfne]
        simp
    have hT1_le_B1 : T1.card ≤ K₁ * B₁.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise hΦ₁_maps
      rw [hfib]
      calc ∑ y ∈ B₁, (T1.filter (fun x => Φ₁ x = y)).card
          ≤ ∑ _y ∈ B₁, K₁ := Finset.sum_le_sum hΦ₁_fiber
        _ = K₁ * B₁.card := by simp [mul_comm]
    -- Now show B₁.card ≤ ∑ d ∈ D, ((U ×ˢ U).filter (p.1 = p.2 mod d)).card
    have hB1_le : B₁.card ≤ ∑ d ∈ D, ((U ×ˢ U).filter
        (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card := by
      have hB1_eq : B₁.card = ∑ d ∈ D, ((U ×ˢ U).filter
          (fun p => (p.2 : ZMod d) = 2 * (a d : ZMod d) - (p.1 : ZMod d))).card := by
        dsimp only [B₁]
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.card_filter]
      rw [hB1_eq]
      refine Finset.sum_le_sum fun d hd => ?_
      have : NeZero d := ⟨by have := hD_pos d hd; omega⟩
      -- LHS = ∑ c : ZMod d, m d c * m d (2 * a d - c)
      have hL : ((U ×ˢ U).filter
          (fun p => (p.2 : ZMod d) = 2 * (a d : ZMod d) - (p.1 : ZMod d))).card =
          ∑ c : ZMod d, m d c * m d (2 * (a d : ZMod d) - c) := by
        have hfib : ((U ×ˢ U).filter
            (fun p => (p.2 : ZMod d) = 2 * (a d : ZMod d) - (p.1 : ZMod d))).card =
            ∑ c : ZMod d, (((U ×ˢ U).filter
              (fun p => (p.2 : ZMod d) = 2 * (a d : ZMod d) - (p.1 : ZMod d))).filter
              (fun p => (p.1 : ZMod d) = c)).card :=
          Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
        rw [hfib]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hEq : (((U ×ˢ U).filter
            (fun p => (p.2 : ZMod d) = 2 * (a d : ZMod d) - (p.1 : ZMod d))).filter
            (fun p => (p.1 : ZMod d) = c)) =
            (U.filter (fun x : ℕ => (x : ZMod d) = c)) ×ˢ
            (U.filter (fun y : ℕ => (y : ZMod d) = 2 * (a d : ZMod d) - c)) := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          constructor
          · rintro ⟨⟨⟨hx, hy⟩, h2⟩, h1⟩
            exact ⟨⟨hx, h1⟩, ⟨hy, by rw [h2, h1]⟩⟩
          · rintro ⟨⟨hx, h1⟩, ⟨hy, h2⟩⟩
            exact ⟨⟨⟨hx, hy⟩, by rw [h2, h1]⟩, h1⟩
        rw [hEq, Finset.card_product]
      -- RHS = ∑ c : ZMod d, (m d c)^2
      have hR : ((U ×ˢ U).filter
          (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card =
          ∑ c : ZMod d, (m d c) ^ 2 := by
        have hfib : ((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card =
            ∑ c : ZMod d, (((U ×ˢ U).filter
              (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).filter
              (fun p => (p.1 : ZMod d) = c)).card :=
          Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
        rw [hfib]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hEq : (((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).filter
            (fun p => (p.1 : ZMod d) = c)) =
            (U.filter (fun x : ℕ => (x : ZMod d) = c)) ×ˢ
            (U.filter (fun y : ℕ => (y : ZMod d) = c)) := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          constructor
          · rintro ⟨⟨⟨hx, hy⟩, h12⟩, h1⟩
            exact ⟨⟨hx, h1⟩, ⟨hy, by rw [← h12, h1]⟩⟩
          · rintro ⟨⟨hx, h1⟩, ⟨hy, h2⟩⟩
            exact ⟨⟨⟨hx, hy⟩, by rw [h1, h2]⟩, h1⟩
        rw [hEq, Finset.card_product, sq]
      rw [hL, hR]
      -- AM-GM: 2 * m(c) * m(2a - c) ≤ m(c)^2 + m(2a - c)^2, and c ↦ 2a - c is a bijection
      have hbij : ∑ c : ZMod d, (m d (2 * (a d : ZMod d) - c)) ^ 2 = ∑ c : ZMod d, (m d c) ^ 2 := by
        let e : ZMod d ≃ ZMod d :=
          { toFun := fun c => 2 * (a d : ZMod d) - c
            invFun := fun c => 2 * (a d : ZMod d) - c
            left_inv := fun c => by ring
            right_inv := fun c => by ring }
        exact Equiv.sum_comp e (fun c => (m d c) ^ 2)
      have h2le : 2 * ∑ c : ZMod d, m d c * m d (2 * (a d : ZMod d) - c) ≤
          ∑ c : ZMod d, ((m d c) ^ 2 + (m d (2 * (a d : ZMod d) - c)) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have hZ : (0 : ℤ) ≤ ((m d c : ℤ) - (m d (2 * (a d : ZMod d) - c) : ℤ)) ^ 2 := sq_nonneg _
        have : (2 * (m d c * m d (2 * (a d : ZMod d) - c)) : ℤ) ≤
            (m d c : ℤ) ^ 2 + (m d (2 * (a d : ZMod d) - c) : ℤ) ^ 2 := by linarith
        exact_mod_cast this
      rw [Finset.sum_add_distrib, hbij] at h2le
      omega
    exact le_trans hT1_le_B1 (Nat.mul_le_mul_left K₁ hB1_le)
  -- Step 6: Bound T2.card ≤ √2 * K₁ * ∑ d ∈ D, S_mod d (in ℝ)
  have hT2_bound :
      (T2.card : ℝ) ≤ Real.sqrt 2 * (K₁ : ℝ) * ∑ d ∈ D,
        (((U ×ˢ U).filter
          (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) := by
    let Φ₂ : (((ℕ × Bool) × (ℕ × Bool)) × (ℕ × ℕ)) → ℕ × (ℕ × ℕ) :=
      fun x => (x.1.1.1, (x.2.2, 2 * x.2.2 - x.2.1))
    let B₂ : Finset (ℕ × (ℕ × ℕ)) :=
      (D ×ˢ (U ×ˢ U)).filter fun y =>
        (y.2.2 : ZMod y.1) = 2 * (y.2.1 : ZMod y.1) - (a y.1 : ZMod y.1)
    have hΦ₂_maps : ∀ x ∈ T2, Φ₂ x ∈ B₂ := by
      intro x hx
      have hxT_good : x ∈ T_good := (Finset.mem_filter.mp hx).1
      have hxT : x ∈ T := (Finset.mem_filter.mp hxT_good).1
      have hcase := (Finset.mem_filter.mp hx).2
      have hx_mem := Finset.mem_filter.mp hxT
      have hprod := Finset.mem_product.mp hx_mem.1
      have hd : x.1.1.1 ∈ D := (Finset.mem_product.mp (Finset.mem_product.mp hprod.1).1).1
      have he : x.1.2.1 ∈ D := (Finset.mem_product.mp (Finset.mem_product.mp hprod.1).2).1
      have he_pos : 1 ≤ x.1.2.1 := hD_pos _ he
      have hwU : x.2.2 ∈ U := (Finset.mem_product.mp hprod.2).2
      have hu_Sd : x.2.1 ∈ apHalf a ℓ x.1.1.1 x.1.1.2 := hx_mem.2.2.1
      have hu_Se : x.2.1 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := hx_mem.2.2.2.1
      have hw_Se : x.2.2 ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := hx_mem.2.2.2.2.1
      have hz_U_and_le : x.2.1 ≤ 2 * x.2.2 ∧ 2 * x.2.2 - x.2.1 ∈ U := by
        rcases Finset.mem_image.mp hu_Se with ⟨ju, hju, hju_eq⟩
        rcases Finset.mem_image.mp hw_Se with ⟨jw, hjw, hjw_eq⟩
        have hju_lt : ju < ℓ := Finset.mem_range.mp hju
        have hjw_lt : jw < ℓ := Finset.mem_range.mp hjw
        rcases hcase with ⟨hδ, huw⟩ | ⟨hδ, hwu⟩
        · rw [hδ] at hju_eq hjw_eq
          simp only [Bool.false_eq_true, ↓reduceIte] at hju_eq hjw_eq
          have hj_lt : ju < jw := by
            by_contra hge
            push Not at hge
            have : x.2.2 ≤ x.2.1 := by
              rw [← hju_eq, ← hjw_eq]
              exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hge) _
            omega
          refine ⟨by omega, ?_⟩
          have hz_eq : 2 * x.2.2 - x.2.1 = a x.1.2.1 + (2 * jw - ju) * x.1.2.1 := by
            rw [← hju_eq, ← hjw_eq]
            have hadd_mul : (2 * jw - ju) * x.1.2.1 + ju * x.1.2.1 = 2 * (jw * x.1.2.1) := by
              rw [← Nat.add_mul]; have : 2 * jw - ju + ju = 2 * jw := by omega
              rw [this]; ring
            exact Nat.sub_eq_of_eq_add (by linarith)
          rw [hz_eq]
          exact hSU x.1.2.1 he (2 * jw - ju) (by omega)
        · rw [hδ] at hju_eq hjw_eq
          simp only [↓reduceIte] at hju_eq hjw_eq
          have hj_lt : jw < ju := by
            by_contra hge
            push Not at hge
            have : x.2.1 ≤ x.2.2 := by
              rw [← hju_eq, ← hjw_eq]
              exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
            omega
          have h2w_gt : x.2.1 < 2 * x.2.2 := by
            rw [← hju_eq, ← hjw_eq]
            have : ℓ + ju < 2 * (ℓ + jw) := by omega
            have hmul : (ℓ + ju) * x.1.2.1 < (2 * (ℓ + jw)) * x.1.2.1 :=
              Nat.mul_lt_mul_of_pos_right this (by omega)
            linarith
          refine ⟨by omega, ?_⟩
          have hz_eq : 2 * x.2.2 - x.2.1 = a x.1.2.1 + (ℓ + 2 * jw - ju) * x.1.2.1 := by
            rw [← hju_eq, ← hjw_eq]
            have hadd_mul : (ℓ + 2 * jw - ju) * x.1.2.1 + (ℓ + ju) * x.1.2.1 =
                2 * ((ℓ + jw) * x.1.2.1) := by
              rw [← Nat.add_mul]; have : ℓ + 2 * jw - ju + (ℓ + ju) = 2 * (ℓ + jw) := by omega
              rw [this]; ring
            exact Nat.sub_eq_of_eq_add (by linarith)
          rw [hz_eq]
          exact hSU x.1.2.1 he (ℓ + 2 * jw - ju) (by omega)
      have hcong : ((2 * x.2.2 - x.2.1 : ℕ) : ZMod x.1.1.1) =
          2 * (x.2.2 : ZMod x.1.1.1) - (a x.1.1.1 : ZMod x.1.1.1) := by
        have hu_mod : (x.2.1 : ZMod x.1.1.1) = (a x.1.1.1 : ZMod x.1.1.1) := by
          rcases Finset.mem_image.mp hu_Sd with ⟨j, _, hj_eq⟩
          rw [← hj_eq]
          push_cast
          simp
        have hadd : x.2.1 + (2 * x.2.2 - x.2.1) = 2 * x.2.2 :=
          Nat.add_sub_of_le hz_U_and_le.1
        have hadd_z : (x.2.1 : ZMod x.1.1.1) + ((2 * x.2.2 - x.2.1 : ℕ) : ZMod x.1.1.1) =
            2 * (x.2.2 : ZMod x.1.1.1) := by
          have := congrArg (fun n : ℕ => (n : ZMod x.1.1.1)) hadd
          simpa [Nat.cast_add, Nat.cast_mul] using this
        rw [hu_mod] at hadd_z
        linear_combination hadd_z
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hd, Finset.mem_product.mpr ⟨hwU, hz_U_and_le.2⟩⟩, hcong⟩
    have hΦ₂_fiber : ∀ y ∈ B₂, (T2.filter (fun x => Φ₂ x = y)).card ≤ K₁ := by
      intro y _
      by_cases hfne : (T2.filter (fun x => Φ₂ x = y)).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hfne
        have hx₀_T2 : x₀ ∈ T2 := (Finset.mem_filter.mp hx₀).1
        have hx₀_Φ : Φ₂ x₀ = y := (Finset.mem_filter.mp hx₀).2
        let u₀ := x₀.2.1
        let w₀ := x₀.2.2
        have hx₀_Tgood : x₀ ∈ T_good := (Finset.mem_filter.mp hx₀_T2).1
        have hx₀_good : (D.filter (fun d => d ∣ natDiff u₀ w₀)).card ≤ K₁ :=
          (Finset.mem_filter.mp hx₀_Tgood).2
        let diff : ℕ := natDiff u₀ w₀
        have hle_2w : ∀ z ∈ T2, z.2.1 ≤ 2 * z.2.2 := by
          intro z hz
          have hzT := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
          have hcase := (Finset.mem_filter.mp hz).2
          have hzm := Finset.mem_filter.mp hzT
          have heDz : z.1.2.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hzm.1).1).2).1
          have hePz : 1 ≤ z.1.2.1 := hD_pos _ heDz
          rcases hcase with ⟨_, hlt⟩ | ⟨hδ, _⟩
          · omega
          · rcases Finset.mem_image.mp hzm.2.2.2.1 with ⟨ju, hju, hju_eq⟩
            rcases Finset.mem_image.mp hzm.2.2.2.2.1 with ⟨jw, _, hjw_eq⟩
            rw [hδ] at hju_eq hjw_eq
            simp only [↓reduceIte] at hju_eq hjw_eq
            have hju_lt : ju < ℓ := Finset.mem_range.mp hju
            rw [← hju_eq, ← hjw_eq]
            have : (ℓ + ju) * z.1.2.1 ≤ (2 * (ℓ + jw)) * z.1.2.1 :=
              Nat.mul_le_mul_right _ (by omega)
            linarith
        have hinj : Set.InjOn (fun x : ((ℕ × Bool) × (ℕ × Bool)) × (ℕ × ℕ) => x.1.2.1)
            (T2.filter (fun x => Φ₂ x = y) : Set _) := by
          intro x₁ hx₁ x₂ hx₂ he_eq
          dsimp only at he_eq
          have h1T2 := (Finset.mem_filter.mp hx₁).1
          have h2T2 := (Finset.mem_filter.mp hx₂).1
          have h1Φ : Φ₂ x₁ = Φ₂ x₂ := by
            rw [(Finset.mem_filter.mp hx₁).2, (Finset.mem_filter.mp hx₂).2]
          have hd_eq : x₁.1.1.1 = x₂.1.1.1 := congrArg (fun p => p.1) h1Φ
          have hw_eq : x₁.2.2 = x₂.2.2 := congrArg (fun p => p.2.1) h1Φ
          have hz_eq : 2 * x₁.2.2 - x₁.2.1 = 2 * x₂.2.2 - x₂.2.1 := congrArg (fun p => p.2.2) h1Φ
          have h1le := hle_2w x₁ h1T2
          have h2le := hle_2w x₂ h2T2
          have hu_eq : x₁.2.1 = x₂.2.1 := by omega
          have h1T := (Finset.mem_filter.mp (Finset.mem_filter.mp h1T2).1).1
          have h2T := (Finset.mem_filter.mp (Finset.mem_filter.mp h2T2).1).1
          have h1m := Finset.mem_filter.mp h1T
          have h2m := Finset.mem_filter.mp h2T
          have hd1D : x₁.1.1.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp h1m.1).1).1).1
          have he1D : x₁.1.2.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp h1m.1).1).2).1
          have hε_eq : x₁.1.1.2 = x₂.1.1.2 := by
            have h1u : x₁.2.1 ∈ apHalf a ℓ x₁.1.1.1 x₁.1.1.2 := h1m.2.2.1
            have h2u : x₁.2.1 ∈ apHalf a ℓ x₁.1.1.1 x₂.1.1.2 := by
              rw [hd_eq, hu_eq]; exact h2m.2.2.1
            have hdisj := apHalf_disjoint a ℓ x₁.1.1.1 (hD_pos _ hd1D)
            cases b1 : x₁.1.1.2 <;> cases b2 : x₂.1.1.2 <;> simp_all [Finset.disjoint_left]
          have hδ_eq : x₁.1.2.2 = x₂.1.2.2 := by
            have h1u : x₁.2.1 ∈ apHalf a ℓ x₁.1.2.1 x₁.1.2.2 := h1m.2.2.2.1
            have h2u : x₁.2.1 ∈ apHalf a ℓ x₁.1.2.1 x₂.1.2.2 := by
              rw [he_eq, hu_eq]; exact h2m.2.2.2.1
            have hdisj := apHalf_disjoint a ℓ x₁.1.2.1 (hD_pos _ he1D)
            cases b1 : x₁.1.2.2 <;> cases b2 : x₂.1.2.2 <;> simp_all [Finset.disjoint_left]
          rcases x₁ with ⟨⟨⟨d1, ε1⟩, ⟨e1, δ1⟩⟩, ⟨u1, w1⟩⟩
          rcases x₂ with ⟨⟨⟨d2, ε2⟩, ⟨e2, δ2⟩⟩, ⟨u2, w2⟩⟩
          simp only at hd_eq he_eq hε_eq hδ_eq hu_eq hw_eq
          subst hd_eq; subst he_eq; subst hε_eq; subst hδ_eq; subst hu_eq; subst hw_eq
          rfl
        have hmaps : ∀ x ∈ T2.filter (fun x => Φ₂ x = y),
            x.1.2.1 ∈ D.filter (fun e => e ∣ diff) := by
          intro x hx
          have hxT2 := (Finset.mem_filter.mp hx).1
          have hxΦ : Φ₂ x = Φ₂ x₀ := by rw [(Finset.mem_filter.mp hx).2, hx₀_Φ]
          have hxT := (Finset.mem_filter.mp (Finset.mem_filter.mp hxT2).1).1
          have hxm := Finset.mem_filter.mp hxT
          have heD : x.1.2.1 ∈ D :=
            (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_product.mp hxm.1).1).2).1
          have hw_eq : x.2.2 = w₀ := congrArg (fun p => p.2.1) hxΦ
          have hz_eq : 2 * x.2.2 - x.2.1 = 2 * w₀ - u₀ := congrArg (fun p => p.2.2) hxΦ
          have hu_eq : x.2.1 = u₀ := by
            have := hle_2w x hxT2
            have := hle_2w x₀ hx₀_T2
            omega
          have he_dvd : x.1.2.1 ∣ diff := by
            have hu_Se : u₀ ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := by rw [← hu_eq]; exact hxm.2.2.2.1
            have hw_Se : w₀ ∈ apHalf a ℓ x.1.2.1 x.1.2.2 := by rw [← hw_eq]; exact hxm.2.2.2.2.1
            rcases Finset.mem_image.mp hu_Se with ⟨ju, _, hju_eq⟩
            rcases Finset.mem_image.mp hw_Se with ⟨jw, _, hjw_eq⟩
            dsimp [diff, natDiff]
            split_ifs with hle
            · refine ⟨(if x.1.2.2 then ℓ + jw else jw) - (if x.1.2.2 then ℓ + ju else ju), ?_⟩
              rw [mul_comm, Nat.sub_mul, ← hju_eq, ← hjw_eq]
              omega
            · refine ⟨(if x.1.2.2 then ℓ + ju else ju) - (if x.1.2.2 then ℓ + jw else jw), ?_⟩
              rw [mul_comm, Nat.sub_mul, ← hju_eq, ← hjw_eq]
              omega
          exact Finset.mem_filter.mpr ⟨heD, he_dvd⟩
        calc (T2.filter (fun x => Φ₂ x = y)).card
            ≤ (D.filter (fun e => e ∣ diff)).card :=
              Finset.card_le_card_of_injOn _ hmaps hinj
          _ ≤ K₁ := hx₀_good
      · rw [Finset.not_nonempty_iff_eq_empty.mp hfne]
        simp
    have hT2_le_B2 : T2.card ≤ K₁ * B₂.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise hΦ₂_maps
      rw [hfib]
      calc ∑ y ∈ B₂, (T2.filter (fun x => Φ₂ x = y)).card
          ≤ ∑ _y ∈ B₂, K₁ := Finset.sum_le_sum hΦ₂_fiber
        _ = K₁ * B₂.card := by simp [mul_comm]
    -- Show (B₂.card : ℝ) ≤ √2 * ∑ d ∈ D, S_mod d
    have hB2_le : (B₂.card : ℝ) ≤ Real.sqrt 2 * ∑ d ∈ D,
        (((U ×ˢ U).filter
          (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) := by
      have hB2_eq : B₂.card = ∑ d ∈ D, ((U ×ˢ U).filter
          (fun p => (p.2 : ZMod d) = 2 * (p.1 : ZMod d) - (a d : ZMod d))).card := by
        dsimp only [B₂]
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.card_filter]
      rw [hB2_eq, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun d hd => ?_
      have : NeZero d := ⟨by have := hD_pos d hd; omega⟩
      have hL : ((U ×ˢ U).filter
          (fun p => (p.2 : ZMod d) = 2 * (p.1 : ZMod d) - (a d : ZMod d))).card =
          ∑ c : ZMod d, m d c * m d (2 * c - (a d : ZMod d)) := by
        have hfib : ((U ×ˢ U).filter
            (fun p => (p.2 : ZMod d) = 2 * (p.1 : ZMod d) - (a d : ZMod d))).card =
            ∑ c : ZMod d, (((U ×ˢ U).filter
              (fun p => (p.2 : ZMod d) = 2 * (p.1 : ZMod d) - (a d : ZMod d))).filter
              (fun p => (p.1 : ZMod d) = c)).card :=
          Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
        rw [hfib]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hEq : (((U ×ˢ U).filter
            (fun p => (p.2 : ZMod d) = 2 * (p.1 : ZMod d) - (a d : ZMod d))).filter
            (fun p => (p.1 : ZMod d) = c)) =
            (U.filter (fun x : ℕ => (x : ZMod d) = c)) ×ˢ
            (U.filter (fun y : ℕ => (y : ZMod d) = 2 * c - (a d : ZMod d))) := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          constructor
          · rintro ⟨⟨⟨hx, hy⟩, h2⟩, h1⟩
            exact ⟨⟨hx, h1⟩, ⟨hy, by rw [h2, h1]⟩⟩
          · rintro ⟨⟨hx, h1⟩, ⟨hy, h2⟩⟩
            exact ⟨⟨⟨hx, hy⟩, by rw [h2, h1]⟩, h1⟩
        rw [hEq, Finset.card_product]
      have hR : ((U ×ˢ U).filter
          (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card =
          ∑ c : ZMod d, (m d c) ^ 2 := by
        have hfib : ((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card =
            ∑ c : ZMod d, (((U ×ˢ U).filter
              (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).filter
              (fun p => (p.1 : ZMod d) = c)).card :=
          Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
        rw [hfib]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hEq : (((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).filter
            (fun p => (p.1 : ZMod d) = c)) =
            (U.filter (fun x : ℕ => (x : ZMod d) = c)) ×ˢ
            (U.filter (fun y : ℕ => (y : ZMod d) = c)) := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          constructor
          · rintro ⟨⟨⟨hx, hy⟩, h12⟩, h1⟩
            exact ⟨⟨hx, h1⟩, ⟨hy, by rw [← h12, h1]⟩⟩
          · rintro ⟨⟨hx, h1⟩, ⟨hy, h2⟩⟩
            exact ⟨⟨⟨hx, hy⟩, by rw [h1, h2]⟩, h1⟩
        rw [hEq, Finset.card_product, sq]
      -- At-most-2-to-1 bound: ∑ c, m(2c - a)^2 ≤ 2 * ∑ r, m(r)^2
      have h2to1 : ∑ c : ZMod d, (m d (2 * c - (a d : ZMod d))) ^ 2 ≤
          2 * ∑ r : ZMod d, (m d r) ^ 2 := by
        have hfib : ∑ c : ZMod d, (m d (2 * c - (a d : ZMod d))) ^ 2 =
            ∑ r : ZMod d, ∑ c ∈ Finset.univ.filter (fun c : ZMod d => 2 * c - (a d : ZMod d) = r),
              (m d (2 * c - (a d : ZMod d))) ^ 2 :=
          (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
        rw [hfib, Finset.mul_sum]
        refine Finset.sum_le_sum fun r _ => ?_
        have hconst : ∑ c ∈ Finset.univ.filter (fun c : ZMod d => 2 * c - (a d : ZMod d) = r),
            (m d (2 * c - (a d : ZMod d))) ^ 2 =
            (Finset.univ.filter (fun c : ZMod d => 2 * c - (a d : ZMod d) = r)).card * (m d r) ^ 2 := by
          rw [Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.mp hc).2]),
            Finset.sum_const, smul_eq_mul]
        rw [hconst]
        exact Nat.mul_le_mul_right _ (zmod_two_mul_sub_fiber_le_two d (a d : ZMod d) r)
      rw [hL, hR]
      -- Use 2 * √2 * x * y ≤ 2 * x^2 + y^2
      have hsq2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hsq2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hstep : 2 * Real.sqrt 2 * (∑ c : ZMod d, (m d c : ℝ) * (m d (2 * c - (a d : ZMod d)) : ℝ)) ≤
          2 * (∑ c : ZMod d, (m d c : ℝ) ^ 2) +
            ∑ c : ZMod d, (m d (2 * c - (a d : ZMod d)) : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun c _ => ?_
        have hnn : 0 ≤ (Real.sqrt 2 * (m d c : ℝ) - (m d (2 * c - (a d : ZMod d)) : ℝ)) ^ 2 :=
          sq_nonneg _
        nlinarith [hsq2_sq]
      have h2to1_real : ∑ c : ZMod d, (m d (2 * c - (a d : ZMod d)) : ℝ) ^ 2 ≤
          2 * ∑ c : ZMod d, (m d c : ℝ) ^ 2 := by exact_mod_cast h2to1
      have hcastL : ((∑ c : ZMod d, m d c * m d (2 * c - (a d : ZMod d)) : ℕ) : ℝ) =
          ∑ c : ZMod d, (m d c : ℝ) * (m d (2 * c - (a d : ZMod d)) : ℝ) := by
        push_cast; rfl
      have hcastR : ((∑ c : ZMod d, (m d c) ^ 2 : ℕ) : ℝ) = ∑ c : ZMod d, (m d c : ℝ) ^ 2 := by
        push_cast; rfl
      rw [hcastL, hcastR]
      nlinarith [hsq2_sq, hsq2_pos]
    have hT2_cast : (T2.card : ℝ) ≤ (K₁ : ℝ) * (B₂.card : ℝ) := by exact_mod_cast hT2_le_B2
    calc (T2.card : ℝ) ≤ (K₁ : ℝ) * (B₂.card : ℝ) := hT2_cast
      _ ≤ (K₁ : ℝ) * (Real.sqrt 2 * ∑ d ∈ D,
            (((U ×ˢ U).filter
              (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hB2_le (Nat.cast_nonneg K₁)
      _ = Real.sqrt 2 * (K₁ : ℝ) * ∑ d ∈ D,
            (((U ×ˢ U).filter
              (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) := by ring
  -- Step 7: Bound ∑ d ∈ D, #{(z₁, z₂) ∈ U × U | z₁ ≡ z₂ (mod d)} ≤ |D|*|U| + κ*|U|^2
  have hSmod_bound :
      ∑ d ∈ D, ((U ×ˢ U).filter
          (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card ≤
        D.card * U.card + κ * U.card ^ 2 := by
    -- Rewrite LHS by swapping sums over d ∈ D and (z₁, z₂) ∈ U ×ˢ U
    have hswap : ∑ d ∈ D, ((U ×ˢ U).filter
        (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card =
        ∑ p ∈ U ×ˢ U, (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    -- Split U ×ˢ U into diagonal (p.1 = p.2) and off-diagonal (p.1 ≠ p.2)
    have hsplit : ∑ p ∈ U ×ˢ U, (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card =
        ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 = p.2),
          (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card +
        ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2),
          (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card := by
      rw [← Finset.sum_filter_add_sum_filter_not (U ×ˢ U) (fun p => p.1 = p.2)]
    rw [hsplit]
    have hdiag : ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 = p.2),
        (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card = D.card * U.card := by
      have hcard_diag : ((U ×ˢ U).filter (fun p => p.1 = p.2)).card = U.card := by
        have hEq : (U ×ˢ U).filter (fun p => p.1 = p.2) = U.image (fun u => (u, u)) := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨hx, _⟩, rfl⟩; exact ⟨x, hx, rfl⟩
          · rintro ⟨u, hu, hEq⟩
            rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
            exact ⟨⟨hu, hu⟩, rfl⟩
        rw [hEq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
      have hpt : ∀ p ∈ (U ×ˢ U).filter (fun p => p.1 = p.2),
          (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card = D.card := by
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
        simp
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, hcard_diag, mul_comm]
    have hoff : ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2),
        (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card ≤ κ * U.card ^ 2 := by
      have hpt : ∀ p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2),
          (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card ≤ κ := by
        intro p hp
        have hpU := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
        have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
        let diff := if p.1 ≤ p.2 then p.2 - p.1 else p.1 - p.2
        have hdiff_pos : 1 ≤ diff := by dsimp [diff]; split_ifs <;> omega
        have hdiff_le : diff ≤ H := by
          dsimp [diff]
          split_ifs with hle
          · exact hU_diam p.1 hpU.1 p.2 hpU.2 hle
          · exact hU_diam p.2 hpU.2 p.1 hpU.1 (by omega)
        have hsub : D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d)) ⊆
            D.filter (fun d => d ∣ diff) := by
          intro d hd
          have hdD := (Finset.mem_filter.mp hd).1
          have hmod := (Finset.mem_filter.mp hd).2
          refine Finset.mem_filter.mpr ⟨hdD, ?_⟩
          dsimp [diff]
          split_ifs with hle
          · rw [← ZMod.natCast_eq_zero_iff]
            have hcast : ((p.2 - p.1 : ℕ) : ZMod d) = (p.2 : ZMod d) - (p.1 : ZMod d) :=
              Nat.cast_sub hle
            rw [hcast, hmod, sub_self]
          · rw [← ZMod.natCast_eq_zero_iff]
            have hcast : ((p.1 - p.2 : ℕ) : ZMod d) = (p.1 : ZMod d) - (p.2 : ZMod d) :=
              Nat.cast_sub (by omega)
            rw [hcast, hmod, sub_self]
        exact le_trans (Finset.card_le_card hsub) (hκ diff hdiff_pos hdiff_le)
      calc ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2),
            (D.filter (fun d => (p.1 : ZMod d) = (p.2 : ZMod d))).card
          ≤ ∑ _p ∈ (U ×ˢ U).filter (fun p => p.1 ≠ p.2), κ := Finset.sum_le_sum hpt
        _ = ((U ×ˢ U).filter (fun p => p.1 ≠ p.2)).card * κ := by simp
        _ ≤ (U ×ˢ U).card * κ := Nat.mul_le_mul_right κ (Finset.card_filter_le _ _)
        _ = κ * U.card ^ 2 := by rw [Finset.card_product, sq, mul_comm]
    omega
  -- Step 8: Combine lower bound and upper bound in ℝ
  have hT_lower_real :
      (((ℓ - 1 : ℕ) : ℝ) / 2) * (4 * (D.card : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 -
        2 * (D.card : ℝ) * (ℓ : ℝ) * (U.card : ℝ)) ≤ (U.card : ℝ) * (T_good.card : ℝ) := by
    have hnat : (((ℓ - 1) * (4 * D.card ^ 2 * ℓ ^ 2) : ℕ) : ℝ) ≤
        ((U.card * (2 * T_good.card + (ℓ - 1) * (2 * D.card * ℓ)) : ℕ) : ℝ) := by
      exact_mod_cast hT_lower_nat
    push_cast at hnat
    linarith
  have hT_upper_real :
      (T_good.card : ℝ) ≤ (1 + Real.sqrt 2) * (K₁ : ℝ) *
        ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) := by
    have hsplit_r : (T_good.card : ℝ) ≤ (T1.card : ℝ) + (T2.card : ℝ) := by exact_mod_cast hT_split
    have hT1_r : (T1.card : ℝ) ≤ (K₁ : ℝ) * ∑ d ∈ D,
        (((U ×ˢ U).filter
          (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) := by
      have := hT1_bound
      exact_mod_cast this
    have hSmod_r : ∑ d ∈ D, (((U ×ˢ U).filter
        (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) ≤
        (D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2 := by
      exact_mod_cast hSmod_bound
    have hcoeff_nn : 0 ≤ (1 + Real.sqrt 2) * (K₁ : ℝ) := by positivity
    calc (T_good.card : ℝ) ≤ (T1.card : ℝ) + (T2.card : ℝ) := hsplit_r
      _ ≤ (K₁ : ℝ) * ∑ d ∈ D, (((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) +
          Real.sqrt 2 * (K₁ : ℝ) * ∑ d ∈ D, (((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) := add_le_add hT1_r hT2_bound
      _ = (1 + Real.sqrt 2) * (K₁ : ℝ) * ∑ d ∈ D, (((U ×ˢ U).filter
            (fun p => (p.1 : ZMod d) = (p.2 : ZMod d))).card : ℝ) := by ring
      _ ≤ (1 + Real.sqrt 2) * (K₁ : ℝ) *
            ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hSmod_r hcoeff_nn
  calc (((ℓ - 1 : ℕ) : ℝ) / 2) * (4 * (D.card : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 -
          2 * (D.card : ℝ) * (ℓ : ℝ) * (U.card : ℝ))
      ≤ (U.card : ℝ) * (T_good.card : ℝ) := hT_lower_real
    _ ≤ (U.card : ℝ) * ((1 + Real.sqrt 2) * (K₁ : ℝ) *
          ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hT_upper_real (Nat.cast_nonneg _)
    _ = (1 + Real.sqrt 2) * (K₁ : ℝ) * (U.card : ℝ) *
          ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) := by ring

/-- **Lemma A' (Division Form):** Exact absorbed 3-path modular reflection inequality when `U.Nonempty`. -/
theorem lemma_A_prime
    (D U : Finset ℕ) (a : ℕ → ℕ) (X : ℝ) (ℓ H κ K₁ : ℕ)
    (hX : 0 < X)
    (hD_dyad : ∀ d ∈ D, X / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X)
    (hℓ : 2 ≤ ℓ)
    (hU_ne : U.Nonempty)
    (hSU : ∀ d ∈ D, ∀ j < 2 * ℓ, a d + j * d ∈ U)
    (hU_diam : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → v - u ≤ H)
    (hκ : ∀ t : ℕ, 1 ≤ t → t ≤ H → (D.filter (fun d => d ∣ t)).card ≤ κ)
    (hK₁ : ∀ e ∈ D, 4 * e.divisors.card ≤ K₁) :
    (((ℓ - 1 : ℕ) : ℝ) / 2) * (4 * (D.card : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (U.card : ℝ) -
        2 * (D.card : ℝ) * (ℓ : ℝ))
      ≤ (1 + Real.sqrt 2) * (K₁ : ℝ) *
          ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) := by
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU_ne
  have hnodiv := lemma_A_prime_nodiv D U a X ℓ H κ K₁ hX hD_dyad hℓ hSU hU_diam hκ hK₁
  have hmul : (((ℓ - 1 : ℕ) : ℝ) / 2) * (4 * (D.card : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 / (U.card : ℝ) -
      2 * (D.card : ℝ) * (ℓ : ℝ)) * (U.card : ℝ) =
      (((ℓ - 1 : ℕ) : ℝ) / 2) * (4 * (D.card : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 -
        2 * (D.card : ℝ) * (ℓ : ℝ) * (U.card : ℝ)) := by
    field_simp [ne_of_gt hU_pos]
  nlinarith

/-! ### Section 3: Lemma B' — Uniform `|U|`-Elimination Principle for Absorbed Slices & Hall Framework -/

/-- **Lemma B' (Single-Slice Uniform `|U|`-Elimination for Absorbed Slices):**
Under the hypotheses of Lemma A' with `|D| ≤ M` (`M ≥ 0`) and `U.Nonempty`, uniformly for all `|U| ≥ 1`:
```
|D| / |U| ≤ 1 / ℓ + √(5 / 2) * (K₁ * M)^{1/2} / ℓ^{3/2} + (5 / 2)^{1/3} * (K₁ * κ * M)^{1/3} / ℓ.
``` -/
theorem lemma_B_prime_single
    (D U : Finset ℕ) (a : ℕ → ℕ) (X : ℝ) (ℓ H κ K₁ : ℕ) (M : ℝ)
    (hX : 0 < X)
    (hD_dyad : ∀ d ∈ D, X / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X)
    (hℓ : 2 ≤ ℓ)
    (hU_ne : U.Nonempty)
    (hM : (D.card : ℝ) ≤ M)
    (hSU : ∀ d ∈ D, ∀ j < 2 * ℓ, a d + j * d ∈ U)
    (hU_diam : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → v - u ≤ H)
    (hκ : ∀ t : ℕ, 1 ≤ t → t ≤ H → (D.filter (fun d => d ∣ t)).card ≤ κ)
    (hK₁ : ∀ e ∈ D, 4 * e.divisors.card ≤ K₁) :
    (D.card : ℝ) / (U.card : ℝ) ≤
      1 / (ℓ : ℝ) +
      Real.sqrt (5 / 2) * ((K₁ : ℝ) * M) ^ ((1 : ℝ) / 2) / (ℓ : ℝ) ^ ((3 : ℝ) / 2) +
      ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * ((K₁ : ℝ) * (κ : ℝ) * M) ^ ((1 : ℝ) / 3) / (ℓ : ℝ) := by
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU_ne
  have hℓ_ge2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hM_nn : 0 ≤ M := le_trans (Nat.cast_nonneg _) hM
  have hκ_nn : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg κ
  have hK₁_nn : (0 : ℝ) ≤ (K₁ : ℝ) := Nat.cast_nonneg K₁
  have hA := lemma_A_prime_nodiv D U a X ℓ H κ K₁ hX hD_dyad hℓ hSU hU_diam hκ hK₁
  have hsqrt2 : 1 + Real.sqrt 2 ≤ (5 : ℝ) / 2 := by
    have : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hℓ_sub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  rw [hℓ_sub] at hA
  have hℓ3 : (ℓ : ℝ) ^ 3 * (D.card : ℝ) ^ 2 ≤
      (ℓ : ℝ) ^ 2 * (D.card : ℝ) * (U.card : ℝ) +
      (5 / 2 : ℝ) * (K₁ : ℝ) * (D.card : ℝ) * (U.card : ℝ) ^ 2 +
      (5 / 2 : ℝ) * (K₁ : ℝ) * (κ : ℝ) * (U.card : ℝ) ^ 3 := by
    have hcoeff1 : (ℓ : ℝ) ^ 3 ≤ 2 * (ℓ : ℝ) ^ 2 * ((ℓ : ℝ) - 1) := by nlinarith
    have hcoeff2 : (((ℓ : ℝ) - 1) / 2) * (2 * (D.card : ℝ) * (ℓ : ℝ) * (U.card : ℝ)) ≤
        (ℓ : ℝ) ^ 2 * (D.card : ℝ) * (U.card : ℝ) := by
      have hnn : 0 ≤ (D.card : ℝ) * (ℓ : ℝ) * (U.card : ℝ) := by positivity
      nlinarith
    have hcoeff3 : (1 + Real.sqrt 2) * (K₁ : ℝ) * (U.card : ℝ) *
        ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) ≤
        (5 / 2 : ℝ) * (K₁ : ℝ) * (U.card : ℝ) *
          ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) := by
      have hnn : 0 ≤ (K₁ : ℝ) * (U.card : ℝ) *
          ((D.card : ℝ) * (U.card : ℝ) + (κ : ℝ) * (U.card : ℝ) ^ 2) := by positivity
      nlinarith
    nlinarith [sq_nonneg (D.card : ℝ)]
  -- Quadratic inequality for x = |D| / |U|
  set x : ℝ := (D.card : ℝ) / (U.card : ℝ)
  set A_q : ℝ := 1 / (ℓ : ℝ) + 5 * (K₁ : ℝ) * (U.card : ℝ) / (2 * (ℓ : ℝ) ^ 3)
  set B_q : ℝ := 5 * (K₁ : ℝ) * (κ : ℝ) * (U.card : ℝ) / (2 * (ℓ : ℝ) ^ 3)
  have hquad : x ^ 2 ≤ A_q * x + B_q := by
    have hden_pos : 0 < (ℓ : ℝ) ^ 3 * (U.card : ℝ) ^ 2 := by positivity
    have hmul : x ^ 2 * ((ℓ : ℝ) ^ 3 * (U.card : ℝ) ^ 2) ≤
        (A_q * x + B_q) * ((ℓ : ℝ) ^ 3 * (U.card : ℝ) ^ 2) := by
      have hL : x ^ 2 * ((ℓ : ℝ) ^ 3 * (U.card : ℝ) ^ 2) =
          (ℓ : ℝ) ^ 3 * (D.card : ℝ) ^ 2 := by
        dsimp [x]; field_simp [ne_of_gt hU_pos]
      have hR : (A_q * x + B_q) * ((ℓ : ℝ) ^ 3 * (U.card : ℝ) ^ 2) =
          (ℓ : ℝ) ^ 2 * (D.card : ℝ) * (U.card : ℝ) +
          (5 / 2 : ℝ) * (K₁ : ℝ) * (D.card : ℝ) * (U.card : ℝ) ^ 2 +
          (5 / 2 : ℝ) * (K₁ : ℝ) * (κ : ℝ) * (U.card : ℝ) ^ 3 := by
        dsimp [x, A_q, B_q]; field_simp [ne_of_gt hU_pos, ne_of_gt hℓ_pos]
      rw [hL, hR]
      exact hℓ3
    nlinarith
  have hx_le_quad : x ≤ A_q + Real.sqrt B_q :=
    quad_le_imp_le_add_sqrt (by positivity) (by positivity) hquad
  have hx_le_M : x ≤ M / (U.card : ℝ) := div_le_div_of_nonneg_right hM (le_of_lt hU_pos)
  set X_m : ℝ := M / (U.card : ℝ)
  set b_t : ℝ := 5 * (K₁ : ℝ) * (U.card : ℝ) / (2 * (ℓ : ℝ) ^ 3)
  set c_t : ℝ := Real.sqrt B_q
  have hx_min : x ≤ 1 / (ℓ : ℝ) + min X_m b_t + min X_m c_t := by
    have h1 : x ≤ min X_m (1 / (ℓ : ℝ) + b_t + c_t) :=
      le_min hx_le_M (by simpa [A_q, b_t, c_t] using hx_le_quad)
    exact le_trans h1 (min_add_three_le (by positivity) (by positivity) (by positivity) (Real.sqrt_nonneg _))
  -- Bound min X_m b_t ≤ √(5/2) * (K₁ * M)^(1/2) / ℓ^(3/2)
  have hb_bound : min X_m b_t ≤
      Real.sqrt (5 / 2) * ((K₁ : ℝ) * M) ^ ((1 : ℝ) / 2) / (ℓ : ℝ) ^ ((3 : ℝ) / 2) := by
    have h1 := min_le_rpow_mul_rpow (X := X_m) (Y := b_t) (p := 1 / 2) (q := 1 / 2)
      (by positivity) (by positivity) (by norm_num) (by norm_num) (by norm_num)
    refine le_trans h1 ?_
    have hprod : X_m * b_t = (5 / 2 : ℝ) * ((K₁ : ℝ) * M) / (ℓ : ℝ) ^ 3 := by
      dsimp [X_m, b_t]; field_simp [ne_of_gt hU_pos, ne_of_gt hℓ_pos]
    have hmul_rpow : X_m ^ ((1 : ℝ) / 2) * b_t ^ ((1 : ℝ) / 2) = (X_m * b_t) ^ ((1 : ℝ) / 2) :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    rw [hmul_rpow, hprod, Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow]
    have hℓ32 : ((ℓ : ℝ) ^ 3) ^ ((1 : ℝ) / 2) = (ℓ : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (ℓ : ℝ) 3, ← Real.rpow_mul (le_of_lt hℓ_pos)]
      norm_num
    rw [hℓ32]
  -- Bound min X_m c_t ≤ (5/2)^(1/3) * (K₁ * κ * M)^(1/3) / ℓ
  have hc_bound : min X_m c_t ≤
      ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * ((K₁ : ℝ) * (κ : ℝ) * M) ^ ((1 : ℝ) / 3) / (ℓ : ℝ) := by
    have h1 := min_le_rpow_mul_rpow (X := X_m) (Y := c_t) (p := 1 / 3) (q := 2 / 3)
      (by positivity) (Real.sqrt_nonneg _) (by norm_num) (by norm_num) (by norm_num)
    refine le_trans h1 ?_
    have hc23 : c_t ^ ((2 : ℝ) / 3) = B_q ^ ((1 : ℝ) / 3) := by
      dsimp [c_t]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hc23, ← Real.mul_rpow (by positivity) (by positivity)]
    have hprod : X_m * B_q = ((5 : ℝ) / 2) * ((K₁ : ℝ) * (κ : ℝ) * M) / (ℓ : ℝ) ^ 3 := by
      dsimp [X_m, B_q]; field_simp [ne_of_gt hU_pos, ne_of_gt hℓ_pos]
    rw [hprod, Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) (by positivity)]
    have hℓ1 : ((ℓ : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (ℓ : ℝ) := by
      rw [← Real.rpow_natCast (ℓ : ℝ) 3, ← Real.rpow_mul (le_of_lt hℓ_pos)]
      norm_num
    rw [hℓ1]
  linarith

/-- **Lemma B' (Partitioned Uniform Hall Criterion for Absorbed Slices):**
If `S ⊆ ℕ` is covered by dyadic slices `slice α ⊆ (X α / 2, X α]` (`α ∈ idx`), each with
AP half-length `ℓ α ≥ 2` inside `U` of diameter `≤ H`, size `|slice α| ≤ M α`, divisor multiplicity
`≤ κ α` (`κ α ≥ 1`), and `4 * τ(e) ≤ K₁ α` for all `e ∈ slice α`, and if
`∑ α ∈ idx, (K₁ α * κ α * M α)^(1/3) / ℓ α ≤ 1/10` and `∑ α ∈ idx, 1 / ℓ α ≤ 1/10`,
then `S.card ≤ U.card`. -/
theorem lemma_B_prime
    {ι : Type*} (idx : Finset ι)
    (S U : Finset ℕ) (slice : ι → Finset ℕ) (a : ι → ℕ → ℕ)
    (X : ι → ℝ) (ℓ κ K₁ : ι → ℕ) (M : ι → ℝ) (H : ℕ)
    (hcover : S ⊆ idx.biUnion slice)
    (hX : ∀ α ∈ idx, 0 < X α)
    (hdyad : ∀ α ∈ idx, ∀ d ∈ slice α, X α / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X α)
    (hℓ : ∀ α ∈ idx, 2 ≤ ℓ α)
    (hκ_pos : ∀ α ∈ idx, 1 ≤ κ α)
    (hM : ∀ α ∈ idx, ((slice α).card : ℝ) ≤ M α)
    (hSU : ∀ α ∈ idx, ∀ d ∈ slice α, ∀ j < 2 * ℓ α, a α d + j * d ∈ U)
    (hU_diam : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → v - u ≤ H)
    (hκ : ∀ α ∈ idx, ∀ t : ℕ, 1 ≤ t → t ≤ H → ((slice α).filter (fun d => d ∣ t)).card ≤ κ α)
    (hK₁ : ∀ α ∈ idx, ∀ e ∈ slice α, 4 * e.divisors.card ≤ K₁ α)
    (hSum1 : ∑ α ∈ idx, ((K₁ α : ℝ) * (κ α : ℝ) * M α) ^ ((1 : ℝ) / 3) / (ℓ α : ℝ) ≤ 1 / 10)
    (hSum0 : ∑ α ∈ idx, (1 : ℝ) / (ℓ α : ℝ) ≤ 1 / 10) :
    S.card ≤ U.card := by
  by_cases hS_empty : S.card = 0
  · omega
  obtain ⟨d₀, hd₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hS_empty)
  rcases Finset.mem_biUnion.mp (hcover hd₀) with ⟨α₀, hα₀, hd₀_slice⟩
  have hU_ne : U.Nonempty :=
    ⟨a α₀ d₀ + 0 * d₀, hSU α₀ hα₀ d₀ hd₀_slice 0 (by have := hℓ α₀ hα₀; omega)⟩
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU_ne
  have hS_le_sum : (S.card : ℝ) ≤ ∑ α ∈ idx, ((slice α).card : ℝ) := by
    have hnat : S.card ≤ ∑ α ∈ idx, (slice α).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    exact_mod_cast hnat
  let x : ι → ℝ := fun α => ((K₁ α : ℝ) * (κ α : ℝ) * M α) ^ ((1 : ℝ) / 3) / (ℓ α : ℝ)
  have hx_nn : ∀ α ∈ idx, 0 ≤ x α := by
    intro α hα
    have hM_nn : 0 ≤ M α := le_trans (Nat.cast_nonneg _) (hM α hα)
    dsimp [x]; positivity
  have hslice_le : ∀ α ∈ idx,
      ((slice α).card : ℝ) / (U.card : ℝ) ≤
        1 / (ℓ α : ℝ) +
        Real.sqrt (5 / 2) * (x α) ^ ((3 : ℝ) / 2) +
        ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * x α := by
    intro α hα
    have hB := lemma_B_prime_single (slice α) U (a α) (X α) (ℓ α) H (κ α) (K₁ α) (M α)
      (hX α hα) (hdyad α hα) (hℓ α hα) hU_ne (hM α hα) (hSU α hα) hU_diam (hκ α hα) (hK₁ α hα)
    refine le_trans hB ?_
    have hM_nn : 0 ≤ M α := le_trans (Nat.cast_nonneg _) (hM α hα)
    have hκ1 : (1 : ℝ) ≤ (κ α : ℝ) := by exact_mod_cast hκ_pos α hα
    have hK₁_nn : (0 : ℝ) ≤ (K₁ α : ℝ) := Nat.cast_nonneg _
    have hℓ_pos : (0 : ℝ) < (ℓ α : ℝ) := by have := hℓ α hα; exact_mod_cast (by omega : 0 < ℓ α)
    have hx32 : ((K₁ α : ℝ) * M α) ^ ((1 : ℝ) / 2) / (ℓ α : ℝ) ^ ((3 : ℝ) / 2) ≤
        (x α) ^ ((3 : ℝ) / 2) := by
      have hx_eq : (x α) ^ ((3 : ℝ) / 2) =
          ((K₁ α : ℝ) * (κ α : ℝ) * M α) ^ ((1 : ℝ) / 2) / (ℓ α : ℝ) ^ ((3 : ℝ) / 2) := by
        dsimp [x]
        rw [Real.div_rpow (by positivity) (le_of_lt hℓ_pos),
          ← Real.rpow_mul (by positivity)]
        norm_num
      rw [hx_eq]
      refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hℓ_pos) _)
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have h1 : (K₁ α : ℝ) * M α = (K₁ α : ℝ) * 1 * M α := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ1 hK₁_nn) hM_nn
    have hsq52_nn : 0 ≤ Real.sqrt (5 / 2) := Real.sqrt_nonneg _
    have hmul_le : Real.sqrt (5 / 2) * ((K₁ α : ℝ) * M α) ^ ((1 : ℝ) / 2) / (ℓ α : ℝ) ^ ((3 : ℝ) / 2) ≤
        Real.sqrt (5 / 2) * (x α) ^ ((3 : ℝ) / 2) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hx32 hsq52_nn
    have h3eq : ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * ((K₁ α : ℝ) * (κ α : ℝ) * M α) ^ ((1 : ℝ) / 3) / (ℓ α : ℝ) =
        ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * x α := by
      dsimp [x]; ring
    linarith
  have hratio_lt : (S.card : ℝ) / (U.card : ℝ) < 1 := by
    have h1 : (S.card : ℝ) / (U.card : ℝ) ≤ ∑ α ∈ idx, ((slice α).card : ℝ) / (U.card : ℝ) := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right hS_le_sum (le_of_lt hU_pos)
    have h2 : ∑ α ∈ idx, ((slice α).card : ℝ) / (U.card : ℝ) ≤
        (∑ α ∈ idx, (1 : ℝ) / (ℓ α : ℝ)) +
        Real.sqrt (5 / 2) * (∑ α ∈ idx, (x α) ^ ((3 : ℝ) / 2)) +
        ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * (∑ α ∈ idx, x α) := by
      calc ∑ α ∈ idx, ((slice α).card : ℝ) / (U.card : ℝ)
          ≤ ∑ α ∈ idx, (1 / (ℓ α : ℝ) + Real.sqrt (5 / 2) * (x α) ^ ((3 : ℝ) / 2) +
              ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * x α) := Finset.sum_le_sum hslice_le
        _ = (∑ α ∈ idx, (1 : ℝ) / (ℓ α : ℝ)) +
            Real.sqrt (5 / 2) * (∑ α ∈ idx, (x α) ^ ((3 : ℝ) / 2)) +
            ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * (∑ α ∈ idx, x α) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h3 : ∑ α ∈ idx, (x α) ^ ((3 : ℝ) / 2) ≤ (∑ α ∈ idx, x α) ^ ((3 : ℝ) / 2) :=
      sum_rpow_three_halves_le idx x hx_nn
    have hSum1_nn : 0 ≤ ∑ α ∈ idx, x α := Finset.sum_nonneg hx_nn
    have hSum1_32 : (∑ α ∈ idx, x α) ^ ((3 : ℝ) / 2) ≤ ((1 : ℝ) / 10) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hSum1_nn hSum1 (by norm_num)
    have hsq52 : Real.sqrt (5 / 2) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h10_32 : ((1 : ℝ) / 10) ^ ((3 : ℝ) / 2) ≤ 1 / 10 := by
      calc ((1 : ℝ) / 10) ^ ((3 : ℝ) / 2)
          ≤ ((1 : ℝ) / 10) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
        _ = 1 / 10 := Real.rpow_one _
    have h52_13 : ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) ≤ 2 := by
      have hpow : (((5 : ℝ) / 2) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast (((5 : ℝ) / 2) ^ ((1 : ℝ) / 3)) 3,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      by_contra hgt
      push Not at hgt
      have : (2 : ℝ) ^ (3 : ℕ) < (((5 : ℝ) / 2) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) :=
        pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
      linarith
    have hterm2 : Real.sqrt (5 / 2) * (∑ α ∈ idx, (x α) ^ ((3 : ℝ) / 2)) ≤ 2 / 10 := by
      have hle1 := le_trans h3 hSum1_32
      have hle2 := le_trans hle1 h10_32
      have hnn : 0 ≤ ∑ α ∈ idx, (x α) ^ ((3 : ℝ) / 2) :=
        Finset.sum_nonneg fun α hα => Real.rpow_nonneg (hx_nn α hα) _
      nlinarith
    have hterm3 : ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) * (∑ α ∈ idx, x α) ≤ 2 / 10 := by
      have hnn : 0 ≤ ((5 : ℝ) / 2) ^ ((1 : ℝ) / 3) := by positivity
      nlinarith
    linarith
  have hlt_real : (S.card : ℝ) < (U.card : ℝ) := (div_lt_one hU_pos).mp hratio_lt
  exact_mod_cast le_of_lt hlt_real

/-- In `(m, m + H]`, every `d ∈ [1, N]` has an arithmetic progression of length `2 * ℓ` inside
`(m, m + H] ∩ dℤ` whenever `2 * ℓ * N ≤ H`. -/
private lemma exists_ap_in_Ioc (m H N ℓ d : ℕ) (hd1 : 1 ≤ d) (hdN : d ≤ N)
    (h2ℓN : 2 * ℓ * N ≤ H) :
    ∃ a : ℕ, ∀ j < 2 * ℓ, m < a + j * d ∧ a + j * d ≤ m + H ∧ d ∣ (a + j * d) := by
  obtain ⟨a, ha_gt, ha_le, ha_dvd⟩ := exists_multiple_in_block m d d hd1 (le_refl d)
  refine ⟨a, fun j hj => ⟨by omega, ?_, dvd_add ha_dvd (dvd_mul_left d j)⟩⟩
  have h1 : (j + 1) * d ≤ 2 * ℓ * N := Nat.mul_le_mul (by omega) hdN
  have h2 : a + j * d ≤ m + (j + 1) * d := by
    have : (j + 1) * d = d + j * d := by ring
    omega
  omega

/-- Hall's Marriage Theorem wrapper for closed-right interval `(m, m + H]` on any `A ⊆ Icc 1 n`. -/
private lemma exists_distinct_multiples_of_hall (A : Finset ℕ) (m H : ℕ)
    (hHall : ∀ S : Finset ℕ, S ⊆ A →
      S.card ≤ ((Finset.Ioc m (m + H)).filter (fun t => ∃ k ∈ S, k ∣ t)).card) :
    ∃ a : ℕ → ℕ,
      (∀ i ∈ A, ∀ j ∈ A, a i = a j → i = j) ∧
      (∀ k ∈ A, m < a k ∧ a k ≤ m + H ∧ k ∣ a k) := by
  classical
  let t : { k : ℕ // k ∈ A } → Finset ℕ :=
    fun k => (Finset.Ioc m (m + H)).filter (fun x => k.1 ∣ x)
  have hH : ∀ s : Finset { k : ℕ // k ∈ A }, s.card ≤ (s.biUnion t).card := by
    intro s
    let S : Finset ℕ := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hS_sub : S ⊆ A := by
      intro k hk
      rcases Finset.mem_map.mp hk with ⟨⟨k', hk'⟩, _, rfl⟩
      exact hk'
    have hEq : s.biUnion t = (Finset.Ioc m (m + H)).filter (fun x => ∃ k ∈ S, k ∣ x) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, t, S, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨k, hk, hxIoc, hdvd⟩
        exact ⟨hxIoc, k.1, ⟨k, hk, rfl⟩, hdvd⟩
      · rintro ⟨hxIoc, _, ⟨k, hk, rfl⟩, hdvd⟩
        exact ⟨k, hk, hxIoc, hdvd⟩
    rw [hEq, ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
    exact hHall S hS_sub
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hH
  refine ⟨fun k => if h : k ∈ A then f ⟨k, h⟩ else 0, ?_, ?_⟩
  · intro i hi j hj hEq
    simp only [hi, hj, dite_true] at hEq
    exact congrArg Subtype.val (hf_inj hEq)
  · intro k hk
    simp only [hk, dite_true]
    have hflt := Finset.mem_filter.mp (hf_mem ⟨k, hk⟩)
    have hIoc := Finset.mem_Ioc.mp hflt.1
    exact ⟨hIoc.1, hIoc.2, hflt.2⟩

/-- Elementary trivial bound: for any `A ⊆ Icc 1 n` and `H ≥ n * A.card` (in particular `H = n^2`),
`(m, m + H]` contains distinct multiples for all `k ∈ A`. -/
private lemma exists_distinct_multiples_trivial_sq (A : Finset ℕ) (n m H : ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hH : n * n ≤ H) :
    ∃ a : ℕ → ℕ,
      (∀ i ∈ A, ∀ j ∈ A, a i = a j → i = j) ∧
      (∀ k ∈ A, m < a k ∧ a k ≤ m + H ∧ k ∣ a k) := by
  refine exists_distinct_multiples_of_hall A m H fun S hS => ?_
  by_cases hSe : S.card = 0
  · omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hSe)
  have hk_Icc := Finset.mem_Icc.mp (hA (hS hk))
  have hk1 : 1 ≤ k := hk_Icc.1
  have hkn : k ≤ n := hk_Icc.2
  obtain ⟨a₀, ha₀_gt, ha₀_le, ha₀_dvd⟩ := exists_multiple_in_block m k k hk1 (le_refl k)
  -- The n elements {a₀ + j * k : j < n} all lie in the neighborhood of S
  let img := (Finset.range n).image (fun j => a₀ + j * k)
  have himg_sub : img ⊆ (Finset.Ioc m (m + H)).filter (fun t => ∃ d ∈ S, d ∣ t) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    have hj_lt : j < n := Finset.mem_range.mp hj
    have h1 : (j + 1) * k ≤ n * n := Nat.mul_le_mul (by omega) hkn
    have h2 : a₀ + j * k ≤ m + (j + 1) * k := by
      have : (j + 1) * k = k + j * k := by ring
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, k, hk, dvd_add ha₀_dvd (dvd_mul_left k j)⟩
  have himg_card : img.card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j₁ _ j₂ _ hEq
    dsimp only at hEq
    have : j₁ * k = j₂ * k := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < k) this
  have hS_le_n : S.card ≤ n := by
    calc S.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card (Finset.Subset.trans hS hA)
      _ = n := by simp
  calc S.card ≤ n := hS_le_n
    _ = img.card := himg_card.symm
    _ ≤ ((Finset.Ioc m (m + H)).filter (fun t => ∃ d ∈ S, d ∣ t)).card :=
        Finset.card_le_card himg_sub

/-! ### Section 4: Elementary Chebyshev Primorial, Prime Reciprocal Sums & Lemma C1 -/

/-- Product of pairwise coprime divisors divides the target in `ℕ`. -/
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
      · -- Even N = m + m ≥ 4, so N is not prime
        have hN_not_prime : ¬ Nat.Prime N := by
          intro hp
          have h2dvd : 2 ∣ N := ⟨m, by omega⟩
          have h2eq : 2 = N := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd
          omega
        have hEq : (Finset.Icc 1 N).filter Nat.Prime = (Finset.Icc 1 (N - 1)).filter Nat.Prime := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨h1, h2⟩, hp⟩
            refine ⟨⟨h1, ?_⟩, hp⟩
            by_contra hgt
            have : p = N := by omega
            subst this; exact hN_not_prime hp
          · rintro ⟨⟨h1, h2⟩, hp⟩
            exact ⟨⟨h1, by omega⟩, hp⟩
        rw [hEq]
        calc ∏ p ∈ (Finset.Icc 1 (N - 1)).filter Nat.Prime, p
            ≤ 4 ^ (N - 1) := ih (N - 1) (by omega)
          _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
      · -- Odd N = 2 * m + 1 with m ≥ 1
        have hm1 : 1 ≤ m := by omega
        let P1 := (Finset.Icc 1 (m + 1)).filter Nat.Prime
        let P2 := (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime
        have hdisj : Disjoint P1 P2 := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
          have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).1
          omega
        have hunion : (Finset.Icc 1 N).filter Nat.Prime = P1 ∪ P2 := by
          ext p
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, P1, P2]
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
        -- Every prime p ∈ P2 divides Nat.choose (2 * m + 1) m
        have hdvd_each : ∀ p ∈ P2, p ∣ Nat.choose (2 * m + 1) m := by
          intro p hp
          have hp_Ioc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
          have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
          have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m + 1)
          have hsub : 2 * m + 1 - m = m + 1 := by omega
          rw [hsub] at hfac
          have hp_dvd_top : p ∣ (2 * m + 1).factorial :=
            (Nat.Prime.dvd_factorial hp_prime).mpr hp_Ioc.2
          rw [← hfac] at hp_dvd_top
          have hp_not_m1 : ¬ p ∣ (m + 1).factorial := by
            rw [Nat.Prime.dvd_factorial hp_prime]; omega
          have hp_not_m : ¬ p ∣ m.factorial := by
            rw [Nat.Prime.dvd_factorial hp_prime]; omega
          rcases hp_prime.dvd_mul.mp hp_dvd_top with h1 | h2
          · rcases hp_prime.dvd_mul.mp h1 with h11 | h12
            · exact h11
            · exact (hp_not_m h12).elim
          · exact (hp_not_m1 h2).elim
        have hcop : (P2 : Set ℕ).Pairwise (fun p q => Nat.Coprime p q) := by
          intro p hp q hq hpq
          exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
        have hprod_dvd : ∏ p ∈ P2, p ∣ Nat.choose (2 * m + 1) m :=
          nat_prod_dvd_of_coprime P2 id (Nat.choose (2 * m + 1) m) hcop hdvd_each
        have hch_pos : 0 < Nat.choose (2 * m + 1) m := Nat.choose_pos (by omega)
        have hP2_le_ch : ∏ p ∈ P2, p ≤ Nat.choose (2 * m + 1) m :=
          Nat.le_of_dvd hch_pos hprod_dvd
        -- 2 * choose (2m + 1) m ≤ 2 ^ (2m + 1) ⟹ choose (2m + 1) m ≤ 4 ^ m
        have hch_le : Nat.choose (2 * m + 1) m ≤ 4 ^ m := by
          have hsum := Nat.sum_range_choose (2 * m + 1)
          have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
            have := Nat.choose_symm (by omega : m ≤ 2 * m + 1)
            simpa [show 2 * m + 1 - m = m + 1 by omega] using this
          have hpair : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (2 * m + 2) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
          have hle_sum : Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) ≤
              ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k := by
            have hne : m ≠ m + 1 := by omega
            have h2 := Finset.sum_le_sum_of_subset (f := fun k => Nat.choose (2 * m + 1) k) hpair
            simpa [Finset.sum_pair hne] using h2
          rw [hsum, hsymm] at hle_sum
          have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
            rw [pow_succ, pow_mul]; norm_num; ring
          omega
        have hP2 : ∏ p ∈ P2, p ≤ 4 ^ m := le_trans hP2_le_ch hch_le
        calc (∏ p ∈ P1, p) * (∏ p ∈ P2, p)
            ≤ 4 ^ (m + 1) * 4 ^ m := Nat.mul_le_mul hP1 hP2
          _ = 4 ^ (2 * m + 1) := by rw [← pow_add]; congr 1; omega
          _ = 4 ^ N := by rw [hm]

/-- Dyadic prime count bound: for `r : ℕ`, `r * #{p ∈ (2^r, 2^(r+1)] | p.Prime} ≤ 4 * 2^r`. -/
private lemma card_primes_dyadic_le (r : ℕ) :
    r * ((Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime).card ≤ 4 * 2 ^ r := by
  let S := (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hsub : S ⊆ (Finset.Icc 1 (2 ^ (r + 1))).filter Nat.Prime := by
    intro p hp
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, (Finset.mem_filter.mp hp).2⟩
  have hpow_le : 2 ^ (r * S.card) ≤ 2 ^ (4 * 2 ^ r) := by
    calc 2 ^ (r * S.card) = (2 ^ r) ^ S.card := by rw [pow_mul]
      _ = ∏ _p ∈ S, 2 ^ r := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' fun p hp =>
            le_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      _ ≤ ∏ p ∈ (Finset.Icc 1 (2 ^ (r + 1))).filter Nat.Prime, p :=
            Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
              Nat.Prime.one_le (Finset.mem_filter.mp hp).2
      _ ≤ 4 ^ (2 ^ (r + 1)) := prod_primes_le_four_pow (2 ^ (r + 1))
      _ = 2 ^ (4 * 2 ^ r) := by
            have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
            rw [h4, ← pow_mul, pow_succ]
            congr 1; ring
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le

/-- Dyadic prime reciprocal sum: for `r ≥ 1`, `∑_{2^r < p ≤ 2^(r+1)} 1/p ≤ 4 / r`. -/
private lemma sum_inv_primes_dyadic_le (r : ℕ) (hr : 1 ≤ r) :
    ∑ p ∈ (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 4 / (r : ℝ) := by
  let S := (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h2r_pos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
  have hpt : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ r : ℕ) : ℝ) := by
    intro p hp
    have hp_gt : 2 ^ r < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact one_div_le_one_div_of_le h2r_pos (by exact_mod_cast le_of_lt hp_gt)
  have hcard : (r : ℝ) * (S.card : ℝ) ≤ 4 * ((2 ^ r : ℕ) : ℝ) := by
    exact_mod_cast card_primes_dyadic_le r
  calc ∑ p ∈ S, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _p ∈ S, (1 : ℝ) / ((2 ^ r : ℕ) : ℝ) := Finset.sum_le_sum hpt
    _ = (S.card : ℝ) / ((2 ^ r : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ 4 / (r : ℝ) := by
        rw [div_le_div_iff₀ h2r_pos hr_pos]
        linarith

/-- Doubly-exponential bucket prime reciprocal sum: for every `m : ℕ`,
`∑_{2^(2^m) < p ≤ 2^(2^(m+1))} 1/p ≤ 4`. -/
private lemma sum_inv_primes_bucket_le (m : ℕ) :
    ∑ p ∈ (Finset.Ioc (2 ^ (2 ^ m)) (2 ^ (2 ^ (m + 1)))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 4 := by
  let B := (Finset.Ioc (2 ^ (2 ^ m)) (2 ^ (2 ^ (m + 1)))).filter Nat.Prime
  let I := Finset.Ico (2 ^ m) (2 ^ (m + 1))
  let F : ℕ → Finset ℕ := fun r => (Finset.Ioc (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  have hsub : B ⊆ I.biUnion F := by
    intro p hp
    have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    -- Let r = Nat.log 2 (p - 1); since 2^(2^m) < p ≤ 2^(2^(m+1)), 2^m ≤ r < 2^(m+1)
    let r := Nat.log 2 (p - 1)
    have hp1_pos : 1 ≤ p - 1 := by
      have : 2 ^ (2 ^ m) ≥ 2 := by
        have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) h1)
      omega
    have hr_le : 2 ^ r ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
    have hr_lt : p - 1 < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
    have hr_ge : 2 ^ m ≤ r := by
      exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    have hr_ub : r < 2 ^ (m + 1) := by
      by_contra hge
      push Not at hge
      have : 2 ^ (2 ^ (m + 1)) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hge
      omega
    refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_Ico.mpr ⟨hr_ge, hr_ub⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hp_prime⟩
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) F := by
    intro r₁ _ r₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1
    have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (r₁ + 1) ≤ 2 ^ r₂ := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    · have : 2 ^ (r₂ + 1) ≤ 2 ^ r₁ := Nat.pow_le_pow_right (by norm_num) hgt
      omega
  have h2m_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
  calc ∑ p ∈ B, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ I.biUnion F, (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ r ∈ I, ∑ p ∈ F r, (1 : ℝ) / (p : ℝ) := Finset.sum_biUnion hdisj
    _ ≤ ∑ r ∈ I, (4 : ℝ) / (r : ℝ) := by
        refine Finset.sum_le_sum fun r hr => sum_inv_primes_dyadic_le r ?_
        have := (Finset.mem_Ico.mp hr).1
        have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        omega
    _ ≤ ∑ _r ∈ I, (4 : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr_ge : 2 ^ m ≤ r := (Finset.mem_Ico.mp hr).1
        exact div_le_div_of_nonneg_left (by norm_num) h2m_pos (by exact_mod_cast hr_ge)
    _ = (I.card : ℝ) * ((4 : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 4 := by
        have hIcard : I.card = 2 ^ m := by
          rw [Nat.card_Ico, pow_succ]
          omega
        rw [hIcard]
        field_simp [ne_of_gt h2m_pos]

/-- Mertens-style upper bound on prime reciprocals: for all `X : ℕ`,
`∑_{p ≤ X} 1/p ≤ 5 + 4 * Nat.log 2 (Nat.log 2 X)`. -/
private lemma sum_inv_primes_le (X : ℕ) :
    ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      5 + 4 * (Nat.log 2 (Nat.log 2 X) : ℝ) := by
  let M := Nat.log 2 (Nat.log 2 X)
  let B : ℕ → Finset ℕ := fun m => (Finset.Ioc (2 ^ (2 ^ m)) (2 ^ (2 ^ (m + 1)))).filter Nat.Prime
  have hsub : (Finset.Icc 1 X).filter Nat.Prime ⊆ {2} ∪ (Finset.range (M + 1)).biUnion B := by
    intro p hp
    have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    by_cases hp2 : p = 2
    · exact Finset.mem_union_left _ (by simp [hp2])
    · have hp_gt2 : 2 < p := by have := hp_prime.two_le; omega
      refine Finset.mem_union_right _ ?_
      let r := Nat.log 2 (p - 1)
      have hr_pos : 1 ≤ r := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hr_le : 2 ^ r ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
      have hr_lt : p - 1 < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
      let m := Nat.log 2 r
      have hm_le : 2 ^ m ≤ r := Nat.pow_log_le_self 2 (by omega)
      have hm_lt : r < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
      have hm_le_M : m ≤ M := by
        have hr_le_logX : r ≤ Nat.log 2 X := Nat.log_mono_right (by omega)
        exact Nat.log_mono_right hr_le_logX
      refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hp_prime⟩
      · have : 2 ^ (2 ^ m) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hm_le
        omega
      · have : 2 ^ (r + 1) ≤ 2 ^ (2 ^ (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
  have hdisj : Set.PairwiseDisjoint (Finset.range (M + 1) : Set ℕ) B := by
    intro m₁ _ m₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1
    have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (2 ^ (m₁ + 1)) ≤ 2 ^ (2 ^ m₂) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hlt)
      omega
    · have : 2 ^ (2 ^ (m₂ + 1)) ≤ 2 ^ (2 ^ m₁) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hgt)
      omega
  have h2_not_in : (2 : ℕ) ∉ (Finset.range (M + 1)).biUnion B := by
    intro hmem
    rcases Finset.mem_biUnion.mp hmem with ⟨m, _, hm⟩
    have hgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    have h2 : 2 ≤ 2 ^ (2 ^ m) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega
  calc ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ ({2} ∪ (Finset.range (M + 1)).biUnion B), (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (1 : ℝ) / 2 + ∑ p ∈ (Finset.range (M + 1)).biUnion B, (1 : ℝ) / (p : ℝ) := by
        rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr h2_not_in), Finset.sum_singleton]
        norm_num
    _ = (1 : ℝ) / 2 + ∑ m ∈ Finset.range (M + 1), ∑ p ∈ B m, (1 : ℝ) / (p : ℝ) := by
        rw [Finset.sum_biUnion hdisj]
    _ ≤ (1 : ℝ) / 2 + ∑ _m ∈ Finset.range (M + 1), (4 : ℝ) := by
        gcongr with m _
        exact sum_inv_primes_bucket_le m
    _ = (1 : ℝ) / 2 + 4 * ((M + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 5 + 4 * (M : ℝ) := by push_cast; linarith

/-- Elementary Chebyshev upper bound: for all `N ≥ 2`, `π(N) ≤ 6 * N / log N`. -/
private lemma primeCounting_le_six_div_log (N : ℕ) (hN : 2 ≤ N) :
    (((Finset.Icc 1 N).filter Nat.Prime).card : ℝ) ≤ 6 * (N : ℝ) / Real.log (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let s := Nat.sqrt N
  let Slo := (Finset.Icc 1 s).filter Nat.Prime
  let Shi := (Finset.Ioc s N).filter Nat.Prime
  have hcard_le : ((Finset.Icc 1 N).filter Nat.Prime).card ≤ Slo.card + Shi.card := by
    have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Slo ∪ Shi := by
      intro p hp
      have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      have hp_prime := (Finset.mem_filter.mp hp).2
      by_cases hle : p ≤ s
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hIcc.1, hle⟩, hp_prime⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hIcc.2⟩, hp_prime⟩)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le Slo Shi)
  -- Bound Slo.card ≤ s ≤ √N ≤ 2 * N / log N
  have hSlo : (Slo.card : ℝ) ≤ 2 * (N : ℝ) / Real.log (N : ℝ) := by
    have h1 : Slo.card ≤ s := by
      calc Slo.card ≤ (Finset.Icc 1 s).card := Finset.card_filter_le _ _
        _ = s := by simp
    have h2 : (s : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg s) (le_of_lt hN_pos)]
      have hsq : s * s ≤ N := Nat.sqrt_le N
      have : (s : ℝ) * (s : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsq
      nlinarith
    have hlog_sqrt : Real.log (Real.sqrt (N : ℝ)) ≤ Real.sqrt (N : ℝ) := by
      have hsq_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
      linarith [Real.log_le_sub_one_of_pos hsq_pos]
    have hlog_eq : Real.log (N : ℝ) = 2 * Real.log (Real.sqrt (N : ℝ)) := by
      rw [Real.log_sqrt (le_of_lt hN_pos)]; ring
    have hmul : Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ 2 * (N : ℝ) := by
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt (le_of_lt hN_pos)
      have hnn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have h3 : Real.sqrt (N : ℝ) ≤ 2 * (N : ℝ) / Real.log (N : ℝ) :=
      (le_div_iff₀ hlogN_pos).mpr hmul
    exact le_trans (by exact_mod_cast h1) (le_trans h2 h3)
  -- Bound Shi.card ≤ 4 * N / log N using (√N)^{Shi.card} ≤ ∏_{p ∈ Shi} p ≤ 4^N
  have hShi : (Shi.card : ℝ) ≤ 4 * (N : ℝ) / Real.log (N : ℝ) := by
    have hsub : Shi ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
      intro p hp
      have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hIoc.2⟩, (Finset.mem_filter.mp hp).2⟩
    have hprod_nat : ∏ p ∈ Shi, p ≤ 4 ^ N :=
      le_trans (Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
        Nat.Prime.one_le (Finset.mem_filter.mp hp).2) (prod_primes_le_four_pow N)
    have hpow_le : (Real.sqrt (N : ℝ)) ^ Shi.card ≤ (4 : ℝ) ^ N := by
      have h1 : (Real.sqrt (N : ℝ)) ^ Shi.card = ∏ _p ∈ Shi, Real.sqrt (N : ℝ) := by simp
      rw [h1]
      have h2 : ∏ _p ∈ Shi, Real.sqrt (N : ℝ) ≤ ∏ p ∈ Shi, (p : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun p hp => ?_
        have hgt : s < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        have hsq : N < p * p := by
          have : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
          nlinarith
        rw [Real.sqrt_le_left (Nat.cast_nonneg p)]
        have : (N : ℝ) ≤ (p : ℝ) * (p : ℝ) := by exact_mod_cast le_of_lt hsq
        nlinarith
      have h3 : (∏ p ∈ Shi, (p : ℝ)) ≤ (4 : ℝ) ^ N := by
        have hcast : ((∏ p ∈ Shi, p : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by exact_mod_cast hprod_nat
        simpa [Nat.cast_prod] using hcast
      exact le_trans h2 h3
    have hsq_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    have hlog_le : Real.log ((Real.sqrt (N : ℝ)) ^ Shi.card) ≤ Real.log ((4 : ℝ) ^ N) :=
      Real.log_le_log (pow_pos hsq_pos _) hpow_le
    rw [Real.log_pow, Real.log_pow, Real.log_sqrt (le_of_lt hN_pos)] at hlog_le
    have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
      have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      rw [h4, Real.log_pow]
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      push_cast; linarith
    have hmul : (Shi.card : ℝ) * Real.log (N : ℝ) ≤ 4 * (N : ℝ) := by nlinarith
    exact (le_div_iff₀ hlogN_pos).mpr hmul
  have hcast : (((Finset.Icc 1 N).filter Nat.Prime).card : ℝ) ≤ (Slo.card : ℝ) + (Shi.card : ℝ) := by
    exact_mod_cast hcard_le
  have hsum : 2 * (N : ℝ) / Real.log (N : ℝ) + 4 * (N : ℝ) / Real.log (N : ℝ) =
      6 * (N : ℝ) / Real.log (N : ℝ) := by ring
  linarith

/-- Mertens Euler product upper bound: for `n : ℕ`,
`∏_{p ≤ n} (1 - 1/p)⁻¹ ≤ exp(10 + 8 * Nat.log 2 (Nat.log 2 n))`. -/
private lemma prod_inv_one_sub_prime_le (n : ℕ) :
    ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤
      Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) := by
  let P := (Finset.Icc 1 n).filter Nat.Prime
  have hpt : ∀ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤ Real.exp (2 * ((1 : ℝ) / (p : ℝ))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hden_pos : 0 < 1 - (1 : ℝ) / (p : ℝ) := by
      have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    have h1 : (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤ 1 + 2 * ((1 : ℝ) / (p : ℝ)) := by
      rw [inv_le_comm₀ hden_pos (by positivity)]
      have : (1 - (1 : ℝ) / (p : ℝ)) * (1 + 2 * ((1 : ℝ) / (p : ℝ))) =
          1 + ((1 : ℝ) / (p : ℝ)) * (1 - 2 / (p : ℝ)) := by ring
      have h2p : 2 / (p : ℝ) ≤ 1 := (div_le_one hp_pos).mpr hp2
      have hprod_ge : 1 ≤ (1 - (1 : ℝ) / (p : ℝ)) * (1 + 2 * ((1 : ℝ) / (p : ℝ))) := by
        rw [this]; nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hp_pos)]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      linarith
    linarith [h1, Real.add_one_le_exp (2 * ((1 : ℝ) / (p : ℝ)))]
  calc ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹
      ≤ ∏ p ∈ P, Real.exp (2 * ((1 : ℝ) / (p : ℝ))) := by
        refine Finset.prod_le_prod (fun p hp => ?_) hpt
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
        exact inv_nonneg.mpr (by linarith)
    _ = Real.exp (∑ p ∈ P, 2 * ((1 : ℝ) / (p : ℝ))) := (Real.exp_sum P _).symm
    _ = Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by rw [← Finset.mul_sum]
    _ ≤ Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hsum := sum_inv_primes_le n
        linarith

/-- Total number of prime factors with multiplicity: `Ω(n) = ∑_p v_p(n)`. -/
private def bigOmega (n : ℕ) : ℕ := n.factorization.sum (fun _ k => k)

private lemma bigOmega_one : bigOmega 1 = 0 := by simp [bigOmega]

private lemma bigOmega_prime_mul {p t : ℕ} (hp : p.Prime) (ht : t ≠ 0) :
    bigOmega (p * t) = bigOmega t + 1 := by
  unfold bigOmega
  rw [Nat.factorization_mul hp.ne_zero ht,
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    hp.factorization, Finsupp.sum_single_index rfl]
  omega

private lemma bigOmega_eq_zero_iff {d : ℕ} (hd : d ≠ 0) : bigOmega d = 0 ↔ d = 1 := by
  constructor
  · intro h0
    by_contra hne1
    have hp : d.minFac.Prime := Nat.minFac_prime hne1
    have hdvd : d.minFac ∣ d := Nat.minFac_dvd d
    rcases hdvd with ⟨q, hq⟩
    have hq_ne : q ≠ 0 := by intro h; rw [h, mul_zero] at hq; exact hd hq
    rw [hq, bigOmega_prime_mul hp hq_ne] at h0
    omega
  · rintro rfl; exact bigOmega_one

/-- **Lemma C1 (Exact Polynomial Divisor Bound, Combinatorial Form):**
For every `t ≥ 1` and every `k : ℕ`, the number of divisors `d ∣ t` with `Ω(d) = k` satisfies
`#{d ∣ t : Ω(d) = k} ≤ binom(Ω(t), k)`.
(Equivalently, `[x^k] ∏ (1 + x + ... + x^{e_i}) ≤ binom(∑ e_i, k)`.) -/
theorem lemma_C1_divisors_bigOmega_le_choose (t k : ℕ) (ht : 1 ≤ t) :
    (t.divisors.filter (fun d => bigOmega d = k)).card ≤ Nat.choose (bigOmega t) k := by
  induction t using Nat.strong_induction_on generalizing k with
  | h t ih =>
    by_cases ht1 : t = 1
    · subst ht1
      rw [bigOmega_one]
      cases k with
      | zero =>
        calc ((1 : ℕ).divisors.filter (fun d => bigOmega d = 0)).card
            ≤ (1 : ℕ).divisors.card := Finset.card_filter_le _ _
          _ = 1 := by decide
          _ = Nat.choose 0 0 := by simp
      | succ k' =>
        have hempty : ((1 : ℕ).divisors.filter (fun d => bigOmega d = k' + 1)) = ∅ := by
          ext d
          simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false, not_and]
          rintro ⟨hdvd, _⟩
          have hd1 : d = 1 := Nat.eq_one_of_dvd_one hdvd
          rw [hd1, bigOmega_one]; omega
        rw [hempty]; simp
    · let p := t.minFac
      have hp : p.Prime := Nat.minFac_prime ht1
      let t' := t / p
      have ht_eq : t = p * t' := (Nat.mul_div_cancel' (Nat.minFac_dvd t)).symm
      have ht'_pos : 1 ≤ t' := by
        have hp_le : p ≤ t := Nat.minFac_le (by omega)
        exact Nat.div_pos hp_le hp.pos
      have ht'_lt : t' < t := Nat.div_lt_self (by omega) hp.one_lt
      have hΩ_eq : bigOmega t = bigOmega t' + 1 := by
        conv_lhs => rw [ht_eq]
        exact bigOmega_prime_mul hp (Nat.ne_of_gt ht'_pos)
      rw [hΩ_eq]
      cases k with
      | zero =>
        have hsub : t.divisors.filter (fun d => bigOmega d = 0) ⊆ {1} := by
          intro d hd
          have hmem := Finset.mem_filter.mp hd
          have hd_ne : d ≠ 0 := by
            intro h0; rw [h0] at hmem
            have : 0 ∣ t := (Nat.mem_divisors.mp hmem.1).1
            rw [zero_dvd_iff] at this
            omega
          have hd1 : d = 1 := (bigOmega_eq_zero_iff hd_ne).mp hmem.2
          simp [hd1]
        calc (t.divisors.filter (fun d => bigOmega d = 0)).card
            ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
          _ = 1 := by simp
          _ = Nat.choose (bigOmega t' + 1) 0 := by simp
      | succ k' =>
        let A := t'.divisors.filter (fun d => bigOmega d = k' + 1)
        let B := (t'.divisors.filter (fun d => bigOmega d = k')).image (fun d => p * d)
        have hsub : t.divisors.filter (fun d => bigOmega d = k' + 1) ⊆ A ∪ B := by
          intro d hd
          have hmem := Finset.mem_filter.mp hd
          have hdvd_t : d ∣ p * t' := by rw [← ht_eq]; exact (Nat.mem_divisors.mp hmem.1).1
          by_cases hpd : p ∣ d
          · refine Finset.mem_union_right _ ?_
            rcases hpd with ⟨d', rfl⟩
            have hd'_ne : d' ≠ 0 := by
              intro h0; rw [h0, mul_zero] at hmem
              have : 0 ∣ t := (Nat.mem_divisors.mp hmem.1).1
              rw [zero_dvd_iff] at this; omega
            have hd'_dvd : d' ∣ t' := (mul_dvd_mul_iff_left hp.ne_zero).mp hdvd_t
            have hΩ_d' : bigOmega d' = k' := by
              have := hmem.2
              rw [bigOmega_prime_mul hp hd'_ne] at this
              omega
            exact Finset.mem_image.mpr
              ⟨d', Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd'_dvd, by omega⟩, hΩ_d'⟩, rfl⟩
          · refine Finset.mem_union_left _ ?_
            have hcop : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
            have hd_dvd_t' : d ∣ t' := hcop.symm.dvd_of_dvd_mul_left hdvd_t
            exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd_dvd_t', by omega⟩, hmem.2⟩
        calc (t.divisors.filter (fun d => bigOmega d = k' + 1)).card
            ≤ (A ∪ B).card := Finset.card_le_card hsub
          _ ≤ A.card + B.card := Finset.card_union_le A B
          _ ≤ A.card + (t'.divisors.filter (fun d => bigOmega d = k')).card :=
              Nat.add_le_add_left Finset.card_image_le _
          _ ≤ Nat.choose (bigOmega t') (k' + 1) + Nat.choose (bigOmega t') k' :=
              Nat.add_le_add (ih t' ht'_lt (k' + 1) ht'_pos) (ih t' ht'_lt k' ht'_pos)
          _ = Nat.choose (bigOmega t' + 1) (k' + 1) := by
              rw [Nat.choose_succ_succ, add_comm]

/-- Hockey-stick identity: `∑ j ∈ range (M + 1), choose (j + s) s = choose (M + s + 1) (s + 1)`. -/
private lemma sum_choose_add_eq (M s : ℕ) :
    ∑ j ∈ Finset.range (M + 1), Nat.choose (j + s) s = Nat.choose (M + s + 1) (s + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, add_comm (Nat.choose (M + s + 1) (s + 1))]
    have h1 : M + 1 + s = M + s + 1 := by omega
    rw [h1, ← Nat.choose_succ_succ]

/-- Stars-and-bars bound: `# {f : Fin s → ℕ | ∑ i, f i ≤ M} ≤ choose (M + s) s`. -/
private lemma stars_and_bars_le (s M : ℕ) :
    ((Fintype.piFinset (fun _ : Fin s => Finset.range (M + 1))).filter
      (fun f => ∑ i : Fin s, f i ≤ M)).card ≤ Nat.choose (M + s) s := by
  induction s generalizing M with
  | zero =>
    have hle : ((Fintype.piFinset (fun _ : Fin 0 => Finset.range (M + 1))).filter
        (fun f => ∑ i : Fin 0, f i ≤ M)).card ≤ 1 := by
      calc _ ≤ (Fintype.piFinset (fun _ : Fin 0 => Finset.range (M + 1))).card :=
              Finset.card_filter_le _ _
        _ = 1 := by simp
    simp [Nat.choose_zero_right]
  | succ s ih =>
    let S := (Fintype.piFinset (fun _ : Fin (s + 1) => Finset.range (M + 1))).filter
      (fun f => ∑ i : Fin (s + 1), f i ≤ M)
    have hmaps : ∀ f ∈ S, f 0 ∈ Finset.range (M + 1) := by
      intro f hf
      have hsum := (Finset.mem_filter.mp hf).2
      have h0 : f 0 ≤ ∑ i : Fin (s + 1), f i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      exact Finset.mem_range.mpr (by omega)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ r ∈ Finset.range (M + 1),
        (S.filter (fun f => f 0 = r)).card ≤ Nat.choose ((M - r) + s) s := by
      intro r hr
      have hr_le : r ≤ M := by have := Finset.mem_range.mp hr; omega
      let T := (Fintype.piFinset (fun _ : Fin s => Finset.range (M - r + 1))).filter
        (fun g => ∑ i : Fin s, g i ≤ M - r)
      let tail : (Fin (s + 1) → ℕ) → (Fin s → ℕ) := fun f i => f i.succ
      have htail_maps : ∀ f ∈ S.filter (fun f => f 0 = r), tail f ∈ T := by
        intro f hf
        have hfS := (Finset.mem_filter.mp hf).1
        have hf0 : f 0 = r := (Finset.mem_filter.mp hf).2
        have hsum := (Finset.mem_filter.mp hfS).2
        rw [Fin.sum_univ_succ, hf0] at hsum
        refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
        · have hi : f i.succ ≤ ∑ j : Fin s, f j.succ :=
            Finset.single_le_sum (f := fun j : Fin s => f j.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          dsimp only [tail]
          exact Finset.mem_range.mpr (by omega)
        · dsimp only [tail]; omega
      have htail_inj : Set.InjOn tail (S.filter (fun f => f 0 = r) : Set _) := by
        intro f₁ hf₁ f₂ hf₂ hEq
        funext i
        refine Fin.cases ?_ (fun j => congrFun hEq j) i
        rw [(Finset.mem_filter.mp hf₁).2, (Finset.mem_filter.mp hf₂).2]
      exact le_trans (Finset.card_le_card_of_injOn tail htail_maps htail_inj) (ih (M - r))
    calc ∑ r ∈ Finset.range (M + 1), (S.filter (fun f => f 0 = r)).card
        ≤ ∑ r ∈ Finset.range (M + 1), Nat.choose ((M - r) + s) s := Finset.sum_le_sum hfib
      _ = ∑ j ∈ Finset.range (M + 1), Nat.choose (j + s) s := by
          rw [← Finset.sum_range_reflect (fun j => Nat.choose (j + s) s) (M + 1)]
          refine Finset.sum_congr rfl fun r hr => ?_
          have : M + 1 - 1 - r = M - r := by omega
          rw [this]
      _ = Nat.choose (M + s + 1) (s + 1) := sum_choose_add_eq M s

/-- Elementary binomial upper bound: for `k ≥ 1`, `choose R k ≤ (e * R / k) ^ k`. -/
private lemma binom_le_exp_pow (R k : ℕ) (hk : 1 ≤ k) :
    (Nat.choose R k : ℝ) ≤ (Real.exp 1 * (R : ℝ) / (k : ℝ)) ^ k := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  -- Step 1: choose R k * k! = R.descFactorial k ≤ R ^ k
  have h1 : (Nat.choose R k : ℝ) * (k.factorial : ℝ) ≤ (R : ℝ) ^ k := by
    have hnat : Nat.choose R k * k.factorial ≤ R ^ k := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow R k
    exact_mod_cast hnat
  -- Step 2: k ^ k / k! ≤ exp k = (exp 1) ^ k
  have h2 : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1) ^ k := by
    have hsum := Real.sum_le_exp_of_nonneg (le_of_lt hk_pos) (k + 1)
    have hterm : (k : ℝ) ^ k / (k.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (k + 1), (k : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (k : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    have hexp : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
      rw [← Real.exp_nat_mul, mul_one]
    linarith
  have h3 : (k : ℝ) ^ k ≤ (Real.exp 1) ^ k * (k.factorial : ℝ) :=
    (div_le_iff₀ hfac_pos).mp h2
  have h4 : (Nat.choose R k : ℝ) * (k : ℝ) ^ k ≤ (Real.exp 1 * (R : ℝ)) ^ k := by
    calc (Nat.choose R k : ℝ) * (k : ℝ) ^ k
        ≤ (Nat.choose R k : ℝ) * ((Real.exp 1) ^ k * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ = (Real.exp 1) ^ k * ((Nat.choose R k : ℝ) * (k.factorial : ℝ)) := by ring
      _ ≤ (Real.exp 1) ^ k * (R : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (le_of_lt (Real.exp_pos 1)) k)
      _ = (Real.exp 1 * (R : ℝ)) ^ k := (mul_pow _ _ k).symm
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hk_pos k)).mpr h4

/-- Elementary exponential optimization: for `A ≥ 0` and `k ≥ 1`, `(e * A / k) ^ k ≤ exp A`. -/
private lemma exp_mul_div_pow_le_exp {A : ℝ} (hA : 0 ≤ A) (k : ℕ) (hk : 1 ≤ k) :
    (Real.exp 1 * A / (k : ℝ)) ^ k ≤ Real.exp A := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  by_cases hA0 : A = 0
  · rw [hA0, mul_zero, zero_div, zero_pow (by omega), Real.exp_zero]; norm_num
  · have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hbase : Real.exp 1 * A / (k : ℝ) ≤ Real.exp (A / (k : ℝ)) := by
      have hlog : Real.log (A / (k : ℝ)) ≤ A / (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hA_pos hk_pos)
      have hAk : Real.exp 1 * A / (k : ℝ) = Real.exp (1 + Real.log (A / (k : ℝ))) := by
        rw [Real.exp_add, Real.exp_log (div_pos hA_pos hk_pos), mul_div_assoc]
      rw [hAk]
      exact Real.exp_le_exp.mpr (by linarith)
    calc (Real.exp 1 * A / (k : ℝ)) ^ k
        ≤ (Real.exp (A / (k : ℝ))) ^ k :=
          pow_le_pow_left₀ (by positivity) hbase k
      _ = Real.exp ((k : ℝ) * (A / (k : ℝ))) := (Real.exp_nat_mul _ k).symm
      _ = Real.exp A := by rw [mul_div_cancel₀ A (ne_of_gt hk_pos)]

/-- Elementary prime-split divisor bound: for any `t ≥ 1`, `B ≥ 2` with `t ≤ B`, and `Z ≥ 2`,
`τ(t) ≤ (Nat.log 2 B + 1) ^ Z * 2 ^ (log B / log Z)`. -/
private lemma card_divisors_le_prime_split (t B Z : ℕ) (ht : 1 ≤ t) (htB : t ≤ B) (hZ : 2 ≤ Z) :
    (t.divisors.card : ℝ) ≤
      ((Nat.log 2 B + 1 : ℕ) : ℝ) ^ Z * (2 : ℝ) ^ (Real.log (B : ℝ) / Real.log (Z : ℝ)) := by
  -- Step 1: t.divisors.card ≤ ∏ p ∈ t.primeFactors, (t.factorization p + 1)
  have hdiv_prod : t.divisors.card ≤ ∏ p ∈ t.primeFactors, (t.factorization p + 1) := by
    let Φ : ℕ → (∀ p : t.primeFactors, ℕ) := fun d p => d.factorization p.1
    let box : Finset (∀ p : t.primeFactors, ℕ) :=
      Fintype.piFinset fun p : t.primeFactors => Finset.range (t.factorization p.1 + 1)
    have hmaps : ∀ d ∈ t.divisors, Φ d ∈ box := by
      intro d hd
      have hdvd := (Nat.mem_divisors.mp hd).1
      refine Fintype.mem_piFinset.mpr fun p => Finset.mem_range.mpr ?_
      have hle : d.factorization p.1 ≤ t.factorization p.1 :=
        (Nat.factorization_le_iff_dvd (by intro h0; rw [h0, zero_dvd_iff] at hdvd; omega) (by omega)).mpr hdvd p.1
      dsimp only [Φ]; omega
    have hinj : Set.InjOn Φ (t.divisors : Set ℕ) := by
      intro d₁ hd₁ d₂ hd₂ hEq
      have hd₁_dvd := (Nat.mem_divisors.mp hd₁).1
      have hd₂_dvd := (Nat.mem_divisors.mp hd₂).1
      have hd₁_ne : d₁ ≠ 0 := by intro h0; rw [h0, zero_dvd_iff] at hd₁_dvd; omega
      have hd₂_ne : d₂ ≠ 0 := by intro h0; rw [h0, zero_dvd_iff] at hd₂_dvd; omega
      apply Nat.eq_of_factorization_eq hd₁_ne hd₂_ne
      intro p
      by_cases hp : p ∈ t.primeFactors
      · exact congrFun hEq ⟨p, hp⟩
      · have htp : t.factorization p = 0 := by
          rw [Nat.mem_primeFactors] at hp
          by_contra hne
          have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hne)
          have hdvd : p ∣ t := Nat.dvd_of_factorization_pos hne
          exact hp ⟨hprime, hdvd, by omega⟩
        have h1 : d₁.factorization p ≤ t.factorization p :=
          (Nat.factorization_le_iff_dvd hd₁_ne (by omega)).mpr hd₁_dvd p
        have h2 : d₂.factorization p ≤ t.factorization p :=
          (Nat.factorization_le_iff_dvd hd₂_ne (by omega)).mpr hd₂_dvd p
        omega
    calc t.divisors.card ≤ box.card := Finset.card_le_card_of_injOn Φ hmaps hinj
      _ = ∏ p : t.primeFactors, (t.factorization p.1 + 1) := by simp [box]
      _ = ∏ p ∈ t.primeFactors, (t.factorization p + 1) :=
          Finset.prod_coe_sort t.primeFactors (fun p => t.factorization p + 1)
  -- Step 2: Split t.primeFactors into p ≤ Z and p > Z
  let P_sm := t.primeFactors.filter (fun p => p ≤ Z)
  let P_lg := t.primeFactors.filter (fun p => ¬ p ≤ Z)
  have hprod_split : ∏ p ∈ t.primeFactors, (t.factorization p + 1) =
      (∏ p ∈ P_sm, (t.factorization p + 1)) * (∏ p ∈ P_lg, (t.factorization p + 1)) :=
    (Finset.prod_filter_mul_prod_filter_not t.primeFactors (fun p => p ≤ Z) _).symm
  -- Small primes: each v_p(t) ≤ Nat.log 2 B and |P_sm| ≤ Z
  have hsm_le : ∏ p ∈ P_sm, (t.factorization p + 1) ≤ (Nat.log 2 B + 1) ^ Z := by
    have hcard : P_sm.card ≤ Z := by
      have hsub : P_sm ⊆ Finset.Icc 1 Z := by
        intro p hp
        have hp_pf := (Finset.mem_filter.mp hp).1
        have hp_le := (Finset.mem_filter.mp hp).2
        exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp_pf).one_le, hp_le⟩
      calc P_sm.card ≤ (Finset.Icc 1 Z).card := Finset.card_le_card hsub
        _ = Z := by simp
    have hfac_le : ∀ p ∈ P_sm, t.factorization p + 1 ≤ Nat.log 2 B + 1 := by
      intro p hp
      have hp_pf := (Finset.mem_filter.mp hp).1
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp_pf).two_le
      have hpow : 2 ^ (t.factorization p) ≤ B := by
        calc 2 ^ (t.factorization p) ≤ p ^ (t.factorization p) := Nat.pow_le_pow_left hp2 _
          _ ≤ t := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd t p)
          _ ≤ B := htB
      have : t.factorization p ≤ Nat.log 2 B := Nat.le_log_of_pow_le (by norm_num) hpow
      omega
    calc ∏ p ∈ P_sm, (t.factorization p + 1)
        ≤ ∏ _p ∈ P_sm, (Nat.log 2 B + 1) := Finset.prod_le_prod' hfac_le
      _ = (Nat.log 2 B + 1) ^ P_sm.card := by simp
      _ ≤ (Nat.log 2 B + 1) ^ Z := Nat.pow_le_pow_right (by omega) hcard
  -- Large primes: e + 1 ≤ 2^e, and Z ^ (∑_{p > Z} e) ≤ t ≤ B
  have hlg_le : ((∏ p ∈ P_lg, (t.factorization p + 1) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (Real.log (B : ℝ) / Real.log (Z : ℝ)) := by
    have h1 : ∏ p ∈ P_lg, (t.factorization p + 1) ≤ 2 ^ (∑ p ∈ P_lg, t.factorization p) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod' fun p _ => ?_
      have : ∀ e : ℕ, e + 1 ≤ 2 ^ e := by
        intro e; induction e with
        | zero => simp
        | succ e ihe => rw [pow_succ]; omega
      exact this (t.factorization p)
    -- Show Z ^ (∑ p ∈ P_lg, t.factorization p) ≤ B
    have hZ_pow : Z ^ (∑ p ∈ P_lg, t.factorization p) ≤ B := by
      have h2 : ∏ p ∈ P_lg, p ^ (t.factorization p) ∣ t := by
        have hcop : (P_lg : Set ℕ).Pairwise (fun p q => Nat.Coprime (p ^ t.factorization p) (q ^ t.factorization q)) := by
          intro p hp q hq hpq
          exact ((Nat.coprime_primes
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).mpr hpq).pow _ _
        exact nat_prod_dvd_of_coprime P_lg (fun p => p ^ t.factorization p) t hcop
          fun p _ => Nat.ordProj_dvd t p
      calc Z ^ (∑ p ∈ P_lg, t.factorization p)
          = ∏ p ∈ P_lg, Z ^ (t.factorization p) := (Finset.prod_pow_eq_pow_sum P_lg _ Z).symm
        _ ≤ ∏ p ∈ P_lg, p ^ (t.factorization p) := Finset.prod_le_prod' fun p hp =>
              Nat.pow_le_pow_left (by have := (Finset.mem_filter.mp hp).2; omega) _
        _ ≤ t := Nat.le_of_dvd (by omega) h2
        _ ≤ B := htB
    have hlogZ_pos : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
    have hZ_pos : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast (by omega : 0 < Z)
    have hsum_le : ((∑ p ∈ P_lg, t.factorization p : ℕ) : ℝ) ≤ Real.log (B : ℝ) / Real.log (Z : ℝ) := by
      have hreal : (Z : ℝ) ^ (∑ p ∈ P_lg, t.factorization p) ≤ (B : ℝ) := by exact_mod_cast hZ_pow
      have hlog := Real.log_le_log (pow_pos hZ_pos _) hreal
      rw [Real.log_pow] at hlog
      exact (le_div_iff₀ hlogZ_pos).mpr hlog
    calc ((∏ p ∈ P_lg, (t.factorization p + 1) : ℕ) : ℝ)
        ≤ ((2 ^ (∑ p ∈ P_lg, t.factorization p) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (2 : ℝ) ^ ((∑ p ∈ P_lg, t.factorization p : ℕ) : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (Real.log (B : ℝ) / Real.log (Z : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hsum_le
  have hcast : (t.divisors.card : ℝ) ≤
      ((∏ p ∈ P_sm, (t.factorization p + 1) : ℕ) : ℝ) *
        ((∏ p ∈ P_lg, (t.factorization p + 1) : ℕ) : ℝ) := by
    have : t.divisors.card ≤ (∏ p ∈ P_sm, (t.factorization p + 1)) * (∏ p ∈ P_lg, (t.factorization p + 1)) := by
      rw [← hprod_split]; exact hdiv_prod
    exact_mod_cast this
  have hsm_real : ((∏ p ∈ P_sm, (t.factorization p + 1) : ℕ) : ℝ) ≤ ((Nat.log 2 B + 1 : ℕ) : ℝ) ^ Z := by
    exact_mod_cast hsm_le
  exact le_trans hcast (mul_le_mul hsm_real hlg_le (Nat.cast_nonneg _) (by positivity))

/-! ### Section 6: Lemma C2 — Constant-1 Joint Euler-Product Rankin Bound & Factor Estimates -/

/-- Elementary lower bound `1 / 2 ≤ log 2` from `1 + (-1/2) ≤ exp (-1/2)`. -/
private lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h1 : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
    have := Real.add_one_le_exp (-(1 : ℝ) / 2)
    linarith
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

/-- Elementary `Nat` inequality `e + 1 ≤ 2 ^ e`. -/
private lemma nat_succ_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- Elementary `Nat` inequality `(e + 1) ^ 4 ≤ 81 * 2 ^ e` for all `e : ℕ`. -/
private lemma nat_succ_pow_four_le (e : ℕ) : (e + 1) ^ 4 ≤ 81 * 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 6
    · interval_cases k <;> norm_num
    · have hk6 : 6 ≤ k := by omega
      have hstep : (k + 2) ^ 4 ≤ 2 * (k + 1) ^ 4 := by
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk6
        have : 2 * (6 + r + 1) ^ 4 = (6 + r + 2) ^ 4 + (r ^ 4 + 24 * r ^ 3 + 204 * r ^ 2 + 696 * r + 706) := by ring
        omega
      calc (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring
        _ ≤ 2 * (k + 1) ^ 4 := hstep
        _ ≤ 2 * (81 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 81 * 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- Optimization inequality `(e * A / k) ^ (2 * k / 3) ≤ exp (2 / 3 * A)` for `A ≥ 0`, `k ≥ 1`. -/
private lemma exp_mul_div_pow_two_thirds_le_exp {A : ℝ} (hA : 0 ≤ A) (k : ℕ) (hk : 1 ≤ k) :
    ((Real.exp 1 * A / (k : ℝ)) ^ (2 * k)) ^ ((1 : ℝ) / 3) ≤ Real.exp ((2 : ℝ) / 3 * A) := by
  have h1 := exp_mul_div_pow_le_exp hA k hk
  have hpow2 : (Real.exp 1 * A / (k : ℝ)) ^ (2 * k) ≤ (Real.exp A) ^ (2 : ℕ) := by
    rw [mul_comm 2 k, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h1 2
  calc ((Real.exp 1 * A / (k : ℝ)) ^ (2 * k)) ^ ((1 : ℝ) / 3)
      ≤ ((Real.exp A) ^ (2 : ℕ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hpow2 (by norm_num)
    _ = Real.exp ((2 : ℝ) / 3 * A) := by
        rw [← Real.exp_nat_mul, ← Real.exp_mul]
        congr 1; push_cast; ring

/-- Squareful optimization bound: for `x ≥ 0`, `e * x * 2 ^ (-x / 4) ≤ 8`. -/
private lemma exp_mul_x_mul_two_neg_quarter_le_eight {x : ℝ} (hx : 0 ≤ x) :
    Real.exp 1 * x * (2 : ℝ) ^ (-x / 4) ≤ 8 := by
  have hlog2 := half_le_log_two
  have h2pow : (2 : ℝ) ^ (-x / 4) ≤ Real.exp (-x / 8) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hxexp : x * Real.exp (-x / 8) ≤ 8 * Real.exp (-1) := by
    have h1 : x / 8 ≤ Real.exp (x / 8 - 1) := by
      have := Real.add_one_le_exp (x / 8 - 1)
      linarith
    have h2 : Real.exp (x / 8 - 1) * Real.exp (-x / 8) = Real.exp (-1) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : (x / 8) * Real.exp (-x / 8) ≤ Real.exp (-1) := by
      calc (x / 8) * Real.exp (-x / 8)
          ≤ Real.exp (x / 8 - 1) * Real.exp (-x / 8) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-1) := h2
    linarith
  calc Real.exp 1 * x * (2 : ℝ) ^ (-x / 4)
      ≤ Real.exp 1 * x * Real.exp (-x / 8) :=
        mul_le_mul_of_nonneg_left h2pow (by positivity)
    _ = Real.exp 1 * (x * Real.exp (-x / 8)) := by ring
    _ ≤ Real.exp 1 * (8 * Real.exp (-1)) :=
        mul_le_mul_of_nonneg_left hxexp (le_of_lt (Real.exp_pos 1))
    _ = 8 * (Real.exp 1 * Real.exp (-1)) := by ring
    _ = 8 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Finite geometric sum upper bound: for `0 ≤ r < 1`, `∑ e ∈ range (E + 1), r^e ≤ (1 - r)⁻¹`. -/
private lemma geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (E : ℕ) :
    ∑ e ∈ Finset.range (E + 1), r ^ e ≤ (1 - r)⁻¹ := by
  have hden : 0 < 1 - r := by linarith
  have hmul : (1 - r) * ∑ e ∈ Finset.range (E + 1), r ^ e = 1 - r ^ (E + 1) := by
    induction E with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hle : (1 - r) * ∑ e ∈ Finset.range (E + 1), r ^ e ≤ 1 := by
    rw [hmul]; linarith [pow_nonneg hr0 (E + 1)]
  rw [← one_div, le_div_iff₀ hden]
  linarith

/-- Tail of geometric sum from `e = 2`: for `0 ≤ r ≤ 3/4`,
`∑ e ∈ Ico 2 (E + 1), r^e ≤ 4 * r^2`. -/
private lemma geom_sum_from_two_le {r : ℝ} (hr0 : 0 ≤ r) (hr34 : r ≤ 3 / 4) (E : ℕ) :
    ∑ e ∈ Finset.Ico 2 (E + 1), r ^ e ≤ 4 * r ^ 2 := by
  by_cases hE : E < 2
  · have : Finset.Ico 2 (E + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty]; positivity
  · have hshift : ∑ e ∈ Finset.Ico 2 (E + 1), r ^ e =
        r ^ 2 * ∑ j ∈ Finset.range (E - 1), r ^ j := by
      have h1 : Finset.Ico 2 (E + 1) = (Finset.range (E - 1)).image (fun j => j + 2) := by
        ext e
        simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨e - 2, by omega, by omega⟩
        · rintro ⟨j, hj, rfl⟩; omega
      rw [h1, Finset.sum_image (fun _ _ _ _ h => by omega), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, mul_comm]
    rw [hshift]
    have hE1 : E - 1 = (E - 2) + 1 := by omega
    rw [hE1]
    have hgeo := geom_sum_le_inv hr0 (by linarith) (E - 2)
    have hinv : (1 - r)⁻¹ ≤ 4 := by
      have hpos : (0 : ℝ) < 1 - r := by linarith
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    calc r ^ 2 * ∑ j ∈ Finset.range (E - 2 + 1), r ^ j
        ≤ r ^ 2 * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeo (sq_nonneg r)
      _ ≤ r ^ 2 * 4 := mul_le_mul_of_nonneg_left hinv (sq_nonneg r)
      _ = 4 * r ^ 2 := by ring

/-- **Constant-1 Finite Euler Product Bound (Rankin Trick Core):**
For any `N, E : ℕ` with `N < 2 ^ (E + 1)`, any finite set `P` of primes containing all primes
`≤ N`, and any non-negative prime-power weight `w : ℕ → ℕ → ℝ`,
`∑ d ∈ Icc 1 N, ∏ p ∈ P, w p (d.factorization p) ≤ ∏ p ∈ P, ∑ e ∈ range (E + 1), w p e`. -/
private lemma euler_product_rankin_bound (N E : ℕ) (P : Finset ℕ)
    (hNE : N < 2 ^ (E + 1))
    (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_cover : ∀ p, Nat.Prime p → p ≤ N → p ∈ P)
    (w : ℕ → ℕ → ℝ) (hw_nn : ∀ p ∈ P, ∀ e, 0 ≤ w p e) :
    ∑ d ∈ Finset.Icc 1 N, ∏ p ∈ P, w p (d.factorization p) ≤
      ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), w p e := by
  classical
  let Φ : ℕ → (∀ _p : P, Fin (E + 1)) := fun d p =>
    if h : d.factorization p.1 < E + 1 then ⟨d.factorization p.1, h⟩ else ⟨0, Nat.zero_lt_succ E⟩
  have hfac_lt : ∀ d ∈ Finset.Icc 1 N, ∀ p : P, d.factorization p.1 < E + 1 := by
    intro d hd p
    have hd_Icc := Finset.mem_Icc.mp hd
    have hp2 : 2 ≤ p.1 := (hP_prime p.1 p.2).two_le
    have hpow : 2 ^ (d.factorization p.1) ≤ N := by
      calc 2 ^ (d.factorization p.1) ≤ p.1 ^ (d.factorization p.1) := Nat.pow_le_pow_left hp2 _
        _ ≤ d := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd d p.1)
        _ ≤ N := hd_Icc.2
    have hlt : 2 ^ (d.factorization p.1) < 2 ^ (E + 1) := lt_of_le_of_lt hpow hNE
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  have hΦ_val : ∀ d ∈ Finset.Icc 1 N, ∀ p : P, (Φ d p).1 = d.factorization p.1 := by
    intro d hd p
    dsimp only [Φ]; rw [dif_pos (hfac_lt d hd p)]
  have hinj : Set.InjOn Φ (Finset.Icc 1 N : Set ℕ) := by
    intro d₁ hd₁ d₂ hd₂ hEq
    have h1 := Finset.mem_Icc.mp hd₁
    have h2 := Finset.mem_Icc.mp hd₂
    apply Nat.eq_of_factorization_eq (by omega) (by omega)
    intro p
    by_cases hp : p ∈ P
    · have := congrArg Fin.val (congrFun hEq ⟨p, hp⟩)
      rwa [hΦ_val d₁ hd₁ ⟨p, hp⟩, hΦ_val d₂ hd₂ ⟨p, hp⟩] at this
    · have h0 : ∀ d, 1 ≤ d → d ≤ N → d.factorization p = 0 := by
        intro d hd1 hdN
        by_contra hne
        have hp_pf : p ∈ d.primeFactors := Finsupp.mem_support_iff.mpr hne
        have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
        have hp_dvd : p ∣ d := Nat.dvd_of_factorization_pos hne
        have hp_le : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hp_dvd) hdN
        exact hp (hP_cover p hp_pr hp_le)
      rw [h0 d₁ h1.1 h1.2, h0 d₂ h2.1 h2.2]
  have hsum_img : ∑ d ∈ Finset.Icc 1 N, ∏ p ∈ P, w p (d.factorization p) =
      ∑ v ∈ (Finset.Icc 1 N).image Φ, ∏ p : P, w p.1 (v p).1 := by
    rw [Finset.sum_image (fun d₁ hd₁ d₂ hd₂ hEq => hinj hd₁ hd₂ hEq)]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← Finset.prod_coe_sort P (fun p => w p (d.factorization p))]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hΦ_val d hd p]
  rw [hsum_img]
  calc ∑ v ∈ (Finset.Icc 1 N).image Φ, ∏ p : P, w p.1 (v p).1
      ≤ ∑ v : (∀ _p : P, Fin (E + 1)), ∏ p : P, w p.1 (v p).1 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ =>
          Finset.prod_nonneg fun p _ => hw_nn p.1 p.2 (v p).1
    _ = ∏ p : P, ∑ e : Fin (E + 1), w p.1 e.1 :=
        (Fintype.prod_sum (fun p : P => fun e : Fin (E + 1) => w p.1 e.1)).symm
    _ = ∏ p : P, ∑ e ∈ Finset.range (E + 1), w p.1 e := by
        refine Finset.prod_congr rfl fun p _ => Fin.sum_univ_eq_sum_range (fun e => w p.1 e) (E + 1)
    _ = ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), w p e :=
        Finset.prod_coe_sort P (fun p => ∑ e ∈ Finset.range (E + 1), w p e)

/-! ### Prime-Factorization Decomposition Helpers (Small Squareful, Small Squarefree, Buckets) -/

/-- Small primes `≤ Y`. -/
private def primesSmall (Y : ℕ) : Finset ℕ := (Finset.Icc 1 Y).filter Nat.Prime

/-- Bucket `m` of large primes in `(max Y (2^(2^m)), min n (2^(2^(m+1)))]`. -/
private def primeBucket (Y n m : ℕ) : Finset ℕ :=
  (Finset.Ioc (max Y (2 ^ (2 ^ m))) (min n (2 ^ (2 ^ (m + 1))))).filter Nat.Prime

/-- Squareful small-prime part `q_sm(d) = ∏_{p ≤ Y, v_p(d) ≥ 2} p^{v_p(d)}`. -/
private def qSm (Y d : ℕ) : ℕ :=
  ∏ p ∈ (primesSmall Y).filter (fun p => 2 ≤ d.factorization p), p ^ (d.factorization p)

/-- Squarefree small-prime part `u_sm(d) = ∏_{p ≤ Y, v_p(d) = 1} p`. -/
private def uSm (Y d : ℕ) : ℕ :=
  ∏ p ∈ (primesSmall Y).filter (fun p => d.factorization p = 1), p

/-- Number of distinct prime factors of `q_sm(d)`. -/
private def omegaQ (Y d : ℕ) : ℕ :=
  ((primesSmall Y).filter (fun p => 2 ≤ d.factorization p)).card

/-- Number of distinct prime factors of `u_sm(d)`. -/
private def omegaU (Y d : ℕ) : ℕ :=
  ((primesSmall Y).filter (fun p => d.factorization p = 1)).card

/-- Bucket-`m` part of `d`. -/
private def bucketPart (Y n m d : ℕ) : ℕ :=
  ∏ p ∈ primeBucket Y n m, p ^ (d.factorization p)

/-- Total prime multiplicity of `d` in bucket `m`. -/
private def bucketOmega (Y n m d : ℕ) : ℕ :=
  ∑ p ∈ primeBucket Y n m, d.factorization p

private lemma bucketPart_pos (Y n m d : ℕ) : 1 ≤ bucketPart Y n m d := by
  unfold bucketPart
  exact Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (Finset.mem_filter.mp hp).2.pos

private lemma bigOmega_prod_prime_pow (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (e : ℕ → ℕ) :
    bigOmega (∏ p ∈ S, p ^ (e p)) = ∑ p ∈ S, e p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bigOmega_one]
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.sum_insert hp]
    have hpr : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs_pr : ∀ q ∈ s, Nat.Prime q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hprod_ne : (∏ q ∈ s, q ^ e q) ≠ 0 := by
      have hpos : 1 ≤ ∏ q ∈ s, q ^ e q :=
        Finset.one_le_prod' fun q hq => Nat.one_le_pow _ _ (hs_pr q hq).pos
      omega
    have hpow_ne : p ^ e p ≠ 0 := pow_ne_zero _ hpr.ne_zero
    unfold bigOmega
    rw [Nat.factorization_mul hpow_ne hprod_ne,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Nat.factorization_pow, hpr.factorization, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.sum_single_index rfl]
    have hih := ih hs_pr
    unfold bigOmega at hih
    rw [hih]

private lemma bigOmega_bucketPart (Y n m d : ℕ) :
    bigOmega (bucketPart Y n m d) = bucketOmega Y n m d := by
  unfold bucketPart bucketOmega
  exact bigOmega_prod_prime_pow _ (fun p hp => (Finset.mem_filter.mp hp).2) _

/-- Exact partition of primes `≤ n` into `primesSmall Y` and disjoint `primeBucket Y n m`
for `m ∈ Icc m_start M_max`. -/
private lemma primes_partition_eq (Y n m_start M_max : ℕ)
    (hY2 : 2 ≤ Y) (hYn : Y ≤ n)
    (hms : 2 ^ (2 ^ m_start) ≤ Y)
    (hMm : n ≤ 2 ^ (2 ^ (M_max + 1))) :
    (Finset.Icc 1 n).filter Nat.Prime =
      primesSmall Y ∪ (Finset.Icc m_start M_max).biUnion (primeBucket Y n) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_biUnion,
    primesSmall, primeBucket, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp1, hpn⟩, hp_pr⟩
    by_cases hpY : p ≤ Y
    · exact Or.inl ⟨⟨hp1, hpY⟩, hp_pr⟩
    · refine Or.inr ?_
      have hp_gt2 : 2 < p := by omega
      let r := Nat.log 2 (p - 1)
      have hr_pos : 1 ≤ r := Nat.le_log_of_pow_le (by norm_num) (by omega)
      have hr_le : 2 ^ r ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
      have hr_lt : p - 1 < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
      let m := Nat.log 2 r
      have hm_le : 2 ^ m ≤ r := Nat.pow_log_le_self 2 (by omega)
      have hm_lt : r < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
      have hlo : 2 ^ (2 ^ m) < p := by
        have : 2 ^ (2 ^ m) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hm_le
        omega
      have hhi : p ≤ 2 ^ (2 ^ (m + 1)) := by
        have : 2 ^ (r + 1) ≤ 2 ^ (2 ^ (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hm_ge : m_start ≤ m := by
        by_contra hlt; push Not at hlt
        have hle1 : m + 1 ≤ m_start := by omega
        have hle2 : 2 ^ (2 ^ (m + 1)) ≤ 2 ^ (2 ^ m_start) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hle1)
        omega
      have hm_ub : m ≤ M_max := by
        by_contra hgt; push Not at hgt
        have hle1 : M_max + 1 ≤ m := by omega
        have hle2 : 2 ^ (2 ^ (M_max + 1)) ≤ 2 ^ (2 ^ m) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hle1)
        omega
      refine ⟨m, ⟨hm_ge, hm_ub⟩, ⟨?_, ?_⟩, hp_pr⟩
      · exact max_lt (by omega) hlo
      · exact le_min hpn hhi
  · rintro (⟨⟨hp1, hpY⟩, hp_pr⟩ | ⟨m, _, ⟨hlo, hhi⟩, hp_pr⟩)
    · exact ⟨⟨hp1, le_trans hpY hYn⟩, hp_pr⟩
    · exact ⟨⟨hp_pr.one_le, le_trans hhi (min_le_left _ _)⟩, hp_pr⟩

private lemma primeBucket_pairwiseDisjoint (Y n : ℕ) (I : Finset ℕ) :
    Set.PairwiseDisjoint (I : Set ℕ) (primeBucket Y n) := by
  intro m₁ _ m₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1
  have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpow : 2 ^ (2 ^ (m₁ + 1)) ≤ 2 ^ (2 ^ m₂) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hlt)
    have h1u : p ≤ 2 ^ (2 ^ (m₁ + 1)) := le_trans h1.2 (min_le_right _ _)
    have h2l : 2 ^ (2 ^ m₂) < p := lt_of_le_of_lt (le_max_right _ _) h2.1
    omega
  · have hpow : 2 ^ (2 ^ (m₂ + 1)) ≤ 2 ^ (2 ^ m₁) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hgt)
    have h2u : p ≤ 2 ^ (2 ^ (m₂ + 1)) := le_trans h2.2 (min_le_right _ _)
    have h1l : 2 ^ (2 ^ m₁) < p := lt_of_le_of_lt (le_max_right _ _) h1.1
    omega

private lemma primesSmall_disjoint_buckets (Y n : ℕ) (I : Finset ℕ) :
    Disjoint (primesSmall Y) (I.biUnion (primeBucket Y n)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have hle : p ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
  rcases Finset.mem_biUnion.mp hp2 with ⟨m, _, hm⟩
  have hgt : Y < p := lt_of_le_of_lt (le_max_left _ _) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
  omega

/-- Unique factorization identity: for `1 ≤ d ≤ n`, `d = qSm Y d * uSm Y d * ∏ m, bucketPart Y n m d`. -/
private lemma eq_qSm_mul_uSm_mul_prod_bucketPart (Y n m_start M_max d : ℕ)
    (hY2 : 2 ≤ Y) (hYn : Y ≤ n) (hms : 2 ^ (2 ^ m_start) ≤ Y)
    (hMm : n ≤ 2 ^ (2 ^ (M_max + 1))) (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    d = qSm Y d * uSm Y d * ∏ m ∈ Finset.Icc m_start M_max, bucketPart Y n m d := by
  have hd_prod : ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, p ^ (d.factorization p) = d := by
    have hsub : d.primeFactors ⊆ (Finset.Icc 1 n).filter Nat.Prime := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpr.one_le, le_trans (Nat.le_of_dvd (by omega) hdvd) hdn⟩, hpr⟩
    have h1 : ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, p ^ (d.factorization p) =
        ∏ p ∈ d.primeFactors, p ^ (d.factorization p) := by
      symm
      refine Finset.prod_subset hsub fun p _ hp_not => ?_
      have h0 : d.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not
      rw [h0, pow_zero]
    rw [h1]
    exact Nat.prod_factorization_pow_eq_self (by omega)
  conv_lhs => rw [← hd_prod, primes_partition_eq Y n m_start M_max hY2 hYn hms hMm,
    Finset.prod_union (primesSmall_disjoint_buckets Y n _),
    Finset.prod_biUnion (primeBucket_pairwiseDisjoint Y n _)]
  congr 1
  -- Split primesSmall Y into v_p(d) ≥ 2, v_p(d) = 1, and v_p(d) = 0
  have hsm : ∏ p ∈ primesSmall Y, p ^ (d.factorization p) = qSm Y d * uSm Y d := by
    rw [← Finset.prod_filter_mul_prod_filter_not (primesSmall Y) (fun p => 2 ≤ d.factorization p)]
    congr 1
    -- On ¬ (2 ≤ d.factorization p), either d.factorization p = 1 or = 0
    unfold uSm
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)) (fun p => d.factorization p = 1)]
    have h0prod : ∏ p ∈ ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)).filter
        (fun p => ¬ d.factorization p = 1), p ^ (d.factorization p) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have h2 := (Finset.mem_filter.mp hp).2
      have hzero : d.factorization p = 0 := by omega
      rw [hzero, pow_zero]
    rw [h0prod, mul_one]
    have hfilt : ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)).filter
        (fun p => d.factorization p = 1) = (primesSmall Y).filter (fun p => d.factorization p = 1) := by
      ext p; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
      · rintro ⟨hp, h1⟩; exact ⟨⟨hp, by omega⟩, h1⟩
    rw [hfilt]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2, pow_one]
  exact hsm

/-- **Lemma C2a (Exact Divisor Bound on a Multi-Scale Slice):**
For any `t ∈ [1, H]`, the number of `d ∈ [1, n]` dividing `t` with prescribed
`(a = Nat.log 2 (qSm Y d), s = omegaQ Y d, k₀ = omegaU Y d, k m = bucketOmega Y n m d)` is at most
`choose |P_sm| k₀ * (if s = 0 then 1 else choose |P_sm| s * choose (a - s) s) * ∏ m, choose (R m) (k m)`. -/
private lemma lemma_C2a_slice_divisor_bound
    (Y n m_start M_max H t a s k₀ : ℕ) (k : ℕ → ℕ)
    (hY2 : 2 ≤ Y) (hYn : Y ≤ n) (hms : 2 ^ (2 ^ m_start) ≤ Y)
    (hMm : n ≤ 2 ^ (2 ^ (M_max + 1))) (ht1 : 1 ≤ t) (htH : t ≤ H) :
    let M_idx := Finset.Icc m_start M_max
    let R : ℕ → ℕ := fun m => Nat.log 2 H / 2 ^ m
    ((Finset.Icc 1 n).filter fun d =>
        d ∣ t ∧
        Nat.log 2 (qSm Y d) = a ∧
        omegaQ Y d = s ∧
        omegaU Y d = k₀ ∧
        ∀ m ∈ M_idx, bucketOmega Y n m d = k m).card ≤
      Nat.choose (primesSmall Y).card k₀ *
      (if s = 0 then 1 else Nat.choose (primesSmall Y).card s * Nat.choose (a - s) s) *
      ∏ m ∈ M_idx, Nat.choose (R m) (k m) := by
  classical
  intro M_idx R
  let D := (Finset.Icc 1 n).filter fun d =>
    d ∣ t ∧ Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
    ∀ m ∈ M_idx, bucketOmega Y n m d = k m
  -- First rule out impossible case s ≥ 1 ∧ a < 2 * s (then D = ∅)
  by_cases hvalid : s = 0 ∨ 2 * s ≤ a
  swap
  · have hD_empty : D = ∅ := by
      ext d
      simp only [D, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      rintro _ _ ha_eq hs_eq _ _
      -- 2^(2*s) ≤ qSm Y d < 2^(a + 1)
      have hq_ge : 2 ^ (2 * s) ≤ qSm Y d := by
        let Sq := (primesSmall Y).filter (fun p => 2 ≤ d.factorization p)
        have hcard : Sq.card = s := hs_eq
        calc 2 ^ (2 * s) = (2 ^ 2) ^ Sq.card := by rw [hcard, ← pow_mul]
          _ = ∏ _p ∈ Sq, 2 ^ 2 := by simp
          _ ≤ ∏ p ∈ Sq, p ^ (d.factorization p) := by
              refine Finset.prod_le_prod' fun p hp => ?_
              have hp2 : 2 ≤ p := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.two_le
              have he2 : 2 ≤ d.factorization p := (Finset.mem_filter.mp hp).2
              calc 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
                _ ≤ p ^ (d.factorization p) := Nat.pow_le_pow_right (by omega) he2
          _ = qSm Y d := rfl
      have hq_lt : qSm Y d < 2 ^ (a + 1) := by
        rw [← ha_eq]; exact Nat.lt_pow_succ_log_self (by norm_num) (qSm Y d)
      have h2s_lt : 2 * s < a + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt hq_ge hq_lt)
      omega
    change D.card ≤ _
    rw [hD_empty, Finset.card_empty]
    exact Nat.zero_le _
  -- Build sets of possible uSm, qSm, and bucketPart values
  let Uset : Finset ℕ := ((primesSmall Y).powersetCard k₀).image (fun S => ∏ p ∈ S, p)
  have hU_card : Uset.card ≤ Nat.choose (primesSmall Y).card k₀ := by
    calc Uset.card ≤ ((primesSmall Y).powersetCard k₀).card := Finset.card_image_le
      _ = Nat.choose (primesSmall Y).card k₀ := Finset.card_powersetCard k₀ _
  -- Qset: possible qSm values
  let Qset : Finset ℕ :=
    if hs : s = 0 then {1}
    else (((primesSmall Y).powersetCard s) ×ˢ
      ((Fintype.piFinset (fun _ : Fin s => Finset.range (a - 2 * s + 1))).filter
        (fun f => ∑ i : Fin s, f i ≤ a - 2 * s))).image fun pf =>
          if hcard : pf.1.card = s then
            ∏ i : Fin s, (pf.1.orderEmbOfFin hcard i) ^ (pf.2 i + 2)
          else 1
  have hQ_card : Qset.card ≤ if s = 0 then 1 else Nat.choose (primesSmall Y).card s * Nat.choose (a - s) s := by
    by_cases hs : s = 0
    · simp [Qset, hs]
    · simp only [Qset, hs, dite_false, if_false]
      have h2s : 2 * s ≤ a := hvalid.resolve_left hs
      have hsub_eq : a - 2 * s + s = a - s := by omega
      calc _ ≤ (((primesSmall Y).powersetCard s) ×ˢ
            ((Fintype.piFinset (fun _ : Fin s => Finset.range (a - 2 * s + 1))).filter
              (fun f => ∑ i : Fin s, f i ≤ a - 2 * s))).card := Finset.card_image_le
        _ = ((primesSmall Y).powersetCard s).card *
            ((Fintype.piFinset (fun _ : Fin s => Finset.range (a - 2 * s + 1))).filter
              (fun f => ∑ i : Fin s, f i ≤ a - 2 * s)).card := Finset.card_product _ _
        _ ≤ Nat.choose (primesSmall Y).card s * Nat.choose (a - 2 * s + s) s := by
            rw [Finset.card_powersetCard]
            exact Nat.mul_le_mul_left _ (stars_and_bars_le s (a - 2 * s))
        _ = Nat.choose (primesSmall Y).card s * Nat.choose (a - s) s := by rw [hsub_eq]
  -- Bset m: divisors of t_m := bucketPart Y n m t with bigOmega = k m
  let Bset : ℕ → Finset ℕ := fun m =>
    (bucketPart Y n m t).divisors.filter (fun dm => bigOmega dm = k m)
  have hB_card : ∀ m ∈ M_idx, (Bset m).card ≤ Nat.choose (R m) (k m) := by
    intro m _
    have htm_pos : 1 ≤ bucketPart Y n m t := bucketPart_pos Y n m t
    have hC1 := lemma_C1_divisors_bigOmega_le_choose (bucketPart Y n m t) (k m) htm_pos
    -- Show bigOmega (bucketPart Y n m t) ≤ R m
    have hΩ_le : bigOmega (bucketPart Y n m t) ≤ R m := by
      rw [bigOmega_bucketPart]
      -- (2^(2^m))^(bucketOmega Y n m t) ≤ bucketPart Y n m t ≤ t ≤ H
      have htm_dvd : bucketPart Y n m t ∣ t := by
        unfold bucketPart
        have hcop : (primeBucket Y n m : Set ℕ).Pairwise
            (fun p q => Nat.Coprime (p ^ t.factorization p) (q ^ t.factorization q)) := by
          intro p hp q hq hne
          exact ((Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hne).pow _ _
        exact nat_prod_dvd_of_coprime (primeBucket Y n m) (fun p => p ^ t.factorization p) t hcop
          fun p _ => Nat.ordProj_dvd t p
      have hpow : 2 ^ (2 ^ m * bucketOmega Y n m t) ≤ H := by
        calc 2 ^ (2 ^ m * bucketOmega Y n m t)
            = (2 ^ (2 ^ m)) ^ (∑ p ∈ primeBucket Y n m, t.factorization p) := by rw [pow_mul]; rfl
          _ = ∏ p ∈ primeBucket Y n m, (2 ^ (2 ^ m)) ^ (t.factorization p) :=
              (Finset.prod_pow_eq_pow_sum _ _ _).symm
          _ ≤ ∏ p ∈ primeBucket Y n m, p ^ (t.factorization p) := by
              refine Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_left ?_ _
              have hgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
              exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) hgt)
          _ = bucketPart Y n m t := rfl
          _ ≤ t := Nat.le_of_dvd (by omega) htm_dvd
          _ ≤ H := htH
      have hlog : 2 ^ m * bucketOmega Y n m t ≤ Nat.log 2 H := Nat.le_log_of_pow_le (by norm_num) hpow
      dsimp only [R]
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos m)).mpr (by rwa [mul_comm])
    exact le_trans hC1 (Nat.choose_le_choose (k m) hΩ_le)
  -- Inject D into Uset × Qset × Π m : M_idx, Bset m
  let Bprod : Finset (∀ _m : M_idx, ℕ) := Fintype.piFinset fun m : M_idx => Bset m.1
  let Ψ : ℕ → ℕ × ℕ × (∀ _m : M_idx, ℕ) :=
    fun d => (uSm Y d, qSm Y d, fun m => bucketPart Y n m.1 d)
  have hmaps : ∀ d ∈ D, Ψ d ∈ Uset ×ˢ (Qset ×ˢ Bprod) := by
    intro d hd
    have hdm := Finset.mem_filter.mp hd
    have hd_Icc := Finset.mem_Icc.mp hdm.1
    rcases hdm.2 with ⟨hd_dvd, ha_eq, hs_eq, hk₀_eq, hk_eq⟩
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · -- uSm Y d ∈ Uset
      refine Finset.mem_image.mpr ⟨(primesSmall Y).filter (fun p => d.factorization p = 1), ?_, rfl⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hk₀_eq⟩
    · -- qSm Y d ∈ Qset
      by_cases hs : s = 0
      · simp only [Qset, hs, dite_true, Finset.mem_singleton]
        have hSq_empty : (primesSmall Y).filter (fun p => 2 ≤ d.factorization p) = ∅ := by
          rw [← Finset.card_eq_zero]; exact hs_eq.trans hs
        dsimp only [Ψ]; unfold qSm; rw [hSq_empty]; simp
      · simp only [Qset, hs, dite_false, Finset.mem_image]
        let Sq := (primesSmall Y).filter (fun p => 2 ≤ d.factorization p)
        have hSq_card : Sq.card = s := hs_eq
        have h2s : 2 * s ≤ a := hvalid.resolve_left hs
        let e_emb := Sq.orderEmbOfFin hSq_card
        let f : Fin s → ℕ := fun i => d.factorization (e_emb i) - 2
        have hf_ge2 : ∀ i : Fin s, 2 ≤ d.factorization (e_emb i) := fun i =>
          (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem Sq hSq_card i)).2
        have hsum_le : ∑ i : Fin s, d.factorization (e_emb i) ≤ a := by
          have hpow : 2 ^ (∑ i : Fin s, d.factorization (e_emb i)) ≤ qSm Y d := by
            rw [← Finset.prod_pow_eq_pow_sum]
            have hq_eq : qSm Y d = ∏ i : Fin s, (e_emb i) ^ (d.factorization (e_emb i)) := by
              unfold qSm
              exact (Finset.prod_bij (fun (i : Fin s) _ => e_emb i)
                (fun i _ => Finset.orderEmbOfFin_mem Sq hSq_card i)
                (fun i₁ _ i₂ _ h => e_emb.injective h)
                (fun p hp => by
                  have hmem : p ∈ Set.range e_emb := by
                    rw [Finset.range_orderEmbOfFin Sq hSq_card]; exact hp
                  obtain ⟨i, hi⟩ := Set.mem_range.mp hmem
                  exact ⟨i, Finset.mem_univ i, hi⟩)
                (fun _ _ => rfl)).symm
            rw [hq_eq]
            refine Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left ?_ _
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp
              (Finset.orderEmbOfFin_mem Sq hSq_card i)).1).2.two_le
          have hlt : qSm Y d < 2 ^ (a + 1) := by
            rw [← ha_eq]; exact Nat.lt_pow_succ_log_self (by norm_num) (qSm Y d)
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt hpow hlt)
          omega
        have hf_sum : ∑ i : Fin s, f i ≤ a - 2 * s := by
          have hadd : ∑ i : Fin s, (f i + 2) = ∑ i : Fin s, d.factorization (e_emb i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have := hf_ge2 i; dsimp [f]; omega
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hadd
          omega
        refine ⟨(Sq, f), Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hSq_card⟩,
           Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr ?_, hf_sum⟩⟩, ?_⟩
        · have hi : f i ≤ ∑ j : Fin s, f j :=
            Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          dsimp only; omega
        · simp only [hSq_card, dite_true]
          dsimp only [Ψ]; unfold qSm
          refine Finset.prod_bij (fun (i : Fin s) _ => e_emb i)
            (fun i _ => Finset.orderEmbOfFin_mem Sq hSq_card i)
            (fun i₁ _ i₂ _ h => e_emb.injective h)
            (fun p hp => by
              have hmem : p ∈ Set.range e_emb := by
                rw [Finset.range_orderEmbOfFin Sq hSq_card]; exact hp
              obtain ⟨i, hi⟩ := Set.mem_range.mp hmem
              exact ⟨i, Finset.mem_univ i, hi⟩)
            (fun i _ => ?_)
          have := hf_ge2 i
          dsimp only [f]
          congr 1; omega
    · -- bucketPart Y n m d ∈ Bset m
      refine Fintype.mem_piFinset.mpr fun m => Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, ?_⟩
      · -- bucketPart Y n m d ∣ bucketPart Y n m t
        unfold bucketPart
        refine Finset.prod_dvd_prod_of_dvd _ _ fun p _ => Nat.pow_dvd_pow p ?_
        exact (Nat.factorization_le_iff_dvd (by omega) (by omega)).mpr hd_dvd p
      · have := bucketPart_pos Y n m.1 t; omega
      · rw [bigOmega_bucketPart]; exact hk_eq m.1 m.2
  have hinj : Set.InjOn Ψ (D : Set ℕ) := by
    intro d₁ hd₁ d₂ hd₂ hEq
    have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1
    have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1
    have hu : uSm Y d₁ = uSm Y d₂ := congrArg (fun x => x.1) hEq
    have hq : qSm Y d₁ = qSm Y d₂ := congrArg (fun x => x.2.1) hEq
    have hb : ∀ m : M_idx, bucketPart Y n m.1 d₁ = bucketPart Y n m.1 d₂ :=
      fun m => congrFun (congrArg (fun x => x.2.2) hEq) m
    rw [eq_qSm_mul_uSm_mul_prod_bucketPart Y n m_start M_max d₁ hY2 hYn hms hMm h1.1 h1.2,
      eq_qSm_mul_uSm_mul_prod_bucketPart Y n m_start M_max d₂ hY2 hYn hms hMm h2.1 h2.2,
      hu, hq]
    congr 1
    exact Finset.prod_congr rfl fun m hm => hb ⟨m, hm⟩
  calc D.card ≤ (Uset ×ˢ (Qset ×ˢ Bprod)).card := Finset.card_le_card_of_injOn Ψ hmaps hinj
    _ = Uset.card * (Qset.card * Bprod.card) := by simp [Finset.card_product]
    _ = Uset.card * Qset.card * Bprod.card := by ring
    _ ≤ Nat.choose (primesSmall Y).card k₀ *
        (if s = 0 then 1 else Nat.choose (primesSmall Y).card s * Nat.choose (a - s) s) *
        ∏ m ∈ M_idx, Nat.choose (R m) (k m) := by
        have hBprod : Bprod.card ≤ ∏ m ∈ M_idx, Nat.choose (R m) (k m) := by
          have hcard : Bprod.card = ∏ m ∈ M_idx, (Bset m).card := by
            dsimp only [Bprod]
            rw [Fintype.card_piFinset]
            exact Finset.prod_coe_sort M_idx (fun m => (Bset m).card)
          rw [hcard]
          exact Finset.prod_le_prod' hB_card
        exact Nat.mul_le_mul (Nat.mul_le_mul hU_card hQ_card) hBprod

/-- **Lemma C2b (Constant-1 Joint Euler-Product Rankin Slice Count Bound):**
For any `N ≤ n`, `Y ≥ 2` (`Y ≤ n`), `2^(2^m_start) ≤ Y`, `n ≤ 2^(2^(M_max + 1))`,
`γ_u, γ_q ≥ 1`, and bucket tilts `lam : ℕ → ℝ` with `1 ≤ lam m` and `∀ p ∈ primeBucket Y n m, lam m ≤ (1/2) * p`:
the number of `d ∈ [1, N]` in slice `(a, s, k₀, k)` satisfies
```
|slice| ≤ N * 2^(-a/2) * (γ_q^s)⁻¹ * (γ_u^k₀)⁻¹ * (∏ m, (lam m ^ k m)⁻¹)
          * exp (γ_u * U_bd + γ_q * (4 * U_bd))
          * exp (10 + 8 * Nat.log 2 (Nat.log 2 n))
          * ∏ m, exp (8 * (lam m - 1))
```
where `U_bd = max 1 (∑_{p ≤ Y} 1/p)`. -/
private lemma lemma_C2b_slice_euler_rankin
    (Y n N m_start M_max a s k₀ : ℕ) (k : ℕ → ℕ)
    (γ_u γ_q : ℝ) (lam : ℕ → ℝ)
    (hY2 : 2 ≤ Y) (hYn : Y ≤ n) (hNn : N ≤ n)
    (hms : 2 ^ (2 ^ m_start) ≤ Y) (hMm : n ≤ 2 ^ (2 ^ (M_max + 1)))
    (hγu : 1 ≤ γ_u) (hγq : 1 ≤ γ_q)
    (hlam_lo : ∀ m ∈ Finset.Icc m_start M_max, 1 ≤ lam m)
    (hlam_hi : ∀ m ∈ Finset.Icc m_start M_max, ∀ p ∈ primeBucket Y n m, lam m ≤ (p : ℝ) / 2) :
    let M_idx := Finset.Icc m_start M_max
    let U_bd : ℝ := max 1 (∑ p ∈ primesSmall Y, (1 : ℝ) / (p : ℝ))
    (((Finset.Icc 1 N).filter fun d =>
        Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
        ∀ m ∈ M_idx, bucketOmega Y n m d = k m).card : ℝ) ≤
      (N : ℝ) * (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ_q ^ s)⁻¹ * (γ_u ^ k₀)⁻¹ *
      (∏ m ∈ M_idx, (lam m ^ (k m))⁻¹) *
      Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) *
      Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) *
      ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := by
  classical
  intro M_idx U_bd
  by_cases hN0 : N = 0
  · simp [hN0]
  let P := (Finset.Icc 1 n).filter Nat.Prime
  let E := Nat.log 2 N
  have hNE : N < 2 ^ (E + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  -- For any prime p ∈ P with p > Y, find its unique bucket index m_of p ∈ M_idx
  let m_of : ℕ → ℕ := fun p => Nat.log 2 (Nat.log 2 (p - 1))
  have hm_of_eq : ∀ m ∈ M_idx, ∀ p ∈ primeBucket Y n m, m_of p = m := by
    intro m _ p hp
    have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hlo : 2 ^ (2 ^ m) < p := lt_of_le_of_lt (le_max_right _ _) hIoc.1
    have hhi : p ≤ 2 ^ (2 ^ (m + 1)) := le_trans hIoc.2 (min_le_right _ _)
    have hr_lo : 2 ^ m ≤ Nat.log 2 (p - 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    have hr_hi : Nat.log 2 (p - 1) < 2 ^ (m + 1) := by
      by_contra hge; push Not at hge
      have hpow : 2 ^ (2 ^ (m + 1)) ≤ p - 1 :=
        le_trans (Nat.pow_le_pow_right (by norm_num) hge) (Nat.pow_log_le_self 2 (by omega))
      omega
    have h1 : m ≤ m_of p := Nat.le_log_of_pow_le (by norm_num) hr_lo
    have h2 : m_of p < m + 1 := by
      by_contra hge; push Not at hge
      have hpow : 2 ^ (m + 1) ≤ Nat.log 2 (p - 1) :=
        le_trans (Nat.pow_le_pow_right (by norm_num) hge) (Nat.pow_log_le_self 2 (by
          have : 1 ≤ 2 ^ m := Nat.one_le_two_pow; omega))
      omega
    omega
  -- Define prime-power weight w p e
  let w : ℕ → ℕ → ℝ := fun p e =>
    if e = 0 then 1
    else if p ≤ Y then
      if e = 1 then γ_u / (p : ℝ)
      else γ_q * ((p : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ^ e
    else (lam (m_of p) / (p : ℝ)) ^ e
  have hw_nn : ∀ p ∈ P, ∀ e, 0 ≤ w p e := by
    intro p hp e
    dsimp only [w]
    split_ifs with he0 hpY he1
    · positivity
    · positivity
    · positivity
    · -- p ∈ P and ¬ (p ≤ Y), so p ∈ primeBucket Y n (m_of p)
      have hpart := primes_partition_eq Y n m_start M_max hY2 hYn hms hMm
      have hp' : p ∈ primesSmall Y ∪ M_idx.biUnion (primeBucket Y n) := by rw [← hpart]; exact hp
      rcases Finset.mem_union.mp hp' with hsm | hlg
      · exfalso; exact hpY (Finset.mem_Icc.mp (Finset.mem_filter.mp hsm).1).2
      · rcases Finset.mem_biUnion.mp hlg with ⟨m, hm, hpm⟩
        rw [hm_of_eq m hm p hpm]
        have := hlam_lo m hm
        positivity
  -- Step 1: Lower bound ∏ p ∈ P, w p (d.factorization p) for every d in our slice
  let D := (Finset.Icc 1 N).filter fun d =>
    Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
    ∀ m ∈ M_idx, bucketOmega Y n m d = k m
  have hW_lower : ∀ d ∈ D,
      (N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ * (∏ m ∈ M_idx, lam m ^ (k m)) ≤
        ∏ p ∈ P, w p (d.factorization p) := by
    intro d hd
    have hdm := Finset.mem_filter.mp hd
    have hd_Icc := Finset.mem_Icc.mp hdm.1
    rcases hdm.2 with ⟨ha_eq, hs_eq, hk₀_eq, hk_eq⟩
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    -- Compute ∏ p ∈ P, w p (d.factorization p) = (d : ℝ)⁻¹ * (qSm Y d)^(1/2) * γ_q^s * γ_u^k₀ * ∏ lam^k
    have hP_eq : P = primesSmall Y ∪ M_idx.biUnion (primeBucket Y n) :=
      primes_partition_eq Y n m_start M_max hY2 hYn hms hMm
    have hprod_split : ∏ p ∈ P, w p (d.factorization p) =
        (∏ p ∈ primesSmall Y, w p (d.factorization p)) *
        ∏ m ∈ M_idx, ∏ p ∈ primeBucket Y n m, w p (d.factorization p) := by
      rw [hP_eq, Finset.prod_union (primesSmall_disjoint_buckets Y n _),
        Finset.prod_biUnion (primeBucket_pairwiseDisjoint Y n _)]
    -- Evaluate small-prime product
    have hsm_eval : ∏ p ∈ primesSmall Y, w p (d.factorization p) =
        ((qSm Y d : ℝ) ^ ((1 : ℝ) / 2) / (qSm Y d : ℝ)) * γ_q ^ s * (γ_u ^ k₀ / (uSm Y d : ℝ)) := by
      let Sq := (primesSmall Y).filter (fun p => 2 ≤ d.factorization p)
      let Su := (primesSmall Y).filter (fun p => d.factorization p = 1)
      rw [← Finset.prod_filter_mul_prod_filter_not (primesSmall Y) (fun p => 2 ≤ d.factorization p)]
      have h1 : ∏ p ∈ Sq, w p (d.factorization p) =
          ((qSm Y d : ℝ) ^ ((1 : ℝ) / 2) / (qSm Y d : ℝ)) * γ_q ^ s := by
        have hpt : ∀ p ∈ Sq, w p (d.factorization p) =
            (((p ^ d.factorization p : ℕ) : ℝ) ^ ((1 : ℝ) / 2) / ((p ^ d.factorization p : ℕ) : ℝ)) * γ_q := by
          intro p hp
          have hp_sm := (Finset.mem_filter.mp hp).1
          have hpY : p ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_sm).1).2
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp_sm).2.pos
          have he2 : 2 ≤ d.factorization p := (Finset.mem_filter.mp hp).2
          dsimp only [w]
          rw [if_neg (by omega), if_pos hpY, if_neg (by omega)]
          rw [Nat.cast_pow, inv_pow, ← Real.rpow_natCast ((p : ℝ) ^ ((1 : ℝ) / 2)) (d.factorization p),
            ← Real.rpow_mul (le_of_lt hp_pos)]
          -- Show ((p : ℝ) ^ e)^(1/2) / (p : ℝ)^e = ((p : ℝ)^(1/2 * e))⁻¹
          have hpow_half : ((p : ℝ) ^ d.factorization p) ^ ((1 : ℝ) / 2) =
              (p : ℝ) ^ ((1 : ℝ) / 2 * (d.factorization p : ℝ)) := by
            rw [← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul (le_of_lt hp_pos)]; congr 1; ring
          have hpow_full : (p : ℝ) ^ d.factorization p =
              (p : ℝ) ^ ((1 : ℝ) / 2 * (d.factorization p : ℝ)) *
              (p : ℝ) ^ ((1 : ℝ) / 2 * (d.factorization p : ℝ)) := by
            rw [← Real.rpow_add hp_pos, ← Real.rpow_natCast (p : ℝ)]; congr 1; ring
          rw [hpow_half, hpow_full]
          have hpos' : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 * (d.factorization p : ℝ)) := Real.rpow_pos_of_pos hp_pos _
          field_simp [ne_of_gt hpos']
        have hSq_card : Sq.card = s := hs_eq
        rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_div_distrib,
          Finset.prod_const, hSq_card]
        have hq_cast : (qSm Y d : ℝ) = ∏ p ∈ Sq, ((p ^ d.factorization p : ℕ) : ℝ) := by
          unfold qSm; rw [Nat.cast_prod]
        rw [hq_cast, Real.finsetProd_rpow Sq _ (fun _ _ => Nat.cast_nonneg _)]
      -- Second part: ¬ (2 ≤ v_p(d)) splits into v_p(d) = 1 (gives γ_u^k₀ / uSm) and v_p(d) = 0 (gives 1)
      have h2 : ∏ p ∈ (primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p),
          w p (d.factorization p) = γ_u ^ k₀ / (uSm Y d : ℝ) := by
        rw [← Finset.prod_filter_mul_prod_filter_not
          ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)) (fun p => d.factorization p = 1)]
        have hzero : ∏ p ∈ ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)).filter
            (fun p => ¬ d.factorization p = 1), w p (d.factorization p) = 1 := by
          refine Finset.prod_eq_one fun p hp => ?_
          have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have h2 := (Finset.mem_filter.mp hp).2
          have h0 : d.factorization p = 0 := by omega
          dsimp only [w]; rw [if_pos h0]
        rw [hzero, mul_one]
        have hfilt : ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)).filter
            (fun p => d.factorization p = 1) = Su := by
          ext p; simp only [Finset.mem_filter, Su]
          constructor
          · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
          · rintro ⟨hp, h1⟩; exact ⟨⟨hp, by omega⟩, h1⟩
        rw [hfilt]
        have hpt : ∀ p ∈ Su, w p (d.factorization p) = γ_u / (p : ℝ) := by
          intro p hp
          have hpY : p ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
          have he1 : d.factorization p = 1 := (Finset.mem_filter.mp hp).2
          dsimp only [w]; rw [if_neg (by omega), if_pos hpY, if_pos he1]
        have hSu_card : Su.card = k₀ := hk₀_eq
        rw [Finset.prod_congr rfl hpt, Finset.prod_div_distrib, Finset.prod_const, hSu_card]
        congr 1; unfold uSm; rw [Nat.cast_prod]
      rw [h1, h2]
    -- Evaluate bucket products
    have hlg_eval : ∀ m ∈ M_idx, ∏ p ∈ primeBucket Y n m, w p (d.factorization p) =
        lam m ^ (k m) / (bucketPart Y n m d : ℝ) := by
      intro m hm
      have hpt : ∀ p ∈ primeBucket Y n m, w p (d.factorization p) =
          lam m ^ (d.factorization p) / ((p ^ d.factorization p : ℕ) : ℝ) := by
        intro p hp
        have hp_gtY : Y < p := lt_of_le_of_lt (le_max_left _ _) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        dsimp only [w]
        by_cases he0 : d.factorization p = 0
        · rw [if_pos he0, he0]; simp
        · rw [if_neg he0, if_neg (by omega), hm_of_eq m hm p hp, div_pow, Nat.cast_pow]
      rw [Finset.prod_congr rfl hpt, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      have hbo : ∑ p ∈ primeBucket Y n m, d.factorization p = k m := hk_eq m hm
      rw [hbo]
      congr 1; unfold bucketPart; rw [Nat.cast_prod]
    rw [hprod_split, hsm_eval, Finset.prod_congr rfl hlg_eval, Finset.prod_div_distrib]
    -- Combine denominators: qSm * uSm * ∏ bucketPart = d
    have hd_fact : (d : ℝ) = (qSm Y d : ℝ) * (uSm Y d : ℝ) * ∏ m ∈ M_idx, (bucketPart Y n m d : ℝ) := by
      have hnat := eq_qSm_mul_uSm_mul_prod_bucketPart Y n m_start M_max d hY2 hYn hms hMm hd_Icc.1 (le_trans hd_Icc.2 hNn)
      exact_mod_cast hnat
    have hq_pos : (0 : ℝ) < (qSm Y d : ℝ) := by
      have : 1 ≤ qSm Y d := Finset.one_le_prod' fun p hp =>
        Nat.one_le_pow _ _ (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos
      exact_mod_cast this
    have hu_pos : (0 : ℝ) < (uSm Y d : ℝ) := by
      have : 1 ≤ uSm Y d := Finset.one_le_prod' fun p hp =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos
      exact_mod_cast this
    have hb_pos : (0 : ℝ) < ∏ m ∈ M_idx, (bucketPart Y n m d : ℝ) :=
      Finset.prod_pos fun m _ => by exact_mod_cast bucketPart_pos Y n m d
    have hcomb : ((qSm Y d : ℝ) ^ ((1 : ℝ) / 2) / (qSm Y d : ℝ)) * γ_q ^ s * (γ_u ^ k₀ / (uSm Y d : ℝ)) *
        ((∏ m ∈ M_idx, lam m ^ k m) / ∏ m ∈ M_idx, (bucketPart Y n m d : ℝ)) =
        (d : ℝ)⁻¹ * (qSm Y d : ℝ) ^ ((1 : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ * (∏ m ∈ M_idx, lam m ^ k m) := by
      rw [hd_fact]; field_simp [ne_of_gt hq_pos, ne_of_gt hu_pos, ne_of_gt hb_pos]
    rw [hcomb]
    -- Compare (N : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ and 2^(a/2) ≤ (qSm Y d)^(1/2)
    have hd_inv : (N : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ :=
      inv_anti₀ hd_pos (by exact_mod_cast hd_Icc.2)
    have hq_ge : (2 : ℝ) ^ ((a : ℝ) / 2) ≤ (qSm Y d : ℝ) ^ ((1 : ℝ) / 2) := by
      have h2a : (2 : ℝ) ^ a ≤ (qSm Y d : ℝ) := by
        have hq1 : 1 ≤ qSm Y d := Finset.one_le_prod' fun p hp =>
          Nat.one_le_pow _ _ (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos
        have : 2 ^ a ≤ qSm Y d := by rw [← ha_eq]; exact Nat.pow_log_le_self 2 (by omega)
        exact_mod_cast this
      calc (2 : ℝ) ^ ((a : ℝ) / 2) = ((2 : ℝ) ^ a) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_mul (by norm_num)]; congr 1; ring
        _ ≤ (qSm Y d : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h2a (by norm_num)
    have hprod_nn : 0 ≤ γ_q ^ s * γ_u ^ k₀ * ∏ m ∈ M_idx, lam m ^ k m := by
      refine mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (Finset.prod_nonneg fun m hm => pow_nonneg (by linarith [hlam_lo m hm]) _)
    have h1 := mul_le_mul hd_inv hq_ge (by positivity) (by positivity)
    calc (N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ * ∏ m ∈ M_idx, lam m ^ k m
        = ((N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2)) * (γ_q ^ s * γ_u ^ k₀ * ∏ m ∈ M_idx, lam m ^ k m) := by ring
      _ ≤ ((d : ℝ)⁻¹ * (qSm Y d : ℝ) ^ ((1 : ℝ) / 2)) * (γ_q ^ s * γ_u ^ k₀ * ∏ m ∈ M_idx, lam m ^ k m) :=
          mul_le_mul_of_nonneg_right h1 hprod_nn
      _ = (d : ℝ)⁻¹ * (qSm Y d : ℝ) ^ ((1 : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ * ∏ m ∈ M_idx, lam m ^ k m := by ring
  -- Step 2: Apply euler_product_rankin_bound
  have hRankin : ∑ d ∈ Finset.Icc 1 N, ∏ p ∈ P, w p (d.factorization p) ≤
      ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), w p e :=
    euler_product_rankin_bound N E P hNE (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p hp hpN => Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, le_trans hpN hNn⟩, hp⟩)
      w hw_nn
  have hD_le_sum : (D.card : ℝ) * ((N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ *
      ∏ m ∈ M_idx, lam m ^ k m) ≤ ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), w p e := by
    calc (D.card : ℝ) * ((N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ *
            ∏ m ∈ M_idx, lam m ^ k m)
        = ∑ _d ∈ D, ((N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ *
            ∏ m ∈ M_idx, lam m ^ k m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ d ∈ D, ∏ p ∈ P, w p (d.factorization p) := Finset.sum_le_sum hW_lower
      _ ≤ ∑ d ∈ Finset.Icc 1 N, ∏ p ∈ P, w p (d.factorization p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ =>
            Finset.prod_nonneg fun p hp => hw_nn p hp _
      _ ≤ ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), w p e := hRankin
  -- Step 3: Upper bound the Euler product ∏ p ∈ P, ∑ e, w p e
  have hEuler_ub : ∏ p ∈ P, ∑ e ∈ Finset.range (E + 1), w p e ≤
      Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) *
      Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) *
      ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := by
    have hP_eq : P = primesSmall Y ∪ M_idx.biUnion (primeBucket Y n) :=
      primes_partition_eq Y n m_start M_max hY2 hYn hms hMm
    rw [hP_eq, Finset.prod_union (primesSmall_disjoint_buckets Y n _),
      Finset.prod_biUnion (primeBucket_pairwiseDisjoint Y n _)]
    -- Small primes factor: ≤ exp (γ_u * U_bd + γ_q * 4 * U_bd)
    have hsm_ub : ∏ p ∈ primesSmall Y, ∑ e ∈ Finset.range (E + 1), w p e ≤
        Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) := by
      have hpt : ∀ p ∈ primesSmall Y, ∑ e ∈ Finset.range (E + 1), w p e ≤
          Real.exp ((γ_u + 4 * γ_q) * ((1 : ℝ) / (p : ℝ))) := by
        intro p hp
        have hpY : p ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        -- Split range (E + 1) into 0, 1 (if E ≥ 1), and Ico 2 (E + 1)
        have hsum_le : ∑ e ∈ Finset.range (E + 1), w p e ≤ 1 + (γ_u + 4 * γ_q) * ((1 : ℝ) / (p : ℝ)) := by
          cases E with
          | zero =>
            simp [w]; positivity
          | succ E' =>
            rw [Finset.sum_range_succ']
            have hw0 : w p 0 = 1 := by simp [w]
            rw [hw0]
            cases E' with
            | zero =>
              simp only [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, zero_add]
              have hw1 : w p 1 = γ_u / (p : ℝ) := by simp [w, hpY]
              rw [hw1]
              have : 0 ≤ 4 * γ_q * ((1 : ℝ) / (p : ℝ)) := by positivity
              linarith [show γ_u / (p : ℝ) = γ_u * ((1 : ℝ) / (p : ℝ)) by ring]
            | succ E'' =>
              rw [Finset.sum_range_succ']
              have hw1 : w p 1 = γ_u / (p : ℝ) := by simp [w, hpY]
              rw [hw1]
              -- Remaining sum is over e ∈ Ico 2 (E'' + 3)
              have htail_eq : ∑ k ∈ Finset.range (E'' + 1), w p (k + 1 + 1) =
                  γ_q * ∑ e ∈ Finset.Ico 2 (E'' + 3), (((p : ℝ) ^ ((1 : ℝ) / 2))⁻¹) ^ e := by
                have hbij : Finset.Ico 2 (E'' + 3) = (Finset.range (E'' + 1)).image (fun k => k + 1 + 1) := by
                  ext e; simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
                  constructor
                  · intro ⟨h1, h2⟩; exact ⟨e - 2, by omega, by omega⟩
                  · rintro ⟨k, hk, rfl⟩; omega
                rw [hbij, Finset.sum_image (fun _ _ _ _ h => by omega), Finset.mul_sum]
                refine Finset.sum_congr rfl fun k _ => ?_
                dsimp only [w]
                rw [if_neg (by omega), if_pos hpY, if_neg (by omega)]
              rw [htail_eq]
              let r : ℝ := ((p : ℝ) ^ ((1 : ℝ) / 2))⁻¹
              have hr0 : 0 ≤ r := by positivity
              have hr34 : r ≤ 3 / 4 := by
                have hsq : (4 / 3 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
                  rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (le_of_lt hp_pos)]
                  linarith
                have hpos' : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hp_pos _
                rw [show (3 : ℝ) / 4 = ((4 : ℝ) / 3)⁻¹ by norm_num]
                exact inv_anti₀ (by norm_num) hsq
              have hgeo := geom_sum_from_two_le hr0 hr34 (E'' + 2)
              have hr2 : r ^ 2 = (1 : ℝ) / (p : ℝ) := by
                dsimp only [r]
                rw [inv_pow, ← Real.rpow_natCast ((p : ℝ) ^ ((1 : ℝ) / 2)) 2,
                  ← Real.rpow_mul (le_of_lt hp_pos)]
                norm_num
              rw [hr2] at hgeo
              have hq_tail : γ_q * ∑ e ∈ Finset.Ico 2 (E'' + 3), r ^ e ≤ 4 * γ_q * ((1 : ℝ) / (p : ℝ)) := by
                have := mul_le_mul_of_nonneg_left hgeo (by linarith : 0 ≤ γ_q)
                linarith
              linarith [show γ_u / (p : ℝ) = γ_u * ((1 : ℝ) / (p : ℝ)) by ring]
        linarith [hsum_le, Real.add_one_le_exp ((γ_u + 4 * γ_q) * ((1 : ℝ) / (p : ℝ)))]
      calc ∏ p ∈ primesSmall Y, ∑ e ∈ Finset.range (E + 1), w p e
          ≤ ∏ p ∈ primesSmall Y, Real.exp ((γ_u + 4 * γ_q) * ((1 : ℝ) / (p : ℝ))) :=
            Finset.prod_le_prod (fun p hp => Finset.sum_nonneg fun e _ =>
              hw_nn p (by rw [hP_eq]; exact Finset.mem_union_left _ hp) e) hpt
        _ = Real.exp (∑ p ∈ primesSmall Y, (γ_u + 4 * γ_q) * ((1 : ℝ) / (p : ℝ))) := (Real.exp_sum _ _).symm
        _ = Real.exp ((γ_u + 4 * γ_q) * ∑ p ∈ primesSmall Y, (1 : ℝ) / (p : ℝ)) := by rw [← Finset.mul_sum]
        _ ≤ Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) := by
            apply Real.exp_le_exp.mpr
            have hle : ∑ p ∈ primesSmall Y, (1 : ℝ) / (p : ℝ) ≤ U_bd := le_max_right 1 _
            have hnn : 0 ≤ γ_u + 4 * γ_q := by linarith
            nlinarith
    -- Large-prime bucket product: ≤ exp(10 + 8 log2 log2 n) * ∏ m, exp(8 * (lam m - 1))
    have hlg_ub : ∏ m ∈ M_idx, ∏ p ∈ primeBucket Y n m, ∑ e ∈ Finset.range (E + 1), w p e ≤
        Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) * ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := by
      have hpt : ∀ m ∈ M_idx, ∀ p ∈ primeBucket Y n m,
          ∑ e ∈ Finset.range (E + 1), w p e ≤
            (1 - (1 : ℝ) / (p : ℝ))⁻¹ * Real.exp (2 * (lam m - 1) * ((1 : ℝ) / (p : ℝ))) := by
        intro m hm p hp
        have hp_gtY : Y < p := lt_of_le_of_lt (le_max_left _ _) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hlam1 : 1 ≤ lam m := hlam_lo m hm
        have hlam_half : lam m / (p : ℝ) ≤ 1 / 2 := by
          have := hlam_hi m hm p hp
          rw [div_le_iff₀ hp_pos]; linarith
        have hsum_eq : ∑ e ∈ Finset.range (E + 1), w p e =
            ∑ e ∈ Finset.range (E + 1), (lam m / (p : ℝ)) ^ e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          dsimp only [w]
          by_cases he0 : e = 0
          · rw [if_pos he0, he0, pow_zero]
          · rw [if_neg he0, if_neg (by omega), hm_of_eq m hm p hp]
        rw [hsum_eq]
        have hgeo := geom_sum_le_inv (by positivity) (by linarith : lam m / (p : ℝ) < 1) E
        -- (1 - lam/p)⁻¹ = (1 - 1/p)⁻¹ * ((1 - 1/p) / (1 - lam/p))
        have hden1 : 0 < 1 - (1 : ℝ) / (p : ℝ) := by
          have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
          linarith
        have hden2 : 0 < 1 - lam m / (p : ℝ) := by linarith
        have hsplit : (1 - lam m / (p : ℝ))⁻¹ =
            (1 - (1 : ℝ) / (p : ℝ))⁻¹ * ((1 - (1 : ℝ) / (p : ℝ)) / (1 - lam m / (p : ℝ))) := by
          rw [mul_div_assoc', inv_mul_cancel₀ (ne_of_gt hden1), one_div]
        have hratio : (1 - (1 : ℝ) / (p : ℝ)) / (1 - lam m / (p : ℝ)) ≤
            Real.exp (2 * (lam m - 1) * ((1 : ℝ) / (p : ℝ))) := by
          have h1 : (1 - (1 : ℝ) / (p : ℝ)) / (1 - lam m / (p : ℝ)) =
              1 + ((lam m - 1) * ((1 : ℝ) / (p : ℝ))) / (1 - lam m / (p : ℝ)) := by
            have hnum : (1 - (1 : ℝ) / (p : ℝ)) =
                (1 - lam m / (p : ℝ)) + (lam m - 1) * ((1 : ℝ) / (p : ℝ)) := by ring
            rw [hnum, add_div, div_self (ne_of_gt hden2)]
          have h2 : ((lam m - 1) * ((1 : ℝ) / (p : ℝ))) / (1 - lam m / (p : ℝ)) ≤
              2 * (lam m - 1) * ((1 : ℝ) / (p : ℝ)) := by
            rw [div_le_iff₀ hden2]
            have hnn : 0 ≤ (lam m - 1) * ((1 : ℝ) / (p : ℝ)) := by
              exact mul_nonneg (by linarith) (by positivity)
            nlinarith
          linarith [Real.add_one_le_exp (2 * (lam m - 1) * ((1 : ℝ) / (p : ℝ)))]
        calc ∑ e ∈ Finset.range (E + 1), (lam m / (p : ℝ)) ^ e
            ≤ (1 - lam m / (p : ℝ))⁻¹ := hgeo
          _ = (1 - (1 : ℝ) / (p : ℝ))⁻¹ * ((1 - (1 : ℝ) / (p : ℝ)) / (1 - lam m / (p : ℝ))) := hsplit
          _ ≤ (1 - (1 : ℝ) / (p : ℝ))⁻¹ * Real.exp (2 * (lam m - 1) * ((1 : ℝ) / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr (le_of_lt hden1))
      have hbm : ∀ m ∈ M_idx, ∏ p ∈ primeBucket Y n m, ∑ e ∈ Finset.range (E + 1), w p e ≤
          (∏ p ∈ primeBucket Y n m, (1 - (1 : ℝ) / (p : ℝ))⁻¹) * Real.exp (8 * (lam m - 1)) := by
        intro m hm
        calc ∏ p ∈ primeBucket Y n m, ∑ e ∈ Finset.range (E + 1), w p e
            ≤ ∏ p ∈ primeBucket Y n m,
                ((1 - (1 : ℝ) / (p : ℝ))⁻¹ * Real.exp (2 * (lam m - 1) * ((1 : ℝ) / (p : ℝ)))) :=
              Finset.prod_le_prod (fun p hp => Finset.sum_nonneg fun e _ =>
                hw_nn p (by rw [hP_eq]; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hm, hp⟩)) e)
                (hpt m hm)
          _ = (∏ p ∈ primeBucket Y n m, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
              Real.exp (2 * (lam m - 1) * ∑ p ∈ primeBucket Y n m, (1 : ℝ) / (p : ℝ)) := by
              rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
          _ ≤ (∏ p ∈ primeBucket Y n m, (1 - (1 : ℝ) / (p : ℝ))⁻¹) * Real.exp (8 * (lam m - 1)) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
                (Finset.prod_nonneg fun p hp => inv_nonneg.mpr ?_)
              · have hsub : primeBucket Y n m ⊆
                    (Finset.Ioc (2 ^ (2 ^ m)) (2 ^ (2 ^ (m + 1)))).filter Nat.Prime := by
                  intro p hp
                  have hIoc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
                  exact Finset.mem_filter.mpr
                    ⟨Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (le_max_right _ _) hIoc.1,
                      le_trans hIoc.2 (min_le_right _ _)⟩, (Finset.mem_filter.mp hp).2⟩
                have hsum4 : ∑ p ∈ primeBucket Y n m, (1 : ℝ) / (p : ℝ) ≤ 4 :=
                  le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
                    (sum_inv_primes_bucket_le m)
                have hlam1 : 0 ≤ lam m - 1 := by linarith [hlam_lo m hm]
                nlinarith
              · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
                have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
                linarith
      calc ∏ m ∈ M_idx, ∏ p ∈ primeBucket Y n m, ∑ e ∈ Finset.range (E + 1), w p e
          ≤ ∏ m ∈ M_idx, ((∏ p ∈ primeBucket Y n m, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
              Real.exp (8 * (lam m - 1))) :=
            Finset.prod_le_prod (fun m hm => Finset.prod_nonneg fun p hp => Finset.sum_nonneg fun e _ =>
              hw_nn p (by rw [hP_eq]; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hm, hp⟩)) e) hbm
        _ = (∏ p ∈ M_idx.biUnion (primeBucket Y n), (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
            ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_biUnion (primeBucket_pairwiseDisjoint Y n _)]
        _ ≤ (∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹) * ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => le_of_lt (Real.exp_pos _))
            have hsub : M_idx.biUnion (primeBucket Y n) ⊆ P := by
              rw [hP_eq]; exact Finset.subset_union_right
            rw [← Finset.prod_sdiff hsub]
            refine le_mul_of_one_le_left
              (Finset.prod_nonneg fun p hp => inv_nonneg.mpr ?_)
              (Finset.one_le_prod fun p hp => ?_)
            · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
                exact_mod_cast (Finset.mem_filter.mp (hsub hp)).2.two_le
              have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
              linarith
            · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
                exact_mod_cast (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.two_le
              have h1p_pos : 0 < 1 - (1 : ℝ) / (p : ℝ) := by
                have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
                linarith
              rw [one_le_inv₀ h1p_pos]
              have : (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by positivity
              linarith
        _ ≤ Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) *
            ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) :=
            mul_le_mul_of_nonneg_right (prod_inv_one_sub_prime_le n)
              (Finset.prod_nonneg fun _ _ => le_of_lt (Real.exp_pos _))
    calc (∏ p ∈ primesSmall Y, ∑ e ∈ Finset.range (E + 1), w p e) *
            ∏ m ∈ M_idx, ∏ p ∈ primeBucket Y n m, ∑ e ∈ Finset.range (E + 1), w p e
        ≤ Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) *
          (Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) *
            ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1))) :=
          mul_le_mul hsm_ub hlg_ub
            (Finset.prod_nonneg fun m hm => Finset.prod_nonneg fun p hp => Finset.sum_nonneg fun e _ =>
              hw_nn p (by rw [hP_eq]; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hm, hp⟩)) e)
            (le_of_lt (Real.exp_pos _))
      _ = Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) *
          Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) *
          ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := by ring
  -- Step 4: Divide by the positive coefficient on the LHS
  have hD_le_E : (D.card : ℝ) * ((N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ *
      ∏ m ∈ M_idx, lam m ^ k m) ≤
      Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) *
      Real.exp (10 + 8 * (Nat.log 2 (Nat.log 2 n) : ℝ)) *
      ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) := le_trans hD_le_sum hEuler_ub
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcoeff_pos : 0 < (N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ *
      ∏ m ∈ M_idx, lam m ^ k m := by
    refine mul_pos (mul_pos (mul_pos (mul_pos (inv_pos.mpr hN_pos) (by positivity))
      (pow_pos (by linarith) _)) (pow_pos (by linarith) _))
      (Finset.prod_pos fun m hm => pow_pos (by linarith [hlam_lo m hm]) _)
  have hinv_eq : ((N : ℝ)⁻¹ * (2 : ℝ) ^ ((a : ℝ) / 2) * γ_q ^ s * γ_u ^ k₀ *
      ∏ m ∈ M_idx, lam m ^ k m)⁻¹ =
      (N : ℝ) * (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ_q ^ s)⁻¹ * (γ_u ^ k₀)⁻¹ *
      ∏ m ∈ M_idx, (lam m ^ k m)⁻¹ := by
    have h2neg : ((2 : ℝ) ^ ((a : ℝ) / 2))⁻¹ = (2 : ℝ) ^ (-(a : ℝ) / 2) := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
    simp only [mul_inv, inv_inv, Finset.prod_inv_distrib, h2neg]
  have hmul_inv := mul_le_mul_of_nonneg_right hD_le_E (inv_nonneg.mpr (le_of_lt hcoeff_pos))
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hcoeff_pos), mul_one, hinv_eq] at hmul_inv
  linarith

/-! ### Exact Divisor-Count Bound on Multi-Scale Regime 2 Slices (`K₁` Bound) -/

/-- Exact divisor-count bound on a multi-scale Regime 2 slice:
for `1 ≤ d ≤ n` with `Nat.log 2 (qSm Y d) = a`, `omegaQ Y d = s`, `omegaU Y d = k₀`, and
`bucketOmega Y n m d = k m` for all `m ∈ Icc m_start M_max`,
```
d.divisors.card ≤ 3 ^ s * 2 ^ ((a + 3) / 4) * 2 ^ k₀ * ∏ m ∈ Icc m_start M_max, 2 ^ (k m).
``` -/
private lemma slice_divisors_card_le
    (Y n m_start M_max d a s k₀ : ℕ) (k : ℕ → ℕ)
    (hY2 : 2 ≤ Y) (hYn : Y ≤ n) (hms : 2 ^ (2 ^ m_start) ≤ Y)
    (hMm : n ≤ 2 ^ (2 ^ (M_max + 1)))
    (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (ha : Nat.log 2 (qSm Y d) = a) (hs : omegaQ Y d = s) (hk₀ : omegaU Y d = k₀)
    (hk : ∀ m ∈ Finset.Icc m_start M_max, bucketOmega Y n m d = k m) :
    d.divisors.card ≤
      3 ^ s * 2 ^ ((a + 3) / 4) * 2 ^ k₀ * ∏ m ∈ Finset.Icc m_start M_max, 2 ^ (k m) := by
  classical
  have hdiv_prod : d.divisors.card ≤ ∏ p ∈ d.primeFactors, (d.factorization p + 1) := by
    let Φ : ℕ → (∀ p : d.primeFactors, ℕ) := fun x p => x.factorization p.1
    let box : Finset (∀ p : d.primeFactors, ℕ) :=
      Fintype.piFinset fun p : d.primeFactors => Finset.range (d.factorization p.1 + 1)
    have hmaps : ∀ x ∈ d.divisors, Φ x ∈ box := by
      intro x hx
      have hdvd := (Nat.mem_divisors.mp hx).1
      refine Fintype.mem_piFinset.mpr fun p => Finset.mem_range.mpr ?_
      have hle : x.factorization p.1 ≤ d.factorization p.1 :=
        (Nat.factorization_le_iff_dvd (by intro h0; rw [h0, zero_dvd_iff] at hdvd; omega) (by omega)).mpr hdvd p.1
      dsimp only [Φ]; omega
    have hinj : Set.InjOn Φ (d.divisors : Set ℕ) := by
      intro x₁ hx₁ x₂ hx₂ hEq
      have h1 := (Nat.mem_divisors.mp hx₁).1
      have h2 := (Nat.mem_divisors.mp hx₂).1
      have hx₁_ne : x₁ ≠ 0 := by intro h0; rw [h0, zero_dvd_iff] at h1; omega
      have hx₂_ne : x₂ ≠ 0 := by intro h0; rw [h0, zero_dvd_iff] at h2; omega
      apply Nat.eq_of_factorization_eq hx₁_ne hx₂_ne
      intro p
      by_cases hp : p ∈ d.primeFactors
      · exact congrFun hEq ⟨p, hp⟩
      · have hdp : d.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
        have hle1 : x₁.factorization p ≤ d.factorization p :=
          (Nat.factorization_le_iff_dvd hx₁_ne (by omega)).mpr h1 p
        have hle2 : x₂.factorization p ≤ d.factorization p :=
          (Nat.factorization_le_iff_dvd hx₂_ne (by omega)).mpr h2 p
        omega
    calc d.divisors.card ≤ box.card := Finset.card_le_card_of_injOn Φ hmaps hinj
      _ = ∏ p : d.primeFactors, (d.factorization p.1 + 1) := by simp [box]
      _ = ∏ p ∈ d.primeFactors, (d.factorization p + 1) :=
          Finset.prod_coe_sort d.primeFactors (fun p => d.factorization p + 1)
  have hsub_pf : d.primeFactors ⊆ (Finset.Icc 1 n).filter Nat.Prime := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpr.one_le, le_trans (Nat.le_of_dvd (by omega) hdvd) hdn⟩, hpr⟩
  have hprod_eq : ∏ p ∈ d.primeFactors, (d.factorization p + 1) =
      ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (d.factorization p + 1) := by
    refine Finset.prod_subset hsub_pf fun p _ hp_not => ?_
    have h0 : d.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not
    rw [h0]; rfl
  rw [hprod_eq, primes_partition_eq Y n m_start M_max hY2 hYn hms hMm,
    Finset.prod_union (primesSmall_disjoint_buckets Y n _),
    Finset.prod_biUnion (primeBucket_pairwiseDisjoint Y n _)] at hdiv_prod
  let Sq := (primesSmall Y).filter (fun p => 2 ≤ d.factorization p)
  let Su := (primesSmall Y).filter (fun p => d.factorization p = 1)
  have hsm_split : ∏ p ∈ primesSmall Y, (d.factorization p + 1) =
      (∏ p ∈ Sq, (d.factorization p + 1)) * 2 ^ k₀ := by
    rw [← Finset.prod_filter_mul_prod_filter_not (primesSmall Y) (fun p => 2 ≤ d.factorization p)]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)) (fun p => d.factorization p = 1)]
    have h0prod : ∏ p ∈ ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)).filter
        (fun p => ¬ d.factorization p = 1), (d.factorization p + 1) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have h2 := (Finset.mem_filter.mp hp).2
      have h0 : d.factorization p = 0 := by omega
      rw [h0]; rfl
    rw [h0prod, mul_one]
    have hfilt : ((primesSmall Y).filter (fun p => ¬ 2 ≤ d.factorization p)).filter
        (fun p => d.factorization p = 1) = Su := by
      ext p; simp only [Finset.mem_filter, Su]
      constructor
      · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
      · rintro ⟨hp, h1⟩; exact ⟨⟨hp, by omega⟩, h1⟩
    rw [hfilt]
    calc ∏ p ∈ Su, (d.factorization p + 1)
        = ∏ _p ∈ Su, 2 := Finset.prod_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      _ = 2 ^ Su.card := by simp
      _ = 2 ^ k₀ := by rw [← hk₀]; rfl
  have hSq_le : ∏ p ∈ Sq, (d.factorization p + 1) ≤ 3 ^ s * 2 ^ ((a + 3) / 4) := by
    have hsum_e : ∑ p ∈ Sq, d.factorization p ≤ a := by
      have hpow : 2 ^ (∑ p ∈ Sq, d.factorization p) ≤ qSm Y d := by
        rw [← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_left ?_ _
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.two_le
      have hlt : qSm Y d < 2 ^ (a + 1) := by
        rw [← ha]; exact Nat.lt_pow_succ_log_self (by norm_num) (qSm Y d)
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt hpow hlt)
      omega
    have hpow4 : (∏ p ∈ Sq, (d.factorization p + 1)) ^ 4 ≤ (3 ^ s * 2 ^ ((a + 3) / 4)) ^ 4 := by
      calc (∏ p ∈ Sq, (d.factorization p + 1)) ^ 4
          = ∏ p ∈ Sq, (d.factorization p + 1) ^ 4 := (Finset.prod_pow Sq 4 _).symm
        _ ≤ ∏ p ∈ Sq, (81 * 2 ^ (d.factorization p)) :=
            Finset.prod_le_prod' fun p _ => nat_succ_pow_four_le (d.factorization p)
        _ = 81 ^ Sq.card * 2 ^ (∑ p ∈ Sq, d.factorization p) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
        _ ≤ 81 ^ s * 2 ^ (4 * ((a + 3) / 4)) := by
            have hScard : Sq.card = s := hs
            rw [hScard]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = (3 ^ s * 2 ^ ((a + 3) / 4)) ^ 4 := by
            have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
            rw [h81, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
            congr 2 <;> ring
    exact (Nat.pow_le_pow_iff_left (by norm_num : 4 ≠ 0)).mp hpow4
  have hbuck_le : ∏ m ∈ Finset.Icc m_start M_max, ∏ p ∈ primeBucket Y n m, (d.factorization p + 1) ≤
      ∏ m ∈ Finset.Icc m_start M_max, 2 ^ (k m) := by
    refine Finset.prod_le_prod' fun m hm => ?_
    calc ∏ p ∈ primeBucket Y n m, (d.factorization p + 1)
        ≤ ∏ p ∈ primeBucket Y n m, 2 ^ (d.factorization p) :=
          Finset.prod_le_prod' fun p _ => nat_succ_le_two_pow (d.factorization p)
      _ = 2 ^ (bucketOmega Y n m d) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = 2 ^ (k m) := by rw [hk m hm]
  rw [hsm_split] at hdiv_prod
  calc d.divisors.card
      ≤ (∏ p ∈ Sq, (d.factorization p + 1)) * 2 ^ k₀ *
          ∏ m ∈ Finset.Icc m_start M_max, ∏ p ∈ primeBucket Y n m, (d.factorization p + 1) := hdiv_prod
    _ ≤ (3 ^ s * 2 ^ ((a + 3) / 4)) * 2 ^ k₀ *
          ∏ m ∈ Finset.Icc m_start M_max, 2 ^ (k m) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hSq_le) hbuck_le

/-! ### Per-Factor Optimization Bounds (`F'_u`, `F'_q`, `F'_m`) for the `1/2` Exponent -/

/-- Absorbed squarefree small-prime factor bound (`F'_u`). -/
private lemma factor_Fu_le (P_card k₀ : ℕ) {U_bd : ℝ} (hU : 1 ≤ U_bd) :
    let γ := max 1 ((k₀ : ℝ) / U_bd)
    ((2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * (γ ^ k₀)⁻¹ * Real.exp (γ * U_bd)) ^ ((1 : ℝ) / 3) ≤
      Real.exp (U_bd / 3) * Real.exp ((2 : ℝ) / 3 * Real.sqrt (2 * (P_card : ℝ) * U_bd)) := by
  intro γ
  by_cases hk : k₀ = 0
  · subst hk
    have hγ : γ = 1 := by dsimp [γ]; simp
    rw [hγ, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, inv_one, mul_one,
      one_mul, one_mul, ← Real.exp_mul, show U_bd * ((1 : ℝ) / 3) = U_bd / 3 by ring, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (2 : ℝ) / 3 * Real.sqrt (2 * (P_card : ℝ) * U_bd) := by positivity
    linarith
  · have hk1 : 1 ≤ k₀ := by omega
    have hk_pos : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk1
    have hU_pos : 0 < U_bd := by linarith
    have hγ_bound : (γ ^ k₀)⁻¹ * Real.exp (γ * U_bd) ≤
        Real.exp U_bd * (Real.exp 1 * U_bd / (k₀ : ℝ)) ^ k₀ := by
      by_cases hcase : (k₀ : ℝ) ≤ U_bd
      · have hγ1 : γ = 1 := max_eq_left ((div_le_one hU_pos).mpr hcase)
        rw [hγ1, one_pow, inv_one, one_mul, one_mul]
        have hbase_ge1 : 1 ≤ Real.exp 1 * U_bd / (k₀ : ℝ) := by
          rw [one_le_div hk_pos]
          have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          nlinarith
        nlinarith [one_le_pow₀ (n := k₀) hbase_ge1, Real.exp_pos U_bd]
      · push Not at hcase
        have hγeq : γ = (k₀ : ℝ) / U_bd := max_eq_right ((one_le_div hU_pos).mpr (le_of_lt hcase))
        rw [hγeq, div_mul_cancel₀ _ (ne_of_gt hU_pos), div_pow, inv_div]
        have hexp_k : Real.exp (k₀ : ℝ) = (Real.exp 1) ^ k₀ := by rw [← Real.exp_nat_mul, mul_one]
        rw [hexp_k, ← mul_div_right_comm, ← mul_pow, mul_comm U_bd (Real.exp 1), ← div_pow]
        have heU : 1 ≤ Real.exp U_bd := Real.one_le_exp (by linarith)
        nlinarith [pow_nonneg (show 0 ≤ Real.exp 1 * U_bd / (k₀ : ℝ) by positivity) k₀]
    have hch := binom_le_exp_pow P_card k₀ hk1
    have hinside : (2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * (γ ^ k₀)⁻¹ * Real.exp (γ * U_bd) ≤
        Real.exp U_bd * (Real.exp 1 * Real.sqrt (2 * (P_card : ℝ) * U_bd) / (k₀ : ℝ)) ^ (2 * k₀) := by
      have h1 : (2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * ((γ ^ k₀)⁻¹ * Real.exp (γ * U_bd)) ≤
          (2 : ℝ) ^ k₀ * (Real.exp 1 * (P_card : ℝ) / (k₀ : ℝ)) ^ k₀ *
            (Real.exp U_bd * (Real.exp 1 * U_bd / (k₀ : ℝ)) ^ k₀) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hch (by positivity)) hγ_bound (by positivity) (by positivity)
      have hsq : Real.sqrt (2 * (P_card : ℝ) * U_bd) ^ 2 = 2 * (P_card : ℝ) * U_bd :=
        Real.sq_sqrt (by positivity)
      have h2eq : (2 : ℝ) ^ k₀ * (Real.exp 1 * (P_card : ℝ) / (k₀ : ℝ)) ^ k₀ *
            (Real.exp U_bd * (Real.exp 1 * U_bd / (k₀ : ℝ)) ^ k₀) =
          Real.exp U_bd * (Real.exp 1 * Real.sqrt (2 * (P_card : ℝ) * U_bd) / (k₀ : ℝ)) ^ (2 * k₀) := by
        rw [pow_mul]
        have hbase : 2 * (Real.exp 1 * (P_card : ℝ) / (k₀ : ℝ)) * (Real.exp 1 * U_bd / (k₀ : ℝ)) =
            (Real.exp 1 * Real.sqrt (2 * (P_card : ℝ) * U_bd) / (k₀ : ℝ)) ^ 2 := by
          rw [div_pow, mul_pow, hsq]; ring
        calc (2 : ℝ) ^ k₀ * (Real.exp 1 * (P_card : ℝ) / (k₀ : ℝ)) ^ k₀ *
              (Real.exp U_bd * (Real.exp 1 * U_bd / (k₀ : ℝ)) ^ k₀)
            = Real.exp U_bd * ((2 : ℝ) ^ k₀ * (Real.exp 1 * (P_card : ℝ) / (k₀ : ℝ)) ^ k₀ *
                (Real.exp 1 * U_bd / (k₀ : ℝ)) ^ k₀) := by ring
          _ = Real.exp U_bd * (2 * (Real.exp 1 * (P_card : ℝ) / (k₀ : ℝ)) *
                (Real.exp 1 * U_bd / (k₀ : ℝ))) ^ k₀ := by rw [← mul_pow, ← mul_pow]
          _ = Real.exp U_bd * ((Real.exp 1 * Real.sqrt (2 * (P_card : ℝ) * U_bd) / (k₀ : ℝ)) ^ 2) ^ k₀ := by
                rw [hbase]
      linarith [h1, h2eq, show (2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * (γ ^ k₀)⁻¹ * Real.exp (γ * U_bd) =
        (2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * ((γ ^ k₀)⁻¹ * Real.exp (γ * U_bd)) by ring]
    calc ((2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * (γ ^ k₀)⁻¹ * Real.exp (γ * U_bd)) ^ ((1 : ℝ) / 3)
        ≤ (Real.exp U_bd * (Real.exp 1 * Real.sqrt (2 * (P_card : ℝ) * U_bd) / (k₀ : ℝ)) ^ (2 * k₀)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hinside (by norm_num)
      _ = Real.exp (U_bd / 3) *
            ((Real.exp 1 * Real.sqrt (2 * (P_card : ℝ) * U_bd) / (k₀ : ℝ)) ^ (2 * k₀)) ^ ((1 : ℝ) / 3) := by
          rw [Real.mul_rpow (le_of_lt (Real.exp_pos _)) (by positivity), ← Real.exp_mul,
            show U_bd * ((1 : ℝ) / 3) = U_bd / 3 by ring]
      _ ≤ Real.exp (U_bd / 3) * Real.exp ((2 : ℝ) / 3 * Real.sqrt (2 * (P_card : ℝ) * U_bd)) :=
          mul_le_mul_of_nonneg_left (exp_mul_div_pow_two_thirds_le_exp (by positivity) k₀ hk1)
            (le_of_lt (Real.exp_pos _))

/-- Absorbed squareful small-prime factor bound (`F'_q`). -/
private lemma factor_Fq_le (P_card a s : ℕ) {Q_bd : ℝ} (hQ : 1 ≤ Q_bd) :
    let γ := max 1 ((s : ℝ) / Q_bd)
    ((3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) *
      ((if s = 0 then 1 else Nat.choose P_card s * Nat.choose (a - s) s : ℕ) : ℝ) *
      (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ ^ s)⁻¹ * Real.exp (γ * Q_bd)) ^ ((1 : ℝ) / 3) ≤
      Real.exp (Q_bd / 3) * Real.exp ((2 : ℝ) / 3 * Real.sqrt (24 * (P_card : ℝ) * Q_bd)) := by
  intro γ
  have h2comb : (2 : ℝ) ^ ((a : ℝ) / 4) * (2 : ℝ) ^ (-(a : ℝ) / 2) = (2 : ℝ) ^ (-(a : ℝ) / 4) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  by_cases hs : s = 0
  · subst hs
    have hγ : γ = 1 := by dsimp [γ]; simp
    simp only [↓reduceIte, pow_zero, one_mul, Nat.cast_one, mul_one, hγ, inv_one]
    have hrew : (2 : ℝ) ^ ((a : ℝ) / 4) * (2 : ℝ) ^ (-(a : ℝ) / 2) * Real.exp Q_bd =
        (2 : ℝ) ^ (-(a : ℝ) / 4) * Real.exp Q_bd := by rw [h2comb]
    rw [hrew]
    have h2le : (2 : ℝ) ^ (-(a : ℝ) / 4) ≤ 1 := by
      have hneg : -(a : ℝ) / 4 ≤ 0 := by linarith [Nat.cast_nonneg (α := ℝ) a]
      calc (2 : ℝ) ^ (-(a : ℝ) / 4) ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hneg
        _ = 1 := Real.rpow_zero 2
    have hprod_le : (2 : ℝ) ^ (-(a : ℝ) / 4) * Real.exp Q_bd ≤ Real.exp Q_bd := by
      nlinarith [Real.exp_pos Q_bd]
    calc ((2 : ℝ) ^ (-(a : ℝ) / 4) * Real.exp Q_bd) ^ ((1 : ℝ) / 3)
        ≤ (Real.exp Q_bd) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) hprod_le (by norm_num)
      _ = Real.exp (Q_bd / 3) := by rw [← Real.exp_mul]; congr 1; ring
      _ ≤ Real.exp (Q_bd / 3) * Real.exp ((2 : ℝ) / 3 * Real.sqrt (24 * (P_card : ℝ) * Q_bd)) := by
          have h1 : 1 ≤ Real.exp ((2 : ℝ) / 3 * Real.sqrt (24 * (P_card : ℝ) * Q_bd)) :=
            Real.one_le_exp (by positivity)
          nlinarith [Real.exp_pos (Q_bd / 3)]
  · simp only [hs, ↓reduceIte, Nat.cast_mul]
    have hs1 : 1 ≤ s := by omega
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    have hQ_pos : 0 < Q_bd := by linarith
    have hγ_bound : (γ ^ s)⁻¹ * Real.exp (γ * Q_bd) ≤
        Real.exp Q_bd * (Real.exp 1 * Q_bd / (s : ℝ)) ^ s := by
      by_cases hcase : (s : ℝ) ≤ Q_bd
      · have hγ1 : γ = 1 := max_eq_left ((div_le_one hQ_pos).mpr hcase)
        rw [hγ1, one_pow, inv_one, one_mul, one_mul]
        have hbase_ge1 : 1 ≤ Real.exp 1 * Q_bd / (s : ℝ) := by
          rw [one_le_div hs_pos]
          have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          nlinarith
        nlinarith [one_le_pow₀ (n := s) hbase_ge1, Real.exp_pos Q_bd]
      · push Not at hcase
        have hγeq : γ = (s : ℝ) / Q_bd := max_eq_right ((one_le_div hQ_pos).mpr (le_of_lt hcase))
        rw [hγeq, div_mul_cancel₀ _ (ne_of_gt hQ_pos), div_pow, inv_div]
        have hexp_s : Real.exp (s : ℝ) = (Real.exp 1) ^ s := by rw [← Real.exp_nat_mul, mul_one]
        rw [hexp_s, ← mul_div_right_comm, ← mul_pow, mul_comm Q_bd (Real.exp 1), ← div_pow]
        have heQ : 1 ≤ Real.exp Q_bd := Real.one_le_exp (by linarith)
        nlinarith [pow_nonneg (show 0 ≤ Real.exp 1 * Q_bd / (s : ℝ) by positivity) s]
    have hch1 := binom_le_exp_pow P_card s hs1
    have hch2 : (Nat.choose (a - s) s : ℝ) ≤ (Real.exp 1 * ((a : ℝ) / (s : ℝ))) ^ s := by
      refine le_trans (binom_le_exp_pow (a - s) s hs1) ?_
      refine pow_le_pow_left₀ (by positivity) ?_ s
      have has : ((a - s : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast Nat.sub_le a s
      rw [mul_div_assoc]
      gcongr
    have h2pow_s : (2 : ℝ) ^ (-(a : ℝ) / 4) = ((2 : ℝ) ^ (-((a : ℝ) / (s : ℝ)) / 4)) ^ s := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-((a : ℝ) / (s : ℝ)) / 4)) s,
        ← Real.rpow_mul (by norm_num)]
      congr 1; field_simp [ne_of_gt hs_pos]
    have hopt := exp_mul_x_mul_two_neg_quarter_le_eight (x := (a : ℝ) / (s : ℝ)) (by positivity)
    have hinside :
        (3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) * ((Nat.choose P_card s : ℝ) * (Nat.choose (a - s) s : ℝ)) *
          (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ ^ s)⁻¹ * Real.exp (γ * Q_bd) ≤
        Real.exp Q_bd * (Real.exp 1 * Real.sqrt (24 * (P_card : ℝ) * Q_bd) / (s : ℝ)) ^ (2 * s) := by
      have hrearr :
          (3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) * ((Nat.choose P_card s : ℝ) * (Nat.choose (a - s) s : ℝ)) *
            (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ ^ s)⁻¹ * Real.exp (γ * Q_bd) =
          (3 : ℝ) ^ s * (2 : ℝ) ^ (-(a : ℝ) / 4) * ((Nat.choose P_card s : ℝ) * (Nat.choose (a - s) s : ℝ)) *
            ((γ ^ s)⁻¹ * Real.exp (γ * Q_bd)) := by
        calc _ = (3 : ℝ) ^ s * ((2 : ℝ) ^ ((a : ℝ) / 4) * (2 : ℝ) ^ (-(a : ℝ) / 2)) *
              ((Nat.choose P_card s : ℝ) * (Nat.choose (a - s) s : ℝ)) * ((γ ^ s)⁻¹ * Real.exp (γ * Q_bd)) := by ring
          _ = _ := by rw [h2comb]
      rw [hrearr, h2pow_s]
      have h1 :
          (3 : ℝ) ^ s * ((2 : ℝ) ^ (-((a : ℝ) / (s : ℝ)) / 4)) ^ s *
            ((Nat.choose P_card s : ℝ) * (Nat.choose (a - s) s : ℝ)) * ((γ ^ s)⁻¹ * Real.exp (γ * Q_bd)) ≤
          (3 : ℝ) ^ s * ((2 : ℝ) ^ (-((a : ℝ) / (s : ℝ)) / 4)) ^ s *
            ((Real.exp 1 * (P_card : ℝ) / (s : ℝ)) ^ s * (Real.exp 1 * ((a : ℝ) / (s : ℝ))) ^ s) *
            (Real.exp Q_bd * (Real.exp 1 * Q_bd / (s : ℝ)) ^ s) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (mul_le_mul hch1 hch2 (Nat.cast_nonneg _) (by positivity)) (by positivity))
          hγ_bound (by positivity) (by positivity)
      refine le_trans h1 ?_
      have h2eq :
          (3 : ℝ) ^ s * ((2 : ℝ) ^ (-((a : ℝ) / (s : ℝ)) / 4)) ^ s *
            ((Real.exp 1 * (P_card : ℝ) / (s : ℝ)) ^ s * (Real.exp 1 * ((a : ℝ) / (s : ℝ))) ^ s) *
            (Real.exp Q_bd * (Real.exp 1 * Q_bd / (s : ℝ)) ^ s) =
          Real.exp Q_bd *
            ((3 * (Real.exp 1 * ((a : ℝ) / (s : ℝ)) * (2 : ℝ) ^ (-((a : ℝ) / (s : ℝ)) / 4))) *
              ((Real.exp 1 * (P_card : ℝ) / (s : ℝ)) * (Real.exp 1 * Q_bd / (s : ℝ)))) ^ s := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]; ring
      rw [h2eq]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
      rw [pow_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ s
      have hsq : Real.sqrt (24 * (P_card : ℝ) * Q_bd) ^ 2 = 24 * (P_card : ℝ) * Q_bd :=
        Real.sq_sqrt (by positivity)
      have hrhs : (Real.exp 1 * Real.sqrt (24 * (P_card : ℝ) * Q_bd) / (s : ℝ)) ^ 2 =
          24 * ((Real.exp 1 * (P_card : ℝ) / (s : ℝ)) * (Real.exp 1 * Q_bd / (s : ℝ))) := by
        rw [div_pow, mul_pow, hsq]; ring
      rw [hrhs]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    calc ((3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) * ((Nat.choose P_card s : ℝ) * (Nat.choose (a - s) s : ℝ)) *
            (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ ^ s)⁻¹ * Real.exp (γ * Q_bd)) ^ ((1 : ℝ) / 3)
        ≤ (Real.exp Q_bd * (Real.exp 1 * Real.sqrt (24 * (P_card : ℝ) * Q_bd) / (s : ℝ)) ^ (2 * s)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hinside (by norm_num)
      _ = Real.exp (Q_bd / 3) *
            ((Real.exp 1 * Real.sqrt (24 * (P_card : ℝ) * Q_bd) / (s : ℝ)) ^ (2 * s)) ^ ((1 : ℝ) / 3) := by
          rw [Real.mul_rpow (le_of_lt (Real.exp_pos _)) (by positivity), ← Real.exp_mul,
            show Q_bd * ((1 : ℝ) / 3) = Q_bd / 3 by ring]
      _ ≤ Real.exp (Q_bd / 3) * Real.exp ((2 : ℝ) / 3 * Real.sqrt (24 * (P_card : ℝ) * Q_bd)) :=
          mul_le_mul_of_nonneg_left (exp_mul_div_pow_two_thirds_le_exp (by positivity) s hs1)
            (le_of_lt (Real.exp_pos _))

/-- Absorbed large-prime bucket factor bound (`F'_m`): with `lam k = max 1 (k / 8)`,
`(2^k * choose R k * (lam^k)⁻¹ * exp (8 * (lam - 1)))^(1/3) ≤ exp (8/3 * √R)`. -/
private lemma factor_Fm_le (R k : ℕ) :
    let lam : ℝ := max 1 ((k : ℝ) / 8)
    ((2 : ℝ) ^ k * (Nat.choose R k : ℝ) * (lam ^ k)⁻¹ * Real.exp (8 * (lam - 1))) ^ ((1 : ℝ) / 3) ≤
      Real.exp ((8 : ℝ) / 3 * Real.sqrt (R : ℝ)) := by
  intro lam
  by_cases hk : k = 0
  · subst hk
    have hlam : lam = 1 := by dsimp [lam]; simp
    rw [hlam, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, inv_one,
      mul_one, sub_self, mul_zero, Real.exp_zero, mul_one, Real.one_rpow]
    exact Real.one_le_exp (by positivity)
  · have hk1 : 1 ≤ k := by omega
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hlam_bound : (lam ^ k)⁻¹ * Real.exp (8 * (lam - 1)) ≤ (8 * Real.exp 1 / (k : ℝ)) ^ k := by
      by_cases hcase : (k : ℝ) ≤ 8
      · have hlam1 : lam = 1 := max_eq_left (by linarith)
        rw [hlam1, one_pow, inv_one, sub_self, mul_zero, Real.exp_zero, mul_one]
        have hbase_ge1 : 1 ≤ 8 * Real.exp 1 / (k : ℝ) := by
          rw [one_le_div hk_pos]
          have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          nlinarith
        exact one_le_pow₀ hbase_ge1
      · push Not at hcase
        have hlam_eq : lam = (k : ℝ) / 8 := max_eq_right (by linarith)
        rw [hlam_eq, div_pow, inv_div]
        have hexp_le : Real.exp (8 * ((k : ℝ) / 8 - 1)) ≤ (Real.exp 1) ^ k := by
          rw [← Real.exp_nat_mul, mul_one]
          exact Real.exp_le_exp.mpr (by linarith)
        calc (8 : ℝ) ^ k / (k : ℝ) ^ k * Real.exp (8 * ((k : ℝ) / 8 - 1))
            ≤ (8 : ℝ) ^ k / (k : ℝ) ^ k * (Real.exp 1) ^ k :=
              mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ = (8 * Real.exp 1 / (k : ℝ)) ^ k := by rw [div_pow, mul_pow]; ring
    have hch := binom_le_exp_pow R k hk1
    have hinside : (2 : ℝ) ^ k * (Nat.choose R k : ℝ) * (lam ^ k)⁻¹ * Real.exp (8 * (lam - 1)) ≤
        (Real.exp 1 * (4 * Real.sqrt (R : ℝ)) / (k : ℝ)) ^ (2 * k) := by
      have h1 : (2 : ℝ) ^ k * (Nat.choose R k : ℝ) * ((lam ^ k)⁻¹ * Real.exp (8 * (lam - 1))) ≤
          (2 : ℝ) ^ k * (Real.exp 1 * (R : ℝ) / (k : ℝ)) ^ k * (8 * Real.exp 1 / (k : ℝ)) ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_left hch (by positivity)) hlam_bound (by positivity) (by positivity)
      have hsq : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt (Nat.cast_nonneg R)
      have h2eq : (2 : ℝ) ^ k * (Real.exp 1 * (R : ℝ) / (k : ℝ)) ^ k * (8 * Real.exp 1 / (k : ℝ)) ^ k =
          (Real.exp 1 * (4 * Real.sqrt (R : ℝ)) / (k : ℝ)) ^ (2 * k) := by
        rw [pow_mul, ← mul_pow, ← mul_pow]
        congr 1
        rw [div_pow, mul_pow, mul_pow, hsq]; ring
      linarith [h1, h2eq, show (2 : ℝ) ^ k * (Nat.choose R k : ℝ) * (lam ^ k)⁻¹ * Real.exp (8 * (lam - 1)) =
        (2 : ℝ) ^ k * (Nat.choose R k : ℝ) * ((lam ^ k)⁻¹ * Real.exp (8 * (lam - 1))) by ring]
    calc ((2 : ℝ) ^ k * (Nat.choose R k : ℝ) * (lam ^ k)⁻¹ * Real.exp (8 * (lam - 1))) ^ ((1 : ℝ) / 3)
        ≤ ((Real.exp 1 * (4 * Real.sqrt (R : ℝ)) / (k : ℝ)) ^ (2 * k)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hinside (by norm_num)
      _ ≤ Real.exp ((2 : ℝ) / 3 * (4 * Real.sqrt (R : ℝ))) :=
          exp_mul_div_pow_two_thirds_le_exp (by positivity) k hk1
      _ = Real.exp ((8 : ℝ) / 3 * Real.sqrt (R : ℝ)) := by congr 1; ring

/-! ### Section 6b: Regime 1 + Regime 2 Assembly (Large `n` World-Record `1/2` Existence) -/

/-- Cardinality of dependent `Fin`-product as a `ℝ`-product over `I`. -/
private lemma card_pi_fin_real (I : Finset ℕ) (f : ℕ → ℕ) :
    ((Finset.univ : Finset (∀ m : I, Fin (f m.1 + 1))).card : ℝ) =
      ∏ m ∈ I, ((f m + 1 : ℕ) : ℝ) := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin, Nat.cast_prod]
  exact Finset.prod_coe_sort I (fun m => ((f m + 1 : ℕ) : ℝ))

/-- Fast standalone algebraic factorization for a single absorbed Regime 2 slice term
(keeps `M_idx`, `R`, `U_bd`, etc. as opaque parameters so Lean never unfolds `let` bindings). -/
private lemma regime2_term_factor_le
    (N_val ℓ_val M_max_val U_bd γ_u γ_q : ℝ) (hN : 0 ≤ N_val) (hℓ_pos : 0 < ℓ_val)
    (hγu : 1 ≤ γ_u) (hγq : 1 ≤ γ_q)
    (P_card a s k₀ : ℕ) (M_idx : Finset ℕ) (R : ℕ → ℕ)
    (kv : ∀ m : M_idx, Fin (R m.1 + 1)) :
    let extK : ℕ → ℕ := fun m => if h : m ∈ M_idx then (kv ⟨m, h⟩).1 else 0
    let lam : ℕ → ℝ := fun m => max 1 ((extK m : ℝ) / 8)
    let K₁_val : ℕ :=
      4 * (3 ^ s * 2 ^ ((a + 3) / 4) * 2 ^ k₀ * ∏ m ∈ M_idx, 2 ^ (extK m))
    let κ_val : ℕ :=
      Nat.choose P_card k₀ *
      (if s = 0 then 1 else Nat.choose P_card s * Nat.choose (a - s) s) *
      ∏ m ∈ M_idx, Nat.choose (R m) (extK m)
    let M_val : ℝ :=
      N_val * (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ_q ^ s)⁻¹ * (γ_u ^ k₀)⁻¹ *
      (∏ m ∈ M_idx, (lam m ^ (extK m))⁻¹) *
      Real.exp (γ_u * U_bd + γ_q * (4 * U_bd)) *
      Real.exp (10 + 8 * M_max_val) *
      ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1))
    ((K₁_val : ℝ) * (κ_val : ℝ) * M_val) ^ ((1 : ℝ) / 3) / ℓ_val ≤
      (2 * (N_val ^ ((1 : ℝ) / 3) / ℓ_val) * Real.exp ((10 + 8 * M_max_val) / 3)) *
      (((3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) *
        ((if s = 0 then 1 else Nat.choose P_card s * Nat.choose (a - s) s : ℕ) : ℝ) *
        (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ_q ^ s)⁻¹ * Real.exp (γ_q * (4 * U_bd))) ^ ((1 : ℝ) / 3)) *
      (((2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * (γ_u ^ k₀)⁻¹ * Real.exp (γ_u * U_bd)) ^ ((1 : ℝ) / 3)) *
      ∏ m : M_idx,
        (((2 : ℝ) ^ (kv m).1 * (Nat.choose (R m.1) (kv m).1 : ℝ) *
          ((max 1 (((kv m).1 : ℝ) / 8)) ^ (kv m).1)⁻¹ *
          Real.exp (8 * (max 1 (((kv m).1 : ℝ) / 8) - 1))) ^ ((1 : ℝ) / 3)) := by
  intro extK lam K₁_val κ_val M_val
  have hlam_ge1 : ∀ m, 1 ≤ lam m := fun _ => le_max_left 1 _
  have hM_nn : 0 ≤ M_val := by
    dsimp only [M_val]
    have h1 : 0 ≤ ∏ m ∈ M_idx, (lam m ^ extK m)⁻¹ :=
      Finset.prod_nonneg fun m _ => inv_nonneg.mpr (pow_nonneg (by linarith [hlam_ge1 m]) _)
    have h2 : 0 ≤ ∏ m ∈ M_idx, Real.exp (8 * (lam m - 1)) :=
      Finset.prod_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
    positivity
  have h2a_le : ((2 ^ ((a + 3) / 4) : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ ((a : ℝ) / 4) := by
    have hnat : 4 * ((a + 3) / 4) ≤ a + 4 := by omega
    have hreal : (((a + 3) / 4 : ℕ) : ℝ) ≤ (a : ℝ) / 4 + 1 := by
      have : (4 : ℝ) * (((a + 3) / 4 : ℕ) : ℝ) ≤ (a : ℝ) + 4 := by exact_mod_cast hnat
      linarith
    calc ((2 ^ ((a + 3) / 4) : ℕ) : ℝ)
        = (2 : ℝ) ^ (((a + 3) / 4 : ℕ) : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((a : ℝ) / 4 + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hreal
      _ = 2 * (2 : ℝ) ^ ((a : ℝ) / 4) := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]; ring
  have hK₁_le : (K₁_val : ℝ) ≤
      8 * ((3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m)) := by
    dsimp only [K₁_val]
    push_cast
    have hnn : 0 ≤ (3 : ℝ) ^ s * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m) := by positivity
    calc 4 * ((3 : ℝ) ^ s * ((2 : ℝ) ^ ((a + 3) / 4)) * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m))
        = 4 * ((2 ^ ((a + 3) / 4) : ℕ) : ℝ) * ((3 : ℝ) ^ s * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m)) := by
          push_cast; ring
      _ ≤ 4 * (2 * (2 : ℝ) ^ ((a : ℝ) / 4)) * ((3 : ℝ) ^ s * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2a_le (by norm_num)) hnn
      _ = 8 * ((3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m)) := by ring
  let Q_part : ℝ :=
    (3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) *
    ((if s = 0 then 1 else Nat.choose P_card s * Nat.choose (a - s) s : ℕ) : ℝ) *
    (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ_q ^ s)⁻¹ * Real.exp (γ_q * (4 * U_bd))
  let U_part : ℝ :=
    (2 : ℝ) ^ k₀ * (Nat.choose P_card k₀ : ℝ) * (γ_u ^ k₀)⁻¹ * Real.exp (γ_u * U_bd)
  let M_part : ℕ → ℝ := fun m =>
    (2 : ℝ) ^ (extK m) * (Nat.choose (R m) (extK m) : ℝ) *
    (lam m ^ (extK m))⁻¹ * Real.exp (8 * (lam m - 1))
  have hQ_nn : 0 ≤ Q_part := by dsimp [Q_part]; positivity
  have hU_nn : 0 ≤ U_part := by dsimp [U_part]; positivity
  have hMp_nn : ∀ m ∈ M_idx, 0 ≤ M_part m := fun m _ => by
    dsimp [M_part]
    have : 0 ≤ (lam m ^ extK m)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith [hlam_ge1 m]) _)
    positivity
  have hprod_le : (K₁_val : ℝ) * (κ_val : ℝ) * M_val ≤
      (8 * N_val * Real.exp (10 + 8 * M_max_val)) * Q_part * U_part * ∏ m ∈ M_idx, M_part m := by
    have hstep1 : (K₁_val : ℝ) * (κ_val : ℝ) * M_val ≤
        (8 * ((3 : ℝ) ^ s * (2 : ℝ) ^ ((a : ℝ) / 4) * (2 : ℝ) ^ k₀ * ∏ m ∈ M_idx, (2 : ℝ) ^ (extK m))) *
          (κ_val : ℝ) * M_val :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₁_le (Nat.cast_nonneg _)) hM_nn
    refine le_trans hstep1 (le_of_eq ?_)
    have hMprod_eq :
        (∏ m ∈ M_idx, (2 : ℝ) ^ (extK m)) *
        (∏ m ∈ M_idx, (Nat.choose (R m) (extK m) : ℝ)) *
        (∏ m ∈ M_idx, (lam m ^ (extK m))⁻¹) *
        (∏ m ∈ M_idx, Real.exp (8 * (lam m - 1))) =
        ∏ m ∈ M_idx, M_part m := by
      simp only [M_part, ← Finset.prod_mul_distrib]
    dsimp only [κ_val, M_val, Q_part, U_part]
    push_cast
    rw [Real.exp_add, ← hMprod_eq]
    ring
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [this, ← Real.rpow_natCast (2 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
  have hexp_M : (Real.exp (10 + 8 * M_max_val)) ^ ((1 : ℝ) / 3) =
      Real.exp ((10 + 8 * M_max_val) / 3) := by
    rw [← Real.exp_mul]; congr 1; ring
  have hprod_rpow : (∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3) =
      ∏ m : M_idx,
        (((2 : ℝ) ^ (kv m).1 * (Nat.choose (R m.1) (kv m).1 : ℝ) *
          ((max 1 (((kv m).1 : ℝ) / 8)) ^ (kv m).1)⁻¹ *
          Real.exp (8 * (max 1 (((kv m).1 : ℝ) / 8) - 1))) ^ ((1 : ℝ) / 3)) := by
    rw [← Real.finsetProd_rpow M_idx _ hMp_nn, ← Finset.prod_coe_sort M_idx]
    refine Finset.prod_congr rfl fun m _ => ?_
    dsimp only [M_part, lam, extK]
    simp only [m.2, dite_true]
  have htop : ((K₁_val : ℝ) * (κ_val : ℝ) * M_val) ^ ((1 : ℝ) / 3) ≤
      (2 * N_val ^ ((1 : ℝ) / 3) * Real.exp ((10 + 8 * M_max_val) / 3)) *
      Q_part ^ ((1 : ℝ) / 3) * U_part ^ ((1 : ℝ) / 3) * (∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3) := by
    calc ((K₁_val : ℝ) * (κ_val : ℝ) * M_val) ^ ((1 : ℝ) / 3)
        ≤ ((8 * N_val * Real.exp (10 + 8 * M_max_val)) * Q_part * U_part * ∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hprod_le (by norm_num)
      _ = (8 * N_val * Real.exp (10 + 8 * M_max_val)) ^ ((1 : ℝ) / 3) *
            Q_part ^ ((1 : ℝ) / 3) * U_part ^ ((1 : ℝ) / 3) * (∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3) := by
          rw [Real.mul_rpow (by positivity) (Finset.prod_nonneg hMp_nn),
            Real.mul_rpow (by positivity) hU_nn,
            Real.mul_rpow (by positivity) hQ_nn]
      _ = (2 * N_val ^ ((1 : ℝ) / 3) * Real.exp ((10 + 8 * M_max_val) / 3)) *
            Q_part ^ ((1 : ℝ) / 3) * U_part ^ ((1 : ℝ) / 3) * (∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3) := by
          rw [Real.mul_rpow (by positivity) (le_of_lt (Real.exp_pos _)),
            Real.mul_rpow (by norm_num) hN, h8, hexp_M]
  calc ((K₁_val : ℝ) * (κ_val : ℝ) * M_val) ^ ((1 : ℝ) / 3) / ℓ_val
      ≤ ((2 * N_val ^ ((1 : ℝ) / 3) * Real.exp ((10 + 8 * M_max_val) / 3)) *
          Q_part ^ ((1 : ℝ) / 3) * U_part ^ ((1 : ℝ) / 3) * (∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3)) / ℓ_val :=
        div_le_div_of_nonneg_right htop (le_of_lt hℓ_pos)
    _ = (2 * (N_val ^ ((1 : ℝ) / 3) / ℓ_val) * Real.exp ((10 + 8 * M_max_val) / 3)) *
          Q_part ^ ((1 : ℝ) / 3) * U_part ^ ((1 : ℝ) / 3) * (∏ m ∈ M_idx, M_part m) ^ ((1 : ℝ) / 3) := by ring
    _ = _ := by rw [hprod_rpow]

/-- Auxiliary asymptotic inequalities for `n ≥ 16` with `200 ≤ log (log n)` (exponent `1/2`). -/
private lemma large_n_log_bounds (n : ℕ) (hn16 : 16 ≤ n)
    (hLL : 200 ≤ Real.log (Real.log (n : ℝ))) :
    let L := Real.log (n : ℝ)
    let LL := Real.log L
    let E_half := (L / LL) ^ ((1 : ℝ) / 2)
    0 < L ∧ LL ^ 5 ≤ L ∧ LL ^ 4 ≤ L ∧ 2 * LL ^ 2 ≤ Real.exp (LL / 2) ∧
    LL ^ 2 ≤ E_half ∧ 40000 ≤ E_half ∧ 600 * E_half + 2 ≤ (2 / 3 : ℝ) * L := by
  intro L LL E_half
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hexp_LL : Real.exp LL = L := Real.exp_log hL_pos
  -- LL^7 / 5040 ≤ exp LL = L and 5040 ≤ 200^2 ≤ LL^2 ⟹ LL^5 ≤ L
  have hL_ge_LL5 : LL ^ 5 ≤ L := by
    have hsum := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ LL) 8
    have h7 : LL ^ 7 / ((7 : ℕ).factorial : ℝ) ≤
        ∑ i ∈ Finset.range 8, LL ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => LL ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
    have hfac7 : ((7 : ℕ).factorial : ℝ) = 5040 := by norm_num
    rw [hfac7] at h7
    have hle : LL ^ 7 / 5040 ≤ L := by linarith
    have hLL2 : (5040 : ℝ) ≤ LL ^ 2 := by nlinarith
    have hLL5_nn : 0 ≤ LL ^ 5 := pow_nonneg (by linarith) 5
    have h7eq : LL ^ 7 = LL ^ 5 * LL ^ 2 := by ring
    nlinarith
  have hL_ge_LL4 : LL ^ 4 ≤ L := by
    have h1 : LL ^ 4 ≤ LL ^ 5 := by
      have : LL ^ 4 * 1 ≤ LL ^ 4 * LL := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith [show LL ^ 4 * LL = LL ^ 5 by ring]
    linarith
  have hLL2_exp : 2 * LL ^ 2 ≤ Real.exp (LL / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ LL / 2) 4
    have h3 : (LL / 2) ^ 3 / ((3 : ℕ).factorial : ℝ) ≤
        ∑ i ∈ Finset.range 4, (LL / 2) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (LL / 2) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
    have hfac3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfac3] at h3
    have hle : (LL / 2) ^ 3 / 6 ≤ Real.exp (LL / 2) := le_trans h3 hsum
    nlinarith [sq_nonneg LL]
  -- LL^2 ≤ E_half ⟺ LL^4 ≤ L / LL ⟺ LL^5 ≤ L
  have hLL2_Ehalf : LL ^ 2 ≤ E_half := by
    have hpow2 : (LL ^ 2) ^ (2 : ℕ) ≤ E_half ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast E_half 2]
      dsimp only [E_half]
      rw [← Real.rpow_mul (by positivity)]
      norm_num
      rw [le_div_iff₀ (by linarith)]
      have h5 : (LL ^ 2) ^ 2 * LL = LL ^ 5 := by ring
      linarith
    by_contra hgt; push Not at hgt
    have : E_half ^ (2 : ℕ) < (LL ^ 2) ^ (2 : ℕ) :=
      pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
    linarith
  have hEhalf_ge : 40000 ≤ E_half := by nlinarith
  -- 600 * E_half + 2 ≤ (2/3) * L (follows from 601 * E_half ≤ (2/3) * L)
  have h600 : 600 * E_half + 2 ≤ (2 / 3 : ℝ) * L := by
    have h601 : 601 * E_half ≤ (2 / 3 : ℝ) * L := by
      have hpow2 : (601 * E_half) ^ (2 : ℕ) ≤ ((2 / 3 : ℝ) * L) ^ (2 : ℕ) := by
        rw [mul_pow, ← Real.rpow_natCast E_half 2]
        dsimp only [E_half]
        rw [← Real.rpow_mul (by positivity)]
        norm_num
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        have hL_ge : (200 : ℝ) ^ 5 ≤ L := le_trans (pow_le_pow_left₀ (by norm_num) hLL 5) hL_ge_LL5
        have hL_LL : (200 : ℝ) ^ 6 ≤ L * LL := by
          calc (200 : ℝ) ^ 6 = (200 : ℝ) ^ 5 * 200 := by ring
            _ ≤ L * LL := mul_le_mul hL_ge hLL (by norm_num) (le_of_lt hL_pos)
        have hnum : (361201 : ℝ) ≤ (4 / 9 : ℝ) * (L * LL) := by linarith
        calc (361201 : ℝ) * L ≤ ((4 / 9 : ℝ) * (L * LL)) * L :=
              mul_le_mul_of_nonneg_right hnum (le_of_lt hL_pos)
          _ = ((2 / 3 : ℝ) * L) ^ 2 * LL := by ring
      by_contra hgt; push Not at hgt
      have : ((2 / 3 : ℝ) * L) ^ (2 : ℕ) < (601 * E_half) ^ (2 : ℕ) :=
        pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
      linarith
    linarith
  exact ⟨hL_pos, hL_ge_LL5, hL_ge_LL4, hLL2_exp, hLL2_Ehalf, hEhalf_ge, h600⟩

/-- **Core World-Record `1/2` Existence Theorem (Large `n`, Closed-Right Interval `(m, m + H]`):**
For any `n ≥ 16` with `200 ≤ log (log n)` and any `H` satisfying
`n^(4/3) * exp (600 * (log n / log (log n))^(1/2)) ≤ H ≤ n^2`,
and every `m : ℕ`, the interval `(m, m + H]` contains `n` distinct multiples `a 1, ..., a n`
with `k ∣ a k` for all `1 ≤ k ≤ n`. -/
private lemma exists_distinct_multiples_world_record_large
    (n m H : ℕ) (hn16 : 16 ≤ n)
    (hLL : 200 ≤ Real.log (Real.log (n : ℝ)))
    (hH_lo : (n : ℝ) ^ ((4 : ℝ) / 3) *
      Real.exp (600 * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2)) ≤ (H : ℝ))
    (hH_hi : (H : ℝ) ≤ (n : ℝ) ^ (2 : ℕ)) :
    ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + H ∧ k ∣ a k) := by
  classical
  let L : ℝ := Real.log (n : ℝ)
  let LL : ℝ := Real.log L
  let E_half : ℝ := (L / LL) ^ ((1 : ℝ) / 2)
  obtain ⟨hL_pos, _, hL_ge_LL4, hLL2_exp, hLL2_Ehalf, hEhalf_ge, _⟩ :=
    large_n_log_bounds n hn16 hLL
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLL_pos : 0 < LL := by linarith
  have hexp_LL : Real.exp LL = L := Real.exp_log hL_pos
  have hexp_L : Real.exp L = (n : ℝ) := Real.exp_log hn_pos
  have hH_pos_r : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le (by positivity) hH_lo
  have hH_ge_100n : 100 * n ≤ H := by
    have h43 : (n : ℝ) ^ ((4 : ℝ) / 3) = (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      have : ((4 : ℝ) / 3) = 1 + ((1 : ℝ) / 3) := by norm_num
      rw [this, Real.rpow_add hn_pos, Real.rpow_one]
    have hn13 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    have hexp100 : (100 : ℝ) ≤ Real.exp (600 * E_half) := by
      linarith [Real.add_one_le_exp (600 * E_half)]
    have hreal : (100 * n : ℝ) ≤ (H : ℝ) := by
      calc (100 * n : ℝ) = (n : ℝ) * 1 * 100 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 3) * Real.exp (600 * E_half) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hn13 (le_of_lt hn_pos)) hexp100 (by norm_num) (by positivity)
        _ = (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (600 * E_half) := by rw [← h43]
        _ ≤ (H : ℝ) := hH_lo
    exact_mod_cast hreal
  -- Setup parameters for Regime 1 & Regime 2
  let J : ℕ := Nat.log 2 n + 1
  let j₀ : ℕ := Nat.ceil (12 * L / LL)
  let N : ℕ → ℕ := fun j => n / 2 ^ j
  let Y : ℕ := Nat.floor (16 * L / LL)
  let m_start : ℕ := Nat.log 2 (Nat.log 2 Y)
  let M_max : ℕ := Nat.log 2 (Nat.log 2 n)
  let M_idx : Finset ℕ := Finset.Icc m_start M_max
  let R : ℕ → ℕ := fun m => Nat.log 2 H / 2 ^ m
  let U_bd : ℝ := max 1 (∑ p ∈ primesSmall Y, (1 : ℝ) / (p : ℝ))
  -- Key parameter inequalities
  have hL_ge_1e8 : (10 : ℝ) ^ (8 : ℕ) ≤ L := by
    have : (200 : ℝ) ^ 4 ≤ LL ^ 4 := pow_le_pow_left₀ (by norm_num) hLL 4
    linarith
  have hY_ge_lo : 16 * L / LL - 1 ≤ (Y : ℝ) := sub_le_iff_le_add.mpr (le_of_lt (Nat.lt_floor_add_one _))
  have hY_le_hi : (Y : ℝ) ≤ 16 * L / LL := Nat.floor_le (by positivity)
  have hY2 : 2 ≤ Y := by
    have hdiv : (10 : ℝ) ≤ 16 * L / LL := by
      rw [le_div_iff₀ hLL_pos]
      have : LL ^ 2 ≤ L := by nlinarith [pow_le_pow_left₀ (by norm_num) hLL 2]
      nlinarith
    have : (2 : ℝ) ≤ (Y : ℝ) := by linarith
    exact_mod_cast this
  have hYn : Y ≤ n := by
    have hL_le_n : L ≤ (n : ℝ) := by linarith [Real.log_le_sub_one_of_pos hn_pos]
    have hdiv_le : 16 * L / LL ≤ L := by rw [div_le_iff₀ hLL_pos]; nlinarith
    have : (Y : ℝ) ≤ (n : ℝ) := le_trans hY_le_hi (le_trans hdiv_le hL_le_n)
    exact_mod_cast this
  have hY_ge_exp : Real.exp (LL / 2) ≤ (Y : ℝ) := by
    have h1 : Real.exp (LL / 2) * (2 * LL ^ 2) ≤ L := by
      calc Real.exp (LL / 2) * (2 * LL ^ 2)
          ≤ Real.exp (LL / 2) * Real.exp (LL / 2) :=
            mul_le_mul_of_nonneg_left hLL2_exp (le_of_lt (Real.exp_pos _))
        _ = Real.exp LL := by rw [← Real.exp_add]; congr 1; ring
        _ = L := hexp_LL
    have h2 : Real.exp (LL / 2) ≤ L / LL := by
      rw [le_div_iff₀ hLL_pos]
      nlinarith [Real.exp_pos (LL / 2)]
    have h3 : (1 : ℝ) ≤ L / LL := le_trans (Real.one_le_exp (by linarith)) h2
    have h16 : 16 * L / LL = 16 * (L / LL) := by ring
    linarith only [hY_ge_lo, h2, h3, h16]
  have hlogY_ge : LL / 2 ≤ Real.log (Y : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hY_ge_exp
    rwa [Real.log_exp] at h
  have hnatlogY_ge : LL / 3 ≤ (Nat.log 2 Y : ℝ) := by
    have hpow : (Y : ℝ) < (2 : ℝ) ^ (Nat.log 2 Y + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) Y
    have hlg := Real.log_lt_log (by exact_mod_cast (by omega : 0 < Y)) hpow
    rw [Real.log_pow] at hlg
    have hlog2_le : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 : LL / 2 < ((Nat.log 2 Y + 1 : ℕ) : ℝ) * 1 := by
      have : ((Nat.log 2 Y + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((Nat.log 2 Y + 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2_le (Nat.cast_nonneg _)
      linarith
    push_cast at h1; linarith
  have hms : 2 ^ (2 ^ m_start) ≤ Y := by
    have h1 : 2 ^ m_start ≤ Nat.log 2 Y := Nat.pow_log_le_self 2 (by
      have : (1 : ℝ) ≤ (Nat.log 2 Y : ℝ) := by linarith
      have : 1 ≤ Nat.log 2 Y := by exact_mod_cast this
      omega)
    exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) (Nat.pow_log_le_self 2 (by omega))
  have hMm : n ≤ 2 ^ (2 ^ (M_max + 1)) := by
    have h1 : Nat.log 2 n + 1 ≤ 2 ^ (M_max + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (Nat.log 2 n)
    have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    exact le_of_lt (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) h1))
  have h2ms_ge : LL / 6 ≤ ((2 ^ m_start : ℕ) : ℝ) := by
    have hlt : (Nat.log 2 Y : ℝ) < ((2 ^ (m_start + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) (Nat.log 2 Y)
    have h2 : ((2 ^ (m_start + 1) : ℕ) : ℝ) = 2 * ((2 ^ m_start : ℕ) : ℝ) := by
      rw [pow_succ]; push_cast; ring
    linarith
  have hnatlogH_le : (Nat.log 2 H : ℝ) ≤ 4 * L := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 H) ≤ (n : ℝ) ^ (2 : ℕ) :=
      le_trans (by exact_mod_cast Nat.pow_log_le_self 2 (by omega)) hH_hi
    have hlg := Real.log_le_log (pow_pos (by norm_num) _) hpow
    rw [Real.log_pow, Real.log_pow] at hlg
    have := half_le_log_two
    push_cast at hlg
    nlinarith
  have hnatlogn_le : (Nat.log 2 n : ℝ) ≤ 2 * L := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlg := Real.log_le_log (pow_pos (by norm_num) _) hpow
    rw [Real.log_pow] at hlg
    have := half_le_log_two
    nlinarith
  have hMmax_le : (M_max : ℝ) ≤ 3 * LL := by
    have hpow : (2 : ℝ) ^ M_max ≤ 2 * L :=
      le_trans (by exact_mod_cast Nat.pow_log_le_self 2 (by
        have : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
        omega)) hnatlogn_le
    have hlg := Real.log_le_log (pow_pos (by norm_num) _) hpow
    rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hL_pos)] at hlg
    have hlog2_le : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := half_le_log_two
    nlinarith
  have hUbd_le : U_bd ≤ 20 * LL := by
    have h1 := sum_inv_primes_le Y
    have hms_le_Mm : m_start ≤ M_max := Nat.log_mono_right (Nat.log_mono_right hYn)
    have h2 : (m_start : ℝ) ≤ (M_max : ℝ) := by exact_mod_cast hms_le_Mm
    dsimp only [U_bd, primesSmall]
    exact max_le (by linarith only [hLL]) (by linarith only [h1, h2, hMmax_le, hLL])
  have hPsm_card_le : ((primesSmall Y).card : ℝ) ≤ 192 * L / LL ^ 2 := by
    have hpi := primeCounting_le_six_div_log Y hY2
    calc ((primesSmall Y).card : ℝ) ≤ 6 * (Y : ℝ) / Real.log (Y : ℝ) := hpi
      _ ≤ 6 * (16 * L / LL) / (LL / 2) :=
          div_le_div₀ (by positivity) (by linarith) (by linarith) hlogY_ge
      _ = 192 * L / LL ^ 2 := by field_simp [ne_of_gt hLL_pos]; ring
  -- Bound R m ≤ 24 * (L / LL) * (1/2)^(m - m_start) for m ∈ M_idx
  have hRm_le : ∀ m ∈ M_idx, (R m : ℝ) ≤ 24 * (L / LL) * ((1 : ℝ) / 2) ^ (m - m_start) := by
    intro m hm
    have hm_ge : m_start ≤ m := (Finset.mem_Icc.mp hm).1
    have h2m_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
    have hdiv : (R m : ℝ) ≤ (Nat.log 2 H : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
      rw [le_div_iff₀ h2m_pos]
      exact_mod_cast Nat.div_mul_le_self (Nat.log 2 H) (2 ^ m)
    have h2m_eq : ((2 ^ m : ℕ) : ℝ) = ((2 ^ m_start : ℕ) : ℝ) * (2 : ℝ) ^ (m - m_start) := by
      have : 2 ^ m = 2 ^ m_start * 2 ^ (m - m_start) := by rw [← pow_add, Nat.add_sub_of_le hm_ge]
      rw [this]; push_cast; rfl
    have hden_ge : (LL / 6) * (2 : ℝ) ^ (m - m_start) ≤ ((2 ^ m : ℕ) : ℝ) := by
      rw [h2m_eq]; exact mul_le_mul_of_nonneg_right h2ms_ge (by positivity)
    calc (R m : ℝ) ≤ (Nat.log 2 H : ℝ) / ((2 ^ m : ℕ) : ℝ) := hdiv
      _ ≤ (4 * L) / ((LL / 6) * (2 : ℝ) ^ (m - m_start)) :=
          div_le_div₀ (by positivity) hnatlogH_le (by positivity) hden_ge
      _ = 24 * (L / LL) * ((1 : ℝ) / 2) ^ (m - m_start) := by
          rw [div_pow, one_pow]; field_simp [ne_of_gt hLL_pos]; ring
  -- Regime 1 divisor bound: for all 1 ≤ t ≤ H, t.divisors.card ≤ exp (6 * L / LL)
  have hR1_div : ∀ t : ℕ, 1 ≤ t → t ≤ H → (t.divisors.card : ℝ) ≤ Real.exp (6 * L / LL) := by
    intro t ht1 htH
    let Z : ℕ := Nat.floor (L / LL ^ 2)
    have hZ_ge_lo : L / LL ^ 2 - 1 ≤ (Z : ℝ) := sub_le_iff_le_add.mpr (le_of_lt (Nat.lt_floor_add_one _))
    have hZ_le_hi : (Z : ℝ) ≤ L / LL ^ 2 := Nat.floor_le (by positivity)
    have hZ_ge_exp : Real.exp (LL / 2) ≤ (Z : ℝ) := by
      have h1 : Real.exp (LL / 2) * (2 * LL ^ 2) ≤ L := by
        calc Real.exp (LL / 2) * (2 * LL ^ 2)
            ≤ Real.exp (LL / 2) * Real.exp (LL / 2) :=
              mul_le_mul_of_nonneg_left hLL2_exp (le_of_lt (Real.exp_pos _))
          _ = Real.exp LL := by rw [← Real.exp_add]; congr 1; ring
          _ = L := hexp_LL
      have h2 : 2 * Real.exp (LL / 2) ≤ L / LL ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h3 : (1 : ℝ) ≤ Real.exp (LL / 2) := Real.one_le_exp (by linarith)
      linarith
    have hZ2 : 2 ≤ Z := by
      have : (2 : ℝ) ≤ Real.exp (LL / 2) := by linarith [Real.add_one_le_exp (LL / 2)]
      exact_mod_cast le_trans this hZ_ge_exp
    have hlogZ_ge : LL / 2 ≤ Real.log (Z : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) hZ_ge_exp
      rwa [Real.log_exp] at this
    have htB : t ≤ n ^ 2 := by
      have : (t : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := le_trans (by exact_mod_cast htH) hH_hi
      exact_mod_cast this
    have hps := card_divisors_le_prime_split t (n ^ 2) Z ht1 htB hZ2
    -- Factor 1: (Nat.log 2 (n^2) + 1) ^ Z ≤ exp (2 * L / LL)
    have hF1 : ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) ^ Z ≤ Real.exp (2 * L / LL) := by
      have hbase_le : ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) ≤ 5 * L := by
        have hpow : (2 : ℝ) ^ (Nat.log 2 (n ^ 2)) ≤ (n : ℝ) ^ (2 : ℕ) := by
          exact_mod_cast Nat.pow_log_le_self 2 (by positivity)
        have hlg := Real.log_le_log (pow_pos (by norm_num) _) hpow
        rw [Real.log_pow, Real.log_pow] at hlg
        have := half_le_log_two
        push_cast at hlg ⊢
        nlinarith
      have hbase_pos : (0 : ℝ) < ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) := by positivity
      have hlog5L : Real.log (5 * L) ≤ 2 * LL := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hL_pos)]
        have : Real.log 5 ≤ 5 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
        linarith
      have hlog_base : Real.log ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) ≤ 2 * LL :=
        le_trans (Real.log_le_log hbase_pos hbase_le) hlog5L
      have hZlog : (Z : ℝ) * Real.log ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) ≤ 2 * L / LL := by
        calc (Z : ℝ) * Real.log ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ)
            ≤ (L / LL ^ 2) * (2 * LL) :=
              mul_le_mul hZ_le_hi hlog_base (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Nat.log 2 (n ^ 2) + 1))) (by positivity)
          _ = 2 * L / LL := by field_simp [ne_of_gt hLL_pos]
      calc ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) ^ Z
          = Real.exp ((Z : ℝ) * Real.log ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase_pos, mul_comm]
        _ ≤ Real.exp (2 * L / LL) := Real.exp_le_exp.mpr hZlog
    -- Factor 2: 2 ^ (log (n^2) / log Z) ≤ exp (4 * L / LL)
    have hF2 : (2 : ℝ) ^ (Real.log ((n ^ 2 : ℕ) : ℝ) / Real.log (Z : ℝ)) ≤ Real.exp (4 * L / LL) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have hlog2_le : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hlog_n2 : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * L := by
        rw [Nat.cast_pow, Real.log_pow]; push_cast; rfl
      rw [hlog_n2]
      have hdiv_le : 2 * L / Real.log (Z : ℝ) ≤ 4 * L / LL := by
        calc 2 * L / Real.log (Z : ℝ) ≤ 2 * L / (LL / 2) :=
              div_le_div_of_nonneg_left (by positivity) (by linarith) hlogZ_ge
          _ = 4 * L / LL := by ring
      calc Real.log 2 * (2 * L / Real.log (Z : ℝ))
          ≤ 1 * (4 * L / LL) := mul_le_mul hlog2_le hdiv_le (by positivity) (by norm_num)
        _ = 4 * L / LL := one_mul _
    calc (t.divisors.card : ℝ)
        ≤ ((Nat.log 2 (n ^ 2) + 1 : ℕ) : ℝ) ^ Z *
            (2 : ℝ) ^ (Real.log ((n ^ 2 : ℕ) : ℝ) / Real.log (Z : ℝ)) := hps
      _ ≤ Real.exp (2 * L / LL) * Real.exp (4 * L / LL) :=
          mul_le_mul hF1 hF2 (by positivity) (by positivity)
      _ = Real.exp (6 * L / LL) := by rw [← Real.exp_add]; congr 1; ring
  -- Now apply Hall's Marriage Theorem on A = Finset.Icc 1 n
  suffices h : ∃ a : ℕ → ℕ,
      (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, a i = a j → i = j) ∧
      (∀ k ∈ Finset.Icc 1 n, m < a k ∧ a k ≤ m + H ∧ k ∣ a k) by
    obtain ⟨a, hinj, hprop⟩ := h
    exact ⟨a, fun i j hi1 hin hj1 hjn hEq =>
      hinj i (Finset.mem_Icc.mpr ⟨hi1, hin⟩) j (Finset.mem_Icc.mpr ⟨hj1, hjn⟩) hEq,
      fun k hk1 hkn => hprop k (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)⟩
  refine exists_distinct_multiples_of_hall (Finset.Icc 1 n) m H fun S hS => ?_
  let U := (Finset.Ioc m (m + H)).filter (fun t => ∃ k ∈ S, k ∣ t)
  have hU_diam : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → v - u ≤ H := by
    intro u hu v hv _
    have hu_Ioc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1
    have hv_Ioc := Finset.mem_Ioc.mp (Finset.mem_filter.mp hv).1
    omega
  -- Define Regime 1 & Regime 2 index type: Sum ℕ (ℕ × (ℕ × ℕ) × ℕ × (∀ m : M_idx, Fin (R m.1 + 1)))
  let K_type := ∀ m : M_idx, Fin (R m.1 + 1)
  let AS_set : Finset (ℕ × ℕ) :=
    ((Finset.range (Nat.log 2 n + 1)) ×ˢ (Finset.range ((primesSmall Y).card + 1))).filter
      fun p => p.2 = 0 ∨ 2 * p.2 ≤ p.1
  let K0_set : Finset ℕ := Finset.range ((primesSmall Y).card + 1)
  let K_set : Finset K_type := Finset.univ
  let J1_set : Finset ℕ := Finset.Ico j₀ J
  let J2_set : Finset ℕ := Finset.range (min j₀ J)
  let R2_idx : Finset (ℕ × (ℕ × ℕ) × ℕ × K_type) := J2_set ×ˢ (AS_set ×ˢ (K0_set ×ˢ K_set))
  let idx : Finset (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) :=
    J1_set.image Sum.inl ∪ R2_idx.image Sum.inr
  let extK : K_type → ℕ → ℕ := fun kv m => if h : m ∈ M_idx then (kv ⟨m, h⟩).1 else 0
  let dyadic : ℕ → Finset ℕ := fun j => S.filter (fun d => 2 ^ j * d ≤ n ∧ n < 2 ^ (j + 1) * d)
  let slice : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → Finset ℕ := fun α =>
    match α with
    | Sum.inl j => dyadic j
    | Sum.inr (j, (a, s), k₀, kv) =>
        (dyadic j).filter fun d =>
          Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
          ∀ m ∈ M_idx, bucketOmega Y n m d = extK kv m
  let X_dyad : ℕ → ℝ := fun j => (n : ℝ) / (2 : ℝ) ^ j
  let X_of : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → ℝ := fun α =>
    match α with
    | Sum.inl j => X_dyad j
    | Sum.inr (j, _) => X_dyad j
  let ℓ_dyad : ℕ → ℕ := fun j => H / (2 * max 1 (N j))
  let ℓ_of : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → ℕ := fun α =>
    match α with
    | Sum.inl j => ℓ_dyad j
    | Sum.inr (j, _) => ℓ_dyad j
  let κ_R1 : ℕ := max 1 (Nat.ceil (Real.exp (6 * L / LL)))
  let κ_of : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → ℕ := fun α =>
    match α with
    | Sum.inl _ => κ_R1
    | Sum.inr (_, (a, s), k₀, kv) =>
        Nat.choose (primesSmall Y).card k₀ *
        (if s = 0 then 1 else Nat.choose (primesSmall Y).card s * Nat.choose (a - s) s) *
        ∏ m ∈ M_idx, Nat.choose (R m) (extK kv m)
  let K₁_of : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → ℕ := fun α =>
    match α with
    | Sum.inl _ => 4 * κ_R1
    | Sum.inr (_, (a, s), k₀, kv) =>
        4 * (3 ^ s * 2 ^ ((a + 3) / 4) * 2 ^ k₀ * ∏ m ∈ M_idx, 2 ^ (extK kv m))
  let γ_u_of : ℕ → ℝ := fun k₀ => max 1 ((k₀ : ℝ) / U_bd)
  let γ_q_of : ℕ → ℝ := fun s => max 1 ((s : ℝ) / (4 * U_bd))
  let lam_of : K_type → ℕ → ℝ := fun kv m => max 1 ((extK kv m : ℝ) / 8)
  let M_of : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → ℝ := fun α =>
    match α with
    | Sum.inl j => (N j : ℝ)
    | Sum.inr (j, (a, s), k₀, kv) =>
        (N j : ℝ) * (2 : ℝ) ^ (-(a : ℝ) / 2) * (γ_q_of s ^ s)⁻¹ * (γ_u_of k₀ ^ k₀)⁻¹ *
        (∏ m ∈ M_idx, (lam_of kv m ^ (extK kv m))⁻¹) *
        Real.exp (γ_u_of k₀ * U_bd + γ_q_of s * (4 * U_bd)) *
        Real.exp (10 + 8 * (M_max : ℝ)) *
        ∏ m ∈ M_idx, Real.exp (8 * (lam_of kv m - 1))
  let a_start : (ℕ ⊕ (ℕ × (ℕ × ℕ) × ℕ × K_type)) → ℕ → ℕ := fun _ d => (m / d + 1) * d
  -- Verify hcover : S ⊆ idx.biUnion slice
  have hcover : S ⊆ idx.biUnion slice := by
    intro d hd
    have hd_Icc := Finset.mem_Icc.mp (hS hd)
    have hq_pos : 1 ≤ n / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by simpa using hd_Icc.2)
    let j := Nat.log 2 (n / d)
    have hj_le : 2 ^ j ≤ n / d := Nat.pow_log_le_self 2 (by omega)
    have hj_lt : n / d < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n / d)
    have hj_J : j < J := by
      have : j ≤ Nat.log 2 n := Nat.log_mono_right (Nat.div_le_self n d)
      omega
    have hd_dyad : d ∈ dyadic j := Finset.mem_filter.mpr
      ⟨hd, (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hj_le,
        (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp hj_lt⟩
    by_cases hj_big : j₀ ≤ j
    · refine Finset.mem_biUnion.mpr ⟨Sum.inl j, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_Ico.mpr ⟨hj_big, hj_J⟩)), hd_dyad⟩
    · -- Regime 2: construct (a, s), k₀, kv for d
      let a_d := Nat.log 2 (qSm Y d)
      let s_d := omegaQ Y d
      let k₀_d := omegaU Y d
      have hq_dvd : qSm Y d ∣ d := by
        conv_rhs => rw [eq_qSm_mul_uSm_mul_prod_bucketPart Y n m_start M_max d hY2 hYn hms hMm hd_Icc.1 hd_Icc.2]
        exact ⟨uSm Y d * ∏ m ∈ M_idx, bucketPart Y n m d, by ring⟩
      have hq_le_n : qSm Y d ≤ n := le_trans (Nat.le_of_dvd (by omega) hq_dvd) hd_Icc.2
      have ha_lt : a_d < Nat.log 2 n + 1 := by
        have : a_d ≤ Nat.log 2 n := Nat.log_mono_right hq_le_n
        omega
      have hs_lt : s_d < (primesSmall Y).card + 1 := by
        have : s_d ≤ (primesSmall Y).card := Finset.card_filter_le _ _
        omega
      have hk₀_lt : k₀_d < (primesSmall Y).card + 1 := by
        have : k₀_d ≤ (primesSmall Y).card := Finset.card_filter_le _ _
        omega
      have hvalid_as : s_d = 0 ∨ 2 * s_d ≤ a_d := by
        by_cases hs0 : s_d = 0
        · exact Or.inl hs0
        · right
          have hq_ge : 2 ^ (2 * s_d) ≤ qSm Y d := by
            let Sq := (primesSmall Y).filter (fun p => 2 ≤ d.factorization p)
            calc 2 ^ (2 * s_d) = (2 ^ 2) ^ Sq.card := by rw [← pow_mul]; rfl
              _ = ∏ _p ∈ Sq, 2 ^ 2 := by simp
              _ ≤ ∏ p ∈ Sq, p ^ (d.factorization p) := Finset.prod_le_prod' fun p hp => by
                  have hp2 : 2 ≤ p := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.two_le
                  have he2 : 2 ≤ d.factorization p := (Finset.mem_filter.mp hp).2
                  exact le_trans (Nat.pow_le_pow_left hp2 2) (Nat.pow_le_pow_right (by omega) he2)
              _ = qSm Y d := rfl
          exact Nat.le_log_of_pow_le (by norm_num) hq_ge
      have hbo_le_R : ∀ m : M_idx, bucketOmega Y n m.1 d < R m.1 + 1 := by
        intro m
        have hbp_dvd : bucketPart Y n m.1 d ∣ d := by
          conv_rhs => rw [eq_qSm_mul_uSm_mul_prod_bucketPart Y n m_start M_max d hY2 hYn hms hMm hd_Icc.1 hd_Icc.2]
          exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i => bucketPart Y n i d) m.2) _
        have hpow : 2 ^ (2 ^ m.1 * bucketOmega Y n m.1 d) ≤ H := by
          calc 2 ^ (2 ^ m.1 * bucketOmega Y n m.1 d)
              = (2 ^ (2 ^ m.1)) ^ (∑ p ∈ primeBucket Y n m.1, d.factorization p) := by rw [pow_mul]; rfl
            _ = ∏ p ∈ primeBucket Y n m.1, (2 ^ (2 ^ m.1)) ^ (d.factorization p) :=
                (Finset.prod_pow_eq_pow_sum _ _ _).symm
            _ ≤ ∏ p ∈ primeBucket Y n m.1, p ^ (d.factorization p) := Finset.prod_le_prod' fun p hp =>
                Nat.pow_le_pow_left (le_of_lt (lt_of_le_of_lt (le_max_right _ _)
                  (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1)) _
            _ = bucketPart Y n m.1 d := rfl
            _ ≤ d := Nat.le_of_dvd (by omega) hbp_dvd
            _ ≤ n := hd_Icc.2
            _ ≤ H := by omega
        have hlog : 2 ^ m.1 * bucketOmega Y n m.1 d ≤ Nat.log 2 H := Nat.le_log_of_pow_le (by norm_num) hpow
        have : bucketOmega Y n m.1 d ≤ R m.1 :=
          (Nat.le_div_iff_mul_le (Nat.two_pow_pos m.1)).mpr (by rwa [mul_comm])
        omega
      let kv_d : K_type := fun m => ⟨bucketOmega Y n m.1 d, hbo_le_R m⟩
      refine Finset.mem_biUnion.mpr ⟨Sum.inr (j, (a_d, s_d), k₀_d, kv_d),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr ha_lt, Finset.mem_range.mpr hs_lt⟩, hvalid_as⟩,
             Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk₀_lt, Finset.mem_univ _⟩⟩⟩)), ?_⟩
      refine Finset.mem_filter.mpr ⟨hd_dyad, rfl, rfl, rfl, fun m hm => ?_⟩
      dsimp only [extK, kv_d]; rw [dif_pos hm]
  -- Helper: dyadic bounds for j < J
  have hℓ_dyad_ge : ∀ j < J, 2 ≤ ℓ_dyad j := by
    intro j _
    have hNj_le : max 1 (N j) ≤ n := max_le (by omega) (Nat.div_le_self n _)
    have : 2 * (2 * max 1 (N j)) ≤ H := by omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 2 * max 1 (N j))).mpr (by linarith)
  have hℓ_dyad_lb : ∀ j < J, (H : ℝ) / (4 * ((n : ℝ) / (2 : ℝ) ^ j)) ≤ (ℓ_dyad j : ℝ) := by
    intro j hj
    have h2j_le_n : 2 ^ j ≤ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : j ≤ Nat.log 2 n))
        (Nat.pow_log_le_self 2 (by omega))
    have hNj_ge1 : 1 ≤ N j := (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).mpr (by simpa using h2j_le_n)
    have hmax : max 1 (N j) = N j := max_eq_right hNj_ge1
    have hNj_le_real : (N j : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ j := by
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self n (2 ^ j)
    have hNj_pos : (0 : ℝ) < (N j : ℝ) := by exact_mod_cast hNj_ge1
    have hdiv_ge : (H : ℝ) / (4 * (N j : ℝ)) ≤ (ℓ_dyad j : ℝ) := by
      have hℓ2 := hℓ_dyad_ge j hj
      have hrem : H < (ℓ_dyad j + 1) * (2 * N j) := by
        dsimp [ℓ_dyad]; rw [hmax]
        have := Nat.div_add_mod H (2 * N j)
        have := Nat.mod_lt H (by omega : 0 < 2 * N j)
        nlinarith
      have hstep : H ≤ 2 * ℓ_dyad j * (2 * N j) := by
        have : ℓ_dyad j + 1 ≤ 2 * ℓ_dyad j := by omega
        have : (ℓ_dyad j + 1) * (2 * N j) ≤ (2 * ℓ_dyad j) * (2 * N j) := Nat.mul_le_mul_right _ this
        omega
      have hreal : (H : ℝ) ≤ (ℓ_dyad j : ℝ) * (4 * (N j : ℝ)) := by
        have : (H : ℝ) ≤ ((2 * ℓ_dyad j * (2 * N j) : ℕ) : ℝ) := by exact_mod_cast hstep
        push_cast at this; linarith
      exact (div_le_iff₀ (by positivity)).mpr hreal
    exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity) (by linarith)) hdiv_ge
  have hdyad_SU : ∀ j < J, ∀ d ∈ dyadic j, ∀ r < 2 * ℓ_dyad j, (m / d + 1) * d + r * d ∈ U := by
    intro j _ d hd r hr
    have hdS := (Finset.mem_filter.mp hd).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (hS hdS)).1
    have hd2j := (Finset.mem_filter.mp hd).2.1
    have hdN : d ≤ N j := (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).mpr (by rwa [mul_comm])
    have hN1 : 1 ≤ N j := le_trans hd1 hdN
    have hmax : max 1 (N j) = N j := max_eq_right hN1
    have h2ℓN : 2 * ℓ_dyad j * N j ≤ H := by
      dsimp [ℓ_dyad]; rw [hmax]
      have := Nat.div_mul_le_self H (2 * N j); linarith
    have ha_gt : m < (m / d + 1) * d := by
      have := Nat.div_add_mod m d; have := Nat.mod_lt m (by omega : 0 < d); nlinarith
    have ha_le : (m / d + 1) * d ≤ m + d := by
      have := Nat.div_mul_le_self m d; nlinarith
    have hr1 : (r + 1) * d ≤ 2 * ℓ_dyad j * N j := Nat.mul_le_mul (by omega) hdN
    have hhi : (m / d + 1) * d + r * d ≤ m + H := by
      have : (r + 1) * d = d + r * d := by ring
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, hhi⟩, d, hdS, dvd_add (dvd_mul_left d _) (dvd_mul_left d r)⟩
  -- Helper: lam_of kv m ≤ p / 2 for all kv : K_type, m ∈ M_idx, p ∈ primeBucket Y n m
  have hlam_hi_all : ∀ kv : K_type, ∀ m ∈ M_idx, ∀ p ∈ primeBucket Y n m, lam_of kv m ≤ (p : ℝ) / 2 := by
    intro kv m hm p hp
    have hp_gtY : Y < p := lt_of_le_of_lt (le_max_left _ _) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hp_geY : (Y : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_of_lt hp_gtY
    have hRm := hRm_le m hm
    have hpow_le1 : ((1 : ℝ) / 2) ^ (m - m_start) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hRm_ub : (R m : ℝ) ≤ 24 * (L / LL) := by nlinarith [div_nonneg (le_of_lt hL_pos) (le_of_lt hLL_pos)]
    have hk_le_R : (extK kv m : ℝ) ≤ (R m : ℝ) := by
      dsimp only [extK]; rw [dif_pos hm]
      have : (kv ⟨m, hm⟩).1 ≤ R m := Nat.lt_succ_iff.mp (kv ⟨m, hm⟩).2
      exact_mod_cast this
    dsimp only [lam_of]
    refine max_le ?_ ?_
    · have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      linarith
    · have h3 : (extK kv m : ℝ) / 8 ≤ 3 * (L / LL) := by linarith
      have hY_half : 3 * (L / LL) ≤ (Y : ℝ) / 2 := by
        have hLL_le_L : LL ≤ L := by
          calc LL = LL ^ (1 : ℕ) := (pow_one LL).symm
            _ ≤ LL ^ (4 : ℕ) := pow_le_pow_right₀ (by linarith only [hLL]) (by norm_num)
            _ ≤ L := hL_ge_LL4
        have h1 : (1 : ℝ) ≤ L / LL := (one_le_div hLL_pos).mpr hLL_le_L
        have h16 : 16 * L / LL = 16 * (L / LL) := by ring
        linarith only [hY_ge_lo, h1, h16]
      linarith only [h3, hY_half, hp_geY]
  -- Verify hX, hdyad, hℓ, hκ_pos, hM, hSU, hκ, hK₁ for idx
  have hX : ∀ α ∈ idx, 0 < X_of α := by
    intro α _
    cases α with
    | inl j => dsimp only [X_of, X_dyad]; positivity
    | inr x => dsimp only [X_of, X_dyad]; positivity
  have hdyad_mem : ∀ j : ℕ, ∀ d ∈ dyadic j, X_dyad j / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X_dyad j := by
    intro j d hd
    have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hle : 2 ^ j * d ≤ n := (Finset.mem_filter.mp hd).2.1
    have hlt : n < 2 ^ (j + 1) * d := (Finset.mem_filter.mp hd).2.2
    have hle_r : (2 : ℝ) ^ j * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
    have hlt_r : (n : ℝ) < (2 : ℝ) ^ (j + 1) * (d : ℝ) := by exact_mod_cast hlt
    dsimp only [X_dyad]
    constructor
    · rw [div_div, div_lt_iff₀ (by positivity)]
      rw [pow_succ] at hlt_r
      linarith
    · rw [le_div_iff₀ h2j_pos]
      linarith
  have hdyad : ∀ α ∈ idx, ∀ d ∈ slice α, X_of α / 2 < (d : ℝ) ∧ (d : ℝ) ≤ X_of α := by
    intro α hα d hd
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
      exact hdyad_mem j d hd
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, _, rfl⟩
      exact hdyad_mem j d (Finset.mem_filter.mp hd).1
  have hℓ : ∀ α ∈ idx, 2 ≤ ℓ_of α := by
    intro α hα
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, hj, rfl⟩
      exact hℓ_dyad_ge j (Finset.mem_Ico.mp hj).2
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, hmem, rfl⟩
      have hj := Finset.mem_range.mp (Finset.mem_product.mp hmem).1
      exact hℓ_dyad_ge j (lt_of_lt_of_le hj (min_le_right _ _))
  have hκ_pos : ∀ α ∈ idx, 1 ≤ κ_of α := by
    intro α hα
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
      exact le_max_left 1 _
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, hmem, rfl⟩
      have h2m := Finset.mem_product.mp (Finset.mem_product.mp hmem).2
      have has := Finset.mem_filter.mp h2m.1
      have has_p := Finset.mem_product.mp has.1
      have hk₀_le : k₀ ≤ (primesSmall Y).card :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp h2m.2).1)
      have hs_le : s ≤ (primesSmall Y).card := Nat.lt_succ_iff.mp (Finset.mem_range.mp has_p.2)
      dsimp only [κ_of]
      have h1 : 1 ≤ Nat.choose (primesSmall Y).card k₀ := Nat.choose_pos hk₀_le
      have h2 : 1 ≤ (if s = 0 then 1 else Nat.choose (primesSmall Y).card s * Nat.choose (a - s) s) := by
        split_ifs with hs0
        · exact le_refl 1
        · have h2s : 2 * s ≤ a := has.2.resolve_left hs0
          have hc1 : 1 ≤ Nat.choose (primesSmall Y).card s := Nat.choose_pos hs_le
          have hc2 : 1 ≤ Nat.choose (a - s) s := Nat.choose_pos (by omega)
          nlinarith only [hc1, hc2]
      have h3 : 1 ≤ ∏ m ∈ M_idx, Nat.choose (R m) (extK kv m) :=
        Finset.one_le_prod' fun m hm => by
          dsimp only [extK]; rw [dif_pos hm]
          exact Nat.choose_pos (Nat.lt_succ_iff.mp (kv ⟨m, hm⟩).2)
      exact Nat.mul_pos (Nat.mul_pos h1 h2) h3
  have hM : ∀ α ∈ idx, ((slice α).card : ℝ) ≤ M_of α := by
    intro α hα
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
      have hsub : dyadic j ⊆ Finset.Icc 1 (N j) := by
        intro d hd
        have hdS := (Finset.mem_filter.mp hd).1
        have hd2j := (Finset.mem_filter.mp hd).2.1
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hdS)).1,
          (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).mpr (by rwa [mul_comm])⟩
      have hcard : (dyadic j).card ≤ N j := le_trans (Finset.card_le_card hsub) (by simp)
      dsimp only [slice, M_of]; exact_mod_cast hcard
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, _, rfl⟩
      have hsub : slice (Sum.inr (j, (a, s), k₀, kv)) ⊆
          (Finset.Icc 1 (N j)).filter fun d =>
            Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
            ∀ m ∈ M_idx, bucketOmega Y n m d = extK kv m := by
        intro d hd
        have hdm := Finset.mem_filter.mp hd
        have hdy := Finset.mem_filter.mp hdm.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hdy.1)).1,
          (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).mpr (by rw [mul_comm]; exact hdy.2.1)⟩, hdm.2⟩
      have hcard : ((slice (Sum.inr (j, (a, s), k₀, kv))).card : ℝ) ≤
          (((Finset.Icc 1 (N j)).filter fun d =>
            Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
            ∀ m ∈ M_idx, bucketOmega Y n m d = extK kv m).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact le_trans hcard (lemma_C2b_slice_euler_rankin Y n (N j) m_start M_max a s k₀ (extK kv)
        (γ_u_of k₀) (γ_q_of s) (lam_of kv) hY2 hYn (Nat.div_le_self n _) hms hMm
        (le_max_left 1 _) (le_max_left 1 _) (fun _ _ => le_max_left 1 _) (hlam_hi_all kv))
  have hSU : ∀ α ∈ idx, ∀ d ∈ slice α, ∀ r < 2 * ℓ_of α, a_start α d + r * d ∈ U := by
    intro α hα d hd r hr
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, hj, rfl⟩
      exact hdyad_SU j (Finset.mem_Ico.mp hj).2 d hd r hr
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, hmem, rfl⟩
      have hj := Finset.mem_range.mp (Finset.mem_product.mp hmem).1
      exact hdyad_SU j (lt_of_lt_of_le hj (min_le_right _ _)) d (Finset.mem_filter.mp hd).1 r hr
  have hκ : ∀ α ∈ idx, ∀ t : ℕ, 1 ≤ t → t ≤ H → ((slice α).filter (fun d => d ∣ t)).card ≤ κ_of α := by
    intro α hα t ht1 htH
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
      have hsub : (dyadic j).filter (fun d => d ∣ t) ⊆ t.divisors := by
        intro d hd
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, by omega⟩
      have hcard_r : (((dyadic j).filter (fun d => d ∣ t)).card : ℝ) ≤ (κ_R1 : ℝ) := by
        calc (((dyadic j).filter (fun d => d ∣ t)).card : ℝ)
            ≤ (t.divisors.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ Real.exp (6 * L / LL) := hR1_div t ht1 htH
          _ ≤ (Nat.ceil (Real.exp (6 * L / LL)) : ℝ) := Nat.le_ceil _
          _ ≤ (κ_R1 : ℝ) := by exact_mod_cast le_max_right 1 _
      exact_mod_cast hcard_r
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, _, rfl⟩
      have hsub : (slice (Sum.inr (j, (a, s), k₀, kv))).filter (fun d => d ∣ t) ⊆
          (Finset.Icc 1 n).filter fun d =>
            d ∣ t ∧ Nat.log 2 (qSm Y d) = a ∧ omegaQ Y d = s ∧ omegaU Y d = k₀ ∧
            ∀ m ∈ M_idx, bucketOmega Y n m d = extK kv m := by
        intro d hd
        have h1 := Finset.mem_filter.mp hd
        have h2 := Finset.mem_filter.mp h1.1
        have h3 := Finset.mem_filter.mp h2.1
        exact Finset.mem_filter.mpr ⟨hS h3.1, h1.2, h2.2⟩
      exact le_trans (Finset.card_le_card hsub)
        (lemma_C2a_slice_divisor_bound Y n m_start M_max H t a s k₀ (extK kv) hY2 hYn hms hMm ht1 htH)
  have hK₁ : ∀ α ∈ idx, ∀ e ∈ slice α, 4 * e.divisors.card ≤ K₁_of α := by
    intro α hα e he
    rcases Finset.mem_union.mp hα with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
      have he_Icc := Finset.mem_Icc.mp (hS (Finset.mem_filter.mp he).1)
      have he_le_H : e ≤ H := by omega
      have hdiv_r : (e.divisors.card : ℝ) ≤ (κ_R1 : ℝ) := by
        calc (e.divisors.card : ℝ) ≤ Real.exp (6 * L / LL) := hR1_div e he_Icc.1 he_le_H
          _ ≤ (Nat.ceil (Real.exp (6 * L / LL)) : ℝ) := Nat.le_ceil _
          _ ≤ (κ_R1 : ℝ) := by exact_mod_cast le_max_right 1 _
      have hdiv_nat : e.divisors.card ≤ κ_R1 := by exact_mod_cast hdiv_r
      dsimp only [K₁_of]
      omega
    · rcases Finset.mem_image.mp h2 with ⟨⟨j, ⟨a, s⟩, k₀, kv⟩, _, rfl⟩
      have hm1 := Finset.mem_filter.mp he
      have hm2 := Finset.mem_filter.mp hm1.1
      have he_Icc := Finset.mem_Icc.mp (hS hm2.1)
      rcases hm1.2 with ⟨ha_eq, hs_eq, hk₀_eq, hk_eq⟩
      have hdiv := slice_divisors_card_le Y n m_start M_max e a s k₀ (extK kv)
        hY2 hYn hms hMm he_Icc.1 he_Icc.2 ha_eq hs_eq hk₀_eq hk_eq
      dsimp only [K₁_of]
      exact Nat.mul_le_mul_left 4 hdiv
  -- Disjoint union split for sums over idx
  have hdisj_idx : Disjoint (J1_set.image Sum.inl) (R2_idx.image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩
    cases h
  -- Bound total Regime 2 slice count per dyadic scale: |AS_set| * |K0_set| * |K_set| ≤ exp (10 * LL^2)
  have hAS_card_le : (AS_set.card : ℝ) ≤ Real.exp (3 * LL) := by
    have h1 : AS_set.card ≤ (Nat.log 2 n + 1) * ((primesSmall Y).card + 1) := by
      calc AS_set.card ≤ ((Finset.range (Nat.log 2 n + 1)) ×ˢ (Finset.range ((primesSmall Y).card + 1))).card :=
            Finset.card_filter_le _ _
        _ = (Nat.log 2 n + 1) * ((primesSmall Y).card + 1) := by simp [Finset.card_product]
    have h2 : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * L := by push_cast; linarith
    have h3 : (((primesSmall Y).card + 1 : ℕ) : ℝ) ≤ 17 * L := by
      have hcardY : (primesSmall Y).card ≤ Y := le_trans (Finset.card_filter_le _ _) (by simp)
      have hY_le_16L : (Y : ℝ) ≤ 16 * L := by
        have : 16 * L / LL ≤ 16 * L := div_le_self (by positivity) (by linarith)
        linarith
      push_cast; linarith [show ((primesSmall Y).card : ℝ) ≤ (Y : ℝ) by exact_mod_cast hcardY]
    have h51 : (51 : ℝ) ≤ Real.exp LL := by linarith [hexp_LL]
    calc (AS_set.card : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * (((primesSmall Y).card + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ (3 * L) * (17 * L) := mul_le_mul h2 h3 (Nat.cast_nonneg _) (by positivity)
      _ = 51 * (Real.exp LL * Real.exp LL) := by rw [hexp_LL]; ring
      _ ≤ Real.exp LL * (Real.exp LL * Real.exp LL) :=
          mul_le_mul_of_nonneg_right h51 (by positivity)
      _ = Real.exp (3 * LL) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hK0_card_le : (K0_set.card : ℝ) ≤ Real.exp (2 * LL) := by
    have hcardY : (primesSmall Y).card ≤ Y := le_trans (Finset.card_filter_le _ _) (by simp)
    have hY_le_16L : (Y : ℝ) ≤ 16 * L := by
      have : 16 * L / LL ≤ 16 * L := div_le_self (by positivity) (by linarith)
      linarith
    have h17 : (17 : ℝ) ≤ Real.exp LL := by linarith [hexp_LL]
    calc (K0_set.card : ℝ) = (((primesSmall Y).card + 1 : ℕ) : ℝ) := by simp [K0_set]
      _ ≤ 17 * L := by push_cast; linarith [show ((primesSmall Y).card : ℝ) ≤ (Y : ℝ) by exact_mod_cast hcardY]
      _ = 17 * Real.exp LL := by rw [hexp_LL]
      _ ≤ Real.exp LL * Real.exp LL := mul_le_mul_of_nonneg_right h17 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (2 * LL) := by rw [← Real.exp_add]; congr 1; ring
  have hK_card_le : (∏ m ∈ M_idx, ((R m + 1 : ℕ) : ℝ)) ≤ Real.exp (7 * LL ^ 2) := by
    have hpt : ∀ m ∈ M_idx, ((R m + 1 : ℕ) : ℝ) ≤ Real.exp (2 * LL) := by
      intro m _
      have hRm_le_logH : R m ≤ Nat.log 2 H := Nat.div_le_self _ _
      have h5 : (5 : ℝ) ≤ Real.exp LL := by linarith [hexp_LL]
      calc ((R m + 1 : ℕ) : ℝ) ≤ (Nat.log 2 H : ℝ) + 1 := by push_cast; linarith [show (R m : ℝ) ≤ (Nat.log 2 H : ℝ) by exact_mod_cast hRm_le_logH]
        _ ≤ 5 * L := by linarith
        _ = 5 * Real.exp LL := by rw [hexp_LL]
        _ ≤ Real.exp LL * Real.exp LL := mul_le_mul_of_nonneg_right h5 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (2 * LL) := by rw [← Real.exp_add]; congr 1; ring
    have hMcard : (M_idx.card : ℝ) ≤ 3 * LL + 1 := by
      have : M_idx.card ≤ M_max + 1 := by
        dsimp only [M_idx]; rw [Nat.card_Icc]; omega
      have hcast : (M_idx.card : ℝ) ≤ (M_max : ℝ) + 1 := by exact_mod_cast this
      linarith
    calc ∏ m ∈ M_idx, ((R m + 1 : ℕ) : ℝ)
        ≤ ∏ _m ∈ M_idx, Real.exp (2 * LL) := Finset.prod_le_prod (fun _ _ => by positivity) hpt
      _ = Real.exp ((M_idx.card : ℝ) * (2 * LL)) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp (7 * LL ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  -- Helper geometric sum ∑ j ∈ range k, (1/2)^j ≤ 2
  have hgeom2 : ∀ k : ℕ, ∑ j ∈ Finset.range k, ((1 : ℝ) / 2) ^ j ≤ 2 := by
    intro k
    have haux : ∀ r : ℕ, ∑ j ∈ Finset.range r, ((1 : ℝ) / 2) ^ j = 2 * (1 - ((1 : ℝ) / 2) ^ r) := by
      intro r; induction r with
      | zero => simp
      | succ r ihr => rw [Finset.sum_range_succ, ihr]; ring
    rw [haux k]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  -- Helper: 4 * n^(4/3) / H ≤ 4 * exp (-600 * E_half)
  have h4n43_H : 4 * (n : ℝ) ^ ((4 : ℝ) / 3) / (H : ℝ) ≤ 4 * Real.exp (-(600 * E_half)) := by
    rw [div_le_iff₀ hH_pos_r, Real.exp_neg]
    have hexp_pos : 0 < Real.exp (600 * E_half) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left hH_lo (show 0 ≤ 4 * (Real.exp (600 * E_half))⁻¹ by positivity)
    have hL : 4 * (Real.exp (600 * E_half))⁻¹ * ((n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (600 * E_half)) =
        4 * (n : ℝ) ^ ((4 : ℝ) / 3) := by field_simp [ne_of_gt hexp_pos]
    linarith
  -- Step A: Verify hSum0 ≤ 1/10
  have hSum0 : ∑ α ∈ idx, (1 : ℝ) / (ℓ_of α : ℝ) ≤ 1 / 10 := by
    rw [Finset.sum_union hdisj_idx,
      Finset.sum_image (fun _ _ _ _ h => Sum.inl.inj h),
      Finset.sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
    have hℓ_inv : ∀ j < J, (1 : ℝ) / (ℓ_dyad j : ℝ) ≤ (4 * (n : ℝ) / (H : ℝ)) * ((1 : ℝ) / 2) ^ j := by
      intro j hj
      have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      calc (1 : ℝ) / (ℓ_dyad j : ℝ)
          ≤ 1 / ((H : ℝ) / (4 * ((n : ℝ) / (2 : ℝ) ^ j))) :=
            one_div_le_one_div_of_le (by positivity) (hℓ_dyad_lb j hj)
        _ = (4 * (n : ℝ) / (H : ℝ)) * ((1 : ℝ) / 2) ^ j := by
            rw [div_pow, one_pow]; field_simp [ne_of_gt hH_pos_r, ne_of_gt h2j_pos]
    have h4n_H : 4 * (n : ℝ) / (H : ℝ) ≤ 4 * Real.exp (-(600 * E_half)) := by
      have hn_le_43 : (n : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := by
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have : 4 * (n : ℝ) / (H : ℝ) ≤ 4 * (n : ℝ) ^ ((4 : ℝ) / 3) / (H : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hH_pos_r)
      linarith
    have h0_R1 : ∑ j ∈ J1_set, (1 : ℝ) / (ℓ_dyad j : ℝ) ≤ 1 / 20 := by
      have hsub : J1_set ⊆ Finset.range J := fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      calc ∑ j ∈ J1_set, (1 : ℝ) / (ℓ_dyad j : ℝ)
          ≤ ∑ j ∈ J1_set, (4 * (n : ℝ) / (H : ℝ)) * ((1 : ℝ) / 2) ^ j :=
            Finset.sum_le_sum fun j hj => hℓ_inv j (Finset.mem_Ico.mp hj).2
        _ = (4 * (n : ℝ) / (H : ℝ)) * ∑ j ∈ J1_set, ((1 : ℝ) / 2) ^ j := by rw [← Finset.mul_sum]
        _ ≤ (4 * Real.exp (-(600 * E_half))) * 2 := by
            refine mul_le_mul h4n_H ?_ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (hgeom2 J)
        _ ≤ 1 / 20 := by
            have h160 : (160 : ℝ) ≤ Real.exp (600 * E_half) := by
              linarith only [hEhalf_ge, Real.add_one_le_exp (600 * E_half)]
            rw [Real.exp_neg]
            have : (Real.exp (600 * E_half))⁻¹ ≤ 1 / 160 := by
              rw [one_div]; exact inv_anti₀ (by norm_num) h160
            linarith only [this]
    have h0_R2 : ∑ x ∈ R2_idx, (1 : ℝ) / (ℓ_dyad x.1 : ℝ) ≤ 1 / 20 := by
      have hfact : ∑ x ∈ R2_idx, (1 : ℝ) / (ℓ_dyad x.1 : ℝ) =
          (∑ j ∈ J2_set, (1 : ℝ) / (ℓ_dyad j : ℝ)) *
            ((AS_set.card : ℝ) * (K0_set.card : ℝ) * (K_set.card : ℝ)) := by
        dsimp only [R2_idx]
        rw [Finset.sum_product]
        have hconst : ∀ j ∈ J2_set,
            ∑ y ∈ AS_set ×ˢ (K0_set ×ˢ K_set), (1 : ℝ) / (ℓ_dyad j : ℝ) =
              ((1 : ℝ) / (ℓ_dyad j : ℝ)) * ((AS_set.card : ℝ) * (K0_set.card : ℝ) * (K_set.card : ℝ)) := by
          intro j _
          rw [Finset.sum_const, Finset.card_product, Finset.card_product, nsmul_eq_mul]
          push_cast; ring
        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
      rw [hfact]
      have hK_eq : (K_set.card : ℝ) = ∏ m ∈ M_idx, ((R m + 1 : ℕ) : ℝ) :=
        card_pi_fin_real M_idx R
      have hsum_j2 : ∑ j ∈ J2_set, (1 : ℝ) / (ℓ_dyad j : ℝ) ≤ 8 * Real.exp (-(600 * E_half)) := by
        have hsub : J2_set ⊆ Finset.range J := fun j hj =>
          Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _))
        calc ∑ j ∈ J2_set, (1 : ℝ) / (ℓ_dyad j : ℝ)
            ≤ ∑ j ∈ J2_set, (4 * (n : ℝ) / (H : ℝ)) * ((1 : ℝ) / 2) ^ j :=
              Finset.sum_le_sum fun j hj => hℓ_inv j (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _))
          _ = (4 * (n : ℝ) / (H : ℝ)) * ∑ j ∈ J2_set, ((1 : ℝ) / 2) ^ j := by rw [← Finset.mul_sum]
          _ ≤ (4 * Real.exp (-(600 * E_half))) * 2 :=
              mul_le_mul h4n_H (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (hgeom2 J))
                (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
          _ = 8 * Real.exp (-(600 * E_half)) := by ring
      have hcnt_le : (AS_set.card : ℝ) * (K0_set.card : ℝ) * (K_set.card : ℝ) ≤ Real.exp (10 * E_half) := by
        rw [hK_eq]
        calc (AS_set.card : ℝ) * (K0_set.card : ℝ) * ∏ m ∈ M_idx, ((R m + 1 : ℕ) : ℝ)
            ≤ Real.exp (3 * LL) * Real.exp (2 * LL) * Real.exp (7 * LL ^ 2) :=
              mul_le_mul (mul_le_mul hAS_card_le hK0_card_le (Nat.cast_nonneg _) (by positivity))
                hK_card_le (by positivity) (by positivity)
          _ = Real.exp (5 * LL + 7 * LL ^ 2) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (10 * E_half) := Real.exp_le_exp.mpr (by nlinarith only [hLL, hLL2_Ehalf])
      calc (∑ j ∈ J2_set, (1 : ℝ) / (ℓ_dyad j : ℝ)) *
              ((AS_set.card : ℝ) * (K0_set.card : ℝ) * (K_set.card : ℝ))
          ≤ (8 * Real.exp (-(600 * E_half))) * Real.exp (10 * E_half) :=
            mul_le_mul hsum_j2 hcnt_le (by positivity) (by positivity)
        _ = 8 * Real.exp (-(590 * E_half)) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ 1 / 20 := by
            have h160 : (160 : ℝ) ≤ Real.exp (590 * E_half) := by
              linarith only [hEhalf_ge, Real.add_one_le_exp (590 * E_half)]
            rw [Real.exp_neg]
            have : (Real.exp (590 * E_half))⁻¹ ≤ 1 / 160 := by
              rw [one_div]; exact inv_anti₀ (by norm_num) h160
            linarith only [this]
    linarith only [h0_R1, h0_R2]
  -- Step B: Verify hSum1 ≤ 1/10 (Absorbed 1/3-power sum!)
  have hSum1 : ∑ α ∈ idx, ((K₁_of α : ℝ) * (κ_of α : ℝ) * M_of α) ^ ((1 : ℝ) / 3) / (ℓ_of α : ℝ) ≤ 1 / 10 := by
    rw [Finset.sum_union hdisj_idx,
      Finset.sum_image (fun _ _ _ _ h => Sum.inl.inj h),
      Finset.sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
    -- Helper: (N j)^(1/3) / ℓ_dyad j ≤ (4 * n^(4/3) / H) * (2 ^ (-(4/3) * j))
    have hNj_div_ℓ : ∀ j < J, (N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ) ≤
        (4 * (n : ℝ) ^ ((4 : ℝ) / 3) / (H : ℝ)) * (2 : ℝ) ^ (-((4 : ℝ) / 3) * (j : ℝ)) := by
      intro j hj
      have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hNj_le : (N j : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ j := by
        rw [le_div_iff₀ h2j_pos]; exact_mod_cast Nat.div_mul_le_self n (2 ^ j)
      have hM13 : (N j : ℝ) ^ ((1 : ℝ) / 3) ≤ ((n : ℝ) / (2 : ℝ) ^ j) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hNj_le (by norm_num)
      calc (N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)
          ≤ ((n : ℝ) / (2 : ℝ) ^ j) ^ ((1 : ℝ) / 3) / ((H : ℝ) / (4 * ((n : ℝ) / (2 : ℝ) ^ j))) :=
            div_le_div₀ (by positivity) hM13 (by positivity) (hℓ_dyad_lb j hj)
        _ = (4 * (n : ℝ) ^ ((4 : ℝ) / 3) / (H : ℝ)) * (2 : ℝ) ^ (-((4 : ℝ) / 3) * (j : ℝ)) := by
            rw [Real.div_rpow (le_of_lt hn_pos) (le_of_lt h2j_pos)]
            have h43 : (n : ℝ) ^ ((4 : ℝ) / 3) = (n : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) := by
              have : ((4 : ℝ) / 3) = ((1 : ℝ) / 3) + 1 := by norm_num
              rw [this, Real.rpow_add hn_pos, Real.rpow_one]
            have h2pow : (2 : ℝ) ^ (-((4 : ℝ) / 3) * (j : ℝ)) =
                (((2 : ℝ) ^ j) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ j)⁻¹ := by
              rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
                ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_neg (by norm_num)]
              congr 1; ring
            rw [h43, h2pow]
            field_simp [ne_of_gt hH_pos_r, ne_of_gt h2j_pos]
    -- Regime 1 sum ≤ 1/20
    have h1_R1 : ∑ j ∈ J1_set,
        (((4 * κ_R1 : ℕ) : ℝ) * (κ_R1 : ℝ) * (N j : ℝ)) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ) ≤ 1 / 20 := by
      have h4_13 : (4 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
        have hpow3 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) := by
          rw [← Real.rpow_natCast ((4 : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
          norm_num
        by_contra hgt; push Not at hgt
        have : (2 : ℝ) ^ (3 : ℕ) < ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) :=
          pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
        linarith
      have hκ_ub : (κ_R1 : ℝ) ≤ 2 * Real.exp (6 * L / LL) := by
        have h1 : (1 : ℝ) ≤ Real.exp (6 * L / LL) := Real.one_le_exp (by positivity)
        have hceil : (Nat.ceil (Real.exp (6 * L / LL)) : ℝ) < Real.exp (6 * L / LL) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        dsimp only [κ_R1]; rw [Nat.cast_max, Nat.cast_one]
        exact max_le (by linarith) (by linarith)
      have hκ23 : (κ_R1 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 * Real.exp (4 * L / LL) := by
        have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hκ_ub (by norm_num : (0 : ℝ) ≤ 2 / 3)
        rw [Real.mul_rpow (by norm_num) (le_of_lt (Real.exp_pos _)), ← Real.exp_mul] at h1
        have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
          calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        have h4 : 6 * L / LL * ((2 : ℝ) / 3) = 4 * L / LL := by ring
        rw [h4] at h1
        nlinarith [Real.exp_pos (4 * L / LL)]
      have hpt : ∀ j ∈ J1_set,
          (((4 * κ_R1 : ℕ) : ℝ) * (κ_R1 : ℝ) * (N j : ℝ)) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ) ≤
            (16 * Real.exp (-(600 * E_half))) * ((2 : ℝ) / 3) ^ j := by
        intro j hj
        have hj_ge : j₀ ≤ j := (Finset.mem_Ico.mp hj).1
        have hj_lt : j < J := (Finset.mem_Ico.mp hj).2
        have hj_real : 12 * L / LL ≤ (j : ℝ) :=
          le_trans (Nat.le_ceil _) (by exact_mod_cast hj_ge)
        have hsplit_num : (((4 * κ_R1 : ℕ) : ℝ) * (κ_R1 : ℝ) * (N j : ℝ)) ^ ((1 : ℝ) / 3) =
            (4 : ℝ) ^ ((1 : ℝ) / 3) * (κ_R1 : ℝ) ^ ((2 : ℝ) / 3) * (N j : ℝ) ^ ((1 : ℝ) / 3) := by
          have hsq : ((4 * κ_R1 : ℕ) : ℝ) * (κ_R1 : ℝ) * (N j : ℝ) = 4 * (κ_R1 : ℝ) ^ (2 : ℕ) * (N j : ℝ) := by
            push_cast; ring
          rw [hsq, Real.mul_rpow (by positivity) (Nat.cast_nonneg _),
            Real.mul_rpow (by norm_num) (by positivity),
            ← Real.rpow_natCast (κ_R1 : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
          norm_num
        have h2split : (2 : ℝ) ^ (-((4 : ℝ) / 3) * (j : ℝ)) =
            (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ)) * (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
        have h2dec1 : (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ)) ≤ Real.exp (-(4 * L / LL)) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
          apply Real.exp_le_exp.mpr
          have hlog2 := half_le_log_two
          have hnn : 0 ≤ L / LL := div_nonneg (le_of_lt hL_pos) (le_of_lt hLL_pos)
          have h12 : 12 * L / LL = 12 * (L / LL) := by ring
          have h4 : 4 * L / LL = 4 * (L / LL) := by ring
          nlinarith only [hj_real, hlog2, hnn, h12, h4]
        have h2dec2 : (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ)) ≤ ((2 : ℝ) / 3) ^ j := by
          have h12_23 : (2 : ℝ) ^ (-(2 : ℝ) / 3) ≤ 2 / 3 := by
            have hpow3 : ((2 : ℝ) ^ (-(2 : ℝ) / 3)) ^ (3 : ℕ) ≤ ((2 : ℝ) / 3) ^ (3 : ℕ) := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(2 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
              have hneg2 : (2 : ℝ) ^ (-(2 : ℝ) / 3 * (3 : ℕ)) = (4 : ℝ)⁻¹ := by
                have : (-(2 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = -(2 : ℝ) := by norm_num
                rw [this, Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
              rw [hneg2]; norm_num
            by_contra hgt; push Not at hgt
            have : ((2 : ℝ) / 3) ^ (3 : ℕ) < ((2 : ℝ) ^ (-(2 : ℝ) / 3)) ^ (3 : ℕ) :=
              pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
            linarith
          have heq : (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ)) = ((2 : ℝ) ^ (-(2 : ℝ) / 3)) ^ j := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(2 : ℝ) / 3)) j, ← Real.rpow_mul (by norm_num)]
            congr 1; ring
          rw [heq]
          exact pow_le_pow_left₀ (by positivity) h12_23 j
        have h1 := hNj_div_ℓ j hj_lt
        rw [hsplit_num, mul_div_assoc]
        calc (4 : ℝ) ^ ((1 : ℝ) / 3) * (κ_R1 : ℝ) ^ ((2 : ℝ) / 3) * ((N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ))
            ≤ (2 * (2 * Real.exp (4 * L / LL))) *
                ((4 * Real.exp (-(600 * E_half))) * (2 : ℝ) ^ (-((4 : ℝ) / 3) * (j : ℝ))) :=
              mul_le_mul (mul_le_mul h4_13 hκ23 (by positivity) (by norm_num))
                (le_trans h1 (mul_le_mul_of_nonneg_right h4n43_H (by positivity)))
                (by positivity) (by positivity)
          _ = (16 * Real.exp (-(600 * E_half))) *
                (Real.exp (4 * L / LL) * (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ))) *
                (2 : ℝ) ^ (-((2 : ℝ) / 3) * (j : ℝ)) := by rw [h2split]; ring
          _ ≤ (16 * Real.exp (-(600 * E_half))) *
                (Real.exp (4 * L / LL) * Real.exp (-(4 * L / LL))) *
                ((2 : ℝ) / 3) ^ j := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h2dec1 (le_of_lt (Real.exp_pos _))) (by positivity))
                h2dec2 (by positivity) (by positivity)
          _ = (16 * Real.exp (-(600 * E_half))) * ((2 : ℝ) / 3) ^ j := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have hsub : J1_set ⊆ Finset.range J := fun j hj => Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      have hgeom23 : ∑ j ∈ J1_set, ((2 : ℝ) / 3) ^ j ≤ 3 := by
        calc ∑ j ∈ J1_set, ((2 : ℝ) / 3) ^ j
            ≤ ∑ j ∈ Finset.range J, ((2 : ℝ) / 3) ^ j :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
          _ ≤ 3 := by
              have haux : ∀ k : ℕ, ∑ d ∈ Finset.range k, ((2 : ℝ) / 3) ^ d =
                  3 * (1 - ((2 : ℝ) / 3) ^ k) := by
                intro k; induction k with
                | zero => simp
                | succ k ih => rw [Finset.sum_range_succ, ih]; ring
              rw [haux J]
              linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) J]
      calc ∑ j ∈ J1_set, (((4 * κ_R1 : ℕ) : ℝ) * (κ_R1 : ℝ) * (N j : ℝ)) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)
          ≤ ∑ j ∈ J1_set, (16 * Real.exp (-(600 * E_half))) * ((2 : ℝ) / 3) ^ j := Finset.sum_le_sum hpt
        _ = (16 * Real.exp (-(600 * E_half))) * ∑ j ∈ J1_set, ((2 : ℝ) / 3) ^ j := by rw [← Finset.mul_sum]
        _ ≤ (16 * Real.exp (-(600 * E_half))) * 3 := mul_le_mul_of_nonneg_left hgeom23 (by positivity)
        _ = 48 * Real.exp (-(600 * E_half)) := by ring
        _ ≤ 1 / 20 := by
            have h960 : (960 : ℝ) ≤ Real.exp (600 * E_half) := by linarith [Real.add_one_le_exp (600 * E_half)]
            rw [Real.exp_neg]
            have : (Real.exp (600 * E_half))⁻¹ ≤ 1 / 960 := by
              rw [one_div]; exact inv_anti₀ (by norm_num) h960
            linarith
    -- Regime 2 sum ≤ 1/20
    have h1_R2 : ∑ x ∈ R2_idx,
        ((K₁_of (Sum.inr x) : ℝ) * (κ_of (Sum.inr x) : ℝ) * M_of (Sum.inr x)) ^ ((1 : ℝ) / 3) / (ℓ_dyad x.1 : ℝ) ≤ 1 / 20 := by
      have hinner : ∀ j ∈ J2_set,
          ∑ y ∈ AS_set ×ˢ (K0_set ×ˢ K_set),
            ((K₁_of (Sum.inr (j, y)) : ℝ) * (κ_of (Sum.inr (j, y)) : ℝ) * M_of (Sum.inr (j, y))) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ) ≤
            2 * ((N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)) * Real.exp (550 * E_half) := by
        intro j hj
        have hjJ : j < J := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        have hℓ_pos : (0 : ℝ) < (ℓ_dyad j : ℝ) := by
          have := hℓ_dyad_ge j hjJ; exact_mod_cast (by omega : 0 < ℓ_dyad j)
        let C_pref : ℝ := 2 * ((N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)) *
          Real.exp ((10 + 8 * (M_max : ℝ)) / 3)
        let Fq : (ℕ × ℕ) → ℝ := fun p =>
          ((3 : ℝ) ^ p.2 * (2 : ℝ) ^ ((p.1 : ℝ) / 4) *
            ((if p.2 = 0 then 1 else Nat.choose (primesSmall Y).card p.2 * Nat.choose (p.1 - p.2) p.2 : ℕ) : ℝ) *
            (2 : ℝ) ^ (-(p.1 : ℝ) / 2) * (γ_q_of p.2 ^ p.2)⁻¹ * Real.exp (γ_q_of p.2 * (4 * U_bd))) ^ ((1 : ℝ) / 3)
        let Fu : ℕ → ℝ := fun k₀ =>
          ((2 : ℝ) ^ k₀ * (Nat.choose (primesSmall Y).card k₀ : ℝ) *
            (γ_u_of k₀ ^ k₀)⁻¹ * Real.exp (γ_u_of k₀ * U_bd)) ^ ((1 : ℝ) / 3)
        let Fm : ∀ (m : M_idx), Fin (R m.1 + 1) → ℝ := fun m k =>
          ((2 : ℝ) ^ k.1 * (Nat.choose (R m.1) k.1 : ℝ) *
            ((max 1 ((k.1 : ℝ) / 8)) ^ k.1)⁻¹ * Real.exp (8 * (max 1 ((k.1 : ℝ) / 8) - 1))) ^ ((1 : ℝ) / 3)
        have hterm_le : ∀ y ∈ AS_set ×ˢ (K0_set ×ˢ K_set),
            ((K₁_of (Sum.inr (j, y)) : ℝ) * (κ_of (Sum.inr (j, y)) : ℝ) * M_of (Sum.inr (j, y))) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ) ≤
            C_pref * (Fq y.1 * (Fu y.2.1 * ∏ m : M_idx, Fm m (y.2.2 m))) := by
          rintro ⟨⟨a, s⟩, k₀, kv⟩ _
          have h := regime2_term_factor_le (N j : ℝ) (ℓ_dyad j : ℝ) (M_max : ℝ) U_bd
            (γ_u_of k₀) (γ_q_of s) (Nat.cast_nonneg _) hℓ_pos (le_max_left 1 _) (le_max_left 1 _)
            (primesSmall Y).card a s k₀ M_idx R kv
          dsimp only [K₁_of, κ_of, M_of, C_pref, Fq, Fu, Fm, lam_of, extK]
          linarith [h]
        have hfact_sum :
            ∑ p ∈ AS_set, ∑ z ∈ K0_set ×ˢ K_set, Fq p * (Fu z.1 * ∏ m : M_idx, Fm m (z.2 m)) =
            (∑ p ∈ AS_set, Fq p) * (∑ k₀ ∈ K0_set, Fu k₀) *
              ∏ m : M_idx, ∑ k : Fin (R m.1 + 1), Fm m k := by
          have h1 : ∀ p ∈ AS_set,
              ∑ z ∈ K0_set ×ˢ K_set, Fq p * (Fu z.1 * ∏ m : M_idx, Fm m (z.2 m)) =
              Fq p * ((∑ k₀ ∈ K0_set, Fu k₀) * ∑ kv ∈ K_set, ∏ m : M_idx, Fm m (kv m)) := by
            intro p _
            rw [← Finset.mul_sum, Finset.sum_product]
            congr 1
            simp_rw [← Finset.mul_sum]
            rw [← Finset.sum_mul]
          rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
          dsimp only [K_set]
          rw [← Fintype.prod_sum Fm]
          ring
        have hU_ge1 : 1 ≤ U_bd := le_max_left 1 _
        have hQ_ge1 : 1 ≤ 4 * U_bd := by linarith
        have hEhalf_sqrt : Real.sqrt (L / LL) = E_half := Real.sqrt_eq_rpow (L / LL)
        -- 1. ∑ Fq ≤ exp (3 * LL + 4 * U_bd / 3 + 406 * E_half)
        have hFq_exp_le : (2 : ℝ) / 3 * Real.sqrt (24 * ((primesSmall Y).card : ℝ) * (4 * U_bd)) ≤ 406 * E_half := by
          have hprod : 24 * ((primesSmall Y).card : ℝ) * (4 * U_bd) ≤ 368640 * (L / LL) := by
            have h1 : ((primesSmall Y).card : ℝ) * (4 * U_bd) ≤ (192 * L / LL ^ 2) * (80 * LL) :=
              mul_le_mul hPsm_card_le (by linarith) (by positivity) (by positivity)
            have h2 : (192 * L / LL ^ 2) * (80 * LL) = 15360 * (L / LL) := by
              field_simp [ne_of_gt hLL_pos]; ring
            linarith
          have hsq : Real.sqrt (24 * ((primesSmall Y).card : ℝ) * (4 * U_bd)) ≤ 608 * E_half := by
            have h368 : Real.sqrt 368640 ≤ 608 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
            calc Real.sqrt (24 * ((primesSmall Y).card : ℝ) * (4 * U_bd))
                ≤ Real.sqrt (368640 * (L / LL)) := Real.sqrt_le_sqrt hprod
              _ = Real.sqrt 368640 * E_half := by rw [Real.sqrt_mul (by norm_num), hEhalf_sqrt]
              _ ≤ 608 * E_half := mul_le_mul_of_nonneg_right h368 (by positivity)
          linarith
        have hSumFq : ∑ p ∈ AS_set, Fq p ≤ Real.exp (3 * LL + 4 * U_bd / 3 + 406 * E_half) := by
          have hpt : ∀ p ∈ AS_set, Fq p ≤ Real.exp (4 * U_bd / 3 + 406 * E_half) := by
            intro p _
            have hf := factor_Fq_le (primesSmall Y).card p.1 p.2 hQ_ge1
            calc Fq p ≤ Real.exp (4 * U_bd / 3) *
                  Real.exp ((2 : ℝ) / 3 * Real.sqrt (24 * ((primesSmall Y).card : ℝ) * (4 * U_bd))) := hf
              _ = Real.exp (4 * U_bd / 3 + (2 : ℝ) / 3 * Real.sqrt (24 * ((primesSmall Y).card : ℝ) * (4 * U_bd))) :=
                  (Real.exp_add _ _).symm
              _ ≤ Real.exp (4 * U_bd / 3 + 406 * E_half) := Real.exp_le_exp.mpr (by linarith)
          calc ∑ p ∈ AS_set, Fq p
              ≤ ∑ _p ∈ AS_set, Real.exp (4 * U_bd / 3 + 406 * E_half) := Finset.sum_le_sum hpt
            _ = (AS_set.card : ℝ) * Real.exp (4 * U_bd / 3 + 406 * E_half) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ Real.exp (3 * LL) * Real.exp (4 * U_bd / 3 + 406 * E_half) :=
                mul_le_mul_of_nonneg_right hAS_card_le (le_of_lt (Real.exp_pos _))
            _ = Real.exp (3 * LL + 4 * U_bd / 3 + 406 * E_half) := by rw [← Real.exp_add]; congr 1; ring
        -- 2. ∑ Fu ≤ exp (2 * LL + U_bd / 3 + 60 * E_half)
        have hFu_exp_le : (2 : ℝ) / 3 * Real.sqrt (2 * ((primesSmall Y).card : ℝ) * U_bd) ≤ 60 * E_half := by
          have hprod : 2 * ((primesSmall Y).card : ℝ) * U_bd ≤ 7680 * (L / LL) := by
            have h1 : ((primesSmall Y).card : ℝ) * U_bd ≤ (192 * L / LL ^ 2) * (20 * LL) :=
              mul_le_mul hPsm_card_le hUbd_le (by positivity) (by positivity)
            have h2 : (192 * L / LL ^ 2) * (20 * LL) = 3840 * (L / LL) := by
              field_simp [ne_of_gt hLL_pos]; ring
            linarith
          have hsq : Real.sqrt (2 * ((primesSmall Y).card : ℝ) * U_bd) ≤ 88 * E_half := by
            have h7680 : Real.sqrt 7680 ≤ 88 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
            calc Real.sqrt (2 * ((primesSmall Y).card : ℝ) * U_bd)
                ≤ Real.sqrt (7680 * (L / LL)) := Real.sqrt_le_sqrt hprod
              _ = Real.sqrt 7680 * E_half := by rw [Real.sqrt_mul (by norm_num), hEhalf_sqrt]
              _ ≤ 88 * E_half := mul_le_mul_of_nonneg_right h7680 (by positivity)
          linarith
        have hSumFu : ∑ k₀ ∈ K0_set, Fu k₀ ≤ Real.exp (2 * LL + U_bd / 3 + 60 * E_half) := by
          have hpt : ∀ k₀ ∈ K0_set, Fu k₀ ≤ Real.exp (U_bd / 3 + 60 * E_half) := by
            intro k₀ _
            have hf := factor_Fu_le (primesSmall Y).card k₀ hU_ge1
            calc Fu k₀ ≤ Real.exp (U_bd / 3) *
                  Real.exp ((2 : ℝ) / 3 * Real.sqrt (2 * ((primesSmall Y).card : ℝ) * U_bd)) := hf
              _ = Real.exp (U_bd / 3 + (2 : ℝ) / 3 * Real.sqrt (2 * ((primesSmall Y).card : ℝ) * U_bd)) :=
                  (Real.exp_add _ _).symm
              _ ≤ Real.exp (U_bd / 3 + 60 * E_half) := Real.exp_le_exp.mpr (by linarith)
          calc ∑ k₀ ∈ K0_set, Fu k₀
              ≤ ∑ _k₀ ∈ K0_set, Real.exp (U_bd / 3 + 60 * E_half) := Finset.sum_le_sum hpt
            _ = (K0_set.card : ℝ) * Real.exp (U_bd / 3 + 60 * E_half) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ Real.exp (2 * LL) * Real.exp (U_bd / 3 + 60 * E_half) :=
                mul_le_mul_of_nonneg_right hK0_card_le (le_of_lt (Real.exp_pos _))
            _ = Real.exp (2 * LL + U_bd / 3 + 60 * E_half) := by rw [← Real.exp_add]; congr 1; ring
        -- 3. ∏ m, ∑ k, Fm m k ≤ exp (7 * LL^2 + 54 * E_half)
        have hSumFm : ∏ m : M_idx, ∑ k : Fin (R m.1 + 1), Fm m k ≤ Real.exp (7 * LL ^ 2 + 54 * E_half) := by
          have hper_m : ∀ m : M_idx, ∑ k : Fin (R m.1 + 1), Fm m k ≤
              ((R m.1 + 1 : ℕ) : ℝ) * Real.exp ((8 : ℝ) / 3 * Real.sqrt (R m.1 : ℝ)) := by
            intro m
            calc ∑ k : Fin (R m.1 + 1), Fm m k
                ≤ ∑ _k : Fin (R m.1 + 1), Real.exp ((8 : ℝ) / 3 * Real.sqrt (R m.1 : ℝ)) :=
                  Finset.sum_le_sum fun k _ => factor_Fm_le (R m.1) k.1
              _ = ((R m.1 + 1 : ℕ) : ℝ) * Real.exp ((8 : ℝ) / 3 * Real.sqrt (R m.1 : ℝ)) := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hsum_R12 : ∑ m ∈ M_idx, (8 : ℝ) / 3 * Real.sqrt (R m : ℝ) ≤ 54 * E_half := by
            have hsq24 : Real.sqrt 24 ≤ 5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
            have hsq12 : Real.sqrt ((1 : ℝ) / 2) ≤ 3 / 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
            have hpt : ∀ m ∈ M_idx, (8 : ℝ) / 3 * Real.sqrt (R m : ℝ) ≤
                ((40 : ℝ) / 3) * E_half * ((3 : ℝ) / 4) ^ (m - m_start) := by
              intro m hm
              have h1 : Real.sqrt (R m : ℝ) ≤ Real.sqrt (24 * (L / LL) * ((1 : ℝ) / 2) ^ (m - m_start)) :=
                Real.sqrt_le_sqrt (hRm_le m hm)
              have hsqrt_pow : Real.sqrt (((1 : ℝ) / 2) ^ (m - m_start)) =
                  (Real.sqrt ((1 : ℝ) / 2)) ^ (m - m_start) := by
                rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
                  ← Real.rpow_natCast ((1 : ℝ) / 2) (m - m_start),
                  ← Real.rpow_natCast (((1 : ℝ) / 2) ^ ((1 : ℝ) / 2)) (m - m_start),
                  ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
                hEhalf_sqrt, hsqrt_pow] at h1
              have hpow_le : (Real.sqrt ((1 : ℝ) / 2)) ^ (m - m_start) ≤ ((3 : ℝ) / 4) ^ (m - m_start) :=
                pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq12 _
              have h2 : Real.sqrt 24 * E_half * (Real.sqrt ((1 : ℝ) / 2)) ^ (m - m_start) ≤
                  5 * E_half * ((3 : ℝ) / 4) ^ (m - m_start) :=
                mul_le_mul (mul_le_mul_of_nonneg_right hsq24 (by positivity)) hpow_le (by positivity) (by positivity)
              linarith
            have hgeom34 : ∑ m ∈ M_idx, ((3 : ℝ) / 4) ^ (m - m_start) ≤ 4 := by
              have hinj : Set.InjOn (fun m => m - m_start) (M_idx : Set ℕ) := by
                intro m₁ hm₁ m₂ hm₂ hEq
                have h1 := (Finset.mem_Icc.mp hm₁).1
                have h2 := (Finset.mem_Icc.mp hm₂).1
                dsimp only at hEq; omega
              have hsub : M_idx.image (fun m => m - m_start) ⊆ Finset.range (M_max + 1) := by
                intro d hd
                rcases Finset.mem_image.mp hd with ⟨m, hm, rfl⟩
                have := (Finset.mem_Icc.mp hm).2
                exact Finset.mem_range.mpr (by omega)
              rw [← Finset.sum_image (fun m₁ hm₁ m₂ hm₂ hEq => hinj hm₁ hm₂ hEq)]
              calc ∑ d ∈ M_idx.image (fun m => m - m_start), ((3 : ℝ) / 4) ^ d
                  ≤ ∑ d ∈ Finset.range (M_max + 1), ((3 : ℝ) / 4) ^ d :=
                    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
                _ ≤ 4 := by
                    have haux : ∀ k : ℕ, ∑ d ∈ Finset.range k, ((3 : ℝ) / 4) ^ d =
                        4 * (1 - ((3 : ℝ) / 4) ^ k) := by
                      intro k; induction k with
                      | zero => simp
                      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
                    rw [haux (M_max + 1)]
                    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (M_max + 1)]
            calc ∑ m ∈ M_idx, (8 : ℝ) / 3 * Real.sqrt (R m : ℝ)
                ≤ ∑ m ∈ M_idx, ((40 : ℝ) / 3) * E_half * ((3 : ℝ) / 4) ^ (m - m_start) := Finset.sum_le_sum hpt
              _ = ((40 : ℝ) / 3) * E_half * ∑ m ∈ M_idx, ((3 : ℝ) / 4) ^ (m - m_start) := by rw [← Finset.mul_sum]
              _ ≤ ((40 : ℝ) / 3) * E_half * 4 := mul_le_mul_of_nonneg_left hgeom34 (by positivity)
              _ ≤ 54 * E_half := by linarith [show (0 : ℝ) ≤ E_half by positivity]
          calc ∏ m : M_idx, ∑ k : Fin (R m.1 + 1), Fm m k
              ≤ ∏ m : M_idx, (((R m.1 + 1 : ℕ) : ℝ) * Real.exp ((8 : ℝ) / 3 * Real.sqrt (R m.1 : ℝ))) :=
                Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun k _ => by dsimp [Fm]; positivity)
                  (fun m _ => hper_m m)
            _ = (∏ m ∈ M_idx, ((R m + 1 : ℕ) : ℝ)) * Real.exp (∑ m ∈ M_idx, (8 : ℝ) / 3 * Real.sqrt (R m : ℝ)) := by
                rw [Finset.prod_mul_distrib,
                  Finset.prod_coe_sort M_idx (fun m => ((R m + 1 : ℕ) : ℝ)),
                  Finset.prod_coe_sort M_idx (fun m => Real.exp ((8 : ℝ) / 3 * Real.sqrt (R m : ℝ))),
                  ← Real.exp_sum]
            _ ≤ Real.exp (7 * LL ^ 2) * Real.exp (54 * E_half) :=
                mul_le_mul hK_card_le (Real.exp_le_exp.mpr hsum_R12) (by positivity) (by positivity)
            _ = Real.exp (7 * LL ^ 2 + 54 * E_half) := (Real.exp_add _ _).symm
        have htotal_exp :
            (10 + 8 * (M_max : ℝ)) / 3 + (3 * LL + 4 * U_bd / 3 + 406 * E_half) +
            (2 * LL + U_bd / 3 + 60 * E_half) + (7 * LL ^ 2 + 54 * E_half) ≤ 550 * E_half := by
          nlinarith only [hLL, hLL2_Ehalf, hMmax_le, hUbd_le]
        calc ∑ y ∈ AS_set ×ˢ (K0_set ×ˢ K_set),
              ((K₁_of (Sum.inr (j, y)) : ℝ) * (κ_of (Sum.inr (j, y)) : ℝ) * M_of (Sum.inr (j, y))) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)
            ≤ ∑ y ∈ AS_set ×ˢ (K0_set ×ˢ K_set),
                C_pref * (Fq y.1 * (Fu y.2.1 * ∏ m : M_idx, Fm m (y.2.2 m))) := Finset.sum_le_sum hterm_le
          _ = C_pref * ((∑ p ∈ AS_set, Fq p) * (∑ k₀ ∈ K0_set, Fu k₀) *
                ∏ m : M_idx, ∑ k : Fin (R m.1 + 1), Fm m k) := by
              rw [← Finset.mul_sum, Finset.sum_product, hfact_sum]
          _ ≤ C_pref * (Real.exp (3 * LL + 4 * U_bd / 3 + 406 * E_half) *
                Real.exp (2 * LL + U_bd / 3 + 60 * E_half) *
                Real.exp (7 * LL ^ 2 + 54 * E_half)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by dsimp [C_pref]; positivity)
              exact mul_le_mul (mul_le_mul hSumFq hSumFu (Finset.sum_nonneg fun _ _ => by dsimp [Fu]; positivity) (by positivity))
                hSumFm (Finset.prod_nonneg fun m _ => Finset.sum_nonneg fun k _ => by dsimp [Fm]; positivity) (by positivity)
          _ = 2 * ((N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)) *
              Real.exp ((10 + 8 * (M_max : ℝ)) / 3 + (3 * LL + 4 * U_bd / 3 + 406 * E_half) +
                (2 * LL + U_bd / 3 + 60 * E_half) + (7 * LL ^ 2 + 54 * E_half)) := by
              dsimp only [C_pref]
              rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
              congr 2; ring
          _ ≤ 2 * ((N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)) * Real.exp (550 * E_half) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htotal_exp) (by positivity)
      dsimp only [R2_idx]
      rw [Finset.sum_product]
      calc ∑ j ∈ J2_set, ∑ y ∈ AS_set ×ˢ (K0_set ×ˢ K_set),
              ((K₁_of (Sum.inr (j, y)) : ℝ) * (κ_of (Sum.inr (j, y)) : ℝ) * M_of (Sum.inr (j, y))) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)
          ≤ ∑ j ∈ J2_set, (2 * ((N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)) * Real.exp (550 * E_half)) :=
            Finset.sum_le_sum hinner
        _ = 2 * (∑ j ∈ J2_set, (N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)) * Real.exp (550 * E_half) := by
            simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
        _ ≤ 2 * (8 * Real.exp (-(600 * E_half))) * Real.exp (550 * E_half) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (le_of_lt (Real.exp_pos _))
            have hpt : ∀ j ∈ J2_set, (N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ) ≤
                (4 * Real.exp (-(600 * E_half))) * ((1 : ℝ) / 2) ^ j := by
              intro j hj
              have hjJ : j < J := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
              have h1 := hNj_div_ℓ j hjJ
              have h2pow : (2 : ℝ) ^ (-((4 : ℝ) / 3) * (j : ℝ)) ≤ ((1 : ℝ) / 2) ^ j := by
                rw [one_div, inv_pow, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_neg (by norm_num)]
                exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) j])
              exact le_trans h1 (mul_le_mul h4n43_H h2pow (by positivity) (by positivity))
            have hsub : J2_set ⊆ Finset.range J := fun j hj =>
              Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _))
            calc ∑ j ∈ J2_set, (N j : ℝ) ^ ((1 : ℝ) / 3) / (ℓ_dyad j : ℝ)
                ≤ ∑ j ∈ J2_set, (4 * Real.exp (-(600 * E_half))) * ((1 : ℝ) / 2) ^ j := Finset.sum_le_sum hpt
              _ = (4 * Real.exp (-(600 * E_half))) * ∑ j ∈ J2_set, ((1 : ℝ) / 2) ^ j := by rw [← Finset.mul_sum]
              _ ≤ (4 * Real.exp (-(600 * E_half))) * 2 :=
                  mul_le_mul_of_nonneg_left
                    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (hgeom2 J))
                    (by positivity)
              _ = 8 * Real.exp (-(600 * E_half)) := by ring
        _ = 16 * (Real.exp (-(600 * E_half)) * Real.exp (550 * E_half)) := by ring
        _ = 16 * Real.exp (-(50 * E_half)) := by rw [← Real.exp_add]; congr 2; ring
        _ ≤ 1 / 20 := by
            have h320 : (320 : ℝ) ≤ Real.exp (50 * E_half) := by
              linarith only [hEhalf_ge, Real.add_one_le_exp (50 * E_half)]
            rw [Real.exp_neg]
            have : (Real.exp (50 * E_half))⁻¹ ≤ 1 / 320 := by
              rw [one_div]; exact inv_anti₀ (by norm_num) h320
            linarith only [this]
    linarith only [h1_R1, h1_R2]
  exact lemma_B_prime idx S U slice a_start X_of ℓ_of κ_of K₁_of M_of H
    hcover hX hdyad hℓ hκ_pos hM hSU hU_diam hκ hK₁ hSum1 hSum0

/-! ### Section 7: Headline Minimax-Sharp `1/2` World-Record Theorems (Pure-Mathlib `sInf` & `⨆` Forms) -/

/-- Explicit nonemptiness of the closed-right admissible set for every `n, m : ℕ` (so `sInf` is non-degenerate). -/
theorem ppl173_closed_set_nonempty (n m : ℕ) :
    ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ).Nonempty := by
  refine ⟨n * n, ?_⟩
  obtain ⟨a, hinj, hprop⟩ :=
    exists_distinct_multiples_trivial_sq (Finset.Icc 1 n) n m (n * n) (le_refl _) (le_refl _)
  exact ⟨a, fun i j hi1 hin hj1 hjn hEq =>
    hinj i (Finset.mem_Icc.mpr ⟨hi1, hin⟩) j (Finset.mem_Icc.mpr ⟨hj1, hjn⟩) hEq,
    fun k hk1 hkn => hprop k (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)⟩

/-- Explicit nonemptiness of the open-interval admissible set for every `n, m : ℕ` (so `sInf` is non-degenerate). -/
theorem ppl173_open_set_nonempty (n m : ℕ) :
    ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ).Nonempty := by
  obtain ⟨h, a, hinj, hprop⟩ := ppl173_closed_set_nonempty n m
  refine ⟨h + 1, a, hinj, fun k hk1 hkn => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hprop k hk1 hkn
  exact ⟨h1, by omega, h3⟩

/-- Explicit `BddAbove` witness for the closed-right supremum over `m : ℕ` (so `⨆` is non-degenerate). -/
theorem ppl173_closed_bddAbove (n : ℕ) :
    BddAbove (Set.range fun m : ℕ => ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ)) := by
  refine ⟨((n * n : ℕ) : ℝ), ?_⟩
  rintro _ ⟨m', rfl⟩
  have hm' : n * n ∈ ({ h : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m' < a k ∧ a k ≤ m' + h ∧ k ∣ a k) } : Set ℕ) := by
    obtain ⟨a, hinj, hprop⟩ :=
      exists_distinct_multiples_trivial_sq (Finset.Icc 1 n) n m' (n * n) (le_refl _) (le_refl _)
    exact ⟨a, fun i j hi1 hin hj1 hjn hEq =>
      hinj i (Finset.mem_Icc.mpr ⟨hi1, hin⟩) j (Finset.mem_Icc.mpr ⟨hj1, hjn⟩) hEq,
      fun k hk1 hkn => hprop k (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)⟩
  dsimp only; exact_mod_cast Nat.sInf_le hm'

/-- Explicit `BddAbove` witness for the open-interval supremum over `m : ℕ` (so `⨆` is non-degenerate). -/
theorem ppl173_open_bddAbove (n : ℕ) :
    BddAbove (Set.range fun m : ℕ => ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ)) := by
  refine ⟨((n * n + 1 : ℕ) : ℝ), ?_⟩
  rintro _ ⟨m', rfl⟩
  have hm' : n * n + 1 ∈ ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m' < a k ∧ a k < m' + L ∧ k ∣ a k) } : Set ℕ) := by
    obtain ⟨a, hinj, hprop⟩ :=
      exists_distinct_multiples_trivial_sq (Finset.Icc 1 n) n m' (n * n) (le_refl _) (le_refl _)
    refine ⟨a, fun i j hi1 hin hj1 hjn hEq =>
      hinj i (Finset.mem_Icc.mpr ⟨hi1, hin⟩) j (Finset.mem_Icc.mpr ⟨hj1, hjn⟩) hEq,
      fun k hk1 hkn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hprop k (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)
    exact ⟨h1, by omega, h3⟩
  dsimp only; exact_mod_cast Nat.sInf_le hm'

/-- For every `n ≥ 16`, `1 ≤ (log n / log (log n)) ^ (1/2)` and `0 < log (log n)`. -/
private lemma one_le_world_record_half_exp (n : ℕ) (hn16 : 16 ≤ n) :
    0 < Real.log (Real.log (n : ℝ)) ∧
    1 ≤ (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2) := by
  have hlog2 := half_le_log_two
  have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by rw [h16, Real.log_pow]; push_cast; rfl
  have hL_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by exact_mod_cast hn16 : (16 : ℝ) ≤ (n : ℝ))
    linarith
  have hLL_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos (by linarith)
  have hLL_le_L : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log (n : ℝ))]
  have hratio : 1 ≤ Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
    (one_le_div hLL_pos).mpr hLL_le_L
  exact ⟨hLL_pos, Real.one_le_rpow hratio (by norm_num)⟩

/-- **HEADLINE NEW MINIMAX-SHARP `1/2` WORLD RECORD (Closed-Right `(m, m + h]` Supremum Form):**
Unconditionally in pure Mathlib, strictly improving both our prior Lean-verified `2/3` bound
(`PPL173_WorldRecordFourThirds.lean`) and Chen–Korsky (`arXiv:2607.26450`, Aug 2026):
```
∃ C > 0, ∀ n ≥ 16, sup_m f_closed(n, m) ≤ n^{4/3} * exp (C * (log n / log (log n))^{1/2}).
``` -/
theorem ppl173_world_record_half_closed_iSup :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      (⨆ m : ℕ, ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ (n : ℝ) ^ ((4 : ℝ) / 3) *
            Real.exp (C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2)) := by
  let N₀ : ℕ := Nat.ceil (Real.exp (Real.exp 200))
  let C : ℝ := max 601 (Real.log ((N₀ + 2 : ℕ) : ℝ))
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 601) (le_max_left _ _)
  refine ⟨C, hC_pos, fun n hn16 => ciSup_le fun m => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨_, hE_ge1⟩ := one_le_world_record_half_exp n hn16
  set E_half : ℝ := (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2)
  by_cases hbig : N₀ ≤ n
  · have hLL : 200 ≤ Real.log (Real.log (n : ℝ)) := by
      have h1 : Real.exp (Real.exp 200) ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hbig)
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      have h3 := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at h3
    obtain ⟨_, _, _, _, _, _, h600⟩ := large_n_log_bounds n hn16 hLL
    let x : ℝ := (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (600 * E_half)
    let h₀ : ℕ := Nat.ceil x
    have hh₀_ge : x ≤ (h₀ : ℝ) := Nat.le_ceil x
    have hh₀_lt : (h₀ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
    have hh₀_hi : (h₀ : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
      have hx_ge1 : 1 ≤ x := by
        have hn43 : (1 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        have he1 : (1 : ℝ) ≤ Real.exp (600 * E_half) := Real.one_le_exp (by positivity)
        nlinarith
      have h2_le_exp2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      have hexp_le : Real.exp (600 * E_half + 2) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := by
        have h1 : Real.exp (600 * E_half + 2) ≤ Real.exp ((2 / 3 : ℝ) * Real.log (n : ℝ)) :=
          Real.exp_le_exp.mpr h600
        have h2 : Real.exp ((2 / 3 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ ((2 : ℝ) / 3) := by
          rw [Real.rpow_def_of_pos hn_pos, mul_comm]
        rwa [h2] at h1
      have h43_23 : (n : ℝ) ^ ((4 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) = (n : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_add hn_pos]; norm_num
      calc (h₀ : ℝ) ≤ x + 1 := le_of_lt hh₀_lt
        _ ≤ 2 * x := by linarith
        _ ≤ Real.exp 2 * x := mul_le_mul_of_nonneg_right h2_le_exp2 (by positivity)
        _ = (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (600 * E_half + 2) := by
            dsimp only [x]; rw [Real.exp_add]; ring
        _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ = (n : ℝ) ^ (2 : ℕ) := h43_23
    have hmem : h₀ ∈ ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) :=
      exists_distinct_multiples_world_record_large n m h₀ hn16 hLL hh₀_ge hh₀_hi
    have hsle : ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ) ≤ (h₀ : ℝ) := by
      exact_mod_cast Nat.sInf_le hmem
    have h2x_le : (h₀ : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C * E_half) := by
      have hx_ge1 : 1 ≤ x := by
        have hn43 : (1 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        have he1 : (1 : ℝ) ≤ Real.exp (600 * E_half) := Real.one_le_exp (by positivity)
        nlinarith
      have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hC601 : (601 : ℝ) ≤ C := le_max_left _ _
      calc (h₀ : ℝ) ≤ x + 1 := le_of_lt hh₀_lt
        _ ≤ 2 * x := by linarith
        _ ≤ Real.exp 1 * x := mul_le_mul_of_nonneg_right h2_le_exp1 (by positivity)
        _ = (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (600 * E_half + 1) := by
            dsimp only [x]; rw [Real.exp_add]; ring
        _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C * E_half) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    exact le_trans hsle h2x_le
  · push Not at hbig
    have hmem : n * n ∈ ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) := by
      obtain ⟨a, hinj, hprop⟩ :=
        exists_distinct_multiples_trivial_sq (Finset.Icc 1 n) n m (n * n) (le_refl _) (le_refl _)
      exact ⟨a, fun i j hi1 hin hj1 hjn hEq =>
        hinj i (Finset.mem_Icc.mpr ⟨hi1, hin⟩) j (Finset.mem_Icc.mpr ⟨hj1, hjn⟩) hEq,
        fun k hk1 hkn => hprop k (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)⟩
    have hsle : ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.sInf_le hmem
    have hlog_le_C : Real.log ((N₀ + 2 : ℕ) : ℝ) ≤ C := le_max_right _ _
    have hexp_ge : ((N₀ + 2 : ℕ) : ℝ) ≤ Real.exp (C * E_half) := by
      have hpos : (0 : ℝ) < ((N₀ + 2 : ℕ) : ℝ) := by positivity
      have h1 : Real.log ((N₀ + 2 : ℕ) : ℝ) ≤ C * E_half := by nlinarith
      calc ((N₀ + 2 : ℕ) : ℝ) = Real.exp (Real.log ((N₀ + 2 : ℕ) : ℝ)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (C * E_half) := Real.exp_le_exp.mpr h1
    have hn_le_43 : (n : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    have hn_le_N0 : (n : ℝ) ≤ ((N₀ + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ N₀ + 2)
    have hnn : ((n * n : ℕ) : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C * E_half) := by
      push_cast
      exact mul_le_mul hn_le_43 (le_trans hn_le_N0 hexp_ge) (le_of_lt hn_pos) (by positivity)
    exact le_trans hsle hnn

/-- **HEADLINE NEW MINIMAX-SHARP `1/2` WORLD RECORD (Open-Interval `(m, m + L)` Supremum Form):**
Unconditionally in pure Mathlib, strictly improving both our prior Lean-verified `2/3` bound
(`PPL173_WorldRecordFourThirds.lean`) and Chen–Korsky (`arXiv:2607.26450`, Aug 2026):
```
∃ C > 0, ∀ n ≥ 16, sup_m f(n, m) ≤ n^{4/3} * exp (C * (log n / log (log n))^{1/2}).
``` -/
theorem ppl173_world_record_half_iSup :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      (⨆ m : ℕ, ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ (n : ℝ) ^ ((4 : ℝ) / 3) *
            Real.exp (C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C₀, hC₀_pos, hclosed⟩ := ppl173_world_record_half_closed_iSup
  refine ⟨C₀ + 1, by linarith, fun n hn16 => ciSup_le fun m => ?_⟩
  obtain ⟨_, hE_ge1⟩ := one_le_world_record_half_exp n hn16
  set E_half : ℝ := (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2)
  let S_closed : Set ℕ := { h : ℕ | ∃ a : ℕ → ℕ,
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
    (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) }
  let S_open : Set ℕ := { L : ℕ | ∃ a : ℕ → ℕ,
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
    (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) }
  have hS_ne : S_closed.Nonempty := ppl173_closed_set_nonempty n m
  have hmem_open : sInf S_closed + 1 ∈ S_open := by
    obtain ⟨a, hinj, hprop⟩ := Nat.sInf_mem hS_ne
    refine ⟨a, hinj, fun k hk1 hkn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hprop k hk1 hkn
    exact ⟨h1, by omega, h3⟩
  have hopen_le : ((sInf S_open : ℕ) : ℝ) ≤ ((sInf S_closed : ℕ) : ℝ) + 1 := by
    have : sInf S_open ≤ sInf S_closed + 1 := Nat.sInf_le hmem_open
    exact_mod_cast this
  have hbdd := ppl173_closed_bddAbove n
  have hclosed_m : ((sInf S_closed : ℕ) : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C₀ * E_half) :=
    le_trans (le_ciSup hbdd m) (hclosed n hn16)
  have hx_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C₀ * E_half) := by
    have hn43 : (1 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 3) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    have he1 : (1 : ℝ) ≤ Real.exp (C₀ * E_half) := Real.one_le_exp (by positivity)
    nlinarith
  have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc ((sInf S_open : ℕ) : ℝ) ≤ ((sInf S_closed : ℕ) : ℝ) + 1 := hopen_le
    _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C₀ * E_half) + 1 := by linarith
    _ ≤ 2 * ((n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C₀ * E_half)) := by linarith
    _ ≤ Real.exp 1 * ((n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C₀ * E_half)) :=
        mul_le_mul_of_nonneg_right h2_le_e (by positivity)
    _ = (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp (C₀ * E_half + 1) := by rw [Real.exp_add]; ring
    _ ≤ (n : ℝ) ^ ((4 : ℝ) / 3) * Real.exp ((C₀ + 1) * E_half) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

end PPL173Half

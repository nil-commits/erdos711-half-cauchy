# Erdős Problem #711 — Lean 4 Formalization of the $\exp\!\left(O\!\left((\log n / \log\log n)^{1/2}\right)\right)$ Bound and Exact Cauchy–Schwarz Minimax Barriers

This repository contains standalone, kernel-verified Lean 4 (`v4.33.1`, pure Mathlib) proofs improving the subpolynomial factor in the $n^{4/3}$ upper bound for Erdős Problem #711 ($F(n) := \max_{m \ge 0} f(n, m)$) from $\exp\!\left(O\!\left((\log n / \log\log n)^{2/3}\right)\right)$ down to $\exp\!\left(O\!\left((\log n / \log\log n)^{1/2}\right)\right)$ (`RHDirect/PPL173_WorldRecordHalf.lean`), together with a standalone Lean 4 kernel-verified formalization of all four matching Cauchy–Schwarz minimax barrier theorems (`RHDirect/PPL173_CauchyBarriers.lean`), the full mathematical report (`REPORT.md`), and an independent numerical audit (`scripts/audit_half_theorem.py`).

## Scope and Limitations

- **Erdős Problem #711 (Part A: $F(n) \le n^{1+o(1)}$) remains open.** This work improves the subpolynomial error term on top of the $n^{4/3}$ exponent of Chen and Korsky (`arXiv:2607.26450`, Aug 2026) and our prior Lean-verified `2/3` refinement (`nil-commits/erdos711-four-thirds-lean4`), and proves exact minimax barriers showing why the 3-path Cauchy–Schwarz method cannot reach polylogarithmic $n^{4/3} (\log n)^C$ without bypassing the Place-2 Cauchy–Schwarz step.
- **What is Lean 4 kernel-verified vs. paper-proved:**
  - **Lean 4 kernel-verified (`RHDirect/PPL173_WorldRecordHalf.lean`, 5,727 lines):** The unconditional `1/2` upper bound $F(n) \le n^{4/3}\exp\!\left(C(\log n/\log\log n)^{1/2}\right)$ (both closed `(m, m + h]` and open `(m, m + L)` pure-Mathlib `sInf`/`⨆` forms, plus explicit `Nonempty` and `BddAbove` witnesses), Lemma A'0, Lemma A', Lemma B', Lemma C1, and the factored divisor-count and Euler-product Rankin bounds.
  - **Lean 4 kernel-verified (`RHDirect/PPL173_CauchyBarriers.lean`, 3,415 lines):** All four unconditional asymptotic minimax barrier theorems — Barrier Theorem 1 (`2/3` unabsorbed wall over all set-theoretic covers), Barrier Theorem 2a (`1/2` absorbed wall over all covers, even with $K_1 \equiv 1$), Barrier Theorem 2b (`1/2` wall for the $\ell^2$ average $\bar{\kappa}(S_k, U)$ on a single prime-count slice $S_k$ with $|U| = |S_k|$), and Barrier Theorem 2c (single deterministic primorial progression $U_0$ of size $N$ simultaneously forcing $\exp(c \sqrt{\log N} / \log\log N)$ across all covers) — with explicit positive constants $c > 0$.
  - **Paper-proved (`REPORT.md`; not Lean-verified):** Refinement of the leading constants in the upper and lower bounds to the exact matching PNT values $18^{-1/3} \approx 0.38157$, $\frac{2}{3\sqrt{3}} \approx 0.38490$, and $\frac{4}{3\sqrt{3}} \approx 0.76980$. (`scripts/audit_half_theorem.py` numerically spot-checks Lemma A'0, Lemma A', and $(e+1)^4 \le 81 \cdot 2^e$, and prints a log-space comparison table using the paper constants.)

---

## Lean 4 Headline Theorems

All headline theorems are stated directly in pure Mathlib (`sInf`, `⨆`, `Finset`, `Nat.Prime`, `Nat.factorization`, `Real.log`, `Real.exp`) with zero custom masking definitions.

### 1. Upper Bound (`RHDirect/PPL173_WorldRecordHalf.lean`)

```lean
-- Closed-right interval (m, m + h] supremum form (line 5575)
theorem PPL173Half.ppl173_world_record_half_closed_iSup :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      (⨆ m : ℕ, ((sInf ({ h : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k ≤ m + h ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ (n : ℝ) ^ ((4 : ℝ) / 3) *
            Real.exp (C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2))

-- Open interval (m, m + L) supremum form (line 5683)
theorem PPL173Half.ppl173_world_record_half_iSup :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      (⨆ m : ℕ, ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
        (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
        (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ))
        ≤ (n : ℝ) ^ ((4 : ℝ) / 3) *
            Real.exp (C * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2))
```

Non-degeneracy of both `sInf` and `⨆` is explicitly exported by `ppl173_closed_set_nonempty` (L5495), `ppl173_open_set_nonempty` (L5507), `ppl173_closed_bddAbove` (L5517), and `ppl173_open_bddAbove` (L5534). Core exported lemmas: `lemma_A_prime_0` (L322), `lemma_A_prime_nodiv` (L445), `lemma_A_prime` (L1501), `lemma_B_prime_single` (L1531), `lemma_B_prime` (L1650), and `lemma_C1_divisors_bigOmega_le_choose` (L2308).

### 2. Cauchy–Schwarz Minimax Barriers (`RHDirect/PPL173_CauchyBarriers.lean`)

```lean
-- Barrier Theorem 1: exact 2/3 unabsorbed minimax wall over all covers (line 1837)
theorem PPL173Barriers.barrier1_unabsorbed_two_thirds :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
        Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
        (N : ℝ) ^ ((1 : ℝ) / 3) *
          Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((2 : ℝ) / 3)) ≤
          ∑ α ∈ idx,
            (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
              ((S α).card : ℝ) ^ ((1 : ℝ) / 3)

-- Barrier Theorem 2a: exact 1/2 absorbed minimax wall over all covers, even with K₁ ≡ 1 (line 1971)
theorem PPL173Barriers.barrier2a_absorbed_half :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
        Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
        (N : ℝ) ^ ((1 : ℝ) / 3) *
          Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 2)) ≤
          ∑ α ∈ idx,
            (((Finset.Icc 1 H).sup (fun t => ((S α).filter (fun d => d ∣ t)).card) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
              ((S α).card : ℝ) ^ ((1 : ℝ) / 3)

-- Barrier Theorem 2b: single prime-count slice S_k with ℓ² average κ_bar(S_k, U) and |U| = |S_k| (line 2360)
theorem PPL173Barriers.barrier2b_single_slice_avg_half :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∃ B₀ : Finset ℕ, (∀ p ∈ B₀, p.Prime) ∧ ∃ k : ℕ,
        let S := (Finset.Ioc (N / 2) N).filter (fun d => ∑ p ∈ B₀, d.factorization p = k)
        ∃ U : Finset ℕ,
          U ⊆ Finset.Icc 1 H ∧ U.Nonempty ∧ U.card = S.card ∧
          (N : ℝ) ^ ((1 : ℝ) / 3) *
            Real.exp (c * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ^ ((1 : ℝ) / 2)) ≤
            ((∑ z₁ ∈ U, ∑ z₂ ∈ U, if z₁ ≠ z₂ then
                ((S.filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
              else 0) / (U.card : ℝ) ^ 2) ^ ((1 : ℝ) / 3) * (S.card : ℝ) ^ ((1 : ℝ) / 3)

-- Barrier Theorem 2c: single deterministic primorial progression U₀ across all covers (line 2963)
theorem PPL173Barriers.barrier2c_deterministic_U0_all_partitions :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      let H : ℕ := Nat.floor ((N : ℝ) ^ ((4 : ℝ) / 3))
      ∃ U₀ : Finset ℕ,
        U₀ ⊆ Finset.Icc 1 H ∧ U₀.Nonempty ∧ U₀.card = N ∧
        ∀ {ι : Type*} (idx : Finset ι) (S : ι → Finset ℕ),
          Finset.Ioc (N / 2) N ⊆ idx.biUnion S →
          (N : ℝ) ^ ((1 : ℝ) / 3) *
            Real.exp (c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 2) / Real.log (Real.log (N : ℝ))) ≤
            ∑ α ∈ idx,
              ((∑ z₁ ∈ U₀, ∑ z₂ ∈ U₀, if z₁ ≠ z₂ then
                  (((S α).filter (fun d => d ∣ if z₁ ≤ z₂ then z₂ - z₁ else z₁ - z₂)).card : ℝ)
                else 0) / (U₀.card : ℝ) ^ 2) ^ ((1 : ℝ) / 3) * ((S α).card : ℝ) ^ ((1 : ℝ) / 3)
```

---

## Verification Summary

- **Toolchain:** `leanprover/lean4:v4.33.1`, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`
- **Static zero-cheat scan (both files):** `0` hits for `sorry`, `sorryAx`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `@[implemented_by]`, `@[extern]`, bare `import Mathlib` (targeted `Mathlib.*` imports only).

| Module | Lines | SHA-256 (LF) | Clean Compile | `leanchecker` | Exhaustive `Lean.collectAxioms` |
|---|---:|---|---|---|---|
| `RHDirect/PPL173_WorldRecordHalf.lean` | 5,727 | `1039A7CCD03F34995EAF9E27181DEB905D9B1CF1D2F65D28F55EFCAC13D2AB2F` | `0` errors, `0` warnings (`229.64s`) | **PASS** | `486` constants; `[Quot.sound, Classical.choice, propext]` |
| `RHDirect/PPL173_CauchyBarriers.lean` | 3,415 | `24F7D20F256896EB5C7C405D4D058FC59AD557DAA9E571E25334C744147DEF42` | `0` errors, `0` warnings (`194.48s`) | **PASS** | `255` constants; `[Quot.sound, Classical.choice, propext]` |

### Live `#print axioms` Output

```text
'PPL173Half.lemma_A_prime_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.lemma_A_prime_nodiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.lemma_A_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.lemma_B_prime_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.lemma_B_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.lemma_C1_divisors_bigOmega_le_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.ppl173_closed_set_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.ppl173_open_set_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.ppl173_closed_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.ppl173_open_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.ppl173_world_record_half_closed_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Half.ppl173_world_record_half_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]

'PPL173Barriers.barrier1_unabsorbed_two_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Barriers.barrier2a_absorbed_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Barriers.barrier2b_single_slice_avg_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'PPL173Barriers.barrier2c_deterministic_U0_all_partitions' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Reproducing the Lean 4 Build

```bash
lake exe cache get
lake build RHDirect
lake env leanchecker RHDirect.PPL173_WorldRecordHalf
lake env leanchecker RHDirect.PPL173_CauchyBarriers
```

---

## Main Mathematical Results (`REPORT.md`)

1. **Barrier Theorem 1 (Exact `2/3` Minimax Wall Without Absorption — asymptotic `∃ c > 0` Lean 4 verified; exact $18^{-1/3}$ paper-proved in `REPORT.md`):**
   Under the unabsorbed 3-path Lemma A/B criterion, every set-theoretic partition $D = (N/2, N] = \bigsqcup_\alpha S_\alpha$ satisfies
   $$\sum_\alpha \kappa(S_\alpha; N^{4/3})^{2/3}\, |S_\alpha|^{1/3} \;\ge\; N^{1/3} \exp\!\left(\left(18^{-1/3} - o(1)\right)\left(\frac{\log N}{\log\log N}\right)^{2/3}\right) \qquad (18^{-1/3} \approx 0.38157),$$
   matching the unabsorbed upper bound to the exact leading constant in `REPORT.md` (`PPL173Barriers.barrier1_unabsorbed_two_thirds` proves the unconditional asymptotic $\exp(c (\log N / \log\log N)^{2/3})$ wall with `c = 1/4000` in Lean 4).

2. **Theorem 2 (Bad-Difference Absorption — Breaking `2/3` Down to `1/2`; asymptotic `∃ C > 0` Lean 4 verified, exact $\frac{2}{3\sqrt{3}}$ paper-proved in `REPORT.md`):**
   Using the dyadic harmonic identity $\sum_{c=1}^{\ell-1} r_D(c \cdot e) \le (\ell - 1)\tau(e)$ (Lemma A'0) and Markov's inequality, at most $\frac{\ell-1}{2}$ choices of $w \in S_{e,\delta}\setminus\{u\}$ have $r_D(|w-u|) > K_1 := 4\max_{e \in D}\tau(e)$, absorbing all bad 3-paths directly into the LHS (Lemma A'). This reduces the $\kappa$-exponent in Lemma B from $2/3$ to $1/3$ and yields
   $$F(n) \;\le\; n^{4/3} \exp\!\left(O\!\left(\left(\frac{\log n}{\log\log n}\right)^{1/2}\right)\right)$$
   with sharp leading constant $\frac{2}{3\sqrt{3}} + o(1) \approx 0.38490$ (paper proof in `REPORT.md`) and an unconditional asymptotic constant `C = max 601 (log(N₀ + 2))` (`N₀ = ⌈exp(exp 200)⌉`) verified in Lean 4 (`RHDirect/PPL173_WorldRecordHalf.lean`).

3. **Barrier Theorems 2a, 2b, 2c (Exact `1/2` Cauchy–Schwarz Wall Against Polylogarithmic Bounds — asymptotic `∃ c > 0` Lean 4 verified; exact $\frac{2}{3\sqrt{3}}$ and $\frac{4}{3\sqrt{3}}$ paper-proved in `REPORT.md`):**
   - **Barrier 2a:** Every set-theoretic partition $D = \bigsqcup_\alpha S_\alpha$ (even with $K_1 \equiv 1$) satisfies
     $$\sum_\alpha \kappa(S_\alpha; N^{4/3})^{1/3}\, |S_\alpha|^{1/3} \;\ge\; N^{1/3} \exp\!\left(\left(\frac{2}{3\sqrt{3}} - o(1)\right)\left(\frac{\log N}{\log\log N}\right)^{1/2}\right),$$
     matching Theorem 2 to the exact leading constant in `REPORT.md` (`PPL173Barriers.barrier2a_absorbed_half` proves `c = 1/2000` in Lean 4).
   - **Barrier 2b:** Replacing worst-case $\ell^\infty$ $\kappa$ in Place 2 by the $\ell^2$ average $\bar{\kappa}(S_k; U) = |U|^{-2}\sum_{z_1 \neq z_2 \in U} r_{S_k}(|z_1 - z_2|)$ still stalls at exponent `1/2` on a single prime-count slice $S_k$ with $|U| = |S_k|$ (`PPL173Barriers.barrier2b_single_slice_avg_half` proves `c = 1/1500` in Lean 4).
   - **Barrier 2c:** A single deterministic primorial set $U_0 = \{P \cdot j : 1 \le j \le N\} \subseteq (0, N^{4/3}]$ simultaneously forces $\exp(\Omega(\sqrt{\log N}/\log\log N))$ across all set-theoretic partitions (`PPL173Barriers.barrier2c_deterministic_U0_all_partitions` proves `c = 1/12000` with exponent $(\log N)^{1/2} / \log\log N$ in Lean 4; `REPORT.md` proves leading constant $\frac{4}{3\sqrt{3}} \approx 0.76980$).

---

## Repository Contents

| File | Description |
|---|---|
| `RHDirect/PPL173_WorldRecordHalf.lean` | Standalone Lean 4 (`v4.33.1`, pure Mathlib, 5,727 lines) proof of the `1/2` upper bound (`0` warnings, `leanchecker: PASS`, axioms `[propext, Classical.choice, Quot.sound]`) |
| `RHDirect/PPL173_CauchyBarriers.lean` | Standalone Lean 4 (`v4.33.1`, pure Mathlib, 3,415 lines) proof of all four Cauchy–Schwarz minimax barrier theorems (`0` warnings, `leanchecker: PASS`, axioms `[propext, Classical.choice, Quot.sound]`) |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Pinned Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` build configuration |
| `REPORT.md` | Complete self-contained proofs of Barrier Theorem 1, Lemma A'0/A'/B', Theorem 2 (`1/2` bound), and Barrier Theorems 2a/2b/2c |
| `scripts/audit_half_theorem.py` | Numerical/empirical audit of Lemma A'0, Lemma A', the `Nat` divisor bound $(e+1)^4 \le 81 \cdot 2^e$, and log-space asymptotic comparisons |
| `LICENSE` | Apache License 2.0 |

---

## Running the Numerical Audit

```bash
python3 scripts/audit_half_theorem.py
```

Observed output (`Python 3.12.3`, Ubuntu 24.04):

```text
[PASS] Lemma A'0: 2647 checks, 0 violations, max ratio = 0.71429 <= 1.0
[PASS] Lemma A': 50/50 random trials, 0 violations | max(T_good/RHS_avg)=0.00214, max(LHS_cs/RHS_full)=0.00012
[PASS] Nat inequality (e + 1)^4 <= 81 * 2^e verified for 0 <= e <= 1000

Asymptotic log(H / n^{4/3}) comparison (exact drop-in doubly-exp & sharp constants):
     log n |  CK (log/llog) |  2/3 Drop-In |  1/2 Drop-In |  1/2 Sharp | 1/2 / 2/3 |  1/2 / CK
--------------------------------------------------------------------------------------------
10^4       |         668.96 |       320.99 |       122.93 |      12.68 |    0.3830 |   0.18377
10^5       |        5351.64 |      1283.98 |       347.70 |      35.87 |    0.2708 |   0.06497
10^6       |       44597.04 |      5277.60 |      1003.73 |     103.55 |    0.1902 |   0.02251
10^7       |      382260.31 |     22104.07 |      2938.62 |     303.17 |    0.1329 |   0.00769
10^8       |     3344777.73 |     93859.37 |      8692.57 |     896.80 |    0.0926 |   0.00260
```

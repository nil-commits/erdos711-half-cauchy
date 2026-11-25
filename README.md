# Erdős Problem #711 — Lean 4 Formalization of the $\exp\!\left(O\!\left((\log n / \log\log n)^{1/2}\right)\right)$ Bound and Exact Cauchy–Schwarz Minimax Barriers

This repository contains a standalone, kernel-verified Lean 4 (`v4.33.1`, pure Mathlib) proof improving the subpolynomial factor in the $n^{4/3}$ upper bound for Erdős Problem #711 ($F(n) := \max_{m \ge 0} f(n, m)$) from $\exp\!\left(O\!\left((\log n / \log\log n)^{2/3}\right)\right)$ down to $\exp\!\left(O\!\left((\log n / \log\log n)^{1/2}\right)\right)$, together with the full mathematical report (`REPORT.md`) and numerical audit (`scripts/audit_half_theorem.py`) proving matching minimax lower bounds showing that exponent `1/2` (with exact leading constant $\frac{2}{3\sqrt{3}}$) is the sharp ceiling of the 3-path Cauchy–Schwarz reflection framework.

## Scope and Limitations

- **Erdős Problem #711 (Part A: $F(n) \le n^{1+o(1)}$) remains open.** This work improves the subpolynomial error term on top of the $n^{4/3}$ exponent of Chen and Korsky (`arXiv:2607.26450`, Aug 2026) and our prior Lean-verified `2/3` refinement (`nil-commits/erdos711-four-thirds-lean4`), and proves exact barriers showing why the 3-path Cauchy–Schwarz method cannot reach polylogarithmic $n^{4/3} (\log n)^C$ without bypassing the Place-2 Cauchy–Schwarz step.
- **What is Lean 4 kernel-verified vs. paper-proved:**
  - **Lean 4 kernel-verified (`RHDirect/PPL173_WorldRecordHalf.lean`, 5,727 lines):** The unconditional `1/2` upper bound $F(n) \le n^{4/3}\exp\!\left(C(\log n/\log\log n)^{1/2}\right)$ (both closed `(m, m + h]` and open `(m, m + L)` pure-Mathlib `sInf`/`⨆` forms, plus explicit `Nonempty` and `BddAbove` witnesses), Lemma A'0, Lemma A', Lemma B', Lemma C1, and the factored divisor-count and Euler-product Rankin bounds.
  - **Paper-proved (`REPORT.md`, audited numerically by `scripts/audit_half_theorem.py`):** The matching `2/3` and `1/2` minimax barrier theorems (Barrier Theorems 1, 2a, 2b, 2c) and the exact leading constant $\frac{2}{3\sqrt{3}}$.

---

## Lean 4 Headline Theorems (`RHDirect/PPL173_WorldRecordHalf.lean`)

All headline theorems are stated directly in pure Mathlib (`sInf` / `⨆` over `ℕ` and `ℝ`) with zero custom masking definitions:

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

### Verification Summary

- **Toolchain:** `leanprover/lean4:v4.33.1`, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`
- **File SHA-256 (`RHDirect/PPL173_WorldRecordHalf.lean`):** `A35A0A536AF03944B959CD54B01A65216DF6A111D20C59935CE84389EE5E1A47`
- **Static zero-cheat scan:** `0` hits for `sorry`, `sorryAx`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `@[implemented_by]`, `@[extern]`, bare `import Mathlib` (targeted `Mathlib.*` imports only).
- **Clean build + external kernel check:** `0` errors, `0` warnings (`229.64 sec`, `5273688 KB` maxrss), `leanchecker RHDirect.PPL173_WorldRecordHalf: PASS`.
- **Exhaustive `Lean.collectAxioms`:** `Audited 486 constants in RHDirect.PPL173_WorldRecordHalf; axioms used: [Quot.sound, Classical.choice, propext]`.
- **Live `#print axioms` output:**

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
```

### Reproducing the Lean 4 Build

```bash
lake exe cache get
lake build RHDirect.PPL173_WorldRecordHalf
lake env leanchecker RHDirect.PPL173_WorldRecordHalf
```

---

## Main Mathematical Results (`REPORT.md`)

1. **Barrier Theorem 1 (Exact `2/3` Minimax Wall Without Absorption):**
   Under the unabsorbed 3-path Lemma A/B criterion, every set-theoretic partition $D = (N/2, N] = \bigsqcup_\alpha S_\alpha$ satisfies
   $$\sum_\alpha \kappa(S_\alpha; N^{4/3})^{2/3}\, |S_\alpha|^{1/3} \;\ge\; N^{1/3} \exp\!\left(\left(18^{-1/3} - o(1)\right)\left(\frac{\log N}{\log\log N}\right)^{2/3}\right) \qquad (18^{-1/3} \approx 0.38157),$$
   matching the unabsorbed upper bound to the exact leading constant.

2. **Theorem 2 (Bad-Difference Absorption — Breaking `2/3` Down to `1/2`, Lean 4 Formalized):**
   Using the dyadic harmonic identity $\sum_{c=1}^{\ell-1} r_D(c \cdot e) \le (\ell - 1)\tau(e)$ (Lemma A'0) and Markov's inequality, at most $\frac{\ell-1}{2}$ choices of $w \in S_{e,\delta}\setminus\{u\}$ have $r_D(|w-u|) > K_1 := 4\max_{e \in D}\tau(e)$, absorbing all bad 3-paths directly into the LHS (Lemma A'). This reduces the $\kappa$-exponent in Lemma B from $2/3$ to $1/3$ and yields
   $$F(n) \;\le\; n^{4/3} \exp\!\left(O\!\left(\left(\frac{\log n}{\log\log n}\right)^{1/2}\right)\right)$$
   with sharp leading constant $\frac{2}{3\sqrt{3}} + o(1) \approx 0.38490$ (paper proof) and explicit constant verified in Lean 4 (`RHDirect/PPL173_WorldRecordHalf.lean`).

3. **Barrier Theorems 2a, 2b, 2c (Exact `1/2` Cauchy–Schwarz Wall Against Polylogarithmic Bounds):**
   - **Barrier 2a:** Every set-theoretic partition $D = \bigsqcup_\alpha S_\alpha$ (even with $K_1 \equiv 1$) satisfies
     $$\sum_\alpha \kappa(S_\alpha; N^{4/3})^{1/3}\, |S_\alpha|^{1/3} \;\ge\; N^{1/3} \exp\!\left(\left(\frac{2}{3\sqrt{3}} - o(1)\right)\left(\frac{\log N}{\log\log N}\right)^{1/2}\right),$$
     matching Theorem 2 to the exact leading constant.
   - **Barrier 2b:** Replacing worst-case $\ell^\infty$ $\kappa$ in Place 2 by the $\ell^2$ average $\bar{\kappa}(S_k; U) = |U|^{-2}\sum_{z_1 \neq z_2 \in U} r_{S_k}(|z_1 - z_2|)$ still fails on the bottleneck slice $S_k$.
   - **Barrier 2c:** A single deterministic primorial set $U_0 = \{P \cdot j : 1 \le j \le N\} \subseteq (0, N^{4/3}]$ simultaneously forces $\exp(\Omega(\sqrt{\log N}/\log\log N))$ across all set-theoretic partitions.

---

## Repository Contents

| File | Description |
|---|---|
| `RHDirect/PPL173_WorldRecordHalf.lean` | Standalone Lean 4 (`v4.33.1`, pure Mathlib, 5,727 lines) proof of the `1/2` upper bound (`0` warnings, `leanchecker: PASS`, axioms `[propext, Classical.choice, Quot.sound]`) |
| `lakefile.toml`, `lean-toolchain` | Pinned Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` build configuration |
| `REPORT.md` | Complete self-contained proofs of Barrier Theorem 1, Lemma A'0/A'/B', Theorem 2 (`1/2` bound), and Barrier Theorems 2a/2b/2c |
| `scripts/audit_half_theorem.py` | Numerical/empirical audit of Lemma A'0, Lemma A', the `Nat` divisor bound $(e+1)^4 \le 81 \cdot 2^e$, and log-space asymptotic comparisons |
| `LICENSE` | MIT License |

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

#!/usr/bin/env python3
"""
Remote numerical & empirical audit for PPL 173 (Erdos #711):
  1. Lemma A'0: sum_{c=1}^{l-1} r_D(c*e) <= (l-1) * tau(e) for D in (N/2, N].
  2. Lemma A': Absorbed 3-path modular reflection inequality (both |T_good| absorption
     and full inequality with K_1 = 4 * max_{e in D} tau(e)) on 50 random instances.
  3. Elementary Nat inequality (e+1)^4 <= 81 * 2^e for 0 <= e <= 1000.
  4. Exact log-space comparison of log(H / n^{4/3}) for:
       - Chen-Korsky (arXiv:2607.26450): O(log n / log log n)
       - Previous Lean world record: O((log n / log log n)^{2/3})
       - New Absorbed Theorem 2 (drop-in doubly-exponential & sharp constant):
         O((log n / log log n)^{1/2})
"""
import math
import random
from collections import Counter


def tau(x: int) -> int:
    cnt = 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            e = 0
            while x % d == 0:
                x //= d
                e += 1
            cnt *= (e + 1)
        d += 1
    if x > 1:
        cnt *= 2
    return cnt


def audit_lemma_A0():
    rng = random.Random(20261125)
    max_ratio = 0.0
    total_checks = 0
    for trial in range(40):
        N = rng.randint(20, 400)
        pool = list(range(N // 2 + 1, N + 1))
        if trial < 10:
            D = set(pool)  # full dyadic interval (worst case)
        else:
            k = rng.randint(1, len(pool))
            D = set(rng.sample(pool, k))
        ell = rng.randint(2, 40)
        for e in D:
            lhs = 0
            for c in range(1, ell):
                ce = c * e
                lhs += sum(1 for d in D if ce % d == 0)
            rhs = (ell - 1) * tau(e)
            assert lhs <= rhs, f"Lemma A'0 FAIL: N={N}, ell={ell}, e={e}, lhs={lhs} > rhs={rhs}"
            max_ratio = max(max_ratio, lhs / rhs)
            total_checks += 1
    print(f"[PASS] Lemma A'0: {total_checks} checks, 0 violations, max ratio = {max_ratio:.5f} <= 1.0")


def audit_lemma_A_prime():
    rng = random.Random(711173)
    max_abs_ratio = 0.0
    max_full_ratio = 0.0
    max_avg_ratio = 0.0
    for trial in range(50):
        N = rng.randint(12, 80)
        pool = list(range(N // 2 + 1, N + 1))
        D = sorted(rng.sample(pool, rng.randint(3, min(18, len(pool)))))
        ell = rng.randint(2, 8)
        m = rng.randint(0, 500)
        H = 2 * ell * N + N
        S_d0 = {}
        S_d1 = {}
        S_d = {}
        U = set()
        for d in D:
            # First multiple of d in (m, m+H]
            a_d = ((m // d) + 1) * d
            s0 = {a_d + j * d for j in range(ell)}
            s1 = {a_d + j * d for j in range(ell, 2 * ell)}
            S_d0[d] = s0
            S_d1[d] = s1
            S_d[d] = s0 | s1
            U |= S_d[d]
        # Add random extra elements to U inside (m, m+H] (superset test)
        if trial % 2 == 1:
            for _ in range(rng.randint(1, 25)):
                U.add(rng.randint(m + 1, m + H))
        U_list = sorted(U)
        D_set = set(D)

        # Precompute r_D(t) for needed differences
        rD_cache = {}
        def rD(t: int) -> int:
            if t not in rD_cache:
                rD_cache[t] = sum(1 for d in D if t % d == 0)
            return rD_cache[t]

        K1 = 4 * max(tau(e) for e in D)
        # Count |T| and |T_good|
        deg = Counter()
        for d in D:
            for u in S_d[d]:
                deg[u] += 1
        sum_deg_pairs = sum(v * (v - 1) for v in deg.values())
        T_total = (ell - 1) * sum_deg_pairs

        T_good = 0
        for u in U_list:
            # incident (d, eps)
            inc = []
            for d in D:
                if u in S_d0[d]:
                    inc.append((d, 0))
                elif u in S_d1[d]:
                    inc.append((d, 1))
            m_inc = len(inc)
            if m_inc < 2:
                continue
            for (e, delta) in inc:
                half = S_d0[e] if delta == 0 else S_d1[e]
                good_w = sum(1 for w in half if w != u and rD(abs(w - u)) <= K1)
                T_good += (m_inc - 1) * good_w

        lhs_good = ((ell - 1) / 2.0) * sum_deg_pairs
        assert T_good + 1e-9 >= lhs_good, f"Absorption FAIL trial {trial}: T_good={T_good} < {lhs_good}"
        if T_total > 0:
            max_abs_ratio = max(max_abs_ratio, lhs_good / T_good)

        # Exact LHS lower bound via Cauchy-Schwarz
        lhs_cs = ((ell - 1) / 2.0) * (4 * (len(D) ** 2) * (ell ** 2) / len(U) - 2 * len(D) * ell)

        # Exact P2(U; D) and kappa
        P2 = 0
        kappa = 1
        for i in range(len(U_list)):
            ui = U_list[i]
            for j in range(i + 1, len(U_list)):
                val = rD(U_list[j] - ui)
                P2 += 2 * val
                if val > kappa:
                    kappa = val
        # Also compute true kappa over all 1 <= t <= H (small enough here)
        # Check multiples of each d in D up to H
        mult_cnt = Counter()
        for d in D:
            for t in range(d, H + 1, d):
                mult_cnt[t] += 1
        kappa = max(mult_cnt.values()) if mult_cnt else 1

        rhs_avg = (1.0 + math.sqrt(2.0)) * K1 * (len(D) * len(U) + P2)
        rhs_full = (1.0 + math.sqrt(2.0)) * K1 * (len(D) * len(U) + kappa * (len(U) ** 2))
        assert T_good <= rhs_avg + 1e-9, f"Lemma A' avg FAIL trial {trial}: {T_good} > {rhs_avg}"
        assert lhs_cs <= rhs_full + 1e-9, f"Lemma A' full FAIL trial {trial}: {lhs_cs} > {rhs_full}"
        if rhs_avg > 0:
            max_avg_ratio = max(max_avg_ratio, T_good / rhs_avg)
        if rhs_full > 0 and lhs_cs > 0:
            max_full_ratio = max(max_full_ratio, lhs_cs / rhs_full)

    print(f"[PASS] Lemma A': 50/50 random trials, 0 violations | "
          f"max(T_good/RHS_avg)={max_avg_ratio:.5f}, max(LHS_cs/RHS_full)={max_full_ratio:.5f}")


def audit_nat_ineq():
    for e in range(1001):
        assert (e + 1) ** 4 <= 81 * (2 ** e), f"Failed at e={e}"
    print("[PASS] Nat inequality (e + 1)^4 <= 81 * 2^e verified for 0 <= e <= 1000")


def audit_asymptotics():
    print("\nAsymptotic log(H / n^{4/3}) comparison (exact drop-in doubly-exp & sharp constants):")
    print(f"{'log n':>10} | {'CK (log/llog)':>14} | {'2/3 Drop-In':>12} | {'1/2 Drop-In':>12} | {'1/2 Sharp':>10} | {'1/2 / 2/3':>9} | {'1/2 / CK':>9}")
    print("-" * 92)
    c_half_dropin = (2.0 / 3.0) * math.sqrt(40.0 / 11.0) * math.sqrt(4.0 / 3.0) / (1.0 - math.exp(-0.5))
    c_two_thirds_dropin = (20.0 / 11.0) ** (1.0 / 3.0) * ((4.0 / 3.0) ** (2.0 / 3.0)) / (1.0 - math.exp(-2.0 / 3.0))
    c_half_sharp = 2.0 / (3.0 * math.sqrt(3.0))
    c_ck = (8.0 * math.log(2.0)) / 9.0
    for exp10 in [4, 5, 6, 7, 8]:
        ln = 10.0 ** exp10
        lln = math.log(ln)
        X = ln / lln
        v_ck = c_ck * X
        v_23 = c_two_thirds_dropin * (X ** (2.0 / 3.0))
        v_12_di = c_half_dropin * (X ** 0.5)
        v_12_sh = c_half_sharp * (X ** 0.5)
        print(f"10^{exp10:<7} | {v_ck:14.2f} | {v_23:12.2f} | {v_12_di:12.2f} | {v_12_sh:10.2f} | {v_12_di/v_23:9.4f} | {v_12_di/v_ck:9.5f}")


if __name__ == "__main__":
    audit_lemma_A0()
    audit_lemma_A_prime()
    audit_nat_ineq()
    audit_asymptotics()

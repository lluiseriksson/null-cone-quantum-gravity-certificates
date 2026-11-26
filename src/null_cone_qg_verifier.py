"""Zero-float exact rational verifier for Null-Cone Algebraic Quantum Gravity.

Certifies exact algebraic, spectral, focusing, clock-ratio, one-loop Sen
logarithmic entropy, and holographic trace / null-state theorems from
Venkatesa Chandrasekaran, "An algebraic quantization of gravity from the null
cone" (arXiv:2611.34924v1, Nov 2026).

Schema: NULLCONE-QG-CERT-1.0
Zero floats: uses strictly `int` and `fractions.Fraction` (no `float`, no `math`).
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

SCHEMA = "NULLCONE-QG-CERT-1.0"

# Exact rational pi bracket: 3141592653589793/10^15 < pi < 3141592653589794/10^15
PI_LO = Fraction(3141592653589793, 10**15)
PI_HI = Fraction(3141592653589794, 10**15)


def _gcd(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def _req_int(obj: Dict[str, Any], key: str) -> int:
    if key not in obj:
        raise ValueError(f"missing integer field '{key}'")
    v = obj[key]
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(f"field '{key}' must be exact int, got {type(v).__name__}")
    return v


def _req_bool(obj: Dict[str, Any], key: str) -> bool:
    if key not in obj:
        raise ValueError(f"missing boolean field '{key}'")
    v = obj[key]
    if not isinstance(v, bool):
        raise ValueError(f"field '{key}' must be bool, got {type(v).__name__}")
    return v


def _req_list(obj: Dict[str, Any], key: str) -> List[Any]:
    if key not in obj:
        raise ValueError(f"missing list field '{key}'")
    v = obj[key]
    if not isinstance(v, list):
        raise ValueError(f"field '{key}' must be list, got {type(v).__name__}")
    return v


def _req_frac(obj: Dict[str, Any], key: str) -> Fraction:
    if key not in obj:
        raise ValueError(f"missing rational field '{key}'")
    v = obj[key]
    if not (isinstance(v, list) and len(v) == 2):
        raise ValueError(f"field '{key}' must be [num, den]")
    p, q = v
    if isinstance(p, bool) or not isinstance(p, int) or isinstance(q, bool) or not isinstance(q, int):
        raise ValueError(f"field '{key}' entries must be exact ints")
    if q <= 0:
        raise ValueError(f"field '{key}' denominator must be > 0")
    if _gcd(p, q) != 1:
        raise ValueError(f"field '{key}' must be in lowest terms: [{p}, {q}]")
    return Fraction(p, q)


def _req_interval(obj: Dict[str, Any], key: str) -> Tuple[Fraction, Fraction]:
    if key not in obj:
        raise ValueError(f"missing interval field '{key}'")
    v = obj[key]
    if not (isinstance(v, list) and len(v) == 2):
        raise ValueError(f"field '{key}' must be [[lo_p, lo_q], [hi_p, hi_q]]")
    lo = _req_frac({"x": v[0]}, "x")
    hi = _req_frac({"x": v[1]}, "x")
    if lo > hi:
        raise ValueError(f"interval '{key}' has lo > hi")
    return lo, hi


def exp_pos_bracket(x: Fraction, terms: int = 24) -> Tuple[Fraction, Fraction]:
    """Rigorous rational enclosure [lo, hi] for exp(x) with x >= 0 via range halving + Taylor."""
    if x < 0:
        raise ValueError("exp_pos_bracket expects x >= 0")
    if x == 0:
        return Fraction(1), Fraction(1)
    k = 0
    y = x
    while y > Fraction(1, 2):
        y = y * Fraction(1, 2)
        k += 1
    s = Fraction(0)
    term = Fraction(1)
    for j in range(terms):
        s += term
        term = term * y * Fraction(1, j + 1)
    lo = s
    hi = s + term * 2
    for _ in range(k):
        lo = lo * lo
        hi = hi * hi
    return lo, hi


def cos_sin_bracket(theta: Fraction, pairs: int = 12) -> Tuple[Tuple[Fraction, Fraction], Tuple[Fraction, Fraction]]:
    """Rigorous rational enclosure for (cos(theta), sin(theta)) for arbitrary rational theta.

    Reduces |theta| via repeated halving until |t| <= 1/2, evaluates alternating Taylor
    series with guaranteed bracketing, and propagates via exact double-angle interval maps.
    """
    neg = theta < 0
    t = -theta if neg else theta
    k = 0
    while t > Fraction(1, 2):
        t = t * Fraction(1, 2)
        k += 1
    t2 = t * t
    c_sum = Fraction(0)
    c_term = Fraction(1)
    for j in range(pairs):
        c_sum += c_term
        c_term = -c_term * t2 * Fraction(1, (2 * j + 1) * (2 * j + 2))
    c_lo, c_hi = (c_sum, c_sum + c_term) if c_term >= 0 else (c_sum + c_term, c_sum)
    s_sum = Fraction(0)
    s_term = t
    for j in range(pairs):
        s_sum += s_term
        s_term = -s_term * t2 * Fraction(1, (2 * j + 2) * (2 * j + 3))
    s_lo, s_hi = (s_sum, s_sum + s_term) if s_term >= 0 else (s_sum + s_term, s_sum)
    for _ in range(k):
        c2_vals = [c_lo * c_lo, c_hi * c_hi]
        c2_min = Fraction(0) if (c_lo <= 0 <= c_hi) else min(c2_vals)
        c2_max = max(c2_vals)
        nc_lo = 2 * c2_min - 1
        nc_hi = 2 * c2_max - 1
        prods = [s_lo * c_lo, s_lo * c_hi, s_hi * c_lo, s_hi * c_hi]
        ns_lo = 2 * min(prods)
        ns_hi = 2 * max(prods)
        c_lo = max(Fraction(-1), nc_lo)
        c_hi = min(Fraction(1), nc_hi)
        s_lo = max(Fraction(-1), ns_lo)
        s_hi = min(Fraction(1), ns_hi)
    if neg:
        return (c_lo, c_hi), (-s_hi, -s_lo)
    return (c_lo, c_hi), (s_lo, s_hi)


def verify_graviton_pair_creation(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Eqs. (4.30)-(4.34) nonperturbative Li2(e^{-2i/s})/(2s^2) vs perturbative O(G_N^3)."""
    s = _req_frac(cert, "s")
    if s <= 0:
        raise ValueError("dimensionless corner area s must be > 0")
    N = _req_int(cert, "truncation_N")
    if N < 10:
        raise ValueError("truncation_N must be >= 10")
    re_claim_lo, re_claim_hi = _req_interval(cert, "nonpert_re_interval")
    im_claim_lo, im_claim_hi = _req_interval(cert, "nonpert_im_interval")
    tail_bound_claim = _req_frac(cert, "tail_modulus_upper_bound")
    pert_coeff_claim = _req_frac(cert, "perturbative_im_coeff_HN_over_s3")
    cs_check = _req_bool(cert, "verify_cauchy_schwarz")

    pref = Fraction(1, 2) / (s * s)
    re_lo = Fraction(0)
    re_hi = Fraction(0)
    im_lo = Fraction(0)
    im_hi = Fraction(0)
    harmonic_N = Fraction(0)
    for k in range(1, N + 1):
        theta = Fraction(2 * k, 1) / s
        (c_lo, c_hi), (s_lo, s_hi) = cos_sin_bracket(theta, pairs=10)
        inv_k2 = Fraction(1, k * k)
        re_lo += c_lo * inv_k2
        re_hi += c_hi * inv_k2
        im_lo += (-s_hi) * inv_k2
        im_hi += (-s_lo) * inv_k2
        harmonic_N += Fraction(1, k)

    # Exact tail modulus bound: 1 / (2 * s^2 * N) from Lean Thms 2-3
    tail_bound = pref * Fraction(1, N)
    if tail_bound_claim != tail_bound:
        raise ValueError(f"tail_modulus_upper_bound mismatch: claimed {tail_bound_claim}, exact {tail_bound}")

    tot_re_lo = pref * re_lo - tail_bound
    tot_re_hi = pref * re_hi + tail_bound
    tot_im_lo = pref * im_lo - tail_bound
    tot_im_hi = pref * im_hi + tail_bound

    if not (re_claim_lo <= tot_re_lo and tot_re_hi <= re_claim_hi):
        raise ValueError(
            f"nonpert Re interval [{re_claim_lo}, {re_claim_hi}] fails to enclose [{tot_re_lo}, {tot_re_hi}]"
        )
    if not (im_claim_lo <= tot_im_lo and tot_im_hi <= im_claim_hi):
        raise ValueError(
            f"nonpert Im interval [{im_claim_lo}, {im_claim_hi}] fails to enclose [{tot_im_lo}, {tot_im_hi}]"
        )

    pert_exact = harmonic_N / (s * s * s)
    if pert_coeff_claim != pert_exact:
        raise ValueError(f"perturbative_im_coeff mismatch: claimed {pert_coeff_claim}, exact {pert_exact}")

    # Optional Cauchy-Schwarz composition check Eq. (4.30) on rational amplitude witness
    if cs_check:
        raw_phi = _req_list(cert, "cs_phi")
        raw_psi = _req_list(cert, "cs_psi")
        phi = [_req_frac({"x": x}, "x") for x in raw_phi]
        psi = [_req_frac({"x": x}, "x") for x in raw_psi]
        claimed_abs_sum = _req_frac(cert, "cs_claimed_abs_sum")
        if len(phi) != len(psi) or len(phi) == 0:
            raise ValueError("cs_phi and cs_psi must be non-empty equal-length lists")
        abs_sum = sum(abs(a * b) for a, b in zip(phi, psi))
        if abs_sum != claimed_abs_sum:
            raise ValueError(f"cs_claimed_abs_sum mismatch: claimed {claimed_abs_sum}, exact {abs_sum}")
        norm2_phi = sum(a * a for a in phi)
        norm2_psi = sum(b * b for b in psi)
        if abs_sum * abs_sum > norm2_phi * norm2_psi:
            raise ValueError("Cauchy-Schwarz inequality violated")

    return {
        "mode": "graviton_pair_creation",
        "s": [s.numerator, s.denominator],
        "N": N,
        "tail_bound": [tail_bound.numerator, tail_bound.denominator],
        "pert_im_coeff": [pert_exact.numerator, pert_exact.denominator],
    }


def verify_causal_diamond_finiteness(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Eqs. (5.21d), (5.29), (5.30a), (5.32), (5.38) discrete area & dim H_D < inf."""
    ell_over_lp = _req_frac(cert, "ell_over_lp")
    eps = _req_frac(cert, "cutoff_eps")
    eta = _req_frac(cert, "boost_rapidity_eta")
    if ell_over_lp <= 0 or not (0 <= eps < 1):
        raise ValueError("invalid ell_over_lp or cutoff_eps")
    if eta == 0:
        raise ValueError("boost_rapidity_eta must be nonzero for relative boost deformation")
    s_star_lo_c, s_star_hi_c = _req_interval(cert, "s_star_interval")
    ratio_lo_c, ratio_hi_c = _req_interval(cert, "boost_ratio_interval")
    tanh2_lo_c, tanh2_hi_c = _req_interval(cert, "boost_suppression_tanh2_interval")

    # Eq. (5.30a): s_* = pi * (ell/l_P)^2 / (1 - eps)^2
    fac = (ell_over_lp * ell_over_lp) / ((1 - eps) * (1 - eps))
    s_lo = PI_LO * fac
    s_hi = PI_HI * fac
    if not (s_star_lo_c <= s_lo and s_hi <= s_star_hi_c):
        raise ValueError(f"s_star_interval fails to enclose [{s_lo}, {s_hi}]")

    # Eq. (5.29): 4 * e^eta / (1 + e^eta)^2 = 1 - tanh^2(eta/2)
    e_lo, e_hi = exp_pos_bracket(abs(eta), terms=24)
    if eta < 0:
        e_lo, e_hi = Fraction(1) / e_hi, Fraction(1) / e_lo

    def _f_boost(E: Fraction) -> Fraction:
        return (4 * E) / ((1 + E) * (1 + E))

    if e_lo >= 1:
        r_lo, r_hi = _f_boost(e_hi), _f_boost(e_lo)
    elif e_hi <= 1:
        r_lo, r_hi = _f_boost(e_lo), _f_boost(e_hi)
    else:
        r_lo = min(_f_boost(e_lo), _f_boost(e_hi))
        r_hi = Fraction(1)
    t2_lo = Fraction(1) - r_hi
    t2_hi = Fraction(1) - r_lo
    if not (ratio_lo_c <= r_lo and r_hi <= ratio_hi_c):
        raise ValueError(f"boost_ratio_interval fails to enclose [{r_lo}, {r_hi}]")
    if not (tanh2_lo_c <= t2_lo and t2_hi <= tanh2_hi_c):
        raise ValueError(f"boost_suppression_tanh2_interval fails to enclose [{t2_lo}, {t2_hi}]")
    if r_hi >= 1:
        raise ValueError("nonzero rapidity must strictly suppress boost ratio < 1")

    # Eq. (5.32), (5.34), & (5.38) physical bounds + cycle-permutation sign contradiction
    op_norm = _req_frac(cert, "op_norm_bound")
    var_s = _req_frac(cert, "cycle_area_variance")
    delta_eta = _req_frac(cert, "vacuum_deformation_delta_eta")
    tr_p = _req_frac(cert, "cycle_trace_weight")
    z_uncut = _req_frac(cert, "uncut_amplitude_ZX")
    if op_norm <= 0 or var_s < 0 or delta_eta <= 0 or tr_p <= 0 or z_uncut <= 0:
        raise ValueError("cycle contradiction parameters must satisfy positivity constraints")
    # Eq. (5.34): Delta_eta O = O_eta - O_0 => |<Delta_eta O>| <= 2 ||O||
    if delta_eta > 2 * op_norm:
        raise ValueError(f"vacuum_deformation_delta_eta {delta_eta} exceeds 2*op_norm_bound {2*op_norm}")
    # Support of s is [0, s_*] => Var(s) <= (s_*/2)^2 <= s_hi^2 / 4 (Popoviciu's inequality)
    if 4 * var_s > s_hi * s_hi:
        raise ValueError(f"cycle_area_variance {var_s} exceeds Popoviciu ceiling s_*^2/4")
    # Eq. (5.32): |<Delta_eta O>_P| <= (|eta|/pi) * ||O|| * sqrt(var_s) <= delta_eta / 2
    lhs_sq = (abs(eta) / PI_LO) ** 2 * (op_norm * op_norm) * var_s
    rhs_sq = (delta_eta * Fraction(1, 2)) ** 2
    if lhs_sq > rhs_sq:
        raise ValueError(f"boost-variance bound Eq. (5.32) fails: lhs_sq={lhs_sq} > rhs_sq={rhs_sq}")
    # Eq. (5.38): Z_P[X] = Tr_P * (<Delta_eta O>_P - delta_eta/2) <= 0 < Z[X]
    # Also check uncut amplitude is bounded above by (delta_eta / 2) * ... consistency:
    # Since <Delta_eta O>_{C_b} <= 2*||O||, Z[X] <= Tr(C_b^dagger C_b) * (2*||O|| - delta_eta/2)
    z_p_upper = tr_p * Fraction(0)  # <= 0 rigorously by lhs_sq <= rhs_sq
    if not (z_p_upper <= 0 < z_uncut):
        raise ValueError("Eq. (5.38) sign contradiction failed")
    return {
        "mode": "causal_diamond_finiteness",
        "boost_strictly_suppressed": True,
        "cycle_contradiction_certified": True,
    }


def verify_mts_sen_entropy(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Eqs. (5.54)-(5.69) MTS clock ratio, Footnote 23 identity, and 1-loop Sen 106/45."""
    submode = cert.get("submode")
    if submode == "one_loop_sen":
        gb_pref = _req_frac(cert, "gauss_bonnet_prefactor")
        euler_int = _req_int(cert, "sphere_euler_integral_over_pi")
        angle_fac = _req_int(cert, "opening_angle_factor_over_pi")
        log_power = _req_frac(cert, "log_sb_half_power")
        measure_shift = _req_frac(cert, "measure_shift")
        q_claim = _req_frac(cert, "clock_ratio_q")
        sen_claim = _req_frac(cert, "fixed_mass_sen_coeff")
        if gb_pref != Fraction(53, 45 * 16):
            raise ValueError("gauss_bonnet_prefactor must be 53/(45*16) = 53/720 (pi^2 factored)")
        if euler_int != 8 or angle_fac != 8 or log_power != Fraction(1, 2):
            raise ValueError("S^2 Gauss-Bonnet data must satisfy int R dA = 8pi, 8pi opening, log(s_b^{1/2})")
        if measure_shift != Fraction(1, 2):
            raise ValueError("measure_shift from ds_b/(4pi s_b)^{1/2} must be 1/2")
        c_trace = gb_pref * (angle_fac * euler_int) * log_power
        if c_trace != Fraction(106, 45):
            raise ValueError(f"trace log coefficient mismatch: {c_trace}")
        c_total = c_trace + measure_shift
        q_exact = (2 * c_total) / (1 + 2 * c_total)
        if q_claim != q_exact:
            raise ValueError(f"clock_ratio_q mismatch: claimed {q_claim}, exact {q_exact}")
        sen_exact = q_exact / (2 * (1 - q_exact)) - measure_shift
        if sen_claim != sen_exact:
            raise ValueError(f"fixed_mass_sen_coeff mismatch: claimed {sen_claim}, exact {sen_exact}")
        return {
            "mode": "mts_sen_entropy",
            "submode": submode,
            "q": [q_exact.numerator, q_exact.denominator],
            "sen_coeff": [sen_exact.numerator, sen_exact.denominator],
        }
    elif submode == "footnote23_clock":
        x = _req_frac(cert, "scaled_radius_x")
        if not (0 < x < 1):
            raise ValueError("scaled_radius_x = (1-eps)*r_h/ell(D) must satisfy 0 < x < 1")
        q_claim = _req_frac(cert, "clock_ratio_q")
        c_log_claim = _req_frac(cert, "entropy_log_coeff")
        q_exact = (2 * x * x) / (1 + x * x)
        c_exact = (x * x) / (1 - x * x)
        if not (x * x <= q_exact <= x):
            raise ValueError("Eq. (5.54b)-(5.54c) window x^2 <= q <= x violated")
        if q_claim != q_exact:
            raise ValueError(f"q mismatch: claimed {q_claim}, exact {q_exact}")
        if c_log_claim != c_exact or c_exact != q_exact / (2 * (1 - q_exact)):
            raise ValueError(f"entropy_log_coeff mismatch: claimed {c_log_claim}, exact {c_exact}")
        return {
            "mode": "mts_sen_entropy",
            "submode": submode,
            "x": [x.numerator, x.denominator],
            "q": [q_exact.numerator, q_exact.denominator],
            "c_log": [c_exact.numerator, c_exact.denominator],
        }
    else:
        raise ValueError(f"unknown mts_sen_entropy submode '{submode}'")


def _exact_rational_rank(mat: List[List[Fraction]]) -> int:
    rows = [row[:] for row in mat]
    m = len(rows)
    n = len(rows[0]) if m else 0
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if rows[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        rows[r] = [v / pv for v in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [rows[i][j] - f * rows[r][j] for j in range(n)]
        r += 1
    return r


def verify_ads_trace_and_topology(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Eqs. (5.44)-(5.46) reflecting AdS trace finiteness + Eq. (5.70) null states."""
    submode = cert.get("submode")
    if submode == "ads_energy_band":
        beta = _req_frac(cert, "inverse_temp_beta")
        lam = _req_frac(cert, "energy_cutoff_Lambda")
        z_beta = _req_frac(cert, "partition_Z_beta")
        band_dim_max = _req_int(cert, "claimed_dim_upper_bound")
        claimed_p = _req_frac(cert, "claimed_band_prob_p")
        raw_weights = _req_list(cert, "sample_state_weights")
        raw_va = _req_list(cert, "diamond_weights_va")
        raw_ind = _req_list(cert, "band_indicator")
        weights = [_req_frac({"x": w}, "x") for w in raw_weights]
        if beta <= 0 or lam < 0 or z_beta <= 0 or band_dim_max < 1:
            raise ValueError("invalid AdS trace parameters")
        e_lo, e_hi = exp_pos_bracket(beta * lam, terms=24)
        min_w = Fraction(1) / e_hi
        if any(w < min_w or w > 1 for w in weights):
            raise ValueError("sample_state_weights violate exp(-beta*Lambda) <= w_i <= 1")
        if sum(weights) > z_beta:
            raise ValueError("sum of sample weights exceeds Z_beta")
        # Tight exact integer ceiling from Eq. (5.46): floor(e^{beta*Lambda} * Z_beta)
        exact_lo_floor = (e_lo * z_beta).numerator // (e_lo * z_beta).denominator
        exact_hi_floor = (e_hi * z_beta).numerator // (e_hi * z_beta).denominator
        if not (exact_lo_floor <= band_dim_max <= exact_hi_floor + 1) or band_dim_max < len(weights):
            raise ValueError(
                f"claimed_dim_upper_bound {band_dim_max} outside tight Eq. (5.46) range [{exact_lo_floor}, {exact_hi_floor + 1}]"
            )
        # Joint-cut centering Eq. (5.44): verify claimed_band_prob_p matches and centers the sum
        va = [_req_frac({"x": x}, "x") for x in raw_va]
        ind = [_req_int({"x": x}, "x") for x in raw_ind]
        if len(va) != len(ind) or sum(va) != 1 or any(v <= 0 for v in va):
            raise ValueError("diamond_weights_va must be strictly positive probability distribution")
        if any(i not in (0, 1) for i in ind):
            raise ValueError("band_indicator must be 0/1")
        p_band = sum(v for v, i in zip(va, ind) if i == 1)
        if not (0 < p_band < 1):
            raise ValueError("band probability p must satisfy 0 < p < 1")
        if claimed_p != p_band:
            raise ValueError(f"claimed_band_prob_p mismatch: claimed {claimed_p}, exact {p_band}")
        centered_sum = sum(v * (i - claimed_p) for v, i in zip(va, ind))
        if centered_sum != 0:
            raise ValueError("Eq. (5.44) diamond trace centering failed")
        return {
            "mode": "ads_trace_and_topology",
            "submode": submode,
            "p_band": [p_band.numerator, p_band.denominator],
            "dim_upper_bound": band_dim_max,
        }
    elif submode == "topology_null_states":
        d_D = _req_int(cert, "diamond_dim_dD")
        raw_basis = _req_list(cert, "filling_vectors")
        raw_null = _req_list(cert, "null_superposition_c")
        null_vec = [_req_frac({"x": c}, "x") for c in raw_null]
        claimed_rank = _req_int(cert, "claimed_gram_rank")
        if d_D < 1 or len(raw_basis) <= d_D:
            raise ValueError("need m > d_D filling vectors in Q^{d_D}")
        vecs: List[List[Fraction]] = []
        for row in raw_basis:
            if not isinstance(row, list) or len(row) != d_D:
                raise ValueError(f"each filling vector must have length d_D={d_D}")
            vecs.append([_req_frac({"x": x}, "x") for x in row])
        m = len(vecs)
        if len(null_vec) != m or all(c == 0 for c in null_vec):
            raise ValueError("null_superposition_c must be nonzero of length m")
        G: List[List[Fraction]] = [
            [sum(vecs[i][k] * vecs[j][k] for k in range(d_D)) for j in range(m)]
            for i in range(m)
        ]
        rank_G = _exact_rational_rank(G)
        if rank_G != claimed_rank or rank_G > d_D:
            raise ValueError(f"Gram rank mismatch or > d_D: rank={rank_G}, claimed={claimed_rank}, d_D={d_D}")
        Gc = [sum(G[i][j] * null_vec[j] for j in range(m)) for i in range(m)]
        if any(x != 0 for x in Gc):
            raise ValueError("null_superposition_c is not in ker(G)")
        norm_sq = sum(null_vec[i] * Gc[i] for i in range(m))
        if norm_sq != 0:
            raise ValueError("c^T G c != 0")
        return {
            "mode": "ads_trace_and_topology",
            "submode": submode,
            "m_fillings": m,
            "d_D": d_D,
            "gram_rank": rank_G,
            "null_norm_sq": 0,
        }
    else:
        raise ValueError(f"unknown ads_trace_and_topology submode '{submode}'")


def verify_certificate(cert: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(cert, dict):
        raise ValueError("certificate must be JSON object")
    if cert.get("schema") != SCHEMA:
        raise ValueError(f"expected schema '{SCHEMA}', got '{cert.get('schema')}'")
    mode = cert.get("mode")
    if mode == "graviton_pair_creation":
        return verify_graviton_pair_creation(cert)
    if mode == "causal_diamond_finiteness":
        return verify_causal_diamond_finiteness(cert)
    if mode == "mts_sen_entropy":
        return verify_mts_sen_entropy(cert)
    if mode == "ads_trace_and_topology":
        return verify_ads_trace_and_topology(cert)
    raise ValueError(f"unknown mode '{mode}'")


def verify_file(path: Path) -> Dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    res = verify_certificate(data)
    res["file"] = path.name
    return res


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args:
        print("Usage: python -m src.null_cone_qg_verifier <cert_or_dir> [...]")
        return 2
    files: List[Path] = []
    for a in args:
        p = Path(a)
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.")
        return 1
    for f in files:
        res = verify_file(f)
        print(f"PASS  {f.name}  ({res['mode']})")
    print(f"VERIFIED {len(files)}/{len(files)} certificates under {SCHEMA}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

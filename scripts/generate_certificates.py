"""Generate all 16 canonical certificates for Paper 86 (NULLCONE-QG-CERT-1.0)."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from src.null_cone_qg_verifier import (
    PI_HI,
    PI_LO,
    SCHEMA,
    cos_sin_bracket,
    exp_pos_bracket,
    verify_certificate,
)


def _fr(f: Fraction) -> list[int]:
    return [f.numerator, f.denominator]


def _round_lo(f: Fraction, denom: int = 10**6) -> Fraction:
    num = (f.numerator * denom) // f.denominator
    return Fraction(num, denom)


def _round_hi(f: Fraction, denom: int = 10**6) -> Fraction:
    num = -((-f.numerator * denom) // f.denominator)
    return Fraction(num, denom)


def make_mode1_cert(cid: str, s: Fraction, N: int, cs: bool = False) -> dict:
    pref = Fraction(1, 2) / (s * s)
    re_lo = Fraction(0)
    re_hi = Fraction(0)
    im_lo = Fraction(0)
    im_hi = Fraction(0)
    H_N = Fraction(0)
    for k in range(1, N + 1):
        (c_lo, c_hi), (s_lo, s_hi) = cos_sin_bracket(Fraction(2 * k, 1) / s, pairs=10)
        ik2 = Fraction(1, k * k)
        re_lo += c_lo * ik2
        re_hi += c_hi * ik2
        im_lo += (-s_hi) * ik2
        im_hi += (-s_lo) * ik2
        H_N += Fraction(1, k)
    tb = pref * Fraction(1, N)
    tot_re_lo = _round_lo(pref * re_lo - tb, 10**5)
    tot_re_hi = _round_hi(pref * re_hi + tb, 10**5)
    tot_im_lo = _round_lo(pref * im_lo - tb, 10**5)
    tot_im_hi = _round_hi(pref * im_hi + tb, 10**5)
    pert = H_N / (s * s * s)
    cert = {
        "schema": SCHEMA,
        "id": cid,
        "mode": "graviton_pair_creation",
        "s": _fr(s),
        "truncation_N": N,
        "nonpert_re_interval": [_fr(tot_re_lo), _fr(tot_re_hi)],
        "nonpert_im_interval": [_fr(tot_im_lo), _fr(tot_im_hi)],
        "tail_modulus_upper_bound": _fr(tb),
        "perturbative_im_coeff_HN_over_s3": _fr(pert),
        "verify_cauchy_schwarz": cs,
    }
    if cs:
        phi = [Fraction(1, 2), Fraction(-3, 5), Fraction(1, 4), Fraction(2, 7)]
        psi = [Fraction(2, 3), Fraction(1, 5), Fraction(-3, 4), Fraction(1, 7)]
        abs_sum = sum(abs(a * b) for a, b in zip(phi, psi))
        cert["cs_phi"] = [_fr(x) for x in phi]
        cert["cs_psi"] = [_fr(x) for x in psi]
        cert["cs_claimed_abs_sum"] = _fr(abs_sum)
    return cert


def make_mode2_cert(cid: str, ell: Fraction, eps: Fraction, eta: Fraction, var_s: Fraction, delta_eta: Fraction) -> dict:
    fac = (ell * ell) / ((1 - eps) * (1 - eps))
    s_lo = _round_lo(PI_LO * fac, 10**4)
    s_hi = _round_hi(PI_HI * fac, 10**4)
    e_lo, e_hi = exp_pos_bracket(abs(eta), terms=24)
    if eta < 0:
        e_lo, e_hi = Fraction(1) / e_hi, Fraction(1) / e_lo
    f_lo = (4 * e_hi) / ((1 + e_hi) ** 2) if e_lo >= 1 else (4 * e_lo) / ((1 + e_lo) ** 2)
    f_hi = (4 * e_lo) / ((1 + e_lo) ** 2) if e_lo >= 1 else (4 * e_hi) / ((1 + e_hi) ** 2)
    r_lo = _round_lo(f_lo, 10**5)
    r_hi = _round_hi(f_hi, 10**5)
    t2_lo = _round_lo(1 - f_hi, 10**5)
    t2_hi = _round_hi(1 - f_lo, 10**5)
    return {
        "schema": SCHEMA,
        "id": cid,
        "mode": "causal_diamond_finiteness",
        "ell_over_lp": _fr(ell),
        "cutoff_eps": _fr(eps),
        "boost_rapidity_eta": _fr(eta),
        "s_star_interval": [_fr(s_lo), _fr(s_hi)],
        "boost_ratio_interval": [_fr(r_lo), _fr(r_hi)],
        "boost_suppression_tanh2_interval": [_fr(t2_lo), _fr(t2_hi)],
        "op_norm_bound": [1, 1],
        "cycle_area_variance": _fr(var_s),
        "vacuum_deformation_delta_eta": _fr(delta_eta),
        "cycle_trace_weight": [1, 10],
        "uncut_amplitude_ZX": [1, 100],
    }


def main() -> None:
    out = Path("certificates")
    out.mkdir(parents=True, exist_ok=True)
    certs = [
        make_mode1_cert("C01_pair_s2_N40", Fraction(2, 1), 40, cs=True),
        make_mode1_cert("C02_pair_s5_N60", Fraction(5, 1), 60, cs=False),
        make_mode1_cert("C03_pair_s10_N80", Fraction(10, 1), 80, cs=True),
        make_mode1_cert("C04_pair_s20_N100", Fraction(20, 1), 100, cs=False),
        make_mode2_cert("C05_diamond_eta1_ell10", Fraction(10, 1), Fraction(1, 10), Fraction(1, 1), Fraction(1, 100), Fraction(1, 5)),
        make_mode2_cert("C06_diamond_eta2_ell25", Fraction(25, 1), Fraction(1, 20), Fraction(2, 1), Fraction(1, 400), Fraction(1, 4)),
        make_mode2_cert("C07_diamond_eta_half_ell50", Fraction(50, 1), Fraction(1, 50), Fraction(1, 2), Fraction(1, 25), Fraction(1, 5)),
        make_mode2_cert("C08_diamond_eta_neg1_ell100", Fraction(100, 1), Fraction(1, 100), Fraction(-1, 1), Fraction(1, 200), Fraction(1, 8)),
        {
            "schema": SCHEMA,
            "id": "C09_one_loop_sen_exact",
            "mode": "mts_sen_entropy",
            "submode": "one_loop_sen",
            "gauss_bonnet_prefactor": [53, 720],
            "sphere_euler_integral_over_pi": 8,
            "opening_angle_factor_over_pi": 8,
            "log_sb_half_power": [1, 2],
            "measure_shift": [1, 2],
            "clock_ratio_q": [257, 302],
            "fixed_mass_sen_coeff": [106, 45],
        },
        {
            "schema": SCHEMA,
            "id": "C10_footnote23_x_half",
            "mode": "mts_sen_entropy",
            "submode": "footnote23_clock",
            "scaled_radius_x": [1, 2],
            "clock_ratio_q": [2, 5],
            "entropy_log_coeff": [1, 3],
        },
        {
            "schema": SCHEMA,
            "id": "C11_footnote23_x_3_5",
            "mode": "mts_sen_entropy",
            "submode": "footnote23_clock",
            "scaled_radius_x": [3, 5],
            "clock_ratio_q": [9, 17],
            "entropy_log_coeff": [9, 16],
        },
        {
            "schema": SCHEMA,
            "id": "C12_footnote23_x_4_5",
            "mode": "mts_sen_entropy",
            "submode": "footnote23_clock",
            "scaled_radius_x": [4, 5],
            "clock_ratio_q": [32, 41],
            "entropy_log_coeff": [16, 9],
        },
        {
            "schema": SCHEMA,
            "id": "C13_ads_band_beta1_lam2",
            "mode": "ads_trace_and_topology",
            "submode": "ads_energy_band",
            "inverse_temp_beta": [1, 1],
            "energy_cutoff_Lambda": [2, 1],
            "partition_Z_beta": [5, 2],
            "claimed_dim_upper_bound": 18,
            "claimed_band_prob_p": [1, 2],
            "sample_state_weights": [[1, 1], [1, 2], [1, 4], [1, 5]],
            "diamond_weights_va": [[1, 2], [1, 3], [1, 6]],
            "band_indicator": [1, 0, 0],
        },
        {
            "schema": SCHEMA,
            "id": "C14_ads_band_beta2_lam1",
            "mode": "ads_trace_and_topology",
            "submode": "ads_energy_band",
            "inverse_temp_beta": [2, 1],
            "energy_cutoff_Lambda": [1, 1],
            "partition_Z_beta": [4, 1],
            "claimed_dim_upper_bound": 29,
            "claimed_band_prob_p": [1, 2],
            "sample_state_weights": [[1, 1], [3, 4], [1, 2], [1, 3], [1, 5]],
            "diamond_weights_va": [[1, 4], [1, 4], [1, 4], [1, 4]],
            "band_indicator": [1, 1, 0, 0],
        },
        {
            "schema": SCHEMA,
            "id": "C15_topology_null_d3_m4",
            "mode": "ads_trace_and_topology",
            "submode": "topology_null_states",
            "diamond_dim_dD": 3,
            "filling_vectors": [
                [[1, 1], [0, 1], [0, 1]],
                [[0, 1], [1, 1], [0, 1]],
                [[0, 1], [0, 1], [1, 1]],
                [[1, 1], [2, 1], [-1, 1]],
            ],
            "null_superposition_c": [[1, 1], [2, 1], [-1, 1], [-1, 1]],
            "claimed_gram_rank": 3,
        },
        {
            "schema": SCHEMA,
            "id": "C16_topology_null_d4_m6",
            "mode": "ads_trace_and_topology",
            "submode": "topology_null_states",
            "diamond_dim_dD": 4,
            "filling_vectors": [
                [[1, 1], [1, 1], [0, 1], [0, 1]],
                [[0, 1], [1, 1], [1, 1], [0, 1]],
                [[0, 1], [0, 1], [1, 1], [1, 1]],
                [[1, 1], [0, 1], [0, 1], [1, 1]],
                [[2, 1], [1, 1], [1, 1], [2, 1]],
                [[1, 1], [2, 1], [2, 1], [1, 1]],
            ],
            "null_superposition_c": [[1, 1], [-1, 1], [1, 1], [-1, 1], [0, 1], [0, 1]],
            "claimed_gram_rank": 3,
        },
    ]
    for c in certs:
        verify_certificate(c)
        (out / f"{c['id']}.json").write_text(json.dumps(c, indent=2) + "\n", encoding="utf-8")
    print(f"Generated and verified {len(certs)} certificates in {out}")


if __name__ == "__main__":
    main()

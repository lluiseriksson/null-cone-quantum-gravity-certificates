"""Comprehensive unit, canonical, forgery, and AST zero-float tests for Paper 86."""

from __future__ import annotations

import ast
import copy
import json
from fractions import Fraction
from pathlib import Path
import pytest

from src.null_cone_qg_verifier import (
    SCHEMA,
    cos_sin_bracket,
    exp_pos_bracket,
    verify_certificate,
    verify_file,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = REPO_ROOT / "certificates"
CERT_FILES = sorted(CERT_DIR.glob("*.json"))


def test_sixteen_canonical_certificates_exist() -> None:
    assert len(CERT_FILES) == 16


@pytest.mark.parametrize("cert_path", CERT_FILES, ids=[p.stem for p in CERT_FILES])
def test_canonical_certificate_passes(cert_path: Path) -> None:
    res = verify_file(cert_path)
    assert res["file"] == cert_path.name


def test_zero_float_ast_audit() -> None:
    src_path = REPO_ROOT / "src" / "null_cone_qg_verifier.py"
    tree = ast.parse(src_path.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"float literal found: {node.value}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
            pytest.fail("float() call found")
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name not in ("math", "cmath", "numpy", "scipy")
        if isinstance(node, ast.ImportFrom):
            assert node.module not in ("math", "cmath", "numpy", "scipy")


def test_exp_and_trig_brackets_tight() -> None:
    lo, hi = exp_pos_bracket(Fraction(1, 1))
    assert Fraction(271828, 100000) < lo <= hi < Fraction(271829, 100000)
    (clo, chi), (slo, shi) = cos_sin_bracket(Fraction(1, 2))
    assert Fraction(8775, 10000) < clo <= chi < Fraction(8776, 10000)
    assert Fraction(4794, 10000) < slo <= shi < Fraction(4795, 10000)


def test_reject_wrong_schema() -> None:
    c = json.loads((CERT_DIR / "C09_one_loop_sen_exact.json").read_text(encoding="utf-8"))
    c["schema"] = "WRONG-1.0"
    with pytest.raises(ValueError, match="schema"):
        verify_certificate(c)


def test_reject_understated_tail_bound() -> None:
    c = json.loads((CERT_DIR / "C01_pair_s2_N40.json").read_text(encoding="utf-8"))
    c["tail_modulus_upper_bound"] = [1, 100000]
    with pytest.raises(ValueError, match="tail_modulus_upper_bound"):
        verify_certificate(c)


def test_reject_inflated_tail_bound() -> None:
    c = json.loads((CERT_DIR / "C01_pair_s2_N40.json").read_text(encoding="utf-8"))
    c["tail_modulus_upper_bound"] = [1000, 1]
    with pytest.raises(ValueError, match="tail_modulus_upper_bound"):
        verify_certificate(c)


def test_reject_forged_perturbative_harmonic() -> None:
    c = json.loads((CERT_DIR / "C02_pair_s5_N60.json").read_text(encoding="utf-8"))
    c["perturbative_im_coeff_HN_over_s3"] = [1, 10]
    with pytest.raises(ValueError, match="perturbative_im_coeff"):
        verify_certificate(c)


def test_reject_zero_boost_rapidity() -> None:
    c = json.loads((CERT_DIR / "C05_diamond_eta1_ell10.json").read_text(encoding="utf-8"))
    c["boost_rapidity_eta"] = [0, 1]
    with pytest.raises(ValueError, match="nonzero"):
        verify_certificate(c)


def test_reject_unphysical_delta_eta() -> None:
    c = json.loads((CERT_DIR / "C05_diamond_eta1_ell10.json").read_text(encoding="utf-8"))
    c["vacuum_deformation_delta_eta"] = [10, 1]
    with pytest.raises(ValueError, match="2\\*op_norm_bound"):
        verify_certificate(c)


def test_reject_popoviciu_variance_overflow() -> None:
    c = json.loads((CERT_DIR / "C05_diamond_eta1_ell10.json").read_text(encoding="utf-8"))
    c["cycle_area_variance"] = [1000000, 1]
    with pytest.raises(ValueError, match="Popoviciu"):
        verify_certificate(c)


def test_reject_non_reduced_rational() -> None:
    c = json.loads((CERT_DIR / "C09_one_loop_sen_exact.json").read_text(encoding="utf-8"))
    c["clock_ratio_q"] = [514, 604]
    with pytest.raises(ValueError, match="lowest terms"):
        verify_certificate(c)


def test_reject_forged_sen_coeff() -> None:
    c = json.loads((CERT_DIR / "C09_one_loop_sen_exact.json").read_text(encoding="utf-8"))
    c["fixed_mass_sen_coeff"] = [107, 45]
    with pytest.raises(ValueError, match="fixed_mass_sen_coeff"):
        verify_certificate(c)


def test_reject_forged_clock_ratio_q() -> None:
    c = json.loads((CERT_DIR / "C09_one_loop_sen_exact.json").read_text(encoding="utf-8"))
    c["clock_ratio_q"] = [256, 302]
    with pytest.raises(ValueError):
        verify_certificate(c)


def test_reject_forged_footnote23_identity() -> None:
    c = json.loads((CERT_DIR / "C10_footnote23_x_half.json").read_text(encoding="utf-8"))
    c["entropy_log_coeff"] = [1, 2]
    with pytest.raises(ValueError, match="entropy_log_coeff"):
        verify_certificate(c)


def test_reject_cycle_variance_violation() -> None:
    c = json.loads((CERT_DIR / "C05_diamond_eta1_ell10.json").read_text(encoding="utf-8"))
    c["cycle_area_variance"] = [10, 1]
    with pytest.raises(ValueError, match="boost-variance"):
        verify_certificate(c)


def test_reject_bool_as_int_injection() -> None:
    c = json.loads((CERT_DIR / "C15_topology_null_d3_m4.json").read_text(encoding="utf-8"))
    c["claimed_gram_rank"] = True
    with pytest.raises(ValueError, match="exact int"):
        verify_certificate(c)


def test_reject_non_null_superposition() -> None:
    c = json.loads((CERT_DIR / "C15_topology_null_d3_m4.json").read_text(encoding="utf-8"))
    c["null_superposition_c"] = [[1, 1], [0, 1], [0, 1], [0, 1]]
    with pytest.raises(ValueError, match="ker\\(G\\)"):
        verify_certificate(c)


def test_reject_forged_ads_weight_sum() -> None:
    c = json.loads((CERT_DIR / "C13_ads_band_beta1_lam2.json").read_text(encoding="utf-8"))
    c["partition_Z_beta"] = [1, 2]
    with pytest.raises(ValueError, match="exceeds Z_beta"):
        verify_certificate(c)


def test_reject_inflated_ads_dim_upper_bound() -> None:
    c = json.loads((CERT_DIR / "C13_ads_band_beta1_lam2.json").read_text(encoding="utf-8"))
    c["claimed_dim_upper_bound"] = 1000000
    with pytest.raises(ValueError, match="outside tight"):
        verify_certificate(c)


def test_reject_forged_band_prob_p() -> None:
    c = json.loads((CERT_DIR / "C13_ads_band_beta1_lam2.json").read_text(encoding="utf-8"))
    c["claimed_band_prob_p"] = [1, 3]
    with pytest.raises(ValueError, match="claimed_band_prob_p"):
        verify_certificate(c)


def test_reject_forged_diamond_centering() -> None:
    c = json.loads((CERT_DIR / "C13_ads_band_beta1_lam2.json").read_text(encoding="utf-8"))
    c["band_indicator"] = [1, 1, 1]
    with pytest.raises(ValueError, match="band probability"):
        verify_certificate(c)


def test_reject_forged_boost_interval() -> None:
    c = copy.deepcopy(json.loads((CERT_DIR / "C05_diamond_eta1_ell10.json").read_text(encoding="utf-8")))
    c["boost_ratio_interval"] = [[9, 10], [1, 1]]
    with pytest.raises(ValueError, match="boost_ratio_interval"):
        verify_certificate(c)

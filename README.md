# Formal Certification of Null-Cone Algebraic Quantum Gravity (`NULLCONE-QG-CERT-1.0`)

**Author:** Lluis Eriksson  
**License:** `MIT` (code, Lean 4 proofs, certificates, tests); `CC-BY-4.0` (manuscript, figures)  
**Target Preprint:** Venkatesa Chandrasekaran, *"An algebraic quantization of gravity from the null cone"*, `arXiv:2611.34924v1` (25 November 2026).

## Verification Summary
- **Constructive Lean 4.35.0 kernel** (`lean/NullConeQGCert.lean`): 18/18 theorems (`0 sorry`, `0` custom axioms, `0 Classical.choice`, `0` warnings).
- **Zero-float exact rational Python verifier** (`src/null_cone_qg_verifier.py`): AST-audited zero-float implementation across 4 modes (nonperturbative graviton pair creation vs. $O(G_N^3)$ log divergence, causal diamond focusing/boost/cycle contradiction, marginally trapped surface clock ratio & exact 1-loop Sen $106/45$ entropy recovery, reflecting AdS energy-band trace finiteness & spatial topology Gram null states).
- **Certificates & Tests:** 16/16 canonical JSON certificates (`certificates/C01`–`C16`), 38/38 pytest unit + forgery + AST checks.

## Replay Commands
```bash
(cd lean && lake build)
python -m src.null_cone_qg_verifier certificates
pytest -q
```

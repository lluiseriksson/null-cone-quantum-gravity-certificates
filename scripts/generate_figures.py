"""Generate 3 publication-quality figures for Paper 86 (NULLCONE-QG-CERT-1.0)."""

from __future__ import annotations

import math
from pathlib import Path
import matplotlib.pyplot as plt
import numpy as np


def main() -> None:
    out = Path("paper/figures")
    out.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.size": 9.5,
        "axes.labelsize": 10,
        "axes.titlesize": 10.5,
        "legend.fontsize": 8.5,
        "figure.dpi": 220,
    })

    # Fig 1: Nonperturbative finite Li_2(e^{-2i/s})/(2s^2) vs perturbative O(G_N^3) log-divergent H_N/s^3
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.3))
    Ns = np.arange(1, 151)
    s_val = 5.0
    nonpert_mod = []
    pert_mag = []
    re_s = 0.0
    im_s = 0.0
    h_s = 0.0
    for k in Ns:
        th = 2.0 * k / s_val
        re_s += math.cos(th) / (k * k)
        im_s -= math.sin(th) / (k * k)
        h_s += 1.0 / k
        nonpert_mod.append(math.hypot(re_s, im_s) / (2.0 * s_val * s_val))
        pert_mag.append(h_s / (s_val ** 3))
    ax1.plot(Ns, nonpert_mod, lw=2.0, color="#1f4e79", label=r"Nonpert. $|S_N(s=5)|$ (Eq. 4.33)")
    ax1.plot(Ns, pert_mag, lw=2.0, ls="--", color="#b22222", label=r"Pert. $O(G_N^3)$ $H_N/s^3$ (Eq. 4.34)")
    ax1.set_xlabel(r"Radial mode cutoff $N$")
    ax1.set_ylabel("Amplitude magnitude")
    ax1.set_title("(a) Convergence vs. UV Log Divergence")
    ax1.grid(alpha=0.25)
    ax1.legend(loc="lower right", frameon=True)

    s_grid = np.linspace(1.5, 25.0, 200)
    env = (math.pi ** 2 / 6.0) / (2.0 * s_grid ** 2)
    cert_s = [2.0, 5.0, 10.0, 20.0]
    cert_mods = []
    for sv in cert_s:
        r0 = sum(math.cos(2 * k / sv) / (k * k) for k in range(1, 300)) / (2 * sv * sv)
        i0 = -sum(math.sin(2 * k / sv) / (k * k) for k in range(1, 300)) / (2 * sv * sv)
        cert_mods.append(math.hypot(r0, i0))
    ax2.semilogy(s_grid, env, lw=2.0, color="#2e6b3e", label=r"Envelope $\pi^2 / (12 s^2)$")
    ax2.scatter(cert_s, cert_mods, color="#d95f02", zorder=5, s=42, label="Certified C01–C04")
    ax2.set_xlabel(r"Dimensionless corner area $s = A/(4 G_N \hbar)$")
    ax2.set_ylabel(r"$|\mathrm{Li}_2(e^{-2i/s})/(2 s^2)|$")
    ax2.set_title("(b) Certified Nonperturbative Enclosures")
    ax2.grid(alpha=0.25, which="both")
    ax2.legend(loc="upper right", frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig1_graviton_pair_creation.png", dpi=220)
    plt.close(fig)

    # Fig 2: Boost suppression Eq. (5.29) & Focusing area ceiling Eq. (5.30a)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.3))
    etas = np.linspace(-3.0, 3.0, 300)
    ratio = 4.0 * np.exp(etas) / ((1.0 + np.exp(etas)) ** 2)
    supp = np.tanh(etas / 2.0) ** 2
    ax1.plot(etas, ratio, lw=2.0, color="#1f4e79", label=r"Boost ratio $4 e^\eta/(1+e^\eta)^2$")
    ax1.plot(etas, supp, lw=2.0, ls="--", color="#c0392b", label=r"Suppression $\tanh^2(\eta/2)$")
    c_etas = [-1.0, 0.5, 1.0, 2.0]
    c_rat = [4 * math.exp(e) / (1 + math.exp(e)) ** 2 for e in c_etas]
    ax1.scatter(c_etas, c_rat, color="#d95f02", zorder=5, s=42, label="Certified C05–C08")
    ax1.set_xlabel(r"Corner boost rapidity $\eta$")
    ax1.set_ylabel("Dimensionless factor")
    ax1.set_ylim(-0.05, 1.48)
    ax1.set_title("(a) Relative Boost Suppression (Eq. 5.29)")
    ax1.grid(alpha=0.25)
    ax1.legend(loc="upper center", ncol=1, fontsize=8.0, frameon=True)

    ell_vals = np.linspace(5.0, 100.0, 200)
    for eps, col in [(0.01, "#1f4e79"), (0.05, "#2e6b3e"), (0.10, "#8e44ad")]:
        s_star = math.pi * (ell_vals ** 2) / ((1.0 - eps) ** 2)
        ax2.semilogy(ell_vals, s_star, lw=1.8, color=col, label=rf"$\epsilon = {eps:.2f}$")
    ax2.set_xlabel(r"Clock cutoff $\ell(D)/\ell_P$")
    ax2.set_ylabel(r"Area ceiling $s_* = \pi\ell^2/((1-\epsilon)^2\ell_P^2)$")
    ax2.set_title("(b) Raychaudhuri Focusing Ceiling (Eq. 5.30a)")
    ax2.grid(alpha=0.25, which="both")
    ax2.legend(loc="lower right", frameon=True)
    fig.tight_layout()
    fig.savefig(out / "fig2_boost_and_focusing.png", dpi=220)
    plt.close(fig)

    # Fig 3: Clock ratio q(x) & exact one-loop Sen 106/45 vs Lorentzian trace q = 257/302
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.3))
    xs = np.linspace(0.05, 0.92, 250)
    q_fn23 = 2.0 * xs * xs / (1.0 + xs * xs)
    ax1.fill_between(xs, xs * xs, xs, color="#d6eaf8", alpha=0.65, label=r"Eq. (5.54) window $x^2 \leq q \leq x$")
    ax1.plot(xs, q_fn23, lw=2.0, color="#1f4e79", label=r"Footnote 23 $q = 2x^2/(1+x^2)$")
    q_sen = 257.0 / 302.0
    ax1.axhline(q_sen, lw=1.6, ls=":", color="#b22222", label=r"1-loop $q = 257/302 \approx 0.8510$")
    cx = [0.5, 0.6, 0.8]
    cq = [2 * x * x / (1 + x * x) for x in cx]
    ax1.scatter(cx, cq, color="#d95f02", zorder=5, s=42, label="Certified C10–C12")
    ax1.set_xlabel(r"Scaled horizon radius $x = (1-\epsilon) r_h / \ell(D)$")
    ax1.set_ylabel(r"Limiting clock ratio $q$")
    ax1.set_title("(a) Marginally Trapped Clock Ratio")
    ax1.grid(alpha=0.25)
    ax1.legend(loc="upper left", frameon=True)

    labels = [
        "Trace\n" + r"$q/(2(1-q))$",
        "Measure\nshift $+1/2$",
        "Sen fixed-$M$\n" + r"$106/45$",
    ]
    vals = [257.0 / 90.0, 0.5, 106.0 / 45.0]
    cols = ["#1f4e79", "#7f8c8d", "#2e6b3e"]
    bars = ax2.bar(labels, vals, color=cols, width=0.55, edgecolor="#222222")
    for b, v, txt in zip(bars, vals, ["257/90\n(2.8556)", "1/2\n(0.5000)", "106/45\n(2.3556)"]):
        ax2.text(b.get_x() + b.get_width() / 2.0, v + 0.08, txt, ha="center", va="bottom", fontsize=8.3)
    ax2.set_ylim(0, 3.45)
    ax2.set_ylabel(r"Coefficient of $\log(A / 4 G_N \hbar)$")
    ax2.set_title("(b) Exact 1-Loop Sen Entropy Recovery")
    ax2.grid(axis="y", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out / "fig3_sen_entropy_and_clock.png", dpi=220)
    plt.close(fig)
    print("Generated 3 figures for Paper 86.")


if __name__ == "__main__":
    main()

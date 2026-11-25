# A Machine-Certified Degree-2,799 Counterexample to Smale's Mean Value Conjecture

[![Exact Machine Certification (pandroots 0.31.0)](https://github.com/ivan-fr/smale-deg2799/actions/workflows/ci.yml/badge.svg)](https://github.com/ivan-fr/smale-deg2799/actions/workflows/ci.yml)

**Author:** Ivan Besevic (ESIEE-IT, France — `ivan.besevic@edu.esiee-it.fr`)

## Certified Theorem

Let $P(z) = \sum_{k=0}^{2799} c_k z^k \in \mathbb{Z}[i][z]$ be the explicit Gaussian-integer polynomial archived in [`data/champion_deg2799.gpoly`](data/champion_deg2799.gpoly) (SHA-256: `5d1ad7a2509a488934031144d6c2bee5ab36d027bcee392087657a1b117dbfdc`, $c_{2799} \neq 0$, max coefficient bit-length $1{,}011$, leading coefficient bit-length $558$), and let
$$a = \frac{22901 - 11056\,i}{2^{15}} \in \mathbb{Q}(i)$$
be the exact 15-bit dyadic anchor. Define the normalized polynomial
$$p(u) = \frac{P(u + a) - P(a)}{P'(a)} \in \mathbb{Q}(i)[u], \qquad \deg(p) = 2{,}799, \quad p(0) = 0, \quad p'(0) = 1.$$

Then **all $2{,}798$ critical points** $\zeta_1, \dots, \zeta_{2798} \in \mathbb{C}$ of $p$ are simple, lie in $|c_j| < 0.96$, and satisfy the unconditionally certified global enclosure
$$\min_{p'(\zeta) = 0} \left|\frac{p(\zeta)}{\zeta}\right| = \min_{P'(c) = 0} \left|\frac{P(c) - P(a)}{(c - a)\, P'(a)}\right| \in \bigl[\,1.0002520813917934477351916,\;\; 1.0002520813917934477351917\,\bigr] > 1.$$

By standard leading-term perturbation ($\varepsilon u^n$ for sufficiently small $\varepsilon > 0$), explicit counterexamples to Smale's Mean Value Conjecture ($K \le 1$) exist for **every degree $n \ge 2{,}799$**.

---

## Comparison with Previous World Records

| Metric | Adamczewski & Colbrook (Oct 2026, `arXiv:2610.36158`) | Besevic (Nov 24, 2026, `zenodo.24512942`) | **This Work (Nov 25, 2026)** | Improvement |
|---|---|---|---|---|
| **Exact Polynomial Degree $d$** | `29,984` | `7,299` | **`2,799`** | **2.61x below 7,299 / 10.71x below 29,984** |
| **Certified Global $\min \lvert p(\zeta)/\zeta \rvert$** | `(1.00000049595801, ...04)` | `[1.00002719655422710959, ...60]` | **`[1.0002520813917934477351916, ...17]`** | **9.27x / 508.3x larger margin above 1** |
| **Exact Anchor $a \in \mathbb{Q}(i)$** | — | 53-bit dyadic | **`(22901 - 11056*i) / 2^15`** | Exact 15-bit dyadic |
| **Artifact Size (`.gpoly`)** | — | `7.6 MB` (`max_bits = 2,311`) | **`1.3 MB`** (`max_bits = 1,011`) | **5.8x smaller** |
| **Root Certification Engine** | — | Custom BigInt Rouché | **[`pandroots 0.31.0`](https://crates.io/crates/pandroots) (`certify_roots_exact`)** | Crates.io verified library |
| **Total Verification Time** | — | `413.72 s` (10 cores) | **`10.43 s`** (10 cores: `8.56 s` `pandroots` + `1.85 s` Smale bounds) | **39.7x faster** |

---

## Certification Architecture (Zero Floating-Point Assumptions)

Every proof inequality in [`src/bin/certify_smale.rs`](src/bin/certify_smale.rs) executes strictly in exact arbitrary-precision integer arithmetic (`pandroots 0.31.0` + `num_bigint::BigInt`):

1. **Stage 1 — Exact Root Certification via [`pandroots 0.31.0`](https://crates.io/crates/pandroots):**
   - Forms the exact Gaussian-integer derivative $P'(z) = \sum_{k=1}^{2799} k c_k z^{k-1} \in \mathbb{Z}[i][z]$.
   - Calls `pandroots::certify_roots_exact` with `target_radius_bits = 795`.
   - Using zero-allocation exact `u64` limb ball arithmetic, exact Rouché's theorem on every disc, and an exact integer sweep-line pairwise disjointness proof, `pandroots` certifies all **2,798 / 2,798** critical points as simple roots inside pairwise-disjoint exact dyadic discs $D(z_j, r_j)$ with $r_j \le 2^{-795}$ in **8.56 seconds** (326.8 roots/s).
   - By the Fundamental Theorem of Algebra, these 2,798 disjoint discs account for 100% of all critical points of $P$ in $\mathbb{C}$.

2. **Stage 2 — Exact BigInt Smale Ratio Enclosure:**
   - Directly embeds every `pandroots`-certified center $z_j$ with **zero rounding** at $F = 1{,}024$ fractional bits.
   - Verifies $|z_j| + r_j \le 96/100$ in exact integer arithmetic for all 2,798 discs.
   - Evaluates $P(a), P'(a)$, and $P(z_j)$ via rigorous fixed-point Horner with explicit ulp error tracking, combines with the exact global Lipschitz bound $|P(w) - P(z_j)| \le M_1(96/100)\, r_j$, and proves strictly $> 1$ for **2,798 / 2,798** discs in **1.85 seconds**.

3. **Independent 700-Digit Python `mpmath` Audit (`verify_independent.py`):**
   - Independently polishes the worst critical point (`root #2037` at `0.575825497716 - 0.126546779359i`), its 7 nearest neighbors, the 4 outermost critical points, and 8 strided boundary roots to 517–695 decimal digits.
   - Confirms `Smale = 1.000252081391793447735191684`, agreeing with all 25 certified digits from the Rust `pandroots` certifier.

---

## Reproducing the Proof

```bash
# 1. Run full 100% exact pandroots-0.31.0 machine certification (~10s on 10 cores)
cargo run --release --bin certify_smale

# 2. Optional: independent 700-digit Python mpmath verification
python3 verify_independent.py data/champion_deg2799.gpoly data/champion_deg2799.seeds 2037
```

## Artifact Checksums (SHA-256)

| File | Size | SHA-256 |
|---|---|---|
| `data/champion_deg2799.gpoly` | 1.3 MB | `5d1ad7a2509a488934031144d6c2bee5ab36d027bcee392087657a1b117dbfdc` |
| `data/champion_deg2799.seeds` | 128 KB | `e6fd4dd2a528f58d0b0d690e1401687bbf864cfd6489860841c975ac58045e4a` |
| `paper/Smale_Degree_2799_Counterexample.pdf` | — | Preprint describing the construction and `pandroots 0.31.0` proof |

## License

MIT License. See [`LICENSE`](LICENSE).

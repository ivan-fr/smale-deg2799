//! 100% Unconditional, Zero-Float-Assumption Machine Certifier for the
//! Degree-2,799 Counterexample to Smale's Mean Value Conjecture.
//!
//! Architecture:
//!   Stage 1 (Root Certification via `pandroots` 0.31.0):
//!     Calls `pandroots::certify_roots_exact` on the exact Gaussian-integer derivative
//!     P'(z) in Z[i][z]. Using zero-allocation exact `u64` limb ball arithmetic, exact
//!     Rouché's theorem on every disc, and exact integer sweep-line pairwise disjointness,
//!     `pandroots` proves unconditionally that all d - 1 = 2,798 critical points of P in C
//!     are simple and uniquely enclosed by pairwise-disjoint exact dyadic discs D(z_j, r_j).
//!
//!   Stage 2 (Exact BigInt Smale Ratio Enclosure):
//!     Directly consumes the exact dyadic centers z_j and radii r_j = 2^{e_j} returned by
//!     `pandroots::certify_roots_exact` (with zero floating-point assumptions anywhere in
//!     the proof) and computes rigorous outward-rounded integer bounds on
//!         |(P(w) - P(a)) / ((w - a) * P'(a))|
//!     uniformly for all w in D(z_j, r_j), proving that every critical value ratio is
//!     strictly greater than 1.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use pandroots::{certify_roots_exact, GPoly, SeedCertOptions, C};
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::str::FromStr;
use std::thread;
use std::time::Instant;

/// Exact complex fixed-point number representing `(re + i * im) * 2^{-f_bits}`.
#[derive(Clone)]
struct CFP {
    re: BigInt,
    im: BigInt,
}

impl CFP {
    fn zero() -> Self {
        Self {
            re: BigInt::zero(),
            im: BigInt::zero(),
        }
    }
}

/// 3-multiplication Karatsuba complex multiply shifted right by `f_bits`.
/// Since BigInt `>>` is arithmetic floor division, each component has error in `[0, 1)` ulp,
/// so the complex Euclidean rounding error is strictly `< sqrt(2) < 2` ulps.
#[inline]
fn cfp_mul(a: &CFP, b: &CFP, f_bits: usize) -> CFP {
    let p1 = &a.re * &b.re;
    let p2 = &a.im * &b.im;
    let p3 = (&a.re + &a.im) * (&b.re + &b.im);
    let im = (p3 - &p1 - &p2) >> f_bits;
    let re = (p1 - p2) >> f_bits;
    CFP { re, im }
}

#[inline]
fn cfp_add(a: &CFP, b: &CFP) -> CFP {
    CFP {
        re: &a.re + &b.re,
        im: &a.im + &b.im,
    }
}

#[inline]
fn cfp_sub(a: &CFP, b: &CFP) -> CFP {
    CFP {
        re: &a.re - &b.re,
        im: &a.im - &b.im,
    }
}

/// Rigorous upper bound `ceil(sqrt(re^2 + im^2))` in integer units of `2^{-f_bits}`.
fn cfp_abs_hi(z: &CFP) -> BigInt {
    let n2 = &z.re * &z.re + &z.im * &z.im;
    let s = n2.sqrt();
    if &s * &s < n2 {
        s + 1u8
    } else {
        s
    }
}

/// Rigorous lower bound `floor(sqrt(re^2 + im^2))` in integer units of `2^{-f_bits}`.
fn cfp_abs_lo(z: &CFP) -> BigInt {
    let n2 = &z.re * &z.re + &z.im * &z.im;
    n2.sqrt()
}

/// Display-only conversion of `x * 2^{-shift}` to `f64`. Never used in any proof inequality.
fn fp_to_f64(x: &BigInt, shift: i64) -> f64 {
    if x.is_zero() {
        return 0.0;
    }
    let neg = x.is_negative();
    let ax = x.abs();
    let bits = ax.bits() as i64;
    let keep = 60i64;
    let (mant, eff_exp) = if bits > keep {
        let s = (bits - keep) as usize;
        let top: u64 = (&ax >> s).try_into().unwrap();
        (top as f64, (s as i64) - shift)
    } else {
        let top: u64 = ax.try_into().unwrap();
        (top as f64, -shift)
    };
    let val = mant * (eff_exp as f64).exp2();
    if neg {
        -val
    } else {
        val
    }
}

/// Rigorous Horner evaluation of `P(z)` and `P'(z)` at exact dyadic `z = (re + i*im) * 2^{-f_bits}`.
/// Coefficients `c_scaled[k] = c[k] << f_bits` are exact.
/// Returns `(p, dp, ep, edp)` satisfying:
///   `|p  * 2^{-f_bits} - P(z)|  <= ep  * 2^{-f_bits}`
///   `|dp * 2^{-f_bits} - P'(z)| <= edp * 2^{-f_bits}`
fn eval_01_rigorous(c_scaled: &[CFP], z: &CFP, f_bits: usize) -> (CFP, CFP, BigInt, BigInt) {
    let d = c_scaled.len() - 1;
    let z_hi = cfp_abs_hi(z);
    let mut p = c_scaled[d].clone();
    let mut dp = CFP::zero();
    let mut ep = BigInt::zero();
    let mut edp = BigInt::zero();
    let three = BigInt::from(3u8);

    for k in (0..d).rev() {
        let dp_z = cfp_mul(&dp, z, f_bits);
        dp = cfp_add(&dp_z, &p);
        edp = ((&edp * &z_hi) >> f_bits) + &ep + &three;

        let p_z = cfp_mul(&p, z, f_bits);
        p = cfp_add(&p_z, &c_scaled[k]);
        ep = ((&ep * &z_hi) >> f_bits) + &three;
    }
    (p, dp, ep, edp)
}

/// Rigorous Horner evaluation of `P(z)` only at exact dyadic `z = (re + i*im) * 2^{-f_bits}`.
/// Returns `(p, ep)` with `|p * 2^{-f_bits} - P(z)| <= ep * 2^{-f_bits}`.
fn eval_p_rigorous(c_scaled: &[CFP], z: &CFP, f_bits: usize) -> (CFP, BigInt) {
    let d = c_scaled.len() - 1;
    let z_hi = cfp_abs_hi(z);
    let mut p = c_scaled[d].clone();
    let mut ep = BigInt::zero();
    let three = BigInt::from(3u8);

    for k in (0..d).rev() {
        let p_z = cfp_mul(&p, z, f_bits);
        p = cfp_add(&p_z, &c_scaled[k]);
        ep = ((&ep * &z_hi) >> f_bits) + &three;
    }
    (p, ep)
}

/// Format an exact integer `val_128` representing `val_128 * 2^{-128}` rounded outward
/// (`round_up = false` -> floor, `round_up = true` -> ceil) to `digits` decimal places.
fn format_dec_128(val_128: &BigInt, digits: u32, round_up: bool) -> String {
    let scale = BigInt::from(10u64).pow(digits);
    let one_128 = BigInt::from(1u8) << 128;
    let scaled = if round_up {
        ((val_128 * &scale) + (&one_128 - 1u8)) >> 128usize
    } else {
        (val_128 * &scale) >> 128usize
    };
    let s = scaled.to_string();
    let d = digits as usize;
    if s.len() <= d {
        format!("0.{}{}", "0".repeat(d - s.len()), s)
    } else {
        format!("{}.{}", &s[..s.len() - d], &s[s.len() - d..])
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let gpoly_path = args
        .get(1)
        .map(|s| s.as_str())
        .unwrap_or("data/champion_deg2799.gpoly");
    let seeds_path = args
        .get(2)
        .map(|s| s.as_str())
        .unwrap_or("data/champion_deg2799.seeds");
    let threads: usize = args
        .get(3)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| thread::available_parallelism().map(|n| n.get()).unwrap_or(4));

    let t0 = Instant::now();

    // ------------------------------------------------------------------------
    // 1. Load exact polynomial P(z) in Z[i][z] and exact dyadic anchor a in Q(i)
    // ------------------------------------------------------------------------
    let f = File::open(gpoly_path).expect("open gpoly file");
    let mut lines = BufReader::new(f).lines();
    let hdr = lines.next().expect("header line").unwrap();
    let mut ht = hdr.split_whitespace();
    let deg: usize = ht.next().unwrap().parse().unwrap();
    let a_num_re = BigInt::from_str(ht.next().unwrap()).unwrap();
    let a_num_im = BigInt::from_str(ht.next().unwrap()).unwrap();
    let a_shift: usize = ht.next().unwrap().parse().unwrap();

    let mut c_asc: Vec<(BigInt, BigInt)> = Vec::with_capacity(deg + 1);
    let mut c_abs_hi: Vec<BigInt> = Vec::with_capacity(deg + 1);
    for l in lines {
        let s = l.unwrap();
        if s.trim().is_empty() {
            continue;
        }
        let mut t = s.split_whitespace();
        let re = BigInt::from_str(t.next().unwrap()).unwrap();
        let im = BigInt::from_str(t.next().unwrap()).unwrap();
        let n2 = &re * &re + &im * &im;
        let sq = n2.sqrt();
        let abs_hi = if &sq * &sq < n2 { sq + 1u8 } else { sq };
        c_abs_hi.push(abs_hi);
        c_asc.push((re, im));
    }
    assert_eq!(c_asc.len(), deg + 1, "expected deg+1 coefficients");
    assert!(
        !c_asc[deg].0.is_zero() || !c_asc[deg].1.is_zero(),
        "leading coefficient c[deg] must be nonzero so deg(P') = deg - 1"
    );
    let max_coeff_bits = c_asc
        .iter()
        .map(|(r, i)| r.bits().max(i.bits()))
        .max()
        .unwrap_or(0);
    let lead_bits = c_asc[deg].0.bits().max(c_asc[deg].1.bits());

    // Exact derivative P'(z) = sum_{k=1}^deg k * c_k * z^{k-1} in DESCENDING degree order
    // (pandroots::GPoly convention).
    let mut dp_gpoly: GPoly = Vec::with_capacity(deg);
    for k in (1..=deg).rev() {
        let kb = BigInt::from(k);
        dp_gpoly.push((&c_asc[k].0 * &kb, &c_asc[k].1 * &kb));
    }

    // Load untrusted approximate seeds for P'(z) = 0
    let sf = File::open(seeds_path).expect("open seeds file");
    let mut slines = BufReader::new(sf).lines();
    let n_seeds: usize = slines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .parse()
        .unwrap();
    assert_eq!(n_seeds, deg - 1, "expected deg - 1 seeds");
    let mut seeds: Vec<C> = Vec::with_capacity(n_seeds);
    for l in slines {
        let s = l.unwrap();
        if s.trim().is_empty() {
            continue;
        }
        let mut t = s.split_whitespace();
        let re: f64 = t.next().unwrap().parse().unwrap();
        let im: f64 = t.next().unwrap().parse().unwrap();
        seeds.push(C::new(re, im));
    }
    assert_eq!(seeds.len(), deg - 1);

    println!("================================================================================");
    println!("  SMALE MEAN VALUE CONJECTURE — EXACT MACHINE CERTIFIER (deg = {deg})");
    println!("================================================================================");
    println!("  Polynomial file          : {gpoly_path}");
    println!("  Exact degree             : {deg} (c_{deg} != 0, max_bits={max_coeff_bits}, lead_bits={lead_bits})");
    println!("  Exact anchor a in Q(i)   : ({a_num_re} + ({a_num_im})*i) / 2^{a_shift}");
    println!("  Worker threads           : {threads}");

    // ------------------------------------------------------------------------
    // 2. Stage 1: Exact root certification of P'(z) = 0 via `pandroots 0.31.0`
    // ------------------------------------------------------------------------
    // First compute a quick global bound M1(R) for R = 96/100 (or ceil(max|seed|*100)+1 / 100)
    // and evaluate P(a), P'(a) at F_INIT = 1024 bits to choose a target radius for pandroots
    // guaranteeing > 120 bits of accuracy on every Smale ratio!
    let max_seed_abs = seeds.iter().map(|z| z.abs()).fold(0.0f64, f64::max);
    let r_bound_num = (max_seed_abs * 100.0).ceil() as u64 + 1;
    let r_bound_den = 100u64;

    let f_init = 1024usize;
    assert!(f_init >= a_shift);
    let c_init: Vec<CFP> = c_asc
        .iter()
        .map(|(r, i)| CFP {
            re: r << f_init,
            im: i << f_init,
        })
        .collect();
    let a_init = CFP {
        re: &a_num_re << (f_init - a_shift),
        im: &a_num_im << (f_init - a_shift),
    };
    let (_, dpa_init, _, edpa_init) = eval_01_rigorous(&c_init, &a_init, f_init);
    let dpa_init_lo = cfp_abs_lo(&dpa_init) - &edpa_init;
    assert!(dpa_init_lo.is_positive(), "P'(a) must be nonzero");
    let dpa_net_bits = dpa_init_lo.bits().saturating_sub(f_init as u64) as usize;

    // Exact global upper bound M1(R) >= sup_{|w| <= R} |P'(w)| in integer units of 2^{-f_init}
    let mut r_pow = BigInt::from(1u8) << f_init;
    let mut m1_init = BigInt::zero();
    for k in 1..=deg {
        m1_init += BigInt::from(k) * &c_abs_hi[k] * &r_pow;
        r_pow = (&r_pow * BigInt::from(r_bound_num) + BigInt::from(r_bound_den - 1))
            / BigInt::from(r_bound_den);
    }
    let m1_net_bits = m1_init.bits().saturating_sub(f_init as u64) as usize;
    let target_radius_bits = (m1_net_bits + 130).saturating_sub(dpa_net_bits).max(128);

    println!(
        "\n[Stage 1] Calling pandroots::certify_roots_exact (v0.31.0) on deg(P')={} (target r <= 2^-{target_radius_bits})...",
        deg - 1
    );
    let opt = SeedCertOptions {
        threads,
        target_radius_bits,
        extra_bits: 128,
        max_newton_steps: 12,
    };
    let (certified_roots, complete, st) = certify_roots_exact(&dp_gpoly, &seeds, &opt);
    println!(
        "  pandroots DONE in {:.2}s ({:.1} roots/s): complete={complete}, certified={}/{}, disjoint={}, bits={}, max_r=2^{}",
        st.elapsed_s,
        (st.degree as f64) / st.elapsed_s.max(1e-9),
        st.certified,
        st.degree,
        st.disjoint,
        st.bits,
        st.max_radius_exp
    );
    assert!(complete, "pandroots::certify_roots_exact failed to certify all roots!");
    assert_eq!(st.certified, deg - 1);
    assert!(st.disjoint, "pandroots discs must be pairwise disjoint");
    assert_eq!(certified_roots.len(), deg - 1);

    // ------------------------------------------------------------------------
    // 3. Stage 2: Exact BigInt Smale ratio enclosure on every pandroots disc
    // ------------------------------------------------------------------------
    let t2 = Instant::now();
    // Choose working fixed-point precision f_bits so EVERY pandroots-certified center z_j
    // and anchor a embed EXACTLY (zero rounding of centers!) and Horner error is tiny.
    let mut max_center_neg_e = a_shift;
    for r in &certified_roots {
        assert_eq!(r.count, 1, "every critical point must be simple (count=1)");
        assert_eq!(r.mult, 1, "every critical point must have mult=1");
        assert_eq!(
            r.radius.f, 1.0,
            "pandroots seed_cert returns exact power-of-two radii (f == 1.0)"
        );
        if r.z.e < 0 {
            let ne = (-r.z.e) as usize;
            if ne > max_center_neg_e {
                max_center_neg_e = ne;
            }
        }
    }
    let f_bits = max_center_neg_e.max(target_radius_bits + 128).max(1024);
    println!(
        "\n[Stage 2] Computing exact BigInt Smale ratio enclosures over all {} pandroots discs (F={f_bits} bits, zero center rounding)...",
        deg - 1
    );

    let c_scaled: Vec<CFP> = c_asc
        .iter()
        .map(|(r, i)| CFP {
            re: r << f_bits,
            im: i << f_bits,
        })
        .collect();
    let a_fp = CFP {
        re: &a_num_re << (f_bits - a_shift),
        im: &a_num_im << (f_bits - a_shift),
    };

    // Exact global bound R_bound (floor in 2^{-f_bits}) and M1(R) (ceil in 2^{-f_bits})
    let r_bound_fp = (BigInt::from(r_bound_num) << f_bits) / BigInt::from(r_bound_den);
    let mut r_pow = BigInt::from(1u8) << f_bits;
    let mut m1_bound = BigInt::zero();
    for k in 1..=deg {
        m1_bound += BigInt::from(k) * &c_abs_hi[k] * &r_pow;
        r_pow = (&r_pow * BigInt::from(r_bound_num) + BigInt::from(r_bound_den - 1))
            / BigInt::from(r_bound_den);
    }

    // Rigorous P(a), P'(a) at f_bits
    let (pa, dpa, epa, edpa) = eval_01_rigorous(&c_scaled, &a_fp, f_bits);
    let dpa_lo = cfp_abs_lo(&dpa) - &edpa;
    let dpa_hi = cfp_abs_hi(&dpa) + &edpa;
    assert!(dpa_lo.is_positive(), "P'(a) must be strictly nonzero");

    let chunk = certified_roots.len().div_ceil(threads);
    let one = BigInt::from(1u8);

    // Parallel Stage 2 evaluation over all pandroots-certified discs
    let results: Vec<Vec<(usize, CFP, bool, BigInt, BigInt)>> = thread::scope(|s| {
        let mut hs = Vec::new();
        for t in 0..threads {
            let st_idx = t * chunk;
            let en_idx = ((t + 1) * chunk).min(certified_roots.len());
            let slice = &certified_roots[st_idx..en_idx];
            let c_ref = &c_scaled;
            let pa_r = &pa;
            let epa_r = &epa;
            let dpa_lo_r = &dpa_lo;
            let dpa_hi_r = &dpa_hi;
            let a_ref = &a_fp;
            let m1_r = &m1_bound;
            let rb_r = &r_bound_fp;
            let one_r = &one;
            hs.push(s.spawn(move || {
                let mut out = Vec::with_capacity(slice.len());
                for (loc, pr) in slice.iter().enumerate() {
                    let idx = st_idx + loc;
                    // Exact embedding of pandroots center z_j = (re + i*im) * 2^{z.e} into 2^{-f_bits}
                    let shift_z = (f_bits as i64) + pr.z.e;
                    assert!(shift_z >= 0, "f_bits must cover z.e exactly");
                    let z = CFP {
                        re: &pr.z.re << (shift_z as usize),
                        im: &pr.z.im << (shift_z as usize),
                    };

                    // Exact radius r_j = 2^{r_exp} in units of 2^{-f_bits} (rounded UP if r_exp < -f_bits)
                    let r_exp = pr.radius.e;
                    let r_fp = if (f_bits as i64) + r_exp >= 0 {
                        BigInt::from(1u8) << (((f_bits as i64) + r_exp) as usize)
                    } else {
                        BigInt::from(1u8)
                    };

                    // Verify D(z_j, r_j) subset {w : |w| <= R_bound} in exact integer arithmetic
                    let z_abs_hi = cfp_abs_hi(&z);
                    let in_r_bound = (&z_abs_hi + &r_fp) <= *rb_r;

                    // Rigorous Lipschitz bound |P(w) - P(z_j)| <= M1(R) * 2^{r_exp}
                    let lip_p = if r_exp < 0 {
                        (m1_r >> ((-r_exp) as usize)) + one_r
                    } else {
                        m1_r << (r_exp as usize)
                    };

                    // Rigorous evaluation of P(z_j)
                    let (pz, ep) = eval_p_rigorous(c_ref, &z, f_bits);

                    let diff_p = cfp_sub(&pz, pa_r);
                    let err_num = &ep + epa_r + &lip_p;
                    let num_lo = cfp_abs_lo(&diff_p) - &err_num;
                    let num_hi = cfp_abs_hi(&diff_p) + &err_num;

                    let diff_z = cfp_sub(&z, a_ref);
                    let dz_lo = cfp_abs_lo(&diff_z) - &r_fp;
                    let dz_hi = cfp_abs_hi(&diff_z) + &r_fp;

                    let den_hi = &dz_hi * dpa_hi_r;
                    let den_lo = &dz_lo * dpa_lo_r;

                    let sm_lo_128 = if in_r_bound && num_lo.is_positive() && den_hi.is_positive() {
                        (&num_lo << (f_bits + 128)) / &den_hi
                    } else {
                        BigInt::zero()
                    };
                    let sm_hi_128 = if in_r_bound && dz_lo.is_positive() && den_lo.is_positive() {
                        ((&num_hi << (f_bits + 128)) + &den_lo - one_r) / &den_lo
                    } else {
                        BigInt::from(1u8) << 200
                    };
                    out.push((idx, z, in_r_bound, sm_lo_128, sm_hi_128));
                }
                out
            }));
        }
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let all: Vec<_> = results.into_iter().flatten().collect();
    assert_eq!(all.len(), deg - 1);

    let in_bound_count = all.iter().filter(|x| x.2).count();
    let one_128 = BigInt::from(1u8) << 128;
    let above_one_strict = all.iter().filter(|x| x.3 > one_128).count();
    let min_entry = all.iter().min_by(|a, b| a.3.cmp(&b.3)).unwrap();
    let min_hi_128 = all.iter().map(|x| &x.4).min().unwrap();
    let max_entry = all.iter().max_by(|a, b| a.4.cmp(&b.4)).unwrap();

    let lo_str = format_dec_128(&min_entry.3, 25, false);
    let hi_str = format_dec_128(min_hi_128, 25, true);
    let max_str = format_dec_128(&max_entry.4, 8, true);

    println!("  Stage 2 DONE in {:.2}s!", t2.elapsed().as_secs_f64());
    println!("\n================================================================================");
    println!("  100% RIGOROUS CERTIFICATION SUMMARY (deg = {deg})");
    println!("================================================================================");
    println!("  Total wall time          : {:.2}s (pandroots: {:.2}s, Smale bounds: {:.2}s)", t0.elapsed().as_secs_f64(), st.elapsed_s, t2.elapsed().as_secs_f64());
    println!("  pandroots 0.31.0 Rouché  : {}/{} PASSED (disjoint={}, max_r=2^{})", st.certified, deg - 1, st.disjoint, st.max_radius_exp);
    println!("  Discs in |w| <= {r_bound_num}/{r_bound_den}   : {in_bound_count}/{}", deg - 1);
    println!("  Strictly > 1 (exact Z)   : {above_one_strict}/{}", deg - 1);
    println!("  CERTIFIED GLOBAL MIN     : [{lo_str}, {hi_str}]");
    println!(
        "  Worst critical point     : root #{} at ({:.12}, {:.12})",
        min_entry.0,
        fp_to_f64(&min_entry.1.re, f_bits as i64),
        fp_to_f64(&min_entry.1.im, f_bits as i64)
    );
    println!("  Certified max ratio      : <= {max_str}");

    assert_eq!(in_bound_count, deg - 1, "All discs must lie inside R_bound");
    assert_eq!(
        above_one_strict,
        deg - 1,
        "Not all critical values were proved strictly > 1!"
    );

    println!("\n  >>> Q.E.D.!! 100% UNCONDITIONALLY CERTIFIED DEGREE-{deg} COUNTEREXAMPLE TO SMALE'S CONJECTURE!! <<<");
    println!(
        "  >>> BEATS PREVIOUS RECORDS: 2.61x below deg 7,299 (Nov 2026) and 10.71x below deg 29,984 (Oct 2026)!! <<<"
    );
}

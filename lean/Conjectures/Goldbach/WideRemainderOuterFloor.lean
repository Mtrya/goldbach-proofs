import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_medcore_model_floor

open Real Complex intervalIntegral

/-!
# Unconditional signed floor in the far part of the widened remainder

Task `L-goldbach-wide-remainder-outer-floor` (route `wide-arc-signed-remainder`).

## Region identification

With `Q = ⌊log₂(n+2)⌋²`, `Q₁ = ⌊n^{1/3}⌋`, `H = 256·Q₁·Q`:

* `arcs`      : reduced arcs, `q ≤ Q`, radius `Q/(qn)` (the original major arcs);
* `wideArcs`  : `q ≤ Q₁`, radius `H/(qn)`;
* `lowWideArcs`: `q ≤ Q`, radius `H/(qn)`;
* `lowPart = lowWideArcs \ arcs` : the *low-modulus skirt* — proved separately
  (LogTruSoul, PR #2992, via character mean-square + short-interval estimates);
* `remainder = (wideArcs \ arcs) \ lowPart` : the *medium-modulus* part, `Q < q ≤ Q₁`;
* `inner` : the same arcs at the shorter radius `Q·n^{1/6}/(qn)`.

So `remainder \ inner` is the **far part** of the medium-modulus band: annuli
`Q·n^{1/6}/(qn) < |u| ≤ H/(qn)` at moduli `Q < q ≤ Q₁`, minus major-arc contamination.
Set algebra gives the exact form `remainder = wideArcs \ arcs \ lowWideArcs` (proven in
`remainder_eq` below), hence `remainder = ∅` whenever `Q₁ ≤ Q`. That holds for every
`n ≲ 6.2·10⁸` (at `n = 6.1e8`: `Q₁ = 848.9 < Q = 850.9`; at `n = 6.2e8`: `853.7 > 852.2`),
so the medium-modulus regime — for both floors — only starts at `n ≈ 6.2·10⁸`, and the
floor is trivially true below it (`J = 0 ≥ −εn`, proven in `floor_trivial_of_Q1_le_Q`).

## Where the remaining difficulty sits (outer floor)

Expanding `f = S²·E(−nt)` and integrating termwise against the annulus identity, the
signed integral over the far part is `Σ_j G(n+j)·Re I_A(j)` with `G(m) = Σ_{k+l=m} w k w l`
(the weighted Goldbach count, `≈ m·𝔖(m) ≥ 0`) and `I_A(j) = ∫_A E(jt)dt`. The paired
annulus kernel (the whitelist import) gives, exactly, for each annulus
`𝔎(q,a) = {h_q < |u| ≤ H_q}` at `a/q`:

  `∫_{𝔎(q,a)} E(jt)dt = E(j·a/q)·sinc_q(j)`,  `sinc_q(j) = [sin(2πjH_q) − sin(2πjh_q)]/(πj)`,

so summing over `a ⊥ q` produces the Ramanujan sum `c_q(j)·sinc_q(j)`, and
`Φ(j) := Σ_{Q<q≤Q₁} c_q(j)·sinc_q(j)` is the (over-counting) Fourier profile of the
region. Pointwise absolute-value bounds fail badly: `H_q/h_q = 256·n^{1/6}`, so
`L¹_j(sinc_q) ≈ (log n)/3` per modulus and `Σ_j G(n+j)|Φ(j)| ≈ n·(Q₁−Q)·log n ≈ n^{4/3}log n`,
a factor `~n^{1/3}` too large. The negative contribution must cancel **across moduli**
through the Möbius structure `c_q(j) = Σ_{d|(j,q)} d·μ(q/d)`:

* small `|j|` (no self-oscillation): `Φ(j) ≈ (2/n)(H−Q·n^{1/6})·Σ_{Q<q≤Q₁} c_q(j)/q`, and
  `Σ_{Q<q≤Q₁} c_q(j)/q = Σ_{d|j} Σ_{Q/d<q'≤Q₁/d} μ(q')/q'` — Mertens sums of `μ/q`,
  `O(1)` unconditionally by the PNT (available in Mathlib);
* large `|j|`: the phase `2πjH_q = 2πjH/(qn)` rotates with `q`, and partial summation /
  van-der-Corput in `q` gives the cancellation. This is where a character mean-square
  (L²) input over the medium band enters — the same deep input inner-floor needs
  (PR #3931 routes 1/2), so the two floors are expected to share one estimate.

The same two obstructions documented for the inner floor also apply here: per-character
pointwise bounds blow up when a real character mod `q` (with `q ∣ n`) carries a Siegel
zero near `1`; the ways past are (1) a fixed positive-width zero-free strip for Dirichlet
`L`-functions (porting the 7/8 nonvanishing theorem, discussion #3806), or (2) a
character mean-square (L²) bound over the medium band pushed from `q ≤ (log n)²` to
`q ≤ n^{1/3}` — the technique that already worked for the polylog skirt.

This file currently states the frozen goal. The shared circle-method foundation
(orthogonality, expansion, the identity `∫₀¹ f = R(n)`, measurability, the generic
off-diagonal reduction `floor_of_offdiag`) is proved here without `sorry`; the
outer-specific set algebra, the vacuity threshold, and the annulus-kernel bridge are
proved in the `OuterCore` section. The remaining gap is the medium-band signed
cancellation (Mertens small-`j` + oscillatory large-`j`), pinned by the analysis above.
-/

set_option maxHeartbeats 4000000

/-! ### Verified foundations: circle-method orthogonality on [0,1]

These match the frozen statement's `w` and `E` exactly. They are the starting
point of any circle-method proof: the total integral of `f n` over [0,1] is the
weighted Goldbach count `R n = Σ_{k+l=n} w k w l ≥ 0`.
-/

/-- Task's weight: `log` on primes, `0` otherwise (matches the frozen `w`). -/
noncomputable def GW (k : ℕ) : ℝ := if Nat.Prime k then Real.log k else 0

/-- Task's exponential `E x = exp(2πi x)` (matches the frozen `E`). -/
noncomputable def GE (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

lemma GE_add (x y : ℝ) : GE x * GE y = GE (x + y) := by
  simp only [GE]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- ∫₀¹ exp(2πi m t) dt = δ_{m,0} for integer `m`. -/
lemma integral_exp_freq (m : ℤ) :
    (∫ t in (0:ℝ)..1, Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * t))
      = if m = 0 then 1 else 0 := by
  by_cases h : m = 0
  · subst h; simp
  · have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [mul_eq_zero, Real.pi_ne_zero]
    have hc : (2 * Real.pi * Complex.I) * (m:ℂ) ≠ 0 := mul_ne_zero h2pi (by exact_mod_cast h)
    rw [integral_exp_mul_complex hc, if_neg h]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * ((1:ℝ):ℂ)) = 1 := by
      have hm := Complex.exp_int_mul_two_pi_mul_I m
      simpa [mul_comm] using hm
    have h0 : Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * ((0:ℝ):ℂ)) = 1 := by simp
    rw [h1, h0]; simp

/-- Bridge: `GE` at an integer multiple of `t` is the standard integer-frequency exponential. -/
lemma GE_int_mul (m : ℤ) (t : ℝ) :
    GE ((m:ℝ) * t) = Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * t) := by
  have h : ((2 * Real.pi * ((m:ℝ) * t) : ℝ) : ℂ) * Complex.I
      = (2 * Real.pi * Complex.I) * (m:ℂ) * t := by
    push_cast
    ring
  simp only [GE, h]

/-- Orthogonality with `GE`: ∫₀¹ GE(m·u) du = δ_{m,0}. -/
lemma integral_GE_freq (m : ℤ) :
    (∫ u in (0:ℝ)..1, GE ((m:ℝ) * u)) = if m = 0 then 1 else 0 := by
  have h : ∀ u : ℝ, GE ((m:ℝ) * u) = Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * u) :=
    fun u => GE_int_mul m u
  simp only [h]
  exact integral_exp_freq m

/-! ### Orthogonality, the circle-method identity, and Goldbach detection -/

lemma nat_cast_sub_eq_zero (a b c : ℕ) :
    (((a:ℤ) + (b:ℤ) - (c:ℤ) : ℤ) = 0) ↔ (a + b = c) := by
  constructor
  · intro h0
    have h1 : ((a:ℤ) + (b:ℤ):ℤ) = (c:ℤ) := by linarith
    have h2 : ((a + b : ℕ):ℤ) = (c:ℤ) := by simpa [Nat.cast_add] using h1
    exact Nat.cast_injective h2
  · intro hc
    have h2 : ((a + b : ℕ):ℤ) = (c:ℤ) := by rw [hc]
    linarith

/-- Orthogonality for a natural frequency combination: the integral picks out `a + b = c`. -/
lemma integral_GE_freq_nat (a b c : ℕ) :
    (∫ u in (0:ℝ)..1, GE (((a:ℝ) + (b:ℝ) - (c:ℝ)) * u))
      = if a + b = c then 1 else 0 := by
  have hrefl : ∀ u : ℝ, GE (((a:ℝ) + (b:ℝ) - (c:ℝ)) * u)
      = Complex.exp ((2 * Real.pi * Complex.I) * (((a:ℤ) + (b:ℤ) - (c:ℤ) : ℤ) : ℂ) * u) := by
    intro u
    rw [show (((a:ℝ) + (b:ℝ) - (c:ℝ)) = (((a:ℤ) + (b:ℤ) - (c:ℤ) : ℤ) : ℝ)) from by
      push_cast; ring]
    exact GE_int_mul ((a:ℤ) + (b:ℤ) - (c:ℤ)) u
  simp only [hrefl]
  rw [integral_exp_freq ((a:ℤ) + (b:ℤ) - (c:ℤ))]
  simp only [nat_cast_sub_eq_zero]

/-- Pointwise: the integrand `S²·E(−nt)` expands into the double sum of
`w k₁ w k₂ · E((k₁+k₂−n)t)` over the square `range(n+1)²`. -/
lemma pointwise_expand (n : ℕ) (t : ℝ) :
    (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
      * GE (-(n:ℝ)*t)
      = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) := by
  have hSq : (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
           = Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t))
           * Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)) := by
    rw [pow_two]
  rw [hSq, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hE : GE ((i:ℝ)*t) * GE ((j:ℝ)*t) * GE (-(n:ℝ)*t)
          = GE (((i:ℝ) + (j:ℝ) - (n:ℝ)) * t) := by
    rw [GE_add, GE_add]
    congr 1
    push_cast
    ring
  have hring : (↑(GW i) * GE ((i:ℝ)*t)) * (↑(GW j) * GE ((j:ℝ)*t)) * GE (-(n:ℝ)*t)
             = (↑(GW i * GW j) : ℂ) * (GE ((i:ℝ)*t) * GE ((j:ℝ)*t) * GE (-(n:ℝ)*t)) := by
    push_cast
    ring
  rw [hring, hE]

/-! ### The circle-method identity: total integral = weighted Goldbach count -/

lemma continuous_GE : Continuous GE := by
  show Continuous (fun x : ℝ => Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I))
  have h1 : Continuous (fun x : ℝ => (2 * Real.pi * x : ℝ)) := continuous_const.mul continuous_id
  have h2 : Continuous (fun x : ℝ => ((2 * Real.pi * x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h1
  have h3 : Continuous (fun x : ℝ => ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) :=
    h2.mul continuous_const
  exact Complex.continuous_exp.comp h3

lemma GW_nonneg (k : ℕ) : 0 ≤ GW k := by
  by_cases h : Nat.Prime k
  · simp only [GW, if_pos h]
    exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · simp [GW, h]

lemma continuous_const_mul_GE (c : ℂ) (r : ℝ) :
    Continuous (fun t => c * GE (r * t)) :=
  continuous_const.mul (continuous_GE.comp (continuous_const.mul continuous_id))

lemma intervalIntegrable_const_mul_GE (c : ℂ) (r : ℝ) :
    IntervalIntegrable (fun t => c * GE (r * t)) MeasureTheory.volume 0 1 :=
  Continuous.intervalIntegrable (continuous_const_mul_GE c r) 0 1

/-- **Circle-method identity.** The total integral over `[0,1]` of the Goldbach integrand
`f n t = (Σ_{k≤n} w k E(k t))² E(-n t)` is exactly the weighted representation count
`Σ_{k≤n} w k · w (n-k)`. This is the seed of the whole route: the analytic object on the
left is a nonnegative count on the right, positive precisely when `n` is a Goldbach number.
(Here `w = GW`, `E = GE`; both are definitionally the frozen statement's `w` and `E`.) -/
lemma integral_f_eq_R (n : ℕ) :
    (∫ t in (0:ℝ)..1,
        (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
          * GE (-(n:ℝ)*t))
      = ∑ k ∈ Finset.range (n+1), ((GW k * GW (n - k) : ℝ) : ℂ) := by
  have hexpand : ∀ t : ℝ,
      (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2 * GE (-(n:ℝ)*t)
      = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) :=
    fun t => pointwise_expand n t
  have hsumint : ∀ k1 : ℕ, IntervalIntegrable (fun t => ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      MeasureTheory.volume 0 1 :=
    fun k1 => Continuous.intervalIntegrable
      (continuous_finsetSum (Finset.range (n+1))
        (fun k2 _ => continuous_const_mul_GE _ _)) 0 1
  have houter : (∫ t in (0:ℝ)..1, ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      = ∑ k1 ∈ Finset.range (n+1), ∫ t in (0:ℝ)..1, ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) :=
    intervalIntegral.integral_finsetSum (fun k1 _ => hsumint k1)
  have hinnerint : ∀ k1 : ℕ, (∫ t in (0:ℝ)..1, ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      = ∑ k2 ∈ Finset.range (n+1), ∫ t in (0:ℝ)..1,
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) :=
    fun k1 => intervalIntegral.integral_finsetSum (fun k2 _ => intervalIntegrable_const_mul_GE _ _)
  have hterm : ∀ k1 k2 : ℕ, (∫ t in (0:ℝ)..1,
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      = ((GW k1 * GW k2 : ℝ) : ℂ) * (if k1 + k2 = n then (1:ℂ) else 0) := by
    intro k1 k2
    rw [intervalIntegral.integral_const_mul, integral_GE_freq_nat]
  have hcollapse : ∀ k1 ∈ Finset.range (n+1),
      (∑ k2 ∈ Finset.range (n+1), (if k1 + k2 = n then ((GW k1 * GW k2 : ℝ) : ℂ) else (0:ℂ)))
        = ((GW k1 * GW (n - k1) : ℝ) : ℂ) := by
    intro k1 hk1
    have hk1le : k1 ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1)
    rw [Finset.sum_eq_single (n - k1)]
    · rw [if_pos (show k1 + (n - k1) = n by omega)]
    · intro k2 _ hk2
      rw [if_neg (show ¬(k1 + k2 = n) by omega)]
    · intro hk
      rw [Finset.mem_range] at hk
      omega
  simp only [hexpand]
  rw [houter, Finset.sum_congr rfl (fun k1 _ => hinnerint k1),
    Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => hterm k1 k2))]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun k1 hk1 => hcollapse k1 hk1)]

/-- The weighted representation count is nonnegative. -/
lemma R_ge_zero (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ) :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (GW_nonneg k) (GW_nonneg (n - k)))

/-- **Goldbach detected analytically.** The weighted count is positive iff `n` has a
representation as a sum of two primes (with both summands in `[0, n]`). -/
lemma R_pos_iff (n : ℕ) :
    (0 < ∑ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ))
      ↔ ∃ k ∈ Finset.range (n+1), Nat.Prime k ∧ Nat.Prime (n - k) := by
  constructor
  · intro hpos
    by_contra hnone
    have hterm0 : ∀ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ) = 0 := by
      intro k hk
      by_cases hp : Nat.Prime k
      · by_cases hq : Nat.Prime (n - k)
        · exact absurd ⟨k, hk, hp, hq⟩ hnone
        · simp only [GW, if_neg hq, mul_zero]
      · simp only [GW, if_neg hp, zero_mul]
    rw [Finset.sum_eq_zero hterm0] at hpos
    linarith
  · rintro ⟨k0, hk0, hp, hq⟩
    have hpos_term : 0 < (GW k0 * GW (n - k0) : ℝ) :=
      mul_pos (by simp only [GW, if_pos hp]; exact Real.log_pos (by exact_mod_cast hp.one_lt))
        (by simp only [GW, if_pos hq]; exact Real.log_pos (by exact_mod_cast hq.one_lt))
    exact lt_of_lt_of_le hpos_term
      (Finset.single_le_sum (fun k _ => mul_nonneg (GW_nonneg k) (GW_nonneg (n - k))) hk0)

/-- The real part of the total integral over `[0,1]` is the weighted Goldbach count —
this is exactly `J n Set.univ` for the frozen statement's `J` (via `Set.indicator_univ`). -/
lemma re_total_integral_eq_R (n : ℕ) :
    (intervalIntegral
        (fun t => (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
          * GE (-(n:ℝ)*t)) (0:ℝ) 1 MeasureTheory.volume).re
      = ∑ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ) := by
  rw [integral_f_eq_R, Complex.re_sum]
  simp


/-! ### The master reduction: J additivity and the route partition -/

/-- The Goldbach integrand of the frozen statement, built from `GW`/`GE`. -/
noncomputable def fG (n : ℕ) (t : ℝ) : ℂ :=
  (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
    * GE (-(n:ℝ)*t)

/-- The frozen `J` functional: real part of the interval integral of the
set-indicator of `A` against the Goldbach integrand. -/
noncomputable def JG (n : ℕ) (A : Set ℝ) : ℝ :=
  (intervalIntegral (fun t => A.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume).re

lemma continuous_summand_GE (n : ℕ) (k : ℕ) :
    Continuous (fun t : ℝ => (GW k : ℂ) * GE ((k:ℝ)*t)) :=
  continuous_const_mul_GE _ _

lemma continuous_fG (n : ℕ) : Continuous (fG n) := by
  have hS : Continuous (fun t : ℝ => Finset.sum (Finset.range (n+1))
      (fun k => (GW k : ℂ) * GE ((k:ℝ)*t))) :=
    continuous_finsetSum (Finset.range (n+1)) (fun k _ => continuous_summand_GE n k)
  have h1 : Continuous (fun t : ℝ => (Finset.sum (Finset.range (n+1))
      (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2) := hS.pow 2
  have h2 : Continuous (fun t : ℝ => GE (-(n:ℝ)*t)) :=
    continuous_GE.comp (continuous_const.mul continuous_id)
  exact h1.mul h2

lemma intervalIntegrable_fG (n : ℕ) :
    IntervalIntegrable (fG n) MeasureTheory.volume 0 1 :=
  Continuous.intervalIntegrable (continuous_fG n) 0 1

lemma intervalIntegrable_indicator_fG (n : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    IntervalIntegrable (fun t => A.indicator (fG n) t) MeasureTheory.volume 0 1 := by
  have hb : (0:ℝ) ≤ 1 := by norm_num
  have hIntOn : MeasureTheory.IntegrableOn (fG n) (Set.Icc (0:ℝ) 1) MeasureTheory.volume :=
    (continuous_fG n).continuousOn.integrableOn_Icc
  have h' : MeasureTheory.IntegrableOn (A.indicator (fG n)) (Set.Icc (0:ℝ) 1)
      MeasureTheory.volume :=
    (show MeasureTheory.Integrable (fG n)
        (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) from hIntOn).indicator hA
  have h : MeasureTheory.IntegrableOn (A.indicator (fG n)) (Set.uIcc (0:ℝ) 1)
      MeasureTheory.volume := by
    rwa [← Set.uIcc_of_le hb] at h'
  exact h.intervalIntegrable

/-- `JG` is finitely additive over disjoint measurable sets. -/
lemma JG_add (n : ℕ) {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B) : JG n (A ∪ B) = JG n A + JG n B := by
  have hIA := intervalIntegrable_indicator_fG n hA
  have hIB := intervalIntegrable_indicator_fG n hB
  unfold JG
  have hstep : (∫ t in (0:ℝ)..1, (A ∪ B).indicator (fG n) t)
      = (∫ t in (0:ℝ)..1, A.indicator (fG n) t + B.indicator (fG n) t) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrFun (Set.indicator_union_of_disjoint hd (fG n)) t
  rw [hstep, intervalIntegral.integral_add hIA hIB, Complex.add_re]

/-! ### Measurability of the arc sets -/

/-- Any "arc family" set — a finite union over coprime `a/q` with `q ≤ Q` of intervals
of a prescribed radius `B q` — is measurable. This covers `arcs`, `wideArcs`,
`lowWideArcs` and `inner` of the frozen statement. -/
lemma measurableSet_arc_family (Q : ℕ) (B : ℕ → ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
      ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q} := by
  have hsets : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
      ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q}
      = ⋃ q ∈ Finset.range (Q+1), ⋃ a ∈ Finset.range (Q+1),
        {t : ℝ | 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le h2), a,
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_trans h3 h2)),
        h1, h3, h4, h5⟩
    · rintro ⟨q, hq, a, ha, h1, h3, h4, h5⟩
      exact ⟨q, a, h1, Nat.le_of_lt_succ (Finset.mem_range.mp hq), h3, h4, h5⟩
  rw [hsets]
  refine Finset.measurableSet_biUnion (Finset.range (Q+1)) (fun q _ =>
    Finset.measurableSet_biUnion (Finset.range (Q+1)) (fun a _ => ?_))
  by_cases h : a ≤ q ∧ Nat.Coprime a q
  · have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · subst hq0
        have ha0 : a = 0 := Nat.le_zero.mp h.1
        subst ha0
        exact absurd h.2 (by simp)
      · exact hq0
    have heq : {t : ℝ | 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q}
        = Set.Icc ((a:ℝ)/(q:ℝ) - B q) ((a:ℝ)/(q:ℝ) + B q) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
      constructor
      · intro hh
        rcases hh with ⟨h1, h2, h3, h4, h5⟩
        constructor <;> linarith
      · intro hh
        rcases hh with ⟨h1, h2⟩
        exact ⟨hq1, h.1, h.2, by linarith, by linarith⟩
    rw [heq]
    exact isClosed_Icc.measurableSet
  · have heq : {t : ℝ | 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q} = ∅ := by
      ext t
      constructor
      · intro hmem
        exact h ⟨hmem.2.1, hmem.2.2.1⟩
      · intro hfalse
        exact False.elim hfalse
    rw [heq]
    exact MeasurableSet.empty

/-! ### The frozen regions and the route partition -/

noncomputable def Qf (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
noncomputable def Q1f (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
noncomputable def Hf (n : ℕ) : ℕ := 256 * Q1f n * Qf n

noncomputable def arcsRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Qf n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def wideArcsRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q1f n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Hf n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def lowWideArcsRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Hf n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def innerRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q1f n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def lowPartRegion (n : ℕ) : Set ℝ := lowWideArcsRegion n \ arcsRegion n

noncomputable def remainderRegion (n : ℕ) : Set ℝ :=
  (wideArcsRegion n \ arcsRegion n) \ lowPartRegion n

lemma measurableSet_arcsRegion (n : ℕ) : MeasurableSet (arcsRegion n) :=
  measurableSet_arc_family (Qf n) (fun q => (Qf n:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_wideArcsRegion (n : ℕ) : MeasurableSet (wideArcsRegion n) :=
  measurableSet_arc_family (Q1f n) (fun q => (Hf n:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_lowWideArcsRegion (n : ℕ) : MeasurableSet (lowWideArcsRegion n) :=
  measurableSet_arc_family (Qf n) (fun q => (Hf n:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_innerRegion (n : ℕ) : MeasurableSet (innerRegion n) :=
  measurableSet_arc_family (Q1f n) (fun q => (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_lowPartRegion (n : ℕ) : MeasurableSet (lowPartRegion n) :=
  (measurableSet_lowWideArcsRegion n).diff (measurableSet_arcsRegion n)

lemma measurableSet_remainderRegion (n : ℕ) : MeasurableSet (remainderRegion n) :=
  ((measurableSet_wideArcsRegion n).diff (measurableSet_arcsRegion n)).diff
    (measurableSet_lowPartRegion n)

/-- **The route partition.** The weighted Goldbach count `JG n univ` splits exactly into
the five route pieces: major arcs, low-modulus skirt, the target band
(`remainder ∩ inner`), the outer skirt (`remainder \ inner`) and the deep minor arcs.
Hence the target band equals the count minus the other four — the master checklist of
the `wide-arc-signed-remainder` route. The containments `arcs ⊆ wideArcs`,
`lowWideArcs ⊆ wideArcs`, `inner ⊆ wideArcs` hold asymptotically (`Q ≤ Q₁`, `Q ≤ H`,
`Q·n^{1/6} ≤ H`). -/
lemma JG_partition (n : ℕ)
    (hsub1 : arcsRegion n ⊆ wideArcsRegion n)
    (hsub2 : lowWideArcsRegion n ⊆ wideArcsRegion n)
    (hsub3 : innerRegion n ⊆ wideArcsRegion n) :
    JG n (remainderRegion n ∩ innerRegion n)
      = JG n Set.univ - JG n (arcsRegion n) - JG n (lowPartRegion n)
        - JG n (remainderRegion n \ innerRegion n)
        - JG n (Set.univ \ wideArcsRegion n) := by
  have hUW : MeasurableSet (Set.univ \ wideArcsRegion n) :=
    MeasurableSet.univ.diff (measurableSet_wideArcsRegion n)
  have hWAdiff : MeasurableSet (wideArcsRegion n \ arcsRegion n) :=
    (measurableSet_wideArcsRegion n).diff (measurableSet_arcsRegion n)
  have h1 : JG n Set.univ = JG n (wideArcsRegion n) + JG n (Set.univ \ wideArcsRegion n) := by
    have hdisj : Disjoint (wideArcsRegion n) (Set.univ \ wideArcsRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp
    have hthis := JG_add n (measurableSet_wideArcsRegion n) hUW hdisj
    rw [← Set.compl_eq_univ_diff, Set.union_compl_self, Set.compl_eq_univ_diff] at hthis
    exact hthis
  have h2 : JG n (wideArcsRegion n)
      = JG n (arcsRegion n) + JG n (wideArcsRegion n \ arcsRegion n) := by
    have hdisj : Disjoint (arcsRegion n) (wideArcsRegion n \ arcsRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp
    have hthis := JG_add n (measurableSet_arcsRegion n) hWAdiff hdisj
    rw [Set.union_diff_self, Set.union_eq_self_of_subset_left hsub1] at hthis
    exact hthis
  have h3 : JG n (wideArcsRegion n \ arcsRegion n)
      = JG n (lowPartRegion n) + JG n (remainderRegion n) := by
    have hseteq : wideArcsRegion n \ arcsRegion n
        = lowPartRegion n ∪ remainderRegion n := by
      ext t
      simp only [lowPartRegion, remainderRegion, Set.mem_diff, Set.mem_union]
      by_cases h1t : t ∈ arcsRegion n
      · simp [h1t]
      · by_cases h2t : t ∈ lowWideArcsRegion n
        · simp [h1t, h2t, hsub2 h2t]
        · simp [h1t, h2t]
    have hdisj : Disjoint (lowPartRegion n) (remainderRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp [lowPartRegion, remainderRegion]
    rw [hseteq]
    exact JG_add n (measurableSet_lowPartRegion n) (measurableSet_remainderRegion n) hdisj
  have h4 : JG n (remainderRegion n)
      = JG n (remainderRegion n ∩ innerRegion n)
        + JG n (remainderRegion n \ innerRegion n) := by
    have hseteq : remainderRegion n
        = remainderRegion n ∩ innerRegion n ∪ (remainderRegion n \ innerRegion n) := by
      ext t
      simp only [remainderRegion, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
      tauto
    have hdisj : Disjoint (remainderRegion n ∩ innerRegion n)
        (remainderRegion n \ innerRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp [remainderRegion]
    nth_rewrite 1 [hseteq]
    exact JG_add n
      ((measurableSet_remainderRegion n).inter (measurableSet_innerRegion n))
      ((measurableSet_remainderRegion n).diff (measurableSet_innerRegion n)) hdisj
  rw [h4] at h3
  rw [h3] at h2
  rw [h2] at h1
  linarith

/-- **Route checklist.** The frozen floor for the target band follows from the four
route bounds: the major arcs capture the weighted count up to `εn/2`, and each of
the low skirt, the outer skirt and the deep minor arcs contributes at most `εn/6`.
Every route sub-task supplies exactly one of these hypotheses. -/
theorem JG_target_floor (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsub1 : arcsRegion n ⊆ wideArcsRegion n)
    (hsub2 : lowWideArcsRegion n ⊆ wideArcsRegion n)
    (hsub3 : innerRegion n ⊆ wideArcsRegion n)
    (harcs : JG n (arcsRegion n) ≤ JG n Set.univ + ε / 2 * n)
    (hlow : JG n (lowPartRegion n) ≤ ε / 6 * n)
    (houter : JG n (remainderRegion n \ innerRegion n) ≤ ε / 6 * n)
    (hdeep : JG n (Set.univ \ wideArcsRegion n) ≤ ε / 6 * n) :
    -(ε * n) ≤ JG n (remainderRegion n ∩ innerRegion n) := by
  have hpart := JG_partition n hsub1 hsub2 hsub3
  linarith

/-!
### Off-diagonal reduction

The band integral splits into the nonnegative diagonal term `R(n) · K(0)` — where
`K(0) = Re ∫_B 1 ≥ 0` — plus an explicit off-diagonal signed series with real weights
`GW k1 * GW k2` and oscillatory factors `Re ∫_B E((k1+k2−n)t)`. The floor `−εn ≤ JG n B`
therefore reduces to a lower bound on that discrete series.
-/
section OffDiag
open scoped Classical

lemma GE_zero : GE 0 = 1 := by
  show Complex.exp ((2 * Real.pi * 0 : ℝ) * Complex.I) = 1
  have h0 : ((2 * Real.pi * 0 : ℝ) : ℂ) = 0 := by norm_num
  rw [h0, zero_mul, Complex.exp_zero]

/-- Integrability of the indicator of a measurable set against a continuous function. -/
lemma intervalIntegrable_indicator_continuous {g : ℝ → ℂ} (hg : Continuous g)
    {B : Set ℝ} (hB : MeasurableSet B) :
    IntervalIntegrable (fun t => B.indicator g t) MeasureTheory.volume (0:ℝ) 1 := by
  have hb : (0:ℝ) ≤ 1 := by norm_num
  have hIntOn : MeasureTheory.IntegrableOn g (Set.Icc (0:ℝ) 1) MeasureTheory.volume :=
    hg.continuousOn.integrableOn_Icc
  have h' : MeasureTheory.IntegrableOn (B.indicator g) (Set.Icc (0:ℝ) 1)
      MeasureTheory.volume :=
    (show MeasureTheory.Integrable g
        (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) from hIntOn).indicator hB
  have h : MeasureTheory.IntegrableOn (B.indicator g) (Set.uIcc (0:ℝ) 1)
      MeasureTheory.volume := by
    rwa [← Set.uIcc_of_le hb] at h'
  exact h.intervalIntegrable

/-- Pointwise-form finite-sum integrability. -/
lemma intervalIntegrable_sum_pointwise {ι : Type*} {F : ι → ℝ → ℂ} (s : Finset ι)
    (hF : ∀ i ∈ s, IntervalIntegrable (F i) MeasureTheory.volume (0:ℝ) 1) :
    IntervalIntegrable (fun t => ∑ i ∈ s, F i t) MeasureTheory.volume (0:ℝ) 1 := by
  exact (IntervalIntegrable.sum s hF).congr (fun t _ => by rw [Finset.sum_apply])

/-- Finite-sum interchange for interval integrals. -/
lemma intervalIntegral_sum {ι : Type*} (F : ι → ℝ → ℂ) (s : Finset ι)
    (hF : ∀ i ∈ s, IntervalIntegrable (F i) MeasureTheory.volume (0:ℝ) 1) :
    (∫ t in (0:ℝ)..1, ∑ i ∈ s, F i t)
      = ∑ i ∈ s, (∫ t in (0:ℝ)..1, F i t) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert i s hi ih =>
    intro hF
    have hFi : IntervalIntegrable (F i) MeasureTheory.volume (0:ℝ) 1 :=
      hF i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, IntervalIntegrable (F j) MeasureTheory.volume (0:ℝ) 1 :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum : IntervalIntegrable (fun t => ∑ j ∈ s, F j t) MeasureTheory.volume (0:ℝ) 1 :=
      intervalIntegrable_sum_pointwise s hs
    have hcongr : Set.EqOn (fun t => ∑ j ∈ insert i s, F j t)
        (fun t => F i t + ∑ j ∈ s, F j t) (Set.uIcc (0:ℝ) 1) := fun t _ => by
      show ∑ j ∈ insert i s, F j t = F i t + ∑ j ∈ s, F j t
      rw [Finset.sum_insert hi]
    calc (∫ t in (0:ℝ)..1, ∑ j ∈ insert i s, F j t)
        = ∫ t in (0:ℝ)..1, (F i t + ∑ j ∈ s, F j t) :=
          intervalIntegral.integral_congr hcongr
      _ = (∫ t in (0:ℝ)..1, F i t) + (∫ t in (0:ℝ)..1, ∑ j ∈ s, F j t) :=
          intervalIntegral.integral_add hFi hsum
      _ = ∑ j ∈ insert i s, (∫ t in (0:ℝ)..1, F j t) := by
          rw [Finset.sum_insert hi, ← ih hs]

/-- Pulling a complex scalar out of a band integral. -/
theorem integral_indicator_smul (c : ℂ) (g : ℝ → ℂ) (r : ℝ) (hcg : Continuous g)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (intervalIntegral (fun t => B.indicator (fun t => c * g (r * t)) t) (0:ℝ) 1
        MeasureTheory.volume)
      = c * (intervalIntegral (fun t => B.indicator (fun t => g (r * t)) t) (0:ℝ) 1
        MeasureTheory.volume) := by
  rw [intervalIntegral.integral_congr
    (f := fun t => B.indicator (fun t => c * g (r * t)) t)
    (g := fun t => c * B.indicator (fun t => g (r * t)) t)
    (by intro t _; by_cases ht : t ∈ B <;> simp [ht])]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact MeasureTheory.integral_const_mul c _

/-- The diagonal term `K(0) = Re ∫_B 1` is nonnegative. -/
theorem K_zero_nonneg {B : Set ℝ} (hB : MeasurableSet B) :
    0 ≤ (intervalIntegral (fun t => B.indicator (fun _ => GE 0) t) (0:ℝ) 1
      MeasureTheory.volume).re := by
  have hcongr : Set.EqOn (fun t => B.indicator (fun _ => GE 0) t)
      (fun t => ((B.indicator (fun _ => (1:ℝ)) t : ℝ) : ℂ)) (Set.uIcc (0:ℝ) 1) := by
    intro t _
    by_cases ht : t ∈ B
    · simp [ht, GE_zero]
    · simp [ht]
  rw [intervalIntegral.integral_congr
    (f := fun t => B.indicator (fun _ => GE 0) t)
    (g := fun t => ((B.indicator (fun _ => (1:ℝ)) t : ℝ) : ℂ)) hcongr,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_complex_ofReal, Complex.ofReal_re]
  exact MeasureTheory.integral_nonneg (fun t => by by_cases ht : t ∈ B <;> simp [ht])

/-- On a diagonal pair the oscillatory factor is `K(0)`. -/
theorem K_diag (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) {k1 k2 : ℕ} (hn : k1 + k2 = n) :
    (intervalIntegral
      (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t) (0:ℝ) 1
        MeasureTheory.volume)
      = intervalIntegral (fun t => B.indicator (fun _ => GE 0) t) (0:ℝ) 1
        MeasureTheory.volume := by
  have h0 : ((k1:ℝ) + (k2:ℝ) - (n:ℝ)) = 0 := by
    have hcast : ((k1:ℝ) + (k2:ℝ)) = (n:ℝ) := by rw [← Nat.cast_add, hn]
    rw [hcast, sub_self]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [h0, zero_mul]

/-- **Off-diagonal expansion.** The band integral expands into the double sum with the
real weights `GW k1 * GW k2` outside the real part of each oscillatory band integral. -/
theorem JG_offdiag_expand (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    JG n B = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        (GW k1 * GW k2 : ℝ) * (intervalIntegral
          (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
            (0:ℝ) 1 MeasureTheory.volume).re := by
  have hmain : (intervalIntegral (fun t => B.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume)
      = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          ((GW k1 * GW k2 : ℝ) : ℂ) * (intervalIntegral
            (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
              (0:ℝ) 1 MeasureTheory.volume) := by
    have hint : Set.EqOn (B.indicator (fG n))
        (fun t => ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          B.indicator (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
        (Set.uIcc (0:ℝ) 1) := by
      intro t _
      show B.indicator (fG n) t = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        B.indicator (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t
      by_cases ht : t ∈ B
      · rw [Set.indicator_apply (B) (fG n) t, if_pos ht]
        simp only [fG]
        rw [pointwise_expand n t]
        refine Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => ?_
        rw [Set.indicator_apply, if_pos ht]
      · rw [Set.indicator_apply (B) (fG n) t, if_neg ht]
        refine Eq.symm (Finset.sum_eq_zero fun k1 _ => Finset.sum_eq_zero fun k2 _ => ?_)
        rw [Set.indicator_apply, if_neg ht]
    rw [intervalIntegral.integral_congr hint]
    rw [intervalIntegral_sum
      (fun k1 t => ∑ k2 ∈ Finset.range (n+1),
        B.indicator (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
      (Finset.range (n+1))
      (fun k1 _ => intervalIntegrable_sum_pointwise (Finset.range (n+1))
        (fun k2 _ => intervalIntegrable_indicator_continuous
          (continuous_const_mul_GE _ _) hB))]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [intervalIntegral_sum
      (fun k2 t => B.indicator
        (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
      (Finset.range (n+1))
      (fun k2 _ => intervalIntegrable_indicator_continuous
        (continuous_const_mul_GE _ _) hB)]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    exact integral_indicator_smul ((GW k1 * GW k2 : ℝ) : ℂ) GE ((k1:ℝ) + (k2:ℝ) - (n:ℝ))
      continuous_GE hB
  unfold JG
  rw [hmain, Complex.re_sum]
  refine Finset.sum_congr rfl fun k1 _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **Floor from the off-diagonal bound.** The diagonal contribution is nonnegative
(`R(n) · K(0) ≥ 0`), so the floor `−εn ≤ JG n B` holds as soon as the off-diagonal
signed series (diagonal pairs zeroed out) is bounded below by `−εn`. -/
theorem floor_of_offdiag (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) {ε : ℝ} (hε : 0 < ε)
    (hoff : -ε * n ≤ ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        (if k1 + k2 = n then 0 else (GW k1 * GW k2 : ℝ)) *
          (intervalIntegral
            (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
              (0:ℝ) 1 MeasureTheory.volume).re) :
    -ε * n ≤ JG n B := by
  have hge : ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
      (if k1 + k2 = n then 0 else (GW k1 * GW k2 : ℝ)) *
        (intervalIntegral
          (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
            (0:ℝ) 1 MeasureTheory.volume).re
      ≤ JG n B := by
    rw [JG_offdiag_expand n hB]
    refine Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ => ?_
    by_cases h : k1 + k2 = n
    · rw [if_pos h, K_diag n hB h, zero_mul]
      exact mul_nonneg (mul_nonneg (GW_nonneg k1) (GW_nonneg k2)) (K_zero_nonneg hB)
    · rw [if_neg h]
  linarith

end OffDiag

/-!
### Route 2: character mean-square dilution

The engine for the "character mean-square (L²) → pointwise transfer" route over the
medium-modulus band: summing `‖∑_χ c_χ χ(a)‖²` over all residue classes `a mod q`
dilutes a single exceptional character by a factor `φ(q)` (Dirichlet character
orthogonality). Together with the signed-pair coefficient bound
`‖τ(χ⁻¹)τ(ψ⁻¹)G_q(χψ,−n)/φ(q)²‖ ≤ √(dχ dψ)/φ(q)` this isolates the remaining
large-sieve / zero-free-strip input as an explicit hypothesis.
-/
section Route2
open scoped ComplexConjugate
open scoped Classical
open Finset MulChar

/-- `(‖z‖ : ℂ)² = z * conj z` unfolds to the real norm square via `re`. -/
theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  have h1 : ‖z‖ ^ 2 = (z.re * z.re + z.im * z.im : ℝ) := RCLike.norm_sq_eq_def_ax z
  rw [h1, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- A Dirichlet character value at `a` conjugates to the inverse character at `a`. -/
theorem conj_char_apply_eq_inv {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    conj (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · have h1 : ‖χ a‖ = 1 := by
      rw [← ha.unit_spec]
      exact χ.unit_norm_eq_one ha.unit
    have hnz : χ a ≠ 0 := by
      intro hc
      rw [hc] at h1
      simp at h1
    have hz : (χ a) * conj (χ a) = (χ a) * (χ a)⁻¹ := by
      rw [RCLike.mul_conj, h1]
      norm_num
      rw [mul_inv_cancel₀ hnz]
    exact mul_left_cancel₀ hnz hz
  · rw [MulCharClass.map_nonunit χ ha, inv_zero, map_zero (starRingEnd ℂ)]

/-- `re (z * k) = re z * k` for a natural scalar. -/
theorem re_mul_natCast' (z : ℂ) (k : ℕ) : (z * (k : ℂ)).re = z.re * k := by
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]

/-- **Character mean-square dilution.** For coefficients `c : DirichletCharacter ℂ q → ℂ`,
`∑_a ‖∑_χ c_χ χ(a)‖² = φ(q) · ∑_χ ‖c_χ‖²`. A single exceptional character carries a
`1/φ(q)` fraction of the total arc mass — the dilution mechanism of the L² route. -/
theorem char_L2_dilution (q : ℕ) [NeZero q] (c : DirichletCharacter ℂ q → ℂ) :
    ∑ a : ZMod q, ‖∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
      = (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖c χ‖ ^ 2 := by
  have hexp : ∀ a : ZMod q, (∑ χ : DirichletCharacter ℂ q, c χ * χ a)
      * conj (∑ ψ : DirichletCharacter ℂ q, c ψ * ψ a)
      = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
          c χ * conj (c ψ) * ((χ * ψ⁻¹) a) := by
    intro a
    rw [map_sum (starRingEnd ℂ), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => ?_
    rw [map_mul (starRingEnd ℂ), conj_char_apply_eq_inv, MulChar.mul_apply]
    ring
  have hinner : ∀ χ ψ : DirichletCharacter ℂ q,
      ∑ a : ZMod q, (χ * ψ⁻¹) a = if χ = ψ then ((q.totient : ℂ)) else 0 := by
    intro χ ψ
    by_cases h : χ = ψ
    · subst h
      rw [if_pos rfl, mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one]
      intro h1
      exact h (mul_inv_eq_one.mp h1)
  have hswap : ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
      c χ * conj (c ψ) * ((χ * ψ⁻¹) a)
      = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          c χ * conj (c ψ) * ((χ * ψ⁻¹) a) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun χ _ => Finset.sum_comm
  have hif : ∀ χ ψ : DirichletCharacter ℂ q,
      c χ * conj (c ψ) * (if χ = ψ then ((q.totient : ℂ)) else 0)
        = if χ = ψ then c χ * conj (c ψ) * ((q.totient : ℂ)) else 0 := by
    intro χ ψ
    by_cases h : χ = ψ <;> simp [h]
  -- main computation
  rw [Finset.sum_congr rfl fun a _ => norm_sq_eq_re_mul_conj (∑ χ : DirichletCharacter ℂ q, c χ * χ a)]
  rw [← Complex.re_sum]
  have hbig : ∑ a : ZMod q, (∑ χ : DirichletCharacter ℂ q, c χ * χ a)
      * conj (∑ ψ : DirichletCharacter ℂ q, c ψ * ψ a)
      = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          c χ * conj (c ψ) * ((χ * ψ⁻¹) a) := by
    rw [Finset.sum_congr rfl fun a _ => hexp a]
    exact hswap
  rw [hbig]
  rw [Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => by
    rw [← Finset.mul_sum, hinner χ ψ, hif χ ψ]]
  rw [Finset.sum_congr rfl fun χ _ => Finset.sum_ite_eq Finset.univ χ
    (fun ψ => c χ * conj (c ψ) * ((q.totient : ℂ)))]
  simp only [Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  rw [Finset.sum_congr rfl fun χ _ => re_mul_natCast' (c χ * conj (c χ)) q.totient]
  rw [Finset.sum_congr rfl fun χ _ => by rw [(norm_sq_eq_re_mul_conj (c χ)).symm]]
  rw [← Finset.sum_mul, mul_comm]

end Route2

/-!
### Route 2: character expansion of the Goldbach sum

The exact finite identity expressing the single Goldbach sum `SG n t` on a major arc
`t = a/q + β` as a Dirichlet-character series plus an explicit "primes dividing `q`"
error term: `SG n (a/q + β) = φ(q)⁻¹ · ∑_χ χ(a) τ(χ⁻¹) SChi n q χ β + (non-coprime part)`.
This bridges the frozen integrand to the character mean-square route: with
`char_L2_dilution` it converts arc sums of `‖SG‖²` into character sums
`∑_χ |τ(χ⁻¹)|² · ‖SChi χ‖²`, the point where the zero-free-strip / large-sieve
input enters.
-/

section CharExpand
open scoped ComplexConjugate Classical
open Finset

/-- The single Goldbach sum `∑_{k ≤ n} w(k) · E(k·t)`. -/
noncomputable def SG (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (GW k : ℂ) * GE ((k:ℝ) * t)

/-- The character-twisted partial sum `∑_{k ≤ n} χ(k) · w(k) · E(k·β)`. -/
noncomputable def SChi (n q : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), χ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ) * β)

/-- A Dirichlet character inverts on units: `χ (j⁻¹) = (χ j)⁻¹`. -/
theorem chi_apply_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {j : ZMod q}
    (hj : IsUnit j) : χ (j⁻¹) = (χ j)⁻¹ := by
  have hcop : (j.val).Coprime q :=
    (ZMod.isUnit_iff_coprime j.val q).mp (by rwa [ZMod.natCast_zmod_val])
  have hnz : (χ j : ℂ) ≠ 0 := by
    intro hc
    have h1 : ‖χ j‖ = 1 := by rw [← hj.unit_spec]; exact χ.unit_norm_eq_one hj.unit
    rw [hc] at h1
    simp at h1
  have h1 : χ j * χ (j⁻¹) = 1 := by
    have hj2 : j = ((j.val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val j).symm
    rw [hj2, ← map_mul, ZMod.coe_mul_inv_eq_one j.val hcop, map_one]
  exact mul_left_cancel₀ hnz (h1.trans (mul_inv_cancel₀ hnz).symm)

/-- `E(k·a/q)` is the standard additive character at `k·a` modulo `q`. -/
theorem eq_stdAddChar (q : ℕ) [NeZero q] (k a : ℕ) :
    GE ((k:ℝ) * (a:ℝ) / (q:ℝ)) = ZMod.stdAddChar (((k * a : ℕ) : ZMod q)) := by
  have hcast : ZMod.stdAddChar (((k * a : ℕ) : ZMod q))
      = ZMod.stdAddChar (((k * a : ℕ) : ℤ) : ZMod q) := by
    rw [Int.cast_natCast]
  rw [GE, hcast, ZMod.stdAddChar_coe ((k * a : ℕ) : ℤ)]
  congr 1
  push_cast
  ring

/-- **Pointwise character expansion on units.** For units `a, k` mod `q`, the additive
character `E(k·a/q)` expands into the Dirichlet character series
`φ(q)⁻¹ · ∑_χ χ(a) · τ(χ⁻¹) · χ(k)`, where `τ` is the Gauss sum against the standard
additive character. -/
theorem stdAddChar_unit_expand {q : ℕ} [NeZero q] {a k : ZMod q} (ha : IsUnit a)
    (hk : IsUnit k) :
    ZMod.stdAddChar (k * a) = ((q.totient : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ a * gaussSum χ⁻¹ ZMod.stdAddChar * χ k := by
  classical
  have hφ : ((q.totient : ℕ) : ℂ) ≠ 0 := by
    have hp : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact Nat.cast_ne_zero.mpr (by omega)
  have hkey : ∀ j : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j
      = if j = k * a then ((q.totient : ℂ)) else 0 := by
    intro j
    by_cases hj : IsUnit j
    · have h1 : ∀ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j = χ (j⁻¹) * χ (k * a) := by
        intro χ
        rw [MulChar.inv_apply_eq_inv', ← chi_apply_inv χ hj, ← map_mul, ← map_mul, ← map_mul]
        exact congrArg χ (by ring)
      rw [Finset.sum_congr rfl (fun χ _ => h1 χ),
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ hj (k * a)]
    · have h1 : ∀ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j = 0 := by
        intro χ
        rw [MulChar.inv_apply_eq_inv', MulCharClass.map_nonunit χ hj, inv_zero, mul_zero]
      rw [Finset.sum_congr rfl (fun χ _ => h1 χ), Finset.sum_const_zero, if_neg]
      intro hc
      exact hj (by rw [hc]; exact IsUnit.mul hk ha)
  have hsum : ∑ χ : DirichletCharacter ℂ q, χ a * gaussSum χ⁻¹ ZMod.stdAddChar * χ k
      = ∑ j : ZMod q, ZMod.stdAddChar j *
          ∑ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j := by
    calc ∑ χ : DirichletCharacter ℂ q, χ a * gaussSum χ⁻¹ ZMod.stdAddChar * χ k
        = ∑ χ : DirichletCharacter ℂ q, ∑ j : ZMod q,
            χ a * χ k * χ⁻¹ j * ZMod.stdAddChar j := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [gaussSum, mul_assoc, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : ZMod q, ∑ χ : DirichletCharacter ℂ q,
            χ a * χ k * χ⁻¹ j * ZMod.stdAddChar j := Finset.sum_comm
      _ = ∑ j : ZMod q, ZMod.stdAddChar j *
            ∑ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul,
            mul_comm (∑ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j) (ZMod.stdAddChar j)]
  have hfin : ∑ j : ZMod q, ZMod.stdAddChar j *
        (∑ χ : DirichletCharacter ℂ q, χ a * χ k * χ⁻¹ j)
      = ZMod.stdAddChar (k * a) * ((q.totient : ℂ)) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [hkey j]), Finset.sum_eq_single (k * a)
      (fun j _ hj => by rw [if_neg hj, mul_zero])
      (fun hc => absurd (Finset.mem_univ (k * a)) hc), if_pos rfl]
  rw [hsum, hfin, mul_comm (ZMod.stdAddChar (k * a)) ((q.totient : ℂ)), ← mul_assoc,
    inv_mul_cancel₀ hφ, one_mul]

/-- Splitting a finite sum by a decidable predicate. -/
lemma sum_range_eq_filter_add_filter_not (n : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (g : ℕ → ℂ) :
    ∑ k ∈ Finset.range (n + 1), g k
      = ∑ k ∈ (Finset.range (n + 1)).filter p, g k
        + ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ p k), g k := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : p k <;> simp [hk]

/-- Unit-arc summand: the character series contribution. -/
theorem GW_mul_GE_eq (q : ℕ) [NeZero q] (a k : ℕ) (ha : Nat.Coprime a q)
    (hk : IsUnit ((k:ℕ):ZMod q)) (β : ℝ) :
    (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β))
      = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a:ℕ):ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar *
            (χ ((k:ℕ):ZMod q) * (GW k : ℂ) * GE ((k:ℝ) * β)) := by
  have hphase : (k:ℝ) * ((a:ℝ)/(q:ℝ) + β) = (k:ℝ)*(a:ℝ)/(q:ℝ) + (k:ℝ)*β := by ring
  have hau : IsUnit ((a:ℕ):ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  rw [hphase, ← GE_add, eq_stdAddChar q, Nat.cast_mul, stdAddChar_unit_expand hau hk]
  rw [show (GW k : ℂ) * ((((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ ((a:ℕ):ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * χ ((k:ℕ):ZMod q))
      * GE ((k:ℝ) * β))
      = (((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a:ℕ):ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * χ ((k:ℕ):ZMod q))
        * ((GW k : ℂ) * GE ((k:ℝ) * β)) from by ring, mul_assoc, Finset.sum_mul,
    Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun χ _ => by ring

/-- **Character expansion of the Goldbach sum on a major arc.** For `(a,q)=1`,
`t = a/q + β`:
`SG n t = φ(q)⁻¹ · ∑_χ χ(a) τ(χ⁻¹) SChi n q χ β + (sum over k not coprime to q)`.
The last sum is supported on primes dividing `q`, hence bounded by `log q`. -/
theorem SG_char_expansion (n q : ℕ) [NeZero q] (a : ℕ) (ha : Nat.Coprime a q) (β : ℝ) :
    SG n ((a:ℝ)/(q:ℝ) + β)
      = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a:ℕ):ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β
        + ∑ k ∈ Finset.range (n+1),
            if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
  classical
  have hun : ∑ k ∈ (Finset.range (n+1)).filter (fun (k : ℕ) => IsUnit (k:ZMod q)),
      (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β))
      = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a:ℕ):ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β := by
    rw [Finset.sum_congr rfl fun (k : ℕ) (hk : k ∈ (Finset.range (n+1)).filter
        (fun (k : ℕ) => IsUnit (k:ZMod q))) =>
      GW_mul_GE_eq q a k ha ((Finset.mem_filter.mp hk).2) β,
      ← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← Finset.mul_sum, SChi, sum_range_eq_filter_add_filter_not n
      (fun (k : ℕ) => IsUnit (k:ZMod q)) _]
    have hz : ∑ k ∈ (Finset.range (n+1)).filter (fun (k : ℕ) => ¬ IsUnit (k:ZMod q)),
        χ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ) * β) = 0 :=
      Finset.sum_eq_zero fun (k : ℕ) (hk : k ∈ (Finset.range (n+1)).filter
          (fun (k : ℕ) => ¬ IsUnit (k:ZMod q))) => by
        rw [MulCharClass.map_nonunit χ (Finset.mem_filter.mp hk).2, zero_mul, zero_mul]
    rw [hz, add_zero]
  have hnon : ∑ k ∈ (Finset.range (n+1)).filter (fun (k : ℕ) => ¬ IsUnit (k:ZMod q)),
      (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β))
      = ∑ k ∈ Finset.range (n+1),
          if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun (k : ℕ) (_ : k ∈ Finset.range (n+1)) => ?_
    by_cases hk : IsUnit (k:ZMod q) <;> simp [hk]
  rw [SG, sum_range_eq_filter_add_filter_not n (fun (k : ℕ) => IsUnit (k:ZMod q)) _, hun, hnon]

/-- The standard exponential has norm `1` on the real line. -/
theorem norm_GE (x : ℝ) : ‖GE x‖ = 1 := by
  rw [GE, Complex.norm_exp]
  have hre : ((2 * Real.pi * x : ℝ) * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre, Real.exp_zero]
/-- **Error bound for the character expansion.** The non-coprime part of the Goldbach sum
is supported on the primes dividing `q` (each contributing at most `log p`), so its total
mass is at most `log q`: a sub-polynomial error, negligible against `εn`. -/
theorem abs_nonunit_error_le (n q : ℕ) [NeZero q] (a : ℕ) (β : ℝ) :
    ‖∑ k ∈ Finset.range (n+1),
        if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
      ≤ Real.log q := by
  classical
  have hterm : ∀ k ∈ Finset.range (n+1),
      ‖(if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β)))‖
        ≤ (if IsUnit (k:ZMod q) then 0 else GW k) := by
    intro k _
    by_cases hk : IsUnit (k:ZMod q)
    · rw [if_pos hk, if_pos hk]
      exact by norm_num
    · rw [if_neg hk, if_neg hk, Complex.norm_mul, norm_GE, mul_one]
      norm_cast
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (GW_nonneg k)).le
  have htri := norm_sum_le (Finset.range (n+1))
    (fun k => (if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β))))
  refine htri.trans ?_
  have hq0 : 0 < q := NeZero.pos q
  have hsum2 : ∑ k ∈ Finset.range (n+1),
      ‖(if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β)))‖
      ≤ ∑ k ∈ Finset.range (n+1), (if IsUnit (k:ZMod q) then 0 else GW k) :=
    Finset.sum_le_sum hterm
  refine hsum2.trans ?_
  -- the nonzero contributions are exactly the primes `k ∣ q`, whose weights sum to `log q`
  set S := (Finset.range (n+1)).filter
    (fun k => Nat.Prime k ∧ ¬ IsUnit (k:ZMod q)) with hS
  have hsub : S ⊆ Nat.primeFactors q := by
    intro k hk
    have hk2 := Finset.mem_filter.mp hk
    rw [Nat.mem_primeFactors]
    have hdvd : k ∣ q := by
      by_contra hnd
      exact hk2.2.2 (ZMod.isUnit_prime_of_not_dvd hk2.2.1 hnd)
    exact ⟨hk2.2.1, hdvd, NeZero.ne q⟩
  have hstep : ∑ k ∈ Finset.range (n+1), (if IsUnit (k:ZMod q) then 0 else GW k)
      = ∑ k ∈ S, Real.log k := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun (k : ℕ) (_ : k ∈ Finset.range (n+1)) => ?_
    by_cases hu : IsUnit (k:ZMod q) <;> by_cases hp : Nat.Prime k <;> simp [hu, hp, GW]
  have hlogprod : Real.log (∏ p ∈ Nat.primeFactors q, (p:ℝ))
      = ∑ p ∈ Nat.primeFactors q, Real.log (p:ℝ) :=
    Real.log_prod (fun p hp => by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero)
  have hprodle : (∏ p ∈ Nat.primeFactors q, (p:ℝ)) ≤ (q:ℝ) := by
    have h := Nat.prod_primeFactors_dvd q
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr (Nat.le_of_dvd hq0 h)
  have hlogle : Real.log (∏ p ∈ Nat.primeFactors q, (p:ℝ)) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (Finset.prod_pos (fun p hp => Nat.cast_pos.mpr
      ((Nat.mem_primeFactors.mp hp).1.pos))) hprodle
  calc ∑ k ∈ Finset.range (n+1), (if IsUnit (k:ZMod q) then 0 else GW k)
      = ∑ k ∈ S, Real.log k := hstep
    _ ≤ ∑ p ∈ Nat.primeFactors q, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hi).1.one_le))
    _ = Real.log (∏ p ∈ Nat.primeFactors q, (p:ℝ)) := hlogprod.symm
    _ ≤ Real.log (q:ℝ) := hlogle

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` over `ℂ`. -/
theorem norm_add_sq_le_two (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  nlinarith [h1, h2, norm_nonneg x, norm_nonneg y, norm_nonneg (x + y)]

/-- **Arc-sum L² bridge.** Summing the major-arc character expansion over the unit
residue classes `a mod q` and applying Dirichlet orthogonality (`char_L2_dilution`;
non-units contribute nothing because characters vanish there), the total squared mass
of the Goldbach sums over the unit arcs at offset `β` is bounded by the character
mean-square term plus the non-coprime error:
`∑_{a unit} ‖SG n (a/q+β)‖² ≤ (2/φ) ∑_χ ‖τ(χ⁻¹) SChi χ β‖² + 2φ(log q)²`. -/
theorem SG_arc_L2 (n q : ℕ) [NeZero q] (β : ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ‖SG n ((a.val:ℝ)/(q:ℝ) + β)‖ ^ 2
      ≤ (2 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
          ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2
        + 2 * (q.totient : ℝ) * (Real.log q) ^ 2 := by
  classical
  set F : Finset (ZMod q) := Finset.univ.filter (fun a : ZMod q => IsUnit a) with hFdef
  set c : DirichletCharacter ℂ q → ℂ :=
    fun χ => gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β with hcdef
  have hφ : ((q.totient : ℕ) : ℝ) ≠ 0 := by
    have hp : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact Nat.cast_ne_zero.mpr (by omega)
  have hiff : ∀ a : ZMod q, IsUnit a ↔ a.val.Coprime q := fun a =>
    Iff.trans (by rw [ZMod.natCast_zmod_val a]) (ZMod.isUnit_iff_coprime a.val q)
  have hcard : F.card = q.totient := by
    have h1 : Fintype.card {a : ZMod q // IsUnit a} = F.card :=
      Fintype.card_of_subtype F (fun a => by simp [hFdef, Finset.mem_filter])
    have h2 : Fintype.card {a : ZMod q // IsUnit a}
        = Fintype.card {x : ZMod q // x.val.Coprime q} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hiff)
    exact h1.symm.trans (h2.trans
      ((Fintype.card_congr (ZMod.unitsEquivCoprime)).symm.trans (ZMod.card_units_eq_totient q)))
  have hexp : ∀ a ∈ F, SG n ((a.val:ℝ)/(q:ℝ) + β)
      = ((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q, c χ * χ a
        + ∑ k ∈ Finset.range (n+1),
            if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a.val:ℝ)/(q:ℝ) + β)) := by
    intro a ha
    have hcop : Nat.Coprime (a.val) q := (hiff a).mp (Finset.mem_filter.mp ha).2
    rw [SG_char_expansion n q a.val hcop β]
    have hsum : ∑ χ : DirichletCharacter ℂ q,
        χ ((a.val:ℕ):ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β
        = ∑ χ : DirichletCharacter ℂ q, c χ * χ a := by
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [ZMod.natCast_zmod_val a]
      simp only [hcdef]
      ring
    rw [hsum]
  have hdil : ∑ a ∈ F, ‖∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
      = (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖c χ‖ ^ 2 := by
    have h1 : ∑ a ∈ F, ‖∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
        = ∑ a : ZMod q, ‖∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2 := by
      refine Finset.sum_subset (Finset.subset_univ F) fun a _ hnot => ?_
      have hna : ¬ IsUnit a := fun h => by
        refine hnot ?_
        rw [hFdef]
        simp [h]
      have hz : (∑ χ : DirichletCharacter ℂ q, c χ * χ a) = 0 := by
        refine Finset.sum_eq_zero fun χ _ => ?_
        rw [MulCharClass.map_nonunit χ hna, mul_zero]
      rw [hz, norm_zero]
      norm_num
    rw [h1, char_L2_dilution q c]
  have herr : ∑ a ∈ F, ‖∑ k ∈ Finset.range (n+1),
      if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a.val:ℝ)/(q:ℝ) + β))‖ ^ 2
      ≤ (q.totient : ℝ) * (Real.log q) ^ 2 := by
    have h1 : ∑ a ∈ F, ‖∑ k ∈ Finset.range (n+1),
        if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a.val:ℝ)/(q:ℝ) + β))‖ ^ 2
        ≤ ∑ a ∈ F, (Real.log q) ^ 2 :=
      Finset.sum_le_sum fun a _ =>
        pow_le_pow_left₀ (norm_nonneg _) (abs_nonunit_error_le n q a.val β) 2
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h1
    exact h1
  calc ∑ a ∈ F, ‖SG n ((a.val:ℝ)/(q:ℝ) + β)‖ ^ 2
      ≤ ∑ a ∈ F, (2 * ‖((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
          + 2 * ‖∑ k ∈ Finset.range (n+1),
              if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a.val:ℝ)/(q:ℝ) + β))‖ ^ 2) :=
        Finset.sum_le_sum fun a ha => by rw [hexp a ha]; exact norm_add_sq_le_two _ _
    _ = 2 * ∑ a ∈ F, ‖((q.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
        + 2 * ∑ a ∈ F, ‖∑ k ∈ Finset.range (n+1),
              if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a.val:ℝ)/(q:ℝ) + β))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 2 * ((q.totient : ℝ))⁻¹ ^ 2 * ∑ a ∈ F, ‖∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
        + 2 * ∑ a ∈ F, ‖∑ k ∈ Finset.range (n+1),
              if IsUnit (k:ZMod q) then 0 else (GW k : ℂ) * GE ((k:ℝ) * ((a.val:ℝ)/(q:ℝ) + β))‖ ^ 2 := by
        simp only [norm_mul, norm_inv, RCLike.norm_natCast, mul_pow]
        rw [← Finset.mul_sum]
        ring
    _ ≤ 2 * ((q.totient : ℝ))⁻¹ ^ 2 * ((q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖c χ‖ ^ 2)
        + 2 * (q.totient : ℝ) * (Real.log q) ^ 2 := by
        rw [hdil]
        linarith [herr]
    _ = (2 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
          ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2
        + 2 * (q.totient : ℝ) * (Real.log q) ^ 2 := by
        simp only [hcdef]
        field_simp

/-- A Dirichlet character is nonzero on units. -/
theorem chi_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {j : ZMod q}
    (hj : IsUnit j) : (χ j : ℂ) ≠ 0 := by
  intro hc
  have h1 : ‖(χ j : ℂ)‖ = 1 := by
    rw [← hj.unit_spec]
    exact χ.unit_norm_eq_one hj.unit
  rw [hc] at h1
  simp at h1

/-- Conjugation of the standard exponential reverses the frequency. -/
lemma conj_GE (x : ℝ) : conj (GE x) = GE (-x) := by
  rw [GE, ← Complex.exp_conj, map_mul (starRingEnd ℂ), Complex.conj_ofReal, Complex.conj_I, GE]
  congr 1
  push_cast
  ring

/-- **Parseval for the character-twisted sum.** The full-line L² norm of the
character-twisted Goldbach sum is the diagonal weight sum over units:
`∫₀¹ ‖SChi n q χ β‖² dβ = ∑_{k≤n} |χ(k)|² w(k)² = ∑_{k≤n, (k,q)=1} w(k)²`,
since characters are `1` on units and vanish off them. This is the orthogonality
input of the character mean-square route. -/
theorem SChi_L2 (n q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∫ β in (0:ℝ)..1, ‖SChi n q χ β‖ ^ 2
      = ∑ k ∈ Finset.range (n+1), (if IsUnit ((k:ℕ):ZMod q) then (GW k : ℝ) ^ 2 else 0) := by
  classical
  have hcontSChi : Continuous (fun β => SChi n q χ β) := by
    show Continuous (fun β => ∑ k ∈ Finset.range (n+1), χ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ)*β))
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul
      (continuous_GE.comp (continuous_const.mul continuous_id)))
  have hint : IntervalIntegrable (fun β => SChi n q χ β * conj (SChi n q χ β))
      MeasureTheory.volume 0 1 :=
    (hcontSChi.mul (Complex.continuous_conj.comp hcontSChi)).intervalIntegrable 0 1
  -- conjugate sum in terms of the inverse character (valid on units and non-units alike)
  have hconj' : ∀ β : ℝ, conj (SChi n q χ β)
      = ∑ l ∈ Finset.range (n+1), χ⁻¹ (l:ZMod q) * (GW l : ℂ) * GE (-((l:ℝ) * β)) := by
    intro β
    rw [SChi, map_sum (starRingEnd ℂ)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, conj_char_apply_eq_inv, Complex.conj_ofReal, conj_GE]
  -- pointwise expansion of |SChi β|² as the (k, l) double sum
  have hpoint : ∀ β : ℝ, SChi n q χ β * conj (SChi n q χ β)
      = ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
          ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β) := by
    intro β
    rw [hconj' β, SChi, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hE : GE ((k:ℝ)*β) * GE (-((l:ℝ)*β)) = GE (((k:ℝ) - (l:ℝ)) * β) := by
      rw [GE_add]
      congr 1
      ring
    push_cast
    rw [← hE]
    ring
  -- each term integrates to the coefficient times the frequency Kronecker delta
  have hterm : ∀ k l : ℕ, (∫ β in (0:ℝ)..1,
        ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β))
      = ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q))
        * (if ((k:ℤ) - (l:ℤ) : ℤ) = 0 then (1:ℂ) else 0) := by
    intro k l
    have hfreq : ((k:ℝ) - (l:ℝ)) = (((k:ℤ) - (l:ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [hfreq, intervalIntegral.integral_const_mul, integral_GE_freq]
  -- the delta collapses the double sum to the diagonal
  have hcollapse : ∀ k ∈ Finset.range (n+1),
      (∑ l ∈ Finset.range (n+1), ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q))
          * (if ((k:ℤ) - (l:ℤ) : ℤ) = 0 then (1:ℂ) else 0))
        = (if IsUnit ((k:ℕ):ZMod q) then ((GW k : ℝ) ^ 2 : ℂ) else 0) := by
    intro k hk
    rw [Finset.sum_eq_single k]
    · by_cases hu : IsUnit ((k:ℕ):ZMod q)
      · rw [if_pos (show (((k:ℤ)-(k:ℤ):ℤ) = 0) by push_cast; ring), if_pos hu,
          MulChar.inv_apply_eq_inv', mul_inv_cancel₀ (chi_ne_zero χ hu)]
        push_cast
        ring
      · rw [if_neg hu, MulCharClass.map_nonunit χ hu]
        simp
    · intro l _ hl
      rw [if_neg (by omega), mul_zero]
    · intro hcon
      exact absurd hk hcon
  -- the complex integral identity
  have hcomplex : ∫ β in (0:ℝ)..1, SChi n q χ β * conj (SChi n q χ β)
      = ∑ k ∈ Finset.range (n+1), (if IsUnit ((k:ℕ):ZMod q) then ((GW k : ℝ) ^ 2 : ℂ) else 0) := by
    have hsumint : ∀ k : ℕ, IntervalIntegrable (fun β => ∑ l ∈ Finset.range (n+1),
          ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β))
        MeasureTheory.volume 0 1 :=
      fun k => Continuous.intervalIntegrable
        (continuous_finsetSum (Finset.range (n+1))
          (fun l _ => continuous_const_mul_GE
            (((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q))) ((k:ℝ) - (l:ℝ)))) 0 1
    have houter : (∫ β in (0:ℝ)..1, ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
          ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β))
        = ∑ k ∈ Finset.range (n+1), ∫ β in (0:ℝ)..1, ∑ l ∈ Finset.range (n+1),
          ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β) :=
      intervalIntegral.integral_finsetSum (fun k _ => hsumint k)
    have hinnerint : ∀ k : ℕ, (∫ β in (0:ℝ)..1, ∑ l ∈ Finset.range (n+1),
          ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β))
        = ∑ l ∈ Finset.range (n+1), ∫ β in (0:ℝ)..1,
          ((GW k * GW l : ℝ) : ℂ) * (χ (k:ZMod q) * χ⁻¹ (l:ZMod q)) * GE (((k:ℝ) - (l:ℝ)) * β) :=
      fun k => intervalIntegral.integral_finsetSum
        (fun l (_ : l ∈ Finset.range (n+1)) => intervalIntegrable_const_mul_GE _ _)
    simp only [hpoint]
    rw [houter, Finset.sum_congr rfl (fun k _ => hinnerint k),
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => hterm k l)),
      Finset.sum_congr rfl (fun k hk => hcollapse k hk)]
  have hcomplexR : ∫ β, SChi n q χ β * conj (SChi n q χ β)
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 1))
      = ∑ k ∈ Finset.range (n+1), (if IsUnit ((k:ℕ):ZMod q) then ((GW k : ℝ) ^ 2 : ℂ) else 0) := by
    rw [← intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]
    exact hcomplex
  have hintR : MeasureTheory.Integrable (fun β => SChi n q χ β * conj (SChi n q χ β))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) := by
    rw [← Set.uIoc_of_le (le_of_lt zero_lt_one)]
    exact IntervalIntegrable.def' hint
  -- bridge the real norm square through the real part
  have hbridge : ∫ β in (0:ℝ)..1, ‖SChi n q χ β‖ ^ 2
      = (∫ β, SChi n q χ β * conj (SChi n q χ β)
          ∂(MeasureTheory.volume.restrict (Set.Ioc 0 1))).re := by
    rw [intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun β =>
        norm_sq_eq_re_mul_conj (SChi n q χ β))]
    exact integral_re hintR
  rw [hbridge, hcomplexR, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hu : IsUnit ((k:ℕ):ZMod q) <;> simp [hu, Complex.ofReal_re, ← Complex.ofReal_pow]

/-- The norm of the Goldbach integrand is the squared modulus of the Goldbach sum
(`‖E‖ = 1`). -/
theorem norm_fG (n : ℕ) (t : ℝ) : ‖fG n t‖ = ‖SG n t‖ ^ 2 := by
  show ‖(∑ k ∈ Finset.range (n+1), (GW k : ℂ) * GE ((k:ℝ)*t)) ^ 2 * GE (-(n:ℝ)*t)‖
      = ‖∑ k ∈ Finset.range (n+1), (GW k : ℂ) * GE ((k:ℝ)*t)‖ ^ 2
  rw [Complex.norm_mul, norm_GE, mul_one, Complex.norm_pow]

/-- **JG is dominated by the local L² mass.** For measurable `A`, the signed integral
`JG n A` is bounded above by the L² mass of the Goldbach sum over `A`:
`JG n A ≤ ∫_{A∩[0,1]} ‖S n t‖² dt`. This converts the route bounds of
`JG_target_floor` into L² statements about the Goldbach sum. -/
theorem JG_le_L2 (n : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
    JG n A
      ≤ ∫ x in Set.uIoc (0:ℝ) 1, (A.indicator (fun t => ‖SG n t‖ ^ 2)) x ∂MeasureTheory.volume := by
  show (intervalIntegral (fun t => A.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume).re
      ≤ ∫ x in Set.uIoc (0:ℝ) 1, (A.indicator (fun t => ‖SG n t‖ ^ 2)) x ∂MeasureTheory.volume
  calc (intervalIntegral (fun t => A.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume).re
      ≤ ‖(intervalIntegral (fun t => A.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume : ℂ)‖ :=
        Complex.re_le_norm _
    _ ≤ ∫ x in Set.uIoc (0:ℝ) 1, ‖(A.indicator (fG n) x : ℂ)‖ ∂MeasureTheory.volume :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = ∫ x in Set.uIoc (0:ℝ) 1, (A.indicator (fun t => ‖SG n t‖ ^ 2)) x ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ A
        · simp [hx, norm_fG]
        · simp [hx]

/-- Conjugation turns the character-twisted sum at `-u` into the inverse-character
sum at `u`. -/
theorem SChi_neg_conj (n q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) :
    conj (SChi n q χ (-u)) = SChi n q χ⁻¹ u := by
  show conj (∑ k ∈ Finset.range (n+1), χ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ)*(-u)))
      = ∑ k ∈ Finset.range (n+1), χ⁻¹ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ)*u)
  rw [map_sum (starRingEnd ℂ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, conj_char_apply_eq_inv, Complex.conj_ofReal, conj_GE,
    neg_mul_eq_mul_neg, neg_neg]

/-- The standard additive character lies on the unit circle. -/
theorem norm_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle x).norm_coe

/-- **Gauss-sum aggregate.** The squared Gauss sums of all Dirichlet characters mod `q`
(in inverse-character form, as they enter the arc bound) sum to `φ(q)²`. -/
theorem gaussSum_aggregate (q : ℕ) [NeZero q] :
    ∑ χ : DirichletCharacter ℂ q, ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2
      = ((q.totient : ℕ) : ℝ) ^ 2 := by
  classical
  have hψ1 : ∀ x : ZMod q, ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1 := by
    intro x
    have h1 : ‖ZMod.stdAddChar x‖ = 1 := norm_stdAddChar x
    have hnz : ZMod.stdAddChar x ≠ 0 := by
      intro hc
      rw [hc] at h1
      simp at h1
    have hz : ZMod.stdAddChar x * conj (ZMod.stdAddChar x)
        = ZMod.stdAddChar x * (ZMod.stdAddChar x)⁻¹ := by
      rw [RCLike.mul_conj, h1]
      norm_num
      rw [mul_inv_cancel₀ hnz]
    rw [hz, mul_inv_cancel₀ hnz]
  have hcard : (Finset.univ.filter (fun x : ZMod q => IsUnit x)).card = q.totient := by
    have h1 : Fintype.card {a : ZMod q // IsUnit a}
        = (Finset.univ.filter (fun x : ZMod q => IsUnit x)).card :=
      Fintype.card_of_subtype _ (by simp)
    have h2 : Fintype.card {a : ZMod q // IsUnit a}
        = Fintype.card {x : ZMod q // x.val.Coprime q} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun a => Iff.trans
        (by rw [ZMod.natCast_zmod_val a]) (ZMod.isUnit_iff_coprime a.val q)))
    exact h1.symm.trans (h2.trans
      ((Fintype.card_congr (ZMod.unitsEquivCoprime)).symm.trans (ZMod.card_units_eq_totient q)))
  -- dual-side Dirichlet orthogonality
  have hinner : ∀ x y : ZMod q, (∑ χ : DirichletCharacter ℂ q, χ⁻¹ x * χ y)
      = if IsUnit x ∧ x = y then ((q.totient : ℕ) : ℂ) else 0 := by
    intro x y
    by_cases hx : IsUnit x
    · have hconv : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ x = χ x⁻¹ := fun χ => by
        rw [MulChar.inv_apply_eq_inv', ← chi_apply_inv χ hx]
      rw [Finset.sum_congr rfl (fun χ _ => by rw [hconv χ]),
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx y]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos (show IsUnit x ∧ x = y from ⟨hx, hxy⟩)]
      · simp [hxy]
    · rw [if_neg (fun hc => hx hc.1)]
      refine Finset.sum_eq_zero fun χ _ => ?_
      rw [MulChar.inv_apply_eq_inv', MulCharClass.map_nonunit χ hx, inv_zero, zero_mul]
  -- pointwise expansion of the squared modulus as a double sum
  have hexpand : ∀ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ ZMod.stdAddChar * conj (gaussSum χ⁻¹ ZMod.stdAddChar)
      = ∑ x : ZMod q, ∑ y : ZMod q,
          ZMod.stdAddChar x * conj (ZMod.stdAddChar y) * (χ⁻¹ x * χ y) := by
    intro χ
    have h1 : gaussSum χ⁻¹ ZMod.stdAddChar
        = ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar a := rfl
    rw [h1, map_sum (starRingEnd ℂ), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul (starRingEnd ℂ), conj_char_apply_eq_inv, inv_inv]
    ring
  have hswap : ∑ χ : DirichletCharacter ℂ q, ∑ x : ZMod q, ∑ y : ZMod q,
      ZMod.stdAddChar x * conj (ZMod.stdAddChar y) * (χ⁻¹ x * χ y)
    = ∑ x : ZMod q, ∑ y : ZMod q, ∑ χ : DirichletCharacter ℂ q,
      ZMod.stdAddChar x * conj (ZMod.stdAddChar y) * (χ⁻¹ x * χ y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun χ _ => norm_sq_eq_re_mul_conj (gaussSum χ⁻¹ ZMod.stdAddChar)),
    ← Complex.re_sum, Finset.sum_congr rfl (fun χ _ => hexpand χ), hswap]
  -- evaluate the inner character sum pointwise
  have hpoint : ∀ x y : ZMod q,
      ∑ χ : DirichletCharacter ℂ q,
        ZMod.stdAddChar x * conj (ZMod.stdAddChar y) * (χ⁻¹ x * χ y)
      = if IsUnit x ∧ x = y then
          ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ) else 0 := by
    intro x y
    rw [← Finset.mul_sum, hinner x y]
    by_cases h : IsUnit x ∧ x = y
    · rw [if_pos h, if_pos h, h.2]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hpoint x y))]
  -- non-units contribute nothing; each unit pairs only with itself
  have hzero : ∀ x : ZMod q, ¬IsUnit x → ∑ y : ZMod q,
      (if IsUnit x ∧ x = y then
        ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ) else 0) = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun y _ => ?_
    exact if_neg (fun hc => hx hc.1)
  have hstep : ∑ x : ZMod q, ∑ y : ZMod q,
      (if IsUnit x ∧ x = y then
        ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ) else 0)
    = ∑ x ∈ Finset.univ.filter (fun x : ZMod q => IsUnit x),
        ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ) := by
    refine (Finset.sum_subset (Finset.filter_subset (fun x : ZMod q => IsUnit x) Finset.univ)
      (fun x _ hx => hzero x (fun hc => hx (Finset.mem_filter.mpr
        ⟨Finset.mem_univ x, hc⟩)))).symm.trans ?_
    refine Finset.sum_congr rfl fun x hx => ?_
    have hu : IsUnit x := (Finset.mem_filter.mp hx).2
    have hy : ∀ y : ZMod q, (if IsUnit x ∧ x = y then
        ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ) else 0)
      = (if x = y then
        ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ) else 0) := by
      intro y
      by_cases h : x = y
      · rw [if_pos (show IsUnit x ∧ x = y from ⟨hu, h⟩), if_pos h]
      · simp [h, hu]
    rw [Finset.sum_congr rfl (fun y _ => hy y), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ x)]
  rw [hstep]
  have hsum1 : ∑ x ∈ Finset.univ.filter (fun x : ZMod q => IsUnit x),
      ZMod.stdAddChar x * conj (ZMod.stdAddChar x) * ((q.totient : ℕ) : ℂ)
    = ∑ x ∈ Finset.univ.filter (fun x : ZMod q => IsUnit x), ((q.totient : ℕ) : ℂ) :=
    Finset.sum_congr rfl (fun x _ => by rw [hψ1 x, one_mul])
  rw [hsum1, Finset.sum_const, nsmul_eq_mul, hcard, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im]
  ring

/-- **Integrated arc mass.** Integrating the arc-sum L² bridge over a symmetric phase
interval `[-δ, δ]` pulls the constant Gauss-sum factors out of the β-integral:
`∫_{-δ}^{δ} ∑_a ‖SG n (a/q+β)‖² dβ ≤ (2/φ) ∑_χ ‖τ(χ⁻¹)‖² · ∫_{-δ}^{δ} ‖SChi χ β‖² dβ
+ 4φ(log q)²δ`. -/
theorem arcMass_integral_bound (n q : ℕ) [NeZero q] (δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ β in (-δ:ℝ)..δ, ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
        ‖SG n ((a.val:ℝ)/(q:ℝ) + β)‖ ^ 2
      ≤ (2 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
          ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2)
        + 4 * (q.totient : ℝ) * (Real.log q) ^ 2 * δ := by
  classical
  have hSGc : Continuous (SG n) := by
    show Continuous (fun t : ℝ => ∑ k ∈ Finset.range (n+1), (GW k : ℂ) * GE ((k:ℝ)*t))
    exact continuous_finsetSum _ (fun k _ => continuous_summand_GE n k)
  have hSChic : ∀ χ : DirichletCharacter ℂ q, Continuous (fun β : ℝ => SChi n q χ β) := by
    intro χ
    show Continuous (fun β : ℝ => ∑ k ∈ Finset.range (n+1),
      χ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ)*β))
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul
      (continuous_GE.comp (continuous_const.mul continuous_id)))
  have hLcont : Continuous (fun β : ℝ => ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ‖SG n ((a.val:ℝ)/(q:ℝ) + β)‖ ^ 2) :=
    continuous_finsetSum _ (fun a _ =>
      (hSGc.norm.pow 2).comp (continuous_const.add continuous_id))
  have hLint := (hLcont.intervalIntegrable (-δ:ℝ) δ :
    IntervalIntegrable _ MeasureTheory.volume _ _)
  have hRcont1 : Continuous (fun β : ℝ => (2 / (q.totient : ℝ)) *
      ∑ χ : DirichletCharacter ℂ q, ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ (fun χ _ =>
      ((show Continuous fun _ : ℝ => gaussSum χ⁻¹ ZMod.stdAddChar from
        continuous_const).mul (hSChic χ)).norm.pow 2))
  have hRcont : Continuous (fun β : ℝ => (2 / (q.totient : ℝ)) *
      ∑ χ : DirichletCharacter ℂ q, ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2
      + 2 * (q.totient : ℝ) * (Real.log q) ^ 2) :=
    hRcont1.add continuous_const
  have hRint := (hRcont.intervalIntegrable (-δ:ℝ) δ :
    IntervalIntegrable _ MeasureTheory.volume _ _)
  have hRint1 := (hRcont1.intervalIntegrable (-δ:ℝ) δ :
    IntervalIntegrable _ MeasureTheory.volume _ _)
  have hRint2 : IntervalIntegrable (fun _ : ℝ => 2 * (q.totient : ℝ) * (Real.log q) ^ 2)
      MeasureTheory.volume (-δ:ℝ) δ :=
    (continuous_const (y := 2 * (q.totient : ℝ) * (Real.log q) ^ 2)).intervalIntegrable
      (-δ:ℝ) δ
  refine le_trans (intervalIntegral.integral_mono (show (-δ:ℝ) ≤ δ by linarith) hLint hRint
    (fun β => SG_arc_L2 n q β)) ?_
  -- evaluate the right-hand integral
  have hintχ : ∀ χ : DirichletCharacter ℂ q,
      IntervalIntegrable (fun β : ℝ => ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2)
        MeasureTheory.volume (-δ:ℝ) δ := by
    intro χ
    exact (((show Continuous fun _ : ℝ => gaussSum χ⁻¹ ZMod.stdAddChar from
      continuous_const).mul (hSChic χ)).norm.pow 2).intervalIntegrable _ _
  have hintχ2 : ∀ χ : DirichletCharacter ℂ q,
      ∫ β in (-δ:ℝ)..δ, ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2
        = ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2 := by
    intro χ
    have e1 : (-δ:ℝ) ≤ δ := by linarith
    rw [intervalIntegral.integral_of_le e1,
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun β => by
        rw [norm_mul, mul_pow]),
      MeasureTheory.integral_const_mul,
      (intervalIntegral.integral_of_le e1).symm]
  have hRHS : ∫ β in (-δ:ℝ)..δ, ((2 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ⁻¹ ZMod.stdAddChar * SChi n q χ β‖ ^ 2
      + 2 * (q.totient : ℝ) * (Real.log q) ^ 2)
    = (2 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2)
      + 4 * (q.totient : ℝ) * (Real.log q) ^ 2 * δ := by
    rw [intervalIntegral.integral_add hRint1 hRint2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun χ _ => hintχ χ),
      Finset.sum_congr rfl (fun χ _ => hintχ2 χ)]
    rw [intervalIntegral.integral_const, smul_eq_mul,
      show (δ:ℝ) - (-δ) = 2 * δ from by ring]
    ring
  rw [hRHS]

/-- The unit-restricted diagonal weight sum `∑_{k≤n, (k,q)=1} w(k)²`. -/
noncomputable def Wsq (n q : ℕ) [NeZero q] : ℝ :=
  ∑ k ∈ Finset.range (n+1), (if IsUnit ((k:ℕ):ZMod q) then (GW k : ℝ) ^ 2 else 0)

lemma Wsq_nonneg (n q : ℕ) [NeZero q] : 0 ≤ Wsq n q :=
  Finset.sum_nonneg (fun k _ => by by_cases h : IsUnit ((k:ℕ):ZMod q) <;> simp [h] <;>
    positivity)

/-- **Short-phase arc mass.** For `δ ≤ 1`, the Goldbach arc mass over the symmetric phase
interval is bounded by twice the unit diagonal weight plus the non-coprime error:
`∫_{-δ}^{δ} ∑_a ‖SG n (a/q+β)‖² dβ ≤ 4φ·Wsq(n,q) + 4φ(log q)²δ`. -/
theorem arcMass_bound (n q : ℕ) [NeZero q] (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ β in (-δ:ℝ)..δ, ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
        ‖SG n ((a.val:ℝ)/(q:ℝ) + β)‖ ^ 2
      ≤ 4 * (q.totient : ℝ) * Wsq n q + 4 * (q.totient : ℝ) * (Real.log q) ^ 2 * δ := by
  classical
  have hSChic : ∀ χ : DirichletCharacter ℂ q, Continuous (fun β : ℝ => SChi n q χ β) := by
    intro χ
    show Continuous (fun β : ℝ => ∑ k ∈ Finset.range (n+1),
      χ (k:ZMod q) * (GW k : ℂ) * GE ((k:ℝ)*β))
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul
      (continuous_GE.comp (continuous_const.mul continuous_id)))
  have hcontχ : ∀ χ : DirichletCharacter ℂ q, Continuous (fun β : ℝ => ‖SChi n q χ β‖ ^ 2) :=
    fun χ => (hSChic χ).norm.pow 2
  have hpt : ∀ χ : DirichletCharacter ℂ q, ∀ u : ℝ,
      ‖SChi n q χ (-u)‖ = ‖SChi n q χ⁻¹ u‖ := by
    intro χ u
    rw [← Complex.norm_conj, SChi_neg_conj]
  refine le_trans (arcMass_integral_bound n q δ hδ) ?_
  -- each symmetric character integral is at most twice the full-line diagonal mass
  have hpair : ∀ χ : DirichletCharacter ℂ q,
      ∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2 ≤ 2 * Wsq n q := by
    intro χ
    have hf1 : IntervalIntegrable (fun β : ℝ => ‖SChi n q χ β‖ ^ 2)
        MeasureTheory.volume (-δ:ℝ) 0 := (hcontχ χ).intervalIntegrable _ _
    have hf2 : IntervalIntegrable (fun β : ℝ => ‖SChi n q χ β‖ ^ 2)
        MeasureTheory.volume (0:ℝ) δ := (hcontχ χ).intervalIntegrable _ _
    have hnegint : ∫ β in (-δ:ℝ)..0, ‖SChi n q χ β‖ ^ 2
        = ∫ u in (0:ℝ)..δ, ‖SChi n q χ (-u)‖ ^ 2 :=
      (intervalIntegral.integral_comp_neg (f := fun u : ℝ => ‖SChi n q χ u‖ ^ 2)
          (a := (0:ℝ)) (b := δ)).symm
    have h1 : ∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2
        = (∫ β in (-δ:ℝ)..0, ‖SChi n q χ β‖ ^ 2) + ∫ β in (0:ℝ)..δ, ‖SChi n q χ β‖ ^ 2 := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hf1 hf2]
    have hsplit : ∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2
        = (∫ u in (0:ℝ)..δ, ‖SChi n q χ (-u)‖ ^ 2) + ∫ u in (0:ℝ)..δ, ‖SChi n q χ u‖ ^ 2 := by
      rw [h1, hnegint]
    rw [hsplit]
    have hneg : Continuous (fun u : ℝ => ‖SChi n q χ (-u)‖ ^ 2) :=
      (hcontχ χ).comp continuous_id.neg
    have h1 : ∫ u in (0:ℝ)..δ, ‖SChi n q χ (-u)‖ ^ 2
        ≤ ∫ u in (0:ℝ)..1, ‖SChi n q χ⁻¹ u‖ ^ 2 := by
      refine le_trans (intervalIntegral.integral_mono_interval (le_refl _) hδ hδ1
        (Filter.Eventually.of_forall (fun u => sq_nonneg (‖SChi n q χ (-u)‖)))
        (hneg.intervalIntegrable (0:ℝ) 1 :
          IntervalIntegrable _ MeasureTheory.volume _ _)) ?_
      rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun u => by
          rw [hpt χ u]),
        intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    have h2 : ∫ u in (0:ℝ)..δ, ‖SChi n q χ u‖ ^ 2
        ≤ ∫ u in (0:ℝ)..1, ‖SChi n q χ u‖ ^ 2 :=
      intervalIntegral.integral_mono_interval (le_refl _) hδ hδ1
        (Filter.Eventually.of_forall (fun u => sq_nonneg (‖SChi n q χ u‖)))
        ((hcontχ χ).intervalIntegrable _ _)
    rw [SChi_L2 n q χ⁻¹] at h1
    rw [SChi_L2 n q χ] at h2
    have hwsq : Wsq n q = ∑ k ∈ Finset.range (n + 1), (if IsUnit ((k:ℕ):ZMod q) then (GW k : ℝ) ^ 2 else 0) := rfl
    rw [hwsq]
    refine le_trans (add_le_add (le_trans h1 le_rfl) (le_trans h2 le_rfl)) ?_
    rw [two_mul]
  have hsum : ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2)
    ≤ ((q.totient : ℕ) : ℝ) ^ 2 * (2 * Wsq n q) := by
    have h1 : ∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ q,
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (2 * Wsq n q) :=
      Finset.sum_le_sum (fun χ _ =>
        mul_le_mul_of_nonneg_left (hpair χ) (sq_nonneg _))
    rw [← Finset.sum_mul, gaussSum_aggregate q] at h1
    exact h1
  have hφ : (0:ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hφ0 : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
  have hkey : (2 / (q.totient : ℝ)) * (((q.totient : ℕ) : ℝ) ^ 2 * (2 * Wsq n q))
      = 4 * (q.totient : ℝ) * Wsq n q := by
    field_simp
    ring
  have hc : (0:ℝ) ≤ 2 / (q.totient : ℝ) := div_nonneg (by norm_num) (le_of_lt hφ)
  have hmain : (2 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * (∫ β in (-δ:ℝ)..δ, ‖SChi n q χ β‖ ^ 2)
    ≤ 4 * (q.totient : ℝ) * Wsq n q := by
    refine le_trans (mul_le_mul_of_nonneg_left hsum hc) ?_
    rw [hkey]
  exact add_le_add hmain le_rfl

/-! ### Kernel mass bounds on symmetric intervals (skirt infrastructure) -/

lemma phase_eq_GE (x : ℝ) : GoldbachExplicitModeledMajor.phase x = GE x := rfl

lemma phase_add (x y : ℝ) : GoldbachExplicitModeledMajor.phase x * GoldbachExplicitModeledMajor.phase y
    = GoldbachExplicitModeledMajor.phase (x + y) := by
  unfold GoldbachExplicitModeledMajor.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma conj_phase (x : ℝ) : conj (GoldbachExplicitModeledMajor.phase x)
    = GoldbachExplicitModeledMajor.phase (-x) := by
  have h1 : GoldbachExplicitModeledMajor.phase x = GE x := rfl
  have h2 : GoldbachExplicitModeledMajor.phase (-x) = GE (-x) := rfl
  rw [h1, h2, conj_GE]

lemma phase_nat (k : ℕ) : GoldbachExplicitModeledMajor.phase (k:ℝ) = 1 := by
  unfold GoldbachExplicitModeledMajor.phase
  have h := Complex.exp_int_mul_two_pi_mul_I (k:ℤ)
  have he : ((2 * Real.pi * (k:ℝ) : ℝ) : ℂ) * Complex.I = ((k:ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, h]

lemma continuous_phase : Continuous (fun x : ℝ => GoldbachExplicitModeledMajor.phase x) := by
  unfold GoldbachExplicitModeledMajor.phase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

lemma continuous_kernel (n : ℕ) :
    Continuous (fun x : ℝ => GoldbachExplicitModeledMajor.kernel n x) := by
  unfold GoldbachExplicitModeledMajor.kernel
  exact continuous_finsetSum _ (fun k _ => continuous_phase.comp
    (continuous_const.mul continuous_id))

lemma continuous_kernel_norm (n : ℕ) :
    Continuous (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2) :=
  (continuous_kernel n).norm.pow 2

/-- Pointwise: the geometric kernel has norm at most `n+1`. -/
lemma kernel_norm_le_card (n : ℕ) (β : ℝ) :
    ‖GoldbachExplicitModeledMajor.kernel n β‖ ≤ (n + 1 : ℝ) := by
  unfold GoldbachExplicitModeledMajor.kernel
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ k : ℕ, ‖GoldbachExplicitModeledMajor.phase ((k:ℝ) * β)‖ = (1:ℝ) := fun k =>
    Complex.norm_exp_ofReal_mul_I _
  rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  simp

/-- Telescoping identity for the geometric kernel. -/
lemma kernel_mul_one_sub_phase (n : ℕ) (β : ℝ) :
    GoldbachExplicitModeledMajor.kernel n β * (1 - GoldbachExplicitModeledMajor.phase β)
      = 1 - GoldbachExplicitModeledMajor.phase ((n + 1 : ℕ) * β) := by
  induction n with
  | zero =>
    have h : GoldbachExplicitModeledMajor.kernel 0 β = 1 := by
      unfold GoldbachExplicitModeledMajor.kernel
      simp [GoldbachExplicitModeledMajor.phase]
    rw [h]
    simp [GoldbachExplicitModeledMajor.phase]
  | succ m ih =>
    have hsum : GoldbachExplicitModeledMajor.kernel (m + 1) β
        = GoldbachExplicitModeledMajor.kernel m β
          + GoldbachExplicitModeledMajor.phase ((m + 1 : ℕ) * β) := by
      unfold GoldbachExplicitModeledMajor.kernel
      rw [Finset.sum_range_succ]
    have hmul : GoldbachExplicitModeledMajor.phase ((m + 1 : ℕ) * β)
        * GoldbachExplicitModeledMajor.phase β
      = GoldbachExplicitModeledMajor.phase ((m + 1 + 1 : ℕ) * β) := by
      rw [phase_add]
      congr 1
      push_cast
      ring
    rw [hsum, add_mul, ih, mul_sub, mul_one, hmul]
    ring

/-- Parseval for the geometric kernel over a full period. -/
lemma kernelMass_half (n : ℕ) : GoldbachExplicitModeledMajor.kernelMass n (1/2) = (n + 1 : ℝ) := by
  have hper : ∀ β : ℝ, ‖GoldbachExplicitModeledMajor.kernel n (β + 1)‖ ^ 2
      = ‖GoldbachExplicitModeledMajor.kernel n β‖ ^ 2 := by
    intro β
    have h1 : GoldbachExplicitModeledMajor.kernel n (β + 1)
        = GoldbachExplicitModeledMajor.kernel n β := by
      unfold GoldbachExplicitModeledMajor.kernel
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show ((k:ℝ)*(β+1)) = ((k:ℝ)*β + (k:ℝ)) from by ring, ← phase_add, phase_nat, mul_one]
    rw [h1]
  have hp : Function.Periodic (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2) 1 :=
    fun x => hper x
  have hshift : GoldbachExplicitModeledMajor.kernelMass n (1/2)
      = ∫ u in (0:ℝ)..1, ‖GoldbachExplicitModeledMajor.kernel n u‖ ^ 2 := by
    unfold GoldbachExplicitModeledMajor.kernelMass
    have h2 := hp.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
    rw [show (-(1/2 : ℝ) + 1) = 1/2 from by ring, show ((0:ℝ) + 1) = 1 from by ring] at h2
    exact h2
  have hpoint : ∀ u : ℝ, GoldbachExplicitModeledMajor.kernel n u
        * conj (GoldbachExplicitModeledMajor.kernel n u)
      = ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
          GoldbachExplicitModeledMajor.phase (((k:ℝ) - (l:ℝ)) * u) := by
    intro u
    unfold GoldbachExplicitModeledMajor.kernel
    rw [map_sum (starRingEnd ℂ), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [conj_phase, phase_add]
    congr 1
    ring
  have hterm : ∀ k l : ℕ, (∫ u in (0:ℝ)..1,
        GoldbachExplicitModeledMajor.phase (((k:ℝ) - (l:ℝ)) * u))
      = (if ((k:ℤ) - (l:ℤ) : ℤ) = 0 then (1:ℂ) else 0) := by
    intro k l
    have hfreq : ((k:ℝ) - (l:ℝ)) = (((k:ℤ) - (l:ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [hfreq]
    exact integral_GE_freq ((k:ℤ) - (l:ℤ))
  have hcollapse : (∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
        (if ((k:ℤ) - (l:ℤ) : ℤ) = 0 then (1:ℂ) else 0))
      = ((n + 1 : ℕ) : ℂ) := by
    have hinner : ∀ k ∈ Finset.range (n+1), (∑ l ∈ Finset.range (n+1),
          (if ((k:ℤ) - (l:ℤ) : ℤ) = 0 then (1:ℂ) else 0)) = (1:ℂ) := by
      intro k hk
      rw [Finset.sum_eq_single k]
      · rw [if_pos (by push_cast; ring)]
      · intro l _ hl
        rw [if_neg (by omega)]
      · intro hcon
        exact absurd hk hcon
    calc (∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
            (if ((k:ℤ) - (l:ℤ) : ℤ) = 0 then (1:ℂ) else 0))
        = ∑ k ∈ Finset.range (n+1), (1:ℂ) := Finset.sum_congr rfl (fun k hk => hinner k hk)
      _ = ((n + 1 : ℕ) : ℂ) := by simp
  have hint1 : ∀ k l : ℕ, IntervalIntegrable
      (fun u : ℝ => GoldbachExplicitModeledMajor.phase (((k:ℝ)-(l:ℝ))*u))
      MeasureTheory.volume 0 1 :=
    fun k l => Continuous.intervalIntegrable
      (continuous_phase.comp (continuous_const.mul continuous_id)) 0 1
  have hsumint : ∀ k : ℕ, IntervalIntegrable (fun u : ℝ => ∑ l ∈ Finset.range (n+1),
        GoldbachExplicitModeledMajor.phase (((k:ℝ)-(l:ℝ))*u)) MeasureTheory.volume 0 1 :=
    fun k => Continuous.intervalIntegrable
      (continuous_finsetSum _ (fun l _ => continuous_phase.comp
        (continuous_const.mul continuous_id))) 0 1
  have hint2 : IntervalIntegrable (fun u : ℝ => GoldbachExplicitModeledMajor.kernel n u
      * conj (GoldbachExplicitModeledMajor.kernel n u)) MeasureTheory.volume 0 1 :=
    ((continuous_kernel n).mul
      (Complex.continuous_conj.comp (continuous_kernel n))).intervalIntegrable 0 1
  have hintR : MeasureTheory.Integrable (fun u : ℝ => GoldbachExplicitModeledMajor.kernel n u
      * conj (GoldbachExplicitModeledMajor.kernel n u))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) := by
    rw [← Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hint2.def'
  have hcomplex : ∫ u in (0:ℝ)..1, GoldbachExplicitModeledMajor.kernel n u
        * conj (GoldbachExplicitModeledMajor.kernel n u)
      = ((n + 1 : ℕ) : ℂ) := by
    simp only [hpoint]
    rw [intervalIntegral.integral_finsetSum (fun k _ => hsumint k)]
    have h2 : ∀ k : ℕ, (∫ u in (0:ℝ)..1, ∑ l ∈ Finset.range (n+1),
          GoldbachExplicitModeledMajor.phase (((k:ℝ)-(l:ℝ))*u))
        = ∑ l ∈ Finset.range (n+1), (if ((k:ℤ)-(l:ℤ):ℤ) = 0 then (1:ℂ) else 0) := by
      intro k
      rw [intervalIntegral.integral_finsetSum (fun l _ => hint1 k l)]
      exact Finset.sum_congr rfl (fun l _ => hterm k l)
    rw [Finset.sum_congr rfl (fun k _ => h2 k), hcollapse]
  have hcomplexM : ∫ u, GoldbachExplicitModeledMajor.kernel n u
        * conj (GoldbachExplicitModeledMajor.kernel n u)
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 1))
      = ((n + 1 : ℕ) : ℂ) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hcomplex
  have hbridge : ∫ u in (0:ℝ)..1, ‖GoldbachExplicitModeledMajor.kernel n u‖ ^ 2
      = (∫ u, GoldbachExplicitModeledMajor.kernel n u
          * conj (GoldbachExplicitModeledMajor.kernel n u)
          ∂(MeasureTheory.volume.restrict (Set.Ioc 0 1))).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun u =>
        norm_sq_eq_re_mul_conj (GoldbachExplicitModeledMajor.kernel n u))]
    exact integral_re hintR
  rw [hshift, hbridge, hcomplexM]
  simp

/-- The kernel mass over a symmetric interval is at most a full period's mass. -/
lemma kernelMass_le_card (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hb2 : b ≤ 1/2) :
    GoldbachExplicitModeledMajor.kernelMass n b ≤ (n + 1 : ℝ) := by
  have h1 : GoldbachExplicitModeledMajor.kernelMass n b
      ≤ GoldbachExplicitModeledMajor.kernelMass n (1/2) :=
    GoldbachExplicitModeledMajor.kernelMass_mono hb (by linarith) n
  rw [kernelMass_half n] at h1
  exact h1

/-- The kernel mass over a symmetric interval is at most length times the peak. -/
lemma kernelMass_le_length (n : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    GoldbachExplicitModeledMajor.kernelMass n b ≤ 2 * b * ((n + 1 : ℝ) ^ 2) := by
  have hint : IntervalIntegrable (fun β : ℝ => ‖GoldbachExplicitModeledMajor.kernel n β‖ ^ 2)
      MeasureTheory.volume (-b) b := (continuous_kernel_norm n).intervalIntegrable (-b) b
  have hconst : IntervalIntegrable (fun _ : ℝ => ((n + 1 : ℝ) ^ 2))
      MeasureTheory.volume (-b) b := continuous_const.intervalIntegrable (-b) b
  unfold GoldbachExplicitModeledMajor.kernelMass
  calc ∫ β in -b..b, ‖GoldbachExplicitModeledMajor.kernel n β‖ ^ 2
      ≤ ∫ β in -b..b, ((n + 1 : ℝ) ^ 2) :=
        intervalIntegral.integral_mono (by linarith) hint hconst
          (fun β => pow_le_pow_left₀ (by positivity) (kernel_norm_le_card n β) 2)
    _ = 2 * b * ((n + 1 : ℝ) ^ 2) := by
        rw [intervalIntegral.integral_const, show (b:ℝ) - (-b) = 2 * b from by ring,
          smul_eq_mul]

/-- The annulus kernel mass is at most a full period's mass. -/
lemma kernelMass_annulus_le_card (n : ℕ) (h k : ℝ) (hh : 0 ≤ h) (hkh : h ≤ k) (hk2 : k ≤ 1/2) :
    GoldbachExplicitModeledMajor.kernelMass n k - GoldbachExplicitModeledMajor.kernelMass n h
      ≤ (n + 1 : ℝ) := by
  have hnonneg : 0 ≤ GoldbachExplicitModeledMajor.kernelMass n h := by
    have h0 : GoldbachExplicitModeledMajor.kernelMass n 0 = 0 := by
      unfold GoldbachExplicitModeledMajor.kernelMass
      rw [neg_zero, intervalIntegral.integral_same]
    exact h0 ▸ GoldbachExplicitModeledMajor.kernelMass_mono (by norm_num) hh n
  have h1 : GoldbachExplicitModeledMajor.kernelMass n k - GoldbachExplicitModeledMajor.kernelMass n h
      ≤ GoldbachExplicitModeledMajor.kernelMass n k := by linarith
  exact le_trans h1 (kernelMass_le_card n k (hh.trans hkh) hk2)

/-- The annulus kernel mass is at most its length times the peak. -/
lemma kernelMass_annulus_le_length (n : ℕ) (h k : ℝ) (hh : 0 ≤ h) (hkh : h ≤ k) :
    GoldbachExplicitModeledMajor.kernelMass n k - GoldbachExplicitModeledMajor.kernelMass n h
      ≤ 2 * k * ((n + 1 : ℝ) ^ 2) := by
  have hnonneg : 0 ≤ GoldbachExplicitModeledMajor.kernelMass n h := by
    have h0 : GoldbachExplicitModeledMajor.kernelMass n 0 = 0 := by
      unfold GoldbachExplicitModeledMajor.kernelMass
      rw [neg_zero, intervalIntegral.integral_same]
    exact h0 ▸ GoldbachExplicitModeledMajor.kernelMass_mono (by norm_num) hh n
  have h1 : GoldbachExplicitModeledMajor.kernelMass n k - GoldbachExplicitModeledMajor.kernelMass n h
      ≤ GoldbachExplicitModeledMajor.kernelMass n k := by linarith
  exact le_trans h1 (kernelMass_le_length n k (hh.trans hkh))

/-- The annulus kernel mass obeys both bounds. -/
theorem kernelMass_annulus_le (n : ℕ) (h k : ℝ) (hh : 0 ≤ h) (hkh : h ≤ k) (hk2 : k ≤ 1/2) :
    GoldbachExplicitModeledMajor.kernelMass n k - GoldbachExplicitModeledMajor.kernelMass n h
      ≤ min ((n + 1 : ℝ)) (2 * k * ((n + 1 : ℝ) ^ 2)) :=
  le_min (kernelMass_annulus_le_card n h k hh hkh hk2)
    (kernelMass_annulus_le_length n h k hh hkh)

/-! ### Frequency decay of the kernel

On the annulus `h < |β| ≤ k` away from the integers the kernel satisfies
`|K_n(β)| ≤ 1/(2|β|)`, so the annulus mass decays like `1/(2h) = qn/(2Q)`.
This is the bound that captures the `1/β²` tail of the Dirichlet kernel. -/

/-- `|sin(πβ)| = sin(π|β|)` for `|β| ≤ 1/2`. -/
lemma abs_sin_eq_sin_abs (β : ℝ) (hβ : |β| ≤ 1/2) :
    |Real.sin (Real.pi * β)| = Real.sin (Real.pi * |β|) := by
  rcases le_total 0 β with h0 | h0
  · rw [abs_of_nonneg h0]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [h0, Real.pi_pos])
      (by nlinarith [hβ, le_abs_self β, h0, Real.pi_pos]))
  · have hb : |β| = -β := abs_of_nonpos h0
    have hble : -β ≤ 1 / 2 := by rw [← hb]; exact hβ
    have hsin : Real.sin (Real.pi * β) = -Real.sin (Real.pi * (-β)) := by
      rw [← Real.sin_neg]
      congr 1
      ring
    rw [hsin, abs_neg, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [h0, Real.pi_pos])
        (by nlinarith [Real.pi_pos, hble])), hb]

/-- `|sin(πβ)| ≥ 2|β|` for `|β| ≤ 1/2`. -/
lemma abs_sin_ge_two_mul_abs (β : ℝ) (hβ : |β| ≤ 1/2) :
    2 * |β| ≤ |Real.sin (Real.pi * β)| := by
  rw [abs_sin_eq_sin_abs β hβ]
  have hpi : Real.pi * |β| ≤ Real.pi / 2 := by
    calc Real.pi * |β| ≤ Real.pi * (1 / 2) := by nlinarith [hβ, abs_nonneg β, Real.pi_pos]
      _ = Real.pi / 2 := by ring
  have h1 : 2 / Real.pi * (Real.pi * |β|) ≤ Real.sin (Real.pi * |β|) :=
    Real.mul_le_sin (by nlinarith [abs_nonneg β, Real.pi_pos]) (by linarith [hpi, Real.pi_pos])
  have h2 : (2:ℝ) / Real.pi * (Real.pi * |β|) = 2 * |β| := by
    field_simp [Real.pi_pos.ne]
  rw [h2] at h1
  exact h1

/-- The kernel is conjugate-symmetric: `K_n(-x) = conj K_n(x)`. -/
lemma kernel_neg (n : ℕ) (x : ℝ) :
    GoldbachExplicitModeledMajor.kernel n (-x) = conj (GoldbachExplicitModeledMajor.kernel n x) := by
  unfold GoldbachExplicitModeledMajor.kernel
  rw [map_sum (starRingEnd ℂ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conj_phase, show (k:ℝ) * (-x) = -((k:ℝ) * x) from by ring]

/-- `|1 - phase β| = 2|sin(πβ)|`. -/
lemma norm_one_sub_phase (β : ℝ) :
    ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase β‖ = 2 * |Real.sin (Real.pi * β)| := by
  have hsplit : (1:ℂ) - GoldbachExplicitModeledMajor.phase β
      = GoldbachExplicitModeledMajor.phase (β / 2)
          * (GoldbachExplicitModeledMajor.phase (-(β / 2))
              - GoldbachExplicitModeledMajor.phase (β / 2)) := by
    have h1 := phase_add (β / 2) (β / 2)
    have h2 := phase_add (β / 2) (-(β / 2))
    have h3 : GoldbachExplicitModeledMajor.phase (0:ℝ) = 1 := by
      unfold GoldbachExplicitModeledMajor.phase; simp
    have h4 : GoldbachExplicitModeledMajor.phase (β / 2)
        * (GoldbachExplicitModeledMajor.phase (-(β / 2))
            - GoldbachExplicitModeledMajor.phase (β / 2))
        = GoldbachExplicitModeledMajor.phase (β / 2) * GoldbachExplicitModeledMajor.phase (-(β / 2))
            - GoldbachExplicitModeledMajor.phase (β / 2) * GoldbachExplicitModeledMajor.phase (β / 2) := by
      ring
    rw [show (β / 2 + β / 2 : ℝ) = β from by ring] at h1
    rw [show (β / 2 + -(β / 2) : ℝ) = 0 from by ring] at h2
    rw [h4, h2, h3, h1]
  have hdiff : GoldbachExplicitModeledMajor.phase (-(β / 2))
      - GoldbachExplicitModeledMajor.phase (β / 2)
      = -2 * Complex.I * (Real.sin (Real.pi * β) : ℂ) := by
    unfold GoldbachExplicitModeledMajor.phase
    have hu : (2 * Real.pi * (β / 2) : ℝ) = Real.pi * β := by ring
    have hv : (2 * Real.pi * (-(β / 2)) : ℝ) = -(Real.pi * β) := by ring
    rw [hu, hv, Complex.ofReal_sin]
    have hsin : Complex.sin ((Real.pi * β : ℝ) : ℂ)
        = (Complex.exp (-((Real.pi * β : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((Real.pi * β : ℝ) : ℂ) * Complex.I)) * Complex.I / 2 := rfl
    rw [hsin]
    have hI2 : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
    have hkey2 : ∀ a b : ℂ, -2 * Complex.I * ((b - a) * Complex.I / 2) = b - a := by
      intro a b
      have hexp : (-2:ℂ) * Complex.I * ((b - a) * Complex.I / 2)
          = ((-2:ℂ) * Complex.I * Complex.I) * (b - a) / 2 := by ring
      have h2 : ((-2:ℂ) * Complex.I * Complex.I) = 2 := by
        rw [show (-2:ℂ) * Complex.I * Complex.I = -2 * (Complex.I * Complex.I) from by ring, hI2]
        ring
      rw [hexp, h2]
      ring
    rw [hkey2]
    push_cast
    ring
  rw [hsplit, hdiff, norm_mul, norm_mul, norm_mul]
  have hp : ‖GoldbachExplicitModeledMajor.phase (β / 2)‖ = 1 := by
    unfold GoldbachExplicitModeledMajor.phase
    exact Complex.norm_exp_ofReal_mul_I _
  have hI : ‖(Complex.I:ℂ)‖ = 1 := Complex.norm_I
  have hsn : ‖(Real.sin (Real.pi * β) : ℂ)‖ = |Real.sin (Real.pi * β)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h2c : ‖(2:ℂ)‖ = 2 := Complex.norm_two
  rw [hp, norm_neg, h2c, hI, hsn]
  ring

/-- Pointwise frequency bound: `|K_n(β)| ≤ 1/(2|β|)` away from `0` (and the integers). -/
lemma kernel_norm_le_freq (n : ℕ) (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ 1/2) :
    ‖GoldbachExplicitModeledMajor.kernel n β‖ ≤ 1 / (2 * |β|) := by
  have hkey := kernel_mul_one_sub_phase n β
  have habs : |Real.sin (Real.pi * β)| = Real.sin (Real.pi * |β|) := abs_sin_eq_sin_abs β hβ
  have hsinpos : (0:ℝ) < |Real.sin (Real.pi * β)| := by
    rw [habs]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [abs_pos.mpr hβ0, Real.pi_pos])
      (by nlinarith [abs_pos.mpr hβ0, abs_nonneg β, Real.pi_pos, hβ])
  have h1 : ‖GoldbachExplicitModeledMajor.kernel n β‖
      * ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase β‖
      = ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase ((n+1:ℕ) * β)‖ := by
    rw [← norm_mul, hkey]
  have h2 : ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase ((n+1:ℕ) * β)‖ ≤ 2 := by
    have h3 : ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase ((n+1:ℕ) * β)‖
        ≤ ‖(1:ℂ)‖ + ‖GoldbachExplicitModeledMajor.phase ((n+1:ℕ) * β)‖ := norm_sub_le _ _
    have h4 : ‖GoldbachExplicitModeledMajor.phase ((n+1:ℕ) * β)‖ = 1 := by
      unfold GoldbachExplicitModeledMajor.phase
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_one] at h3
    linarith
  have hbound : 2 * |β| ≤ |Real.sin (Real.pi * β)| := abs_sin_ge_two_mul_abs β hβ
  have hpos : (0:ℝ) < ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase β‖ := by
    rw [norm_one_sub_phase β]; linarith
  calc ‖GoldbachExplicitModeledMajor.kernel n β‖
      ≤ 2 / ‖(1:ℂ) - GoldbachExplicitModeledMajor.phase β‖ :=
        le_div_iff₀ hpos |>.mpr (le_trans (le_of_eq h1) h2)
    _ ≤ 1 / (2 * |β|) := by
        rw [norm_one_sub_phase β]
        have hx : (0:ℝ) < |β| := abs_pos.mpr hβ0
        have hs : (0:ℝ) < |Real.sin (Real.pi * β)| := hsinpos
        have hgoal : (1:ℝ) / |Real.sin (Real.pi * β)| ≤ 1 / (2 * |β|) := by
          refine (div_le_div_iff_of_pos_left (by norm_num) (by linarith) (by linarith)).mpr ?_
          exact hbound
        have hkey2 : (2:ℝ) / (2 * |Real.sin (Real.pi * β)|)
            = 1 / |Real.sin (Real.pi * β)| := by
          field_simp
        rw [hkey2]
        exact hgoal

/-- The annulus kernel mass decays like `1/(2h)`: `∫_{h<|β|≤k} |K_n|² ≤ 1/(2h)`. -/
lemma kernelMass_le_decay (n : ℕ) (h k : ℝ) (hh : 0 < h) (hkh : h ≤ k) (hk2 : k ≤ 1/2) :
    GoldbachExplicitModeledMajor.kernelMass n k - GoldbachExplicitModeledMajor.kernelMass n h
      ≤ 1 / (2 * h) := by
  have hsplit : GoldbachExplicitModeledMajor.kernelMass n k
      = GoldbachExplicitModeledMajor.kernelMass n h
        + 2 * ∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2 := by
    unfold GoldbachExplicitModeledMajor.kernelMass
    have hintA : IntervalIntegrable (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        MeasureTheory.volume (-k) (-h) := (continuous_kernel_norm n).intervalIntegrable (-k) (-h)
    have hintB : IntervalIntegrable (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        MeasureTheory.volume (-h) k := (continuous_kernel_norm n).intervalIntegrable (-h) k
    have hintC : IntervalIntegrable (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        MeasureTheory.volume (-h) h := (continuous_kernel_norm n).intervalIntegrable (-h) h
    have hintD : IntervalIntegrable (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        MeasureTheory.volume h k := (continuous_kernel_norm n).intervalIntegrable h k
    have hA : (∫ x in (-k:ℝ)..(-h), ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        + (∫ x in (-h:ℝ)..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        = ∫ x in (-k:ℝ)..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals hintA hintB
    have hB : (∫ x in (-h:ℝ)..h, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        + (∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        = ∫ x in (-h:ℝ)..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals hintC hintD
    have heven : ∀ x : ℝ, ‖GoldbachExplicitModeledMajor.kernel n (-x)‖ ^ 2
        = ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2 := fun x =>
      by rw [kernel_neg, Complex.norm_conj]
    have hC : ∫ x in (-k:ℝ)..(-h), ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2
        = ∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2 := by
      rw [← intervalIntegral.integral_comp_neg]
      exact intervalIntegral.integral_congr_ae (MeasureTheory.ae_of_all _ fun x _ => heven x)
    rw [← hA, ← hB, hC]
    ring
  have hint2 : IntervalIntegrable (fun x : ℝ => 1 / (4 * x ^ 2)) MeasureTheory.volume h k := by
    refine ContinuousOn.intervalIntegrable ?_
    have hc : ContinuousOn (fun x : ℝ => 1 / (4 * x ^ 2)) (Set.uIcc h k) := by
      rw [Set.uIcc_of_le hkh]
      exact ContinuousOn.div continuousOn_const
        (Continuous.continuousOn (by fun_prop : Continuous (fun x : ℝ => 4 * x ^ 2)))
        (fun x hx => by
          have hxpos : (0:ℝ) < x := by nlinarith [hh, hx.1]
          exact ne_of_gt (show (0:ℝ) < 4 * x ^ 2 by nlinarith [hxpos, hxpos]))
    exact hc
  have hmono : ∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2
      ≤ ∫ x in h..k, (1 / (4 * x ^ 2)) := by
    have hint : IntervalIntegrable (fun x : ℝ => ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2)
        MeasureTheory.volume h k := (continuous_kernel_norm n).intervalIntegrable h k
    exact intervalIntegral.integral_mono_on (by linarith) hint hint2
      (fun x hx => by
        have hxpos : (0:ℝ) < x := by nlinarith [hh, hx.1]
        have hxfreq := kernel_norm_le_freq n x (ne_of_gt hxpos) (by
          rw [abs_of_pos hxpos]; nlinarith [hx.2, hk2])
        rw [abs_of_pos hxpos] at hxfreq
        have h1 : ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2
            ≤ (1 / (2 * x)) ^ 2 := pow_le_pow_left₀ (by positivity) hxfreq 2
        have h2 : (1 / (2 * x)) ^ 2 = 1 / (4 * x ^ 2) := by
          rw [div_pow, mul_pow]; norm_num
        rw [h2] at h1
        exact h1)
  have hval : ∫ x in h..k, (1 / (4 * x ^ 2)) = 1 / (4 * h) - 1 / (4 * k) := by
    have hderiv : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y : ℝ => -((1:ℝ)/4)/y) (1 / (4 * x ^ 2)) x := by
      intro x hx
      have h1 := hasDerivAt_inv hx
      have h2 := h1.const_mul (-((1:ℝ)/4))
      have h3 : (fun y : ℝ => -((1:ℝ)/4)/y) = fun y : ℝ => -((1:ℝ)/4) * y⁻¹ := by
        funext y; field_simp
      rw [← h3] at h2
      have h4 : (-((1:ℝ)/4)) * (-(x ^ 2)⁻¹) = 1 / (4 * x ^ 2) := by
        field_simp
      rw [h4] at h2
      exact h2
    have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (ne_of_gt (show (0:ℝ) < x by
        have hx' : x ∈ Set.Icc h k := by rwa [Set.uIcc_of_le hkh] at hx
        nlinarith [hh, hx'.1]))) hint2
    exact hres.trans (by field_simp; ring)
  have hchain : GoldbachExplicitModeledMajor.kernelMass n k
      - GoldbachExplicitModeledMajor.kernelMass n h
      = 2 * ∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2 := by
    rw [hsplit]; ring
  have hbound2 : 2 * ∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2
      ≤ 2 * (1 / (4 * h) - 1 / (4 * k)) := by
    calc 2 * ∫ x in h..k, ‖GoldbachExplicitModeledMajor.kernel n x‖ ^ 2
        ≤ 2 * ∫ x in h..k, 1 / (4 * x ^ 2) := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 2 * (1 / (4 * h) - 1 / (4 * k)) := by rw [hval]
  have hfinal : 2 * (1 / (4 * h) - 1 / (4 * k)) ≤ 1 / (2 * h) := by
    have h6 : (0:ℝ) < k := by nlinarith [hh, hkh]
    have h7 : (0:ℝ) ≤ 1 / (2 * k) := div_nonneg (by norm_num) (by linarith)
    have h8 : 2 * (1 / (4 * h) - 1 / (4 * k)) = 1 / (2 * h) - 1 / (2 * k) := by
      field_simp
      ring
    rw [h8]
    linarith
  rw [hchain]
  exact le_trans hbound2 hfinal

/-- Bridge: `1 - phase y = -2i·phase(y/2)·sin(πy)`. -/
lemma one_sub_phase (y : ℝ) :
    (1:ℂ) - GoldbachExplicitModeledMajor.phase y
      = -2 * Complex.I * GoldbachExplicitModeledMajor.phase (y / 2)
          * (Real.sin (Real.pi * y) : ℂ) := by
  have key : ∀ E : ℂ, 1 - Complex.exp E
      = -2 * Complex.I * Complex.exp (E / 2)
          * ((Complex.exp (-(E / 2)) - Complex.exp (E / 2)) * Complex.I / 2) := by
    intro E
    have hunit : Complex.exp (E / 2) * Complex.exp (-(E / 2)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hA2 : Complex.exp E = Complex.exp (E / 2) ^ 2 := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    have hI2 : (Complex.I * Complex.I : ℂ) = -1 := Complex.I_mul_I
    have hrw : -2 * Complex.I * Complex.exp (E / 2)
          * ((Complex.exp (-(E / 2)) - Complex.exp (E / 2)) * Complex.I / 2)
        = (Complex.I * Complex.I)
          * (Complex.exp (E / 2) ^ 2
            - Complex.exp (E / 2) * Complex.exp (-(E / 2))) := by
      ring
    rw [hA2, hrw, hI2, hunit]
    ring
  have hsin : Complex.sin ((Real.pi * y : ℝ) : ℂ)
      = (Complex.exp (-((Real.pi * y : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((Real.pi * y : ℝ) : ℂ) * Complex.I)) * Complex.I / 2 := rfl
  unfold GoldbachExplicitModeledMajor.phase
  rw [key (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I), Complex.ofReal_sin, hsin]
  have hX1 : ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I / 2
      = ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    have h : (2 * Real.pi * y : ℝ) = 2 * (Real.pi * y) := by ring
    rw [h]
    push_cast
    ring
  have hX2 : ((2 * Real.pi * (y / 2) : ℝ) : ℂ) * Complex.I
      = ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    have h : (2 * Real.pi * (y / 2) : ℝ) = Real.pi * y := by ring
    rw [h]
  rw [hX1, hX2]
  ring

/-- Closed form of the geometric kernel away from the integers:
`K_n(β) = phase(nβ/2) · sin(π(n+1)β) / sin(πβ)`. -/
lemma kernel_eq_phase_sin (n : ℕ) (β : ℝ) (hβ : Real.sin (Real.pi * β) ≠ 0) :
    GoldbachExplicitModeledMajor.kernel n β
      = GoldbachExplicitModeledMajor.phase ((n:ℝ) / 2 * β)
          * ((Real.sin (Real.pi * ((n:ℝ) + 1) * β)
              / Real.sin (Real.pi * β) : ℝ) : ℂ) := by
  have hp2ne : GoldbachExplicitModeledMajor.phase (β / 2) ≠ 0 := by
    unfold GoldbachExplicitModeledMajor.phase
    exact Complex.exp_ne_zero _
  have hs2c : ((Real.sin (Real.pi * β) : ℝ) : ℂ) ≠ 0 := by
    intro hz
    rw [Complex.ofReal_eq_zero] at hz
    exact hβ hz
  have hp1 : GoldbachExplicitModeledMajor.phase (((n + 1 : ℕ) * β) / 2)
      = GoldbachExplicitModeledMajor.phase ((n:ℝ) / 2 * β)
          * GoldbachExplicitModeledMajor.phase (β / 2) := by
    rw [phase_add]
    congr 1
    push_cast
    ring
  have hsinarg : (Real.pi * ((n + 1 : ℕ) * β) : ℝ) = Real.pi * ((n:ℝ) + 1) * β := by
    push_cast
    ring
  have hstep : GoldbachExplicitModeledMajor.kernel n β
      * ((Real.sin (Real.pi * β) : ℝ) : ℂ)
      = GoldbachExplicitModeledMajor.phase ((n:ℝ) / 2 * β)
          * ((Real.sin (Real.pi * ((n:ℝ) + 1) * β) : ℝ) : ℂ) := by
    have hkey := kernel_mul_one_sub_phase n β
    rw [one_sub_phase β, one_sub_phase ((n + 1 : ℕ) * β), hp1, hsinarg] at hkey
    have hD : (-2:ℂ) * Complex.I * GoldbachExplicitModeledMajor.phase (β / 2)
        * ((Real.sin (Real.pi * β) : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp2ne) hs2c
    have h2 : GoldbachExplicitModeledMajor.kernel n β
        * ((Real.sin (Real.pi * β) : ℝ) : ℂ)
        * ((-2:ℂ) * Complex.I * GoldbachExplicitModeledMajor.phase (β / 2)
            * ((Real.sin (Real.pi * β) : ℝ) : ℂ))
      = GoldbachExplicitModeledMajor.phase ((n:ℝ) / 2 * β)
        * ((Real.sin (Real.pi * ((n:ℝ) + 1) * β) : ℝ) : ℂ)
        * ((-2:ℂ) * Complex.I * GoldbachExplicitModeledMajor.phase (β / 2)
            * ((Real.sin (Real.pi * β) : ℝ) : ℂ)) := by
      have h1 := congrArg (fun z : ℂ => z * ((Real.sin (Real.pi * β) : ℝ) : ℂ)) hkey
      have h3 : GoldbachExplicitModeledMajor.kernel n β
          * ((Real.sin (Real.pi * β) : ℝ) : ℂ)
          * ((-2:ℂ) * Complex.I * GoldbachExplicitModeledMajor.phase (β / 2)
              * ((Real.sin (Real.pi * β) : ℝ) : ℂ))
        = (GoldbachExplicitModeledMajor.kernel n β
            * ((-2:ℂ) * Complex.I * GoldbachExplicitModeledMajor.phase (β / 2)
                * ((Real.sin (Real.pi * β) : ℝ) : ℂ)))
          * ((Real.sin (Real.pi * β) : ℝ) : ℂ) := by
        ring
      rw [h3, h1]
      ring
    exact mul_right_cancel₀ hD h2
  have hdiv : ((Real.sin (Real.pi * ((n:ℝ) + 1) * β) : ℝ) : ℂ)
      / ((Real.sin (Real.pi * β) : ℝ) : ℂ)
      = ((Real.sin (Real.pi * ((n:ℝ) + 1) * β) / Real.sin (Real.pi * β) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
  rw [(eq_div_iff hs2c).mpr hstep, mul_div_assoc, hdiv]

/-- The annulus integrand is real and nonnegative:
`K_n(β)²·phase(-nβ) = (sin(π(n+1)β)/sin(πβ))²`. -/
lemma kernel_sq_phase_sin (n : ℕ) (β : ℝ) (hβ : Real.sin (Real.pi * β) ≠ 0) :
    GoldbachExplicitModeledMajor.kernel n β ^ 2
        * GoldbachExplicitModeledMajor.phase (-(n:ℝ) * β)
      = ((Real.sin (Real.pi * ((n:ℝ) + 1) * β)
          / Real.sin (Real.pi * β) : ℝ) : ℂ) ^ 2 := by
  have h1 := kernel_eq_phase_sin n β hβ
  have hpow : GoldbachExplicitModeledMajor.phase ((n:ℝ) / 2 * β) ^ 2
      = GoldbachExplicitModeledMajor.phase ((n:ℝ) * β) := by
    rw [pow_two, phase_add]
    congr 1
    ring
  have hzero : GoldbachExplicitModeledMajor.phase (0:ℝ) = 1 := by
    unfold GoldbachExplicitModeledMajor.phase
    simp
  have hunit : GoldbachExplicitModeledMajor.phase ((n:ℝ) * β)
      * GoldbachExplicitModeledMajor.phase (-(n:ℝ) * β) = 1 := by
    rw [phase_add, show (((n:ℝ) * β + -(n:ℝ) * β):ℝ) = 0 from by ring, hzero]
  rw [h1, mul_pow, hpow, mul_right_comm, hunit, one_mul]

end CharExpand

section Ramanujan

/-- `GE` at a natural multiple of `x` is a power of `GE x`. -/
lemma GE_mul_nat (x : ℝ) (b : ℕ) : GE (x * b) = GE x ^ b := by
  induction b with
  | zero => simp [GE]
  | succ k ih =>
    have h : x * ((k:ℝ) + 1) = x * (k:ℝ) + x := by ring
    rw [Nat.cast_add_one, pow_succ, h, ← GE_add, ih]

/-- `GE` at a natural number is `1`. -/
lemma GE_nat_eq_one (k : ℕ) : GE (k:ℝ) = 1 := by
  have h : GE (k:ℝ) = GoldbachExplicitModeledMajor.phase (k:ℝ) := rfl
  rw [h]
  exact phase_nat k

/-- Complete additive-character sum over one period:
`∑_{b<m} e(nb/m) = m` if `m ∣ n`, and `0` otherwise. -/
lemma complete_char_sum (m n : ℕ) (hm : 0 < m) :
    ∑ b ∈ Finset.range m, GE ((n:ℝ) * b / m)
      = if m ∣ n then ((m:ℕ):ℂ) else 0 := by
  have hm0 : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hterm : ∀ b : ℕ, GE ((n:ℝ) * b / m) = GE ((n:ℝ) / m) ^ b := by
    intro b
    have h : ((n:ℝ) * b / m : ℝ) = ((n:ℝ) / m) * b := by rw [mul_div_right_comm]
    rw [h, GE_mul_nat]
  simp only [hterm]
  have hkey : GE ((n:ℝ) / m) = 1 ↔ m ∣ n := by
    have hshape : ((2 * Real.pi * ((n:ℝ) / m) : ℝ) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I * (n:ℂ) / (m:ℂ) := by
      push_cast
      ring
    unfold GE
    rw [hshape, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne']
  by_cases hd : m ∣ n
  · rw [hkey.mpr hd, if_pos hd]
    simp
  · have hζ1 : GE ((n:ℝ) / m) ≠ 1 := fun h => hd (hkey.mp h)
    have hζm : GE ((n:ℝ) / m) ^ m = 1 := by
      have h : (((n:ℝ) / m) * m : ℝ) = (n:ℝ) := by field_simp
      rw [← GE_mul_nat, h, GE_nat_eq_one]
    rw [if_neg hd, geom_sum_eq hζ1 m, hζm]
    simp


/-- `GE` at the negation is the inverse of `GE`. -/
lemma GE_neg (x : ℝ) : GE (-x) = (GE x)⁻¹ := by
  have h := GE_add (-x) x
  rw [neg_add_cancel, GE_zero] at h
  exact eq_inv_of_mul_eq_one_left h

/-- `e(n/m) = 1` iff `m ∣ n`. -/
lemma GE_div_eq_one_iff (m n : ℕ) (hm : 0 < m) : GE ((n:ℝ) / m) = 1 ↔ m ∣ n := by
  have hshape : ((2 * Real.pi * ((n:ℝ) / m) : ℝ) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * (n:ℂ) / (m:ℂ) := by
    push_cast
    ring
  unfold GE
  rw [hshape, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne']

/-- `e(-n/m) = 1` iff `m ∣ n`. -/
lemma GE_neg_div_eq_one_iff (m n : ℕ) (hm : 0 < m) : GE (-(n:ℝ) / m) = 1 ↔ m ∣ n := by
  rw [neg_div, GE_neg, inv_eq_one, GE_div_eq_one_iff m n hm]

/-- Complete additive-character sum with negative frequency:
`∑_{b<m} e(-nb/m) = m` if `m ∣ n`, and `0` otherwise. -/
lemma complete_char_sum_neg (m n : ℕ) (hm : 0 < m) :
    ∑ b ∈ Finset.range m, GE (-(n:ℝ) * b / m)
      = if m ∣ n then ((m:ℕ):ℂ) else 0 := by
  have hm0 : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hterm : ∀ b : ℕ, GE (-(n:ℝ) * b / m) = GE (-(n:ℝ) / m) ^ b := by
    intro b
    have h : ((-(n:ℝ)) * b / m : ℝ) = ((-(n:ℝ)) / m) * b := by rw [mul_div_right_comm]
    rw [h, GE_mul_nat]
  simp only [hterm]
  by_cases hd : m ∣ n
  · rw [GE_neg_div_eq_one_iff m n hm |>.mpr hd, if_pos hd]
    simp
  · have hζ1 : GE (-(n:ℝ) / m) ≠ 1 := fun h => hd (GE_neg_div_eq_one_iff m n hm |>.mp h)
    have hζm : GE (-(n:ℝ) / m) ^ m = 1 := by
      have h : (((-(n:ℝ)) / m) * m : ℝ) = (-(n:ℝ)) := by field_simp
      have hn1 : GE (-(n:ℝ)) = 1 := by
        rw [GE_neg, GE_nat_eq_one, inv_one]
      rw [← GE_mul_nat, h, hn1]
    rw [if_neg hd, geom_sum_eq hζ1 m, hζm]
    simp

/-- The Ramanujan sum `c_q(n) = ∑_{(a,q)=1} e(-na/q)`. -/
noncomputable def csum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), GE (-(n:ℝ) * a / q)

/-- Möbius sum over the divisors of `g` is the coprimality indicator. -/
lemma sum_moebius_divisors_eq_indicator (g : ℕ) (hg : 0 < g) :
    (∑ d ∈ Nat.divisors g, (ArithmeticFunction.moebius d : ℂ)) = if g = 1 then 1 else 0 := by
  by_cases h1 : g = 1
  · subst h1
    rw [if_pos rfl, Nat.divisors_one, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one, Int.cast_one]
  · rw [if_neg h1]
    have hne : Nat.primeFactors g ≠ ∅ := by
      intro hempty
      rcases Nat.primeFactors_eq_empty.mp hempty with h0 | h1'
      · exact hg.ne' h0
      · exact h1 h1'
    have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub
      (f := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      (ArithmeticFunction.isMultiplicative_zeta.natCast) (n := g) (by positivity)
    simp only [ArithmeticFunction.natCoe_apply] at h
    have hz : ∀ d : ℕ, 0 < d → ((ArithmeticFunction.zeta d : ℕ) : ℂ) = 1 := by
      intro d hd
      rw [ArithmeticFunction.zeta_apply_ne hd.ne', Nat.cast_one]
    rw [Finset.sum_congr rfl (fun d hd => by
      rw [hz d (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hg), mul_one])] at h
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [← h, Finset.prod_eq_zero hp (by rw [hz p (Nat.mem_primeFactors.mp hp).1.pos, sub_self])]

/-- Möbius expansion of the Ramanujan sum into complete character sums. -/
lemma csum_eq_moebius (q n : ℕ) (hq : 0 < q) :
    csum q n
      = ∑ d ∈ Nat.divisors q, (ArithmeticFunction.moebius d : ℂ)
          * (if (q/d:ℕ) ∣ n then ((q/d:ℕ):ℂ) else 0) := by
  have hcop : ∀ a : ℕ, (Nat.gcd a q).divisors = (Nat.divisors q).filter (fun d => d ∣ a) := by
    intro a
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro h
      have h2 := Nat.dvd_gcd_iff.mp h.1
      exact ⟨⟨h2.2, hq.ne'⟩, h2.1⟩
    · intro h
      exact ⟨Nat.dvd_gcd h.2 h.1.1, Nat.gcd_pos_of_pos_right a hq |>.ne'⟩
  have hind : ∀ a : ℕ, (if Nat.Coprime a q then (1:ℂ) else 0)
      = ∑ d ∈ (Nat.gcd a q).divisors, (ArithmeticFunction.moebius d : ℂ) := by
    intro a
    by_cases hc : Nat.Coprime a q
    · rw [if_pos hc, sum_moebius_divisors_eq_indicator (Nat.gcd a q)
        (Nat.gcd_pos_of_pos_right a hq), if_pos (Nat.coprime_iff_gcd_eq_one.mp hc)]
    · rw [if_neg hc, sum_moebius_divisors_eq_indicator (Nat.gcd a q)
        (Nat.gcd_pos_of_pos_right a hq),
        if_neg (fun h1 => hc (Nat.coprime_iff_gcd_eq_one.mpr h1))]
  have hmul : ∀ a : ℕ, (if Nat.Coprime a q then GE (-(n:ℝ) * a / q) else 0)
      = (∑ d ∈ (Nat.gcd a q).divisors, (ArithmeticFunction.moebius d : ℂ))
          * GE (-(n:ℝ) * a / q) := by
    intro a
    by_cases hc : Nat.Coprime a q
    · rw [if_pos hc, sum_moebius_divisors_eq_indicator (Nat.gcd a q)
        (Nat.gcd_pos_of_pos_right a hq), if_pos (Nat.coprime_iff_gcd_eq_one.mp hc), one_mul]
    · rw [if_neg hc, sum_moebius_divisors_eq_indicator (Nat.gcd a q)
        (Nat.gcd_pos_of_pos_right a hq),
        if_neg (fun h1 => hc (Nat.coprime_iff_gcd_eq_one.mpr h1)), zero_mul]
  have hreidx : ∀ d : ℕ, d ∣ q →
      (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), GE (-(n:ℝ) * a / q))
        = ∑ b ∈ Finset.range (q/d), GE (-(n:ℝ) * b / ((q/d : ℕ) : ℝ)) := by
    intro d hd
    have hd0 : d ≠ 0 := fun h => hq.ne' (by rw [h] at hd; exact Nat.zero_dvd.mp hd)
    have hd0' : 0 < d := Nat.pos_of_dvd_of_pos hd hq
    have hinj : Set.InjOn (fun b => d * b) ↑(Finset.range (q/d)) := by
      intro x _ y _ h
      have h' : d * x = d * y := h
      exact Nat.eq_of_mul_eq_mul_left hd0' h'
    have hsummand : ∀ x : ℕ,
        GE (-(n:ℝ) * ((d * x : ℕ) : ℝ) / q) = GE (-(n:ℝ) * x / ((q/d : ℕ) : ℝ)) := by
      intro x
      have hq0 : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have hqz : ((q:ℝ) / d) ≠ 0 := div_ne_zero hq0 (Nat.cast_ne_zero.mpr hd0)
      have hcd : ((q/d : ℕ) : ℝ) = (q:ℝ) / (d:ℝ) := Nat.cast_div hd (Nat.cast_ne_zero.mpr hd0)
      have halg : (-(n:ℝ) * ((d:ℝ) * (x:ℝ)) / q) = (-(n:ℝ) * (x:ℝ) / ((q/d : ℕ) : ℝ)) := by
        rw [hcd, div_div_eq_mul_div]
        ring
      rw [Nat.cast_mul, halg]
    have hset : (Finset.range q).filter (fun a => d ∣ a)
        = (Finset.range (q/d)).image (fun b => d * b) := by
      ext a
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · intro h
        exact ⟨a / d, by rw [Finset.mem_range, Nat.div_lt_div_right hd0 hd]; exact h.1,
          Nat.mul_div_cancel' h.2⟩
      · rintro ⟨b, hb1, hb2⟩
        have hb2' : d * b = a := hb2
        have hb1' : b < q / d := by rwa [Finset.mem_range] at hb1
        refine ⟨?_, ?_⟩
        · rw [← hb2']
          have h1 : d * b < d * (q / d) := (Nat.mul_lt_mul_left hd0').mpr hb1'
          rwa [Nat.mul_div_cancel' hd] at h1
        · rw [← hb2']
          exact ⟨b, rfl⟩
    rw [hset, Finset.sum_image hinj, Finset.sum_congr rfl (fun x _ => hsummand x)]
  rw [csum, Finset.sum_filter, Finset.sum_congr rfl (fun a _ => hmul a)]
  simp only [hcop]
  simp only [Finset.sum_mul]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_filter]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun d hd => by
    rw [hreidx d (Nat.dvd_of_mem_divisors hd), complete_char_sum_neg (q/d) n
      (Nat.div_pos (Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors hd) hq))])]

/-- The reciprocal identity function on `ℕ`, as a multiplicative arithmetic function into `ℂ`. -/
private noncomputable def invId : ArithmeticFunction ℂ := ⟨fun d => ((d : ℕ) : ℂ)⁻¹, by
  rw [Nat.cast_zero, inv_zero]⟩

private lemma isMultiplicative_invId : invId.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn _ => ?_⟩
  · simp only [invId, ArithmeticFunction.coe_mk, Nat.cast_one, inv_one]
  · simp only [invId, ArithmeticFunction.coe_mk]
    rw [Nat.cast_mul, mul_inv (m:ℂ) (n:ℂ)]

/-- Möbius inversion of the totient: `∑_{d ∣ g} μ(d) · (g/d) = φ(g)`. -/
lemma sum_moebius_mul_div_eq_totient (g : ℕ) (hg : 0 < g) (hsq : Squarefree g) :
    ∑ d ∈ Nat.divisors g, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (((g/d : ℕ) : ℂ))
      = ((Nat.totient g : ℕ) : ℂ) := by
  classical
  have hrec := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub
    (f := invId) isMultiplicative_invId (n := g) hg.ne'
  simp only [invId, ArithmeticFunction.coe_mk] at hrec
  have hcast : ∀ d ∈ Nat.divisors g, ((g/d : ℕ) : ℂ) = (g:ℂ)/(d:ℂ) := fun d hd =>
    Nat.cast_div (Nat.dvd_of_mem_divisors hd)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hg)))
  have hpt : ∀ d ∈ Nat.divisors g, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((g:ℂ)/(d:ℂ))
      = (g:ℂ) * (((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((d:ℂ)⁻¹)) := fun d hd => by
    field_simp
  rw [Finset.sum_congr rfl (fun d hd => by rw [hcast d hd, hpt d hd]), ← Finset.mul_sum]
  rw [← hrec]
  have hsq0 : (g:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hp1 : ∏ p ∈ g.primeFactors, (1 - (p:ℂ)⁻¹)
      = (∏ p ∈ g.primeFactors, ((p:ℂ) - 1)) / ∏ p ∈ g.primeFactors, ((p:ℕ):ℂ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_primeFactors hp))
    field_simp
  have hden : ∏ p ∈ g.primeFactors, ((p:ℕ):ℂ) = (g:ℂ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hphi : (Nat.totient g : ℕ) = ∏ p ∈ g.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hsq,
      Nat.div_self hg, one_mul]
  rw [hp1, hden, hphi, Nat.cast_prod, mul_comm (g:ℂ), div_mul_cancel₀ _ hsq0]
  have hfin : ∀ p ∈ g.primeFactors, (((p:ℕ):ℂ) - 1) = ((p - 1 : ℕ) : ℂ) := fun p hp =>
    (Nat.cast_sub (Nat.succ_le_of_lt (Nat.pos_of_mem_primeFactors hp))).symm
  exact Finset.prod_congr rfl hfin

/-- Squarefree evaluation of the Ramanujan sum: `c_q(n) = μ(q/(q,n)) · φ((q,n))`. -/
lemma csum_eq_moebius_totient (q n : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    csum q n
      = ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℂ)
          * ((Nat.totient (Nat.gcd q n) : ℕ) : ℂ) := by
  classical
  set g := Nat.gcd q n with hgdef
  have hg : 0 < g := by rw [hgdef, Nat.gcd_comm]; exact Nat.gcd_pos_of_pos_right n hq
  have hgq : g ∣ q := by rw [hgdef]; exact Nat.gcd_dvd_left q n
  have hgsq : Squarefree g := by
    rw [hgdef]; exact Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left q n) hsq
  have hcqg : Nat.Coprime (q / g) g :=
    Nat.coprime_of_squarefree_mul (by rw [Nat.mul_comm, Nat.mul_div_cancel' hgq]; exact hsq)
  rw [csum_eq_moebius q n hq]
  have hcond : ∀ d ∈ Nat.divisors q, ((q/d : ℕ) ∣ n) ↔ ((q/d : ℕ) ∣ g) := by
    intro d hd
    refine ⟨fun h => Nat.dvd_gcd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)) h,
      fun h => Nat.dvd_trans h (Nat.gcd_dvd_right q n)⟩
  have hstep : ∀ d ∈ Nat.divisors q, (ArithmeticFunction.moebius d : ℂ)
      * (if (q/d:ℕ) ∣ n then ((q/d:ℕ):ℂ) else 0)
      = (ArithmeticFunction.moebius d : ℂ)
      * (if (q/d:ℕ) ∣ g then ((q/d:ℕ):ℂ) else 0) := fun d hd => by
    simp only [hcond d hd]
  rw [Finset.sum_congr rfl hstep]
  simp only [mul_ite_zero, ← Finset.sum_filter]
  have hset : (Nat.divisors q).filter (fun d => (q/d : ℕ) ∣ g)
      = (Nat.divisors g).image (fun e => q / e) := by
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · intro ⟨hdq, hdg⟩
      refine ⟨q / d, Nat.mem_divisors.mpr ⟨hdg, hg.ne'⟩, Nat.div_div_self hdq.1 hq.ne'⟩
    · rintro ⟨e, he, hde⟩
      obtain ⟨heg, _⟩ := Nat.mem_divisors.mp he
      have heq : e ∣ q := Nat.dvd_trans heg hgq
      refine ⟨?_, ?_⟩
      · rw [← hde]
        exact ⟨Nat.div_dvd_of_dvd heq, hq.ne'⟩
      · rw [← hde, Nat.div_div_self heq hq.ne']
        exact heg
  rw [hset, Finset.sum_image (fun e he f hf h => by
    rw [← Nat.div_div_self (Nat.dvd_trans (Nat.dvd_of_mem_divisors he) hgq) hq.ne', h,
      Nat.div_div_self (Nat.dvd_trans (Nat.dvd_of_mem_divisors hf) hgq) hq.ne'])]
  rw [Finset.sum_congr rfl (fun e he => by
    rw [Nat.div_div_self (Nat.dvd_trans (Nat.dvd_of_mem_divisors he) hgq) hq.ne'])]
  -- Reindex `e = g/d` and split `μ(q/e) = μ(q/g) · μ(d)`.
  have hset2 : Nat.divisors g = (Nat.divisors g).image (fun d => g / d) := by
    ext e
    rw [Nat.mem_divisors, Finset.mem_image]
    constructor
    · intro he
      refine ⟨g / e, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd he.1, he.2⟩,
        Nat.div_div_self he.1 he.2⟩
    · rintro ⟨d, hd, hde⟩
      obtain ⟨hdg, hne⟩ := Nat.mem_divisors.mp hd
      rw [← hde]
      exact ⟨Nat.div_dvd_of_dvd hdg, hne⟩
  rw [hset2, Finset.sum_image (fun d hd f hf h => by
    rw [← Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hg.ne', h,
      Nat.div_div_self (Nat.dvd_of_mem_divisors hf) hg.ne'])]
  have hsplit : ∀ d ∈ Nat.divisors g, (ArithmeticFunction.moebius (q / (g / d)) : ℂ)
      * (((g/d:ℕ):ℂ))
      = (ArithmeticFunction.moebius (q / g) : ℂ)
        * ((ArithmeticFunction.moebius d : ℂ) * (((g/d:ℕ):ℂ))) := by
    intro d hd
    have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
    have hq2 : q = ((q / g) * d) * (g / d) := by
      rw [Nat.mul_assoc, Nat.mul_div_cancel' hdg, Nat.mul_comm (q / g) g,
        Nat.mul_div_cancel' hgq]
    have hqs : q / (g / d) = (q / g) * d :=
      Nat.div_eq_of_eq_mul_left (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hdg) hg) hq2
    rw [hqs, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius
      (Nat.coprime_iff_gcd_eq_one.mp (hcqg.coprime_dvd_right hdg)), Int.cast_mul, mul_assoc]
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum,
    ← sum_moebius_mul_div_eq_totient g hg hgsq]

/-- Coprime evaluation of the Ramanujan sum: `c_q(a) = μ(q)` when `(a,q) = 1`. -/
lemma csum_of_coprime (q a : ℕ) (hq : 0 < q) (hsq : Squarefree q) (hcop : Nat.Coprime a q) :
    csum q a = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  rw [csum_eq_moebius_totient q a hq hsq, Nat.gcd_comm, Nat.coprime_iff_gcd_eq_one.mp hcop,
    Nat.div_one, Nat.totient_one, Nat.cast_one, mul_one]

/-- The reduced-residue identity `∑_{(a,q)=1} c_q(a)²·e(-na/q) = c_q(n)` for squarefree `q`,
combining the singular-series weights with the Ramanujan sum. -/
lemma csum_reduced_sq_sum (q n : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      (csum q a) ^ 2 * GE (-(n:ℝ) * a / q) = csum q n := by
  have hconst : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      (csum q a) ^ 2 * GE (-(n:ℝ) * a / q) = GE (-(n:ℝ) * a / q) := by
    intro a ha
    have hcop := (Finset.mem_filter.mp ha).2
    rw [csum_of_coprime q a hq hsq hcop, ← Int.cast_pow,
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl hconst, csum]

/-- Divisor form of the Ramanujan sum: `c_q(n) = ∑_{d | (q,n)} d · μ(q/d)`. -/
lemma csum_eq_divisor_moebius (q n : ℕ) (hq : 0 < q) :
    csum q n = ∑ d ∈ Nat.divisors (Nat.gcd q n),
      ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * ((d : ℕ) : ℂ) := by
  classical
  have hg : 0 < Nat.gcd q n := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_right n hq
  rw [csum_eq_moebius q n hq]
  have hmap : Nat.divisors q = (Nat.divisors q).image (fun d => q / d) := by
    ext e
    rw [Nat.mem_divisors, Finset.mem_image]
    constructor
    · intro he
      refine ⟨q / e, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd he.1, he.2⟩,
        Nat.div_div_self he.1 he.2⟩
    · rintro ⟨d, hd, hde⟩
      obtain ⟨hdq, hne⟩ := Nat.mem_divisors.mp hd
      rw [← hde]
      exact ⟨Nat.div_dvd_of_dvd hdq, hne⟩
  rw [hmap, Finset.sum_image (fun d hd e he h => by
    rw [← Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne', h,
      Nat.div_div_self (Nat.dvd_of_mem_divisors he) hq.ne'])]
  rw [Finset.sum_congr rfl (fun e he => by
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hq.ne'])]
  simp only [mul_ite_zero, ← Finset.sum_filter]
  have hfil : (Nat.divisors q).filter (fun e => e ∣ n) = Nat.divisors (Nat.gcd q n) := by
    ext e
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    refine ⟨fun h => ⟨Nat.dvd_gcd h.1.1 h.2, hg.ne'⟩, fun h => ?_⟩
    obtain ⟨h1, h2⟩ := Nat.dvd_gcd_iff.mp h.1
    exact ⟨⟨h1, hq.ne'⟩, h2⟩
  rw [hfil]

/-- The Ramanujan sum is an integer, exhibited as an `ℤ`-cast. -/
lemma csum_eq_intCast (q n : ℕ) (hq : 0 < q) :
    csum q n = ((∑ d ∈ Nat.divisors (Nat.gcd q n),
      ArithmeticFunction.moebius (q / d) * (d : ℤ) : ℤ) : ℂ) := by
  rw [csum_eq_divisor_moebius q n hq, Int.cast_sum]
  exact Finset.sum_congr rfl fun d _ => (Int.cast_mul _ _).symm

/-- The Ramanujan sum has zero imaginary part. -/
lemma csum_im_eq_zero (q n : ℕ) (hq : 0 < q) : (csum q n).im = 0 := by
  rw [csum_eq_intCast q n hq]
  rfl

/-- For squarefree `q`, the real Ramanujan sum satisfies `c_q(n) ≥ -φ((q,n))`. -/
lemma csum_re_ge_neg_totient (q n : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    -((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) ≤ (csum q n).re := by
  have hg0 : 0 < Nat.gcd q n := Nat.gcd_pos_of_pos_left n hq
  have hval : (csum q n).re
      = ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℝ)
        * ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) := by
    rw [csum_eq_moebius_totient q n hq hsq, Complex.mul_re]
    simp
  have hgsq : Squarefree (q / Nat.gcd q n) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q n)) hsq
  have hunit : ArithmeticFunction.moebius (q / Nat.gcd q n) = 1
      ∨ ArithmeticFunction.moebius (q / Nat.gcd q n) = -1 :=
    sq_eq_one_iff.mp (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hgsq)
  rw [hval]
  have hφ : 0 ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases hunit with h | h
  · rw [h, Int.cast_one, one_mul]
    linarith
  · rw [h, Int.cast_neg, Int.cast_one, neg_one_mul]

open Classical in
/-- Conditional model-sum floor: with nonnegative weights on squarefree moduli, the
weighted Ramanujan model sum is bounded below by minus the mass of its negative part.
Since `|c_q(n)| = φ((q,n))`, bounding that negative part by `ε*n` is precisely the
remaining signed-cancellation problem for the skirt. -/
lemma model_sum_floor_of_neg_bound (s : Finset ℕ) (n : ℕ) (ε : ℝ) (w : ℕ → ℝ)
    (hq : ∀ q ∈ s, 0 < q) (hsq : ∀ q ∈ s, Squarefree q) (hw : ∀ q ∈ s, 0 ≤ w q)
    (hbound : ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) * w q ≤ ε * (n : ℝ)) :
    ∑ q ∈ s, (csum q n).re * w q ≥ -(ε * (n : ℝ)) := by
  classical
  have hdisj : Disjoint (s.filter (fun q => (csum q n).re < 0))
      (s.filter (fun q => ¬((csum q n).re < 0))) :=
    Finset.disjoint_left.mpr fun a ha hb => by
      simp only [Finset.mem_filter] at ha hb
      exact absurd ha.2 hb.2
  have hsplit : ∑ q ∈ s, (csum q n).re * w q
      = ∑ q ∈ s.filter (fun q => (csum q n).re < 0), (csum q n).re * w q
        + ∑ q ∈ s.filter (fun q => ¬((csum q n).re < 0)), (csum q n).re * w q := by
    rw [← Finset.sum_union hdisj, Finset.filter_union_filter_not_eq]
  have hpos : 0 ≤ ∑ q ∈ s.filter (fun q => ¬((csum q n).re < 0)), (csum q n).re * w q :=
    Finset.sum_nonneg fun q hq' => by
      have hq'' : q ∈ s := (Finset.mem_filter.mp hq').1
      exact mul_nonneg (le_of_not_gt (Finset.mem_filter.mp hq').2) (hw q hq'')
  have hfinal : ∑ q ∈ s, (csum q n).re * w q
      ≥ -∑ q ∈ s.filter (fun q => (csum q n).re < 0),
          ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) * w q := by
    rw [hsplit]
    have h1 : ∑ q ∈ s.filter (fun q => (csum q n).re < 0), (csum q n).re * w q
        ≥ ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
            (-((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)) * w q :=
      Finset.sum_le_sum fun q hq' => by
        have hq'' : q ∈ s := (Finset.mem_filter.mp hq').1
        exact mul_le_mul_of_nonneg_right (csum_re_ge_neg_totient q n (hq q hq'') (hsq q hq''))
          (hw q hq'')
    have h2 : ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        (-((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)) * w q
        = -∑ q ∈ s.filter (fun q => (csum q n).re < 0),
            ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) * w q := by
      rw [Finset.sum_congr rfl (fun q _ => neg_mul ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) (w q)),
        Finset.sum_neg_distrib]
    linarith [hpos, h1, h2]
  exact ge_trans hfinal (neg_le_neg hbound)

/-! ### The skirt annulus kernel mass ΔJ(q)

For a reduced denominator `q`, the skirt is the annulus between the core arcs
(radius `Q/(qn)`) and the inner region (radius `Q·n^(1/6)/(qn)`).  Its model
contribution is governed by the kernel mass on that annulus; since
`K_n(β)^2 · e(-nβ) = (sin π(n+1)β / sin πβ)^2 ≥ 0` (`kernel_sq_phase_sin`),
the quantity below is real and nonnegative. -/

/-- The kernel mass on the skirt annulus at denominator `q`: between the core
radius `Q/(qn)` and the inner radius `Q·n^(1/6)/(qn)`. -/
noncomputable def deltaJ (n q : ℕ) : ℝ :=
  GoldbachExplicitModeledMajor.kernelMass n
    ((Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)))
    - GoldbachExplicitModeledMajor.kernelMass n
      ((Qf n:ℝ)/((q:ℝ)*(n:ℝ)))

/-- The inner skirt radius dominates the core radius. -/
lemma deltaJ_radii_mono (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (Qf n:ℝ)/((q:ℝ)*(n:ℝ)) ≤ (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) := by
  have hq0 : 0 < (q:ℝ)*(n:ℝ) := mul_pos (by exact_mod_cast hq) (by exact_mod_cast hn)
  have hone : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hpow : 1 ≤ (n:ℝ)^(1/6:ℝ) := Real.one_le_rpow hone (by norm_num)
  have hkey : (Qf n:ℝ)/((q:ℝ)*(n:ℝ)) * (n:ℝ)^(1/6:ℝ)
      = (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) := div_mul_eq_mul_div _ _ _
  rw [← hkey]
  exact le_mul_of_one_le_right (div_nonneg (by positivity) hq0.le) hpow

/-- The skirt annulus mass is nonnegative. -/
lemma deltaJ_nonneg (n q : ℕ) : 0 ≤ deltaJ n q := by
  by_cases hn : 0 < n
  · by_cases hq : 0 < q
    · exact sub_nonneg.mpr (GoldbachExplicitModeledMajor.kernelMass_mono
        (div_nonneg (by positivity) (mul_pos (by exact_mod_cast hq) (by exact_mod_cast hn)).le)
        (deltaJ_radii_mono n q hn hq) n)
    · have hq0 : q = 0 := by omega
      subst hq0
      simp only [deltaJ, Nat.cast_zero, zero_mul, div_zero, sub_self, le_refl]
  · have hn0 : n = 0 := by omega
    subst hn0
    simp only [deltaJ, Nat.cast_zero, Real.zero_rpow (by norm_num : (1/6:ℝ) ≠ 0), mul_zero,
      div_zero, sub_self, le_refl]

/-- The skirt annulus mass is at most a full period's mass. -/
lemma deltaJ_le_card (n q : ℕ) (hn : 0 < n) (hq : 0 < q)
    (h : (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2) :
    deltaJ n q ≤ (n + 1 : ℝ) := by
  have hh : 0 ≤ (Qf n:ℝ)/((q:ℝ)*(n:ℝ)) :=
    div_nonneg (by positivity) (mul_pos (by exact_mod_cast hq) (by exact_mod_cast hn)).le
  exact kernelMass_annulus_le_card n _ _ hh (deltaJ_radii_mono n q hn hq) h

/-- The skirt annulus mass is at most its length times the peak. -/
lemma deltaJ_le_length (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    deltaJ n q ≤ 2 * ((Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ))) * ((n+1:ℝ)^2) := by
  have hh : 0 ≤ (Qf n:ℝ)/((q:ℝ)*(n:ℝ)) :=
    div_nonneg (by positivity) (mul_pos (by exact_mod_cast hq) (by exact_mod_cast hn)).le
  exact kernelMass_annulus_le_length n _ _ hh (deltaJ_radii_mono n q hn hq)

/-- The skirt annulus mass decays like the core radius: ΔJ(q) ≤ qn/(2Q). -/
lemma deltaJ_le_decay (n q : ℕ) (hn : 0 < n) (hq : 0 < q)
    (h : (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2) :
    deltaJ n q ≤ (q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) := by
  have hq0 : 0 < (q:ℝ)*(n:ℝ) := mul_pos (by exact_mod_cast hq) (by exact_mod_cast hn)
  have hl : 0 < Nat.log 2 (n+2) := Nat.log_pos (by norm_num) (by omega)
  have hQ0 : 0 < Qf n := by
    unfold Qf
    rw [pow_two]
    exact Nat.mul_pos hl hl
  have hr1 : 0 < (Qf n:ℝ)/((q:ℝ)*(n:ℝ)) := div_pos (by exact_mod_cast hQ0) hq0
  have hconv : 1/(2*((Qf n:ℝ)/((q:ℝ)*(n:ℝ)))) = (q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) := by
    rw [← mul_div_assoc, div_div_eq_mul_div, one_mul]
  have hkd := kernelMass_le_decay n _ _ hr1 (deltaJ_radii_mono n q hn hq) h
  rwa [hconv] at hkd

/-- The three upper bounds together. -/
theorem deltaJ_le (n q : ℕ) (hn : 0 < n) (hq : 0 < q)
    (h : (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2) :
    deltaJ n q ≤ min ((n+1:ℝ))
      (min (2*((Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)))*((n+1:ℝ)^2))
        ((q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)))) :=
  le_min (deltaJ_le_card n q hn hq h)
    (le_min (deltaJ_le_length n q hn hq) (deltaJ_le_decay n q hn hq h))

/-- The real part of the Ramanujan sum on a squarefree modulus is
`μ(q/(q,n))·φ((q,n))`. -/
lemma csum_re_eq (q n : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    (csum q n).re
      = ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℝ)
          * ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) := by
  rw [csum_eq_moebius_totient q n hq hsq]
  simp [Complex.mul_re]

/-- The skirt model-sum floor with the concrete kernel-mass weights:
if the negative part of the weighted Ramanujan sums is at most `εn`, then the
whole skirt model sum is at least `-εn`. -/
lemma model_sum_floor_deltaJ (s : Finset ℕ) (n : ℕ) (ε : ℝ)
    (hq : ∀ q ∈ s, 0 < q) (hsq : ∀ q ∈ s, Squarefree q)
    (hbound : ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2) ≤ ε * (n : ℝ)) :
    ∑ q ∈ s, (csum q n).re * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≥ -(ε * (n : ℝ)) :=
  model_sum_floor_of_neg_bound s n ε (fun q => deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
    hq hsq (fun q _ => div_nonneg (deltaJ_nonneg n q)
      (sq_nonneg ((Nat.totient q : ℕ) : ℝ))) hbound

/-- The negative part of the skirt mass is bounded termwise by the decay bound
`ΔJ(q) ≤ qn/(2Q)`, turning the analytic condition into a purely arithmetic sum. -/
lemma skirt_negMass_le_decay (s : Finset ℕ) (n : ℕ)
    (hq : ∀ q ∈ s, 0 < q) (hn : 0 < n)
    (hr : ∀ q ∈ s, (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2) :
    ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ ∑ q ∈ s, ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * ((q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
  have hl : 0 < Nat.log 2 (n+2) := Nat.log_pos (by norm_num) (by omega)
  have hQ0 : 0 < (Qf n:ℝ) := by
    unfold Qf
    rw [pow_two]
    exact_mod_cast Nat.mul_pos hl hl
  have hnonneg : ∀ q ∈ s, 0 ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
        * ((q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
    intro q hq'
    have hq0 : 0 < q := hq q hq'
    exact mul_nonneg (by positivity : 0 ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ))
      (div_nonneg (div_nonneg (mul_nonneg (by exact_mod_cast hq0.le) (by exact_mod_cast hn.le))
        (mul_nonneg zero_le_two hQ0.le))
        (by positivity : 0 ≤ ((Nat.totient q : ℕ) : ℝ) ^ 2))
  refine (Finset.sum_le_sum fun q hq' => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun q => (csum q n).re < 0) s)
      (fun i hi _ => hnonneg i hi))
  have hq0 : 0 < q := hq q ((Finset.mem_filter.mp hq').1)
  have hrq := hr q ((Finset.mem_filter.mp hq').1)
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (deltaJ_le_decay n q hn hq0 hrq)
      (by positivity : 0 ≤ ((Nat.totient q : ℕ) : ℝ) ^ 2))
    (by positivity : 0 ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ))

/-- The filtered arithmetic reduction: the negative part of the skirt mass is
bounded by the decay bound applied **on the negative set only**.  Unlike the
unfiltered `skirt_negMass_le_decay`, this hypothesis stays true for primorial
`n` (where the positive `q ∣ n` terms make the full sum linear in `Q₁`). -/
lemma skirt_negMass_le_decay_filtered (s : Finset ℕ) (n : ℕ)
    (hq : ∀ q ∈ s, 0 < q) (hn : 0 < n)
    (hr : ∀ q ∈ s, (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2) :
    ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * ((q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
  refine Finset.sum_le_sum fun q hq' => ?_
  have hq0 : 0 < q := hq q ((Finset.mem_filter.mp hq').1)
  have hrq := hr q ((Finset.mem_filter.mp hq').1)
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (deltaJ_le_decay n q hn hq0 hrq)
      (by positivity : 0 ≤ ((Nat.totient q : ℕ) : ℝ) ^ 2))
    (by positivity : 0 ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ))

/-- The sharp conditional skirt floor: if the **negative-set** arithmetic sum
`Σ_{q∈s, c_q(n)<0} φ((q,n))·qn/(2Q·φ(q)²)` is at most `εn`, then the skirt
model sum is at least `−εn`.  This is the primorial-compatible interface. -/
lemma model_sum_floor_of_neg_arith_bound (s : Finset ℕ) (n : ℕ) (ε : ℝ)
    (hq : ∀ q ∈ s, 0 < q) (hsq : ∀ q ∈ s, Squarefree q) (hn : 0 < n)
    (hr : ∀ q ∈ s, (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2)
    (hbound : ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * ((q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ ε * (n : ℝ)) :
    ∑ q ∈ s, (csum q n).re * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≥ -(ε * (n : ℝ)) :=
  model_sum_floor_deltaJ s n ε hq hsq
    ((skirt_negMass_le_decay_filtered s n hq hn hr).trans hbound)

/-! ### Uniform T₁-type estimates for the inner band

For the inner band the moduli are small (`q ≤ Q₁(n) ≈ n^{1/3}`), so the whole
band can be taken as `s = Finset.Icc 1 (Q1f n)`.  On this band every modulus is
squarefree, and `Re c_q(n) = μ(q/(q,n))·φ((q,n))`.  For the *model* sum the
decisive point is the cancellation of the Möbius factor over the band: the main
term `Σ_{q≤Q₁} μ(q)·φ(q)·ΔJ(q)/φ(q)²` is controlled by the absolutely convergent
`1/φ²` weight (bounded by the tail lemma below), while the correction is
supported where a prime of `q` divides `n`.

The uniform estimate below isolates the arithmetic core: the signed sum over the
band is bounded by the **absolutely convergent** `1/φ²` weight times the uniform
`ΔJ` cap.  The remaining analytic step — replacing `ΔJ(q)` by its uniform bounds
and taking `n → ∞` — is the `o(1)` conclusion of the T₁ programme.
-/

/-- Band split of the Ramanujan real part on the inner band: the signed weight
`Re c_q(n)/φ(q)²` is bounded in absolute value by `1/φ((q,n))·(1/φ(q) + ...)`;
concretely `|Re c_q(n)| ≤ φ((q,n))` (since `|μ| ≤ 1`), and for squarefree `q`
with `(q,n) = 1` it is exactly `|μ(q)| = 1`. -/
lemma abs_csum_re_le_totient_gcd (q n : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    |(csum q n).re| ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) := by
  have hgsq : Squarefree (q / Nat.gcd q n) :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q n)) hsq
  have hunit : |((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℝ)| = 1 := by
    have h := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hgsq
    exact_mod_cast h
  have habs : |(csum q n).re|
      = |((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ) : ℝ)|
        * ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) := by
    rw [csum_re_eq q n hq hsq, abs_mul]
    congr 1
    exact abs_of_nonneg (Nat.cast_nonneg (Nat.totient (Nat.gcd q n)))
  rw [habs, hunit, one_mul]

/-- The negative part of the skirt mass is at most `(n+1)` times the purely
arithmetic sum `Σ_{q∈s} φ((q,n))/φ(q)²` (card bound `ΔJ(q) ≤ n+1`).  For the
floor it suffices that the filtered version of this arithmetic sum be `o(1)`. -/
lemma skirt_negMass_le_card (s : Finset ℕ) (n : ℕ)
    (hq : ∀ q ∈ s, 0 < q) (hn : 0 < n)
    (hr : ∀ q ∈ s, (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2) :
    ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ (n + 1 : ℝ)
        * ∑ q ∈ s, ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
            / ((Nat.totient q : ℕ) : ℝ) ^ 2 := by
  have hstep1 : ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
      ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
        * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
      (n + 1 : ℝ) * (((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
        / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
    refine Finset.sum_le_sum fun q hq' => ?_
    have hq0 : 0 < q := hq q ((Finset.mem_filter.mp hq').1)
    have hrq := hr q ((Finset.mem_filter.mp hq').1)
    have hA : deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2
        ≤ (n + 1 : ℝ) / ((Nat.totient q : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (deltaJ_le_card n q hn hq0 hrq)
        (by positivity : 0 ≤ ((Nat.totient q : ℕ) : ℝ) ^ 2)
    calc ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
        ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * ((n + 1 : ℝ) / ((Nat.totient q : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ))
      _ = (n + 1 : ℝ) * (((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
        rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc']
  have hstep2 : (n + 1 : ℝ) * ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
      (((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ (n + 1 : ℝ) * ∑ q ∈ s, (((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
        / ((Nat.totient q : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun q => (csum q n).re < 0) s)
        (fun i hi _ => div_nonneg (by positivity : 0 ≤ ((Nat.totient (Nat.gcd i n) : ℕ) : ℝ))
          (by positivity : 0 ≤ ((Nat.totient i : ℕ) : ℝ) ^ 2)))
      (by positivity : 0 ≤ (n + 1 : ℝ))
  have hstep3 : ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
      (n + 1 : ℝ) * (((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
        / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≤ (n + 1 : ℝ) * ∑ q ∈ s.filter (fun q => (csum q n).re < 0),
        (((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) / ((Nat.totient q : ℕ) : ℝ) ^ 2) :=
    (Finset.mul_sum (s.filter (fun q => (csum q n).re < 0))
      (fun q => ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ) / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      (n + 1 : ℝ)).symm.le
  exact hstep1.trans (hstep3.trans hstep2)

/-- End-to-end conditional skirt floor: a purely arithmetic bound on the
negative-part sum implies the model-sum floor. -/
lemma model_sum_floor_of_arith_bound (s : Finset ℕ) (n : ℕ) (ε : ℝ)
    (hq : ∀ q ∈ s, 0 < q) (hsq : ∀ q ∈ s, Squarefree q) (hn : 0 < n)
    (hr : ∀ q ∈ s, (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)) ≤ 1/2)
    (hbound : ∑ q ∈ s, ((Nat.totient (Nat.gcd q n) : ℕ) : ℝ)
          * ((q:ℝ)*(n:ℝ)/(2*(Qf n:ℝ)) / ((Nat.totient q : ℕ) : ℝ) ^ 2) ≤ ε * (n : ℝ)) :
    ∑ q ∈ s, (csum q n).re * (deltaJ n q / ((Nat.totient q : ℕ) : ℝ) ^ 2)
      ≥ -(ε * (n : ℝ)) :=
  model_sum_floor_deltaJ s n ε hq hsq ((skirt_negMass_le_decay s n hq hn hr).trans hbound)

/-- Pointwise equality of the squared kernel modulus with the signed integrand:
`|K_n(β)|² = K_n(β)²·e(-nβ) = (sin π(n+1)β / sin πβ)²`.  Hence the skirt mass
`deltaJ` is exactly the integral of the signed model integrand off the integers. -/
lemma kernel_norm_sq_eq_sin (n : ℕ) (β : ℝ) (hβ : Real.sin (Real.pi * β) ≠ 0) :
    ‖GoldbachExplicitModeledMajor.kernel n β‖ ^ 2
      = (Real.sin (Real.pi * ((n:ℝ) + 1) * β) / Real.sin (Real.pi * β)) ^ 2 := by
  have h1 := kernel_sq_phase_sin n β hβ
  have hphase : ‖GoldbachExplicitModeledMajor.phase (-(n:ℝ) * β)‖ = 1 := by
    rw [phase_eq_GE]
    exact norm_GE (-(n:ℝ) * β)
  have h2 : ‖GoldbachExplicitModeledMajor.kernel n β‖ ^ 2
      = ‖GoldbachExplicitModeledMajor.kernel n β ^ 2
          * GoldbachExplicitModeledMajor.phase (-(n:ℝ) * β)‖ := by
    rw [norm_mul, norm_pow, hphase, mul_one]
  rw [h2, h1, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow (Real.sin
    (Real.pi * ((n:ℝ) + 1) * β) / Real.sin (Real.pi * β)) 2, abs_eq_self.mpr (sq_nonneg _)]

/-- Real divisor form: `Re c_q(n) = ∑_{d | (q,n)} d · μ(q/d)` as a real sum. -/
lemma csum_re_divisor_real (q n : ℕ) (hq : 0 < q) :
    (csum q n).re
      = ∑ d ∈ Nat.divisors (Nat.gcd q n),
          ((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ) * ((d : ℕ) : ℝ) := by
  rw [csum_eq_intCast q n hq, Complex.intCast_re]
  push_cast
  rfl

/-- Divisor swap for the signed `T₁` sum: for any finite family of moduli `s`,
`∑_{q∈s} Re c_q(n)/φ(q)²` rearranges into `∑_{d∣n} d · ∑_{q∈s, d∣q} μ(q/d)/φ(q)²`.
This is the basis for uniform signed bounds: the inner Möbius sums cancel. -/
lemma t1_divisor_swap (s : Finset ℕ) (n : ℕ) (hn : 0 < n) (hs : ∀ q ∈ s, 0 < q) :
    ∑ q ∈ s, (csum q n).re / ((Nat.totient q : ℕ) : ℝ) ^ 2
      = ∑ d ∈ Nat.divisors n, ((d : ℕ) : ℝ) * ∑ q ∈ s.filter (fun q => d ∣ q),
          ((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ) / ((Nat.totient q : ℕ) : ℝ) ^ 2 := by
  classical
  have key : ∀ q ∈ s, (csum q n).re / ((Nat.totient q : ℕ) : ℝ) ^ 2
      = ∑ d ∈ (Nat.divisors n).filter (fun d => d ∣ q),
          ((d : ℕ) : ℝ) * (((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ)
            / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
    intro q hq
    have hq0 : 0 < q := hs q hq
    have hg0 : Nat.gcd q n ≠ 0 := Nat.ne_of_gt (by
      rw [Nat.gcd_comm]; exact Nat.gcd_pos_of_pos_right n hq0)
    have hdiv : Nat.divisors (Nat.gcd q n) = (Nat.divisors n).filter (fun d => d ∣ q) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
      constructor
      · intro h
        exact ⟨⟨Nat.dvd_trans h.1 (Nat.gcd_dvd_right q n), Nat.ne_of_gt hn⟩,
          Nat.dvd_trans h.1 (Nat.gcd_dvd_left q n)⟩
      · intro h
        exact ⟨Nat.dvd_gcd h.2 h.1.1, hg0⟩
    rw [csum_re_divisor_real q n hq0, hdiv, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hswap : ∑ q ∈ s, ∑ d ∈ (Nat.divisors n).filter (fun d => d ∣ q),
      ((d : ℕ) : ℝ) * (((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ)
        / ((Nat.totient q : ℕ) : ℝ) ^ 2)
    = ∑ d ∈ Nat.divisors n, ∑ q ∈ s.filter (fun q => d ∣ q),
        ((d : ℕ) : ℝ) * (((ArithmeticFunction.moebius (q / d) : ℤ) : ℝ)
          / ((Nat.totient q : ℕ) : ℝ) ^ 2) := by
    refine Finset.sum_comm' fun q d => ?_
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
    · intro h
      exact ⟨h.1.1, ⟨h.2, h.1.2⟩⟩
  rw [Finset.sum_congr rfl (fun q hq => key q hq), hswap]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

/-- `16^{ω(k)} ≤ 2^24 · k` for `k > 0`: only six primes lie below 16, and each prime
`p ≥ 16` contributes `16 ≤ p`. -/
lemma sixteen_pow_primeFactors_card_le (k : ℕ) (hk : 0 < k) :
    (16 : ℝ) ^ k.primeFactors.card ≤ 2 ^ 24 * (k : ℝ) := by
  have h6 : (Finset.range 16).filter Nat.Prime = {2, 3, 5, 7, 11, 13} := by decide
  have hcard : ((k.primeFactors).filter (fun p => p < 16)).card ≤ 6 := by
    have hsub : ((k.primeFactors).filter (fun p => p < 16))
        ⊆ (Finset.range 16).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.2, hp.1.1⟩
    calc ((k.primeFactors).filter (fun p => p < 16)).card
        ≤ ((Finset.range 16).filter Nat.Prime).card := Finset.card_le_card hsub
      _ = 6 := by rw [h6]; decide
  have hsplit := Finset.prod_filter_mul_prod_filter_not k.primeFactors (fun p => p < 16)
    (fun _ => (16 : ℝ))
  have hsmall : (∏ p ∈ (k.primeFactors).filter (fun p => p < 16), (16 : ℝ)) ≤ 2 ^ 24 := by
    rw [Finset.prod_const]
    calc (16 : ℝ) ^ ((k.primeFactors).filter (fun p => p < 16)).card
        ≤ (16 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hcard
      _ ≤ (2 : ℝ) ^ 24 := by norm_num
  have hlarge : (∏ p ∈ (k.primeFactors).filter (fun p => ¬(p < 16)), (16 : ℝ)) ≤ (k : ℝ) := by
    have h1 : ((k.primeFactors).filter (fun p => ¬(p < 16))).prod (fun _ => 16)
        ≤ ((k.primeFactors).filter (fun p => ¬(p < 16))).prod (fun p => p) :=
      Finset.prod_le_prod (fun p hp => by
        rw [Finset.mem_filter] at hp
        exact Nat.not_lt.mp hp.2)
    have h2 : ((k.primeFactors).filter (fun p => ¬(p < 16))).prod (fun p => p)
        ≤ k.primeFactors.prod (fun p => p) :=
      Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
        (fun p hp _ => Nat.succ_le_of_lt (Nat.pos_of_mem_primeFactors hp))
    have h3 : k.primeFactors.prod (fun p => p) ≤ k :=
      Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k)
    exact_mod_cast h1.trans (h2.trans h3)
  have hprod : ∏ p ∈ k.primeFactors, (16 : ℝ) = (16 : ℝ) ^ k.primeFactors.card :=
    Finset.prod_const 16
  calc (16 : ℝ) ^ k.primeFactors.card = ∏ p ∈ k.primeFactors, (16 : ℝ) := hprod.symm
    _ = (∏ p ∈ (k.primeFactors).filter (fun p => p < 16), (16 : ℝ))
        * ∏ p ∈ (k.primeFactors).filter (fun p => ¬(p < 16)), (16 : ℝ) := hsplit.symm
    _ ≤ 2 ^ 24 * (k : ℝ) := mul_le_mul hsmall hlarge (by positivity) (by positivity)

/-- `1/φ(k)² ≤ 4096/(√k·k)` for `k > 0`: elementary polynomial tail bound. -/
lemma inv_totient_sq_le (k : ℕ) (hk : 0 < k) :
    1 / ((Nat.totient k : ℕ) : ℝ) ^ 2 ≤ 4096 / (Real.sqrt k * (k : ℝ)) := by
  have hphi : (k : ℝ) / 2 ^ k.primeFactors.card ≤ (Nat.totient k : ℝ) := by
    have hq := Nat.totient_eq_mul_prod_factors k
    simp only [inv_eq_one_div] at hq
    have hfac : ∀ p ∈ k.primeFactors, (1:ℚ)/2 ≤ 1 - 1/(p:ℚ) := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp2 : (2:ℚ) ≤ (p:ℚ) := by exact_mod_cast hp.1.two_le
      have hinv : 1/(p:ℚ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    have hprod : (1:ℚ)/2^k.primeFactors.card ≤ ∏ p ∈ k.primeFactors, (1 - 1/(p:ℚ)) := by
      have heq : ((1:ℚ)/2)^k.primeFactors.card = (1:ℚ)/2^k.primeFactors.card := by
        rw [div_pow, one_pow]
      rw [← heq, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun p _ => by norm_num) fun p hp => hfac p hp
    have hstep : (k:ℚ) * ((1:ℚ)/2^k.primeFactors.card) ≤ (Nat.totient k : ℚ) := by
      calc (k:ℚ) * ((1:ℚ)/2^k.primeFactors.card)
          ≤ (k:ℚ) * ∏ p ∈ k.primeFactors, (1 - 1/(p:ℚ)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = ((Nat.totient k : ℕ) : ℚ) := hq.symm
    have h2 := mul_le_mul_of_nonneg_right hstep
      (by positivity : 0 ≤ (2:ℚ) ^ k.primeFactors.card)
    have h3 : (k:ℚ) * ((1:ℚ)/((2:ℚ)^k.primeFactors.card) * ((2:ℚ)^k.primeFactors.card)) = k := by
      field_simp
    have hcast : (k:ℚ) ≤ ((Nat.totient k : ℕ) : ℚ) * ((2:ℚ)^k.primeFactors.card) := by
      rwa [mul_assoc, h3] at h2
    have hRat : ((k:ℚ) : ℝ)
        ≤ ((Nat.totient k : ℕ) : ℚ) * (((2:ℚ)^k.primeFactors.card) : ℝ) := by
      have h0 : (((Nat.totient k : ℕ) : ℚ) * ((2:ℚ)^k.primeFactors.card) : ℝ)
          = ((Nat.totient k : ℕ) : ℝ) * ((2:ℝ)^k.primeFactors.card) := by
        push_cast; ring
      rw [h0]
      exact_mod_cast hcast
    rw [div_le_iff₀ (by positivity : 0 < (2:ℝ) ^ k.primeFactors.card)]
    exact hRat
  have hpow : (4 : ℝ) ^ k.primeFactors.card ≤ 4096 * Real.sqrt k := by
    have hsq : ((4 : ℝ) ^ k.primeFactors.card) ^ 2 ≤ (4096 * Real.sqrt k) ^ 2 := by
      have h1 : ((4 : ℝ) ^ k.primeFactors.card) ^ 2 = (16 : ℝ) ^ k.primeFactors.card := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have h2 : (4096 * Real.sqrt k) ^ 2 = 2 ^ 24 * (k : ℝ) := by
        have h4096 : (4096 : ℝ) ^ 2 = 2 ^ 24 := by norm_num
        rw [mul_pow, h4096, Real.sq_sqrt (by positivity : 0 ≤ (k:ℝ))]
      rw [h1, h2]
      exact sixteen_pow_primeFactors_card_le k hk
    exact (sq_le_sq₀ (pow_nonneg (by norm_num) _) (by positivity)).mp hsq
  have hpos : 0 < (Nat.totient k : ℕ) := Nat.totient_pos.mpr hk
  have hφpos : 0 < (Nat.totient k : ℝ) := by exact_mod_cast hpos
  have hstep : 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2
      ≤ ((4 : ℝ) ^ k.primeFactors.card) / ((k : ℝ) ^ 2) := by
    have h2 : 1 / (Nat.totient k : ℝ) ≤ (2:ℝ)^k.primeFactors.card / (k:ℝ) := by
      have hkle : (k:ℝ) ≤ 2 ^ k.primeFactors.card * (Nat.totient k : ℝ) := by
        have h := hphi
        rwa [div_le_iff₀ (by positivity : 0 < (2:ℝ) ^ k.primeFactors.card), mul_comm] at h
      rw [le_div_iff₀ (by positivity : 0 < (k:ℝ)), mul_comm, mul_one_div, div_le_iff₀ hφpos]
      exact hkle
    have h3 : (1 / (Nat.totient k : ℝ)) ^ 2
        ≤ ((2:ℝ)^k.primeFactors.card / (k:ℝ)) ^ 2 :=
      (sq_le_sq₀ (by positivity : 0 ≤ 1 / (Nat.totient k : ℝ))
        (by positivity : 0 ≤ (2:ℝ)^k.primeFactors.card / (k:ℝ))).mpr h2
    have h4 : ((2:ℝ)^k.primeFactors.card / (k:ℝ)) ^ 2
        = ((4 : ℝ) ^ k.primeFactors.card) / ((k : ℝ) ^ 2) := by
      rw [div_pow, ← pow_mul, mul_comm, pow_mul]
      norm_num
    calc 1 / (Nat.totient k : ℝ) ^ 2 = (1 / (Nat.totient k : ℝ)) ^ 2 := by
          rw [div_pow, one_pow]
      _ ≤ ((2:ℝ)^k.primeFactors.card / (k:ℝ)) ^ 2 := h3
      _ = ((4 : ℝ) ^ k.primeFactors.card) / ((k : ℝ) ^ 2) := h4
  have hfinal : ((4 : ℝ) ^ k.primeFactors.card) / ((k : ℝ) ^ 2)
      ≤ 4096 / (Real.sqrt k * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsqrt : Real.sqrt k * Real.sqrt k = (k : ℝ) := Real.mul_self_sqrt (by positivity : 0 ≤ (k:ℝ))
    calc (4 : ℝ) ^ k.primeFactors.card * (Real.sqrt k * (k:ℝ))
        ≤ 4096 * Real.sqrt k * (Real.sqrt k * (k:ℝ)) :=
          mul_le_mul_of_nonneg_right hpow (mul_nonneg (Real.sqrt_nonneg k) (by positivity : 0 ≤ (k:ℝ)))
      _ = 4096 * ((Real.sqrt k * Real.sqrt k) * (k:ℝ)) := by ring
      _ = 4096 * ((k : ℝ) * (k : ℝ)) := by rw [hsqrt]
      _ = 4096 * (k : ℝ) ^ 2 := by ring
  exact hstep.trans hfinal

/-- Uniform tail: `∑_{M < k ≤ N} 1/φ(k)² ≤ 24576/√M` for `M > 0`.  Elementary
(polynomial decay), no PNT needed. -/
lemma sum_inv_totient_sq_tail (M N : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.Ioc M N, 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2) ≤ 24576 / Real.sqrt M := by
  have hterm : ∀ k : ℕ, 0 < k → 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2
      ≤ 16384 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1)) := by
    intro k hk
    have hkpos : 0 < (k:ℝ) := by positivity
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
    have hsk1 : 0 < Real.sqrt (k + 1) := Real.sqrt_pos.mpr (by positivity : 0 < (k:ℝ) + 1)
    have hk1 : 1 ≤ (k:ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hk)
    have hk2 : (k:ℝ) ≤ (k:ℝ) ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_right hk1 (by positivity : 0 ≤ (k:ℝ))
    have hdiff : (Real.sqrt (k + 1) - Real.sqrt k) * (Real.sqrt (k + 1) + Real.sqrt k) = 1 := by
      rw [sub_mul, mul_add, mul_add,
        Real.mul_self_sqrt (by positivity : 0 ≤ (k:ℝ) + 1),
        Real.mul_self_sqrt (by positivity : 0 ≤ (k:ℝ))]
      ring
    have hsplit : Real.sqrt ((k:ℝ) * ((k:ℝ) + 1)) = Real.sqrt k * Real.sqrt (k + 1) :=
      Real.sqrt_mul (by positivity : 0 ≤ (k:ℝ)) ((k:ℝ) + 1)
    have hkey : Real.sqrt ((k:ℝ) * ((k:ℝ) + 1)) ≤ 3 * (k:ℝ) - 1 := by
      have hb : 0 ≤ 3 * (k:ℝ) - 1 := by linarith
      have hsq : (Real.sqrt ((k:ℝ) * ((k:ℝ) + 1))) ^ 2 ≤ (3 * (k:ℝ) - 1) ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ (k:ℝ) * ((k:ℝ) + 1))]
        nlinarith
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hb).mp hsq
    have hA : Real.sqrt (k + 1) * (Real.sqrt (k + 1) + Real.sqrt k) ≤ 4 * (k:ℝ) := by
      have ht2 : Real.sqrt (k + 1) * Real.sqrt (k + 1) = (k:ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity : 0 ≤ (k:ℝ) + 1)
      have h2 := hkey
      rw [hsplit] at h2
      linarith
    have hts : Real.sqrt (k + 1) - Real.sqrt k = 1 / (Real.sqrt (k + 1) + Real.sqrt k) := by
      rw [eq_div_iff_mul_eq (ne_of_gt (add_pos hsk1 hsk))]
      exact hdiff
    have hB : Real.sqrt (k + 1) ≤ 4 * (k:ℝ) * (Real.sqrt (k + 1) - Real.sqrt k) := by
      have h2 : Real.sqrt (k + 1) ≤ 4 * (k:ℝ) / (Real.sqrt (k + 1) + Real.sqrt k) := by
        rw [le_div_iff₀ (add_pos hsk1 hsk)]
        exact hA
      have h3 : 4 * (k:ℝ) * (Real.sqrt (k + 1) - Real.sqrt k)
          = 4 * (k:ℝ) / (Real.sqrt (k + 1) + Real.sqrt k) := by
        rw [hts, mul_one_div]
      rw [h3]
      exact h2
    have hfrac : 1 / Real.sqrt k - 1 / Real.sqrt (k + 1)
        = (Real.sqrt (k + 1) - Real.sqrt k) / (Real.sqrt k * Real.sqrt (k + 1)) := by
      rw [div_sub_div (1:ℝ) (1:ℝ) (ne_of_gt hsk) (ne_of_gt hsk1)]
      simp only [one_mul, mul_one]
    have hsecond : 1 / (Real.sqrt k * (k:ℝ))
        ≤ 4 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1)) := by
      rw [hfrac, ← mul_div_assoc, div_le_div_iff₀ (mul_pos hsk hkpos) (mul_pos hsk hsk1)]
      have hmul : Real.sqrt k * Real.sqrt (k + 1)
          ≤ 4 * (Real.sqrt (k + 1) - Real.sqrt k) * (Real.sqrt k * (k:ℝ)) := by
        have h := hB
        nlinarith [hsk]
      simpa using hmul
    calc 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2
        ≤ 4096 / (Real.sqrt k * (k:ℝ)) := inv_totient_sq_le k hk
      _ ≤ 16384 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1)) := by
          have h5 : 4096 / (Real.sqrt k * (k:ℝ))
              = 4096 * (1 / (Real.sqrt k * (k:ℝ))) := (mul_one_div _ _).symm
          rw [h5]
          calc 4096 * (1 / (Real.sqrt k * (k:ℝ)))
              ≤ 4096 * (4 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1))) :=
                mul_le_mul_of_nonneg_left hsecond (by norm_num)
            _ = 16384 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1)) := by
                rw [← mul_assoc]
                norm_num
  have hsum : (∑ k ∈ Finset.Ioc M N, 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.Ioc M N, (16384 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1))) :=
    Finset.sum_le_sum fun k hk => hterm k (lt_trans hM (Finset.mem_Ioc.mp hk).1)
  have htele : ∀ j : ℕ, (∑ k ∈ Finset.Ioc M (M + j),
        (1 / Real.sqrt k - 1 / Real.sqrt (k + 1)))
      = 1 / Real.sqrt (M + 1) - 1 / Real.sqrt (M + j + 1) := by
    intro j
    induction j with
    | zero =>
      rw [Nat.add_zero, Finset.Ioc_eq_empty_of_le (Nat.le_refl M), Finset.sum_empty,
        Nat.cast_zero, add_zero]
      linarith
    | succ j ih =>
      have hMN : M ≤ M + j := Nat.le_add_right M j
      have hC : Real.sqrt ((Nat.cast M + Nat.cast (j + 1)) + 1)
          = Real.sqrt (Nat.cast (M + j + 1) + 1) :=
        congrArg Real.sqrt (by push_cast; ring)
      have hMj : (Nat.cast (M + j + 1) : ℝ) = Nat.cast M + Nat.cast j + 1 := by
        push_cast; ring
      rw [show M + (j + 1) = M + j + 1 from by ring, Finset.sum_Ioc_succ_top hMN, ih, hC, hMj]
      linarith
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by positivity : 0 < (M:ℝ))
  rcases Nat.lt_or_ge N (M + 1) with hN | hN
  · have hempty : Finset.Ioc M N = ∅ := Finset.Ioc_eq_empty_of_le (Nat.lt_succ_iff.mp hN)
    rw [hempty, Finset.sum_empty]
    exact div_nonneg (by norm_num) hsM.le
  · have hleM : M ≤ N := Nat.le_trans (Nat.le_succ M) hN
    have htel := htele (N - M)
    rw [Nat.add_sub_cancel' hleM] at htel
    have hNcast : (Nat.cast M + Nat.cast (N - M) : ℝ) = Nat.cast N := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hleM]
    have hstep1 : (∑ k ∈ Finset.Ioc M N, 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2)
        ≤ 16384 * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (N + 1)) := by
      calc (∑ k ∈ Finset.Ioc M N, 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2)
          ≤ ∑ k ∈ Finset.Ioc M N, (16384 * (1 / Real.sqrt k - 1 / Real.sqrt (k + 1))) := hsum
        _ = 16384 * ∑ k ∈ Finset.Ioc M N, (1 / Real.sqrt k - 1 / Real.sqrt (k + 1)) :=
            (Finset.mul_sum _ _ _).symm
        _ = 16384 * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (N + 1)) := by rw [htel, hNcast]
    have hbound : 1 / Real.sqrt (M + 1) - 1 / Real.sqrt (N + 1) ≤ 1 / Real.sqrt (M + 1) := by
      have hposN : 0 ≤ 1 / Real.sqrt (N + 1) :=
        div_nonneg zero_le_one (Real.sqrt_nonneg (N + 1))
      linarith
    have hstep2 : 16384 * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (N + 1))
        ≤ 16384 / Real.sqrt M := by
      have h1 : 16384 * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (N + 1))
          ≤ 16384 * (1 / Real.sqrt (M + 1)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
      have h2 : 16384 * (1 / Real.sqrt (M + 1)) = 16384 / Real.sqrt (M + 1) :=
        mul_one_div _ _
      have h3 : 16384 / Real.sqrt (M + 1) ≤ 16384 / Real.sqrt M := by
        have hsM1 : 0 < Real.sqrt (M + 1) :=
          Real.sqrt_pos.mpr (by positivity : 0 < (M:ℝ) + 1)
        rw [div_le_div_iff₀ hsM1 hsM]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ M)) (by norm_num)
      exact (h1.trans h2.le).trans h3
    calc (∑ k ∈ Finset.Ioc M N, 1 / ((Nat.totient k : ℕ) : ℝ) ^ 2)
        ≤ 16384 * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (N + 1)) := hstep1
      _ ≤ 16384 / Real.sqrt M := hstep2
      _ ≤ 24576 / Real.sqrt M := by
          rw [div_le_div_iff₀ hsM hsM]
          exact mul_le_mul_of_nonneg_right (by norm_num : (16384:ℝ) ≤ 24576)
            (Real.sqrt_nonneg M)




/-! ### Outer-specific structure: set algebra, vacuity threshold, target measurability -/

section OuterCore

/-- Set algebra: the remainder is `wideArcs ∖ (arcs ∪ lowWideArcs)` — the wide arcs
that are neither original major arcs nor low-modulus wide arcs. -/
lemma remainder_eq (n : ℕ) :
    remainderRegion n = wideArcsRegion n \ (arcsRegion n ∪ lowWideArcsRegion n) := by
  unfold remainderRegion lowPartRegion
  ext t
  simp only [Set.mem_diff, Set.mem_union]
  tauto

/-- **Vacuity threshold.** If `Q₁(n) ≤ Q(n)` then `wideArcs ⊆ lowWideArcs` (same radius
`H/(qn)`, fewer moduli), so the remainder — and hence also `remainder ∖ inner` — is
empty. This holds for every `n ≲ 6.2·10⁸`, where the medium-modulus regime has not
started; the floor is trivial there. -/
lemma remainder_eq_empty (n : ℕ) (h : Q1f n ≤ Qf n) : remainderRegion n = ∅ := by
  have hw : wideArcsRegion n ⊆ lowWideArcsRegion n := by
    intro t ht
    unfold wideArcsRegion at ht
    obtain ⟨q, a, hq1, hq2, ha, hcop, hrad⟩ := ht
    unfold lowWideArcsRegion
    exact ⟨q, a, hq1, le_trans hq2 h, ha, hcop, hrad⟩
  have hsub : wideArcsRegion n \ (arcsRegion n ∪ lowWideArcsRegion n) ⊆ ∅ := by
    intro t ht
    have h2 : t ∉ lowWideArcsRegion n := fun hmem => ht.2 (Or.inr hmem)
    exact h2 (hw ht.1)
  rw [remainder_eq]
  exact Set.subset_empty_iff.mp hsub

lemma JG_empty (n : ℕ) : JG n ∅ = 0 := by
  unfold JG
  have h0 : (fun t => (∅ : Set ℝ).indicator (fG n) t) = fun _ => (0 : ℂ) := by
    funext t
    simp
  rw [h0, intervalIntegral.integral_zero, Complex.zero_re]

/-- The frozen floor holds trivially whenever the remainder is empty. -/
lemma floor_trivial_of_Q1_le_Q (n : ℕ) (h : Q1f n ≤ Qf n) {ε : ℝ} (hε : 0 < ε) :
    -(ε * n) ≤ JG n (remainderRegion n \ innerRegion n) := by
  have hE : remainderRegion n \ innerRegion n = ∅ := by
    rw [remainder_eq_empty n h, Set.empty_sdiff]
  rw [hE, JG_empty]
  have hn : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg n)
  linarith

lemma measurableSet_outerTarget (n : ℕ) :
    MeasurableSet (remainderRegion n \ innerRegion n) :=
  (measurableSet_remainderRegion n).diff (measurableSet_innerRegion n)

end OuterCore

theorem WideRemainderOuterFloor : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n \ inner n) := by
  sorry

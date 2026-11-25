import Mathlib

/-!
# L-goldbach-reflection-phase

The reflection phase identity: substituting `k ↦ n - k` in the generating sum
exhibits the reflected coefficients weighted by the inverted phase. Peeling
the boundary term and shifting the index turns the reflected sum into the
original one scaled by `z ^ n`.
-/

theorem PEqualNP.Outside.L_goldbach_reflection_phase :
    ∀ (n : ℕ) (b : ℕ → ℂ) (z : ℂ), z ≠ 0 → (∑ k ∈ Finset.range (n+1), b (n-k)*z^k) = z^n * ∑ k ∈ Finset.range (n+1), b k*(z⁻¹)^k := by
  intro n
  induction n with
  | zero =>
    intro b z hz
    simp
  | succ n ih =>
    intro b z hz
    rw [Finset.sum_range_succ']
    conv_rhs => rw [Finset.sum_range_succ]
    have hinner : ∑ k ∈ Finset.range (n+1), b (n+1-(k+1)) * z^(k+1) = z * ∑ k ∈ Finset.range (n+1), b (n-k) * z^k := by
      have h1 : ∀ k ∈ Finset.range (n+1), b (n+1-(k+1)) * z^(k+1) = z * (b (n-k) * z^k) := by
        intro k _
        have hsk : n + 1 - (k + 1) = n - k := by omega
        rw [hsk, pow_succ z k]
        ring
      rw [Finset.sum_congr rfl h1, Finset.mul_sum]
    rw [hinner, ih b z hz]
    have hzz : z^(n+1) * (z⁻¹)^(n+1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    have hlast : z^(n+1) * (∑ k ∈ Finset.range (n+1), b k * (z⁻¹)^k + b (n+1) * (z⁻¹)^(n+1)) = z^(n+1) * ∑ k ∈ Finset.range (n+1), b k * (z⁻¹)^k + b (n+1) := by
      rw [mul_add]
      congr 1
      rw [show z^(n+1) * (b (n+1) * (z⁻¹)^(n+1)) = b (n+1) * (z^(n+1) * (z⁻¹)^(n+1)) from by ring, hzz, mul_one]
    rw [hlast, pow_succ z n]
    norm_num
    ring

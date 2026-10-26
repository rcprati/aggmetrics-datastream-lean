/-
Copyright (c) 2026 Ronaldo C. Prati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ronaldo C. Prati
-/
import Aggmetrics.DataStreamDelay

/-!
# Variance of the fading estimator under autocorrelation (data-stream paper, Remark "Autocorrelated entries")

For second-order stationary entries `X_k` with variance `v` and autocorrelation `ρ_d`, the variance of
the fading estimator `∑ₖ wₖ(t) Xₖ` is `v ∑ᵢ ∑ⱼ wᵢ wⱼ ρ(|i - j|)` at every `t`, and it converges to
`v (1-α)/(1+α) κ(α)` with `κ(α) = 1 + 2 ∑_{d≥1} α^d ρ_d`.

* `fading_variance_autocorr`: the exact finite-`t` variance, from Mathlib's covariance;
* `covSum_succ`: an exact recursion `D_{t+1} = α² D_t + 2α(1-α) E_t + (1-α)²`;
* `covSum_bound`: `|D_t - V| ≤ max(2, |V|) α^t`, with `V = (1-α)/(1+α) κ(α)`;
* `covSum_tendsto`, `fading_variance_tendsto`: the limit;
* `kappa_iid`, `kappa_ar1`: `κ = 1` for independent entries and `(1+αr)/(1-αr)` for `ρ_d = r^d`.
-/

open Finset ProbabilityTheory MeasureTheory Filter Topology

namespace Aggmetrics.DataStream

/-- `D_t = ∑ᵢ ∑ⱼ wᵢ wⱼ ρ(|i - j|)` with the fading weights of `t` instances. -/
noncomputable def covSum (ρ : ℕ → ℝ) (α : ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ range t, ∑ j ∈ range t,
    fadeWeight α t i * fadeWeight α t j * ρ (Int.natAbs ((i : ℤ) - j))

/-- `E_t = ∑_{d<t} (1-α) α^d ρ(d+1)`. -/
noncomputable def lagSum (ρ : ℕ → ℝ) (α : ℝ) (t : ℕ) : ℝ :=
  ∑ d ∈ range t, (1 - α) * α ^ d * ρ (d + 1)

/-- `E_∞ = ∑_{d≥0} (1-α) α^d ρ(d+1)`. -/
noncomputable def einf (ρ : ℕ → ℝ) (α : ℝ) : ℝ := ∑' d : ℕ, (1 - α) * α ^ d * ρ (d + 1)

/-- `κ(α) = 1 + 2 ∑_{d≥1} α^d ρ_d`. -/
noncomputable def kappaFactor (ρ : ℕ → ℝ) (α : ℝ) : ℝ := 1 + 2 * ∑' d : ℕ, α ^ (d + 1) * ρ (d + 1)

/-- The limit `V = (1-α)/(1+α) κ(α)`. -/
noncomputable def kappaVar (ρ : ℕ → ℝ) (α : ℝ) : ℝ := (1 - α) / (1 + α) * kappaFactor ρ α

/-! ### Exact variance at every `t` -/

/-- **Variance of the fading estimator with dependent entries**, exact for every `t`. -/
theorem fading_variance_autocorr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (ρ : ℕ → ℝ)
    (hcov : ∀ i j, cov[X i, X j; μ] = v * ρ (Int.natAbs ((i : ℤ) - j))) (α : ℝ) (t : ℕ) :
    Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ] = v * covSum ρ α t := by
  rw [variance_fun_sum' (fun k _ => (hL2 k).const_mul (fadeWeight α t k))]
  unfold covSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  ring

/-! ### The recursion -/

theorem natAbs_sub_of_lt {i t : ℕ} (h : i < t) : Int.natAbs ((i : ℤ) - (t : ℤ)) = t - i := by
  have e : ((i : ℤ) - (t : ℤ)) = -((t - i : ℕ) : ℤ) := by omega
  rw [e]
  simp

theorem natAbs_sub_of_lt' {i t : ℕ} (h : i < t) : Int.natAbs ((t : ℤ) - (i : ℤ)) = t - i := by
  have e : ((t : ℤ) - (i : ℤ)) = ((t - i : ℕ) : ℤ) := by omega
  rw [e]
  simp

/-- Exact recursion for the double sum. -/
theorem covSum_succ (ρ : ℕ → ℝ) (hρ0 : ρ 0 = 1) (α : ℝ) (t : ℕ) :
    covSum ρ α (t + 1)
      = α ^ 2 * covSum ρ α t + 2 * α * (1 - α) * lagSum ρ α t + (1 - α) ^ 2 := by
  have hE : ∑ i ∈ range t, fadeWeight α t i * ρ (t - i) = lagSum ρ α t := by
    unfold lagSum
    have h := Finset.sum_range_reflect (fun d => (1 - α) * α ^ d * ρ (d + 1)) t
    rw [← h]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hit := Finset.mem_range.mp hi
    unfold fadeWeight
    have e : t - i = (t - 1 - i) + 1 := by omega
    rw [e]
  have hI : ∀ i ∈ range t,
      ∑ j ∈ range (t + 1), fadeWeight α (t + 1) i * fadeWeight α (t + 1) j
          * ρ (Int.natAbs ((i : ℤ) - j))
        = α ^ 2 * ∑ j ∈ range t, fadeWeight α t i * fadeWeight α t j * ρ (Int.natAbs ((i : ℤ) - j))
          + α * (1 - α) * (fadeWeight α t i * ρ (t - i)) := by
    intro i hi
    have hit : i < t := Finset.mem_range.mp hi
    rw [Finset.sum_range_succ]
    have h1 : ∀ j ∈ range t, fadeWeight α (t + 1) i * fadeWeight α (t + 1) j
          * ρ (Int.natAbs ((i : ℤ) - j))
        = α ^ 2 * (fadeWeight α t i * fadeWeight α t j * ρ (Int.natAbs ((i : ℤ) - j))) := by
      intro j hj
      rw [fadeWeight_succ hit, fadeWeight_succ (Finset.mem_range.mp hj)]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, fadeWeight_succ hit, fadeWeight_last,
      natAbs_sub_of_lt hit]
    ring
  have hL : ∑ j ∈ range (t + 1), fadeWeight α (t + 1) t * fadeWeight α (t + 1) j
        * ρ (Int.natAbs ((t : ℤ) - j))
      = α * (1 - α) * (∑ j ∈ range t, fadeWeight α t j * ρ (t - j)) + (1 - α) ^ 2 := by
    rw [Finset.sum_range_succ]
    have h1 : ∀ j ∈ range t, fadeWeight α (t + 1) t * fadeWeight α (t + 1) j
          * ρ (Int.natAbs ((t : ℤ) - j))
        = α * (1 - α) * (fadeWeight α t j * ρ (t - j)) := by
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      rw [fadeWeight_last, fadeWeight_succ hjt, natAbs_sub_of_lt' hjt]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, fadeWeight_last]
    simp only [sub_self, Int.natAbs_zero, hρ0, mul_one]
    ring
  unfold covSum
  rw [Finset.sum_range_succ, Finset.sum_congr rfl hI, hL, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hE]
  ring

/-! ### Tails -/

theorem einf_eq (ρ : ℕ → ℝ) (α : ℝ) :
    einf ρ α = (1 - α) * ∑' d : ℕ, α ^ d * ρ (d + 1) := by
  unfold einf
  rw [← tsum_mul_left]
  exact tsum_congr (fun d => by ring)

theorem tsum_shift (ρ : ℕ → ℝ) (α : ℝ) :
    ∑' d : ℕ, α ^ (d + 1) * ρ (d + 1) = α * ∑' d : ℕ, α ^ d * ρ (d + 1) := by
  rw [← tsum_mul_left]
  exact tsum_congr (fun d => by ring)

theorem hasSum_fade_geom {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    HasSum (fun i : ℕ => (1 - α) * α ^ (i + t)) (α ^ t) := by
  have : (fun i : ℕ => (1 - α) * α ^ (i + t)) = fun j => (1 - α) * α ^ (t + j) := by
    funext i
    rw [Nat.add_comm]
  rw [this]
  exact fade_tail_sum h0 h1 t

theorem summable_lag {ρ : ℕ → ℝ} (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Summable (fun d : ℕ => (1 - α) * α ^ d * ρ (d + 1)) := by
  have hg := hasSum_fade_geom h0 h1 0
  have hg' : HasSum (fun d : ℕ => (1 - α) * α ^ d) 1 := by simpa using hg
  have hb : ∀ d : ℕ, ‖(1 - α) * α ^ d * ρ (d + 1)‖ ≤ (1 - α) * α ^ d := fun d => by
    have h2 : 0 ≤ (1 - α) * α ^ d := mul_nonneg (by linarith) (pow_nonneg h0 d)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    exact mul_le_of_le_one_right h2 (hρ (d + 1))
  first
    | exact Summable.of_norm_bounded hg'.summable hb
    | exact Summable.of_norm_bounded _ hg'.summable hb

/-- The tail of the lag sum: `|E_t - E_∞| ≤ α^t`. -/
theorem lag_tail {ρ : ℕ → ℝ} (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    |lagSum ρ α t - einf ρ α| ≤ α ^ t := by
  have hs := summable_lag hρ h0 h1
  have hsplit : (∑ d ∈ range t, (1 - α) * α ^ d * ρ (d + 1))
      + ∑' i : ℕ, (1 - α) * α ^ (i + t) * ρ (i + t + 1)
      = ∑' d : ℕ, (1 - α) * α ^ d * ρ (d + 1) := hs.sum_add_tsum_nat_add t
  have h : lagSum ρ α t - einf ρ α
      = -∑' i : ℕ, (1 - α) * α ^ (i + t) * ρ (i + t + 1) := by
    unfold lagSum einf
    linarith
  rw [h, abs_neg]
  have := tsum_of_norm_bounded (hasSum_fade_geom h0 h1 t)
    (f := fun i : ℕ => (1 - α) * α ^ (i + t) * ρ (i + t + 1)) (fun i => by
      have h2 : 0 ≤ (1 - α) * α ^ (i + t) := mul_nonneg (by linarith) (pow_nonneg h0 _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
      exact mul_le_of_le_one_right h2 (hρ _))
  simpa [Real.norm_eq_abs] using this

/-! ### The bound and the limit -/

theorem covSum_bound {ρ : ℕ → ℝ} (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) (t : ℕ) :
    |covSum ρ α t - kappaVar ρ α| ≤ max 2 |kappaVar ρ α| * α ^ t := by
  have hfix : kappaVar ρ α
      = α ^ 2 * kappaVar ρ α + 2 * α * (1 - α) * einf ρ α + (1 - α) ^ 2 := by
    rw [einf_eq]
    unfold kappaVar kappaFactor
    rw [tsum_shift]
    have : (1 + α) ≠ 0 := by linarith
    field_simp
    ring
  have hM2 : (2 : ℝ) ≤ max 2 |kappaVar ρ α| := le_max_left _ _
  induction t with
  | zero =>
    simp only [covSum, Finset.range_zero, Finset.sum_empty, zero_sub, abs_neg, pow_zero, mul_one]
    exact le_max_right _ _
  | succ t ih =>
    have hrec := covSum_succ ρ hρ0 α t
    have hE := lag_tail hρ h0 h1 t
    have hdiff : covSum ρ α (t + 1) - kappaVar ρ α
        = α ^ 2 * (covSum ρ α t - kappaVar ρ α)
          + 2 * α * (1 - α) * (lagSum ρ α t - einf ρ α) := by
      rw [hrec]
      linear_combination (-1 : ℝ) * hfix
    rw [hdiff]
    have hαt : 0 ≤ α ^ t := pow_nonneg h0 t
    have hc : 0 ≤ 2 * α * (1 - α) := by
      have : 0 ≤ 1 - α := by linarith
      positivity
    calc |α ^ 2 * (covSum ρ α t - kappaVar ρ α) + 2 * α * (1 - α) * (lagSum ρ α t - einf ρ α)|
        ≤ |α ^ 2 * (covSum ρ α t - kappaVar ρ α)|
          + |2 * α * (1 - α) * (lagSum ρ α t - einf ρ α)| := by
          first | exact abs_add_le _ _ | exact abs_add _ _
      _ = α ^ 2 * |covSum ρ α t - kappaVar ρ α|
          + 2 * α * (1 - α) * |lagSum ρ α t - einf ρ α| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2), abs_of_nonneg hc]
      _ ≤ α ^ 2 * (max 2 |kappaVar ρ α| * α ^ t) + 2 * α * (1 - α) * α ^ t :=
        add_le_add (mul_le_mul_of_nonneg_left ih (by positivity))
          (mul_le_mul_of_nonneg_left hE hc)
      _ ≤ max 2 |kappaVar ρ α| * α ^ (t + 1) := by
        have key : ∀ M : ℝ, 2 ≤ M → α ^ 2 * (M * α ^ t) + 2 * α * (1 - α) * α ^ t
            ≤ M * α ^ (t + 1) := by
          intro M hM
          rw [pow_succ α t]
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hαt h0) (by linarith : (0 : ℝ) ≤ 1 - α))
            (by linarith : (0 : ℝ) ≤ M - 2)]
        exact key _ hM2

/-- **The double sum converges to `V = (1-α)/(1+α) κ(α)`.** -/
theorem covSum_tendsto {ρ : ℕ → ℝ} (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) :
    Tendsto (fun t => covSum ρ α t) atTop (𝓝 (kappaVar ρ α)) := by
  have hpow : Tendsto (fun t : ℕ => max 2 |kappaVar ρ α| * α ^ t) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul (max 2 |kappaVar ρ α|)
  have h : Tendsto (fun t => covSum ρ α t - kappaVar ρ α) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => by
      rw [Real.norm_eq_abs]
      exact covSum_bound hρ0 hρ h0 h1 t) hpow
  exact tendsto_sub_nhds_zero_iff.mp h

/-- **Variance of the fading estimator with dependent entries**: the limit is
`v (1-α)/(1+α) κ(α)`, that is, the effective sample size is divided by `κ(α)`. -/
theorem fading_variance_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (ρ : ℕ → ℝ)
    (hcov : ∀ i j, cov[X i, X j; μ] = v * ρ (Int.natAbs ((i : ℤ) - j)))
    (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Tendsto (fun t => Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ]) atTop
      (𝓝 (v * kappaVar ρ α)) := by
  have := (covSum_tendsto hρ0 hρ h0 h1).const_mul v
  refine this.congr (fun t => ?_)
  rw [fading_variance_autocorr μ X hL2 v ρ hcov α t]

/-! ### Two cases -/

/-- Independent entries: `κ = 1`, and the limit is the `(1-α)/(1+α) v` of the paper. -/
theorem kappa_iid (α : ℝ) :
    kappaVar (fun d => if d = 0 then 1 else 0) α = (1 - α) / (1 + α) := by
  unfold kappaVar kappaFactor
  simp

/-- `AR(1)` autocorrelation `ρ_d = r^d`: `κ = (1 + αr)/(1 - αr)`. -/
theorem kappa_ar1 {α r : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hr : |r| < 1) :
    kappaFactor (fun d => r ^ d) α = (1 + α * r) / (1 - α * r) := by
  have habs : |α * r| < 1 := by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg r]
  have hne : 1 - α * r ≠ 0 := by
    have := (abs_lt.mp habs).2
    linarith
  unfold kappaFactor
  show 1 + 2 * ∑' d : ℕ, α ^ (d + 1) * r ^ (d + 1) = _
  have h : ∑' d : ℕ, α ^ (d + 1) * r ^ (d + 1) = (α * r) / (1 - α * r) := by
    have e : ∀ d : ℕ, α ^ (d + 1) * r ^ (d + 1) = (α * r) * (α * r) ^ d := fun d => by
      rw [← mul_pow, pow_succ]
      ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one habs, ← div_eq_mul_inv]
  rw [h]
  field_simp
  ring

end Aggmetrics.DataStream

import Aggmetrics.DataStream
import Aggmetrics.DataStreamDelay

/-!
# Prior-invariance with integrals, the variance of the fading estimator, the Jacobians and the
# drift profiles (data-stream paper, Sections 3 and 5)

Formalized here, on top of `Aggmetrics.DataStream` and `Aggmetrics.DataStreamDelay`:

* **D1** the canonical coordinates as integrals of the decision function against the
  class-conditional laws, free of the prior (`recall_integral`, `specificity_integral`), and the
  dependence of the precision on the prior (`precision_depends_on_prior`);
* **D2** the expectation and the variance of the fading estimator at every `t`, from independence
  (`fading_expectation`, `fading_variance`, `fadeWeight_sq_sum`);
* **D3** the closed-form Jacobians of the precision and of `F₁` in `(R₁₁, R₀₀, π)`
  (`precision_dR` and its five siblings) and of the accuracy, and the exactness of the mid-point
  rule for the accuracy (`accuracy_midpoint_exact`);
* **D4** the drift profiles: the state after an abrupt drift (`abrupt_state`), its half-life
  (`half_life`), the tracking lag under a steady velocity (`tracking_lag`, `tracking_lag_tendsto`)
  and the damping of a transient outlier (`outlier_response`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory Filter

namespace Aggmetrics.DataStream

/-! ### D1. The canonical coordinates as integrals -/

/-- **Recall is free of the prior.** The expected cell masses of the positive class are
`π ∫ f dP₁` and `π ∫ (1 - f) dP₁`; their ratio is `∫ f dP₁` for every `π ≠ 0`. -/
theorem recall_integral {X : Type*} [MeasurableSpace X] (P1 : Measure X) [IsProbabilityMeasure P1]
    (f : X → ℝ) (hf : Integrable f P1) (π : ℝ) (hπ : π ≠ 0) :
    (π * ∫ x, f x ∂P1) / (π * ∫ x, f x ∂P1 + π * ∫ x, (1 - f x) ∂P1) = ∫ x, f x ∂P1 := by
  have h : ∫ x, (1 - f x) ∂P1 = 1 - ∫ x, f x ∂P1 := by
    rw [integral_sub (integrable_const 1) hf]
    simp
  rw [h]
  exact cell_ratio_prior_invariant π _ hπ

/-- **Specificity is free of the prior.** -/
theorem specificity_integral {X : Type*} [MeasurableSpace X] (P0 : Measure X)
    [IsProbabilityMeasure P0] (f : X → ℝ) (hf : Integrable f P0) (π : ℝ) (hπ : π ≠ 1) :
    ((1 - π) * ∫ x, (1 - f x) ∂P0)
        / ((1 - π) * ∫ x, (1 - f x) ∂P0 + (1 - π) * ∫ x, f x ∂P0) = ∫ x, (1 - f x) ∂P0 := by
  have h : ∫ x, f x ∂P0 = 1 - ∫ x, (1 - f x) ∂P0 := by
    rw [integral_sub (integrable_const 1) hf]
    simp
  rw [h]
  exact cell_ratio_prior_invariant (1 - π) _ (sub_ne_zero.mpr (Ne.symm hπ))

/-- Precision as a function of the canonical coordinates and the prior. -/
noncomputable def precision (R S π : ℝ) : ℝ := π * R / (π * R + (1 - π) * (1 - S))

/-- Unlike the canonical coordinates, the precision depends on the prior: with
`R₁₁ = R₀₀ = 0.85`, it is `0.85` at `π = 1/2` and `17/74` at `π = 1/20`. -/
theorem precision_depends_on_prior :
    precision (17 / 20) (17 / 20) (1 / 2) = 17 / 20 ∧
    precision (17 / 20) (17 / 20) (1 / 20) = 17 / 74 ∧
    precision (17 / 20) (17 / 20) (1 / 2) ≠ precision (17 / 20) (17 / 20) (1 / 20) := by
  unfold precision
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### D2. Expectation and variance of the fading estimator -/

theorem fadeWeight_sq_sum {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    ∑ k ∈ range t, (fadeWeight α t k) ^ 2 = (1 - α) / (1 + α) * (1 - α ^ (2 * t)) := by
  unfold fadeWeight
  have h := Finset.sum_range_reflect (fun j => ((1 - α) * α ^ j) ^ 2) t
  rw [h]
  have hgeo := geom_sum_mul_neg (α ^ 2) t
  have hne : (1 - α ^ 2) ≠ 0 := by nlinarith
  have hs : ∑ j ∈ range t, ((1 - α) * α ^ j) ^ 2 = (1 - α) ^ 2 * ∑ j ∈ range t, (α ^ 2) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hs, eq_div_of_mul_eq hne hgeo]
  have hα2 : (α ^ 2) ^ t = α ^ (2 * t) := by rw [← pow_mul]
  rw [hα2]
  have h1a : (1 - α) ≠ 0 := by linarith
  have h1b : (1 + α) ≠ 0 := by linarith
  have h1c : (1 - α ^ 2) = (1 - α) * (1 + α) := by ring
  rw [h1c]
  field_simp

/-- **Expectation of the fading estimator**, `E[C_α(t)] = (1 - α^t) C_pop`, for any `t`. -/
theorem fading_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : ∀ k, Integrable (X k) μ) (c : ℝ)
    (hmean : ∀ k, ∫ ω, X k ω ∂μ = c) (α : ℝ) (t : ℕ) :
    ∫ ω, ∑ k ∈ range t, fadeWeight α t k * X k ω ∂μ = (1 - α ^ t) * c := by
  rw [integral_finsetSum _ (fun k _ => (hint k).const_mul _)]
  simp_rw [integral_const_mul, hmean]
  rw [← Finset.sum_mul, fadeWeight_sum]

/-- **Variance of the fading estimator** for independent entries with variance `v`:
`Var(C_α(t)) = (1-α)/(1+α) (1 - α^{2t}) v`, for any `t`. -/
theorem fading_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (hvar : ∀ k, Var[X k; μ] = v)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ]
      = (1 - α) / (1 + α) * (1 - α ^ (2 * t)) * v := by
  have hsum : (fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω)
      = ∑ k ∈ range t, (fun ω => fadeWeight α t k * X k ω) := by
    ext ω
    simp [Finset.sum_apply]
  have hcomp : iIndepFun (fun k => (fun x : ℝ => fadeWeight α t k * x) ∘ X k) μ :=
    hX.comp (fun k x => fadeWeight α t k * x) (fun k => measurable_const.mul measurable_id)
  rw [hsum, IndepFun.variance_sum (fun k _ => (hL2 k).const_mul (fadeWeight α t k))
    (fun i _ j _ hij => hcomp.indepFun hij)]
  have hk : ∀ k ∈ range t, Var[fun ω => fadeWeight α t k * X k ω; μ]
      = (fadeWeight α t k) ^ 2 * v := fun k _ => by
    rw [variance_const_mul, hvar k]
  rw [Finset.sum_congr rfl hk, ← Finset.sum_mul, fadeWeight_sq_sum h0 h1]

/-! ### D3. Closed-form Jacobians -/

/-- `F₁` as a function of the canonical coordinates and the prior. -/
noncomputable def f1 (R S π : ℝ) : ℝ := 2 * π * R / (π * (1 + R) + (1 - π) * (1 - S))

/-- Accuracy as a function of the canonical coordinates and the prior. -/
def accuracy (R S π : ℝ) : ℝ := π * R + (1 - π) * S

theorem hasDerivAt_ratio_lin (a b c d x D : ℝ) (hD : c * x + d = D) (hD0 : D ≠ 0) :
    HasDerivAt (fun y => (a * y + b) / (c * y + d)) ((a * D - (a * x + b) * c) / D ^ 2) x := by
  subst hD
  have hlin : ∀ a b : ℝ, HasDerivAt (fun y => a * y + b) a x := fun a b => by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  exact (hlin a b).div (hlin c d) hD0

/-- `∂ Precision / ∂R₁₁ = π(1-π)(1-R₀₀) / D²`. -/
theorem precision_dR (R S π : ℝ) (hD : π * R + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => precision y S π)
      (π * (1 - π) * (1 - S) / (π * R + (1 - π) * (1 - S)) ^ 2) R := by
  have h := hasDerivAt_ratio_lin π 0 π ((1 - π) * (1 - S)) R (π * R + (1 - π) * (1 - S))
    (by ring) hD
  convert h using 1
  · funext y
    unfold precision
    ring
  · field_simp
    ring

/-- `∂ Precision / ∂R₀₀ = π(1-π)R₁₁ / D²`. -/
theorem precision_dS (R S π : ℝ) (hD : π * R + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => precision R y π)
      (π * (1 - π) * R / (π * R + (1 - π) * (1 - S)) ^ 2) S := by
  have h := hasDerivAt_ratio_lin 0 (π * R) (-(1 - π)) (π * R + (1 - π)) S
    (π * R + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold precision
    ring
  · field_simp
    ring

/-- `∂ Precision / ∂π = R₁₁(1-R₀₀) / D²`. -/
theorem precision_dπ (R S π : ℝ) (hD : π * R + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => precision R S y)
      (R * (1 - S) / (π * R + (1 - π) * (1 - S)) ^ 2) π := by
  have h := hasDerivAt_ratio_lin R 0 (R - (1 - S)) (1 - S) π (π * R + (1 - π) * (1 - S))
    (by ring) hD
  convert h using 1
  · funext y
    unfold precision
    ring
  · field_simp
    ring

/-- `∂ F₁ / ∂R₁₁ = 2π[π + (1-π)(1-R₀₀)] / D²`. -/
theorem f1_dR (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 y S π)
      (2 * π * (π + (1 - π) * (1 - S)) / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) R := by
  have h := hasDerivAt_ratio_lin (2 * π) 0 π (π + (1 - π) * (1 - S)) R
    (π * (1 + R) + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold f1
    ring
  · field_simp
    ring

/-- `∂ F₁ / ∂R₀₀ = 2π(1-π)R₁₁ / D²`. -/
theorem f1_dS (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 R y π)
      (2 * π * (1 - π) * R / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) S := by
  have h := hasDerivAt_ratio_lin 0 (2 * π * R) (-(1 - π)) (π * (1 + R) + (1 - π)) S
    (π * (1 + R) + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold f1
    ring
  · field_simp
    ring

/-- `∂ F₁ / ∂π = 2R₁₁(1-R₀₀) / D²`. -/
theorem f1_dπ (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 R S y)
      (2 * R * (1 - S) / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) π := by
  have h := hasDerivAt_ratio_lin (2 * R) 0 (R + S) (1 - S) π
    (π * (1 + R) + (1 - π) * (1 - S)) (by ring) hD
  convert h using 1
  · funext y
    unfold f1
    ring
  · field_simp
    ring

/-- The partials of the accuracy: `π`, `1 - π` and `R₁₁ - R₀₀`. -/
theorem accuracy_partials (R S π : ℝ) :
    HasDerivAt (fun y => accuracy y S π) π R ∧ HasDerivAt (fun y => accuracy R y π) (1 - π) S ∧
      HasDerivAt (fun y => accuracy R S y) (R - S) π := by
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_id R).const_mul π).add_const ((1 - π) * S)
    convert h using 1
    · simp [accuracy]
    · simp
  · have h := ((hasDerivAt_id S).const_mul (1 - π)).const_add (π * R)
    convert h using 1
    · funext y
      simp [accuracy]
    · simp
  · have h1 := ((hasDerivAt_id π).mul_const R)
    have h2 := (((hasDerivAt_id π).const_sub 1).mul_const S)
    have h := h1.add h2
    convert h using 1
    · funext y
      simp [accuracy]
    · simp
      ring

/-- The mid-point rule is exact for the accuracy, which is bilinear in `(R, π)`:
`ΔM = π̄ ΔR₁₁ + (1 - π̄) ΔR₀₀ + (R̄₁₁ - R̄₀₀) Δπ`. -/
theorem accuracy_midpoint_exact (R0 S0 π0 R1 S1 π1 : ℝ) :
    accuracy R1 S1 π1 - accuracy R0 S0 π0
      = ((π0 + π1) / 2) * (R1 - R0) + (1 - (π0 + π1) / 2) * (S1 - S0)
        + ((R0 + R1) / 2 - (S0 + S1) / 2) * (π1 - π0) := by
  unfold accuracy
  ring

/-! ### D4. The drift profiles -/

/-- **Abrupt drift.** If the expected instance matrix is `B` from step `n₀` on, the fading state
moves from `C(n₀)` to `B` as `C(n₀ + s) = α^s C(n₀) + (1 - α^s) B`. -/
theorem abrupt_state {V : Type*} [AddCommGroup V] [Module ℝ V] (α : ℝ) (B : V) (c : ℕ → V)
    (hc : ∀ n, c (n + 1) = α • c n + (1 - α) • B) (n0 s : ℕ) :
    c (n0 + s) = α ^ s • c n0 + (1 - α ^ s) • B := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← add_assoc, hc, ih]
    module

/-- **Half-life.** After `s ≥ ln 2 / ln(1/α)` steps the weight of the old concept is at most
one half. -/
theorem half_life (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (s : ℕ)
    (hs : (s : ℝ) ≥ Real.log 2 / (-Real.log α)) : α ^ s ≤ 1 / 2 := by
  have e : Real.log (1 / (1 / 2 : ℝ)) / (-Real.log (1 - (1 - α))) = Real.log 2 / (-Real.log α) := by
    rw [one_div_one_div, sub_sub_cancel]
  have h := window_sizing_rule (1 - α) (1 / 2) (by linarith) (by linarith) (by norm_num) s
    (by rw [e]; exact hs)
  rwa [sub_sub_cancel] at h

/-- **Tracking lag.** For a population that drifts at a steady velocity `d`,
`pop n = a + n d`, and the fading recurrence `c (n+1) = α c n + (1-α) pop (n+1)`, the error is
`c n - pop n = L + α^n (c 0 - pop 0 - L)` with `L = -α d/(1-α)`. -/
theorem tracking_lag (α a d : ℝ) (h1 : α < 1) (c : ℕ → ℝ)
    (hc : ∀ n, c (n + 1) = α * c n + (1 - α) * (a + (n + 1 : ℕ) * d)) (n : ℕ) :
    c n - (a + n * d) = -(α * d) / (1 - α) + α ^ n * (c 0 - a + α * d / (1 - α)) := by
  have h1a : (1 - α) ≠ 0 := by linarith
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [hc n]
    push_cast
    have e : c n = a + n * d - α * d / (1 - α) + α ^ n * (c 0 - a + α * d / (1 - α)) := by
      have := ih
      field_simp at this ⊢
      linarith
    rw [e]
    field_simp
    ring

/-- The tracking lag converges to the constant `-α d / (1 - α)`, `-(n_eff - 1) d`. -/
theorem tracking_lag_tendsto (α a d : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (c : ℕ → ℝ)
    (hc : ∀ n, c (n + 1) = α * c n + (1 - α) * (a + (n + 1 : ℕ) * d)) :
    Tendsto (fun n : ℕ => c n - (a + n * d)) atTop (nhds (-(α * d) / (1 - α))) := by
  have hpow : Tendsto (fun n : ℕ => α ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have h := (hpow.mul_const (c 0 - a + α * d / (1 - α))).const_add (-(α * d) / (1 - α))
  simp only [zero_mul, add_zero] at h
  refine h.congr (fun n => ?_)
  rw [tracking_lag α a d h1 c hc n]

/-- **Transient outlier.** An isolated unit shock at step `n₀` enters the fading state with
amplitude `1 - α` and is damped as `α^k`. -/
theorem outlier_response {V : Type*} [AddCommGroup V] [Module ℝ V] (α : ℝ) (n0 : ℕ) (s : V)
    (c : ℕ → V) (hc : ∀ n, c (n + 1) = α • c n + (1 - α) • (if n = n0 then s else 0))
    (h0 : c n0 = 0) (k : ℕ) :
    c (n0 + 1 + k) = ((1 - α) * α ^ k) • s := by
  induction k with
  | zero =>
    simp only [add_zero]
    rw [hc, h0]
    simp
  | succ k ih =>
    rw [← add_assoc, hc, ih, if_neg (by omega)]
    module

end Aggmetrics.DataStream

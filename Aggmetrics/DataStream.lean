import Aggmetrics.Basic

/-!
# Formalization of results from the data-stream companion paper

`papers/05-data-stream/outline.tex` extends the base framework
(`Aggmetrics.Basic`) to streaming evaluation. Seven results are formalized here. The temporal
part of Theorem 1 (the state `Yᵀ W P`, its commutation with the selection matrices, classes with a
zero denominator), the fading and window recurrences, the exact discrete drift decomposition and the
running example are in `Aggmetrics.DataStreamTemporal` and `Aggmetrics.DataStreamExample`. The
latency part (marginal consistency, bias identity, the invariant of Algorithm 1, the eviction tail,
the zero-division policies) is in `Aggmetrics.DataStreamDelay`. The undefined-window probability
from independence, with latency and under fading, and the multiclass prior-invariance are in
`Aggmetrics.DataStreamProb`. The integrals of the prior-invariance, the variance at every `t`, the
closed-form Jacobians and the drift profiles are in `Aggmetrics.DataStreamDrift`. The table of paper
statements against theorems is `DATASTREAM_COVERAGE.md`. Algorithm 1 with eviction, the exact
effect of eviction on the state and the bound on the queue are in `Aggmetrics.DataStreamEviction`.
The variance of the fading estimator for autocorrelated entries is in `Aggmetrics.DataStreamAutocorr`.

* `temporal_decomposability` — Theorem ("Dynamic Temporal Preservation of Linear
  Decomposability"): the micro-temporal composition of any linear-fractional measure
  equals the denominator-weighted macro-temporal composition, at every timestamp. This is
  the paper's own `⟨a,v⟩/⟨b,v⟩` instantiation of `Aggmetrics.weighted_ratio_mixture`.
* `recall_prior_invariant` / `specificity_prior_invariant` — Proposition ("Strict
  Prior-Invariance of the Canonical Basis"): the canonical recall/specificity coordinates
  carry no functional dependence on the class prior `π(t)`, for *any* evolution of the
  classifier and class-conditional distributions — the algebraic core of the paper's
  measure-theoretic proof, isolated from the integrals themselves.
* `undefined_window_probability` — Proposition ("Undefined-Window Probability Under Stationary
  Arrivals"): the probability that class `j` never arrives in a window of `W` positions is
  `(1-p)^W`. The paper's own justification is one line ("by independence"); the content taken
  directly here as a hypothesis is exactly that one line — the defining
  multiplicativity-over-intersections property of independent events — rather than built up from
  Mathlib's general `iIndepSet` machinery, whose exact API for "independence transfers to
  complements" was judged not worth the added risk for a proposition of this size. What *is*
  proved is the connecting step the paper leaves implicit: converting the arrival probability `p`
  into the non-arrival probability `1-p` via `measure_compl`.
* `window_sizing_rule` — Corollary ("Design rule for the undefined-window rate"): sizing the
  window at `W ≥ log(1/δ)/(-log(1-p))` keeps the undefined-window probability below the target
  tolerance `δ`, a direct log-manipulation consequence of `undefined_window_probability`.
* `expectation_convergence` / `variance_scaling_limit` — Proposition ("Asymptotic Expectation and
  Variance Scaling"): `E[C_α(t)] → C_pop` and `Var([C_α(t)]_{jk}) → (1-α)/(1+α) · [V_inst]_{jk}`
  as `t → ∞`, treating the per-instance variance as a fixed nonnegative real constant under
  stationary `P_0` and the geometric unrolling of the fading recurrence as given, matching the
  paper's own one-line derivation. The paper's further approximation `≈ 1/(2 n_eff)` is only exact
  in the limit `α → 1` (with `n_eff = 1/(1-α)`), so it is deliberately left outside these two
  exact-limit statements.
* `jacobian_decomposition` — Theorem ("Analytical Jacobian Drift Decomposition"): for a composite
  metric `M(t) = g(R11(t), R00(t), π(t))`, the total temporal derivative splits additively into the
  "concept drift" part (partials w.r.t. the canonical coordinates, dotted with their rates of
  change) and the "prior shift" part (the partial w.r.t. `π`, times its rate of change) — the
  general multivariate chain rule, instantiated to `ℝ × ℝ × ℝ`, with the three-way additive split
  falling out of linearity of the Fréchet derivative alone.
-/

open Finset MeasureTheory

namespace Aggmetrics.DataStream

/-- Theorem (Dynamic Temporal Preservation of Linear Decomposability): for a linear-fractional
measure `M(v) = ⟨a,v⟩ / ⟨b,v⟩` with canonical coefficient vectors `a b : Fin 4 → ℝ`, evaluated
on per-class contingency vectors `v j : Fin 4 → ℝ`, the micro-temporal composition equals the
denominator-weighted macro-temporal composition, exactly, at every timestamp. -/
theorem temporal_decomposability {m : ℕ} (hm : 0 < m) (a b : Fin 4 → ℝ) (v : Fin m → Fin 4 → ℝ)
    (hden : ∀ j, 0 < ∑ i, b i * v j i) :
    (∑ j, ∑ i, a i * v j i) / (∑ j, ∑ i, b i * v j i)
      = ∑ j, ((∑ i, b i * v j i) / ∑ l, ∑ i, b i * v l i)
          * ((∑ i, a i * v j i) / (∑ i, b i * v j i)) :=
  weighted_ratio_mixture hm (fun j => ∑ i, a i * v j i) (fun j => ∑ i, b i * v j i) hden

/-- Algebraic core of the prior-invariance proof: if a cell count is `prior * rate` and its
complement is `prior * (1 - rate)`, the ratio of the first to their sum is exactly `rate`,
independently of `prior` — for *any* positive prior, not just in the limit or on average. -/
theorem cell_ratio_prior_invariant (prior rate : ℝ) (hprior : prior ≠ 0) :
    (prior * rate) / (prior * rate + prior * (1 - rate)) = rate := by
  have hsum : prior * rate + prior * (1 - rate) = prior := by ring
  rw [hsum, mul_comm, mul_div_assoc, div_self hprior, mul_one]

/-- Proposition (Strict Prior-Invariance of the Canonical Basis), recall coordinate: with
`A(t) = π(t) * Recall(t)` and `C(t) = π(t) * (1 - Recall(t))` (law of total probability on the
positive class), `A(t) / (A(t) + C(t))` is exactly `Recall(t)`, for every `π(t) ≠ 0`, whatever
`f_t` and `P_t(X ∣ Y)` are doing. -/
theorem recall_prior_invariant (prior r : ℝ) (hprior : prior ≠ 0) :
    (prior * r) / (prior * r + prior * (1 - r)) = r :=
  cell_ratio_prior_invariant prior r hprior

/-- Proposition (Strict Prior-Invariance of the Canonical Basis), specificity coordinate: the
identical argument on the negative-class row, with `(1 - π(t))` in place of `π(t)`. -/
theorem specificity_prior_invariant (prior specificity : ℝ) (hprior : prior ≠ 1) :
    ((1 - prior) * specificity) / ((1 - prior) * specificity + (1 - prior) * (1 - specificity))
      = specificity :=
  cell_ratio_prior_invariant (1 - prior) specificity (sub_ne_zero.mpr (Ne.symm hprior))

/-- Proposition (Undefined-Window Probability Under Stationary Arrivals): if the `W`
per-position non-arrival events for class `j` are mutually independent (taken directly as the
multiplicativity-over-the-full-intersection property that is independence's defining content)
and each has the same arrival probability `p`, the probability that class `j` never arrives in
the window is exactly `(1-p)^W`. -/
theorem undefined_window_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : ℕ) (A : Fin W → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : μ (⋂ i, (A i)ᶜ) = ∏ i, μ (A i)ᶜ)
    (p : ENNReal) (hp : ∀ i, μ (A i) = p) :
    μ (⋂ i, (A i)ᶜ) = (1 - p) ^ W := by
  rw [hindep]
  have hcompl : ∀ i, μ (A i)ᶜ = 1 - p := fun i => by
    rw [measure_compl (hA i) (measure_ne_top μ _), hp, measure_univ]
  simp [hcompl]

/-- Corollary (Design rule for the undefined-window rate): if the window size `W` satisfies
`W ≥ log(1/δ) / (-log(1-p))`, the undefined-window probability `(1-p)^W` stays at or below the
target tolerance `δ`. -/
theorem window_sizing_rule (p δ : ℝ) (hp1 : 0 < p) (hp2 : p < 1) (hδ : 0 < δ)
    (W : ℕ) (hW : (W : ℝ) ≥ Real.log (1 / δ) / (-Real.log (1 - p))) :
    (1 - p) ^ W ≤ δ := by
  have h1p_pos : 0 < 1 - p := by linarith
  have h1p_lt1 : 1 - p < 1 := by linarith
  have hlog_neg : Real.log (1 - p) < 0 := Real.log_neg h1p_pos h1p_lt1
  have hL_pos : 0 < -Real.log (1 - p) := by linarith
  rw [ge_iff_le, div_le_iff₀ hL_pos] at hW
  have hinv_log : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [hinv_log] at hW
  have hring : (W : ℝ) * (-Real.log (1 - p)) = -((W : ℝ) * Real.log (1 - p)) := by ring
  rw [hring] at hW
  have hpow_log : Real.log ((1 - p) ^ W) = (W : ℝ) * Real.log (1 - p) := Real.log_pow (1 - p) W
  have key : Real.log ((1 - p) ^ W) ≤ Real.log δ := by
    rw [hpow_log]; linarith [hW]
  have hpow_pos : 0 < (1 - p) ^ W := pow_pos h1p_pos W
  have hexp := Real.exp_le_exp.mpr key
  rwa [Real.exp_log hpow_pos, Real.exp_log hδ] at hexp

/-- Proposition, expectation half of "Asymptotic Expectation and Variance
Scaling": unrolling the fading recurrence gives `E[C_α(t)] = (1 - α^t) * C_pop` under a
stationary generating distribution (taken here as the starting point, matching the paper's own
one-line derivation); this is the `t → ∞` convergence `E[C_α(t)] → C_pop`. -/
theorem expectation_convergence (α c : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    Filter.Tendsto (fun t : ℕ => (1 - α ^ t) * c) Filter.atTop (nhds c) := by
  have hpow : Filter.Tendsto (fun t : ℕ => α ^ t) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα1.le hα2
  have h1 : Filter.Tendsto (fun t : ℕ => 1 - α ^ t) Filter.atTop (nhds (1 - 0)) :=
    Filter.Tendsto.const_sub 1 hpow
  simpa using h1.mul_const c

/-- Proposition, variance half of "Asymptotic Expectation and Variance Scaling":
treating the per-instance variance `v = [V_inst]_{jk}` as a fixed nonnegative real constant under
a stationary `P_0` (the paper's own reduction), and the geometric unrolling `Var(C_α(t)) =
(1-α)^2 ∑_{k<t} α^{2k} v` of the fading recurrence as given, the `t → ∞` limit is exactly
`(1-α)/(1+α) * v`. Note: the paper's further step `≈ v / (2 n_eff)` with `n_eff = 1/(1-α)` is
only an *approximation* valid as `α → 1` (it is not an exact identity for general `α`), so it is
deliberately left out of this exact-limit statement. -/
theorem variance_scaling_limit (α v : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    Filter.Tendsto (fun t : ℕ => (1 - α) ^ 2 * (∑ k ∈ Finset.range t, α ^ (2 * k)) * v)
      Filter.atTop (nhds ((1 - α) / (1 + α) * v)) := by
  have hα2_nonneg : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hα2_lt_one : α ^ 2 < 1 := by nlinarith
  have hsum : HasSum (fun k : ℕ => (α ^ 2) ^ k) (1 - α ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one hα2_nonneg hα2_lt_one
  have htendsto :
      Filter.Tendsto (fun t : ℕ => ∑ k ∈ Finset.range t, (α ^ 2) ^ k) Filter.atTop
        (nhds (1 - α ^ 2)⁻¹) :=
    hsum.tendsto_sum_nat
  have heq : ∀ t : ℕ, (∑ k ∈ Finset.range t, α ^ (2 * k)) = ∑ k ∈ Finset.range t, (α ^ 2) ^ k := by
    intro t
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_mul]
  have hfinal :
      Filter.Tendsto (fun t : ℕ => (1 - α) ^ 2 * (∑ k ∈ Finset.range t, (α ^ 2) ^ k) * v)
        Filter.atTop (nhds ((1 - α) ^ 2 * (1 - α ^ 2)⁻¹ * v)) :=
    (htendsto.const_mul ((1 - α) ^ 2)).mul_const v
  have h1pα : (1 : ℝ) + α ≠ 0 := by linarith
  have h1mα : (1 : ℝ) - α ≠ 0 := by linarith
  have hval : (1 - α) ^ 2 * (1 - α ^ 2)⁻¹ * v = (1 - α) / (1 + α) * v := by
    have h1ma2 : (1 : ℝ) - α ^ 2 ≠ 0 := by
      have : (1 : ℝ) - α ^ 2 = (1 - α) * (1 + α) := by ring
      rw [this]; exact mul_ne_zero h1mα h1pα
    field_simp
    ring
  simpa only [heq, hval] using hfinal

/-- Theorem, "Analytical Jacobian Drift Decomposition": for a composite metric
`M(t) = g(R11(t), R00(t), π(t))` built from a Fréchet-differentiable `g : ℝ × ℝ × ℝ → ℝ` and
differentiable canonical-coordinate/prior curves, the total temporal derivative is exactly the
multivariate chain rule, split along the paper's own grouping: the "concept drift" part (the
partials w.r.t. the two canonical coordinates `R11`, `R00`, each times its own rate of change)
plus the "prior shift" part (the partial w.r.t. `π`, times its rate of change). This is the
general chain rule (`HasFDerivAt.comp_hasDerivAt`) instantiated to `ℝ × ℝ × ℝ`, with the
three-way additive split obtained from linearity of the Fréchet derivative `g'` alone — no
extra hypothesis beyond differentiability of `g` and of the three coordinate curves is needed. -/
theorem jacobian_decomposition
    (g : ℝ × ℝ × ℝ → ℝ) (R11 R00 π : ℝ → ℝ) (t : ℝ)
    (r11' r00' π' : ℝ)
    (hR11 : HasDerivAt R11 r11' t) (hR00 : HasDerivAt R00 r00' t) (hπ : HasDerivAt π π' t)
    (g' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (hg : HasFDerivAt g g' (R11 t, R00 t, π t)) :
    HasDerivAt (fun s => g (R11 s, R00 s, π s))
      (g' (1, 0, 0) * r11' + g' (0, 1, 0) * r00' + g' (0, 0, 1) * π') t := by
  have hpath : HasDerivAt (fun s => (R11 s, R00 s, π s)) (r11', r00', π') t :=
    hR11.prodMk (hR00.prodMk hπ)
  have hcomp : HasDerivAt (fun s => g (R11 s, R00 s, π s)) (g' (r11', r00', π')) t :=
    hg.comp_hasDerivAt t hpath
  have hval : g' (r11', r00', π')
      = g' (1, 0, 0) * r11' + g' (0, 1, 0) * r00' + g' (0, 0, 1) * π' := by
    have hsplit : (r11', r00', π') =
        r11' • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + r00' • ((0 : ℝ), (1 : ℝ), (0 : ℝ))
          + π' • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  rwa [hval] at hcomp

end Aggmetrics.DataStream

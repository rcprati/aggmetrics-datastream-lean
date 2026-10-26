# aggmetrics-datastream-lean

Lean 4 / Mathlib formalization accompanying the paper *A Temporal Algebraic Framework for Data Stream
Evaluation Under Delayed Labels and Distribution Shifts*.

## Contents

| File | Content |
|---|---|
| `Aggmetrics/Basic.lean` | The part of the base framework formalization that the data-stream modules use (`weighted_ratio_mixture`, `micro_eq_macro_iff`, ...) |
| `Aggmetrics/DataStream.lean` | Decomposability on given cells, prior-invariance cancellation, undefined-window probability, window-sizing rule, limits of the fading estimator, chain rule |
| `Aggmetrics/DataStreamTemporal.lean` | The temporal state, commutation with the selection matrices, Theorem 1 with its temporal part, recurrences, exact drift decomposition |
| `Aggmetrics/DataStreamDelay.lean` | Marginal consistency of the product t-norm, bias identity, invariant of Algorithm 1, eviction tail, zero-division policies |
| `Aggmetrics/DataStreamProb.lean` | Undefined-window probability from independence, with latency and under fading, multiclass prior-invariance |
| `Aggmetrics/DataStreamDrift.lean` | Prior-invariance with integrals, variance of the fading estimator at every `t`, closed-form Jacobians, drift profiles |
| `Aggmetrics/DataStreamEviction.lean` | Algorithm 1 with eviction, exact effect on the state, bound on the queue |
| `Aggmetrics/DataStreamAutocorr.lean` | Variance of the fading estimator under autocorrelation |
| `Aggmetrics/DataStreamExample.lean` | The running example of the paper, recomputed |

## Build

```bash
lake exe cache get   # Mathlib build cache
lake build
```

Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (see `lean-toolchain` and `lake-manifest.json`).
No `sorry`. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`
(check with `#print axioms <name>`).

Docstrings in the files refer to the paths of the authors' working repository; the paper's statements are
mapped to theorems in the table below.

## Statements of the paper checked in Lean
Paper: `papers/05-data-stream/outline.tex`. All theorems are in the namespace `Aggmetrics.DataStream`
and depend only on `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`).
Build: `lake build` in this directory.

| Paper statement | Lean file | Theorems | Covered with the following limits |
|---|---|---|---|
| Theorem 1, decomposability under any nonnegative weighting | `DataStreamTemporal` | `state`, `classTable_state`, `temporal_decomposability_matrix`, `temporal_decomposability_stream` | Nonnegative label and prediction vectors; pooled denominator positive; classes with a zero denominator omitted |
| Same, on given per-class cells | `DataStream` | `temporal_decomposability` | All denominators positive |
| Fading and window recurrences (Eqs. `fading_update`, `window_update`) | `DataStreamTemporal` | `fadeState_eq_state`, `fadeWeight_sum`, `window_recurrence`, `winWeight_sum` | Window recurrence for `n ≥ W` |
| Change of the pooled measure (Eq. `drift_decomposition`) | `DataStreamTemporal` | `discrete_decomposition`, `micro_change_decomposition` | Exact |
| Running example (states, tables, precision) | `DataStreamExample` | `fade_state_four`, `window_state_eight`, `window_tables`, `precision_example` | Values of the paper |
| Marginal consistency of the product t-norm; defects | `DataStreamDelay` | `outer_row_sum`, `outer_col_sum`, `defect_product`, `defect_min_example`, `defect_luk_example`, `tnorm_hard_min`, `tnorm_hard_luk` | Defects of min and Łukasiewicz on the running example only |
| Uniqueness of the product t-norm | `TNorm` (base paper) | `marginal_consistency_iff_product` | |
| Bias identity (Eq. `bias`) | `DataStreamDelay` | `bias_identity`, `bias_expectation_zero` | Expectation: residual has mean zero given the scores |
| Algorithm 1 invariant (Eq. `unified_cm`) | `DataStreamDelay`, `DataStreamEviction` | `algState_eq`, `algStateE_eq`, `algState_sub_algStateE` | Exponential fading; with eviction, the state minus the discarded corrections (exact) |
| Eviction tail (Eq. `truncation_bound`) and its effect on the state | `DataStreamDelay`, `DataStreamEviction` | `fade_tail_sum`, `fade_tail_lt`, `evicted_change_bound`, `eviction_entry_bound`, `eviction_entry_bound_count` | Entries of the label, stand-in and prediction vectors in `[0,1]`; bound `α^s` in total and `ε` per discarded correction |
| Bounded queue (`\|Q(t)\| ≤ s* ≤ n_eff ln(1/(n_eff ε)) + 2`) | `DataStreamEviction` | `queue_card_le`, `evict_age_exists` | Any predicate on the entries; `n_eff ε < 1` for the logarithmic form |
| Column sums independent of the stand-in | `DataStreamDelay` | `unified_col_sum` | |
| Zero-division policies, audit property | `DataStreamDelay` | `perClass_audit`, `perClass_default`, `macroExclude_indep`, `macroNan_none`, `macroZero_eq_exclude`, `policy_example` | |
| Cell-ratio lemma | `DataStream` | `cell_ratio_prior_invariant` | |
| Prior invariance, binary (Prop. `prior_invariance`) | `DataStreamDrift`, `DataStream` | `recall_integral`, `specificity_integral`, `precision_depends_on_prior`, `recall_prior_invariant`, `specificity_prior_invariant` | Class-conditional laws are probability measures; decision function integrable |
| Undefined-window probability (Prop. `undefined_window`) | `DataStreamProb` | `undefined_window_indep`, `undefined_window_indep_const`, `undefined_window_fading_lower`, `undefined_window_fading_upper` | From `iIndepSet`; the two ages of the fading bounds enter through their defining inequalities |
| Window-sizing rule (Cor. `window_sizing`) | `DataStream` | `window_sizing_rule` | |
| Latency corollary (Cor. `undefined_latency`) | `DataStreamProb` | `undefined_latency`, `latency_const_delay`, `latency_delay_ge_window`, `window_sizing_latency` | |
| Multiclass prior invariance (Prop. `multiclass_invariance`) | `DataStreamProb` | `row_prior_invariant`, `spec_joint_eq_formula`, `spec_composition_invariant`, `spec_constant_column`, `spec_example` | |
| Expectation and variance of the fading estimator (Prop. `variance_scaling`) | `DataStreamDrift`, `DataStream` | `fading_expectation`, `fading_variance`, `fadeWeight_sq_sum`, `expectation_convergence`, `variance_scaling_limit` | Independent entries with equal mean and variance |
| Variance with autocorrelated entries (Remark `autocorr`, Eq. `variance_inflation`) | `DataStreamAutocorr` | `fading_variance_autocorr`, `covSum_succ`, `lag_tail`, `covSum_bound`, `covSum_tendsto`, `fading_variance_tendsto`, `kappa_iid`, `kappa_ar1` | Stationary covariance `v ρ(\|i-j\|)`, `ρ(0)=1`, `\|ρ\|≤1`; exact for every `t`; `\|D_t - V\| ≤ max(2,\|V\|) α^t` |
| Chain rule (Eq. `jacobian_decomposition`) | `DataStream` | `jacobian_decomposition` | |
| Closed-form Jacobians; mid-point rule exact for accuracy | `DataStreamDrift` | `precision_dR`, `precision_dS`, `precision_dπ`, `f1_dR`, `f1_dS`, `f1_dπ`, `accuracy_partials`, `accuracy_midpoint_exact` | Precision, `F₁` and accuracy |
| Drift profiles: abrupt, half-life, tracking lag, outlier | `DataStreamDrift` | `abrupt_state`, `half_life`, `tracking_lag`, `tracking_lag_tendsto`, `outlier_response` | Gradual and reoccurring profiles are not formalized |

## Not formalized

The bursty (Markov) extension of the undefined-window probability, the sliding-window form of
Algorithm 1 with eviction, the complexity bounds, the
Jacobian of the balanced accuracy, the error of the mid-point rule for `F₁` and the precision, the
gradual and reoccurring drift profiles, and every empirical result of the paper.


## Citation and license

Released under the [Apache License 2.0](LICENSE), the license of Lean 4 and Mathlib, which this project
depends on. Each Lean file carries the Mathlib-style copyright header. See `CITATION.cff` to cite the
software; cite the paper as well.

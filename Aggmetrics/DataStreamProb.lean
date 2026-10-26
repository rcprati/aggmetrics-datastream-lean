/-
Copyright (c) 2026 Ronaldo C. Prati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ronaldo C. Prati
-/
import Aggmetrics.DataStream
import Aggmetrics.DataStreamDelay

/-!
# Probability of undefined windows and multiclass prior-invariance (data-stream paper)

Formalized here, on top of `Aggmetrics.DataStream` and `Aggmetrics.DataStreamDelay`:

* **C1** the undefined-window probability of a sliding window **from Mathlib's independence**
  (`iIndepSet`), not from an assumed product formula, for arrivals with arbitrary per-position
  probabilities (`undefined_window_indep`) and equal ones (`undefined_window_indep_const`);
* **C2** the latency corollary `∏ₛ (1 - p b F(s))` (`undefined_latency`), its value for a constant
  delay `(1 - pb)^(W-Δ)` (`latency_const_delay`), for a delay beyond the window
  (`latency_delay_ge_window`) and the window size it requires (`window_sizing_latency`);
* **C3** the two-sided bound on the undefined-window probability under exponential fading with a
  mass tolerance (`undefined_window_fading_lower`, `undefined_window_fading_upper`);
* **C4** the multiclass prior-invariance: rows of the confusion matrix do not depend on the prior
  (`row_prior_invariant`), the one-vs-rest specificity is the prior-weighted formula of the paper
  (`spec_joint_eq_formula`), depends on the prior only through the composition of the other
  classes (`spec_composition_invariant`), is invariant when column `j` is constant
  (`spec_constant_column`), and moves otherwise, on the running example (`spec_example`).
-/

open Finset Matrix MeasureTheory ProbabilityTheory

namespace Aggmetrics.DataStream

/-! ### C1. Undefined windows from independence -/

/-- The complements of independent events are independent: the probability of the intersection
of the complements over a finite set is the product of the probabilities of the complements. -/
theorem iIndepSet_compl_meas_biInter {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ι → Set Ω) (hA : iIndepSet A μ) (S : Finset ι) :
    μ (⋂ i ∈ S, (A i)ᶜ) = ∏ i ∈ S, μ (A i)ᶜ := by
  have hf : iIndepFun (fun i => (A i).indicator fun _ω => (1 : ℝ)) μ := hA.iIndepFun_indicator
  refine hf.meas_biInter (fun i _ => ?_)
  refine MeasurableSpace.measurableSet_comap.mpr ⟨{0}, measurableSet_singleton 0, ?_⟩
  ext ω
  by_cases h : ω ∈ A i <;> simp [Set.indicator, h]

/-- Probability that none of the independent events `A i`, `i ∈ S`, occurs. -/
theorem undefined_window_indep {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ι → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
    (μ (⋂ i ∈ S, (A i)ᶜ)).toReal = ∏ i ∈ S, (1 - (μ (A i)).toReal) := by
  rw [iIndepSet_compl_meas_biInter μ A hA S, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [measure_compl (hmeas i) (measure_ne_top μ _), measure_univ,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

/-- **Undefined-window probability, from independence.** If the arrivals of class `j` at the `W`
positions of the window are independent events of probability `p`, none occurs with probability
`(1 - p)^W`. -/
theorem undefined_window_indep_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p) (W : ℕ) :
    (μ (⋂ i ∈ range W, (A i)ᶜ)).toReal = (1 - p) ^ W := by
  rw [undefined_window_indep μ A hA hmeas,
    Finset.prod_congr rfl (fun i _ => (by rw [hp i] : 1 - (μ (A i)).toReal = 1 - p)),
    Finset.prod_const, Finset.card_range]

/-! ### C2. Latency -/

/-- **Undefined-window probability with latency.** If the event `A s` "the instance of age `s` is
a verified instance of class `j`" has probability `q s = p b F(s)`, and these events are
independent, no verified instance of the class is in the window with probability `∏ₛ (1 - q s)`. -/
theorem undefined_latency {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (q : ℕ → ℝ) (hq : ∀ s, (μ (A s)).toReal = q s) (W : ℕ) :
    (μ (⋂ s ∈ range W, (A s)ᶜ)).toReal = ∏ s ∈ range W, (1 - q s) := by
  rw [undefined_window_indep μ A hA hmeas]
  exact Finset.prod_congr rfl (fun s _ => by rw [hq s])

/-- A constant delay `Δ ≤ W`: the factors of the first `Δ` ages are `1` and the others `1 - pb`. -/
theorem latency_const_delay (pb : ℝ) (Δ W : ℕ) (hΔ : Δ ≤ W) :
    ∏ s ∈ range W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = (1 - pb) ^ (W - Δ) := by
  have h := Finset.prod_Ico_consecutive
    (fun s => 1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) (Nat.zero_le Δ) hΔ
  rw [Finset.range_eq_Ico, ← h]
  have h1 : ∏ s ∈ Ico 0 Δ, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 := by
    refine Finset.prod_eq_one (fun s hs => ?_)
    have : s < Δ := (Finset.mem_Ico.mp hs).2
    simp [not_le.mpr this]
  have h2 : ∏ s ∈ Ico Δ W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = (1 - pb) ^ (W - Δ) := by
    rw [Finset.prod_congr rfl (fun s hs => by
      have : Δ ≤ s := (Finset.mem_Ico.mp hs).1
      simp [this] : ∀ s ∈ Ico Δ W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 - pb)]
    rw [Finset.prod_const, Nat.card_Ico]
  rw [h1, h2, one_mul]

/-- A delay of at least the window: every window is undefined. -/
theorem latency_delay_ge_window (pb : ℝ) (Δ W : ℕ) (hΔ : W ≤ Δ) :
    ∏ s ∈ range W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 := by
  refine Finset.prod_eq_one (fun s hs => ?_)
  have : s < W := Finset.mem_range.mp hs
  have : ¬ Δ ≤ s := by omega
  simp [this]

/-- The window needed for a target tolerance `δ` grows by the delay:
`W ≥ Δ + ln(1/δ) / (-ln(1 - pb))` keeps `(1 - pb)^(W - Δ)` below `δ`. -/
theorem window_sizing_latency (pb δ : ℝ) (hp1 : 0 < pb) (hp2 : pb < 1) (hδ : 0 < δ)
    (Δ W : ℕ) (hΔ : Δ ≤ W)
    (hW : (W : ℝ) ≥ Δ + Real.log (1 / δ) / (-Real.log (1 - pb))) :
    (1 - pb) ^ (W - Δ) ≤ δ := by
  refine window_sizing_rule pb δ hp1 hp2 hδ (W - Δ) ?_
  rw [Nat.cast_sub hΔ]
  linarith

/-! ### C3. Undefined windows under exponential fading -/

/-- Lower bound: if `α^k ≤ ε`, then `k` silent steps leave a class with mass at most `ε`, so the
class is unsupported with probability at least `(1 - p)^k`. -/
theorem undefined_window_fading_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p)
    {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t k : ℕ) (hk : α ^ k ≤ ε) :
    (1 - p) ^ k ≤ (μ {ω | ∑ s ∈ range t,
        (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε}).toReal := by
  have hsub : (⋂ s ∈ range k, (A s)ᶜ) ⊆ {ω | ∑ s ∈ range t,
      (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε} := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range] at hω
    simp only [Set.mem_setOf_eq]
    have hsum : ∑ s ∈ range t, (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω
        = ∑ s ∈ (range t).filter (fun s => k ≤ s),
            (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      by_cases hs : k ≤ s
      · simp [hs]
      · have hsk : s < k := not_le.mp hs
        simp [hs, Set.indicator_apply, hω s hsk]
    rw [hsum]
    calc _ ≤ |∑ s ∈ (range t).filter (fun s => k ≤ s),
              (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω| := le_abs_self _
      _ ≤ α ^ k := evicted_change_bound h0 h1 k _ (fun s hs => (Finset.mem_filter.mp hs).2)
            (fun s => (A s).indicator (fun _ => (1 : ℝ)) ω)
            (fun s => by by_cases h : ω ∈ A s <;> simp [h])
      _ ≤ ε := hk
  calc (1 - p) ^ k = (μ (⋂ s ∈ range k, (A s)ᶜ)).toReal :=
        (undefined_window_indep_const μ A hA hmeas p hp k).symm
    _ ≤ _ := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)

/-- Upper bound: if every age below `k ≤ t` carries a weight above `ε`, an arrival in the last
`k` steps keeps the class supported, so it is unsupported with probability at most `(1 - p)^k`. -/
theorem undefined_window_fading_upper {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA : iIndepSet A μ)
    (hmeas : ∀ i, MeasurableSet (A i)) (p : ℝ) (hp : ∀ i, (μ (A i)).toReal = p)
    {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t k : ℕ) (hk : ∀ s < k, ε < (1 - α) * α ^ s)
    (hkt : k ≤ t) :
    (μ {ω | ∑ s ∈ range t,
        (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε}).toReal ≤ (1 - p) ^ k := by
  have hsub : {ω | ∑ s ∈ range t,
      (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω ≤ ε} ⊆ ⋂ s ∈ range k, (A s)ᶜ := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
    intro s hs hAs
    simp only [Set.mem_setOf_eq] at hω
    have hnn : ∀ i ∈ range t,
        0 ≤ (1 - α) * α ^ i * (A i).indicator (fun _ => (1 : ℝ)) ω := fun i _ =>
      mul_nonneg (mul_nonneg (by linarith) (pow_nonneg h0 i))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    have hle := Finset.single_le_sum hnn (Finset.mem_range.mpr (lt_of_lt_of_le hs hkt))
    have h2 : (1 - α) * α ^ s * (A s).indicator (fun _ => (1 : ℝ)) ω = (1 - α) * α ^ s := by
      simp [Set.indicator_of_mem hAs]
    rw [h2] at hle
    have := hk s hs
    linarith
  calc _ ≤ (μ (⋂ s ∈ range k, (A s)ᶜ)).toReal :=
        ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    _ = (1 - p) ^ k := undefined_window_indep_const μ A hA hmeas p hp k

/-! ### C4. Multiclass prior-invariance -/

/-- The rows of the confusion matrix do not depend on the prior: normalizing the joint cells
`π_k c_{kl}` of a class with `π_k ≠ 0` gives back `c_{kl}`. -/
theorem row_prior_invariant {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ)
    (hrow : ∀ k, ∑ l, c k l = 1) (k l : Fin m) (hπ : π k ≠ 0) :
    (π k * c k l) / (∑ l', π k * c k l') = c k l := by
  rw [← Finset.mul_sum, hrow k, mul_one]
  exact mul_div_cancel_left₀ _ hπ

/-- One-vs-rest specificity of class `j` from the joint cells: true negatives over negatives. -/
noncomputable def specJoint {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) : ℝ :=
  (∑ k ∈ univ.erase j, ∑ l ∈ univ.erase j, π k * c k l) / (∑ k ∈ univ.erase j, π k)

/-- The formula of the paper, `∑_{k≠j} π_k/(1-π_j) (1 - c_{kj})`. -/
noncomputable def specFormula {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ k ∈ univ.erase j, (π k / (1 - π j)) * (1 - c k j)

/-- The specificity from the joint cells is the formula of the paper. -/
theorem spec_joint_eq_formula {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m)
    (hπ : ∑ k, π k = 1) (hrow : ∀ k, ∑ l, c k l = 1) (hj : π j ≠ 1) :
    specJoint π c j = specFormula π c j := by
  have hden : ∑ k ∈ univ.erase j, π k = 1 - π j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hπ]
  have hnum : ∀ k, ∑ l ∈ univ.erase j, π k * c k l = π k * (1 - c k j) := fun k => by
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j), hrow k]
  unfold specJoint specFormula
  rw [hden, Finset.sum_congr rfl (fun k _ => hnum k), Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The specificity depends on the prior only through the composition of the other classes. -/
theorem spec_composition_invariant {m : ℕ} (π π' : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m)
    (h : ∀ k ∈ univ.erase j, π k / (1 - π j) = π' k / (1 - π' j)) :
    specFormula π c j = specFormula π' c j :=
  Finset.sum_congr rfl (fun k hk => by rw [h k hk])

/-- If column `j` of the confusion matrix is constant over `k ≠ j`, the specificity is `1 - γ`
for every prior. -/
theorem spec_constant_column {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) (γ : ℝ)
    (hπ : ∑ k, π k = 1) (hj : π j ≠ 1) (hcol : ∀ k, k ≠ j → c k j = γ) :
    specFormula π c j = 1 - γ := by
  have hden : ∑ k ∈ univ.erase j, π k = 1 - π j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hπ]
  have h1j : (1 - π j) ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
  unfold specFormula
  rw [Finset.sum_congr rfl (fun k hk => by rw [hcol k (Finset.ne_of_mem_erase hk)]),
    ← Finset.sum_mul, ← Finset.sum_div, hden]
  field_simp

/-- Running example: each class is mistaken for the next one. A label shift between `B` and `C`
leaves the rows and the recall of `A` unchanged, and moves the specificity of `A` from `7/8` to
`13/16`. -/
theorem spec_example :
    specFormula ![1 / 2, 1 / 4, 1 / 4]
      ![![3 / 4, 1 / 4, 0], ![0, 3 / 4, 1 / 4], ![1 / 4, 0, 3 / 4]] 0 = 7 / 8 ∧
    specFormula ![1 / 2, 1 / 8, 3 / 8]
      ![![3 / 4, 1 / 4, 0], ![0, 3 / 4, 1 / 4], ![1 / 4, 0, 3 / 4]] 0 = 13 / 16 := by
  constructor <;>
  · simp only [specFormula, Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_three]
    norm_num

end Aggmetrics.DataStream

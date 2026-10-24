import Aggmetrics.DataStreamTemporal

/-!
# Verification latency, the interim estimate and Algorithm 1 (data-stream paper, Section 4)

Formalized here, on top of `Aggmetrics.DataStreamTemporal`:

* **B1** the interim contribution `ỹ pᵀ` of the product `t`-norm has the prescribed marginals
  (`outer_row_sum`, `outer_col_sum`, `defect_product`); the minimum and the Łukasiewicz `t`-norm
  have a positive marginal defect on the soft example of the paper (`defect_min_example`,
  `defect_luk_example`) and coincide with the product on hard predictions
  (`tnorm_hard_min`, `tnorm_hard_luk`);
* **B2** the bias identity `C_oracle - C = ∑ₖ (1 - Oₖ) wₖ (yₖ - ỹₖ) pₖᵀ` (`bias_identity`) and its
  expectation under calibration (`bias_expectation_zero`);
* **B3** the invariant of Algorithm 1 for exponential fading without eviction: after every step
  the running matrix equals the unified state, in which a label that has arrived replaces the
  stand-in (`algState_eq`);
* **B4** the geometric tail behind the eviction bound (`fade_tail_sum`, `fade_tail_lt`) and the
  bound on the change caused by evicted corrections (`evicted_change_bound`);
* **B5** the zero-division policies `exclude`, `zero`, `nan` and the audit property
  (`macroExclude`, `macroZero`, `macroNan`, `perClass_*`);
* **B6** the column sums of the unified state do not depend on the stand-in (`unified_col_sum`).
-/

open Finset Matrix MeasureTheory

namespace Aggmetrics.DataStream

/-! ### B1. Marginal consistency of the product `t`-norm -/

theorem outer_row_sum {m : ℕ} (yt p : Fin m → ℝ) (hp : ∑ b, p b = 1) (a : Fin m) :
    ∑ b, outer yt p a b = yt a := by
  simp [outer, ← Finset.mul_sum, hp]

theorem outer_col_sum {m : ℕ} (yt p : Fin m → ℝ) (hy : ∑ a, yt a = 1) (b : Fin m) :
    ∑ a, outer yt p a b = p b := by
  simp [outer, ← Finset.sum_mul, hy]

/-- Marginal defect of a bivariate aggregation operator `T` on `(ỹ, p)`: the `ℓ¹` distance of the
column sums of `T(ỹ_a, p_b)` to `p` plus that of the row sums to `ỹ`. -/
noncomputable def defect {m : ℕ} (T : ℝ → ℝ → ℝ) (yt p : Fin m → ℝ) : ℝ :=
  ∑ b, |∑ a, T (yt a) (p b) - p b| + ∑ a, |∑ b, T (yt a) (p b) - yt a|

/-- The product `t`-norm has zero marginal defect. -/
theorem defect_product {m : ℕ} (yt p : Fin m → ℝ) (hy : ∑ a, yt a = 1) (hp : ∑ b, p b = 1) :
    defect (fun x y => x * y) yt p = 0 := by
  unfold defect
  have h1 : ∀ b, ∑ a, yt a * p b = p b := fun b => by rw [← Finset.sum_mul, hy, one_mul]
  have h2 : ∀ a, ∑ b, yt a * p b = yt a := fun a => by rw [← Finset.mul_sum, hp, mul_one]
  simp [h1, h2]

/-- The soft prediction and stand-in of instance 7 in the running example. -/
noncomputable def softEx : Fin 3 → ℝ := ![1 / 8, 1 / 8, 3 / 4]

/-- The minimum `t`-norm has marginal defect `3/2` on the running example. -/
theorem defect_min_example : defect (fun x y => min x y) softEx softEx = 3 / 2 := by
  norm_num [defect, softEx, Fin.sum_univ_three, min_def, abs_of_nonneg, abs_of_nonpos]

/-- The Łukasiewicz `t`-norm has marginal defect `1` on the running example. -/
theorem defect_luk_example : defect (fun x y => max 0 (x + y - 1)) softEx softEx = 1 := by
  norm_num [defect, softEx, Fin.sum_univ_three, max_def, abs_of_nonneg, abs_of_nonpos]

/-- On a hard (one-hot) prediction the minimum `t`-norm is the product. -/
theorem tnorm_hard_min {m : ℕ} (yt : Fin m → ℝ) (hy : ∀ a, 0 ≤ yt a ∧ yt a ≤ 1) (k a b : Fin m) :
    min (yt a) (if b = k then (1 : ℝ) else 0) = yt a * (if b = k then (1 : ℝ) else 0) := by
  by_cases h : b = k
  · simp [h, (hy a).2]
  · simp [h, (hy a).1]

/-- On a hard prediction the Łukasiewicz `t`-norm is the product. -/
theorem tnorm_hard_luk {m : ℕ} (yt : Fin m → ℝ) (hy : ∀ a, 0 ≤ yt a ∧ yt a ≤ 1) (k a b : Fin m) :
    max 0 (yt a + (if b = k then (1 : ℝ) else 0) - 1) = yt a * (if b = k then (1 : ℝ) else 0) := by
  by_cases h : b = k
  · simp [h, (hy a).1]
  · simp [h, (hy a).2]

/-! ### B2. The bias identity -/

/-- The unified state: instances with `O k = 1` contribute their verified label, the others their
stand-in. -/
noncomputable def unified {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ k, (O k * w k) • outer (y k) (p k) + ∑ k, ((1 - O k) * w k) • outer (yt k) (p k)

/-- `C_oracle - C = ∑ₖ (1 - Oₖ) wₖ (yₖ - ỹₖ) pₖᵀ`, exactly. -/
theorem bias_identity {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ) :
    state w y p - unified w O y yt p
      = ∑ k, ((1 - O k) * w k) • outer (fun c => y k c - yt k c) (p k) := by
  ext a b
  simp only [unified, state_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, outer, Matrix.of_apply, smul_eq_mul]
  rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Under calibration (the residual `y - ỹ` has mean zero given the scores and predictions, which
are fixed here), the expected bias is zero. -/
theorem bias_expectation_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (w O : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (y yt : Fin n → Ω → Fin m → ℝ)
    (hint : ∀ k a, Integrable (fun ω => y k ω a - yt k ω a) μ)
    (hcal : ∀ k a, ∫ ω, (y k ω a - yt k ω a) ∂μ = 0) (a b : Fin m) :
    ∫ ω, (∑ k, ((1 - O k) * w k) • outer (fun c => y k ω c - yt k ω c) (p k)) a b ∂μ = 0 := by
  have h : ∀ ω, (∑ k, ((1 - O k) * w k) • outer (fun c => y k ω c - yt k ω c) (p k)) a b
      = ∑ k, ((1 - O k) * w k * p k b) * (y k ω a - yt k ω a) := by
    intro ω
    simp only [Matrix.sum_apply, Matrix.smul_apply, outer, Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp_rw [h]
  rw [integral_finset_sum _ (fun k _ => (hint k a).const_mul _)]
  simp [integral_const_mul, hcal]

/-! ### B6. Column sums do not depend on the stand-in -/

/-- The column sums of the unified state are those of the oracle state: the stand-in changes the
label side (rows) of the state and not the prediction side (columns). -/
theorem unified_col_sum {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ)
    (hy : ∀ k, ∑ a, y k a = 1) (hyt : ∀ k, ∑ a, yt k a = 1) (b : Fin m) :
    ∑ a, unified w O y yt p a b = ∑ k, w k * p k b := by
  have h : ∀ a, unified w O y yt p a b
      = ∑ k, ((O k * w k) * (y k a * p k b) + ((1 - O k) * w k) * (yt k a * p k b)) := by
    intro a
    simp only [unified, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, outer,
      Matrix.of_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  calc ∑ a, ((O k * w k) * (y k a * p k b) + ((1 - O k) * w k) * (yt k a * p k b))
      = (O k * w k * p k b) * ∑ a, y k a + ((1 - O k) * w k * p k b) * ∑ a, yt k a := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun a _ => by ring)
    _ = w k * p k b := by rw [hy k, hyt k]; ring

/-! ### B3. The invariant of Algorithm 1 (exponential fading, no eviction) -/

theorem fadeWeight_succ {α : ℝ} {n k : ℕ} (hk : k < n) :
    fadeWeight α (n + 1) k = α * fadeWeight α n k := by
  unfold fadeWeight
  have : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
  rw [this, pow_succ]
  ring

theorem fadeWeight_last (α : ℝ) (n : ℕ) : fadeWeight α (n + 1) n = 1 - α := by
  simp [fadeWeight]

open scoped Classical in
/-- Label vector of instance `k` in the state after `n` instances: the verified label if the
instance is audited and its label has arrived (`arr k ≤ n`), the stand-in otherwise. -/
noncomputable def zvec {m : ℕ} (y yt : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (n k : ℕ) : Fin m → ℝ :=
  if aud k ∧ arr k ≤ n then y k else yt k

open scoped Classical in
/-- Algorithm 1 with exponential fading and no eviction. At step `n + 1` it decays the state,
credits the stand-in of the new instance `n` and, for every audited instance whose label arrives
at this step, swaps the stand-in for the verified term. -/
noncomputable def algState {m : ℕ} (α : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 0
  | n + 1 =>
      (α • algState α y yt p aud arr n + (1 - α) • outer (yt n) (p n))
        + ∑ k ∈ (range (n + 1)).filter (fun k => aud k ∧ arr k = n + 1),
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k))

open scoped Classical in
/-- **Invariant of Algorithm 1.** If every label arrives after its instance (`k < arr k`), the
running matrix after `n` steps is the unified state `∑ₖ w_k(n) ỹ-or-y_k p_kᵀ` with the fading
weights, in which a label that has arrived has replaced its stand-in. -/
theorem algState_eq {m : ℕ} (α : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (harr : ∀ k, k < arr k) (n : ℕ) :
    algState α y yt p aud arr n
      = ∑ k ∈ range n, fadeWeight α n k • outer (zvec y yt aud arr n k) (p k) := by
  induction n with
  | zero => simp [algState]
  | succ n ih =>
    rw [algState, ih]
    have hk : ∀ k ∈ range n,
        fadeWeight α (n + 1) k • outer (zvec y yt aud arr (n + 1) k) (p k)
          = α • (fadeWeight α n k • outer (zvec y yt aud arr n k) (p k))
            + (if aud k ∧ arr k = n + 1 then
                fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0) := by
      intro k hk'
      have hkn : k < n := Finset.mem_range.mp hk'
      rw [fadeWeight_succ hkn]
      by_cases h : aud k ∧ arr k = n + 1
      · have h1 : zvec y yt aud arr (n + 1) k = y k := by
          unfold zvec
          rw [if_pos ⟨h.1, by omega⟩]
        have h2 : zvec y yt aud arr n k = yt k := by
          unfold zvec
          rw [if_neg (by rintro ⟨_, h3⟩; omega)]
        rw [if_pos h, h1, h2, smul_sub, smul_smul]
        abel
      · have h3 : (aud k ∧ arr k ≤ n + 1) ↔ (aud k ∧ arr k ≤ n) := by
          constructor
          · rintro ⟨h4, h5⟩
            refine ⟨h4, ?_⟩
            have h6 : arr k ≠ n + 1 := fun h7 => h ⟨h4, h7⟩
            omega
          · rintro ⟨h4, h5⟩
            exact ⟨h4, by omega⟩
        have h1 : zvec y yt aud arr (n + 1) k = zvec y yt aud arr n k := by
          unfold zvec
          simp only [h3]
        rw [if_neg h, h1, smul_smul, add_zero]
    have hlast : fadeWeight α (n + 1) n • outer (zvec y yt aud arr (n + 1) n) (p n)
        = (1 - α) • outer (yt n) (p n)
          + (if aud n ∧ arr n = n + 1 then
              fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0) := by
      rw [fadeWeight_last]
      by_cases h : aud n ∧ arr n = n + 1
      · have h1 : zvec y yt aud arr (n + 1) n = y n := by
          unfold zvec
          rw [if_pos ⟨h.1, by omega⟩]
        rw [if_pos h, h1, smul_sub]
        abel
      · have h3 : ¬ (aud n ∧ arr n ≤ n + 1) := by
          rintro ⟨h4, h5⟩
          exact h ⟨h4, by have := harr n; omega⟩
        have h1 : zvec y yt aud arr (n + 1) n = yt n := by
          unfold zvec
          rw [if_neg h3]
        rw [if_neg h, h1, add_zero]
    rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_congr rfl hk, Finset.sum_add_distrib, ← Finset.smul_sum, hlast]
    abel

/-! ### B4. The geometric tail behind the eviction bound -/

/-- The tail of the fading weights from age `s` on carries mass exactly `α^s`. -/
theorem fade_tail_sum {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (s : ℕ) :
    HasSum (fun j : ℕ => (1 - α) * α ^ (s + j)) (α ^ s) := by
  have hne : (1 - α) ≠ 0 := by linarith
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left ((1 - α) * α ^ s)
  convert h using 1
  · ext j
    rw [pow_add]
    ring
  · field_simp

/-- If the weight of an entry of age `s` is below `ε`, the tail from `s` on carries less than
`ε n_eff`, with `n_eff = 1/(1-α)`. -/
theorem fade_tail_lt {α ε : ℝ} (h1 : α < 1) (s : ℕ) (hs : (1 - α) * α ^ s < ε) :
    α ^ s < ε * (1 / (1 - α)) := by
  have hpos : 0 < 1 - α := by linarith
  rw [mul_one_div, lt_div_iff₀ hpos, mul_comm]
  exact hs

theorem fade_Ico_sum {α : ℝ} (s N : ℕ) (hsN : s ≤ N) :
    ∑ j ∈ Ico s N, (1 - α) * α ^ j = α ^ s - α ^ N := by
  induction N, hsN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    ring

/-- Late corrections that are evicted change the state by at most the tail mass `α^s` per entry,
if each correction has entries bounded by one (as `y pᵀ - ỹ pᵀ` has for probability vectors). -/
theorem evicted_change_bound {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (s : ℕ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, s ≤ j) (d : ℕ → ℝ) (hd : ∀ j, |d j| ≤ 1) :
    |∑ j ∈ S, (1 - α) * α ^ j * d j| ≤ α ^ s := by
  have hw : ∀ j, 0 ≤ (1 - α) * α ^ j := fun j => mul_nonneg (by linarith) (pow_nonneg h0 j)
  have h2 : |∑ j ∈ S, (1 - α) * α ^ j * d j| ≤ ∑ j ∈ S, (1 - α) * α ^ j := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_of_nonneg (hw j)]
    exact mul_le_of_le_one_right (hw j) (hd j)
  refine h2.trans ?_
  set N := max s (S.sup id + 1) with hN
  have hsub : S ⊆ Ico s N := by
    intro j hj
    rw [Finset.mem_Ico]
    exact ⟨hS j hj, lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
      (le_max_right _ _)⟩
  have hsN : s ≤ N := le_max_left _ _
  calc ∑ j ∈ S, (1 - α) * α ^ j ≤ ∑ j ∈ Ico s N, (1 - α) * α ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    _ = α ^ s - α ^ N := fade_Ico_sum s N hsN
    _ ≤ α ^ s := by have := pow_nonneg h0 N; linarith

/-! ### B5. The zero-division policies and the audit property -/

/-- Number of classes with non-zero support. -/
def active {m : ℕ} (u : Fin m → Bool) : ℕ := (univ.filter fun j => u j = true).card

/-- `policy = exclude`: average over the supported classes (undefined if there is none). -/
noncomputable def macroExclude {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) : Option ℝ :=
  if active u = 0 then none else some ((∑ j, if u j = true then v j else 0) / (active u : ℝ))

/-- `policy = zero`: an unsupported class counts as `0`. -/
noncomputable def macroZero {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) : Option ℝ :=
  some ((∑ j, if u j = true then v j else 0) / (m : ℝ))

/-- `policy = nan`: undefined as soon as one class is unsupported. -/
noncomputable def macroNan {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) : Option ℝ :=
  if ∀ j, u j = true then some ((∑ j, v j) / (m : ℝ)) else none

/-- The value a policy reports for class `j`: `none` means no number is reported. -/
def perClass (policy : String) {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m) :
    Option ℝ :=
  if u j = true then some (v j) else
    if policy = "zero" then some 0 else if policy = "one" then some 1 else none

/-- **Audit property.** `exclude` and `nan` never report a number for an unsupported class. -/
theorem perClass_audit {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m)
    (hj : u j = false) :
    perClass "exclude" u v j = none ∧ perClass "nan" u v j = none := by
  simp [perClass, hj]

/-- `zero` and `one` always report a number, supported or not. -/
theorem perClass_default {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m) :
    (perClass "zero" u v j).isSome ∧ (perClass "one" u v j).isSome := by
  unfold perClass
  by_cases hj : u j = true <;> simp [hj]

/-- The macro value of `exclude` does not depend on the values of unsupported classes. -/
theorem macroExclude_indep {m : ℕ} (u : Fin m → Bool) (v v' : Fin m → ℝ)
    (h : ∀ j, u j = true → v j = v' j) : macroExclude u v = macroExclude u v' := by
  unfold macroExclude
  congr 3
  exact Finset.sum_congr rfl (fun j _ => by by_cases hj : u j = true <;> simp [hj, h j])

/-- `nan` is undefined as soon as one class is unsupported. -/
theorem macroNan_none {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (h : ∃ j, u j = false) :
    macroNan u v = none := by
  obtain ⟨j, hj⟩ := h
  unfold macroNan
  rw [if_neg]
  intro hall
  have := hall j
  simp [hj] at this

/-- `zero` is the `exclude` average shrunk by the share of supported classes. -/
theorem macroZero_eq_exclude {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (e : ℝ)
    (hne : active u ≠ 0) (hm : (m : ℝ) ≠ 0) (he : macroExclude u v = some e) :
    macroZero u v = some (e * (active u : ℝ) / (m : ℝ)) := by
  unfold macroExclude at he
  rw [if_neg hne] at he
  have hact : (active u : ℝ) ≠ 0 := by exact_mod_cast hne
  have he' : (∑ j, if u j = true then v j else 0) / (active u : ℝ) = e := Option.some.inj he
  unfold macroZero
  congr 1
  rw [← he']
  field_simp

/-- Running example: the recalls `(1, 2/3, undefined)` with support `(1, 1, 0)` give `5/6` under
`exclude`, `5/9` under `zero` and no value under `nan`. -/
theorem policy_example :
    macroExclude ![true, true, false] ![1, 2 / 3, 0] = some (5 / 6) ∧
    macroZero ![true, true, false] ![1, 2 / 3, 0] = some (5 / 9) ∧
    macroNan ![true, true, false] ![1, 2 / 3, 0] = none := by
  have hact : active ![true, true, false] = 2 := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [macroExclude, hact]
    norm_num [Fin.sum_univ_three]
  · simp only [macroZero]
    norm_num [Fin.sum_univ_three]
  · exact macroNan_none _ _ ⟨2, rfl⟩

end Aggmetrics.DataStream

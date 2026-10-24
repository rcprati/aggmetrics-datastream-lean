import Aggmetrics.Basic

/-!
# The temporal state and Theorem 1 of the data-stream paper, with the temporal part

`Aggmetrics.DataStream.temporal_decomposability` takes the per-class cells as given and needs every
class denominator to be positive. This file formalizes the rest of the statement
(`papers/05-data-stream/outline.tex`, Theorem "Dynamic Temporal Preservation of Linear
Decomposability"):

* the temporal state `C(t) = Yᵀ W P` for any nonnegative weighting (`state`), and its rank-one
  expansion `∑ₖ wₖ yₖ pₖᵀ` (`state_eq_sum`, `state_eq_mul`);
* the per-class selection matrices `S_j` and the congruence `S_j C S_jᵀ` (`sel`, `classTable`), with
  the four cells `TP, FN, FP, TN` read off from `C` (`classTable_TP` and its three siblings);
* the commutation of the temporal operator with the selection matrices (`classTable_state`);
* the theorem itself, with the paper's hypotheses `0 ≤ a ≤ b`, a positive pooled denominator and
  classes with a zero denominator omitted (`temporal_decomposability_matrix`,
  `temporal_decomposability_stream`);
* the weight families (exponential fading, sliding window) and their recurrences
  (`fadeState_eq_state`, `window_recurrence`);
* the exact discrete form of the drift decomposition (`discrete_decomposition`).
-/

open Finset Matrix

namespace Aggmetrics.DataStream

/-! ### A ratio of sums, allowing classes with a zero denominator -/

/-- Generalization of `weighted_ratio_mixture`: classes whose denominator is zero are allowed, if
their numerator is zero too, and then carry weight zero. -/
theorem weighted_ratio_mixture_nonneg {m : ℕ} (num den : Fin m → ℝ)
    (hnum : ∀ j, den j = 0 → num j = 0) (hpos : 0 < ∑ j, den j) :
    (∑ j, num j) / (∑ j, den j)
      = ∑ j, (den j / ∑ k, den k) * (num j / den j) := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : den j = 0
  · simp [hj, hnum j hj]
  · field_simp [hj, hpos.ne']

/-! ### The temporal state and the selection matrices -/

/-- Rank-one contribution `y pᵀ` of one instance. -/
def outer {m : ℕ} (y p : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => y a * p b

/-- Temporal state `C = Yᵀ W P = ∑ₖ wₖ yₖ pₖᵀ` for the weights `w`, the label vectors `y` and the
prediction vectors `p` of `n` instances. -/
def state {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k, w k • outer (y k) (p k)

theorem state_apply {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) (a b : Fin m) :
    state w y p a b = ∑ k, w k * (y k a * p k b) := by
  simp [state, outer, Matrix.sum_apply]

/-- `C = Yᵀ W P` as a matrix product. -/
theorem state_eq_mul {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) :
    state w y p = (Matrix.of y)ᵀ * Matrix.diagonal w * Matrix.of p := by
  ext a b
  simp [state_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm]

/-- The selection matrix `S_j ∈ ℝ^{2×m}`: first row `e_j`, second row `1 - e_j`. -/
def sel {m : ℕ} (j : Fin m) : Matrix (Fin 2) (Fin m) ℝ :=
  Matrix.of fun r l =>
    if r = 0 then (if l = j then 1 else 0) else (if l = j then 0 else 1)

/-- The `2 × 2` per-class table `S_j C S_jᵀ`, with cells `[TP FN; FP TN]`. -/
def classTable {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : Matrix (Fin 2) (Fin 2) ℝ :=
  sel j * C * (sel j)ᵀ

theorem sel_nonneg {m : ℕ} (j : Fin m) (r : Fin 2) (l : Fin m) : 0 ≤ sel j r l := by
  simp only [sel, Matrix.of_apply]
  split_ifs <;> norm_num

/-- Commutation: the congruence `S_j · S_jᵀ` is linear in the state. -/
theorem classTable_sum {m n : ℕ} (c : Fin n → ℝ) (C : Fin n → Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable (∑ k, c k • C k) j = ∑ k, c k • classTable (C k) j := by
  simp [classTable, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The temporal operator commutes with the selection matrices: the per-class table of the state
is the same weighted sum of the per-class tables of the instances. -/
theorem classTable_state {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) (j : Fin m) :
    classTable (state w y p) j = ∑ k, w k • classTable (outer (y k) (p k)) j :=
  classTable_sum w (fun k => outer (y k) (p k)) j

theorem classTable_nonneg {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : ∀ a b, 0 ≤ C a b)
    (j : Fin m) (r s : Fin 2) : 0 ≤ classTable C j r s := by
  simp only [classTable, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (sel_nonneg j r a) (hC a b)) (sel_nonneg j s b)

theorem state_nonneg {m n : ℕ} {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) {y p : Fin n → Fin m → ℝ}
    (hy : ∀ k a, 0 ≤ y k a) (hp : ∀ k a, 0 ≤ p k a) (a b : Fin m) : 0 ≤ state w y p a b := by
  rw [state_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (mul_nonneg (hy k a) (hp k b))

/-! ### The four cells of a class table -/

theorem classTable_TP {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 0 0 = C j j := by
  simp [classTable, sel, Matrix.mul_apply, Matrix.transpose_apply]

theorem classTable_apply {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) (r s : Fin 2) :
    classTable C j r s = ∑ b, (∑ a, sel j r a * C a b) * sel j s b := by
  simp [classTable, Matrix.mul_apply, Matrix.transpose_apply]

theorem sel_zero {m : ℕ} (j l : Fin m) : sel j 0 l = if l = j then 1 else 0 := by simp [sel]

theorem sel_one {m : ℕ} (j l : Fin m) : sel j 1 l = if l = j then 0 else 1 := by simp [sel]

theorem sum_ne_mul {m : ℕ} (f : Fin m → ℝ) (j : Fin m) :
    ∑ x, (if x = j then (0 : ℝ) else 1) * f x = ∑ x ∈ univ.erase j, f x := by
  have h1 : ∑ x ∈ univ.erase j, (if x = j then (0 : ℝ) else 1) * f x
      = ∑ x, (if x = j then (0 : ℝ) else 1) * f x :=
    Finset.sum_subset (Finset.erase_subset j univ) (fun x _ hx => by
      have : x = j := by simpa using hx
      simp [this])
  rw [← h1]
  exact Finset.sum_congr rfl (fun x hx => by simp [Finset.ne_of_mem_erase hx])

theorem classTable_FN {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 0 1 = ∑ b ∈ univ.erase j, C j b := by
  rw [classTable_apply]
  have : ∀ b, (∑ a, sel j 0 a * C a b) = C j b := fun b => by simp [sel_zero]
  simp only [this, sel_one]
  rw [← sum_ne_mul (fun b => C j b) j]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem classTable_FP {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 1 0 = ∑ a ∈ univ.erase j, C a j := by
  rw [classTable_apply]
  have : ∀ b, (∑ a, sel j 1 a * C a b) = ∑ a ∈ univ.erase j, C a b := fun b => by
    simp only [sel_one]
    exact sum_ne_mul (fun a => C a b) j
  simp only [this, sel_zero]
  simp

theorem classTable_TN {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 1 1 = ∑ a ∈ univ.erase j, ∑ b ∈ univ.erase j, C a b := by
  rw [classTable_apply]
  have : ∀ b, (∑ a, sel j 1 a * C a b) = ∑ a ∈ univ.erase j, C a b := fun b => by
    simp only [sel_one]
    exact sum_ne_mul (fun a => C a b) j
  simp only [this]
  simp only [sel_one]
  rw [show (∑ b, (∑ a ∈ univ.erase j, C a b) * (if b = j then (0 : ℝ) else 1))
      = ∑ b, (if b = j then (0 : ℝ) else 1) * ∑ a ∈ univ.erase j, C a b from
        Finset.sum_congr rfl fun b _ => mul_comm _ _,
    sum_ne_mul (fun b => ∑ a ∈ univ.erase j, C a b) j]
  exact Finset.sum_comm

/-! ### Linear-fractional measures on a class table -/

/-- A linear form `⟨a, v⟩` on the cells `v = (TP, FN, FP, TN)` of a `2 × 2` table. -/
def lin (a : Fin 4 → ℝ) (T : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  a 0 * T 0 0 + a 1 * T 0 1 + a 2 * T 1 0 + a 3 * T 1 1

/-- The linear-fractional measure `⟨a,v⟩ / ⟨b,v⟩`. -/
noncomputable def measure (a b : Fin 4 → ℝ) (T : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  lin a T / lin b T

theorem lin_sum {m : ℕ} (a : Fin 4 → ℝ) (T : Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    lin a (∑ j, T j) = ∑ j, lin a (T j) := by
  simp [lin, Matrix.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]

theorem lin_nonneg {a : Fin 4 → ℝ} (ha : ∀ i, 0 ≤ a i) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : ∀ r s, 0 ≤ T r s) : 0 ≤ lin a T := by
  unfold lin
  have := ha 0; have := ha 1; have := ha 2; have := ha 3
  have := hT 0 0; have := hT 0 1; have := hT 1 0; have := hT 1 1
  positivity

theorem lin_le {a b : Fin 4 → ℝ} (hab : ∀ i, a i ≤ b i) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : ∀ r s, 0 ≤ T r s) : lin a T ≤ lin b T := by
  unfold lin
  have h0 := mul_le_mul_of_nonneg_right (hab 0) (hT 0 0)
  have h1 := mul_le_mul_of_nonneg_right (hab 1) (hT 0 1)
  have h2 := mul_le_mul_of_nonneg_right (hab 2) (hT 1 0)
  have h3 := mul_le_mul_of_nonneg_right (hab 3) (hT 1 1)
  linarith

/-! ### Theorem 1, with the temporal part -/

/-- **Dynamic Temporal Preservation of Linear Decomposability**, matrix form. For a nonnegative
state `C`, a measure `⟨a,v⟩/⟨b,v⟩` with `0 ≤ a ≤ b` and a positive pooled denominator, the measure
of the pooled per-class tables `∑ⱼ S_j C S_jᵀ` equals the denominator-weighted average of the
per-class measures; classes with a zero denominator get weight zero. -/
theorem temporal_decomposability_matrix {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos : 0 < ∑ j, lin b (classTable C j)) :
    measure a b (∑ j, classTable C j)
      = ∑ j, (lin b (classTable C j) / ∑ l, lin b (classTable C l))
          * measure a b (classTable C j) := by
  unfold measure
  rw [lin_sum, lin_sum]
  refine weighted_ratio_mixture_nonneg (fun j => lin a (classTable C j))
    (fun j => lin b (classTable C j)) (fun j hj => ?_) hpos
  have h0 := lin_nonneg ha (classTable_nonneg hC j)
  have h1 := lin_le hab (classTable_nonneg hC j)
  have hj' : lin b (classTable C j) = 0 := hj
  show lin a (classTable C j) = 0
  linarith

/-- The same for the temporal state `Yᵀ W P` of a stream, for **any** nonnegative weighting `w`
and nonnegative label and prediction vectors. -/
theorem temporal_decomposability_stream {m n : ℕ} (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (y p : Fin n → Fin m → ℝ) (hy : ∀ k a, 0 ≤ y k a) (hp : ∀ k a, 0 ≤ p k a)
    (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos : 0 < ∑ j, lin b (classTable (state w y p) j)) :
    measure a b (∑ j, classTable (state w y p) j)
      = ∑ j, (lin b (classTable (state w y p) j) / ∑ l, lin b (classTable (state w y p) l))
          * measure a b (classTable (state w y p) j) :=
  temporal_decomposability_matrix _ (state_nonneg hw hy hp) a b ha hab hpos

/-! ### Weight families and their recurrences -/

/-- Exponential-fading weight `(1-α) α^{n-1-k}` of instance `k` (0-indexed) in a state of `n`
instances. -/
def fadeWeight (α : ℝ) (n k : ℕ) : ℝ := (1 - α) * α ^ (n - 1 - k)

theorem fadeWeight_nonneg {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n k : ℕ) : 0 ≤ fadeWeight α n k :=
  mul_nonneg (by linarith) (pow_nonneg h0 _)

/-- The total mass of the fading weights is `1 - α^n`. -/
theorem fadeWeight_sum (α : ℝ) (n : ℕ) : ∑ k ∈ range n, fadeWeight α n k = 1 - α ^ n := by
  unfold fadeWeight
  rw [← Finset.mul_sum]
  have h := Finset.sum_range_reflect (fun j => α ^ j) n
  rw [h, mul_comm]
  exact geom_sum_mul_neg α n

/-- State after `n` instances, by the fading recurrence `C(n+1) = α C(n) + (1-α) y pᵀ`. -/
def fadeState {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 0
  | n + 1 => α • fadeState α y p n + (1 - α) • outer (y n) (p n)

/-- The fading recurrence computes the weighted sum with the fading weights. -/
theorem fadeState_eq_sum {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    fadeState α y p n = ∑ k ∈ range n, fadeWeight α n k • outer (y k) (p k) := by
  induction n with
  | zero => simp [fadeState]
  | succ n ih =>
    rw [fadeState, ih, Finset.sum_range_succ, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < n := Finset.mem_range.mp hk
      rw [smul_smul]
      congr 1
      unfold fadeWeight
      have : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [this, pow_succ]
      ring
    · simp [fadeWeight]

/-- The fading recurrence is the temporal state `Yᵀ W P` with the fading weights. -/
theorem fadeState_eq_state {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    fadeState α y p n
      = state (fun k : Fin n => fadeWeight α n k) (fun k => y k) (fun k => p k) := by
  rw [fadeState_eq_sum]
  unfold state
  exact (Fin.sum_univ_eq_sum_range (fun k => fadeWeight α n k • outer (y k) (p k)) n).symm

/-- Sliding-window weight `1/W` on the last `W` of `n` instances. -/
noncomputable def winWeight (W n k : ℕ) : ℝ := if n - W ≤ k then 1 / (W : ℝ) else 0

theorem winWeight_nonneg (W n k : ℕ) : 0 ≤ winWeight W n k := by
  unfold winWeight
  split_ifs <;> positivity

/-- Once the window has filled, its weights sum to one. -/
theorem winWeight_sum {W n : ℕ} (hW : 0 < W) (hWn : W ≤ n) :
    ∑ k ∈ range n, winWeight W n k = 1 := by
  unfold winWeight
  rw [← Finset.sum_filter]
  have hf : (range n).filter (fun k => n - W ≤ k) = Ico (n - W) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have : n - (n - W) = W := by omega
  rw [this]
  have hW' : (W : ℝ) ≠ 0 := by positivity
  field_simp

/-- State of the sliding window after `n` instances. -/
noncomputable def winState {m : ℕ} (W : ℕ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ range n, winWeight W n k • outer (y k) (p k)

/-- The window recurrence `C(n+1) = C(n) + (1/W)(y_n p_nᵀ - y_{n-W} p_{n-W}ᵀ)`. -/
theorem window_recurrence {m : ℕ} {W n : ℕ} (hW : 0 < W) (hWn : W ≤ n) (y p : ℕ → Fin m → ℝ) :
    winState W y p (n + 1)
      = winState W y p n + (1 / (W : ℝ)) • (outer (y n) (p n) - outer (y (n - W)) (p (n - W))) := by
  unfold winState
  rw [Finset.sum_range_succ]
  have hstep : ∀ k ∈ range n, winWeight W (n + 1) k • outer (y k) (p k)
      = winWeight W n k • outer (y k) (p k)
        - (if k = n - W then (1 / (W : ℝ)) • outer (y k) (p k) else 0) := by
    intro k hk
    unfold winWeight
    by_cases h1 : k = n - W
    · subst h1
      have e1 : ¬ (n + 1 - W ≤ n - W) := by omega
      have e2 : n - W ≤ n - W := le_refl _
      simp [e1, e2]
    · have : (n + 1 - W ≤ k) ↔ (n - W ≤ k) := by omega
      by_cases h2 : n - W ≤ k
      · simp [this.mpr h2, h2, h1]
      · simp [(not_congr this).mpr h2, h2, h1]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hmem : n - W ∈ range n := Finset.mem_range.mpr (by omega)
  rw [if_pos hmem]
  have hlast : winWeight W (n + 1) n = 1 / (W : ℝ) := by
    unfold winWeight
    rw [if_pos (by omega)]
  rw [hlast, smul_sub]
  abel

/-! ### The drift decomposition, exactly -/

/-- Exact discrete product rule: `Δ(ωM) = ω̄ ΔM + Δω M̄` with mid-point values. -/
theorem discrete_decomposition {m : ℕ} (ω0 ω1 M0 M1 : Fin m → ℝ) :
    ∑ j, (ω1 j * M1 j - ω0 j * M0 j)
      = ∑ j, ((ω0 j + ω1 j) / 2) * (M1 j - M0 j)
        + ∑ j, (ω1 j - ω0 j) * ((M0 j + M1 j) / 2) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The denominator weight of class `j` in the state `C`. -/
noncomputable def omega {m : ℕ} (b : Fin 4 → ℝ) (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : ℝ :=
  lin b (classTable C j) / ∑ l, lin b (classTable C l)

/-- The change of the pooled measure between two states splits into an intrinsic part (change of
the per-class measures, mid-point weights) and a prevalence part (change of the weights, mid-point
measures), exactly. This is Eq. `drift_decomposition` of the paper. -/
theorem micro_change_decomposition {m : ℕ} (C0 C1 : Matrix (Fin m) (Fin m) ℝ)
    (hC0 : ∀ a b, 0 ≤ C0 a b) (hC1 : ∀ a b, 0 ≤ C1 a b)
    (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos0 : 0 < ∑ j, lin b (classTable C0 j)) (hpos1 : 0 < ∑ j, lin b (classTable C1 j)) :
    measure a b (∑ j, classTable C1 j) - measure a b (∑ j, classTable C0 j)
      = ∑ j, ((omega b C0 j + omega b C1 j) / 2)
            * (measure a b (classTable C1 j) - measure a b (classTable C0 j))
        + ∑ j, (omega b C1 j - omega b C0 j)
            * ((measure a b (classTable C0 j) + measure a b (classTable C1 j)) / 2) := by
  rw [temporal_decomposability_matrix C1 hC1 a b ha hab hpos1,
    temporal_decomposability_matrix C0 hC0 a b ha hab hpos0, ← Finset.sum_sub_distrib]
  exact discrete_decomposition (omega b C0) (omega b C1)
    (fun j => measure a b (classTable C0 j)) (fun j => measure a b (classTable C1 j))

end Aggmetrics.DataStream

import Aggmetrics.DataStream
import Aggmetrics.DataStreamDelay

/-!
# Eviction inside Algorithm 1 and the bound on the queue (data-stream paper, Section 4)

`Aggmetrics.DataStreamDelay.algState_eq` proves the invariant of Algorithm 1 without eviction.
Formalized here:

* the algorithm **with** eviction (`algStateE`): a correction is applied only if the entry of the
  queue has not been evicted, that is, if its fading weight at the previous step is still at least
  `ε`;
* the **exact** difference between the two states, the sum of the discarded corrections at their
  final weights (`algState_sub_algStateE`, `lostState`);
* two bounds on that difference per entry: the tail mass `α^s` (`eviction_entry_bound`), where `s`
  is the first age whose weight is below `ε`, and `m ε` for `m` discarded corrections
  (`eviction_entry_bound_count`);
* the **bound on the queue**: at most `N` entries survive eviction whenever `(1-α) α^N < ε`
  (`queue_card_le`), with an explicit `N ≤ n_eff · ln(1/(n_eff ε)) + 2` (`evict_age_exists`).
-/

open Finset Matrix
open scoped Classical

namespace Aggmetrics.DataStream

theorem fadeWeight_antitone {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {n n' k : ℕ} (hnn : n ≤ n') :
    fadeWeight α n' k ≤ fadeWeight α n k := by
  unfold fadeWeight
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact pow_le_pow_of_le_one h0 h1 (by omega)

/-! ### The queue is bounded -/

/-- At most `N` entries of the queue survive eviction, whenever the weight of an entry of age `N`
is below `ε`. -/
theorem queue_card_le {α ε : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {N : ℕ}
    (hN : (1 - α) * α ^ N < ε) (n : ℕ) (P : ℕ → Prop) :
    ((range n).filter (fun k => P k ∧ ε ≤ fadeWeight α n k)).card ≤ N := by
  have hinj : Set.InjOn (fun k => n - 1 - k)
      ↑((range n).filter (fun k => P k ∧ ε ≤ fadeWeight α n k)) := by
    intro k hk k' hk' h
    have h1 := (Finset.mem_filter.mp hk).1
    have h2 := (Finset.mem_filter.mp hk').1
    simp only [Finset.mem_range] at h1 h2
    simp only at h
    omega
  have hmaps : ∀ k ∈ (range n).filter (fun k => P k ∧ ε ≤ fadeWeight α n k),
      (fun k => n - 1 - k) k ∈ range N := by
    intro k hk
    obtain ⟨hkr, hP, hε⟩ := Finset.mem_filter.mp hk
    rw [Finset.mem_range]
    by_contra hlt
    push_neg at hlt
    have : fadeWeight α n k ≤ (1 - α) * α ^ N := by
      unfold fadeWeight
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1.le hlt) (by linarith)
    linarith
  calc _ ≤ (range N).card :=
        Finset.card_le_card_of_injOn _
          (by first
            | exact fun k hk => hmaps k hk
            | exact fun k hk => Finset.mem_coe.mpr (hmaps k (Finset.mem_coe.mp hk))) hinj
    _ = N := Finset.card_range N

/-- An age `N` with `(1-α) α^N < ε` exists, and it is at most `n_eff · ln(1/(n_eff ε)) + 2`, with
`n_eff = 1/(1-α)`. -/
theorem evict_age_exists {α ε : ℝ} (h0 : 0 < α) (h1 : α < 1) (hε : 0 < ε) :
    ∃ N : ℕ, (1 - α) * α ^ N < ε ∧
      (N : ℝ) ≤ max (Real.log ((1 - α) / ε)) 0 / (1 - α) + 2 := by
  have hpos : 0 < 1 - α := by linarith
  set x := Real.log ((1 - α) / ε) / (-Real.log α) with hx
  have hlogα : Real.log α < 0 := Real.log_neg h0 h1
  refine ⟨⌈x⌉₊ + 1, ?_, ?_⟩
  · have hW : ((⌈x⌉₊ : ℕ) : ℝ) ≥ Real.log (1 / (ε / (1 - α))) / (-Real.log (1 - (1 - α))) := by
      rw [one_div_div, sub_sub_cancel]
      exact Nat.le_ceil x
    have hsz := window_sizing_rule (1 - α) (ε / (1 - α)) hpos (by linarith)
      (div_pos hε hpos) ⌈x⌉₊ hW
    rw [sub_sub_cancel] at hsz
    have h3 : α ^ (⌈x⌉₊ + 1) < ε / (1 - α) := by
      refine lt_of_lt_of_le ?_ hsz
      rw [pow_succ]
      nlinarith [pow_pos h0 ⌈x⌉₊]
    calc (1 - α) * α ^ (⌈x⌉₊ + 1) < (1 - α) * (ε / (1 - α)) :=
          mul_lt_mul_of_pos_left h3 hpos
      _ = ε := by field_simp
  · push_cast
    by_cases hxn : x ≤ 0
    · have : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hxn
      rw [this]
      have : 0 ≤ max (Real.log ((1 - α) / ε)) 0 / (1 - α) := by positivity
      simp only [Nat.cast_zero]
      linarith
    · push_neg at hxn
      have hceil := Nat.ceil_lt_add_one hxn.le
      have hL : 0 < Real.log ((1 - α) / ε) := by
        by_contra hnot
        push_neg at hnot
        have : x ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnot (by linarith)
        linarith
      have hle : 1 - α ≤ -Real.log α := by
        have := Real.log_le_sub_one_of_pos h0
        linarith
      have hxle : x ≤ Real.log ((1 - α) / ε) / (1 - α) :=
        div_le_div_of_nonneg_left hL.le hpos hle
      rw [max_eq_left hL.le]
      linarith

/-! ### Algorithm 1 with eviction -/

/-- Algorithm 1, exponential fading, **with** eviction: the correction of an entry that arrived
before the current step is applied only if its weight at the previous step is at least `ε`. -/
noncomputable def algStateE {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 0
  | n + 1 =>
      (α • algStateE α ε y yt p aud arr n + (1 - α) • outer (yt n) (p n))
        + ∑ k ∈ (range (n + 1)).filter
            (fun k => aud k ∧ arr k = n + 1 ∧ (k = n ∨ ε ≤ fadeWeight α n k)),
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k))

/-- The correction of instance `k` is discarded: its label arrived (`arr k ≤ n`) after the entry
had been evicted (its weight at the previous step, `arr k - 1`, was below `ε`). -/
def discarded (α ε : ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ) (n k : ℕ) : Prop :=
  aud k ∧ arr k ≤ n ∧ k + 1 ≠ arr k ∧ fadeWeight α (arr k - 1) k < ε

/-- The discarded corrections, at their final weights in the state after `n` steps. -/
noncomputable def lostState {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ range n, if discarded α ε aud arr n k then
    fadeWeight α n k • (outer (y k) (p k) - outer (yt k) (p k)) else 0

/-- **Exact effect of eviction.** The state of the algorithm without eviction exceeds the state
with eviction by the sum of the discarded corrections. -/
theorem algState_sub_algStateE {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (n : ℕ) :
    algState α y yt p aud arr n - algStateE α ε y yt p aud arr n
      = lostState α ε y yt p aud arr n := by
  induction n with
  | zero => simp [algState, algStateE, lostState]
  | succ n ih =>
    rw [algState, algStateE]
    have hS : (∑ k ∈ (range (n + 1)).filter (fun k => aud k ∧ arr k = n + 1),
          fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)))
        - (∑ k ∈ (range (n + 1)).filter
            (fun k => aud k ∧ arr k = n + 1 ∧ (k = n ∨ ε ≤ fadeWeight α n k)),
          fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)))
        = ∑ k ∈ range n, if (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) then
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0 := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_range_succ]
      have hlast : ((if aud n ∧ arr n = n + 1 then
            fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0)
          - (if aud n ∧ arr n = n + 1 ∧ (n = n ∨ ε ≤ fadeWeight α n n) then
            fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0)) = 0 := by
        by_cases h : aud n ∧ arr n = n + 1
        · simp [h]
        · simp [h]
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkn : k ≠ n := by
        have := Finset.mem_range.mp hk
        omega
      by_cases h1 : aud k ∧ arr k = n + 1
      · by_cases h2 : ε ≤ fadeWeight α n k
        · have h2' : ¬ fadeWeight α n k < ε := not_lt.mpr h2
          simp [h1, h2, h2', hkn]
        · have h2' : fadeWeight α n k < ε := not_le.mp h2
          simp [h1, h2, h2', hkn]
      · have a1 : ¬ (aud k ∧ arr k = n + 1 ∧ (k = n ∨ ε ≤ fadeWeight α n k)) :=
          fun h => h1 ⟨h.1, h.2.1⟩
        have a2 : ¬ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) :=
          fun h => h1 ⟨h.1, h.2.1⟩
        rw [if_neg h1, if_neg a1, if_neg a2]
        simp
    have hstep : ∀ k ∈ range n,
        (if discarded α ε aud arr (n + 1) k then
          fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0)
        = α • (if discarded α ε aud arr n k then
            fadeWeight α n k • (outer (y k) (p k) - outer (yt k) (p k)) else 0)
          + (if (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) then
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0) := by
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hak := harr k
      rw [fadeWeight_succ hkn]
      by_cases hc1 : arr k ≤ n
      · have e1 : discarded α ε aud arr (n + 1) k ↔ discarded α ε aud arr n k := by
          unfold discarded
          constructor
          · rintro ⟨a, b, c, d⟩
            exact ⟨a, hc1, c, d⟩
          · rintro ⟨a, b, c, d⟩
            exact ⟨a, by omega, c, d⟩
        have e2 : ¬ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) := by
          rintro ⟨_, h, _⟩
          omega
        by_cases hd : discarded α ε aud arr n k
        · rw [if_pos (e1.mpr hd), if_pos hd, if_neg e2, add_zero, smul_smul]
        · rw [if_neg (fun h => hd (e1.mp h)), if_neg hd, if_neg e2]
          simp
      · by_cases hc2 : arr k = n + 1
        · have e1 : ¬ discarded α ε aud arr n k := by
            unfold discarded
            rintro ⟨_, h, _⟩
            omega
          have e2 : discarded α ε aud arr (n + 1) k
              ↔ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) := by
            unfold discarded
            constructor
            · rintro ⟨a, b, c, d⟩
              refine ⟨a, hc2, ?_⟩
              rw [hc2] at d
              simpa using d
            · rintro ⟨a, b, d⟩
              refine ⟨a, by omega, by omega, ?_⟩
              rw [b]
              simpa using d
          rw [if_neg e1]
          simp only [smul_zero, zero_add]
          by_cases hh : (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε)
          · rw [if_pos (e2.mpr hh), if_pos hh]
          · rw [if_neg (fun h => hh (e2.mp h)), if_neg hh]
        · have e1 : ¬ discarded α ε aud arr n k := by
            unfold discarded
            rintro ⟨_, h, _⟩
            omega
          have e2 : ¬ discarded α ε aud arr (n + 1) k := by
            unfold discarded
            rintro ⟨_, h, _⟩
            omega
          have e3 : ¬ (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) := by
            rintro ⟨_, h, _⟩
            omega
          rw [if_neg e1, if_neg e2, if_neg e3]
          simp
    have hlost : lostState α ε y yt p aud arr (n + 1)
        = α • lostState α ε y yt p aud arr n
          + ∑ k ∈ range n, if (aud k ∧ arr k = n + 1 ∧ fadeWeight α n k < ε) then
              fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k)) else 0 := by
      unfold lostState
      rw [Finset.sum_range_succ, Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
        ← Finset.smul_sum]
      have hlastn : (if discarded α ε aud arr (n + 1) n then
          fadeWeight α (n + 1) n • (outer (y n) (p n) - outer (yt n) (p n)) else 0) = 0 := by
        rw [if_neg]
        unfold discarded
        rintro ⟨_, h, h', _⟩
        have := harr n
        omega
      rw [hlastn, add_zero]
    have hA : algState α y yt p aud arr n
        = algStateE α ε y yt p aud arr n + lostState α ε y yt p aud arr n := by
      rw [← ih]
      abel
    rw [hlost, hA, ← hS]
    simp only [smul_add]
    abel

/-- The state with eviction is the unified state minus the discarded corrections. -/
theorem algStateE_eq {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (n : ℕ) :
    algStateE α ε y yt p aud arr n
      = (∑ k ∈ range n, fadeWeight α n k • outer (zvec y yt aud arr n k) (p k))
        - lostState α ε y yt p aud arr n := by
  rw [← algState_eq α y yt p aud arr harr n, ← algState_sub_algStateE α ε y yt p aud arr harr n]
  abel

/-! ### Bounds on the effect of eviction -/

/-- The weighted sum of bounded terms over instances of age at least `s` is at most `α^s`. -/
theorem evicted_sum_bound {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (n s : ℕ) (D : Finset ℕ)
    (hD : ∀ k ∈ D, k < n ∧ s ≤ n - 1 - k) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1) :
    |∑ k ∈ D, fadeWeight α n k * d k| ≤ α ^ s := by
  have h := evicted_change_bound h0 h1 s (D.image (fun k => n - 1 - k))
    (by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      exact (hD k hk).2)
    (fun j => d (n - 1 - j)) (fun j => hd _)
  rw [Finset.sum_image (by
    intro k hk k' hk' hkk
    have := hD k hk
    have := hD k' hk'
    simp only at hkk
    omega)] at h
  have heq : ∑ k ∈ D, fadeWeight α n k * d k
      = ∑ k ∈ D, (1 - α) * α ^ (n - 1 - k) * d (n - 1 - (n - 1 - k)) :=
    Finset.sum_congr rfl (fun k hk => by
      have := (hD k hk).1
      have e : n - 1 - (n - 1 - k) = k := by omega
      rw [e]
      rfl)
  rw [heq]
  exact h

theorem lost_entry {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (n : ℕ) (a b : Fin m) :
    (lostState α ε y yt p aud arr n) a b
      = ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k),
          fadeWeight α n k * ((y k a - yt k a) * p k b) := by
  unfold lostState
  rw [Matrix.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : discarded α ε aud arr n k
  · simp only [h, if_true, Matrix.smul_apply, Matrix.sub_apply, outer, Matrix.of_apply,
      smul_eq_mul]
    ring
  · simp [h]

theorem abs_delta_le {m : ℕ} (y yt p : ℕ → Fin m → ℝ)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1) (k : ℕ) (a b : Fin m) :
    |(y k a - yt k a) * p k b| ≤ 1 := by
  have h1 := hy k a
  have h2 := hyt k a
  have h3 := hp k b
  have hd : |y k a - yt k a| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hpp : |p k b| ≤ 1 := abs_le.mpr ⟨by linarith [h3.1], h3.2⟩
  calc |(y k a - yt k a) * p k b| = |y k a - yt k a| * |p k b| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul hd hpp (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **Eviction changes each entry of the state by at most the tail mass `α^s`**, where `s` is the
first age whose weight is below `ε`, if the label and prediction vectors have entries in `[0,1]`. -/
theorem eviction_entry_bound {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (h0 : 0 ≤ α) (h1 : α < 1)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1)
    {s : ℕ} (hs : ∀ j, (1 - α) * α ^ j < ε → s ≤ j) (n : ℕ) (a b : Fin m) :
    |(algState α y yt p aud arr n - algStateE α ε y yt p aud arr n) a b| ≤ α ^ s := by
  rw [algState_sub_algStateE α ε y yt p aud arr harr n, lost_entry]
  refine evicted_sum_bound h0 h1 n s _ ?_ (fun k => (y k a - yt k a) * p k b)
    (fun k => abs_delta_le y yt p hy hyt hp k a b)
  intro k hk
  obtain ⟨hkr, hd⟩ := Finset.mem_filter.mp hk
  refine ⟨Finset.mem_range.mp hkr, ?_⟩
  obtain ⟨ha, harn, hne, hw⟩ := hd
  have hakk := harr k
  have hj : (1 - α) * α ^ (arr k - 1 - 1 - k) < ε := by
    have e : fadeWeight α (arr k - 1) k = (1 - α) * α ^ (arr k - 1 - 1 - k) := rfl
    rw [← e]
    exact hw
  have := hs _ hj
  omega

/-- **Eviction changes each entry by less than `ε` per discarded correction.** -/
theorem eviction_entry_bound_count {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (h0 : 0 ≤ α) (h1 : α < 1)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1) (n : ℕ) (a b : Fin m) :
    |(algState α y yt p aud arr n - algStateE α ε y yt p aud arr n) a b|
      ≤ ((range n).filter (fun k => discarded α ε aud arr n k)).card * ε := by
  rw [algState_sub_algStateE α ε y yt p aud arr harr n, lost_entry]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k),
        |fadeWeight α n k * ((y k a - yt k a) * p k b)|
      ≤ ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k), ε := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        obtain ⟨hkr, hd⟩ := Finset.mem_filter.mp hk
        obtain ⟨ha, harn, hne, hw⟩ := hd
        have hW0 : 0 ≤ fadeWeight α n k := fadeWeight_nonneg h0 h1.le n k
        have hWε : fadeWeight α n k < ε :=
          lt_of_le_of_lt (fadeWeight_antitone h0 h1.le (by omega : arr k - 1 ≤ n)) hw
        rw [abs_mul, abs_of_nonneg hW0]
        exact (mul_le_of_le_one_right hW0 (abs_delta_le y yt p hy hyt hp k a b)).trans hWε.le
    _ = ((range n).filter (fun k => discarded α ε aud arr n k)).card * ε := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Aggmetrics.DataStream

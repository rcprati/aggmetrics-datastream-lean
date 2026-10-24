import Aggmetrics.DataStreamTemporal

/-!
# The running example of the data-stream paper, checked in Lean

The stream of Example "Running example: the stream and its temporal state" has `8` instances and
three classes `A, B, C` (`0, 1, 2`), true labels `A B A C B A B B` and predictions `A B B C B A C B`.
This file recomputes the temporal states and the pooled and weighted macro precision of the paper
with `norm_num`, so that the numbers printed in the paper are statements about the definitions of
`Aggmetrics.DataStreamTemporal`.
-/

open Finset Matrix

namespace Aggmetrics.DataStream.RunningExample

/-- True labels (classes `A, B, C = 0, 1, 2`). -/
def lab : ℕ → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 0 | 6 => 1 | 7 => 1 | _ => 0

/-- Predicted labels. -/
def pre : ℕ → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | 5 => 0 | 6 => 2 | 7 => 1 | _ => 0

/-- One-hot label vectors. -/
noncomputable def y : ℕ → Fin 3 → ℝ := fun k j => if lab k = j then 1 else 0

/-- One-hot prediction vectors. -/
noncomputable def p : ℕ → Fin 3 → ℝ := fun k j => if pre k = j then 1 else 0

/-- Exponential fading with `α = 1/2`: the state after the first four instances. -/
theorem fade_state_four :
    fadeState (1 / 2) y p 4 = !![1 / 16, 1 / 4, 0; 0, 1 / 8, 0; 0, 0, 1 / 2] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [fadeState, outer, y, p, lab, pre] <;> norm_num

/-- Sliding window `W = 4`: the state at `t = 8` covers instances `5` to `8`. -/
theorem window_state_eight :
    winState 4 y p 8 = !![1 / 4, 0, 0; 0, 1 / 2, 1 / 4; 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [winState, winWeight, Finset.sum_range_succ, outer, y, p, lab, pre] <;> norm_num

/-- Coefficients of precision, `TP / (TP + FP)`, on the cells `(TP, FN, FP, TN)`. -/
def aPrec : Fin 4 → ℝ := ![1, 0, 0, 0]

def bPrec : Fin 4 → ℝ := ![1, 0, 1, 0]

/-- The per-class tables of the window state at `t = 8`. -/
theorem window_tables :
    classTable (winState 4 y p 8) 0 = !![1 / 4, 0; 0, 3 / 4] ∧
    classTable (winState 4 y p 8) 1 = !![1 / 2, 1 / 4; 0, 1 / 4] ∧
    classTable (winState 4 y p 8) 2 = !![0, 0; 1 / 4, 3 / 4] := by
  rw [window_state_eight]
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [classTable, sel, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- Pooled precision `3/4`, weights `(1/4, 1/2, 1/4)`, per-class precisions `(1, 1, 0)`, the
denominator-weighted macro `3/4` (Theorem 1) and the unweighted macro `2/3`. -/
theorem precision_example :
    measure aPrec bPrec (∑ j, classTable (winState 4 y p 8) j) = 3 / 4 ∧
    (omega bPrec (winState 4 y p 8) 0 = 1 / 4 ∧ omega bPrec (winState 4 y p 8) 1 = 1 / 2 ∧
      omega bPrec (winState 4 y p 8) 2 = 1 / 4) ∧
    (measure aPrec bPrec (classTable (winState 4 y p 8) 0) = 1 ∧
      measure aPrec bPrec (classTable (winState 4 y p 8) 1) = 1 ∧
      measure aPrec bPrec (classTable (winState 4 y p 8) 2) = 0) ∧
    (∑ j, omega bPrec (winState 4 y p 8) j * measure aPrec bPrec (classTable (winState 4 y p 8) j)
      = 3 / 4) ∧
    ((measure aPrec bPrec (classTable (winState 4 y p 8) 0)
      + measure aPrec bPrec (classTable (winState 4 y p 8) 1)
      + measure aPrec bPrec (classTable (winState 4 y p 8) 2)) / 3 = 2 / 3) := by
  obtain ⟨h0, h1, h2⟩ := window_tables
  have hsum : ∑ j, classTable (winState 4 y p 8) j = !![3 / 4, 1 / 4; 1 / 4, 7 / 4] := by
    rw [Fin.sum_univ_three, h0, h1, h2]
    ext r s
    fin_cases r <;> fin_cases s <;> simp <;> norm_num
  have hden : ∀ j, lin bPrec (classTable (winState 4 y p 8) j) = ![1 / 4, 1 / 2, 1 / 4] j := by
    intro j
    fin_cases j
    · simp [lin, bPrec, h0]
    · simp [lin, bPrec, h1] <;> norm_num
    · simp [lin, bPrec, h2]
  have hom : ∀ j, omega bPrec (winState 4 y p 8) j = ![1 / 4, 1 / 2, 1 / 4] j := by
    intro j
    unfold omega
    rw [Fin.sum_univ_three]
    simp only [hden]
    fin_cases j <;> simp <;> norm_num
  have hm0 : measure aPrec bPrec (classTable (winState 4 y p 8) 0) = 1 := by
    simp [measure, lin, aPrec, bPrec, h0]
  have hm1 : measure aPrec bPrec (classTable (winState 4 y p 8) 1) = 1 := by
    simp [measure, lin, aPrec, bPrec, h1]
  have hm2 : measure aPrec bPrec (classTable (winState 4 y p 8) 2) = 0 := by
    simp [measure, lin, aPrec, bPrec, h2]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨hm0, hm1, hm2⟩, ?_, ?_⟩
  · rw [hsum]
    simp [measure, lin, aPrec, bPrec]
    norm_num
  · rw [hom]; simp
  · rw [hom]; simp
  · rw [hom]; simp
  · rw [Fin.sum_univ_three, hm0, hm1, hm2, hom, hom, hom]
    simp
    norm_num
  · rw [hm0, hm1, hm2]
    norm_num

end Aggmetrics.DataStream.RunningExample

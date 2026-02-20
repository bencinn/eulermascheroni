import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-!
# Euler–Mascheroni Constant as an Infinite Sum

This file proves that the Euler–Mascheroni constant can be expressed as
the infinite sum

∑' n, (1 / (n + 1) - log ((n + 2) / (n + 1))).

We conclude that the series sums to `Real.eulerMascheroniConstant`.
-/
namespace EulerMascheroniInfiniteSum

open Filter

/-- Inner sum of the infinite sum definition -/
noncomputable def eulerMascheroni_sum_inner (n : ℕ) :=
  1 / (n + 1) - Real.log ((n + 2) / (n + 1))

lemma eulerMascheroni_sum_inner_nonneg : ∀ n, 0 ≤ eulerMascheroni_sum_inner n := by
  intro n
  unfold eulerMascheroni_sum_inner
  have h_pos : 0 < ((n + 2) : ℝ) / (n + 1) := by positivity
  have h_log := Real.log_le_sub_one_of_pos h_pos
  field_simp at h_log
  simp at h_log
  push_cast at *
  have h_pos' : (0 : ℝ) < n + 1 := by positivity
  rw [mul_comm] at h_log
  rw [← le_div_iff₀ h_pos'] at h_log
  linarith

lemma eulerMascheroni_sum_partial : ∀ N, ∑ k ∈ Finset.range N, eulerMascheroni_sum_inner k
    = (harmonic N : ℝ) - Real.log (N + 1) := by
  intro N
  induction' N with n ih
  · simp
  · rw [Finset.sum_range_succ, ih, harmonic_succ]
    unfold eulerMascheroni_sum_inner
    push_cast
    have h_log : Real.log ((n + 2) / (n + 1)) = Real.log (n + 2) - Real.log (n + 1) := by
      exact Real.log_div (by positivity) (by positivity)
    rw [h_log]
    ring_nf

-- TODO: use Real.eulerMascheroniConstant_lt_two_thirds and Real.eulerMascheroniSeq_lt_eulerMascheroniConstant to get lower upper bound?
lemma eulerMascheroni_sum_bound : ∀ N, ∑ k ∈ Finset.range N, eulerMascheroni_sum_inner k ≤ 1 := by
  intro N
  rw [eulerMascheroni_sum_partial N]
  have := Real.eulerMascheroniSeq_lt_eulerMascheroniSeq' N 1
  rw [Real.eulerMascheroniSeq'_one] at this
  unfold Real.eulerMascheroniSeq at this
  linarith

/-- the infinite sum is equal to `Real.eulerMascheroniConstant` -/
theorem eulerMascheroni_tsum :
  ∑' n, eulerMascheroni_sum_inner n = Real.eulerMascheroniConstant := by
  apply HasSum.tsum_eq
  unfold Real.eulerMascheroniConstant
  rw [Summable.hasSum_iff_tendsto_nat]
  · simp_rw [eulerMascheroni_sum_partial]
    exact Real.tendsto_eulerMascheroniSeq
  · exact summable_of_sum_range_le eulerMascheroni_sum_inner_nonneg eulerMascheroni_sum_bound

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import EulerMascheroni.EulerMascheroniInfiniteSum

/-!
# Antisymmetric definition of the Euler–Mascheroni Constant
We use the previous results of `tendsto_riemannZeta_sub_one_div` to create the antisymmetric definition of `Real.eulerMascheroniConstant`
-/
namespace EulerMascheroniAntisymmetric

open Filter Topology

/-- the inner of the integral series (off by one) -/
noncomputable def eulerMascheroni_inner_int_series (n : ℕ) := 1/(n+1) - ∫ t in (n+1)..(n+2), (1/t)

lemma eulerMascheroni_int_series : Real.eulerMascheroniConstant = ∑' n, eulerMascheroni_inner_int_series n := by
  rw [<-EulerMascheroniInfiniteSum.eulerMascheroni_tsum]
  have this : ∀ (x : ℕ), EulerMascheroniInfiniteSum.eulerMascheroni_sum_inner x = eulerMascheroni_inner_int_series x := by
    unfold EulerMascheroniInfiniteSum.eulerMascheroni_sum_inner eulerMascheroni_inner_int_series
    intro x
    rw [integral_one_div]
    intro h
    rw [Set.mem_uIcc] at h
    cases h <;> linarith
  exact tsum_congr this

/- since we offset by one already, we can just -/
lemma eulerMascheroni_int_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2) :
  0 ≤ 1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x) ∧
  1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x) ≤ 1/((n+1)^2)
  := by
    constructor
    · apply sub_nonneg_of_le
      let g (t : ℝ) := (n+1 : ℝ)^(-x)
      have h_const_int : ∫ (t) in (n + 1)..(n + 2), (n + 1 : ℝ)^(-x) = 1 / (n + 1 : ℝ)^(x) := by
        simp [intervalIntegral.integral_const]
        rw [Real.rpow_neg]
        · grind
        · positivity
      rw [<-h_const_int]
      apply intervalIntegral.integral_mono_on
      · linarith
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div
        · exact continuousOn_const
        · apply ContinuousOn.rpow continuousOn_id continuousOn_const
          grind -- what the fuck
        · intro u hu
          rw [Set.uIcc_of_le (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)] at hu
          have : 0 < u := by linarith [hu.1]
          positivity
      · apply ContinuousOn.intervalIntegrable
        exact continuousOn_const
      · intro t ht
        rw [Real.rpow_neg (by positivity), one_div]
        gcongr
        exact ht.1
    · sorry -- i don't even know if it is true

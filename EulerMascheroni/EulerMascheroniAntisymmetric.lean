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

open Filter Topology MeasureTheory

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
    have h_const_int : ∫ (t) in (n + 1)..(n + 2), (n + 1 : ℝ)^(-x) = 1 / (n + 1 : ℝ)^(x) := by
        simp [intervalIntegral.integral_const]
        rw [Real.rpow_neg]
        · grind
        · positivity
    constructor
    · apply sub_nonneg_of_le
      let g (t : ℝ) := (n+1 : ℝ)^(-x)
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
    · rw [<- h_const_int]
      have h_rhs_int : ∫ (t : ℝ) in (n + 1)..(n + 2), (1 / (n + 1 : ℝ)^2) = 1 / (n + 1 : ℝ)^2 := by
        simp [intervalIntegral.integral_const]
        ring
      have h_int_LHS : IntervalIntegrable (fun u : ℝ ↦ (n + 1 : ℝ)^(-x)) volume (n + 1) (n + 2) := by
        apply ContinuousOn.intervalIntegrable
        exact continuousOn_const

      have h_int_RHS_const : IntervalIntegrable (fun u : ℝ ↦ 1 / (n + 1 : ℝ)^2) volume (n + 1) (n + 2) := by
        apply ContinuousOn.intervalIntegrable
        exact continuousOn_const

      have h_int_RHS_fun : IntervalIntegrable (fun u : ℝ ↦ 1 / u^x) volume (n + 1) (n + 2) := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div
        · exact continuousOn_const
        · apply ContinuousOn.rpow continuousOn_id continuousOn_const
          grind
        · intro u hu
          rw [Set.uIcc_of_le (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)] at hu
          have : 0 < u := by linarith [hu.1]
          positivity

      rw [← intervalIntegral.integral_sub]
      · have inner_h_eq (x_1 : ℝ) (hx1_bound : (n + 1 : ℝ) ≤ x_1) : (n + 1) ^ (-x) - 1 / x_1 ^ x = ∫ (u : ℝ) in (n+1)..(x_1), x*(u^(-x-1)) := by
          have h_rewrite : (n + 1 : ℝ) ^ (-x) - 1 / x_1 ^ x = -(x_1 ^ (-x)) - -((n + 1 : ℝ) ^ (-x)) := by
            have h_pow : x_1 ^ (-x) = 1 / x_1 ^ x := by
              rw [Real.rpow_neg, one_div]
              linarith
            rw [← h_pow]
            ring
          rw [h_rewrite]
          symm
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u ↦ -(u ^ (-x)))
          · intro u hu
            have u_pos : 0 < u := by rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
            have h_pow : HasDerivAt (fun w : ℝ ↦ w ^ (-x)) (-x * u ^ (-x - 1)) u := by
              apply Real.hasDerivAt_rpow_const
              left
              exact ne_of_gt u_pos
            have h_neg := HasDerivAt.neg h_pow
            convert h_neg using 1
            ring
          · #check ContinuousOn.rpow_const
            apply ContinuousOn.intervalIntegrable
            apply ContinuousOn.mul
            · exact continuousOn_const
            · apply ContinuousOn.rpow_const
              · exact continuousOn_id
              · intro wtf hwtf
                left
                #check hwtf
                #check Set.mem_uIcc
                rcases Set.mem_uIcc.mp hwtf with ⟨hn, hx_1⟩ | ⟨hx_1, hn⟩ <;> 
                  · have h_pos : 0 < wtf := by linarith
                    exact ne_of_gt h_pos
        -- damn this have hand
        have :
          ∫ x₁ in (n+1 : ℝ)..(n+2), ((n+1 : ℝ)^(-x) - 1 / x₁^x)
          = ∫ x₁ in (n+1 : ℝ)..(n+2), (∫ u in (n+1 : ℝ)..x₁, x * u^(-x-1)) := by
          refine intervalIntegral.integral_congr ?_
          intro x₁ hx₁
          have hx1_bound : (n + 1 : ℝ) ≤ x₁ := by
            rw [Set.uIcc_of_le (show (n + 1 : ℝ) ≤ n + 2 by linarith)] at hx₁
            exact hx₁.1
          simpa using inner_h_eq x₁ hx1_bound
        rw [this]
        calc
          ∫ x₁ in (n+1)..(n+2), ∫ u in (n+1)..x₁, x * u^(-x-1)
          _ ≤ ∫ x₁ in (n+1)..(n+2), ∫ u in (n+1)..x₁, x * (n+1 : ℝ)^(-x-1) := by sorry
          _ = ∫ x₁ in (n+1)..(n+2), x * (n+1 : ℝ)^(-x-1) * (x₁ - (n+1)) := by sorry
          _ = 1/2 * x * (n+1 : ℝ)^(-x-1) := by sorry
          _ ≤ 1 / (n+1 : ℝ)^2 := by sorry
      · exact intervalIntegrable_const
      · simp_all only [intervalIntegral.integral_const, add_sub_add_left_eq_sub, smul_eq_mul, one_div, ne_eq,
        enorm_ne_top, not_false_eq_true, intervalIntegrable_const]

#check eulerMascheroni_int_bound

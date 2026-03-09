import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import EulerMascheroni.EulerMascheroniInfiniteSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Antisymmetric definition of the Euler–Mascheroni Constant
We use the previous results of `tendsto_riemannZeta_sub_one_div` to create the antisymmetric definition of `Real.eulerMascheroniConstant`
-/
namespace EulerMascheroniAntisymmetric

open Filter Topology MeasureTheory Set

/-- the inner of the integral series (off by one) -/
noncomputable def eulerMascheroni_inner_int_series (n : ℕ) (x : ℝ) := 1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x)

lemma eulerMascheroni_inner_int_pow_series_one (n : ℕ) :
  eulerMascheroni_inner_int_series n 1 = 1/(n+1) - ∫ t in (n+1)..(n+2), (1/t) := by
  unfold eulerMascheroni_inner_int_series
  simp only [Real.rpow_one]

lemma eulerMascheroni_int_series : Real.eulerMascheroniConstant = ∑' n, eulerMascheroni_inner_int_series n 1 := by
  rw [<-EulerMascheroniInfiniteSum.eulerMascheroni_tsum]
  have this : ∀ (x : ℕ), EulerMascheroniInfiniteSum.eulerMascheroni_sum_inner x = eulerMascheroni_inner_int_series x 1 := by
    unfold EulerMascheroniInfiniteSum.eulerMascheroni_sum_inner
    intro x
    rw [eulerMascheroni_inner_int_pow_series_one, integral_one_div]
    intro h
    rw [mem_uIcc] at h
    cases h <;> linarith
  exact tsum_congr this

-- in the paper it is actually t instead of _ but i digress
lemma h_const_int (n : ℕ) (x : ℝ) : ∫ _ in (n + 1)..(n + 2), 1/((n + 1 : ℝ)^x) = 1 / (n + 1 : ℝ)^(x) := by
  simp [intervalIntegral.integral_const]; grind

/- since we offset by one already, we can just -/
lemma eulerMascheroni_int_lower_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) :
  0 ≤ eulerMascheroni_inner_int_series n x
  := by
    unfold eulerMascheroni_inner_int_series
    rw [<-h_const_int]
    apply sub_nonneg_of_le
    have h_bounds : n + 2 = (n + 1 : ℝ) + 1 := by ring
    rw [h_bounds]
    generalize hc : (n + 1 : ℝ) = c
    have hc_pos : 0 < c := by rw [← hc]; positivity
    refine intervalIntegral.integral_mono_on (by linarith) ?_ intervalIntegrable_const (fun t ht ↦ ?_)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div
      · exact continuousOn_const
      · apply ContinuousOn.rpow continuousOn_id continuousOn_const; grind
      · intro u hu
        rw [Set.uIcc_of_le (show c ≤ c + 1 by linarith)] at hu
        have : 0 < u := by linarith [hu.1]
        positivity
    · rw [one_div (c^x), <-Real.rpow_neg]
      · rw [Real.rpow_neg (by positivity), one_div]; gcongr; exact ht.1
      · positivity

lemma eulerMascheroni_int_upper_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2) :
  eulerMascheroni_inner_int_series n x ≤ 1/((n+1)^2) := by
    unfold eulerMascheroni_inner_int_series
    rw [<-h_const_int]
    have h_bounds : n + 2 = (n + 1 : ℝ) + 1 := by ring
    rw [h_bounds]
    generalize hc : (n + 1 : ℝ) = c
    have hc_ge_one : 1 ≤ c := by rw [← hc]; exact le_add_of_nonneg_left (by positivity)
    have hc_pos : 0 < c := by rw [← hc]; positivity
    have huIcc_pos : ∀ t ∈ Set.uIcc c (c + 1), 0 < t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at ht
      linarith
    -- followed the proof in the paper
    calc
      _ = ∫ t in c..c+1, 1/(c^x) - 1/(t^x) := by
        rw [← intervalIntegral.integral_sub]
        · exact intervalIntegrable_const
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div
          · exact continuousOn_const
          · apply ContinuousOn.rpow_const continuousOn_id; intro t ht; right; positivity
          · intro t ht; have := huIcc_pos t ht; positivity
      _ = ∫ t in c..c+1, ∫ u in c..t, x*(u^(-x-1)) := by
        have h_inner_eq (t : ℝ) (ht : c ≤ t) :
          (∫ u in c..t, x * u ^ (-x - 1)) = 1 / c ^ x - 1 / t ^ x := by
            -- #search "integral_const_mul."
            simp_rw [← smul_eq_mul, intervalIntegral.integral_smul, smul_eq_mul]
            rw [integral_rpow]
            · simp; field_simp
              have ht_pos : 0 ≤ t := by linarith
              rw [sub_mul, ← Real.rpow_add hc_pos, neg_add_cancel, Real.rpow_zero, Real.rpow_neg ht_pos]
              ring
            · right
              constructor
              · linarith
              · intro hu; rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu; linarith
        apply intervalIntegral.integral_congr
        intro t ht; dsimp
        -- aesop at it again wwwwww
        simp_all only [one_div, le_add_iff_nonneg_right, zero_le_one, uIcc_of_le, mem_Icc]
      _ ≤ x*(c^(-x-1)) * ∫ t in c..c+1, ∫ u in c..t, 1 := by
        simp_rw [← intervalIntegral.integral_const_mul, mul_one]
        refine intervalIntegral.integral_mono_on (by linarith) ?_ (by apply ContinuousOn.intervalIntegrable; fun_prop) (fun t ht ↦  ?_)
        · apply ContinuousOn.intervalIntegrable
          apply intervalIntegral.continuousOn_primitive_interval
          apply ContinuousOn.integrableOn_uIcc
          refine ContinuousOn.mul continuousOn_const (ContinuousOn.rpow_const continuousOn_id (fun t ht ↦  ?_))
          left; exact (huIcc_pos t ht).ne'
        · rw [Set.mem_Icc] at ht
          refine intervalIntegral.integral_mono_on ht.1 ?_ intervalIntegrable_const (fun u hu ↦  ?_)
          · apply ContinuousOn.intervalIntegrable
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.rpow_const
            · intro u hu
              rw [Set.uIcc_of_le ht.1, Set.mem_Icc] at hu
              exact continuousWithinAt_id
            · intro x_1 hx_1
              left
              rw [Set.uIcc_of_le ht.1, Set.mem_Icc] at hx_1
              linarith
          · apply mul_le_mul_of_nonneg_left
            · refine Real.rpow_le_rpow_of_nonpos ?_ hu.1 ?_ <;> linarith
            · positivity
      _ = x*(c^(-x-1)) * 1/2 := by
        simp [intervalIntegral.integral_sub, integral_id, intervalIntegral.integral_const]
        ring
      _ ≤ 1/(c^2) := by
        have h_exp : -x - 1 ≤ -2 := by linarith
        calc
          _ = (x / 2) * c ^ (-x - 1) := by ring
          _ ≤ 1 * c ^ (-x - 1) := by gcongr; linarith
          _ = c ^ (-x - 1) := by ring
          _ ≤ c ^ (-2) := Real.rpow_le_rpow_of_exponent_le hc_ge_one h_exp
          _ = 1 / c ^ 2 := by rw [Real.rpow_neg (by positivity), Real.rpow_two]; ring

lemma eulerMascheroni_int_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2) :
  0 ≤ eulerMascheroni_inner_int_series n x ∧ eulerMascheroni_inner_int_series n x ≤ 1/((n+1)^2) := by
    exact ⟨eulerMascheroni_int_lower_bound n x hx_lo, eulerMascheroni_int_upper_bound n x hx_lo hx_hi⟩

lemma eulerMascheroni_int_uniform : 
  TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, eulerMascheroni_inner_int_series n x)
    (fun x => ∑' (n : ℕ), eulerMascheroni_inner_int_series n x) atTop (Set.Icc 1 2) := by
      have hu : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ 2)) := by
        have : (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ 2)) = fun n : ℕ => (fun m : ℕ => 1 / (m : ℝ) ^ 2) (n + 1) := by
          ext n; push_cast; rfl
        rw [this]
        exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by linarith))
      refine tendstoUniformlyOn_tsum_nat hu ?_
      intro n x hx
      have ⟨h_lower, h_upper⟩ := eulerMascheroni_int_bound n x hx.1 hx.2
      rw [Real.norm_of_nonneg h_lower]
      exact h_upper

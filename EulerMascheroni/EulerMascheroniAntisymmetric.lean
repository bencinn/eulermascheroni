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
noncomputable def eulerMascheroni_inner_int_series (n : ℕ) := 1/(n+1) - ∫ t in (n+1)..(n+2), (1/t)

lemma eulerMascheroni_int_series : Real.eulerMascheroniConstant = ∑' n, eulerMascheroni_inner_int_series n := by
  rw [<-EulerMascheroniInfiniteSum.eulerMascheroni_tsum]
  have this : ∀ (x : ℕ), EulerMascheroniInfiniteSum.eulerMascheroni_sum_inner x = eulerMascheroni_inner_int_series x := by
    unfold EulerMascheroniInfiniteSum.eulerMascheroni_sum_inner eulerMascheroni_inner_int_series
    intro x
    rw [integral_one_div]
    intro h
    rw [mem_uIcc] at h
    cases h <;> linarith
  exact tsum_congr this

-- in the paper it is actually t instead of _ but i digress
lemma h_const_int (n : ℕ) (x : ℝ) : ∫ _ in (n + 1)..(n + 2), 1/((n + 1 : ℝ)^x) = 1 / (n + 1 : ℝ)^(x) := by
  simp [intervalIntegral.integral_const]
  grind

/- since we offset by one already, we can just -/
lemma eulerMascheroni_int_lower_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2) :
  0 ≤ 1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x)
  := by
    rw [<-h_const_int]
    apply sub_nonneg_of_le
    apply intervalIntegral.integral_mono_on
    · linarith
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div
      · exact continuousOn_const
      · apply ContinuousOn.rpow continuousOn_id continuousOn_const; grind
      · intro u hu
        rw [Set.uIcc_of_le (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)] at hu
        have : 0 < u := by linarith [hu.1]
        positivity
    · apply ContinuousOn.intervalIntegrable; exact continuousOn_const
    · intro t ht
      rw [one_div ((n+1 : ℝ)^x)]
      rw [<-Real.rpow_neg]
      · rw [Real.rpow_neg (by positivity), one_div]; gcongr; exact ht.1
      · positivity

lemma eulerMascheroni_int_upper_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2) :
  1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x) ≤ 1/((n+1)^2) := by
    rw [<-h_const_int]
    calc
      _ = ∫ t in (n+1)..(n+2), 1/((n+1)^x) - 1/(t^x) := by
        rw [← intervalIntegral.integral_sub]
        · exact intervalIntegrable_const
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div
          · exact continuousOn_const
          · apply ContinuousOn.rpow_const continuousOn_id; intro t ht; right; positivity
          · intro t ht
            rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at ht -- one liner is so real
            have : 0 < t := by linarith [n, ht.1]
            positivity
      _ = ∫ t in (n+1)..(n+2), ∫ u in (n+1)..t, x*(u^(-x-1)) := by
        have h_inner_eq (t : ℝ) (ht : n + 1 ≤ t) :
          (∫ u in (n + 1 : ℝ)..t, x * u ^ (-x - 1)) = 1 / (n + 1 : ℝ) ^ x - 1 / t ^ x := by
            -- #search "integral_const_mul."
            simp_rw [← smul_eq_mul, intervalIntegral.integral_smul, smul_eq_mul]
            have hpow : -x - 1 ≠ -1 := by linarith
            rw [integral_rpow]
            · simp; field_simp
              have hn_pos : 0 < (n : ℝ) + 1 := by positivity
              have ht_pos : 0 ≤ t := by linarith
              calc
                _ = -(t ^ (-x) * ((n : ℝ) + 1) ^ x - ((n : ℝ) + 1) ^ (-x) * ((n : ℝ) + 1) ^ x) := by rw [sub_mul]
                _ = -(t ^ (-x) * ((n : ℝ) + 1) ^ x - ((n : ℝ) + 1) ^ (-x + x)) := by rw [← Real.rpow_add hn_pos]
                _ = -(t ^ (-x) * ((n : ℝ) + 1) ^ x - ((n : ℝ) + 1) ^ (0 : ℝ)) := by rw [neg_add_cancel]
                _ = -(t ^ (-x) * ((n : ℝ) + 1) ^ x - 1) := by rw [Real.rpow_zero]
                _ = 1 - t ^ (-x) * ((n : ℝ) + 1) ^ x := by ring
                _ = 1 - (t ^ x)⁻¹ * ((n : ℝ) + 1) ^ x := by rw [Real.rpow_neg ht_pos]
                _ = 1 - ((n : ℝ) + 1) ^ x / t ^ x := by rw [div_eq_inv_mul]
            · right
              constructor
              · exact hpow
              · rw [Set.uIcc_of_le (by linarith), Set.mem_Icc, not_and_or]; left; linarith
        apply intervalIntegral.integral_congr
        intro t ht; dsimp
        -- aesop at it again wwwwww
        rw [h_inner_eq t (by simp_all only [one_div, add_le_add_iff_left, Nat.one_le_ofNat, uIcc_of_le, mem_Icc])]
      _ ≤ x*((n+1)^(-x-1)) * ∫ t in (n+1)..(n+2), ∫ u in (n+1)..t, 1 := by
        simp_rw [← intervalIntegral.integral_const_mul, mul_one]
        apply intervalIntegral.integral_mono_on
        · linarith
        · change IntervalIntegrable (fun u ↦ ∫ (t : ℝ) in ↑n + 1..u, x * t ^ (-x - 1)) volume (↑n + 1) (↑n + 2)
          apply ContinuousOn.intervalIntegrable
          apply intervalIntegral.continuousOn_primitive_interval
          -- apply intervalIntegral.continuousOn_primitive_interval
          apply ContinuousOn.integrableOn_uIcc
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.rpow_const continuousOn_id
          intro t ht
          rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at ht
          left
          intro h
          simp only [id] at h
          linarith [ht.1]
        · apply ContinuousOn.intervalIntegrable
          fun_prop -- what the fuck
        · intro t ht
          dsimp
          rw [Set.mem_Icc] at ht
          apply intervalIntegral.integral_mono_on
          · exact ht.1
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
          · exact intervalIntegrable_const
          · intro u hu
            dsimp
            have hu_left : n + 1 ≤ u := hu.1
            apply mul_le_mul_of_nonneg_left
            · refine Real.rpow_le_rpow_of_nonpos ?_ hu_left ?_
              · positivity
              · linarith
            · positivity
      _ = x*((n+1)^(-x-1)) * 1/2 := by
        have h_outer : ∫ (t : ℝ) in (n+1)..(n+2), t - (n + 1) = 1 / 2 := by
          simp [intervalIntegral.integral_sub, integral_id]
          ring
        -- i love aesop
        simp_all only [intervalIntegral.intervalIntegrable_id, ne_eq, enorm_ne_top, not_false_eq_true,
          intervalIntegrable_const, intervalIntegral.integral_sub, integral_id, Real.enorm_natCast,
          ENNReal.natCast_ne_top, enorm_one, ENNReal.one_ne_top, intervalIntegral.integral_add,
          intervalIntegral.integral_const, add_sub_add_left_eq_sub, smul_eq_mul, mul_one, one_div]
        rfl
      _ ≤ 1/((n+1)^2) := by
        have h_base : (1 : ℝ) ≤ (n + 1 : ℝ) := by linarith
        have h_exp : -x - 1 ≤ -2 := by linarith
        have h_pow_le : (n + 1 : ℝ) ^ (-x - 1) ≤ (n + 1 : ℝ) ^ (-2 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le h_base h_exp
        have h_x_le : x * (1 / 2) ≤ 1 := by linarith
        calc
          _ = (x * (1 / 2)) * (n + 1) ^ (-x - 1) := by ring
          _ ≤ 1 * (n + 1) ^ (-x - 1) := by gcongr
          _ = (n + 1) ^ (-x - 1) := by ring
          _ ≤ (n + 1) ^ (-2) := h_pow_le
          _ = 1 / (n + 1) ^ 2 := by
            rw [Real.rpow_neg (by positivity), Real.rpow_two]
            · simp_all only [le_add_iff_nonneg_left, Nat.cast_nonneg, tsub_le_iff_right, le_neg_add_iff_add_le,
              add_neg_le_iff_le_add, Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, one_div]

lemma eulerMascheroni_int_bound (n : ℕ) (x : ℝ) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 2) :
  0 ≤ 1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x) ∧ 1/((n+1)^x) - ∫ t in (n+1)..(n+2), 1/(t^x) ≤ 1/((n+1)^2) := by
    exact ⟨eulerMascheroni_int_lower_bound n x hx_lo hx_hi, eulerMascheroni_int_upper_bound n x hx_lo hx_hi⟩

#check eulerMascheroni_int_lower_bound

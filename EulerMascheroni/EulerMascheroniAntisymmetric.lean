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
noncomputable def eulerMascheroni_inner_int_series (n : ℕ) := 1/(n+1) + ∫ t in (n+1)..(n+2), (1/t)

lemma eulerMascheroni_int_series : Real.eulerMascheroniConstant = ∑' n, eulerMascheroni_inner_int_series n :=
  by sorry

import TangentSquared.Evaluation
import Mathlib.Analysis.Calculus.SmoothSeries

set_option maxHeartbeats 2000000
open Filter Set
open scoped Topology
namespace TangentSquaredTask

noncomputable def sineDerivativeTerm (α b : ℝ) (n : ℕ) : ℝ :=
  Real.cos (2*(n+1 : ℝ)*angle b)*(2*(n+1 : ℝ)/(1+b^2))*Real.exp (-((n+1 : ℝ)^2)/α)

lemma sineTerm_hasDerivAt (α b : ℝ) (n : ℕ) :
    HasDerivAt (fun y => TangentShiftTask.spectralTerm α y n) (sineDerivativeTerm α b n) b := by
  have ha : HasDerivAt angle (1/(1+b^2)) b := Real.hasDerivAt_arctan b
  have h := ((ha.const_mul (2*(n+1 : ℝ))).sin).mul_const (Real.exp (-((n+1 : ℝ)^2)/α))
  convert h using 1 <;> (try rfl)
  unfold sineDerivativeTerm
  ring

lemma sineDerivative_bound (α b : ℝ) (n : ℕ) :
    ‖sineDerivativeTerm α b n‖ ≤ 2*(n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α) := by
  have hd : 0 < 1+b^2 := by positivity
  have hc : |2*(n+1 : ℝ)/(1+b^2)| ≤ 2*(n+1 : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg b,show (0 : ℝ) ≤ n+1 by positivity]
  unfold sineDerivativeTerm
  rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (mul_le_mul (Real.abs_cos_le_one _) hc (abs_nonneg _) (by norm_num)).trans_eq (by ring)

lemma sineSum_hasDerivAt (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    HasDerivAt (fun y => ∑' n : ℕ, TangentShiftTask.spectralTerm α y n)
      (∑' n : ℕ, sineDerivativeTerm α b n) b := by
  have hm : Summable (fun n : ℕ => 2*(n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α)) := by
    apply ((PeriodicPoleTask.spectral_summable α hα).mul_left 2).congr
    intro n
    unfold PeriodicPoleTask.spectralTerm
    ring
  apply hasDerivAt_tsum_of_isPreconnected hm
    (g := fun n y => TangentShiftTask.spectralTerm α y n)
    (t := Ioi (0 : ℝ)) isOpen_Ioi (convex_Ioi _).isPreconnected
    (g' := fun n y => sineDerivativeTerm α y n) (y₀ := b)
  · intro n y _
    exact sineTerm_hasDerivAt α y n
  · intro n y _
    exact sineDerivative_bound α y n
  · exact hb
  · exact TangentShiftTask.spectral_summable α b hα
  · exact hb

lemma spectralSum_derivative_identity (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    2/b*(∑' n : ℕ,TangentShiftTask.spectralTerm α b n) +
      (1+b^2)/b^3*(∑' n : ℕ,TangentShiftTask.spectralTerm α b n) -
      (1+b^2)/b^2*(∑' n : ℕ,sineDerivativeTerm α b n) =
      ∑' n : ℕ,spectralTerm α b n := by
  have h0 := TangentShiftTask.spectral_summable α b hα
  have hm : Summable (fun n : ℕ => 2*(n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α)) := by
    apply ((PeriodicPoleTask.spectral_summable α hα).mul_left 2).congr
    intro n
    unfold PeriodicPoleTask.spectralTerm
    ring
  have h1 : Summable (sineDerivativeTerm α b) := Summable.of_norm_bounded hm (sineDerivative_bound α b)
  rw [← tsum_mul_left,← tsum_mul_left,← tsum_mul_left,
    ← (h0.mul_left (2/b)).tsum_add (h0.mul_left ((1+b^2)/b^3)),
    ← ((h0.mul_left (2/b)).add (h0.mul_left ((1+b^2)/b^3))).tsum_sub (h1.mul_left ((1+b^2)/b^2))]
  apply tsum_congr
  intro n
  unfold TangentShiftTask.spectralTerm sineDerivativeTerm spectralTerm coefficient
  field_simp [hb.ne',show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

lemma principalValue_hasDerivAt (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    HasDerivAt (TangentShiftTask.principalValue α) (2*b*finitePartValue α b) b := by
  have hi := hasDerivAt_id b
  have hD : HasDerivAt (fun y : ℝ => 1+y^2) (2*b) b := by
    simpa only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq] using (hi.pow 2).const_add 1
  have hT := sineSum_hasDerivAt α b hα hb
  have hnum := (hasDerivAt_const b (2 : ℝ)).div hi hb.ne'
  have hbracket := ((hnum.mul hT).const_add 1)
  have hfactor := (hasDerivAt_const b (-Real.sqrt (Real.pi/α))).div hD
    (show (1 : ℝ)+b^2 ≠ 0 by positivity)
  have h := hfactor.mul hbracket
  change HasDerivAt (TangentShiftTask.principalValue α) _ b at h
  have he := spectralSum_derivative_identity α b hα hb
  unfold finitePartValue
  rw [← he]
  convert h using 1
  dsimp only [Pi.mul_apply,Pi.div_apply,id_eq]
  field_simp [hb.ne',show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

end TangentSquaredTask

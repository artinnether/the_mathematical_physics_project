import TangentSquared.Series
import TuringTask.PeriodizationSmooth

set_option maxHeartbeats 1000000
open Set Filter
namespace TangentSquaredTask

lemma poleMass_periodized (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    poleMass α b=PeriodicPoleTask.periodizedWeight α (angle b)+
      PeriodicPoleTask.periodizedWeight α (-angle b) := by
  have ht : |angle b| ≤ Real.pi/2 := by
    rw [abs_of_pos (TangentShiftTask.angle_pos b hb)]
    exact (TangentShiftTask.angle_lt_half_pi b).le
  have hp := PeriodicPoleTask.periodizedWeight_summable α (angle b) hα ht
  have hm := PeriodicPoleTask.periodizedWeight_summable α (-angle b) hα (by simpa using ht)
  unfold poleMass PeriodicPoleTask.periodizedWeight
  rw [← hp.tsum_add hm]
  apply tsum_congr
  intro k
  unfold weight PeriodicPoleTask.weight
  congr 1 <;> congr 1 <;> ring

lemma massDerivative_summable (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Summable (massDerivativeTerm α b) := by
  have ht : |angle b| ≤ Real.pi/2 := by
    rw [abs_of_pos (TangentShiftTask.angle_pos b hb)]
    exact (TangentShiftTask.angle_lt_half_pi b).le
  have hp : Summable (fun k : ℤ => PeriodicPoleTask.weightDerivative α (angle b+k*Real.pi)) :=
    Summable.of_norm_bounded (PeriodicPoleTask.latticeFirstMajorant_summable α hα)
      (fun k => PeriodicPoleTask.shifted_weightDerivative_bound α (angle b) k hα ht)
  have hm : Summable (fun k : ℤ => PeriodicPoleTask.weightDerivative α (-angle b+k*Real.pi)) :=
    Summable.of_norm_bounded (PeriodicPoleTask.latticeFirstMajorant_summable α hα)
      (fun k => PeriodicPoleTask.shifted_weightDerivative_bound α (-angle b) k hα (by simpa using ht))
  apply ((hp.sub hm).div_const (1+b^2)).congr
  intro k
  unfold massDerivativeTerm PeriodicPoleTask.weightDerivative PeriodicPoleTask.weight weight
  rw [show angle b+(k : ℝ)*Real.pi=k*Real.pi+angle b by ring,
    show -angle b+(k : ℝ)*Real.pi=k*Real.pi-angle b by ring]
  ring

lemma massDerivativeValue_eq (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    massDerivativeValue α b=
      (PeriodicPoleTask.periodizedDerivative α (angle b)-
       PeriodicPoleTask.periodizedDerivative α (-angle b))/(1+b^2) := by
  have ht : |angle b| ≤ Real.pi/2 := by
    rw [abs_of_pos (TangentShiftTask.angle_pos b hb)]
    exact (TangentShiftTask.angle_lt_half_pi b).le
  have hp : Summable (fun k : ℤ => PeriodicPoleTask.weightDerivative α (angle b+k*Real.pi)) :=
    Summable.of_norm_bounded (PeriodicPoleTask.latticeFirstMajorant_summable α hα)
      (fun k => PeriodicPoleTask.shifted_weightDerivative_bound α (angle b) k hα ht)
  have hm : Summable (fun k : ℤ => PeriodicPoleTask.weightDerivative α (-angle b+k*Real.pi)) :=
    Summable.of_norm_bounded (PeriodicPoleTask.latticeFirstMajorant_summable α hα)
      (fun k => PeriodicPoleTask.shifted_weightDerivative_bound α (-angle b) k hα (by simpa using ht))
  unfold massDerivativeValue PeriodicPoleTask.periodizedDerivative
  rw [← hp.tsum_sub hm,← tsum_div_const]
  apply tsum_congr
  intro k
  unfold massDerivativeTerm PeriodicPoleTask.weightDerivative PeriodicPoleTask.weight weight
  rw [show angle b+(k : ℝ)*Real.pi=k*Real.pi+angle b by ring,
    show -angle b+(k : ℝ)*Real.pi=k*Real.pi-angle b by ring]
  ring

lemma poleMass_hasDerivAt (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    HasDerivAt (poleMass α) (massDerivativeValue α b) b := by
  have hp : angle b ∈ Ioo (-Real.pi/2) (Real.pi/2) :=
    ⟨by linarith [TangentShiftTask.angle_pos b hb,Real.pi_pos],TangentShiftTask.angle_lt_half_pi b⟩
  have hm : -angle b ∈ Ioo (-Real.pi/2) (Real.pi/2) := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have ha : HasDerivAt angle (1/(1+b^2)) b := Real.hasDerivAt_arctan b
  have h := ((PeriodicPoleTask.periodizedWeight_hasDerivAt α (angle b) hα hp).comp b ha).add
    ((PeriodicPoleTask.periodizedWeight_hasDerivAt α (-angle b) hα hm).comp b ha.neg)
  rw [massDerivativeValue_eq α b hα hb]
  have he : PeriodicPoleTask.periodizedDerivative α (angle b)*(1/(1+b^2))+
      PeriodicPoleTask.periodizedDerivative α (-angle b)*(-(1/(1+b^2))) =
      (PeriodicPoleTask.periodizedDerivative α (angle b)-PeriodicPoleTask.periodizedDerivative α (-angle b))/(1+b^2) := by ring
  rw [he] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hb] with y hy
  exact poleMass_periodized α y hα hy

end TangentSquaredTask

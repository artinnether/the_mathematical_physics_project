import TuringTask.OuterTruncation
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Set
namespace PeriodicPoleTask

lemma periodizedWeight_summable (α t : ℝ) (hα : 0 < α) (ht : |t| ≤ Real.pi/2) :
    Summable (fun k : ℤ => weight α (t+(k : ℝ)*Real.pi)) :=
  (latticeMajorant_summable α hα).of_nonneg_of_le
    (fun _k => (weight_pos α _).le) (fun k => shifted_weight_bound α t k hα ht)

lemma periodizedWeight_continuousOn (α : ℝ) (hα : 0 < α) :
    ContinuousOn (periodizedWeight α) (Icc (-Real.pi/2) (Real.pi/2)) := by
  apply continuousOn_tsum (fun k => by unfold weight; fun_prop)
    (latticeMajorant_summable α hα)
  intro k t ht
  rw [Real.norm_eq_abs, abs_of_pos (weight_pos _ _)]
  exact shifted_weight_bound α t k hα (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)

lemma periodizedWeight_at_zero (α : ℝ) : periodizedWeight α 0 = poleMass α := by
  simp only [periodizedWeight, poleMass, zero_add]

lemma periodizedWeight_even (α t : ℝ) : periodizedWeight α (-t) = periodizedWeight α t := by
  unfold periodizedWeight
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => weight α (-t+(k : ℝ)*Real.pi))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, Int.cast_neg, neg_mul]
  have he : -t + -((k : ℝ)*Real.pi) = -(t+(k : ℝ)*Real.pi) := by ring
  rw [he,weight_even]

lemma poleMass_pos (α : ℝ) (hα : 0 < α) : 0 < poleMass α := by
  exact (poleMass_summable α hα).tsum_pos (fun k => (weight_pos α _).le) 0
    (weight_pos α _)

end PeriodicPoleTask

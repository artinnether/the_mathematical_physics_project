import SimpleTangent.Basic
import TuringTask.Periodization

namespace TangentShiftTask

lemma angle_pos (b : ℝ) (hb : 0 < b) : 0 < angle b :=
  Real.arctan_pos.mpr hb
lemma angle_lt_half_pi (b : ℝ) : angle b < Real.pi/2 := Real.arctan_lt_pi_div_two b

lemma poleMass_summable (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Summable (fun k : ℤ =>
      weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b)) := by
  have hp : |angle b| ≤ Real.pi/2 := by
    rw [abs_of_pos (angle_pos b hb)]
    exact (angle_lt_half_pi b).le
  have h1 := PeriodicPoleTask.periodizedWeight_summable α (angle b) hα hp
  have h2 := PeriodicPoleTask.periodizedWeight_summable α (-angle b) hα (by simpa using hp)
  convert h1.add h2 using 1
  funext k
  change weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b) =
    weight α (angle b+k*Real.pi)+weight α (-angle b+k*Real.pi)
  congr 1 <;> congr 1 <;> ring

lemma poleMass_pos (α b : ℝ) (hα : 0 < α) (hb : 0 < b) : 0 < poleMass α b := by
  unfold poleMass
  apply (poleMass_summable α b hα hb).tsum_pos (i := (0 : ℤ))
  · intro k
    exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · exact add_pos (Real.exp_pos _) (Real.exp_pos _)

end TangentShiftTask

import SimpleTangent.BoundaryEvaluation

set_option maxHeartbeats 1000000
namespace TangentShiftTask

lemma poleMass_fourier (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    poleMass α b = 2*Real.sqrt (Real.pi/α)/Real.pi*(1+2*cosineSpectral α b) := by
  have he : poleMass α b=ShiftedCosineTask.poleMass (α/4) (2*angle b) := by
    unfold poleMass ShiftedCosineTask.poleMass
    apply tsum_congr
    intro k
    unfold weight ShiftedCosineTask.weight
    congr 1 <;> congr 1 <;> ring
  rw [he,ShiftedCosineTask.poleMass_fourier (α/4) (2*angle b) (by positivity)
    (by linarith [angle_pos b hb]) (by linarith [angle_lt_half_pi b])]
  have hs : Real.sqrt (Real.pi/(α/4))=2*Real.sqrt (Real.pi/α) := by
    rw [show Real.pi/(α/4)=4*(Real.pi/α) by ring,Real.sqrt_mul (by norm_num)]
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [hs]
  unfold cosineSpectral
  congr 2
  congr 1
  apply tsum_congr
  intro n
  unfold ShiftedCosineTask.gaussianTerm
  congr 1
  · congr 1
    ring
  · congr 1
    ring

lemma feynmanBoundaryValue_eq (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    feynmanBoundaryValue α b = (principalValue α b : ℂ)-Complex.I*
      ((Real.pi*poleMass α b/(2*b*(1+b^2)) : ℝ) : ℂ) := by
  rw [boundary_value_parts α b hα hb,poleMass_fourier α b hα hb]
  congr 2
  congr 1
  field_simp [hb.ne',Real.pi_ne_zero]

lemma feynman_tendsto_value (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Filter.Tendsto (feynmanIntegral α b) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((principalValue α b : ℂ)-Complex.I*
        ((Real.pi*poleMass α b/(2*b*(1+b^2)) : ℝ) : ℂ))) := by
  rw [← feynmanBoundaryValue_eq α b hα hb]
  exact feynman_tendsto_boundary α b hα hb

end TangentShiftTask

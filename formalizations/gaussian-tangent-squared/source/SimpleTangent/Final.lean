import SimpleTangent.Specification
import SimpleTangent.PrincipalValue
import SimpleTangent.MassFourier
import SimpleTangent.Abel

open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

theorem gaussian_tangent_shifted_poles (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    TangentShiftClaim α b := by
  refine ⟨outerValue α b,principalValue α b,poleMass_summable α b hα hb,?_,
    outerValue_tendsto α b hα hb,spectral_summable α b hα,rfl,poleMass_pos α b hα hb,
    (fun ε hε => feynman_integrable α b ε hα hε),feynman_tendsto_value α b hα hb,
    (fun r hr hr1 => abel_integrable α b r hα hr hr1),?_,abel_tendsto α b hα⟩
  · intro δ hδ hd
    exact truncation_tendsto α b δ hα hb hδ (lt_min_iff.mp hd).1 (lt_min_iff.mp hd).2
  · intro r hr hr1
    rw [abelIntegral_eq α b r hα hr hr1]
    unfold abelSeriesValue
    congr 3
    apply tsum_congr
    intro n
    ring

lemma feynman_limit_im_negative (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    ((principalValue α b : ℂ)-Complex.I*((Real.pi*poleMass α b/(2*b*(1+b^2)) : ℝ) : ℂ)).im < 0 := by
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
    Complex.I_re,Complex.I_im,one_mul,zero_mul,add_zero,zero_sub]
  have hm := poleMass_pos α b hα hb
  exact neg_neg_of_pos (by positivity)

end TangentShiftTask

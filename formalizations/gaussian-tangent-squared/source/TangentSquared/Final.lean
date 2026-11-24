import TangentSquared.Specification
import TangentSquared.Outer
import TangentSquared.Asymptotics
import TangentSquared.Abel
import TangentSquared.BoundaryEvaluation

namespace TangentSquaredTask

theorem gaussian_tangent_squared_poles (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    SquaredPoleClaim α b := by
  refine ⟨outerValue α b,finitePartValue α b,poleMass_summable α b hα hb,
    poleMass_pos α b hα hb,?_,hadamard_tendsto α b hα hb,
    outerValue_tendsto_atTop α b hα hb,outerValue_scaled_tendsto α b hα hb,
    spectral_summable α b hα,rfl,principalValue_hasDerivAt α b hα hb,
    massDerivative_summable α b hα hb,poleMass_hasDerivAt α b hα hb,
    (fun ε hε => feynman_integrable α b ε hα hε),feynman_tendsto_value α b hα hb,
    (fun r hr hr1 => abel_integrable α b r hα hr hr1),
    (fun r hr hr1 => abelIntegral_eq α b r hα hr hr1),abel_tendsto α b hα⟩
  intro δ hδ hd
  exact truncation_tendsto α b δ hα hb hδ (lt_min_iff.mp hd).1 (lt_min_iff.mp hd).2

end TangentSquaredTask

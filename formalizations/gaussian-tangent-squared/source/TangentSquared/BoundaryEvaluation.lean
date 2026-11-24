import TangentSquared.FeynmanEvaluation
import TangentSquared.MassFourierDerivative

set_option maxHeartbeats 3000000
open Filter
open scoped Topology
namespace TangentSquaredTask

lemma boundary_constants (b : ℝ) (hb : 0 < b) :
    regulatorA (Complex.I*(b : ℂ)) = ((1/(1+b^2)^2 : ℝ) : ℂ)+
      Complex.I*(((1+3*b^2)/(2*b^3*(1+b^2)^2) : ℝ) : ℂ) ∧
    regulatorB (Complex.I*(b : ℂ)) =
      Complex.I*(((1+3*b^2)/(b^3*(1+b^2)^2) : ℝ) : ℂ) ∧
    regulatorC (Complex.I*(b : ℂ)) = ((-2/(b^2*(1+b^2)^2) : ℝ) : ℂ) := by
  have hB : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hD : 1+(b : ℂ)^2 ≠ 0 := by exact_mod_cast (show (1+b^2 : ℝ) ≠ 0 by positivity)
  have hP : 1+Complex.I*(b : ℂ) ≠ 0 := by
    rw [← TangentShiftTask.root_at_zero b hb]
    exact TangentShiftTask.one_add_root_ne b 0
  have hQ : 1-(Complex.I*(b : ℂ))^2=1+(b : ℂ)^2 := by
    rw [mul_pow,Complex.I_sq]
    ring
  unfold regulatorA regulatorB regulatorC
  rw [hQ]
  constructor
  · push_cast
    field_simp [hB,hD,hP,Complex.I_ne_zero]
    ring_nf
    simp [show Complex.I^5=Complex.I by rw [Complex.I_pow_eq_pow_mod]; norm_num,show Complex.I^6=(-1 : ℂ) by rw [Complex.I_pow_eq_pow_mod]; norm_num [Complex.I_sq]]; ring
  constructor
  · push_cast
    field_simp [hB,hD,Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  · push_cast
    field_simp [hB,hD,Complex.I_ne_zero]
    ring_nf
    simp [Complex.I_sq]

lemma weighted_boundary_series_parts (α b : ℝ) (hα : 0 < α) :
    (∑' n : ℕ,(n+1 : ℂ)*TangentShiftTask.boundaryRatio b^(n+1)*
      (Real.exp (-((n+1 : ℝ)^2)/α) : ℂ)) =
      (((1+b^2)/2*(∑' n : ℕ,sineDerivativeTerm α b n) : ℝ) : ℂ)+
      Complex.I*(((1+b^2)/2*(∑' n : ℕ,cosineDerivativeTerm α b n) : ℝ) : ℂ) := by
  have hm : Summable (fun n : ℕ => 2*(n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α)) := by
    apply ((weighted_gaussian_summable α hα).mul_left 2).congr
    intro n
    ring
  have hs := Summable.of_norm_bounded hm (sineDerivative_bound α b)
  have hc := Summable.of_norm_bounded hm (cosineDerivative_bound α b)
  have he (n : ℕ) : (n+1 : ℂ)*TangentShiftTask.boundaryRatio b^(n+1)*
      (Real.exp (-((n+1 : ℝ)^2)/α) : ℂ) =
      (((1+b^2)/2*sineDerivativeTerm α b n : ℝ) : ℂ)+
      Complex.I*(((1+b^2)/2*cosineDerivativeTerm α b n : ℝ) : ℂ) := by
    rw [TangentShiftTask.boundaryRatio_phase,ShiftedCosineTask.unitPhase_pow]
    simp only [ShiftedCosineTask.unitPhase,Nat.cast_add,Nat.cast_one]
    rw [show (n+1 : ℝ)*(-2*angle b)=-(2*(n+1 : ℝ)*angle b) by ring,Real.cos_neg,Real.sin_neg]
    unfold sineDerivativeTerm cosineDerivativeTerm
    push_cast
    field_simp [show 1+(b : ℂ)^2 ≠ 0 by exact_mod_cast (show (1+b^2 : ℝ) ≠ 0 by positivity)]
  simp_rw [he]
  rw [(Complex.summable_ofReal.mpr (hs.mul_left ((1+b^2)/2))).tsum_add
    ((Complex.summable_ofReal.mpr (hc.mul_left ((1+b^2)/2))).mul_left Complex.I),tsum_mul_left,
    ← Complex.ofReal_tsum,← Complex.ofReal_tsum,tsum_mul_left,tsum_mul_left]

lemma complexBoundaryValue_eq (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    complexBoundaryValue α b=(finitePartValue α b : ℂ)+Complex.I*(imaginaryValue α b : ℂ) := by
  unfold complexBoundaryValue
  rw [(boundary_constants b hb).1,(boundary_constants b hb).2.1,
    (boundary_constants b hb).2.2,TangentShiftTask.boundary_series_parts α b hα,
    weighted_boundary_series_parts α b hα]
  unfold finitePartValue imaginaryValue
  rw [massDerivativeValue_fourier α b hα hb]
  have hm : poleMass α b=2*Real.sqrt (Real.pi/α)/Real.pi*(1+2*TangentShiftTask.cosineSpectral α b) :=
    TangentShiftTask.poleMass_fourier α b hα hb
  rw [hm,← spectralSum_derivative_identity α b hα hb]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hb.ne',
    show 1+(b : ℂ)^2 ≠ 0 by exact_mod_cast (show (1+b^2 : ℝ) ≠ 0 by positivity),
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  simp [Complex.I_sq]

lemma feynman_tendsto_value (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (feynmanIntegral α b) (𝓝[>] (0 : ℝ))
      (𝓝 ((finitePartValue α b : ℂ)+Complex.I*(imaginaryValue α b : ℂ))) := by
  rw [← complexBoundaryValue_eq α b hα hb]
  exact feynman_tendsto_boundary α b hα hb

end TangentSquaredTask

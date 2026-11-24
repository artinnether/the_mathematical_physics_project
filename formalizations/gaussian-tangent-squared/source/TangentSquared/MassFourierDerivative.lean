import TangentSquared.Parameter
import TangentSquared.MassDerivative
import SimpleTangent.MassFourier

set_option maxHeartbeats 2000000
open Filter Set
open scoped Topology
namespace TangentSquaredTask

noncomputable def cosineDerivativeTerm (α b : ℝ) (n : ℕ) : ℝ :=
  -Real.sin (2*(n+1 : ℝ)*angle b)*(2*(n+1 : ℝ)/(1+b^2))*Real.exp (-((n+1 : ℝ)^2)/α)

lemma cosineTerm_hasDerivAt (α b : ℝ) (n : ℕ) :
    HasDerivAt (fun y => Real.exp (-((n+1 : ℝ)^2)/α)*Real.cos (2*(n+1 : ℝ)*angle y)) (cosineDerivativeTerm α b n) b := by
  have ha : HasDerivAt angle (1/(1+b^2)) b := Real.hasDerivAt_arctan b
  have h := ((ha.const_mul (2*(n+1 : ℝ))).cos).mul_const (Real.exp (-((n+1 : ℝ)^2)/α))
  convert h using 1 <;> (try rfl)
  · funext y
    ring
  · unfold cosineDerivativeTerm
    ring

lemma cosineDerivative_bound (α b : ℝ) (n : ℕ) :
    ‖cosineDerivativeTerm α b n‖ ≤ 2*(n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α) := by
  have hd : 0 < 1+b^2 := by positivity
  have hc : |2*(n+1 : ℝ)/(1+b^2)| ≤ 2*(n+1 : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg b,show (0 : ℝ) ≤ n+1 by positivity]
  unfold cosineDerivativeTerm
  rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),abs_neg]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (mul_le_mul (Real.abs_sin_le_one _) hc (abs_nonneg _) (by norm_num)).trans_eq (by ring)

lemma cosineSum_hasDerivAt (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    HasDerivAt (fun y => ∑' n : ℕ, Real.exp (-((n+1 : ℝ)^2)/α)*Real.cos (2*(n+1 : ℝ)*angle y))
      (∑' n : ℕ, cosineDerivativeTerm α b n) b := by
  have hm : Summable (fun n : ℕ => 2*(n+1 : ℝ)*Real.exp (-((n+1 : ℝ)^2)/α)) := by
    apply ((PeriodicPoleTask.spectral_summable α hα).mul_left 2).congr
    intro n
    unfold PeriodicPoleTask.spectralTerm
    ring
  apply hasDerivAt_tsum_of_isPreconnected hm
    (g := fun (n : ℕ) y => Real.exp (-((n+1 : ℝ)^2)/α)*Real.cos (2*(n+1 : ℝ)*angle y))
    (t := Ioi (0 : ℝ)) isOpen_Ioi (convex_Ioi _).isPreconnected
    (g' := fun n y => cosineDerivativeTerm α y n) (y₀ := b)
  · intro n y _
    exact cosineTerm_hasDerivAt α y n
  · intro n y _
    exact cosineDerivative_bound α y n
  · exact hb
  · exact TangentShiftTask.gaussian_sequence_summable α hα |>.of_norm_bounded (by
      intro n
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))
  · exact hb


lemma poleMass_fourier_hasDerivAt (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    HasDerivAt (poleMass α)
      (4*Real.sqrt (Real.pi/α)/Real.pi*(∑' n : ℕ,cosineDerivativeTerm α b n)) b := by
  have h := ((cosineSum_hasDerivAt α b hα hb).const_mul 2).const_add 1
  have h' := h.const_mul (2*Real.sqrt (Real.pi/α)/Real.pi)
  have he : poleMass α =ᶠ[𝓝 b] (fun y => 2*Real.sqrt (Real.pi/α)/Real.pi*
      (1+2*TangentShiftTask.cosineSpectral α y)) := by
    filter_upwards [eventually_gt_nhds hb] with y hy
    exact TangentShiftTask.poleMass_fourier α y hα hy
  have hf := h'.congr_of_eventuallyEq he
  convert hf using 1 <;> (try rfl); ring

lemma massDerivativeValue_fourier (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    massDerivativeValue α b =
      4*Real.sqrt (Real.pi/α)/Real.pi*(∑' n : ℕ,cosineDerivativeTerm α b n) :=
  (poleMass_hasDerivAt α b hα hb).unique (poleMass_fourier_hasDerivAt α b hα hb)

end TangentSquaredTask

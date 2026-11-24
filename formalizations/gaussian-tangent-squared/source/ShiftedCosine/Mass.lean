import ShiftedCosine.Series

open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma poleMass_eq (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    poleMass a θ = 2*PeriodicPoleTask.periodizedWeight (4*a) (θ/2) := by
  have hp : |θ/2| ≤ Real.pi/2 := by rw [abs_of_pos (by positivity : 0 < θ/2)]; linarith
  have hn : |(-θ)/2| ≤ Real.pi/2 := by rw [neg_div,abs_neg]; exact hp
  have h1 := PeriodicPoleTask.periodizedWeight_summable (4*a) (θ/2) (by positivity) hp
  have h2 := PeriodicPoleTask.periodizedWeight_summable (4*a) ((-θ)/2) (by positivity) hn
  unfold poleMass
  have he (k : ℤ) : weight a (2*k*Real.pi+θ)+weight a (2*k*Real.pi-θ) =
      PeriodicPoleTask.weight (4*a) (θ/2+k*Real.pi)+
      PeriodicPoleTask.weight (4*a) ((-θ)/2+k*Real.pi) := by
    rw [shifted_weight,show 2*(k : ℝ)*Real.pi-θ=2*k*Real.pi+(-θ) by ring,shifted_weight]
  simp_rw [he]
  rw [h1.tsum_add h2]
  change PeriodicPoleTask.periodizedWeight (4*a) (θ/2)+
    PeriodicPoleTask.periodizedWeight (4*a) ((-θ)/2) = _
  rw [neg_div,PeriodicPoleTask.periodizedWeight_even]
  ring

noncomputable def massDerivative (a θ : ℝ) : ℝ :=
  PeriodicPoleTask.periodizedDerivative (4*a) (θ/2)

lemma poleMass_hasDerivAt (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    HasDerivAt (poleMass a) (massDerivative a θ) θ := by
  have ht : θ/2 ∈ Ioo (-Real.pi/2) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have h := (PeriodicPoleTask.periodizedWeight_hasDerivAt (4*a) (θ/2)
    (by positivity) ht).comp θ ((hasDerivAt_id θ).div_const 2)
  have h := h.const_mul 2
  have he : poleMass a =ᶠ[𝓝 θ]
      (fun t : ℝ => 2*PeriodicPoleTask.periodizedWeight (4*a) (t/2)) := by
    filter_upwards [eventually_gt_nhds hθ,eventually_lt_nhds hπ] with t ht0 htπ
    exact poleMass_eq a t ha ht0 htπ
  have h := h.congr_of_eventuallyEq he
  apply h.congr_deriv
  unfold massDerivative
  ring

lemma mass_div_sine_hasDerivAt (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    HasDerivAt (fun t : ℝ => poleMass a t/Real.sin t)
      ((massDerivative a θ*Real.sin θ-poleMass a θ*Real.cos θ)/Real.sin θ^2) θ := by
  exact (poleMass_hasDerivAt a θ ha hθ hπ).div (Real.hasDerivAt_sin θ)
    (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'

end ShiftedCosineTask

import ShiftedCosine.HadamardEvaluation
import ShiftedCosine.MassFourier
import ShiftedCosine.Abel
import ShiftedCosine.SpecialCase
import Mathlib.Topology.Algebra.Order.Field

open Filter MeasureTheory
open scoped Topology
namespace ShiftedCosineTask

lemma divergenceCoefficient_pos (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    0 < 2*poleMass a θ/Real.sin θ^2 :=
  div_pos (mul_pos (by norm_num) (poleMass_positive a θ ha hθ hπ))
    (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ hπ))

lemma outerValue_tendsto_atTop (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (outerValue a θ) (𝓝[>] (0 : ℝ)) atTop := by
  have hd : Tendsto (fun δ : ℝ => 2*poleMass a θ/(Real.sin θ^2*δ)) (𝓝[>] (0 : ℝ)) atTop := by
    have h := (tendsto_inv_nhdsGT_zero : Tendsto (fun δ : ℝ => δ⁻¹) (𝓝[>] (0 : ℝ)) atTop).const_mul_atTop
      (divergenceCoefficient_pos a θ ha hθ hπ)
    convert h using 1
    ext δ
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simpa only [sub_add_cancel] using (hadamard_tendsto a θ ha hθ hπ).add_atTop hd

lemma scaled_outerValue_tendsto (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Tendsto (fun δ => δ*outerValue a θ δ) (𝓝[>] (0 : ℝ))
      (𝓝 (2*poleMass a θ/Real.sin θ^2)) := by
  have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (hi.mul (hadamard_tendsto a θ ha hθ hπ)).add_const (2*poleMass a θ/Real.sin θ^2)
  simp only [zero_mul,zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ : 0 < δ := hδ
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ hπ).ne'
  field_simp [hs,ne_of_gt hδ]
  ring

lemma feynmanIntegral_half_pi_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (feynmanIntegral a (Real.pi/2)) (𝓝[>] (0 : ℝ))
      (𝓝 ((4*Real.sqrt (Real.pi/a)*∑' n : ℕ, (n+1 : ℝ)*(-1 : ℝ)^n*
        Real.exp (-((n+1 : ℝ)^2)/a) : ℝ) + Complex.I*
        (-2*Real.sqrt (Real.pi/a)*∑' n : ℕ, (2*n+1 : ℝ)*(-1 : ℝ)^n*
          Real.exp (-((2*n+1 : ℝ)^2)/(4*a)) : ℝ))) := by
  simpa only [finitePartValue_half_pi a ha,imaginaryValue_half_pi a ha] using
    feynmanIntegral_tendsto a (Real.pi/2) ha (by positivity) (by linarith [Real.pi_pos])

/-- The original integrals, with shared actual-limit witnesses and no analytic assumptions. -/
def ShiftedCosineClaim (a θ : ℝ) : Prop :=
  Summable (fun k : ℤ => weight a (2*k*Real.pi+θ)+weight a (2*k*Real.pi-θ)) ∧
  Summable (fun n : ℕ => realCoefficient θ n*gaussianTerm a n) ∧
  Summable (fun n : ℕ => imaginaryCoefficient θ n*gaussianTerm a n) ∧
  (∀ δ : ℝ, 0 < δ → δ < θ → δ < Real.pi-θ →
    Tendsto (truncation a θ δ) atTop (𝓝 (outerValue a θ δ))) ∧
  Tendsto (fun δ => outerValue a θ δ-2*poleMass a θ/(Real.sin θ^2*δ))
    (𝓝[>] (0 : ℝ)) (𝓝 (finitePartValue a θ)) ∧
  Tendsto (fun δ => δ*outerValue a θ δ) (𝓝[>] (0 : ℝ)) (𝓝 (2*poleMass a θ/Real.sin θ^2)) ∧
  0 < 2*poleMass a θ/Real.sin θ^2 ∧
  Tendsto (outerValue a θ) (𝓝[>] (0 : ℝ)) atTop ∧
  (∀ ε : ℝ, 0 < ε → Integrable (feynmanIntegrand a θ ε)) ∧
  Tendsto (feynmanIntegral a θ) (𝓝[>] (0 : ℝ))
    (𝓝 ((finitePartValue a θ : ℂ)+Complex.I*(imaginaryValue a θ : ℂ))) ∧
  DifferentiableAt ℝ (poleMass a) θ ∧
  HasDerivAt (fun t => poleMass a t/Real.sin t) (imaginaryValue a θ*Real.sin θ/Real.pi) θ ∧
  (∀ r : ℝ, 0 < r → r < 1 → Integrable (fun x => weight a x*abelKernel θ r x)) ∧
  (∀ r : ℝ, 0 < r → r < 1 → abelIntegral a θ r=
    2*Real.sqrt (Real.pi/a)*∑' n : ℕ, realCoefficient θ n*gaussianTerm a n*r^(n+1)) ∧
  Tendsto (abelIntegral a θ) (𝓝[<] (1 : ℝ)) (𝓝 (finitePartValue a θ))

theorem shifted_cosine_double_poles (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    ShiftedCosineClaim a θ := by
  exact ⟨poleMass_summable a θ ha hθ hπ,real_spectral_summable a θ ha hθ hπ,
    imaginary_spectral_summable a θ ha hθ hπ,
    fun δ hδ hδθ hδπ => truncation_tendsto a θ δ ha hθ hπ hδ hδθ hδπ,
    hadamard_tendsto a θ ha hθ hπ,scaled_outerValue_tendsto a θ ha hθ hπ,
    divergenceCoefficient_pos a θ ha hθ hπ,outerValue_tendsto_atTop a θ ha hθ hπ,
    fun ε hε => feynman_integrable a θ ε ha hε,feynmanIntegral_tendsto a θ ha hθ hπ,
    (poleMass_hasDerivAt a θ ha hθ hπ).differentiableAt,
    imaginaryValue_mass_derivative a θ ha hθ hπ,
    fun r hr hr1 => abel_integrable a θ r ha hθ hπ hr hr1,
    fun r hr hr1 => abelIntegral_eq a θ r ha hθ hπ hr hr1,
    abelIntegral_tendsto a θ ha hθ hπ⟩

/-- Fixed exercise target, including the special case of the same limit values. -/
def ShiftedCosineTarget : Prop :=
  ∀ a θ : ℝ, 0 < a → 0 < θ → θ < Real.pi →
    ShiftedCosineClaim a θ ∧
    finitePartValue a (Real.pi/2) =
      4*Real.sqrt (Real.pi/a)*∑' n : ℕ, (n+1 : ℝ)*(-1 : ℝ)^n*
        Real.exp (-((n+1 : ℝ)^2)/a) ∧
    imaginaryValue a (Real.pi/2) =
      -2*Real.sqrt (Real.pi/a)*∑' n : ℕ, (2*n+1 : ℝ)*(-1 : ℝ)^n*
        Real.exp (-((2*n+1 : ℝ)^2)/(4*a))

theorem shifted_cosine_complete : ShiftedCosineTarget := by
  intro a θ ha hθ hπ
  exact ⟨shifted_cosine_double_poles a θ ha hθ hπ,
    finitePartValue_half_pi a ha,imaginaryValue_half_pi a ha⟩

end ShiftedCosineTask

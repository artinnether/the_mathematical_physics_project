import TangentSquared.Basic

open Filter MeasureTheory
open scoped Topology
namespace TangentSquaredTask

/-- The complete target uses common witnesses for the actual integrals and limits. -/
def SquaredPoleClaim (α b : ℝ) : Prop :=
  ∃ J : ℝ → ℝ, ∃ H : ℝ,
    Summable (fun k : ℤ => weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b)) ∧
    0 < poleMass α b ∧
    (∀ δ : ℝ, 0 < δ → δ < min (angle b) (Real.pi/2-angle b) →
      Tendsto (truncation α b δ) atTop (𝓝 (J δ))) ∧
    Tendsto (fun δ => J δ-subtraction α b δ) (𝓝[>] (0 : ℝ)) (𝓝 H) ∧
    Tendsto J (𝓝[>] (0 : ℝ)) atTop ∧
    Tendsto (fun δ => δ*J δ) (𝓝[>] (0 : ℝ))
      (𝓝 (poleMass α b/(2*b^2*(1+b^2)^2))) ∧
    Summable (spectralTerm α b) ∧ H=finitePartValue α b ∧
    HasDerivAt (TangentShiftTask.principalValue α) (2*b*H) b ∧
    Summable (massDerivativeTerm α b) ∧
    HasDerivAt (poleMass α) (massDerivativeValue α b) b ∧
    (∀ ε : ℝ, 0 < ε → Integrable (feynmanIntegrand α b ε)) ∧
    Tendsto (feynmanIntegral α b) (𝓝[>] (0 : ℝ))
      (𝓝 ((H : ℂ)+Complex.I*(imaginaryValue α b : ℂ))) ∧
    (∀ r : ℝ, 0 < r → r < 1 → Integrable (fun x => weight α x*abelKernel b r x)) ∧
    (∀ r : ℝ, 0 < r → r < 1 →
      abelIntegral α b r=Real.sqrt (Real.pi/α)/(1+b^2)^2*
        (1+∑' n : ℕ, spectralTerm α b n*r^(n+1))) ∧
    Tendsto (abelIntegral α b) (𝓝[<] (1 : ℝ)) (𝓝 H)

end TangentSquaredTask

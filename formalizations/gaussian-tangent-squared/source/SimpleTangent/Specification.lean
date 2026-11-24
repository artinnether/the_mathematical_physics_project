import SimpleTangent.Basic

open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

/-- Shared witnesses for the actual outer limit and actual principal value. -/
def TangentShiftClaim (α b : ℝ) : Prop :=
  ∃ J : ℝ → ℝ, ∃ P : ℝ,
    Summable (fun k : ℤ =>
      weight α (k*Real.pi+angle b)+weight α (k*Real.pi-angle b)) ∧
    (∀ δ : ℝ, 0 < δ → δ < min (angle b) (Real.pi/2-angle b) →
      Tendsto (truncation α b δ) atTop (𝓝 (J δ))) ∧
    Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 P) ∧
    Summable (spectralTerm α b) ∧ P = principalValue α b ∧
    0 < poleMass α b ∧
    (∀ ε : ℝ, 0 < ε → Integrable (feynmanIntegrand α b ε)) ∧
    Tendsto (feynmanIntegral α b) (𝓝[>] (0 : ℝ))
      (𝓝 ((P : ℂ)-Complex.I*(Real.pi*poleMass α b/(2*b*(1+b^2)) : ℝ))) ∧
    (∀ r : ℝ, 0 < r → r < 1 → Integrable (fun x => weight α x*abelKernel b r x)) ∧
    (∀ r : ℝ, 0 < r → r < 1 →
      abelIntegral α b r = -Real.sqrt (Real.pi/α)/(1+b^2)*
        (1+2/b*∑' n : ℕ, r^(n+1)*spectralTerm α b n)) ∧
    Tendsto (abelIntegral α b) (𝓝[<] (1 : ℝ)) (𝓝 P)

end TangentShiftTask

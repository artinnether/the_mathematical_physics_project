import TuringTask.Basic

open Filter MeasureTheory
open scoped Topology
namespace PeriodicPoleTask

/-- The requested convergence statements use common witnesses J, H and F. -/
def PeriodicPoleClaim (α : ℝ) : Prop :=
  ∃ (J : ℝ → ℝ) (H : ℝ) (F : ℂ),
    Summable (fun k : ℤ => weight α (k * Real.pi)) ∧
    (∀ δ : ℝ, 0 < δ → δ < Real.pi / 2 →
      Tendsto (truncation α δ) atTop (𝓝 (J δ))) ∧
    Tendsto (fun δ : ℝ => J δ - 2 * poleMass α / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 H) ∧
    H = finitePartValue α ∧
    Summable (spectralTerm α) ∧
    Tendsto J (𝓝[>] (0 : ℝ)) atTop ∧
    (∀ ε : ℝ, 0 < ε → Integrable (feynmanIntegrand α ε)) ∧
    Tendsto (feynmanIntegral α) (𝓝[>] (0 : ℝ)) (𝓝 F) ∧
    F = (finitePartValue α : ℂ) ∧
    F - (H : ℂ) = 0 ∧
    (∀ k : ℤ, Real.cos ((k : ℝ) * Real.pi) = (-1 : ℝ)^k) ∧
    (∀ ε : ℝ, 0 < ε → (feynmanIntegral α ε).im = 0) ∧
    (∀ r : ℝ, 0 < r → r < 1 →
      Integrable (fun x : ℝ => weight α x * abelKernel r x)) ∧
    Tendsto (abelIntegral α) (𝓝[<] (1 : ℝ)) (𝓝 H) ∧
    H < 0

end PeriodicPoleTask

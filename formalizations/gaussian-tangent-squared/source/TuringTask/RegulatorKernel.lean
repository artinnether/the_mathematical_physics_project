import TuringTask.GeometricFourier
import TuringTask.RegulatorSeries

namespace PeriodicPoleTask

noncomputable def regulatedRealKernel (ε x : ℝ) : ℝ :=
  (Real.sin x ^ 2 - ε^2) / (Real.sin x ^ 2 + ε^2)^2

lemma regulatorRatio_strict (ε : ℝ) (hε : 0 < ε) :
    0 < regulatorRatio ε ∧ regulatorRatio ε < 1 := by
  have hs := regulatorScale_sq ε
  have hn : 0 ≤ regulatorScale ε := Real.sqrt_nonneg _
  have ha : 0 < regulatorScale ε - ε := by nlinarith
  have hb : regulatorScale ε - ε < 1 := by nlinarith
  unfold regulatorRatio
  exact ⟨sq_pos_of_pos ha, by nlinarith⟩

lemma regulatorRatio_identities (ε : ℝ) :
    1-regulatorRatio ε = 2*ε*(regulatorScale ε-ε) ∧
    1+regulatorRatio ε = 2*regulatorScale ε*(regulatorScale ε-ε) ∧
    1-regulatorRatio ε^2 = 4*ε*regulatorScale ε*regulatorRatio ε ∧
    1+regulatorRatio ε^2 = 2*regulatorRatio ε*(1+2*ε^2) := by
  have hs := regulatorScale_sq ε
  have h1 : 1-regulatorRatio ε = 2*ε*(regulatorScale ε-ε) := by
    unfold regulatorRatio; nlinarith
  have h2 : 1+regulatorRatio ε = 2*regulatorScale ε*(regulatorScale ε-ε) := by
    unfold regulatorRatio; nlinarith
  refine ⟨h1, h2, ?_, ?_⟩
  · calc
      1-regulatorRatio ε^2 = (1-regulatorRatio ε)*(1+regulatorRatio ε) := by ring
      _ = _ := by rw [h1,h2]; unfold regulatorRatio; ring
  · calc
      1+regulatorRatio ε^2 = (1+regulatorRatio ε)^2 - 2*regulatorRatio ε := by ring
      _ = 4*regulatorScale ε^2*regulatorRatio ε-2*regulatorRatio ε := by
        rw [h2]; unfold regulatorRatio; ring
      _ = _ := by rw [hs]; ring

lemma regulator_geometricDenominator (ε x : ℝ) :
    geometricDenominator (regulatorRatio ε) (2*x) =
      4*regulatorRatio ε*(Real.sin x^2+ε^2) := by
  have h := (regulatorRatio_identities ε).2.2.2
  rw [geometricDenominator, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma regulatedRealKernel_fourier (ε x : ℝ) (hε : 0 < ε) :
    regulatedRealKernel ε x =
      -ε / regulatorScale ε^3 *
        (1+2*∑' n : ℕ, regulatorRatio ε^(n+1)*Real.cos ((n+1 : ℝ)*(2*x))) -
      4 / regulatorScale ε^2 *
        (∑' n : ℕ, (n+1 : ℝ)*regulatorRatio ε^(n+1)*Real.cos ((n+1 : ℝ)*(2*x))) := by
  have hq := regulatorRatio_strict ε hε
  have haq : |regulatorRatio ε| < 1 := by simpa [abs_of_pos hq.1] using hq.2
  have hd : Real.sin x^2+ε^2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (Real.sin x)] : 0 < Real.sin x^2+ε^2)
  have hs0 : regulatorScale ε ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (regulatorScale_ge_one ε))
  have hq0 := ne_of_gt hq.1
  have hs := regulatorScale_sq ε
  have hid := regulatorRatio_identities ε
  have hcos : Real.cos (2*x) = 1-2*Real.sin x^2 := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x]
  have hC : 1+2*(∑' n : ℕ, regulatorRatio ε^(n+1)*Real.cos ((n+1 : ℝ)*(2*x))) =
      ε*regulatorScale ε/(Real.sin x^2+ε^2) := by
    rw [cosine_geometric_tsum _ _ haq]
    calc
      _ = (1-regulatorRatio ε^2)/geometricDenominator (regulatorRatio ε) (2*x) := by
        have hD := ne_of_gt (geometricDenominator_pos (regulatorRatio ε) (2*x) haq)
        field_simp [hD]; unfold geometricDenominator; ring
      _ = _ := by rw [hid.2.2.1, regulator_geometricDenominator]; field_simp <;> ring
  have hN : (∑' n : ℕ, (n+1 : ℝ)*regulatorRatio ε^(n+1)*Real.cos ((n+1 : ℝ)*(2*x))) =
      (ε^2-(1+2*ε^2)*Real.sin x^2)/(4*(Real.sin x^2+ε^2)^2) := by
    rw [cosine_weighted_tsum _ _ haq, regulator_geometricDenominator, hcos, hid.2.2.2]
    field_simp
    ring
  rw [hC,hN]
  unfold regulatedRealKernel
  field_simp [hd,hs0]
  linear_combination (Real.sin x^2 - ε^2) * hs

end PeriodicPoleTask

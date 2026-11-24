import TangentSquared.Hadamard

set_option maxHeartbeats 2000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentSquaredTask

lemma coefficient_decomposition (b : ℝ) (hb : 0 < b) (n : ℕ) :
    coefficient b n=4/b*Real.sin (2*(n+1 : ℝ)*angle b)+
      8/(1+b^2)^2*ShiftedCosineTask.realCoefficient (2*angle b) n := by
  unfold coefficient ShiftedCosineTask.realCoefficient
  rw [TangentShiftTask.angle_sin_two,TangentShiftTask.angle_cos_two]
  rw [show (n+1 : ℝ)*(2*angle b)=2*(n+1 : ℝ)*angle b by ring]
  field_simp [hb.ne',show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

lemma gaussianTerm_rescaled (α : ℝ) (n : ℕ) :
    ShiftedCosineTask.gaussianTerm (α/4) n=Real.exp (-((n+1 : ℝ)^2)/α) := by
  unfold ShiftedCosineTask.gaussianTerm
  congr 1
  ring

lemma spectral_sum_decomposition (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    (∑' n : ℕ, spectralTerm α b n) =
      4/b*(∑' n : ℕ, TangentShiftTask.spectralTerm α b n) +
      8/(1+b^2)^2*(∑' n : ℕ,
        ShiftedCosineTask.realCoefficient (2*angle b) n*ShiftedCosineTask.gaussianTerm (α/4) n) := by
  have hθ : 0 < 2*angle b := by linarith [TangentShiftTask.angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [TangentShiftTask.angle_lt_half_pi b]
  have h0 := (TangentShiftTask.spectral_summable α b hα).mul_left (4/b)
  have h1 := (ShiftedCosineTask.real_spectral_summable (α/4) (2*angle b)
    (by positivity) hθ hπ).mul_left (8/(1+b^2)^2)
  rw [← tsum_mul_left,← tsum_mul_left,← h0.tsum_add h1]
  apply tsum_congr
  intro n
  unfold spectralTerm TangentShiftTask.spectralTerm
  rw [coefficient_decomposition b hb n,gaussianTerm_rescaled]
  ring

lemma decomposedValue_eq (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    decomposedValue α b=finitePartValue α b := by
  have hθ : 0 < 2*angle b := by linarith [TangentShiftTask.angle_pos b hb]
  have hπ : 2*angle b < Real.pi := by linarith [TangentShiftTask.angle_lt_half_pi b]
  have hs : Real.sqrt (Real.pi/(α/4))=2*Real.sqrt (Real.pi/α) := by
    rw [show Real.pi/(α/4)=4*(Real.pi/α) by ring,Real.sqrt_mul (by norm_num),
      show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  have ht : (∑' n : ℕ,ShiftedCosineTask.gaussianTerm (α/4) n*Real.sin ((n+1 : ℝ)*(2*angle b)))=
      ∑' n : ℕ,TangentShiftTask.spectralTerm α b n := by
    apply tsum_congr
    intro n
    rw [gaussianTerm_rescaled]
    unfold TangentShiftTask.spectralTerm
    rw [show (n+1 : ℝ)*(2*angle b)=2*(n+1 : ℝ)*angle b by ring]
    ring
  unfold decomposedValue finitePartValue
  rw [ShiftedCosineTask.simplePVIntegral_eq_series (α/4) (2*angle b) (by positivity) hθ hπ]
  unfold ShiftedCosineTask.finitePartValue
  rw [hs,ht,TangentShiftTask.angle_sin_two,spectral_sum_decomposition α b hα hb]
  field_simp [hb.ne',show (1 : ℝ)+b^2 ≠ 0 by positivity]
  ring

lemma hadamard_tendsto (α b : ℝ) (hα : 0 < α) (hb : 0 < b) :
    Tendsto (fun δ => outerValue α b δ-subtraction α b δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (finitePartValue α b)) := by
  rw [← decomposedValue_eq α b hα hb]
  exact hadamard_tendsto_decomposed α b hα hb

end TangentSquaredTask

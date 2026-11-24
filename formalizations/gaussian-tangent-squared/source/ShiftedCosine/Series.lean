import ShiftedCosine.Basic
import TuringTask.PeriodizationSmooth

open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma gaussianTerm_summable (a : ℝ) (ha : 0 < a) : Summable (gaussianTerm a) := by
  have h := PeriodicPoleTask.summable_gaussian_polynomial (1/(4*a)) (by positivity) 0
  have h := (summable_nat_add_iff 1).mpr h
  apply h.congr
  intro n
  simp only [pow_zero,one_mul,Nat.cast_add,Nat.cast_one,gaussianTerm]
  congr 1
  ring

lemma weightedTerm_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (n+1 : ℝ)*gaussianTerm a n) := by
  exact PeriodicPoleTask.spectral_summable (4*a) (by positivity)

lemma coefficient_bound (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) (n : ℕ) :
    ‖realCoefficient θ n‖ ≤ (n+1 : ℝ)/Real.sin θ^2+1/Real.sin θ^3 ∧
    ‖imaginaryCoefficient θ n‖ ≤ (n+1 : ℝ)/Real.sin θ^2+1/Real.sin θ^3 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  have hc := Real.abs_cos_le_one ((n+1 : ℝ)*θ)
  have ht := Real.abs_sin_le_one ((n+1 : ℝ)*θ)
  have hct := Real.abs_cos_le_one θ
  have hprod (f : ℝ) (hf : |f| ≤ 1) : |Real.cos θ*f| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hct hf (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hfirst (f : ℝ) (hf : |f| ≤ 1) :
      ‖-(n+1 : ℝ)*f/Real.sin θ^2‖ ≤ (n+1 : ℝ)/Real.sin θ^2 := by
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ n+1 by positivity),abs_of_pos (pow_pos hs 2)]
    exact div_le_div_of_nonneg_right (by nlinarith [hf]) (by positivity)
  have hsecond (f : ℝ) (hf : |f| ≤ 1) :
      ‖Real.cos θ*f/Real.sin θ^3‖ ≤ 1/Real.sin θ^3 := by
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos hs 3)]
    exact div_le_div_of_nonneg_right (hprod f hf) (by positivity)
  constructor
  · exact (norm_add_le _ _).trans (add_le_add (hfirst _ hc) (hsecond _ ht))
  · exact (norm_sub_le _ _).trans (add_le_add (hfirst _ ht) (hsecond _ hc))

lemma spectral_majorant_summable (a θ : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => ((n+1 : ℝ)/Real.sin θ^2+1/Real.sin θ^3)*gaussianTerm a n) := by
  have h := ((weightedTerm_summable a ha).div_const (Real.sin θ^2)).add
    ((gaussianTerm_summable a ha).mul_left (1/Real.sin θ^3))
  apply h.congr
  intro n
  ring

lemma real_spectral_summable (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Summable (fun n : ℕ => realCoefficient θ n*gaussianTerm a n) := by
  apply Summable.of_norm_bounded (spectral_majorant_summable a θ ha)
  intro n
  rw [norm_mul, show ‖gaussianTerm a n‖ = gaussianTerm a n from
    by rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]]
  exact mul_le_mul_of_nonneg_right (coefficient_bound θ hθ hπ n).1 (Real.exp_pos _).le

lemma imaginary_spectral_summable (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Summable (fun n : ℕ => imaginaryCoefficient θ n*gaussianTerm a n) := by
  apply Summable.of_norm_bounded (spectral_majorant_summable a θ ha)
  intro n
  rw [norm_mul, show ‖gaussianTerm a n‖ = gaussianTerm a n from
    by rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianTerm a n from Real.exp_pos _)]]
  exact mul_le_mul_of_nonneg_right (coefficient_bound θ hθ hπ n).2 (Real.exp_pos _).le

lemma shifted_weight (a θ : ℝ) (k : ℤ) :
    weight a (2*k*Real.pi+θ) = PeriodicPoleTask.weight (4*a) (θ/2+k*Real.pi) := by
  unfold weight PeriodicPoleTask.weight
  congr 1
  ring

lemma poleMass_summable (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    Summable (fun k : ℤ => weight a (2*k*Real.pi+θ)+weight a (2*k*Real.pi-θ)) := by
  have hp : |θ/2| ≤ Real.pi/2 := by rw [abs_of_pos (by positivity : 0 < θ/2)]; linarith
  have hn : |(-θ)/2| ≤ Real.pi/2 := by rw [neg_div,abs_neg]; exact hp
  have h1 := PeriodicPoleTask.periodizedWeight_summable (4*a) (θ/2) (by positivity) hp
  have h2 := PeriodicPoleTask.periodizedWeight_summable (4*a) ((-θ)/2) (by positivity) hn
  have h := h1.add h2
  apply h.congr
  intro k
  rw [shifted_weight,show 2*(k : ℝ)*Real.pi-θ=2*k*Real.pi+(-θ) by ring,shifted_weight]

lemma poleMass_positive (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    0 < poleMass a θ := by
  apply (poleMass_summable a θ ha hθ hπ).tsum_pos
    (fun k => by unfold weight; positivity) 0
  unfold weight
  positivity

end ShiftedCosineTask

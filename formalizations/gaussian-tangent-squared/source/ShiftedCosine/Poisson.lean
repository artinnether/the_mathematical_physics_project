import ShiftedCosine.Mass
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace ShiftedCosineTask

lemma gaussian_lattice_poisson (a θ : ℝ) (ha : 0 < a) :
    (∑' k : ℤ, (weight a (2*k*Real.pi+θ) : ℂ)) =
      (1/Real.sqrt (4*Real.pi*a) : ℂ)*
        ∑' n : ℤ, (Real.exp (-((n : ℝ)^2)/(4*a)) : ℂ)*
          Complex.exp (((n : ℝ)*θ : ℝ)*Complex.I) := by
  have hp : 0 < 4*Real.pi*a := by positivity
  have hi := Complex.tsum_exp_neg_quadratic
    (a := (4*Real.pi*a : ℝ)) (by simpa using hp) ((-2*a*θ : ℝ) : ℂ)
  have hs : ((4*Real.pi*a : ℝ) : ℂ)^(1/2 : ℂ) = (Real.sqrt (4*Real.pi*a) : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hp.le]
    norm_num
  rw [hs] at hi
  have hl (k : ℤ) : (weight a (2*k*Real.pi+θ) : ℂ) =
      (Real.exp (-a*θ^2) : ℂ)*
        Complex.exp (-Real.pi*(4*Real.pi*a : ℝ)*(k : ℂ)^2+
          2*Real.pi*(-2*a*θ : ℝ)*(k : ℂ)) := by
    unfold weight
    simp_rw [Complex.ofReal_exp]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hl]
  rw [tsum_mul_left,hi]
  have hr (n : ℤ) : (Real.exp (-a*θ^2) : ℂ)*
      Complex.exp (-Real.pi/((4*Real.pi*a : ℝ) : ℂ)*
        ((n : ℂ)+Complex.I*((-2*a*θ : ℝ) : ℂ))^2) =
      (Real.exp (-((n : ℝ)^2)/(4*a)) : ℂ)*
        Complex.exp (((n : ℝ)*θ : ℝ)*Complex.I) := by
    simp_rw [Complex.ofReal_exp]
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    field_simp [ha.ne',Real.pi_ne_zero]
    ring_nf
    simp [Complex.I_sq]
  calc
    _ = (1/(Real.sqrt (4*Real.pi*a) : ℂ))*
        ((Real.exp (-a*θ^2) : ℂ)*∑' n : ℤ,
          Complex.exp (-Real.pi/((4*Real.pi*a : ℝ) : ℂ)*
            ((n : ℂ)+Complex.I*((-2*a*θ : ℝ) : ℂ))^2)) := by ring
    _ = _ := by
      rw [← tsum_mul_left]
      simp_rw [hr]

lemma integer_gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-((n : ℝ)^2)/(4*a))) := by
  have h := PeriodicPoleTask.gaussianPolynomial_summable_int (1/(4*a*Real.pi^2)) (by positivity) 0
  apply h.congr
  intro n
  simp only [pow_zero,one_mul]
  unfold PeriodicPoleTask.weight
  congr 1
  field_simp [Real.pi_ne_zero]

lemma poleMass_fourier (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    poleMass a θ = Real.sqrt (Real.pi/a)/Real.pi*
      (1+2*∑' n : ℕ, gaussianTerm a n*Real.cos ((n+1 : ℝ)*θ)) := by
  let f : ℤ → ℝ := fun n => Real.exp (-((n : ℝ)^2)/(4*a))*Real.cos ((n : ℝ)*θ)
  have hg := integer_gaussian_summable a ha
  have hcomplex : Summable (fun n : ℤ => (Real.exp (-((n : ℝ)^2)/(4*a)) : ℂ)*
      Complex.exp (((n : ℝ)*θ : ℝ)*Complex.I)) := by
    apply hg.of_norm_bounded
    intro n
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_one]
  have hreal : Summable f := by
    apply hg.of_norm_bounded
    intro n
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  have heven : Function.Even f := by
    intro n
    simp [f,neg_mul,Real.cos_neg]
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hreal
  have hp : (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, gaussianTerm a n*Real.cos ((n+1 : ℝ)*θ) := by
    convert tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ)) using 1
    simp only [f,gaussianTerm,Nat.cast_add,Nat.cast_one]
    push_cast
    rfl
  rw [hp] at hsplit
  simp only [f,Int.cast_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),neg_zero,zero_div,
    Real.exp_zero,zero_mul,Real.cos_zero,one_mul,nsmul_eq_mul,Nat.cast_ofNat] at hsplit
  have hw : Summable (fun k : ℤ => weight a (2*k*Real.pi+θ)) := by
    have h := PeriodicPoleTask.periodizedWeight_summable (4*a) (θ/2) (by positivity)
      (by rw [abs_of_pos (by positivity : 0 < θ/2)]; linarith)
    simpa only [shifted_weight] using h
  have hwc : Summable (fun k : ℤ => (weight a (2*k*Real.pi+θ) : ℂ)) := by
    apply hw.of_norm_bounded
    intro k
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < weight a (2*k*Real.pi+θ) from Real.exp_pos _)]
  have h := congrArg Complex.re (gaussian_lattice_poisson a θ ha)
  rw [← Complex.ofReal_one,← Complex.ofReal_div] at h
  rw [Complex.re_tsum hwc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_tsum hcomplex] at h
  simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,
    zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re] at h
  change (∑' k : ℤ, weight a (2*k*Real.pi+θ)) =
    (1/Real.sqrt (4*Real.pi*a))*(∑' n : ℤ, f n) at h
  rw [hsplit] at h
  have hm : poleMass a θ = 2*(∑' k : ℤ, weight a (2*k*Real.pi+θ)) := by
    rw [poleMass_eq a θ ha hθ hπ]
    congr 1
    unfold PeriodicPoleTask.periodizedWeight
    apply tsum_congr
    intro k
    rw [shifted_weight]
  rw [hm,h]
  have hs4 : Real.sqrt (4*Real.pi*a) = 2*Real.sqrt Real.pi*Real.sqrt a := by
    rw [show 4*Real.pi*a=4*(Real.pi*a) by ring,Real.sqrt_mul (by norm_num),Real.sqrt_mul Real.pi_pos.le]
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
    ring
  have hc : 2*(1/Real.sqrt (4*Real.pi*a)) = Real.sqrt (Real.pi/a)/Real.pi := by
    rw [hs4,Real.sqrt_div Real.pi_pos.le]
    field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne',(Real.sqrt_pos.2 ha).ne',Real.pi_ne_zero]
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  rw [← mul_assoc,hc]

end ShiftedCosineTask

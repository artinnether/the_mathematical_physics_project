import SimpleTangent.Basic
import ShiftedCosine.ComplexGeometric

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set
open scoped Topology
namespace TangentShiftTask

noncomputable def rootRadius (b ε : ℝ) : ℝ := Real.sqrt (b^4+ε^2)
noncomputable def rootRe (b ε : ℝ) : ℝ := Real.sqrt ((rootRadius b ε-b^2)/2)
noncomputable def rootIm (b ε : ℝ) : ℝ := Real.sqrt ((rootRadius b ε+b^2)/2)
noncomputable def regulatorRoot (b ε : ℝ) : ℂ := (rootRe b ε : ℂ)+Complex.I*(rootIm b ε : ℂ)
noncomputable def regulatorRatio (b ε : ℝ) : ℂ := (1-regulatorRoot b ε)/(1+regulatorRoot b ε)

lemma radius_ge (b ε : ℝ) : b^2 ≤ rootRadius b ε := by
  unfold rootRadius
  have h := Real.sq_sqrt (show 0 ≤ b^4+ε^2 by positivity)
  have hn := Real.sqrt_nonneg (b^4+ε^2)
  nlinarith [sq_nonneg ε]
lemma radius_gt (b ε : ℝ) (hε : 0 < ε) : b^2 < rootRadius b ε := by
  unfold rootRadius
  have h := Real.sq_sqrt (show 0 ≤ b^4+ε^2 by positivity)
  have hn := Real.sqrt_nonneg (b^4+ε^2)
  nlinarith [sq_pos_of_pos hε]
lemma rootRe_pos (b ε : ℝ) (hε : 0 < ε) : 0 < rootRe b ε := by
  apply Real.sqrt_pos.mpr
  exact div_pos (sub_pos.mpr (radius_gt b ε hε)) (by norm_num)
lemma root_squares (b ε : ℝ) :
    rootRe b ε^2=(rootRadius b ε-b^2)/2 ∧ rootIm b ε^2=(rootRadius b ε+b^2)/2 := by
  constructor
  · exact Real.sq_sqrt (div_nonneg (sub_nonneg.mpr (radius_ge b ε)) (by norm_num))
  · exact Real.sq_sqrt (by have h := Real.sqrt_nonneg (b^4+ε^2); change 0 ≤ (rootRadius b ε+b^2)/2; unfold rootRadius; positivity)
lemma root_product (b ε : ℝ) (hε : 0 < ε) : 2*rootRe b ε*rootIm b ε=ε := by
  obtain ⟨hu,hv⟩ := root_squares b ε
  have hr : rootRadius b ε^2=b^4+ε^2 := Real.sq_sqrt (by positivity)
  have hp : (2*rootRe b ε*rootIm b ε)^2=ε^2 := by
    calc
      _ = 4*rootRe b ε^2*rootIm b ε^2 := by ring
      _ = _ := by rw [hu,hv]; nlinarith [hr]
  have hn : 0 ≤ 2*rootRe b ε*rootIm b ε := by unfold rootRe rootIm; positivity
  nlinarith
lemma root_square (b ε : ℝ) (hε : 0 < ε) :
    regulatorRoot b ε^2=-(b : ℂ)^2+Complex.I*(ε : ℂ) := by
  obtain ⟨hu,hv⟩ := root_squares b ε
  have hp := root_product b ε hε
  apply Complex.ext <;>
    simp only [regulatorRoot, pow_two, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      zero_mul,mul_zero,one_mul,add_zero,zero_add,sub_zero,neg_zero]
  · nlinarith
  · nlinarith
lemma root_ne_zero (b ε : ℝ) (hε : 0 < ε) : regulatorRoot b ε ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [regulatorRoot] at hr
  exact (rootRe_pos b ε hε).ne' hr
lemma one_add_root_ne (b ε : ℝ) : 1+regulatorRoot b ε ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [regulatorRoot, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.zero_re,zero_mul,mul_zero,sub_zero,add_zero] at hr
  have hn : 0 ≤ rootRe b ε := Real.sqrt_nonneg _
  linarith
lemma ratio_norm_lt_one (b ε : ℝ) (hε : 0 < ε) : ‖regulatorRatio b ε‖ < 1 := by
  have hp := rootRe_pos b ε hε
  have hn : Complex.normSq (1-regulatorRoot b ε) < Complex.normSq (1+regulatorRoot b ε) := by
    simp only [regulatorRoot,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.one_re,Complex.one_im,zero_mul,mul_zero,one_mul,add_zero,zero_add,sub_zero,zero_sub]
    nlinarith
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hn
  unfold regulatorRatio
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (one_add_root_ne b ε))).mpr
  nlinarith [norm_nonneg (1-regulatorRoot b ε),norm_nonneg (1+regulatorRoot b ε)]
lemma root_at_zero (b : ℝ) (hb : 0 < b) : regulatorRoot b 0=Complex.I*(b : ℂ) := by
  have hr : rootRadius b 0=b^2 := by
    unfold rootRadius
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero,show b^4=(b^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg b)]
  simp only [regulatorRoot,rootRe,rootIm,hr,sub_self,zero_div,Real.sqrt_zero,
    Complex.ofReal_zero,zero_add]
  rw [show (b^2+b^2)/2=b^2 by ring,Real.sqrt_sq hb.le]
lemma root_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (regulatorRoot b) (𝓝[>] (0 : ℝ)) (𝓝 (Complex.I*(b : ℂ))) := by
  rw [← root_at_zero b hb]
  have hc : Continuous (regulatorRoot b) := by unfold regulatorRoot rootRe rootIm rootRadius; fun_prop
  exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
lemma ratio_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (regulatorRatio b) (𝓝[>] (0 : ℝ))
      (𝓝 ((1-Complex.I*(b : ℂ))/(1+Complex.I*(b : ℂ)))) := by
  have hd : 1+Complex.I*(b : ℂ) ≠ 0 := by
    rw [← root_at_zero b hb]; exact one_add_root_ne b 0
  exact (tendsto_const_nhds.sub (root_tendsto b hb)).div
    (tendsto_const_nhds.add (root_tendsto b hb)) hd

end TangentShiftTask

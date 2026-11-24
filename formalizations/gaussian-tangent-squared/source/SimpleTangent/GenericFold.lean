import SimpleTangent.SimpleCosine

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
namespace ShiftedCosineTask

lemma gaussian_fold_bounded (a : ℝ) (ha : 0 < a) (K : ℝ → ℂ)
    (hK : Continuous K) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖K x‖ ≤ C)
    (hshift : ∀ t (k : ℤ), K (t+k*(2*Real.pi))=K t) :
    (∫ x : ℝ,(weight a x : ℂ)*K x)=
      ∫ t in (-Real.pi)..Real.pi,(periodWeight a t : ℂ)*K t := by
  have hi : Integrable (fun x => (weight a x : ℂ)*K x) :=
    (integrable_exp_neg_mul_sq ha).ofReal.mul_bdd hK.aestronglyMeasurable
      (Eventually.of_forall hbound)
  rw [integral_eq_tsum_cells _ hi (2*Real.pi) (by positivity)]
  simp_rw [hshift]
  rw [show -(2*Real.pi)/2=-Real.pi by ring,show (2*Real.pi)/2=Real.pi by ring]
  let f : ℤ → C(ℝ,ℂ) := fun k => ⟨fun t => (weight a (t+k*(2*Real.pi)) : ℂ)*K t,
    (by apply Continuous.mul (by unfold weight; fun_prop) hK)⟩
  have hn : Summable (fun k : ℤ => ‖(f k).restrict (⟨uIcc (-Real.pi) Real.pi,isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply ((PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    apply (ContinuousMap.norm_le _ (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).2
    intro t
    have ht0 : (t : ℝ) ∈ uIcc (-Real.pi) Real.pi := t.property
    have ht : (t : ℝ) ∈ Icc (-Real.pi) Real.pi :=
      Eq.mp (congrArg (fun s : Set ℝ => (t : ℝ) ∈ s) (uIcc_of_le (by linarith [Real.pi_pos]))) ht0
    change ‖(weight a ((t : ℝ)+k*(2*Real.pi)) : ℂ)*K t‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0 < weight a ((t : ℝ)+k*(2*Real.pi)) from Real.exp_pos _)]
    have hw := weight_cell_bound a t k ha (abs_le.mpr ht)
    rw [show 2*(k : ℝ)*Real.pi+(t : ℝ)=(t : ℝ)+k*(2*Real.pi) by ring] at hw
    exact (mul_le_mul hw (hbound t) (norm_nonneg _)
      (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).trans_eq (by ring)
  change (∑' k : ℤ,∫ t in (-Real.pi)..Real.pi,f k t)=_
  rw [intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn]
  apply intervalIntegral.integral_congr
  intro t ht
  change (∑' k : ℤ,(weight a (t+k*(2*Real.pi)) : ℂ)*K t)=_
  rw [tsum_mul_right,← Complex.ofReal_tsum]
  congr 1
  rw [periodWeight_tsum]
  apply congrArg Complex.ofReal
  apply tsum_congr
  intro k
  congr 1
  ring


end ShiftedCosineTask

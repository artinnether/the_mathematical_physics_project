import SimpleTangent.GenericFold

set_option maxHeartbeats 1000000
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
namespace ShiftedCosineTask

lemma gaussian_interval_bound (a u v C : ℝ) (k : ℤ) (ha : 0 < a) (hC : 0 ≤ C)
    (K : ℝ → ℝ) (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi, ‖K t‖ ≤ C)
    (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v) :
    ‖∫ t in u..v, weight a (2*k*Real.pi+t)*K t‖ ≤
      2*Real.pi*C*PeriodicPoleTask.latticeMajorant (4*a) k := by
  have hm : 0 ≤ PeriodicPoleTask.latticeMajorant (4*a) k := by
    unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := C*PeriodicPoleTask.latticeMajorant (4*a) k)
    (f := fun t : ℝ => weight a (2*k*Real.pi+t)*K t) ?_
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)] at h
    have hlen : v-u ≤ 2*Real.pi := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlen (mul_nonneg hC hm)]
  · intro t ht
    rw [uIoc_of_le huv] at ht
    have ht' : t ∈ Icc (-Real.pi) Real.pi := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hw := weight_cell_bound a t k ha (abs_le.mpr ht')
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (show 0 < weight a (2*k*Real.pi+t) from Real.exp_pos _)]
    exact (mul_le_mul hw (hbound t ht') (norm_nonneg _) hm).trans_eq (by ring)

lemma gaussian_interval_fold (a u v C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (K : ℝ → ℝ) (hK : Continuous K)
    (hbound : ∀ t ∈ Icc (-Real.pi) Real.pi, ‖K t‖ ≤ C)
    (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v) :
    Summable (fun k : ℤ => ∫ t in u..v, weight a (2*k*Real.pi+t)*K t) ∧
    (∑' k : ℤ, ∫ t in u..v, weight a (2*k*Real.pi+t)*K t)=
      ∫ t in u..v, periodWeight a t*K t := by
  have hs : Summable (fun k : ℤ => ∫ t in u..v, weight a (2*k*Real.pi+t)*K t) :=
    ((PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).mul_left (2*Real.pi*C)).of_norm_bounded
      (fun k => gaussian_interval_bound a u v C k ha hC K hbound hu hv huv)
  refine ⟨hs,?_⟩
  let f : ℤ → C(ℝ,ℝ) := fun k => ⟨fun t => weight a (2*k*Real.pi+t)*K t,
    (by apply Continuous.mul (by unfold weight; fun_prop) hK)⟩
  have hn : Summable (fun k : ℤ => ‖(f k).restrict (⟨uIcc u v,isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply ((PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    apply (ContinuousMap.norm_le _ (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).2
    intro t
    have ht0 : (t : ℝ) ∈ uIcc u v := t.property
    have ht1 : (t : ℝ) ∈ Icc u v := Eq.mp (congrArg (fun s : Set ℝ => (t : ℝ) ∈ s) (uIcc_of_le huv)) ht0
    have ht : (t : ℝ) ∈ Icc (-Real.pi) Real.pi := ⟨by linarith [ht1.1],by linarith [ht1.2]⟩
    change ‖weight a (2*k*Real.pi+(t : ℝ))*K t‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (show 0 < weight a (2*k*Real.pi+(t : ℝ)) from Real.exp_pos _)]
    have hw := weight_cell_bound a t k ha (abs_le.mpr ht)
    exact (mul_le_mul hw (hbound t ht) (norm_nonneg _)
      (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).trans_eq (by ring)
  change (∑' k : ℤ, ∫ t in u..v,f k t)=_
  rw [intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn]
  apply intervalIntegral.integral_congr
  intro t ht
  change (∑' k : ℤ,weight a (2*k*Real.pi+t)*K t)=_
  rw [tsum_mul_right,← periodWeight_tsum]

end ShiftedCosineTask

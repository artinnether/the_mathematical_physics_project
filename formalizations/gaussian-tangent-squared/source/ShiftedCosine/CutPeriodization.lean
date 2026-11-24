import ShiftedCosine.RemainderIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology
namespace ShiftedCosineTask

lemma periodWeight_tsum (a t : ℝ) : periodWeight a t = ∑' k : ℤ, weight a (2*k*Real.pi+t) := by
  unfold periodWeight PeriodicPoleTask.periodizedWeight
  simp_rw [shifted_weight]

noncomputable def clippedWeight (a θ C : ℝ) (k : ℤ) (t : ℝ) : ℝ :=
  weight a (2*k*Real.pi+t)/max ((Real.cos t-Real.cos θ)^2) (1/(C+1))

lemma clippedWeight_continuous (a θ C : ℝ) (k : ℤ) (hC : 0 ≤ C) :
    Continuous (clippedWeight a θ C k) := by
  unfold clippedWeight weight
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact (lt_of_lt_of_le (by positivity : 0 < 1/(C+1)) (le_max_right _ _)).ne'

lemma clippedWeight_bound (a θ C t : ℝ) (k : ℤ) (ha : 0 < a) (hC : 0 ≤ C) (ht : |t| ≤ Real.pi) :
    ‖clippedWeight a θ C k t‖ ≤ PeriodicPoleTask.latticeMajorant (4*a) k*(C+1) := by
  have hf : 0 < 1/(C+1) := by positivity
  have hd : 0 < max ((Real.cos t-Real.cos θ)^2) (1/(C+1)) := lt_of_lt_of_le hf (le_max_right _ _)
  unfold clippedWeight
  rw [norm_div,Real.norm_eq_abs,abs_of_pos (show 0 < weight a (2*k*Real.pi+t) from Real.exp_pos _),
    Real.norm_eq_abs,abs_of_pos hd]
  have hw := weight_cell_bound a t k ha ht
  have hm : 0 ≤ PeriodicPoleTask.latticeMajorant (4*a) k := by
    unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity
  have h := div_le_div₀ hm hw hf (le_max_right ((Real.cos t-Real.cos θ)^2) (1/(C+1)))
  exact h.trans_eq (by field_simp)

lemma clippedWeight_eq (a θ δ C t : ℝ) (k : ℤ) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ excludedCell θ δ, ‖1/(Real.cos t-Real.cos θ)^2‖ ≤ C)
    (ht : t ∈ excludedCell θ δ) :
    clippedWeight a θ C k t=weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2 := by
  have hq := cut_cos_ne θ δ t hθ hπ hδ ht
  have hq2 := sq_pos_of_ne_zero hq
  have hb := hbound t ht
  rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1/(Real.cos t-Real.cos θ)^2)] at hb
  have hfloor : 1/(C+1) ≤ (Real.cos t-Real.cos θ)^2 := by
    apply (div_le_iff₀ (by positivity : 0 < C+1)).2
    have hb := (div_le_iff₀ hq2).mp hb
    nlinarith
  unfold clippedWeight
  rw [max_eq_left hfloor]

lemma folded_cut_integral (a θ δ u v : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v)
    (hsubset : Icc u v ⊆ excludedCell θ δ) :
    (∑' k : ℤ, ∫ t in u..v, weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2)=
      ∫ t in u..v, periodWeight a t/(Real.cos t-Real.cos θ)^2 := by
  obtain ⟨C,hC,hbound⟩ := cut_kernel_bounded θ δ hθ hπ hδ
  let f : ℤ → C(ℝ,ℝ) := fun k => ⟨clippedWeight a θ C k,clippedWeight_continuous a θ C k hC⟩
  have hm := (PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).mul_right (C+1)
  have hn : Summable (fun k : ℤ => ‖(f k).restrict (⟨uIcc u v,isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply hm.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    apply (ContinuousMap.norm_le _ (by unfold PeriodicPoleTask.latticeMajorant PeriodicPoleTask.weight; positivity)).2
    intro t
    have ht0 : (t : ℝ) ∈ uIcc u v := t.property
    have ht : (t : ℝ) ∈ Icc u v := Eq.mp (congrArg (fun s : Set ℝ => (t : ℝ) ∈ s) (uIcc_of_le huv)) ht0
    exact clippedWeight_bound a θ C t k ha hC (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hi := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hn
  calc
    _ = ∑' k : ℤ, ∫ t in u..v, f k t := by
      apply tsum_congr
      intro k
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      exact (clippedWeight_eq a θ δ C t k hθ hπ hδ hC hbound (hsubset ht)).symm
    _ = ∫ t in u..v, ∑' k : ℤ, f k t := hi
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      change (∑' k : ℤ, clippedWeight a θ C k t) = _
      simp_rw [clippedWeight_eq a θ δ C t _ hθ hπ hδ hC hbound (hsubset ht)]
      rw [tsum_div_const,← periodWeight_tsum]

lemma outerValue_periodized (a θ δ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hδ : 0 < δ) (hδθ : δ < θ) (hδπ : δ < Real.pi-θ) :
    outerValue a θ δ=cutIntegral θ δ (fun t => periodWeight a t/(Real.cos t-Real.cos θ)^2) := by
  obtain ⟨C,hC,hbound⟩ := cut_kernel_bounded θ δ hθ hπ hδ
  have hs (u v : ℝ) (hu : -Real.pi ≤ u) (hv : v ≤ Real.pi) (huv : u ≤ v)
      (hsubset : Icc u v ⊆ excludedCell θ δ) :
      Summable (fun k : ℤ => ∫ t in u..v, weight a (2*k*Real.pi+t)/(Real.cos t-Real.cos θ)^2) :=
    ((PeriodicPoleTask.latticeMajorant_summable (4*a) (by positivity)).mul_left (2*Real.pi*C)).of_norm_bounded
      (fun k => interval_cell_bound a θ δ u v C k ha hC hbound hu hv huv hsubset)
  have hl := hs (-Real.pi) (-θ-δ) le_rfl (by linarith) (by linarith) (fun t ht => Or.inl (Or.inl ht))
  have hm := hs (-θ+δ) (θ-δ) (by linarith) (by linarith) (by linarith) (fun t ht => Or.inl (Or.inr ht))
  have hr := hs (θ+δ) Real.pi (by linarith) le_rfl (by linarith) (fun t ht => Or.inr ht)
  unfold outerValue cell cutIntegral
  rw [(hl.add hm).tsum_add hr,hl.tsum_add hm]
  rw [folded_cut_integral a θ δ (-Real.pi) (-θ-δ) ha hθ hπ hδ le_rfl (by linarith) (by linarith)
      (fun t ht => Or.inl (Or.inl ht)),
    folded_cut_integral a θ δ (-θ+δ) (θ-δ) ha hθ hπ hδ (by linarith) (by linarith) (by linarith)
      (fun t ht => Or.inl (Or.inr ht)),
    folded_cut_integral a θ δ (θ+δ) Real.pi ha hθ hπ hδ (by linarith) le_rfl (by linarith)
      (fun t ht => Or.inr ht)]

end ShiftedCosineTask

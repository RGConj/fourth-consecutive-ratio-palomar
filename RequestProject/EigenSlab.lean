module

public import RequestProject.SobolevClip
public import RequestProject.L2FiniteIntegrable

/-! # Testing the actual weak eigenfunction equation on a level slab -/

@[expose] public section
open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio
variable {N : ℕ}

def eigenSlab (p : Amb N) (a b : ℝ) : Set (RN N) :=
  {x | a < (p.1 : RN N → ℝ) x ∧ (p.1 : RN N → ℝ) x < b}

lemma measurableSet_eigenSlab (p : Amb N) (a b : ℝ) : MeasurableSet (eigenSlab p a b) :=
  (measurableSet_lt measurable_const (Lp.stronglyMeasurable p.1).measurable).inter
    (measurableSet_lt (Lp.stronglyMeasurable p.1).measurable measurable_const)

lemma clipPair_norm_integral (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) :
    (∫ x, ‖((clipPair a b ha hb p).2 : RN N → RN N) x‖) =
      ∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖ := by
  rw [← integral_indicator (measurableSet_eigenSlab p a b)]
  apply integral_congr_ae
  filter_upwards [clipPair_snd_ae a b ha hb hab hp] with x hx
  rw [hx]
  by_cases hs : a < (p.1 : RN N → ℝ) x ∧ (p.1 : RN N → ℝ) x < b
  · simp only [if_pos hs, indicator_of_mem (show x ∈ eigenSlab p a b from hs)]
  · simp only [if_neg hs, norm_zero, indicator_of_notMem (show x ∉ eigenSlab p a b from hs)]

/-- Exact energy identity on a strict slab obtained by a genuine H₀¹ test. -/
theorem eigen_slab_energy_identity {D : Set (RN N)} {p : Amb N} {lam : ℝ}
    (hp : IsEigenfunction D p lam) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    (∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖ ^ 2) =
      lam * ∫ x, (p.1 : RN N → ℝ) x * clipValue a b ((p.1 : RN N → ℝ) x) := by
  have hw := hp.2.2 (clipPair a b ha hb p) (clipPair_mem_H a b ha hb hp.1)
  have hl : qf p (clipPair a b ha hb p) =
      ∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖ ^ 2 := by
    rw [qf, L2.inner_def, ← integral_indicator (measurableSet_eigenSlab p a b)]
    apply integral_congr_ae
    filter_upwards [clipPair_snd_ae a b ha hb hab hp.1] with x hx
    rw [hx]
    by_cases hs : x ∈ eigenSlab p a b
    · have hs' : a < (p.1 : RN N → ℝ) x ∧ (p.1 : RN N → ℝ) x < b := hs
      simp [hs', hs, real_inner_self_eq_norm_sq]
    · have hs' : ¬ (a < (p.1 : RN N → ℝ) x ∧ (p.1 : RN N → ℝ) x < b) := hs
      simp [hs', hs]
  have hr : l2 p (clipPair a b ha hb p) =
      ∫ x, (p.1 : RN N → ℝ) x * clipValue a b ((p.1 : RN N → ℝ) x) := by
    rw [l2, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [clipPair_fst_ae a b ha hb p] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  rwa [hl, hr] at hw

/-- The slab energy is bounded by eigenvalue times slab height times tail mass. -/
theorem eigen_slab_energy_le {D : Set (RN N)} {p : Amb N} {lam : ℝ}
    (hp : IsEigenfunction D p lam) (hlam : 0 ≤ lam)
    (hpi : Integrable (p.1 : RN N → ℝ) volume)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    (∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖ ^ 2) ≤
      lam * ((b - a) * ∫ x in {x | a < (p.1 : RN N → ℝ) x}, (p.1 : RN N → ℝ) x) := by
  rw [eigen_slab_energy_identity hp a b ha hb hab]
  apply mul_le_mul_of_nonneg_left _ hlam
  let A := {x | a < (p.1 : RN N → ℝ) x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (Lp.stronglyMeasurable p.1).measurable
  have hprod : Integrable (fun x => (p.1 : RN N → ℝ) x * clipValue a b ((p.1 : RN N → ℝ) x)) volume := by
    have hi := L2.integrable_inner (𝕜 := ℝ) p.1 (clipPair a b ha hb p).1
    apply hi.congr
    filter_upwards [clipPair_fst_ae a b ha hb p] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  rw [← integral_const_mul, ← integral_indicator hA]
  apply integral_mono_ae hprod ((hpi.const_mul (b - a)).indicator hA)
  filter_upwards [hp0] with x hx
  by_cases hxa : a < (p.1 : RN N → ℝ) x
  · rw [indicator_of_mem hxa]
    exact (mul_le_mul_of_nonneg_left (clipValue_le_height hab _) hx).trans_eq (mul_comm _ _)
  · rw [indicator_of_notMem hxa, clipValue_eq_zero hab (not_lt.mp hxa), mul_zero]

end FourthRatio
end

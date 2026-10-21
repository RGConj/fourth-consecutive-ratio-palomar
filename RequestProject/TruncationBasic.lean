module

public import RequestProject.Localization

/-!
# Elementary facts on truncations and positivity (part 1)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma L2_coeFn_sum {ι : Type*} (s : Finset ι) (g : ι → L2 N) :
    ((∑ i ∈ s, g i : L2 N) : RN N → ℝ) =ᵐ[volume] fun x => ∑ i ∈ s, (g i : RN N → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 volume] with x hx
    exact hx
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (g j) (∑ i ∈ s, g i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hj]

lemma L2v_coeFn_sum {ι : Type*} (s : Finset ι) (g : ι → L2v N) :
    ((∑ i ∈ s, g i : L2v N) : RN N → RN N) =ᵐ[volume] fun x => ∑ i ∈ s, (g i : RN N → RN N) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (RN N) 2 volume] with x hx
    exact hx
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (g j) (∑ i ∈ s, g i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hj]

lemma negPart_neg (v : Amb N) : negPart (-v) = posPart v := by
  simp [negPart]

lemma posPart_neg (v : Amb N) : posPart (-v) = negPart v := rfl

lemma H_empty_eq (v : Amb N) (hv : v ∈ H (∅ : Set (RN N))) : v = 0 := by
  obtain ⟨h1, h2⟩ := mem_vanishOn.mp (H_le_vanishOn _ hv)
  simp only [Set.compl_empty, Measure.restrict_univ] at h1 h2
  exact Prod.ext (Lp.eq_zero_iff_ae_eq_zero.mpr h1) (Lp.eq_zero_iff_ae_eq_zero.mpr h2)

lemma nonempty_of_mem_H {D : Set (RN N)} {v : Amb N} (hv : v ∈ H D) (h0 : v ≠ 0) :
    D.Nonempty := by
  rcases D.eq_empty_or_nonempty with rfl | h
  · exact absurd (H_empty_eq v hv) h0
  · exact h

/-- `v₊ - v₋ = v` for `v ∈ H_D ∩ C(D)` (uses Lemma 3.1 and closability). -/
lemma posPart_sub_negPart {D : Set (RN N)} (hD : IsAdmissible D) {v : Amb N}
    (hv : v ∈ H D) {f : RN N → ℝ} (hf : IsContRep D v f) : posPart v - negPart v = v := by
  have hp := (parts_mem hD hv hf).1
  have hn := (parts_mem hD hv hf).2
  have hmem : posPart v - negPart v - v ∈ H D :=
    (H D).sub_mem ((H D).sub_mem (H_mono (posSign_subset D f) hp)
      (H_mono (negSign_subset D f) hn)) hv
  have h1 : (posPart v - negPart v - v).1 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    simp only [Prod.fst_sub]
    filter_upwards [Lp.coeFn_sub (posPart v - negPart v).1 v.1,
      Lp.coeFn_sub (posPart v).1 (negPart v).1, posPart_fst_ae v, negPart_fst_ae v]
      with x h1 h2 h3 h4
    simp only [Prod.fst_sub] at h1
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, Pi.zero_apply]
    rcases le_total ((v.1 : RN N → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have h0 : l2 (posPart v - negPart v - v) (posPart v - negPart v - v) = 0 := by
    rw [l2, h1, inner_zero_left]
  have := eq_zero_of_l2_self_eq_zero hmem h0
  exact sub_eq_zero.mp this

/-- If `v ∈ H_D` has a continuous representative which is positive on `D`, then `v₊ = v` and
`v₋ = 0`. -/
lemma posPart_eq_self_of_pos {D : Set (RN N)} (hDm : MeasurableSet D) {v : Amb N}
    (hv : v ∈ H D) {f : RN N → ℝ} (hf : IsContRep D v f) (hpos : ∀ x ∈ D, 0 < f x) :
    posPart v = v ∧ negPart v = 0 := by
  obtain ⟨hv1, hv2⟩ := mem_vanishOn.mp (H_le_vanishOn D hv)
  rw [EventuallyEq, ae_restrict_iff' hDm.compl] at hv1 hv2
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  -- `v ≥ 0` a.e., and `v > 0` a.e. on `D`
  have hnn : ∀ᵐ x ∂volume, 0 ≤ (v.1 : RN N → ℝ) x ∧
      (x ∈ D → 0 < (v.1 : RN N → ℝ) x) ∧ (x ∉ D → (v.2 : RN N → RN N) x = 0) := by
    filter_upwards [hv1, hv2, hf2] with x h1 h2 h3
    by_cases hx : x ∈ D
    · exact ⟨(h3 hx ▸ hpos x hx).le, fun _ => h3 hx ▸ hpos x hx, fun h => absurd hx h⟩
    · exact ⟨(h1 hx).symm ▸ le_rfl, fun h => absurd h hx, fun _ => h2 hx⟩
  constructor
  · refine Prod.ext ?_ ?_
    · refine Lp.ext ?_
      filter_upwards [posPart_fst_ae v, hnn] with x h1 h2
      rw [h1, max_eq_left h2.1]
    · refine Lp.ext ?_
      filter_upwards [posPart_snd_ae v, hnn] with x h1 h2
      rw [h1]
      by_cases hx : x ∈ D
      · rw [Set.indicator_of_mem (show x ∈ posSetL2 v.1 from h2.2.1 hx)]
      · simp [h2.2.2 hx]
  · refine Prod.ext ?_ ?_
    · refine Lp.ext ?_
      filter_upwards [negPart_fst_ae v, hnn, Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))]
        with x h1 h2 h3
      rw [h1, Prod.fst_zero, h3, Pi.zero_apply, max_eq_right (neg_nonpos.mpr h2.1)]
    · refine Lp.ext ?_
      filter_upwards [posPart_snd_ae (-v), hnn, Lp.coeFn_neg v.1,
        Lp.coeFn_zero (RN N) 2 (volume : Measure (RN N))] with x h1 h2 h3 h4
      rw [negPart, h1, Prod.snd_zero, h4, Pi.zero_apply]
      refine Set.indicator_of_notMem ?_ _
      simp only [posSetL2, Set.mem_setOf_eq, Prod.fst_neg, h3, Pi.neg_apply, not_lt]
      linarith [h2.1]

/-- Positivity of the `L²` pairing of a nonnegative nonzero element of `H_D` with a function
whose continuous representative is positive on `D`. -/
lemma l2_pos_of_nonneg {D : Set (RN N)} (hD : IsAdmissible D) {w g : Amb N}
    (hw : w ∈ H D) (hw0 : w ≠ 0) (hwnn : 0 ≤ᵐ[volume] (w.1 : RN N → ℝ))
    (hg : g ∈ H D) {f : RN N → ℝ} (hf : IsContRep D g f) (hpos : ∀ x ∈ D, 0 < f x) :
    0 < l2 w g := by
  have hDm : MeasurableSet D := hD.1.measurableSet
  obtain ⟨hg1, -⟩ := mem_vanishOn.mp (H_le_vanishOn D hg)
  obtain ⟨hw1, -⟩ := mem_vanishOn.mp (H_le_vanishOn D hw)
  rw [EventuallyEq, ae_restrict_iff' hDm.compl] at hg1 hw1
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  have hint := L2.integrable_inner (𝕜 := ℝ) w.1 g.1
  have hnn : 0 ≤ᵐ[volume] fun x => ⟪(w.1 : RN N → ℝ) x, (g.1 : RN N → ℝ) x⟫ := by
    filter_upwards [hwnn, hg1, hf2] with x h1 h2 h3
    simp only [Pi.zero_apply, RCLike.inner_apply, conj_trivial]
    by_cases hx : x ∈ D
    · rw [h3 hx]; exact mul_nonneg (hpos x hx).le h1
    · rw [h2 hx]; simp
  rw [l2, L2.inner_def]
  refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) ?_
  intro h0
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0.symm
  have hw1z : w.1 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hz, hw1, hf2] with x h1 h2 h3
    simp only [Pi.zero_apply, RCLike.inner_apply, conj_trivial] at h1 ⊢
    by_cases hx : x ∈ D
    · rw [h3 hx] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (hpos x hx).ne'
      · exact h
    · exact h2 hx
  exact hw0 (eq_zero_of_l2_self_eq_zero hw (by rw [l2, hw1z, inner_zero_left]))

end FourthRatio

end

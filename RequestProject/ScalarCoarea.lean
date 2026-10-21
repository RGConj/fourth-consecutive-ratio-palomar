module

/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Scalar coarea

This file proves Federer's weighted scalar coarea formula for globally Lipschitz maps from a
finite-dimensional Euclidean space to the real line.  The proof combines the equal-dimensional
change-of-variables theorem, Rademacher's theorem, and normalized Euclidean Hausdorff measure:

* regular level sets are covered by countably many bi-Lipschitz coordinate graphs;
* an injective lower-dimensional area formula computes each graph slice;
* an Eilenberg covering argument eliminates critical fibers almost everywhere;
* Rademacher's theorem eliminates the remaining nondifferentiability set.

The principal result is `LipschitzWith.scalarCoareaFormula`; weighted lower-dimensional chart
identities and direct slab corollaries for maps whose derivative norm is one almost everywhere
are developed alongside it.
-/

@[expose] public section

open Set MeasureTheory MeasureTheory.Measure Metric Filter Module Asymptotics TopologicalSpace
open scoped ENNReal NNReal Function Topology Pointwise

noncomputable section

namespace ProbabilityTheory

/-- The scalar Jacobian of a map from Euclidean space to the real line.  At points where the map
is not differentiable, Mathlib's `fderiv` is definitionally zero. -/
def scalarJacobian {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal ‖fderiv ℝ f x‖

/-- The weighted Euclidean codimension-one content of one level fiber. -/
def scalarCoareaFiber {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in f ⁻¹' {t}, w x ∂(Measure.euclideanHausdorffMeasure (d - 1))

/-- The scalar Jacobian is Borel measurable for every map. -/
@[fun_prop]
theorem measurable_scalarJacobian {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Measurable (scalarJacobian f) := by
  exact ENNReal.measurable_ofReal.comp
    (continuous_norm.measurable.comp (measurable_fderiv ℝ f))

/-- Every level fiber of a Lipschitz scalar map is Borel measurable. -/
theorem measurableSet_lipschitz_fiber {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f) (t : ℝ) :
    MeasurableSet (f ⁻¹' {t}) := by
  exact measurableSet_singleton t |>.preimage hf.continuous.measurable

/-- The inverse image of a half-open interval under a Lipschitz scalar map is Borel measurable. -/
theorem measurableSet_lipschitz_slab {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f) (a b : ℝ) :
    MeasurableSet (f ⁻¹' Ioc a b) := by
  exact measurableSet_Ioc.preimage hf.continuous.measurable

/-- Inserting a slab indicator into the weight inserts the same interval indicator into the
level-fiber profile.  This is the pointwise set algebra needed for the slab form of coarea. -/
theorem scalarCoareaFiber_indicator_lipschitz_slab {d : ℕ}
    {C : ℝ≥0} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (a b t : ℝ) :
    scalarCoareaFiber f ((f ⁻¹' Ioc a b).indicator w) t =
      (Ioc a b).indicator (scalarCoareaFiber f w) t := by
  have hfiber := measurableSet_lipschitz_fiber hf t
  by_cases ht : t ∈ Ioc a b
  · rw [indicator_of_mem ht]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hfiber] with x hx
    have hxs : x ∈ f ⁻¹' Ioc a b := by
      change f x ∈ Ioc a b
      simpa only [mem_preimage, mem_singleton_iff] using hx.symm ▸ ht
    rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem ht]
    calc
      scalarCoareaFiber f ((f ⁻¹' Ioc a b).indicator w) t =
          ∫⁻ _x in f ⁻¹' {t}, 0
            ∂(Measure.euclideanHausdorffMeasure (d - 1)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hfiber] with x hx
        have hxs : x ∉ f ⁻¹' Ioc a b := by
          change f x ∉ Ioc a b
          simpa only [mem_preimage, mem_singleton_iff] using hx.symm ▸ ht
        rw [indicator_of_notMem hxs]
      _ = 0 := by simp

/-- The outer integral of a slab-indicated weight is exactly the corresponding set integral of
the unmodified level-fiber profile. -/
theorem lintegral_scalarCoareaFiber_indicator_lipschitz_slab {d : ℕ}
    {C : ℝ≥0} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (a b : ℝ) :
    ∫⁻ t, scalarCoareaFiber f ((f ⁻¹' Ioc a b).indicator w) t =
      ∫⁻ t in Ioc a b, scalarCoareaFiber f w t := by
  simp_rw [scalarCoareaFiber_indicator_lipschitz_slab f hf w a b]
  exact lintegral_indicator measurableSet_Ioc _

/-- Federer's weighted scalar coarea identity, packaged as a reusable property of a scalar map. -/
def ScalarCoareaFormula {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞), Measurable w →
    ∫⁻ x, scalarJacobian f x * w x ∂volume =
      ∫⁻ t : ℝ, scalarCoareaFiber f w t

/-- Points of a set where the derivative of an endomorphism is invertible. -/
def fderivNondegenerateSet {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (s : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  s ∩ {x | (fderiv ℝ g x).det ≠ 0}

/-- The nondegenerate derivative region of a measurable set is measurable. -/
theorem measurableSet_fderivNondegenerateSet {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s) :
    MeasurableSet (fderivNondegenerateSet g s) := by
  apply hs.inter
  exact (measurableSet_singleton 0).compl.preimage
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ g))

/-- The absolute-determinant density vanishes off the nondegenerate derivative region. -/
theorem setLIntegral_abs_det_mul_eq_fderivNondegenerateSet {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume) =
      ∫⁻ x in fderivNondegenerateSet g s,
        ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume := by
  have hrset := measurableSet_fderivNondegenerateSet g hs
  rw [← lintegral_indicator hs, ← lintegral_indicator hrset]
  apply lintegral_congr
  intro x
  by_cases hxs : x ∈ s
  · by_cases hdetx : (fderiv ℝ g x).det ≠ 0
    · simp [fderivNondegenerateSet, hxs, hdetx]
    · have hzero : (fderiv ℝ g x).det = 0 := not_ne_iff.mp hdetx
      simp [fderivNondegenerateSet, hxs, hzero]
  · simp [fderivNondegenerateSet, hxs]

/-- The nondegenerate region of a differentiable endomorphism admits a countable measurable
cover by pairwise-disjoint ambient pieces on each of which the map is injective.  This is the
local-injectivity partition underlying the area formula with multiplicity. -/
theorem exists_measurable_injOn_partition_of_det_fderiv_ne_zero {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (s : Set (EuclideanSpace ℝ (Fin d)))
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x)
    (hdet : ∀ x ∈ s, (fderiv ℝ g x).det ≠ 0) :
    ∃ t : ℕ → Set (EuclideanSpace ℝ (Fin d)),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          s ⊆ ⋃ n, t n ∧
            (∀ n, InjOn g (s ∩ t n)) ∧
              ∀ n, ∃ K : ℝ≥0,
                AntilipschitzWith K ((s ∩ t n).restrict g) := by
  classical
  let r : (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) → ℝ≥0 := fun A ↦
    if _hE : Subsingleton (EuclideanSpace ℝ (Fin d)) then 1
    else if hA : A.det = 0 then 1
    else ‖((A.toContinuousLinearEquivOfDetNeZero hA).symm :
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖₊⁻¹ / 2
  have hrpos : ∀ A, r A ≠ 0 := by
    intro A
    by_cases hE : Subsingleton (EuclideanSpace ℝ (Fin d))
    · simp [r, hE]
    by_cases hA : A.det = 0
    · simp [r, hE, hA]
    let B := A.toContinuousLinearEquivOfDetNeZero hA
    have hnorm : 0 < ‖(B.symm :
        EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖₊ := by
      simpa [hE] using B.subsingleton_or_nnnorm_symm_pos.resolve_left hE
    simp only [r, hE, hA, dite_false]
    exact div_ne_zero (inv_ne_zero hnorm.ne') (by norm_num)
  obtain ⟨t, A, ht_disj, ht_meas, ht_cover, ht_approx, ht_source⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt g s
      (fderiv ℝ g) (fun x hx ↦ (hg x hx).hasFDerivAt.hasFDerivWithinAt) r hrpos
  have hanti (n : ℕ) : ∃ K : ℝ≥0,
      AntilipschitzWith K ((s ∩ t n).restrict g) := by
    rcases eq_empty_or_nonempty s with hs | hs
    · refine ⟨1, ?_⟩
      intro x _y
      have hx : x.1 ∈ (∅ : Set (EuclideanSpace ℝ (Fin d))) := by
        simpa [hs] using x.property.1
      exact hx.elim
    obtain ⟨y, hy, hAy⟩ := ht_source hs n
    have hA : (A n).det ≠ 0 := by
      rw [hAy]
      exact hdet y hy
    let B := (A n).toContinuousLinearEquivOfDetNeZero hA
    by_cases hE : Subsingleton (EuclideanSpace ℝ (Fin d))
    · exact ⟨1, AntilipschitzWith.of_subsingleton⟩
    have hnorm : 0 < ‖(B.symm :
        EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖₊ := by
      simpa [hE] using B.subsingleton_or_nnnorm_symm_pos.resolve_left hE
    have happ : ApproximatesLinearOn g
        (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (s ∩ t n)
        (‖(B.symm : EuclideanSpace ℝ (Fin d) →L[ℝ]
          EuclideanSpace ℝ (Fin d))‖₊⁻¹ / 2) := by
      simpa [r, hE, hA, B, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
        ht_approx n
    exact ⟨_, happ.antilipschitz
      (Or.inr (NNReal.half_lt_self (inv_ne_zero hnorm.ne')))⟩
  exact ⟨t, ht_disj, ht_meas, ht_cover,
    fun n ↦ injOn_iff_injective.2 (hanti n).choose_spec.injective, hanti⟩

/-- Pull a weight back along the measurable inverse of a measurable embedding.  Values outside
the range are immaterial and are supplied by `MeasurableEmbedding.invFun`. -/
noncomputable def measurableEmbeddingInverseWeight
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Nonempty α]
    {f : α → β} (hf : MeasurableEmbedding f) (w : α → ℝ≥0∞) : β → ℝ≥0∞ :=
  w ∘ hf.invFun

/-- Measurability of a weight pulled back by the inverse of a measurable embedding. -/
theorem measurable_measurableEmbeddingInverseWeight
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Nonempty α]
    {f : α → β} (hf : MeasurableEmbedding f) {w : α → ℝ≥0∞} (hw : Measurable w) :
    Measurable (measurableEmbeddingInverseWeight hf w) :=
  hw.comp hf.measurable_invFun

/-- On the range, pulling a weight back by a measurable embedding recovers the source value. -/
@[simp]
theorem measurableEmbeddingInverseWeight_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Nonempty α]
    {f : α → β} (hf : MeasurableEmbedding f) (w : α → ℝ≥0∞) (x : α) :
    measurableEmbeddingInverseWeight hf w (f x) = w x := by
  rw [measurableEmbeddingInverseWeight, Function.comp_apply, hf.leftInverse_invFun x]

/-- Equal-dimensional area formula with multiplicity, represented by a countable family of
injective images.  Critical points contribute zero on the source and their image is null; every
regular preimage contributes once through the unique disjoint source piece containing it. -/
theorem exists_area_multiplicity_partition {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x) :
    ∃ t : ℕ → Set (EuclideanSpace ℝ (Fin d)),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          fderivNondegenerateSet g s = ⋃ n, fderivNondegenerateSet g s ∩ t n ∧
            (∀ n, InjOn g (fderivNondegenerateSet g s ∩ t n)) ∧
              (∀ n, ∃ K : ℝ≥0, AntilipschitzWith K
                ((fderivNondegenerateSet g s ∩ t n).restrict g)) ∧
                ∀ (h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞), Measurable h →
                  ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ g x).det| * h (g x) ∂volume =
                    ∫⁻ y, ∑' n,
                      (g '' (fderivNondegenerateSet g s ∩ t n)).indicator h y := by
  let rset := fderivNondegenerateSet g s
  have hrset : MeasurableSet rset := measurableSet_fderivNondegenerateSet g hs
  obtain ⟨t, ht_disj, ht_meas, ht_cover, ht_inj, ht_anti⟩ :=
    exists_measurable_injOn_partition_of_det_fderiv_ne_zero g rset
      (fun x hx ↦ hg x hx.1) (fun x hx ↦ hx.2)
  have ht_cover_eq : rset = ⋃ n, rset ∩ t n := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp (ht_cover hx)
      exact mem_iUnion.mpr ⟨n, hx, hxn⟩
    · exact iUnion_subset fun _ ↦ inter_subset_left
  refine ⟨t, ht_disj, ht_meas, ht_cover_eq, ht_inj, ht_anti, ?_⟩
  intro h hh
  have hrestrict :
      (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ g x).det| * h (g x) ∂volume) =
        ∫⁻ x in rset, ENNReal.ofReal |(fderiv ℝ g x).det| * h (g x) ∂volume := by
    exact setLIntegral_abs_det_mul_eq_fderivNondegenerateSet g hs (fun x ↦ h (g x))
  rw [hrestrict, ht_cover_eq]
  rw [lintegral_iUnion (fun n ↦ hrset.inter (ht_meas n))
    (pairwise_disjoint_mono ht_disj fun _ ↦ inter_subset_right)]
  have himage (n : ℕ) : MeasurableSet (g '' (rset ∩ t n)) := by
    apply measurable_image_of_fderivWithin (hrset.inter (ht_meas n))
      (fun x hx ↦ (hg x hx.1.1).hasFDerivAt.hasFDerivWithinAt) (ht_inj n)
  have hpiece (n : ℕ) :
      (∫⁻ x in rset ∩ t n, ENNReal.ofReal |(fderiv ℝ g x).det| * h (g x) ∂volume) =
        ∫⁻ y in g '' (rset ∩ t n), h y ∂volume := by
    symm
    exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (hrset.inter (ht_meas n))
      (fun x hx ↦ (hg x hx.1.1).hasFDerivAt.hasFDerivWithinAt) (ht_inj n) h
  calc
    (∑' n, ∫⁻ x in rset ∩ t n,
        ENNReal.ofReal |(fderiv ℝ g x).det| * h (g x) ∂volume) =
        ∑' n, ∫⁻ y in g '' (rset ∩ t n), h y ∂volume := by
      congr 1
      funext n
      exact hpiece n
    _ = ∑' n, ∫⁻ y, (g '' (rset ∩ t n)).indicator h y ∂volume := by
      congr 1
      funext n
      exact (lintegral_indicator (himage n) h).symm
    _ = ∫⁻ y, ∑' n, (g '' (rset ∩ t n)).indicator h y ∂volume := by
      symm
      exact lintegral_tsum fun n ↦ (hh.indicator (himage n)).aemeasurable

/-- Weighted area formula with multiplicity.  On each injective regular piece, `v n` is the
source weight transported through the measurable inverse; summing the image indicators counts
every regular preimage with its own weight. -/
theorem exists_weighted_area_multiplicity_partition {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) :
    ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin d)))
        (v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          fderivNondegenerateSet g s = ⋃ n, fderivNondegenerateSet g s ∩ t n ∧
            (∀ n, InjOn g (fderivNondegenerateSet g s ∩ t n)) ∧
              (∀ n, ∃ K : ℝ≥0, AntilipschitzWith K
                ((fderivNondegenerateSet g s ∩ t n).restrict g)) ∧
                (∀ n, Measurable (v n)) ∧
                  (∀ n x, x ∈ fderivNondegenerateSet g s ∩ t n → v n (g x) = w x) ∧
                    (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume) =
                      ∫⁻ y, ∑' n,
                        (g '' (fderivNondegenerateSet g s ∩ t n)).indicator (v n) y := by
  classical
  let rset := fderivNondegenerateSet g s
  have hrset : MeasurableSet rset := measurableSet_fderivNondegenerateSet g hs
  obtain ⟨t, ht_disj, ht_meas, ht_cover, ht_inj, ht_anti, _⟩ :=
    exists_area_multiplicity_partition g hs hg
  let p : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun n ↦ rset ∩ t n
  have hpmeas (n : ℕ) : MeasurableSet (p n) := hrset.inter (ht_meas n)
  have hemb (n : ℕ) : MeasurableEmbedding ((p n).restrict g) := by
    apply measurableEmbedding_of_fderivWithin (hpmeas n)
      (fun x hx ↦ (hg x hx.1.1).hasFDerivAt.hasFDerivWithinAt)
    exact ht_inj n
  let v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun n ↦
    if hp : (p n).Nonempty then
      letI : Nonempty (p n) := hp.to_subtype
      measurableEmbeddingInverseWeight (hemb n) (fun x : p n ↦ w x)
    else 0
  have hvmeas (n : ℕ) : Measurable (v n) := by
    dsimp only [v]
    split_ifs with hp
    · letI : Nonempty (p n) := hp.to_subtype
      exact measurable_measurableEmbeddingInverseWeight (hemb n)
        (hw.comp measurable_subtype_coe)
    · exact measurable_const
  have hvapply (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ p n) :
      v n (g x) = w x := by
    have hp : (p n).Nonempty := ⟨x, hx⟩
    simp only [v, dif_pos hp]
    letI : Nonempty (p n) := hp.to_subtype
    convert measurableEmbeddingInverseWeight_apply (hemb n)
      (fun z : p n ↦ w z) ⟨x, hx⟩ using 1
    rfl
  refine ⟨t, v, ht_disj, ht_meas, ht_cover, ht_inj, ht_anti, hvmeas, ?_, ?_⟩
  · intro n x hx
    exact hvapply n x hx
  conv_lhs =>
    rw [setLIntegral_abs_det_mul_eq_fderivNondegenerateSet g hs w]
    rw [ht_cover]
    rw [lintegral_iUnion (fun n ↦ hrset.inter (ht_meas n))
      (pairwise_disjoint_mono ht_disj fun _ ↦ inter_subset_right)]
  have himage (n : ℕ) : MeasurableSet (g '' (p n)) := by
    apply measurable_image_of_fderivWithin (hpmeas n)
      (fun x hx ↦ (hg x hx.1.1).hasFDerivAt.hasFDerivWithinAt)
    exact ht_inj n
  have hpiece (n : ℕ) :
      (∫⁻ x in p n, ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume) =
        ∫⁻ y, (g '' (p n)).indicator (v n) y ∂volume := by
    calc
      (∫⁻ x in p n, ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume) =
          ∫⁻ x in p n, ENNReal.ofReal |(fderiv ℝ g x).det| * v n (g x) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (hpmeas n)] with x hx
        rw [hvapply n x hx]
      _ = ∫⁻ y in g '' (p n), v n y ∂volume := by
        symm
        exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hpmeas n)
          (fun x hx ↦ (hg x hx.1.1).hasFDerivAt.hasFDerivWithinAt) (ht_inj n) (v n)
      _ = ∫⁻ y, (g '' (p n)).indicator (v n) y ∂volume :=
        (lintegral_indicator (himage n) (v n)).symm
  change (∑' n, ∫⁻ x in p n,
    ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume) = _
  calc
    (∑' n, ∫⁻ x in p n,
        ENNReal.ofReal |(fderiv ℝ g x).det| * w x ∂volume) =
        ∑' n, ∫⁻ y, (g '' (p n)).indicator (v n) y ∂volume := by
      congr 1
      funext n
      exact hpiece n
    _ = ∫⁻ y, ∑' n, (g '' (p n)).indicator (v n) y ∂volume := by
      symm
      exact lintegral_tsum fun n ↦ ((hvmeas n).indicator (himage n)).aemeasurable

/-- Replacing one row of the identity matrix by `v` changes its determinant to the corresponding
coordinate of `v`. -/
theorem Matrix.det_updateRow_one {d : ℕ} (i : Fin d) (v : Fin d → ℝ) :
    (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) i v).det = v i := by
  have hrow : ∑ k, v k • (1 : Matrix (Fin d) (Fin d) ℝ) k = v := by
    ext j
    simp [Matrix.one_apply, eq_comm]
  conv_lhs => rw [← hrow]
  simpa using Matrix.det_updateRow_sum (1 : Matrix (Fin d) (Fin d) ℝ) i v

/-- Replace the `i`-th Euclidean coordinate of `x` by `f x`. -/
def scalarCoordinateChart {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  x + (f x - x i) • EuclideanSpace.single i 1

@[simp]
theorem scalarCoordinateChart_apply_same {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    scalarCoordinateChart i f x i = f x := by
  simp [scalarCoordinateChart]

@[simp]
theorem scalarCoordinateChart_apply_of_ne {d : ℕ} {i j : Fin d} (hji : j ≠ i)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    scalarCoordinateChart i f x j = x j := by
  simp [scalarCoordinateChart, hji]

/-- Derivative of `scalarCoordinateChart`: the identity with its `i`-th output coordinate
replaced by the functional `L`. -/
def scalarCoordinateDerivative {d : ℕ} (i : Fin d)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ _ +
    (L - EuclideanSpace.proj i).smulRight (EuclideanSpace.single i 1)

@[simp]
theorem scalarCoordinateDerivative_apply_same {d : ℕ} (i : Fin d)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    scalarCoordinateDerivative i L x i = L x := by
  simp [scalarCoordinateDerivative]

@[simp]
theorem scalarCoordinateDerivative_apply_of_ne {d : ℕ} {i j : Fin d} (hji : j ≠ i)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    scalarCoordinateDerivative i L x j = x j := by
  simp [scalarCoordinateDerivative, hji]

/-- Fréchet derivative of the coordinate-replacement chart. -/
theorem HasFDerivAt.scalarCoordinateChart {d : ℕ} {i : Fin d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hf : HasFDerivAt f L x) :
    HasFDerivAt (scalarCoordinateChart i f) (scalarCoordinateDerivative i L) x := by
  change HasFDerivAt
    (fun y ↦ y + (f y - EuclideanSpace.proj i y) • EuclideanSpace.single i 1)
    (ContinuousLinearMap.id ℝ _ +
      (L - EuclideanSpace.proj i).smulRight (EuclideanSpace.single i 1)) x
  exact (hasFDerivAt_id x).add
    ((hf.sub (EuclideanSpace.proj i).hasFDerivAt).smul_const
      (EuclideanSpace.single i 1))

/-- The determinant of the coordinate-replacement derivative is the corresponding directional
derivative of the scalar map. -/
theorem scalarCoordinateDerivative_det {d : ℕ} (i : Fin d)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    (scalarCoordinateDerivative i L).det = L (EuclideanSpace.single i 1) := by
  let b : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hmatrix :
      LinearMap.toMatrix b b (scalarCoordinateDerivative i L :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) =
        Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) i
          (fun j ↦ L (EuclideanSpace.single j 1)) := by
    ext j k
    by_cases hji : j = i
    · subst j
      simp [LinearMap.toMatrix_apply, b, EuclideanSpace.basisFun_apply]
    · simp [LinearMap.toMatrix_apply, b, EuclideanSpace.basisFun_apply,
        scalarCoordinateDerivative_apply_of_ne hji, Matrix.updateRow_apply, Matrix.one_apply, hji]
  change LinearMap.det (scalarCoordinateDerivative i L :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = _
  rw [← LinearMap.det_toMatrix b]
  rw [hmatrix, Matrix.det_updateRow_one]

private noncomputable def coordinateInsertionLinear {n : ℕ} (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap <|
    { toFun := fun z ↦ WithLp.toLp 2 (i.insertNth 0 z.ofLp)
      map_add' := by
        intro x y
        ext j
        induction j using i.succAboveCases <;> simp
      map_smul' := by
        intro c x
        ext j
        induction j using i.succAboveCases <;> simp }

@[simp] private theorem coordinateInsertionLinear_apply {n : ℕ} (i : Fin (n + 1))
    (z : EuclideanSpace ℝ (Fin n)) :
    coordinateInsertionLinear i z = WithLp.toLp 2 (i.insertNth 0 z.ofLp) := rfl

private noncomputable def coordinateProjection {n : ℕ} (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap <|
    { toFun := fun x ↦ WithLp.toLp 2 (fun j ↦ x (i.succAbove j))
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }

@[simp] private theorem coordinateProjection_apply {n : ℕ} (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    coordinateProjection i x j = x (i.succAbove j) := rfl

private theorem coordinateProjection_comp_insertion {n : ℕ} (i : Fin (n + 1)) :
    (coordinateProjection i).comp (coordinateInsertionLinear i) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext z j
  simp

private theorem coordinateInsertionLinear_inner {n : ℕ} (i : Fin (n + 1))
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (coordinateInsertionLinear i x) (coordinateInsertionLinear i y) = inner ℝ x y := by
  simp [coordinateInsertionLinear_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, i.sum_univ_succAbove]

@[simp] private theorem coordinateInsertionLinear_single {n : ℕ} (i : Fin (n + 1))
    (j : Fin n) (a : ℝ) :
    coordinateInsertionLinear i (EuclideanSpace.single j a) =
      EuclideanSpace.single (i.succAbove j) a := by
  ext k
  induction k using i.succAboveCases <;> simp [Pi.single_apply, eq_comm]

private theorem coordinateInsertionLinear_norm {n : ℕ} (i : Fin (n + 1))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖coordinateInsertionLinear i x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simpa [norm_sq_eq_re_inner] using coordinateInsertionLinear_inner i x x

private noncomputable def coordinateGraphInverseDerivative {n : ℕ} (i : Fin (n + 1))
    (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  coordinateInsertionLinear i -
    ((L (EuclideanSpace.single i 1))⁻¹ •
      L.comp (coordinateInsertionLinear i)).smulRight (EuclideanSpace.single i 1)

@[simp] private theorem coordinateGraphInverseDerivative_apply_same {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    coordinateGraphInverseDerivative i L z i =
      -(L (coordinateInsertionLinear i z) / L (EuclideanSpace.single i 1)) := by
  simp [coordinateGraphInverseDerivative, div_eq_mul_inv, mul_comm]

@[simp] private theorem coordinateGraphInverseDerivative_apply_succAbove {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coordinateGraphInverseDerivative i L z (i.succAbove j) = z j := by
  simp [coordinateGraphInverseDerivative]

private theorem coordinateProjection_comp_graphInverseDerivative {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :
    (coordinateProjection i).comp (coordinateGraphInverseDerivative i L) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext z j
  simp

private theorem coordinateGraphInverseDerivative_apply_basis {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (j : Fin n) :
    coordinateGraphInverseDerivative i L (EuclideanSpace.single j 1) =
      coordinateInsertionLinear i (EuclideanSpace.single j 1) -
        (L (EuclideanSpace.single (i.succAbove j) 1) /
          L (EuclideanSpace.single i 1)) • EuclideanSpace.single i 1 := by
  rw [coordinateGraphInverseDerivative]
  simp only [_root_.sub_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply]
  rw [coordinateInsertionLinear_single]
  congr 1
  rw [div_eq_mul_inv, smul_eq_mul]
  ring_nf

private theorem coordinateGraphInverseDerivative_gram_apply {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (j k : Fin n) :
    Matrix.gram ℝ
      (fun q ↦ coordinateGraphInverseDerivative i L
        ((EuclideanSpace.basisFun (Fin n) ℝ) q)) j k =
      (1 : Matrix (Fin n) (Fin n) ℝ) j k +
        (L (EuclideanSpace.single (i.succAbove j) 1) /
          L (EuclideanSpace.single i 1)) *
        (L (EuclideanSpace.single (i.succAbove k) 1) /
          L (EuclideanSpace.single i 1)) := by
  rw [Matrix.gram_apply]
  simp only [EuclideanSpace.basisFun_apply,
    coordinateGraphInverseDerivative_apply_basis]
  rw [coordinateInsertionLinear_single, coordinateInsertionLinear_single]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  simp [EuclideanSpace.inner_single_right,
    Matrix.one_apply, eq_comm]
  ring

private theorem continuousLinearMap_norm_sq_eq_sum_apply_single_sq {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ j : Fin m, L (EuclideanSpace.single j 1) ^ 2 := by
  let g : EuclideanSpace ℝ (Fin m) := (InnerProductSpace.toDual ℝ _).symm L
  have hsum := (EuclideanSpace.basisFun (Fin m) ℝ).sum_sq_inner_left g
  have hnorm : ‖g‖ = ‖L‖ := (InnerProductSpace.toDual ℝ _).symm.norm_map L
  have happly (x : EuclideanSpace ℝ (Fin m)) : inner ℝ g x = L x := by
    exact InnerProductSpace.toDual_symm_apply
  simp only [EuclideanSpace.basisFun_apply, happly] at hsum
  rw [hnorm] at hsum
  exact hsum.symm

private theorem coordinateGraphInverseDerivative_gram {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :
    Matrix.gram ℝ
      (fun q ↦ coordinateGraphInverseDerivative i L
        ((EuclideanSpace.basisFun (Fin n) ℝ) q)) =
      1 + Matrix.replicateCol Unit
          (fun j ↦ L (EuclideanSpace.single (i.succAbove j) 1) /
            L (EuclideanSpace.single i 1)) *
        Matrix.replicateRow Unit
          (fun j ↦ L (EuclideanSpace.single (i.succAbove j) 1) /
            L (EuclideanSpace.single i 1)) := by
  ext j k
  rw [coordinateGraphInverseDerivative_gram_apply]
  simp [Matrix.mul_apply]

private theorem coordinateGraphInverseDerivative_normDet_mul_abs {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (hi : L (EuclideanSpace.single i 1) ≠ 0) :
    |L (EuclideanSpace.single i 1)| *
        (coordinateGraphInverseDerivative i L).toLinearMap.normDet = ‖L‖ := by
  let a : ℝ := L (EuclideanSpace.single i 1)
  let b : Fin n → ℝ := fun j ↦
    L (EuclideanSpace.single (i.succAbove j) 1) / a
  have hgram : Matrix.gram ℝ
      (fun q ↦ coordinateGraphInverseDerivative i L
        ((EuclideanSpace.basisFun (Fin n) ℝ) q)) =
      1 + Matrix.replicateCol Unit b * Matrix.replicateRow Unit b := by
    simpa [a, b] using coordinateGraphInverseDerivative_gram i L
  have hdet : (Matrix.gram ℝ
      (fun q ↦ coordinateGraphInverseDerivative i L
        ((EuclideanSpace.basisFun (Fin n) ℝ) q))).det =
      1 + ∑ j, b j ^ 2 := by
    rw [hgram, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, pow_two]
  have hnormDetSq := LinearMap.normDet_sq_eq_det_gram
    (coordinateGraphInverseDerivative i L).toLinearMap
      (EuclideanSpace.basisFun (Fin n) ℝ)
  have hdet' : (Matrix.gram ℝ
      (fun q ↦ (coordinateGraphInverseDerivative i L).toLinearMap
        ((EuclideanSpace.basisFun (Fin n) ℝ) q))).det =
      1 + ∑ j, b j ^ 2 := by simpa using hdet
  rw [hdet'] at hnormDetSq
  have hnormSq := continuousLinearMap_norm_sq_eq_sum_apply_single_sq L
  rw [i.sum_univ_succAbove] at hnormSq
  have ha : a ≠ 0 := by simpa [a] using hi
  have hratio : a ^ 2 * (1 + ∑ j, b j ^ 2) = ‖L‖ ^ 2 := by
    calc
      a ^ 2 * (1 + ∑ j, b j ^ 2) =
          a ^ 2 + ∑ j, a ^ 2 * b j ^ 2 := by
        rw [mul_add, mul_one, Finset.mul_sum]
      _ = a ^ 2 +
          ∑ j, L (EuclideanSpace.single (i.succAbove j) 1) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [b]
        field_simp [ha]
      _ = ‖L‖ ^ 2 := by simpa [a] using hnormSq.symm
  have hnormDetSq' :
      (coordinateGraphInverseDerivative i L).toLinearMap.normDet ^ 2 =
        1 + ∑ j, b j ^ 2 := by simpa using hnormDetSq
  have hsq :
      (|a| * (coordinateGraphInverseDerivative i L).toLinearMap.normDet) ^ 2 =
        ‖L‖ ^ 2 := by
    rw [mul_pow, sq_abs, hnormDetSq', hratio]
  have hnonneg : 0 ≤ |a| *
      (coordinateGraphInverseDerivative i L).toLinearMap.normDet :=
    mul_nonneg (abs_nonneg _) (LinearMap.normDet_nonneg _)
  have := (sq_eq_sq₀ hnonneg (norm_nonneg L)).mp hsq
  simpa [a] using this

private def coordinateAffineInsertion {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  coordinateInsertionLinear i z + t • EuclideanSpace.single i 1

@[simp] private theorem coordinateAffineInsertion_apply_same {n : ℕ}
    (i : Fin (n + 1)) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    coordinateAffineInsertion i t z i = t := by
  simp [coordinateAffineInsertion]

@[simp] private theorem coordinateAffineInsertion_apply_succAbove {n : ℕ}
    (i : Fin (n + 1)) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coordinateAffineInsertion i t z (i.succAbove j) = z j := by
  simp [coordinateAffineInsertion]

private theorem coordinateProjection_coordinateAffineInsertion {n : ℕ}
    (i : Fin (n + 1)) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    coordinateProjection i (coordinateAffineInsertion i t z) = z := by
  ext j
  simp

private theorem coordinateAffineInsertion_dist {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    dist (coordinateAffineInsertion i t x) (coordinateAffineInsertion i t y) = dist x y := by
  simp only [dist_eq_norm, coordinateAffineInsertion]
  rw [add_sub_add_right_eq_sub, ← map_sub, coordinateInsertionLinear_norm]

private theorem lipschitzWith_coordinateAffineInsertion {n : ℕ}
    (i : Fin (n + 1)) (t : ℝ) :
    LipschitzWith 1 (coordinateAffineInsertion i t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [coordinateAffineInsertion_dist, NNReal.coe_one, one_mul]

private theorem hasFDerivAt_coordinateAffineInsertion {n : ℕ}
    (i : Fin (n + 1)) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (coordinateAffineInsertion i t) (coordinateInsertionLinear i) z := by
  unfold coordinateAffineInsertion
  exact (coordinateInsertionLinear i).hasFDerivAt.add_const
    (t • EuclideanSpace.single i 1)

private noncomputable def coordinateProductMeasurableEquiv {n : ℕ} (i : Fin (n + 1)) :
    ℝ × EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm).trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm.trans <|
      MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)

private theorem coordinateProductMeasurableEquiv_apply {n : ℕ} (i : Fin (n + 1))
    (x : ℝ × EuclideanSpace ℝ (Fin n)) :
    coordinateProductMeasurableEquiv i x = coordinateAffineInsertion i x.1 x.2 := by
  ext j
  induction j using i.succAboveCases with
  | x =>
      simp [coordinateProductMeasurableEquiv, coordinateAffineInsertion,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
      rfl
  | p j =>
      simp [coordinateProductMeasurableEquiv, coordinateAffineInsertion,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
      rfl

private theorem measurePreserving_coordinateProductMeasurableEquiv {n : ℕ}
    (i : Fin (n + 1)) : MeasurePreserving (coordinateProductMeasurableEquiv i) := by
  let e₁ : ℝ × EuclideanSpace ℝ (Fin n) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  let e₂ : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm
  let e₃ : (Fin (n + 1) → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
    MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)
  have h₁ : MeasurePreserving e₁ := by
    have he₁ : (e₁ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ × (Fin n → ℝ)) =
        Prod.map id WithLp.ofLp := by
      funext x
      apply Prod.ext <;> rfl
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    rw [he₁]
    simpa [e₁, MeasurableEquiv.prodCongr] using
      (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_ofLp (Fin n))
  have h₂ : MeasurePreserving e₂ :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i).symm _
  have h₃ : MeasurePreserving e₃ := PiLp.volume_preserving_toLp (Fin (n + 1))
  simpa [coordinateProductMeasurableEquiv, e₁, e₂, e₃] using h₁.trans (h₂.trans h₃)

private theorem lintegral_eq_lintegral_coordinateSections {n : ℕ}
    (i : Fin (n + 1)) (g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ y, g y ∂volume) =
      ∫⁻ t : ℝ, ∫⁻ z : EuclideanSpace ℝ (Fin n),
        g (coordinateAffineInsertion i t z) ∂volume ∂volume := by
  let e := coordinateProductMeasurableEquiv i
  have he : MeasurePreserving e := measurePreserving_coordinateProductMeasurableEquiv i
  calc
    (∫⁻ y, g y ∂volume) = ∫⁻ x : ℝ × EuclideanSpace ℝ (Fin n), g (e x) ∂volume :=
      (he.lintegral_comp hg).symm
    _ = ∫⁻ t : ℝ, ∫⁻ z : EuclideanSpace ℝ (Fin n), g (e (t, z)) ∂volume ∂volume := by
      rw [Measure.volume_eq_prod, lintegral_prod]
      exact (hg.comp he.measurable).aemeasurable
    _ = _ := by
      simp_rw [e, coordinateProductMeasurableEquiv_apply]

private theorem scalarCoordinateDerivative_comp_graphInverseDerivative {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (hi : L (EuclideanSpace.single i 1) ≠ 0) :
    (scalarCoordinateDerivative i L).comp (coordinateGraphInverseDerivative i L) =
      coordinateInsertionLinear i := by
  ext z j
  induction j using i.succAboveCases with
  | x =>
      simp [coordinateGraphInverseDerivative]
      field_simp [hi]
      ring
  | p j => simp [i.succAbove_ne j]

private theorem eq_coordinateGraphInverseDerivative_of_comp {n : ℕ}
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (hi : L (EuclideanSpace.single i 1) ≠ 0)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hA : (scalarCoordinateDerivative i L).comp A = coordinateInsertionLinear i) :
    A = coordinateGraphInverseDerivative i L := by
  have hdet : (scalarCoordinateDerivative i L).det ≠ 0 := by
    rw [scalarCoordinateDerivative_det]
    exact hi
  have hinj : Function.Injective (scalarCoordinateDerivative i L) := by
    intro x y hxy
    apply (scalarCoordinateDerivative i L).toContinuousLinearEquivOfDetNeZero hdet |>.injective
    simpa only [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] using hxy
  apply ContinuousLinearMap.ext
  intro z
  apply hinj
  exact DFunLike.congr_fun hA z |>.trans <|
    (DFunLike.congr_fun (scalarCoordinateDerivative_comp_graphInverseDerivative i L hi) z).symm

/-- At every differentiability point of `f`, the Jacobian determinant of its coordinate chart is
the corresponding partial derivative. -/
theorem fderiv_scalarCoordinateChart_det {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {x : EuclideanSpace ℝ (Fin d)}
    (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (scalarCoordinateChart i f) x).det =
      fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hchart := HasFDerivAt.scalarCoordinateChart (i := i) hf.hasFDerivAt
  rw [hchart.fderiv, scalarCoordinateDerivative_det]

/-- A nonzero scalar functional on Euclidean space is nonzero on some standard basis vector. -/
theorem ContinuousLinearMap.exists_apply_single_ne_zero {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ i : Fin d, L (EuclideanSpace.single i 1) ≠ 0 := by
  by_contra h
  have hzero : ∀ i : Fin d, L (EuclideanSpace.single i 1) = 0 := by
    intro i
    exact not_ne_iff.mp (not_exists.mp h i)
  apply hL
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro i
  simp [EuclideanSpace.basisFun_apply, hzero i]

/-- Differentiability points whose first nonzero scalar partial derivative occurs at `i`. -/
def scalarFirstRegularSet {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | DifferentiableAt ℝ f x ∧
    fderiv ℝ f x (EuclideanSpace.single i 1) ≠ 0 ∧
      ∀ j : Fin d, j < i → fderiv ℝ f x (EuclideanSpace.single j 1) = 0}

/-- Each first-nonzero-coordinate region is Borel measurable. -/
theorem measurableSet_scalarFirstRegularSet {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : MeasurableSet (scalarFirstRegularSet i f) := by
  have hpartial (j : Fin d) : Measurable fun x ↦
      fderiv ℝ f x (EuclideanSpace.single j 1) :=
    measurable_fderiv_apply_const ℝ f (EuclideanSpace.single j 1)
  have hprevious : MeasurableSet {x | ∀ j : Fin d, j < i →
      fderiv ℝ f x (EuclideanSpace.single j 1) = 0} := by
    have heq : {x | ∀ j : Fin d, j < i →
        fderiv ℝ f x (EuclideanSpace.single j 1) = 0} =
        ⋂ j : Fin d, ⋂ (_h : j < i),
          {x | fderiv ℝ f x (EuclideanSpace.single j 1) = 0} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_singleton 0).preimage (hpartial j)
  exact (measurableSet_of_differentiableAt ℝ f).inter
    ((measurableSet_singleton 0).compl.preimage (hpartial i) |>.inter hprevious)

/-- The first-nonzero-coordinate regions are pairwise disjoint. -/
theorem pairwise_disjoint_scalarFirstRegularSet {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    Pairwise (Disjoint on fun i : Fin d ↦ scalarFirstRegularSet i f) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hxi.2.1 (hxj.2.2 i hijlt)
  · exact hxj.2.1 (hxi.2.2 j hjilt)

/-- The first-nonzero-coordinate regions cover exactly the differentiability points with nonzero
Fréchet derivative. -/
theorem iUnion_scalarFirstRegularSet {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (⋃ i : Fin d, scalarFirstRegularSet i f) =
      {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact ⟨hxi.1, fun hzero ↦ hxi.2.1 (by rw [hzero]; simp)⟩
  · intro hx
    obtain ⟨i, hi⟩ := ContinuousLinearMap.exists_apply_single_ne_zero
      (fderiv ℝ f x) hx.2
    let P : Fin d → Prop := fun j ↦
      fderiv ℝ f x (EuclideanSpace.single j 1) ≠ 0
    have hex : ∃ j, P j := ⟨i, hi⟩
    let k : Fin d := Fin.find P hex
    apply mem_iUnion.mpr
    refine ⟨k, hx.1, Fin.find_spec hex, ?_⟩
    intro j hj
    exact not_ne_iff.mp (Fin.find_min hex hj)

/-- Surface-to-coordinate Jacobian ratio on the chart selected by `i`. -/
def scalarCoordinateAreaWeight {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  scalarJacobian f x /
    ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)| * w x

/-- The surface-to-coordinate weight is measurable. -/
theorem measurable_scalarCoordinateAreaWeight {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    {w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hw : Measurable w) :
    Measurable (scalarCoordinateAreaWeight i f w) := by
  apply Measurable.mul _ hw
  apply Measurable.div (measurable_scalarJacobian f)
  exact ENNReal.measurable_ofReal.comp <|
    continuous_abs.measurable.comp
      (measurable_fderiv_apply_const ℝ f (EuclideanSpace.single i 1))

/-- On the selected first-regular region, the coordinate determinant cancels the chart ratio and
recovers the full scalar Jacobian. -/
theorem ofReal_abs_partial_mul_scalarCoordinateAreaWeight {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ scalarFirstRegularSet i f) :
    ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)| *
        scalarCoordinateAreaWeight i f w x = scalarJacobian f x * w x := by
  let a := ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)|
  have ha0 : a ≠ 0 := by
    dsimp only [a]
    intro hzero
    exact (not_le.mpr (abs_pos.mpr hx.2.1)) (ENNReal.ofReal_eq_zero.mp hzero)
  have hatop : a ≠ ∞ := ENNReal.ofReal_ne_top
  rw [scalarCoordinateAreaWeight]
  change a * (scalarJacobian f x / a * w x) = _
  rw [← mul_assoc, ENNReal.mul_div_cancel ha0 hatop]

/-- The full scalar-Jacobian integral is the sum over the disjoint first-nonzero-coordinate
regions. -/
theorem lintegral_scalarJacobian_eq_tsum_firstRegular {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    (∫⁻ x, scalarJacobian f x * w x ∂volume) =
      ∑' i : Fin d, ∫⁻ x in scalarFirstRegularSet i f,
        scalarJacobian f x * w x ∂volume := by
  let rset : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0}
  have hrset : MeasurableSet rset :=
    (measurableSet_of_differentiableAt ℝ f).inter
      ((measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ f))
  have hrestrict :
      (∫⁻ x, scalarJacobian f x * w x ∂volume) =
        ∫⁻ x in rset, scalarJacobian f x * w x ∂volume := by
    rw [← lintegral_indicator hrset]
    apply lintegral_congr
    intro x
    by_cases hdiff : DifferentiableAt ℝ f x
    · by_cases hzero : fderiv ℝ f x = 0
      · simp [rset, hdiff, hzero, scalarJacobian]
      · simp [rset, hdiff, hzero]
    · have hzero := fderiv_zero_of_not_differentiableAt hdiff
      simp [rset, hdiff, hzero, scalarJacobian]
  rw [hrestrict]
  have hunion : (⋃ i : Fin d, scalarFirstRegularSet i f) = rset :=
    iUnion_scalarFirstRegularSet f
  rw [← hunion]
  exact lintegral_iUnion (fun i ↦ measurableSet_scalarFirstRegularSet i f)
    (pairwise_disjoint_scalarFirstRegularSet f) _

/-- Region where a chosen scalar partial derivative is nonzero. -/
def scalarCoordinateRegularSet {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (s : Set (EuclideanSpace ℝ (Fin d))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  s ∩ {x | fderiv ℝ f x (EuclideanSpace.single i 1) ≠ 0}

/-- On a differentiability set, nondegeneracy of the coordinate-replacement chart is exactly
nonvanishing of the selected scalar partial derivative. -/
theorem fderivNondegenerateSet_scalarCoordinateChart {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    fderivNondegenerateSet (scalarCoordinateChart i f) s =
      scalarCoordinateRegularSet i f s := by
  ext x
  simp only [fderivNondegenerateSet, scalarCoordinateRegularSet, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    rw [fderiv_scalarCoordinateChart_det i f (hf x hx.1)] at hx
    exact hx.2
  · intro hx
    refine ⟨hx.1, ?_⟩
    rw [fderiv_scalarCoordinateChart_det i f (hf x hx.1)]
    exact hx.2

/-- Weighted area-with-multiplicity formula for the scalar coordinate chart.  It is the exact
equal-dimensional graph chart used in Federer's scalar coarea proof. -/
theorem exists_weighted_scalarCoordinate_area_partition {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) :
    ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin d)))
        (v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          scalarCoordinateRegularSet i f s =
            ⋃ n, scalarCoordinateRegularSet i f s ∩ t n ∧
            (∀ n, InjOn (scalarCoordinateChart i f)
              (scalarCoordinateRegularSet i f s ∩ t n)) ∧
              (∀ n, ∃ K : ℝ≥0, AntilipschitzWith K
                ((scalarCoordinateRegularSet i f s ∩ t n).restrict
                  (scalarCoordinateChart i f))) ∧
                (∀ n, Measurable (v n)) ∧
                  (∀ n x, x ∈ scalarCoordinateRegularSet i f s ∩ t n →
                    v n (scalarCoordinateChart i f x) = w x) ∧
                    (∫⁻ x in s,
                        ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)| * w x ∂volume) =
                      ∫⁻ y, ∑' n,
                        ((scalarCoordinateChart i f) ''
                          (scalarCoordinateRegularSet i f s ∩ t n)).indicator (v n) y := by
  have hg : ∀ x ∈ s, DifferentiableAt ℝ (scalarCoordinateChart i f) x := by
    intro x hx
    exact (HasFDerivAt.scalarCoordinateChart (i := i) (hf x hx).hasFDerivAt).differentiableAt
  obtain ⟨t, v, ht_disj, ht_meas, ht_cover, ht_inj, ht_anti,
      hv_meas, hv_apply, harea⟩ :=
    exists_weighted_area_multiplicity_partition (scalarCoordinateChart i f) hs hg w hw
  have hreg := fderivNondegenerateSet_scalarCoordinateChart i f hf
  rw [hreg] at ht_cover ht_inj ht_anti hv_apply harea
  refine ⟨t, v, ht_disj, ht_meas, ht_cover, ht_inj, ht_anti,
    hv_meas, hv_apply, ?_⟩
  calc
    (∫⁻ x in s,
        ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)| * w x ∂volume) =
        ∫⁻ x in s,
          ENNReal.ofReal |(fderiv ℝ (scalarCoordinateChart i f) x).det| * w x ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      rw [fderiv_scalarCoordinateChart_det i f (hf x hx)]
    _ = _ := harea

/-- Inside a first-regular region, the corresponding coordinate is nondegenerate everywhere. -/
theorem scalarCoordinateRegularSet_firstRegular {d : ℕ} (i : Fin d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    scalarCoordinateRegularSet i f (scalarFirstRegularSet i f) =
      scalarFirstRegularSet i f := by
  ext x
  simp only [scalarCoordinateRegularSet, mem_inter_iff, mem_setOf_eq]
  constructor
  · exact fun hx ↦ hx.1
  · exact fun hx ↦ ⟨hx, hx.2.1⟩

/-- Global rectifiable-chart representation of the scalar Jacobian integral.  The outer index
chooses the first nonzero partial derivative; the inner index is the measurable injective
partition for that coordinate chart. -/
theorem exists_scalarJacobian_chart_representation {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) :
    ∃ (t : Fin d → ℕ → Set (EuclideanSpace ℝ (Fin d)))
        (v : Fin d → ℕ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
      (∀ i, Pairwise (Disjoint on t i)) ∧
        (∀ i n, MeasurableSet (t i n)) ∧
          (∀ i, scalarFirstRegularSet i f =
            ⋃ n, scalarFirstRegularSet i f ∩ t i n) ∧
            (∀ i n, InjOn (scalarCoordinateChart i f)
              (scalarFirstRegularSet i f ∩ t i n)) ∧
              (∀ i n, Measurable (v i n)) ∧
                (∫⁻ x, scalarJacobian f x * w x ∂volume) =
                  ∫⁻ y, ∑' i : Fin d, ∑' n,
                    ((scalarCoordinateChart i f) ''
                      (scalarFirstRegularSet i f ∩ t i n)).indicator (v i n) y := by
  classical
  have hex (i : Fin d) :
      ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin d)))
          (v : ℕ → EuclideanSpace ℝ (Fin d) → ℝ≥0∞),
        Pairwise (Disjoint on t) ∧
          (∀ n, MeasurableSet (t n)) ∧
            scalarFirstRegularSet i f = ⋃ n, scalarFirstRegularSet i f ∩ t n ∧
              (∀ n, InjOn (scalarCoordinateChart i f)
                (scalarFirstRegularSet i f ∩ t n)) ∧
                (∀ n, Measurable (v n)) ∧
                  (∫⁻ x in scalarFirstRegularSet i f,
                      scalarJacobian f x * w x ∂volume) =
                    ∫⁻ y, ∑' n,
                      ((scalarCoordinateChart i f) ''
                        (scalarFirstRegularSet i f ∩ t n)).indicator (v n) y := by
    obtain ⟨t, v, ht_disj, ht_meas, ht_cover, ht_inj, _ht_anti,
        hv_meas, _hv_apply, harea⟩ :=
      exists_weighted_scalarCoordinate_area_partition i f
        (measurableSet_scalarFirstRegularSet i f) (fun x hx ↦ hx.1)
        (scalarCoordinateAreaWeight i f w) (measurable_scalarCoordinateAreaWeight i f hw)
    have hreg := scalarCoordinateRegularSet_firstRegular i f
    rw [hreg] at ht_cover ht_inj harea
    refine ⟨t, v, ht_disj, ht_meas, ht_cover, ht_inj, hv_meas, ?_⟩
    calc
      (∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume) =
          ∫⁻ x in scalarFirstRegularSet i f,
            ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)| *
              scalarCoordinateAreaWeight i f w x ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_scalarFirstRegularSet i f)] with x hx
        exact (ofReal_abs_partial_mul_scalarCoordinateAreaWeight i f w hx).symm
      _ = _ := harea
  choose t v hdata using hex
  have ht_disj : ∀ i, Pairwise (Disjoint on t i) := fun i ↦ (hdata i).1
  have ht_meas : ∀ i n, MeasurableSet (t i n) := fun i ↦ (hdata i).2.1
  have ht_cover : ∀ i, scalarFirstRegularSet i f =
      ⋃ n, scalarFirstRegularSet i f ∩ t i n := fun i ↦ (hdata i).2.2.1
  have ht_inj : ∀ i n, InjOn (scalarCoordinateChart i f)
      (scalarFirstRegularSet i f ∩ t i n) := fun i ↦ (hdata i).2.2.2.1
  have hv_meas : ∀ i n, Measurable (v i n) := fun i ↦ (hdata i).2.2.2.2.1
  have harea (i : Fin d) :
      (∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume) =
        ∫⁻ y, ∑' n,
          ((scalarCoordinateChart i f) ''
            (scalarFirstRegularSet i f ∩ t i n)).indicator (v i n) y :=
    (hdata i).2.2.2.2.2
  refine ⟨t, v, ht_disj, ht_meas, ht_cover, ht_inj, hv_meas, ?_⟩
  rw [lintegral_scalarJacobian_eq_tsum_firstRegular f w]
  simp_rw [harea]
  symm
  apply lintegral_tsum
  intro i
  apply Measurable.aemeasurable
  apply Measurable.tsum
  intro n
  apply (hv_meas i n).indicator
  apply measurable_image_of_fderivWithin
    ((measurableSet_scalarFirstRegularSet i f).inter (ht_meas i n))
    (fun x hx ↦
      (HasFDerivAt.scalarCoordinateChart (i := i) hx.1.1.hasFDerivAt).hasFDerivWithinAt)
    (ht_inj i n)

section LowerDimensionalArea

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- An injective continuous linear map, with its codomain restricted to its range, is a continuous
linear equivalence. -/
noncomputable def continuousLinearEquivRange (A : U →L[ℝ] V) (hA : Function.Injective A) :
    U ≃L[ℝ] A.range := by
  letI : CompleteSpace U := FiniteDimensional.complete ℝ U
  letI : CompleteSpace A.range := FiniteDimensional.complete ℝ A.range
  exact ContinuousLinearEquiv.ofBijective A.rangeRestrict
    (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hA
      exact Subtype.ext_iff.mp hxy)
    (by
      rw [LinearMap.range_eq_top]
      exact A.toLinearMap.surjective_rangeRestrict)

/-- The lower-dimensional Jacobian is continuous in the operator norm. -/
theorem continuous_normDet :
    Continuous (fun A : U →L[ℝ] V ↦ A.toLinearMap.normDet) := by
  have hadj : Continuous (fun A : U →L[ℝ] V ↦ A.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  have hcomp : Continuous (fun A : U →L[ℝ] V ↦ A.adjoint ∘L A) :=
    hadj.clm_comp continuous_id
  have hgram : Continuous (fun A : U →L[ℝ] V ↦ (A.adjoint ∘L A).det) :=
    ContinuousLinearMap.continuous_det.comp hcomp
  convert Real.continuous_sqrt.comp hgram using 1
  funext A
  change A.toLinearMap.normDet = Real.sqrt ((A.adjoint ∘L A).det)
  rw [← A.normDet_sq]
  exact (Real.sqrt_sq A.toLinearMap.normDet_nonneg).symm

omit [FiniteDimensional ℝ V] in
/-- The derivative of a differentiable map into an arbitrary finite-dimensional codomain is
almost everywhere as close to a fixed linear approximation as the map itself.  The density-point
argument is independent of the codomain dimension. -/
theorem ApproximatesLinearOn.norm_fderiv_sub_le_general
    [MeasurableSpace U] [BorelSpace U]
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {δ : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hs : MeasurableSet s)
    (f' : U → U →L[ℝ] V) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    ∀ᵐ x ∂(volume.restrict s), ‖f' x - A‖₊ ≤ δ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure U) s,
    ae_restrict_mem hs]
  intro x hx xs
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  suffices H : ∀ ε, 0 < ε →
      ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
    have hlim :
        Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε)
          (𝓝[>] 0) (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at hlim
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin]
    exact H
  intro ε εpos
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one (volume : Measure U) s x hx _
      measurableSet_closedBall (measure_closedBall_pos (volume : Measure U) z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
      ∃ ρ > 0, ball x ρ ∩ s ⊆
        {y : U | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.def εpos)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
      ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
          Pi.sub_apply, map_smul, smul_sub]
      _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ :=
        norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ :=
        add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
      congr 1
      simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I
        exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr

omit [FiniteDimensional ℝ V] in
/-- At a Lebesgue density-one point, a within derivative is unique even when the source set has
no interior.  This is the pointwise density substitute for `UniqueDiffWithinAt` used by Lipschitz
graph parameterizations. -/
theorem HasFDerivWithinAt.eq_of_volume_density_one
    [MeasurableSpace U] [BorelSpace U]
    {f : U → V} {s : Set U} {x : U} {A B : U →L[ℝ] V}
    (hx : Tendsto
      (fun r ↦ volume (s ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hA : HasFDerivWithinAt f A s x) (hB : HasFDerivWithinAt f B s x) : A = B := by
  apply ContinuousLinearMap.ext
  intro z
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  suffices hbound : ∀ ε, 0 < ε →
      ‖(A - B) z‖ ≤ 2 * ε * (‖z‖ + ε) + ‖A - B‖ * ε by
    have hcont : Continuous
        (fun ε : ℝ ↦ 2 * ε * (‖z‖ + ε) + ‖A - B‖ * ε) := by fun_prop
    have hfull : Tendsto
        (fun ε : ℝ ↦ 2 * ε * (‖z‖ + ε) + ‖A - B‖ * ε)
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using hcont.tendsto (0 : ℝ)
    have hlim : Tendsto
        (fun ε : ℝ ↦ 2 * ε * (‖z‖ + ε) + ‖A - B‖ * ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := hfull.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hbound ε hε
  intro ε hε
  have hhit : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one volume s x hx _ measurableSet_closedBall
      (measure_closedBall_pos volume z hε).ne'
  obtain ⟨ρA, hρApos, hρA⟩ :
      ∃ ρ > 0, ball x ρ ∩ s ⊆
        {y : U | ‖f y - f x - A (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 (hA.isLittleO.def hε)
  obtain ⟨ρB, hρBpos, hρB⟩ :
      ∃ ρ > 0, ball x ρ ∩ s ⊆
        {y : U | ‖f y - f x - B (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 (hB.isLittleO.def hε)
  have hρpos : 0 < min ρA ρB := lt_min hρApos hρBpos
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      {x} + r • closedBall z ε ⊆ ball x (min ρA ρB) := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall
      (ball_mem_nhds x hρpos)
  obtain ⟨r, ⟨y, ⟨hys, hy⟩⟩, hry, hrpos⟩ :
      ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x (min ρA ρB) ∧ 0 < r :=
    (hhit.and (hsmall.and self_mem_nhdsWithin)).exists
  obtain ⟨a, haz, hya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, hxa⟩
    exact ⟨a, ha, by simp only [hxa, add_neg_cancel_left]⟩
  have hya_ball : y ∈ ball x (min ρA ρB) := hry hy
  have hAerr : ‖f y - f x - A (y - x)‖ ≤ ε * ‖y - x‖ :=
    hρA ⟨mem_ball.mpr ((mem_ball.mp hya_ball).trans_le (min_le_left _ _)), hys⟩
  have hBerr : ‖f y - f x - B (y - x)‖ ≤ ε * ‖y - x‖ :=
    hρB ⟨mem_ball.mpr ((mem_ball.mp hya_ball).trans_le (min_le_right _ _)), hys⟩
  have hnorm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 haz]
  have hscaled : r * ‖(A - B) a‖ ≤ r * (2 * ε) * (‖z‖ + ε) := by
    calc
      r * ‖(A - B) a‖ = ‖(A - B) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpos.le]
      _ = ‖(f y - f x - B (y - x)) - (f y - f x - A (y - x))‖ := by
        congr 1
        simp only [hya, add_sub_cancel_left, FunLike.coe_sub, Pi.sub_apply, map_smul, smul_sub]
        module
      _ ≤ ‖f y - f x - B (y - x)‖ + ‖f y - f x - A (y - x)‖ :=
        norm_sub_le _ _
      _ ≤ ε * ‖y - x‖ + ε * ‖y - x‖ := add_le_add hBerr hAerr
      _ = r * (2 * ε) * ‖a‖ := by
        simp only [hya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hrpos.le]
        ring
      _ ≤ r * (2 * ε) * (‖z‖ + ε) := by gcongr
  have ha_bound : ‖(A - B) a‖ ≤ 2 * ε * (‖z‖ + ε) := by
    rw [mul_assoc] at hscaled
    exact (mul_le_mul_iff_right₀ hrpos).1 hscaled
  calc
    ‖(A - B) z‖ = ‖(A - B) a + (A - B) (z - a)‖ := by
      congr 1
      simp only [map_sub]
      abel
    _ ≤ ‖(A - B) a‖ + ‖(A - B) (z - a)‖ := norm_add_le _ _
    _ ≤ 2 * ε * (‖z‖ + ε) + ‖A - B‖ * ‖z - a‖ := by
      exact add_le_add ha_bound (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ 2 * ε * (‖z‖ + ε) + ‖A - B‖ * ε := by
      rw [mem_closedBall_iff_norm'] at haz
      gcongr

omit [FiniteDimensional ℝ V] in
/-- Two almost-everywhere within-derivative fields for the same function agree almost
everywhere with respect to source volume. -/
theorem ae_eq_of_ae_hasFDerivWithinAt_of_volume
    [MeasurableSpace U] [BorelSpace U]
    {f : U → V} {s : Set U} {A B : U → U →L[ℝ] V}
    (hA : ∀ᵐ x ∂volume.restrict s, HasFDerivWithinAt f (A x) s x)
    (hB : ∀ᵐ x ∂volume.restrict s, HasFDerivWithinAt f (B x) s x) :
    A =ᵐ[volume.restrict s] B := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume s, hA, hB]
  intro x hx hxA hxB
  exact HasFDerivWithinAt.eq_of_volume_density_one hx hxA hxB

/-- If a Lipschitz parameterization is a right inverse to a continuous linear map on its source
set, then the continuous linear map composed with its within derivative is the identity almost
everywhere.  Density-point uniqueness removes any `UniqueDiffWithinAt` premise. -/
theorem ae_comp_fderivWithin_eq_id_of_lipschitzOnWith
    [MeasurableSpace U] [BorelSpace U]
    {C : ℝ≥0} {φ : U → V} {s : Set U} (hs : MeasurableSet s)
    (hφ : LipschitzOnWith C φ s) (P : V →L[ℝ] U)
    (heq : EqOn id (fun z ↦ P (φ z)) s) :
    ∀ᵐ z ∂volume.restrict s,
      P.comp (fderivWithin ℝ φ s z) = ContinuousLinearMap.id ℝ U := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume s,
    hφ.ae_differentiableWithinAt hs, ae_restrict_mem hs]
  intro z hz hdiff hzs
  have hcomp : HasFDerivWithinAt (fun y ↦ P (φ y))
      (P.comp (fderivWithin ℝ φ s z)) s z :=
    P.hasFDerivAt.comp_hasFDerivWithinAt z hdiff.hasFDerivWithinAt
  have hcomp_id : HasFDerivWithinAt id
      (P.comp (fderivWithin ℝ φ s z)) s z := hcomp.congr' heq hzs
  exact HasFDerivWithinAt.eq_of_volume_density_one hz hcomp_id
    (hasFDerivAt_id z).hasFDerivWithinAt

/-- A Lipschitz right-inverse parameterization has injective within derivative almost
everywhere. -/
theorem ae_injective_fderivWithin_of_lipschitzOnWith_of_comp_eq_id
    [MeasurableSpace U] [BorelSpace U]
    {C : ℝ≥0} {φ : U → V} {s : Set U} (hs : MeasurableSet s)
    (hφ : LipschitzOnWith C φ s) (P : V →L[ℝ] U)
    (heq : EqOn id (fun z ↦ P (φ z)) s) :
    ∀ᵐ z ∂volume.restrict s,
      Function.Injective (fderivWithin ℝ φ s z) := by
  filter_upwards [ae_comp_fderivWithin_eq_id_of_lipschitzOnWith hs hφ P heq]
  intro z hz x y hxy
  have hP := congr_arg P hxy
  change (P.comp (fderivWithin ℝ φ s z)) x =
    (P.comp (fderivWithin ℝ φ s z)) y at hP
  rw [hz] at hP
  exact hP

/-- The derivative field of a differentiable map between finite-dimensional inner-product
spaces is almost everywhere measurable on its measurable source set.  The proof uses a countable
uniform-linearization partition. -/
theorem aemeasurable_fderivWithin_general
    [MeasurableSpace U] [BorelSpace U]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable f' (volume.restrict s) := by
  refine aemeasurable_of_unif_approx fun ε εpos ↦ ?_
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
  have hδ : 0 < δ := εpos
  obtain ⟨t, A, ht_disj, ht_meas, ht_cover, ht_approx, _⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf'
      (fun _ ↦ δ) (fun _ ↦ hδ.ne')
  obtain ⟨g, hg_meas, hg⟩ :
      ∃ g : U → U →L[ℝ] V, Measurable g ∧
        ∀ (n : ℕ) (x : U), x ∈ t n → g x = A n :=
    exists_measurable_piecewise t ht_meas (fun n _ ↦ A n) (fun _ ↦ measurable_const) <|
      ht_disj.mono fun _ _ h ↦ by simp only [h.inter_eq, eqOn_empty]
  refine ⟨g, hg_meas.aemeasurable, ?_⟩
  suffices hclose : ∀ᵐ x : U ∂sum fun n ↦ volume.restrict (s ∩ t n),
      dist (g x) (f' x) ≤ ε by
    have hmeasure : volume.restrict s ≤
        sum fun n ↦ volume.restrict (s ∩ t n) := by
      have hs_union : s = ⋃ n, s ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl ht_cover) inter_subset_left
      conv_lhs => rw [hs_union]
      exact restrict_iUnion_le
    exact ae_mono hmeasure hclose
  refine ae_sum_iff.2 fun n ↦ ?_
  have hderiv : ∀ᵐ x : U ∂volume.restrict (s ∩ t n), ‖f' x - A n‖₊ ≤ δ :=
    ApproximatesLinearOn.norm_fderiv_sub_le_general (ht_approx n)
      (hs.inter (ht_meas n)) f' (fun x hx ↦ (hf' x hx.1).mono inter_subset_left)
  have hg_piece : ∀ᵐ x : U ∂volume.restrict (s ∩ t n), g x = A n := by
    suffices ∀ᵐ x : U ∂volume.restrict (t n), g x = A n from
      ae_mono (restrict_mono inter_subset_right le_rfl) this
    filter_upwards [ae_restrict_mem (ht_meas n)]
    exact hg n
  filter_upwards [hderiv, hg_piece] with x hx hgx
  rw [← nndist_eq_nnnorm] at hx
  rw [hgx, dist_comm]
  exact hx

/-- The lower-dimensional Jacobian density attached to a differentiable field is almost
everywhere measurable. -/
theorem aemeasurable_ofReal_normDet_fderivWithin_general
    [MeasurableSpace U] [BorelSpace U]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet)
      (volume.restrict s) := by
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (continuous_normDet.measurable.comp_aemeasurable
      (aemeasurable_fderivWithin_general hs hf'))

/-- Simultaneously control `normDet` and the inverse-range error near an injective map. -/
theorem exists_normDet_inverse_control (A : U →L[ℝ] V) (hA : Function.Injective A)
    (r : ℝ≥0) (hr : 1 < r) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      δ * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < 1 - r⁻¹ ∧
      δ * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < r - 1 ∧
      ∀ B : U →L[ℝ] V, ‖B - A‖ ≤ δ →
        A.toLinearMap.normDet ≤ r * B.toLinearMap.normDet ∧
          B.toLinearMap.normDet ≤ r * A.toLinearMap.normDet := by
  have hdet_ne : A.toLinearMap.normDet ≠ 0 :=
    (A.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hA
  have hdet : 0 < A.toLinearMap.normDet :=
    lt_of_le_of_ne A.toLinearMap.normDet_nonneg (Ne.symm hdet_ne)
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  let η : ℝ := A.toLinearMap.normDet * ((r : ℝ) - 1) / (2 * (r : ℝ))
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, hcontrol⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ B : U →L[ℝ] V, dist B A < δ₁ →
        dist B.toLinearMap.normDet A.toLinearMap.normDet < η := by
    exact Metric.continuousAt_iff.1 continuous_normDet.continuousAt η hη
  let q₀ : ℝ := min (1 - ((r : ℝ)⁻¹)) ((r : ℝ) - 1)
  have hq₀ : 0 < q₀ := lt_min (sub_pos.mpr (inv_lt_one_of_one_lt₀ hrR)) (sub_pos.mpr hrR)
  let M : ℝ := ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖
  have hM : 0 ≤ M := by
    exact norm_nonneg ((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)
  let δ₂ : ℝ := q₀ / (2 * (M + 1))
  have hδ₂ : 0 < δ₂ := by positivity
  let δ : ℝ≥0 := ⟨min (δ₁ / 2) δ₂, (le_of_lt (lt_min (half_pos hδ₁) hδ₂))⟩
  refine ⟨δ, lt_min (half_pos hδ₁) hδ₂, ?_, ?_, ?_⟩
  · have hreal : (δ : ℝ) * M < q₀ := by
      have hδle : (δ : ℝ) ≤ δ₂ := min_le_right _ _
      calc
        (δ : ℝ) * M ≤ δ₂ * M := mul_le_mul_of_nonneg_right hδle hM
        _ ≤ δ₂ * (M + 1) := by
          gcongr
          linarith
        _ = q₀ / 2 := by
          dsimp [δ₂]
          field_simp
        _ < q₀ := half_lt_self hq₀
    have hpart : (δ : ℝ) * M < 1 - ((r : ℝ)⁻¹) := hreal.trans_le (min_le_left _ _)
    have hrinv : r⁻¹ ≤ 1 := (inv_le_one₀ (show 0 < r by positivity)).2 hr.le
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_mul, NNReal.coe_sub hrinv, NNReal.coe_inv]
    simpa [M] using hpart
  · have hreal : (δ : ℝ) * M < q₀ := by
      have hδle : (δ : ℝ) ≤ δ₂ := min_le_right _ _
      calc
        (δ : ℝ) * M ≤ δ₂ * M := mul_le_mul_of_nonneg_right hδle hM
        _ ≤ δ₂ * (M + 1) := by
          gcongr
          linarith
        _ = q₀ / 2 := by
          dsimp [δ₂]
          field_simp
        _ < q₀ := half_lt_self hq₀
    have hpart : (δ : ℝ) * M < (r : ℝ) - 1 := hreal.trans_le (min_le_right _ _)
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_mul, NNReal.coe_sub hr.le]
    simpa [M] using hpart
  · intro B hB
    have hdist : dist B A < δ₁ := by
      rw [dist_eq_norm]
      calc
        ‖B - A‖ ≤ δ := hB
        _ ≤ δ₁ / 2 := min_le_left _ _
        _ < δ₁ := half_lt_self hδ₁
    have hclose := hcontrol B hdist
    rw [Real.dist_eq] at hclose
    rcases abs_lt.mp hclose with ⟨hlower, hupper⟩
    have hηeq : 2 * (r : ℝ) * η = A.toLinearMap.normDet * ((r : ℝ) - 1) := by
      dsimp [η]
      field_simp
    have hleft : A.toLinearMap.normDet / (r : ℝ) ≤ A.toLinearMap.normDet - η := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < r)).2
      nlinarith
    constructor
    · have hquot : A.toLinearMap.normDet / (r : ℝ) < B.toLinearMap.normDet := by
        linarith
      exact le_of_lt (by
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < r)).1 hquot
        simpa [mul_comm] using this)
    · have heta : η ≤ ((r : ℝ) - 1) * A.toLinearMap.normDet := by
        nlinarith
      exact le_of_lt (by nlinarith)

private noncomputable def areaControlRadius (r : ℝ≥0) (hr : 1 < r)
    (A : U →L[ℝ] V) : ℝ≥0 := by
  classical
  exact if hA : Function.Injective A then
      (exists_normDet_inverse_control A hA r hr).choose
    else 1

private theorem areaControlRadius_pos (r : ℝ≥0) (hr : 1 < r) (A : U →L[ℝ] V) :
    0 < areaControlRadius r hr A := by
  classical
  by_cases hA : Function.Injective A
  · simpa [areaControlRadius, hA] using
      (exists_normDet_inverse_control A hA r hr).choose_spec.1
  · simp [areaControlRadius, hA]

private theorem areaControlRadius_spec (r : ℝ≥0) (hr : 1 < r)
    (A : U →L[ℝ] V) (hA : Function.Injective A) :
    areaControlRadius r hr A *
        ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < 1 - r⁻¹ ∧
      areaControlRadius r hr A *
        ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < r - 1 ∧
      ∀ B : U →L[ℝ] V, ‖B - A‖ ≤ areaControlRadius r hr A →
        A.toLinearMap.normDet ≤ r * B.toLinearMap.normDet ∧
          B.toLinearMap.normDet ≤ r * A.toLinearMap.normDet := by
  classical
  simpa [areaControlRadius, hA] using
    (exists_normDet_inverse_control A hA r hr).choose_spec.2

private theorem one_add_lt_of_lt_sub_one {q r : ℝ≥0} (hr : 1 < r)
    (hq : q < r - 1) : 1 + q < r := by
  have hqR : (q : ℝ) < (r : ℝ) - 1 := by
    have := NNReal.coe_lt_coe.mpr hq
    rw [NNReal.coe_sub hr.le] at this
    exact this
  apply NNReal.coe_lt_coe.mp
  push_cast
  linarith

private theorem inv_one_sub_lt_of_lt_one_sub_inv {q r : ℝ≥0} (hr : 1 < r)
    (hq : q < 1 - r⁻¹) : (1 - q)⁻¹ < r := by
  have hq1 : q < 1 := hq.trans_le (tsub_le_self)
  have hpos : (0 : ℝ) < 1 - (q : ℝ) := by
    have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
    exact sub_pos.mpr hq1R
  have hrinv : r⁻¹ ≤ 1 := (inv_le_one₀ (show 0 < r by positivity)).2 hr.le
  have hqR : (q : ℝ) < 1 - ((r : ℝ)⁻¹) := by
    have := NNReal.coe_lt_coe.mpr hq
    rw [NNReal.coe_sub hrinv, NNReal.coe_inv] at this
    exact this
  apply NNReal.coe_lt_coe.mp
  rw [NNReal.coe_inv, NNReal.coe_sub hq1.le]
  apply (inv_lt_iff_one_lt_mul₀ hpos).2
  have hinv : (r : ℝ) * (r : ℝ)⁻¹ = 1 := by field_simp
  have hri : (r : ℝ)⁻¹ < 1 - (q : ℝ) := by linarith
  have hmul := mul_lt_mul_of_pos_left hri (show (0 : ℝ) < r by positivity)
  rwa [hinv] at hmul

private theorem tendsto_areaErrorFactor_right (m : ℕ) :
    Tendsto (fun r : ℝ≥0 ↦ (r : ℝ≥0∞) ^ m * r) (𝓝[>] 1) (𝓝 1) := by
  have hcoe : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) (𝓝 (1 : ℝ≥0)) (𝓝 1) :=
    ENNReal.tendsto_coe.2 tendsto_id
  have hfull : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ≥0∞) ^ m * r)
      (𝓝 (1 : ℝ≥0)) (𝓝 ((1 : ℝ≥0∞) ^ m * 1)) :=
    ENNReal.Tendsto.mul (ENNReal.Tendsto.pow hcoe) (by simp) hcoe (by simp)
  simpa using hfull.mono_left nhdsWithin_le_nhds

private theorem tendsto_areaErrorFactor_left (m : ℕ) :
    Tendsto (fun r : ℝ≥0 ↦ (r : ℝ≥0∞) * r ^ m) (𝓝[>] 1) (𝓝 1) := by
  have hcoe : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) (𝓝 (1 : ℝ≥0)) (𝓝 1) :=
    ENNReal.tendsto_coe.2 tendsto_id
  have hfull : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ≥0∞) * r ^ m)
      (𝓝 (1 : ℝ≥0)) (𝓝 ((1 : ℝ≥0∞) * 1 ^ m)) :=
    ENNReal.Tendsto.mul hcoe (by simp) (ENNReal.Tendsto.pow hcoe) (by simp)
  simpa using hfull.mono_left nhdsWithin_le_nhds

omit [FiniteDimensional ℝ V] in
@[simp] theorem continuousLinearEquivRange_apply
    (A : U →L[ℝ] V) (hA : Function.Injective A)
    (x : U) : (continuousLinearEquivRange A hA x : V) = A x := by
  simp [continuousLinearEquivRange, ContinuousLinearEquiv.coeFn_ofBijective]

omit [FiniteDimensional ℝ V] in
/-- Passing to the range coordinates of an injective continuous linear map preserves its
lower-dimensional Jacobian. -/
theorem continuousLinearEquivRange_normDet (A : U →L[ℝ] V) (hA : Function.Injective A) :
    (continuousLinearEquivRange A hA).toLinearMap.normDet = A.toLinearMap.normDet := by
  have heq : (continuousLinearEquivRange A hA).toLinearMap =
      A.toLinearMap.codRestrict A.range (fun x ↦ ⟨x, rfl⟩) := by
    ext x
    exact continuousLinearEquivRange_apply A hA x
  rw [heq]
  exact LinearMap.normDet_codRestrict (fun x => A.toLinearMap.mem_range_self x)

/-- Reparametrize a map by the range coordinates of an injective linear approximation. -/
noncomputable def linearRangeReparam (f : U → V) (A : U →L[ℝ] V)
    (hA : Function.Injective A) : A.range → V :=
  fun z ↦ f ((continuousLinearEquivRange A hA).symm z)

omit [FiniteDimensional ℝ V] in
/-- On a set where `f` is approximated by an injective linear map `A`, range coordinates turn
`f` into a Lipschitz map.  The constant records precisely the approximation error transported
through the inverse of `A` on its range. -/
theorem ApproximatesLinearOn.lipschitzOnWith_linearRangeReparam
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f A s c) (hA : Function.Injective A) :
    LipschitzOnWith
      (1 + c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊)
      (linearRangeReparam f A hA) (continuousLinearEquivRange A hA '' s) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz z' hz'
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hz'
  let e := continuousLinearEquivRange A hA
  have hxy : dist x y ≤ ‖(e.symm : A.range →L[ℝ] U)‖ * dist (e x) (e y) := by
    simpa using (e.symm : A.range →L[ℝ] U).dist_le_opNorm (e x) (e y)
  have happ := hf x hx y hy
  simp only [linearRangeReparam, ContinuousLinearEquiv.symm_apply_apply]
  calc
    dist (f x) (f y) = ‖f x - f y‖ := dist_eq_norm _ _
    _ = ‖(f x - f y - A (x - y)) + A (x - y)‖ := by
      congr 1
      abel
    _ ≤ ‖f x - f y - A (x - y)‖ + ‖A (x - y)‖ := norm_add_le _ _
    _ ≤ c * ‖x - y‖ + ‖A (x - y)‖ := add_le_add happ le_rfl
    _ = c * dist x y + dist (e x) (e y) := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      rfl
    _ ≤ c * (‖(e.symm : A.range →L[ℝ] U)‖ * dist (e x) (e y)) +
        dist (e x) (e y) := by gcongr
    _ = (1 + c * ‖(e.symm : A.range →L[ℝ] U)‖) * dist (e x) (e y) := by ring

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The standard Hausdorff-measure distortion estimate also holds for Mathlib's Euclidean
normalization of Hausdorff measure. -/
theorem LipschitzOnWith.euclideanHausdorffMeasure_image_le
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {K : ℝ≥0} {f : U → V} {s : Set U} (hf : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  simp_rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  have h := hf.hausdorffMeasure_image_le (d := (d : ℝ)) (by positivity)
  rw [ENNReal.rpow_natCast] at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_right h
      (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (μH[(d : ℝ)] : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞)

/-- Antilipschitz maps obey the corresponding lower distortion estimate for Euclidean
Hausdorff measure. -/
theorem AntilipschitzWith.le_euclideanHausdorffMeasure_image
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} (hf : AntilipschitzWith K f) (d : ℕ) (s : Set X) :
    μHE[d] s ≤ (K : ℝ≥0∞) ^ d * μHE[d] (f '' s) := by
  simp_rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  have h := hf.le_hausdorffMeasure_image (d := (d : ℝ)) (by positivity) s
  rw [ENNReal.rpow_natCast] at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_right h
      (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (μH[(d : ℝ)] : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞)

omit [FiniteDimensional ℝ V] in
/-- A quantitative upper area bound on a set where a map is uniformly approximated by an
injective linear map.  This is the local estimate used in the lower-dimensional area argument. -/
theorem ApproximatesLinearOn.euclideanHausdorffMeasure_image_le
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f A s c) (hA : Function.Injective A) :
    μHE[Module.finrank ℝ U] (f '' s) ≤
      ((1 + c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ : ℝ≥0) :
          ℝ≥0∞) ^ Module.finrank ℝ U *
        ENNReal.ofReal A.toLinearMap.normDet * volume s := by
  let e := continuousLinearEquivRange A hA
  have himage : f '' s = linearRangeReparam f A hA '' (e '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
      simp [linearRangeReparam, e]
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [linearRangeReparam, e]
  rw [himage]
  calc
    μHE[Module.finrank ℝ U] (linearRangeReparam f A hA '' (e '' s)) ≤
        ((1 + c * ‖(e.symm : A.range →L[ℝ] U)‖₊ : ℝ≥0) : ℝ≥0∞) ^
            Module.finrank ℝ U *
          μHE[Module.finrank ℝ U] (e '' s) :=
      LipschitzOnWith.euclideanHausdorffMeasure_image_le
        (ApproximatesLinearOn.lipschitzOnWith_linearRangeReparam hf hA) _
    _ = ((1 + c * ‖(e.symm : A.range →L[ℝ] U)‖₊ : ℝ≥0) : ℝ≥0∞) ^
          Module.finrank ℝ U *
          (ENNReal.ofReal e.toLinearMap.normDet * volume s) := by
      have hemeasure : μHE[Module.finrank ℝ U] (e '' s) =
          ENNReal.ofReal e.toLinearMap.normDet * volume s := by
        simpa using e.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
      rw [hemeasure]
    _ = ((1 + c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ :
            ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ U *
          ENNReal.ofReal A.toLinearMap.normDet * volume s := by
      rw [continuousLinearEquivRange_normDet A hA]
      simp [e, mul_assoc]

omit [FiniteDimensional ℝ V] in
/-- If the approximation error is smaller than the least expansion of `A`, then the
range-coordinate restriction is quantitatively antilipschitz. -/
theorem ApproximatesLinearOn.antilipschitzWith_linearRangeReparam_restrict
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f A s c) (hA : Function.Injective A)
    (hsmall : c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < 1) :
    AntilipschitzWith
      (1 - c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊)⁻¹
      (fun z : continuousLinearEquivRange A hA '' s ↦
        linearRangeReparam f A hA z.1) := by
  apply AntilipschitzWith.of_le_mul_dist
  rintro ⟨z, ⟨x, hx, rfl⟩⟩ ⟨z', ⟨y, hy, rfl⟩⟩
  let e := continuousLinearEquivRange A hA
  let q : ℝ≥0 := c * ‖(e.symm : A.range →L[ℝ] U)‖₊
  have hxy : dist x y ≤ ‖(e.symm : A.range →L[ℝ] U)‖ * dist (e x) (e y) := by
    simpa using (e.symm : A.range →L[ℝ] U).dist_le_opNorm (e x) (e y)
  have herr : ‖f x - f y - A (x - y)‖ ≤ (q : ℝ) * dist (e x) (e y) := by
    calc
      ‖f x - f y - A (x - y)‖ ≤ c * ‖x - y‖ := hf x hx y hy
      _ = c * dist x y := by rw [dist_eq_norm]
      _ ≤ c * (‖(e.symm : A.range →L[ℝ] U)‖ * dist (e x) (e y)) := by gcongr
      _ = (q : ℝ) * dist (e x) (e y) := by simp [q, mul_assoc]
  have hlinear : dist (e x) (e y) ≤
      dist (f x) (f y) + ‖f x - f y - A (x - y)‖ := by
    calc
      dist (e x) (e y) = ‖A (x - y)‖ := by
        rw [dist_eq_norm, ← map_sub]
        rfl
      _ = ‖(f x - f y) - (f x - f y - A (x - y))‖ := by
        congr 1
        abel
      _ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := norm_sub_le _ _
      _ = dist (f x) (f y) + ‖f x - f y - A (x - y)‖ := by rw [dist_eq_norm]
  have hcore : (1 - (q : ℝ)) * dist (e x) (e y) ≤ dist (f x) (f y) := by
    nlinarith
  have hq : q < 1 := by simpa [q, e] using hsmall
  have hpos : 0 < 1 - (q : ℝ) := sub_pos.mpr (by exact_mod_cast hq)
  simp only [linearRangeReparam, ContinuousLinearEquiv.symm_apply_apply]
  change dist (e x) (e y) ≤ _
  calc
    dist (e x) (e y) = (1 - (q : ℝ))⁻¹ * ((1 - (q : ℝ)) * dist (e x) (e y)) := by
      field_simp
    _ ≤ (1 - (q : ℝ))⁻¹ * dist (f x) (f y) :=
      mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr hpos.le)
    _ = ((1 - q)⁻¹ : ℝ≥0) * dist (f x) (f y) := by
      rw [NNReal.coe_inv, NNReal.coe_sub hq.le]
      norm_num

omit [FiniteDimensional ℝ V] in
/-- The lower local area bound complementary to
`ApproximatesLinearOn.euclideanHausdorffMeasure_image_le`. -/
theorem ApproximatesLinearOn.normDet_mul_volume_le_euclideanHausdorffMeasure_image
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f A s c) (hA : Function.Injective A)
    (hsmall : c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < 1) :
    ENNReal.ofReal A.toLinearMap.normDet * volume s ≤
      (((1 - c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊)⁻¹ :
          ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ U *
        μHE[Module.finrank ℝ U] (f '' s) := by
  let e := continuousLinearEquivRange A hA
  let t : Set A.range := e '' s
  let g : t → V := fun z ↦ linearRangeReparam f A hA z.1
  have hanti : AntilipschitzWith
      (1 - c * ‖(e.symm : A.range →L[ℝ] U)‖₊)⁻¹ g := by
    simpa [e, t, g] using
      ApproximatesLinearOn.antilipschitzWith_linearRangeReparam_restrict hf hA hsmall
  have hmeasure := AntilipschitzWith.le_euclideanHausdorffMeasure_image hanti
    (Module.finrank ℝ U) (Set.univ : Set t)
  have ht : μHE[Module.finrank ℝ U] (e '' s) = μHE[Module.finrank ℝ U] (Set.univ : Set t) := by
    have hiso := isometry_subtype_coe.euclideanHausdorffMeasure_image
      (d := Module.finrank ℝ U) (Set.univ : Set t)
    calc
      μHE[Module.finrank ℝ U] (e '' s) =
          μHE[Module.finrank ℝ U] (((↑) : t → A.range) '' Set.univ) := by
        congr 1
        ext z
        simp only [Set.mem_image, Set.mem_univ, true_and]
        constructor
        · intro hz
          exact ⟨⟨z, by simpa [t] using hz⟩, rfl⟩
        · rintro ⟨⟨z', hz'⟩, rfl⟩
          simpa [t] using hz'
      _ = μHE[Module.finrank ℝ U] (Set.univ : Set t) := hiso
  have hg : g '' (Set.univ : Set t) = f '' s := by
    ext y
    constructor
    · rintro ⟨⟨z, ⟨x, hx, hzx⟩⟩, -, rfl⟩
      refine ⟨x, hx, ?_⟩
      subst z
      simp [g, linearRangeReparam, e]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨e x, ⟨x, hx, rfl⟩⟩, Set.mem_univ _, ?_⟩
      simp [g, linearRangeReparam, e]
  have hemeasure : ENNReal.ofReal e.toLinearMap.normDet * volume s =
      μHE[Module.finrank ℝ U] (e '' s) := by
    simpa using e.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s |>.symm
  rw [← continuousLinearEquivRange_normDet A hA, hemeasure, ht]
  simpa [e, g, hg] using hmeasure

omit [FiniteDimensional ℝ V] in
/-- Multiplicative form of the local upper area estimate. -/
theorem ApproximatesLinearOn.euclideanHausdorffMeasure_image_le_mul
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {c r : ℝ≥0}
    (hf : ApproximatesLinearOn f A s c) (hA : Function.Injective A) (hr : 1 < r)
    (hsmall : c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < r - 1) :
    μHE[Module.finrank ℝ U] (f '' s) ≤
      (r : ℝ≥0∞) ^ Module.finrank ℝ U *
        ENNReal.ofReal A.toLinearMap.normDet * volume s := by
  refine (ApproximatesLinearOn.euclideanHausdorffMeasure_image_le hf hA).trans ?_
  have hK := one_add_lt_of_lt_sub_one hr hsmall
  gcongr

omit [FiniteDimensional ℝ V] in
/-- Multiplicative form of the local lower area estimate. -/
theorem ApproximatesLinearOn.mul_le_euclideanHausdorffMeasure_image
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {A : U →L[ℝ] V} {s : Set U} {c r : ℝ≥0}
    (hf : ApproximatesLinearOn f A s c) (hA : Function.Injective A) (hr : 1 < r)
    (hsmall : c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < 1 - r⁻¹) :
    ENNReal.ofReal A.toLinearMap.normDet * volume s ≤
      (r : ℝ≥0∞) ^ Module.finrank ℝ U * μHE[Module.finrank ℝ U] (f '' s) := by
  have hunit : c * ‖((continuousLinearEquivRange A hA).symm : A.range →L[ℝ] U)‖₊ < 1 :=
    hsmall.trans_le tsub_le_self
  refine (ApproximatesLinearOn.normDet_mul_volume_le_euclideanHausdorffMeasure_image
    hf hA hunit).trans ?_
  have hK := inv_one_sub_lt_of_lt_one_sub_inv hr hsmall
  gcongr

private theorem euclideanHausdorffMeasure_image_le_lintegral_normDet_fixed
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) (r : ℝ≥0) (hr : 1 < r) :
    μHE[Module.finrank ℝ U] (f '' s) ≤
      ((r : ℝ≥0∞) ^ Module.finrank ℝ U * r) *
        ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hA_rep⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf'
      (areaControlRadius r hr) fun B ↦ (areaControlRadius_pos r hr B).ne'
  have hAinj : ∀ n, Function.Injective (A n) := by
    intro n
    obtain ⟨y, hy, hAy⟩ := hA_rep hsne n
    rw [hAy]
    exact hf'inj y hy
  have s_eq : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
  calc
    μHE[Module.finrank ℝ U] (f '' s) ≤
        ∑' n, μHE[Module.finrank ℝ U] (f '' (s ∩ t n)) := by
      conv_lhs => rw [s_eq, image_iUnion]
      exact measure_iUnion_le
        (μ := (μHE[Module.finrank ℝ U] : Measure V)) (fun n : ℕ ↦ f '' (s ∩ t n))
    _ ≤ ∑' n, (r : ℝ≥0∞) ^ Module.finrank ℝ U *
        ENNReal.ofReal (A n).toLinearMap.normDet * volume (s ∩ t n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact ApproximatesLinearOn.euclideanHausdorffMeasure_image_le_mul
        (ht n) (hAinj n) hr (areaControlRadius_spec r hr (A n) (hAinj n)).2.1
    _ = ∑' n, (r : ℝ≥0∞) ^ Module.finrank ℝ U *
        ∫⁻ _x in s ∩ t n, ENNReal.ofReal (A n).toLinearMap.normDet ∂volume := by
      congr 1
      funext n
      rw [setLIntegral_const]
      simp [mul_assoc]
    _ ≤ ∑' n, ((r : ℝ≥0∞) ^ Module.finrank ℝ U * r) *
        ∫⁻ x in s ∩ t n, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [mul_assoc]
      gcongr
      rw [← lintegral_const_mul' (μ := volume.restrict (s ∩ t n))
        (r : ℝ≥0∞) (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet) ENNReal.coe_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ApproximatesLinearOn.norm_fderiv_sub_le_general (ht n)
        (hs.inter (t_meas n)) f' (fun x hx ↦ (hf' x hx.1).mono inter_subset_left)] with x hx
      have hnorm := (areaControlRadius_spec r hr (A n) (hAinj n)).2.2 (f' x) hx
      calc
        ENNReal.ofReal (A n).toLinearMap.normDet ≤
            ENNReal.ofReal (r * (f' x).toLinearMap.normDet) := ENNReal.ofReal_le_ofReal hnorm.1
        _ = (r : ℝ≥0∞) * ENNReal.ofReal (f' x).toLinearMap.normDet := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r)]
          simp
    _ = ((r : ℝ≥0∞) ^ Module.finrank ℝ U * r) *
        ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      conv_rhs => rw [s_eq]
      rw [lintegral_iUnion]
      · exact fun n ↦ hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n ↦ inter_subset_right

private theorem lintegral_normDet_le_euclideanHausdorffMeasure_image_fixed
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) (hfinj : InjOn f s)
    (r : ℝ≥0) (hr : 1 < r) :
    (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume) ≤
      ((r : ℝ≥0∞) * r ^ Module.finrank ℝ U) *
        μHE[Module.finrank ℝ U] (f '' s) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hA_rep⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf'
      (areaControlRadius r hr) fun B ↦ (areaControlRadius_pos r hr B).ne'
  have hAinj : ∀ n, Function.Injective (A n) := by
    intro n
    obtain ⟨y, hy, hAy⟩ := hA_rep hsne n
    rw [hAy]
    exact hf'inj y hy
  have s_eq : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
  have himage_meas : ∀ n, MeasurableSet (f '' (s ∩ t n)) := by
    intro n
    apply (hs.inter (t_meas n)).image_of_continuousOn_injOn
    · intro x hx
      exact (hf' x hx.1).continuousWithinAt.mono inter_subset_left
    · exact hfinj.mono inter_subset_left
  have himage_disj : Pairwise (Disjoint on fun n ↦ f '' (s ∩ t n)) := by
    intro i j hij
    apply Disjoint.image _ hfinj inter_subset_left inter_subset_left
    exact Disjoint.mono inter_subset_right inter_subset_right (t_disj hij)
  calc
    (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume) =
        ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume := by
      conv_lhs => rw [s_eq]
      rw [lintegral_iUnion]
      · exact fun n ↦ hs.inter (t_meas n)
      · exact pairwise_disjoint_mono t_disj fun n ↦ inter_subset_right
    _ ≤ ∑' n, (r : ℝ≥0∞) *
        (ENNReal.ofReal (A n).toLinearMap.normDet * volume (s ∩ t n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← setLIntegral_const]
      rw [← lintegral_const_mul' (μ := volume.restrict (s ∩ t n))
        (r : ℝ≥0∞) (fun _x ↦ ENNReal.ofReal (A n).toLinearMap.normDet) ENNReal.coe_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ApproximatesLinearOn.norm_fderiv_sub_le_general (ht n)
        (hs.inter (t_meas n)) f' (fun x hx ↦ (hf' x hx.1).mono inter_subset_left)] with x hx
      have hnorm := (areaControlRadius_spec r hr (A n) (hAinj n)).2.2 (f' x) hx
      calc
        ENNReal.ofReal (f' x).toLinearMap.normDet ≤
            ENNReal.ofReal (r * (A n).toLinearMap.normDet) := ENNReal.ofReal_le_ofReal hnorm.2
        _ = (r : ℝ≥0∞) * ENNReal.ofReal (A n).toLinearMap.normDet := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r)]
          simp
    _ ≤ ∑' n, ((r : ℝ≥0∞) * r ^ Module.finrank ℝ U) *
        μHE[Module.finrank ℝ U] (f '' (s ∩ t n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hlocal := ApproximatesLinearOn.mul_le_euclideanHausdorffMeasure_image
        (ht n) (hAinj n) hr (areaControlRadius_spec r hr (A n) (hAinj n)).1
      simpa [mul_assoc] using mul_le_mul_right hlocal (r : ℝ≥0∞)
    _ = ((r : ℝ≥0∞) * r ^ Module.finrank ℝ U) *
        μHE[Module.finrank ℝ U] (f '' s) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      conv_rhs => rw [s_eq, image_iUnion]
      exact (measure_iUnion himage_disj himage_meas).symm

private theorem euclideanHausdorffMeasure_image_le_lintegral_normDet_of_injective
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) :
    μHE[Module.finrank ℝ U] (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume := by
  let I := ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume
  have hlim : Tendsto
      (fun r : ℝ≥0 ↦ ((r : ℝ≥0∞) ^ Module.finrank ℝ U * r) * I)
      (𝓝[>] 1) (𝓝 I) := by
    simpa [I] using ENNReal.Tendsto.mul_const
      (tendsto_areaErrorFactor_right (Module.finrank ℝ U)) (Or.inl one_ne_zero)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [mem_Ioi] at hr
  exact euclideanHausdorffMeasure_image_le_lintegral_normDet_fixed hs hf' hf'inj r hr

private theorem lintegral_normDet_le_euclideanHausdorffMeasure_image_of_injective
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) (hfinj : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume) ≤
      μHE[Module.finrank ℝ U] (f '' s) := by
  let M := μHE[Module.finrank ℝ U] (f '' s)
  have hlim : Tendsto
      (fun r : ℝ≥0 ↦ ((r : ℝ≥0∞) * r ^ Module.finrank ℝ U) * M)
      (𝓝[>] 1) (𝓝 M) := by
    simpa [M] using ENNReal.Tendsto.mul_const
      (tendsto_areaErrorFactor_left (Module.finrank ℝ U)) (Or.inl one_ne_zero)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [mem_Ioi] at hr
  exact lintegral_normDet_le_euclideanHausdorffMeasure_image_fixed
    hs hf' hf'inj hfinj r hr

/-- Lower-dimensional area formula on a measurable injective differentiability piece whose
derivative is injective everywhere.  This is the exact globalization of the local chart bounds. -/
theorem lintegral_normDet_fderivWithin_eq_euclideanHausdorffMeasure_image_of_injective
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) (hfinj : InjOn f s) :
    (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume) =
      μHE[Module.finrank ℝ U] (f '' s) :=
  le_antisymm
    (lintegral_normDet_le_euclideanHausdorffMeasure_image_of_injective hs hf' hf'inj hfinj)
    (euclideanHausdorffMeasure_image_le_lintegral_normDet_of_injective hs hf' hf'inj)

omit [FiniteDimensional ℝ V] in
/-- A differentiable injective lower-dimensional parameterization of a measurable set is a
measurable embedding. -/
theorem measurableEmbedding_restrict_of_fderivWithin_general
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfinj : InjOn f s) : MeasurableEmbedding (s.restrict f) := by
  have hdiff : DifferentiableOn ℝ f s := fun x hx ↦ (hf' x hx).differentiableWithinAt
  exact hdiff.continuousOn.measurableEmbedding hs hfinj

/-- Measure form of the lower-dimensional area formula on an injective full-rank piece.  The
pushforward of source volume weighted by `normDet` is Euclidean Hausdorff measure restricted to
the image. -/
theorem map_withDensity_normDet_fderivWithin_eq_euclideanHausdorffMeasure
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) (hfinj : InjOn f s) :
    Measure.map f
        ((volume.restrict s).withDensity
          (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet)) =
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
        (f '' s) := by
  classical
  obtain ⟨u, hu, huf⟩ : ∃ u : U → V, Measurable u ∧ EqOn u f s := by
    refine ⟨piecewise s f 0, ?_, piecewise_eqOn _ _ _⟩
    refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn hs
    exact (show DifferentiableOn ℝ f s from
      fun x hx ↦ (hf' x hx).differentiableWithinAt).continuousOn
  have hu' : ∀ x ∈ s, HasFDerivWithinAt u (f' x) s x := fun x hx ↦
    (hf' x hx).congr (fun y hy ↦ huf hy) (huf hx)
  have huinj : InjOn u s := hfinj.congr huf.symm
  have hmap :
      Measure.map u
          ((volume.restrict s).withDensity
            (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet)) =
        (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
          (u '' s) := by
    apply Measure.ext
    intro q hq
    have hpre : MeasurableSet (u ⁻¹' q) := hu hq
    rw [Measure.map_apply hu hq, withDensity_apply _ hpre,
      Measure.restrict_apply hq]
    change (∫⁻ x in u ⁻¹' q,
      ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume.restrict s) = _
    rw [Measure.restrict_restrict hpre]
    change (∫⁻ x in u ⁻¹' q ∩ s,
      ENNReal.ofReal (f' x).toLinearMap.normDet ∂volume) = _
    have hsource : MeasurableSet (u ⁻¹' q ∩ s) := hpre.inter hs
    have harea :=
      lintegral_normDet_fderivWithin_eq_euclideanHausdorffMeasure_image_of_injective
        hsource
        (fun x hx ↦ (hu' x hx.2).mono inter_subset_right)
        (fun x hx ↦ hf'inj x hx.2)
        (huinj.mono inter_subset_right)
    rw [harea, image_preimage_inter]
  have hueq :
      u =ᵐ[(volume.restrict s).withDensity
        (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet)] f := by
    apply (withDensity_absolutelyContinuous _ _).ae_eq
    filter_upwards [ae_restrict_mem hs] with x hx
    exact huf hx
  calc
    Measure.map f
        ((volume.restrict s).withDensity
          (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet)) =
        Measure.map u
          ((volume.restrict s).withDensity
            (fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet)) :=
      Measure.map_congr hueq.symm
    _ = (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
        (u '' s) := hmap
    _ = (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
        (f '' s) := by rw [huf.image_eq]

/-- Weighted lower-dimensional change of variables on an injective full-rank differentiability
piece. -/
theorem lintegral_image_eq_lintegral_normDet_fderivWithin_mul
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {f' : U → U →L[ℝ] V} {s : Set U}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf'inj : ∀ x ∈ s, Function.Injective (f' x)) (hfinj : InjOn f s)
    (g : V → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in f '' s, g y
        ∂(Measure.euclideanHausdorffMeasure (Module.finrank ℝ U))) =
      ∫⁻ x in s,
        ENNReal.ofReal (f' x).toLinearMap.normDet * g (f x) ∂volume := by
  let J : U → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (f' x).toLinearMap.normDet
  have hJ : AEMeasurable J (volume.restrict s) := by
    simpa [J] using aemeasurable_ofReal_normDet_fderivWithin_general hs hf'
  have hf_meas : AEMeasurable f (volume.restrict s) := by
    apply ContinuousOn.aemeasurable₀ (fun x hx ↦ ?_) hs.nullMeasurableSet
    exact (hf' x hx).differentiableWithinAt.continuousWithinAt
  have hf_density : AEMeasurable f ((volume.restrict s).withDensity J) :=
    hf_meas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hgf : AEMeasurable (fun x ↦ g (f x)) (volume.restrict s) :=
    hg.comp_aemeasurable hf_meas
  have hmap :=
    map_withDensity_normDet_fderivWithin_eq_euclideanHausdorffMeasure
      hs hf' hf'inj hfinj
  change (∫⁻ y, g y ∂
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
        (f '' s)) = _
  rw [← hmap]
  rw [lintegral_map' hg.aemeasurable hf_density]
  rw [lintegral_withDensity_eq_lintegral_mul₀ hJ hgf]
  rfl

/-- A Lipschitz map admits a measurable full-volume source subset on which the within derivative
exists and is injective, provided injectivity of the within derivative holds almost everywhere.
This isolates the Rademacher exceptional set used by the global area formula. -/
theorem exists_measurable_fullMeasure_differentiableWithinAt_injective
    [MeasurableSpace U] [BorelSpace U]
    {C : ℝ≥0} {f : U → V} {s : Set U} (hs : MeasurableSet s)
    (hf : LipschitzOnWith C f s)
    (hinj : ∀ᵐ x ∂volume.restrict s,
      Function.Injective (fderivWithin ℝ f s x)) :
    ∃ t : Set U, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[volume] s ∧
      (∀ x ∈ t, DifferentiableWithinAt ℝ f s x) ∧
        ∀ x ∈ t, Function.Injective (fderivWithin ℝ f s x) := by
  let good : Set U :=
    {x | x ∈ s ∧ DifferentiableWithinAt ℝ f s x ∧
      Function.Injective (fderivWithin ℝ f s x)}
  have hgood_restrict : ∀ᵐ x ∂volume.restrict s, x ∈ good := by
    filter_upwards [ae_restrict_mem hs, hf.ae_differentiableWithinAt hs, hinj]
    intro x hxs hdiff hderiv
    exact ⟨hxs, hdiff, hderiv⟩
  have hgood_imp : ∀ᵐ x ∂volume, x ∈ s → x ∈ good :=
    (ae_restrict_iff' hs).1 hgood_restrict
  have hgood_eq : good =ᵐ[volume] s := by
    filter_upwards [hgood_imp] with x hx
    apply propext
    exact ⟨fun h ↦ h.1, hx⟩
  have hgood_null : NullMeasurableSet good volume :=
    hs.nullMeasurableSet.congr hgood_eq.symm
  obtain ⟨t, ht_good, ht_meas, ht_good_ae⟩ := hgood_null.exists_measurable_subset_ae_eq
  have ht_sub : t ⊆ s := fun x hx ↦ (ht_good hx).1
  refine ⟨t, ht_sub, ht_meas, ht_good_ae.trans hgood_eq, ?_, ?_⟩
  · exact fun x hx ↦ (ht_good hx).2.1
  · exact fun x hx ↦ (ht_good hx).2.2

/-- A Lipschitz restriction admits a measurable full-volume source subset on which it is
differentiable within the original source set at every point. -/
private theorem exists_measurable_fullMeasure_differentiableWithinAt
    [MeasurableSpace U] [BorelSpace U]
    {C : ℝ≥0} {f : U → V} {s : Set U} (hs : MeasurableSet s)
    (hf : LipschitzOnWith C f s) :
    ∃ t : Set U, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[volume] s ∧
      ∀ x ∈ t, DifferentiableWithinAt ℝ f s x := by
  let good : Set U := {x | x ∈ s ∧ DifferentiableWithinAt ℝ f s x}
  have hgood_restrict : ∀ᵐ x ∂volume.restrict s, x ∈ good := by
    filter_upwards [ae_restrict_mem hs, hf.ae_differentiableWithinAt hs]
    intro x hxs hdiff
    exact ⟨hxs, hdiff⟩
  have hgood_imp : ∀ᵐ x ∂volume, x ∈ s → x ∈ good :=
    (ae_restrict_iff' hs).1 hgood_restrict
  have hgood_eq : good =ᵐ[volume] s := by
    filter_upwards [hgood_imp] with x hx
    apply propext
    exact ⟨fun h ↦ h.1, hx⟩
  have hgood_null : NullMeasurableSet good volume :=
    hs.nullMeasurableSet.congr hgood_eq.symm
  obtain ⟨t, ht_good, ht_meas, ht_good_ae⟩ := hgood_null.exists_measurable_subset_ae_eq
  exact ⟨t, fun x hx ↦ (ht_good hx).1, ht_meas, ht_good_ae.trans hgood_eq,
    fun x hx ↦ (ht_good hx).2⟩

/-- Almost-everywhere chain rule for postcomposition by a continuous linear map on a measurable
Lipschitz source set.  Density-point uniqueness removes a `UniqueDiffWithinAt` assumption. -/
theorem ae_fderivWithin_clm_comp_of_lipschitzOnWith
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace U] [BorelSpace U]
    {C : ℝ≥0} {f : U → V} {s : Set U} (hs : MeasurableSet s)
    (hf : LipschitzOnWith C f s) (L : V →L[ℝ] W) :
    ∀ᵐ x ∂volume.restrict s,
      fderivWithin ℝ (fun z ↦ L (f z)) s x =
        L.comp (fderivWithin ℝ f s x) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume s,
    hf.ae_differentiableWithinAt hs]
  intro x hxdensity hfdiff
  have hcomp : HasFDerivWithinAt (fun z ↦ L (f z))
      (L.comp (fderivWithin ℝ f s x)) s x :=
    L.hasFDerivAt.comp_hasFDerivWithinAt x hfdiff.hasFDerivWithinAt
  have hcompdiff : DifferentiableWithinAt ℝ (fun z ↦ L (f z)) s x :=
    by simpa [Function.comp_def] using
      (DifferentiableAt.comp_differentiableWithinAt (f := f) (g := fun y ↦ L y)
        (x := x) L.differentiableAt hfdiff)
  exact HasFDerivWithinAt.eq_of_volume_density_one hxdensity
    hcompdiff.hasFDerivWithinAt hcomp

/-- Equal-rank Lipschitz area formula with multiplicity.  The returned measurable source pieces
are pairwise disjoint and injective for `f`; almost everywhere, their union is exactly the
nonzero-Jacobian region.  Thus singular derivatives are retained in the source statement and
eliminated only because their `normDet` density vanishes. -/
theorem exists_equalRank_lipschitz_area_multiplicity_partition
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V)
    {K : ℝ≥0} {f : U → V} {s : Set U} (hs : MeasurableSet s)
    (hf : LipschitzOnWith K f s) (w : V → ℝ≥0∞) (hw : Measurable w) :
    ∃ p : ℕ → Set U,
      Pairwise (Disjoint on p) ∧
        (∀ n, MeasurableSet (p n)) ∧
          (∀ n, p n ⊆ s) ∧
            (∀ n, InjOn f (p n)) ∧
              (∀ n, MeasurableSet (f '' p n)) ∧
                (∀ᵐ x ∂volume.restrict s,
                  (ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet ≠ 0 ↔
                    x ∈ ⋃ n, p n)) ∧
                  (∫⁻ x in s,
                      ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * w (f x)
                        ∂volume) =
                    ∫⁻ y, ∑' n, (f '' p n).indicator w y ∂volume := by
  classical
  let f' : U → U →L[ℝ] V := fun x ↦ fderivWithin ℝ f s x
  obtain ⟨t, ht_sub, ht_meas, ht_ae, ht_diff⟩ :=
    exists_measurable_fullMeasure_differentiableWithinAt hs hf
  have ht_deriv : ∀ x ∈ t, HasFDerivWithinAt f (f' x) t x := fun x hx ↦
    (ht_diff x hx).hasFDerivWithinAt.mono ht_sub
  let hfm : AEMeasurable f' (volume.restrict t) :=
    aemeasurable_fderivWithin_general ht_meas ht_deriv
  let D : U → U →L[ℝ] V := hfm.mk f'
  have hD_meas : Measurable D := hfm.measurable_mk
  have hD_eq : f' =ᵐ[volume.restrict t] D := hfm.ae_eq_mk
  let r₀ : Set U := t ∩ {x | (D x).toLinearMap.normDet ≠ 0}
  have hr₀_meas : MeasurableSet r₀ := by
    apply ht_meas.inter
    exact (measurableSet_singleton 0).compl.preimage
      (continuous_normDet.measurable.comp hD_meas)
  have hD_imp : ∀ᵐ x ∂volume, x ∈ t → f' x = D x :=
    (ae_restrict_iff' ht_meas).1 hD_eq
  let good : Set U := {x | x ∈ r₀ ∧ f' x = D x}
  have hgood_eq : good =ᵐ[volume] r₀ := by
    filter_upwards [hD_imp] with x hx
    apply propext
    exact ⟨fun h ↦ h.1, fun hrx ↦ ⟨hrx, hx hrx.1⟩⟩
  have hgood_null : NullMeasurableSet good volume :=
    hr₀_meas.nullMeasurableSet.congr hgood_eq.symm
  obtain ⟨r, hr_good, hr_meas, hr_good_ae⟩ :=
    hgood_null.exists_measurable_subset_ae_eq
  have hr_r₀_ae : r =ᵐ[volume] r₀ := hr_good_ae.trans hgood_eq
  have hr_sub_t : r ⊆ t := fun x hx ↦ (hr_good hx).1.1
  have hr_sub_s : r ⊆ s := hr_sub_t.trans ht_sub
  have hr_diff : ∀ x ∈ r, DifferentiableWithinAt ℝ f s x := fun x hx ↦
    ht_diff x (hr_sub_t hx)
  have hr_deriv : ∀ x ∈ r, HasFDerivWithinAt f (f' x) r x := fun x hx ↦
    (hr_diff x hx).hasFDerivWithinAt.mono hr_sub_s
  have hr_f'inj : ∀ x ∈ r, Function.Injective (f' x) := by
    intro x hx
    have hxgood := hr_good hx
    rw [hxgood.2]
    exact ((D x).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hxgood.1.2
  have hD_on_s : f' =ᵐ[volume.restrict s] D := by
    have hrestrict : volume.restrict t = volume.restrict s :=
      Measure.restrict_congr_set ht_ae
    rw [← hrestrict]
    exact hD_eq
  have ht_mem : ∀ᵐ x ∂volume.restrict s, x ∈ t := by
    rw [ae_restrict_iff' hs]
    filter_upwards [ht_ae] with x hx hxs
    change x ∈ t
    rw [hx]
    exact hxs
  have hr_mem_eq : ∀ᵐ x ∂volume.restrict s, x ∈ r ↔ x ∈ r₀ := by
    exact ae_restrict_of_ae (hr_r₀_ae.mono fun _ hx ↦ iff_of_eq hx)
  have hregular_iff : ∀ᵐ x ∂volume.restrict s,
      (ENNReal.ofReal (f' x).toLinearMap.normDet ≠ 0 ↔ x ∈ r) := by
    filter_upwards [ht_mem, hD_on_s, hr_mem_eq] with x hxt hDx hrx
    have hnorm_iff : ENNReal.ofReal (f' x).toLinearMap.normDet ≠ 0 ↔
        (f' x).toLinearMap.normDet ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      constructor
      · exact ne_of_gt
      · intro hne
        exact lt_of_le_of_ne (f' x).toLinearMap.normDet_nonneg (Ne.symm hne)
    rw [hnorm_iff, hrx]
    change (f' x).toLinearMap.normDet ≠ 0 ↔
      x ∈ t ∧ (D x).toLinearMap.normDet ≠ 0
    simp only [hxt, true_and]
    rw [hDx]
  by_cases hrne : r.Nonempty
  · let q : ℝ≥0 := 2
    have hq : 1 < q := by norm_num [q]
    obtain ⟨a, A, ha_disj, ha_meas, ha_cover, ha_approx, hA_rep⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f r f' hr_deriv
        (areaControlRadius q hq) fun B ↦ (areaControlRadius_pos q hq B).ne'
    have hAinj (n : ℕ) : Function.Injective (A n) := by
      obtain ⟨x, hx, hAx⟩ := hA_rep hrne n
      rw [hAx]
      exact hr_f'inj x hx
    let p : ℕ → Set U := fun n ↦ r ∩ a n
    have hp_meas (n : ℕ) : MeasurableSet (p n) := hr_meas.inter (ha_meas n)
    have hp_sub_r (n : ℕ) : p n ⊆ r := inter_subset_left
    have hp_sub_s (n : ℕ) : p n ⊆ s := (hp_sub_r n).trans hr_sub_s
    have hp_disj : Pairwise (Disjoint on p) :=
      pairwise_disjoint_mono ha_disj fun _ x hx ↦ hx.2
    have hp_union : r = ⋃ n, p n := by
      rw [← inter_iUnion]
      exact Subset.antisymm (subset_inter Subset.rfl ha_cover) inter_subset_left
    have hp_inj (n : ℕ) : InjOn f (p n) := by
      let e := continuousLinearEquivRange (A n) (hAinj n)
      have hsmall : areaControlRadius q hq (A n) *
          ‖(e.symm : (A n).range →L[ℝ] U)‖₊ < 1 :=
        (areaControlRadius_spec q hq (A n) (hAinj n)).1.trans_le tsub_le_self
      have hanti := ApproximatesLinearOn.antilipschitzWith_linearRangeReparam_restrict
        (ha_approx n) (hAinj n) hsmall
      intro x hx y hy hxy
      let zx : e '' p n := ⟨e x, ⟨x, hx, rfl⟩⟩
      let zy : e '' p n := ⟨e y, ⟨y, hy, rfl⟩⟩
      have hz : zx = zy := hanti.injective (by
        change linearRangeReparam f (A n) (hAinj n) zx.1 =
          linearRangeReparam f (A n) (hAinj n) zy.1
        simpa [zx, zy, e, linearRangeReparam] using hxy)
      have hexy : e x = e y := by
        simpa [zx, zy] using congr_arg Subtype.val hz
      exact e.injective hexy
    have himage_meas (n : ℕ) : MeasurableSet (f '' p n) := by
      apply (hp_meas n).image_of_continuousOn_injOn
      · exact (hf.mono (hp_sub_s n)).continuousOn
      · exact hp_inj n
    have hcoverage : ∀ᵐ x ∂volume.restrict s,
        (ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet ≠ 0 ↔
          x ∈ ⋃ n, p n) := by
      simpa only [f', ← hp_union] using hregular_iff
    have hsource_r :
        (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet * w (f x) ∂volume) =
          ∫⁻ x in r, ENNReal.ofReal (f' x).toLinearMap.normDet * w (f x) ∂volume := by
      rw [← lintegral_indicator hs, ← lintegral_indicator hr_meas]
      apply lintegral_congr_ae
      have hregular_imp := (ae_restrict_iff' hs).1 hregular_iff
      filter_upwards [hregular_imp] with x hx
      by_cases hxs : x ∈ s
      · have hiff := hx hxs
        by_cases hJ : ENNReal.ofReal (f' x).toLinearMap.normDet ≠ 0
        · have hxr : x ∈ r := hiff.mp hJ
          simp [hxs, hxr]
        · have hJzero : ENNReal.ofReal (f' x).toLinearMap.normDet = 0 :=
            not_ne_iff.mp hJ
          have hxnr : x ∉ r := fun hxr ↦ hJ (hiff.mpr hxr)
          simp [hxs, hJzero, hxnr]
      · have hxnr : x ∉ r := fun hxr ↦ hxs (hr_sub_s hxr)
        simp [hxs, hxnr]
    have hpiece (n : ℕ) :
        (∫⁻ x in p n, ENNReal.ofReal (f' x).toLinearMap.normDet * w (f x) ∂volume) =
          ∫⁻ y in f '' p n, w y ∂volume := by
      have harea := lintegral_image_eq_lintegral_normDet_fderivWithin_mul
        (hp_meas n)
        (fun x hx ↦ (hr_deriv x hx.1).mono inter_subset_left)
        (fun x hx ↦ hr_f'inj x hx.1) (hp_inj n) w hw
      rw [hrank, InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at harea
      exact harea.symm
    refine ⟨p, hp_disj, hp_meas, hp_sub_s, hp_inj, himage_meas, hcoverage, ?_⟩
    rw [show (∫⁻ x in s,
      ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * w (f x) ∂volume) =
        ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet * w (f x) ∂volume by rfl]
    rw [hsource_r, hp_union,
      lintegral_iUnion hp_meas hp_disj]
    calc
      (∑' n, ∫⁻ x in p n,
          ENNReal.ofReal (f' x).toLinearMap.normDet * w (f x) ∂volume) =
          ∑' n, ∫⁻ y in f '' p n, w y ∂volume := by
        congr 1
        funext n
        exact hpiece n
      _ = ∑' n, ∫⁻ y, (f '' p n).indicator w y ∂volume := by
        congr 1
        funext n
        exact (lintegral_indicator (himage_meas n) w).symm
      _ = ∫⁻ y, ∑' n, (f '' p n).indicator w y ∂volume := by
        symm
        exact lintegral_tsum fun n ↦ (hw.indicator (himage_meas n)).aemeasurable
  · have hrempty : r = ∅ := not_nonempty_iff_eq_empty.mp hrne
    let p : ℕ → Set U := fun _ ↦ ∅
    have hcoverage : ∀ᵐ x ∂volume.restrict s,
        (ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet ≠ 0 ↔
          x ∈ ⋃ n, p n) := by
      simpa only [f', hrempty, p, iUnion_empty, mem_empty_iff_false, iff_false] using
        hregular_iff
    refine ⟨p, ?_, ?_, ?_, ?_, ?_, hcoverage, ?_⟩
    · intro i j _
      change Disjoint (∅ : Set U) ∅
      exact Set.disjoint_empty (∅ : Set U)
    · exact fun _ ↦ MeasurableSet.empty
    · exact fun _ ↦ empty_subset _
    · simp [p]
    · exact fun _ ↦ by simp [p]
    · have hzero : ∀ᵐ x ∂volume.restrict s,
          ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet = 0 := by
        filter_upwards [hregular_iff] with x hx
        apply not_ne_iff.mp
        intro hne
        have hxr : x ∈ r := hx.mp hne
        rw [hrempty] at hxr
        exact hxr.elim
      calc
        (∫⁻ x in s,
            ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * w (f x) ∂volume) =
            ∫⁻ _x : U in s, 0 := by
          apply lintegral_congr_ae
          filter_upwards [hzero] with x hx
          simp [hx]
        _ = 0 := by simp
        _ = ∫⁻ y, ∑' n, (f '' p n).indicator w y ∂volume := by simp [p]

/-- Weighted lower-dimensional area formula for an injective Lipschitz parameterization whose
within derivative has full rank almost everywhere.  Rademacher's theorem removes the null
nondifferentiability set; Lipschitz Hausdorff distortion removes its image. -/
theorem lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_lipschitzOnWith
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {C : ℝ≥0} {f : U → V} {s : Set U} (hs : MeasurableSet s)
    (hf : LipschitzOnWith C f s) (hfinj : InjOn f s)
    (hf'inj : ∀ᵐ x ∂volume.restrict s,
      Function.Injective (fderivWithin ℝ f s x))
    (g : V → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in f '' s, g y
        ∂(Measure.euclideanHausdorffMeasure (Module.finrank ℝ U))) =
      ∫⁻ x in s,
        ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * g (f x) ∂volume := by
  obtain ⟨t, ht_sub, ht_meas, ht_ae, ht_diff, ht_inj⟩ :=
    exists_measurable_fullMeasure_differentiableWithinAt_injective hs hf hf'inj
  have ht_deriv : ∀ x ∈ t,
      HasFDerivWithinAt f (fderivWithin ℝ f s x) t x := fun x hx ↦
    (ht_diff x hx).hasFDerivWithinAt.mono ht_sub
  have harea_t :=
    lintegral_image_eq_lintegral_normDet_fderivWithin_mul ht_meas ht_deriv ht_inj
      (hfinj.mono ht_sub) g hg
  have hsource_bad : volume (s \ t) = 0 := (ae_eq_set.1 ht_ae).2
  have hsource_bad_euclidean :
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure U) (s \ t) = 0 := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact hsource_bad
  have himage_bad :
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V)
          (f '' (s \ t)) = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V)
          (f '' (s \ t)) ≤
          (C : ℝ≥0∞) ^ Module.finrank ℝ U *
            (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure U)
              (s \ t) :=
        LipschitzOnWith.euclideanHausdorffMeasure_image_le
          (hf.mono sdiff_subset) (Module.finrank ℝ U)
      _ = 0 := by rw [hsource_bad_euclidean, mul_zero]
  have himage_sub : f '' t ⊆ f '' s := image_mono ht_sub
  have himage_diff_sub : f '' s \ f '' t ⊆ f '' (s \ t) := by
    rintro y ⟨⟨x, hxs, rfl⟩, hnot⟩
    refine ⟨x, ⟨hxs, ?_⟩, rfl⟩
    intro hxt
    exact hnot ⟨x, hxt, rfl⟩
  have himage_ae : f '' t =ᵐ[
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V)] f '' s := by
    apply ae_eq_set.2
    constructor
    · apply measure_mono_null ?_ measure_empty
      intro y hy
      exact (hy.2 (himage_sub hy.1)).elim
    · exact measure_mono_null himage_diff_sub himage_bad
  change (∫⁻ y, g y ∂
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
        (f '' s)) =
    ∫⁻ x,
      ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * g (f x)
        ∂volume.restrict s
  calc
    (∫⁻ y, g y ∂
        (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
          (f '' s)) =
        ∫⁻ y, g y ∂
          (Measure.euclideanHausdorffMeasure (Module.finrank ℝ U) : Measure V).restrict
            (f '' t) := by rw [Measure.restrict_congr_set himage_ae]
    _ = ∫⁻ x,
        ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * g (f x)
          ∂volume.restrict t := harea_t
    _ = ∫⁻ x,
        ENNReal.ofReal (fderivWithin ℝ f s x).toLinearMap.normDet * g (f x)
          ∂volume.restrict s := by rw [Measure.restrict_congr_set ht_ae]

/-- Weighted lower-dimensional area formula for an injective Lipschitz right-inverse chart.  This
is the projection-chart interface used in Ball's convex-boundary argument. -/
theorem lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_comp_eq_id
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {C : ℝ≥0} {φ : U → V} {s : Set U} (hs : MeasurableSet s)
    (hφ : LipschitzOnWith C φ s) (hφinj : InjOn φ s) (P : V →L[ℝ] U)
    (heq : EqOn id (fun z ↦ P (φ z)) s) (g : V → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in φ '' s, g y
        ∂(Measure.euclideanHausdorffMeasure (Module.finrank ℝ U))) =
      ∫⁻ z in s,
        ENNReal.ofReal (fderivWithin ℝ φ s z).toLinearMap.normDet * g (φ z) ∂volume := by
  exact lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_lipschitzOnWith
    hs hφ hφinj
      (ae_injective_fderivWithin_of_lipschitzOnWith_of_comp_eq_id hs hφ P heq) g hg

/-- A zero-Hausdorff-measure set has arbitrarily fine countable covers with arbitrarily small
Hausdorff sum. -/
private theorem exists_hausdorffMeasure_cover_tsum_lt
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {q : ℝ} {s : Set X}
    (hs : Measure.hausdorffMeasure q s = 0) {r ε : ℝ≥0∞}
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, ediam (t n) ≤ r) ∧
      (∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q) < ε := by
  have hinf :
      (⨅ (t : ℕ → Set X) (_ht : s ⊆ ⋃ n, t n) (_hr : ∀ n, ediam (t n) ≤ r),
        ∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q) = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      (⨅ (t : ℕ → Set X) (_ht : s ⊆ ⋃ n, t n)
          (_hr : ∀ n, ediam (t n) ≤ r),
          ∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q) ≤
          ⨆ (r : ℝ≥0∞) (_hr : 0 < r),
            ⨅ (t : ℕ → Set X) (_ht : s ⊆ ⋃ n, t n)
              (_hdiam : ∀ n, ediam (t n) ≤ r),
                ∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q :=
        le_iSup_of_le r (le_iSup_of_le hr le_rfl)
      _ = Measure.hausdorffMeasure q s := (Measure.hausdorffMeasure_apply q s).symm
      _ = 0 := hs
  have hlt :
      (⨅ (t : ℕ → Set X) (_ht : s ⊆ ⋃ n, t n) (_hr : ∀ n, ediam (t n) ≤ r),
        ∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q) < ε := by
    rw [hinf]
    exact hε
  simpa only [iInf_lt_iff, exists_prop] using hlt

/-- If a set has Hausdorff measure strictly below a prescribed bound, then at every positive
scale it has a countable cover whose Hausdorff sum is below the same bound. -/
private theorem exists_hausdorffMeasure_cover_tsum_lt_of_lt
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {q : ℝ} {s : Set X} {A r : ℝ≥0∞}
    (hs : Measure.hausdorffMeasure q s < A) (hr : 0 < r) :
    ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, ediam (t n) ≤ r) ∧
      (∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q) < A := by
  have hinner :
      (⨅ (t : ℕ → Set X) (_ht : s ⊆ ⋃ n, t n) (_hr : ∀ n, ediam (t n) ≤ r),
        ∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ q) ≤
        Measure.hausdorffMeasure q s := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hinner.trans_lt hs
  simpa only [iInf_lt_iff, exists_prop] using hlt

/-- The scalar Eilenberg covering argument, in the form needed for the critical-set step.  A
Lipschitz restriction admits a measurable upper envelope for its codimension-one fiber contents,
whose integral is controlled by the Lipschitz constant and any strict upper bound for the source
Hausdorff measure. -/
private theorem exists_measurable_hausdorffMeasure_fiber_envelope {d : ℕ} (hd : 0 < d)
    {L : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfcont : Continuous f)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hf : LipschitzOnWith L f s)
    {A : ℝ≥0∞} (hA : Measure.hausdorffMeasure (d : ℝ) s < A) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) ≤ G y) ∧
        (∫⁻ y, G y ∂(volume : Measure ℝ)) ≤ (L : ℝ≥0∞) * A := by
  let r : ℕ → ℝ≥0∞ := fun k ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hr_pos (k : ℕ) : 0 < r k := by
    simp [r]
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    exact (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  have hcover (k : ℕ) :
      ∃ t : ℕ → Set (EuclideanSpace ℝ (Fin d)),
        s ⊆ ⋃ n, t n ∧ (∀ n, ediam (t n) ≤ r k) ∧
          (∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ (d : ℝ)) < A :=
    exists_hausdorffMeasure_cover_tsum_lt_of_lt hA (hr_pos k)
  choose t ht_cover ht_diam ht_sum using hcover
  let u : ℕ → ℕ → Set (EuclideanSpace ℝ (Fin d)) :=
    fun k n ↦ closure (t k n ∩ s)
  have ht_bounded (k n : ℕ) : Bornology.IsBounded (t k n) := by
    apply Metric.isBounded_iff_ediam_ne_top.2
    exact ne_top_of_le_ne_top (by simp [r]) (ht_diam k n)
  have hu_compact (k n : ℕ) : IsCompact (u k n) := by
    exact ((ht_bounded k n).subset inter_subset_left).isCompact_closure
  have hu_diam (k n : ℕ) : ediam (u k n) = ediam (t k n ∩ s) := by
    exact ediam_closure (t k n ∩ s)
  have hu_cover (k : ℕ) : s ⊆ ⋃ n, u k n := by
    intro x hx
    rcases mem_iUnion.mp (ht_cover k hx) with ⟨n, hxn⟩
    exact mem_iUnion.2 ⟨n, subset_closure ⟨hxn, hx⟩⟩
  have hu_lip (k n : ℕ) : LipschitzOnWith L f (u k n) := by
    exact (hf.mono inter_subset_right).closure hfcont.continuousOn
  have himage_meas (k n : ℕ) : MeasurableSet (f '' u k n) :=
    (hu_compact k n).image hfcont |>.measurableSet
  have hu_sum (k : ℕ) :
      (∑' n, ediam (u k n) ^ (d : ℝ)) < A := by
    refine (ENNReal.tsum_le_tsum fun n ↦ ?_).trans_lt (ht_sum k)
    by_cases hn : (t k n ∩ s).Nonempty
    · have htn : (t k n).Nonempty := hn.mono inter_subset_left
      simp only [htn, ciSup_pos]
      rw [hu_diam]
      exact ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) (by positivity)
    · have hempty : t k n ∩ s = ∅ := not_nonempty_iff_eq_empty.mp hn
      simp [u, hempty, Nat.ne_of_gt hd]
  let F : ℕ → ℝ → ℝ≥0∞ := fun k y ↦
    ∑' n, (f '' u k n).indicator
      (fun _ ↦ ediam (u k n) ^ ((d - 1 : ℕ) : ℝ)) y
  have hF_meas (k : ℕ) : Measurable (F k) := by
    apply Measurable.tsum
    intro n
    exact measurable_const.indicator (himage_meas k n)
  have himage_volume (k n : ℕ) :
      volume (f '' u k n) ≤ (L : ℝ≥0∞) * ediam (u k n) := by
    calc
      volume (f '' u k n) ≤ ediam (f '' u k n) := Real.volume_le_diam _
      _ ≤ (L : ℝ≥0∞) * ediam (u k n) := by
        apply ediam_image_le_iff.2
        intro x hx y hy
        exact (hu_lip k n hx hy).trans
          (mul_le_mul_right (edist_le_ediam_of_mem hx hy) _)
  have hF_integral (k : ℕ) :
      (∫⁻ y, F k y ∂(volume : Measure ℝ)) ≤ (L : ℝ≥0∞) * A := by
    rw [lintegral_tsum fun n ↦
      (measurable_const.indicator (himage_meas k n)).aemeasurable]
    calc
      (∑' n, ∫⁻ y, (f '' u k n).indicator
          (fun _ ↦ ediam (u k n) ^ ((d - 1 : ℕ) : ℝ)) y ∂volume) =
          ∑' n, ediam (u k n) ^ ((d - 1 : ℕ) : ℝ) * volume (f '' u k n) := by
        congr 1
        funext n
        rw [lintegral_indicator (himage_meas k n), setLIntegral_const]
      _ ≤ ∑' n, ediam (u k n) ^ ((d - 1 : ℕ) : ℝ) *
          ((L : ℝ≥0∞) * ediam (u k n)) := by
        exact ENNReal.tsum_le_tsum fun n ↦ mul_le_mul_right (himage_volume k n) _
      _ = ∑' n, (L : ℝ≥0∞) * ediam (u k n) ^ (d : ℝ) := by
        congr 1
        funext n
        rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast]
        calc
          ediam (u k n) ^ (d - 1) * ((L : ℝ≥0∞) * ediam (u k n)) =
              (L : ℝ≥0∞) * (ediam (u k n) ^ (d - 1) * ediam (u k n)) := by
            ac_rfl
          _ = (L : ℝ≥0∞) * ediam (u k n) ^ d := by
            rw [pow_sub_one_mul (Nat.ne_of_gt hd)]
      _ = (L : ℝ≥0∞) * ∑' n, ediam (u k n) ^ (d : ℝ) :=
        ENNReal.tsum_mul_left
      _ ≤ (L : ℝ≥0∞) * A := mul_le_mul_right (hu_sum k).le _
  have hraw_fiber_le (y : ℝ) :
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) ≤
        liminf (fun k ↦ F k y) atTop := by
    let ι : ℕ → Type := fun k ↦ {n : ℕ // (u k n ∩ f ⁻¹' {y}).Nonempty}
    let v : ∀ k, ι k → Set (EuclideanSpace ℝ (Fin d)) :=
      fun k n ↦ u k n.1 ∩ f ⁻¹' {y}
    have hv_diam (k : ℕ) (n : ι k) : ediam (v k n) ≤ r k := by
      calc
        ediam (v k n) ≤ ediam (u k n.1) := ediam_mono inter_subset_left
        _ = ediam (t k n.1 ∩ s) := hu_diam k n.1
        _ ≤ ediam (t k n.1) := ediam_mono inter_subset_left
        _ ≤ r k := ht_diam k n.1
    have hv_cover (k : ℕ) : s ∩ f ⁻¹' {y} ⊆ ⋃ n, v k n := by
      intro x hx
      rcases mem_iUnion.mp (hu_cover k hx.1) with ⟨n, hxn⟩
      let j : ι k := ⟨n, ⟨x, hxn, hx.2⟩⟩
      exact mem_iUnion.2 ⟨j, hxn, hx.2⟩
    have hcover_bound := Measure.hausdorffMeasure_le_liminf_tsum
      (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) r hr_lim v
      (Eventually.of_forall hv_diam) (Eventually.of_forall hv_cover)
    refine hcover_bound.trans (liminf_le_liminf (Eventually.of_forall fun k ↦ ?_))
    calc
      (∑' n : ι k, ediam (v k n) ^ (((d - 1 : ℕ) : ℝ))) ≤
          ∑' n : ι k, ediam (u k n.1) ^ (((d - 1 : ℕ) : ℝ)) := by
        exact ENNReal.tsum_le_tsum fun n ↦
          ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) (by positivity)
      _ ≤ ∑' n, (f '' u k n).indicator
          (fun _ ↦ ediam (u k n) ^ (((d - 1 : ℕ) : ℝ))) y := by
        apply ENNReal.summable.tsum_le_tsum_of_inj (fun n : ι k ↦ n.1)
          Subtype.coe_injective (fun _ _ ↦ zero_le)
        · intro n
          have hy : y ∈ f '' u k n.1 := by
            rcases n.2 with ⟨x, hx, hfx⟩
            exact ⟨x, hx, mem_singleton_iff.mp hfx⟩
          rw [indicator_of_mem hy]
        · exact ENNReal.summable
      _ = F k y := rfl
  let G : ℝ → ℝ≥0∞ := fun y ↦ liminf (fun k ↦ F k y) atTop
  have hG : Measurable G := Measurable.liminf hF_meas
  refine ⟨G, hG, hraw_fiber_le, ?_⟩
  calc
    (∫⁻ y, G y ∂(volume : Measure ℝ)) ≤
        liminf (fun k ↦ ∫⁻ y, F k y ∂(volume : Measure ℝ)) atTop :=
      lintegral_liminf_le hF_meas
    _ ≤ liminf (fun _k : ℕ ↦ (L : ℝ≥0∞) * A) atTop :=
      liminf_le_liminf (Eventually.of_forall hF_integral)
    _ = (L : ℝ≥0∞) * A := by simp

/-- On a measurable finite-Hausdorff-measure set where the derivative vanishes, almost every
level has zero codimension-one Hausdorff measure.  The proof partitions the set into pieces on
which the map has arbitrarily small Lipschitz constant and then applies the Eilenberg envelope. -/
private theorem ae_hausdorffMeasure_critical_fiber_eq_zero_of_finite {d : ℕ} (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hfcont : Continuous f)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : MeasurableSet s)
    (hcrit : ∀ x ∈ s, DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0)
    (hfinite : Measure.hausdorffMeasure (d : ℝ) s ≠ ∞) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) = 0 := by
  classical
  by_cases hsne : s.Nonempty
  · let δ : ℕ → ℝ≥0 := fun m ↦ ((m + 1 : ℕ) : ℝ≥0)⁻¹
    have hδpos (m : ℕ) : δ m ≠ 0 := by
      simp [δ]
    have hderiv : ∀ x ∈ s, HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) s x := by
      intro x hx
      have h := HasFDerivAt.hasFDerivWithinAt (s := s) (hcrit x hx).1.hasFDerivAt
      simpa [(hcrit x hx).2] using h
    have hpartition (m : ℕ) :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s
        (fun _ ↦ (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) hderiv
        (fun _ ↦ δ m) (fun _ ↦ hδpos m)
    choose t A ht_disj ht_meas ht_cover ht_approx ht_source using hpartition
    let p : ℕ → ℕ → Set (EuclideanSpace ℝ (Fin d)) :=
      fun m n ↦ s ∩ t m n
    have hp_meas (m n : ℕ) : MeasurableSet (p m n) :=
      hs.inter (ht_meas m n)
    have hp_disj (m : ℕ) : Pairwise (Disjoint on p m) :=
      pairwise_disjoint_mono (ht_disj m) fun _ x hx ↦ hx.2
    have hp_union (m : ℕ) : s = ⋃ n, p m n := by
      rw [← inter_iUnion]
      exact Subset.antisymm (subset_inter Subset.rfl (ht_cover m)) inter_subset_left
    have hAzero (m n : ℕ) : A m n = 0 := by
      rcases ht_source m hsne n with ⟨y, hy, hAy⟩
      simpa using hAy
    have hp_lip (m n : ℕ) : LipschitzOnWith (δ m) f (p m n) := by
      have happ := ht_approx m n
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x hx y hy
      simpa [p, hAzero m n] using happ x hx y hy
    let e : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ (n + 1)
    let B : ℕ → ℕ → ℝ≥0∞ := fun m n ↦
      Measure.hausdorffMeasure (d : ℝ) (p m n) + e n
    have hp_finite (m n : ℕ) :
        Measure.hausdorffMeasure (d : ℝ) (p m n) ≠ ∞ :=
      ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
    have hBstrict (m n : ℕ) :
        Measure.hausdorffMeasure (d : ℝ) (p m n) < B m n := by
      exact ENNReal.lt_add_right (hp_finite m n) (by simp [e])
    have henv (m n : ℕ) :=
      exists_measurable_hausdorffMeasure_fiber_envelope hd hfcont (hp_lip m n)
        (hBstrict m n)
    choose G hG_meas hG_fiber hG_integral using henv
    let H : ℕ → ℝ → ℝ≥0∞ := fun m y ↦ ∑' n, G m n y
    have hH_meas (m : ℕ) : Measurable (H m) := by
      exact Measurable.tsum fun n ↦ hG_meas m n
    have hB_sum (m : ℕ) :
        (∑' n, B m n) = Measure.hausdorffMeasure (d : ℝ) s + 1 := by
      have hmeasure :
          (∑' n, Measure.hausdorffMeasure (d : ℝ) (p m n)) =
            Measure.hausdorffMeasure (d : ℝ) s := by
        rw [← measure_iUnion (hp_disj m) (hp_meas m), ← hp_union m]
      calc
        (∑' n, B m n) =
            (∑' n, Measure.hausdorffMeasure (d : ℝ) (p m n)) + ∑' n, e n :=
          ENNReal.tsum_add
        _ = Measure.hausdorffMeasure (d : ℝ) s + 1 := by
          rw [hmeasure]
          simp [e, ENNReal.tsum_geometric_add_one]
          rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    have hH_integral (m : ℕ) :
        (∫⁻ y, H m y ∂(volume : Measure ℝ)) ≤
          (δ m : ℝ≥0∞) * (Measure.hausdorffMeasure (d : ℝ) s + 1) := by
      rw [lintegral_tsum fun n ↦ (hG_meas m n).aemeasurable]
      calc
        (∑' n, ∫⁻ y, G m n y ∂(volume : Measure ℝ)) ≤
            ∑' n, (δ m : ℝ≥0∞) * B m n :=
          ENNReal.tsum_le_tsum fun n ↦ hG_integral m n
        _ = (δ m : ℝ≥0∞) * ∑' n, B m n := ENNReal.tsum_mul_left
        _ = (δ m : ℝ≥0∞) *
            (Measure.hausdorffMeasure (d : ℝ) s + 1) := by rw [hB_sum m]
    have hraw_le (m : ℕ) (y : ℝ) :
        Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) ≤ H m y := by
      have hunion : s ∩ f ⁻¹' {y} = ⋃ n, p m n ∩ f ⁻¹' {y} := by
        rw [hp_union m, iUnion_inter]
      rw [hunion]
      exact (measure_iUnion_le _).trans
        (ENNReal.tsum_le_tsum fun n ↦ hG_fiber m n y)
    let K : ℝ → ℝ≥0∞ := fun y ↦ liminf (fun m ↦ H m y) atTop
    have hK_meas : Measurable K := Measurable.liminf hH_meas
    have hraw_K (y : ℝ) :
        Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) ≤ K y := by
      exact (le_iInf fun m ↦ hraw_le m y).trans iInf_le_liminf
    have hδ_lim : Tendsto (fun m ↦ (δ m : ℝ≥0∞)) atTop (𝓝 0) := by
      simpa [δ] using
        (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
    have htotal_finite : Measure.hausdorffMeasure (d : ℝ) s + 1 ≠ ∞ := by
      simp [hfinite]
    have hbound_lim : Tendsto
        (fun m ↦ (δ m : ℝ≥0∞) * (Measure.hausdorffMeasure (d : ℝ) s + 1))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hδ_lim (Or.inr htotal_finite)
    have hK_integral : (∫⁻ y, K y ∂(volume : Measure ℝ)) = 0 := by
      apply nonpos_iff_eq_zero.mp
      calc
        (∫⁻ y, K y ∂(volume : Measure ℝ)) ≤
            liminf (fun m ↦ ∫⁻ y, H m y ∂(volume : Measure ℝ)) atTop :=
          lintegral_liminf_le hH_meas
        _ ≤ liminf (fun m ↦
            (δ m : ℝ≥0∞) * (Measure.hausdorffMeasure (d : ℝ) s + 1)) atTop :=
          liminf_le_liminf (Eventually.of_forall hH_integral)
        _ = 0 := hbound_lim.liminf_eq
    have hK_zero : K =ᵐ[(volume : Measure ℝ)] 0 :=
      (lintegral_eq_zero_iff hK_meas).mp hK_integral
    filter_upwards [hK_zero] with y hy
    exact nonpos_iff_eq_zero.mp ((hraw_K y).trans_eq hy)
  · have hsempty : s = ∅ := not_nonempty_iff_eq_empty.mp hsne
    simp [hsempty]

/-- The critical set of a globally Lipschitz scalar map has codimension-one Hausdorff-null
intersection with almost every level. -/
private theorem ae_euclideanHausdorffMeasure_critical_fiber_eq_zero {d : ℕ} (hd : 0 < d)
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      Measure.euclideanHausdorffMeasure (d - 1)
        ({x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0} ∩ f ⁻¹' {y}) = 0 := by
  let crit : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0}
  have hcrit_meas : MeasurableSet crit :=
    (measurableSet_of_differentiableAt ℝ f).inter
      ((measurableSet_singleton 0).preimage (measurable_fderiv ℝ f))
  let s : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun k ↦
    crit ∩ closedBall 0 k
  have hs_meas (k : ℕ) : MeasurableSet (s k) :=
    hcrit_meas.inter measurableSet_closedBall
  let c : ℝ≥0∞ := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (Measure.hausdorffMeasure (d : ℝ))
  have hc : c ≠ 0 := by
    simpa [c] using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have hs_finite (k : ℕ) : Measure.hausdorffMeasure (d : ℝ) (s k) ≠ ∞ := by
    have hscaled : c * Measure.hausdorffMeasure (d : ℝ) (s k) < ∞ := by
      calc
        c * Measure.hausdorffMeasure (d : ℝ) (s k) =
            Measure.euclideanHausdorffMeasure d (s k) := by
          rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def]
          rfl
        _ = volume (s k) := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) k) :=
          measure_mono inter_subset_right
        _ < ∞ := measure_closedBall_lt_top
    intro htop
    rw [htop, ENNReal.mul_top hc] at hscaled
    exact (lt_irrefl ∞ hscaled)
  have hlocal (k : ℕ) : ∀ᵐ y ∂(volume : Measure ℝ),
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s k ∩ f ⁻¹' {y}) = 0 := by
    apply ae_hausdorffMeasure_critical_fiber_eq_zero_of_finite hd hf.continuous
      (hs_meas k) _ (hs_finite k)
    intro x hx
    exact hx.1
  have hall : ∀ᵐ y ∂(volume : Measure ℝ), ∀ k,
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s k ∩ f ⁻¹' {y}) = 0 :=
    ae_all_iff.2 hlocal
  have hcrit_union : crit = ⋃ k, s k := by
    exact (iUnion_inter_closedBall_nat crit 0).symm
  have hraw : ∀ᵐ y ∂(volume : Measure ℝ),
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (crit ∩ f ⁻¹' {y}) = 0 := by
    filter_upwards [hall] with y hy
    have hunion : crit ∩ f ⁻¹' {y} = ⋃ k, s k ∩ f ⁻¹' {y} := by
      rw [hcrit_union, iUnion_inter]
    rw [hunion]
    apply nonpos_iff_eq_zero.mp
    calc
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ))
          (⋃ k, s k ∩ f ⁻¹' {y}) ≤
          ∑' k, Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ))
            (s k ∩ f ⁻¹' {y}) := measure_iUnion_le _
      _ = 0 := by simp [hy]
  filter_upwards [hraw] with y hy
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hy, smul_zero]

/-- A volume-null set has Hausdorff-null intersections with almost every level of a global
Lipschitz scalar map.  This is the null-set half of the scalar Eilenberg inequality. -/
private theorem ae_hausdorffMeasure_fiber_eq_zero_of_volume_eq_zero {d : ℕ} (hd : 0 < d)
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f)
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : volume s = 0) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      Measure.euclideanHausdorffMeasure (d - 1) (s ∩ f ⁻¹' {y}) = 0 := by
  let c : ℝ≥0∞ := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (Measure.hausdorffMeasure (d : ℝ))
  have hc : c ≠ 0 := by
    simpa [c] using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have hs_raw : Measure.hausdorffMeasure (d : ℝ) s = 0 := by
    have hscaled : c * Measure.hausdorffMeasure (d : ℝ) s = 0 := by
      have h := hs
      rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume d,
        Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def] at h
      simpa [c] using h
    exact (mul_eq_zero.mp hscaled).resolve_left hc
  let r : ℕ → ℝ≥0∞ := fun k ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hr_pos (k : ℕ) : 0 < r k := by
    simp [r]
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    exact (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  have hcover (k : ℕ) :
      ∃ t : ℕ → Set (EuclideanSpace ℝ (Fin d)),
        s ⊆ ⋃ n, t n ∧ (∀ n, ediam (t n) ≤ r k) ∧
          (∑' n, ⨆ _h : (t n).Nonempty, ediam (t n) ^ (d : ℝ)) < r k :=
    exists_hausdorffMeasure_cover_tsum_lt hs_raw (hr_pos k) (hr_pos k)
  choose t ht_cover ht_diam ht_sum using hcover
  let u : ℕ → ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun k n ↦ closure (t k n)
  have ht_bounded (k n : ℕ) : Bornology.IsBounded (t k n) := by
    apply Metric.isBounded_iff_ediam_ne_top.2
    exact ne_top_of_le_ne_top (by simp [r]) (ht_diam k n)
  have hu_compact (k n : ℕ) : IsCompact (u k n) := by
    exact (ht_bounded k n).isCompact_closure
  have hu_diam (k n : ℕ) : ediam (u k n) = ediam (t k n) := by
    exact ediam_closure (t k n)
  have hu_cover (k : ℕ) : s ⊆ ⋃ n, u k n := by
    exact (ht_cover k).trans (iUnion_mono fun n ↦ subset_closure)
  have himage_meas (k n : ℕ) : MeasurableSet (f '' u k n) :=
    (hu_compact k n).image hf.continuous |>.measurableSet
  let F : ℕ → ℝ → ℝ≥0∞ := fun k y ↦
    ∑' n, (f '' u k n).indicator
      (fun _ ↦ ediam (u k n) ^ ((d - 1 : ℕ) : ℝ)) y
  have hF_meas (k : ℕ) : Measurable (F k) := by
    apply Measurable.tsum
    intro n
    exact measurable_const.indicator (himage_meas k n)
  have himage_volume (k n : ℕ) :
      volume (f '' u k n) ≤ (C : ℝ≥0∞) * ediam (u k n) := by
    calc
      volume (f '' u k n) ≤ ediam (f '' u k n) := Real.volume_le_diam _
      _ ≤ (C : ℝ≥0∞) * ediam (u k n) := by
        simpa using hf.ediam_image_le (u k n)
  have hF_integral (k : ℕ) :
      (∫⁻ y, F k y ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * r k := by
    rw [lintegral_tsum fun n ↦
      (measurable_const.indicator (himage_meas k n)).aemeasurable]
    calc
      (∑' n, ∫⁻ y, (f '' u k n).indicator
          (fun _ ↦ ediam (u k n) ^ ((d - 1 : ℕ) : ℝ)) y ∂volume) =
          ∑' n, ediam (u k n) ^ ((d - 1 : ℕ) : ℝ) * volume (f '' u k n) := by
        congr 1
        funext n
        rw [lintegral_indicator (himage_meas k n), setLIntegral_const]
      _ ≤ ∑' n, ediam (u k n) ^ ((d - 1 : ℕ) : ℝ) *
          ((C : ℝ≥0∞) * ediam (u k n)) := by
        exact ENNReal.tsum_le_tsum fun n ↦
          mul_le_mul_right (himage_volume k n) _
      _ = ∑' n, (C : ℝ≥0∞) *
          (⨆ _h : (t k n).Nonempty, ediam (t k n) ^ (d : ℝ)) := by
        congr 1
        funext n
        rw [hu_diam]
        by_cases hn : (t k n).Nonempty
        · simp only [hn, ciSup_pos]
          rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast]
          calc
            ediam (t k n) ^ (d - 1) * ((C : ℝ≥0∞) * ediam (t k n)) =
                (C : ℝ≥0∞) *
                  (ediam (t k n) ^ (d - 1) * ediam (t k n)) := by ac_rfl
            _ = (C : ℝ≥0∞) * ediam (t k n) ^ d := by
              rw [pow_sub_one_mul (Nat.ne_of_gt hd)]
        · have hempty : t k n = ∅ := not_nonempty_iff_eq_empty.mp hn
          simp [hempty]
      _ = (C : ℝ≥0∞) *
          ∑' n, ⨆ _h : (t k n).Nonempty, ediam (t k n) ^ (d : ℝ) :=
        ENNReal.tsum_mul_left
      _ ≤ (C : ℝ≥0∞) * r k :=
        mul_le_mul_right (ht_sum k).le _
  have hraw_fiber_le (y : ℝ) :
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) ≤
        liminf (fun k ↦ F k y) atTop := by
    let ι : ℕ → Type := fun k ↦
      {n : ℕ // (u k n ∩ f ⁻¹' {y}).Nonempty}
    let v : ∀ k, ι k → Set (EuclideanSpace ℝ (Fin d)) :=
      fun k n ↦ u k n.1 ∩ f ⁻¹' {y}
    have hv_diam (k : ℕ) (n : ι k) : ediam (v k n) ≤ r k := by
      calc
        ediam (v k n) ≤ ediam (u k n.1) := ediam_mono inter_subset_left
        _ = ediam (t k n.1) := hu_diam k n.1
        _ ≤ r k := ht_diam k n.1
    have hv_cover (k : ℕ) : s ∩ f ⁻¹' {y} ⊆ ⋃ n, v k n := by
      intro x hx
      rcases mem_iUnion.mp (hu_cover k hx.1) with ⟨n, hxn⟩
      let j : ι k := ⟨n, ⟨x, hxn, hx.2⟩⟩
      exact mem_iUnion.2 ⟨j, hxn, hx.2⟩
    have hcover_bound := Measure.hausdorffMeasure_le_liminf_tsum
      (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) r hr_lim v
      (Eventually.of_forall hv_diam) (Eventually.of_forall hv_cover)
    refine hcover_bound.trans (liminf_le_liminf (Eventually.of_forall fun k ↦ ?_))
    calc
      (∑' n : ι k, ediam (v k n) ^ (((d - 1 : ℕ) : ℝ))) ≤
          ∑' n : ι k, ediam (u k n.1) ^ (((d - 1 : ℕ) : ℝ)) := by
        exact ENNReal.tsum_le_tsum fun n ↦
          ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) (by positivity)
      _ ≤ ∑' n, (f '' u k n).indicator
          (fun _ ↦ ediam (u k n) ^ (((d - 1 : ℕ) : ℝ))) y := by
        apply ENNReal.summable.tsum_le_tsum_of_inj (fun n : ι k ↦ n.1)
          Subtype.coe_injective (fun _ _ ↦ zero_le)
        · intro n
          have hy : y ∈ f '' u k n.1 := by
            rcases n.2 with ⟨x, hx, hfx⟩
            exact ⟨x, hx, mem_singleton_iff.mp hfx⟩
          rw [indicator_of_mem hy]
        · exact ENNReal.summable
      _ = F k y := rfl
  have hCr_lim : Tendsto (fun k ↦ (C : ℝ≥0∞) * r k) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hr_lim (Or.inr (by simp : (C : ℝ≥0∞) ≠ ∞))
  have hliminf_integral :
      liminf (fun k ↦ ∫⁻ y, F k y ∂(volume : Measure ℝ)) atTop = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      liminf (fun k ↦ ∫⁻ y, F k y ∂(volume : Measure ℝ)) atTop ≤
          liminf (fun k ↦ (C : ℝ≥0∞) * r k) atTop :=
        liminf_le_liminf (Eventually.of_forall hF_integral)
      _ = 0 := hCr_lim.liminf_eq
  have hliminf_lintegral :
      (∫⁻ y, liminf (fun k ↦ F k y) atTop ∂(volume : Measure ℝ)) = 0 := by
    apply nonpos_iff_eq_zero.mp
    exact (lintegral_liminf_le hF_meas).trans_eq hliminf_integral
  have hliminf_zero :
      (fun y ↦ liminf (fun k ↦ F k y) atTop) =ᵐ[(volume : Measure ℝ)] 0 :=
    (lintegral_eq_zero_iff (Measurable.liminf hF_meas)).mp hliminf_lintegral
  have hraw_zero : ∀ᵐ y ∂(volume : Measure ℝ),
      Measure.hausdorffMeasure (((d - 1 : ℕ) : ℝ)) (s ∩ f ⁻¹' {y}) = 0 := by
    filter_upwards [hliminf_zero] with y hy
    exact nonpos_iff_eq_zero.mp ((hraw_fiber_le y).trans_eq hy)
  filter_upwards [hraw_zero] with y hy
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hy, smul_zero]

end LowerDimensionalArea

private theorem MeasurableEmbedding.apply_invFun_of_mem_range
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Nonempty α]
    {g : α → β} (hg : MeasurableEmbedding g) {y : β} (hy : y ∈ range g) :
    g (hg.invFun y) = y := by
  rw [MeasurableEmbedding.invFun, dif_pos hy]
  have h := congr_arg Subtype.val (hg.equivRange.apply_symm_apply ⟨y, hy⟩)
  simpa only [MeasurableEmbedding.equivRange_apply] using h

/-- On one bi-Lipschitz coordinate-chart piece, coordinate Tonelli and the graph area formula
identify the chart slice with the original weighted level fiber. -/
private theorem scalarCoordinatePiece_fiber_formula {n : ℕ} (i : Fin (n + 1))
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) (hw : Measurable w)
    {p : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hp : MeasurableSet p)
    (hpreg : p ⊆ scalarFirstRegularSet i f)
    (hpinj : InjOn (scalarCoordinateChart i f) p)
    {K : ℝ≥0}
    (hpanti : AntilipschitzWith K (p.restrict (scalarCoordinateChart i f)))
    (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) (_hv : Measurable v)
    (hv_apply : ∀ x ∈ p,
      v (scalarCoordinateChart i f x) = scalarCoordinateAreaWeight i f w x)
    (t : ℝ) :
    (∫⁻ x in p ∩ f ⁻¹' {t}, w x
        ∂(Measure.euclideanHausdorffMeasure n)) =
      ∫⁻ z : EuclideanSpace ℝ (Fin n),
        ((scalarCoordinateChart i f '' p).indicator v)
          (coordinateAffineInsertion i t z) ∂volume := by
  classical
  by_cases hpne : p.Nonempty
  · letI : Nonempty p := hpne.to_subtype
    have hchart_deriv : ∀ x ∈ p,
        HasFDerivWithinAt (scalarCoordinateChart i f)
          (scalarCoordinateDerivative i (fderiv ℝ f x)) p x := by
      intro x hx
      exact (HasFDerivAt.scalarCoordinateChart (hpreg hx).1.hasFDerivAt).hasFDerivWithinAt
    have hemb : MeasurableEmbedding (p.restrict (scalarCoordinateChart i f)) :=
      measurableEmbedding_of_fderivWithin hp hchart_deriv hpinj
    have himage : MeasurableSet (scalarCoordinateChart i f '' p) :=
      measurable_image_of_fderivWithin hp hchart_deriv hpinj
    let ψ : EuclideanSpace ℝ (Fin n) → p := fun z ↦
      hemb.invFun (coordinateAffineInsertion i t z)
    let φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
      fun z ↦ (ψ z).1
    let q : Set (EuclideanSpace ℝ (Fin n)) :=
      coordinateAffineInsertion i t ⁻¹' (scalarCoordinateChart i f '' p)
    have hq : MeasurableSet q :=
      himage.preimage (lipschitzWith_coordinateAffineInsertion i t).continuous.measurable
    have hright (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ q) :
        scalarCoordinateChart i f (φ z) = coordinateAffineInsertion i t z := by
      apply MeasurableEmbedding.apply_invFun_of_mem_range hemb
      rcases hz with ⟨x, hx, hxe⟩
      exact ⟨⟨x, hx⟩, hxe⟩
    have hproj_chart (x : EuclideanSpace ℝ (Fin (n + 1))) :
        coordinateProjection i (scalarCoordinateChart i f x) = coordinateProjection i x := by
      ext j
      simp
    have hproj (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ q) :
        coordinateProjection i (φ z) = z := by
      rw [← hproj_chart (φ z), hright z hz,
        coordinateProjection_coordinateAffineInsertion]
    have hφ_lip : LipschitzOnWith K φ q := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hanti := hpanti.le_mul_dist (ψ x) (ψ y)
      change dist (φ x) (φ y) ≤ (K : ℝ) * dist
        (scalarCoordinateChart i f (φ x)) (scalarCoordinateChart i f (φ y)) at hanti
      simpa only [hright x hx, hright y hy,
        coordinateAffineInsertion_dist] using hanti
    have hφ_inj : InjOn φ q := by
      intro x hx y hy hxy
      calc
        x = coordinateProjection i (φ x) := (hproj x hx).symm
        _ = coordinateProjection i (φ y) := congr_arg (coordinateProjection i) hxy
        _ = y := hproj y hy
    have hφ_proj : EqOn id (fun z ↦ coordinateProjection i (φ z)) q := by
      intro z hz
      exact (hproj z hz).symm
    have himageφ : φ '' q = p ∩ f ⁻¹' {t} := by
      apply Subset.antisymm
      · rintro x ⟨z, hz, rfl⟩
        refine ⟨(ψ z).property, ?_⟩
        change f (φ z) = t
        rw [← scalarCoordinateChart_apply_same i f (φ z), hright z hz,
          coordinateAffineInsertion_apply_same]
      · rintro x ⟨hxp, hxlevel⟩
        let z := coordinateProjection i x
        have hinsert : coordinateAffineInsertion i t z = scalarCoordinateChart i f x := by
          ext j
          induction j using i.succAboveCases with
          | x =>
              rw [coordinateAffineInsertion_apply_same,
                scalarCoordinateChart_apply_same]
              exact mem_singleton_iff.mp hxlevel.symm
          | p j =>
              rw [coordinateAffineInsertion_apply_succAbove,
                scalarCoordinateChart_apply_of_ne (i.succAbove_ne j)]
              rfl
        have hzq : z ∈ q := by
          change coordinateAffineInsertion i t z ∈ scalarCoordinateChart i f '' p
          exact hinsert.symm ▸ ⟨x, hxp, rfl⟩
        refine ⟨z, hzq, ?_⟩
        change (hemb.invFun (coordinateAffineInsertion i t z)).1 = x
        rw [hinsert]
        exact congr_arg Subtype.val (hemb.leftInverse_invFun ⟨x, hxp⟩)
    have hderiv : ∀ᵐ z ∂volume.restrict q,
        fderivWithin ℝ φ q z =
          coordinateGraphInverseDerivative i (fderiv ℝ f (φ z)) := by
      filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume q,
        hφ_lip.ae_differentiableWithinAt hq, ae_restrict_mem hq]
      intro z hzdensity hφdiff hzq
      have hxreg : φ z ∈ scalarFirstRegularSet i f := hpreg (ψ z).property
      have hchart := HasFDerivAt.scalarCoordinateChart (i := i) hxreg.1.hasFDerivAt
      have hcomp : HasFDerivWithinAt
          (fun y ↦ scalarCoordinateChart i f (φ y))
          ((scalarCoordinateDerivative i (fderiv ℝ f (φ z))).comp
            (fderivWithin ℝ φ q z)) q z :=
        hchart.comp_hasFDerivWithinAt z hφdiff.hasFDerivWithinAt
      have hcomp' : HasFDerivWithinAt (coordinateAffineInsertion i t)
          ((scalarCoordinateDerivative i (fderiv ℝ f (φ z))).comp
            (fderivWithin ℝ φ q z)) q z :=
        hcomp.congr' (fun y hy ↦ (hright y hy).symm) hzq
      have hlin :
          (scalarCoordinateDerivative i (fderiv ℝ f (φ z))).comp
              (fderivWithin ℝ φ q z) = coordinateInsertionLinear i :=
        HasFDerivWithinAt.eq_of_volume_density_one hzdensity hcomp'
          (hasFDerivAt_coordinateAffineInsertion i t z).hasFDerivWithinAt
      exact eq_coordinateGraphInverseDerivative_of_comp i (fderiv ℝ f (φ z))
        hxreg.2.1 (fderivWithin ℝ φ q z) hlin
    have harea :=
      lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_comp_eq_id
        hq hφ_lip hφ_inj (coordinateProjection i) hφ_proj w hw
    rw [himageφ] at harea
    have harea' :
        (∫⁻ x in p ∩ f ⁻¹' {t}, w x
            ∂(Measure.euclideanHausdorffMeasure n)) =
          ∫⁻ z in q,
            ENNReal.ofReal (fderivWithin ℝ φ q z).toLinearMap.normDet * w (φ z)
              ∂volume := by
      simpa only [finrank_euclideanSpace_fin] using harea
    rw [harea']
    rw [← lintegral_indicator hq]
    apply lintegral_congr_ae
    have hderiv_global : ∀ᵐ z ∂volume, z ∈ q →
        fderivWithin ℝ φ q z =
          coordinateGraphInverseDerivative i (fderiv ℝ f (φ z)) :=
      (ae_restrict_iff' hq).1 hderiv
    filter_upwards [hderiv_global] with z hzderiv
    by_cases hzq : z ∈ q
    · rw [indicator_of_mem hzq]
      specialize hzderiv hzq
      have hxreg : φ z ∈ scalarFirstRegularSet i f := hpreg (ψ z).property
      have hpartial : ENNReal.ofReal
          |fderiv ℝ f (φ z) (EuclideanSpace.single i 1)| ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]
        exact not_le.mpr (abs_pos.mpr hxreg.2.1)
      have hpartial_top : ENNReal.ofReal
          |fderiv ℝ f (φ z) (EuclideanSpace.single i 1)| ≠ ∞ := ENNReal.ofReal_ne_top
      have hzimage : coordinateAffineInsertion i t z ∈
          scalarCoordinateChart i f '' p := hzq
      rw [indicator_of_mem hzimage]
      apply (ENNReal.mul_right_inj hpartial hpartial_top).mp
      rw [hzderiv]
      have hgraph := coordinateGraphInverseDerivative_normDet_mul_abs i
        (fderiv ℝ f (φ z)) hxreg.2.1
      calc
        ENNReal.ofReal |fderiv ℝ f (φ z) (EuclideanSpace.single i 1)| *
            (ENNReal.ofReal
              (coordinateGraphInverseDerivative i (fderiv ℝ f (φ z))).toLinearMap.normDet *
                w (φ z)) =
            scalarJacobian f (φ z) * w (φ z) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hgraph]
          rfl
        _ = ENNReal.ofReal |fderiv ℝ f (φ z) (EuclideanSpace.single i 1)| *
            scalarCoordinateAreaWeight i f w (φ z) :=
          (ofReal_abs_partial_mul_scalarCoordinateAreaWeight i f w hxreg).symm
        _ = ENNReal.ofReal |fderiv ℝ f (φ z) (EuclideanSpace.single i 1)| *
            v (coordinateAffineInsertion i t z) := by
          rw [← hright z hzq, hv_apply (φ z) (ψ z).property]
    · rw [indicator_of_notMem hzq]
      have hznot : coordinateAffineInsertion i t z ∉ scalarCoordinateChart i f '' p := hzq
      rw [indicator_of_notMem hznot]
  · have hpempty : p = ∅ := not_nonempty_iff_eq_empty.mp hpne
    simp [hpempty]

private theorem scalarFirstRegular_coarea {n : ℕ} (i : Fin (n + 1))
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun t : ℝ ↦
      ∫⁻ x in scalarFirstRegularSet i f ∩ f ⁻¹' {t}, w x
        ∂(Measure.euclideanHausdorffMeasure n)) ∧
      (∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume) =
        ∫⁻ t : ℝ, ∫⁻ x in scalarFirstRegularSet i f ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n) ∂volume := by
  classical
  obtain ⟨u, v, hu_disj, hu_meas, hu_cover, hu_inj, hu_anti,
      hv_meas, hv_apply, harea⟩ :=
    exists_weighted_scalarCoordinate_area_partition i f
      (measurableSet_scalarFirstRegularSet i f) (fun x hx ↦ hx.1)
      (scalarCoordinateAreaWeight i f w) (measurable_scalarCoordinateAreaWeight i f hw)
  have hreg := scalarCoordinateRegularSet_firstRegular i f
  rw [hreg] at hu_cover hu_inj hu_anti hv_apply harea
  let p : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun k ↦
    scalarFirstRegularSet i f ∩ u k
  have hp_meas (k : ℕ) : MeasurableSet (p k) :=
    (measurableSet_scalarFirstRegularSet i f).inter (hu_meas k)
  have hp_sub (k : ℕ) : p k ⊆ scalarFirstRegularSet i f := inter_subset_left
  have himage_meas (k : ℕ) : MeasurableSet (scalarCoordinateChart i f '' p k) := by
    apply measurable_image_of_fderivWithin (hp_meas k)
      (fun x hx ↦
        (HasFDerivAt.scalarCoordinateChart (i := i) hx.1.1.hasFDerivAt).hasFDerivWithinAt)
    exact hu_inj k
  let H : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞ := fun y ↦
    ∑' k, (scalarCoordinateChart i f '' p k).indicator (v k) y
  have hH : Measurable H := by
    apply Measurable.tsum
    intro k
    exact (hv_meas k).indicator (himage_meas k)
  have hsource :
      (∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume) =
        ∫⁻ y, H y ∂volume := by
    calc
      (∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume) =
          ∫⁻ x in scalarFirstRegularSet i f,
            ENNReal.ofReal |fderiv ℝ f x (EuclideanSpace.single i 1)| *
              scalarCoordinateAreaWeight i f w x ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_scalarFirstRegularSet i f)] with x hx
        exact (ofReal_abs_partial_mul_scalarCoordinateAreaWeight i f w hx).symm
      _ = ∫⁻ y, H y ∂volume := harea
  let G : ℝ → ℝ≥0∞ := fun t ↦
    ∑' k, ∫⁻ z : EuclideanSpace ℝ (Fin n),
      (scalarCoordinateChart i f '' p k).indicator (v k)
        (coordinateAffineInsertion i t z) ∂volume
  have hG : Measurable G := by
    apply Measurable.tsum
    intro k
    apply Measurable.lintegral_prod_right
    have hjoint : Measurable (fun x : ℝ × EuclideanSpace ℝ (Fin n) ↦
        (scalarCoordinateChart i f '' p k).indicator (v k)
          (coordinateAffineInsertion i x.1 x.2)) := by
      have hcomp := ((hv_meas k).indicator (himage_meas k)).comp
        (coordinateProductMeasurableEquiv i).measurable
      have heq :
          (scalarCoordinateChart i f '' p k).indicator (v k) ∘
              (coordinateProductMeasurableEquiv i) =
            (fun x : ℝ × EuclideanSpace ℝ (Fin n) ↦
              (scalarCoordinateChart i f '' p k).indicator (v k)
                (coordinateAffineInsertion i x.1 x.2)) := by
        funext x
        rw [Function.comp_apply, coordinateProductMeasurableEquiv_apply]
      rw [← heq]
      exact hcomp
    exact hjoint
  have hfiber (t : ℝ) :
      (∫⁻ x in scalarFirstRegularSet i f ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n)) = G t := by
    have hpiece (k : ℕ) :
        (∫⁻ z : EuclideanSpace ℝ (Fin n),
            (scalarCoordinateChart i f '' p k).indicator (v k)
              (coordinateAffineInsertion i t z) ∂volume) =
          ∫⁻ x in p k ∩ f ⁻¹' {t}, w x
            ∂(Measure.euclideanHausdorffMeasure n) := by
      obtain ⟨Kk, hKk⟩ := hu_anti k
      exact (scalarCoordinatePiece_fiber_formula i f w hw (hp_meas k) (hp_sub k)
        (hu_inj k) hKk (v k) (hv_meas k) (hv_apply k) t).symm
    have hunion : scalarFirstRegularSet i f ∩ f ⁻¹' {t} =
        ⋃ k, p k ∩ f ⁻¹' {t} := by
      rw [hu_cover]
      simp only [p, iUnion_inter]
    rw [hunion]
    rw [lintegral_iUnion
      (fun k ↦ (hp_meas k).inter (measurableSet_lipschitz_fiber hf t))
      (pairwise_disjoint_mono hu_disj fun _ x hx ↦ hx.1.2) w]
    simp_rw [← hpiece]
    rfl
  constructor
  · have hfun : (fun t : ℝ ↦
        ∫⁻ x in scalarFirstRegularSet i f ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n)) = G := funext hfiber
    rw [hfun]
    exact hG
  · calc
      (∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume) =
          ∫⁻ y, H y ∂volume := hsource
      _ = ∫⁻ t : ℝ, ∫⁻ z : EuclideanSpace ℝ (Fin n),
          H (coordinateAffineInsertion i t z) ∂volume ∂volume :=
        lintegral_eq_lintegral_coordinateSections i H hH
      _ = ∫⁻ t : ℝ, G t ∂volume := by
        apply lintegral_congr
        intro t
        rw [lintegral_tsum]
        intro k
        exact ((hv_meas k).indicator (himage_meas k) |>.comp
          (lipschitzWith_coordinateAffineInsertion i t).continuous.measurable).aemeasurable
      _ = ∫⁻ t : ℝ, ∫⁻ x in scalarFirstRegularSet i f ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n) ∂volume := by
        apply lintegral_congr
        intro t
        exact (hfiber t).symm

private theorem scalarRegular_coarea {n : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun t : ℝ ↦
      ∫⁻ x in {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0} ∩ f ⁻¹' {t}, w x
        ∂(Measure.euclideanHausdorffMeasure n)) ∧
      (∫⁻ x, scalarJacobian f x * w x ∂volume) =
        ∫⁻ t : ℝ,
          ∫⁻ x in {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0} ∩ f ⁻¹' {t}, w x
            ∂(Measure.euclideanHausdorffMeasure n) ∂volume := by
  classical
  let F : Fin (n + 1) → ℝ → ℝ≥0∞ := fun i t ↦
    ∫⁻ x in scalarFirstRegularSet i f ∩ f ⁻¹' {t}, w x
      ∂(Measure.euclideanHausdorffMeasure n)
  have hcoord (i : Fin (n + 1)) := scalarFirstRegular_coarea i hf w hw
  have hF (i : Fin (n + 1)) : Measurable (F i) := (hcoord i).1
  have hprofile (t : ℝ) :
      (∫⁻ x in {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0} ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n)) =
        ∑' i : Fin (n + 1), F i t := by
    rw [← iUnion_scalarFirstRegularSet f]
    rw [iUnion_inter]
    exact lintegral_iUnion
      (fun i ↦ (measurableSet_scalarFirstRegularSet i f).inter
        (measurableSet_lipschitz_fiber hf t))
      (pairwise_disjoint_mono (pairwise_disjoint_scalarFirstRegularSet f)
        fun _ x hx ↦ hx.1) w
  constructor
  · have hsum : Measurable (fun t ↦ ∑' i : Fin (n + 1), F i t) :=
      Measurable.tsum hF
    have heq : (fun t : ℝ ↦
        ∫⁻ x in {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0} ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n)) =
        fun t ↦ ∑' i : Fin (n + 1), F i t := funext hprofile
    rw [heq]
    exact hsum
  · calc
      (∫⁻ x, scalarJacobian f x * w x ∂volume) =
          ∑' i : Fin (n + 1),
            ∫⁻ x in scalarFirstRegularSet i f, scalarJacobian f x * w x ∂volume :=
        lintegral_scalarJacobian_eq_tsum_firstRegular f w
      _ = ∑' i : Fin (n + 1), ∫⁻ t : ℝ, F i t ∂volume := by
        congr 1
        funext i
        exact (hcoord i).2
      _ = ∫⁻ t : ℝ, ∑' i : Fin (n + 1), F i t ∂volume := by
        symm
        exact lintegral_tsum fun i ↦ (hF i).aemeasurable
      _ = ∫⁻ t : ℝ,
          ∫⁻ x in {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0} ∩ f ⁻¹' {t}, w x
            ∂(Measure.euclideanHausdorffMeasure n) ∂volume := by
        apply lintegral_congr
        intro t
        exact (hprofile t).symm

/-- The scalar coarea formula in positive dimension, obtained by combining the regular graph
formula with the Eilenberg critical-set theorem and Rademacher's null exceptional set. -/
private theorem LipschitzWith.scalarCoareaFormula_succ {n : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : LipschitzWith C f) :
    ScalarCoareaFormula f := by
  intro w hw
  let regular : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x ≠ 0}
  let critical : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0}
  let nondiff : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | ¬DifferentiableAt ℝ f x}
  have hnondiff_volume : volume nondiff = 0 := by
    simpa [nondiff, ae_iff] using hf.ae_differentiableAt
  have hcritical : ∀ᵐ t ∂(volume : Measure ℝ),
      Measure.euclideanHausdorffMeasure n (critical ∩ f ⁻¹' {t}) = 0 := by
    simpa [critical] using
      (ae_euclideanHausdorffMeasure_critical_fiber_eq_zero (Nat.succ_pos n) hf)
  have hnondiff : ∀ᵐ t ∂(volume : Measure ℝ),
      Measure.euclideanHausdorffMeasure n (nondiff ∩ f ⁻¹' {t}) = 0 := by
    simpa [nondiff] using
      (ae_hausdorffMeasure_fiber_eq_zero_of_volume_eq_zero (Nat.succ_pos n) hf
        hnondiff_volume)
  have hprofile : ∀ᵐ t ∂(volume : Measure ℝ),
      scalarCoareaFiber f w t =
        ∫⁻ x in regular ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n) := by
    filter_upwards [hcritical, hnondiff] with t htcritical htnondiff
    let μ : Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
      Measure.euclideanHausdorffMeasure n
    have hbad : μ ((critical ∩ f ⁻¹' {t}) ∪ (nondiff ∩ f ⁻¹' {t})) = 0 :=
      measure_union_null htcritical htnondiff
    have hdiff_sub : f ⁻¹' {t} \ (regular ∩ f ⁻¹' {t}) ⊆
        (critical ∩ f ⁻¹' {t}) ∪ (nondiff ∩ f ⁻¹' {t}) := by
      rintro x ⟨hxfiber, hxnot⟩
      by_cases hxdiff : DifferentiableAt ℝ f x
      · have hxzero : fderiv ℝ f x = 0 := by
          by_contra hxne
          exact hxnot ⟨⟨hxdiff, hxne⟩, hxfiber⟩
        exact Or.inl ⟨⟨hxdiff, hxzero⟩, hxfiber⟩
      · exact Or.inr ⟨hxdiff, hxfiber⟩
    have hsets : f ⁻¹' {t} =ᵐ[μ]
        ((regular ∩ f ⁻¹' {t}) : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
      apply ae_eq_set.2
      constructor
      · exact measure_mono_null hdiff_sub hbad
      · apply measure_mono_null _ measure_empty
        intro x hx
        exact (hx.2 hx.1.2).elim
    change (∫⁻ x, w x ∂μ.restrict (f ⁻¹' {t})) =
      ∫⁻ x, w x ∂μ.restrict (regular ∩ f ⁻¹' {t})
    rw [Measure.restrict_congr_set hsets]
  have hregular := scalarRegular_coarea hf w hw
  calc
    (∫⁻ x, scalarJacobian f x * w x ∂volume) =
        ∫⁻ t : ℝ, ∫⁻ x in regular ∩ f ⁻¹' {t}, w x
          ∂(Measure.euclideanHausdorffMeasure n) ∂volume := by
      simpa [regular] using hregular.2
    _ = ∫⁻ t : ℝ, scalarCoareaFiber f w t :=
      lintegral_congr_ae (hprofile.mono fun _ ht ↦ ht.symm)

/-- Every globally Lipschitz scalar map on a finite-dimensional Euclidean space satisfies
Federer's weighted scalar coarea formula. -/
theorem LipschitzWith.scalarCoareaFormula {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f) :
    ScalarCoareaFormula f := by
  cases d with
  | zero =>
      intro w _hw
      have hderiv (x : EuclideanSpace ℝ (Fin 0)) : fderiv ℝ f x = 0 :=
        Subsingleton.elim _ _
      have hleft : (∫⁻ x, scalarJacobian f x * w x ∂volume) = 0 := by
        simp [scalarJacobian, hderiv]
      have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ f 0 := by
        simp [ae_iff]
      have hright : (∫⁻ t : ℝ, scalarCoareaFiber f w t) = 0 := by
        calc
          (∫⁻ t : ℝ, scalarCoareaFiber f w t) = ∫⁻ _t : ℝ, 0 := by
            apply lintegral_congr_ae
            filter_upwards [hne] with t ht
            have hfiber : f ⁻¹' {t} = ∅ := by
              ext x
              constructor
              · intro hx
                have hx0 : x = 0 := Subsingleton.elim _ _
                exact (ht (by simpa [hx0] using (mem_singleton_iff.mp hx).symm)).elim
              · simp
            simp [scalarCoareaFiber, hfiber]
          _ = 0 := by simp
      exact hleft.trans hright.symm
  | succ n =>
      exact LipschitzWith.scalarCoareaFormula_succ hf

/-- Restricting a scalar-Jacobian integral to a measurable set is the same as inserting the
set's indicator into the weight. -/
theorem setLIntegral_scalarJacobian_mul_eq_lintegral_indicator {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : MeasurableSet s) :
    ∫⁻ x in s, scalarJacobian f x * w x ∂volume =
      ∫⁻ x, scalarJacobian f x * s.indicator w x ∂volume := by
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

/-- On a measurable set where the derivative has norm one almost everywhere, the scalar
Jacobian can be removed from every nonnegative measurable weight. -/
theorem setLIntegral_scalarJacobian_mul_eq_of_ae_norm_fderiv_eq_one {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hjac : ∀ᵐ x ∂(volume.restrict s), ‖fderiv ℝ f x‖ = 1) :
    ∫⁻ x in s, scalarJacobian f x * w x ∂volume = ∫⁻ x in s, w x ∂volume := by
  apply lintegral_congr_ae
  filter_upwards [hjac] with x hx
  simp [scalarJacobian, hx]

/-- Global version of Jacobian elimination. -/
theorem lintegral_scalarJacobian_mul_eq_of_ae_norm_fderiv_eq_one {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hjac : ∀ᵐ x ∂volume, ‖fderiv ℝ f x‖ = 1) :
    ∫⁻ x, scalarJacobian f x * w x ∂volume = ∫⁻ x, w x ∂volume := by
  apply lintegral_congr_ae
  filter_upwards [hjac] with x hx
  simp [scalarJacobian, hx]

/-- A global almost-everywhere unit-Jacobian identity remains valid after restricting to a
measurable set. -/
theorem setLIntegral_scalarJacobian_mul_eq_of_ae_norm_fderiv_eq_one_global {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) {s : Set (EuclideanSpace ℝ (Fin d))}
    (hjac : ∀ᵐ x ∂volume, ‖fderiv ℝ f x‖ = 1) :
    ∫⁻ x in s, scalarJacobian f x * w x ∂volume = ∫⁻ x in s, w x ∂volume := by
  exact setLIntegral_scalarJacobian_mul_eq_of_ae_norm_fderiv_eq_one f w
    (ae_restrict_of_ae hjac)

/-- Unit scalar Jacobian eliminates the derivative factor on every Lipschitz slab. -/
theorem setLIntegral_scalarJacobian_mul_lipschitz_slab_eq {d : ℕ}
    {C : ℝ≥0} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (a b : ℝ)
    (hjac : ∀ᵐ x ∂volume, ‖fderiv ℝ f x‖ = 1) :
    ∫⁻ x in f ⁻¹' Ioc a b, scalarJacobian f x * w x ∂volume =
      ∫⁻ x in f ⁻¹' Ioc a b, w x ∂volume := by
  apply setLIntegral_scalarJacobian_mul_eq_of_ae_norm_fderiv_eq_one f w
  rw [ae_restrict_iff' (measurableSet_lipschitz_slab hf a b)]
  filter_upwards [hjac] with x hx
  exact fun _ ↦ hx

/-- Federer's weighted scalar coarea identity implies its exact half-open slab form. -/
theorem ScalarCoareaFormula.setLIntegral_slab {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hcoarea : ScalarCoareaFormula f)
    (hf : LipschitzWith C f) (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hw : Measurable w) (a b : ℝ) :
    ∫⁻ x in f ⁻¹' Ioc a b, scalarJacobian f x * w x ∂volume =
      ∫⁻ t in Ioc a b, scalarCoareaFiber f w t := by
  rw [setLIntegral_scalarJacobian_mul_eq_lintegral_indicator f w
    (measurableSet_lipschitz_slab hf a b)]
  rw [hcoarea ((f ⁻¹' Ioc a b).indicator w)
    (hw.indicator (measurableSet_lipschitz_slab hf a b))]
  exact lintegral_scalarCoareaFiber_indicator_lipschitz_slab f hf w a b

/-- For a Lipschitz scalar map with almost-everywhere unit derivative norm, scalar coarea reduces
on a slab to unweighted volume disintegration over its level fibers. -/
theorem ScalarCoareaFormula.setLIntegral_slab_of_ae_norm_fderiv_eq_one {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hcoarea : ScalarCoareaFormula f)
    (hf : LipschitzWith C f) (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hw : Measurable w) (a b : ℝ)
    (hjac : ∀ᵐ x ∂volume, ‖fderiv ℝ f x‖ = 1) :
    ∫⁻ x in f ⁻¹' Ioc a b, w x ∂volume =
      ∫⁻ t in Ioc a b, scalarCoareaFiber f w t := by
  rw [← setLIntegral_scalarJacobian_mul_lipschitz_slab_eq f hf w a b hjac]
  exact hcoarea.setLIntegral_slab hf w hw a b

/-- Direct weighted slab form of scalar coarea for a globally Lipschitz map. -/
theorem LipschitzWith.scalarCoarea_setLIntegral_slab {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) (a b : ℝ) :
    ∫⁻ x in f ⁻¹' Ioc a b, scalarJacobian f x * w x ∂volume =
      ∫⁻ t in Ioc a b, scalarCoareaFiber f w t := by
  exact (LipschitzWith.scalarCoareaFormula hf).setLIntegral_slab hf w hw a b

/-- Direct unit-gradient slab disintegration for a globally Lipschitz scalar map. -/
theorem LipschitzWith.setLIntegral_slab_of_ae_norm_fderiv_eq_one {d : ℕ}
    {C : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LipschitzWith C f)
    (w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hw : Measurable w) (a b : ℝ)
    (hjac : ∀ᵐ x ∂volume, ‖fderiv ℝ f x‖ = 1) :
    ∫⁻ x in f ⁻¹' Ioc a b, w x ∂volume =
      ∫⁻ t in Ioc a b, scalarCoareaFiber f w t := by
  exact (LipschitzWith.scalarCoareaFormula hf).setLIntegral_slab_of_ae_norm_fderiv_eq_one
    hf w hw a b hjac

end ProbabilityTheory

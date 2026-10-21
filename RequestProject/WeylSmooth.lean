module

public import RequestProject.WeylMean
public import RequestProject.TestFunctions

/-!
# Weyl's lemma

* `exists_smooth_extension` — a function smooth on an open set `U` agrees near a compact
  `K ⊆ U` with a test function supported in `U`;
* `integral_mul_laplacian_local` — `∫ f Δφ = ∫ Δf φ` for `f` smooth on `U` and a test
  function `φ` supported in `U`;
* `weyl` — **Weyl's lemma**: a weakly harmonic function agrees almost everywhere on `U` with a
  function that is smooth and harmonic on `U`;
* `harmonic_mean_value` — smooth harmonic functions satisfy the mean value property for the
  radial mollifiers `kern n t`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {n : ℕ}

/-! ### Local smooth extensions and integration by parts -/

lemma exists_smooth_extension {U K : Set (RN n)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : RN n → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    ∃ F : RN n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧
      tsupport F ⊆ U ∧ ∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, F x = f x := by
  obtain ⟨χ, hχ, hχc, hχU, V, hVo, hKV, hχ1⟩ := exists_cutoff hK hU hKU
  set F : RN n → ℝ := fun x => χ x * f x with hFdef
  refine ⟨F, ?_, hχc.mul_right, ?_, V ∩ U, hVo.inter hU, subset_inter hKV hKU,
    fun x hx => by simp [hFdef, hχ1 x hx.1]⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxs : x ∉ tsupport χ := fun h => hx (hχU h)
      have hev : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with z hz
        simp [hFdef, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (tsupport_mul_subset_left (f := χ) (g := f)).trans hχU

lemma laplacian_eq_of_eqOn_open {V : Set (RN n)} (hV : IsOpen V) {F f : RN n → ℝ}
    (h : ∀ x ∈ V, F x = f x) {x : RN n} (hx : x ∈ V) :
    Laplacian.laplacian F x = Laplacian.laplacian f x := by
  have hev : F =ᶠ[𝓝 x] f := by
    filter_upwards [hV.mem_nhds hx] with z hz
    exact h z hz
  exact (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds

/-- The Laplacian of a function smooth on an open set is continuous there. -/
lemma continuousOn_laplacian {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    ContinuousOn (Laplacian.laplacian f) U := by
  intro x hx
  obtain ⟨F, hF, -, -, V, hVo, hxV, hFV⟩ :=
    exists_smooth_extension hU isCompact_singleton (singleton_subset_iff.mpr hx) hf
  have hxV' : x ∈ V := hxV rfl
  have hev : Laplacian.laplacian F =ᶠ[𝓝 x] Laplacian.laplacian f := by
    filter_upwards [hVo.mem_nhds hxV'] with z hz
    exact laplacian_eq_of_eqOn_open hVo hFV hz
  exact ((contDiff_laplacian hF).continuous.continuousAt.congr hev).continuousWithinAt

/-- Integration by parts `∫ f Δφ = ∫ Δf φ` for `f` smooth on `U` and a test function `φ`
supported in `U`. -/
lemma integral_mul_laplacian_local {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) {φ : RN n → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ x, f x * Laplacian.laplacian φ x = ∫ x, Laplacian.laplacian f x * φ x := by
  obtain ⟨F, hF, hFc, -, V, hVo, hKV, hFV⟩ := exists_smooth_extension hU hφc hφU hf
  have e1 : ∫ x, f x * Laplacian.laplacian φ x = ∫ x, F x * Laplacian.laplacian φ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp [hFV x (hKV hx)]
    · simp [laplacian_eq_zero_of_notMem_tsupport hx]
  have e2 : ∫ x, Laplacian.laplacian f x * φ x = ∫ x, Laplacian.laplacian F x * φ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp [laplacian_eq_of_eqOn_open hVo hFV (hKV hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [e1, e2, integral_laplacian_mul_comm hF hFc hφ hφc]

/-- Smooth harmonic functions are weakly harmonic. -/
lemma weakHarmonic_of_harmonic {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hΔ : ∀ x ∈ U, Laplacian.laplacian f x = 0) : WeakHarmonic U f := by
  refine ⟨hf.continuousOn.locallyIntegrableOn hU.measurableSet, fun φ hφ hφc hφU => ?_⟩
  rw [integral_mul_laplacian_local hU hf hφ hφc hφU]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport φ
  · simp [hΔ x (hφU hx)]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- A smooth weakly harmonic function is harmonic. -/
lemma harmonic_of_weakHarmonic {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (hw : WeakHarmonic U f) :
    ∀ x ∈ U, Laplacian.laplacian f x = 0 := by
  have hc := continuousOn_laplacian hU hf
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hc.locallyIntegrableOn hU.measurableSet) (fun φ hφ hφc hφU => by
      simp_rw [smul_eq_mul, mul_comm (φ _)]
      rw [← integral_mul_laplacian_local hU hf hφ hφc hφU]
      exact hw.2 φ hφ hφc hφU)
  have heq : EqOn (Laplacian.laplacian f) (fun _ => (0 : ℝ)) U := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU hc continuousOn_const
    rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
    exact hae
  exact fun x hx => heq hx

/-! ### Localisation of the weighted means -/

lemma meanK_indicator {w : RN n → ℝ} {x x0 : RN n} {t r : ℝ} (ht : 0 < t)
    (hsub : closedBall x t ⊆ closedBall x0 r) :
    meanK n t ((closedBall x0 r).indicator w) x = meanK n t w x := by
  rw [meanK_eq, meanK_eq]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hk : kern n t (x - y) = 0
  · simp [hk]
  · have h := support_kern ht hk
    rw [mem_ball, dist_zero_right] at h
    have hy : y ∈ closedBall x0 r := hsub (by
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]; exact h.le)
    simp [indicator_of_mem hy]

lemma locallyIntegrable_indicator {U : Set (RN n)} {w : RN n → ℝ} (hw : LocallyIntegrableOn w U)
    {x0 : RN n} {r : ℝ} (hsub : closedBall x0 r ⊆ U) :
    LocallyIntegrable ((closedBall x0 r).indicator w) := by
  refine Integrable.locallyIntegrable ?_
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact hw.integrableOn_compact_subset hsub (isCompact_closedBall x0 r)

lemma ae_of_local_n {U : Set (RN n)} {P : RN n → Prop}
    (h : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∀ᵐ z, z ∈ V → P z) : ∀ᵐ z, z ∈ U → P z := by
  classical
  choose! V hV hP using h
  set W : U → Set (RN n) := fun x => interior (V x)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W (fun _ => isOpen_interior)
  have hcover : U ⊆ ⋃ i ∈ T, W i := by
    intro x hx
    rw [hTU]
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hV x hx)⟩
  have hloc : ∀ i ∈ T, ∀ᵐ z, z ∈ W i → P z := fun i _ =>
    (hP i i.2).mono fun z hz hzW => hz (interior_subset hzW)
  have hall := (ae_ball_iff hTc).mpr hloc
  filter_upwards [hall] with z hz hzU
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hcover hzU)
  exact hz i hi hzi

/-- Lebesgue differentiation for functions locally integrable on an open set. -/
lemma ae_tendsto_meanK_on {U : Set (RN n)} (hU : IsOpen U) {w : RN n → ℝ}
    (hw : LocallyIntegrableOn w U) :
    ∀ᵐ x, x ∈ U → Tendsto (fun t => meanK n t w x) (𝓝[>] 0) (𝓝 (w x)) := by
  refine ae_of_local_n fun x0 hx0 => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x0 hx0
  have hsub : closedBall x0 (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hεU
  refine ⟨ball x0 (ε / 4), ball_mem_nhds x0 (by linarith), ?_⟩
  filter_upwards [ae_tendsto_meanK (n := n) (locallyIntegrable_indicator hw hsub)] with x hx hxB
  have hxB' : x ∈ closedBall x0 (ε / 2) :=
    ball_subset_closedBall (ball_subset_ball (by linarith) hxB)
  rw [indicator_of_mem hxB'] at hx
  refine hx.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 4 by linarith)] with t ht
  refine meanK_indicator ht.1 fun y hy => ?_
  rw [mem_closedBall] at hy ⊢
  rw [mem_ball] at hxB
  linarith [dist_triangle y x x0, ht.2]

/-! ### Weyl's lemma -/

/-- The limit of the weighted means (the canonical representative). -/
def weylRep (n : ℕ) (w : RN n → ℝ) (x : RN n) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t => meanK n t w x)

lemma weylRep_eq (hn : 1 ≤ n) {U : Set (RN n)} {w : RN n → ℝ} (hw : WeakHarmonic U w)
    {x : RN n} {R : ℝ} (hR : 0 < R) (hxU : closedBall x R ⊆ U) :
    weylRep n w x = meanK n R w x := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioc_mem_nhdsGT hR] with t ht
  exact (meanK_const hn hw ht.1 ht.2 hxU).symm

/-- **Weyl's lemma.** A weakly harmonic function on an open set `U` agrees almost everywhere on
`U` with a function that is smooth and harmonic on `U`. -/
theorem weyl (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U) {w : RN n → ℝ}
    (hw : WeakHarmonic U w) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weylRep n w) U ∧
      (∀ x ∈ U, Laplacian.laplacian (weylRep n w) x = 0) ∧
      ∀ᵐ x, x ∈ U → w x = weylRep n w x := by
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weylRep n w) U := by
    intro x0 hx0
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x0 hx0
    set r := ε / 3
    have hr : 0 < r := by positivity
    have hsub : closedBall x0 (2 * r) ⊆ U :=
      (closedBall_subset_ball (by simp only [r]; linarith)).trans hεU
    have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (meanK n r ((closedBall x0 (2 * r)).indicator w)) :=
      (hasCompactSupport_kern hr).contDiff_convolution_left _ (contDiff_kern r)
        (locallyIntegrable_indicator hw.1 hsub)
    have hev : meanK n r ((closedBall x0 (2 * r)).indicator w) =ᶠ[𝓝 x0] weylRep n w := by
      filter_upwards [ball_mem_nhds x0 hr] with x hx
      have hs : closedBall x r ⊆ closedBall x0 (2 * r) := by
        intro y hy
        rw [mem_closedBall] at hy ⊢
        rw [mem_ball] at hx
        linarith [dist_triangle y x x0]
      rw [meanK_indicator hr hs, weylRep_eq hn hw hr (hs.trans hsub)]
    exact (hG.contDiffAt.congr_of_eventuallyEq hev.symm).contDiffWithinAt
  have hae : ∀ᵐ x, x ∈ U → w x = weylRep n w x := by
    filter_upwards [ae_tendsto_meanK_on hU hw.1] with x hx hxU
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hxU
    have hsub : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
    refine tendsto_nhds_unique (hx hxU) (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < ε / 2 by linarith)] with t ht
    rw [weylRep_eq hn hw ht.1 ((closedBall_subset_closedBall ht.2).trans hsub)]
  refine ⟨hsm, harmonic_of_weakHarmonic hU hsm ⟨hsm.continuousOn.locallyIntegrableOn
    hU.measurableSet, fun φ hφ hφc hφU => ?_⟩, hae⟩
  rw [← hw.2 φ hφ hφc hφU]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  by_cases hxs : x ∈ tsupport φ
  · rw [hx (hφU hxs)]
  · simp [laplacian_eq_zero_of_notMem_tsupport hxs]

/-- **Mean value property** of smooth harmonic functions for the radial mollifiers. -/
theorem harmonic_mean_value (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hΔ : ∀ x ∈ U, Laplacian.laplacian f x = 0) {x : RN n} {t : ℝ} (ht : 0 < t)
    (hxU : closedBall x t ⊆ U) : f x = meanK n t f x := by
  have hw := weakHarmonic_of_harmonic hU hf hΔ
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x t).exists_thickening_subset_open hU hxU
  set t' := t + δ / 2
  have hsub' : closedBall x t' ⊆ U := by
    refine subset_trans (fun y hy => ?_) hδU
    rw [mem_thickening_iff]
    refine ⟨x + (t / (t + δ / 2)) • (y - x), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      rw [mem_closedBall, dist_eq_norm] at hy
      calc t / (t + δ / 2) * ‖y - x‖ ≤ t / (t + δ / 2) * t' := by gcongr
        _ = t := by simp only [t']; field_simp
    · rw [mem_closedBall, dist_eq_norm] at hy
      rw [dist_eq_norm]
      have : y - (x + (t / (t + δ / 2)) • (y - x)) = (1 - t / (t + δ / 2)) • (y - x) := by
        rw [sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      · have h1 : 1 - t / (t + δ / 2) = (δ / 2) / (t + δ / 2) := by field_simp; ring
        rw [h1]
        calc δ / 2 / (t + δ / 2) * ‖y - x‖ ≤ δ / 2 / (t + δ / 2) * t' := by gcongr
          _ = δ / 2 := by simp only [t']; field_simp
          _ < δ := by linarith
      · rw [sub_nonneg, div_le_one (by positivity)]; linarith
  set B := ball x (δ / 2)
  have hBo : IsOpen B := isOpen_ball
  have hBsub : ∀ x' ∈ B, closedBall x' t ⊆ closedBall x t' := by
    intro x' hx' y hy
    rw [mem_closedBall] at hy ⊢
    rw [mem_ball] at hx'
    simp only [t']
    linarith [dist_triangle y x' x]
  have hG : Continuous (meanK n t ((closedBall x t').indicator f)) :=
    (hasCompactSupport_kern ht).continuous_convolution_left _ (contDiff_kern t).continuous
      (locallyIntegrable_indicator hw.1 hsub')
  have hae : f =ᵐ[volume.restrict B] meanK n t ((closedBall x t').indicator f) := by
    rw [EventuallyEq, ae_restrict_iff' hBo.measurableSet]
    filter_upwards [ae_tendsto_meanK_on hU hw.1] with x' hx' hx'B
    have hx'U : x' ∈ U := hsub' (hBsub x' hx'B (mem_closedBall_self ht.le))
    rw [meanK_indicator ht (hBsub x' hx'B)]
    refine tendsto_nhds_unique (hx' hx'U) (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioc_mem_nhdsGT ht] with s hs
    exact (meanK_const hn hw hs.1 hs.2 ((hBsub x' hx'B).trans hsub')).symm
  have heq := Measure.eqOn_open_of_ae_eq hae hBo
    (hf.continuousOn.mono fun y hy => hsub' (hBsub y hy (mem_closedBall_self ht.le)))
    hG.continuousOn
  have := heq (mem_ball_self (by linarith : 0 < δ / 2))
  rw [this, meanK_indicator ht (hBsub x (mem_ball_self (by linarith)))]

end FourthRatio

end

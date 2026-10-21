module

public import RequestProject.SpectralH

/-!
# Rellich's theorem: compactness of `H_D ↪ L²(D)` for bounded `D`

Proof by mollification and the Arzelà–Ascoli theorem, for test functions first:

* translation estimate `‖φ(· + z) - φ‖² ≤ 3 |z|² ‖∇φ‖²`;
* mollification `ψ = ρ_δ * φ` satisfies `‖ψ - φ‖² ≤ 3 δ² ‖∇φ‖²`;
* for fixed `δ` the mollified functions of a bounded family are uniformly bounded, uniformly
  Lipschitz and supported in a fixed ball, hence totally bounded in `L²` by Arzelà–Ascoli;
* hence a bounded set of test functions (in the `H¹` norm, supported in a fixed ball) is totally
  bounded in `L²`, and by density the same holds in `H_D`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Elementary integral inequalities -/

/-- Jensen's inequality for a probability density `w`. -/
lemma sq_integral_le_weighted {α : Type*} [MeasurableSpace α] {μ : Measure α} {w h : α → ℝ}
    (hw : 0 ≤ w) (hw1 : ∫ x, w x ∂μ = 1) (hwi : Integrable w μ)
    (hwh : Integrable (fun x => w x * h x) μ) (hwh2 : Integrable (fun x => w x * h x ^ 2) μ) :
    (∫ x, w x * h x ∂μ) ^ 2 ≤ ∫ x, w x * h x ^ 2 ∂μ := by
  set m := ∫ x, w x * h x ∂μ
  have h0 : 0 ≤ ∫ x, w x * (h x - m) ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _)
  have hexp : ∫ x, w x * (h x - m) ^ 2 ∂μ = ∫ x, w x * h x ^ 2 ∂μ - 2 * m * m + m ^ 2 * 1 := by
    have : (fun x => w x * (h x - m) ^ 2) =
        fun x => (w x * h x ^ 2 - (2 * m) * (w x * h x)) + m ^ 2 * w x := by
      ext x; ring
    have i1 : Integrable (fun x => w x * h x ^ 2 - 2 * m * (w x * h x)) μ :=
      hwh2.sub (hwh.const_mul _)
    have i2 : Integrable (fun x => 2 * m * (w x * h x)) μ := hwh.const_mul _
    have i3 : Integrable (fun x => m ^ 2 * w x) μ := hwi.const_mul _
    rw [this, integral_add i1 i3, integral_sub hwh2 i2, integral_const_mul, integral_const_mul, hw1]
  nlinarith

lemma sq_fderiv_le_norm_gradient_sq (φ : RN N → ℝ) (y z : RN N) :
    (fderiv ℝ φ y z) ^ 2 ≤ ‖gradient φ y‖ ^ 2 * ‖z‖ ^ 2 := by
  have hdx : fderiv ℝ φ y z = ⟪gradient φ y, z⟫ := by
    simp only [gradient, InnerProductSpace.toDual_symm_apply]
  rw [hdx, ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2

/-! ### Translation estimate -/

lemma sub_eq_integral_fderiv {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x z : RN N) : φ (x + z) - φ x = ∫ t in (0 : ℝ)..1, fderiv ℝ φ (x + t • z) z := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (x + t • z)) (fderiv ℝ φ (x + t • z) z) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add x
    exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => fderiv ℝ φ (x + t • z) z :=
    ((hφ.continuous_fderiv (by simp)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)]
  simp

lemma sq_sub_le_integral {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x z : RN N) :
    (φ (x + z) - φ x) ^ 2 ≤ ‖z‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖gradient φ (x + t • z)‖ ^ 2 := by
  have hcont : Continuous fun t : ℝ => fderiv ℝ φ (x + t • z) z :=
    ((hφ.continuous_fderiv (by simp)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hgc : Continuous fun t : ℝ => ‖gradient φ (x + t • z)‖ ^ 2 :=
    ((continuous_gradient_of_contDiff hφ).comp (continuous_const.add
      (continuous_id.smul continuous_const))).norm.pow 2
  rw [sub_eq_integral_fderiv hφ, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor; simp
  have hvol : ∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by simp
  have hi1 : IntegrableOn (fun t : ℝ => fderiv ℝ φ (x + t • z) z) (Ioc 0 1) :=
    (hcont.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun t : ℝ => (fderiv ℝ φ (x + t • z) z) ^ 2) (Ioc 0 1) :=
    ((hcont.pow 2).integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  have hJ := sq_integral_le_weighted (μ := volume.restrict (Ioc (0 : ℝ) 1)) (w := fun _ => 1)
    (h := fun t => fderiv ℝ φ (x + t • z) z) (fun _ => zero_le_one) hvol
    (integrable_const 1) (hi1.const_mul 1) (hi2.const_mul 1)
  simp only [one_mul] at hJ
  refine hJ.trans ?_
  rw [← integral_const_mul]
  refine setIntegral_mono_on ((hcont.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((continuous_const.mul hgc).integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
    fun t _ => ?_
  rw [mul_comm]
  exact sq_fderiv_le_norm_gradient_sq φ _ z

/-- A cutoff in the time variable: continuous, `0 ≤ χ ≤ 1`, `χ = 1` on `[0,1]`, `∫ χ ≤ 3`. -/
lemma exists_time_cutoff : ∃ χ : ℝ → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ t, 0 ≤ χ t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, χ t = 1) ∧ ∫ t, χ t ≤ 3 := by
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩
  refine ⟨b, b.continuous, b.hasCompactSupport, fun t => b.nonneg, fun t ht => ?_, ?_⟩
  · apply b.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    show t ∈ Icc (1 / 2 - 1 / 2) (1 / 2 + 1 / 2)
    norm_num
    exact ht
  · have hle : ∀ t, b t ≤ (Icc (-1 : ℝ) 2).indicator 1 t := by
      intro t
      by_cases ht : t ∈ Icc (-1 : ℝ) 2
      · rw [indicator_of_mem ht]; exact b.le_one
      · rw [indicator_of_notMem ht]
        have : t ∉ support b := by
          rw [b.support_eq, Real.ball_eq_Ioo]
          intro h
          apply ht
          have h' : t ∈ Ioo (1 / 2 - 3 / 2 : ℝ) (1 / 2 + 3 / 2) := h
          norm_num at h'
          exact ⟨h'.1.le, h'.2.le⟩
        exact (notMem_support.mp this).le
    calc ∫ t, b t ≤ ∫ t, (Icc (-1 : ℝ) 2).indicator 1 t :=
          integral_mono (b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport)
            ((continuous_const.integrableOn_Icc (a := (-1 : ℝ)) (b := 2)).integrable_indicator
              measurableSet_Icc) hle
      _ = 3 := by
          rw [integral_indicator measurableSet_Icc]
          simp
          norm_num

/-- **Translation estimate** for test functions: `‖φ(· + z) - φ‖² ≤ 3 |z|² ‖∇φ‖²`. -/
lemma translation_estimate {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (z : RN N) :
    ∫ x, (φ (x + z) - φ x) ^ 2 ≤ 3 * ‖z‖ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
  obtain ⟨χ, hχc, hχs, hχ0, hχ1, hχint⟩ := exists_time_cutoff
  have hgr := continuous_gradient_of_contDiff hφ
  have hgrs := hasCompactSupport_gradient hc
  set G : RN N → ℝ → ℝ := fun x t => χ t * ‖gradient φ (x + t • z)‖ ^ 2 with hG
  have hGc : Continuous G.uncurry := by
    refine (hχc.comp continuous_snd).mul ?_
    exact (hgr.comp (continuous_fst.add (continuous_snd.smul continuous_const))).norm.pow 2
  have hGs : HasCompactSupport G.uncurry := by
    have hK : IsCompact ((fun p : RN N × ℝ => (p.1 - p.2 • z, p.2)) ''
        (tsupport (gradient φ) ×ˢ tsupport χ)) :=
      (hgrs.isCompact.prod hχs.isCompact).image
        ((continuous_fst.sub (continuous_snd.smul continuous_const)).prodMk continuous_snd)
    refine HasCompactSupport.intro hK fun p hp => ?_
    show χ p.2 * ‖gradient φ (p.1 + p.2 • z)‖ ^ 2 = 0
    by_contra hne
    apply hp
    refine ⟨(p.1 + p.2 • z, p.2), ⟨?_, ?_⟩, by simp⟩
    · refine subset_tsupport _ fun h => hne ?_
      simp [h]
    · refine subset_tsupport _ fun h => hne ?_
      simp [h]
  have hGi : Integrable G.uncurry (volume.prod volume) :=
    hGc.integrable_of_hasCompactSupport hGs
  have hpt : ∀ x, (φ (x + z) - φ x) ^ 2 ≤ ‖z‖ ^ 2 * ∫ t, G x t := by
    intro x
    refine (sq_sub_le_integral hφ x z).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have hgc : Continuous fun t : ℝ => ‖gradient φ (x + t • z)‖ ^ 2 :=
      (hgr.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.pow 2
    rw [intervalIntegral.integral_of_le zero_le_one]
    calc ∫ t in Ioc (0 : ℝ) 1, ‖gradient φ (x + t • z)‖ ^ 2
        = ∫ t in Ioc (0 : ℝ) 1, G x t := by
          refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          simp only [G, hχ1 t (Ioc_subset_Icc_self ht), one_mul]
      _ ≤ ∫ t, G x t := by
          refine setIntegral_le_integral ?_ (Eventually.of_forall fun t =>
            mul_nonneg (hχ0 t) (sq_nonneg _))
          exact (hχc.mul hgc).integrable_of_hasCompactSupport hχs.mul_right
  have hint1 : Integrable (fun x => (φ (x + z) - φ x) ^ 2) :=
    (((hφ.continuous.comp (continuous_id.add continuous_const)).sub hφ.continuous).pow 2
      ).integrable_of_hasCompactSupport (by
        have hK : IsCompact (tsupport φ ∪ (fun y => y - z) '' tsupport φ) :=
          hc.isCompact.union (hc.isCompact.image (continuous_id.sub continuous_const))
        refine HasCompactSupport.intro hK fun x hx => ?_
        have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl h)
        have h2 : φ (x + z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
          hx (Or.inr ⟨x + z, h, by simp⟩)
        simp [h1, h2])
  have hint2 : Integrable (fun x => ∫ t, G x t) := hGi.integral_prod_left
  have htrans : ∀ t : ℝ, ∫ x, ‖gradient φ (x + t • z)‖ ^ 2 = ∫ x, ‖gradient φ x‖ ^ 2 :=
    fun t => integral_add_right_eq_self (fun x => ‖gradient φ x‖ ^ 2) (t • z)
  have hnn : 0 ≤ ∫ x, ‖gradient φ x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  calc ∫ x, (φ (x + z) - φ x) ^ 2 ≤ ∫ x, ‖z‖ ^ 2 * ∫ t, G x t :=
        integral_mono hint1 (hint2.const_mul _) hpt
    _ = ‖z‖ ^ 2 * ∫ t, ∫ x, G x t := by
        rw [integral_const_mul, integral_integral_swap_of_hasCompactSupport hGc hGs]
    _ = ‖z‖ ^ 2 * ((∫ t, χ t) * ∫ x, ‖gradient φ x‖ ^ 2) := by
        congr 1
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [G]
        rw [integral_const_mul, htrans]
    _ ≤ 3 * ‖z‖ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hχint hnn
        nlinarith [sq_nonneg ‖z‖, mul_le_mul_of_nonneg_left this (sq_nonneg ‖z‖)]

/-! ### Mollification -/

/-- The mollification `(ρ * φ)(x) = ∫ ρ(y) φ(x - y) dy`. -/
def mollify (ρ φ : RN N → ℝ) (x : RN N) : ℝ := ∫ y, ρ y * φ (x - y)

/-- Hypotheses on a mollifier of radius `δ`. -/
structure IsMollifier (ρ : RN N → ℝ) (δ : ℝ) : Prop where
  cont : Continuous ρ
  compact : HasCompactSupport ρ
  nonneg : ∀ y, 0 ≤ ρ y
  int_one : ∫ y, ρ y = 1
  supp : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ δ
  lip : ∃ L, LipschitzWith L ρ

lemma exists_mollifier {δ : ℝ} (hδ : 0 < δ) : ∃ ρ : RN N → ℝ, IsMollifier ρ δ := by
  let b : ContDiffBump (0 : RN N) := ⟨δ / 2, δ, by positivity, by linarith⟩
  refine ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed,
    fun y => b.nonneg_normed y, b.integral_normed, fun y hy => ?_, ?_⟩
  · have : y ∈ support (b.normed volume) := hy
    rw [b.support_normed_eq, mem_ball_zero_iff] at this
    exact this.le
  · exact ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport_normed
      (b.contDiff_normed (n := 1)) (by norm_num)

section mollifier

variable {ρ : RN N → ℝ} {δ : ℝ} (hρ : IsMollifier ρ δ)
include hρ

lemma IsMollifier.integrable : Integrable ρ := hρ.cont.integrable_of_hasCompactSupport hρ.compact

lemma IsMollifier.integrable_mul {g : RN N → ℝ} (hg : Continuous g) :
    Integrable (fun y => ρ y * g y) :=
  (hρ.cont.mul hg).integrable_of_hasCompactSupport hρ.compact.mul_right

/-- **Mollification estimate**: `‖ρ_δ * φ - φ‖² ≤ 3 δ² ‖∇φ‖²`. -/
lemma mollify_sub_sq_le {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∫ x, (mollify ρ φ x - φ x) ^ 2 ≤ 3 * δ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
  have hφc := hφ.continuous
  set F : RN N → RN N → ℝ := fun x y => ρ y * (φ (x - y) - φ x) ^ 2 with hF
  have hFc : Continuous F.uncurry :=
    (hρ.cont.comp continuous_snd).mul
      (((hφc.comp (continuous_fst.sub continuous_snd)).sub (hφc.comp continuous_fst)).pow 2)
  have hFs : HasCompactSupport F.uncurry := by
    have hK : IsCompact ((tsupport φ ×ˢ tsupport ρ) ∪
        (fun p : RN N × RN N => (p.1 + p.2, p.2)) '' (tsupport φ ×ˢ tsupport ρ)) :=
      (hc.isCompact.prod hρ.compact.isCompact).union ((hc.isCompact.prod hρ.compact.isCompact).image
        ((continuous_fst.add continuous_snd).prodMk continuous_snd))
    refine HasCompactSupport.intro hK fun p hp => ?_
    show ρ p.2 * (φ (p.1 - p.2) - φ p.1) ^ 2 = 0
    by_contra hne
    have hρy : ρ p.2 ≠ 0 := left_ne_zero_of_mul hne
    have hd : φ (p.1 - p.2) - φ p.1 ≠ 0 := fun h => hne (by rw [h]; ring)
    apply hp
    by_cases h1 : φ p.1 = 0
    · right
      refine ⟨(p.1 - p.2, p.2), ⟨subset_tsupport _ fun h => hd (by rw [h, h1]; ring),
        subset_tsupport _ hρy⟩, by simp⟩
    · left
      exact ⟨subset_tsupport _ h1, subset_tsupport _ hρy⟩
  have hFi : Integrable F.uncurry (volume.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have hpt : ∀ x, (mollify ρ φ x - φ x) ^ 2 ≤ ∫ y, F x y := by
    intro x
    have hcx : Continuous fun y => φ (x - y) := hφc.comp (continuous_const.sub continuous_id)
    have e : mollify ρ φ x - φ x = ∫ y, ρ y * (φ (x - y) - φ x) := by
      have h1 : ∫ y, ρ y * φ x = φ x := by rw [integral_mul_const, hρ.int_one, one_mul]
      have h2 : ∫ y, ρ y * (φ (x - y) - φ x) = (∫ y, ρ y * φ (x - y)) - ∫ y, ρ y * φ x := by
        have : (fun y => ρ y * (φ (x - y) - φ x)) = fun y => ρ y * φ (x - y) - ρ y * φ x := by
          ext y; ring
        rw [this]
        exact integral_sub (hρ.integrable_mul hcx) (hρ.integrable.mul_const (φ x))
      rw [h2, h1, mollify]
    rw [e]
    exact sq_integral_le_weighted hρ.nonneg hρ.int_one hρ.integrable
      (hρ.integrable_mul (hcx.sub continuous_const))
      (hρ.integrable_mul ((hcx.sub continuous_const).pow 2))
  have hG0 : 0 ≤ ∫ x, ‖gradient φ x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  calc ∫ x, (mollify ρ φ x - φ x) ^ 2 ≤ ∫ x, ∫ y, F x y :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          hFi.integral_prod_left (Eventually.of_forall hpt)
    _ = ∫ y, ∫ x, F x y := integral_integral_swap_of_hasCompactSupport hFc hFs
    _ ≤ ∫ y, ρ y * (3 * δ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y =>
          integral_nonneg fun x => mul_nonneg (hρ.nonneg y) (sq_nonneg _))
          (hρ.integrable.mul_const _) (Eventually.of_forall fun y => ?_)
        show ∫ x, F x y ≤ ρ y * (3 * δ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2)
        simp only [F]
        rw [integral_const_mul]
        by_cases hy : ρ y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg y)
        have ht := translation_estimate hφ hc (-y)
        simp only [← sub_eq_add_neg, norm_neg] at ht
        refine ht.trans ?_
        have hyδ := hρ.supp y hy
        have : ‖y‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyδ 2
        nlinarith
    _ = 3 * δ ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
        rw [integral_mul_const, hρ.int_one, one_mul]

omit hρ in
lemma mollify_eq' (φ : RN N → ℝ) (x : RN N) : mollify ρ φ x = ∫ y, ρ (x - y) * φ y := by
  have := integral_sub_left_eq_self (μ := (volume : Measure (RN N)))
    (fun y => ρ (x - y) * φ y) x
  simp only [sub_sub_cancel] at this
  rw [mollify, this]

lemma mollify_lipschitz {L : NNReal} (hL : LipschitzWith L ρ) {φ : RN N → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (x x' : RN N) :
    |mollify ρ φ x - mollify ρ φ x'| ≤ L * ‖x - x'‖ * ∫ y, |φ y| := by
  have hi : ∀ z : RN N, Integrable (fun y => ρ (z - y) * φ y) := fun z =>
    ((hρ.cont.comp (continuous_const.sub continuous_id)).mul hφc).integrable_of_hasCompactSupport
      hφs.mul_left
  have hai : Integrable (fun y => |φ y|) :=
    (hφc.abs).integrable_of_hasCompactSupport hφs.abs
  rw [mollify_eq', mollify_eq', ← integral_sub (hi x) (hi x'), ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono ((hi x).sub (hi x')).abs
    (hai.const_mul _) fun y => ?_)
  show |ρ (x - y) * φ y - ρ (x' - y) * φ y| ≤ L * ‖x - x'‖ * |φ y|
  rw [← sub_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have := hL.dist_le_mul (x - y) (x' - y)
  rw [Real.dist_eq, dist_eq_norm, sub_sub_sub_cancel_right] at this
  exact this

lemma mollify_abs_le {M : ℝ} (hM : ∀ y, ρ y ≤ M) {φ : RN N → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (x : RN N) : |mollify ρ φ x| ≤ M * ∫ y, |φ y| := by
  have hi : Integrable (fun y => ρ (x - y) * φ y) :=
    ((hρ.cont.comp (continuous_const.sub continuous_id)).mul hφc).integrable_of_hasCompactSupport
      hφs.mul_left
  have hai : Integrable (fun y => |φ y|) := (hφc.abs).integrable_of_hasCompactSupport hφs.abs
  rw [mollify_eq', ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hi.abs (hai.const_mul _) fun y => ?_)
  show |ρ (x - y) * φ y| ≤ M * |φ y|
  rw [abs_mul, abs_of_nonneg (hρ.nonneg _)]
  exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)

lemma mollify_eq_zero {R : ℝ} {φ : RN N → ℝ} (hsupp : tsupport φ ⊆ closedBall 0 R) {x : RN N}
    (hx : R + δ < ‖x‖) : mollify ρ φ x = 0 := by
  rw [mollify]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  show ρ y * φ (x - y) = 0
  by_cases hy : ρ y = 0
  · simp [hy]
  have h1 := hρ.supp y hy
  have h2 : φ (x - y) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h3 := hsupp h
    rw [mem_closedBall_zero_iff] at h3
    have := norm_sub_norm_le x y
    linarith
  simp [h2]

lemma continuous_mollify {L : NNReal} (hL : LipschitzWith L ρ) {φ : RN N → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) : Continuous (mollify ρ φ) := by
  refine (LipschitzWith.of_dist_le_mul (K := L * Real.toNNReal (∫ y, |φ y|)) fun x x' => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _
    (integral_nonneg fun y => abs_nonneg _)]
  have := mollify_lipschitz hρ hL hφc hφs x x'
  linarith

end mollifier

lemma integral_abs_le_of_supp {R : ℝ} {φ : RN N → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ closedBall 0 R) :
    ∫ y, |φ y| ≤ ((volume (closedBall (0 : RN N) R)).toReal + ∫ y, φ y ^ 2) / 2 := by
  have hind : Integrable ((closedBall (0 : RN N) R).indicator (fun _ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall (0 : RN N) R)).integrable_indicator
      measurableSet_closedBall
  have hsq : Integrable (fun y => φ y ^ 2) :=
    (hφc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_of_vanish hφs
      (fun x hx => by simp [hx]))
  have hai : Integrable (fun y => |φ y|) := (hφc.abs).integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanish hφs (fun x hx => by simp [hx]))
  have : ∫ y, |φ y| ≤ ∫ y, ((closedBall (0 : RN N) R).indicator (fun _ => (1 : ℝ)) y + φ y ^ 2) / 2 := by
    refine integral_mono hai ((hind.add hsq).div_const 2) fun y => ?_
    show |φ y| ≤ ((closedBall (0 : RN N) R).indicator (fun _ => (1 : ℝ)) y + φ y ^ 2) / 2
    by_cases hy : y ∈ closedBall (0 : RN N) R
    · rw [indicator_of_mem hy]
      nlinarith [sq_nonneg (|φ y| - 1), sq_abs (φ y)]
    · have : φ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)
      simp [this, indicator_of_notMem hy]
  refine this.trans (le_of_eq ?_)
  rw [integral_div, integral_add hind hsq, integral_indicator measurableSet_closedBall]
  simp [Measure.real]

/-! ### Arzelà–Ascoli for mollified functions -/

/-- For a fixed mollifier, the mollifications of a family of functions supported in a fixed ball
with bounded `L¹` norm admit finite uniform `η`-nets (Arzelà–Ascoli). -/
lemma finite_net_mollified {ρ : RN N → ℝ} {δ : ℝ} (hρ : IsMollifier ρ δ) {R A : ℝ}
    (Φ : Set (RN N → ℝ))
    (hΦ : ∀ φ ∈ Φ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ closedBall 0 R ∧
      ∫ y, |φ y| ≤ A)
    {η : ℝ} (hη : 0 < η) :
    ∃ t ⊆ Φ, t.Finite ∧ ∀ φ ∈ Φ, ∃ ψ ∈ t, ∀ x, |mollify ρ φ x - mollify ρ ψ x| < η := by
  obtain ⟨L, hL⟩ := hρ.lip
  obtain ⟨M0, hM0⟩ := hρ.cont.bounded_above_of_compact_support hρ.compact
  set M := max M0 0 with hMdef
  have hM : ∀ y, ρ y ≤ M := fun y =>
    (le_abs_self _).trans ((hM0 y).trans (le_max_left _ _))
  have hM0' : 0 ≤ M := le_max_right _ _
  set A' := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  haveI : CompactSpace ↥(closedBall (0 : RN N) (R + δ)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F : Φ → BoundedContinuousFunction ↥(closedBall (0 : RN N) (R + δ)) ℝ := fun φ =>
    BoundedContinuousFunction.mkOfCompact
    (⟨fun p => mollify ρ φ.1 (p : RN N), (continuous_mollify hρ hL (hΦ φ.1 φ.2).1
      (hΦ φ.1 φ.2).2.1).comp continuous_subtype_val⟩ :
        C(↥(closedBall (0 : RN N) (R + δ)), ℝ))
  have hFapply : ∀ φ p, F φ p = mollify ρ φ.1 p := fun _ _ => rfl
  have hcomp : IsCompact (closure (range F)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 (M * A'))
      (isCompact_closedBall _ _) _ ?_ ?_
    · rintro f p ⟨φ, rfl⟩
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, hFapply]
      exact (mollify_abs_le hρ hM (hΦ φ.1 φ.2).1 (hΦ φ.1 φ.2).2.1 p).trans
        (mul_le_mul_of_nonneg_left ((hΦ φ.1 φ.2).2.2.2.trans (le_max_left _ _)) hM0')
    · have hlip : ∀ f : range F, LipschitzWith (L * Real.toNNReal A')
          (f : ↥(closedBall (0 : RN N) (R + δ)) → ℝ) := by
        rintro ⟨f, φ, rfl⟩
        refine LipschitzWith.of_dist_le_mul fun p q => ?_
        show dist (F φ p) (F φ q) ≤ _
        rw [hFapply, hFapply, Real.dist_eq, Subtype.dist_eq, dist_eq_norm, NNReal.coe_mul,
          Real.coe_toNNReal _ hA'0]
        refine (mollify_lipschitz hρ hL (hΦ φ.1 φ.2).1 (hΦ φ.1 φ.2).2.1 p q).trans ?_
        have := (hΦ φ.1 φ.2).2.2.2.trans (le_max_left A 0)
        have h0 : (0 : ℝ) ≤ L * ‖(p : RN N) - q‖ := by positivity
        nlinarith
      exact (LipschitzWith.uniformEquicontinuous _ _ hlip).equicontinuous
  have htb : TotallyBounded (range F) := hcomp.totallyBounded.subset subset_closure
  obtain ⟨t, htF, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded htb η hη
  have hpre : ∀ y ∈ t, ∃ φ : Φ, F φ = y := fun y hy => htF hy
  choose g hg using hpre
  haveI : Finite t := htfin.to_subtype
  refine ⟨range (fun y : t => (g y.1 y.2).1), ?_, finite_range _, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact (g y.1 y.2).2
  · intro φ hφ
    obtain ⟨y, hy, hdist⟩ := mem_iUnion₂.mp (hcover ⟨⟨φ, hφ⟩, rfl⟩)
    refine ⟨(g y hy).1, ⟨⟨y, hy⟩, rfl⟩, fun x => ?_⟩
    by_cases hx : x ∈ closedBall (0 : RN N) (R + δ)
    · have h1 := BoundedContinuousFunction.dist_coe_le_dist (f := F ⟨φ, hφ⟩) (g := F (g y hy))
        ⟨x, hx⟩
      rw [hg y hy] at h1
      rw [mem_ball] at hdist
      have h2 := h1.trans_lt hdist
      rw [← hg y hy, hFapply, hFapply, Real.dist_eq] at h2
      exact h2
    · have hx' : R + δ < ‖x‖ := by
        rw [mem_closedBall_zero_iff, not_le] at hx; exact hx
      rw [mollify_eq_zero hρ (hΦ φ hφ).2.2.1 hx',
        mollify_eq_zero hρ (hΦ _ (g y hy).2).2.2.1 hx', sub_self, abs_zero]
      exact hη

/-! ### Total boundedness of bounded sets of test functions in `L²` -/

open Classical in
/-- A function viewed in `L²` (zero if it is not square integrable). -/
def toL2 (g : RN N → ℝ) : L2 N := if h : MemLp g 2 volume then h.toLp g else 0

lemma toL2_eq {g : RN N → ℝ} (h : MemLp g 2 volume) : toL2 g = h.toLp g := by
  rw [toL2, dif_pos h]

lemma norm_toLp_sq {g : RN N → ℝ} (h : MemLp g 2 volume) : ‖h.toLp g‖ ^ 2 = ∫ x, g x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp] with x hx
  simp [hx, sq]

lemma dist_toL2_sq {f g : RN N → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    dist (toL2 f) (toL2 g) ^ 2 = ∫ x, (f x - g x) ^ 2 := by
  rw [toL2_eq hf, toL2_eq hg, dist_eq_norm, ← MemLp.toLp_sub, norm_toLp_sq]
  rfl

lemma dist_toL2_lt {f g : RN N → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {r : ℝ}
    (hr : 0 < r) (h : ∫ x, (f x - g x) ^ 2 < r ^ 2) : dist (toL2 f) (toL2 g) < r := by
  rw [← dist_toL2_sq hf hg] at h
  exact lt_of_pow_lt_pow_left₀ 2 hr.le h

lemma memLp_mollify {ρ : RN N → ℝ} {δ : ℝ} (hρ : IsMollifier ρ δ) {R : ℝ} {φ : RN N → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ closedBall 0 R) :
    MemLp (mollify ρ φ) 2 volume := by
  obtain ⟨L, hL⟩ := hρ.lip
  refine (continuous_mollify hρ hL hφc hφs).memLp_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : RN N) (R + δ)) fun x hx => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact mollify_eq_zero hρ hsupp hx

/-- Test functions supported in `closedBall 0 R` with `∫ φ² ≤ B` and `∫ |∇φ|² ≤ B`, in `L²`. -/
def testSet (N : ℕ) (R B : ℝ) : Set (L2 N) :=
  {f | ∃ φ : RN N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ closedBall 0 R ∧ ∫ x, φ x ^ 2 ≤ B ∧ ∫ x, ‖gradient φ x‖ ^ 2 ≤ B ∧ f = toL2 φ}

/-- **Rellich for test functions**: `testSet R B` is totally bounded in `L²`. -/
theorem totallyBounded_testSet (R B : ℝ) : TotallyBounded (testSet N R B) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨B', hB'⟩ : ∃ B', B' = |B| + 1 := ⟨_, rfl⟩
  have hB'0 : 0 < B' := by rw [hB']; positivity
  have hBB' : B ≤ B' := by rw [hB']; linarith [le_abs_self B]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / (6 * B') := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have h3δ : 3 * δ ^ 2 * B' < (ε / 3) ^ 2 := by
    rw [hδ, div_pow, mul_pow]
    have hB'1 : 1 ≤ B' := by rw [hB']; linarith [abs_nonneg B]
    field_simp
    nlinarith
  obtain ⟨ρ, hρ⟩ := exists_mollifier (N := N) hδ0
  obtain ⟨V, hV⟩ : ∃ V, V = (volume (closedBall (0 : RN N) (R + δ))).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; exact ENNReal.toReal_nonneg
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (3 * (V + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηV : η ^ 2 * V < (ε / 3) ^ 2 := by
    rw [hη, div_pow, mul_pow, div_pow]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    have : V * 3 ^ 2 < 3 ^ 2 * (V + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ε, mul_lt_mul_of_pos_left this (by positivity : (0:ℝ) < ε ^ 2)]
  let Φ : Set (RN N → ℝ) := {φ | ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ closedBall 0 R ∧ ∫ x, φ x ^ 2 ≤ B ∧ ∫ x, ‖gradient φ x‖ ^ 2 ≤ B}
  have hΦ : ∀ φ ∈ Φ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ closedBall 0 R ∧
      ∫ y, |φ y| ≤ ((volume (closedBall (0 : RN N) R)).toReal + B) / 2 := by
    rintro φ ⟨h1, h2, h3, h4, -⟩
    refine ⟨h1.continuous, h2, h3, (integral_abs_le_of_supp h1.continuous h2 h3).trans ?_⟩
    linarith
  obtain ⟨t, htΦ, htfin, hnet⟩ := finite_net_mollified hρ Φ hΦ hη0
  refine ⟨toL2 '' t, htfin.image _, ?_⟩
  rintro f ⟨φ, h1, h2, h3, h4, h5, rfl⟩
  have hφΦ : φ ∈ Φ := ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ψ, hψt, hψ⟩ := hnet φ hφΦ
  obtain ⟨g1, g2, g3, g4, g5⟩ := htΦ hψt
  refine mem_iUnion₂.mpr ⟨toL2 ψ, mem_image_of_mem _ hψt, ?_⟩
  rw [mem_ball]
  have mφ := memLp_of_testFun h1 h2
  have mψ := memLp_of_testFun g1 g2
  have mmφ := memLp_mollify hρ h1.continuous h2 h3
  have mmψ := memLp_mollify hρ g1.continuous g2 g3
  have d1 : dist (toL2 φ) (toL2 (mollify ρ φ)) < ε / 3 := by
    refine dist_toL2_lt mφ mmφ (by positivity) ?_
    have := mollify_sub_sq_le hρ h1 h2
    have e : ∫ x, (φ x - mollify ρ φ x) ^ 2 = ∫ x, (mollify ρ φ x - φ x) ^ 2 := by
      congr 1; ext x; ring
    rw [e]
    refine this.trans_lt (lt_of_le_of_lt ?_ h3δ)
    exact mul_le_mul_of_nonneg_left (h5.trans hBB') (by positivity)
  have d3 : dist (toL2 (mollify ρ ψ)) (toL2 ψ) < ε / 3 := by
    refine dist_toL2_lt mmψ mψ (by positivity) ?_
    have := mollify_sub_sq_le hρ g1 g2
    refine this.trans_lt (lt_of_le_of_lt ?_ h3δ)
    exact mul_le_mul_of_nonneg_left (g5.trans hBB') (by positivity)
  have d2 : dist (toL2 (mollify ρ φ)) (toL2 (mollify ρ ψ)) < ε / 3 := by
    refine dist_toL2_lt mmφ mmψ (by positivity) (lt_of_le_of_lt ?_ hηV)
    have hind : Integrable ((closedBall (0 : RN N) (R + δ)).indicator (fun _ => η ^ 2)) :=
      (continuous_const.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : RN N) (R + δ))).integrable_indicator measurableSet_closedBall
    calc ∫ x, (mollify ρ φ x - mollify ρ ψ x) ^ 2
        ≤ ∫ x, (closedBall (0 : RN N) (R + δ)).indicator (fun _ => η ^ 2) x := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hind
            (Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ closedBall (0 : RN N) (R + δ)
          · rw [indicator_of_mem hx]
            show (mollify ρ φ x - mollify ρ ψ x) ^ 2 ≤ η ^ 2
            rw [← sq_abs (mollify ρ φ x - _)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hψ x).le 2
          · rw [indicator_of_notMem hx]
            show (mollify ρ φ x - mollify ρ ψ x) ^ 2 ≤ 0
            rw [mem_closedBall_zero_iff, not_le] at hx
            rw [mollify_eq_zero hρ h3 hx, mollify_eq_zero hρ g3 hx]
            simp
      _ = η ^ 2 * V := by
          rw [integral_indicator measurableSet_closedBall, hV]
          simp [Measure.real, mul_comm]
  calc dist (toL2 φ) (toL2 ψ)
      ≤ dist (toL2 φ) (toL2 (mollify ρ φ)) + dist (toL2 (mollify ρ φ)) (toL2 (mollify ρ ψ)) +
        dist (toL2 (mollify ρ ψ)) (toL2 ψ) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-! ### Rellich's theorem on `H_D` -/

lemma fst_mem_closure_testSet {D : Set (RN N)} {R : ℝ} (hR : D ⊆ closedBall 0 R) {C : ℝ}
    {v : Amb N} (hv : v ∈ H D) (hC : ‖v‖ ≤ C) : v.1 ∈ closure (testSet N R ((C + 1) ^ 2)) := by
  have hv' : v ∈ closure (testGraph D) := by rw [← H_eq_closure]; exact hv
  rw [Metric.mem_closure_iff] at hv' ⊢
  intro ε hε
  obtain ⟨b, hb, hdist⟩ := hv' (min ε 1) (lt_min hε one_pos)
  obtain ⟨φ, hφ, hc, hs, rfl⟩ := eq_testPair hb
  have hnb : ‖testPair φ hφ hc‖ ≤ C + 1 := by
    have h1 := norm_le_norm_add_norm_sub' (testPair φ hφ hc) v
    have h2 : ‖testPair φ hφ hc - v‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]; exact hdist.trans_le (min_le_right _ _)
    linarith
  have hC1 : 0 ≤ C + 1 := (norm_nonneg _).trans hnb
  refine ⟨toL2 φ, ⟨φ, hφ, hc, hs.trans hR, ?_, ?_, rfl⟩, ?_⟩
  · have := l2_testPair φ φ hφ hc hφ hc
    simp only [sq]
    rw [← this, l2, real_inner_self_eq_norm_sq, ← sq]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_fst_le _).trans hnb) 2
  · rw [← qf_testPair_self φ hφ hc, qf, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_snd_le _).trans hnb) 2
  · rw [toL2_eq (memLp_of_testFun hφ hc)]
    calc dist v.1 (testPair φ hφ hc).1 ≤ dist v (testPair φ hφ hc) := by
          rw [Prod.dist_eq]; exact le_max_left _ _
      _ < ε := hdist.trans_le (min_le_left _ _)

/-- **Rellich's theorem**: for bounded `D`, a bounded sequence in `H_D` has a subsequence whose
`L²` components converge. -/
theorem rellich {D : Set (RN N)} (hD : Bornology.IsBounded D)
    (v : ℕ → Amb N) (hv : ∀ n, v n ∈ H D) (hb : ∃ C, ∀ n, ‖v n‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : L2 N, Tendsto (fun n => (v (φ n)).1) atTop (𝓝 f) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨R, hR⟩ := hD.subset_closedBall 0
  have hK : IsCompact (closure (testSet N R ((C + 1) ^ 2))) :=
    (totallyBounded_testSet R _).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨f, -, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq fun n => fst_mem_closure_testSet hR (hv n) (hC n)
  exact ⟨φ, hφ, f, hlim⟩

end FourthRatio

end

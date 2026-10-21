module

public import RequestProject.HarmonicAnalytic

/-!
# Lifting the Helmholtz equation to a harmonic function in one more variable

If `Δu + λu = 0` weakly in `D ⊆ ℝ^N` with `λ ≥ 0`, then `w(x, t) = u(x) cosh(√λ t)` is weakly
harmonic in `D × ℝ ⊆ ℝ^{N+1}`.  Combined with Weyl's lemma and the analyticity of harmonic
functions this gives interior analyticity of weak eigenfunctions.

This file contains the coordinate identification `ℝ^N × ℝ ≃ ℝ^{N+1}` (`joinEq`, measure
preserving), the splitting of the Laplacian (`laplacian_joinEq`) and the lifting theorem
`weakHarmonic_lift`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Coordinates -/

/-- The measurable identification `ℝ^N × ℝ ≃ ℝ^{N+1}`, `(x, t) ↦ (x₁, …, x_N, t)`. -/
def joinEq (N : ℕ) : (RN N × ℝ) ≃ᵐ RN (N + 1) :=
  ((MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.toLp 2 (Fin N → ℝ)).symm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last N)).symm).trans
    (MeasurableEquiv.toLp 2 (Fin (N + 1) → ℝ))

lemma joinEq_castSucc (x : RN N) (t : ℝ) (j : Fin N) : joinEq N (x, t) (Fin.castSucc j) = x j := by
  simp [joinEq, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

lemma joinEq_last (x : RN N) (t : ℝ) : joinEq N (x, t) (Fin.last N) = t := by
  simp [joinEq, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

lemma measurePreserving_joinEq : MeasurePreserving (joinEq N) (volume.prod volume) volume := by
  unfold joinEq
  refine MeasurePreserving.trans ?_ (PiLp.volume_preserving_toLp _)
  refine MeasurePreserving.trans ?_
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last N)).symm
  refine (Measure.measurePreserving_swap).trans ?_
  exact (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp _)

/-- The last basis vector of `ℝ^{N+1}`. -/
def eLast (N : ℕ) : RN (N + 1) := EuclideanSpace.single (Fin.last N) 1

/-- The linear embedding `ℝ^N → ℝ^{N+1}`, `x ↦ (x, 0)`. -/
def joinL (N : ℕ) : RN N →L[ℝ] RN (N + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => joinEq N (x, 0)
      map_add' := fun x y => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [joinEq_last]
        · simp [joinEq_castSucc]
      map_smul' := fun c x => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [joinEq_last]
        · simp [joinEq_castSucc] }

lemma joinL_apply (x : RN N) : joinL N x = joinEq N (x, 0) := rfl

lemma joinEq_eq (x : RN N) (t : ℝ) : joinEq N (x, t) = joinL N x + t • eLast N := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [joinL_apply, joinEq_last, eLast]
  · simp [joinL_apply, joinEq_castSucc, eLast, PiLp.single_apply,
      Fin.castSucc_ne_last]

lemma joinL_single (j : Fin N) :
    joinL N (EuclideanSpace.single j 1) = EuclideanSpace.single (Fin.castSucc j) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [joinL_apply, joinEq_last, PiLp.single_apply, (Fin.castSucc_ne_last j).symm]
  · simp [joinL_apply, joinEq_castSucc, PiLp.single_apply]

lemma continuous_joinEq : Continuous fun p : RN N × ℝ => joinEq N p := by
  have : (fun p : RN N × ℝ => joinEq N p) = fun p => joinL N p.1 + p.2 • eLast N := by
    funext p; rw [← joinEq_eq]
  rw [this]
  exact ((joinL N).continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)

/-- The projection `ℝ^{N+1} → ℝ^N` onto the first `N` coordinates. -/
def xpartL (N : ℕ) : RN (N + 1) →L[ℝ] RN N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun j : Fin N => z (Fin.castSucc j))
      map_add' := fun x y => by ext j; simp
      map_smul' := fun c x => by ext j; simp }

lemma xpartL_joinEq (x : RN N) (t : ℝ) : xpartL N (joinEq N (x, t)) = x := by
  ext j
  simp [xpartL, joinEq_castSucc]

/-! ### Splitting the Laplacian -/

lemma laplacian_joinEq {φ : RN (N + 1) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x : RN N) (t : ℝ) :
    Laplacian.laplacian φ (joinEq N (x, t)) =
      Laplacian.laplacian (fun y => φ (joinEq N (y, t))) x +
        iteratedDeriv 2 (fun s => φ (joinEq N (x, s))) t := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  set b' := EuclideanSpace.basisFun (Fin (N + 1)) ℝ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b',
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun y => φ (joinEq N (y, t))) = (fun z => φ (t • eLast N + z)) ∘ joinL N := by
      funext y; simp [joinEq_eq, add_comm]
    have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ (t • eLast N + z)) :=
      hφ.comp (contDiff_const.add contDiff_id)
    rw [e, (joinL N).iteratedFDeriv_comp_right hG x (WithTop.coe_le_coe.mpr le_top),
      iteratedFDeriv_comp_add_left]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hv : (fun i => joinL N (![b j, b j] i)) = ![b' (Fin.castSucc j), b' (Fin.castSucc j)] := by
      funext i
      fin_cases i <;> simp [b, b', joinL_single]
    rw [hv, joinEq_eq, add_comm (joinL N x)]
  · have e : (fun s => φ (joinEq N (x, s))) = fun s => φ (joinL N x + s • eLast N) := by
      funext s; rw [joinEq_eq]
    rw [e, iteratedDeriv_line hφ, joinEq_eq]
    congr 1
    funext i
    fin_cases i <;> simp [b', eLast]

lemma joinEq_symm_apply (z : RN (N + 1)) :
    (joinEq N).symm z = (xpartL N z, z (Fin.last N)) := by
  have hz : joinEq N (xpartL N z, z (Fin.last N)) = z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [joinEq_last]
    · simp [joinEq_castSucc, xpartL]
  conv_lhs => rw [← hz]
  exact (joinEq N).symm_apply_apply _

lemma continuous_joinEq_symm : Continuous fun z : RN (N + 1) => (joinEq N).symm z := by
  simp_rw [joinEq_symm_apply]
  exact (xpartL N).continuous.prodMk ((continuous_apply _).comp (PiLp.continuous_ofLp 2 _))

lemma isCompact_joinEq_preimage {K : Set (RN (N + 1))} (hK : IsCompact K) :
    IsCompact (joinEq N ⁻¹' K) := by
  have : joinEq N ⁻¹' K = (fun z => (joinEq N).symm z) '' K := by
    ext p; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hp; exact ⟨_, hp, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [this]
  exact hK.image continuous_joinEq_symm

/-! ### Integrability on the product -/

lemma integrableOn_prod_mul {u : RN N → ℝ} (hu : LocallyIntegrable u) (c : ℝ)
    {A : Set (RN N)} {B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B) :
    IntegrableOn (fun p : RN N × ℝ => u p.1 * Real.cosh (c * p.2)) (A ×ˢ B)
      (volume.prod volume) := by
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact Integrable.mul_prod (hu.integrableOn_isCompact hA)
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact hB)

/-- `u(x) cosh(ct) G(x, t)` is integrable on `ℝ^N × ℝ` for continuous compactly supported `G`. -/
lemma integrable_prod_mul_of_hasCompactSupport {u : RN N → ℝ} (hu : LocallyIntegrable u) (c : ℝ)
    {G : RN N × ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G) :
    Integrable (fun p : RN N × ℝ => u p.1 * Real.cosh (c * p.2) * G p) (volume.prod volume) := by
  set K := tsupport G
  have hK : IsCompact K := hGc
  set A := Prod.fst '' K
  set B := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hB : IsCompact B := hK.image continuous_snd
  have hKAB : K ⊆ A ×ˢ B := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have h1 : IntegrableOn (fun p : RN N × ℝ => u p.1 * Real.cosh (c * p.2) * G p) (A ×ˢ B)
      (volume.prod volume) :=
    (integrableOn_prod_mul hu c hA hB).mul_continuousOn hG.continuousOn (hA.prod hB)
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro p hp
  have : G p ≠ 0 := right_ne_zero_of_mul hp
  exact hKAB (subset_tsupport _ this)

/-! ### One-dimensional integration by parts against `cosh` -/

lemma integral_cosh_mul_deriv2 {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hhc : HasCompactSupport h) (c : ℝ) :
    ∫ t, Real.cosh (c * t) * iteratedDeriv 2 h t = c ^ 2 * ∫ t, Real.cosh (c * t) * h t := by
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall 0
  set R' := max R 0 + 1
  have hR' : 0 < R' := by positivity
  have hsupp : ∀ t, R' ≤ |t| → ∀ k, iteratedDeriv k h t = 0 := by
    intro t ht k
    have hnot : t ∉ tsupport h := fun hm => by
      have := hR hm
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      have : R < R' := by simp only [R']; linarith [le_max_left R 0]
      linarith
    have hev : h =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hnot] with s hs
      exact image_eq_zero_of_notMem_tsupport hs
    rw [hev.iteratedDeriv_eq k]
    cases k with
    | zero => simp
    | succ k => simp
  have hd : ∀ k, Differentiable ℝ (iteratedDeriv k h) := fun k =>
    hh.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k))
  have hcont : ∀ k, Continuous (iteratedDeriv k h) := fun k => (hd k).continuous
  -- reduce to `[-R', R']`
  have hint : ∀ g : ℝ → ℝ, (∀ t, R' ≤ |t| → g t = 0) → Continuous g →
      ∫ t, g t = ∫ t in (-R')..R', g t := by
    intro g hg hgc
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    apply hg
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hcosh : ∀ t, HasDerivAt (fun t => Real.cosh (c * t)) (c * Real.sinh (c * t)) t := by
    intro t
    have := (Real.hasDerivAt_cosh (c * t)).comp t ((hasDerivAt_id t).const_mul c)
    convert this using 1
    · rfl
    · ring
  have hsinh : ∀ t, HasDerivAt (fun t => c * Real.sinh (c * t)) (c ^ 2 * Real.cosh (c * t)) t := by
    intro t
    have := ((Real.hasDerivAt_sinh (c * t)).comp t ((hasDerivAt_id t).const_mul c)).const_mul c
    convert this using 1
    · rfl
    · ring
  have hder : ∀ k t, HasDerivAt (iteratedDeriv k h) (iteratedDeriv (k + 1) h t) t := by
    intro k t
    rw [iteratedDeriv_succ]
    exact (hd k t).hasDerivAt
  have hc1 : Continuous fun t => Real.cosh (c * t) := Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  have hc2 : Continuous fun t => c * Real.sinh (c * t) :=
    continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hc3 : Continuous fun t => c ^ 2 * Real.cosh (c * t) := continuous_const.mul hc1
  rw [hint (fun t => Real.cosh (c * t) * iteratedDeriv 2 h t)
      (fun t ht => by rw [hsupp t ht 2, mul_zero]) (hc1.mul (hcont 2)),
    hint (fun t => Real.cosh (c * t) * h t) (fun t ht => by rw [show h t = iteratedDeriv 0 h t by simp, hsupp t ht 0, mul_zero])
      (hc1.mul hh.continuous)]
  have hRR : R' ≤ |R'| := le_abs_self _
  have hRR' : R' ≤ |-R'| := by rw [abs_neg]; exact le_abs_self _
  -- first integration by parts
  have e1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -R') (b := R')
    (fun t _ => hcosh t) (fun t _ => hder 1 t) (hc2.intervalIntegrable _ _)
    ((hcont 2).intervalIntegrable _ _)
  rw [hsupp R' hRR 1, hsupp (-R') hRR' 1, mul_zero, mul_zero, sub_zero, zero_sub] at e1
  -- second integration by parts
  have e2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -R') (b := R')
    (fun t _ => hsinh t) (fun t _ => hder 0 t) (hc3.intervalIntegrable _ _)
    ((hcont 1).intervalIntegrable _ _)
  rw [hsupp R' hRR 0, hsupp (-R') hRR' 0, mul_zero, mul_zero, sub_zero, zero_sub] at e2
  simp only [iteratedDeriv_zero] at e2 ⊢
  have e3 : ∫ t in (-R')..R', c ^ 2 * Real.cosh (c * t) * h t =
      c ^ 2 * ∫ t in (-R')..R', Real.cosh (c * t) * h t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [e1, e2, e3]
  ring

/-! ### The lifting theorem -/

/-- The lifted function `w(x, t) = u(x) cosh(c t)` on `ℝ^{N+1}`. -/
def liftFun (N : ℕ) (u : RN N → ℝ) (c : ℝ) (z : RN (N + 1)) : ℝ :=
  u (xpartL N z) * Real.cosh (c * z (Fin.last N))

lemma liftFun_joinEq (u : RN N → ℝ) (c : ℝ) (x : RN N) (t : ℝ) :
    liftFun N u c (joinEq N (x, t)) = u x * Real.cosh (c * t) := by
  simp [liftFun, xpartL_joinEq, joinEq_last]

lemma locallyIntegrable_liftFun {u : RN N → ℝ} (hu : LocallyIntegrable u) (c : ℝ) :
    LocallyIntegrable (liftFun N u c) := by
  rw [locallyIntegrable_iff]
  intro K hK
  rw [← measurePreserving_joinEq.integrableOn_comp_preimage (joinEq N).measurableEmbedding]
  have hfun : liftFun N u c ∘ joinEq N = fun p => u p.1 * Real.cosh (c * p.2) := by
    funext p; exact liftFun_joinEq u c p.1 p.2
  rw [hfun]
  set K' := joinEq N ⁻¹' K
  have hK' : IsCompact K' := isCompact_joinEq_preimage hK
  have hsub : K' ⊆ (Prod.fst '' K') ×ˢ (Prod.snd '' K') := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  exact (integrableOn_prod_mul hu c (hK'.image continuous_fst)
    (hK'.image continuous_snd)).mono_set hsub

lemma contDiff_comp_joinEq_fst {φ : RN (N + 1) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ (joinEq N (y, t))) := by
  simp_rw [joinEq_eq]
  exact hφ.comp ((joinL N).contDiff.add contDiff_const)

lemma contDiff_comp_joinEq_snd {φ : RN (N + 1) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x : RN N) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => φ (joinEq N (x, s))) := by
  simp_rw [joinEq_eq]
  exact hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- **Lifting.** If `∫ u Δφ = -λ ∫ u φ` for all test functions `φ` supported in `D` and `λ ≥ 0`,
then `w(x, t) = u(x) cosh(√λ t)` is weakly harmonic on `D × ℝ`. -/
theorem weakHarmonic_lift {D : Set (RN N)} {u : RN N → ℝ} (hu : LocallyIntegrable u) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hweak : ∀ φ : RN N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ D → ∫ x, u x * Laplacian.laplacian φ x = -lam * ∫ x, u x * φ x) :
    WeakHarmonic (xpartL N ⁻¹' D) (liftFun N u (Real.sqrt lam)) := by
  set c := Real.sqrt lam with hcdef
  have hc2 : c ^ 2 = lam := Real.sq_sqrt hlam
  refine ⟨(locallyIntegrable_liftFun hu c).locallyIntegrableOn _, fun φ hφ hφc hφD => ?_⟩
  set K := tsupport φ
  have hK : IsCompact K := hφc
  set K' := joinEq N ⁻¹' K
  have hK' : IsCompact K' := isCompact_joinEq_preimage hK
  set Φ : RN N × ℝ → ℝ := fun p => φ (joinEq N p) with hΦdef
  set G2 : RN N × ℝ → ℝ := fun p => iteratedDeriv 2 (fun s => φ (joinEq N (p.1, s))) p.2
    with hG2def
  set G1 : RN N × ℝ → ℝ := fun p => Laplacian.laplacian (fun y => φ (joinEq N (y, p.2))) p.1
    with hG1def
  have hG2 : ∀ p, G2 p = iteratedFDeriv ℝ 2 φ (joinEq N p) (fun _ => eLast N) := by
    intro p
    simp only [hG2def]
    have e : (fun s => φ (joinEq N (p.1, s))) = fun s => φ (joinL N p.1 + s • eLast N) := by
      funext s; rw [joinEq_eq]
    rw [e, iteratedDeriv_line hφ, ← joinEq_eq]
  have hsplit : ∀ p, Laplacian.laplacian φ (joinEq N p) = G1 p + G2 p := fun p =>
    laplacian_joinEq hφ p.1 p.2
  have hcj : Continuous fun p : RN N × ℝ => joinEq N p := continuous_joinEq
  have hG2c : Continuous G2 := by
    rw [show G2 = fun p => iteratedFDeriv ℝ 2 φ (joinEq N p) (fun _ => eLast N) from funext hG2]
    exact ((hφ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).eval_const _).comp hcj
  have hG1c : Continuous G1 := by
    have : G1 = fun p => Laplacian.laplacian φ (joinEq N p) - G2 p := by
      funext p; rw [hsplit p]; ring
    rw [this]
    exact ((contDiff_laplacian hφ).continuous.comp hcj).sub hG2c
  have hΦc : Continuous Φ := hφ.continuous.comp hcj
  -- compact supports
  have hvan : ∀ p, p ∉ K' → Φ p = 0 ∧ G1 p = 0 ∧ G2 p = 0 := by
    intro p hp
    have hp' : joinEq N p ∉ tsupport φ := hp
    have h0 : Φ p = 0 := (image_eq_zero_of_notMem_tsupport hp' : φ (joinEq N p) = 0)
    have h2 : G2 p = 0 := by
      rw [hG2]
      have : iteratedFDeriv ℝ 2 φ (joinEq N p) = 0 := by
        by_contra h
        exact hp' (support_iteratedFDeriv_subset 2 h)
      rw [this]; rfl
    refine ⟨h0, ?_, h2⟩
    have := hsplit p
    rw [laplacian_eq_zero_of_notMem_tsupport hp', h2] at this
    linarith
  have hΦs : HasCompactSupport Φ := HasCompactSupport.intro hK' fun p hp => (hvan p hp).1
  have hG1s : HasCompactSupport G1 := HasCompactSupport.intro hK' fun p hp => (hvan p hp).2.1
  have hG2s : HasCompactSupport G2 := HasCompactSupport.intro hK' fun p hp => (hvan p hp).2.2
  have hI0 := integrable_prod_mul_of_hasCompactSupport hu c hΦc hΦs
  have hI1 := integrable_prod_mul_of_hasCompactSupport hu c hG1c hG1s
  have hI2 := integrable_prod_mul_of_hasCompactSupport hu c hG2c hG2s
  -- slices
  have hslice1 : ∀ t, ∫ x, u x * Real.cosh (c * t) * G1 (x, t) =
      -lam * (Real.cosh (c * t) * ∫ x, u x * Φ (x, t)) := by
    intro t
    set φt : RN N → ℝ := fun y => φ (joinEq N (y, t))
    have hφt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φt := contDiff_comp_joinEq_fst hφ t
    have hφtc : HasCompactSupport φt := by
      refine HasCompactSupport.intro (hK.image (xpartL N).continuous) fun y hy => ?_
      by_contra h
      exact hy ⟨_, subset_tsupport _ h, xpartL_joinEq y t⟩
    have hφtD : tsupport φt ⊆ D := by
      have hcont : Continuous fun y : RN N => joinEq N (y, t) :=
        hcj.comp (continuous_id.prodMk continuous_const)
      intro y hy
      have := tsupport_comp_subset_preimage φ hcont hy
      have h2 := hφD this
      simpa [xpartL_joinEq] using h2
    have h := hweak φt hφt hφtc hφtD
    have e1 : ∫ x, u x * Real.cosh (c * t) * G1 (x, t) =
        Real.cosh (c * t) * ∫ x, u x * Laplacian.laplacian φt x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hG1def, φt]; ring)
    rw [e1, h]
    ring
  have hslice2 : ∀ x, ∫ t, u x * Real.cosh (c * t) * G2 (x, t) =
      lam * (u x * ∫ t, Real.cosh (c * t) * Φ (x, t)) := by
    intro x
    set hx : ℝ → ℝ := fun s => φ (joinEq N (x, s))
    have hhx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hx := contDiff_comp_joinEq_snd hφ x
    have hhxc : HasCompactSupport hx := by
      refine HasCompactSupport.intro (hK.image ((continuous_apply (Fin.last N)).comp
        (PiLp.continuous_ofLp 2 _))) fun s hs => ?_
      by_contra h
      exact hs ⟨_, subset_tsupport _ h, by simp [joinEq_last]⟩
    have h := integral_cosh_mul_deriv2 hhx hhxc c
    have e1 : ∫ t, u x * Real.cosh (c * t) * G2 (x, t) =
        u x * ∫ t, Real.cosh (c * t) * iteratedDeriv 2 hx t := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp only [hG2def, hx]; ring)
    rw [e1, h, hc2]
    ring
  -- assemble
  have hmain : ∫ z, liftFun N u c z * Laplacian.laplacian φ z =
      ∫ p : RN N × ℝ, (u p.1 * Real.cosh (c * p.2) * G1 p + u p.1 * Real.cosh (c * p.2) * G2 p)
        ∂(volume.prod volume) := by
    rw [← measurePreserving_joinEq.integral_comp' (f := joinEq N)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    rw [show p = (p.1, p.2) from rfl, liftFun_joinEq, hsplit]
    ring
  rw [hmain, integral_add hI1 hI2, integral_prod_symm _ hI1, integral_prod _ hI2]
  simp only [hslice1, hslice2]
  rw [integral_const_mul, integral_const_mul]
  have e0a : ∫ t, Real.cosh (c * t) * ∫ x, u x * Φ (x, t) =
      ∫ p : RN N × ℝ, u p.1 * Real.cosh (c * p.2) * Φ p ∂(volume.prod volume) := by
    rw [integral_prod_symm _ hI0]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have e0b : ∫ x, u x * ∫ t, Real.cosh (c * t) * Φ (x, t) =
      ∫ p : RN N × ℝ, u p.1 * Real.cosh (c * p.2) * Φ p ∂(volume.prod volume) := by
    rw [integral_prod _ hI0]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  rw [e0a, e0b]
  ring

end FourthRatio

end

module

public import RequestProject.BallSteps
public import RequestProject.DisjointUnion
public import RequestProject.AnnulusRadial

/-!
# The test functions `ψ, ψ xᵢ/|x|` on the annulus

With `R = j_{ν,1}/√a`, `R' = j_{ν,2}/√a` and `A = {R < |x - y| < R'}`, we construct
* `ψ ∈ H₀¹(A)`, the restriction of `-Φ(· - y)` to `A` (via the positive part of a cut-off of
  `-Φ(· - y)` and the localization of positive parts, then restriction to one of two disjoint
  open pieces);
* `ψ · ⟨c, x - y⟩/|x - y| ∈ H₀¹(A)` for every `c ∈ ℝ^N` (multiplication by a smooth bounded
  function).

Each of them, and every linear combination, has explicit representatives of the function and of
its weak gradient (`IsAnnRep`).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- Inner radius `R = j_{ν,1}/√a` of the annulus. -/
def annR (N : ℕ) (a : ℝ) : ℝ := besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a

/-- Outer radius `R' = j_{ν,2}/√a` of the annulus. -/
def annR' (N : ℕ) (a : ℝ) : ℝ := besselZero ((N : ℝ) / 2 - 1) 2 / Real.sqrt a

/-- The annulus `A = {R < |x - y| < R'}`. -/
def annulus (N : ℕ) (a : ℝ) (y : RN N) : Set (RN N) :=
  {x | annR N a < ‖x - y‖ ∧ ‖x - y‖ < annR' N a}

/-- Function part of the representative of `c₀ ψ + ψ ⟨c, z⟩/|z|`, in the variable `z = x - y`. -/
def annP1 (N : ℕ) (a c0 : ℝ) (c z : RN N) : ℝ :=
  (c0 + ⟪c, z⟫ / ‖z‖) * (-radPhi N a ‖z‖)

/-- Gradient part of the representative of `c₀ ψ + ψ ⟨c, z⟩/|z|`. -/
def annP2 (N : ℕ) (a c0 : ℝ) (c z : RN N) : RN N :=
  (c0 + ⟪c, z⟫ / ‖z‖) • (-gradPhi N a z) +
    (-radPhi N a ‖z‖) • (‖z‖⁻¹ • (c - (⟪c, z⟫ / ‖z‖ ^ 2) • z))

/-- `v` is represented on the annulus by `c₀ ψ + ψ ⟨c, x - y⟩/|x - y|` (function and gradient,
zero outside the annulus). -/
def IsAnnRep (a : ℝ) (y : RN N) (v : Amb N) (c0 : ℝ) (c : RN N) : Prop :=
  (v.1 : RN N → ℝ) =ᵐ[volume] (annulus N a y).indicator (fun x => annP1 N a c0 c (x - y)) ∧
  (v.2 : RN N → RN N) =ᵐ[volume] (annulus N a y).indicator (fun x => annP2 N a c0 c (x - y))

lemma IsAnnRep.add {a : ℝ} {y : RN N} {v w : Amb N} {c0 c0' : ℝ} {c c' : RN N}
    (hv : IsAnnRep a y v c0 c) (hw : IsAnnRep a y w c0' c') :
    IsAnnRep a y (v + w) (c0 + c0') (c + c') := by
  refine ⟨?_, ?_⟩
  · filter_upwards [Lp.coeFn_add v.1 w.1, hv.1, hw.1] with x h1 h2 h3
    simp only [Prod.fst_add] at h1 ⊢
    rw [h1, Pi.add_apply, h2, h3]
    by_cases hx : x ∈ annulus N a y
    · simp only [indicator_of_mem hx, annP1, inner_add_left]
      ring
    · simp [indicator_of_notMem hx]
  · filter_upwards [Lp.coeFn_add v.2 w.2, hv.2, hw.2] with x h1 h2 h3
    simp only [Prod.snd_add] at h1 ⊢
    rw [h1, Pi.add_apply, h2, h3]
    by_cases hx : x ∈ annulus N a y
    · simp only [indicator_of_mem hx, annP2, inner_add_left]
      module
    · simp [indicator_of_notMem hx]

lemma IsAnnRep.smul {a : ℝ} {y : RN N} {v : Amb N} {c0 : ℝ} {c : RN N} (t : ℝ)
    (hv : IsAnnRep a y v c0 c) : IsAnnRep a y (t • v) (t * c0) (t • c) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul t v.1, hv.1] with x h1 h2
    simp only [Prod.smul_fst] at h1 ⊢
    rw [h1, Pi.smul_apply, h2]
    by_cases hx : x ∈ annulus N a y
    · simp only [indicator_of_mem hx, annP1, inner_smul_left, smul_eq_mul]
      simp only [RCLike.conj_to_real]
      ring
    · simp [indicator_of_notMem hx]
  · filter_upwards [Lp.coeFn_smul t v.2, hv.2] with x h1 h2
    simp only [Prod.smul_snd] at h1 ⊢
    rw [h1, Pi.smul_apply, h2]
    by_cases hx : x ∈ annulus N a y
    · simp only [indicator_of_mem hx, annP2, inner_smul_left, RCLike.conj_to_real]
      module
    · simp [indicator_of_notMem hx]

lemma IsAnnRep.zero (a : ℝ) (y : RN N) : IsAnnRep a y 0 0 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))] with x h1
    simp only [Prod.fst_zero] at h1 ⊢
    rw [h1]
    simp [annP1]
  · filter_upwards [Lp.coeFn_zero (RN N) 2 (volume : Measure (RN N))] with x h1
    simp only [Prod.snd_zero] at h1 ⊢
    rw [h1]
    simp [annP2]

lemma IsAnnRep.congr {a : ℝ} {y : RN N} {v : Amb N} {c0 c0' : ℝ} {c c' : RN N}
    (hv : IsAnnRep a y v c0 c) (h0 : c0 = c0') (h : c = c') : IsAnnRep a y v c0' c' :=
  h0 ▸ h ▸ hv

/-- Representatives of linear combinations of `ψ, ψ⟨b i, ·⟩/|·|`. -/
lemma IsAnnRep.sum_family {a : ℝ} {y : RN N} {ψ : Amb N} {w : Fin N → Amb N} (b : Fin N → RN N)
    (hψ : IsAnnRep a y ψ 1 0) (hw : ∀ i, IsAnnRep a y (w i) 0 (b i))
    (g : Option (Fin N) → ℝ) :
    IsAnnRep a y (∑ o, g o • o.elim ψ w) (g none) (∑ i, g (some i) • b i) := by
  rw [Fintype.sum_option]
  have hs : ∀ s : Finset (Fin N),
      IsAnnRep a y (∑ i ∈ s, g (some i) • w i) 0 (∑ i ∈ s, g (some i) • b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using IsAnnRep.zero a y
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (((hw j).smul (g (some j))).add ih).congr (by ring) rfl
  exact ((hψ.smul (g none)).add (hs Finset.univ)).congr (by ring) (by simp)

lemma isOpen_annulus (a : ℝ) (y : RN N) : IsOpen (annulus N a y) := by
  have hc : Continuous fun x : RN N => ‖x - y‖ := by fun_prop
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

/-- `Φ` is negative on the annulus. -/
lemma radPhi_neg_annulus (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) {r : ℝ} (h1 : annR N a < r)
    (h2 : r < annR' N a) : radPhi N a r < 0 := by
  have hν := hN_nu hN
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hR : 0 < annR N a := div_pos (besselZero_props hν).1 hsa
  have hr : 0 < r := hR.trans h1
  rw [radPhi_eq_bessel hN ha hr]
  refine mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hr _) (besselJ_neg_between hν ?_ ?_)
  · calc besselZero ((N : ℝ) / 2 - 1) 1 = Real.sqrt a * annR N a := by
          simp only [annR]; field_simp
      _ < Real.sqrt a * r := by gcongr
  · calc Real.sqrt a * r < Real.sqrt a * annR' N a := by gcongr
      _ = besselZero ((N : ℝ) / 2 - 1) 2 := by simp only [annR']; field_simp

/-- Restriction to one of two disjoint open pieces preserves the form domain. -/
lemma restrictTo_mem_H_of_union {A S : Set (RN N)} (hA : IsOpen A) (hS : IsOpen S)
    (hAS : Disjoint A S) {p : Amb N} (hp : p ∈ H (A ∪ S)) : restrictTo A p ∈ H A := by
  classical
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  refine mem_H_of_tendsto (fun k => ?_) (restrictTo_tendsto hA.measurableSet hq)
  obtain ⟨φ, hφ, hφc, hφs, hqk⟩ := eq_testPair (hqT k)
  rw [hqk]
  set D : Bool → Set (RN N) := fun b => if b then A else S
  have hD : ∀ b, IsOpen (D b) := by intro b; cases b <;> simp [D, hA, hS]
  have hdisj : Pairwise (Disjoint on D) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [D, Function.onFun, hAS.symm]
  have hF : tsupport φ ⊆ ⋃ i ∈ ({true, false} : Finset Bool), D i := by
    intro x hx
    rcases hφs hx with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton, mem_iUnion, exists_prop]
      exact ⟨true, Or.inl rfl, by simpa [D] using h⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, mem_iUnion, exists_prop]
      exact ⟨false, Or.inr rfl, by simpa [D] using h⟩
  obtain ⟨c1, c2, c3⟩ := testFn_restrict hD hdisj hφ hφc hF true
  have hDt : D true = A := rfl
  rw [hDt] at c1 c2 c3
  have hgrad : ∀ x, gradient (A.indicator φ) x = A.indicator (gradient φ) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      refine Filter.EventuallyEq.gradient_eq ?_
      filter_upwards [hA.mem_nhds hx] with z hz
      exact indicator_of_mem hz φ
    · rw [indicator_of_notMem hx]
      have hxt : x ∉ tsupport (A.indicator φ) := fun h => hx (c3 h)
      rw [(notMem_tsupport_iff_eventuallyEq.mp hxt).gradient_eq]
      exact gradient_const x 0
  have key : restrictTo A (testPair φ hφ hφc) = testPair (A.indicator φ) c1 c2 := by
    refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
    · filter_upwards [restrictTo_fst_ae hA.measurableSet (testPair φ hφ hφc),
        MemLp.coeFn_toLp (memLp_of_testFun hφ hφc), MemLp.coeFn_toLp (memLp_of_testFun c1 c2)]
        with x h1 h2 h3
      simp only [testPair] at h1 h2 h3 ⊢
      rw [h1, h3]
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    · filter_upwards [restrictTo_snd_ae hA.measurableSet (testPair φ hφ hφc),
        MemLp.coeFn_toLp (memLp_gradient_of_testFun hφ hφc),
        MemLp.coeFn_toLp (memLp_gradient_of_testFun c1 c2)] with x h1 h2 h3
      simp only [testPair] at h1 h2 h3 ⊢
      rw [h1, h3, hgrad]
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [key]
  exact testGraph_subset_H _ (testPair_mem c1 c2 c3)

lemma besselEntire_nonneg_of_le (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) {z : RN N}
    (hz : ‖z‖ ≤ annR N a) : 0 ≤ besselEntire N a z := by
  have hR : 0 < annR N a := div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  have hc : Continuous (besselEntire N a) :=
    continuousOn_univ.mp (besselEntire_analytic hN ha.le).continuousOn
  have hcl : IsClosed {x : RN N | 0 ≤ besselEntire N a x} := isClosed_le continuous_const hc
  have hsub : ball (0 : RN N) (annR N a) ⊆ {x | 0 ≤ besselEntire N a x} := fun x hx =>
    (besselEntire_pos hN ha (by
      change ‖x‖ < annR N a
      simpa only [mem_ball, dist_zero_right] using hx)).le
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_ball _ hR.ne'] at this
  exact this (by simpa using hz)

lemma hasGradientAt_shift (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (y x : RN N) :
    HasGradientAt (fun x => -besselEntire N a (x - y)) (-gradPhi N a (x - y)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have := (((hasGradientAt_besselEntire hN ha (x - y)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const y)).neg
  convert this using 1 <;> (try rfl)
  ext w
  change inner ℝ (-gradPhi N a (x - y)) w = -inner ℝ (gradPhi N a (x - y)) w
  exact inner_neg_left _ _

lemma contDiff_besselEntire (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (besselEntire N a) :=
  contDiffOn_univ.mp ((besselEntire_analytic hN ha).contDiffOn uniqueDiffOn_univ)

/-- **The function `ψ`.** -/
theorem exists_annulus_psi (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    ∃ ψ : Amb N, ψ ∈ H (annulus N a y) ∧ IsAnnRep a y ψ 1 0 := by
  have hν := hN_nu hN
  obtain ⟨-, -, -, hz2, -, -⟩ := besselZero_props hν
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set R := annR N a with hRdef
  set R' := annR' N a with hR'def
  have hR : 0 < R := div_pos (besselZero_props hν).1 hsa
  have hRR : R < R' := div_lt_div_of_pos_right (besselZero_props hν).2.1 hsa
  set A := annulus N a y with hAdef
  have hAo : IsOpen A := isOpen_annulus a y
  have hAm : MeasurableSet A := hAo.measurableSet
  -- a cut-off of `-Φ(· - y)`
  obtain ⟨χ, hχs, hχc, hχE, U, hU, hKU, hU1⟩ := exists_cutoff (isCompact_closedBall y R')
    isOpen_ball (closedBall_subset_ball (by linarith : R' < R' + 1))
  have hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => -besselEntire N a (x - y)) :=
    ((contDiff_besselEntire hN ha.le).comp (contDiff_id.sub contDiff_const)).neg
  set F : RN N → ℝ := fun x => χ x * (-besselEntire N a (x - y)) with hFdef
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hχs.mul hΦs
  have hFc : HasCompactSupport F := hχc.mul_right
  have hFE : tsupport F ⊆ ball y (R' + 1) := tsupport_mul_subset_left.trans hχE
  set v := testPair F hFs hFc with hvdef
  have hvH : v ∈ H (ball y (R' + 1)) := testGraph_subset_H _ (testPair_mem hFs hFc hFE)
  have hE : IsAdmissible (ball y (R' + 1)) :=
    ⟨isOpen_ball, nonempty_ball.mpr (by linarith), isBounded_ball⟩
  have hv1 : (v.1 : RN N → ℝ) =ᵐ[volume] F := MemLp.coeFn_toLp (memLp_of_testFun hFs hFc)
  have hv2 : (v.2 : RN N → RN N) =ᵐ[volume] gradient F :=
    MemLp.coeFn_toLp (memLp_gradient_of_testFun hFs hFc)
  have hvc : IsContRep (ball y (R' + 1)) v F := ⟨hFs.continuous.continuousOn, ae_restrict_of_ae hv1⟩
  have hpos := posPart_mem_H_posSign hE hvH hvc
  -- splitting the positivity set
  have hcn : Continuous fun x : RN N => ‖x - y‖ := by fun_prop
  set S := posSign (ball y (R' + 1)) F ∩ {x | R' < ‖x - y‖}
  have hS : IsOpen S :=
    (isOpen_posSign isOpen_ball hFs.continuous.continuousOn).inter (isOpen_lt continuous_const hcn)
  have hAS : Disjoint A S := by
    rw [Set.disjoint_left]
    intro x hxA hxS
    exact absurd hxS.2 (not_lt.mpr hxA.2.le)
  have hAU : ∀ x ∈ A, x ∈ U := fun x hx => hKU (by
    rw [mem_closedBall, dist_eq_norm]; exact hx.2.le)
  have hFA : ∀ x ∈ A, F x = -radPhi N a ‖x - y‖ := fun x hx => by
    simp only [F, hU1 x (hAU x hx), one_mul, besselEntire_eq_radPhi]
  have hsub : posSign (ball y (R' + 1)) F ⊆ A ∪ S := by
    rintro x ⟨hxE, hxF⟩
    by_cases h : R' < ‖x - y‖
    · exact Or.inr ⟨⟨hxE, hxF⟩, h⟩
    left
    push_neg at h
    have hχ1 : χ x = 1 := hU1 x (hKU (by rw [mem_closedBall, dist_eq_norm]; exact h))
    have hF' : 0 < -besselEntire N a (x - y) := by
      simpa [F, hχ1] using hxF
    refine ⟨?_, lt_of_le_of_ne h ?_⟩
    · by_contra hle
      push_neg at hle
      have := besselEntire_nonneg_of_le hN ha hle
      linarith
    · intro heq
      rw [besselEntire_eq_radPhi, heq] at hF'
      have h0 : radPhi N a R' = 0 := radPhi_zero ha hz2
      linarith
  refine ⟨restrictTo A (posPart v),
    restrictTo_mem_H_of_union hAo hS hAS (H_mono hsub hpos), ?_, ?_⟩
  · filter_upwards [restrictTo_fst_ae hAm (posPart v), posPart_fst_ae' v, hv1] with x h1 h2 h3
    rw [h1]
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2, h3, hFA x hx]
      have := radPhi_neg_annulus hN ha hx.1 hx.2
      rw [max_eq_left (by linarith)]
      simp [annP1]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  · filter_upwards [restrictTo_snd_ae hAm (posPart v), posPart_snd_ae_ite v, hv1, hv2]
      with x h1 h2 h3 h4
    rw [h1]
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2, h3, h4, hFA x hx]
      have := radPhi_neg_annulus hN ha hx.1 hx.2
      rw [if_pos (by linarith), one_smul]
      have hloc : F =ᶠ[𝓝 x] fun x => -besselEntire N a (x - y) := by
        filter_upwards [hU.mem_nhds (hAU x hx)] with z hz
        simp only [F, hU1 z hz, one_mul]
      rw [hloc.gradient_eq, (hasGradientAt_shift hN ha.le y x).gradient]
      simp [annP2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]

lemma hasGradientAt_inner_div_norm (c y x : RN N) (hx : x ≠ y) :
    HasGradientAt (fun x => ⟪c, x - y⟫ / ‖x - y‖)
      (‖x - y‖⁻¹ • (c - (⟪c, x - y⟫ / ‖x - y‖ ^ 2) • (x - y))) x := by
  have hz : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have h1 : HasFDerivAt (fun x => ⟪c, x - y⟫)
      ((innerSL ℝ c).comp (ContinuousLinearMap.id ℝ (RN N))) x :=
    (innerSL ℝ c).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)
  have h2 := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y).norm_sq
  simp only [id] at h2
  have h3 := h2.sqrt (by positivity)
  have hsq : Real.sqrt (‖x - y‖ ^ 2) = ‖x - y‖ := Real.sqrt_sq (norm_nonneg _)
  have h4 := (hasDerivAt_inv (by rw [hsq]; exact hz.ne')).comp_hasFDerivAt x h3
  have h5 := h1.mul h4
  rw [hasGradientAt_iff_hasFDerivAt]
  have heq : (fun x => ⟪c, x - y⟫ / ‖x - y‖) =
      (fun x => ⟪c, x - y⟫) * ((fun t : ℝ => t⁻¹) ∘ fun x => Real.sqrt (‖x - y‖ ^ 2)) := by
    funext z
    simp [Real.sqrt_sq (norm_nonneg _), div_eq_mul_inv]
  rw [heq]
  convert h5 using 1
  ext w
  simp only [hsq, InnerProductSpace.toDual_apply_apply, inner_smul_left, inner_sub_left,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul, comp_apply,
    RCLike.conj_to_real]
  field_simp
  ring

/-- **The functions `ψ ⟨c, x - y⟩/|x - y|`.** -/
theorem exists_annulus_psi_mul (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {ψ : Amb N}
    (hψ : ψ ∈ H (annulus N a y)) (hψr : IsAnnRep a y ψ 1 0) (c : RN N) :
    ∃ w : Amb N, w ∈ H (annulus N a y) ∧ IsAnnRep a y w 0 c := by
  have hν := hN_nu hN
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set R := annR N a with hRdef
  set R' := annR' N a with hR'def
  have hR : 0 < R := div_pos (besselZero_props hν).1 hsa
  set A := annulus N a y with hAdef
  have hcn : Continuous fun x : RN N => ‖x - y‖ := by fun_prop
  set K1 : Set (RN N) := {x | R ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ R'}
  have hK1 : IsCompact K1 := (isCompact_closedBall y R').of_isClosed_subset
    ((isClosed_le continuous_const hcn).inter (isClosed_le hcn continuous_const))
    (fun x hx => by rw [mem_closedBall, dist_eq_norm]; exact hx.2)
  set E1 : Set (RN N) := {x | R / 2 < ‖x - y‖}
  have hE1 : IsOpen E1 := isOpen_lt continuous_const hcn
  have hK1E1 : K1 ⊆ E1 := fun x hx => by
    simp only [E1, mem_setOf_eq]; linarith [hx.1]
  have hE1ne : ∀ x ∈ E1, x ≠ y := fun x hx h => by
    simp only [E1, mem_setOf_eq, h, sub_self, norm_zero] at hx; linarith
  obtain ⟨χ, hχs, hχc, hχE, U, hU, hKU, hU1⟩ := exists_cutoff hK1 hE1 hK1E1
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => χ x * ⟪c, x - y⟫) :=
    hχs.mul (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))
  have hden : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ‖x - y‖) E1 := fun x hx =>
    ((contDiffAt_norm ℝ (sub_ne_zero.mpr (hE1ne x hx))).comp x
      (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt
  set h : RN N → ℝ := fun x => χ x * ⟪c, x - y⟫ / ‖x - y‖ with hhdef
  have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h :=
    contDiff_div_of_tsupport hnum hE1 (tsupport_mul_subset_left.trans hχE) hden
      (fun x hx => (norm_pos_iff.mpr (sub_ne_zero.mpr (hE1ne x hx))).ne')
  have hhc : HasCompactSupport h := hχc.mono fun x hx h0 => hx (by simp [h, h0])
  obtain ⟨hg, C, -, hC⟩ := exists_bound_cutoff hhs hhc
  refine ⟨Mpair hhs.continuous hg hC ψ, Mpair_mem_H_self hhs.continuous hg hC hhs hψ, ?_, ?_⟩
  · have hAK : ∀ x ∈ A, x ∈ K1 := fun x hx => ⟨hx.1.le, hx.2.le⟩
    have hloc : ∀ x ∈ A, h =ᶠ[𝓝 x] fun x => ⟪c, x - y⟫ / ‖x - y‖ := fun x hx => by
      filter_upwards [hU.mem_nhds (hKU (hAK x hx))] with z hz
      simp [h, hU1 z hz]
    have hval : ∀ x ∈ A, h x = ⟪c, x - y⟫ / ‖x - y‖ := fun x hx => (hloc x hx).self_of_nhds
    filter_upwards [Mpair_fst_ae hhs.continuous hg hC ψ, hψr.1] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx, hval x hx]
      simp [annP1]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  · have hAK : ∀ x ∈ A, x ∈ K1 := fun x hx => ⟨hx.1.le, hx.2.le⟩
    have hloc : ∀ x ∈ A, h =ᶠ[𝓝 x] fun x => ⟪c, x - y⟫ / ‖x - y‖ := fun x hx => by
      filter_upwards [hU.mem_nhds (hKU (hAK x hx))] with z hz
      simp [h, hU1 z hz]
    have hval : ∀ x ∈ A, h x = ⟪c, x - y⟫ / ‖x - y‖ := fun x hx => (hloc x hx).self_of_nhds
    have hgr : ∀ x ∈ A, gradient h x =
        ‖x - y‖⁻¹ • (c - (⟪c, x - y⟫ / ‖x - y‖ ^ 2) • (x - y)) := fun x hx => by
      rw [(hloc x hx).gradient_eq,
        (hasGradientAt_inner_div_norm c y x (hE1ne x (hK1E1 (hAK x hx)))).gradient]
    filter_upwards [Mpair_snd_ae hhs.continuous hg hC ψ, hψr.1, hψr.2] with x h1 h2 h3
    rw [h1, h2, h3]
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, hval x hx, hgr x hx]
      simp [annP1, annP2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
      simp

end FourthRatio

end

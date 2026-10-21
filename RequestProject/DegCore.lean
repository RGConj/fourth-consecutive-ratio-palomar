module

public import RequestProject.DegQp

/-!
# No smooth deformation of `qdir` into `-qdir`

Let `U(y, s)` be a smooth unit-vector-valued map on `(ℝ³ ∖ 0) × ℝ` with `U(·, s) = qdir` for
`s ≤ -1` and `U(·, s) = -qdir` for `s ≥ 2`.  We show that this is impossible.

The maps `f_ρ(y) = Φ(y) U(y, ρ(Φ(y)))` (`Φ = |Qp|`) all have Jacobian determinant bounded
independently of the reparametrisation `ρ` (the `ρ'` contribution is a rank-one perturbation
which does not change the determinant).  Comparing, via the null Lagrangian property, a
reparametrisation switching near `Φ = 1` with one switching near `Φ = 2` shows that
`∫_{1<Φ<2} det DQp = 0`, contradicting `det DQp ≥ 0` (and `> 0` somewhere).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio.Degree

/-- The deformation `f_ρ(y) = Φ(y) U(y, ρ(Φ(y)))`. -/
def fdef (U : E3 × ℝ → E3) (ρ : ℝ → ℝ) (y : E3) : E3 := Phi y • U (y, ρ (Phi y))

/-- The matrix of the "frozen" derivative of `y ↦ Φ(y) U(y, s)`. -/
def Amat (U : E3 × ℝ → E3) (y : E3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun b a => fderiv ℝ Phi y (ebas a) * U (y, s) b +
    Phi y * fderiv ℝ U (y, s) (ebas a, 0) b

lemma det_add_rank_one (A : Matrix (Fin 3) (Fin 3) ℝ) (u w z : Fin 3 → ℝ)
    (hA : ∀ a, u 0 * A 0 a + u 1 * A 1 a + u 2 * A 2 a = z a)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 = 0) :
    (Matrix.of fun b a => A b a + w b * z a).det = A.det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  rw [← hA 0, ← hA 1, ← hA 2]
  linear_combination (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
    A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) * hw

lemma jac_neg (h : E3 → E3) (y : E3) : jac (fun x => -h x) y = -jac h y := by
  have : (fun x => -h x) = -h := rfl
  simp only [jac, pd, this, fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply, PiLp.neg_apply, Matrix.det_fin_three,
    Matrix.of_apply]
  ring

lemma jac_congr {f g : E3 → E3} {y : E3} (h : f =ᶠ[𝓝 y] g) : jac f y = jac g y := by
  simp only [jac, pd_congr h]

/-- A unit-vector-valued map is orthogonal to its derivative. -/
lemma inner_fderiv_eq_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : X → E3} {S : Set X} (hS : IsOpen S) (h1 : ∀ q ∈ S, ‖U q‖ = 1) {p : X} (hp : p ∈ S)
    (hd : DifferentiableAt ℝ U p) (v : X) : ⟪U p, fderiv ℝ U p v⟫ = 0 := by
  have hg := hd.hasFDerivAt.inner ℝ hd.hasFDerivAt
  have hconst : (fun q => ⟪U q, U q⟫) =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    rw [real_inner_self_eq_norm_sq, h1 q hq]; norm_num
  have h0 := hg.unique ((hasFDerivAt_const (1 : ℝ) p).congr_of_eventuallyEq hconst)
  have := congrArg (fun L => L v) h0
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.zero_apply] at this
  have h2 : ⟪U p, fderiv ℝ U p v⟫ = ⟪fderiv ℝ U p v, U p⟫ := real_inner_comm _ _
  linarith

/-- The Jacobian of `f_ρ` equals the determinant of the frozen derivative. -/
lemma jac_fdef {U : E3 × ℝ → E3} (hU : ContDiffOn ℝ 2 U {p | p.1 ≠ 0})
    (hU1 : ∀ p : E3 × ℝ, p.1 ≠ 0 → ‖U p‖ = 1) {ρ : ℝ → ℝ} (hρ : Differentiable ℝ ρ)
    {y : E3} (hy : y ≠ 0) : jac (fdef U ρ) y = (Amat U y (ρ (Phi y))).det := by
  have hS : IsOpen {p : E3 × ℝ | p.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  set p : E3 × ℝ := (y, ρ (Phi y)) with hp
  have hpS : p ∈ {p : E3 × ℝ | p.1 ≠ 0} := hy
  have hUd : DifferentiableAt ℝ U p :=
    (hU.contDiffAt (hS.mem_nhds hpS)).differentiableAt (by norm_num)
  have hPhi : HasFDerivAt Phi (fderiv ℝ Phi y) y :=
    ((contDiffAt_Phi hy (n := 1)).differentiableAt (by norm_num)).hasFDerivAt
  have hrho := (hρ (Phi y)).hasDerivAt.comp_hasFDerivAt y hPhi
  have hin := (hasFDerivAt_id y).prodMk hrho
  have hcomp := hUd.hasFDerivAt.comp y hin
  have hf : HasFDerivAt (fdef U ρ) (Phi y • ((fderiv ℝ U p).comp
      ((ContinuousLinearMap.id ℝ E3).prod (deriv ρ (Phi y) • fderiv ℝ Phi y))) +
      (fderiv ℝ Phi y).smulRight (U p)) y := hPhi.smul hcomp
  have hfd : DifferentiableAt ℝ (fdef U ρ) y := hf.differentiableAt
  have key : ∀ a b, pd (fdef U ρ) y a b = Amat U y (ρ (Phi y)) b a +
      (Phi y * deriv ρ (Phi y) * fderiv ℝ U p (0, 1) b) * fderiv ℝ Phi y (ebas a) := by
    intro a b
    have e : pd (fdef U ρ) y a b = (Phi y • ((fderiv ℝ U p).comp ((ContinuousLinearMap.id ℝ E3).prod
        (deriv ρ (Phi y) • fderiv ℝ Phi y))) + (fderiv ℝ Phi y).smulRight (U p)) (ebas a) b := by
      simp only [pd]
      rw [hf.fderiv]
    rw [e]
    have hsplit : ((ebas a, deriv ρ (Phi y) * fderiv ℝ Phi y (ebas a)) : E3 × ℝ) =
        (ebas a, 0) + (deriv ρ (Phi y) * fderiv ℝ Phi y (ebas a)) • ((0 : E3), (1 : ℝ)) := by
      ext <;> simp
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
    rw [hsplit, map_add, map_smul]
    simp only [Amat, Matrix.of_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp]
    ring
  have hjac : jac (fdef U ρ) y = (Matrix.of fun b a => Amat U y (ρ (Phi y)) b a +
      (Phi y * deriv ρ (Phi y) * fderiv ℝ U p (0, 1) b) * fderiv ℝ Phi y (ebas a)).det := by
    simp only [jac]
    congr 1
    ext b a
    simp [key]
  rw [hjac]
  have horth : ∀ v, ⟪U p, fderiv ℝ U p v⟫ = 0 := fun v =>
    inner_fderiv_eq_zero hS (fun q hq => hU1 q hq) hpS hUd v
  have hnorm : U p 0 ^ 2 + U p 1 ^ 2 + U p 2 ^ 2 = 1 := by
    rw [← norm_sq_E3, hU1 p hy]; norm_num
  apply det_add_rank_one _ (fun b => U p b)
  · intro a
    have := horth (ebas a, 0)
    rw [inner_E3] at this
    simp only [Amat, Matrix.of_apply, ← hp]
    linear_combination (fderiv ℝ Phi y (ebas a)) * hnorm + Phi y * this
  · have := horth (0, 1)
    rw [inner_E3] at this
    linear_combination (Phi y * deriv ρ (Phi y)) * this

lemma contDiffAt_fdef {U : E3 × ℝ → E3} (hU : ContDiffOn ℝ 2 U {p | p.1 ≠ 0}) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 ρ) {y : E3} (hy : y ≠ 0) : ContDiffAt ℝ 2 (fdef U ρ) y := by
  have hS : IsOpen {p : E3 × ℝ | p.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hUat : ContDiffAt ℝ 2 U (y, ρ (Phi y)) := hU.contDiffAt (hS.mem_nhds hy)
  have hin : ContDiffAt ℝ 2 (fun x => (x, ρ (Phi x))) y :=
    contDiffAt_id.prodMk (hρ.contDiffAt.comp y (contDiffAt_Phi hy))
  exact (contDiffAt_Phi hy).smul (hUat.comp y hin)

lemma continuousOn_det_Amat {U : E3 × ℝ → E3} (hU : ContDiffOn ℝ 2 U {p | p.1 ≠ 0}) :
    ContinuousOn (fun p : E3 × ℝ => (Amat U p.1 p.2).det) {p | p.1 ≠ 0} := by
  have hS : IsOpen {p : E3 × ℝ | p.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hPhiOn : ContDiffOn ℝ 2 Phi {y : E3 | y ≠ 0} := fun y hy =>
    (contDiffAt_Phi hy).contDiffWithinAt
  have hdPhi : ContinuousOn (fderiv ℝ Phi) {y : E3 | y ≠ 0} :=
    hPhiOn.continuousOn_fderiv_of_isOpen isOpen_ne (by norm_num)
  have hdU : ContinuousOn (fderiv ℝ U) {p : E3 × ℝ | p.1 ≠ 0} :=
    hU.continuousOn_fderiv_of_isOpen hS (by norm_num)
  have hfst : MapsTo Prod.fst {p : E3 × ℝ | p.1 ≠ 0} {y : E3 | y ≠ 0} := fun p hp => hp
  have e1 : ∀ a, ContinuousOn (fun p : E3 × ℝ => fderiv ℝ Phi p.1 (ebas a)) {p | p.1 ≠ 0} :=
    fun a => ((hdPhi.comp continuous_fst.continuousOn hfst).clm_apply continuousOn_const)
  have e2 : ∀ b, ContinuousOn (fun p : E3 × ℝ => U p b) {p | p.1 ≠ 0} := fun b =>
    (EuclideanSpace.proj b : E3 →L[ℝ] ℝ).continuous.comp_continuousOn hU.continuousOn
  have e3 : ContinuousOn (fun p : E3 × ℝ => Phi p.1) {p | p.1 ≠ 0} :=
    (continuous_Phi.comp continuous_fst).continuousOn
  have e4 : ∀ a b, ContinuousOn (fun p : E3 × ℝ => fderiv ℝ U p (ebas a, 0) b) {p | p.1 ≠ 0} :=
    fun a b => (EuclideanSpace.proj b : E3 →L[ℝ] ℝ).continuous.comp_continuousOn
      (hdU.clm_apply continuousOn_const)
  have hent : ∀ b a, ContinuousOn (fun p : E3 × ℝ => Amat U p.1 p.2 b a) {p | p.1 ≠ 0} := by
    intro b a
    simp only [Amat, Matrix.of_apply]
    exact ((e1 a).mul (e2 b)).add (e3.mul (e4 a b))
  simp only [Matrix.det_fin_three]
  have h := hent
  refine ((((((h 0 0).mul (h 1 1)).mul (h 2 2)).sub (((h 0 0).mul (h 1 2)).mul (h 2 1))).sub
    (((h 0 1).mul (h 1 0)).mul (h 2 2))).add (((h 0 1).mul (h 1 2)).mul (h 2 0))).add
    (((h 0 2).mul (h 1 0)).mul (h 2 1)) |>.sub (((h 0 2).mul (h 1 1)).mul (h 2 0))

/-! ### Switching reparametrisations -/

/-- `-1` for `t ≤ c`, `2` for `t ≥ c + δ`, smooth in between. -/
def switch (c δ t : ℝ) : ℝ := -1 + 3 * Real.smoothTransition ((t - c) / δ)

lemma switch_contDiff (c δ : ℝ) : ContDiff ℝ 2 (switch c δ) := by
  unfold switch
  exact contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const δ)))

lemma switch_mem (c δ t : ℝ) : switch c δ t ∈ Icc (-1 : ℝ) 2 := by
  have h0 := Real.smoothTransition.nonneg ((t - c) / δ)
  have h1 := Real.smoothTransition.le_one ((t - c) / δ)
  constructor <;> simp only [switch] <;> linarith

lemma switch_of_le {c δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c) : switch c δ t = -1 := by
  simp only [switch]
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
  ring

lemma switch_of_ge {c δ t : ℝ} (hδ : 0 < δ) (ht : c + δ ≤ t) : switch c δ t = 2 := by
  simp only [switch]
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith))]
  ring

lemma fdef_eq_Qp {U : E3 × ℝ → E3} (hUa : ∀ y : E3, y ≠ 0 → ∀ s ≤ -1, U (y, s) = qdir y)
    {ρ : ℝ → ℝ} {y : E3} (hy : y ≠ 0) (h : ρ (Phi y) ≤ -1) : fdef U ρ y = Qp y := by
  simp only [fdef, hUa y hy _ h, Phi_mul_qdir hy]

lemma fdef_eq_neg_Qp {U : E3 × ℝ → E3} (hUb : ∀ y : E3, y ≠ 0 → ∀ s, 2 ≤ s → U (y, s) = -qdir y)
    {ρ : ℝ → ℝ} {y : E3} (hy : y ≠ 0) (h : 2 ≤ ρ (Phi y)) : fdef U ρ y = -Qp y := by
  simp only [fdef, hUb y hy _ h, smul_neg, Phi_mul_qdir hy]

lemma Phi_zero : Phi 0 = 0 := by simp [Phi, Qp, mk3]

lemma continuousOn_jac_Qp : ContinuousOn (jac Qp) {y : E3 | y ≠ 0} := by
  have hc : ContinuousOn (fun y : E3 => 8 * (y 0 ^ 2 + y 1 ^ 2) * (‖y‖ + y 2 ^ 2 / ‖y‖))
      {y : E3 | y ≠ 0} := by
    have c := fun i => (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.continuousOn
      (s := {y : E3 | y ≠ 0})
    refine (continuousOn_const.mul (((c 0).pow 2).add ((c 1).pow 2))).mul
      (continuous_norm.continuousOn.add (((c 2).pow 2).div continuous_norm.continuousOn ?_))
    intro y hy; exact norm_ne_zero_iff.2 hy
  exact hc.congr fun y hy => jac_Qp hy

lemma jac_Qp_le {y : E3} (hy : y ≠ 0) (h2 : Phi y ≤ 2) : jac Qp y ≤ 128 := by
  rw [jac_Qp hy]
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hn := norm_sq_E3 y
  have hr2 : ‖y‖ ≤ 2 := by nlinarith [norm_sq_le_Phi y]
  have hq : y 2 ^ 2 / ‖y‖ ≤ ‖y‖ := by
    rw [div_le_iff₀ hr]; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  have ha : y 0 ^ 2 + y 1 ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [sq_nonneg (y 2)]
  have hq0 : 0 ≤ y 2 ^ 2 / ‖y‖ := by positivity
  calc 8 * (y 0 ^ 2 + y 1 ^ 2) * (‖y‖ + y 2 ^ 2 / ‖y‖) ≤ 8 * ‖y‖ ^ 2 * (2 * ‖y‖) := by
        have h0 : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
        have h1 : ‖y‖ + y 2 ^ 2 / ‖y‖ ≤ 2 * ‖y‖ := by linarith
        have h3 : 0 ≤ ‖y‖ + y 2 ^ 2 / ‖y‖ := by positivity
        calc 8 * (y 0 ^ 2 + y 1 ^ 2) * (‖y‖ + y 2 ^ 2 / ‖y‖)
            ≤ 8 * ‖y‖ ^ 2 * (‖y‖ + y 2 ^ 2 / ‖y‖) := by gcongr
          _ ≤ 8 * ‖y‖ ^ 2 * (2 * ‖y‖) := by gcongr
    _ ≤ 8 * 2 ^ 2 * (2 * 2) := by gcongr
    _ = 128 := by norm_num

/-- **No smooth deformation of `qdir` into `-qdir`.** -/
theorem no_smooth_deformation (U : E3 × ℝ → E3) (hU : ContDiffOn ℝ 2 U {p | p.1 ≠ 0})
    (hU1 : ∀ p : E3 × ℝ, p.1 ≠ 0 → ‖U p‖ = 1)
    (hUa : ∀ y : E3, y ≠ 0 → ∀ s ≤ -1, U (y, s) = qdir y)
    (hUb : ∀ y : E3, y ≠ 0 → ∀ s, 2 ≤ s → U (y, s) = -qdir y) : False := by
  set Ω : Set E3 := {y | 1 < Phi y ∧ Phi y < 2} with hΩdef
  set Kc : Set E3 := {y | 1 ≤ Phi y ∧ Phi y ≤ 2} with hKcdef
  have hne : ∀ {y : E3}, 1 ≤ Phi y → y ≠ 0 := by
    intro y h h0; subst h0; rw [Phi_zero] at h; norm_num at h
  have hΩo : IsOpen Ω :=
    (isOpen_lt continuous_const continuous_Phi).inter (isOpen_lt continuous_Phi continuous_const)
  have hKc : IsCompact Kc := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_Phi).inter
        (isClosed_le continuous_Phi continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := 2)).subset fun y hy => ?_
      have := norm_sq_le_Phi y
      simp only [Metric.mem_closedBall, dist_zero_right]
      nlinarith [hy.2, norm_nonneg y]
  have hΩK : Ω ⊆ Kc := fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hKcfin : volume Kc < ⊤ := hKc.measure_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Kc ×ˢ Icc (-1 : ℝ) 2, ‖(Amat U p.1 p.2).det‖ ≤ C :=
    (hKc.prod isCompact_Icc).exists_bound_of_continuousOn
      ((continuousOn_det_Amat hU).mono fun p hp => hne hp.1.1)
  have hJint : IntegrableOn (jac Qp) Ω :=
    ((continuousOn_jac_Qp.mono fun y (hy : y ∈ Kc) => hne hy.1).integrableOn_compact hKc).mono_set hΩK
  -- the main estimate for one reparametrisation scale
  have main : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → 2 * ∫ y in Ω, jac Qp y ≤
      (256 + 2 * C) * volume.real (Ω ∩ {y | Phi y ≤ 1 + 2 * δ ∨ 2 - 2 * δ ≤ Phi y}) := by
    intro δ hδ hδ4
    set ρ₁ := switch (1 + δ) δ
    set ρ₂ := switch (2 - 2 * δ) δ
    set f₁ := fdef U ρ₁
    set f₂ := fdef U ρ₂
    set T : Set E3 := {y | Phi y ≤ 1 + 2 * δ ∨ 2 - 2 * δ ≤ Phi y}
    have hf₁ : ContDiffOn ℝ 2 f₁ Ω := fun y hy =>
      (contDiffAt_fdef hU (switch_contDiff _ _) (hne hy.1.le)).contDiffWithinAt
    have hf₂ : ContDiffOn ℝ 2 f₂ Ω := fun y hy =>
      (contDiffAt_fdef hU (switch_contDiff _ _) (hne hy.1.le)).contDiffWithinAt
    -- null Lagrangian
    set K : Set E3 := {y | 1 + δ ≤ Phi y ∧ Phi y ≤ 2 - δ}
    have hKcomp : IsCompact K := hKc.of_isClosed_subset
      ((isClosed_le continuous_const continuous_Phi).inter
        (isClosed_le continuous_Phi continuous_const))
      (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have hKΩ : K ⊆ Ω := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hNL : ∫ y in Ω, (jac f₁ y - jac f₂ y) = 0 := by
      refine null_lagrangian hΩo hKcomp hKΩ hf₁ hf₂ fun y hy => ?_
      show fdef U (switch (1 + δ) δ) y = fdef U (switch (2 - 2 * δ) δ) y
      have hy0 := hne hy.1.1.le
      by_cases h1 : Phi y < 1 + δ
      · rw [fdef_eq_Qp hUa hy0 (switch_of_le hδ h1.le).le,
          fdef_eq_Qp hUa hy0 (switch_of_le hδ (by linarith)).le]
      · have h2 : 2 - δ < Phi y := by
          by_contra h; exact hy.2 ⟨not_lt.1 h1, not_lt.1 h⟩
        rw [fdef_eq_neg_Qp hUb hy0 (switch_of_ge hδ (by linarith)).ge,
          fdef_eq_neg_Qp hUb hy0 (switch_of_ge hδ (by linarith)).ge]
    -- bounds on the Jacobians of the deformations
    have hjb : ∀ ρ : ℝ → ℝ, ContDiff ℝ 2 ρ → (∀ t, ρ t ∈ Icc (-1 : ℝ) 2) →
        ∀ y ∈ Kc, ‖jac (fdef U ρ) y‖ ≤ C := by
      intro ρ hρ hρm y hy
      rw [jac_fdef hU hU1 (hρ.differentiable (by norm_num)) (hne hy.1)]
      exact hC (y, ρ (Phi y)) ⟨hy, hρm _⟩
    have hjc : ∀ ρ : ℝ → ℝ, ContDiff ℝ 2 ρ → ContinuousOn (jac (fdef U ρ)) Kc := by
      intro ρ hρ
      have h1 : ContinuousOn (fun y => (Amat U y (ρ (Phi y))).det) Kc := by
        refine (continuousOn_det_Amat hU).comp (f := fun y => (y, ρ (Phi y))) ?_ ?_
        · exact (continuous_id.prodMk (hρ.continuous.comp continuous_Phi)).continuousOn
        · intro y hy; exact hne hy.1
      exact h1.congr fun y hy => jac_fdef hU hU1 (hρ.differentiable (by norm_num)) (hne hy.1)
    have hI₁ : IntegrableOn (jac f₁) Ω :=
      ((hjc _ (switch_contDiff _ _)).integrableOn_compact hKc).mono_set hΩK
    have hI₂ : IntegrableOn (jac f₂) Ω :=
      ((hjc _ (switch_contDiff _ _)).integrableOn_compact hKc).mono_set hΩK
    -- pointwise identification away from the switching layers
    have hp₁ : ∀ y ∈ Ω, 1 + 2 * δ < Phi y → jac f₁ y = -jac Qp y := by
      intro y hy h
      have hev : f₁ =ᶠ[𝓝 y] fun x => -Qp x := by
        filter_upwards [(isOpen_lt continuous_const continuous_Phi).mem_nhds h] with x hx
        exact fdef_eq_neg_Qp hUb (hne (by linarith [hx.le] : (1:ℝ) ≤ Phi x))
          (switch_of_ge hδ (by linarith [hx.le])).ge
      rw [jac_congr hev, jac_neg]
    have hp₂ : ∀ y ∈ Ω, Phi y < 2 - 2 * δ → jac f₂ y = jac Qp y := by
      intro y hy h
      have hev : f₂ =ᶠ[𝓝 y] Qp := by
        filter_upwards [((isOpen_lt continuous_const continuous_Phi).inter
          (isOpen_lt continuous_Phi continuous_const)).mem_nhds ⟨hy.1, h⟩] with x hx
        exact fdef_eq_Qp hUa (hne hx.1.le) (switch_of_le hδ hx.2.le).le
      rw [jac_congr hev]
    set g : E3 → ℝ := fun y => 2 * jac Qp y + (jac f₁ y - jac f₂ y)
    have hg1 : ∫ y in Ω, g y = 2 * ∫ y in Ω, jac Qp y := by
      simp only [g]
      rw [integral_add (f := fun y => 2 * jac Qp y) (g := fun y => jac f₁ y - jac f₂ y)
        (hJint.const_mul 2) (hI₁.sub hI₂), hNL, integral_const_mul]
      ring
    have hg2 : ∫ y in Ω, g y = ∫ y in Ω ∩ T, g y := by
      refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hΩo.measurableSet
        inter_subset_left fun y hy => ?_
      have hyΩ : y ∈ Ω := hy.1
      have hyT : y ∉ T := fun h => hy.2 ⟨hyΩ, h⟩
      simp only [T, mem_setOf_eq, not_or, not_le] at hyT
      simp only [g, hp₁ y hyΩ hyT.1, hp₂ y hyΩ hyT.2]
      ring
    have hg3 : ‖∫ y in Ω ∩ T, g y‖ ≤ (256 + 2 * C) * volume.real (Ω ∩ T) := by
      refine norm_setIntegral_le_of_norm_le_const
        ((measure_mono (inter_subset_left.trans hΩK)).trans_lt hKcfin) fun y hy => ?_
      have hyK := hΩK hy.1
      have hJ0 := jac_Qp_nonneg (hne hyK.1)
      have hJ1 := jac_Qp_le (hne hyK.1) hyK.2
      have b1 := hjb ρ₁ (switch_contDiff _ _) (switch_mem _ _) y hyK
      have b2 := hjb ρ₂ (switch_contDiff _ _) (switch_mem _ _) y hyK
      simp only [g, Real.norm_eq_abs] at b1 b2 ⊢
      rw [abs_le] at b1 b2 ⊢
      constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
    calc 2 * ∫ y in Ω, jac Qp y = ∫ y in Ω ∩ T, g y := by rw [← hg1, hg2]
      _ ≤ ‖∫ y in Ω ∩ T, g y‖ := Real.le_norm_self _
      _ ≤ _ := hg3
  -- the switching layers have vanishing measure
  set s : ℕ → Set E3 := fun n =>
    Ω ∩ {y | Phi y ≤ 1 + 2 * (1 / ((n : ℝ) + 4)) ∨ 2 - 2 * (1 / ((n : ℝ) + 4)) ≤ Phi y}
  have hs_meas : ∀ n, MeasurableSet (s n) := fun n =>
    hΩo.measurableSet.inter ((measurableSet_le continuous_Phi.measurable measurable_const).union
      (measurableSet_le measurable_const continuous_Phi.measurable))
  have hs_anti : Antitone s := by
    intro n m hnm y hy
    refine ⟨hy.1, ?_⟩
    have : 1 / ((m : ℝ) + 4) ≤ 1 / ((n : ℝ) + 4) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : n + 4 ≤ m + 4))
    rcases hy.2 with h | h
    · left; linarith
    · right; linarith
  have hs_inter : (⋂ n, s n) = ∅ := by
    ext y
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hy : y ∈ Ω
    · obtain ⟨n, hn⟩ := exists_nat_gt (2 / min (Phi y - 1) (2 - Phi y))
      refine ⟨n, fun h => ?_⟩
      have hm : 0 < min (Phi y - 1) (2 - Phi y) := lt_min (by linarith [hy.1]) (by linarith [hy.2])
      have h1 : 2 * (1 / ((n : ℝ) + 4)) < min (Phi y - 1) (2 - Phi y) := by
        rw [div_lt_iff₀ hm] at hn
        rw [mul_one_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have := min_le_left (Phi y - 1) (2 - Phi y)
      have := min_le_right (Phi y - 1) (2 - Phi y)
      rcases h.2 with h' | h' <;> linarith
    · exact ⟨0, fun h => hy h.1⟩
  have hlimE : Tendsto (fun n => volume (s n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := volume) (fun n => (hs_meas n).nullMeasurableSet)
      hs_anti ⟨0, ((measure_mono (inter_subset_left.trans hΩK)).trans_lt hKcfin).ne⟩
    rw [hs_inter, measure_empty] at this
    exact this
  have hlim : Tendsto (fun n => volume.real (s n)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlimE
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_zero] using this
  have hle : 2 * ∫ y in Ω, jac Qp y ≤ 0 := by
    have h := hlim.const_mul (256 + 2 * C)
    rw [mul_zero] at h
    exact ge_of_tendsto' h fun n => main _ (by positivity)
      (one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)]))
  -- positivity of the integral
  set c : ℝ := √(3 / 2)
  set y₀ : E3 := mk3 c 0 0
  have hc2 : c ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hcpos : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have hny₀ : ‖y₀‖ = c := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_E3]; simp [y₀, Real.sqrt_sq hcpos.le]
  have hy₀0 : y₀ ≠ 0 := by rw [← norm_pos_iff, hny₀]; exact hcpos
  have hPhiy₀ : Phi y₀ = 3 / 2 := by
    have h := Phi_sq y₀
    simp only [y₀, mk3_0, mk3_1, mk3_2] at h
    rw [hny₀] at h
    have : Phi y₀ ^ 2 = (3 / 2) ^ 2 := by rw [h]; nlinarith [hc2]
    exact (pow_left_inj₀ (Phi_nonneg _) (by norm_num) (by norm_num : (2:ℕ) ≠ 0)).1 this
  have hy₀Ω : y₀ ∈ Ω := ⟨by rw [hPhiy₀]; norm_num, by rw [hPhiy₀]; norm_num⟩
  have hJy₀ : 0 < jac Qp y₀ := by
    rw [jac_Qp hy₀0, hny₀]; simp [y₀, hc2]; positivity
  set m := jac Qp y₀
  have hev : ∀ᶠ y in 𝓝 y₀, y ∈ Ω ∧ m / 2 < jac Qp y := by
    have h1 := (continuousOn_jac_Qp.continuousAt (isOpen_ne.mem_nhds hy₀0)).eventually
      (lt_mem_nhds (by linarith : m / 2 < m))
    exact Filter.Eventually.and (hΩo.mem_nhds hy₀Ω) h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  have hpos : 0 < ∫ y in Ω, jac Qp y := by
    have hB : Metric.ball y₀ ε ⊆ Ω := fun y hy => (hball hy).1
    have h1 : ∫ y in Metric.ball y₀ ε, jac Qp y ≤ ∫ y in Ω, jac Qp y :=
      setIntegral_mono_set hJint
        (ae_restrict_of_forall_mem hΩo.measurableSet fun y hy => jac_Qp_nonneg (hne hy.1.le))
        (Eventually.of_forall hB)
    have h2 : ∫ y in Metric.ball y₀ ε, (m / 2) ≤ ∫ y in Metric.ball y₀ ε, jac Qp y :=
      setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne) (hJint.mono_set hB)
        measurableSet_ball fun y hy => (hball hy).2.le
    have h3 : 0 < ∫ y in Metric.ball y₀ ε, (m / 2) := by
      rw [setIntegral_const, smul_eq_mul]
      have : 0 < volume.real (Metric.ball y₀ ε) :=
        ENNReal.toReal_pos (Metric.measure_ball_pos volume y₀ hε).ne' measure_ball_lt_top.ne
      positivity
    linarith
  linarith

end FourthRatio.Degree

end

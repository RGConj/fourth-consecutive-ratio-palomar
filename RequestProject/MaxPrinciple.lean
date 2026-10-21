module

public import RequestProject.TruncationBasic
public import RequestProject.Derived
public import RequestProject.TestFunctions

/-!
# Positivity of the ground state

The positivity part of the connected-domain spectral statement is derived
here from the spectral theorem (`ext_spectral`), interior analyticity (`ext_analytic`), Lemma 3.1
and unique continuation:

* a weak eigenfunction with an analytic representative `f` solves `-Δf = λf` pointwise
  (`laplacian_eq_of_weak`; weak gradient identity, integration by parts and the fundamental lemma
  of the calculus of variations);
* at an interior local minimum of a `C²` function the Laplacian is nonnegative
  (`laplacian_nonneg_of_isLocalMin`);
* Hopf's boundary point lemma with the barrier `e^{-α|x-y|²} - e^{-αr²}` (`hopf_contra`) and the
  strong minimum principle for nonnegative superharmonic functions (`strong_min_principle`);
* a first eigenfunction does not change sign (otherwise its positive part would be a first
  eigenfunction vanishing on an open set), hence after a change of sign it is nonnegative,
  superharmonic and not identically zero, hence strictly positive (`ground_state_pos`).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Second-order condition at a local minimum -/

/-- At an interior local minimum of a `C²` function the Laplacian is nonnegative. -/
lemma laplacian_nonneg_of_isLocalMin {h : RN N → ℝ} {z : RN N} (hh : ContDiffAt ℝ 2 h z)
    (hmin : IsLocalMin h z) : 0 ≤ Laplacian.laplacian h z := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  refine Finset.sum_nonneg fun i _ => ?_
  set e := EuclideanSpace.basisFun (Fin N) ℝ i
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_contra hneg
  push_neg at hneg
  set g : ℝ → ℝ := fun t => h (z + t • e) with hg
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const e).const_add z
  have hline_c : Continuous (fun s : ℝ => z + s • e) := by fun_prop
  have hev : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ h y :=
    (hh.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ h (z + t • e) := by
    have := hline_c.continuousAt (x := 0) |>.tendsto
    simp only [zero_smul, add_zero] at this
    exact this.eventually hev
  have hdg : deriv g =ᶠ[𝓝 0] fun t => fderiv ℝ h (z + t • e) e := by
    filter_upwards [hev'] with t ht
    have := ht.hasFDerivAt.comp_hasDerivAt t (hline t)
    exact this.deriv
  have hfd : DifferentiableAt ℝ (fderiv ℝ h) z :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hdd : HasDerivAt (fun t : ℝ => fderiv ℝ h (z + t • e) e)
      (fderiv ℝ (fderiv ℝ h) z e e) 0 := by
    have h1 : HasFDerivAt (fun y => fderiv ℝ h y e)
        ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ h) z)) z :=
      (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp z hfd.hasFDerivAt
    have hz : z + (0 : ℝ) • e = z := by simp
    have h1' : HasFDerivAt (fun y => fderiv ℝ h y e)
        ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ h) z)) (z + (0 : ℝ) • e) := by
      rw [hz]; exact h1
    exact h1'.comp_hasDerivAt (0 : ℝ) (hline 0)
  have hd2 : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ h) z e e := by
    rw [hdg.deriv_eq]; exact hdd.deriv
  have hd1 : deriv g 0 = 0 := by
    rw [hdg.eq_of_nhds]
    simp [hmin.fderiv_eq_zero]
  have hgc : ContinuousAt g 0 := by
    have : ContinuousAt h ((fun s : ℝ => z + s • e) 0) := by
      rw [show (fun s : ℝ => z + s • e) 0 = z by simp]; exact hh.continuousAt
    exact ContinuousAt.comp (g := h) this hline_c.continuousAt
  have hmax := isLocalMax_of_deriv_deriv_neg (by rw [hd2]; exact hneg) hd1 hgc
  have hmin' : IsLocalMin g 0 := by
    have : IsLocalMin h ((fun s : ℝ => z + s • e) 0) := by
      rw [show (fun s : ℝ => z + s • e) 0 = z by simp]; exact hmin
    exact IsLocalMin.comp_continuous (g := fun s : ℝ => z + s • e) (b := 0) this
      hline_c.continuousAt
  have hconst : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hmax, hmin'] with t h1 h2
    exact le_antisymm h1 h2
  have : deriv (deriv g) 0 = 0 := by
    rw [hconst.deriv.deriv_eq]
    simp
  rw [hd2] at this
  linarith

/-! ### The barrier function -/

/-- The Hopf barrier `v(x) = e^{-α|x-y|²} - e^{-αr²}`. -/
def barrier (α r : ℝ) (y x : RN N) : ℝ := Real.exp (-α * ‖x - y‖ ^ 2) - Real.exp (-α * r ^ 2)

lemma contDiff_barrier (α r : ℝ) (y : RN N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (barrier α r y) := by
  unfold barrier
  refine ContDiff.sub ?_ contDiff_const
  exact Real.contDiff_exp.comp (contDiff_const.mul
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)))

lemma laplacian_barrier (α r : ℝ) (y x : RN N) :
    Laplacian.laplacian (barrier α r y) x =
      Real.exp (-α * ‖x - y‖ ^ 2) * (4 * α ^ 2 * ‖x - y‖ ^ 2 - 2 * N * α) := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  set G : ℝ → ℝ := fun s => Real.exp (-α * s) - Real.exp (-α * r ^ 2)
  have h1 : Laplacian.laplacian (barrier α r y) x =
      Laplacian.laplacian (fun z : RN N => G (‖z‖ ^ 2)) (x - y) := by
    change Laplacian.laplacian (fun x => (fun z : RN N => G (‖z‖ ^ 2)) (x - y)) x = _
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    exact Finset.sum_congr rfl fun i _ => by
      rw [iteratedFDeriv_comp_sub (f := fun z : RN N => G (‖z‖ ^ 2)) 2 y x]
  have hG : ∀ s, HasDerivAt G (-α * Real.exp (-α * s)) s := fun s => by
    have := (((hasDerivAt_id s).const_mul (-α)).exp).sub_const (Real.exp (-α * r ^ 2))
    convert this using 1
    · funext z
      simp only [G, id, neg_mul]
    · simp only [id, neg_mul, mul_one]
      ring
  have hG' : ∀ s, HasDerivAt (fun s => -α * Real.exp (-α * s))
      (α ^ 2 * Real.exp (-α * s)) s := fun s => by
    have := (((hasDerivAt_id s).const_mul (-α)).exp).const_mul (-α)
    convert this using 1 <;> (try rfl) <;> simp only [id, neg_mul, mul_one] <;> ring
  rw [h1, laplacian_radial_sq b G _ _ hG hG' (x - y)]
  simp
  ring

lemma hasFDerivAt_barrier (α r : ℝ) (y x : RN N) :
    HasFDerivAt (barrier α r y)
      ((-α * Real.exp (-α * ‖x - y‖ ^ 2) * 2) • innerSL ℝ (x - y)) x := by
  have h1 := (hasStrictFDerivAt_norm_sq (x - y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const y)
  have h2 := ((h1.const_mul (-α)).exp).sub_const (Real.exp (-α * r ^ 2))
  unfold barrier
  convert h2 using 1 <;> (try rfl)
  ext d
  simp only [Function.comp_def, id, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, neg_mul]
  ring

/-! ### Hopf's lemma and the strong minimum principle -/

set_option maxHeartbeats 400000 in
/-- **Hopf's boundary point lemma** (in the form of a contradiction): a nonnegative superharmonic
`C²` function which is positive in a ball `B_r(y)` and vanishes at a boundary point `x₀` of the
ball (interior to `D`) cannot have vanishing gradient at `x₀`. -/
lemma hopf_contra {D : Set (RN N)} {f : RN N → ℝ} (hf2 : ∀ x ∈ D, ContDiffAt ℝ 2 f x)
    (hnn : ∀ x ∈ D, 0 ≤ f x) (hΔ : ∀ x ∈ D, Laplacian.laplacian f x ≤ 0)
    {y x0 : RN N} {r : ℝ} (hr : 0 < r) (hsub : closedBall y r ⊆ D)
    (hpos : ∀ x ∈ ball y r, 0 < f x) (hx0 : dist x0 y = r) (hfx0 : f x0 = 0)
    (hgrad : fderiv ℝ f x0 = 0) : False := by
  set α : ℝ := 2 * N / r ^ 2 + 1 with hα
  have hr2 : 0 < r ^ 2 := by positivity
  have hαpos : 0 < α := by positivity
  have hαr : 2 * N < α * r ^ 2 := by
    rw [hα, add_mul, div_mul_cancel₀ _ hr2.ne']
    linarith
  set v := barrier α r y with hv
  have hv_le : ∀ x, v x ≤ 1 := fun x => by
    have h1 : Real.exp (-α * ‖x - y‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := sq_nonneg ‖x - y‖
      nlinarith
    have h2 := Real.exp_pos (-α * r ^ 2)
    simp only [hv, barrier]
    linarith
  -- positive lower bound of `f` on the inner sphere
  obtain ⟨m, hm, hmS⟩ : ∃ m > 0, ∀ x ∈ sphere y (r / 2), m ≤ f x := by
    rcases (sphere y (r / 2)).eq_empty_or_nonempty with hS | hS
    · exact ⟨1, one_pos, by simp [hS]⟩
    · have hcont : ContinuousOn f (sphere y (r / 2)) := fun x hx =>
        (hf2 x (hsub (by rw [mem_sphere] at hx; rw [mem_closedBall]; linarith))).continuousAt.continuousWithinAt
      obtain ⟨x, hx, hmin⟩ := (isCompact_sphere y (r / 2)).exists_isMinOn hS hcont
      refine ⟨f x, hpos x ?_, fun z hz => hmin hz⟩
      rw [mem_sphere] at hx; rw [mem_ball]; linarith
  -- the closed annulus
  set A := {x : RN N | r / 2 ≤ dist x y ∧ dist x y ≤ r} with hA
  have hAc : IsCompact A := by
    refine (isCompact_closedBall y r).of_isClosed_subset ?_ (fun x hx => hx.2)
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hx0D : x0 ∈ D := hsub (by rw [mem_closedBall, hx0])
  have hx0A : x0 ∈ A := ⟨by rw [hx0]; linarith, hx0.le⟩
  have hvc : ContDiff ℝ 2 v := (contDiff_barrier α r y).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  set Hf : RN N → ℝ := f + (-m) • v with hHf
  have hH : ∀ x, Hf x = f x - m * v x := fun x => by
    simp only [hHf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  -- comparison `f ≥ m v` on the closed annulus
  have hcomp : ∀ x ∈ A, 0 ≤ Hf x := by
    have hcont : ContinuousOn Hf A := fun x hx =>
      ((hf2 x (hsub hx.2)).continuousAt.add
        (hvc.continuous.continuousAt.const_smul (-m))).continuousWithinAt
    obtain ⟨z, hzA, hzmin⟩ := hAc.exists_isMinOn ⟨x0, hx0A⟩ hcont
    intro x hx
    refine le_trans ?_ (hzmin hx)
    by_contra hneg
    push_neg at hneg
    rw [hH] at hneg
    have hzD : z ∈ D := hsub hzA.2
    rcases eq_or_lt_of_le hzA.1 with h1 | h1
    · have h3 := hmS z (by rw [mem_sphere]; exact h1.symm)
      have h4 := hv_le z
      nlinarith
    rcases eq_or_lt_of_le hzA.2 with h2 | h2
    · have h5 : v z = 0 := by
        simp only [hv, barrier, ← dist_eq_norm, h2, sub_self]
      have := hnn z hzD
      rw [h5] at hneg
      linarith
    · have hnhds : A ∈ 𝓝 z := by
        refine mem_of_superset ((isOpen_lt continuous_const
          (continuous_id.dist continuous_const)).inter (isOpen_lt
          (continuous_id.dist continuous_const) continuous_const) |>.mem_nhds ⟨h1, h2⟩) ?_
        exact fun x hx => ⟨hx.1.le, hx.2.le⟩
      have hloc : IsLocalMin Hf z := hzmin.isLocalMin hnhds
      have hHc : ContDiffAt ℝ 2 Hf z := (hf2 z hzD).add (hvc.contDiffAt.const_smul (-m))
      have hlap := laplacian_nonneg_of_isLocalMin hHc hloc
      have hadd : Laplacian.laplacian (f + (-m) • v) z =
          Laplacian.laplacian f z + Laplacian.laplacian ((-m) • v) z :=
        (hf2 z hzD).laplacian_add (hvc.contDiffAt.const_smul (-m))
      rw [hHf, hadd, InnerProductSpace.laplacian_smul (-m) hvc.contDiffAt,
        laplacian_barrier] at hlap
      have hfz := hΔ z hzD
      have hd : r / 2 < ‖z - y‖ := by rw [← dist_eq_norm]; exact h1
      have hpos' : 0 < 4 * α ^ 2 * ‖z - y‖ ^ 2 - 2 * N * α := by
        have : r ^ 2 < 4 * ‖z - y‖ ^ 2 := by nlinarith
        nlinarith
      have he := Real.exp_pos (-α * ‖z - y‖ ^ 2)
      have : 0 < Real.exp (-α * ‖z - y‖ ^ 2) * (4 * α ^ 2 * ‖z - y‖ ^ 2 - 2 * N * α) :=
        mul_pos he hpos'
      have hmX := mul_pos hm this
      simp only [smul_eq_mul] at hlap
      linarith
  -- `x₀` minimises `f - m v` on the annulus; differentiate in the inward direction
  have hv0 : v x0 = 0 := by
    simp only [hv, barrier, ← dist_eq_norm, hx0, sub_self]
  have hmin : IsMinOn Hf A x0 := isMinOn_iff.mpr fun x hx => by
    rw [hH x0, hfx0, hv0]
    simpa using hcomp x hx
  have hfd : HasFDerivAt f (fderiv ℝ f x0) x0 :=
    ((hf2 x0 hx0D).differentiableAt (by norm_num)).hasFDerivAt
  have hderiv : HasFDerivAt Hf (fderiv ℝ f x0 + (-m) •
      ((-α * Real.exp (-α * ‖x0 - y‖ ^ 2) * 2) • innerSL ℝ (x0 - y))) x0 :=
    hfd.add ((hasFDerivAt_barrier α r y x0).const_smul (-m))
  set d : RN N := (1 / 2 : ℝ) • (y - x0) with hd
  have hseg : segment ℝ x0 (x0 + d) ⊆ A := by
    rw [segment_eq_image']
    rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    have heq : x0 + θ • (x0 + d - x0) - y = (1 - θ / 2) • (x0 - y) := by
      simp only [hd, add_sub_cancel_left, smul_smul, smul_sub, sub_smul, one_smul]
      module
    have hn : dist (x0 + θ • (x0 + d - x0)) y = (1 - θ / 2) * r := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg (by linarith), ← dist_eq_norm, hx0]
    have h1 := mul_nonneg (sub_nonneg.2 hθ1) hr.le
    have h2 := mul_nonneg hθ0 hr.le
    refine ⟨?_, ?_⟩
    · rw [hn]; linarith
    · rw [hn]; linarith
  have key := IsLocalMinOn.hasFDerivWithinAt_nonneg (IsMinOn.localize hmin)
    hderiv.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  rw [hgrad] at key
  have hinner : ⟪x0 - y, d⟫ = -(1 / 2) * r ^ 2 := by
    rw [hd, inner_smul_right, ← neg_sub x0 y, inner_neg_right, real_inner_self_eq_norm_sq,
      ← dist_eq_norm, hx0]
    ring
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, zero_add,
    hinner] at key
  have he := Real.exp_pos (-α * ‖x0 - y‖ ^ 2)
  generalize Real.exp (-α * ‖x0 - y‖ ^ 2) = E at key he
  clear_value α
  have hprod : 0 < m * α * E * r ^ 2 := mul_pos (mul_pos (mul_pos hm hαpos) he) hr2
  have hk : -m * (-α * E * 2 * (-(1 / 2) * r ^ 2)) = -(m * α * E * r ^ 2) := by ring
  rw [hk] at key
  linarith

/-- **Strong minimum principle.** A nonnegative superharmonic `C²` function on a domain which
does not vanish identically is strictly positive. -/
theorem strong_min_principle {D : Set (RN N)} (hDo : IsOpen D) (hDc : IsConnected D)
    {f : RN N → ℝ} (hf2 : ∀ x ∈ D, ContDiffAt ℝ 2 f x) (hnn : ∀ x ∈ D, 0 ≤ f x)
    (hΔ : ∀ x ∈ D, Laplacian.laplacian f x ≤ 0) {x1 : RN N} (hx1 : x1 ∈ D) (hfx1 : f x1 ≠ 0) :
    ∀ x ∈ D, 0 < f x := by
  intro x hx
  by_contra hcon
  have hfx : f x = 0 := le_antisymm (not_lt.mp hcon) (hnn x hx)
  have hfc : ContinuousOn f D := fun x hx => (hf2 x hx).continuousAt.continuousWithinAt
  set P := D ∩ f ⁻¹' Ioi 0 with hP
  have hPo : IsOpen P := hfc.isOpen_inter_preimage hDo isOpen_Ioi
  -- a zero of `f` in `D` adherent to `P`
  obtain ⟨z, hzD, hzP, hzcl⟩ : ∃ z ∈ D, z ∉ P ∧ z ∈ closure P := by
    by_contra hno
    push_neg at hno
    have hsub : D ⊆ P ∪ (D \ closure P) := by
      intro w hw
      by_cases hwP : w ∈ P
      · exact Or.inl hwP
      · exact Or.inr ⟨hw, hno w hw hwP⟩
    have hDP := hDc.isPreconnected.subset_left_of_subset_union hPo
      (hDo.sdiff isClosed_closure)
      (Set.disjoint_left.mpr fun w hw1 hw2 => hw2.2 (subset_closure hw1))
      hsub ⟨x1, hx1, hx1, lt_of_le_of_ne (hnn x1 hx1) (Ne.symm hfx1)⟩
    have := (hDP hx).2
    simp only [mem_preimage, mem_Ioi] at this
    linarith
  have hfz : f z = 0 := by
    refine le_antisymm (not_lt.mp fun h => hzP ⟨hzD, h⟩) (hnn z hzD)
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDo z hzD
  set ρ := ε / 4 with hρ
  have hρpos : 0 < ρ := by positivity
  obtain ⟨y, hyP, hyz⟩ := Metric.mem_closure_iff.mp hzcl ρ hρpos
  rw [dist_comm] at hyz
  have hcb : closedBall y (2 * ρ) ⊆ D := fun w hw => hεD (by
    rw [mem_closedBall] at hw
    rw [mem_ball]
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < ε := by linarith)
  set K := closedBall y (2 * ρ) ∩ f ⁻¹' {0} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall y (2 * ρ)).of_isClosed_subset
      ((hfc.mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
      inter_subset_left
  have hzK : z ∈ K := ⟨by rw [mem_closedBall, dist_comm]; linarith, hfz⟩
  obtain ⟨x0, hx0K, hx0min⟩ := hKc.exists_isMinOn ⟨z, hzK⟩
    (continuous_id.dist continuous_const).continuousOn
  set r := dist x0 y with hr
  have hrz : r ≤ dist z y := hx0min hzK
  have hx0y : x0 ≠ y := by
    intro h
    have h1 := hx0K.2
    have h2 := hyP.2
    simp only [mem_preimage, mem_singleton_iff, mem_Ioi] at h1 h2
    rw [h] at h1
    linarith
  have hrpos : 0 < r := dist_pos.mpr hx0y
  have hrρ : r < ρ := by rw [dist_comm] at hyz; linarith
  have hpos : ∀ w ∈ ball y r, 0 < f w := by
    intro w hw
    rw [mem_ball] at hw
    have hwD : w ∈ D := hcb (by rw [mem_closedBall]; linarith)
    refine lt_of_le_of_ne (hnn w hwD) fun h => ?_
    have hwK : w ∈ K := ⟨by rw [mem_closedBall]; linarith, h.symm⟩
    have : r ≤ dist w y := hx0min hwK
    linarith
  have hsub : closedBall y r ⊆ D := fun w hw => hcb (by
    rw [mem_closedBall] at hw ⊢; linarith)
  have hx0D : x0 ∈ D := hsub (by rw [mem_closedBall])
  have hfx0 : f x0 = 0 := hx0K.2
  have hloc : IsLocalMin f x0 := by
    filter_upwards [hDo.mem_nhds hx0D] with w hw
    rw [hfx0]; exact hnn w hw
  exact hopf_contra hf2 hnn hΔ hrpos hsub hpos rfl hfx0 hloc.fderiv_eq_zero

/-! ### The eigenvalue equation holds pointwise -/

/-- A weak solution of `-Δw = λw` in `H_D` with an analytic representative `f` on `D` solves
`Δf = -λf` pointwise in `D`. -/
theorem laplacian_eq_of_weak {D : Set (RN N)} (hDo : IsOpen D) {w : Amb N} {lam : ℝ}
    (hw : w ∈ H D) (hweak : ∀ φ ∈ H D, qf w φ = lam * l2 w φ) {f : RN N → ℝ}
    (hfa : AnalyticOnNhd ℝ f D) (hf : IsContRep D w f) :
    ∀ x ∈ D, Laplacian.laplacian f x = -lam * f x := by
  intro x0 hx0
  have hDm : MeasurableSet D := hDo.measurableSet
  obtain ⟨χ, hχ, hχc, hχD, U, hUo, hx0U, hχ1⟩ :=
    exists_cutoff (isCompact_singleton (x := x0)) hDo (singleton_subset_iff.mpr hx0)
  have hx0U' : x0 ∈ U := hx0U rfl
  set V := U ∩ D with hV
  have hVo : IsOpen V := hUo.inter hDo
  set g : RN N → ℝ := fun x => χ x * f x with hgdef
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ D
    · exact hχ.contDiffAt.mul (hfa x hx).contDiffAt
    · have hxs : x ∉ tsupport χ := fun h => hx (hχD h)
      have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with z hz
        simp [hgdef, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hgc : HasCompactSupport g := hχc.mul_right
  have hgV : ∀ x ∈ V, g x = f x := fun x hx => by simp [hgdef, hχ1 x hx.1]
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  -- the weak equation tested against `φ ∈ C_c^∞(V)`
  have key : ∀ φ : RN N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      ∫ x, φ x • (Laplacian.laplacian g x + lam * g x) = 0 := by
    intro φ hφ hφc hts
    have hp : testPair φ hφ hφc ∈ H D :=
      testGraph_subset_H D (testPair_mem hφ hφc (hts.trans inter_subset_right))
    have hwe := hweak _ hp
    have hq : qf w (testPair φ hφ hφc) = -∫ x, g x * Laplacian.laplacian φ x := by
      rw [qf, weak_gradient_identity hw φ hφ hφc, MeasureTheory.L2.inner_def]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hf2, lapL2_ae φ hφ hφc] with x h1 h2
      simp only [RCLike.inner_apply, conj_trivial]
      rw [h2]
      by_cases hx : x ∈ tsupport φ
      · rw [h1 (hts hx).2, hgV x (hts hx)]; ring
      · rw [laplacian_eq_zero_of_notMem_tsupport hx]; ring
    have hl : l2 w (testPair φ hφ hφc) = ∫ x, g x * φ x := by
      rw [l2, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hf2, MemLp.coeFn_toLp (memLp_of_testFun hφ hφc)] with x h1 h2
      simp only [RCLike.inner_apply, conj_trivial]
      simp only [testPair] at *
      rw [h2]
      by_cases hx : x ∈ tsupport φ
      · rw [h1 (hts hx).2, hgV x (hts hx)]; ring
      · rw [image_eq_zero_of_notMem_tsupport hx]; ring
    rw [hq, hl, ← integral_laplacian_mul_comm hg hgc hφ hφc] at hwe
    have hcΔ : Continuous (Laplacian.laplacian g) := (contDiff_laplacian hg).continuous
    have hi1 : Integrable (fun x => Laplacian.laplacian g x * φ x) :=
      (hcΔ.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have hi2 : Integrable (fun x => g x * φ x) :=
      (hg.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have : ∫ x, φ x • (Laplacian.laplacian g x + lam * g x) =
        (∫ x, Laplacian.laplacian g x * φ x) + lam * ∫ x, g x * φ x := by
      calc ∫ x, φ x • (Laplacian.laplacian g x + lam * g x)
          = ∫ x, (Laplacian.laplacian g x * φ x + lam * (g x * φ x)) := by
            congr 1; ext x; simp only [smul_eq_mul]; ring
        _ = _ := by rw [integral_add hi1 (hi2.const_mul lam), integral_const_mul]
    rw [this]
    linarith
  set F : RN N → ℝ := fun x => Laplacian.laplacian g x + lam * g x with hF
  have hFc : Continuous F := (contDiff_laplacian hg).continuous.add
    (continuous_const.mul hg.continuous)
  have hae := hVo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hFc.locallyIntegrable.locallyIntegrableOn V) key
  have hF0 : F x0 = 0 := by
    by_contra hne
    set W := V ∩ {x | F x ≠ 0}
    have hWo : IsOpen W := hVo.inter (isOpen_ne_fun hFc continuous_const)
    have hWpos : 0 < volume W := hWo.measure_pos volume ⟨x0, ⟨hx0U', hx0⟩, hne⟩
    have hW0 : volume W = 0 := by
      rw [ae_iff] at hae
      refine measure_mono_null (fun x hx => ?_) hae
      simp only [mem_setOf_eq]
      exact fun h => hx.2 (h hx.1)
    exact hWpos.ne' hW0
  have hgf : g =ᶠ[𝓝 x0] f := by
    filter_upwards [hVo.mem_nhds ⟨hx0U', hx0⟩] with x hx
    exact hgV x hx
  have hlap : Laplacian.laplacian g x0 = Laplacian.laplacian f x0 :=
    (InnerProductSpace.laplacian_congr_nhds hgf).eq_of_nhds
  have : F x0 = Laplacian.laplacian f x0 + lam * f x0 := by
    simp only [hF, hlap, hgV x0 ⟨hx0U', hx0⟩]
  linarith

/-! ### First eigenfunctions do not change sign -/

/-- `q(v,v) ≥ λ₁ ‖v‖²` on `H_D`. -/
lemma qf_ge_lam1 {D : Set (RN N)} {v : Amb N}
    (hv : v ∈ H D) : eigenvalue D 1 * l2 v v ≤ qf v v := by
  by_cases h0 : v = 0
  · simp [h0]
  have hpos := l2_self_pos hv h0
  have := eigenvalue_one_le_rayleigh hv h0
  rw [rayleigh, le_div_iff₀ hpos] at this
  linarith

/-- A minimiser of the Rayleigh quotient is a (weak) eigenfunction for `λ₁`. -/
lemma eigen_of_rayleigh_eq {D : Set (RN N)} {v : Amb N}
    (hv : v ∈ H D) (heq : qf v v = eigenvalue D 1 * l2 v v) :
    ∀ φ ∈ H D, qf v φ = eigenvalue D 1 * l2 v φ := by
  intro φ hφ
  set lam := eigenvalue D 1
  set B := qf v φ - lam * l2 v φ
  set Q := qf φ φ - lam * l2 φ φ
  have hQ : 0 ≤ Q := by have := qf_ge_lam1 hφ; simp only [Q]; linarith
  have key : ∀ t : ℝ, 0 ≤ 2 * t * B + t ^ 2 * Q := by
    intro t
    have h := qf_ge_lam1 ((H D).add_mem hv ((H D).smul_mem t hφ))
    simp only [qf_add_left, qf_add_right, qf_smul_left, qf_smul_right, l2_add_left,
      l2_add_right, l2_smul_left, l2_smul_right] at h
    rw [qf_comm φ v, l2_comm φ v] at h
    simp only [B, Q]
    nlinarith
  have h := key (-B / (Q + 1))
  have hQ1 : 0 < Q + 1 := by linarith
  have : 2 * (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q =
      -(B ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by
    field_simp
    ring
  rw [this, le_div_iff₀ (by positivity), zero_mul] at h
  have hB : B ^ 2 = 0 := by nlinarith [sq_nonneg B]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hB
  simp only [B] at this
  linarith

/-- A first eigenfunction of a domain does not change sign: otherwise its positive part would be
a first eigenfunction vanishing on the nonempty open set where the function is negative,
contradicting unique continuation. -/
lemma first_eigen_no_sign_change {D : Set (RN N)} (hD : IsDomain D) {w : Amb N}
    (hw : w ∈ H D) (hw' : ∀ φ ∈ H D, qf w φ = eigenvalue D 1 * l2 w φ) {f : RN N → ℝ}
    (hf : IsContRep D w f) (hP : (posSign D f).Nonempty) (hM : (negSign D f).Nonempty) :
    False := by
  have hDm : MeasurableSet D := hD.1.1.measurableSet
  set P := posSign D f
  set M := negSign D f
  obtain ⟨hp, hn, hqo, hlo⟩ := lemma_parts hD.1 hw hf
  have hpD : posPart w ∈ H D := H_mono (posSign_subset D f) hp
  have hnD : negPart w ∈ H D := H_mono (negSign_subset D f) hn
  have hsplit := posPart_sub_negPart hD.1 hw hf
  have hqw : qf w w = qf (posPart w) (posPart w) + qf (negPart w) (negPart w) := by
    conv_lhs => rw [← hsplit]
    simp only [qf_sub_left, qf_sub_right]
    rw [qf_comm (negPart w) (posPart w), hqo]
    ring
  have hlw : l2 w w = l2 (posPart w) (posPart w) + l2 (negPart w) (negPart w) := by
    conv_lhs => rw [← hsplit]
    simp only [l2_sub_left, l2_sub_right]
    rw [l2_comm (negPart w) (posPart w), hlo]
    ring
  have hww := hw' w hw
  have h1 := qf_ge_lam1 hpD
  have h2 := qf_ge_lam1 hnD
  rw [hqw, hlw, mul_add] at hww
  have hpeq : qf (posPart w) (posPart w) = eigenvalue D 1 * l2 (posPart w) (posPart w) := by
    linarith
  have hpeig := eigen_of_rayleigh_eq hpD hpeq
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  have hp0 : posPart w ≠ 0 := by
    intro h0
    have hz : ((posPart w).1 : RN N → ℝ) =ᵐ[volume] 0 := by
      rw [h0]; exact Lp.coeFn_zero ℝ 2 volume
    have hPm : MeasurableSet P := (isOpen_posSign hD.1.1 hf.1).measurableSet
    have hfalse : ∀ᵐ x ∂volume.restrict P, False := by
      rw [ae_restrict_iff' hPm]
      filter_upwards [hz, posPart_fst_ae w, hf2] with x h1 h2 h3 hx
      rw [h2, h3 hx.1, Pi.zero_apply] at h1
      have := hx.2
      simp only [Set.mem_setOf_eq] at this
      rw [max_eq_left this.le] at h1
      linarith
    have hμ : volume P = 0 := by
      rw [ae_iff] at hfalse
      simpa using hfalse
    exact ((isOpen_posSign hD.1.1 hf.1).measure_pos volume hP).ne' hμ
  have hvan : ((posPart w).1 : RN N → ℝ) =ᵐ[volume.restrict M] 0 := by
    have hMm : MeasurableSet M := (isOpen_negSign hD.1.1 hf.1).measurableSet
    rw [EventuallyEq, ae_restrict_iff' hMm]
    filter_upwards [posPart_fst_ae w, hf2] with x h1 h2 hx
    rw [h1, h2 hx.1, Pi.zero_apply]
    have := hx.2
    simp only [Set.mem_setOf_eq] at this
    exact max_eq_right this.le
  exact ucp_nonvanishing hD ⟨hpD, hp0, hpeig⟩ (isOpen_negSign hD.1.1 hf.1) hM
    (negSign_subset D f) hvan

/-- A nonzero element of `H_D` has a continuous representative which does not vanish
identically on `D`. -/
lemma exists_ne_zero_of_contRep {D : Set (RN N)} (hDm : MeasurableSet D) {u : Amb N}
    (hu : u ∈ H D) (hu0 : u ≠ 0) {g : RN N → ℝ} (hg : IsContRep D u g) :
    ∃ x ∈ D, g x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hu0
  apply eq_zero_of_l2_self_eq_zero hu
  obtain ⟨hu1, -⟩ := mem_vanishOn.mp (H_le_vanishOn D hu)
  rw [EventuallyEq, ae_restrict_iff' hDm.compl] at hu1
  have hg2 := hg.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hg2
  have hz : (u.1 : RN N → ℝ) =ᵐ[volume] 0 := by
    filter_upwards [hu1, hg2] with x h1 h2
    by_cases hx : x ∈ D
    · rw [h2 hx, hcon x hx]; rfl
    · exact h1 hx
  rw [l2, MeasureTheory.L2.inner_def]
  rw [integral_eq_zero_of_ae]
  filter_upwards [hz] with x hx
  simp [hx]

/-! ### Positivity of the ground state -/

/-- **Spectral package, connected sets: positivity.** On a domain the first eigenvalue has a
strictly positive (continuous) eigenfunction. -/
theorem ground_state_pos (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) :
    ∃ u f, IsEigenfunction D u (eigenvalue D 1) ∧ IsContRep D u f ∧ ∀ x ∈ D, 0 < f x := by
  have hDm : MeasurableSet D := hD.1.1.measurableSet
  obtain ⟨e, he, -⟩ := ext_spectral hN hD.1
  have hw : IsEigenfunction D (e 0) (eigenvalue D 1) := he 0
  obtain ⟨f, hfa, hf⟩ := ext_analytic hD hw.1 hw.2.2
  -- reduce to a nonnegative first eigenfunction with an analytic representative
  obtain ⟨u, g, hu, hga, hg, hgnn⟩ : ∃ u g, IsEigenfunction D u (eigenvalue D 1) ∧
      AnalyticOnNhd ℝ g D ∧ IsContRep D u g ∧ ∀ x ∈ D, 0 ≤ g x := by
    by_cases hM : (negSign D f).Nonempty
    · have hP : ¬ (posSign D f).Nonempty := fun hP =>
        first_eigen_no_sign_change hD hw.1 hw.2.2 hf hP hM
      refine ⟨-e 0, fun x => -f x, ⟨(H D).neg_mem hw.1, neg_ne_zero.mpr hw.2.1, ?_⟩,
        fun x hx => (hfa x hx).neg, hf.neg, ?_⟩
      · intro φ hφ
        rw [qf_neg_left, l2_neg_left, hw.2.2 φ hφ]
        ring
      · intro x hx
        by_contra hlt
        exact hP ⟨x, hx, by simp only [mem_setOf_eq]; linarith⟩
    · refine ⟨e 0, f, hw, hfa, hf, fun x hx => ?_⟩
      by_contra hlt
      exact hM ⟨x, hx, lt_of_not_ge hlt⟩
  refine ⟨u, g, hu, hg, ?_⟩
  have hPDE := laplacian_eq_of_weak hD.1.1 hu.1 hu.2.2 hga hg
  obtain ⟨x1, hx1, hgx1⟩ := exists_ne_zero_of_contRep hDm hu.1 hu.2.1 hg
  refine strong_min_principle hD.1.1 hD.2 (fun x hx => (hga x hx).contDiffAt) hgnn
    (fun x hx => ?_) hx1 hgx1
  rw [hPDE x hx]
  have := eigenvalue_nonneg D 1
  have := hgnn x hx
  nlinarith

end FourthRatio

end

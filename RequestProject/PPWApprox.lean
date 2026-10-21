module

public import RequestProject.PPWGapTest
public import RequestProject.PPWProfile
public import RequestProject.PPWSmooth

/-!
# PPW: the gap inequality for the Ashbaugh–Benguria vector field

The gap inequality of `RequestProject/PPWGapTest.lean` is extended by approximation to the
(only piecewise smooth) components `P_i(x) = h(|x - c|²) (x - c)_i` of the Ashbaugh–Benguria
vector field, and summed over `i`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **Gap inequality for a limit of smooth multipliers** (dominated convergence). -/
theorem gap_lim (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    (hu : IsEigenfunction D u (eigenvalue D 1)) (Pk : ℕ → RN N → ℝ)
    (hPk : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pk k)) (P : RN N → ℝ) (G : RN N → RN N)
    {C : ℝ}
    (hbd : ∀ k, ∀ᵐ x, (u.1 : RN N → ℝ) x ≠ 0 → |Pk k x| ≤ C ∧ ‖gradient (Pk k) x‖ ≤ C)
    (hconv : ∀ᵐ x, (u.1 : RN N → ℝ) x ≠ 0 →
      Tendsto (fun k => Pk k x) atTop (𝓝 (P x)) ∧
        Tendsto (fun k => gradient (Pk k) x) atTop (𝓝 (G x))) :
    (eigenvalue D 2 - eigenvalue D 1) *
        ((∫ x, P x ^ 2 * (u.1 : RN N → ℝ) x ^ 2) * (∫ x, (u.1 : RN N → ℝ) x ^ 2) -
          (∫ x, P x * (u.1 : RN N → ℝ) x ^ 2) ^ 2) ≤
      (∫ x, ‖G x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2) * ∫ x, (u.1 : RN N → ℝ) x ^ 2 := by
  set u1 := (u.1 : RN N → ℝ) with hu1
  have hint : Integrable fun x => u1 x ^ 2 := (Lp.memLp u.1).integrable_sq
  have hu1m : AEStronglyMeasurable u1 volume := (Lp.aestronglyMeasurable u.1)
  have hgc : ∀ k, Continuous (gradient (Pk k)) := fun k =>
    (InnerProductSpace.toDual ℝ (RN N)).symm.continuous.comp
      ((hPk k).continuous_fderiv (by simp))
  have T1 : Tendsto (fun k => ∫ x, Pk k x ^ 2 * u1 x ^ 2) atTop
      (𝓝 (∫ x, P x ^ 2 * u1 x ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C ^ 2 * u1 x ^ 2)
      (fun k => (((hPk k).continuous.pow 2).aestronglyMeasurable).mul (hu1m.pow 2))
      (hint.const_mul _) (fun k => ?_) ?_
    · filter_upwards [hbd k] with x hx
      by_cases h0 : u1 x = 0
      · simp [h0]
      · obtain ⟨h1, -⟩ := hx h0
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (u1 x)), abs_pow]
        have hC : 0 ≤ C := (abs_nonneg _).trans h1
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 2) (sq_nonneg _)
    · filter_upwards [hconv] with x hx
      by_cases h0 : u1 x = 0
      · simp [h0]
      · exact ((hx h0).1.pow 2).mul_const _
  have T2 : Tendsto (fun k => ∫ x, Pk k x * u1 x ^ 2) atTop (𝓝 (∫ x, P x * u1 x ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |C| * u1 x ^ 2)
      (fun k => ((hPk k).continuous.aestronglyMeasurable).mul (hu1m.pow 2))
      (hint.const_mul _) (fun k => ?_) ?_
    · filter_upwards [hbd k] with x hx
      by_cases h0 : u1 x = 0
      · simp [h0]
      · obtain ⟨h1, -⟩ := hx h0
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (u1 x))]
        exact mul_le_mul_of_nonneg_right (h1.trans (le_abs_self C)) (sq_nonneg _)
    · filter_upwards [hconv] with x hx
      by_cases h0 : u1 x = 0
      · simp [h0]
      · exact (hx h0).1.mul_const _
  have T3 : Tendsto (fun k => ∫ x, ‖gradient (Pk k) x‖ ^ 2 * u1 x ^ 2) atTop
      (𝓝 (∫ x, ‖G x‖ ^ 2 * u1 x ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C ^ 2 * u1 x ^ 2)
      (fun k => (((hgc k).norm.pow 2).aestronglyMeasurable).mul (hu1m.pow 2))
      (hint.const_mul _) (fun k => ?_) ?_
    · filter_upwards [hbd k] with x hx
      by_cases h0 : u1 x = 0
      · simp [h0]
      · obtain ⟨-, h2⟩ := hx h0
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (u1 x)),
          abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h2 2) (sq_nonneg _)
    · filter_upwards [hconv] with x hx
      by_cases h0 : u1 x = 0
      · simp [h0]
      · exact (((hx h0).2.norm).pow 2).mul_const _
  have hL := (tendsto_const_nhds (x := eigenvalue D 2 - eigenvalue D 1)).mul
    ((T1.mul_const (∫ x, u1 x ^ 2)).sub (T2.pow 2))
  have hR := T3.mul_const (∫ x, u1 x ^ 2)
  exact le_of_tendsto_of_tendsto' hL hR fun k => gap_test hN hD hu (hPk k)


/-- `∑ᵢ ‖(2 d ⟨v, eᵢ⟩) v + h eᵢ‖² = N h² + 4 |v|² h d + 4 |v|⁴ d²`. -/
lemma sum_norm_sq_radial (v : RN N) (h d : ℝ) :
    ∑ i, ‖(d * 2 * ⟪v, EuclideanSpace.basisFun (Fin N) ℝ i⟫) • v +
        h • EuclideanSpace.basisFun (Fin N) ℝ i‖ ^ 2 =
      (N : ℝ) * h ^ 2 + 4 * ‖v‖ ^ 2 * h * d + 4 * (‖v‖ ^ 2) ^ 2 * d ^ 2 := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have hs : ∑ i, ⟪v, b i⟫ ^ 2 = ‖v‖ ^ 2 := by
    have := b.sum_inner_mul_inner v v
    rw [real_inner_self_eq_norm_sq] at this
    rw [← this]; congr 1; funext i; rw [real_inner_comm (b i) v]; ring
  have hterm : ∀ i, ‖(d * 2 * ⟪v, b i⟫) • v + h • b i‖ ^ 2 =
      (d * 2 * ⟪v, b i⟫) ^ 2 * ‖v‖ ^ 2 + 2 * (d * 2 * ⟪v, b i⟫) * h * ⟪v, b i⟫ + h ^ 2 := by
    intro i
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
      b.orthonormal.1 i]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
    ring
  simp only [hterm, Finset.sum_add_distrib]
  have e1 : ∑ i, (d * 2 * ⟪v, b i⟫) ^ 2 * ‖v‖ ^ 2 = 4 * d ^ 2 * ‖v‖ ^ 2 * ∑ i, ⟪v, b i⟫ ^ 2 := by
    rw [Finset.mul_sum]; congr 1; funext i; ring
  have e2 : ∑ i, 2 * (d * 2 * ⟪v, b i⟫) * h * ⟪v, b i⟫ = 4 * d * h * ∑ i, ⟪v, b i⟫ ^ 2 := by
    rw [Finset.mul_sum]; congr 1; funext i; ring
  rw [e1, e2, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `∑ᵢ (h ⟨v, eᵢ⟩)² = |v|² h²`. -/
lemma sum_sq_radial (v : RN N) (h : ℝ) :
    ∑ i, (h * ⟪v, EuclideanSpace.basisFun (Fin N) ℝ i⟫) ^ 2 = ‖v‖ ^ 2 * h ^ 2 := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have hs : ∑ i, ⟪v, b i⟫ ^ 2 = ‖v‖ ^ 2 := by
    have := b.sum_inner_mul_inner v v
    rw [real_inner_self_eq_norm_sq] at this
    rw [← this]; congr 1; funext i; rw [real_inner_comm (b i) v]; ring
  rw [← hs, Finset.sum_mul]; congr 1; funext i; ring

/-- Integrability of `f u²` for `f` bounded where `u ≠ 0`. -/
lemma integrable_mul_sq_of_bdd {f u1 : RN N → ℝ} (hint : Integrable fun x => u1 x ^ 2)
    (hf : AEStronglyMeasurable f volume) (hu1 : AEStronglyMeasurable u1 volume) {K : ℝ}
    (hb : ∀ᵐ x, u1 x ≠ 0 → |f x| ≤ K) : Integrable fun x => f x * u1 x ^ 2 := by
  refine Integrable.mono (hint.const_mul K) (hf.mul (hu1.pow 2)) ?_
  filter_upwards [hb] with x hx
  by_cases h0 : u1 x = 0
  · simp [h0]
  · have hK := hx h0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (u1 x)),
      abs_of_nonneg ((abs_nonneg _).trans hK)]
    exact mul_le_mul_of_nonneg_right hK (sq_nonneg _)

/-- **Gap inequality for the Ashbaugh–Benguria vector field centred at `c`.**  If the vector
field `h(|x - c|²)(x - c)` is `u²`-orthogonal to the constants, then
`(λ₂ - λ₁) ∫ G(|x - c|²) u² ≤ ∫ B(|x - c|²) u²`. -/
theorem profile_gap (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    (hu : IsEigenfunction D u (eigenvalue D 1)) {a : ℝ} (p : ABProfile N a) (c : RN N)
    (hc : ∀ e : RN N, ∫ x, p.prof (‖x - c‖ ^ 2) * ⟪x - c, e⟫ * (u.1 : RN N → ℝ) x ^ 2 = 0) :
    (eigenvalue D 2 - eigenvalue D 1) * ∫ x, p.Gw (‖x - c‖ ^ 2) * (u.1 : RN N → ℝ) x ^ 2 ≤
      ∫ x, p.Bw (‖x - c‖ ^ 2) * (u.1 : RN N → ℝ) x ^ 2 := by
  set u1 := (u.1 : RN N → ℝ) with hu1
  set b := EuclideanSpace.basisFun (Fin N) ℝ with hb
  have hint : Integrable fun x => u1 x ^ 2 := (Lp.memLp u.1).integrable_sq
  have hu1m : AEStronglyMeasurable u1 volume := Lp.aestronglyMeasurable u.1
  by_cases h0 : ∫ x, u1 x ^ 2 = 0
  · have hz : (fun x => u1 x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).mp h0
    have e : ∀ f : RN N → ℝ, ∫ x, f x * u1 x ^ 2 = 0 := fun f => by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    rw [e, e, mul_zero]
  have hpos : 0 < ∫ x, u1 x ^ 2 :=
    lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (Ne.symm h0)
  -- `u` vanishes outside the bounded set `D`
  obtain ⟨M, hDM⟩ := hD.1.2.2.subset_closedBall 0
  have hM : ∀ᵐ x, u1 x ≠ 0 → ‖x‖ ≤ M := by
    have h0 := (mem_vanishOn.mp (H_le_vanishOn D hu.1)).1
    rw [Filter.EventuallyEq, ae_restrict_iff' hD.1.1.measurableSet.compl] at h0
    filter_upwards [h0] with x hx hux
    by_contra hMx
    push_neg at hMx
    have hxD : x ∉ D := fun hxD => by
      have := hDM hxD; rw [mem_closedBall, dist_zero_right] at this; linarith
    exact hux (by simpa using hx hxD)
  -- the sphere `|x - c| = R` is null
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hsph : ∀ᵐ x : RN N, ‖x - c‖ ^ 2 ≠ annR N a ^ 2 := by
    have hnull : volume (sphere c |annR N a|) = 0 := Measure.addHaar_sphere volume c _
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with x hx heq
    apply hx
    rw [mem_sphere, dist_eq_norm]
    have := congrArg Real.sqrt heq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at this
  -- uniform bounds
  set L := M + ‖c‖ with hL
  obtain ⟨C, hC⟩ := p.exists_bound_profK (L ^ 2)
  set C0 := |C|
  set K := C0 * |L| + C0 * 2 * |L| * |L| + C0 with hK
  have hdm : Measurable p.dprof := by
    unfold ABProfile.dprof
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (p.h1_smooth.continuous_deriv (by simp)).measurable
      (p.h2_smooth.continuous_deriv (by simp)).measurable
  have hnc : Continuous fun x : RN N => ‖x - c‖ ^ 2 :=
    ((continuous_id.sub continuous_const).norm).pow 2
  -- the gap inequality for each component
  set P : Fin N → RN N → ℝ := fun i x => p.prof (‖x - c‖ ^ 2) * ⟪x - c, b i⟫ with hP
  set G : Fin N → RN N → RN N := fun i x =>
    (p.dprof (‖x - c‖ ^ 2) * 2 * ⟪x - c, b i⟫) • (x - c) + p.prof (‖x - c‖ ^ 2) • b i with hG
  have comp : ∀ i, (∀ᵐ x, u1 x ≠ 0 → |P i x| ≤ K ∧ ‖G i x‖ ≤ K) ∧
      (eigenvalue D 2 - eigenvalue D 1) * ∫ x, P i x ^ 2 * u1 x ^ 2 ≤
        ∫ x, ‖G i x‖ ^ 2 * u1 x ^ 2 := by
    intro i
    set Pk : ℕ → RN N → ℝ := fun k x => p.profK k (‖x - c‖ ^ 2) * ⟪x - c, b i⟫ with hPk
    have hPks : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pk k) := fun k =>
      contDiff_radial_inner (p.contDiff_profK k) c (b i)
    have hgrad : ∀ k x, gradient (Pk k) x = (p.dprofK k (‖x - c‖ ^ 2) * 2 * ⟪x - c, b i⟫) •
        (x - c) + p.profK k (‖x - c‖ ^ 2) • b i := fun k x =>
      gradient_radial_inner (p.hasDerivAt_profK k) c (b i) x
    have hbi : ‖b i‖ = 1 := b.orthonormal.1 i
    have hbd : ∀ k, ∀ᵐ x, u1 x ≠ 0 → |Pk k x| ≤ K ∧ ‖gradient (Pk k) x‖ ≤ K := by
      intro k
      filter_upwards [hM] with x hx hux
      have hxM := hx hux
      have hxc : ‖x - c‖ ≤ |L| := (norm_sub_le x c).trans ((by linarith : ‖x‖ + ‖c‖ ≤ L).trans
        (le_abs_self L))
      have hs0 : 0 ≤ ‖x - c‖ ^ 2 := sq_nonneg _
      have hsL : ‖x - c‖ ^ 2 ≤ L ^ 2 := by
        rw [← sq_abs L]; exact pow_le_pow_left₀ (norm_nonneg _) hxc 2
      obtain ⟨c1, c2⟩ := hC k _ hs0 hsL
      have c1' : |p.profK k (‖x - c‖ ^ 2)| ≤ C0 := c1.trans (le_abs_self C)
      have c2' : |p.dprofK k (‖x - c‖ ^ 2)| ≤ C0 := c2.trans (le_abs_self C)
      have hin : |⟪x - c, b i⟫| ≤ |L| := by
        have := abs_real_inner_le_norm (x - c) (b i)
        rw [hbi, mul_one] at this; exact this.trans hxc
      have hC0 : 0 ≤ C0 := abs_nonneg C
      have hL0 : 0 ≤ |L| := abs_nonneg L
      constructor
      · simp only [Pk, abs_mul]
        calc |p.profK k (‖x - c‖ ^ 2)| * |⟪x - c, b i⟫| ≤ C0 * |L| :=
              mul_le_mul c1' hin (abs_nonneg _) hC0
          _ ≤ K := by rw [hK]; nlinarith [mul_nonneg (mul_nonneg hC0 hL0) hL0]
      · rw [hgrad]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, hbi, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_mul]
        have : |p.dprofK k (‖x - c‖ ^ 2)| * |(2 : ℝ)| * |⟪x - c, b i⟫| * ‖x - c‖ ≤
            C0 * 2 * |L| * |L| := by
          rw [abs_two]
          gcongr
        rw [hK]; nlinarith [mul_nonneg hC0 hL0]
    have hconv : ∀ᵐ x, u1 x ≠ 0 → Tendsto (fun k => Pk k x) atTop (𝓝 (P i x)) ∧
        Tendsto (fun k => gradient (Pk k) x) atTop (𝓝 (G i x)) := by
      filter_upwards [hsph] with x hx _
      obtain ⟨t1, t2⟩ := p.tendsto_profK hx
      refine ⟨t1.mul_const _, ?_⟩
      simp only [hgrad, G]
      exact (((t2.mul_const 2).mul_const _).smul_const _).add (t1.smul_const _)
    refine ⟨?_, ?_⟩
    · have hall := ae_all_iff.2 hbd
      filter_upwards [hall, hconv] with x h1 h2 hux
      obtain ⟨t1, t2⟩ := h2 hux
      exact ⟨le_of_tendsto' t1.abs fun k => (h1 k hux).1,
        le_of_tendsto' t2.norm fun k => (h1 k hux).2⟩
    · have key := gap_lim hN hD hu Pk hPks (P i) (G i) hbd hconv
      have hci : ∫ x, P i x * u1 x ^ 2 = 0 := hc (b i)
      rw [hci] at key
      have : ((eigenvalue D 2 - eigenvalue D 1) * ∫ x, P i x ^ 2 * u1 x ^ 2) *
          ∫ x, u1 x ^ 2 ≤ (∫ x, ‖G i x‖ ^ 2 * u1 x ^ 2) * ∫ x, u1 x ^ 2 := by
        nlinarith
      exact le_of_mul_le_mul_right this hpos
  -- integrability of the summands
  have hPc : ∀ i, Continuous (P i) := fun i =>
    (p.continuous_prof.comp hnc).mul ((continuous_id.sub continuous_const).inner continuous_const)
  have hGm : ∀ i, Measurable (G i) := fun i => by
    have h1 : Measurable fun x : RN N => p.dprof (‖x - c‖ ^ 2) * 2 * ⟪x - c, b i⟫ :=
      ((hdm.comp hnc.measurable).mul_const 2).mul
        ((continuous_id.sub continuous_const).inner continuous_const).measurable
    exact (h1.smul (continuous_id.sub continuous_const).measurable).add
      ((p.continuous_prof.comp hnc).measurable.smul_const _)
  have iP : ∀ i, Integrable fun x => P i x ^ 2 * u1 x ^ 2 := fun i => by
    refine integrable_mul_sq_of_bdd hint ((hPc i).pow 2).aestronglyMeasurable hu1m (K := K ^ 2) ?_
    filter_upwards [(comp i).1] with x hx hux
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hx hux).1 2
  have iG : ∀ i, Integrable fun x => ‖G i x‖ ^ 2 * u1 x ^ 2 := fun i => by
    refine integrable_mul_sq_of_bdd hint ((hGm i).norm.pow_const 2).aestronglyMeasurable hu1m
      (K := K ^ 2) ?_
    filter_upwards [(comp i).1] with x hx hux
    rw [abs_pow, abs_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hx hux).2 2
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (comp i).2
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => iP i,
    ← integral_finsetSum _ fun i _ => iG i] at hsum
  have eL : (fun x => ∑ i, P i x ^ 2 * u1 x ^ 2) = fun x => p.Gw (‖x - c‖ ^ 2) * u1 x ^ 2 := by
    funext x
    rw [← Finset.sum_mul, ABProfile.Gw]
    congr 1
    exact sum_sq_radial (x - c) _
  have eR : (fun x => ∑ i, ‖G i x‖ ^ 2 * u1 x ^ 2) = fun x => p.Bw (‖x - c‖ ^ 2) * u1 x ^ 2 := by
    funext x
    rw [← Finset.sum_mul, ABProfile.Bw]
    congr 1
    exact sum_norm_sq_radial (x - c) _ _
  rw [eL, eR] at hsum
  exact hsum

end FourthRatio

end

module

public import RequestProject.Truncation

/-!
# Tools for the ball–annulus lemma

* closability: elements of `H_D` are determined by their first component;
* the pair `(φ, ∇φ)` of a test function, and multiplication of `H_D` by cut-off functions;
* a local-to-global principle for almost-everywhere statements;
* the variational characterisation of eigenfunctions;
* a constancy lemma: on a domain `U`, a measurable set `S` such that restriction to `S`
  preserves `H_U` is either null or conull in `U` (proved with the simplicity of the ground
  state);
* connectedness of annuli.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Closability -/

/-- Two elements of `H_D` (`D ∈ 𝒪_N`) with the same first component coincide. -/
lemma eq_of_fst_eq {D : Set (RN N)} {p q : Amb N}
    (hp : p ∈ H D) (hq : q ∈ H D) (h : p.1 = q.1) : p = q := by
  have := eq_zero_of_l2_self_eq_zero ((H D).sub_mem hp hq)
    (by rw [l2, Prod.fst_sub, h, sub_self, inner_zero_left])
  exact sub_eq_zero.mp this

/-! ### Multiplication by cut-off functions preserves `H_D` -/

lemma Mpair_mem_testGraph_self {χ : RN N → ℝ} (hχ : Continuous χ) (hg : Continuous (gradient χ))
    {C : ℝ} (hC : ∀ x, |χ x| ≤ C ∧ ‖gradient χ x‖ ≤ C)
    (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {D : Set (RN N)} {p : Amb N}
    (hp : p ∈ testGraph D) : Mpair hχ hg hC p ∈ testGraph D := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  refine ⟨fun y => χ y * φ y, hχs.mul h1, h2.mul_left, tsupport_mul_subset_right.trans h3,
    ?_, ?_⟩
  · filter_upwards [Mpair_fst_ae hχ hg hC p, h4] with x a b
    rw [a, b]
  · filter_upwards [Mpair_snd_ae hχ hg hC p, h4, h5] with x a b c
    rw [a, b, c]
    have hx1 := (hχs.differentiable (by simp)) x
    have hx2 := (h1.differentiable (by simp)) x
    rw [gradient, gradient, gradient, fderiv_fun_mul hx1 hx2, map_add, map_smul, map_smul]

lemma Mpair_mem_H_self {χ : RN N → ℝ} (hχ : Continuous χ) (hg : Continuous (gradient χ))
    {C : ℝ} (hC : ∀ x, |χ x| ≤ C ∧ ‖gradient χ x‖ ≤ C)
    (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {D : Set (RN N)} {p : Amb N}
    (hp : p ∈ H D) : Mpair hχ hg hC p ∈ H D := by
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  exact mem_H_of_tendsto (fun k => testGraph_subset_H D
    (Mpair_mem_testGraph_self hχ hg hC hχs (hqT k))) (Mpair_tendsto hχ hg hC hq)

/-! ### Restriction to a measurable set -/

lemma restrictTo_fst_ae {S : Set (RN N)} (hS : MeasurableSet S) (p : Amb N) :
    ((restrictTo S p).1 : RN N → ℝ) =ᵐ[volume] S.indicator (p.1 : RN N → ℝ) := by
  rw [restrictTo, dif_pos hS]; exact indL2_ae S hS p.1

lemma restrictTo_snd_ae {S : Set (RN N)} (hS : MeasurableSet S) (p : Amb N) :
    ((restrictTo S p).2 : RN N → RN N) =ᵐ[volume] S.indicator (p.2 : RN N → RN N) := by
  rw [restrictTo, dif_pos hS]; exact indL2v_ae S hS p.2

lemma restrictTo_tendsto {S : Set (RN N)} (hS : MeasurableSet S) {q : ℕ → Amb N} {p : Amb N}
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun k => restrictTo S (q k)) atTop (𝓝 (restrictTo S p)) := by
  have h1 : Tendsto (fun k => ‖(q k).1 - p.1‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_fst.tendsto p).comp hq)
  have h2 : Tendsto (fun k => ‖(q k).2 - p.2‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_snd.tendsto p).comp hq)
  have hf : Tendsto (fun k => (restrictTo S (q k)).1) atTop (𝓝 (restrictTo S p).1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(restrictTo S (q k)).1 - (restrictTo S p).1‖ ≤
        1 * ‖(q k).1 - p.1‖ + 0 * ‖(q k).1 - p.1‖ := fun k => by
      refine Lp2_norm_le_add _ _ _ zero_le_one le_rfl ?_
      filter_upwards [Lp.coeFn_sub (restrictTo S (q k)).1 (restrictTo S p).1,
        Lp.coeFn_sub (q k).1 p.1, restrictTo_fst_ae hS (q k), restrictTo_fst_ae hS p]
        with x a b c d
      rw [a, Pi.sub_apply, c, d, b, Pi.sub_apply, zero_mul, add_zero, one_mul]
      by_cases hxS : x ∈ S <;> simp [hxS]
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    simpa using h1
  have hs : Tendsto (fun k => (restrictTo S (q k)).2) atTop (𝓝 (restrictTo S p).2) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(restrictTo S (q k)).2 - (restrictTo S p).2‖ ≤
        1 * ‖(q k).2 - p.2‖ + 0 * ‖(q k).2 - p.2‖ := fun k => by
      refine Lp2_norm_le_add _ _ _ zero_le_one le_rfl ?_
      filter_upwards [Lp.coeFn_sub (restrictTo S (q k)).2 (restrictTo S p).2,
        Lp.coeFn_sub (q k).2 p.2, restrictTo_snd_ae hS (q k), restrictTo_snd_ae hS p]
        with x a b c d
      rw [a, Pi.sub_apply, c, d, b, Pi.sub_apply, zero_mul, add_zero, one_mul]
      by_cases hxS : x ∈ S <;> simp [hxS]
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    simpa using h2
  exact hf.prodMk_nhds hs

/-! ### Local-to-global for almost everywhere statements -/

lemma ae_of_local {U : Set (RN N)} {P : RN N → Prop}
    (h : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∀ᵐ z, z ∈ V → P z) : ∀ᵐ z, z ∈ U → P z := by
  classical
  choose! V hV hP using h
  set W : U → Set (RN N) := fun x => interior (V x)
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

/-! ### Variational characterisation -/

/-- If a symmetric shifted form is nonnegative on a subspace `W` and vanishes at `v ∈ W`, then
`v` is in its kernel on `W`. -/
lemma bshift_eq_zero_of_min {W : Submodule ℝ (Amb N)} {b : ℝ}
    (hpos : ∀ w ∈ W, 0 ≤ bshift b w w) {v : Amb N} (hv : v ∈ W) (h0 : bshift b v v = 0) :
    ∀ w ∈ W, bshift b v w = 0 := by
  intro w hw
  have key : ∀ t : ℝ, 0 ≤ 2 * t * bshift b v w + t ^ 2 * bshift b w w := fun t => by
    have := hpos (v + t • w) (W.add_mem hv (W.smul_mem t hw))
    have e : bshift b (v + t • w) (v + t • w) =
        bshift b v v + 2 * t * bshift b v w + t ^ 2 * bshift b w w := by
      simp only [bshift, qf_add_left, qf_add_right, qf_smul_left, qf_smul_right, l2_add_left,
        l2_add_right, l2_smul_left, l2_smul_right]
      rw [qf_comm w v, l2_comm w v]
      ring
    rw [e, h0] at this
    linarith
  set B := bshift b v w
  set Q := bshift b w w
  have hQ : 0 ≤ Q := hpos w hw
  have hQ1 : 0 < Q + 1 := by linarith
  have h1 := key (-B / (Q + 1))
  have h2 : (Q + 1) ^ 2 * (2 * (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q) =
      -(B ^ 2 * (Q + 2)) := by
    field_simp
    ring
  have h3 : 0 ≤ (Q + 1) ^ 2 * (2 * (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q) :=
    mul_nonneg (by positivity) h1
  rw [h2] at h3
  have : B ^ 2 * (Q + 2) = 0 := le_antisymm (by linarith) (by positivity)
  rcases mul_eq_zero.mp this with h | h
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  · linarith

/-- A minimiser of the Rayleigh quotient is a first eigenfunction. -/
lemma isEigenfunction_of_rayleigh_min {D : Set (RN N)}
    {v : Amb N} (hv : v ∈ H D) (hv0 : v ≠ 0) (h : qf v v = eigenvalue D 1 * l2 v v) :
    IsEigenfunction D v (eigenvalue D 1) := by
  have hpos : ∀ w ∈ H D, 0 ≤ bshift (eigenvalue D 1) w w := by
    intro w hw
    by_cases hw0 : w = 0
    · simp [hw0, bshift]
    have hl := l2_self_pos hw hw0
    have := eigenvalue_one_le_rayleigh hw hw0
    rw [rayleigh, le_div_iff₀ hl] at this
    simp only [bshift]
    linarith
  have h0 : bshift (eigenvalue D 1) v v = 0 := by simp only [bshift]; linarith
  refine ⟨hv, hv0, fun φ hφ => ?_⟩
  have := bshift_eq_zero_of_min hpos hv h0 φ hφ
  simp only [bshift] at this
  linarith

/-! ### Constancy -/

/-- **Constancy lemma.** Let `U` be a domain and `S` a measurable set such that restricting test
pairs of `U` to `S` stays in `H_U`.  Then `S ∩ U` is null or `U \ S` is null.  (Proof: restrict
the positive ground state of `U` to `S` and to its complement; both pieces are Rayleigh
minimisers, hence multiples of the ground state.) -/
lemma constancy_of_restrict (hN : 2 ≤ N) {U : Set (RN N)} (hU : IsDomain U) {S : Set (RN N)}
    (hS : MeasurableSet S) (h : ∀ p ∈ testGraph U, restrictTo S p ∈ H U) :
    volume (U ∩ S) = 0 ∨ volume (U \ S) = 0 := by
  obtain ⟨hsimp, e, fe, he, hfe, hpos⟩ := ground_state hN hU
  have hUadm := hU.1
  have hUm : MeasurableSet U := hU.1.1.measurableSet
  have hz : restrictTo S e ∈ H U := by
    obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph he.1
    exact mem_H_of_tendsto (fun k => h _ (hqT k)) (restrictTo_tendsto hS hq)
  set z := restrictTo S e with hz_def
  have hz' : e - z ∈ H U := (H U).sub_mem he.1 hz
  have z1 := restrictTo_fst_ae hS e
  have z2 := restrictTo_snd_ae hS e
  have hfeU : ∀ᵐ x, x ∈ U → (e.1 : RN N → ℝ) x = fe x := (ae_restrict_iff' hUm).mp hfe.2
  have hqz : qf z (e - z) = 0 := by
    rw [qf, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [z2, Lp.coeFn_sub e.2 z.2] with x a b
    rw [Prod.snd_sub, b, Pi.sub_apply, a]
    by_cases hx : x ∈ S <;> simp [hx]
  have hlz : l2 z (e - z) = 0 := by
    rw [l2, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [z1, Lp.coeFn_sub e.1 z.1] with x a b
    rw [Prod.fst_sub, b, Pi.sub_apply, a]
    by_cases hx : x ∈ S <;> simp [hx]
  have hsplit : e = z + (e - z) := by abel
  have hqe : qf e e = qf z z + qf (e - z) (e - z) := by
    conv_lhs => rw [hsplit]
    rw [qf_add_left, qf_add_right, qf_add_right, hqz, qf_comm (e - z) z, hqz]
    ring
  have hle : l2 e e = l2 z z + l2 (e - z) (e - z) := by
    conv_lhs => rw [hsplit]
    rw [l2_add_left, l2_add_right, l2_add_right, hlz, l2_comm (e - z) z, hlz]
    ring
  have hlam : qf e e = eigenvalue U 1 * l2 e e := he.2.2 e he.1
  by_cases hz0 : z = 0
  · left
    rw [measure_eq_zero_iff_ae_notMem]
    have h0 : (z.1 : RN N → ℝ) =ᵐ[volume] 0 := by rw [hz0]; exact Lp.coeFn_zero _ _ _
    filter_upwards [z1, h0, hfeU] with x a b c hx
    rw [b, Set.indicator_of_mem hx.2, c hx.1] at a
    exact (hpos x hx.1).ne' (by simpa using a.symm)
  by_cases hz'0 : e - z = 0
  · right
    rw [measure_eq_zero_iff_ae_notMem]
    have h0 : ((e - z).1 : RN N → ℝ) =ᵐ[volume] 0 := by rw [hz'0]; exact Lp.coeFn_zero _ _ _
    filter_upwards [z1, h0, hfeU, Lp.coeFn_sub e.1 z.1] with x a b c d hx
    rw [Prod.fst_sub] at b
    rw [b, Pi.sub_apply, a, Set.indicator_of_notMem hx.2, c hx.1] at d
    exact (hpos x hx.1).ne' (by simpa using d.symm)
  have r1 := eigenvalue_one_le_rayleigh hz hz0
  have r2 := eigenvalue_one_le_rayleigh hz' hz'0
  have l1 := l2_self_pos hz hz0
  have l2' := l2_self_pos hz' hz'0
  rw [rayleigh, le_div_iff₀ l1] at r1
  rw [rayleigh, le_div_iff₀ l2'] at r2
  have hmin : qf z z = eigenvalue U 1 * l2 z z := by
    rw [hqe, hle] at hlam
    linarith
  have hzeig := isEigenfunction_of_rayleigh_min hz hz0 hmin
  obtain ⟨s, hs⟩ := hsimp e z he hzeig
  by_cases hs1 : s = 1
  · exact absurd (by rw [hs, hs1, one_smul, sub_self]) hz'0
  · left
    rw [measure_eq_zero_iff_ae_notMem]
    have hz1' : (z.1 : RN N → ℝ) =ᵐ[volume] fun x => s * (e.1 : RN N → ℝ) x := by
      rw [hs]
      filter_upwards [Lp.coeFn_smul s e.1] with x hx
      rw [Prod.smul_fst, hx, Pi.smul_apply, smul_eq_mul]
    filter_upwards [z1, hz1', hfeU] with x a b c hx
    rw [b, Set.indicator_of_mem hx.2, c hx.1] at a
    have : (1 - s) * fe x = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hs1 (by linarith)
    · exact (hpos x hx.1).ne' h'

/-! ### Annuli -/

lemma isConnected_annulus (hN : 2 ≤ N) (y : RN N) {R R' : ℝ} (hR : 0 ≤ R) (hRR : R < R') :
    IsConnected {x : RN N | R < ‖x - y‖ ∧ ‖x - y‖ < R'} := by
  have hrank : 1 < Module.rank ℝ (RN N) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < N)
  set f : RN N × ℝ → RN N := fun p => y + p.2 • p.1
  have hS : IsConnected (sphere (0 : RN N) 1 ×ˢ Set.Ioo R R') :=
    (isConnected_sphere hrank 0 zero_le_one).prod (isConnected_Ioo hRR)
  have himg : f '' (sphere 0 1 ×ˢ Set.Ioo R R') = {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} := by
    ext x
    constructor
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, rfl⟩
      simp only [mem_sphere_iff_norm, sub_zero] at hv
      have : ‖y + r • v - y‖ = r := by
        rw [add_sub_cancel_left, norm_smul, hv, mul_one,
          Real.norm_of_nonneg (by linarith [hr.1])]
      simp only [f, Set.mem_setOf_eq, this]
      exact hr
    · rintro ⟨h1, h2⟩
      have hne : ‖x - y‖ ≠ 0 := by linarith
      refine ⟨(‖x - y‖⁻¹ • (x - y), ‖x - y‖), ⟨?_, h1, h2⟩, ?_⟩
      · simp [norm_smul, hne]
      · simp [f, smul_smul, hne]
  rw [← himg]
  exact hS.image f (by fun_prop)

/-- A smooth function divided by a function that is smooth and nonvanishing on an open
neighbourhood of its support is smooth. -/
lemma contDiff_div_of_tsupport {ψ g : RN N → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    {U : Set (RN N)} (hU : IsOpen U) (hsupp : tsupport ψ ⊆ U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (hg0 : ∀ x ∈ U, g x ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ψ x / g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport ψ
  · exact hψ.contDiffAt.div (hg.contDiffAt (hU.mem_nhds (hsupp hx))) (hg0 x (hsupp hx))
  · have h0 : (fun x => ψ x / g x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp hx] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq h0

end FourthRatio

end

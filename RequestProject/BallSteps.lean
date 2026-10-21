module

public import RequestProject.BallTools
public import RequestProject.BallIntegrals

/-!
# Steps of the proof of the ball–annulus lemma

Throughout, `u ∈ H_Ω` agrees almost everywhere on `Ω` with a smooth function `g` (in the
application `g = c Φ(· - y)`, by unique continuation for analytic functions).

* `grad_eq_on_of_fst_eq`: then the weak gradient of `u` is `∇g` almost everywhere on `Ω`;
* `Mpair_eq_restrictTo`: the multiplier `χ u` is the restriction to `Ω` of the test pair of `χ g`;
* `restrictTo_testGraph_mem`: on an open set `E` where `g ≠ 0`, restricting test pairs of `E`
  to `Ω` stays in `H_Ω` and in `H_E` (multiplier `(ψ / g) u`);
* `measure_diff_eq_zero_of_connected`: if moreover `E` is connected and meets `Ω`, then
  `E ⊆ Ω` up to a null set (constancy lemma; this is the paper's "`{0,1}`-valued Sobolev
  function" step);
* `H_le_of_measure_diff`: and then `H_E ⊆ H_Ω`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma gradient_mul_of_contDiff {φ ψ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (x : RN N) :
    gradient (fun y => φ y * ψ y) x = φ x • gradient ψ x + ψ x • gradient φ x := by
  have hx1 := (hφ.differentiable (by simp)) x
  have hx2 := (hψ.differentiable (by simp)) x
  rw [gradient, gradient, gradient, fderiv_fun_mul hx1 hx2, map_add, map_smul, map_smul]

lemma gradient_eq_zero_of_eqOn_one {φ : RN N → ℝ} {U : Set (RN N)} (hU : IsOpen U)
    (h1 : ∀ x ∈ U, φ x = 1) {x : RN N} (hx : x ∈ U) : gradient φ x = 0 := by
  have : φ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => h1 y hy
  rw [this.gradient_eq]
  exact gradient_fun_const x 1

lemma vanish_off_of_mem_H {Ω : Set (RN N)} (hΩ : IsOpen Ω) {u : Amb N} (huH : u ∈ H Ω) :
    (∀ᵐ x, x ∉ Ω → (u.1 : RN N → ℝ) x = 0) ∧ (∀ᵐ x, x ∉ Ω → (u.2 : RN N → RN N) x = 0) := by
  obtain ⟨h1, h2⟩ := mem_vanishOn.mp (H_le_vanishOn Ω huH)
  exact ⟨(ae_restrict_iff' hΩ.measurableSet.compl).mp h1,
    (ae_restrict_iff' hΩ.measurableSet.compl).mp h2⟩

lemma testPair_congr {φ ψ : RN N → ℝ} (h : φ = ψ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc' : HasCompactSupport ψ) : testPair φ hφ hc = testPair ψ hψ hc' := by
  subst h; rfl

section Steps

variable (hN : 2 ≤ N) {Ω : Set (RN N)} (hΩ : IsAdmissible Ω) {u : Amb N} (huH : u ∈ H Ω)
  {g : RN N → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
  (hug : ∀ᵐ x, x ∈ Ω → (u.1 : RN N → ℝ) x = g x)

include hΩ huH hg hug in
/-- The weak gradient of `u` is the classical gradient of `g` almost everywhere on `Ω`. -/
lemma grad_eq_on_of_fst_eq : ∀ᵐ x, x ∈ Ω → (u.2 : RN N → RN N) x = gradient g x := by
  have hoff1 := (vanish_off_of_mem_H hΩ.1 huH).1
  refine ae_of_local fun x0 hx0 => ?_
  obtain ⟨φ, hφs, hφc, hφΩ, U, hU, hx0U, hU1⟩ :=
    exists_cutoff isCompact_singleton hΩ.1 (Set.singleton_subset_iff.mpr hx0)
  obtain ⟨hgφ, C, -, hC⟩ := exists_bound_cutoff hφs hφc
  have hM : Mpair hφs.continuous hgφ hC u ∈ H Ω := Mpair_mem_H_self _ _ _ hφs huH
  have hT : testPair (fun x => φ x * g x) (hφs.mul hg) hφc.mul_right ∈ H Ω :=
    testGraph_subset_H Ω (testPair_mem _ _ (tsupport_mul_subset_left.trans hφΩ))
  have heq : Mpair hφs.continuous hgφ hC u =
      testPair (fun x => φ x * g x) (hφs.mul hg) hφc.mul_right := by
    refine eq_of_fst_eq hM hT (Lp.ext ?_)
    filter_upwards [Mpair_fst_ae hφs.continuous hgφ hC u,
      MemLp.coeFn_toLp (memLp_of_testFun (hφs.mul hg) hφc.mul_right), hug, hoff1]
      with x a b c d
    rw [a]
    simp only [testPair]
    rw [b]
    by_cases hx : x ∈ Ω
    · rw [c hx]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφΩ h)), zero_mul, zero_mul]
  refine ⟨U, hU.mem_nhds (hx0U (Set.mem_singleton x0)), ?_⟩
  have h2 : (Mpair hφs.continuous hgφ hC u).2 =
      (testPair (fun x => φ x * g x) (hφs.mul hg) hφc.mul_right).2 := congrArg Prod.snd heq
  filter_upwards [Mpair_snd_ae hφs.continuous hgφ hC u,
    MemLp.coeFn_toLp (memLp_gradient_of_testFun (hφs.mul hg) hφc.mul_right)] with x a b hxU
  have hb : ((testPair (fun x => φ x * g x) (hφs.mul hg) hφc.mul_right).2 : RN N → RN N) x =
      gradient (fun x => φ x * g x) x := b
  rw [← h2, a, gradient_mul_of_contDiff hφs hg, hU1 x hxU,
    gradient_eq_zero_of_eqOn_one hU hU1 hxU] at hb
  simpa using hb

include hΩ huH hg hug in
/-- The multiplier `χ u` is the restriction to `Ω` of the test pair of `χ g`. -/
lemma Mpair_eq_restrictTo {χ : RN N → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ : Continuous χ) (hgχ : Continuous (gradient χ)) {C : ℝ}
    (hC : ∀ x, |χ x| ≤ C ∧ ‖gradient χ x‖ ≤ C) :
    Mpair hχ hgχ hC u = restrictTo Ω (testPair (fun x => χ x * g x) (hχs.mul hg) hχc.mul_right) := by
  have hgrad := grad_eq_on_of_fst_eq hΩ huH hg hug
  obtain ⟨hoff1, hoff2⟩ := vanish_off_of_mem_H hΩ.1 huH
  have hΩm := hΩ.1.measurableSet
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [Mpair_fst_ae hχ hgχ hC u,
      restrictTo_fst_ae hΩm (testPair (fun x => χ x * g x) (hχs.mul hg) hχc.mul_right),
      MemLp.coeFn_toLp (memLp_of_testFun (hχs.mul hg) hχc.mul_right), hug, hoff1]
      with x a b c d e
    rw [a, b]
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
      simp only [testPair]
      rw [c, d hx]
    · rw [Set.indicator_of_notMem hx, e hx, mul_zero]
  · filter_upwards [Mpair_snd_ae hχ hgχ hC u,
      restrictTo_snd_ae hΩm (testPair (fun x => χ x * g x) (hχs.mul hg) hχc.mul_right),
      MemLp.coeFn_toLp (memLp_gradient_of_testFun (hχs.mul hg) hχc.mul_right), hug, hoff1,
      hoff2, hgrad] with x a b c d e f h
    rw [a, b]
    by_cases hx : x ∈ Ω
    · rw [Set.indicator_of_mem hx]
      simp only [testPair]
      rw [c, gradient_mul_of_contDiff hχs hg, d hx, h hx]
    · rw [Set.indicator_of_notMem hx, e hx, f hx, smul_zero, zero_smul, add_zero]

include hΩ huH hg hug in
/-- On an open set `E` where `g ≠ 0`, restricting test pairs of `E` to `Ω` stays in `H_Ω` and
in `H_E`. -/
lemma restrictTo_testGraph_mem {E : Set (RN N)} (hE : IsOpen E) (hg0 : ∀ x ∈ E, g x ≠ 0)
    {p : Amb N} (hp : p ∈ testGraph E) : restrictTo Ω p ∈ H Ω ∧ restrictTo Ω p ∈ H E := by
  obtain ⟨ψ, hψs, hψc, hψE, rfl⟩ := eq_testPair hp
  set χ : RN N → ℝ := fun x => ψ x / g x with hχ_def
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    contDiff_div_of_tsupport hψs hE hψE hg.contDiffOn hg0
  have hsupp : Function.support χ ⊆ Function.support ψ := fun x hx h0 =>
    hx (by simp [hχ_def, h0])
  have hχc : HasCompactSupport χ := hψc.mono hsupp
  have htχ : tsupport χ ⊆ tsupport ψ := closure_mono hsupp
  obtain ⟨hgχ, C, -, hC⟩ := exists_bound_cutoff hχs hχc
  have hprod : (fun x => χ x * g x) = ψ := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · exact div_mul_cancel₀ _ (hg0 x (hψE hx))
    · simp [hχ_def, image_eq_zero_of_notMem_tsupport hx]
  have heq : Mpair hχs.continuous hgχ hC u = restrictTo Ω (testPair ψ hψs hψc) := by
    rw [Mpair_eq_restrictTo hΩ huH hg hug hχs hχc hχs.continuous hgχ hC,
      testPair_congr hprod]
  rw [← heq]
  exact ⟨Mpair_mem_H_self _ _ _ hχs huH,
    Mpair_mem_H hχs.continuous hgχ hC hχs (htχ.trans hψE) huH⟩

include hN hΩ huH hg hug in
/-- If `E` is a connected open set meeting `Ω` on which `g ≠ 0`, then `E ⊆ Ω` up to a null
set. -/
lemma measure_diff_eq_zero_of_connected {E : Set (RN N)} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hg0 : ∀ x ∈ E, g x ≠ 0) (hEΩ : (E ∩ Ω).Nonempty) :
    volume (E \ Ω) = 0 := by
  have hΩm := hΩ.1.measurableSet
  have hcon : ∀ x r, 0 < r → ball x r ⊆ E →
      volume (ball x r ∩ Ω) = 0 ∨ volume (ball x r \ Ω) = 0 := by
    intro x r hr hsub
    refine constancy_of_restrict hN (isDomain_ball x hr) hΩm fun p hp => ?_
    exact (restrictTo_testGraph_mem hΩ huH hg hug isOpen_ball
      (fun z hz => hg0 z (hsub hz)) hp).2
  set T := {x : RN N | ∃ r > 0, ball x r ⊆ E ∧ volume (ball x r \ Ω) = 0} with hT
  set T' := {x : RN N | ∃ r > 0, ball x r ⊆ E ∧ volume (ball x r ∩ Ω) = 0} with hT'
  have hsmall : ∀ (x : RN N) (r : ℝ) (z : RN N), z ∈ ball x r →
      ball z (r - dist z x) ⊆ ball x r := fun x r z _ =>
    ball_subset_ball' (by linarith : r - dist z x + dist z x ≤ r)
  have hTo : IsOpen T := by
    rw [Metric.isOpen_iff]
    rintro x ⟨r, hr, hsub, h0⟩
    refine ⟨r, hr, fun z hz => ⟨r - dist z x, by linarith [mem_ball.mp hz],
      (hsmall x r z hz).trans hsub, measure_mono_null ?_ h0⟩⟩
    exact Set.diff_subset_diff_left (hsmall x r z hz)
  have hT'o : IsOpen T' := by
    rw [Metric.isOpen_iff]
    rintro x ⟨r, hr, hsub, h0⟩
    refine ⟨r, hr, fun z hz => ⟨r - dist z x, by linarith [mem_ball.mp hz],
      (hsmall x r z hz).trans hsub, measure_mono_null ?_ h0⟩⟩
    exact Set.inter_subset_inter_left _ (hsmall x r z hz)
  have hdisj : Disjoint T T' := by
    rw [Set.disjoint_left]
    rintro x ⟨r1, hr1, -, h1⟩ ⟨r2, hr2, -, h2⟩
    have hm : 0 < min r1 r2 := lt_min hr1 hr2
    have hpos := measure_ball_pos (volume : Measure (RN N)) x hm
    have e := measure_inter_add_diff (ball x (min r1 r2)) hΩm (μ := volume)
    have a1 : volume (ball x (min r1 r2) ∩ Ω) = 0 :=
      measure_mono_null (Set.inter_subset_inter_left _ (ball_subset_ball (min_le_right _ _))) h2
    have a2 : volume (ball x (min r1 r2) \ Ω) = 0 :=
      measure_mono_null (Set.diff_subset_diff_left (ball_subset_ball (min_le_left _ _))) h1
    rw [a1, a2, add_zero] at e
    exact hpos.ne' e.symm
  have hcover : E ⊆ T ∪ T' := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hE x hx
    rcases hcon x r hr hsub with h | h
    · exact Or.inr ⟨r, hr, hsub, h⟩
    · exact Or.inl ⟨r, hr, hsub, h⟩
  have hne : (E ∩ T).Nonempty := by
    obtain ⟨x0, hx0E, hx0Ω⟩ := hEΩ
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hE.inter hΩ.1) x0 ⟨hx0E, hx0Ω⟩
    refine ⟨x0, hx0E, r, hr, fun z hz => (hsub hz).1, ?_⟩
    rw [Set.diff_eq_empty.mpr (fun z hz => (hsub hz).2), measure_empty]
  have hET : E ⊆ T := hEc.subset_left_of_subset_union hTo hT'o hdisj hcover hne
  have hae : ∀ᵐ z, z ∈ E → z ∈ Ω := by
    refine ae_of_local fun x hx => ?_
    obtain ⟨r, hr, -, h0⟩ := hET hx
    refine ⟨ball x r, ball_mem_nhds x hr, ?_⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with z hz hzb
    by_contra hzΩ
    exact hz ⟨hzb, hzΩ⟩
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with z hz hzd
  exact hzd.2 (hz hzd.1)

include hΩ huH hg hug in
/-- If `E` is open, `g ≠ 0` on `E` and `E ⊆ Ω` up to a null set, then `H_E ⊆ H_Ω`. -/
lemma H_le_of_measure_diff {E : Set (RN N)} (hE : IsOpen E) (hg0 : ∀ x ∈ E, g x ≠ 0)
    (hEΩ : volume (E \ Ω) = 0) : H E ≤ H Ω := by
  have hΩm := hΩ.1.measurableSet
  have hle : Submodule.span ℝ (testGraph E) ≤ H Ω := by
    rw [Submodule.span_le]
    intro p hp
    have hmem := (restrictTo_testGraph_mem hΩ huH hg hug hE hg0 hp).1
    obtain ⟨ψ, hψs, hψc, hψE, rfl⟩ := eq_testPair hp
    have hae : ∀ᵐ z, z ∉ Ω → z ∉ E := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hEΩ] with z hz hzΩ hzE
      exact hz ⟨hzE, hzΩ⟩
    have heq : restrictTo Ω (testPair ψ hψs hψc) = testPair ψ hψs hψc := by
      refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
      · filter_upwards [restrictTo_fst_ae hΩm (testPair ψ hψs hψc), hae,
          MemLp.coeFn_toLp (memLp_of_testFun hψs hψc)] with z a b c
        rw [a]
        by_cases hz : z ∈ Ω
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          simp only [testPair]
          rw [c, image_eq_zero_of_notMem_tsupport (fun h => b hz (hψE h))]
      · filter_upwards [restrictTo_snd_ae hΩm (testPair ψ hψs hψc), hae,
          MemLp.coeFn_toLp (memLp_gradient_of_testFun hψs hψc)] with z a b c
        rw [a]
        by_cases hz : z ∈ Ω
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          simp only [testPair]
          rw [c]
          have hzs : z ∉ tsupport ψ := fun h => b hz (hψE h)
          simp [gradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hzs]
    rw [← heq]
    exact hmem
  exact Submodule.topologicalClosure_minimal _ hle
    (Submodule.isClosed_topologicalClosure _)

end Steps

end FourthRatio

end

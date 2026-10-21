module

public import RequestProject.BallFinal
public import RequestProject.BesselGap
public import RequestProject.BallSpectral
public import RequestProject.BallDegreeOne

/-!
# The ball–annulus lemma (Section 4 of the paper)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}


lemma nontrivial_RN (hN : 2 ≤ N) : Nontrivial (RN N) := by
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  infer_instance

/-- A continuous function positive on the open ball `‖x‖ < R` is nonnegative on `‖x‖ ≤ R`. -/
lemma nonneg_of_norm_le {Φ : RN N → ℝ} (hΦ : Continuous Φ) {R : ℝ} (hR : 0 < R)
    (hpos : ∀ x, ‖x‖ < R → 0 < Φ x) {x : RN N} (hx : ‖x‖ ≤ R) : 0 ≤ Φ x := by
  have hcl : IsClosed {x : RN N | 0 ≤ Φ x} := isClosed_le continuous_const hΦ
  have hsub : ball (0 : RN N) R ⊆ {x | 0 ≤ Φ x} := fun z hz =>
    (hpos z (by simpa using hz)).le
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_ball _ hR.ne'] at this
  exact this (by simpa using hx)

/-- A connected set containing a point inside `B_R(y)` and a point outside `closedBall y R` meets
the annulus `R < |x - y| < R'`. -/
lemma exists_mem_annulus {Ω : Set (RN N)} (hΩ : IsPreconnected Ω) {y x0 z : RN N} {R R' : ℝ}
    (hRR : R < R') (hx0 : x0 ∈ Ω) (hx0R : ‖x0 - y‖ < R) (hz : z ∈ Ω) (hzR : R < ‖z - y‖) :
    ∃ w ∈ Ω, R < ‖w - y‖ ∧ ‖w - y‖ < R' := by
  set m := min ‖z - y‖ ((R + R') / 2)
  have hm : m ∈ Set.Icc ‖x0 - y‖ ‖z - y‖ := by
    refine ⟨?_, min_le_left _ _⟩
    rw [le_min_iff]; constructor <;> linarith
  obtain ⟨w, hw, hwm⟩ := hΩ.intermediate_value hx0 hz
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn hm
  change ‖w - y‖ = m at hwm
  refine ⟨w, hw, ?_, ?_⟩ <;> rw [hwm]
  · rw [lt_min_iff]; constructor <;> linarith
  · exact (min_le_right _ _).trans_lt (by linarith)

/-- The ball gap `(N-1)/R² < C_N a - a` for `R = j_{N/2-1,1}/√a`, from the Bessel zero
inequality `j_{ν,1}² + (2ν+1) < j_{ν+1,1}²` (`besselZero_sq_gap`). -/
lemma ball_gap (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    ((N : ℝ) - 1) / (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a) ^ 2 < CN N * a - a := by
  have hν : 0 ≤ (N : ℝ) / 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hgap := besselZero_sq_gap hν
  rw [show (N : ℝ) / 2 - 1 + 1 = (N : ℝ) / 2 by ring,
    show 2 * ((N : ℝ) / 2 - 1) + 1 = (N : ℝ) - 1 by ring] at hgap
  have hj := (besselZero_props hν).1
  unfold CN
  set j := besselZero ((N : ℝ) / 2 - 1) 1
  set k := besselZero ((N : ℝ) / 2) 1
  have hj2 : 0 < j ^ 2 := by positivity
  rw [div_pow, Real.sq_sqrt ha.le, div_div_eq_mul_div, div_lt_iff₀ hj2]
  have e : (k ^ 2 / j ^ 2 * a - a) * j ^ 2 = (k ^ 2 - j ^ 2) * a := by
    field_simp
  rw [e]
  nlinarith

/-- **Lemma 4.1 (Ball–annulus estimate).** Let `Ω` be a bounded domain and `u` a
sign-changing eigenfunction (with continuous representative `f`) with eigenvalue `a > 0`.  Suppose that one nodal component `G` (a
connected component of `{u > 0}` or of `{u < 0}`) is, after a translation, a ball ground state:
the zero extension of `u|_G` agrees a.e. with a nonzero multiple of the first eigenfunction
`Φ(· - y) 1_{B_R(y)}` of the ball `B_R(y)`, `R = j_{N/2-1,1}/√a`.  Then
`λ_{2N+2}(Ω) < C_N a`.

(The smoothness of `u` assumed in the paper is not needed: analyticity follows from
`ext_analytic`, proved in `RequestProject/InteriorAnalytic.lean`.)

Proof: by unique continuation for analytic functions `u = c Φ(· - y)` on `Ω`; the Sobolev
multiplier and constancy arguments give `H₀¹(B) ⊆ H₀¹(Ω)` and `H₀¹(A) ⊆ H₀¹(Ω)` for the ball
`B` and the adjacent annulus `A`; the span of a ball ground state and the `N` degree-one ball
eigenfunctions with eigenvalue `C_N a` (`ball_degree_one`; `N + 1` dimensions, `q ≤ C_N a ‖·‖²`) together with the `(N+1)`-dimensional annulus subspace
(`q ≤ t_A ‖·‖²`, `t_A < C_N a` by the radial integral inequalities) give `λ_{2N+2}(Ω) ≤ C_N a`,
and equality would produce an eigenfunction of `Ω` vanishing on `A ∩ Ω`. -/
theorem lemma_ball (hN : 2 ≤ N) {Ω : Set (RN N)} (hΩ : IsDomain Ω) {u : Amb N} {a : ℝ}
    (ha : 0 < a) (hu : IsEigenfunction Ω u a) {f : RN N → ℝ} (hf : IsContRep Ω u f)
    (hpos : (posSign Ω f).Nonempty) (hneg : (negSign Ω f).Nonempty) {G : Set (RN N)}
    (hG : (∃ x ∈ posSign Ω f, G = connectedComponentIn (posSign Ω f) x) ∨
      (∃ x ∈ negSign Ω f, G = connectedComponentIn (negSign Ω f) x))
    (y : RN N) (c : ℝ) (hc : c ≠ 0)
    (hball : G.indicator (u.1 : RN N → ℝ) =ᵐ[volume] fun x =>
      c * (ball y (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a)).indicator
        (fun x => besselProfile N a (x - y)) x) :
    eigenvalue Ω (2 * N + 2) < CN N * a := by
  haveI := nontrivial_RN hN
  set R := besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a with hRdef
  set R' := besselZero ((N : ℝ) / 2 - 1) 2 / Real.sqrt a with hR'def
  obtain ⟨Φ, hΦan, hΦprof, -, hΦpos, hΦneg, hR, hRR, hC, hy⟩ := ext_ball_basic hN ha
  rw [← hRdef] at hΦpos hΦneg hR hRR hy
  rw [← hR'def] at hΦneg hRR hy
  obtain ⟨-, ⟨φB, hφB, -⟩, -⟩ := hy y
  obtain ⟨V2, hV2dim, hV2⟩ := ball_degree_one hN ha y
  have hsep := annulus_sep hN ha y
  simp only at hsep
  rw [← hRdef, ← hR'def] at hsep
  obtain ⟨VA, hVAle, hVAdim, hVAq⟩ := hsep
  have hΦc : Continuous Φ := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hΦan x trivial).continuousAt
  set B : Set (RN N) := ball y R with hB
  set A : Set (RN N) := {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} with hA
  obtain ⟨g, hgdef⟩ : ∃ g : RN N → ℝ, g = fun x => c * Φ (x - y) := ⟨_, rfl⟩
  have hgx : ∀ x, g x = c * Φ (x - y) := fun x => by rw [hgdef]
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    rw [hgdef]
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
      contDiffOn_univ.mp (hΦan.contDiffOn uniqueDiffOn_univ)
    exact contDiff_const.mul (h1.comp (contDiff_id.sub contDiff_const))
  have hgc : Continuous g := hgs.continuous
  have hgan : AnalyticOnNhd ℝ g Ω := fun x _ => by
    rw [hgdef]
    have h2 : AnalyticAt ℝ (fun z : RN N => z - y) x := analyticAt_id.sub analyticAt_const
    exact analyticAt_const.mul (AnalyticAt.comp (g := Φ) (hΦan (x - y) trivial) h2)
  -- Step 1: on the ball, `u = g` and the points lie in `G`.
  have hGopen : IsOpen G := by
    rcases hG with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩
    · exact (isOpen_posSign hΩ.1.1 hf.1).connectedComponentIn
    · exact (isOpen_negSign hΩ.1.1 hf.1).connectedComponentIn
  have hGΩ : G ⊆ Ω := by
    rcases hG with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩
    · exact (connectedComponentIn_subset _ _).trans (posSign_subset _ _)
    · exact (connectedComponentIn_subset _ _).trans (negSign_subset _ _)
  have hS1 : ∀ᵐ x, x ∈ B → x ∈ G ∧ (u.1 : RN N → ℝ) x = g x := by
    have hy0 : ∀ᵐ x : RN N, x ∉ ({y} : Set (RN N)) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton y)
    filter_upwards [hball, hy0] with x hx hxy hxB
    have hxy' : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hxy (by simp [h]))
    have hxn : ‖x - y‖ < R := by rwa [hB, mem_ball, dist_eq_norm] at hxB
    rw [Set.indicator_of_mem hxB, ← hΦprof _ hxy'] at hx
    have hne : c * Φ (x - y) ≠ 0 := mul_ne_zero hc (hΦpos _ hxn).ne'
    by_cases hxG : x ∈ G
    · rw [Set.indicator_of_mem hxG] at hx
      exact ⟨hxG, hx.trans (hgx x).symm⟩
    · rw [Set.indicator_of_notMem hxG] at hx
      exact absurd hx.symm hne
  -- a point of `G` in the ball
  obtain ⟨x0, hx0B, hx0G⟩ : ∃ x0, x0 ∈ B ∧ x0 ∈ G := by
    have hne : (volume.restrict B) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact (measure_ball_pos volume y hR).ne'
    haveI : (ae (volume.restrict B)).NeBot := ae_neBot.mpr hne
    have : ∀ᵐ x ∂(volume.restrict B), x ∈ B ∧ x ∈ G := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        (ae_restrict_iff' measurableSet_ball).mpr hS1] with x hx1 hx2
      exact ⟨hx1, hx2.1⟩
    exact this.exists
  have hx0Ω : x0 ∈ Ω := hGΩ hx0G
  -- Step 2: `f = g` on `Ω` (identity theorem).
  set U := B ∩ G with hU
  have hUo : IsOpen U := isOpen_ball.inter hGopen
  have hUΩ : U ⊆ Ω := Set.inter_subset_right.trans hGΩ
  have hfgU : Set.EqOn f g U := by
    refine eqOn_of_contRep hUo (v := u) ⟨hf.1.mono hUΩ, ae_restrict_of_ae_restrict_of_subset hUΩ hf.2⟩
      ⟨hgc.continuousOn, ?_⟩
    rw [EventuallyEq, ae_restrict_iff' hUo.measurableSet]
    filter_upwards [hS1] with x hx hxU
    exact (hx hxU.1).2
  obtain ⟨f', hf'an, hf'rep⟩ := ext_analytic hΩ hu.1 hu.2.2
  have hff' : Set.EqOn f f' Ω := eqOn_of_contRep hΩ.1.1 hf hf'rep
  have hf'g : Set.EqOn f' g Ω := by
    refine hf'an.eqOn_of_preconnected_of_eventuallyEq hgan hΩ.2.isPreconnected hx0Ω ?_
    filter_upwards [hUo.mem_nhds ⟨hx0B, hx0G⟩] with x hx
    rw [← hff' (hUΩ hx)]
    exact hfgU hx
  have hfg : ∀ x ∈ Ω, f x = g x := fun x hx => (hff' hx).trans (hf'g hx)
  have hug : ∀ᵐ x, x ∈ Ω → (u.1 : RN N → ℝ) x = g x := by
    have := (ae_restrict_iff' hΩ.1.1.measurableSet).mp hf.2
    filter_upwards [this] with x hx hxΩ
    rw [hx hxΩ, hfg x hxΩ]
  -- Step 3: `H_B ⊆ H_Ω`.
  have hx0n : ‖x0 - y‖ < R := by rwa [hB, mem_ball, dist_eq_norm] at hx0B
  have hgB : ∀ x ∈ B, g x ≠ 0 := fun x hx => by
    rw [hgx]
    exact mul_ne_zero hc (hΦpos _ (by rwa [hB, mem_ball, dist_eq_norm] at hx)).ne'
  have hBΩ : H B ≤ H Ω :=
    H_le_of_measure_diff hΩ.1 hu.1 hgs hug isOpen_ball hgB
      (measure_diff_eq_zero_of_connected hN hΩ.1 hu.1 hgs hug isOpen_ball
        (convex_ball y R).isPreconnected hgB ⟨x0, hx0B, hx0Ω⟩)
  -- Step 4: `A ∩ Ω ≠ ∅` and `H_A ⊆ H_Ω`.
  obtain ⟨z, hzΩ, hzneg⟩ : ∃ z ∈ Ω, Φ (z - y) < 0 := by
    have hΦx0 := hΦpos _ hx0n
    rcases hG with ⟨x1, -, rfl⟩ | ⟨x1, -, rfl⟩
    · have h0 : 0 < f x0 := (connectedComponentIn_subset _ _ hx0G).2
      rw [hfg x0 hx0Ω, hgx] at h0
      have hc0 : 0 < c := pos_of_mul_pos_left h0 hΦx0.le
      obtain ⟨z, hzΩ, hz⟩ := hneg
      refine ⟨z, hzΩ, ?_⟩
      have hz' : c * Φ (z - y) < 0 := by rw [← hgx, ← hfg z hzΩ]; exact hz
      by_contra h
      push_neg at h
      exact absurd hz' (not_lt.mpr (mul_nonneg hc0.le h))
    · have h0 : f x0 < 0 := (connectedComponentIn_subset _ _ hx0G).2
      rw [hfg x0 hx0Ω, hgx] at h0
      have hc0 : c < 0 := by
        by_contra h
        push_neg at h
        exact absurd h0 (not_lt.mpr (mul_nonneg h hΦx0.le))
      obtain ⟨z, hzΩ, hz⟩ := hpos
      refine ⟨z, hzΩ, ?_⟩
      have hz' : 0 < c * Φ (z - y) := by rw [← hgx, ← hfg z hzΩ]; exact hz
      by_contra h
      push_neg at h
      exact absurd hz' (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hc0.le h))
  have hzR : R < ‖z - y‖ := by
    by_contra h
    push_neg at h
    exact absurd hzneg (not_lt.mpr (nonneg_of_norm_le hΦc hR hΦpos h))
  obtain ⟨w, hwΩ, hw1, hw2⟩ :=
    exists_mem_annulus hΩ.2.isPreconnected hRR hx0Ω hx0n hzΩ hzR
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
  have hgA : ∀ x ∈ A, g x ≠ 0 := fun x hx => by
    rw [hgx]
    exact mul_ne_zero hc (hΦneg _ hx.1 hx.2).ne
  have hAΩ : H A ≤ H Ω :=
    H_le_of_measure_diff hΩ.1 hu.1 hgs hug hAo hgA
      (measure_diff_eq_zero_of_connected hN hΩ.1 hu.1 hgs hug hAo
        (isConnected_annulus hN y hR.le hRR).isPreconnected hgA ⟨w, ⟨hw1, hw2⟩, hwΩ⟩)
  -- Step 5: the subspaces.
  have hAadm : IsAdmissible A :=
    ⟨hAo, ⟨w, hw1, hw2⟩, isBounded_ball.subset fun x hx => by
      rw [mem_ball, dist_eq_norm]; exact hx.2⟩
  have hBadm : IsAdmissible B := (isDomain_ball y hR).1
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rw [hB, mem_ball, dist_eq_norm] at hxB
    linarith [hxA.1]
  obtain ⟨VB, hVBfin, hVBle, hVBdim, hVBq⟩ := ball_subspace hN ha hC hφB hV2dim hV2
  haveI : FiniteDimensional ℝ VA := FiniteDimensional.of_finrank_pos (by omega)
  -- Step 6: the annulus bound.
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨ev, hev⟩ : ∃ ev : RN N, ev = EuclideanSpace.single (⟨0, by omega⟩ : Fin N) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hρeq : ∀ r : ℝ, 0 < r →
      r ^ (-((N : ℝ) / 2 - 1)) * besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * r) = Φ (r • ev) := by
    intro r hr
    have hn : ‖r • ev‖ = r := by
      rw [norm_smul, hev, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_pos hr]
    have hne : r • ev ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      linarith
    rw [hΦprof _ hne, besselProfile, hn]
  have hρc : ContinuousOn
      (fun r : ℝ => r ^ (-((N : ℝ) / 2 - 1)) * besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * r))
      (Set.Icc R R') :=
    (hΦc.comp (continuous_id.smul continuous_const)).continuousOn.congr fun r hr =>
      hρeq r (hR.trans_le hr.1)
  have hρ0 : ∀ r ∈ Set.Ioo R R',
      r ^ (-((N : ℝ) / 2 - 1)) * besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * r) ≠ 0 := by
    intro r hr
    have hr0 : 0 < r := hR.trans hr.1
    rw [hρeq r hr0]
    have hn : ‖r • ev‖ = r := by
      rw [norm_smul, hev, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_pos hr0]
    have h1 : R < ‖r • ev‖ := by rw [hn]; exact hr.1
    have h2 : ‖r • ev‖ < R' := by rw [hn]; exact hr.2
    exact (hΦneg (r • ev) h1 h2).ne
  have htA := annulus_bound_lt hR hRR hN1 hρc hρ0 (ball_gap hN ha)
  -- Step 7: conclusion.
  have h22 : 2 * N + 2 = (2 * N + 1) + 1 := by ring
  rw [h22]
  exact ball_annulus_spectral hN hΩ hAadm hBadm hAB hAΩ hBΩ ⟨w, ⟨hw1, hw2⟩, hwΩ⟩ htA
    hVAle hVBle (by rw [hVAdim, hVBdim]; ring) hVAq hVBq

end FourthRatio

end

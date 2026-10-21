module

public import RequestProject.PPWApprox
public import RequestProject.PPWABBall
public import RequestProject.PPWCenter
public import RequestProject.PPWTransfer
public import RequestProject.PPWBall
public import RequestProject.PPWProfile

/-!
# The Payne–Pólya–Weinberger inequality and its equality case (assembly)

The Ashbaugh–Benguria argument:
1. `λ₁ = a`, `u` a positive first eigenfunction, `c` a Weinberger centre (`exists_center`);
2. gap inequality `(λ₂ - a) ∫ G(|x-c|²) u² ≤ ∫ B(|x-c|²) u²` (`profile_gap`);
3. transfer from `u²` to the ball's first eigenfunction `z²` (`chiti_mass`, `transfer_anti`,
   `transfer_mono`), using that `B` is nonincreasing and `G` nondecreasing (`ab_profile`);
4. the ball identity `∫ B z² = (C_N - 1) a ∫ G z²` (`ab_profile`).
In the equality case all inequalities are equalities, which forces `u` to vanish outside a ball
`B_R(c)` with `λ₁(B_R(c)) = a` (`transfer_eq_support`), hence `D ⊆ B_R(c)` and
`H₀¹(D) = H₀¹(B_R(c))` (`subset_ball_of_ae_zero`, `H_eq_ball_of_subset`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- A nonnegative integrable function which is a.e. positive on a set of positive measure has
positive integral. -/
lemma integral_pos_of_ae_pos_on {g : RN N → ℝ} (hg : ∀ x, 0 ≤ g x) (hi : Integrable g)
    {S : Set (RN N)} (hS : 0 < volume S) (h : ∀ᵐ x ∂volume.restrict S, 0 < g x) :
    0 < ∫ x, g x := by
  have h1 : 0 < ∫ x in S, g x := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hg) hi.integrableOn]
    have hsupp : {x | 0 < g x} ⊆ Function.support g := fun x hx => (ne_of_gt hx)
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    have h0 : volume.restrict S {x | 0 < g x}ᶜ = 0 := by
      rw [← ae_iff.mp h]; rfl
    have : volume.restrict S univ ≤ volume.restrict S {x | 0 < g x} := by
      calc volume.restrict S univ
          ≤ volume.restrict S {x | 0 < g x} + volume.restrict S {x | 0 < g x}ᶜ := by
            rw [← union_compl_self {x | 0 < g x}]; exact measure_union_le _ _
        _ = _ := by rw [h0, add_zero]
    refine lt_of_lt_of_le ?_ this
    rwa [Measure.restrict_apply_univ]
  exact lt_of_lt_of_le h1 (setIntegral_le_integral hi (Filter.Eventually.of_forall hg))

/-- The common setup and the chain of inequalities of the Ashbaugh–Benguria argument. -/
theorem ppw_chain (hN : 2 ≤ N) (hAB : ABBesselLemmas ((N : ℝ) / 2 - 1)) (hCh : ChitiMass N)
    {D : Set (RN N)} (hD : IsDomain D) :
    eigenvalue D 2 ≤ CN N * eigenvalue D 1 ∧
      (eigenvalue D 2 = CN N * eigenvalue D 1 →
        ∃ c : RN N, D ⊆ ball c (annR N (eigenvalue D 1))) := by
  have hN1 : 1 ≤ N := by omega
  set a := eigenvalue D 1 with ha_def
  have ha : 0 < a := by
    obtain ⟨e, -, -, h, -⟩ := ext_spectral hN hD.1
    exact h
  set R := annR N a with hR_def
  have hR : 0 < R := div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  obtain ⟨u, f, hu, hf, hfpos⟩ := ground_state_pos hN hD
  obtain ⟨p, hG, hB, hid⟩ := ab_profile_of hN hAB ha
  set F2 : RN N → ℝ := fun x => (u.1 : RN N → ℝ) x ^ 2 with hF2
  set E2 : RN N → ℝ := fun x => besselEntire N a x ^ 2 with hE2
  set Z2 : RN N → ℝ := (ball (0 : RN N) R).indicator E2 with hZ2
  have hF2i : Integrable F2 := (Lp.memLp u.1).integrable_sq
  have hF20 : ∀ x, 0 ≤ F2 x := fun x => sq_nonneg _
  have hE2c : Continuous E2 := (contDiff_besselEntire hN ha.le).continuous.pow 2
  have hZ2i : Integrable Z2 := by
    rw [hZ2, integrable_indicator_iff measurableSet_ball]
    exact (hE2c.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      ball_subset_closedBall
  have hZ20 : ∀ x, 0 ≤ Z2 x := fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x
  -- `u` vanishes outside the bounded set `D`
  obtain ⟨M, hDM⟩ := hD.1.2.2.subset_closedBall 0
  have hM : ∀ᵐ x, M < ‖x‖ → F2 x = 0 := by
    have h0 := (mem_vanishOn.mp (H_le_vanishOn D hu.1)).1
    rw [Filter.EventuallyEq, ae_restrict_iff' hD.1.1.measurableSet.compl] at h0
    filter_upwards [h0] with x hx hMx
    have hxD : x ∉ D := fun hxD => by
      have := hDM hxD; rw [mem_closedBall, dist_zero_right] at this; linarith
    simp only [F2, hx hxD, Pi.zero_apply]; ring
  obtain ⟨c, hc⟩ := exists_center p hR hF2i hF20 hM
  -- mass comparison (Chiti)
  have hmass : MassDominated F2 Z2 c := by
    intro r
    have h := hCh hD hu c r
    rw [hZ2, integral_indicator measurableSet_ball, setIntegral_indicator measurableSet_ball]
    exact h
  -- the gap inequality
  have hgap := profile_gap hN hD hu p c hc
  -- the weights
  set Bt : ℝ → ℝ := fun s => p.Bw (max s 0) with hBt_def
  set Gt : ℝ → ℝ := fun s => p.Gw (max s 0) with hGt_def
  have hBt : Antitone Bt := fun s t hst =>
    hB (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max hst le_rfl)
  have hBt0 : ∀ s, 0 ≤ Bt s := fun s => p.Bw_nonneg hN1 _
  have hGt : Monotone Gt := fun s t hst =>
    hG (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max hst le_rfl)
  have hGtK : ∀ s, Gt s ≤ p.κ ^ 2 := fun s => p.Gw_le hR hG (le_max_right _ _)
  have hTB := transfer_anti hN hF2i hZ2i hF20 hZ20 hmass hBt hBt0
  have hTG := transfer_mono hN hF2i hZ2i hF20 hZ20 hmass hGt hGtK
  have hmx : ∀ x : RN N, max (‖x‖ ^ 2) 0 = ‖x‖ ^ 2 := fun x => max_eq_left (sq_nonneg _)
  have eB1 : (∫ x, Bt (‖x - c‖ ^ 2) * F2 x) = ∫ x, p.Bw (‖x - c‖ ^ 2) * F2 x := by
    simp only [Bt, hmx]
  have eG1 : (∫ x, Gt (‖x - c‖ ^ 2) * F2 x) = ∫ x, p.Gw (‖x - c‖ ^ 2) * F2 x := by
    simp only [Gt, hmx]
  have eB2 : (∫ x, Bt (‖x‖ ^ 2) * Z2 x) =
      ∫ x in ball (0 : RN N) R, p.Bw (‖x‖ ^ 2) * besselEntire N a x ^ 2 := by
    rw [← integral_indicator measurableSet_ball]
    congr 1; funext x
    simp only [Bt, hmx, Z2, indicator, E2]
    split_ifs <;> simp
  have eG2 : (∫ x, Gt (‖x‖ ^ 2) * Z2 x) =
      ∫ x in ball (0 : RN N) R, p.Gw (‖x‖ ^ 2) * besselEntire N a x ^ 2 := by
    rw [← integral_indicator measurableSet_ball]
    congr 1; funext x
    simp only [Gt, hmx, Z2, indicator, E2]
    split_ifs <;> simp
  rw [eB1, eB2] at hTB
  rw [eG1, eG2] at hTG
  rw [hid] at hTB
  -- positivity
  have hZpos : 0 < ∫ x, Z2 x := by
    refine integral_pos_of_ae_pos_on hZ20 hZ2i (measure_ball_pos volume (0 : RN N) hR) ?_
    refine (ae_restrict_iff' measurableSet_ball).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [hZ2, indicator_of_mem hx]
    have hx' : ‖x‖ < besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a := by
      simpa [mem_ball, dist_zero_right, R, annR] using hx
    exact pow_pos (besselEntire_pos hN ha hx') 2
  have hcont : Continuous fun x : RN N => ‖x - c‖ ^ 2 :=
    (continuous_id.sub continuous_const).norm.pow 2
  have hApos : 0 < ∫ x, p.Gw (‖x - c‖ ^ 2) * F2 x := by
    have hint : Integrable fun x => p.Gw (‖x - c‖ ^ 2) * F2 x := by
      refine hF2i.bdd_mul (c := p.κ ^ 2) (p.continuous_Gw.comp hcont).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (p.Gw_nonneg (sq_nonneg _))]
      exact p.Gw_le hR hG (sq_nonneg _)
    refine integral_pos_of_ae_pos_on
      (fun x => mul_nonneg (p.Gw_nonneg (sq_nonneg _)) (hF20 x)) hint
      (hD.1.1.measure_pos volume hD.1.2.1) ?_
    have hne : ∀ᵐ x : RN N, x ≠ c := by
      haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
      rw [ae_iff]; simp
    filter_upwards [hf.2, ae_restrict_mem hD.1.1.measurableSet, ae_restrict_of_ae hne]
      with x hx hxD hxc
    refine mul_pos (p.Gw_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxc)) 2)) ?_
    simp only [F2, hx]
    exact pow_pos (hfpos x hxD) 2
  have hC1 : 1 < CN N := CN_gt_one hN
  have hCa : 0 ≤ (CN N - 1) * a := mul_nonneg (by linarith) ha.le
  set A := ∫ x, p.Gw (‖x - c‖ ^ 2) * F2 x
  set Bf := ∫ x, p.Bw (‖x - c‖ ^ 2) * F2 x
  set Gz := ∫ x in ball (0 : RN N) R, p.Gw (‖x‖ ^ 2) * besselEntire N a x ^ 2
  set Z := ∫ x, Z2 x
  set F := ∫ x, F2 x
  have h1 : (eigenvalue D 2 - a) * A * Z ≤ Bf * Z := mul_le_mul_of_nonneg_right hgap hZpos.le
  have h2 : (CN N - 1) * a * (Gz * F) ≤ (CN N - 1) * a * (A * Z) :=
    mul_le_mul_of_nonneg_left hTG hCa
  have hAZ : 0 < A * Z := mul_pos hApos hZpos
  have key : (eigenvalue D 2 - a) * (A * Z) ≤ (CN N - 1) * a * (A * Z) := by
    nlinarith
  have hineq : eigenvalue D 2 ≤ CN N * a := by
    have := le_of_mul_le_mul_right key hAZ
    linarith
  refine ⟨hineq, fun heq => ?_⟩
  -- equality case
  have hBeq : Bf * Z = (CN N - 1) * a * Gz * F := by
    have : (eigenvalue D 2 - a) * (A * Z) = (CN N - 1) * a * (A * Z) := by rw [heq]; ring
    apply le_antisymm hTB
    nlinarith
  have hstrict : ∀ s s', R ^ 2 ≤ s → s < s' → Bt s' < Bt s := by
    intro s s' hs hss'
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    simp only [Bt, max_eq_left hs0.le, max_eq_left (hs0.trans hss').le]
    rw [p.Bw_tail hR hs, p.Bw_tail hR (hs.trans hss'.le)]
    have hN' : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have := p.κ_pos
    exact div_lt_div_of_pos_left (by positivity) hs0 hss'
  have hzR : ∀ x : RN N, R ≤ ‖x‖ → Z2 x = 0 := fun x hx =>
    indicator_of_notMem (by simpa [mem_ball, dist_zero_right] using hx) _
  have heqT : (∫ x, Bt (‖x - c‖ ^ 2) * F2 x) * (∫ x, Z2 x) =
      (∫ x, Bt (‖x‖ ^ 2) * Z2 x) * ∫ x, F2 x := by
    rw [eB1, eB2, hid]; exact hBeq
  have hsupp := transfer_eq_support hN hF2i hZ2i hF20 hZ20 hmass hzR hZpos hBt hBt0 hstrict heqT
  exact ⟨c, subset_ball_of_ae_zero hN hD hu hsupp⟩

/-- **PPW inequality and equality case from the two deep inputs** (sorry-free reduction):
the Bessel function lemmas of Ashbaugh–Benguria for `ν = N/2 - 1` and the mass-concentration form
of Chiti's comparison theorem imply the PPW inequality and its equality case. -/
theorem ppw_of_deep_inputs (hN : 2 ≤ N) (hAB : ABBesselLemmas ((N : ℝ) / 2 - 1))
    (hCh : ChitiMass N) : PPWInequality N ∧ PPWEqualityCase N := by
  refine ⟨fun D hD => (ppw_chain hN hAB hCh hD).1, fun D hD heq => ?_⟩
  obtain ⟨c, hc⟩ := (ppw_chain hN hAB hCh hD).2 heq
  have ha : 0 < eigenvalue D 1 := by
    obtain ⟨e, -, -, h, -⟩ := ext_spectral hN hD.1
    exact h
  have hR : 0 < annR N (eigenvalue D 1) :=
    div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  exact ⟨c, annR N (eigenvalue D 1), hR, (ball_first_eigen hN ha c).1,
    H_eq_ball_of_subset hN hD hc⟩

/-- **PPW inequality** (Ashbaugh–Benguria) for bounded domains. -/
theorem ppw_inequality (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) :
    eigenvalue D 2 ≤ CN N * eigenvalue D 1 :=
  (ppw_of_deep_inputs hN (ab_bessel (hN_nu hN)) (chiti_mass hN)).1 hD

/-- **PPW equality case.** -/
theorem ppw_equality (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D)
    (heq : eigenvalue D 2 = CN N * eigenvalue D 1) :
    ∃ (y : RN N) (R : ℝ), 0 < R ∧ eigenvalue (ball y R) 1 = eigenvalue D 1 ∧
      H D = H (ball y R) :=
  (ppw_of_deep_inputs hN (ab_bessel (hN_nu hN)) (chiti_mass hN)).2 hD heq

end FourthRatio

end

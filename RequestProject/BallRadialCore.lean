module

public import RequestProject.BallRadial

/-!
# The core comparison for sign-changing radial eigenfunctions of the ball

If a weak eigenfunction `u` of `B = B_R(y)`, `R = j_{ν,1}/√a`, with eigenvalue `μ > 0` has a radial
continuous representative `f` with `f(y) > 0` that takes a negative value, then `μ > C_N a`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma isDomain_annulus' (hN : 2 ≤ N) {μ : ℝ} (hμ : 0 < μ) (y : RN N) :
    IsDomain (annulus N μ y) := by
  have hR := annR_pos hN hμ
  have hRR := annR_lt hN hμ
  obtain ⟨e, he⟩ := exists_unit hN
  have hne : (annulus N μ y).Nonempty := by
    refine ⟨y + ((annR N μ + annR' N μ) / 2) • e, ?_, ?_⟩ <;>
      rw [norm_add_smul_unit he y (by linarith)] <;> linarith
  exact ⟨⟨isOpen_annulus μ y, hne,
    (isBounded_ball (x := y) (r := annR' N μ)).subset fun x hx => by
      simpa [dist_eq_norm] using hx.2⟩,
    isConnected_annulus hN y hR.le hRR⟩

/-- `C_N a < μ` as soon as `j_{ν,2}/√μ ≤ j_{ν,1}/√a`. -/
lemma CN_lt_of_annR' (hN : 2 ≤ N) {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ)
    (h : annR' N μ ≤ annR N a) : CN N * a < μ := by
  have hν := hN_nu hN
  obtain ⟨a1, a2, -⟩ := besselZero_props hν
  have hint := besselZero_succ_lt_two hν
  rw [show (N : ℝ) / 2 - 1 + 1 = (N : ℝ) / 2 by ring] at hint
  have hjN : 0 < besselZero ((N : ℝ) / 2) 1 := (besselZero_props (by positivity)).1
  set j1 := besselZero ((N : ℝ) / 2 - 1) 1
  set j2 := besselZero ((N : ℝ) / 2 - 1) 2
  set jN := besselZero ((N : ℝ) / 2) 1
  have hsa := Real.sqrt_pos.mpr ha
  have hsμ := Real.sqrt_pos.mpr hμ
  have h1 : j2 * Real.sqrt a ≤ j1 * Real.sqrt μ := by
    have := h
    simp only [annR', annR] at this
    rw [div_le_div_iff₀ hsμ hsa] at this
    exact this
  have h2 : j2 ^ 2 * a ≤ j1 ^ 2 * μ := by
    have := mul_self_le_mul_self (mul_pos (a1.trans a2) hsa).le h1
    have e1 : j2 * Real.sqrt a * (j2 * Real.sqrt a) = j2 ^ 2 * a := by
      rw [show j2 * Real.sqrt a * (j2 * Real.sqrt a) = j2 ^ 2 * (Real.sqrt a * Real.sqrt a) by ring,
        Real.mul_self_sqrt ha.le]
    have e2 : j1 * Real.sqrt μ * (j1 * Real.sqrt μ) = j1 ^ 2 * μ := by
      rw [show j1 * Real.sqrt μ * (j1 * Real.sqrt μ) = j1 ^ 2 * (Real.sqrt μ * Real.sqrt μ) by ring,
        Real.mul_self_sqrt hμ.le]
    linarith
  have h3 : jN ^ 2 * a < j2 ^ 2 * a :=
    mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hint hjN.le two_ne_zero) ha
  unfold CN
  change jN ^ 2 / j1 ^ 2 * a < μ
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith

/-- **Core comparison.** -/
theorem radial_core (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {u : Amb N} {μ : ℝ}
    (hμ : 0 < μ) (hu : u ∈ H (ball y (annR N a)))
    (hw : ∀ φ ∈ H (ball y (annR N a)), qf u φ = μ * l2 u φ)
    {f : RN N → ℝ} (hf : IsContRep (ball y (annR N a)) u f)
    (hrad : ∀ x ∈ ball y (annR N a), ∀ x' ∈ ball y (annR N a), ‖x - y‖ = ‖x' - y‖ → f x = f x')
    (hy : 0 < f y) {xm : RN N} (hxm : xm ∈ ball y (annR N a)) (hfxm : f xm < 0) :
    CN N * a < μ := by
  set R := annR N a with hRdef
  set B := ball y R with hBdef
  have hR : 0 < R := annR_pos hN ha
  have hBm : MeasurableSet B := isOpen_ball.measurableSet
  have hE : IsAdmissible B := (isDomain_ball y hR).1
  obtain ⟨e, he⟩ := exists_unit hN
  set g : ℝ → ℝ := fun s => f (y + s • e) with hgdef
  have hsB : ∀ s, 0 ≤ s → s < R → y + s • e ∈ B := fun s hs hsR => by
    rw [mem_ball, dist_eq_norm, norm_add_smul_unit he y hs]; exact hsR
  have hfx : ∀ x ∈ B, f x = g ‖x - y‖ := fun x hx => radial_eq_profile he hrad hx
  set rm := ‖xm - y‖ with hrm
  have hrmR : rm < R := by simpa [B, dist_eq_norm] using hxm
  have hgrm : g rm < 0 := by rw [← hfx xm hxm]; exact hfxm
  have hg0 : g 0 = f y := by simp [g]
  have hgc : ContinuousOn g (Icc 0 rm) := by
    have hc : ContinuousOn (fun s : ℝ => y + s • e) (Icc 0 rm) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    exact hf.1.comp hc fun s hs => hsB s hs.1 (lt_of_le_of_lt hs.2 hrmR)
  set T := Icc 0 rm ∩ g ⁻¹' Iic 0 with hTdef
  have hTc : IsClosed T := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hrm0 : 0 ≤ rm := norm_nonneg _
  have hTne : T.Nonempty := ⟨rm, ⟨hrm0, le_rfl⟩, hgrm.le⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set ρ := sInf T with hρdef
  have hρT : ρ ∈ T := hTc.csInf_mem hTne hTb
  have hgρ : g ρ ≤ 0 := hρT.2
  have hlt : ∀ s, 0 ≤ s → s < ρ → 0 < g s := by
    intro s hs hsρ
    by_contra hle
    push_neg at hle
    have : s ∈ T := ⟨⟨hs, hsρ.le.trans hρT.1.2⟩, hle⟩
    exact absurd (csInf_le hTb this) (not_le.mpr hsρ)
  have hρ : 0 < ρ := by
    rcases hρT.1.1.eq_or_lt with h | h
    · rw [← h, hg0] at hgρ; linarith
    · exact h
  have hρR : ρ < R := lt_of_le_of_lt hρT.1.2 hrmR
  have hgρ0 : g ρ = 0 := by
    have hc : ContinuousOn g (Icc 0 ρ) := hgc.mono (Icc_subset_Icc le_rfl hρT.1.2)
    obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc' hρ.le hc ⟨hgρ, (hg0 ▸ hy).le⟩
    rcases hz.2.lt_or_eq with h | h
    · exact absurd hgz (hlt z hz.1 h).ne'
    · rw [← h]; exact hgz
  have hin : ∀ x ∈ B, ‖x - y‖ < ρ → 0 < f x := fun x hx h => by
    rw [hfx x hx]; exact hlt _ (norm_nonneg _) h
  have hon : ∀ x ∈ B, ‖x - y‖ = ρ → f x = 0 := fun x hx h => by
    rw [hfx x hx, h, hgρ0]
  set Bρ := ball y ρ with hBρdef
  have hBρB : Bρ ⊆ B := ball_subset_ball hρR.le
  have hBρm : MeasurableSet Bρ := isOpen_ball.measurableSet
  have hin' : ∀ x ∈ Bρ, 0 < f x := fun x hx =>
    hin x (hBρB hx) (by simpa [Bρ, dist_eq_norm] using hx)
  have hfB : ∀ᵐ x, x ∈ B → (u.1 : RN N → ℝ) x = f x := (ae_restrict_iff' hBm).mp hf.2
  obtain ⟨hu1, hu2⟩ := vanish_off_of_mem_H isOpen_ball hu
  -- positive part restricted to `B_ρ`
  have hpos := posPart_mem_H_posSign hE hu hf
  have hcn : Continuous fun x : RN N => ‖x - y‖ := by fun_prop
  set S := posSign B f ∩ {x | ρ < ‖x - y‖} with hSdef
  have hSo : IsOpen S := (isOpen_posSign isOpen_ball hf.1).inter (isOpen_lt continuous_const hcn)
  have hdisj : Disjoint Bρ S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    have h1 : ‖x - y‖ < ρ := by simpa [Bρ, dist_eq_norm] using hx
    have h2 : ρ < ‖x - y‖ := hxS.2
    linarith
  have hsub : posSign B f ⊆ Bρ ∪ S := by
    rintro x ⟨hxB, hfx0⟩
    rcases lt_trichotomy ‖x - y‖ ρ with h | h | h
    · left; simpa [Bρ, dist_eq_norm] using h
    · exact absurd (hon x hxB h) (ne_of_gt hfx0)
    · right; exact ⟨⟨hxB, hfx0⟩, h⟩
  have hwH : restrictTo Bρ (posPart u) ∈ H Bρ :=
    restrictTo_mem_H_of_union isOpen_ball hSo hdisj (H_mono hsub hpos)
  set w := restrictTo Bρ (posPart u) with hwdef
  have hw1 : (w.1 : RN N → ℝ) =ᵐ[volume] Bρ.indicator f := by
    filter_upwards [restrictTo_fst_ae hBρm (posPart u), posPart_fst_ae' u, hfB] with x e1 e2 e3
    rw [e1]
    by_cases hx : x ∈ Bρ
    · rw [indicator_of_mem hx, indicator_of_mem hx, e2, e3 (hBρB hx),
        max_eq_left (hin' x hx).le]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  have hagree1 : (w.1 : RN N → ℝ) =ᵐ[volume.restrict Bρ] u.1 := by
    rw [EventuallyEq, ae_restrict_iff' hBρm]
    filter_upwards [hw1, hfB] with x e1 e2 hx
    rw [e1, indicator_of_mem hx, e2 (hBρB hx)]
  have hagree2 : (w.2 : RN N → RN N) =ᵐ[volume.restrict Bρ] u.2 := by
    rw [EventuallyEq, ae_restrict_iff' hBρm]
    filter_upwards [restrictTo_snd_ae hBρm (posPart u), posPart_snd_ae_ite u, hfB]
      with x e1 e2 e3 hx
    rw [e1, indicator_of_mem hx, e2, if_pos (by rw [e3 (hBρB hx)]; exact hin' x hx), one_smul]
  have hww := weak_of_agree hBρm hBρB hw hagree1 hagree2
  have hEw : IsEigenfunction Bρ w μ :=
    ⟨hwH, ne_zero_of_indicator_pos isOpen_ball (nonempty_ball.mpr hρ) hin' hw1, hww⟩
  have heig : eigenvalue Bρ 1 = μ :=
    eigenvalue_one_eq_of_nonneg hN (isDomain_ball y hρ) hEw (nonneg_of_indicator_pos hin' hw1)
  have hρeq : ρ = annR N μ := ball_radius_eq hN hρ hμ heig
  -- negative part
  have hfneg : IsContRep B (-u) (-f) := by
    refine ⟨hf.1.neg, ?_⟩
    rw [EventuallyEq, ae_restrict_iff' hBm]
    filter_upwards [Lp.coeFn_neg u.1, hfB] with x e1 e2 hx
    rw [Prod.fst_neg, e1, Pi.neg_apply, e2 hx, Pi.neg_apply]
  have hz := posPart_mem_H_posSign hE ((H B).neg_mem hu) hfneg
  set G := posSign B (-f) with hGdef
  have hGo : IsOpen G := isOpen_posSign isOpen_ball hfneg.1
  have hGm : MeasurableSet G := hGo.measurableSet
  have hGB : G ⊆ B := inter_subset_left
  set A' : Set (RN N) := {x | ρ < ‖x - y‖ ∧ ‖x - y‖ < R} with hA'def
  have hA'o : IsOpen A' := (isOpen_lt continuous_const hcn).inter (isOpen_lt hcn continuous_const)
  have hGA' : G ⊆ A' := by
    rintro x ⟨hxB, hfx0⟩
    simp only [Pi.neg_apply, mem_setOf_eq, neg_pos] at hfx0
    refine ⟨?_, by simpa [B, dist_eq_norm] using hxB⟩
    rcases lt_trichotomy ‖x - y‖ ρ with h | h | h
    · exact absurd (hin x hxB h) (not_lt.mpr hfx0.le)
    · exact absurd (hon x hxB h) hfx0.ne
    · exact h
  set z := posPart (-u) with hzdef
  have hzA' : z ∈ H A' := H_mono hGA' hz
  have hfnB : ∀ᵐ x, x ∈ B → ((-u).1 : RN N → ℝ) x = -f x :=
    (ae_restrict_iff' hBm).mp hfneg.2
  have hz1 : (z.1 : RN N → ℝ) =ᵐ[volume] G.indicator (-f) := by
    filter_upwards [posPart_fst_ae' (-u), hfnB, Lp.coeFn_neg u.1, hu1] with x e1 e2 e3 e4
    rw [e1]
    by_cases hxG : x ∈ G
    · rw [indicator_of_mem hxG, e2 (hGB hxG), max_eq_left hxG.2.le]; rfl
    · rw [indicator_of_notMem hxG]
      by_cases hxB : x ∈ B
      · rw [e2 hxB]
        exact max_eq_right (not_lt.mp fun h => hxG ⟨hxB, h⟩)
      · rw [Prod.fst_neg, e3, Pi.neg_apply, e4 hxB]; simp
  have hzpos : ∀ x ∈ G, 0 < (-f) x := fun x hx => hx.2
  have hGne : G.Nonempty := ⟨xm, hxm, by simp only [Pi.neg_apply, neg_pos]; exact hfxm⟩
  have hz0 : z ≠ 0 := ne_zero_of_indicator_pos hGo hGne hzpos hz1
  have hwneg : ∀ φ ∈ H B, qf (-u) φ = μ * l2 (-u) φ := fun φ hφ => by
    rw [qf_neg_left, l2_neg_left, hw φ hφ]; ring
  have hzagree1 : (z.1 : RN N → ℝ) =ᵐ[volume.restrict G] (-u).1 := by
    rw [EventuallyEq, ae_restrict_iff' hGm]
    filter_upwards [hz1, hfnB] with x e1 e2 hx
    rw [e1, indicator_of_mem hx, e2 (hGB hx)]; rfl
  have hzagree2 : (z.2 : RN N → RN N) =ᵐ[volume.restrict G] (-u).2 := by
    rw [EventuallyEq, ae_restrict_iff' hGm]
    filter_upwards [posPart_snd_ae_ite (-u), hfnB] with x e1 e2 hx
    rw [e1, if_pos (by rw [e2 (hGB hx)]; exact hx.2), one_smul]
  have hzw := weak_of_agree hGm hGB hwneg hzagree1 hzagree2
  have hzq : qf z z = μ * l2 z z := hzw z hz
  -- comparison with the annulus of parameter `μ`
  have hR' : annR' N μ ≤ R := by
    by_contra hlt'
    push_neg at hlt'
    have hA'A : A' ⊆ annulus N μ y := fun x hx => ⟨hρeq ▸ hx.1, hx.2.trans hlt'⟩
    obtain ⟨hA1, -⟩ := annulus_first_eigen hN hμ y
    have hzA : z ∈ H (annulus N μ y) := H_mono hA'A hzA'
    have hzE : IsEigenfunction (annulus N μ y) z (eigenvalue (annulus N μ y) 1) :=
      isEigenfunction_of_rayleigh_min hzA hz0 (by rw [hA1]; exact hzq)
    set U : Set (RN N) := {x | R < ‖x - y‖ ∧ ‖x - y‖ < annR' N μ} with hUdef
    have hUo : IsOpen U := (isOpen_lt continuous_const hcn).inter (isOpen_lt hcn continuous_const)
    have hUne : U.Nonempty := ⟨y + ((R + annR' N μ) / 2) • e, by
      constructor <;> rw [norm_add_smul_unit he y (by linarith)] <;> linarith⟩
    have hUA : U ⊆ annulus N μ y := fun x hx => ⟨by rw [← hρeq]; linarith [hx.1], hx.2⟩
    obtain ⟨hz10, -⟩ := vanish_off_of_mem_H hA'o hzA'
    have hzU : (z.1 : RN N → ℝ) =ᵐ[volume.restrict U] 0 := by
      rw [EventuallyEq, ae_restrict_iff' hUo.measurableSet]
      filter_upwards [hz10] with x hx hxU
      exact hx (fun h => by linarith [h.2, hxU.1])
    exact ucp_nonvanishing (isDomain_annulus' hN hμ y) hzE hUo hUne hUA hzU
  exact CN_lt_of_annR' hN ha hμ hR'

end FourthRatio

end

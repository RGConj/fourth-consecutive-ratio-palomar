module

public import RequestProject.DegCore

/-!
# No continuous homotopy from `qdir` to `-qdir` on the unit sphere

A continuous homotopy on `S² × [0,1]` is approximated by a smooth one (Stone–Weierstrass),
normalised, extended `0`-homogeneously and padded with straight-line homotopies at both ends so
that it becomes exactly `±qdir` for `s ≤ -1`, `s ≥ 2`.  This contradicts
`no_smooth_deformation`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio.Degree

/-- Smooth functions are uniformly dense in the continuous functions on a compact set. -/
lemma exists_smooth_approx {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Set V} (hX : IsCompact X) (f : V → ℝ) (hf : ContinuousOn f X)
    {ε : ℝ} (hε : 0 < ε) : ∃ g : V → ℝ, ContDiff ℝ ⊤ g ∧ ∀ p ∈ X, |g p - f p| < ε := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.1 hX
  let A : Subalgebra ℝ C(X, ℝ) :=
    { carrier := {F | ∃ g : V → ℝ, ContDiff ℝ ⊤ g ∧ ∀ x : X, F x = g x}
      mul_mem' := by
        rintro F G ⟨g, hg, hFg⟩ ⟨k, hk, hGk⟩
        exact ⟨fun x => g x * k x, hg.mul hk, fun x => by simp [hFg, hGk]⟩
      add_mem' := by
        rintro F G ⟨g, hg, hFg⟩ ⟨k, hk, hGk⟩
        exact ⟨fun x => g x + k x, hg.add hk, fun x => by simp [hFg, hGk]⟩
      algebraMap_mem' := by
        intro r
        exact ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have hxy' : (x : V) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hxy'
    refine ⟨fun z => ℓ z, ⟨⟨(ℓ : V → ℝ) ∘ Subtype.val, ℓ.continuous.comp continuous_subtype_val⟩,
      ⟨ℓ, ℓ.contDiff, fun z => rfl⟩, rfl⟩, hℓ⟩
  obtain ⟨⟨G, g, hg, hGg⟩, hG⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsep
      ⟨X.restrict f, hf.restrict⟩ ε hε
  refine ⟨g, hg, fun p hp => ?_⟩
  have h1 := (G - ⟨X.restrict f, hf.restrict⟩).norm_coe_le_norm ⟨p, hp⟩
  have h2 : (G - ⟨X.restrict f, hf.restrict⟩) ⟨p, hp⟩ = g p - f p := by
    simp [hGg]
    rfl
  rw [h2, Real.norm_eq_abs] at h1
  exact lt_of_le_of_lt h1 hG

lemma norm_le_sum_abs (v : E3) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have h : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [norm_sq_E3]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2), sq_abs (v 0), sq_abs (v 1),
      sq_abs (v 2), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 h

/-- Smooth uniform approximation of `ℝ³`-valued continuous maps on compact sets. -/
lemma exists_smooth_approx3 {X : Set (E3 × ℝ)} (hX : IsCompact X) (H : E3 × ℝ → E3)
    (hH : ContinuousOn H X) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : E3 × ℝ → E3, ContDiff ℝ ⊤ K ∧ ∀ p ∈ X, ‖K p - H p‖ < ε := by
  have hc : ∀ i : Fin 3, ContinuousOn (fun p => H p i) X := fun i =>
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp_continuousOn hH
  choose g hg hgH using fun i : Fin 3 => exists_smooth_approx hX _ (hc i) (by positivity : 0 < ε / 3)
  refine ⟨fun p => mk3 (g 0 p) (g 1 p) (g 2 p), ?_, fun p hp => ?_⟩
  · unfold mk3
    exact (((hg 0).smul contDiff_const).add ((hg 1).smul contDiff_const)).add
      ((hg 2).smul contDiff_const)
  · refine lt_of_le_of_lt (norm_le_sum_abs _) ?_
    simp only [PiLp.sub_apply, mk3_0, mk3_1, mk3_2]
    linarith [hgH 0 p hp, hgH 1 p hp, hgH 2 p hp]

/-- Normalisation `x ↦ x / |x|`. -/
def nrm (x : E3) : E3 := ‖x‖⁻¹ • x

lemma norm_nrm {x : E3} (hx : x ≠ 0) : ‖nrm x‖ = 1 := by
  simp [nrm, norm_smul, norm_ne_zero_iff.2 hx]

lemma nrm_of_norm_one {x : E3} (hx : ‖x‖ = 1) : nrm x = x := by simp [nrm, hx]

lemma contDiffAt_nrm {x : E3} (hx : x ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n nrm x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id

lemma qdir_nrm {y : E3} (hy : y ≠ 0) : qdir (nrm y) = qdir y := by
  simp only [nrm]
  exact qdir_smul (inv_pos.2 (norm_pos_iff.2 hy)) y

lemma nrm_mem_sphere {y : E3} (hy : y ≠ 0) : nrm y ∈ sphere (0 : E3) 1 := by
  simp [norm_nrm hy]

/-- If `x` is within `1/4` of a unit vector then `|x| ≥ 3/4`. -/
lemma ne_zero_of_near_unit {x c : E3} (hc : ‖c‖ = 1) (h : ‖x - c‖ ≤ 1 / 4) : x ≠ 0 := by
  intro hx
  rw [hx, zero_sub, norm_neg, hc] at h
  norm_num at h

/-- **No continuous homotopy from `qdir` to `-qdir`** on the unit sphere of `ℝ³`. -/
theorem no_continuous_homotopy (H : E3 × ℝ → E3)
    (hH : ContinuousOn H (sphere (0 : E3) 1 ×ˢ Icc (0 : ℝ) 1))
    (hH1 : ∀ v ∈ sphere (0 : E3) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖H (v, s)‖ = 1)
    (h0 : ∀ v ∈ sphere (0 : E3) 1, H (v, 0) = qdir v)
    (h1 : ∀ v ∈ sphere (0 : E3) 1, H (v, 1) = -qdir v) : False := by
  obtain ⟨K, hK, hKH⟩ := exists_smooth_approx3 ((isCompact_sphere 0 1).prod isCompact_Icc) H hH
    (by norm_num : (0 : ℝ) < 1 / 4)
  set θ0 : ℝ → ℝ := fun s => Real.smoothTransition (s + 1)
  set θ1 : ℝ → ℝ := fun s => Real.smoothTransition (s - 1)
  set κ : ℝ → ℝ := fun s => Real.smoothTransition s
  set X : E3 × ℝ → E3 := fun p => (1 - θ0 p.2) • qdir p.1 +
    (θ0 p.2 - θ1 p.2) • K (nrm p.1, κ p.2) - θ1 p.2 • qdir p.1
  set U : E3 × ℝ → E3 := fun p => nrm (X p)
  have hκ : ∀ s, κ s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- the interpolated vector stays away from zero
  have hXne : ∀ p : E3 × ℝ, p.1 ≠ 0 → X p ≠ 0 := by
    rintro ⟨y, s⟩ hy
    simp only at hy
    have hv := nrm_mem_sphere hy
    have hq : qdir y = qdir (nrm y) := (qdir_nrm hy).symm
    have hqn : ‖qdir (nrm y)‖ = 1 := norm_qdir (by simpa using (ne_of_mem_sphere hv one_ne_zero))
    rcases le_or_gt s 0 with hs | hs
    · have e1 : θ1 s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      have e2 : κ s = 0 := Real.smoothTransition.zero_of_nonpos hs
      have hb := hKH (nrm y, 0) ⟨hv, by simp⟩
      rw [h0 _ hv] at hb
      refine ne_zero_of_near_unit hqn ?_
      have : X (y, s) - qdir (nrm y) = θ0 s • (K (nrm y, 0) - qdir (nrm y)) := by
        simp only [X, e1, e2, hq]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      calc θ0 s * ‖K (nrm y, 0) - qdir (nrm y)‖ ≤ 1 * (1 / 4) :=
            mul_le_mul (Real.smoothTransition.le_one _) hb.le (norm_nonneg _) zero_le_one
        _ = 1 / 4 := by ring
    rcases le_or_gt s 1 with hs1 | hs1
    · have e0 : θ0 s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
      have e1 : θ1 s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      have hb := hKH (nrm y, κ s) ⟨hv, hκ s⟩
      refine ne_zero_of_near_unit (hH1 _ hv _ (hκ s)) ?_
      have : X (y, s) = K (nrm y, κ s) := by simp only [X, e0, e1]; module
      rw [this]; exact hb.le
    · have e0 : θ0 s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
      have e2 : κ s = 1 := Real.smoothTransition.one_of_one_le hs1.le
      have hb := hKH (nrm y, 1) ⟨hv, by simp⟩
      rw [h1 _ hv] at hb
      refine ne_zero_of_near_unit (c := -qdir (nrm y)) (by rw [norm_neg, hqn]) ?_
      have : X (y, s) - -qdir (nrm y) = (1 - θ1 s) • (K (nrm y, 1) - -qdir (nrm y)) := by
        simp only [X, e0, e2, hq]; module
      rw [this, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [Real.smoothTransition.le_one (s - 1)])]
      calc (1 - θ1 s) * ‖K (nrm y, 1) - -qdir (nrm y)‖ ≤ 1 * (1 / 4) :=
            mul_le_mul (by linarith [Real.smoothTransition.nonneg (s - 1)]) hb.le (norm_nonneg _)
              zero_le_one
        _ = 1 / 4 := by ring
  -- smoothness
  have hU : ContDiffOn ℝ 2 U {p | p.1 ≠ 0} := by
    rintro ⟨y, s⟩ hy
    simp only [mem_setOf_eq] at hy
    refine ContDiffAt.contDiffWithinAt ?_
    have hθ : ∀ c : ℝ, ContDiffAt ℝ 2 (fun p : E3 × ℝ => Real.smoothTransition (p.2 + c)) (y, s) :=
      fun c => (Real.smoothTransition.contDiff.comp (contDiff_snd.add contDiff_const)).contDiffAt
    have hq : ContDiffAt ℝ 2 (fun p : E3 × ℝ => qdir p.1) (y, s) :=
      ContDiffAt.comp (g := qdir) (f := Prod.fst) (y, s) (contDiffAt_qdir hy) contDiffAt_fst
    have hKc : ContDiffAt ℝ 2 (fun p : E3 × ℝ => K (nrm p.1, κ p.2)) (y, s) := by
      have hin : ContDiffAt ℝ 2 (fun p : E3 × ℝ => (nrm p.1, κ p.2)) (y, s) :=
        ((contDiffAt_nrm hy).comp (y, s) contDiffAt_fst).prodMk
          (Real.smoothTransition.contDiff.comp contDiff_snd).contDiffAt
      exact (hK.of_le le_top).contDiffAt.comp (y, s) hin
    have hX : ContDiffAt ℝ 2 X (y, s) := by
      have h0' := hθ 1
      have h1' := hθ (-1)
      simp only [← sub_eq_add_neg] at h1'
      exact (((contDiffAt_const.sub h0').smul hq).add ((h0'.sub h1').smul hKc)).sub (h1'.smul hq)
    exact (contDiffAt_nrm (hXne (y, s) hy)).comp (y, s) hX
  refine no_smooth_deformation U hU (fun p hp => norm_nrm (hXne p hp)) ?_ ?_
  · intro y hy s hs
    have e0 : θ0 s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have e1 : θ1 s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [U, X, e0, e1]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact nrm_of_norm_one (norm_qdir hy)
  · intro y hy s hs
    have e0 : θ0 s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have e1 : θ1 s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    simp only [U, X, e0, e1]
    simp only [sub_self, zero_smul, add_zero, one_smul, zero_sub]
    exact nrm_of_norm_one (by rw [norm_neg, norm_qdir hy])

end FourthRatio.Degree

end

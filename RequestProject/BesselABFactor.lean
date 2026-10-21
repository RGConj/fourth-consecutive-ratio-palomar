module

public import RequestProject.BesselRatioConvex
public import RequestProject.RadialQuotientAntitone

/-!
# The decreasing radial factor of the Ashbaugh--Benguria profile

The quotient here is `abW(t)/t` on the positive interval, with its regular
value at zero. This is one of the slope bounds needed for the energy lemma.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

/-- The regular radial factor of the Ashbaugh--Benguria ratio decreases. -/
theorem ab_bessel_factor_antitone {ν : ℝ} (hν : 0 ≤ ν) :
    AntitoneOn (fun t => besselF (ν + 1) (besselZero (ν + 1) 1 * t) /
      besselF ν (besselZero ν 1 * t)) (Ico 0 1) := by
  have hμ : 0 ≤ ν + 1 := by linarith
  obtain ⟨hj, -, hFj, -⟩ := besselZero_props hν
  obtain ⟨hk, -, hFk, -⟩ := besselZero_props hμ
  set j := besselZero ν 1
  set k := besselZero (ν + 1) 1
  set A : ℝ → ℝ := fun t => besselF ν (j * t)
  set A1 : ℝ → ℝ := fun t => j * besselF1 ν (j * t)
  set A2 : ℝ → ℝ := fun t => j ^ 2 * besselF2 ν (j * t)
  set C : ℝ → ℝ := fun t => besselF (ν + 1) (k * t)
  set C1 : ℝ → ℝ := fun t => k * besselF1 (ν + 1) (k * t)
  set C2 : ℝ → ℝ := fun t => k ^ 2 * besselF2 (ν + 1) (k * t)
  have hAd : ∀ t, HasDerivAt A (A1 t) t := by
    intro t
    have h := (hasDerivAt_besselF' hν (j * t)).comp t ((hasDerivAt_id t).const_mul j)
    convert h using 1 <;> (try rfl) <;> (try dsimp only [A1]) <;> ring
  have hA1d : ∀ t, HasDerivAt A1 (A2 t) t := by
    intro t
    have h := ((hasDerivAt_besselF1' hν (j * t)).comp t
      ((hasDerivAt_id t).const_mul j)).const_mul j
    convert h using 1 <;> (try rfl) <;> (try dsimp only [A2]) <;> ring
  have hCd : ∀ t, HasDerivAt C (C1 t) t := by
    intro t
    have h := (hasDerivAt_besselF' hμ (k * t)).comp t ((hasDerivAt_id t).const_mul k)
    convert h using 1 <;> (try rfl) <;> (try dsimp only [C1]) <;> ring
  have hC1d : ∀ t, HasDerivAt C1 (C2 t) t := by
    intro t
    have h := ((hasDerivAt_besselF1' hμ (k * t)).comp t
      ((hasDerivAt_id t).const_mul k)).const_mul k
    convert h using 1 <;> (try rfl) <;> (try dsimp only [C2]) <;> ring
  have hodeA : ∀ t, t * A2 t + (2 * ν + 1) * A1 t + j ^ 2 * t * A t = 0 := by
    intro t
    have h := besselF_ode' hν (j * t)
    dsimp only [A, A1, A2]
    linear_combination j * h
  have hodeC : ∀ t, t * C2 t + (2 * ν + 1 + 2) * C1 t + k ^ 2 * t * C t = 0 := by
    intro t
    have h := besselF_ode' hμ (k * t)
    dsimp only [C, C1, C2]
    linear_combination k * h
  have hAp : ∀ t ∈ Ico 0 1, 0 < A t := by
    intro t ht
    apply besselF_pos_before hν (mul_nonneg hj.le ht.1)
    change j * t < j
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 hj
  have hCp : ∀ t ∈ Icc 0 1, 0 ≤ C t := by
    intro t ht
    by_cases ht1 : t = 1
    · simp [C, ht1, k, hFk]
    · apply le_of_lt
      apply besselF_pos_before hμ (mul_nonneg hk.le ht.1)
      change k * t < k
      simpa only [mul_one] using mul_lt_mul_of_pos_left (lt_of_le_of_ne ht.2 ht1) hk
  have harg : ∀ t ∈ Ioo 0 1, j * t ∈ Ioo 0 j := by
    intro t ht
    refine ⟨mul_pos hj ht.1, ?_⟩
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 hj
  have hKeq : ∀ t ∈ Ioo 0 1,
      -2 * A1 t / (t * A t) - (k ^ 2 - j ^ 2) =
        2 * j ^ 2 * (besselOrderRatio ν (j * t) / (j * t)) - (k ^ 2 - j ^ 2) := by
    intro t ht
    have hne : besselF ν (j * t) ≠ 0 := (hAp t ⟨ht.1.le, ht.2⟩).ne'
    dsimp only [A, A1, besselOrderRatio]
    field_simp [ht.1.ne', hj.ne', hne] <;> ring
  apply radial_quotient_antitone (by linarith : 0 < 2 * ν + 1)
    hAd hA1d hCd hC1d hodeA hodeC
    (by simpa [A, j] using hFj) (by simpa [C, k] using hFk) hAp hCp
  intro t ht u hu htu
  change -2 * A1 t / (t * A t) - (k ^ 2 - j ^ 2) ≤
    -2 * A1 u / (u * A u) - (k ^ 2 - j ^ 2)
  rw [hKeq t ht, hKeq u hu]
  have h := (besselOrderRatio_div_strictMonoOn hν).monotoneOn
    (harg t ht) (harg u hu) (mul_le_mul_of_nonneg_left htu hj.le)
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left h (by positivity)) _

end FourthRatio

end

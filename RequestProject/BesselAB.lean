module

public import RequestProject.WronskianMonotone
public import RequestProject.BesselGap

/-!
# The increasing Ashbaugh--Benguria Bessel ratio

The Wronskian proof in Section 3 of Ashbaugh--Benguria, *A second proof of the
Payne--Pólya--Weinberger conjecture*, Comm. Math. Phys. 147 (1992), 181--190.
This proves the first Bessel monotonicity statement. The decreasing energy
weight requires a separate argument.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

/-- The first Ashbaugh--Benguria Bessel lemma, proved directly by the
Wronskian argument. This is the expression used by `abW`. -/
theorem ab_bessel_monotone {ν : ℝ} (hν : 0 ≤ ν) :
    MonotoneOn (fun t =>
      t * besselSeries (ν + 1) 1 (besselZero (ν + 1) 1 ^ 2 * t ^ 2) /
        besselSeries ν 1 (besselZero ν 1 ^ 2 * t ^ 2)) (Ico 0 1) := by
  have hμ : 0 ≤ ν + 1 := by linarith
  obtain ⟨hj, -, hFj, -⟩ := besselZero_props hν
  obtain ⟨hk, -, hFk, -⟩ := besselZero_props hμ
  set j := besselZero ν 1
  set k := besselZero (ν + 1) 1
  set A : ℝ → ℝ := fun t => besselF ν (j * t)
  set A1 : ℝ → ℝ := fun t => j * besselF1 ν (j * t)
  set A2 : ℝ → ℝ := fun t => j ^ 2 * besselF2 ν (j * t)
  set B : ℝ → ℝ := fun t => t * besselF (ν + 1) (k * t)
  set B1 : ℝ → ℝ := fun t =>
    besselF (ν + 1) (k * t) + t * k * besselF1 (ν + 1) (k * t)
  set B2 : ℝ → ℝ := fun t =>
    2 * k * besselF1 (ν + 1) (k * t) + t * k ^ 2 * besselF2 (ν + 1) (k * t)
  have hAd : ∀ t, HasDerivAt A (A1 t) t := by
    intro t
    have h := (hasDerivAt_besselF' hν (j * t)).comp t ((hasDerivAt_id t).const_mul j)
    convert h using 1 <;> (try rfl) <;> (try dsimp [A1]) <;> ring
  have hA1d : ∀ t, HasDerivAt A1 (A2 t) t := by
    intro t
    have h := ((hasDerivAt_besselF1' hν (j * t)).comp t
      ((hasDerivAt_id t).const_mul j)).const_mul j
    convert h using 1 <;> (try rfl) <;> (try dsimp [A2]) <;> ring
  have hFd : ∀ t, HasDerivAt (fun t => besselF (ν + 1) (k * t))
      (k * besselF1 (ν + 1) (k * t)) t := by
    intro t
    have h := (hasDerivAt_besselF' hμ (k * t)).comp t ((hasDerivAt_id t).const_mul k)
    convert h using 1
    · rfl
    · ring
  have hF1d : ∀ t, HasDerivAt (fun t => besselF1 (ν + 1) (k * t))
      (k * besselF2 (ν + 1) (k * t)) t := by
    intro t
    have h := (hasDerivAt_besselF1' hμ (k * t)).comp t ((hasDerivAt_id t).const_mul k)
    convert h using 1
    · rfl
    · ring
  have hBd : ∀ t, HasDerivAt B (B1 t) t := by
    intro t
    have h := (hasDerivAt_id t).mul (hFd t)
    convert h using 1 <;> (try rfl) <;> (try dsimp [B1]) <;> ring
  have hB1d : ∀ t, HasDerivAt B1 (B2 t) t := by
    intro t
    have h := (hFd t).add ((((hasDerivAt_id t).const_mul k).mul (hF1d t)))
    convert h using 1 <;> (try funext u) <;> dsimp [B1, B2] <;> ring
  have hodeA : ∀ t, t * A2 t + (2 * ν + 1) * A1 t + j ^ 2 * t * A t = 0 := by
    intro t
    have h := besselF_ode' hν (j * t)
    dsimp [A, A1, A2]
    linear_combination j * h
  have hodeB : ∀ t, t ^ 2 * B2 t + (2 * ν + 1) * t * B1 t +
      (k ^ 2 * t ^ 2 - (2 * ν + 1)) * B t = 0 := by
    intro t
    have h := besselF_ode' hμ (k * t)
    dsimp [B, B1, B2]
    linear_combination k * t ^ 2 * h
  have hab : j ^ 2 ≤ k ^ 2 := by
    have h : j < k := besselZero_lt_succ hν
    nlinarith
  have hAp : ∀ t ∈ Ico 0 1, 0 < A t := by
    intro t ht
    apply besselF_pos_before hν (mul_nonneg hj.le ht.1)
    change j * t < j
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 hj
  have hBp : ∀ t ∈ Icc 0 1, 0 ≤ B t := by
    intro t ht
    by_cases ht1 : t = 1
    · simp [B, ht1, k, hFk]
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hp : 0 < besselF (ν + 1) (k * t) := by
        apply besselF_pos_before hμ (mul_nonneg hk.le ht.1)
        change k * t < k
        simpa only [mul_one] using mul_lt_mul_of_pos_left htlt hk
      exact mul_nonneg ht.1 hp.le
  have hm := radial_ratio_monotone (by linarith : 0 < 2 * ν + 1) hab
    hAd hA1d hBd hB1d hodeA hodeB
    (by simpa [A, j] using hFj) (by simp [B, k, hFk]) hAp hBp
  simpa only [A, B, besselF, mul_pow] using hm

end FourthRatio

end

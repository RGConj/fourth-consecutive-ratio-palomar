module

public import RequestProject.ChitiNonnegative
public import RequestProject.GroundState

/-! # Chiti ball-mass comparison for every first Dirichlet eigenfunction -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

theorem first_eigenfunction_ball_mass (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : IsDomain D) {p : Amb N}
    (hp : IsEigenfunction D p (eigenvalue D 1)) (center : RN N) (r : ℝ) :
    (∫ x in ball center r, (p.1 : RN N → ℝ) x ^ 2) *
        (∫ x in ball (0 : RN N) (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt (eigenvalue D 1)),
          besselEntire N (eigenvalue D 1) x ^ 2) ≤
      (∫ x in ball (0 : RN N) r ∩ ball 0 (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt (eigenvalue D 1)),
        besselEntire N (eigenvalue D 1) x ^ 2) * ∫ x, (p.1 : RN N → ℝ) x ^ 2 := by
  have hDm : MeasurableSet D := hD.1.1.measurableSet
  obtain ⟨M, hDsub⟩ := hD.1.2.2.subset_closedBall (0 : RN N)
  have hfin : volume D ≠ ∞ := ne_top_of_le_ne_top
    (isCompact_closedBall (0 : RN N) M).measure_ne_top (measure_mono hDsub)
  have hlam : 0 < eigenvalue D 1 := eigenvalue_one_pos hN hD.1
  obtain ⟨hSimple, u, f, hu, hrep, hpos⟩ := ground_state hN hD
  have hu0 : ∀ᵐ x, 0 ≤ (u.1 : RN N → ℝ) x :=
    ae_nonneg_of_contRep hDm hu.1 hrep (fun x hx => (hpos x hx).le)
  have hmass := eigenfunction_ball_mass_nonnegative hN hDm hfin hu hlam hu0 center r
  obtain ⟨t, ht⟩ := hSimple u p hu hp
  rw [ht]
  have hscale (A : Set (RN N)) :
      (∫ x in A, ((t • u).1 : RN N → ℝ) x ^ 2) = t ^ 2 * ∫ x in A, (u.1 : RN N → ℝ) x ^ 2 := by
    have he : (fun x => ((t • u).1 : RN N → ℝ) x ^ 2) =ᵐ[volume.restrict A]
        (fun x => t ^ 2 * (u.1 : RN N → ℝ) x ^ 2) := by
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul t u.1)] with x hx
      change (((t • u.1 : L2 N) : RN N → ℝ) x) ^ 2 = t ^ 2 * (u.1 : RN N → ℝ) x ^ 2
      rw [hx, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_congr_ae he, integral_const_mul]
  have htotal : (∫ x, ((t • u).1 : RN N → ℝ) x ^ 2) = t ^ 2 * ∫ x, (u.1 : RN N → ℝ) x ^ 2 := by
    simpa only [setIntegral_univ] using hscale univ
  rw [hscale (ball center r), htotal]
  have hs := mul_le_mul_of_nonneg_left hmass (sq_nonneg t)
  convert hs using 1 <;> ring

end FourthRatio
end

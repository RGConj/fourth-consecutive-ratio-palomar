module

public import RequestProject.BesselZeros

/-!
# Interlacing `j_{ν+1,1} < j_{ν,2}`

From `g_ν' = -g_{ν+1}/4` (for the entire series `g_ν(s) = ∑ (-1)^m (s/4)^m / (m! Γ(m+ν+1))`)
we get `F_ν'(x) = -(x/2) F_{ν+1}(x)`, so by Rolle's theorem `F_{ν+1}` vanishes between the first
two zeros of `F_ν`.
-/

@[expose] public section

open Set Nat

noncomputable section

namespace FourthRatio

lemma besselSeries1_eq {ν : ℝ} (hν : 0 ≤ ν) (s : ℝ) :
    besselSeries1 ν s = -(1 / 4) * besselSeries (ν + 1) 1 s := by
  rw [besselSeries1, besselSeries, ← tsum_mul_left]
  congr 1; funext m
  have hpos : 0 < (m : ℝ) + ν + 1 := by positivity
  have hg : Real.Gamma (((m + 1 : ℕ) : ℝ) + ν + 1) = Real.Gamma ((m : ℝ) + (ν + 1) + 1) := by
    push_cast; ring_nf
  unfold besselCoef
  rw [hg, Nat.factorial_succ, Nat.cast_mul, pow_succ, pow_succ]
  have hf : (0 : ℝ) < m ! := by positivity
  have hG : 0 < Real.Gamma ((m : ℝ) + (ν + 1) + 1) := Real.Gamma_pos_of_pos (by positivity)
  push_cast
  field_simp

/-- **Interlacing**: `j_{ν+1,1} < j_{ν,2}`. -/
theorem besselZero_succ_lt_two {ν : ℝ} (hν : 0 ≤ ν) :
    besselZero (ν + 1) 1 < besselZero ν 2 := by
  have hν' : 0 ≤ ν + 1 := by linarith
  obtain ⟨a1, a2, b1, b2, -, -⟩ := besselZero_props hν
  have hcont : ContinuousOn (besselF ν) (Icc (besselZero ν 1) (besselZero ν 2)) :=
    ((besselF_analytic hν).continuousOn).mono (subset_univ _)
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero a2 hcont (by rw [b1, b2])
    (fun x _ => hasDerivAt_besselF hν x)
  have hξpos : 0 < ξ := a1.trans hξ.1
  have hz : besselF (ν + 1) ξ = 0 := by
    rw [besselSeries1_eq hν] at hξ0
    have : ξ * besselF (ν + 1) ξ = 0 := by
      unfold besselF; linarith
    exact (mul_eq_zero.mp this).resolve_left hξpos.ne'
  have e1 := besselZero_succ_eq (ν := ν + 1) 0 le_rfl
  rw [show besselZero (ν + 1) 0 = 0 from rfl] at e1
  have hle : besselZero (ν + 1) 1 ≤ ξ := by
    rw [e1]
    exact csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨hξpos, hz⟩
  exact hle.trans_lt hξ.2

end FourthRatio

end

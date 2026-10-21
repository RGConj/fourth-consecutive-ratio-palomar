module

public import RequestProject.DegQp

/-!
# Squaring tangent lines

For a unit vector `v ∈ S²` and a tangent line `ℝ a` (`a ⊥ v`, `|a| = 1`), `Bmap v (a ⊗ a)` is a
unit vector orthogonal to `qdir v`.  In complex notation (`v = (z, h)`, `a = (α, β)`) it is
`(2α(hα - zβ), Im(α z̄)² - β²)/(1 + h²)`: the tangent vector at `q(v)` obtained by squaring the
direction of the line, which only depends on the line, not on the sign of `a`.
-/

@[expose] public section

open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio.Degree

/-- The squared tangent line, expressed through the matrix `P = a ⊗ a`. -/
def Bmap (v : E3) (P : Fin 3 → Fin 3 → ℝ) : E3 :=
  (1 + v 2 ^ 2)⁻¹ • mk3 (2 * (v 2 * (P 0 0 - P 1 1) - (P 0 2 * v 0 - P 1 2 * v 1)))
    (2 * (2 * v 2 * P 0 1 - (P 0 2 * v 1 + P 1 2 * v 0)))
    (P 1 1 * v 0 ^ 2 - 2 * P 0 1 * v 0 * v 1 + P 0 0 * v 1 ^ 2 - P 2 2)

lemma qdir_of_norm_one {v : E3} (hv : ‖v‖ = 1) :
    qdir v = (1 + v 2 ^ 2)⁻¹ • mk3 (v 0 ^ 2 - v 1 ^ 2) (2 * v 0 * v 1) (2 * v 2) := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hn := norm_sq_E3 v
  rw [hv] at hn
  have hPhi : Phi v = 1 + v 2 ^ 2 := by
    have h := Phi_sq v
    rw [hv] at h
    have : Phi v ^ 2 = (1 + v 2 ^ 2) ^ 2 := by rw [h]; nlinarith
    exact (pow_left_inj₀ (Phi_nonneg _) (by positivity) (by norm_num : (2:ℕ) ≠ 0)).1 this
  simp only [qdir, hPhi, Qp, hv, mul_one]

lemma Bmap_props {v a : E3} (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hva : ⟪v, a⟫ = 0) :
    ‖Bmap v (fun i j => a i * a j)‖ = 1 ∧ ⟪Bmap v (fun i j => a i * a j), qdir v⟫ = 0 := by
  have hn := norm_sq_E3 v
  have hna := norm_sq_E3 a
  rw [hv] at hn
  rw [ha] at hna
  rw [inner_E3] at hva
  have hD : 0 < 1 + v 2 ^ 2 := by positivity
  constructor
  · -- the norm
    have key : ‖mk3 (2 * (v 2 * (a 0 * a 0 - a 1 * a 1) - (a 0 * a 2 * v 0 - a 1 * a 2 * v 1)))
        (2 * (2 * v 2 * (a 0 * a 1) - (a 0 * a 2 * v 1 + a 1 * a 2 * v 0)))
        (a 1 * a 1 * v 0 ^ 2 - 2 * (a 0 * a 1) * v 0 * v 1 + a 0 * a 0 * v 1 ^ 2 - a 2 * a 2)‖ ^ 2
        = (1 + v 2 ^ 2) ^ 2 := by
      rw [norm_sq_E3]
      simp only [mk3_0, mk3_1, mk3_2]
      have hA : a 0 ^ 2 + a 1 ^ 2 = 1 - a 2 ^ 2 := by linarith
      have hZ : v 0 ^ 2 + v 1 ^ 2 = 1 - v 2 ^ 2 := by linarith
      have hP : a 0 * v 0 + a 1 * v 1 = -(a 2 * v 2) := by linarith
      have hq : (a 1 * v 0 - a 0 * v 1) ^ 2 = (1 - a 2 ^ 2) * (1 - v 2 ^ 2) - a 2 ^ 2 * v 2 ^ 2 := by
        have lag : (a 0 * v 0 + a 1 * v 1) ^ 2 + (a 1 * v 0 - a 0 * v 1) ^ 2 =
            (a 0 ^ 2 + a 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by ring
        rw [hA, hZ, hP] at lag
        linarith
      have e1 : (2 * (v 2 * (a 0 * a 0 - a 1 * a 1) - (a 0 * a 2 * v 0 - a 1 * a 2 * v 1))) ^ 2 +
          (2 * (2 * v 2 * (a 0 * a 1) - (a 0 * a 2 * v 1 + a 1 * a 2 * v 0))) ^ 2 =
          4 * (a 0 ^ 2 + a 1 ^ 2) * (v 2 ^ 2 * (a 0 ^ 2 + a 1 ^ 2) -
            2 * v 2 * a 2 * (a 0 * v 0 + a 1 * v 1) + a 2 ^ 2 * (v 0 ^ 2 + v 1 ^ 2)) := by ring
      have e2 : a 1 * a 1 * v 0 ^ 2 - 2 * (a 0 * a 1) * v 0 * v 1 + a 0 * a 0 * v 1 ^ 2 - a 2 * a 2
          = (a 1 * v 0 - a 0 * v 1) ^ 2 - a 2 ^ 2 := by ring
      rw [e1, e2, hA, hZ, hP, hq]
      ring
    have hB : Bmap v (fun i j => a i * a j) = (1 + v 2 ^ 2)⁻¹ • mk3
        (2 * (v 2 * (a 0 * a 0 - a 1 * a 1) - (a 0 * a 2 * v 0 - a 1 * a 2 * v 1)))
        (2 * (2 * v 2 * (a 0 * a 1) - (a 0 * a 2 * v 1 + a 1 * a 2 * v 0)))
        (a 1 * a 1 * v 0 ^ 2 - 2 * (a 0 * a 1) * v 0 * v 1 + a 0 * a 0 * v 1 ^ 2 - a 2 * a 2) := rfl
    rw [hB, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hD]
    have := (pow_left_inj₀ (norm_nonneg _) hD.le (by norm_num : (2:ℕ) ≠ 0)).1 key
    rw [this]
    exact inv_mul_cancel₀ hD.ne'
  · -- orthogonality
    rw [qdir_of_norm_one hv, Bmap, inner_smul_left, inner_smul_right, inner_E3]
    simp only [mk3_0, mk3_1, mk3_2, conj_trivial]
    have hP : a 0 * v 0 + a 1 * v 1 + a 2 * v 2 = 0 := by linarith
    have : (2 * (v 2 * (a 0 * a 0 - a 1 * a 1) - (a 0 * a 2 * v 0 - a 1 * a 2 * v 1))) *
        (v 0 ^ 2 - v 1 ^ 2) +
        (2 * (2 * v 2 * (a 0 * a 1) - (a 0 * a 2 * v 1 + a 1 * a 2 * v 0))) * (2 * v 0 * v 1) +
        (a 1 * a 1 * v 0 ^ 2 - 2 * (a 0 * a 1) * v 0 * v 1 + a 0 * a 0 * v 1 ^ 2 - a 2 * a 2) *
        (2 * v 2) = 0 := by
      linear_combination (2 * v 2 * ((a 0 * v 0 + a 1 * v 1) - a 2 * v 2) -
        2 * a 2 * (v 0 ^ 2 + v 1 ^ 2)) * hP - 2 * v 2 * a 2 ^ 2 * hn
    rw [this]
    ring

end FourthRatio.Degree

end

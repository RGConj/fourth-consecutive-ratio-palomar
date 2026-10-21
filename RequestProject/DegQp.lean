module

public import RequestProject.DegNullLagrangian

/-!
# The model map of degree two

`Qp(y) = (y₀² - y₁², 2 y₀ y₁, 2 y₂ |y|)`: in complex notation `(z, h) ↦ (z², 2h|y|)`.  It is
positively homogeneous of degree two, vanishes only at `0`, and its Jacobian determinant
`8 (y₀² + y₁²)(|y| + y₂²/|y|)` is nonnegative.  Its direction `qdir = Qp/|Qp|` restricted to the
unit sphere is the degree-two map `ζ ↦ ζ²` (stereographic coordinates).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio.Degree

lemma inner_E3 (v w : E3) : ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

lemma norm_sq_E3 (v : E3) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_three]

lemma ebas_apply (i j : Fin 3) : ebas i j = if j = i then 1 else 0 := by
  simp [ebas, PiLp.single_apply]

lemma eq_of_coords {v w : E3} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) : v = w := by
  ext i; fin_cases i <;> assumption

/-- Build a vector of `ℝ³` from its coordinates. -/
def mk3 (a b c : ℝ) : E3 := a • ebas 0 + b • ebas 1 + c • ebas 2

@[simp] lemma mk3_0 (a b c : ℝ) : mk3 a b c 0 = a := by simp [mk3, ebas_apply]
@[simp] lemma mk3_1 (a b c : ℝ) : mk3 a b c 1 = b := by simp [mk3, ebas_apply]
@[simp] lemma mk3_2 (a b c : ℝ) : mk3 a b c 2 = c := by simp [mk3, ebas_apply]

/-- The model map `Qp(y) = (y₀² - y₁², 2 y₀ y₁, 2 y₂ |y|)`. -/
def Qp (y : E3) : E3 := mk3 (y 0 ^ 2 - y 1 ^ 2) (2 * y 0 * y 1) (2 * y 2 * ‖y‖)

/-- `Φ(y) = |Qp(y)|`. -/
def Phi (y : E3) : ℝ := ‖Qp y‖

/-- The direction `Qp/|Qp|`. -/
def qdir (y : E3) : E3 := (Phi y)⁻¹ • Qp y

lemma Phi_sq (y : E3) : Phi y ^ 2 = (y 0 ^ 2 + y 1 ^ 2) ^ 2 + 4 * y 2 ^ 2 * ‖y‖ ^ 2 := by
  rw [Phi, norm_sq_E3 (Qp y)]
  simp only [Qp, mk3_0, mk3_1, mk3_2]
  ring

lemma Phi_nonneg (y : E3) : 0 ≤ Phi y := norm_nonneg _

lemma norm_sq_le_Phi (y : E3) : ‖y‖ ^ 2 ≤ Phi y := by
  have h := Phi_sq y
  have hn := norm_sq_E3 y
  have : (‖y‖ ^ 2) ^ 2 ≤ Phi y ^ 2 := by
    rw [h, hn]; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2),
      mul_nonneg (sq_nonneg (y 2)) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))]
  exact (pow_le_pow_iff_left₀ (by positivity) (Phi_nonneg y) (by norm_num : (2 : ℕ) ≠ 0)).1 this

lemma Phi_le (y : E3) : Phi y ≤ 2 * ‖y‖ ^ 2 := by
  have h := Phi_sq y
  have hn := norm_sq_E3 y
  have : Phi y ^ 2 ≤ (2 * ‖y‖ ^ 2) ^ 2 := by
    rw [h, mul_pow, hn]; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2),
      mul_nonneg (sq_nonneg (y 2)) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))]
  exact (pow_le_pow_iff_left₀ (Phi_nonneg y) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 this

lemma Phi_pos {y : E3} (hy : y ≠ 0) : 0 < Phi y :=
  lt_of_lt_of_le (by positivity) (norm_sq_le_Phi y)

lemma Qp_ne_zero {y : E3} (hy : y ≠ 0) : Qp y ≠ 0 := by
  intro h
  have := Phi_pos hy
  simp [Phi, h] at this

lemma Phi_mul_qdir {y : E3} (hy : y ≠ 0) : Phi y • qdir y = Qp y := by
  simp [qdir, smul_smul, (Phi_pos hy).ne']

lemma norm_qdir {y : E3} (hy : y ≠ 0) : ‖qdir y‖ = 1 := by
  simp only [qdir, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (Phi_pos hy)]
  exact inv_mul_cancel₀ (Phi_pos hy).ne'

lemma Qp_smul {t : ℝ} (ht : 0 < t) (y : E3) : Qp (t • y) = (t ^ 2) • Qp y := by
  apply eq_of_coords <;>
    simp [Qp, norm_smul, abs_of_pos ht] <;> ring

lemma Phi_smul {t : ℝ} (ht : 0 < t) (y : E3) : Phi (t • y) = t ^ 2 * Phi y := by
  simp [Phi, Qp_smul ht, norm_smul, abs_of_pos ht]

lemma qdir_smul {t : ℝ} (ht : 0 < t) (y : E3) : qdir (t • y) = qdir y := by
  simp only [qdir, Phi_smul ht, Qp_smul ht, smul_smul, mul_inv]
  congr 1
  field_simp

/-! ### Smoothness -/

lemma contDiffAt_coord (i : Fin 3) {n : WithTop ℕ∞} (y : E3) :
    ContDiffAt ℝ n (fun x : E3 => x i) y :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.contDiffAt

lemma contDiffAt_Qp {y : E3} (hy : y ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n Qp y := by
  have c := fun i => contDiffAt_coord (n := n) i y
  unfold Qp mk3
  refine ((((c 0).pow 2).sub ((c 1).pow 2)).smul contDiffAt_const).add
    ((((contDiffAt_const.mul (c 0)).mul (c 1))).smul contDiffAt_const) |>.add ?_
  exact ((contDiffAt_const.mul (c 2)).mul (contDiffAt_norm ℝ hy)).smul contDiffAt_const

lemma contDiffAt_Phi {y : E3} (hy : y ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n Phi y :=
  (contDiffAt_norm ℝ (Qp_ne_zero hy)).comp y (contDiffAt_Qp hy)

lemma contDiffAt_qdir {y : E3} (hy : y ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n qdir y :=
  ((contDiffAt_Phi hy).inv (Phi_pos hy).ne').smul (contDiffAt_Qp hy)

lemma continuous_Phi : Continuous Phi := by
  unfold Phi Qp mk3
  fun_prop

/-! ### The Jacobian of `Qp` -/

/-- A partial derivative computed along a coordinate line. -/
lemma pd_eq_of_hasDerivAt {h : E3 → E3} {y : E3} (hd : DifferentiableAt ℝ h y) {a b : Fin 3}
    {c : ℝ} (hc : HasDerivAt (fun t : ℝ => h (y + t • ebas a) b) c 0) : pd h y a b = c := by
  have hl : HasDerivAt (fun t : ℝ => y + t • ebas a) (ebas a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ebas a)).const_add y
  have hd' : HasFDerivAt h (fderiv ℝ h y) (y + (0 : ℝ) • ebas a) := by
    simpa using hd.hasFDerivAt
  have h1 := (EuclideanSpace.proj b : E3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hd'.comp_hasDerivAt (0 : ℝ) hl)
  exact h1.unique hc

lemma line_coord (y : E3) (t : ℝ) (a i : Fin 3) :
    (y + t • ebas a) i = y i + if i = a then t else 0 := by
  simp [ebas_apply]

lemma jac_Qp {y : E3} (hy : y ≠ 0) :
    jac Qp y = 8 * (y 0 ^ 2 + y 1 ^ 2) * (‖y‖ + y 2 ^ 2 / ‖y‖) := by
  have hd : DifferentiableAt ℝ Qp y := (contDiffAt_Qp hy (n := 1)).differentiableAt (by norm_num)
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
  -- the nine partial derivatives (only the needed ones)
  have p00 : pd Qp y 0 0 = 2 * y 0 := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_0, line_coord]
    simp
    have := ((hasDerivAt_id (0:ℝ)).const_add (y 0)).pow 2
    convert this using 1
    · rfl
    · norm_num
  have p10 : pd Qp y 1 0 = -(2 * y 1) := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_0, line_coord]
    simp
    have := (((hasDerivAt_id (0:ℝ)).const_add (y 1)).pow 2).const_sub (y 0 ^ 2)
    simpa using this
  have p20 : pd Qp y 2 0 = 0 := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_0, line_coord]
    simp
    exact hasDerivAt_const _ _
  have p01 : pd Qp y 0 1 = 2 * y 1 := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_1, line_coord]
    simp
    have := (((hasDerivAt_id (0:ℝ)).const_add (y 0)).const_mul 2).mul_const (y 1)
    simpa using this
  have p11 : pd Qp y 1 1 = 2 * y 0 := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_1, line_coord]
    simp
    have := ((hasDerivAt_id (0:ℝ)).const_add (y 1)).const_mul (2 * y 0)
    simpa using this
  have p21 : pd Qp y 2 1 = 0 := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_1, line_coord]
    simp
    exact hasDerivAt_const _ _
  have p22 : pd Qp y 2 2 = 2 * ‖y‖ + 2 * y 2 ^ 2 / ‖y‖ := by
    apply pd_eq_of_hasDerivAt hd
    simp only [Qp, mk3_2, line_coord]
    simp
    have hn : ∀ t : ℝ, ‖y + t • ebas 2‖ = √(y 0 ^ 2 + y 1 ^ 2 + (y 2 + t) ^ 2) := by
      intro t
      rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_E3]
      simp [ebas_apply]
    simp_rw [hn]
    have hs : HasDerivAt (fun t : ℝ => y 0 ^ 2 + y 1 ^ 2 + (y 2 + t) ^ 2) (2 * y 2) 0 := by
      have := (((hasDerivAt_id (0:ℝ)).const_add (y 2)).pow 2).const_add (y 0 ^ 2 + y 1 ^ 2)
      simpa using this
    have h0 : y 0 ^ 2 + y 1 ^ 2 + (y 2 + 0) ^ 2 ≠ 0 := by
      rw [add_zero, ← norm_sq_E3]; positivity
    have hsq := hs.sqrt h0
    have hlin : HasDerivAt (fun t : ℝ => 2 * (y 2 + t)) 2 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_add (y 2)).const_mul 2
    have := hlin.mul hsq
    convert this using 1
    have hnorm : √(y 0 ^ 2 + y 1 ^ 2 + (y 2 + 0) ^ 2) = ‖y‖ := by
      rw [add_zero, ← norm_sq_E3, Real.sqrt_sq (norm_nonneg _)]
    rw [hnorm]
    field_simp
    ring
  simp only [jac, Matrix.det_fin_three, Matrix.of_apply, p00, p10, p20, p01, p11, p21, p22]
  field_simp
  ring

lemma jac_Qp_nonneg {y : E3} (hy : y ≠ 0) : 0 ≤ jac Qp y := by
  rw [jac_Qp hy]
  have := norm_pos_iff.2 hy
  positivity

end FourthRatio.Degree

end

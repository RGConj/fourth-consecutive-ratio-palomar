module

public import RequestProject.BallDegreeOne
public import RequestProject.BallFinal
public import RequestProject.BallSecondLower

/-!
# The second eigenvalue of the ball and the full ball/annulus lemma

From the proved lower half `ball_second_lower` (`λ₂(B) ≥ C_N a`, and eigenfunctions with
eigenvalue `C_N a` span at most `N` dimensions) and the proved degree-one eigenfunctions
(`ball_degree_one`), we derive the statement of the paper: `λ₂(B) = C_N a` and the second
eigenspace has dimension exactly `N`.  The full ball/annulus lemma `ext_ball` follows.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The space of weak eigenfunctions of `D` with eigenvalue `μ` (together with `0`). -/
def eigSub (D : Set (RN N)) (μ : ℝ) : Submodule ℝ (Amb N) where
  carrier := {u | u ∈ H D ∧ ∀ φ ∈ H D, qf u φ = μ * l2 u φ}
  zero_mem' := ⟨(H D).zero_mem, fun φ _ => by simp [qf, l2]⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨(H D).add_mem hu hv, fun φ hφ => by
      rw [qf_add_left, l2_add_left, hu' φ hφ, hv' φ hφ]; ring⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨(H D).smul_mem c hu, fun φ hφ => by
      rw [qf_smul_left, l2_smul_left, hu' φ hφ]; ring⟩

/-- **Ball data, second eigenvalue.** With `ν = N/2 - 1`, `a > 0` and `R = j_{ν,1}/√a`, for every
ball `B = B_R(y)`: `λ₂(B) = C_N a` and the second eigenspace has dimension `N`.

Derived from the lower half `ball_second_lower` (proved in `RequestProject/BallSecondLower.lean`)
together with the proved
degree-one eigenfunctions `ball_degree_one` (which give `λ₂(B) ≤ C_N a` by min–max and at least
`N` independent eigenfunctions). -/
theorem ext_ball_second (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let R := besselZero ν 1 / Real.sqrt a
    ∀ y : RN N,
      eigenvalue (ball y R) 2 = CN N * a ∧
      (∃ V : Submodule ℝ (Amb N), Module.finrank ℝ V = N ∧
        ∀ u, u ∈ V ↔ (u ∈ H (ball y R) ∧ ∀ φ ∈ H (ball y R), qf u φ = CN N * a * l2 u φ)) := by
  intro ν R y
  obtain ⟨hlow, hdim⟩ := ball_second_lower hN ha y
  obtain ⟨V0, hV0dim, hV0⟩ := ball_degree_one hN ha y
  set E := eigSub (ball y R) (CN N * a) with hE
  obtain ⟨hEfin, hEle⟩ := hdim E (fun u hu => hu)
  have hV0E : V0 ≤ E := fun u hu => hV0 u hu
  have hge : N ≤ Module.finrank ℝ E := by
    have := Submodule.finrank_mono hV0E
    omega
  have hC := CN_gt_one hN
  have hR : 0 < R := div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  obtain ⟨-, φB, hφB, -⟩ := ball_first_eigen hN ha y
  obtain ⟨VB, -, hVBle, hVBdim, hVBq⟩ := ball_subspace hN ha hC hφB hV0dim hV0
  have hup : eigenvalue (ball y R) 2 ≤ CN N * a :=
    (eigenvalue_mono hN (isDomain_ball y hR).1 (by norm_num) (by omega)).trans
      (eigenvalue_le_of_subspace hVBle hVBdim (by positivity) hVBq)
  exact ⟨le_antisymm hup hlow, E, le_antisymm hEle hge, fun u => Iff.rfl⟩

/-- **Ball and annulus data, spectral part.** With `ν = N/2 - 1`, `a > 0`,
`R = j_{ν,1}/√a`, `R' = j_{ν,2}/√a` and `Φ = besselEntire N a`, for every ball `B = B_R(y)`:
`λ₁(B) = a`, `λ₂(B) = C_N a`, the second eigenspace has dimension `N`; `Φ(· - y)` restricted to
`B` is a first eigenfunction of `B` and `-Φ(· - y)` restricted to the annulus
`A = {R < |x - y| < R'}` is a first eigenfunction of `A` with eigenvalue `a = λ₁(A)`.

Proved from `ball_first_eigen`, `annulus_first_eigen` and `ext_ball_second` (second eigenvalue
and second eigenspace of the ball); no external input is used. -/
theorem ext_ball_spectral (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let R := besselZero ν 1 / Real.sqrt a
    let R' := besselZero ν 2 / Real.sqrt a
    let Φ := besselEntire N a
    ∀ y : RN N,
      eigenvalue (ball y R) 1 = a ∧ eigenvalue (ball y R) 2 = CN N * a ∧
      (∃ V : Submodule ℝ (Amb N), Module.finrank ℝ V = N ∧
        ∀ u, u ∈ V ↔ (u ∈ H (ball y R) ∧ ∀ φ ∈ H (ball y R), qf u φ = CN N * a * l2 u φ)) ∧
      (∃ φ : Amb N, IsEigenfunction (ball y R) φ a ∧
        (φ.1 : RN N → ℝ) =ᵐ[volume] (ball y R).indicator (fun x => Φ (x - y))) ∧
      (eigenvalue {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} 1 = a ∧
        ∃ ψ : Amb N, IsEigenfunction {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} ψ a ∧
        (ψ.1 : RN N → ℝ) =ᵐ[volume]
          {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'}.indicator (fun x => -Φ (x - y))) := by
  intro ν R R' Φ y
  obtain ⟨hB1, φ, hφ, hφ1⟩ := ball_first_eigen hN ha y
  obtain ⟨hA1, ψ, hψ, hψ1⟩ := annulus_first_eigen hN ha y
  obtain ⟨h2, hV⟩ := ext_ball_second hN ha y
  exact ⟨hB1, h2, hV, ⟨φ, hφ, hφ1⟩, hA1, ψ, hψ, hψ1⟩

/-- **Ball and annulus data (external lemma of the paper, full statement; now proved).** With `ν = N/2 - 1`,
`a > 0`, `R = j_{ν,1}/√a`, `R' = j_{ν,2}/√a`: the Bessel profile `Φ` extends analytically to
`ℝ^N`, solves `-ΔΦ = aΦ`, is positive on `B_R` and negative on the annulus `R < |x| < R'`;
`C_N > 1`; `λ₁(B) = a`, `λ₂(B) = C_N a` for every ball `B = B_R(y)`, the second eigenspace has
dimension `N`; `Φ(· - y)` restricted to `B` is a first eigenfunction of `B` and `-Φ(· - y)`
restricted to the annulus `A` is a positive first eigenfunction of `A` with eigenvalue `a`.

Proved from `RequestProject/BesselEntire.lean` (analyticity, `-ΔΦ = aΦ`, positivity on `B_R`)
`ext_bessel` (Bessel zeros, proved in `RequestProject/BesselZeros.lean`) and
`ext_ball_spectral` (spectral data). -/
theorem ext_ball (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let R := besselZero ν 1 / Real.sqrt a
    let R' := besselZero ν 2 / Real.sqrt a
    ∃ Φ : RN N → ℝ, AnalyticOnNhd ℝ Φ Set.univ ∧
      (∀ x, x ≠ 0 → Φ x = besselProfile N a x) ∧
      (∀ x, Laplacian.laplacian Φ x = -a * Φ x) ∧
      (∀ x, ‖x‖ < R → 0 < Φ x) ∧
      (∀ x, R < ‖x‖ → ‖x‖ < R' → Φ x < 0) ∧
      0 < R ∧ R < R' ∧ 1 < CN N ∧
      ∀ y : RN N,
        eigenvalue (ball y R) 1 = a ∧ eigenvalue (ball y R) 2 = CN N * a ∧
        (∃ V : Submodule ℝ (Amb N), Module.finrank ℝ V = N ∧
          ∀ u, u ∈ V ↔ (u ∈ H (ball y R) ∧ ∀ φ ∈ H (ball y R), qf u φ = CN N * a * l2 u φ)) ∧
        (∃ φ : Amb N, IsEigenfunction (ball y R) φ a ∧
          (φ.1 : RN N → ℝ) =ᵐ[volume] (ball y R).indicator (fun x => Φ (x - y))) ∧
        (eigenvalue {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} 1 = a ∧
          ∃ ψ : Amb N, IsEigenfunction {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} ψ a ∧
          (ψ.1 : RN N → ℝ) =ᵐ[volume]
            {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'}.indicator (fun x => -Φ (x - y))) :=
  by
  intro ν R R'
  obtain ⟨hj1, hj12, hJneg, hC⟩ := ext_bessel hN
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hR : 0 < R := div_pos hj1 hsa
  refine ⟨besselEntire N a, besselEntire_analytic hN ha.le,
    fun _ hx => besselEntire_eq_profile ha hx, besselEntire_laplacian hN ha.le,
    fun x hx => besselEntire_pos hN ha hx, fun x hx1 hx2 => ?_, hR,
    div_lt_div_of_pos_right hj12 hsa, hC, ext_ball_spectral hN ha⟩
  have hx0 : x ≠ 0 := by
    rintro rfl; simp at hx1; linarith
  refine besselEntire_neg_of_besselJ_neg ha hx0 (hJneg _ ?_ ?_)
  · calc besselZero ν 1 = Real.sqrt a * R := by simp only [R]; field_simp
      _ < Real.sqrt a * ‖x‖ := by gcongr
  · calc Real.sqrt a * ‖x‖ < Real.sqrt a * R' := by gcongr
      _ = besselZero ν 2 := by simp only [R']; field_simp


end FourthRatio

end

module

public import Mathlib

/-!
# The Jacobian determinant is a null Lagrangian (three dimensions)

For `C²` maps `f g : ℝ³ → ℝ³` on an open set `Ω` which agree outside a compact subset of `Ω`,
`∫_Ω det Df = ∫_Ω det Dg`.  The proof writes `det Dh = div (h₀ ∇h₁ × ∇h₂)` (symmetry of second
derivatives) and integrates the divergence of a compactly supported `C¹` field.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FourthRatio.Degree

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The standard basis vectors of `ℝ³`. -/
def ebas (i : Fin 3) : E3 := EuclideanSpace.single i 1

/-- The partial derivative `∂_a h_b`. -/
def pd (h : E3 → E3) (y : E3) (a b : Fin 3) : ℝ := fderiv ℝ h y (ebas a) b

/-- The second partial derivative `∂_k ∂_a h_b`. -/
def pd2 (h : E3 → E3) (y : E3) (k a b : Fin 3) : ℝ :=
  fderiv ℝ (fderiv ℝ h) y (ebas k) (ebas a) b

/-- The Jacobian determinant `det Dh(y)`. -/
def jac (h : E3 → E3) (y : E3) : ℝ := Matrix.det (Matrix.of fun b a => pd h y a b)

/-- The components of `∇h₁ × ∇h₂`. -/
def cofv (h : E3 → E3) (y : E3) : Fin 3 → ℝ :=
  ![pd h y 1 1 * pd h y 2 2 - pd h y 2 1 * pd h y 1 2,
    pd h y 2 1 * pd h y 0 2 - pd h y 0 1 * pd h y 2 2,
    pd h y 0 1 * pd h y 1 2 - pd h y 1 1 * pd h y 0 2]

/-- The vector field `h₀ ∇h₁ × ∇h₂` whose divergence is `det Dh`. -/
def Vfield (h : E3 → E3) (y : E3) (j : Fin 3) : ℝ := h y 0 * cofv h y j

/-- The `j`-th partial derivative of the `j`-th component of `Vfield`. -/
def Vderiv (h : E3 → E3) (y : E3) : Fin 3 → ℝ :=
  ![pd h y 0 0 * cofv h y 0 + h y 0 *
      (pd2 h y 0 1 1 * pd h y 2 2 + pd h y 1 1 * pd2 h y 0 2 2
        - (pd2 h y 0 2 1 * pd h y 1 2 + pd h y 2 1 * pd2 h y 0 1 2)),
    pd h y 1 0 * cofv h y 1 + h y 0 *
      (pd2 h y 1 2 1 * pd h y 0 2 + pd h y 2 1 * pd2 h y 1 0 2
        - (pd2 h y 1 0 1 * pd h y 2 2 + pd h y 0 1 * pd2 h y 1 2 2)),
    pd h y 2 0 * cofv h y 2 + h y 0 *
      (pd2 h y 2 0 1 * pd h y 1 2 + pd h y 0 1 * pd2 h y 2 1 2
        - (pd2 h y 2 1 1 * pd h y 0 2 + pd h y 1 1 * pd2 h y 2 0 2))]

lemma hasFDerivAt_pd {h : E3 → E3} {y : E3} (hd : DifferentiableAt ℝ (fderiv ℝ h) y)
    (a b : Fin 3) :
    HasFDerivAt (fun x => pd h x a b)
      ((EuclideanSpace.proj b).comp ((fderiv ℝ (fderiv ℝ h) y).flip (ebas a))) y := by
  have h1 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (ebas a) y)
  have h2 := (EuclideanSpace.proj b).hasFDerivAt.comp y h1
  simpa [pd, Function.comp_def] using h2

lemma hasLineDerivAt_Vfield {h : E3 → E3} {y : E3} (hh : ContDiffAt ℝ 2 h y) (j : Fin 3) :
    HasLineDerivAt ℝ (fun x => Vfield h x j) (Vderiv h y j) y (ebas j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ h) y :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdh : DifferentiableAt ℝ h y := hh.differentiableAt (by norm_num)
  have h0 : HasFDerivAt (fun x => h x 0)
      ((EuclideanSpace.proj (0 : Fin 3)).comp (fderiv ℝ h y)) y := by
    have := (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).hasFDerivAt.comp y hdh.hasFDerivAt
    exact this
  have P := fun a b => hasFDerivAt_pd hd a b
  fin_cases j
  · have := (h0.mul (((P 1 1).mul (P 2 2)).sub ((P 2 1).mul (P 1 2)))).hasLineDerivAt (ebas 0)
    convert this using 1 <;> simp [Vfield, Vderiv, cofv, pd, pd2] <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.sub_apply]) <;> ring
  · have := (h0.mul (((P 2 1).mul (P 0 2)).sub ((P 0 1).mul (P 2 2)))).hasLineDerivAt (ebas 1)
    convert this using 1 <;> simp [Vfield, Vderiv, cofv, pd, pd2] <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.sub_apply]) <;> ring
  · have := (h0.mul (((P 0 1).mul (P 1 2)).sub ((P 1 1).mul (P 0 2)))).hasLineDerivAt (ebas 2)
    convert this using 1 <;> simp [Vfield, Vderiv, cofv, pd, pd2] <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.sub_apply]) <;> ring

lemma pd2_symm {h : E3 → E3} {y : E3} (hh : ContDiffAt ℝ 2 h y) (k a b : Fin 3) :
    pd2 h y k a b = pd2 h y a k b := by
  have := hh.isSymmSndFDerivAt (by simp)
  simp only [pd2]
  rw [this]

lemma sum_Vderiv {h : E3 → E3} {y : E3} (hh : ContDiffAt ℝ 2 h y) :
    Vderiv h y 0 + Vderiv h y 1 + Vderiv h y 2 = jac h y := by
  have s := pd2_symm hh
  simp only [Vderiv, cofv, jac, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [s 1 0 1, s 2 0 2, s 2 0 1, s 1 0 2, s 2 1 1, s 2 1 2]
  ring

/-- The integral of a line derivative of a compactly supported function vanishes. -/
lemma integral_lineDeriv_eq_zero {W W' : E3 → ℝ} {v : E3} (hW : Continuous W)
    (hcW : HasCompactSupport W) (hW' : Continuous W') (hcW' : HasCompactSupport W')
    (hd : ∀ x, HasLineDerivAt ℝ W (W' x) x v) : ∫ x, W' x = 0 := by
  have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := fun _ => (1 : ℝ)) (f' := fun _ => 0) (g := W)
    (g' := W') (v := v) (by simp) (by simpa using hW'.integrable_of_hasCompactSupport hcW')
    (by simpa using hW.integrable_of_hasCompactSupport hcW)
    (fun x _ => by simpa using (hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt v) (fun x _ => hd x)
  simpa using this

lemma pd_congr {f g : E3 → E3} {x : E3} (h : f =ᶠ[𝓝 x] g) (a b : Fin 3) :
    pd f x a b = pd g x a b := by
  simp [pd, h.fderiv_eq]

lemma pd2_congr {f g : E3 → E3} {x : E3} (h : f =ᶠ[𝓝 x] g) (k a b : Fin 3) :
    pd2 f x k a b = pd2 g x k a b := by
  simp [pd2, h.fderiv.fderiv_eq]

lemma Vfield_congr {f g : E3 → E3} {x : E3} (h : f =ᶠ[𝓝 x] g) (j : Fin 3) :
    Vfield f x j = Vfield g x j := by
  simp only [Vfield, cofv, pd_congr h, h.eq_of_nhds]

lemma Vderiv_congr {f g : E3 → E3} {x : E3} (h : f =ᶠ[𝓝 x] g) (j : Fin 3) :
    Vderiv f x j = Vderiv g x j := by
  simp only [Vderiv, cofv, pd_congr h, pd2_congr h, h.eq_of_nhds]

lemma continuousAt_pd {f : E3 → E3} {Ω : Set E3} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 2 f Ω)
    {x : E3} (hx : x ∈ Ω) (a b : Fin 3) : ContinuousAt (fun y => pd f y a b) x := by
  have hc := (hf.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).continuousAt
    (hΩ.mem_nhds hx)
  have := (EuclideanSpace.proj b : E3 →L[ℝ] ℝ).continuous.continuousAt.comp
    (hc.clm_apply (continuousAt_const (y := ebas a)))
  exact this

lemma continuousAt_pd2 {f : E3 → E3} {Ω : Set E3} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 2 f Ω)
    {x : E3} (hx : x ∈ Ω) (k a b : Fin 3) : ContinuousAt (fun y => pd2 f y k a b) x := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) Ω := hf.fderiv_of_isOpen hΩ (by norm_num)
  have hc := (h1.continuousOn_fderiv_of_isOpen hΩ le_rfl).continuousAt (hΩ.mem_nhds hx)
  have := (EuclideanSpace.proj b : E3 →L[ℝ] ℝ).continuous.continuousAt.comp
    ((hc.clm_apply (continuousAt_const (y := ebas k))).clm_apply
      (continuousAt_const (y := ebas a)))
  exact this

lemma continuousAt_coord {f : E3 → E3} {Ω : Set E3} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 2 f Ω)
    {x : E3} (hx : x ∈ Ω) (b : Fin 3) : ContinuousAt (fun y => f y b) x := by
  have hc := (hf.continuousOn.continuousAt (hΩ.mem_nhds hx))
  exact (EuclideanSpace.proj b : E3 →L[ℝ] ℝ).continuous.continuousAt.comp hc

lemma continuousAt_Vfield {f : E3 → E3} {Ω : Set E3} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 2 f Ω)
    {x : E3} (hx : x ∈ Ω) (j : Fin 3) : ContinuousAt (fun y => Vfield f y j) x := by
  have P := continuousAt_pd hΩ hf hx
  have C := continuousAt_coord hΩ hf hx 0
  fin_cases j <;> simp only [Vfield, cofv] <;> simp <;>
    exact C.mul (((P _ _).mul (P _ _)).sub ((P _ _).mul (P _ _)))

lemma continuousAt_Vderiv {f : E3 → E3} {Ω : Set E3} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 2 f Ω)
    {x : E3} (hx : x ∈ Ω) (j : Fin 3) : ContinuousAt (fun y => Vderiv f y j) x := by
  have P := continuousAt_pd hΩ hf hx
  have P2 := continuousAt_pd2 hΩ hf hx
  have C := continuousAt_coord hΩ hf hx 0
  fin_cases j <;> simp only [Vderiv, cofv] <;> simp <;>
    exact ((P _ _).mul (((P _ _).mul (P _ _)).sub ((P _ _).mul (P _ _)))).add
      (C.mul ((((P2 _ _ _).mul (P _ _)).add ((P _ _).mul (P2 _ _ _))).sub
        (((P2 _ _ _).mul (P _ _)).add ((P _ _).mul (P2 _ _ _)))))

/-- **Null Lagrangian.** Two `C²` maps on an open set which agree outside a compact subset have
the same integral of the Jacobian determinant. -/
theorem null_lagrangian {Ω K : Set E3} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {f g : E3 → E3} (hf : ContDiffOn ℝ 2 f Ω) (hg : ContDiffOn ℝ 2 g Ω)
    (hfg : ∀ y ∈ Ω \ K, f y = g y) :
    ∫ y in Ω, (jac f y - jac g y) = 0 := by
  classical
  -- eventual equality away from `K`
  have hev : ∀ x ∈ Ω \ K, f =ᶠ[𝓝 x] g := fun x hx =>
    Filter.eventually_of_mem ((hΩ.sdiff hK.isClosed).mem_nhds hx) hfg
  set W : Fin 3 → E3 → ℝ := fun j x => if x ∈ Ω then Vfield f x j - Vfield g x j else 0
  set W' : Fin 3 → E3 → ℝ := fun j x => if x ∈ Ω then Vderiv f x j - Vderiv g x j else 0
  have hW0 : ∀ j, ∀ x ∉ K, W j x = 0 := by
    intro j x hx
    simp only [W]
    split_ifs with hΩx
    · rw [Vfield_congr (hev x ⟨hΩx, hx⟩)]; ring
    · rfl
  have hW'0 : ∀ j, ∀ x ∉ K, W' j x = 0 := by
    intro j x hx
    simp only [W']
    split_ifs with hΩx
    · rw [Vderiv_congr (hev x ⟨hΩx, hx⟩)]; ring
    · rfl
  have hWev : ∀ j, ∀ x ∉ K, W j =ᶠ[𝓝 x] fun _ => 0 := fun j x hx =>
    Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) (fun y hy => hW0 j y hy)
  have hW'ev : ∀ j, ∀ x ∉ K, W' j =ᶠ[𝓝 x] fun _ => 0 := fun j x hx =>
    Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) (fun y hy => hW'0 j y hy)
  have hWin : ∀ j, ∀ x ∈ Ω, W j =ᶠ[𝓝 x] fun y => Vfield f y j - Vfield g y j :=
    fun j x hx => Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => by simp [W, hy])
  have hW'in : ∀ j, ∀ x ∈ Ω, W' j =ᶠ[𝓝 x] fun y => Vderiv f y j - Vderiv g y j :=
    fun j x hx => Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => by simp [W', hy])
  have hcont : ∀ j, Continuous (W j) := by
    intro j
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ Ω
    · exact ((continuousAt_Vfield hΩ hf hx j).sub
        (continuousAt_Vfield hΩ hg hx j)).congr (hWin j x hx).symm
    · exact continuousAt_const.congr (hWev j x (fun h => hx (hKΩ h))).symm
  have hcont' : ∀ j, Continuous (W' j) := by
    intro j
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ Ω
    · exact ((continuousAt_Vderiv hΩ hf hx j).sub
        (continuousAt_Vderiv hΩ hg hx j)).congr (hW'in j x hx).symm
    · exact continuousAt_const.congr (hW'ev j x (fun h => hx (hKΩ h))).symm
  have hderiv : ∀ j, ∀ x, HasLineDerivAt ℝ (W j) (W' j x) x (ebas j) := by
    intro j x
    by_cases hx : x ∈ Ω
    · have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hΩ.mem_nhds hx)
      have hgx : ContDiffAt ℝ 2 g x := hg.contDiffAt (hΩ.mem_nhds hx)
      have := (hasLineDerivAt_Vfield hfx j).sub (hasLineDerivAt_Vfield hgx j)
      simp only [W', hx, if_true]
      exact HasLineDerivAt.congr_of_eventuallyEq
        (show HasLineDerivAt ℝ (fun y => Vfield f y j - Vfield g y j) _ x (ebas j) from this)
        (hWin j x hx)
    · have hxK : x ∉ K := fun h => hx (hKΩ h)
      rw [hW'0 j x hxK]
      have : HasLineDerivAt ℝ (fun _ : E3 => (0 : ℝ)) 0 x (ebas j) := by
        simpa using (hasFDerivAt_const (0 : ℝ) x).hasLineDerivAt (ebas j)
      exact this.congr_of_eventuallyEq (hWev j x hxK)
  have hzero : ∀ j, ∫ x, W' j x = 0 := fun j =>
    integral_lineDeriv_eq_zero (hcont j) (HasCompactSupport.intro hK (hW0 j)) (hcont' j)
      (HasCompactSupport.intro hK (hW'0 j)) (hderiv j)
  have hint : ∀ j, Integrable (W' j) :=
    fun j => (hcont' j).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hW'0 j))
  calc ∫ y in Ω, (jac f y - jac g y)
      = ∫ y in Ω, (W' 0 y + W' 1 y + W' 2 y) := by
        refine setIntegral_congr_fun hΩ.measurableSet fun y hy => ?_
        have hfy : ContDiffAt ℝ 2 f y := hf.contDiffAt (hΩ.mem_nhds hy)
        have hgy : ContDiffAt ℝ 2 g y := hg.contDiffAt (hΩ.mem_nhds hy)
        simp only [W', hy, if_true, ← sum_Vderiv hfy, ← sum_Vderiv hgy]
        ring
    _ = ∫ y, (W' 0 y + W' 1 y + W' 2 y) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
        simp [W', hy]
    _ = 0 := by
        rw [integral_add (f := fun y => W' 0 y + W' 1 y) (g := W' 2) ((hint 0).add (hint 1))
          (hint 2), integral_add (hint 0) (hint 1),
          hzero 0, hzero 1, hzero 2]
        ring

end FourthRatio.Degree

end

module

public import RequestProject.DegSmooth
public import RequestProject.DegBmap
public import RequestProject.External

/-!
# No line field on a thin slab around a separating level set

This proves the topological input used in the degree contradiction (the packaged form of
External theorem 2.7 in `RequestProject/External.lean`): for continuous `F : S³ → ℝ` with
`F(e) < 0 < F(-e)` and an open neighbourhood `𝒪` of `F⁻¹(0)`, the compact slab
`M = {u ∈ S³ : -ε ≤ F(u) ≤ 0}` (`ε` small) lies in `𝒪` and carries no continuous line field
`u ↦ ℝ w(u)` with `w(u) ⊥ u, e`.

Proof: writing `S³ ∖ {±e} ≅ S² × (-1, 1)`, a line field on `M` would give, after squaring the
lines (`Bmap`), a continuous homotopy from the degree-two map `qdir` to `-qdir` on `S²`
(rotate from `qdir` to `-qdir` through the squared line while crossing the slab), which is
impossible by `no_continuous_homotopy`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric Real
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio.Degree

open FourthRatio

lemma exists_basis_first {e : E4} (he : ‖e‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 4) ℝ E4, b 0 = e := by
  have hcard : Module.finrank ℝ E4 = Fintype.card (Fin 4) := by simp
  have hon : Orthonormal ℝ (({0} : Set (Fin 4)).restrict fun _ => e) := by
    refine ⟨fun i => by change ‖e‖ = 1; exact he, fun i j hij => ?_⟩
    exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, hb 0 rfl⟩

section Basis

variable (b : OrthonormalBasis (Fin 4) ℝ E4)

/-- The point `t b₀ + v₀ b₁ + v₁ b₂ + v₂ b₃`. -/
def emb (t : ℝ) (v : E3) : E4 := t • b 0 + v 0 • b 1 + v 1 • b 2 + v 2 • b 3

lemma inner_b_emb (t : ℝ) (v : E3) :
    ⟪b 0, emb b t v⟫ = t ∧ ⟪b 1, emb b t v⟫ = v 0 ∧ ⟪b 2, emb b t v⟫ = v 1 ∧
      ⟪b 3, emb b t v⟫ = v 2 := by
  simp only [emb, inner_add_right, inner_smul_right, b.inner_eq_ite]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

lemma inner_sum4 (x y : E4) :
    ⟪x, y⟫ = ⟪x, b 0⟫ * ⟪b 0, y⟫ + ⟪x, b 1⟫ * ⟪b 1, y⟫ + ⟪x, b 2⟫ * ⟪b 2, y⟫ +
      ⟪x, b 3⟫ * ⟪b 3, y⟫ := by
  rw [← b.sum_inner_mul_inner x y, Fin.sum_univ_four]

lemma norm_emb_sq (t : ℝ) (v : E3) : ‖emb b t v‖ ^ 2 = t ^ 2 + ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_sum4 b, norm_sq_E3]
  obtain ⟨h0, h1, h2, h3⟩ := inner_b_emb b t v
  rw [real_inner_comm (b 0) (emb b t v), real_inner_comm (b 1) (emb b t v),
    real_inner_comm (b 2) (emb b t v), real_inner_comm (b 3) (emb b t v), h0, h1, h2, h3]
  ring

lemma continuous_emb : Continuous fun p : ℝ × E3 => emb b p.1 p.2 := by
  unfold emb
  fun_prop

end Basis

lemma continuous_Bmap :
    Continuous fun x : E3 × (Fin 3 → Fin 3 → ℝ) => Bmap x.1 x.2 := by
  unfold Bmap mk3
  have hc : ∀ i, Continuous fun x : E3 × (Fin 3 → Fin 3 → ℝ) => x.1 i := fun i =>
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp continuous_fst
  have hP : ∀ i j, Continuous fun x : E3 × (Fin 3 → Fin 3 → ℝ) => x.2 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  have hden : Continuous (fun x : E3 × (Fin 3 → Fin 3 → ℝ) => (1 + x.1 2 ^ 2)⁻¹) :=
    (continuous_const.add ((hc 2).pow 2)).inv₀ fun x =>
      (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'
  refine hden.smul ?_
  refine ((Continuous.smul (M := ℝ) (X := E3) (Y := E3 × (Fin 3 → Fin 3 → ℝ))
    ?_ continuous_const).add (Continuous.smul (M := ℝ) (X := E3)
      (Y := E3 × (Fin 3 → Fin 3 → ℝ)) ?_ continuous_const)).add
        (Continuous.smul (M := ℝ) (X := E3) (Y := E3 × (Fin 3 → Fin 3 → ℝ))
          ?_ continuous_const)
  · exact continuous_const.mul (((hc 2).mul ((hP 0 0).sub (hP 1 1))).sub
        (((hP 0 2).mul (hc 0)).sub ((hP 1 2).mul (hc 1))))
  · exact continuous_const.mul (((continuous_const.mul (hc 2)).mul (hP 0 1)).sub
        (((hP 0 2).mul (hc 1)).add ((hP 1 2).mul (hc 0))))
  · exact (((((hP 1 1).mul ((hc 0).pow 2)).sub (((continuous_const.mul (hP 0 1)).mul (hc 0)).mul
        (hc 1))).add ((hP 0 0).mul ((hc 1).pow 2)))).sub (hP 2 2)

/-- The clamp `x ↦ min 1 (max 0 (-x/ε))`. -/
def clampσ (ε x : ℝ) : ℝ := min 1 (max 0 (-x / ε))

lemma continuous_clampσ (ε : ℝ) : Continuous (clampσ ε) := by
  unfold clampσ; fun_prop

lemma clampσ_of_nonneg {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) : clampσ ε x = 0 := by
  have : -x / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp [clampσ, max_eq_left this]

lemma clampσ_of_le {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ -ε) : clampσ ε x = 1 := by
  have : 1 ≤ -x / ε := by rw [le_div_iff₀ hε]; linarith
  simp [clampσ, max_eq_right (by linarith : (0 : ℝ) ≤ -x / ε), min_eq_left this]

/-! ### The homotopy built from a line field -/

section Homotopy

variable (b : OrthonormalBasis (Fin 4) ℝ E4) (η : ℝ)

/-- The height parameter `τ(s) = (1 - η)(2s - 1) ∈ [-(1-η), 1-η]`. -/
def tau (s : ℝ) : ℝ := (1 - η) * (2 * s - 1)

/-- The parametrisation `S² × [0,1] → S³`, `(v, s) ↦ τ e + √(1-τ²) v`. -/
def uuMap (p : E3 × ℝ) : E4 := emb b (tau η p.2) (√(1 - tau η p.2 ^ 2) • p.1)

lemma continuous_uuMap : Continuous (uuMap b η) := by
  unfold uuMap emb tau
  fun_prop

lemma tau_sq_lt {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    tau η s ^ 2 < 1 := by
  have h1 : |2 * s - 1| ≤ 1 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h2 : |tau η s| < 1 := by
    simp only [tau, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - η)]
    nlinarith [abs_nonneg (2 * s - 1)]
  exact (sq_lt_one_iff_abs_lt_one _).2 h2

lemma uuMap_mem_sphere {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {p : E3 × ℝ}
    (hp : p ∈ sphere (0 : E3) 1 ×ˢ Icc (0 : ℝ) 1) : uuMap b η p ∈ sphere (0 : E4) 1 := by
  obtain ⟨v, s⟩ := p
  obtain ⟨hv, hs⟩ := hp
  have hv1 : ‖v‖ = 1 := by simpa using hv
  have hτ := tau_sq_lt hη0 hη1 hs
  have hsq : 0 < √(1 - tau η s ^ 2) := Real.sqrt_pos.2 (by linarith)
  have h := norm_emb_sq b (tau η s) (√(1 - tau η s ^ 2) • v)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsq, hv1, mul_one,
    Real.sq_sqrt (by linarith)] at h
  simp only [mem_sphere_iff_norm, sub_zero]
  have : ‖uuMap b η (v, s)‖ ^ 2 = 1 := by simp only [uuMap]; rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by norm_num : (2:ℕ) ≠ 0)).1
    (by rw [this]; norm_num)

/-- The matrix of the line-field projection in the basis `b₁, b₂, b₃`. -/
def PmMap (Pi : E4 → E4 → E4) (u : E4) : Fin 3 → Fin 3 → ℝ :=
  fun i j => ⟪b i.succ, Pi u (b j.succ)⟫

open Classical in
/-- The squared line at the parametrised point (zero off `M`). -/
def BtMap (Pi : E4 → E4 → E4) (M : Set E4) (p : E3 × ℝ) : E3 :=
  if uuMap b η p ∈ M then Bmap p.1 (PmMap b Pi (uuMap b η p)) else 0

/-- The homotopy: rotate from `qdir` to `-qdir` through the squared line while crossing the
slab. -/
def HMap (Pi : E4 → E4 → E4) (M : Set E4) (F : E4 → ℝ) (ε : ℝ) (p : E3 × ℝ) : E3 :=
  Real.cos (π * clampσ ε (F (uuMap b η p))) • qdir p.1 +
    Real.sin (π * clampσ ε (F (uuMap b η p))) • BtMap b η Pi M p

lemma BtMap_props {e : E4} (hb0 : b 0 = e) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {Pi : E4 → E4 → E4} {M : Set E4}
    (hw : ∀ u ∈ M, ∃ w : E4, w ≠ 0 ∧ ⟪w, u⟫ = 0 ∧ ⟪w, e⟫ = 0 ∧
      ∀ x, Pi u x = (⟪w, x⟫ / ⟪w, w⟫) • w)
    {p : E3 × ℝ} (hp : p ∈ sphere (0 : E3) 1 ×ˢ Icc (0 : ℝ) 1) (hM : uuMap b η p ∈ M) :
    ‖BtMap b η Pi M p‖ = 1 ∧ ⟪BtMap b η Pi M p, qdir p.1⟫ = 0 := by
  obtain ⟨v, s⟩ := p
  obtain ⟨hv, hs⟩ := hp
  have hv1 : ‖v‖ = 1 := by simpa using hv
  obtain ⟨w, hw0, hwu, hwe, hPw⟩ := hw _ hM
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set a : E3 := mk3 (⟪b 1, w⟫ / ‖w‖) (⟪b 2, w⟫ / ‖w‖) (⟪b 3, w⟫ / ‖w‖) with hadef
  have hww : ⟪w, w⟫ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have hb0w : ⟪b 0, w⟫ = 0 := by rw [hb0, real_inner_comm]; exact hwe
  have hpars : ‖w‖ ^ 2 = ⟪b 1, w⟫ ^ 2 + ⟪b 2, w⟫ ^ 2 + ⟪b 3, w⟫ ^ 2 := by
    have hc : ∀ x : E4, ⟪w, x⟫ = ⟪x, w⟫ := fun x => real_inner_comm x w
    rw [← hww, inner_sum4 b w w]
    simp only [hc, hb0w]
    ring
  have hPm : PmMap b Pi (uuMap b η (v, s)) = fun i j => a i * a j := by
    funext i j
    simp only [PmMap, hPw, inner_smul_right, hww]
    have hn2 : ‖w‖ ^ 2 = ‖w‖ * ‖w‖ := sq _
    fin_cases i <;> fin_cases j <;>
      simp [hadef, real_inner_comm w, hn2] <;> ring
  have ha1 : ‖a‖ = 1 := by
    have : ‖a‖ ^ 2 = 1 := by
      rw [norm_sq_E3]
      simp only [hadef, mk3_0, mk3_1, mk3_2, div_pow]
      rw [← add_div, ← add_div, ← hpars, div_self (by positivity)]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by norm_num : (2:ℕ) ≠ 0)).1
      (by rw [this]; norm_num)
  have hva : ⟪v, a⟫ = 0 := by
    have h := hwu
    rw [inner_sum4 b] at h
    obtain ⟨e0, e1, e2, e3⟩ := inner_b_emb b (tau η s) (√(1 - tau η s ^ 2) • v)
    simp only [uuMap] at h
    rw [e0, e1, e2, e3] at h
    have hc : ∀ x : E4, ⟪w, x⟫ = ⟪x, w⟫ := fun x => real_inner_comm x w
    simp only [PiLp.smul_apply, smul_eq_mul, hc, hb0w] at h
    rw [inner_E3]
    simp only [hadef, mk3_0, mk3_1, mk3_2]
    have hc : 0 < √(1 - tau η s ^ 2) :=
      Real.sqrt_pos.2 (by linarith [tau_sq_lt hη0 hη1 hs])
    have : √(1 - tau η s ^ 2) * (v 0 * ⟪b 1, w⟫ + v 1 * ⟪b 2, w⟫ + v 2 * ⟪b 3, w⟫) = 0 := by
      linarith
    have h2 : v 0 * ⟪b 1, w⟫ + v 1 * ⟪b 2, w⟫ + v 2 * ⟪b 3, w⟫ = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc.ne'
      · exact h
    field_simp
    linarith
  have hB : BtMap b η Pi M (v, s) = Bmap v (fun i j => a i * a j) := by
    simp only [BtMap, if_pos hM, hPm]
  rw [hB]
  exact Bmap_props hv1 ha1 hva

lemma BtMap_norm_le {e : E4} (hb0 : b 0 = e) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {Pi : E4 → E4 → E4} {M : Set E4}
    (hw : ∀ u ∈ M, ∃ w : E4, w ≠ 0 ∧ ⟪w, u⟫ = 0 ∧ ⟪w, e⟫ = 0 ∧
      ∀ x, Pi u x = (⟪w, x⟫ / ⟪w, w⟫) • w)
    {p : E3 × ℝ} (hp : p ∈ sphere (0 : E3) 1 ×ˢ Icc (0 : ℝ) 1) : ‖BtMap b η Pi M p‖ ≤ 1 := by
  by_cases hM : uuMap b η p ∈ M
  · exact (BtMap_props b hb0 hη0 hη1 hw hp hM).1.le
  · simp [BtMap, if_neg hM]

lemma continuousOn_Pi_uuMap {Pi : E4 → E4 → E4} {M : Set E4}
    (hPi : ContinuousOn (fun p : E4 × E4 => Pi p.1 p.2) (M ×ˢ Set.univ))
    {N : Set (E3 × ℝ)} (hNM : ∀ q ∈ N, uuMap b η q ∈ M) (x : E4) :
    ContinuousOn (fun q : E3 × ℝ => Pi (uuMap b η q) x) N := by
  have h1 : Continuous fun q : E3 × ℝ => (uuMap b η q, x) :=
    (continuous_uuMap b η).prodMk continuous_const
  exact hPi.comp h1.continuousOn (fun q hq => ⟨hNM q hq, mem_univ _⟩)

lemma continuousWithinAt_inner_b {N : Set (E3 × ℝ)} {p : E3 × ℝ} {g : E3 × ℝ → E4} (i : Fin 4)
    (h : ContinuousWithinAt g N p) :
    ContinuousWithinAt (fun q => ⟪b i, g q⟫) N p :=
  (continuous_const.inner continuous_id).continuousAt.comp_continuousWithinAt h

lemma continuousWithinAt_PmMap {Pi : E4 → E4 → E4} {M : Set E4}
    (hPi : ContinuousOn (fun p : E4 × E4 => Pi p.1 p.2) (M ×ˢ Set.univ))
    {N : Set (E3 × ℝ)} (hNM : ∀ q ∈ N, uuMap b η q ∈ M) {p : E3 × ℝ} (hpN : p ∈ N) :
    ContinuousWithinAt (fun q => PmMap b Pi (uuMap b η q)) N p := by
  refine continuousWithinAt_pi.2 fun i => continuousWithinAt_pi.2 fun j => ?_
  exact continuousWithinAt_inner_b b i.succ (continuousOn_Pi_uuMap b η hPi hNM _ p hpN)

lemma continuousWithinAt_Bmap_comp {N : Set (E3 × ℝ)} {p : E3 × ℝ}
    {P : E3 × ℝ → Fin 3 → Fin 3 → ℝ} (hP : ContinuousWithinAt P N p) :
    ContinuousWithinAt (fun q => Bmap q.1 (P q)) N p := by
  have h : ContinuousWithinAt (fun q => (q.1, P q)) N p :=
    continuous_fst.continuousWithinAt.prodMk hP
  have h3 := continuous_Bmap.continuousWithinAt.comp h (mapsTo_univ _ _)
  exact h3

lemma continuousWithinAt_BtMap {Pi : E4 → E4 → E4} {M : Set E4}
    (hPi : ContinuousOn (fun p : E4 × E4 => Pi p.1 p.2) (M ×ˢ Set.univ))
    {N : Set (E3 × ℝ)} (hNM : ∀ q ∈ N, uuMap b η q ∈ M) {p : E3 × ℝ} (hpN : p ∈ N) :
    ContinuousWithinAt (BtMap b η Pi M) N p := by
  have hBm := continuousWithinAt_Bmap_comp (continuousWithinAt_PmMap b η hPi hNM hpN)
  refine hBm.congr (fun q hq => ?_) ?_
  · rw [BtMap, if_pos (hNM q hq)]
  · rw [BtMap, if_pos (hNM p hpN)]

end Homotopy

/-- **No continuous line field on a thin slab around `F⁻¹(0)`** (the packaged External
theorem 2.7, proved). -/
theorem degree_no_line_field (e : E4) (he : ‖e‖ = 1) (F : E4 → ℝ)
    (hF : ContinuousOn F (sphere 0 1)) (hFe : F e < 0) (hFe' : 0 < F (-e))
    (O : Set E4) (hO : IsOpen O) (hKO : ∀ u ∈ sphere (0 : E4) 1, F u = 0 → u ∈ O) :
    ∃ M ⊆ O ∩ sphere (0 : E4) 1, IsCompact M ∧
      ¬ ∃ Pi : E4 → E4 → E4, ContinuousOn (fun p : E4 × E4 => Pi p.1 p.2) (M ×ˢ Set.univ) ∧
        ∀ u ∈ M, ∃ w : E4, w ≠ 0 ∧ ⟪w, u⟫ = 0 ∧ ⟪w, e⟫ = 0 ∧
          ∀ x, Pi u x = (⟪w, x⟫ / ⟪w, w⟫) • w := by
  obtain ⟨b, hb0⟩ := exists_basis_first he
  -- a positive lower bound for `|F|` off `O`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ u ∈ sphere (0 : E4) 1, u ∉ O → δ ≤ |F u| := by
    by_cases hne : (sphere (0 : E4) 1 \ O).Nonempty
    · have hc : IsCompact (sphere (0 : E4) 1 \ O) := (isCompact_sphere 0 1).diff hO
      obtain ⟨u₀, hu₀, hmin⟩ := hc.exists_isMinOn hne
        (continuous_abs.comp_continuousOn (hF.mono diff_subset))
      exact ⟨|F u₀|, abs_pos.2 fun h => hu₀.2 (hKO u₀ hu₀.1 h), fun u hu huO => hmin ⟨hu, huO⟩⟩
    · exact ⟨1, one_pos, fun u hu huO => absurd ⟨u, hu, huO⟩ hne⟩
  obtain ⟨ε, hε0, hεδ, hεe⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ / 2 ∧ ε ≤ -F e / 2 :=
    ⟨min (δ / 2) (-F e / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  let M : Set E4 := {u | u ∈ sphere (0 : E4) 1 ∧ -ε ≤ F u ∧ F u ≤ 0}
  refine ⟨M, fun u hu => ⟨?_, hu.1⟩, ?_, ?_⟩
  · by_contra huO
    have h1 := hδ u hu.1 huO
    have : |F u| ≤ ε := abs_le.2 ⟨hu.2.1, by linarith [hu.2.2]⟩
    linarith
  · have hcl : IsClosed M := by
      have := hF.preimage_isClosed_of_isClosed isClosed_sphere (isClosed_Icc (a := -ε) (b := 0))
      convert this using 1
      rfl
    exact (isCompact_sphere 0 1).of_isClosed_subset hcl fun u hu => hu.1
  rintro ⟨Pi, hPi, hw⟩
  -- caps around `±e`
  have he1 : e ∈ sphere (0 : E4) 1 := by simpa using he
  have he2 : -e ∈ sphere (0 : E4) 1 := by simpa using he
  obtain ⟨r₁, hr₁, hr₁F⟩ := Metric.continuousWithinAt_iff.1 (hF e he1) (-F e / 2) (by linarith)
  obtain ⟨r₂, hr₂, hr₂F⟩ := Metric.continuousWithinAt_iff.1 (hF (-e) he2) (F (-e) / 2)
    (by linarith)
  obtain ⟨η, hη0, hη1, hηr₁, hηr₂⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ η ≤ r₁ ^ 2 / 4 ∧
      η ≤ r₂ ^ 2 / 4 :=
    ⟨min (1 / 2) (min (r₁ ^ 2 / 4) (r₂ ^ 2 / 4)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hη1' : η < 1 := by linarith
  have hcap1 : ∀ u ∈ sphere (0 : E4) 1, 1 - η ≤ ⟪e, u⟫ → F u < -ε := by
    intro u hu hue
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hd : dist u e < r₁ := by
      have h2 : dist u e ^ 2 = 2 - 2 * ⟪e, u⟫ := by
        rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
          inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu1, he,
          real_inner_comm u e]
        ring
      have : dist u e ^ 2 < r₁ ^ 2 := by rw [h2]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hr₁.le this
    have := hr₁F hu hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hcap2 : ∀ u ∈ sphere (0 : E4) 1, ⟪e, u⟫ ≤ -(1 - η) → 0 < F u := by
    intro u hu hue
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hd : dist u (-e) < r₂ := by
      have h2 : dist u (-e) ^ 2 = 2 + 2 * ⟪e, u⟫ := by
        rw [dist_eq_norm, sub_neg_eq_add, ← real_inner_self_eq_norm_sq, inner_add_left,
          inner_add_right, inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          hu1, he, real_inner_comm u e]
        ring
      have : dist u (-e) ^ 2 < r₂ ^ 2 := by rw [h2]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hr₂.le this
    have := hr₂F hu hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  -- the homotopy
  let D : Set (E3 × ℝ) := sphere (0 : E3) 1 ×ˢ Icc (0 : ℝ) 1
  let H := HMap b η Pi M F ε
  have huu_sph : ∀ p ∈ D, uuMap b η p ∈ sphere (0 : E4) 1 := fun p hp =>
    uuMap_mem_sphere b hη0 hη1' hp
  have huu_e : ∀ p : E3 × ℝ, ⟪e, uuMap b η p⟫ = tau η p.2 := fun p => by
    rw [← hb0]; exact (inner_b_emb b _ _).1
  have hFuu : ContinuousOn (fun p => F (uuMap b η p)) D :=
    hF.comp (continuous_uuMap b η).continuousOn fun p hp => huu_sph p hp
  have hnotM : ∀ p ∈ D, uuMap b η p ∉ M →
      clampσ ε (F (uuMap b η p)) = 0 ∨ clampσ ε (F (uuMap b η p)) = 1 := by
    intro p hp hM
    have hs := huu_sph p hp
    by_cases h0 : 0 ≤ F (uuMap b η p)
    · left; exact clampσ_of_nonneg hε0 h0
    · right
      refine clampσ_of_le hε0 ?_
      by_contra h1
      exact hM ⟨hs, by linarith, by linarith⟩
  have hqdir1 : ∀ p ∈ D, ‖qdir p.1‖ = 1 := fun p hp =>
    norm_qdir (by simpa using ne_of_mem_sphere hp.1 one_ne_zero)
  -- the homotopy is unit-valued
  have hH1 : ∀ v ∈ sphere (0 : E3) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖H (v, s)‖ = 1 := by
    intro v hv s hs
    have hp : (v, s) ∈ D := ⟨hv, hs⟩
    by_cases hM : uuMap b η (v, s) ∈ M
    · obtain ⟨hB1, hBq⟩ := BtMap_props b hb0 hη0 hη1' hw hp hM
      have hsq2 : ‖H (v, s)‖ ^ 2 = 1 := by
        simp only [H, HMap]
        rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
          real_inner_comm, hBq, hqdir1 _ hp, hB1]
        simp only [Real.norm_eq_abs, conj_trivial, mul_zero, mul_one, add_zero, sq_abs]
        exact Real.cos_sq_add_sin_sq _
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by norm_num : (2:ℕ) ≠ 0)).1
        (by rw [hsq2]; norm_num)
    · have hBt0 : BtMap b η Pi M (v, s) = 0 := by simp [BtMap, if_neg hM]
      simp only [H, HMap, hBt0, smul_zero, add_zero, norm_smul, hqdir1 _ hp, mul_one,
        Real.norm_eq_abs]
      rcases hnotM _ hp hM with h | h <;> rw [h] <;> simp
  -- end conditions
  have h0 : ∀ v ∈ sphere (0 : E3) 1, H (v, 0) = qdir v := by
    intro v hv
    have hp : (v, (0 : ℝ)) ∈ D := ⟨hv, by simp⟩
    have hpos : 0 < F (uuMap b η (v, 0)) :=
      hcap2 _ (huu_sph _ hp) (by rw [huu_e]; simp [tau])
    simp only [H, HMap, clampσ_of_nonneg hε0 hpos.le]
    simp
  have h1 : ∀ v ∈ sphere (0 : E3) 1, H (v, 1) = -qdir v := by
    intro v hv
    have hp : (v, (1 : ℝ)) ∈ D := ⟨hv, by simp⟩
    have hneg : F (uuMap b η (v, 1)) < -ε :=
      hcap1 _ (huu_sph _ hp) (by rw [huu_e]; simp only [tau]; norm_num)
    simp only [H, HMap, clampσ_of_le hε0 hneg.le]
    simp
  -- continuity
  have hHc : ContinuousOn H D := by
    intro p hp
    have hσc : ContinuousWithinAt (fun p => clampσ ε (F (uuMap b η p))) D p :=
      (continuous_clampσ ε).continuousAt.comp_continuousWithinAt (hFuu p hp)
    have hq : ContinuousWithinAt (fun p : E3 × ℝ => qdir p.1) D p := by
      have hp0 : p.1 ≠ 0 := by simpa using ne_of_mem_sphere hp.1 one_ne_zero
      exact ((contDiffAt_qdir hp0 (n := 0)).continuousAt.comp
        continuous_fst.continuousAt).continuousWithinAt
    have hcos : ContinuousWithinAt
        (fun p => Real.cos (π * clampσ ε (F (uuMap b η p))) • qdir p.1) D p :=
      ((Real.continuous_cos.continuousAt.comp_continuousWithinAt
        (continuousWithinAt_const.mul hσc))).smul hq
    have hsin : ContinuousWithinAt
        (fun p => Real.sin (π * clampσ ε (F (uuMap b η p))) • BtMap b η Pi M p) D p := by
      by_cases hin : -ε < F (uuMap b η p) ∧ F (uuMap b η p) < 0
      · have hNnhds : (fun p => F (uuMap b η p)) ⁻¹' Ioo (-ε) 0 ∈ 𝓝[D] p :=
          (hFuu p hp).preimage_mem_nhdsWithin (Ioo_mem_nhds hin.1 hin.2)
        rw [← continuousWithinAt_inter' hNnhds]
        have hNM : ∀ q ∈ D ∩ (fun p => F (uuMap b η p)) ⁻¹' Ioo (-ε) 0, uuMap b η q ∈ M :=
          fun q hq => ⟨huu_sph q hq.1, hq.2.1.le, hq.2.2.le⟩
        have hBtN := continuousWithinAt_BtMap b η hPi hNM (p := p) ⟨hp, hin⟩
        exact ((Real.continuous_sin.continuousAt.comp_continuousWithinAt
          (continuousWithinAt_const.mul (hσc.mono inter_subset_left)))).smul hBtN
      · have hσ01 : clampσ ε (F (uuMap b η p)) = 0 ∨ clampσ ε (F (uuMap b η p)) = 1 := by
          by_cases h0 : 0 ≤ F (uuMap b η p)
          · left; exact clampσ_of_nonneg hε0 h0
          · right
            refine clampσ_of_le hε0 ?_
            by_contra h1
            exact hin ⟨by linarith, by linarith⟩
        have hsin0 : Real.sin (π * clampσ ε (F (uuMap b η p))) = 0 := by
          rcases hσ01 with h | h <;> rw [h] <;> simp
        have hval : (fun q => Real.sin (π * clampσ ε (F (uuMap b η q))) • BtMap b η Pi M q) p
            = 0 := by simp only [hsin0, zero_smul]
        unfold ContinuousWithinAt
        rw [hval]
        have hsc : Tendsto (fun q => |Real.sin (π * clampσ ε (F (uuMap b η q)))|) (𝓝[D] p)
            (𝓝 0) := by
          have hπσ : ContinuousWithinAt (fun q => π * clampσ ε (F (uuMap b η q))) D p :=
            (continuous_id.const_mul π).continuousAt.comp_continuousWithinAt hσc
          have := (continuous_abs.continuousAt.comp_continuousWithinAt
            (Real.continuous_sin.continuousAt.comp_continuousWithinAt hπσ))
          unfold ContinuousWithinAt at this
          simpa [Function.comp_def, hsin0] using this
        refine squeeze_zero_norm' ?_ hsc
        filter_upwards [self_mem_nhdsWithin] with q hq
        rw [norm_smul, Real.norm_eq_abs]
        calc |Real.sin (π * clampσ ε (F (uuMap b η q)))| * ‖BtMap b η Pi M q‖
            ≤ |Real.sin (π * clampσ ε (F (uuMap b η q)))| * 1 :=
              mul_le_mul_of_nonneg_left (BtMap_norm_le b hb0 hη0 hη1' hw hq) (abs_nonneg _)
          _ = _ := mul_one _
    exact hcos.add hsin
  exact no_continuous_homotopy H hHc hH1 h0 h1

end FourthRatio.Degree

end

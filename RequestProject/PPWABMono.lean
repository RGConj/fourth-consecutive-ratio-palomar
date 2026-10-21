module

public import RequestProject.PPWABConstruct

/-!
# Monotonicity of the Ashbaugh–Benguria weights

From the Bessel function lemmas (`ABBesselLemmas`, proved as `ab_bessel`): for the profile `abProfile`, `G(s) = s h(s)²` is
nondecreasing and `B(s) = N h² + 4 s h h' + 4 s² h'²` is nonincreasing on `[0, ∞)`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

noncomputable section

namespace FourthRatio

variable {N : ℕ} {a η : ℝ}

/-- `w(t) = t h₁(R² t²)` for `|t| < 1`. -/
lemma abW_eq (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    abW ((N : ℝ) / 2 - 1) t = t * abH1 N a η (annR N a ^ 2 * t ^ 2) := by
  have e : (N : ℝ) / 2 - 1 + 1 = (N : ℝ) / 2 := by ring
  have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  have hR2 := pow_pos (annR_pos hN ha) 2
  have hs0 : 0 ≤ annR N a ^ 2 * t ^ 2 := by positivity
  have hs : annR N a ^ 2 * t ^ 2 < annR N a ^ 2 := by nlinarith
  rw [abH1_eq_div hN ha hη hη0 hs0 hs, abW, e, abQ, abA,
    besselSeries_scale ((N : ℝ) / 2) (CN N * a), besselSeries_scale ((N : ℝ) / 2 - 1) a,
    ← mul_assoc, ← mul_assoc, CN_mul_annR_sq hN ha, a_mul_annR_sq ha]
  ring

lemma sqrt_div_mem (hR : 0 < annR N a) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < annR N a ^ 2) :
    Real.sqrt s / annR N a ∈ Ico 0 1 :=
  ⟨div_nonneg (Real.sqrt_nonneg s) hR.le, by rw [div_lt_one hR, Real.sqrt_lt' hR]; exact hs⟩

lemma sq_mul_sqrt_div (hR : 0 < annR N a) {s : ℝ} (hs0 : 0 ≤ s) :
    annR N a ^ 2 * (Real.sqrt s / annR N a) ^ 2 = s := by
  rw [div_pow, Real.sq_sqrt hs0]; field_simp

lemma sqrt_div_mono (hR : 0 < annR N a) {x y : ℝ} (hxy : x ≤ y) :
    Real.sqrt x / annR N a ≤ Real.sqrt y / annR N a :=
  div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hxy) hR.le

/-- `G` is nondecreasing on `[0, ∞)`. -/
theorem abProfile_Gw_mono (hN : 2 ≤ N) (hAB : ABBesselLemmas ((N : ℝ) / 2 - 1)) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) :
    MonotoneOn (abProfile hN ha hη0 hη).Gw (Ici 0) := by
  set p := abProfile hN ha hη0 hη
  set R := annR N a with hRdef
  have hR : 0 < R := annR_pos hN ha
  have hW := hAB.1
  have hIoo : ∀ {t : ℝ}, t ∈ Ico 0 1 → t ∈ Ioo (-1) 1 := fun ht => ⟨by linarith [ht.1], ht.2⟩
  have hG : ∀ s, 0 ≤ s → s < R ^ 2 →
      p.Gw s = R ^ 2 * abW ((N : ℝ) / 2 - 1) (Real.sqrt s / R) ^ 2 := by
    intro s hs0 hs
    rw [abW_eq hN ha hη0 hη (hIoo (sqrt_div_mem hR hs0 hs)), sq_mul_sqrt_div hR hs0,
      ABProfile.Gw, p.prof_of_le hs.le]
    show s * abH1 N a η s ^ 2 = _
    rw [mul_pow, div_pow, Real.sq_sqrt hs0, ← hRdef]; field_simp
  have hWnn : ∀ s, 0 ≤ s → s < R ^ 2 → 0 ≤ abW ((N : ℝ) / 2 - 1) (Real.sqrt s / R) := by
    intro s hs0 hs
    rw [abW_eq hN ha hη0 hη (hIoo (sqrt_div_mem hR hs0 hs)), sq_mul_sqrt_div hR hs0]
    exact mul_nonneg (sqrt_div_mem hR hs0 hs).1 (abH1_pos hN ha hη hη0 hs0 hs.le).le
  have hIco : MonotoneOn p.Gw (Ioo 0 (R ^ 2)) := by
    intro x hx y hy hxy
    rw [hG x hx.1.le hx.2, hG y hy.1.le hy.2]
    have h1 := hW (sqrt_div_mem hR hx.1.le hx.2) (sqrt_div_mem hR hy.1.le hy.2)
      (sqrt_div_mono hR hxy)
    have h0 := hWnn x hx.1.le hx.2
    gcongr
  have hIcc := monotoneOn_Icc_of_Ioo p.continuous_Gw hIco
  intro x hx y hy hxy
  rcases le_or_gt y (R ^ 2) with h | h
  · exact hIcc ⟨hx, hxy.trans h⟩ ⟨hy, h⟩ hxy
  · rw [p.Gw_tail hR h.le]
    rcases le_or_gt x (R ^ 2) with h' | h'
    · rw [← p.Gw_tail hR le_rfl]
      exact hIcc ⟨hx, h'⟩ ⟨sq_nonneg _, le_rfl⟩ h'
    · rw [p.Gw_tail hR h'.le]

/-- The smooth expression of `B` on `s < R²`. -/
def abBs (N : ℕ) (a η s : ℝ) : ℝ :=
  (N : ℝ) * abH1 N a η s ^ 2 + 4 * s * abH1 N a η s * deriv (abH1 N a η) s +
    4 * s ^ 2 * deriv (abH1 N a η) s ^ 2

lemma continuous_abBs (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η) : Continuous (abBs N a η) := by
  have h1 := (contDiff_abH1 hN ha hη0).continuous
  have h2 := (contDiff_abH1 hN ha hη0).continuous_deriv (by simp)
  unfold abBs
  fun_prop

lemma abProfile_Bw_eq (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) {s : ℝ} (hs : s < annR N a ^ 2) :
    (abProfile hN ha hη0 hη).Bw s = abBs N a η s := by
  unfold ABProfile.Bw ABProfile.dprof
  rw [(abProfile hN ha hη0 hη).prof_of_le hs.le, if_pos hs]
  rfl

/-- The derivative of `w`. -/
lemma deriv_abW (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    deriv (abW ((N : ℝ) / 2 - 1)) t =
      abH1 N a η (annR N a ^ 2 * t ^ 2) +
        2 * (annR N a ^ 2 * t ^ 2) * deriv (abH1 N a η) (annR N a ^ 2 * t ^ 2) := by
  have hev : abW ((N : ℝ) / 2 - 1) =ᶠ[𝓝 t] fun u => u * abH1 N a η (annR N a ^ 2 * u ^ 2) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact abW_eq hN ha hη0 hη hu
  have h1 : HasDerivAt (fun u => annR N a ^ 2 * u ^ 2) (annR N a ^ 2 * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (annR N a ^ 2)
  have h2 := (((contDiff_abH1 hN ha hη0).differentiable (by simp)) _).hasDerivAt.comp t h1
  have hd : HasDerivAt (fun u => u * abH1 N a η (annR N a ^ 2 * u ^ 2))
      (1 * abH1 N a η (annR N a ^ 2 * t ^ 2) +
        t * (deriv (abH1 N a η) (annR N a ^ 2 * t ^ 2) * (annR N a ^ 2 * (2 * t)))) t :=
    (hasDerivAt_id t).mul h2
  rw [hev.deriv_eq, hd.deriv]
  ring

/-- `B` is nonincreasing on `[0, ∞)`. -/
theorem abProfile_Bw_anti (hN : 2 ≤ N) (hAB : ABBesselLemmas ((N : ℝ) / 2 - 1)) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) :
    AntitoneOn (abProfile hN ha hη0 hη).Bw (Ici 0) := by
  set p := abProfile hN ha hη0 hη
  set R := annR N a with hRdef
  have hR : 0 < R := annR_pos hN ha
  have hB := hAB.2
  set h := abH1 N a η
  have hform : ∀ s ∈ Ioo 0 (R ^ 2), abBs N a η s =
      deriv (abW ((N : ℝ) / 2 - 1)) (Real.sqrt s / R) ^ 2 +
        (2 * ((N : ℝ) / 2 - 1) + 1) *
          (abW ((N : ℝ) / 2 - 1) (Real.sqrt s / R) / (Real.sqrt s / R)) ^ 2 := by
    intro s hs
    have ht := sqrt_div_mem hR hs.1.le hs.2
    have ht' : Real.sqrt s / R ∈ Ioo (-1) 1 := ⟨by linarith [ht.1], ht.2⟩
    have htne : Real.sqrt s / R ≠ 0 :=
      (div_pos (Real.sqrt_pos.mpr hs.1) hR).ne'
    rw [deriv_abW hN ha hη0 hη ht', abW_eq hN ha hη0 hη ht', sq_mul_sqrt_div hR hs.1.le,
      mul_div_cancel_left₀ _ htne, abBs]
    ring
  have hIoo : AntitoneOn (abBs N a η) (Ioo 0 (R ^ 2)) := by
    intro x hx y hy hxy
    rw [hform x hx, hform y hy]
    have mx := sqrt_div_mem hR hx.1.le hx.2
    have my := sqrt_div_mem hR hy.1.le hy.2
    exact hB ⟨div_pos (Real.sqrt_pos.mpr hx.1) hR, mx.2⟩
      ⟨div_pos (Real.sqrt_pos.mpr hy.1) hR, my.2⟩ (sqrt_div_mono hR hxy)
  have hIcc := antitoneOn_Icc_of_Ioo (continuous_abBs hN ha hη0) hIoo
  -- the value at `R²`
  have hRval : p.Bw (R ^ 2) ≤ abBs N a η (R ^ 2) := by
    rw [p.Bw_tail hR le_rfl]
    have hκ : p.κ = R * h (R ^ 2) := rfl
    rw [hκ, abBs]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have e : ((N : ℝ) - 1) * (R * h (R ^ 2)) ^ 2 / R ^ 2 = ((N : ℝ) - 1) * h (R ^ 2) ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_nonneg (h (R ^ 2) + 2 * R ^ 2 * deriv h (R ^ 2))]
  have hA : AntitoneOn p.Bw (Icc 0 (R ^ 2)) := by
    intro x hx y hy hxy
    rcases hy.2.lt_or_eq with hy' | hy'
    · rw [abProfile_Bw_eq hN ha hη0 hη (lt_of_le_of_lt hxy hy'),
        abProfile_Bw_eq hN ha hη0 hη hy']
      exact hIcc hx hy hxy
    · rcases hx.2.lt_or_eq with hx' | hx'
      · rw [abProfile_Bw_eq hN ha hη0 hη hx', hy']
        exact (hRval.trans (hIcc hx ⟨sq_nonneg _, le_rfl⟩ hx.2))
      · rw [hx', hy']
  have hT : AntitoneOn p.Bw (Ici (R ^ 2)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le (pow_pos hR 2) hx
    rw [p.Bw_tail hR hx, p.Bw_tail hR hy]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (sq_nonneg _)) hx0 hxy
  intro x hx y hy hxy
  rcases le_or_gt y (R ^ 2) with h1 | h1
  · exact hA ⟨hx, hxy.trans h1⟩ ⟨hy, h1⟩ hxy
  · rcases le_or_gt x (R ^ 2) with h2 | h2
    · exact (hT (mem_Ici.mpr le_rfl) (mem_Ici.mpr h1.le) h1.le).trans
        (hA ⟨hx, h2⟩ ⟨sq_nonneg _, le_rfl⟩ h2)
    · exact hT (mem_Ici.mpr h2.le) (mem_Ici.mpr h1.le) hxy

end FourthRatio

end

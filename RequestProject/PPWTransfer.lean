module

public import RequestProject.PPWDeep

/-!
# PPW: transferring mass comparison to radial weights

If no ball `B_r(c)` carries (relatively) more of the mass of `f` than `B_r(0)` carries of `z`,
then `∫ W(|x - c|²) f ≤ ∫ W(|x|²) z` (relatively) for every nonnegative nonincreasing weight
`W`, and the reverse inequality holds for bounded nondecreasing weights (layer-cake
representation).  An equality case gives a support bound.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The mass comparison hypothesis. -/
def MassDominated (f z : RN N → ℝ) (c : RN N) : Prop :=
  ∀ r : ℝ, (∫ x in ball c r, f x) * (∫ x, z x) ≤ (∫ x in ball (0 : RN N) r, z x) * ∫ x, f x

/-- The measure `f · dx`. -/
def densM (f : RN N → ℝ) : Measure (RN N) := volume.withDensity fun x => ENNReal.ofReal (f x)

lemma densM_apply {f : RN N → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) {S : Set (RN N)}
    (hS : MeasurableSet S) : densM f S = ENNReal.ofReal (∫ x in S, f x) := by
  rw [densM, withDensity_apply _ hS,
    ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hf0)]

lemma densM_univ {f : RN N → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    densM f univ = ENNReal.ofReal (∫ x, f x) := by
  rw [densM_apply hf hf0 MeasurableSet.univ, Measure.restrict_univ]

lemma densM_ac (f : RN N → ℝ) : densM f ≪ volume := withDensity_absolutelyContinuous _ _

lemma integral_densM {f : RN N → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (g : RN N → ℝ) : ∫ x, g x ∂(densM f) = ∫ x, g x * f x := by
  have := integral_withDensity_eq_integral_smul₀ (μ := (volume : Measure (RN N)))
    (f := fun x => (f x).toNNReal) hf.aemeasurable.real_toNNReal g
  refine this.trans ?_
  congr 1; funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hf0 x), smul_eq_mul, mul_comm]

/-- The key estimate for one superlevel set of a radial nonincreasing weight. -/
lemma mass_superlevel (hN : 2 ≤ N) {f z : RN N → ℝ} (hf : Integrable f) (hz : Integrable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x) {c : RN N} (hm : MassDominated f z c)
    {W : ℝ → ℝ} (hW : Antitone W) (t : ℝ) :
    densM f {x | t < W (‖x - c‖ ^ 2)} * densM z univ ≤
      densM z {x | t < W (‖x‖ ^ 2)} * densM f univ := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  by_cases hall : ∀ s, t < W s
  · have h1 : {x : RN N | t < W (‖x - c‖ ^ 2)} = univ := eq_univ_of_forall fun x => hall _
    have h2 : {x : RN N | t < W (‖x‖ ^ 2)} = univ := eq_univ_of_forall fun x => hall _
    rw [h1, h2, mul_comm]
  push_neg at hall
  obtain ⟨s0, hs0⟩ := hall
  set T := {s : ℝ | t < W s} with hT
  by_cases hne : T.Nonempty
  swap
  · have : {x : RN N | t < W (‖x - c‖ ^ 2)} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => hne ⟨_, hx⟩
    rw [this, measure_empty, zero_mul]; exact bot_le
  have hbdd : BddAbove T := ⟨s0, fun s hs => by
    by_contra h; push_neg at h
    have := hW h.le; simp only [hT, mem_setOf_eq] at hs; linarith⟩
  set σ := sSup T with hσ
  have hlt : ∀ s, s < σ → s ∈ T := fun s hs => by
    obtain ⟨s', hs'T, hss'⟩ := (lt_csSup_iff hbdd hne).mp hs
    exact lt_of_lt_of_le hs'T (hW hss'.le)
  have hle : ∀ s ∈ T, s ≤ σ := fun s hs => le_csSup hbdd hs
  by_cases hσ0 : σ ≤ 0
  · have hsub : {x : RN N | t < W (‖x - c‖ ^ 2)} ⊆ {c} := fun x hx => by
      have h1 := hle _ hx
      have : ‖x - c‖ ^ 2 ≤ 0 := h1.trans hσ0
      have : ‖x - c‖ = 0 := by nlinarith [norm_nonneg (x - c)]
      simpa [sub_eq_zero] using this
    have h0 : densM f {x : RN N | t < W (‖x - c‖ ^ 2)} = 0 :=
      measure_mono_null hsub (densM_ac f (measure_singleton c))
    rw [h0, zero_mul]; exact bot_le
  push_neg at hσ0
  set r := Real.sqrt σ with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hσ0
  have hrr : r ^ 2 = σ := Real.sq_sqrt hσ0.le
  have hsub1 : {x : RN N | t < W (‖x - c‖ ^ 2)} ⊆ ball c r ∪ sphere c r := fun x hx => by
    have h1 : ‖x - c‖ ^ 2 ≤ r ^ 2 := hrr ▸ hle _ hx
    have h2 : ‖x - c‖ ≤ r := by nlinarith [norm_nonneg (x - c)]
    rcases h2.lt_or_eq with h | h
    · left; simpa [mem_ball, dist_eq_norm] using h
    · right; simpa [mem_sphere, dist_eq_norm] using h
  have hsub2 : ball (0 : RN N) r ⊆ {x : RN N | t < W (‖x‖ ^ 2)} := fun x hx => by
    have h1 : ‖x‖ < r := by simpa [mem_ball, dist_zero_right] using hx
    have : ‖x‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg x]
    exact hlt _ (hrr ▸ this)
  have hsph : densM f (sphere c r) = 0 := densM_ac f (Measure.addHaar_sphere volume c r)
  have hA : densM f {x : RN N | t < W (‖x - c‖ ^ 2)} ≤ densM f (ball c r) := by
    calc _ ≤ densM f (ball c r ∪ sphere c r) := measure_mono hsub1
      _ ≤ densM f (ball c r) + densM f (sphere c r) := measure_union_le _ _
      _ = _ := by rw [hsph, add_zero]
  have hB : densM z (ball (0 : RN N) r) ≤ densM z {x : RN N | t < W (‖x‖ ^ 2)} :=
    measure_mono hsub2
  have hC : densM f (ball c r) * densM z univ ≤ densM z (ball (0 : RN N) r) * densM f univ := by
    rw [densM_apply hf hf0 measurableSet_ball, densM_apply hz hz0 measurableSet_ball,
      densM_univ hf hf0, densM_univ hz hz0,
      ← ENNReal.ofReal_mul (setIntegral_nonneg measurableSet_ball fun x _ => hf0 x),
      ← ENNReal.ofReal_mul (setIntegral_nonneg measurableSet_ball fun x _ => hz0 x)]
    exact ENNReal.ofReal_le_ofReal (hm r)
  calc _ ≤ densM f (ball c r) * densM z univ := mul_le_mul_left hA _
    _ ≤ densM z (ball (0 : RN N) r) * densM f univ := hC
    _ ≤ _ := mul_le_mul_left hB _

/-- Radial weights are measurable. -/
lemma measurable_radial_anti {W : ℝ → ℝ} (hW : Antitone W) (c : RN N) :
    Measurable fun x : RN N => W (‖x - c‖ ^ 2) :=
  hW.measurable.comp ((continuous_id.sub continuous_const).norm.pow 2).measurable

/-- The integral of a radial nonincreasing weight against `f`, by the layer-cake formula. -/
lemma integral_radial_eq_lintegral {f : RN N → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    {W : ℝ → ℝ} (hW : Antitone W) (hW0 : ∀ s, 0 ≤ W s) (c : RN N) :
    ∫ x, W (‖x - c‖ ^ 2) * f x =
      (∫⁻ t in Ioi 0, densM f {x | t < W (‖x - c‖ ^ 2)}).toReal := by
  rw [← integral_densM hf hf0, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => hW0 _)
    (measurable_radial_anti hW c).aestronglyMeasurable,
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall fun x => hW0 _)
    (measurable_radial_anti hW c).aemeasurable]

lemma lintegral_superlevel_lt_top {f : RN N → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    {W : ℝ → ℝ} (hW : Antitone W) (hW0 : ∀ s, 0 ≤ W s) (c : RN N) :
    (∫⁻ t in Ioi 0, densM f {x | t < W (‖x - c‖ ^ 2)}) < ⊤ := by
  rw [← lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall fun x => hW0 _)
    (measurable_radial_anti hW c).aemeasurable]
  calc (∫⁻ x, ENNReal.ofReal (W (‖x - c‖ ^ 2)) ∂densM f)
      ≤ ∫⁻ _, ENNReal.ofReal (W 0) ∂densM f :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hW (sq_nonneg _))
    _ = ENNReal.ofReal (W 0) * densM f univ := lintegral_const _
    _ < ⊤ := by
        rw [densM_univ hf hf0]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **Transfer to nonincreasing weights.** -/
theorem transfer_anti (hN : 2 ≤ N) {f z : RN N → ℝ} (hf : Integrable f) (hz : Integrable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x) {c : RN N} (hm : MassDominated f z c)
    {W : ℝ → ℝ} (hW : Antitone W) (hW0 : ∀ s, 0 ≤ W s) :
    (∫ x, W (‖x - c‖ ^ 2) * f x) * (∫ x, z x) ≤ (∫ x, W (‖x‖ ^ 2) * z x) * ∫ x, f x := by
  have hz' : (∫ x, W (‖x‖ ^ 2) * z x) = ∫ x, W (‖x - 0‖ ^ 2) * z x := by simp
  rw [hz', integral_radial_eq_lintegral hf hf0 hW hW0 c,
    integral_radial_eq_lintegral hz hz0 hW hW0 0]
  have hZ : (∫ x, z x) = (densM z univ).toReal := by
    rw [densM_univ hz hz0, ENNReal.toReal_ofReal (integral_nonneg hz0)]
  have hF : (∫ x, f x) = (densM f univ).toReal := by
    rw [densM_univ hf hf0, ENNReal.toReal_ofReal (integral_nonneg hf0)]
  rw [hZ, hF, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  have hfin : (∫⁻ t in Ioi 0, densM z {x | t < W (‖x - 0‖ ^ 2)}) * densM f univ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (lintegral_superlevel_lt_top hz hz0 hW hW0 0).ne ?_
    rw [densM_univ hf hf0]; exact ENNReal.ofReal_ne_top
  refine ENNReal.toReal_mono hfin ?_
  have hmeas : ∀ (g : RN N → ℝ) (μ : Measure (RN N)),
      AEMeasurable (fun t : ℝ => μ {x | t < g x}) (volume.restrict (Ioi 0)) := by
    intro g μ
    have hanti : Antitone (fun t : ℝ => μ {x | t < g x}) := by
      intro s t hst
      apply measure_mono
      intro x hx
      have hxt : t < g x := hx
      exact lt_of_le_of_lt hst hxt
    exact hanti.measurable.aemeasurable
  rw [← lintegral_mul_const'' _ (hmeas (fun x => W (‖x - c‖ ^ 2)) (densM f)),
    ← lintegral_mul_const'' _ (hmeas (fun x => W (‖x - 0‖ ^ 2)) (densM z))]
  refine lintegral_mono fun t => ?_
  have := mass_superlevel hN hf hz hf0 hz0 hm hW t
  simpa using this

lemma integrable_radial_mul {f : RN N → ℝ} (hf : Integrable f) {W : ℝ → ℝ}
    (hWm : Measurable W) {M : ℝ} (hM : ∀ s, 0 ≤ s → |W s| ≤ M) (c : RN N) :
    Integrable fun x => W (‖x - c‖ ^ 2) * f x :=
  hf.bdd_mul (c := M)
    (hWm.comp ((continuous_id.sub continuous_const).norm.pow 2).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM _ (sq_nonneg _))

lemma integrable_radial_anti {f : RN N → ℝ} (hf : Integrable f) {W : ℝ → ℝ} (hW : Antitone W)
    (hW0 : ∀ s, 0 ≤ W s) (c : RN N) : Integrable fun x => W (‖x - c‖ ^ 2) * f x :=
  integrable_radial_mul hf hW.measurable (M := W 0)
    (fun s hs => by rw [abs_of_nonneg (hW0 s)]; exact hW hs) c

/-- **Transfer to nondecreasing bounded weights.** -/
theorem transfer_mono (hN : 2 ≤ N) {f z : RN N → ℝ} (hf : Integrable f) (hz : Integrable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x) {c : RN N} (hm : MassDominated f z c)
    {V : ℝ → ℝ} (hV : Monotone V) {K : ℝ} (hK : ∀ s, V s ≤ K) :
    (∫ x, V (‖x‖ ^ 2) * z x) * (∫ x, f x) ≤ (∫ x, V (‖x - c‖ ^ 2) * f x) * ∫ x, z x := by
  set W : ℝ → ℝ := fun s => K - V s with hW_def
  have hW : Antitone W := fun a b hab => sub_le_sub_left (hV hab) K
  have hW0 : ∀ s, 0 ≤ W s := fun s => sub_nonneg.mpr (hK s)
  have h := transfer_anti hN hf hz hf0 hz0 hm hW hW0
  have hb : ∀ s, 0 ≤ s → |V s| ≤ max |K| |V 0| := fun s hs => by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have := hV hs
      linarith [neg_abs_le (V 0), le_max_right |K| |V 0|]
    · linarith [hK s, le_abs_self K, le_max_left |K| |V 0|]
  have i1 := integrable_radial_mul hf hV.measurable hb c
  have i0 := integrable_radial_mul hz hV.measurable hb 0
  have e1 : (∫ x, W (‖x - c‖ ^ 2) * f x) = K * (∫ x, f x) - ∫ x, V (‖x - c‖ ^ 2) * f x := by
    simp only [W, sub_mul]
    rw [integral_sub (hf.const_mul K) i1, integral_const_mul]
  have e0 : (∫ x, W (‖x‖ ^ 2) * z x) = K * (∫ x, z x) - ∫ x, V (‖x‖ ^ 2) * z x := by
    simp only [W, sub_mul]
    rw [integral_sub (hz.const_mul K) (by simpa using i0), integral_const_mul]
  rw [e1, e0] at h
  nlinarith [h]

/-- **Equality case.**  Equality for a weight that is strictly decreasing on `[R², ∞)`, when `z`
vanishes outside `B_R(0)`, forces `f` to vanish outside the closed ball `B̄_R(c)`. -/
theorem transfer_eq_support (hN : 2 ≤ N) {f z : RN N → ℝ} (hf : Integrable f)
    (hz : Integrable z) (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x) {c : RN N}
    (hm : MassDominated f z c) {R : ℝ} (hzR : ∀ x, R ≤ ‖x‖ → z x = 0) (hZ : 0 < ∫ x, z x)
    {W : ℝ → ℝ} (hW : Antitone W) (hW0 : ∀ s, 0 ≤ W s)
    (hstrict : ∀ s s', R ^ 2 ≤ s → s < s' → W s' < W s)
    (heq : (∫ x, W (‖x - c‖ ^ 2) * f x) * (∫ x, z x) = (∫ x, W (‖x‖ ^ 2) * z x) * ∫ x, f x) :
    ∀ᵐ x, R < ‖x - c‖ → f x = 0 := by
  have hR : 0 < R := by
    by_contra hR; push_neg at hR
    have : ∀ x, z x = 0 := fun x => hzR x (hR.trans (norm_nonneg x))
    simp [this] at hZ
  -- for every `ρ > R`, `f` vanishes outside `B_ρ(c)`
  have key : ∀ ρ, R < ρ → ∀ᵐ x, x ∉ ball c ρ → f x = 0 := by
    intro ρ hρ
    set R' := (R + ρ) / 2 with hR'
    have hRR' : R < R' := by linarith
    have hR'ρ : R' < ρ := by linarith
    set t0 := W (R' ^ 2)
    set t1 := W (ρ ^ 2)
    have ht : t1 < t0 := hstrict _ _ (by nlinarith) (by nlinarith)
    set Wb : ℝ → ℝ := fun s => min (max (W s - t1) 0) (t0 - t1) with hWb_def
    have hWb : Antitone Wb := fun a b hab =>
      min_le_min (max_le_max (sub_le_sub_right (hW hab) _) le_rfl) le_rfl
    have hWb0 : ∀ s, 0 ≤ Wb s := fun s => le_min (le_max_right _ _) (by linarith)
    set W2 : ℝ → ℝ := fun s => W s - Wb s with hW2_def
    have hg : ∀ y y' : ℝ, y ≤ y' →
        y - min (max (y - t1) 0) (t0 - t1) ≤ y' - min (max (y' - t1) 0) (t0 - t1) := by
      intro y y' hyy
      simp only [min_def, max_def]
      split_ifs <;> linarith
    have hW2 : Antitone W2 := fun a b hab => hg _ _ (hW hab)
    have hW20 : ∀ s, 0 ≤ W2 s := fun s => by
      have h1 : Wb s ≤ max (W s - t1) 0 := min_le_left _ _
      have h2 : 0 ≤ t1 := hW0 _
      have h3 := hW0 s
      simp only [W2]
      rcases le_total (W s - t1) 0 with h | h
      · rw [max_eq_right h] at h1; linarith
      · rw [max_eq_left h] at h1; linarith
    have hA2 := transfer_anti hN hf hz hf0 hz0 hm hW2 hW20
    have iWb := integrable_radial_anti hf hWb hWb0 c
    have iW2 := integrable_radial_anti hf hW2 hW20 c
    have iWb0 := integrable_radial_anti hz hWb hWb0 0
    have iW20 := integrable_radial_anti hz hW2 hW20 0
    have hsplit1 : (∫ x, W (‖x - c‖ ^ 2) * f x) =
        (∫ x, W2 (‖x - c‖ ^ 2) * f x) + ∫ x, Wb (‖x - c‖ ^ 2) * f x := by
      rw [← integral_add iW2 iWb]; congr 1; funext x; simp only [W2]; ring
    have hsplit0 : (∫ x, W (‖x‖ ^ 2) * z x) =
        (∫ x, W2 (‖x‖ ^ 2) * z x) + ∫ x, Wb (‖x‖ ^ 2) * z x := by
      rw [← integral_add (by simpa using iW20) (by simpa using iWb0)]
      congr 1; funext x; simp only [W2]; ring
    have hb : (∫ x, Wb (‖x‖ ^ 2) * z x) * (∫ x, f x) ≤
        (∫ x, Wb (‖x - c‖ ^ 2) * f x) * ∫ x, z x := by
      rw [hsplit1, hsplit0] at heq
      nlinarith [heq, hA2]
    have hz1 : (∫ x, Wb (‖x‖ ^ 2) * z x) = (t0 - t1) * ∫ x, z x := by
      rw [← integral_const_mul]; congr 1; funext x
      by_cases hx : R ≤ ‖x‖
      · rw [hzR x hx]; ring
      · push_neg at hx
        have h1 : t0 ≤ W (‖x‖ ^ 2) := hW (by nlinarith [norm_nonneg x])
        have : Wb (‖x‖ ^ 2) = t0 - t1 := by
          simp only [Wb]
          rw [max_eq_left (by linarith), min_eq_right (by linarith)]
        rw [this]
    have hf1 : (∫ x, Wb (‖x - c‖ ^ 2) * f x) ≤ (t0 - t1) * ∫ x in ball c ρ, f x := by
      rw [← integral_indicator measurableSet_ball, ← integral_const_mul]
      refine integral_mono iWb ((hf.indicator measurableSet_ball).const_mul _) fun x => ?_
      by_cases hx : x ∈ ball c ρ
      · rw [indicator_of_mem hx]
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (hf0 x)
      · rw [indicator_of_notMem hx, mul_zero]
        have hx' : ρ ≤ ‖x - c‖ := by simpa [mem_ball, dist_eq_norm] using hx
        have h1 : W (‖x - c‖ ^ 2) ≤ t1 := hW (by nlinarith)
        have : Wb (‖x - c‖ ^ 2) = 0 := by
          simp only [Wb]; rw [max_eq_right (by linarith), min_eq_left (by linarith)]
        rw [this, zero_mul]
    rw [hz1] at hb
    have hF : (∫ x, f x) ≤ ∫ x in ball c ρ, f x := by
      have h1 : (t0 - t1) * (∫ x, z x) * (∫ x, f x) ≤
          (t0 - t1) * (∫ x, z x) * ∫ x in ball c ρ, f x := by
        calc _ = (t0 - t1) * (∫ x, z x) * (∫ x, f x) := rfl
          _ ≤ (∫ x, Wb (‖x - c‖ ^ 2) * f x) * ∫ x, z x := by linarith
          _ ≤ ((t0 - t1) * ∫ x in ball c ρ, f x) * ∫ x, z x :=
              mul_le_mul_of_nonneg_right hf1 hZ.le
          _ = _ := by ring
      exact le_of_mul_le_mul_left h1 (mul_pos (by linarith) hZ)
    have hcompl : (∫ x in (ball c ρ)ᶜ, f x) = 0 := by
      have := integral_add_compl measurableSet_ball hf (s := ball c ρ)
      have h0 : 0 ≤ ∫ x in (ball c ρ)ᶜ, f x := setIntegral_nonneg measurableSet_ball.compl
        fun x _ => hf0 x
      linarith
    have := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.integrableOn).mp hcompl
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball.compl] at this
    exact this
  have hall : ∀ᵐ x, ∀ n : ℕ, x ∉ ball c (R + 1 / ((n : ℝ) + 1)) → f x = 0 :=
    ae_all_iff.mpr fun n => key _ (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                      linarith)
  filter_upwards [hall] with x hx hxR
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxR)
  refine hx n ?_
  simp only [mem_ball, dist_eq_norm, not_lt]
  linarith

end FourthRatio

end

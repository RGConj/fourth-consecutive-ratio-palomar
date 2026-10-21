module

public import RequestProject.SobolevTools

/-!
# Sobolev chain rule for truncations in the model of `H₀¹(D)`

* `Gpair n p`: the composition of a pair with the smooth truncation `Gfun n`;
* `posPart_mem_H`: the Sobolev chain rule `v ∈ H_D ⟹ v₊ ∈ H_D` (with `∇v₊ = 1_{v>0} ∇v`);
* `grad_eq_zero_of_eq_zero`: the weak gradient vanishes a.e. on the zero set (Stampacchia);
* `exists_subseq_posPart_tendsto`: sequential continuity of `v ↦ v₊` in `H_D` (along a
  subsequence).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### A multiplier convergence lemma -/

/-- If `g_k → g₀` in `L²`, the scalar multipliers `a_k` are uniformly bounded and
`a_k g₀ → b g₀` pointwise a.e., then `a_k g_k → b g₀` in `L²`. -/
lemma L2v_mul_tendsto {a : ℕ → RN N → ℝ} {b : RN N → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ k, AEStronglyMeasurable (a k) volume) (hb : AEStronglyMeasurable b volume)
    (haC : ∀ k x, |a k x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    {g : ℕ → L2v N} {g0 : L2v N} (hg : Tendsto g atTop (𝓝 g0))
    {u : ℕ → L2v N} {w : L2v N}
    (hu : ∀ k, (u k : RN N → RN N) =ᵐ[volume] fun x => a k x • (g k : RN N → RN N) x)
    (hw : (w : RN N → RN N) =ᵐ[volume] fun x => b x • (g0 : RN N → RN N) x)
    (hlim : ∀ᵐ x, Tendsto (fun k => a k x • (g0 : RN N → RN N) x) atTop
      (𝓝 (b x • (g0 : RN N → RN N) x))) :
    Tendsto u atTop (𝓝 w) := by
  have hab : ∀ k x, ‖(a k x - b x) • (g0 : RN N → RN N) x‖ ≤
      2 * C * ‖(g0 : RN N → RN N) x‖ := fun k x => by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ((abs_sub _ _).trans ?_) (norm_nonneg _)
    linarith [haC k x, hbC x]
  have hr : ∀ k, MemLp (fun x => (a k x - b x) • (g0 : RN N → RN N) x) 2 volume := fun k =>
    (Lp.memLp g0).of_le_mul (c := 2 * C) (((ha k).sub hb).smul (Lp.aestronglyMeasurable g0))
      (Eventually.of_forall fun x => hab k x)
  set r : ℕ → L2v N := fun k => MemLp.toLp _ (hr k) with hr_def
  have hr0 : Tendsto r atTop (𝓝 0) := by
    refine Lp2_tendsto_of_dominated (g := fun x => 2 * C * ‖(g0 : RN N → RN N) x‖)
      ((Lp.memLp g0).norm.const_mul _) (fun k => ?_) ?_
    · filter_upwards [MemLp.coeFn_toLp (hr k)] with x hx
      rw [hx]; exact hab k x
    · filter_upwards [hlim, Lp.coeFn_zero (RN N) 2 (volume : Measure (RN N)),
        ae_all_iff.mpr fun k => MemLp.coeFn_toLp (hr k)] with x hx h0 hk
      rw [h0]
      have h' := hx.sub_const (b x • (g0 : RN N → RN N) x)
      rw [sub_self] at h'
      refine h'.congr fun k => ?_
      rw [hr_def]
      exact ((hk k).trans (sub_smul _ _ _)).symm
  have hbound : ∀ k, ‖u k - w‖ ≤ C * ‖g k - g0‖ + 1 * ‖r k‖ := fun k => by
    refine Lp2_norm_le_add _ _ _ hC zero_le_one ?_
    filter_upwards [Lp.coeFn_sub (u k) w, Lp.coeFn_sub (g k) g0, hu k, hw,
      MemLp.coeFn_toLp (hr k)] with x h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h3, h4, h2, Pi.sub_apply, h5, one_mul]
    calc ‖a k x • (g k : RN N → RN N) x - b x • (g0 : RN N → RN N) x‖
        = ‖a k x • ((g k : RN N → RN N) x - (g0 : RN N → RN N) x) +
            (a k x - b x) • (g0 : RN N → RN N) x‖ := by
          congr 1; rw [smul_sub, sub_smul]; abel
      _ ≤ ‖a k x • ((g k : RN N → RN N) x - (g0 : RN N → RN N) x)‖ +
            ‖(a k x - b x) • (g0 : RN N → RN N) x‖ := norm_add_le _ _
      _ ≤ C * ‖(g k : RN N → RN N) x - (g0 : RN N → RN N) x‖ +
            ‖(a k x - b x) • (g0 : RN N → RN N) x‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (haC k x) (norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun k => ‖g k - g0‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hg
  have h2 : Tendsto (fun k => ‖r k‖) atTop (𝓝 0) := by simpa using hr0.norm
  simpa using (h1.const_mul C).add (h2.const_mul 1)

/-! ### Composition with the smooth truncations -/

lemma memLp_Gfun_comp (n : ℕ) (f : L2 N) :
    MemLp (fun x => Gfun n ((f : RN N → ℝ) x)) 2 volume := by
  refine (Lp.memLp f).of_le ((contDiff_Gfun n).continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)) (Eventually.of_forall fun x => ?_)
  simpa only [Real.norm_eq_abs] using abs_Gfun_le n _

lemma memLp_dGfun_smul (n : ℕ) (p : Amb N) :
    MemLp (fun x => dGfun n ((p.1 : RN N → ℝ) x) • (p.2 : RN N → RN N) x) 2 volume := by
  refine (Lp.memLp p.2).of_le_mul (c := Cstep)
    (((continuous_dGfun n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable p.1)).smul
      (Lp.aestronglyMeasurable p.2)) (Eventually.of_forall fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_dGfun_le n _) (norm_nonneg _)

/-- The composition `G_n ∘ p` of a pair with the smooth truncation `G_n`, with the gradient
given by the chain rule. -/
def Gpair (n : ℕ) (p : Amb N) : Amb N :=
  (MemLp.toLp _ (memLp_Gfun_comp n p.1), MemLp.toLp _ (memLp_dGfun_smul n p))

lemma Gpair_fst_ae (n : ℕ) (p : Amb N) :
    ((Gpair n p).1 : RN N → ℝ) =ᵐ[volume] fun x => Gfun n ((p.1 : RN N → ℝ) x) :=
  MemLp.coeFn_toLp (memLp_Gfun_comp n p.1)

lemma Gpair_snd_ae (n : ℕ) (p : Amb N) :
    ((Gpair n p).2 : RN N → RN N) =ᵐ[volume]
      fun x => dGfun n ((p.1 : RN N → ℝ) x) • (p.2 : RN N → RN N) x :=
  MemLp.coeFn_toLp (memLp_dGfun_smul n p)

lemma gradient_comp_real {G : ℝ → ℝ} {G' : ℝ} {φ : RN N → ℝ} {x : RN N}
    (hG : HasDerivAt G G' (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    gradient (fun y => G (φ y)) x = G' • gradient φ x := by
  have h := hG.comp_hasFDerivAt x hφ.hasFDerivAt
  rw [gradient, gradient, show (fun y => G (φ y)) = G ∘ φ from rfl, h.fderiv, map_smul]

lemma Gpair_mem_testGraph (n : ℕ) {D : Set (RN N)} {p : Amb N} (hp : p ∈ testGraph D) :
    Gpair n p ∈ testGraph D := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  have hG0 : Gfun n 0 = 0 := (Gfun_eq_zero_iff n 0).mpr (by positivity)
  refine ⟨fun y => Gfun n (φ y), (contDiff_Gfun n).comp h1, h2.comp_left hG0,
    (tsupport_comp_subset hG0 φ).trans h3, ?_, ?_⟩
  · filter_upwards [Gpair_fst_ae n p, h4] with x a b
    rw [a, b]
  · filter_upwards [Gpair_snd_ae n p, h4, h5] with x a b c
    rw [a, b, c, gradient_comp_real (hasDerivAt_Gfun n (φ x))
      ((h1.differentiable (by simp)) x)]

lemma exists_subseq_Gpair_tendsto (n : ℕ) {q : ℕ → Amb N} {p : Amb N}
    (hq : Tendsto q atTop (𝓝 p)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => Gpair n (q (φ k))) atTop (𝓝 (Gpair n p)) := by
  have h1 : Tendsto (fun k => (q k).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hq
  have h2 : Tendsto (fun k => (q k).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hq
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hC : 0 ≤ Cstep := zero_le_one.trans one_le_Cstep
  have hf : Tendsto (fun k => (Gpair n (q (φ k))).1) atTop (𝓝 (Gpair n p).1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(Gpair n (q (φ k))).1 - (Gpair n p).1‖ ≤
        Cstep * ‖(q (φ k)).1 - p.1‖ + 0 * ‖(q (φ k)).1 - p.1‖ := fun k => by
      refine Lp2_norm_le_add _ _ _ hC le_rfl ?_
      filter_upwards [Lp.coeFn_sub (Gpair n (q (φ k))).1 (Gpair n p).1,
        Lp.coeFn_sub (q (φ k)).1 p.1, Gpair_fst_ae n (q (φ k)), Gpair_fst_ae n p]
        with x a b c d
      rw [a, Pi.sub_apply, c, d, b, Pi.sub_apply, zero_mul, add_zero, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact Gfun_lipschitz n _ _
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.mp (h1.comp hφ.tendsto_atTop)).const_mul Cstep
    simpa using this
  have hs : Tendsto (fun k => (Gpair n (q (φ k))).2) atTop (𝓝 (Gpair n p).2) := by
    refine L2v_mul_tendsto (a := fun k x => dGfun n (((q (φ k)).1 : RN N → ℝ) x))
      (b := fun x => dGfun n ((p.1 : RN N → ℝ) x)) hC
      (fun k => (continuous_dGfun n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      ((continuous_dGfun n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (fun k x => abs_dGfun_le n _) (fun x => abs_dGfun_le n _) (h2.comp hφ.tendsto_atTop)
      (fun k => Gpair_snd_ae n _) (Gpair_snd_ae n p) ?_
    filter_upwards [hae] with x hx
    exact (((continuous_dGfun n).tendsto _).comp hx).smul_const _
  exact hf.prodMk_nhds hs

lemma Gpair_mem_H (n : ℕ) {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) : Gpair n p ∈ H D := by
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  obtain ⟨φ, -, hφ⟩ := exists_subseq_Gpair_tendsto n hq
  exact mem_H_of_tendsto (fun k => testGraph_subset_H D (Gpair_mem_testGraph n (hqT (φ k)))) hφ

lemma posPart_snd_ae_ite (p : Amb N) :
    ((posPart p).2 : RN N → RN N) =ᵐ[volume]
      fun x => (if 0 < (p.1 : RN N → ℝ) x then (1 : ℝ) else 0) • (p.2 : RN N → RN N) x := by
  filter_upwards [indL2v_ae (posSetL2 p.1) (measurableSet_posSetL2 p.1) p.2] with x hx
  simp only [posPart]
  rw [hx]
  simp only [Set.indicator_apply, posSetL2, Set.mem_setOf_eq]
  split_ifs <;> simp

lemma aestronglyMeasurable_ite_pos (f : L2 N) :
    AEStronglyMeasurable (fun x => if 0 < (f : RN N → ℝ) x then (1 : ℝ) else 0) volume :=
  (Measurable.ite (measurableSet_posSetL2 f) measurable_const measurable_const).aestronglyMeasurable

lemma abs_ite_pos_le (f : L2 N) (x : RN N) :
    |(if 0 < (f : RN N → ℝ) x then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

lemma tendsto_Gpair_posPart (p : Amb N) :
    Tendsto (fun n => Gpair n p) atTop (𝓝 (posPart p)) := by
  have hC : 0 ≤ Cstep := zero_le_one.trans one_le_Cstep
  have hf : Tendsto (fun n => (Gpair n p).1) atTop (𝓝 (posPart p).1) := by
    refine Lp2_tendsto_of_dominated (g := fun x => ‖(p.1 : RN N → ℝ) x‖) (Lp.memLp p.1).norm
      (fun n => ?_) ?_
    · filter_upwards [Gpair_fst_ae n p] with x hx
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_Gfun_le n _
    · filter_upwards [ae_all_iff.mpr fun n => Gpair_fst_ae n p, Lp.coeFn_posPart p.1]
        with x hx hpx
      simp only [posPart, hx, hpx]
      exact tendsto_Gfun _
  have hs : Tendsto (fun n => (Gpair n p).2) atTop (𝓝 (posPart p).2) := by
    refine L2v_mul_tendsto (a := fun n x => dGfun n ((p.1 : RN N → ℝ) x))
      (b := fun x => if 0 < (p.1 : RN N → ℝ) x then 1 else 0) hC
      (fun n => (continuous_dGfun n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      ((Measurable.ite (measurableSet_posSetL2 p.1) measurable_const
        measurable_const).aestronglyMeasurable)
      (fun n x => abs_dGfun_le n _) (fun x => ?_) tendsto_const_nhds
      (fun n => Gpair_snd_ae n p) ?_ ?_
    · beta_reduce
      split_ifs <;> simp [one_le_Cstep, hC]
    · filter_upwards [indL2v_ae (posSetL2 p.1) (measurableSet_posSetL2 p.1) p.2] with x hx
      simp only [posPart]
      rw [hx]
      simp only [Set.indicator_apply, posSetL2, Set.mem_setOf_eq]
      split_ifs <;> simp
    · exact Eventually.of_forall fun x => (tendsto_dGfun _).smul_const _
  exact hf.prodMk_nhds hs

/-- **Sobolev chain rule** for the positive part: `v ∈ H_D ⟹ v₊ ∈ H_D`. -/
lemma posPart_mem_H {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) : posPart p ∈ H D :=
  mem_H_of_tendsto (fun n => Gpair_mem_H n hp) (tendsto_Gpair_posPart p)

/-- **Stampacchia's lemma**: the weak gradient vanishes almost everywhere on the zero set. -/
lemma grad_eq_zero_of_eq_zero {D : Set (RN N)} {p : Amb N}
    (hp : p ∈ H D) : ∀ᵐ x, (p.1 : RN N → ℝ) x = 0 → (p.2 : RN N → RN N) x = 0 := by
  set z := posPart p - posPart (-p) - p with hz
  have hzH : z ∈ H D :=
    (H D).sub_mem ((H D).sub_mem (posPart_mem_H hp) (posPart_mem_H ((H D).neg_mem hp))) hp
  have hz1 : z.1 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [Lp.coeFn_sub (posPart p - posPart (-p)).1 p.1,
      Lp.coeFn_sub (posPart p).1 (posPart (-p)).1, Lp.coeFn_posPart p.1,
      Lp.coeFn_posPart (-p).1, Lp.coeFn_neg p.1] with x h1 h2 h3 h4 h5
    simp only [hz, Prod.fst_sub, posPart, Prod.fst_neg] at h1 h2 h3 h4 ⊢
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, h5, Pi.neg_apply, Pi.zero_apply]
    rcases le_total ((p.1 : RN N → ℝ) x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have hz0 : z = 0 := eq_zero_of_l2_self_eq_zero hzH (by rw [l2, hz1, inner_zero_left])
  have hz2 : (z.2 : RN N → RN N) =ᵐ[volume] 0 := by rw [hz0]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hz2, Lp.coeFn_sub (posPart p - posPart (-p)).2 p.2,
    Lp.coeFn_sub (posPart p).2 (posPart (-p)).2,
    indL2v_ae (posSetL2 p.1) (measurableSet_posSetL2 p.1) p.2,
    indL2v_ae (posSetL2 (-p).1) (measurableSet_posSetL2 (-p).1) (-p).2,
    Lp.coeFn_neg p.1] with x h0 h1 h2 h3 h4 h5 hx
  simp only [hz, Prod.snd_sub] at h0 h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply] at h0
  simp only [posPart] at h0
  rw [h3, h4] at h0
  have n1 : x ∉ posSetL2 p.1 := by simp [posSetL2, hx]
  have n2 : x ∉ posSetL2 (-p).1 := by
    intro hmem
    simp only [posSetL2, Set.mem_setOf_eq] at hmem
    rw [Prod.fst_neg, h5, Pi.neg_apply, hx] at hmem
    simp at hmem
  rw [Set.indicator_of_notMem n1, Set.indicator_of_notMem n2] at h0
  simpa using h0

/-- Sequential continuity of the positive part in `H_D`, along a subsequence. -/
lemma exists_subseq_posPart_tendsto {D : Set (RN N)}
    {q : ℕ → Amb N} {p : Amb N} (hp : p ∈ H D) (hq : Tendsto q atTop (𝓝 p)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => posPart (q (φ k))) atTop (𝓝 (posPart p)) := by
  have h1 : Tendsto (fun k => (q k).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hq
  have h2 : Tendsto (fun k => (q k).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hq
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hf : Tendsto (fun k => (posPart (q (φ k))).1) atTop (𝓝 (posPart p).1) :=
    (Lp.continuous_posPart.tendsto p.1).comp (h1.comp hφ.tendsto_atTop)
  have hs : Tendsto (fun k => (posPart (q (φ k))).2) atTop (𝓝 (posPart p).2) := by
    refine L2v_mul_tendsto
      (a := fun k x => if 0 < ((q (φ k)).1 : RN N → ℝ) x then (1 : ℝ) else 0)
      (b := fun x => if 0 < (p.1 : RN N → ℝ) x then (1 : ℝ) else 0) zero_le_one
      (fun k => aestronglyMeasurable_ite_pos _) (aestronglyMeasurable_ite_pos _)
      (fun k x => abs_ite_pos_le _ x) (fun x => abs_ite_pos_le _ x)
      (h2.comp hφ.tendsto_atTop) (fun k => posPart_snd_ae_ite _) (posPart_snd_ae_ite p) ?_
    filter_upwards [hae, grad_eq_zero_of_eq_zero hp] with x hx hz
    rcases lt_trichotomy ((p.1 : RN N → ℝ) x) 0 with h | h | h
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hx.eventually (gt_mem_nhds h)] with k hk
      simp [not_lt.mpr hk.le, not_lt.mpr h.le]
    · simp [hz h]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hx.eventually (lt_mem_nhds h)] with k hk
      simp [hk, h]
  exact hf.prodMk_nhds hs

end FourthRatio

end

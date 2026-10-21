module

public import RequestProject.SobolevTrunc

/-!
# Localization of elements of `H_D` and of sign truncations

* `mem_H_of_vanish_off_compact`: an element of `H_D` vanishing (with its gradient) outside a
  compact subset `K` of an open set `E` belongs to `H_E` (multiplication by a cut-off function);
* `posPart_mem_H_posSign`: the membership part of Lemma 3.1, `v₊ ∈ H₀¹(D₊(v))`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal ContDiff Manifold

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Sign sets -/

lemma posSign_subset (D : Set (RN N)) (f : RN N → ℝ) : posSign D f ⊆ D := Set.inter_subset_left
lemma negSign_subset (D : Set (RN N)) (f : RN N → ℝ) : negSign D f ⊆ D := Set.inter_subset_left

lemma isOpen_posSign {D : Set (RN N)} (hD : IsOpen D) {f : RN N → ℝ} (hf : ContinuousOn f D) :
    IsOpen (posSign D f) := hf.isOpen_inter_preimage hD isOpen_Ioi

lemma isOpen_negSign {D : Set (RN N)} (hD : IsOpen D) {f : RN N → ℝ} (hf : ContinuousOn f D) :
    IsOpen (negSign D f) := hf.isOpen_inter_preimage hD isOpen_Iio

lemma negSign_eq_posSign_neg (D : Set (RN N)) (f : RN N → ℝ) :
    negSign D f = posSign D (fun x => -f x) := by
  ext x; simp [negSign, posSign]

lemma IsContRep.neg {D : Set (RN N)} {v : Amb N} {f : RN N → ℝ} (h : IsContRep D v f) :
    IsContRep D (-v) (fun x => -f x) := by
  refine ⟨h.1.neg, ?_⟩
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_neg v.1), h.2] with x h1 h2
  simp only [Prod.fst_neg, h1, Pi.neg_apply, h2]

/-! ### Cut-off functions -/

lemma exists_cutoff {K E : Set (RN N)} (hK : IsCompact K) (hE : IsOpen E) (hKE : K ⊆ E) :
    ∃ χ : RN N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ E ∧ ∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, χ x = 1 := by
  obtain ⟨V, hVo, hKV, hVE, hVc⟩ := exists_open_between_and_isCompact_closure hK hE hKE
  have hKi : K ⊆ interior (closure V) :=
    hKV.trans (interior_maximal subset_closure hVo)
  obtain ⟨g, hg1, hg0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, RN N) (n := (⊤ : ℕ∞)) hK.isClosed hKi
  have hsupp : tsupport g ⊆ closure V := by
    refine closure_minimal (fun x hx => ?_) isClosed_closure
    by_contra h
    exact hx (hg0 x h)
  refine ⟨g, contMDiff_iff_contDiff.mp g.contMDiff, ?_, hsupp.trans hVE, ?_⟩
  · exact hVc.of_isClosed_subset (isClosed_tsupport _) hsupp
  · obtain ⟨U, hU, hKU, hU1⟩ := eventually_nhdsSet_iff_exists.mp hg1
    exact ⟨U, hU, hKU, hU1⟩

/-! ### Multiplication by a cut-off function -/

lemma exists_bound_cutoff {χ : RN N → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    Continuous (gradient χ) ∧ ∃ C, 0 ≤ C ∧ ∀ x, |χ x| ≤ C ∧ ‖gradient χ x‖ ≤ C := by
  obtain ⟨C1, h1⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hg : Continuous (gradient χ) :=
    (InnerProductSpace.toDual ℝ (RN N)).symm.continuous.comp (hχ.continuous_fderiv (by simp))
  have hgc : HasCompactSupport (gradient χ) :=
    (hχc.fderiv (𝕜 := ℝ)).comp_left (g := (InnerProductSpace.toDual ℝ (RN N)).symm) (map_zero _)
  obtain ⟨C2, h2⟩ := hg.bounded_above_of_compact_support hgc
  refine ⟨hg, max (max C1 C2) 0, le_max_right _ _, fun x => ⟨?_, ?_⟩⟩
  · have := h1 x
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h2 x).trans ((le_max_right _ _).trans (le_max_left _ _))

section Cut

variable {χ : RN N → ℝ} (hχ : Continuous χ) (hg : Continuous (gradient χ)) {C : ℝ}
  (hC : ∀ x, |χ x| ≤ C ∧ ‖gradient χ x‖ ≤ C)

include hχ hC in
lemma memLp_cut_fst (f : L2 N) : MemLp (fun x => χ x * (f : RN N → ℝ) x) 2 volume :=
  (Lp.memLp f).of_le_mul (c := C) (hχ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC x).1 (norm_nonneg _))

include hχ hg hC in
lemma memLp_cut_snd (p : Amb N) :
    MemLp (fun x => χ x • (p.2 : RN N → RN N) x + (p.1 : RN N → ℝ) x • gradient χ x) 2
      volume := by
  refine MemLp.add ?_ ?_
  · exact (Lp.memLp p.2).of_le_mul (c := C)
      (hχ.aestronglyMeasurable.smul (Lp.aestronglyMeasurable p.2))
      (Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC x).1 (norm_nonneg _))
  · exact (Lp.memLp p.1).of_le_mul (c := C)
      ((Lp.aestronglyMeasurable p.1).smul hg.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC x).2 (norm_nonneg _))

/-- Multiplication of a pair by the cut-off function `χ` (product rule for the gradient). -/
def Mpair (p : Amb N) : Amb N :=
  (MemLp.toLp _ (memLp_cut_fst hχ hC p.1), MemLp.toLp _ (memLp_cut_snd hχ hg hC p))

lemma Mpair_fst_ae (p : Amb N) :
    ((Mpair hχ hg hC p).1 : RN N → ℝ) =ᵐ[volume] fun x => χ x * (p.1 : RN N → ℝ) x :=
  MemLp.coeFn_toLp (memLp_cut_fst hχ hC p.1)

lemma Mpair_snd_ae (p : Amb N) :
    ((Mpair hχ hg hC p).2 : RN N → RN N) =ᵐ[volume]
      fun x => χ x • (p.2 : RN N → RN N) x + (p.1 : RN N → ℝ) x • gradient χ x :=
  MemLp.coeFn_toLp (memLp_cut_snd hχ hg hC p)

lemma Mpair_tendsto {q : ℕ → Amb N} {p : Amb N} (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun k => Mpair hχ hg hC (q k)) atTop (𝓝 (Mpair hχ hg hC p)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0).1
  have h1 : Tendsto (fun k => ‖(q k).1 - p.1‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_fst.tendsto p).comp hq)
  have h2 : Tendsto (fun k => ‖(q k).2 - p.2‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_snd.tendsto p).comp hq)
  have hf : Tendsto (fun k => (Mpair hχ hg hC (q k)).1) atTop (𝓝 (Mpair hχ hg hC p).1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(Mpair hχ hg hC (q k)).1 - (Mpair hχ hg hC p).1‖ ≤
        C * ‖(q k).1 - p.1‖ + 0 * ‖(q k).1 - p.1‖ := fun k => by
      refine Lp2_norm_le_add _ _ _ hC0 le_rfl ?_
      filter_upwards [Lp.coeFn_sub (Mpair hχ hg hC (q k)).1 (Mpair hχ hg hC p).1,
        Lp.coeFn_sub (q k).1 p.1, Mpair_fst_ae hχ hg hC (q k), Mpair_fst_ae hχ hg hC p]
        with x a b c d
      rw [a, Pi.sub_apply, c, d, b, Pi.sub_apply, zero_mul, add_zero, ← mul_sub, norm_mul,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC x).1 (norm_nonneg _)
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    simpa using h1.const_mul C
  have hs : Tendsto (fun k => (Mpair hχ hg hC (q k)).2) atTop (𝓝 (Mpair hχ hg hC p).2) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(Mpair hχ hg hC (q k)).2 - (Mpair hχ hg hC p).2‖ ≤
        C * ‖(q k).2 - p.2‖ + C * ‖(q k).1 - p.1‖ := fun k => by
      refine Lp2_norm_le_add _ _ _ hC0 hC0 ?_
      filter_upwards [Lp.coeFn_sub (Mpair hχ hg hC (q k)).2 (Mpair hχ hg hC p).2,
        Lp.coeFn_sub (q k).1 p.1, Lp.coeFn_sub (q k).2 p.2, Mpair_snd_ae hχ hg hC (q k),
        Mpair_snd_ae hχ hg hC p] with x a b b' c d
      rw [a, Pi.sub_apply, c, d, b, Pi.sub_apply, b', Pi.sub_apply]
      calc ‖χ x • ((q k).2 : RN N → RN N) x + ((q k).1 : RN N → ℝ) x • gradient χ x -
            (χ x • (p.2 : RN N → RN N) x + (p.1 : RN N → ℝ) x • gradient χ x)‖
          = ‖χ x • (((q k).2 : RN N → RN N) x - (p.2 : RN N → RN N) x) +
              (((q k).1 : RN N → ℝ) x - (p.1 : RN N → ℝ) x) • gradient χ x‖ := by
            congr 1; rw [smul_sub, sub_smul]; abel
        _ ≤ ‖χ x • (((q k).2 : RN N → RN N) x - (p.2 : RN N → RN N) x)‖ +
              ‖(((q k).1 : RN N → ℝ) x - (p.1 : RN N → ℝ) x) • gradient χ x‖ := norm_add_le _ _
        _ ≤ C * ‖((q k).2 : RN N → RN N) x - (p.2 : RN N → RN N) x‖ +
              C * ‖((q k).1 : RN N → ℝ) x - (p.1 : RN N → ℝ) x‖ := by
            gcongr
            · rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hC x).1 (norm_nonneg _)
            · rw [norm_smul, mul_comm]
              exact mul_le_mul_of_nonneg_right (hC x).2 (norm_nonneg _)
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    simpa using (h2.const_mul C).add (h1.const_mul C)
  exact hf.prodMk_nhds hs

lemma Mpair_mem_testGraph (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {D E : Set (RN N)}
    (hχE : tsupport χ ⊆ E) {p : Amb N} (hp : p ∈ testGraph D) :
    Mpair hχ hg hC p ∈ testGraph E := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  refine ⟨fun y => χ y * φ y, hχs.mul h1, h2.mul_left, tsupport_mul_subset_left.trans hχE,
    ?_, ?_⟩
  · filter_upwards [Mpair_fst_ae hχ hg hC p, h4] with x a b
    rw [a, b]
  · filter_upwards [Mpair_snd_ae hχ hg hC p, h4, h5] with x a b c
    rw [a, b, c]
    have hx1 := (hχs.differentiable (by simp)) x
    have hx2 := (h1.differentiable (by simp)) x
    rw [gradient, gradient, gradient, fderiv_fun_mul hx1 hx2, map_add, map_smul, map_smul]

lemma Mpair_mem_H (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {D E : Set (RN N)}
    (hχE : tsupport χ ⊆ E) {p : Amb N} (hp : p ∈ H D) : Mpair hχ hg hC p ∈ H E := by
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  exact mem_H_of_tendsto (fun k => testGraph_subset_H E
    (Mpair_mem_testGraph hχ hg hC hχs hχE (hqT k))) (Mpair_tendsto hχ hg hC hq)

lemma Mpair_eq_self {K U : Set (RN N)} (hU : IsOpen U) (hKU : K ⊆ U)
    (hU1 : ∀ x ∈ U, χ x = 1) {q : Amb N}
    (h1 : ∀ᵐ x, x ∉ K → (q.1 : RN N → ℝ) x = 0)
    (h2 : ∀ᵐ x, x ∉ K → (q.2 : RN N → RN N) x = 0) : Mpair hχ hg hC q = q := by
  have hgrad : ∀ x ∈ U, gradient χ x = 0 := fun x hx => by
    have : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hU1 y hy
    rw [this.gradient_eq]
    exact gradient_fun_const x 1
  refine Prod.ext ?_ ?_
  · refine Lp.ext ?_
    filter_upwards [Mpair_fst_ae hχ hg hC q, h1] with x a b
    rw [a]
    by_cases hx : x ∈ K
    · rw [hU1 x (hKU hx), one_mul]
    · rw [b hx, mul_zero]
  · refine Lp.ext ?_
    filter_upwards [Mpair_snd_ae hχ hg hC q, h1, h2] with x a b c
    rw [a]
    by_cases hx : x ∈ K
    · rw [hU1 x (hKU hx), hgrad x (hKU hx), one_smul, smul_zero, add_zero]
    · rw [b hx, c hx, smul_zero, zero_smul, add_zero]

end Cut

/-- An element of `H_D` vanishing (together with its gradient) outside a compact subset `K` of
an open set `E` belongs to `H_E`. -/
lemma mem_H_of_vanish_off_compact {D E K : Set (RN N)} (hE : IsOpen E) (hK : IsCompact K)
    (hKE : K ⊆ E) {q : Amb N} (hq : q ∈ H D)
    (h1 : ∀ᵐ x, x ∉ K → (q.1 : RN N → ℝ) x = 0)
    (h2 : ∀ᵐ x, x ∉ K → (q.2 : RN N → RN N) x = 0) : q ∈ H E := by
  obtain ⟨χ, hχs, hχc, hχE, U, hU, hKU, hU1⟩ := exists_cutoff hK hE hKE
  obtain ⟨hg, C, -, hC⟩ := exists_bound_cutoff hχs hχc
  rw [← Mpair_eq_self hχs.continuous hg hC hU hKU hU1 h1 h2]
  exact Mpair_mem_H hχs.continuous hg hC hχs hχE hq

/-! ### Lemma 3.1, membership part -/

lemma posPart_fst_ae' (p : Amb N) :
    ((posPart p).1 : RN N → ℝ) =ᵐ[volume] fun x => max ((p.1 : RN N → ℝ) x) 0 :=
  Lp.coeFn_posPart p.1

lemma trunc_min_pointwise {A1 P1 : ℝ} {A2 P2 : RN N} (hA1 : 0 ≤ A1) (hP1 : 0 ≤ P1)
    (hA : A1 = 0 → A2 = 0) (hcase : A1 = 0 ∨ (P1 = 0 ∧ P2 = 0)) :
    A1 - max (A1 - P1) 0 = 0 ∧
      A2 - (if 0 < A1 - P1 then (1 : ℝ) else 0) • (A2 - P2) = 0 := by
  rcases hA1.eq_or_lt with h | h
  · subst h
    rw [hA rfl]
    have : ¬ (0 < 0 - P1) := by linarith
    rw [if_neg this, max_eq_right (by linarith : 0 - P1 ≤ 0)]
    simp
  · rcases hcase with h' | ⟨h1, h2⟩
    · exact absurd h' h.ne'
    · subst h1; subst h2
      simp [h, max_eq_left h.le]

lemma posPart_Gpair_sub_posPart (n : ℕ) (v : Amb N) : posPart (Gpair n v - posPart v) = 0 := by
  have hle : ∀ᵐ x, ((Gpair n v - posPart v).1 : RN N → ℝ) x ≤ 0 := by
    filter_upwards [Lp.coeFn_sub (Gpair n v).1 (posPart v).1, Gpair_fst_ae n v,
      Lp.coeFn_posPart v.1] with x h1 h2 h3
    simp only [Prod.fst_sub] at h1 ⊢
    rw [h1, Pi.sub_apply, h2]
    simp only [posPart] at h3 ⊢
    rw [h3]
    linarith [Gfun_le_max n ((v.1 : RN N → ℝ) x)]
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [Lp.coeFn_posPart (Gpair n v - posPart v).1, hle,
      Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))] with x h1 h2 h3
    rw [show (posPart (Gpair n v - posPart v)).1 = Lp.posPart (Gpair n v - posPart v).1 from rfl,
      h1, Prod.fst_zero, h3, max_eq_right h2, Pi.zero_apply]
  · filter_upwards [posPart_snd_ae_ite (Gpair n v - posPart v), hle,
      Lp.coeFn_zero (RN N) 2 (volume : Measure (RN N))] with x h1 h2 h3
    rw [h1, Prod.snd_zero, h3, if_neg (not_lt.mpr h2), zero_smul, Pi.zero_apply]

/-- **Lemma 3.1, membership part** (Sobolev localization of the positive part): for
`v ∈ H_D` with a continuous representative `f` on `D`, `v₊ ∈ H₀¹(D₊(v))`. -/
theorem posPart_mem_H_posSign {D : Set (RN N)} (hD : IsAdmissible D) {v : Amb N}
    (hv : v ∈ H D) {f : RN N → ℝ} (hf : IsContRep D v f) : posPart v ∈ H (posSign D f) := by
  have hE : IsOpen (posSign D f) := isOpen_posSign hD.1 hf.1
  have hvD : ∀ᵐ x, x ∈ D → (v.1 : RN N → ℝ) x = f x :=
    (ae_restrict_iff' hD.1.measurableSet).mp hf.2
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hv
  have hG : ∀ n, Gpair n v ∈ H (posSign D f) := by
    intro n
    have haH : Gpair n v ∈ H D := Gpair_mem_H n hv
    have hwE : ∀ k, Gpair n v - posPart (Gpair n v - posPart (q k)) ∈ H (posSign D f) := by
      intro k
      obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := hqT k
      have hqH : q k ∈ H D := testGraph_subset_H D (hqT k)
      have hwD : Gpair n v - posPart (Gpair n v - posPart (q k)) ∈ H D :=
        (H D).sub_mem haH (posPart_mem_H ((H D).sub_mem haH (posPart_mem_H hqH)))
      set K := tsupport ψ ∩ f ⁻¹' Set.Ici (1 / ((n : ℝ) + 1)) with hK
      have hKcl : IsClosed K :=
        (hf.1.mono h3).preimage_isClosed_of_isClosed (isClosed_tsupport ψ) isClosed_Ici
      have hKc : IsCompact K := h2.isCompact.of_isClosed_subset hKcl Set.inter_subset_left
      have hKE : K ⊆ posSign D f := fun x hx =>
        ⟨h3 hx.1, lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) (Set.mem_Ici.mp hx.2)⟩
      -- pointwise description of `w = a - (a - (q k)₊)₊`
      have key : ∀ᵐ x, x ∉ K →
          ((Gpair n v - posPart (Gpair n v - posPart (q k))).1 : RN N → ℝ) x = 0 ∧
          ((Gpair n v - posPart (Gpair n v - posPart (q k))).2 : RN N → RN N) x = 0 := by
        filter_upwards [hvD, h4, h5, Gpair_fst_ae n v, Gpair_snd_ae n v,
          posPart_fst_ae' (q k), posPart_snd_ae_ite (q k),
          Lp.coeFn_sub (Gpair n v).1 (posPart (q k)).1,
          Lp.coeFn_sub (Gpair n v).2 (posPart (q k)).2,
          posPart_fst_ae' (Gpair n v - posPart (q k)),
          posPart_snd_ae_ite (Gpair n v - posPart (q k)),
          Lp.coeFn_sub (Gpair n v).1 (posPart (Gpair n v - posPart (q k))).1,
          Lp.coeFn_sub (Gpair n v).2 (posPart (Gpair n v - posPart (q k))).2]
          with x hvx hq1 hq2 ha1 ha2 hP1 hP2 hB1 hB2 hpB1 hpB2 hw1 hw2 hxK
        rw [Prod.fst_sub, Prod.snd_sub, hw1, hw2, Pi.sub_apply, Pi.sub_apply, hpB1, hpB2,
          Prod.fst_sub, Prod.snd_sub, hB1, hB2, Pi.sub_apply, Pi.sub_apply, hP1, hP2, ha1, ha2]
        set c := 1 / ((n : ℝ) + 1)
        refine trunc_min_pointwise (Gfun_nonneg n _) (le_max_right _ _) ?_ ?_
        · intro h0
          rw [dGfun_eq_zero n ((Gfun_eq_zero_iff n _).mp h0), zero_smul]
        · by_cases hxs : x ∈ tsupport ψ
          · left
            have hfx : f x < c := by
              by_contra hc
              exact hxK ⟨hxs, Set.mem_Ici.mpr (not_lt.mp hc)⟩
            rw [Gfun_eq_zero_iff, hvx (h3 hxs)]
            exact hfx.le
          · right
            have hψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxs
            have hgψ : gradient ψ x = 0 := by
              simp [gradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs]
            rw [hq1, hq2, hψ, hgψ]
            simp
      refine mem_H_of_vanish_off_compact hE hKc hKE hwD ?_ ?_
      · filter_upwards [key] with x hx hxK using (hx hxK).1
      · filter_upwards [key] with x hx hxK using (hx hxK).2
    obtain ⟨φ1, -, t1⟩ := exists_subseq_posPart_tendsto hv hq
    have t2 : Tendsto (fun k => Gpair n v - posPart (q (φ1 k))) atTop
        (𝓝 (Gpair n v - posPart v)) := tendsto_const_nhds.sub t1
    obtain ⟨φ2, -, t3⟩ := exists_subseq_posPart_tendsto
      ((H D).sub_mem haH (posPart_mem_H hv)) t2
    rw [posPart_Gpair_sub_posPart] at t3
    have t4 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Gpair n v) atTop
      (𝓝 (Gpair n v))).sub t3
    rw [sub_zero] at t4
    exact mem_H_of_tendsto (fun k => hwE (φ1 (φ2 k))) t4
  exact mem_H_of_tendsto hG (tendsto_Gpair_posPart v)

/-- **Lemma 3.1, membership part** for both sign truncations. -/
theorem parts_mem' {D : Set (RN N)} (hD : IsAdmissible D) {v : Amb N}
    (hv : v ∈ H D) {f : RN N → ℝ} (hf : IsContRep D v f) :
    posPart v ∈ H (posSign D f) ∧ negPart v ∈ H (negSign D f) := by
  refine ⟨posPart_mem_H_posSign hD hv hf, ?_⟩
  rw [negSign_eq_posSign_neg]
  exact posPart_mem_H_posSign hD ((H D).neg_mem hv) hf.neg

end FourthRatio

end

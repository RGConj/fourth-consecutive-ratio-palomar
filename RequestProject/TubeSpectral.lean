module

public import RequestProject.Nodal
public import RequestProject.BallTools
public import RequestProject.TubeDilation

/-!
# Spectral convergence for domains shrinking onto a union of balls

Let `U = ⋃ᵢ B_r(cᵢ)` be a finite union of balls with pairwise disjoint closures and let `Ωₙ` be
admissible sets with `U ⊆ Ωₙ ⊆ D₀` such that almost every point outside the closed balls
eventually leaves `Ωₙ`.  Then `λ_j(Ωₙ) → λ_j(U)` for every `j`.

The upper bound is domain monotonicity.  For the lower bound, the first `j` eigenfunctions of
`Ωₙ` are bounded in `H_{D₀}`; by Rellich's theorem a subsequence converges in `L²`, the limits
lift to `H_{D₀}` with lower semicontinuous energy (via the spectral expansion on `D₀`), they vanish
outside the closed balls, and hence lie in `H_U` (a dilation argument for each ball).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

set_option maxHeartbeats 1000000 in
/-- `L²` limits of energy-bounded sequences in `H_D` lift to `H_D` with the same energy bound. -/
lemma lift_of_tendsto (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {v : ℕ → Amb N}
    (hv : ∀ n, v n ∈ H D) {C : ℝ} (hC : ∀ n, qf (v n) (v n) ≤ C) {f : L2 N}
    (hf : Tendsto (fun n => (v n).1) atTop (𝓝 f)) :
    ∃ w ∈ H D, w.1 = f ∧ qf w w ≤ C := by
  obtain ⟨e, he⟩ := exists_spectralBasis hN hD
  obtain ⟨-, -, -, -, -, hlamtop, -⟩ := ext_spectral hN hD
  set lam : ℕ → ℝ := fun k => eigenvalue D (k + 1) with hlam_def
  have hl1 := eigenvalue_one_pos hN hD
  have hlam1 : ∀ k, eigenvalue D 1 ≤ lam k := fun k =>
    eigenvalue_mono hN hD le_rfl (Nat.le_add_left 1 k)
  have hlam0 : ∀ k, 0 < lam k := fun k => hl1.trans_le (hlam1 k)
  have hC0 : 0 ≤ C := (qf_self_nonneg _).trans (hC 0)
  set c : ℕ → ℝ := fun k => ⟪f, (e k).1⟫ with hc_def
  have hcn : ∀ k, Tendsto (fun n => l2 (v n) (e k)) atTop (𝓝 (c k)) := fun k =>
    Filter.Tendsto.inner (𝕜 := ℝ) hf tendsto_const_nhds
  have hl2e : ∀ k l, l2 (e k) (e l) = if k = l then 1 else 0 := he.2.1
  have hqe : ∀ k l, qf (e k) (e l) = lam k * if k = l then 1 else 0 := by
    intro k l; rw [(he.1 k).2.2 _ (he.mem_H l), hl2e]
  have hqsum : ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      qf (∑ k ∈ s, a k • e k) (∑ k ∈ s, a k • e k) = ∑ k ∈ s, lam k * a k ^ 2 := by
    intro s a
    simp only [qf_sum_left, qf_sum_right, qf_smul_left, qf_smul_right, hqe]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (fun h => absurd hk h)]
    simp; ring
  have hlsum : ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      l2 (∑ k ∈ s, a k • e k) (∑ k ∈ s, a k • e k) = ∑ k ∈ s, a k ^ 2 := by
    intro s a
    simp only [l2_sum_left, l2_sum_right, l2_smul_left, l2_smul_right, hl2e]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (fun h => absurd hk h)]
    simp; ring
  -- partial sums of the energy are bounded
  have hpart : ∀ K, ∑ k ∈ Finset.range K, lam k * c k ^ 2 ≤ C := by
    intro K
    have hlim : Tendsto (fun n => ∑ k ∈ Finset.range K, lam k * l2 (v n) (e k) ^ 2) atTop
        (𝓝 (∑ k ∈ Finset.range K, lam k * c k ^ 2)) :=
      tendsto_finsetSum _ fun k _ => ((hcn k).pow 2).const_mul _
    refine le_of_tendsto' hlim fun n => ?_
    exact (sum_le_hasSum (Finset.range K) (fun k _ => mul_nonneg (hlam0 k).le (sq_nonneg _))
      ((he.2.2 (v n) (hv n)).1)).trans (hC n)
  set g : ℕ → ℝ := fun k => lam k * c k ^ 2 with hg_def
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg (hlam0 k).le (sq_nonneg _)
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  set S : ℕ → Amb N := fun K => ∑ k ∈ Finset.range K, c k • e k with hS_def
  have hSH : ∀ K, S K ∈ H D := fun K =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (he.mem_H k)
  set T : ℕ → ℝ := fun K => ∑' k, g (k + K) with hT_def
  have hT : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add g
  have hIco : ∀ K K', K ≤ K' → ∑ k ∈ Finset.Ico K K', g k ≤ T K := by
    intro K K' _
    rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [add_comm K]
    exact Summable.sum_le_tsum _ (fun i _ => hg0 _) ((summable_nat_add_iff K).mpr hgs)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 1 + 1 / eigenvalue D 1 := ⟨_, rfl⟩
  have h1d : 0 < 1 / eigenvalue D 1 := one_div_pos.mpr hl1
  have hκ0 : 0 ≤ κ := hκ ▸ (add_pos one_pos h1d).le
  have hdist : ∀ K K', K ≤ K' → dist (S K) (S K') ≤ Real.sqrt (κ * T K) := by
    intro K K' hKK'
    have hdiff : S K' - S K = ∑ k ∈ Finset.Ico K K', c k • e k := by
      simp only [hS_def]
      rw [Finset.sum_Ico_eq_sub _ hKK']
    rw [dist_comm, dist_eq_norm, hdiff]
    set p := ∑ k ∈ Finset.Ico K K', c k • e k with hp
    have hq : ‖p.2‖ ^ 2 = ∑ k ∈ Finset.Ico K K', g k := by
      rw [← real_inner_self_eq_norm_sq]; exact hqsum _ _
    have hl : ‖p.1‖ ^ 2 ≤ (1 / eigenvalue D 1) * ∑ k ∈ Finset.Ico K K', g k := by
      rw [← real_inner_self_eq_norm_sq]
      change l2 p p ≤ _
      rw [hlsum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl1]
      simp only [hg_def]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hlam1 k) (sq_nonneg (c k))
    have hsumT := hIco K K' hKK'
    have hsum0 : 0 ≤ ∑ k ∈ Finset.Ico K K', g k := Finset.sum_nonneg fun k _ => hg0 k
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine Real.le_sqrt_of_sq_le ?_
      calc ‖p.1‖ ^ 2 ≤ (1 / eigenvalue D 1) * ∑ k ∈ Finset.Ico K K', g k := hl
        _ ≤ κ * T K := mul_le_mul (hκ ▸ le_add_of_nonneg_left zero_le_one) hsumT hsum0 hκ0
    · refine Real.le_sqrt_of_sq_le ?_
      rw [hq]
      have : (1 : ℝ) ≤ κ := hκ ▸ le_add_of_nonneg_right h1d.le
      exact hsumT.trans (le_mul_of_one_le_left (hsum0.trans hsumT) this)
  have hcauchy : CauchySeq S := by
    refine cauchySeq_of_le_tendsto_0' _ hdist ?_
    have : Tendsto (fun K => Real.sqrt (κ * T K)) atTop (𝓝 (Real.sqrt (κ * 0))) :=
      (Real.continuous_sqrt.tendsto _).comp (hT.const_mul κ)
    simpa using this
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hwH : w ∈ H D :=
    (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hw (Eventually.of_forall hSH)
  -- the first components converge to `f`
  have hR : ∀ K, lam K * ‖f - (S K).1‖ ^ 2 ≤ C := by
    intro K
    have hlim : Tendsto (fun n => (v n - ∑ k ∈ Finset.range K, l2 (v n) (e k) • e k).1) atTop
        (𝓝 (f - (S K).1)) := by
      simp only [Prod.fst_sub, Prod.fst_sum, Prod.smul_fst, hS_def]
      exact hf.sub (tendsto_finsetSum _ fun k _ => (hcn k).smul_const _)
    refine le_of_tendsto' ((hlim.norm.pow 2).const_mul _) fun n => ?_
    have ht := he.tail_le hN hD (hv n) K
    rw [Fin.sum_univ_eq_sum_range (fun i => l2 (v n) (e i) • e i) K] at ht
    rw [← real_inner_self_eq_norm_sq]
    exact ht.trans (hC n)
  have hS1 : Tendsto (fun K => (S K).1) atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun K => Real.sqrt (C / lam K)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (hlamtop.const_div_atTop C)
      simpa only [Function.comp_def, Real.sqrt_zero] using this
    refine squeeze_zero (fun K => norm_nonneg _) (fun K => ?_) hb
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ (hlam0 K), norm_sub_rev, mul_comm]
    exact hR K
  have hw1 : w.1 = f := tendsto_nhds_unique ((continuous_fst.tendsto w).comp hw) hS1
  refine ⟨w, hwH, hw1, ?_⟩
  have hqlim : Tendsto (fun K => qf (S K) (S K)) atTop (𝓝 (qf w w)) := by
    have h2 := (continuous_snd.tendsto w).comp hw
    exact Filter.Tendsto.inner (𝕜 := ℝ) h2 h2
  refine le_of_tendsto' hqlim fun K => ?_
  rw [hqsum]; exact hpart K

/-- A common subsequence along which finitely many bounded sequences in `H_D` converge in `L²`. -/
lemma common_subseq (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) (j : ℕ)
    (v : Fin j → ℕ → Amb N) (hv : ∀ k n, v k n ∈ H D) (hb : ∃ C, ∀ k n, ‖v k n‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Fin j → L2 N,
      ∀ k, Tendsto (fun n => (v k (φ n)).1) atTop (𝓝 (f k)) := by
  induction j with
  | zero => exact ⟨id, strictMono_id, fun k => k.elim0, fun k => k.elim0⟩
  | succ j ih =>
    obtain ⟨C, hC⟩ := hb
    obtain ⟨φ₁, hφ₁, f₁, hf₁⟩ := ih (fun k => v k.castSucc) (fun k n => hv _ n)
      ⟨C, fun k n => hC _ n⟩
    obtain ⟨φ₂, hφ₂, g, hg⟩ := compact_embedding hN hD (fun n => v (Fin.last j) (φ₁ n))
      (fun n => hv _ _) ⟨C, fun n => hC _ _⟩
    refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, Fin.lastCases g f₁, fun k => ?_⟩
    induction k using Fin.lastCases with
    | last => simpa using hg
    | cast k => simpa only [Function.comp_def, Fin.lastCases_castSucc] using
        (hf₁ k).comp hφ₂.tendsto_atTop

/-- The weak gradient vanishes almost everywhere on an open set where the function vanishes. -/
lemma snd_ae_zero_of_fst_ae_zero {D V : Set (RN N)} (hV : IsOpen V) {w : Amb N} (hw : w ∈ H D)
    (h : ∀ᵐ x, x ∈ V → (w.1 : RN N → ℝ) x = 0) : ∀ᵐ x, x ∈ V → (w.2 : RN N → RN N) x = 0 := by
  have he : ∀ e : RN N, ∀ᵐ x ∂(volume : Measure (RN N)), x ∈ V →
      ⟪e, (w.2 : RN N → RN N) x⟫ = 0 := by
    intro e
    have hli : LocallyIntegrable (fun x => ⟪e, (w.2 : RN N → RN N) x⟫) volume := by
      have hm : MemLp (fun x => ⟪e, (w.2 : RN N → RN N) x⟫) 2 volume :=
        (Lp.memLp w.2).const_inner e
      exact hm.locallyIntegrable (by norm_num)
    refine hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli.locallyIntegrableOn V)
      fun θ hθ hθc hθV => ?_
    have hi := ibpFunctional_H hw ⟨θ, hθ, hθc⟩ e
    rw [ibpFunctional_apply] at hi
    have h0 : ∫ x, fderiv ℝ θ x e * (w.1 : RN N → ℝ) x = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [h] with x hx
        by_cases hxV : x ∈ V
        · simp [hx hxV]
        · have : x ∉ tsupport θ := fun h' => hxV (hθV h')
          have hz : fderiv ℝ θ x = 0 :=
            Function.notMem_support.mp fun h' => this (support_fderiv_subset ℝ h')
          simp [hz]
    simp only [h0, add_zero] at hi
    simpa [smul_eq_mul] using hi
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have hall : ∀ᵐ x ∂(volume : Measure (RN N)), ∀ i, x ∈ V →
      ⟪b i, (w.2 : RN N → RN N) x⟫ = 0 :=
    ae_all_iff.mpr fun i => he (b i)
  filter_upwards [hall] with x hx hxV
  have : (w.2 : RN N → RN N) x = ∑ i, ⟪b i, (w.2 : RN N → RN N) x⟫ • b i :=
    (b.sum_repr' _).symm
  rw [this]
  simp [hx _ hxV]

lemma L2_coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → L2 N) :
    ((∑ i ∈ s, f i : L2 N) : RN N → ℝ) =ᵐ[volume] fun x => ∑ i ∈ s, (f i : RN N → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))] with x hx
    exact hx
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

/-- Two restrictions agree if the element vanishes on the symmetric difference. -/
lemma restrictTo_eq_of_vanish {S₁ S₂ : Set (RN N)} (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂)
    {w : Amb N} (hv1 : ∀ᵐ x, x ∈ S₁ → x ∉ S₂ → (w.1 : RN N → ℝ) x = 0)
    (hv1' : ∀ᵐ x, x ∈ S₂ → x ∉ S₁ → (w.1 : RN N → ℝ) x = 0)
    (hv2 : ∀ᵐ x, x ∈ S₁ → x ∉ S₂ → (w.2 : RN N → RN N) x = 0)
    (hv2' : ∀ᵐ x, x ∈ S₂ → x ∉ S₁ → (w.2 : RN N → RN N) x = 0) :
    restrictTo S₁ w = restrictTo S₂ w := by
  refine Prod.ext ?_ ?_
  · refine Lp.ext ?_
    filter_upwards [restrictTo_fst_ae h₁ w, restrictTo_fst_ae h₂ w, hv1, hv1'] with x a b c d
    rw [a, b]
    by_cases x1 : x ∈ S₁ <;> by_cases x2 : x ∈ S₂ <;> simp [x1, x2, c, d]
  · refine Lp.ext ?_
    filter_upwards [restrictTo_snd_ae h₁ w, restrictTo_snd_ae h₂ w, hv2, hv2'] with x a b c d
    rw [a, b]
    by_cases x1 : x ∈ S₁ <;> by_cases x2 : x ∈ S₂ <;> simp [x1, x2, c, d]

/-- An element of some `H_D` vanishing outside a finite union of closed balls with disjoint
closures lies in the form domain of the union of the open balls. -/
lemma mem_H_iUnion_ball_of_vanish {m : ℕ} (c : Fin m → RN N) {r : ℝ} (hr : 0 < r)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) r)) {D : Set (RN N)} {w : Amb N}
    (hw : w ∈ H D) (h : ∀ᵐ x, x ∉ ⋃ i, closedBall (c i) r → (w.1 : RN N → ℝ) x = 0) :
    w ∈ H (⋃ i, ball (c i) r) := by
  classical
  set K := ⋃ i, closedBall (c i) r with hK_def
  have hKc : IsCompact K := isCompact_iUnion fun i => isCompact_closedBall _ _
  have h2 : ∀ᵐ x, x ∉ K → (w.2 : RN N → RN N) x = 0 :=
    snd_ae_zero_of_fst_ae_zero hKc.isClosed.isOpen_compl hw h
  -- separation of the centres
  have hsep : ∀ i j, i ≠ j → 2 * r < dist (c i) (c j) := by
    intro i j hij
    by_contra hle
    push_neg at hle
    have hz1 : midpoint ℝ (c i) (c j) ∈ closedBall (c i) r := by
      rw [mem_closedBall, dist_comm, dist_left_midpoint]
      norm_num
      linarith
    have hz2 : midpoint ℝ (c i) (c j) ∈ closedBall (c j) r := by
      rw [mem_closedBall, dist_comm, dist_right_midpoint]
      norm_num
      linarith
    exact Set.disjoint_left.mp (hdisj hij) hz1 hz2
  obtain ⟨δ₀, hδ₀, hδsep⟩ : ∃ δ₀ > 0, ∀ i j, i ≠ j → 2 * r + 4 * δ₀ < dist (c i) (c j) := by
    have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ p : Fin m × Fin m, p.1 ≠ p.2 →
        2 * r + 4 * δ < dist (c p.1) (c p.2) := by
      rw [Filter.eventually_all]
      intro p
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun _ h => absurd hp h
      · have hc : Continuous fun δ : ℝ => 2 * r + 4 * δ := by fun_prop
        have := hc.tendsto 0
        simp only [mul_zero, add_zero] at this
        exact (this.eventually (gt_mem_nhds (hsep _ _ hp))).mono fun _ h _ => h
    obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε / 2, by positivity, fun i j hij => hP ?_ (i, j) hij⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  -- membership in the slightly larger union
  have hdisjδ : ∀ δ, 0 < δ → δ ≤ δ₀ → Pairwise (Disjoint on fun i => ball (c i) (r + δ)) := by
    intro δ hδ hδle i j hij
    refine (ball_disjoint_ball ?_)
    have := hδsep i j hij
    linarith
  have hwE : ∀ δ, 0 < δ → w ∈ H (⋃ i, ball (c i) (r + δ)) := by
    intro δ hδ
    refine mem_H_of_vanish_off_compact (isOpen_iUnion fun _ => isOpen_ball) hKc ?_ hw h h2
    exact Set.iUnion_mono fun i => closedBall_subset_ball (by linarith)
  -- the pieces
  set P : Fin m → Amb N := fun i => restrictTo (ball (c i) (r + δ₀)) w with hP_def
  have hvanK : ∀ i (δ : ℝ), 0 < δ → δ ≤ δ₀ → ∀ x, x ∈ ball (c i) (r + δ₀) →
      x ∉ ball (c i) (r + δ) → x ∉ K := by
    intro i δ hδ hδle x hx1 hx2 hxK
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxK
    rw [mem_closedBall] at hk
    rw [mem_ball] at hx1 hx2
    by_cases hki : k = i
    · subst hki; linarith
    · have := hδsep k i hki
      have := dist_triangle (c k) x (c i)
      rw [dist_comm] at hk
      linarith [dist_comm x (c i)]
  have hPmem : ∀ i (δ : ℝ), 0 < δ → δ ≤ δ₀ → P i ∈ H (ball (c i) (r + δ)) := by
    intro i δ hδ hδle
    have hres := restrictTo_mem_H_piece (fun i => ball (c i) (r + δ)) (fun _ => isOpen_ball)
      (hdisjδ δ hδ hδle) i (hwE δ hδ)
    have heq : restrictTo (ball (c i) (r + δ)) w = P i := by
      refine restrictTo_eq_of_vanish measurableSet_ball measurableSet_ball ?_ ?_ ?_ ?_
      · filter_upwards with x hx1 hx2
        exact absurd (ball_subset_ball (by linarith) hx1) hx2
      · filter_upwards [h] with x hx hx1 hx2 using hx (hvanK i δ hδ hδle x hx1 hx2)
      · filter_upwards with x hx1 hx2
        exact absurd (ball_subset_ball (by linarith) hx1) hx2
      · filter_upwards [h2] with x hx hx1 hx2 using hx (hvanK i δ hδ hδle x hx1 hx2)
    rw [← heq]; exact hres
  have hPball : ∀ i, P i ∈ H (ball (c i) r) := by
    intro i
    refine mem_H_ball_of_forall_gt hr fun r' hr' => ?_
    by_cases hlt : r' < r + δ₀
    · have := hPmem i (r' - r) (by linarith) (by linarith)
      rwa [show r + (r' - r) = r' by ring] at this
    · exact H_mono (ball_subset_ball (by linarith)) (hPmem i δ₀ hδ₀ le_rfl)
  have hsum : ∑ i, P i ∈ H (⋃ i, ball (c i) r) :=
    Submodule.sum_mem _ fun i _ => H_mono (Set.subset_iUnion (fun i => ball (c i) r) i) (hPball i)
  -- `w` is the sum of its pieces
  have hweq : w = ∑ i, P i := by
    have hsumE : ∑ i, P i ∈ H (⋃ i, ball (c i) (r + δ₀)) :=
      Submodule.sum_mem _ fun i _ => H_mono (Set.subset_iUnion (fun i => ball (c i) (r + δ₀)) i)
        (hPmem i δ₀ hδ₀ le_rfl)
    refine eq_of_fst_eq (hwE δ₀ hδ₀) hsumE (Lp.ext ?_)
    rw [Prod.fst_sum]
    filter_upwards [L2_coeFn_finset_sum Finset.univ (fun i => (P i).1),
      ae_all_iff.mpr fun i => restrictTo_fst_ae (measurableSet_ball (x := c i) (ε := r + δ₀)) w,
      h] with x hx hall hxK
    rw [hx]
    simp only [hP_def, hall]
    by_cases hmem : ∃ k, x ∈ ball (c k) (r + δ₀)
    · obtain ⟨k, hk⟩ := hmem
      rw [Finset.sum_eq_single k]
      · rw [Set.indicator_of_mem hk]
      · intro i _ hik
        have hx' : x ∉ ball (c i) (r + δ₀) := fun hxi =>
          Set.disjoint_left.mp (hdisjδ δ₀ hδ₀ le_rfl hik) hxi hk
        rw [Set.indicator_of_notMem hx']
      · simp
    · push_neg at hmem
      rw [Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hmem i) _]
      refine hxK fun hK => ?_
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hK
      exact hmem k (closedBall_subset_ball (by linarith) hk)
  rw [hweq]; exact hsum

/-- `L²` limits of functions vanishing off `Ω'ₙ` vanish a.e. off `K` when a.e. point outside `K`
eventually leaves `Ω'ₙ`. -/
lemma ae_zero_of_tendsto_L2 {Ω' : ℕ → Set (RN N)} {K : Set (RN N)} {v : ℕ → L2 N} {f : L2 N}
    (hv : ∀ n, ∀ᵐ x, x ∉ Ω' n → (v n : RN N → ℝ) x = 0) (hf : Tendsto v atTop (𝓝 f))
    (hlim : ∀ᵐ x, x ∉ K → ∀ᶠ n in atTop, x ∉ Ω' n) : ∀ᵐ x, x ∉ K → (f : RN N → ℝ) x = 0 := by
  have hm : TendstoInMeasure volume (fun n => (v n : RN N → ℝ)) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (f := v) (f_lim := f)).mp hf)
  obtain ⟨ns, hns_mono, hns⟩ := hm.exists_seq_tendsto_ae
  have hv' : ∀ᵐ x, ∀ n, x ∉ Ω' n → (v n : RN N → ℝ) x = 0 := ae_all_iff.mpr hv
  filter_upwards [hns, hv', hlim] with x h1 h2 h3 hxK
  have hev : ∀ᶠ i in atTop, (v (ns i) : RN N → ℝ) x = 0 :=
    (hns_mono.tendsto_atTop.eventually (h3 hxK)).mono fun i hi => h2 _ hi
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (hev.mono fun i hi => hi.symm))

/-- **Spectral convergence for shrinking domains.** -/
theorem eigenvalue_tendsto_of_shrinking (hN : 2 ≤ N) {m : ℕ} (hm : 1 ≤ m) (c : Fin m → RN N)
    {r : ℝ} (hr : 0 < r) (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) r))
    {D₀ : Set (RN N)} (hD₀ : IsAdmissible D₀) (Ω : ℕ → Set (RN N))
    (hΩ : ∀ n, IsAdmissible (Ω n)) (hUΩ : ∀ n, (⋃ i, ball (c i) r) ⊆ Ω n)
    (hΩD : ∀ n, Ω n ⊆ D₀)
    (hlim : ∀ᵐ x, x ∉ (⋃ i, closedBall (c i) r) → ∀ᶠ n in atTop, x ∉ Ω n) (j : ℕ) :
    Tendsto (fun n => eigenvalue (Ω n) j) atTop (𝓝 (eigenvalue (⋃ i, ball (c i) r) j)) := by
  set U := ⋃ i, ball (c i) r with hU_def
  have hUadm : IsAdmissible U := ⟨isOpen_iUnion fun _ => isOpen_ball,
    ⟨c ⟨0, hm⟩, Set.mem_iUnion.mpr ⟨_, mem_ball_self hr⟩⟩,
    Bornology.isBounded_iUnion.mpr fun _ => isBounded_ball⟩
  have hup : ∀ n, eigenvalue (Ω n) j ≤ eigenvalue U j := fun n =>
    eigenvalue_domain_mono hN hUadm (hUΩ n) j
  refine tendsto_order.2 ⟨fun μ hμ => ?_, fun b hb => Eventually.of_forall fun n =>
    (hup n).trans_lt hb⟩
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨ψ, hψ, hψμ⟩ := extraction_of_frequently_atTop (hcon.mono fun n hn => not_lt.mp hn)
  have hμ0 : 0 ≤ μ := (eigenvalue_nonneg _ _).trans (hψμ 0)
  choose E hE using fun n => exists_spectralBasis hN (hΩ (ψ n))
  set e : Fin j → ℕ → Amb N := fun k n => E n k with he_def
  have heH : ∀ k n, e k n ∈ H D₀ := fun k n => H_mono (hΩD _) ((hE n).mem_H k)
  have hl2e : ∀ n (k l : Fin j), l2 (e k n) (e l n) = if k = l then 1 else 0 := by
    intro n k l
    simp only [he_def, (hE n).2.1, Fin.val_inj]
  have hqe : ∀ n (k l : Fin j), qf (e k n) (e l n) =
      eigenvalue (Ω (ψ n)) ((k : ℕ) + 1) * (if k = l then 1 else 0) := by
    intro n k l
    rw [((hE n).1 k).2.2 _ ((hE n).mem_H l), ← hl2e n k l]
  have hlamk : ∀ n (k : Fin j), eigenvalue (Ω (ψ n)) ((k : ℕ) + 1) ≤ μ := fun n k =>
    (eigenvalue_mono hN (hΩ (ψ n)) (Nat.le_add_left 1 k) (by omega)).trans (hψμ n)
  have hlam0 : ∀ n (k : Fin j), 0 ≤ eigenvalue (Ω (ψ n)) ((k : ℕ) + 1) := fun n k =>
    eigenvalue_nonneg _ _
  -- energy of combinations
  have hqcomb : ∀ (a : Fin j → ℝ) n, qf (∑ k, a k • e k n) (∑ k, a k • e k n) ≤
      μ * ∑ k, a k ^ 2 := by
    intro a n
    simp only [qf_sum_left, qf_sum_right, qf_smul_left, qf_smul_right, hqe]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl, ]) (by simp)]
    simp only [if_true, mul_one]
    nlinarith [hlamk n k, sq_nonneg (a k)]
  -- boundedness
  have hb : ∃ C, ∀ k n, ‖e k n‖ ≤ C := by
    refine ⟨1 + μ, fun k n => ?_⟩
    have h1 : ‖(e k n).1‖ = 1 := by
      have := hl2e n k k
      simp only [if_true, l2] at this
      rw [real_inner_self_eq_norm_sq] at this
      nlinarith [norm_nonneg (e k n).1]
    have h2 : ‖(e k n).2‖ ^ 2 ≤ μ := by
      have := hqe n k k
      simp only [if_true, mul_one, qf] at this
      rw [real_inner_self_eq_norm_sq] at this
      rw [this]; exact hlamk n k
    rw [Prod.norm_def]
    refine max_le (by rw [h1]; linarith) ?_
    nlinarith [norm_nonneg (e k n).2]
  obtain ⟨φ, hφ, f, hf⟩ := common_subseq hN hD₀ j e heH hb
  -- orthonormality of the limits
  have hforth : ∀ k l : Fin j, ⟪f k, f l⟫ = if k = l then 1 else 0 := by
    intro k l
    have h := (Filter.Tendsto.inner (𝕜 := ℝ) (hf k) (hf l))
    have : (fun n => ⟪(e k (φ n)).1, (e l (φ n)).1⟫) = fun _ => if k = l then (1 : ℝ) else 0 := by
      funext n; exact hl2e (φ n) k l
    rw [this] at h
    exact tendsto_nhds_unique tendsto_const_nhds h |>.symm
  -- lifts
  have hlift : ∀ a : Fin j → ℝ, ∃ w ∈ H D₀, w.1 = ∑ k, a k • f k ∧ qf w w ≤ μ * ∑ k, a k ^ 2 := by
    intro a
    refine lift_of_tendsto hN hD₀ (v := fun n => ∑ k, a k • e k (φ n))
      (fun n => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (heH k _))
      (fun n => hqcomb a (φ n)) ?_
    simp only [Prod.fst_sum, Prod.smul_fst]
    exact tendsto_finsetSum _ fun k _ => (hf k).const_smul (a k)
  choose w hwH hw1 hwq using fun k : Fin j => hlift (Pi.single k 1)
  have hw1' : ∀ k, (w k).1 = f k := fun k => by
    rw [hw1 k]; simp [Pi.single_apply]
  -- the limits vanish outside the closed balls
  have hfvan : ∀ k, ∀ᵐ x, x ∉ (⋃ i, closedBall (c i) r) → (f k : RN N → ℝ) x = 0 := by
    intro k
    refine ae_zero_of_tendsto_L2 (Ω' := fun n => Ω (ψ (φ n))) (fun n => ?_) (hf k)
      (by filter_upwards [hlim] with x hx hxK using
        ((hψ.comp hφ).tendsto_atTop.eventually (hx hxK)))
    have hmem := (hE (φ n)).mem_H k
    obtain ⟨h1, -⟩ := mem_vanishOn.mp (H_le_vanishOn _ hmem)
    rw [EventuallyEq, ae_restrict_iff' (hΩ _).1.measurableSet.compl] at h1
    exact h1
  have hwU : ∀ k, w k ∈ H U := fun k =>
    mem_H_iUnion_ball_of_vanish c hr hdisj (hwH k) (by rw [hw1' k]; exact hfvan k)
  -- the trial space
  let T : (Fin j → ℝ) →ₗ[ℝ] Amb N :=
    { toFun := fun a => ∑ k, a k • w k
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t a => by simp [Finset.smul_sum, smul_smul] }
  have hT1 : ∀ a, (T a).1 = ∑ k, a k • f k := fun a => by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_sum, Prod.smul_fst, hw1']
  have hl2T : ∀ a, l2 (T a) (T a) = ∑ k, a k ^ 2 := by
    intro a
    simp only [l2, hT1, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hforth]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl, ]) (by simp)]
    simp; ring
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h0 := hl2T a
    rw [ha, l2_zero_left] at h0
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).mp h0.symm k
      (Finset.mem_univ _)
    simpa using this
  have hTH : ∀ a, T a ∈ H U := fun a => show ∑ k, a k • w k ∈ H U from
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hwU k)
  have hTq : ∀ a, qf (T a) (T a) ≤ μ * l2 (T a) (T a) := by
    intro a
    obtain ⟨w', hw'H, hw'1, hw'q⟩ := hlift a
    have heq : T a = w' := eq_of_fst_eq (D := D₀) (H_mono (hΩD 0 |>.trans' (hUΩ 0)) (hTH a))
      hw'H (by rw [hT1, hw'1])
    rw [heq, ← heq, hl2T, heq]; exact hw'q
  have hle : eigenvalue U j ≤ μ := by
    refine eigenvalue_le_of_subspace (V := LinearMap.range T) ?_ ?_ hμ0 ?_
    · rintro _ ⟨a, rfl⟩; exact hTH a
    · rw [LinearMap.finrank_range_of_inj hTinj]; simp
    · rintro _ ⟨a, rfl⟩; exact hTq a
  linarith

end FourthRatio

end

module

public import RequestProject.Localization
public import RequestProject.InteriorAnalytic

/-!
# Parts of the external theorems that follow from the others

Several statements of Section 2 follow from the definitions and the spectral and interior
analyticity results proved in the project; they are derived here.

* `eigenvalue_domain_mono` — domain monotonicity `D₁ ⊆ D₂ ⇒ λ_j(D₂) ≤ λ_j(D₁)` (part of the
  spectral package): it follows from the min–max definition, `H_{D₁} ≤ H_{D₂}`, and the existence
  of `j`-dimensional subspaces of `H_{D₁}` (spans of eigenfunctions).
* `compact_embedding` — compactness of the embedding `H_D ↪ L²(D)` (part of the spectral
  package): it follows from the spectral expansions of `ext_spectral` and `λ_j → ∞`, since the
  `L²` distance from `v` to its projection onto the first `n` eigenfunctions is at most
  `√(q(v,v)/λ_{n+1})`, so a bounded set in `H_D` is totally bounded in `L²`.
* `ucp` — unique continuation: it follows from interior analyticity (`ext_analytic`) and the
  identity theorem for real-analytic functions on the connected set `D`.
* `ucp_nonvanishing` — a nonzero Dirichlet eigenfunction of a domain cannot vanish on a
  nonempty open subset (the special case of unique continuation): it follows from `ucp`
  applied with `v = 0`, together with closability.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **Domain monotonicity of Dirichlet eigenvalues.** If `D₁ ⊆ D₂` then
`λ_j(D₂) ≤ λ_j(D₁)`. -/
theorem eigenvalue_domain_mono (hN : 2 ≤ N) {D₁ D₂ : Set (RN N)} (h₁ : IsAdmissible D₁)
    (h : D₁ ⊆ D₂) (j : ℕ) :
    eigenvalue D₂ j ≤ eigenvalue D₁ j := by
  obtain ⟨e, he⟩ := exists_spectralBasis hN h₁
  refine csInf_le_csInf ?_ ⟨_, ⟨eigSpan e j, ⟨he.eigSpan_le j, he.finrank_eigSpan j⟩, rfl⟩⟩ ?_
  · exact ⟨0, by rintro _ ⟨V, -, rfl⟩; exact sSup_rayleigh_nonneg V⟩
  · rintro _ ⟨V, ⟨hV, hVj⟩, rfl⟩
    exact ⟨V, ⟨hV.trans (H_mono h), hVj⟩, rfl⟩

/-- Tail estimate: the `L²` distance from `v` to its projection onto the first `n`
eigenfunctions is controlled by `q(v,v) / λ_{n+1}`. -/
lemma IsSpectralBasis.tail_le (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D)
    {e : ℕ → Amb N} (he : IsSpectralBasis D e) {v : Amb N} (hv : v ∈ H D) (n : ℕ) :
    eigenvalue D (n + 1) * l2 (v - ∑ i : Fin n, l2 v (e i) • e i)
      (v - ∑ i : Fin n, l2 v (e i) • e i) ≤ qf v v := by
  set w := v - ∑ i : Fin n, l2 v (e i) • e i with hw
  have hwH : w ∈ H D := Submodule.sub_mem _ hv
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he.mem_H i))
  have hcoef : ∀ j, l2 w (e j) = if j < n then 0 else l2 v (e j) := by
    intro j
    rw [hw, l2_sub_left, l2_sum_left]
    simp only [l2_smul_left, he.2.1]
    split_ifs with hj
    · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
        simp [this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp
      · intro b _
        have : (b : ℕ) ≠ j := fun h => hj (h ▸ b.2)
        simp [this]
  have hl := (he.2.2 w hwH).2
  have hq := (he.2.2 v hv).1
  have := hasSum_le (f := fun j => eigenvalue D (n + 1) * l2 w (e j) ^ 2) ?_
    (hl.mul_left (eigenvalue D (n + 1))) hq
  · exact this
  intro j
  show eigenvalue D (n + 1) * l2 w (e j) ^ 2 ≤ _
  rw [hcoef j]
  split_ifs with hj
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg (eigenvalue_nonneg D _) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (eigenvalue_mono hN hD (Nat.le_add_left 1 n) (by omega)) (sq_nonneg _)

/-- **Compactness of `H_D ↪ L²(D)`.** Bounded sequences in `H_D` have `L²`-convergent
subsequences. -/
theorem compact_embedding (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D)
    (v : ℕ → Amb N) (hv : ∀ n, v n ∈ H D) (hb : ∃ C, ∀ n, ‖v n‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : L2 N, Tendsto (fun n => (v (φ n)).1) atTop (𝓝 f) := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨e, he1, he2, -, -, htend, hsum⟩ := ext_spectral hN hD
  have he : IsSpectralBasis D e := ⟨he1, he2, hsum⟩
  have hTB : TotallyBounded (Set.range fun k => (v k).1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop (4 * C ^ 2 / ε ^ 2)).exists
    let L : (Fin n → ℝ) →L[ℝ] L2 N :=
      ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (e i).1
    have hK : IsCompact (L '' closedBall 0 C) := (isCompact_closedBall 0 C).image L.continuous
    obtain ⟨t, htfin, hcover⟩ :=
      Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 2) (by positivity)
    refine ⟨t, htfin, ?_⟩
    rintro _ ⟨k, rfl⟩
    let c : Fin n → ℝ := fun i => l2 (v k) (e i)
    have hnorm_e : ∀ i, ‖(e i).1‖ = 1 := by
      intro i
      have h := he2 i i
      rw [if_pos rfl, l2, real_inner_self_eq_norm_sq] at h
      have := norm_nonneg (e i).1
      nlinarith
    have hc : c ∈ closedBall 0 C := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hC0]
      intro i
      rw [Real.norm_eq_abs]
      calc |c i| ≤ ‖(v k).1‖ * ‖(e i).1‖ := abs_real_inner_le_norm _ _
        _ ≤ C := by rw [hnorm_e, mul_one]; exact (norm_fst_le _).trans (hC k)
    have hLc : L c = (∑ i : Fin n, c i • e i).1 := by
      simp [L, Prod.fst_sum, c]
    obtain ⟨y, hy, hdist⟩ := Set.mem_iUnion₂.mp (hcover ⟨c, hc, rfl⟩)
    refine Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    have htail := he.tail_le hN hD (hv k) n
    set w := v k - ∑ i : Fin n, l2 (v k) (e i) • e i with hw
    have hw1 : dist (v k).1 (L c) = ‖w.1‖ := by
      rw [dist_eq_norm, hLc, hw, Prod.fst_sub]
    have hl2 : l2 w w = ‖w.1‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hq : qf (v k) (v k) ≤ C ^ 2 := by
      rw [qf, real_inner_self_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_snd_le _).trans (hC k)) 2
    rw [hl2] at htail
    have hlpos : 4 * C ^ 2 < eigenvalue D (n + 1) * ε ^ 2 := by
      rwa [div_lt_iff₀ (by positivity)] at hn
    have hsmall : ‖w.1‖ < ε / 2 := by
      by_contra hcon
      push_neg at hcon
      have h1 : (ε / 2) ^ 2 ≤ ‖w.1‖ ^ 2 := pow_le_pow_left₀ (by positivity) hcon 2
      have h2 : 0 ≤ eigenvalue D (n + 1) := eigenvalue_nonneg D _
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    rw [mem_ball] at hdist ⊢
    calc dist (v k).1 y ≤ dist (v k).1 (L c) + dist (L c) y := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by rw [hw1]; exact add_lt_add hsmall hdist
      _ = ε := by ring
  obtain ⟨f, -, φ, hφ, hlim⟩ :=
    (TotallyBounded.isCompact_of_isClosed hTB.closure isClosed_closure).tendsto_subseq (fun k => subset_closure ⟨k, rfl⟩)
  exact ⟨φ, hφ, f, hlim⟩

/-- **Unique continuation.** Two weak solutions of `-Δw = λw` in `H_D` (with the same `λ`)
that agree on a nonempty open subset of the domain `D` agree on all of `D`. -/
theorem ucp {D : Set (RN N)} (hD : IsDomain D) {u v : Amb N} {lam : ℝ}
    (hu : u ∈ H D) (hu' : ∀ φ ∈ H D, qf u φ = lam * l2 u φ)
    (hv : v ∈ H D) (hv' : ∀ φ ∈ H D, qf v φ = lam * l2 v φ)
    {U : Set (RN N)} (hU : IsOpen U) (hUne : U.Nonempty) (hUD : U ⊆ D)
    (heq : (u.1 : RN N → ℝ) =ᵐ[volume.restrict U] v.1) :
    (u.1 : RN N → ℝ) =ᵐ[volume.restrict D] v.1 := by
  obtain ⟨f, hfa, hfc, hfu⟩ := ext_analytic hD hu hu'
  obtain ⟨g, hga, hgc, hgv⟩ := ext_analytic hD hv hv'
  have h1 : (u.1 : RN N → ℝ) =ᵐ[volume.restrict U] f := ae_restrict_of_ae_restrict_of_subset hUD hfu
  have h2 : (v.1 : RN N → ℝ) =ᵐ[volume.restrict U] g := ae_restrict_of_ae_restrict_of_subset hUD hgv
  have hUfg : (f =ᵐ[volume.restrict U] g) := (h1.symm.trans heq).trans h2
  have hEqU : Set.EqOn f g U :=
    Measure.eqOn_open_of_ae_eq hUfg hU (hfc.mono hUD) (hgc.mono hUD)
  obtain ⟨z, hz⟩ := hUne
  have hloc : f =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hU.mem_nhds hz) hEqU
  have hEqD : Set.EqOn f g D :=
    hfa.eqOn_of_preconnected_of_eventuallyEq hga hD.2.isPreconnected (hUD hz) hloc
  have hfgD : f =ᵐ[volume.restrict D] g :=
    (ae_restrict_mem hD.1.1.measurableSet).mono fun x hx => hEqD hx
  exact (hfu.trans hfgD).trans hgv.symm

/-- **Unique continuation, special case.** A nonzero Dirichlet eigenfunction of a domain cannot
vanish (almost everywhere) on a nonempty open subset. -/
theorem ucp_nonvanishing {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    {lam : ℝ} (hu : IsEigenfunction D u lam)
    {U : Set (RN N)} (hU : IsOpen U) (hUne : U.Nonempty) (hUD : U ⊆ D) :
    ¬ ((u.1 : RN N → ℝ) =ᵐ[volume.restrict U] 0) := by
  intro h0
  have hz : ((0 : Amb N).1 : RN N → ℝ) =ᵐ[volume] 0 := by
    simpa using (Lp.coeFn_zero ℝ 2 (volume : Measure (RN N)))
  have hD' := ucp hD (lam := lam) hu.1 hu.2.2 (H D).zero_mem
    (fun φ _ => by simp [qf, l2]) hU hUne hUD (h0.trans (EventuallyEq.symm (ae_restrict_of_ae hz)))
  have hDc := (mem_vanishOn.mp (H_le_vanishOn D hu.1)).1
  have hall : (u.1 : RN N → ℝ) =ᵐ[volume] 0 := by
    have := ae_restrict_union_iff (μ := volume) D Dᶜ
      (fun x => (u.1 : RN N → ℝ) x = (0 : RN N → ℝ) x)
    rw [Set.union_compl_self, Measure.restrict_univ] at this
    exact this.mpr ⟨EventuallyEq.trans hD' (ae_restrict_of_ae hz), hDc⟩
  have h1 : u.1 = 0 := Lp.eq_zero_iff_ae_eq_zero.mpr hall
  exact hu.2.1 (eq_zero_of_l2_self_eq_zero hu.1 (by simp [l2, h1]))

end FourthRatio

end

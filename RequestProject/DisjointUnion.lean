module

public import RequestProject.SobolevTools

/-!
# Form domain of a disjoint union

The first clause of the paper's disjoint-union statement: for pairwise disjoint open sets
`Dᵢ`, the form domain of the union is the closure of the sum of the form domains,
`H(⋃ Dᵢ) = closure (⨆ H(Dᵢ))`.  This is proved here directly from the definition of `H_D` as
the closure of the test graph: a test function on the union has compact support, which meets
only finitely many `Dᵢ`, and it splits as the finite sum of its restrictions to these `Dᵢ`,
each of which is again a test function.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- `p` is represented by the smooth function `φ` (function and gradient). -/
def RepBy (p : Amb N) (φ : RN N → ℝ) : Prop :=
  (p.1 : RN N → ℝ) =ᵐ[volume] φ ∧ (p.2 : RN N → RN N) =ᵐ[volume] gradient φ

lemma RepBy.unique {p q : Amb N} {φ : RN N → ℝ} (hp : RepBy p φ) (hq : RepBy q φ) : p = q := by
  refine Prod.ext ?_ ?_
  · exact Lp.ext (hp.1.trans hq.1.symm)
  · exact Lp.ext (hp.2.trans hq.2.symm)

lemma RepBy.add {p q : Amb N} {φ ψ : RN N → ℝ} (hp : RepBy p φ) (hq : RepBy q ψ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    RepBy (p + q) (fun y => φ y + ψ y) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [Lp.coeFn_add p.1 q.1, hp.1, hq.1] with x a b c
    simp only [Prod.fst_add] at a ⊢
    rw [a, Pi.add_apply, b, c]
  · filter_upwards [Lp.coeFn_add p.2 q.2, hp.2, hq.2] with x a b c
    rw [Prod.snd_add, a, Pi.add_apply, b, c, gradient_add_of_contDiff hφ hψ]

lemma RepBy.zero : RepBy (0 : Amb N) (fun _ => 0) := by
  refine ⟨Lp.coeFn_zero _ _ _, ?_⟩
  have : gradient (fun _ : RN N => (0 : ℝ)) = 0 := by
    ext1 x; simp [gradient]
  rw [this]; exact Lp.coeFn_zero _ _ _

/-- The restriction of a test function to one of disjoint open sets, finitely many of which
cover its support, is again a test function. -/
lemma testFn_restrict {ι : Type*} {D : ι → Set (RN N)} (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D)) {φ : RN N → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) {F : Finset ι}
    (hF : tsupport φ ⊆ ⋃ i ∈ F, D i) (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((D i).indicator φ) ∧
      HasCompactSupport ((D i).indicator φ) ∧ tsupport ((D i).indicator φ) ⊆ D i := by
  classical
  set K := tsupport φ ∩ D i with hK
  have hKeq : K = tsupport φ \ ⋃ j ∈ F.erase i, D j := by
    ext y
    simp only [K, Set.mem_inter_iff, Set.mem_diff, Set.mem_iUnion, Finset.mem_erase,
      exists_prop, not_exists, not_and]
    constructor
    · rintro ⟨hy, hyi⟩
      refine ⟨hy, fun j ⟨hji, _⟩ hyj => ?_⟩
      exact Set.disjoint_left.mp (hdisj (Ne.symm hji)) hyi hyj
    · rintro ⟨hy, hno⟩
      refine ⟨hy, ?_⟩
      have := hF hy
      simp only [Set.mem_iUnion, exists_prop] at this
      obtain ⟨j, hjF, hyj⟩ := this
      by_cases hji : j = i
      · exact hji ▸ hyj
      · exact absurd hyj (hno j ⟨hji, hjF⟩)
  have hKc : IsClosed K := by
    rw [hKeq]
    exact (isClosed_tsupport φ).sdiff
      (isOpen_biUnion fun j _ => hD j)
  have hsupp : support ((D i).indicator φ) ⊆ K := by
    intro y hy
    rw [mem_support, Set.indicator_apply_ne_zero] at hy
    exact ⟨subset_tsupport φ hy.2, hy.1⟩
  have hts : tsupport ((D i).indicator φ) ⊆ K := closure_minimal hsupp hKc
  refine ⟨?_, hφc.mono' (hsupp.trans Set.inter_subset_left), hts.trans Set.inter_subset_right⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ D i
  · refine (hφ.contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [(hD i).mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy φ
  · have hxK : x ∉ K := fun h => hx h.2
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hKc.isOpen_compl.mem_nhds hxK] with y hy
    by_contra hne
    exact hy (hsupp hne)

/-- An element of the test graph of a disjoint union of open sets lies in the sum of the form
domains of the pieces. -/
lemma testGraph_iUnion_le {ι : Type*} {D : ι → Set (RN N)} (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D)) {p : Amb N} (hp : p ∈ testGraph (⋃ i, D i)) :
    p ∈ ⨆ i, H (D i) := by
  classical
  obtain ⟨φ, hφ, hφc, hφs, h1, h2⟩ := hp
  obtain ⟨F, hF⟩ := hφc.isCompact.elim_finite_subcover D hD hφs
  have hpiece : ∀ i ∈ F, ∃ q : Amb N, q ∈ H (D i) ∧ RepBy q ((D i).indicator φ) := by
    intro i hi
    obtain ⟨c1, c2, c3⟩ := testFn_restrict hD hdisj hφ hφc hF i
    have m1 : MemLp ((D i).indicator φ) 2 (volume : Measure (RN N)) :=
      c1.continuous.memLp_of_hasCompactSupport c2
    have m2 : MemLp (gradient ((D i).indicator φ)) 2 (volume : Measure (RN N)) := by
      refine Continuous.memLp_of_hasCompactSupport ?_ ?_
      · have : gradient ((D i).indicator φ) =
            (fun L => (InnerProductSpace.toDual ℝ (RN N)).symm L) ∘ fderiv ℝ ((D i).indicator φ) := by
          ext1 x; rfl
        rw [this]
        exact (InnerProductSpace.toDual ℝ (RN N)).symm.continuous.comp
          (c1.continuous_fderiv (by simp))
      · have : gradient ((D i).indicator φ) =
            (fun L => (InnerProductSpace.toDual ℝ (RN N)).symm L) ∘ fderiv ℝ ((D i).indicator φ) := by
          ext1 x; rfl
        rw [this]
        exact (c2.fderiv (𝕜 := ℝ)).comp_left (map_zero _)
    refine ⟨(m1.toLp _, m2.toLp _), testGraph_subset_H _ ?_, m1.coeFn_toLp, m2.coeFn_toLp⟩
    exact ⟨_, c1, c2, c3, m1.coeFn_toLp, m2.coeFn_toLp⟩
  choose! q hqH hqR using hpiece
  have hsum : ∀ G ⊆ F, RepBy (∑ i ∈ G, q i) (fun y => ∑ i ∈ G, (D i).indicator φ y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ i ∈ G, (D i).indicator φ y) := by
    intro G
    induction G using Finset.induction_on with
    | empty => intro _; simpa using ⟨RepBy.zero, contDiff_const⟩
    | insert j G hj ih =>
      intro hG
      have hjF : j ∈ F := hG (Finset.mem_insert_self _ _)
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hG)
      have cj := (testFn_restrict hD hdisj hφ hφc hF j).1
      simp only [Finset.sum_insert hj]
      exact ⟨(hqR j hjF).add ih1 cj ih2, cj.add ih2⟩
  have hφeq : (fun y => ∑ i ∈ F, (D i).indicator φ y) = φ := by
    ext y
    by_cases hy : y ∈ tsupport φ
    · have := hF hy
      simp only [Set.mem_iUnion, exists_prop] at this
      obtain ⟨j, hjF, hyj⟩ := this
      rw [Finset.sum_eq_single j]
      · exact Set.indicator_of_mem hyj φ
      · intro b _ hbj
        exact Set.indicator_of_notMem
          (fun hb => Set.disjoint_left.mp (hdisj hbj) hb hyj) φ
      · intro h; exact absurd hjF h
    · have h0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [h0]
      exact Finset.sum_eq_zero fun i _ => by simp [Set.indicator_apply, h0]
  have hrep := (hsum F subset_rfl).1
  rw [hφeq] at hrep
  have : p = ∑ i ∈ F, q i := RepBy.unique ⟨h1, h2⟩ hrep
  rw [this]
  exact Submodule.sum_mem _ fun i hi => (le_iSup (fun i => H (D i)) i) (hqH i hi)

/-- **Form domain of a disjoint union** (first clause of the disjoint-union part of the
spectral package): for pairwise disjoint open sets, `H(⋃ Dᵢ) = closure (⨆ H(Dᵢ))`. -/
theorem H_iUnion_of_disjoint {ι : Type*} (D : ι → Set (RN N)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D)) :
    H (⋃ i, D i) = (⨆ i, H (D i)).topologicalClosure := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_mono
      (Submodule.span_le.mpr fun p hp => testGraph_iUnion_le hD hdisj hp)
  · exact Submodule.topologicalClosure_minimal _
      (iSup_le fun i => H_mono (Set.subset_iUnion D i))
      (Submodule.isClosed_topologicalClosure _)

end FourthRatio

end

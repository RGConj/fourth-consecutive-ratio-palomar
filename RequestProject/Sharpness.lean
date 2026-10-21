module

public import RequestProject.Components
public import RequestProject.TubeChain

/-!
# Disconnected sets and sharpness (Section 6 of the paper)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **Corollary 6.1, upper bound.** For `m ∈ {1,2,3,4}` and every `D ∈ 𝒪_N`,
`λ_{m+1}(D) ≤ C_N λ_m(D)`. -/
theorem cor_upper (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N)
    (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {D : Set (RN N)}
    (hD : IsAdmissible D) : eigenvalue D (m + 1) ≤ CN N * eigenvalue D m := by
  by_contra h
  push_neg at h
  obtain ⟨C, hC⟩ := exists_comp_le hN hD hm1
  have := (comp_analysis hppw hppwEq hN hD hm1 hm4 h.le le_rfl C hC).2.2
  linarith

/-- Necessity in Corollary 6.1. -/
lemma cor_equality_mp (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N)
    (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {D : Set (RN N)}
    (hD : IsAdmissible D) (heq : eigenvalue D (m + 1) = CN N * eigenvalue D m) :
    ∃ (x y : Fin m → RN N) (R : ℝ), 0 < R ∧ (∀ i, x i ∈ D) ∧
      Pairwise (fun i j => connectedComponentIn D (x i) ≠ connectedComponentIn D (x j)) ∧
      (∀ i, H (connectedComponentIn D (x i)) = H (ball (y i) R) ∧
        eigenvalue (connectedComponentIn D (x i)) 1 = eigenvalue D m) ∧
      ∀ z ∈ D, (∀ i, connectedComponentIn D z ≠ connectedComponentIn D (x i)) →
        CN N * eigenvalue D m ≤ eigenvalue (connectedComponentIn D z) 1 := by
  have ha0 : 0 < eigenvalue D m := eigenvalue_pos hN hD hm1
  have hC1 := one_lt_CN hN
  have hT1 : CN N * eigenvalue D m ≤ eigenvalue D (m + 1) := heq.ge
  let Sset : Set (comps D) := {C | eigenvalue (C : Set (RN N)) 1 ≤ eigenvalue D m}
  have hcomp : ∀ C : comps D, C ∈ Sset → eigenvalue (C : Set (RN N)) 1 = eigenvalue D m ∧
      eigenvalue (C : Set (RN N)) 2 = CN N * eigenvalue D m := fun C hC =>
    ⟨(comp_analysis hppw hppwEq hN hD hm1 hm4 hT1 le_rfl C hC).1,
      (comp_analysis hppw hppwEq hN hD hm1 hm4 hT1 le_rfl C hC).2.1⟩
  have haT : eigenvalue D m < eigenvalue D (m + 1) := by rw [heq]; nlinarith
  have hcount := eigCount_eq_of_gap hN hD hm1 le_rfl haT
  rw [eigCount_eq_pairs hN hD] at hcount
  have hpairs : pairs (fun C : comps D => (C : Set (RN N))) (eigenvalue D m) =
      (fun C => (C, 1)) '' Sset := by
    ext ⟨C, j⟩
    simp only [pairs, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨hj, hle⟩
      have hCa := (isDomain_of_mem_comps hD C.2).1
      have hC1' : eigenvalue (C : Set (RN N)) 1 ≤ eigenvalue D m :=
        (eigenvalue_mono hN hCa le_rfl hj).trans hle
      refine ⟨C, hC1', rfl, ?_⟩
      by_contra hj1
      have h2 := eigenvalue_mono hN hCa (by norm_num : 1 ≤ 2) (by omega : 2 ≤ j)
      rw [(hcomp C hC1').2] at h2
      nlinarith
    · rintro ⟨C', hC', rfl, rfl⟩
      exact ⟨le_rfl, hC'⟩
  have hinj : Injective (fun C : comps D => (C, (1 : ℕ))) := fun C C' h => (Prod.mk.inj h).1
  have hSenc : Sset.encard = m := by
    rw [← hcount, hpairs, hinj.injOn.encard_image]
  have hfin : Sset.Finite := Set.finite_of_encard_eq_coe hSenc
  have hcard : hfin.toFinset.card = m := by
    have := hfin.encard_eq_coe_toFinset_card
    rw [hSenc] at this
    exact_mod_cast this.symm
  let F := hfin.toFinset
  let f : Fin m → comps D := fun i => (F.equivFin.symm (Fin.cast hcard.symm i)).1
  have hfinj : Injective f := by
    intro i j h
    have := Subtype.ext h
    simpa using this
  have hfS : ∀ i, f i ∈ Sset := fun i => hfin.mem_toFinset.mp (F.equivFin.symm _).2
  have hSf : ∀ C ∈ Sset, ∃ i, f i = C := by
    intro C hC
    refine ⟨Fin.cast hcard (F.equivFin ⟨C, hfin.mem_toFinset.mpr hC⟩), ?_⟩
    simp [f]
  have hx : ∀ i, ∃ x ∈ D, connectedComponentIn D x = (f i : Set (RN N)) := fun i => (f i).2
  choose x hxD hxeq using hx
  have hdom : ∀ i, IsDomain (connectedComponentIn D (x i)) := fun i =>
    isDomain_of_mem_comps hD ⟨x i, hxD i, rfl⟩
  have hlam : ∀ i, eigenvalue (connectedComponentIn D (x i)) 1 = eigenvalue D m ∧
      eigenvalue (connectedComponentIn D (x i)) 2 = CN N * eigenvalue D m := by
    intro i; rw [hxeq i]; exact hcomp _ (hfS i)
  have hppw : ∀ i, ∃ (y : RN N) (R : ℝ), 0 < R ∧
      eigenvalue (ball y R) 1 = eigenvalue (connectedComponentIn D (x i)) 1 ∧
      H (connectedComponentIn D (x i)) = H (ball y R) := fun i =>
    hppwEq (hdom i) (by rw [(hlam i).1, (hlam i).2])
  choose y R' hR' hlamR hH using hppw
  set R := besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt (eigenvalue D m)
  have hRR : ∀ i, R' i = R := fun i =>
    ball_radius_eq hN (hR' i) ha0 ((hlamR i).trans (hlam i).1)
  refine ⟨x, y, R, ?_, hxD, ?_, fun i => ⟨?_, (hlam i).1⟩, ?_⟩
  · rw [← hRR ⟨0, hm1⟩]; exact hR' _
  · intro i j hij h
    rw [hxeq i, hxeq j] at h
    exact hij (hfinj (Subtype.ext h))
  · rw [hH i, hRR i]
  · intro z hz hne
    by_contra hlt
    push_neg at hlt
    let C : comps D := ⟨connectedComponentIn D z, z, hz, rfl⟩
    have hle := comp_eig_le hN hD hm1 hT1 C le_rfl hlt
    obtain ⟨i, hi⟩ := hSf C hle
    exact hne i (by rw [hxeq i, hi])

/-- Sufficiency in Corollary 6.1. -/
lemma cor_equality_mpr (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) {D : Set (RN N)}
    (hD : IsAdmissible D) (x y : Fin m → RN N) (R : ℝ) (hR : 0 < R) (hxD : ∀ i, x i ∈ D)
    (hpw : Pairwise (fun i j => connectedComponentIn D (x i) ≠ connectedComponentIn D (x j)))
    (hball : ∀ i, H (connectedComponentIn D (x i)) = H (ball (y i) R) ∧
      eigenvalue (connectedComponentIn D (x i)) 1 = eigenvalue D m)
    (hother : ∀ z ∈ D, (∀ i, connectedComponentIn D z ≠ connectedComponentIn D (x i)) →
      CN N * eigenvalue D m ≤ eigenvalue (connectedComponentIn D z) 1) :
    eigenvalue D (m + 1) = CN N * eigenvalue D m := by
  have ha0 : 0 < eigenvalue D m := eigenvalue_pos hN hD hm1
  have hC1 := one_lt_CN hN
  have haT : eigenvalue D m < CN N * eigenvalue D m := by nlinarith
  let e : Fin m → comps D := fun i => ⟨connectedComponentIn D (x i), x i, hxD i, rfl⟩
  have he : Injective e := by
    intro i j h
    by_contra hij
    exact hpw hij (congrArg Subtype.val h)
  have hspec : ∀ i, eigenvalue ((e i : comps D) : Set (RN N)) 1 = eigenvalue D m ∧
      eigenvalue ((e i : comps D) : Set (RN N)) 2 = CN N * eigenvalue D m := by
    intro i
    refine ⟨(hball i).2, ?_⟩
    change eigenvalue (connectedComponentIn D (x i)) 2 = _
    rw [eigenvalue_congr (hball i).1 2, eigenvalue_two_ball hN (y i) hR,
      ← eigenvalue_congr (hball i).1 1, (hball i).2]
  have hoth : ∀ c : comps D, c ∉ Set.range e →
      CN N * eigenvalue D m ≤ eigenvalue (c : Set (RN N)) 1 := by
    rintro ⟨C, z, hz, rfl⟩ hc
    refine hother z hz fun i h => hc ⟨i, Subtype.ext ?_⟩
    exact h.symm
  obtain ⟨h0, hmid, htop⟩ := pairs_special hN (fun C : comps D => (C : Set (RN N)))
    (fun C => (isDomain_of_mem_comps hD C.2).1) e he haT hspec hoth
  refine (eig_of_counts hN hD hm1 haT (fun s hs => ?_) (fun s hs1 hs2 => ?_) ?_).2
  · rw [eigCount_eq_pairs hN hD, h0 s hs, Set.encard_empty]
    exact_mod_cast hm1
  · rw [eigCount_eq_pairs hN hD, hmid s hs1 hs2]
  · rw [eigCount_eq_pairs hN hD]; exact htop hm1

/-- **Corollary 6.1, equality classification.** For `m ∈ {1,2,3,4}` and `D ∈ 𝒪_N`, equality
`λ_{m+1}(D) = C_N λ_m(D)` holds iff there are `m` distinct connected components `D₁,…,D_m` of
`D` and congruent balls `B₁,…,B_m` with `H₀¹(Dᵢ) = H₀¹(Bᵢ)` and `λ₁(Dᵢ) = λ_m(D)`, while every
other component `D'` satisfies `λ₁(D') ≥ C_N λ_m(D)`. -/
theorem cor_equality (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N)
    (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {D : Set (RN N)}
    (hD : IsAdmissible D) :
    eigenvalue D (m + 1) = CN N * eigenvalue D m ↔
      ∃ (x y : Fin m → RN N) (R : ℝ), 0 < R ∧ (∀ i, x i ∈ D) ∧
        Pairwise (fun i j => connectedComponentIn D (x i) ≠ connectedComponentIn D (x j)) ∧
        (∀ i, H (connectedComponentIn D (x i)) = H (ball (y i) R) ∧
          eigenvalue (connectedComponentIn D (x i)) 1 = eigenvalue D m) ∧
        ∀ z ∈ D, (∀ i, connectedComponentIn D z ≠ connectedComponentIn D (x i)) →
          CN N * eigenvalue D m ≤ eigenvalue (connectedComponentIn D z) 1 :=
  ⟨cor_equality_mp hppw hppwEq hN hm1 hm4 hD, fun ⟨x, y, R, hR, hxD, hpw, hball, hother⟩ =>
    cor_equality_mpr hN hm1 hD x y R hR hxD hpw hball hother⟩

/-- **Corollary 6.2 (Sharpness among smooth connected domains).** For `m ∈ {1,2,3,4}`,
`sup λ_{m+1}(Ω)/λ_m(Ω) = C_N`, the supremum being over bounded domains with smooth boundary. -/
theorem cor_sharpness (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N)
    (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    IsLUB {r : ℝ | ∃ Ω : Set (RN N), IsDomain Ω ∧ HasSmoothBoundary Ω ∧
      r = eigenvalue Ω (m + 1) / eigenvalue Ω m} (CN N) := by
  have hC1 := one_lt_CN hN
  obtain ⟨Φ', _, _, _, _, _, hr, _, _, hb⟩ := ext_ball hN (one_pos : (0 : ℝ) < 1)
  set r := besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt 1
  have hball : ∀ y : RN N, eigenvalue (ball y r) 1 = 1 ∧ eigenvalue (ball y r) 2 = CN N :=
    fun y => ⟨(hb y).1, by simpa using (hb y).2.1⟩
  let v : RN N := EuclideanSpace.single ⟨0, by omega⟩ 1
  have hv : ‖v‖ = 1 := by simp [v]
  let c : Fin m → RN N := fun i => (4 * r * ((i : ℕ) : ℝ)) • v
  have hdisj : Pairwise (Disjoint on fun i => closedBall (c i) r) := by
    intro i j hij
    refine closedBall_disjoint_closedBall ?_
    have hij' : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by
      intro h; exact hij (Fin.ext (by exact_mod_cast h))
    have h1 : 1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne hij' with h | h
      · have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
          have : (i : ℕ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
          exact_mod_cast this
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
          have : (j : ℕ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
          exact_mod_cast this
        rw [abs_of_nonneg (by linarith)]; linarith
    have hd : dist (c i) (c j) = 4 * r * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rw [dist_eq_norm]
      simp only [c, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * r)]
    rw [hd]
    nlinarith
  let e1 : RN N := EuclideanSpace.single ⟨1, by omega⟩ 1
  have he1 : ‖e1‖ = 1 := by simp [e1]
  have h01 : ⟪v, e1⟫ = 0 := by simp [v, e1, EuclideanSpace.inner_single_left]
  obtain ⟨Ω, hΩ, hconv⟩ := chain_tubes hN hm1 hr hv he1 h01 hdisj
  set U := ⋃ i, ball (c i) r
  have hU : IsAdmissible U := ⟨isOpen_iUnion fun _ => isOpen_ball,
    ⟨c ⟨0, hm1⟩, Set.mem_iUnion.mpr ⟨_, mem_ball_self hr⟩⟩,
    Bornology.isBounded_iUnion.mpr fun _ => isBounded_ball⟩
  have hcount := (eigCount_iUnion hN (fun i => ball (c i) r) (fun _ => isOpen_ball)
    (fun _ => nonempty_ball.mpr hr)
    (fun i j hij => (hdisj hij).mono ball_subset_closedBall ball_subset_closedBall) hU)
  obtain ⟨h0, hmid, htop⟩ := pairs_special hN (fun i => ball (c i) r)
    (fun i => (isDomain_ball _ hr).1) id injective_id hC1 (fun i => hball (c i))
    (fun c hc => absurd (Set.mem_range_self c) hc)
  have heig := eig_of_counts hN hU hm1 hC1 (fun s hs => ?_) (fun s hs1 hs2 => ?_) ?_
  rotate_left
  · rw [hcount s]
    change (pairs (fun i => ball (c i) r) s).encard < m
    rw [h0 s hs, Set.encard_empty]
    exact_mod_cast hm1
  · rw [hcount s]
    exact hmid s hs1 hs2
  · rw [hcount]
    exact htop hm1
  have hlim : Tendsto (fun n => eigenvalue (Ω n) (m + 1) / eigenvalue (Ω n) m) atTop
      (𝓝 (CN N / 1)) := by
    have h1 := hconv (m + 1)
    have h2 := hconv m
    rw [heig.2] at h1
    rw [heig.1] at h2
    exact h1.div h2 one_ne_zero
  refine ⟨?_, fun ub hub => ?_⟩
  · rintro x ⟨Ω', hdom, -, rfl⟩
    have h := cor_upper hppw hppwEq hN hm1 hm4 hdom.1
    have hpos := eigenvalue_pos hN hdom.1 hm1
    rw [div_le_iff₀ hpos]
    exact h
  · have hev : ∀ᶠ n in atTop, eigenvalue (Ω n) (m + 1) / eigenvalue (Ω n) m ≤ ub :=
      Eventually.of_forall fun n => hub ⟨Ω n, (hΩ n).1, (hΩ n).2.1, rfl⟩
    have := le_of_tendsto hlim hev
    simpa using this

end FourthRatio

end

module

public import RequestProject.MainTheorem
public import RequestProject.DisjointCount
public import RequestProject.BallSecond
public import RequestProject.Higher
public import RequestProject.CompCount

/-!
# Connected components and eigenvalue counting (preparation for Section 6)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma eigCount_eq_of_gap (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ}
    (hm : 1 ≤ m) {s : ℝ} (h1 : eigenvalue D m ≤ s) (h2 : s < eigenvalue D (m + 1)) :
    eigCount D s = m := by
  have hge := (le_eigCount_iff hN hD hm s).mpr h1
  have hlt : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ eigCount D s := fun h =>
    absurd ((le_eigCount_iff hN hD (by omega) s).mp h) (not_le.mpr h2)
  push_neg at hlt
  have : eigCount D s ≤ m := by
    rw [← ENat.lt_add_one_iff (ENat.coe_ne_top m)]; exact_mod_cast hlt
  exact le_antisymm this hge

lemma eigenvalue_pos (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ}
    (hm : 1 ≤ m) : 0 < eigenvalue D m :=
  (eigenvalue_one_pos hN hD).trans_le (eigenvalue_mono hN hD le_rfl hm)

lemma CN_pos (hN : 2 ≤ N) : 0 < CN N := zero_lt_one.trans (one_lt_CN hN)

/-- Below a gap at level `m`, every eigenvalue of a component below the cutoff is at most
`λ_m(D)`. -/
lemma comp_eig_le (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ} (hm : 1 ≤ m)
    {T : ℝ} (hT : T ≤ eigenvalue D (m + 1)) (C : comps D) {j : ℕ} (hj : 1 ≤ j)
    (hlt : eigenvalue (C : Set (RN N)) j < T) :
    eigenvalue (C : Set (RN N)) j ≤ eigenvalue D m := by
  by_contra hgt
  push_neg at hgt
  set a := eigenvalue D m
  set s := eigenvalue (C : Set (RN N)) j
  have hs : s < eigenvalue D (m + 1) := hlt.trans_le hT
  have ha : a < eigenvalue D (m + 1) := hgt.trans hs
  have hca := eigCount_eq_of_gap hN hD hm le_rfl ha
  have hcs := eigCount_eq_of_gap hN hD hm hgt.le hs
  rw [eigCount_eq_pairs hN hD] at hca hcs
  have hfin : (pairs (fun C : comps D => (C : Set (RN N))) a).Finite :=
    Set.finite_of_encard_eq_coe hca
  have heq := hfin.eq_of_subset_of_encard_le (pairs_mono _ hgt.le) (by rw [hca, hcs])
  have hmem : (C, j) ∈ pairs (fun C : comps D => (C : Set (RN N))) s := ⟨hj, le_rfl⟩
  rw [← heq] at hmem
  exact absurd hmem.2 (not_le.mpr hgt)

/-- **Component analysis** (core of the proof of Corollary 6.1).  If `C_N λ_m(D) ≤ T ≤
λ_{m+1}(D)` with `1 ≤ m ≤ 4`, every component `C` with `λ₁(C) ≤ λ_m(D)` satisfies
`λ₁(C) = λ_m(D)` and `λ₂(C) = C_N λ_m(D)`, and `T = C_N λ_m(D)`. -/
lemma comp_analysis (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ} (hm1 : 1 ≤ m)
    (hm4 : m ≤ 4) {T : ℝ} (hT1 : CN N * eigenvalue D m ≤ T) (hT2 : T ≤ eigenvalue D (m + 1))
    (C : comps D) (hC1 : eigenvalue (C : Set (RN N)) 1 ≤ eigenvalue D m) :
    eigenvalue (C : Set (RN N)) 1 = eigenvalue D m ∧
      eigenvalue (C : Set (RN N)) 2 = CN N * eigenvalue D m ∧ T = CN N * eigenvalue D m := by
  set a := eigenvalue D m with ha_def
  have hdom : IsDomain (C : Set (RN N)) := isDomain_of_mem_comps hD C.2
  have hCadm := hdom.1
  have ha0 : 0 < a := eigenvalue_pos hN hD hm1
  have hC1' := one_lt_CN hN
  have haT : a < eigenvalue D (m + 1) := by nlinarith
  have hcount := eigCount_eq_of_gap hN hD hm1 le_rfl haT
  rw [eigCount_eq_pairs hN hD] at hcount
  set P := pairs (fun C : comps D => (C : Set (RN N))) a
  have hPfin : P.Finite := Set.finite_of_encard_eq_coe hcount
  set K := {j : ℕ | 1 ≤ j ∧ eigenvalue (C : Set (RN N)) j ≤ a}
  have hmaps : Set.MapsTo (fun j : ℕ => (C, j)) K P := fun j hj => hj
  have hinj : Set.InjOn (fun j : ℕ => (C, j)) K := fun j _ k _ h => by
    simpa using h
  have hKle : K.encard ≤ m := by
    rw [← hcount]; exact Set.encard_le_encard_of_injOn hmaps hinj
  have hKfin : K.Finite := Set.finite_of_encard_le_coe hKle
  obtain ⟨k, hkK, hkmax⟩ := Set.exists_max_image K id hKfin ⟨1, le_rfl, hC1⟩
  simp only [id] at hkmax
  have hk1 : 1 ≤ k := hkK.1
  have hkm : k ≤ m := by
    have hsub : (↑(Finset.Icc 1 k) : Set ℕ) ⊆ K := by
      intro j hj
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj
      exact ⟨hj.1, (eigenvalue_mono hN hCadm hj.1 hj.2).trans hkK.2⟩
    have := (Set.encard_le_encard hsub).trans hKle
    rw [Set.encard_coe_eq_coe_finsetCard] at this
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact_mod_cast this
  have hnext : T ≤ eigenvalue (C : Set (RN N)) (k + 1) := by
    by_contra hlt
    push_neg at hlt
    have := comp_eig_le hN hD hm1 hT2 C (by omega) hlt
    have := hkmax (k + 1) ⟨by omega, this⟩
    omega
  have hkle := hkK.2
  have mono := fun i j (hi : 1 ≤ i) (hij : i ≤ j) => eigenvalue_mono hN hCadm hi hij
  have hCN0 := CN_pos hN
  have hk4 : k ≤ 4 := hkm.trans hm4
  interval_cases k
  · have hppw := hppw.admissible hN hCadm
    have h1 : CN N * eigenvalue (C : Set (RN N)) 1 ≤ CN N * a :=
      mul_le_mul_of_nonneg_left hkle hCN0.le
    refine ⟨?_, by linarith, by linarith⟩
    have : CN N * eigenvalue (C : Set (RN N)) 1 = CN N * a := by linarith
    exact mul_left_cancel₀ hCN0.ne' this
  · have h := higher_ratio hppw hppwEq hN hdom
    have h1 : CN N * eigenvalue (C : Set (RN N)) 2 ≤ CN N * a :=
      mul_le_mul_of_nonneg_left hkle hCN0.le
    have := mono 3 4 (by norm_num) (by norm_num)
    linarith
  · have h := higher_ratio hppw hppwEq hN hdom
    have h1 : CN N * eigenvalue (C : Set (RN N)) 3 ≤ CN N * a :=
      mul_le_mul_of_nonneg_left hkle hCN0.le
    have h2 : CN N * eigenvalue (C : Set (RN N)) 2 ≤ CN N * eigenvalue (C : Set (RN N)) 3 :=
      mul_le_mul_of_nonneg_left (mono 2 3 (by norm_num) (by norm_num)) hCN0.le
    linarith
  · have h := fourth_ratio_of_ppw hppw hppwEq hN hdom
    have h1 : CN N * eigenvalue (C : Set (RN N)) 4 ≤ CN N * a :=
      mul_le_mul_of_nonneg_left hkle hCN0.le
    linarith

/-! ### Counting for configurations of balls -/

/-- Eigenvalues from counting data. -/
lemma eig_of_counts (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ} (hm : 1 ≤ m)
    {a T : ℝ} (haT : a < T) (hlow : ∀ s < a, eigCount D s < m)
    (hmid : ∀ s, a ≤ s → s < T → eigCount D s = m) (htop : ((m + 1 : ℕ) : ℕ∞) ≤ eigCount D T) :
    eigenvalue D m = a ∧ eigenvalue D (m + 1) = T := by
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact (le_eigCount_iff hN hD hm a).mp (hmid a le_rfl haT).ge
  · by_contra hlt
    push_neg at hlt
    have h1 := (le_eigCount_iff hN hD hm _).mpr (le_refl (eigenvalue D m))
    exact absurd (hlow _ hlt) (not_lt.mpr h1)
  · exact (le_eigCount_iff hN hD (by omega) T).mp htop
  · by_contra hlt
    push_neg at hlt
    have h1 := (le_eigCount_iff hN hD (by omega : 1 ≤ m + 1) (max a (eigenvalue D (m + 1)))).mpr
      (le_max_right _ _)
    rw [hmid _ (le_max_left _ _) (max_lt haT hlt)] at h1
    have : m + 1 ≤ m := by exact_mod_cast h1
    omega

/-- The pair sets of a family consisting of `m` "balls" (`λ₁ = a`, `λ₂ = T`) and pieces with
first eigenvalue at least `T`. -/
lemma pairs_special (hN : 2 ≤ N) {ι : Type*} (Df : ι → Set (RN N))
    (hadm : ∀ i, IsAdmissible (Df i)) {m : ℕ} (e : Fin m → ι) (he : Injective e) {a T : ℝ}
    (haT : a < T) (hspec : ∀ i, eigenvalue (Df (e i)) 1 = a ∧ eigenvalue (Df (e i)) 2 = T)
    (hother : ∀ c, c ∉ Set.range e → T ≤ eigenvalue (Df c) 1) :
    (∀ s < a, pairs Df s = ∅) ∧
      (∀ s, a ≤ s → s < T → (pairs Df s).encard = m) ∧
      (1 ≤ m → ((m + 1 : ℕ) : ℕ∞) ≤ (pairs Df T).encard) := by
  have hge1 : ∀ c j, 1 ≤ j → eigenvalue (Df c) 1 ≤ eigenvalue (Df c) j := fun c j hj =>
    eigenvalue_mono hN (hadm c) le_rfl hj
  have hlow : ∀ c, a ≤ eigenvalue (Df c) 1 := by
    intro c
    by_cases hc : c ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hc; exact (hspec i).1.ge
    · exact haT.le.trans (hother c hc)
  have himg : (Set.range fun i => (e i, 1)).encard = m := by
    have hinj : Injective (fun i => (e i, 1)) := fun i j h => he (Prod.mk.inj h).1
    rw [← Set.image_univ, hinj.injOn.encard_image, Set.encard_univ]
    simp
  refine ⟨fun s hs => ?_, fun s hs1 hs2 => ?_, fun hm => ?_⟩
  · ext ⟨c, j⟩
    simp only [pairs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro hj
    exact hs.trans_le ((hlow c).trans (hge1 c j hj))
  · have : pairs Df s = Set.range fun i => (e i, 1) := by
      ext ⟨c, j⟩
      simp only [pairs, Set.mem_setOf_eq, Set.mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨hj, hle⟩
        by_cases hc : c ∈ Set.range e
        · obtain ⟨i, rfl⟩ := hc
          refine ⟨i, rfl, ?_⟩
          by_contra hj1
          have := eigenvalue_mono hN (hadm (e i)) (by norm_num : 1 ≤ 2) (by omega : 2 ≤ j)
          rw [(hspec i).2] at this
          linarith
        · have := (hother c hc).trans (hge1 c j hj)
          linarith
      · rintro ⟨i, rfl, rfl⟩
        exact ⟨le_rfl, (hspec i).1.le.trans hs1⟩
    rw [this, himg]
  · have hsub : insert (e ⟨0, hm⟩, 2) (Set.range fun i => (e i, 1)) ⊆ pairs Df T := by
      intro p hp
      rcases hp with rfl | ⟨i, rfl⟩
      · exact ⟨by norm_num, (hspec _).2.le⟩
      · exact ⟨le_rfl, (hspec i).1.le.trans haT.le⟩
    have hnot : (e ⟨0, hm⟩, 2) ∉ Set.range fun i => (e i, 1) := by
      rintro ⟨i, hi⟩
      simp only [Prod.mk.injEq] at hi
      omega
    have := Set.encard_le_encard hsub
    rw [Set.encard_insert_of_notMem hnot, himg] at this
    exact_mod_cast this

/-- For every ball, `λ₂ = C_N λ₁`. -/
lemma eigenvalue_two_ball (hN : 2 ≤ N) (y : RN N) {R : ℝ} (hR : 0 < R) :
    eigenvalue (ball y R) 2 = CN N * eigenvalue (ball y R) 1 := by
  have ha := eigenvalue_one_pos hN (isDomain_ball y hR).1
  have hrad := ball_radius_eq hN hR ha rfl
  obtain ⟨Φ', _, _, _, _, _, _, _, _, hb'⟩ := ext_ball hN ha
  have h := (hb' y).2.1
  rw [← hrad] at h
  exact h

end FourthRatio

end

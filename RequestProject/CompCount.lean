module

public import RequestProject.DisjointCount
public import RequestProject.Derived

/-!
# Counting over connected components; reduction of the PPW inequality to domains
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The pairs `(i, j)` with `λ_j(Dᵢ) ≤ s`. -/
def pairs {ι : Type*} (Df : ι → Set (RN N)) (s : ℝ) : Set (ι × ℕ) :=
  {p | 1 ≤ p.2 ∧ eigenvalue (Df p.1) p.2 ≤ s}

lemma pairs_mono {ι : Type*} (Df : ι → Set (RN N)) {s s' : ℝ} (h : s ≤ s') :
    pairs Df s ⊆ pairs Df s' := fun _ hp => ⟨hp.1, hp.2.trans h⟩

lemma eigCount_eq_pairs (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) (s : ℝ) :
    eigCount D s = (pairs (fun C : comps D => (C : Set (RN N))) s).encard := by
  haveI := countable_comps hD.1
  have h := (eigCount_iUnion hN (fun C : comps D => (C : Set (RN N)))
    (fun C => (mem_comps_props hD.1 C.2).1) (fun C => (mem_comps_props hD.1 C.2).2.1)
    (fun C C' hne => comps_disjoint C.2 C'.2 (fun h => hne (Subtype.ext h)))
    (by rw [iUnion_comps]; exact hD)) s
  rw [iUnion_comps] at h
  exact h

/-- Some component has first eigenvalue at most `λ_m(D)`. -/
lemma exists_comp_le (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ}
    (hm : 1 ≤ m) : ∃ C : comps D, eigenvalue (C : Set (RN N)) 1 ≤ eigenvalue D m := by
  have h := (le_eigCount_iff hN hD hm (eigenvalue D m)).mpr le_rfl
  rw [eigCount_eq_pairs hN hD] at h
  have hne : (pairs (fun C : comps D => (C : Set (RN N))) (eigenvalue D m)).Nonempty := by
    rw [← Set.encard_pos]
    exact lt_of_lt_of_le (by exact_mod_cast hm) h
  obtain ⟨⟨C, j⟩, hj1, hj⟩ := hne
  exact ⟨C, (eigenvalue_mono hN (isDomain_of_mem_comps hD C.2).1 le_rfl hj1).trans hj⟩

/-- The PPW inequality for domains implies it for every nonempty bounded open set: a connected
component `C` of `D` with `λ₁(C) = λ₁(D)` gives `λ₂(D) ≤ λ₂(C) ≤ C_N λ₁(C) = C_N λ₁(D)`. -/
theorem PPWInequality.admissible (hppw : PPWInequality N) (hN : 2 ≤ N) {D : Set (RN N)}
    (hD : IsAdmissible D) : eigenvalue D 2 ≤ CN N * eigenvalue D 1 := by
  obtain ⟨C, hC⟩ := exists_comp_le hN hD le_rfl
  have hCdom := isDomain_of_mem_comps hD C.2
  have hCD : (C : Set (RN N)) ⊆ D := by
    obtain ⟨x, -, hx⟩ := C.2
    rw [← hx]; exact connectedComponentIn_subset _ _
  have h1 : eigenvalue D 1 ≤ eigenvalue (C : Set (RN N)) 1 :=
    eigenvalue_domain_mono hN hCdom.1 hCD 1
  have h2 : eigenvalue D 2 ≤ eigenvalue (C : Set (RN N)) 2 :=
    eigenvalue_domain_mono hN hCdom.1 hCD 2
  have h3 := hppw hCdom
  have hC1 : eigenvalue (C : Set (RN N)) 1 = eigenvalue D 1 := le_antisymm hC h1
  rw [hC1] at h3
  linarith

end FourthRatio

end

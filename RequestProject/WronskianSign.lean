module

public import RequestProject.WronskianMonotone

/-!
# A Wronskian with one derivative sign change

A monotone coefficient determines the sign of the derivative. Vanishing at
both endpoints then determines the sign of the Wronskian itself.
-/

@[expose] public section

open Set

namespace FourthRatio

lemma nonpos_of_increasing_coefficient {f f1 K : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hf : ∀ t ∈ Ioo 0 1, HasDerivAt f (f1 t) t)
    (hK : MonotoneOn K (Ioo 0 1))
    (hneg : ∀ t ∈ Ioo 0 1, K t ≤ 0 → f1 t ≤ 0)
    (hpos : ∀ t ∈ Ioo 0 1, 0 ≤ K t → 0 ≤ f1 t) :
    ∀ x ∈ Icc 0 1, f x ≤ 0 := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0, h0]
  by_cases hx1 : x = 1
  · simp [hx1, h1]
  have hx' : x ∈ Ioo 0 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),
    lt_of_le_of_ne hx.2 hx1⟩
  by_cases hcut : K x ≤ 0
  · have hm : AntitoneOn f (Icc 0 x) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f1) (convex_Icc _ _)
        (hc.mono ?_) ?_ ?_
      · intro t ht
        exact ⟨ht.1, ht.2.trans hx.2⟩
      · intro t ht
        rw [interior_Icc] at ht
        exact (hf t ⟨ht.1, ht.2.trans_le hx.2⟩).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Ioo 0 1 := ⟨ht.1, ht.2.trans_le hx.2⟩
        exact hneg t ht' ((hK ht' hx' ht.2.le).trans hcut)
    simpa only [h0] using hm ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
  · have hm : MonotoneOn f (Icc x 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f1) (convex_Icc _ _)
        (hc.mono ?_) ?_ ?_
      · intro t ht
        exact ⟨hx.1.trans ht.1, ht.2⟩
      · intro t ht
        rw [interior_Icc] at ht
        exact (hf t ⟨hx.1.trans_lt ht.1, ht.2⟩).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht' : t ∈ Ioo 0 1 := ⟨hx.1.trans_lt ht.1, ht.2⟩
        exact hpos t ht' ((not_le.mp hcut).le.trans (hK hx' ht' ht.1.le))
    simpa only [h1] using hm ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2

end FourthRatio

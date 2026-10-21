module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith

/-!
# The integral consequence of a single crossing

This is an elementary step in Chiti's comparison argument: profiles with equal
total mass and one crossing have ordered cumulative masses. The actual eigenfunction comparison is developed in `ChitiRatio` and
`ChitiCumulative`, using the separately proved Talenti and ball-model results.
-/

@[expose] public section

open MeasureTheory Set

namespace FourthRatio

/-- Equal-mass profiles with a single crossing have ordered integrals on every
measurable set nested with the crossing set. No radial or positivity convention
is hidden in this general measure-theoretic lemma. -/
theorem integral_le_of_single_crossing {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (heq : (∫ x, f x ∂μ) = ∫ x, g x ∂μ)
    {A s : Set α} (hA : MeasurableSet A) (hs : MeasurableSet s)
    (hinside : ∀ᵐ x ∂μ.restrict A, f x ≤ g x)
    (houtside : ∀ᵐ x ∂μ.restrict Aᶜ, g x ≤ f x)
    (hnested : s ⊆ A ∨ A ⊆ s) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ := by
  rcases hnested with hsmall | hlarge
  · apply setIntegral_mono_ae_restrict hf.integrableOn hg.integrableOn
    apply (ae_restrict_iff' hs).mpr
    exact ((ae_restrict_iff' hA).mp hinside).mono fun x hx hxs => hx (hsmall hxs)
  · have hcomp : (∫ x in sᶜ, g x ∂μ) ≤ ∫ x in sᶜ, f x ∂μ := by
      apply setIntegral_mono_ae_restrict hg.integrableOn hf.integrableOn
      apply (ae_restrict_iff' hs.compl).mpr
      exact ((ae_restrict_iff' hA.compl).mp houtside).mono fun x hx hxs =>
        hx (fun hxA => hxs (hlarge hxA))
    have hsumf := integral_add_compl hs hf
    have hsumg := integral_add_compl hs hg
    linarith

end FourthRatio

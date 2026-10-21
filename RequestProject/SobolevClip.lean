module

public import RequestProject.SobolevUpperPart
public import RequestProject.SobolevLevelSets

/-! # Bounded slab truncations and their actual weak gradients -/

@[expose] public section
open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio
variable {N : ℕ}

def clipValue (a b t : ℝ) : ℝ := max (t - a) 0 - max (t - b) 0

lemma clipValue_eq_min {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    clipValue a b t = min (max (t - a) 0) (b - a) := by
  unfold clipValue
  rcases le_or_gt t a with hta | hta
  · rw [max_eq_right (sub_nonpos.mpr hta), max_eq_right (sub_nonpos.mpr (hta.trans hab)),
      min_eq_left (sub_nonneg.mpr hab)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr hta.le)]
    rcases le_or_gt t b with htb | htb
    · rw [max_eq_right (sub_nonpos.mpr htb), min_eq_left (by linarith)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr htb.le), min_eq_right (by linarith)]
      ring

lemma clipValue_nonneg {a b : ℝ} (hab : a ≤ b) (t : ℝ) : 0 ≤ clipValue a b t := by
  rw [clipValue_eq_min hab]
  exact le_min (le_max_right _ _) (sub_nonneg.mpr hab)

lemma clipValue_le_height {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clipValue a b t ≤ b - a := by
  rw [clipValue_eq_min hab]
  exact min_le_right _ _

lemma clipValue_eq_zero {a b t : ℝ} (hab : a ≤ b) (hta : t ≤ a) : clipValue a b t = 0 := by
  rw [clipValue_eq_min hab, max_eq_right (sub_nonpos.mpr hta), min_eq_left (sub_nonneg.mpr hab)]

def clipPair (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : Amb N) : Amb N :=
  upperPartPair a ha p - upperPartPair b hb p

lemma clipPair_mem_H (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) : clipPair a b ha hb p ∈ H D :=
  (H D).sub_mem (upperPartPair_mem_H a ha hp) (upperPartPair_mem_H b hb hp)

lemma clipPair_fst_ae (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : Amb N) :
    ((clipPair a b ha hb p).1 : RN N → ℝ) =ᵐ[volume]
      fun x => clipValue a b ((p.1 : RN N → ℝ) x) := by
  filter_upwards [Lp.coeFn_sub (upperPartPair a ha p).1 (upperPartPair b hb p).1,
    upperPartPair_fst_ae a ha p, upperPartPair_fst_ae b hb p] with x hx h1 h2
  simp only [clipPair, Prod.fst_sub, hx, Pi.sub_apply, h1, h2, clipValue]

/-- The gradient is supported on the strict slab; the upper endpoint is removed
using the proved arbitrary-level Stampacchia lemma. -/
theorem clipPair_snd_ae (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b)
    {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) :
    ((clipPair a b ha hb p).2 : RN N → RN N) =ᵐ[volume]
      fun x => if a < (p.1 : RN N → ℝ) x ∧ (p.1 : RN N → ℝ) x < b then
        (p.2 : RN N → RN N) x else 0 := by
  filter_upwards [Lp.coeFn_sub (upperPartPair a ha p).2 (upperPartPair b hb p).2,
    upperPartPair_snd_ae a ha p, upperPartPair_snd_ae b hb p,
    grad_eq_zero_on_level hp b] with x hx h1 h2 hz
  simp only [clipPair, Prod.snd_sub, hx, Pi.sub_apply, h1, h2]
  rcases lt_trichotomy ((p.1 : RN N → ℝ) x) b with hlt | heq | hgt
  · have hnb : ¬ b < (p.1 : RN N → ℝ) x := not_lt_of_ge hlt.le
    by_cases haa : a < (p.1 : RN N → ℝ) x <;> simp [hlt, hnb, haa]
  · rw [hz heq]
    simp
  · have haa : a < (p.1 : RN N → ℝ) x := hab.trans_lt hgt
    simp [hgt, haa, not_lt_of_ge hgt.le]

end FourthRatio
end

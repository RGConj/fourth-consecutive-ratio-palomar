module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Linarith

/-!
# Level crossings for a scalar differential equation

The compact-superlevel argument proves the derivative sign at a downward
crossing. Convexity of the vector field at a fixed level then rules out a
positive derivative between prescribed endpoint values.
-/

@[expose] public section

open Set Filter Topology

namespace FourthRatio

lemma exists_downcrossing {f f1 : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hfa : c < f a) (hfb : f b < c)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f1 x) x) :
    ∃ x ∈ Ioo a b, f x = c ∧ f1 x ≤ 0 := by
  let S : Set ℝ := Icc a b ∩ f ⁻¹' Ici c
  have hcl : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hco : IsCompact S := (isCompact_Icc : IsCompact (Icc a b)).of_isClosed_subset
    hcl inter_subset_left
  obtain ⟨x, hxmax⟩ := hco.exists_isGreatest ⟨a, ⟨⟨le_rfl, hab.le⟩, hfa.le⟩⟩
  have hxI : x ∈ Icc a b := hxmax.1.1
  have hxc : c ≤ f x := hxmax.1.2
  have hxb : x < b := by
    by_contra h
    have he : x = b := le_antisymm hxI.2 (not_lt.mp h)
    rw [he] at hxc
    exact (not_le_of_gt hfb) hxc
  have hxcl : x ∈ closure (Ioo x b) := by
    rw [closure_Ioo hxb.ne]
    exact ⟨le_rfl, hxb.le⟩
  obtain ⟨s, hs, hsLim⟩ := mem_closure_iff_seq_limit.mp hxcl
  have hsI : ∀ n, s n ∈ Icc a b := fun n =>
    ⟨hxI.1.trans (hs n).1.le, (hs n).2.le⟩
  have hslt : ∀ n, f (s n) < c := by
    intro n
    by_contra h
    have hm : s n ∈ S := ⟨hsI n, not_lt.mp h⟩
    exact (not_le_of_gt (hs n).1) (hxmax.2 hm)
  have hsWithin : Tendsto s atTop (𝓝[Icc a b] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsLim, Eventually.of_forall hsI⟩
  have hflim := (hf x hxI).tendsto.comp hsWithin
  have hfxc : f x = c :=
    (le_of_tendsto hflim (Eventually.of_forall fun n => (hslt n).le)).antisymm hxc
  have hax : a < x := by
    by_contra h
    have he : x = a := le_antisymm (not_lt.mp h) hxI.1
    rw [he] at hfxc
    linarith
  have hsNE : Tendsto s atTop (𝓝[≠] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsLim, Eventually.of_forall fun n => (hs n).1.ne'⟩
  have hslim := (hd x ⟨hax, hxb⟩).tendsto_slope.comp hsNE
  refine ⟨x, ⟨hax, hxb⟩, hfxc, le_of_tendsto hslim ?_⟩
  apply Eventually.of_forall
  intro n
  change slope f x (s n) ≤ 0
  rw [slope_def_field, hfxc]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hslt n).le)
    (sub_nonneg.mpr (hs n).1.le)

lemma exists_left_right_of_deriv_pos {f : ℝ → ℝ} {f1 a b x : ℝ}
    (hax : a < x) (hxb : x < b) (hd : HasDerivAt f f1 x) (hp : 0 < f1) :
    ∃ l ∈ Ioo a x, ∃ r ∈ Ioo x b, f l < f x ∧ f x < f r := by
  have hSl : ∀ᶠ y in 𝓝[≠] x, 0 < slope f x y :=
    hd.tendsto_slope.eventually (lt_mem_nhds hp)
  have hLeft : ∀ᶠ y in 𝓝[<] x, 0 < slope f x y := hSl.filter_mono
    (nhdsWithin_mono x fun y hy => ne_of_lt hy)
  have hRight : ∀ᶠ y in 𝓝[>] x, 0 < slope f x y := hSl.filter_mono
    (nhdsWithin_mono x fun y hy => ne_of_gt hy)
  obtain ⟨l, hlS, hl⟩ := (hLeft.and (Ioo_mem_nhdsLT hax)).exists
  obtain ⟨r, hrS, hr⟩ := (hRight.and (Ioo_mem_nhdsGT hxb)).exists
  refine ⟨l, hl, r, hr, ?_, ?_⟩
  · have hn : l - x < 0 := sub_neg.mpr hl.2
    have h := mul_neg_of_pos_of_neg hlS hn
    rw [slope_def_field, div_mul_cancel₀ _ hn.ne] at h
    exact sub_neg.mp h
  · have hp' : 0 < r - x := sub_pos.mpr hr.1
    have h := mul_pos hrS hp'
    rw [slope_def_field, div_mul_cancel₀ _ hp'.ne'] at h
    exact sub_pos.mp h

/-- A bounded solution running from one to zero cannot turn upwards when the
vector field is convex in time at every fixed level in the unit interval. -/
lemma nonpos_deriv_of_convex_ode {q q1 : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hc : ContinuousOn q (Icc 0 1)) (h0 : q 0 = 1) (h1 : q 1 = 0)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt q (q1 t) t)
    (hrange : ∀ t ∈ Ioo 0 1, q t ∈ Icc 0 1)
    (hode : ∀ t ∈ Ioo 0 1, q1 t = F (q t) t)
    (hconv : ∀ c ∈ Icc 0 1, ConvexOn ℝ (Ioo 0 1) (F c)) :
    ∀ t ∈ Ioo 0 1, q1 t ≤ 0 := by
  intro x hx
  by_contra hnot
  have hp : 0 < q1 x := lt_of_not_ge hnot
  obtain ⟨l, hl, r, hr, hql, hqr⟩ := exists_left_right_of_deriv_pos hx.1 hx.2 (hd x hx) hp
  have hlI : l ∈ Ioo 0 1 := ⟨hl.1, hl.2.trans hx.2⟩
  have hrI : r ∈ Ioo 0 1 := ⟨hx.1.trans hr.1, hr.2⟩
  have hqx0 : 0 < q x := lt_of_le_of_lt (hrange l hlI).1 hql
  have hqx1 : q x < 1 := lt_of_lt_of_le hqr (hrange r hrI).2
  obtain ⟨u, hu, hqu, hdu⟩ := exists_downcrossing hl.1
    (hc.mono (Icc_subset_Icc_right hlI.2.le)) (by rw [h0]; exact hqx1) hql
    (fun t ht => hd t ⟨ht.1, ht.2.trans hlI.2⟩)
  obtain ⟨v, hv, hqv, hdv⟩ := exists_downcrossing hr.2
    (hc.mono (Icc_subset_Icc_left hrI.1.le)) hqr (by rw [h1]; exact hqx0)
    (fun t ht => hd t ⟨hrI.1.trans ht.1, ht.2⟩)
  have huI : u ∈ Ioo 0 1 := ⟨hu.1, hu.2.trans hlI.2⟩
  have hvI : v ∈ Ioo 0 1 := ⟨hrI.1.trans hv.1, hv.2⟩
  have hFu : F (q x) u ≤ 0 := by
    have he := hode u huI
    rw [hqu] at he
    rw [← he]
    exact hdu
  have hFv : F (q x) v ≤ 0 := by
    have he := hode v hvI
    rw [hqv] at he
    rw [← he]
    exact hdv
  have hFmid := (hconv (q x) ⟨hqx0.le, hqx1.le⟩).le_max_of_mem_Icc huI hvI
    ⟨(hu.2.trans hl.2).le, (hr.1.trans hv.1).le⟩
  have hle : F (q x) x ≤ 0 := hFmid.trans (max_le hFu hFv)
  rw [← hode x hx] at hle
  exact (not_le_of_gt hp) hle

end FourthRatio

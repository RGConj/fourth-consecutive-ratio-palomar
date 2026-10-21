module

public import RequestProject.PPWDeep

/-!
# Elementary properties of Ashbaugh–Benguria profiles
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

namespace ABProfile

variable {a : ℝ} (p : ABProfile N a)

lemma prof_of_le {s : ℝ} (hs : s ≤ annR N a ^ 2) : p.prof s = p.h1 s := if_pos hs

lemma prof_of_lt {s : ℝ} (hs : annR N a ^ 2 < s) : p.prof s = p.h2 s := if_neg (not_le.mpr hs)

lemma prof_pos {s : ℝ} (hs : 0 ≤ s) : 0 < p.prof s := by
  by_cases h : s ≤ annR N a ^ 2
  · rw [p.prof_of_le h]; exact p.h1_pos s hs h
  · rw [p.prof_of_lt (not_le.mp h), p.h2_eq s (not_le.mp h).le]
    exact div_pos p.κ_pos (Real.sqrt_pos.mpr (lt_of_le_of_lt (sq_nonneg _) (not_le.mp h)))

lemma Bw_nonneg (hN : 1 ≤ N) (s : ℝ) : 0 ≤ p.Bw s := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h : p.Bw s = (p.prof s + 2 * s * p.dprof s) ^ 2 + ((N : ℝ) - 1) * p.prof s ^ 2 := by
    unfold Bw; ring
  rw [h]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))

lemma prof_tail {s : ℝ} (hs : annR N a ^ 2 ≤ s) :
    p.prof s = p.κ / Real.sqrt s := by
  rcases hs.eq_or_lt with h | h
  · rw [← h, p.prof_of_le le_rfl, p.matching, p.h2_eq _ le_rfl]
  · rw [p.prof_of_lt h, p.h2_eq _ h.le]

lemma Gw_tail (hR : 0 < annR N a) {s : ℝ} (hs : annR N a ^ 2 ≤ s) : p.Gw s = p.κ ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  rw [Gw, p.prof_tail hs, div_pow, Real.sq_sqrt hs0.le]
  field_simp

lemma Gw_le (hR : 0 < annR N a) (hG : MonotoneOn p.Gw (Ici 0)) {s : ℝ} (hs : 0 ≤ s) :
    p.Gw s ≤ p.κ ^ 2 := by
  rcases le_total s (annR N a ^ 2) with h | h
  · rw [← p.Gw_tail hR le_rfl]
    exact hG hs (mem_Ici.mpr (by positivity)) h
  · rw [p.Gw_tail hR h]

lemma deriv_h2 (hR : 0 < annR N a) {s : ℝ} (hs : annR N a ^ 2 ≤ s) :
    deriv p.h2 s = -(p.κ / (2 * s * Real.sqrt s)) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have h1 : HasDerivAt (fun t => p.κ / Real.sqrt t) (-(p.κ / (2 * s * Real.sqrt s))) s := by
    have := ((Real.hasDerivAt_sqrt hs0.ne').inv hsq.ne').const_mul p.κ
    convert this using 1
    · funext t
      simp only [div_eq_mul_inv, Pi.inv_apply]
    · rw [Real.sq_sqrt hs0.le]
      field_simp
  have h2 : HasDerivWithinAt p.h2 (-(p.κ / (2 * s * Real.sqrt s))) (Ici (annR N a ^ 2)) s :=
    h1.hasDerivWithinAt.congr (fun t ht => p.h2_eq t ht) (p.h2_eq s hs)
  have h3 : HasDerivWithinAt p.h2 (deriv p.h2 s) (Ici (annR N a ^ 2)) s :=
    ((p.h2_smooth.differentiable (by simp)) s).hasDerivAt.hasDerivWithinAt
  exact (uniqueDiffOn_Ici _ s hs).eq_deriv _ h3 h2

lemma Bw_tail (hR : 0 < annR N a) {s : ℝ} (hs : annR N a ^ 2 ≤ s) :
    p.Bw s = ((N : ℝ) - 1) * p.κ ^ 2 / s := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hd : p.dprof s = -(p.κ / (2 * s * Real.sqrt s)) := by
    rw [dprof, if_neg (not_lt.mpr hs), p.deriv_h2 hR hs]
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  rw [Bw, hd, p.prof_tail hs]
  field_simp
  rw [hss]
  ring

lemma continuous_prof : Continuous p.prof := by
  unfold prof
  refine Continuous.if_le p.h1_smooth.continuous p.h2_smooth.continuous continuous_id
    continuous_const ?_
  intro x hx; rw [hx, p.matching]
lemma continuous_Gw : Continuous p.Gw := continuous_id.mul (p.continuous_prof.pow 2)

lemma Gw_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ p.Gw s := mul_nonneg hs (sq_nonneg _)

lemma Gw_pos {s : ℝ} (hs : 0 < s) : 0 < p.Gw s := mul_pos hs (pow_pos (p.prof_pos hs.le) 2)

end ABProfile

end FourthRatio

end

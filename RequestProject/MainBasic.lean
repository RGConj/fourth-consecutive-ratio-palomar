module

public import RequestProject.MainSetup

/-!
# The fourth consecutive ratio: basic properties of the configuration (Section 5.1–5.2)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma one_lt_CN (hN : 2 ≤ N) : 1 < CN N := CN_gt_one hN

namespace Setup

variable (S : Setup N)

lemma hΩadm : IsAdmissible S.Ω := S.hΩ.1

lemma U_mem (c : E4) : S.U c ∈ H S.Ω :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (S.he.mem_H i)

lemma U_fst (c : E4) : (S.U c).1 = ∑ i : Fin 4, c i • (S.e i).1 := by
  simp [U, Prod.fst_sum]

lemma fU_rep (c : E4) : IsContRep S.Ω (S.U c) (S.fU c) := by
  refine ⟨continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (S.hf i).1, ?_⟩
  have hall : ∀ᵐ x ∂(volume.restrict S.Ω), ∀ i : Fin 4, ((S.e i).1 : RN N → ℝ) x = S.f i x :=
    ae_all_iff.mpr fun i => (S.hf i).2
  have hsm : ∀ᵐ x ∂(volume.restrict S.Ω), ∀ i : Fin 4,
      ((c i • (S.e i).1 : L2 N) : RN N → ℝ) x = c i * ((S.e i).1 : RN N → ℝ) x :=
    ae_all_iff.mpr fun i => ae_restrict_of_ae (by
      filter_upwards [Lp.coeFn_smul (c i) (S.e i).1] with x hx
      rw [hx, Pi.smul_apply, smul_eq_mul])
  filter_upwards [ae_restrict_of_ae (L2_coeFn_sum Finset.univ fun i : Fin 4 => c i • (S.e i).1),
    hsm, hall] with x h1 h2 h3
  rw [U_fst, h1]
  simp only [fU]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i, h3 i]

lemma l2_U_e (c : E4) (j : Fin 4) : l2 (S.U c) (S.e j) = c j := by
  rw [l2_comm]
  exact S.he.l2_sum_e (fun i => c i) j

lemma l2_U (c c' : E4) : l2 (S.U c) (S.U c') = ⟪c, c'⟫ := by
  conv_lhs => rw [U]
  rw [l2_sum_left]
  simp only [l2_smul_left, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [l2_comm, l2_U_e]; ring

lemma U_neg (c : E4) : S.U (-c) = -S.U c := by
  simp [U, Finset.sum_neg_distrib]

lemma fU_neg (c : E4) : S.fU (-c) = fun x => -S.fU c x := by
  ext x; simp [fU, Finset.sum_neg_distrib]

lemma U_ne_zero {c : E4} (hc : c ≠ 0) : S.U c ≠ 0 := by
  intro h
  have := S.l2_U c c
  rw [h, l2_zero_left, real_inner_self_eq_norm_sq] at this
  exact hc (by simpa using this.symm)

lemma a_pos : 0 < S.a :=
  (eigenvalue_one_pos S.hN S.hΩadm).trans_le (eigenvalue_mono S.hN S.hΩadm le_rfl (by norm_num))

lemma lam1_lt_a : eigenvalue S.Ω 1 < S.a :=
  (lam1_lt_lam2 S.hN S.hΩ S.he).trans_le (eigenvalue_mono S.hN S.hΩadm (by norm_num)
    (by norm_num))

lemma a_lt_b : S.a < S.b := by
  have h1 := one_lt_CN S.hN
  have h2 := S.a_pos
  have h3 := S.hgap
  simp only [a, b] at *
  nlinarith

lemma Qa_U (c : E4) :
    Qshift S.a (S.U c) = ∑ i : Fin 4, (eigenvalue S.Ω ((i : ℕ) + 1) - S.a) * c i ^ 2 := by
  rw [← bshift_eq]
  exact S.he.bshift_sum (fun i => c i) S.a

lemma Qa_U_le (c : E4) : Qshift S.a (S.U c) ≤ 0 := by
  rw [Qa_U]
  refine Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  have := eigenvalue_mono S.hN S.hΩadm (Nat.le_add_left 1 i) (by omega : (i : ℕ) + 1 ≤ 4)
  simp only [a]; linarith

lemma c0_eq_zero_of_Qa {c : E4} (h : Qshift S.a (S.U c) = 0) : c 0 = 0 := by
  rw [Qa_U] at h
  have hnp : ∀ i ∈ Finset.univ, (eigenvalue S.Ω ((i : Fin 4) + 1) - S.a) * c i ^ 2 ≤ 0 :=
    fun i _ => mul_nonpos_of_nonpos_of_nonneg (by
      have := eigenvalue_mono S.hN S.hΩadm (Nat.le_add_left 1 i) (by omega : (i : ℕ) + 1 ≤ 4)
      simp only [a]; linarith) (sq_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp h 0 (Finset.mem_univ _)
  have hlt : eigenvalue S.Ω (((0 : Fin 4) : ℕ) + 1) - S.a < 0 := by
    simpa using S.lam1_lt_a
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hlt.ne
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

lemma posPart_sub_negPart_U (c : E4) : posPart (S.U c) - negPart (S.U c) = S.U c :=
  posPart_sub_negPart S.hΩadm (S.U_mem c) (S.fU_rep c)

lemma Qa_U_split (c : E4) :
    Qshift S.a (S.U c) = Qshift S.a (posPart (S.U c)) + Qshift S.a (negPart (S.U c)) := by
  obtain ⟨hq, hl⟩ := parts_orthogonal (S.U c)
  conv_lhs => rw [← S.posPart_sub_negPart_U c]
  simp only [Qshift, qf_sub_left, qf_sub_right, l2_sub_left, l2_sub_right,
    qf_comm (negPart _) (posPart _), l2_comm (negPart _) (posPart _), hq, hl]
  ring

lemma posPart_U_mem (c : E4) : posPart (S.U c) ∈ H S.Ω :=
  H_mono (posSign_subset _ _) (parts_mem S.hΩadm (S.U_mem c) (S.fU_rep c)).1

lemma negPart_U_mem (c : E4) : negPart (S.U c) ∈ H S.Ω :=
  H_mono (negSign_subset _ _) (parts_mem S.hΩadm (S.U_mem c) (S.fU_rep c)).2

lemma continuous_U_fst : Continuous fun c : E4 => (S.U c).1 := by
  simp only [U_fst]
  fun_prop

lemma continuous_posPart_U_fst : Continuous fun c : E4 => (posPart (S.U c)).1 :=
  Lp.continuous_posPart.comp S.continuous_U_fst

lemma qf_posPart_U (c : E4) :
    qf (posPart (S.U c)) (posPart (S.U c)) =
      ∑ i : Fin 4, c i * (eigenvalue S.Ω ((i : ℕ) + 1) * l2 (S.e i) (posPart (S.U c))) := by
  have h1 : qf (posPart (S.U c)) (posPart (S.U c)) = qf (posPart (S.U c)) (S.U c) := by
    have := congrArg (qf (posPart (S.U c))) (S.posPart_sub_negPart_U c)
    rw [qf_sub_right, (parts_orthogonal (S.U c)).1, sub_zero] at this
    exact this
  have h2 := S.posPart_U_mem c
  rw [h1, qf_comm]
  generalize posPart (S.U c) = p at h2 ⊢
  rw [U, qf_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qf_smul_left, (S.he.1 i).2.2 _ h2]

lemma continuous_Qa_posPart_U : Continuous fun c : E4 => Qshift S.a (posPart (S.U c)) := by
  have hl : ∀ w : Amb N, Continuous fun c : E4 => l2 w (posPart (S.U c)) := fun w =>
    continuous_inner.comp (continuous_const.prodMk S.continuous_posPart_U_fst)
  have hll : Continuous fun c : E4 => l2 (posPart (S.U c)) (posPart (S.U c)) :=
    continuous_inner.comp (S.continuous_posPart_U_fst.prodMk S.continuous_posPart_U_fst)
  simp only [Qshift, qf_posPart_U]
  refine Continuous.sub (continuous_finsetSum _ fun i _ => ?_) (continuous_const.mul hll)
  exact (continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _)).mul
    (continuous_const.mul (hl _))

lemma Fbal_eq (c : E4) : S.Fbal c = 2 * Qshift S.a (posPart (S.U c)) - Qshift S.a (S.U c) := by
  rw [Qa_U_split, Fbal]; ring

lemma continuous_Fbal : Continuous S.Fbal := by
  have : Continuous fun c : E4 => Qshift S.a (S.U c) := by
    simp only [Qa_U]
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).pow 2
  have h := ((continuous_const (y := (2 : ℝ))).mul S.continuous_Qa_posPart_U).sub this
  convert h using 1
  funext c
  exact S.Fbal_eq c

lemma Fbal_continuousOn : ContinuousOn S.Fbal (sphere 0 1) :=
  S.continuous_Fbal.continuousOn

lemma Fbal_neg (c : E4) : S.Fbal (-c) = -S.Fbal c := by
  simp only [Fbal, U_neg, posPart_neg, negPart_neg]
  ring

lemma U_e4 : S.U e4 = S.e 0 := by
  simp [U, e4, PiLp.single_apply]

lemma Fbal_e4 : S.Fbal e4 < 0 := by
  obtain ⟨h1, h2⟩ := posPart_eq_self_of_pos S.hΩadm.1.measurableSet (S.he.mem_H 0) (S.hf 0)
    S.hf0
  have heig := S.he.1 0
  have hq : qf (S.e 0) (S.e 0) = eigenvalue S.Ω 1 * l2 (S.e 0) (S.e 0) :=
    heig.2.2 _ (S.he.mem_H 0)
  have hl : l2 (S.e 0) (S.e 0) = 1 := by simpa using S.he.2.1 0 0
  simp only [Fbal, U_e4, h1, h2, Qshift, qf_zero_left, l2_zero_left, mul_zero, sub_zero, hq, hl]
  linarith [S.lam1_lt_a]

lemma posPart_fst_nonneg (v : Amb N) : 0 ≤ᵐ[volume] ((posPart v).1 : RN N → ℝ) := by
  filter_upwards [posPart_fst_ae v] with x hx
  rw [hx]; exact le_max_right _ _

lemma negPart_fst_nonneg (v : Amb N) : 0 ≤ᵐ[volume] ((negPart v).1 : RN N → ℝ) := by
  filter_upwards [negPart_fst_ae v] with x hx
  rw [hx]; exact le_max_right _ _

lemma balance {c : E4} (hc : c ∈ S.K) :
    Qshift S.a (posPart (S.U c)) ≤ 0 ∧ Qshift S.a (negPart (S.U c)) ≤ 0 ∧
      posPart (S.U c) ≠ 0 ∧ negPart (S.U c) ≠ 0 := by
  obtain ⟨hsph, hF⟩ := hc
  have hsplit := S.Qa_U_split c
  have hle := S.Qa_U_le c
  simp only [Fbal, sub_eq_zero] at hF
  have hc0 : c ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨c, hsph⟩
  have hU0 := S.U_ne_zero hc0
  have hdiff := S.posPart_sub_negPart_U c
  have hl0 := S.l2_U_e c 0
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro hp
    have hQ : Qshift S.a (S.U c) = 0 := by
      rw [hsplit, ← hF, hp]; simp [Qshift]
    have h00 := S.c0_eq_zero_of_Qa hQ
    rw [hp, zero_sub] at hdiff
    have hn0 : negPart (S.U c) ≠ 0 := fun h => hU0 (by rw [← hdiff, h, neg_zero])
    have := l2_pos_of_nonneg S.hΩadm (S.negPart_U_mem c) hn0 (negPart_fst_nonneg _)
      (S.he.mem_H 0) (S.hf 0) S.hf0
    rw [← hdiff, l2_neg_left, h00] at hl0
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod] at hl0
    linarith
  · intro hn
    have hQ : Qshift S.a (S.U c) = 0 := by
      rw [hsplit, hF, hn]; simp [Qshift]
    have h00 := S.c0_eq_zero_of_Qa hQ
    rw [hn, sub_zero] at hdiff
    have hp0 : posPart (S.U c) ≠ 0 := fun h => hU0 (by rw [← hdiff, h])
    have := l2_pos_of_nonneg S.hΩadm (S.posPart_U_mem c) hp0 (posPart_fst_nonneg _)
      (S.he.mem_H 0) (S.hf 0) S.hf0
    rw [← hdiff, h00] at hl0
    simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod] at hl0
    linarith

lemma neg_mem_K {c : E4} (hc : c ∈ S.K) : -c ∈ S.K := by
  refine ⟨by simpa using hc.1, ?_⟩
  rw [Fbal_neg, hc.2, neg_zero]

end Setup

lemma IsEigenfunction.smul {D : Set (RN N)} {u : Amb N} {lam : ℝ}
    (hu : IsEigenfunction D u lam) {s : ℝ} (hs : s ≠ 0) : IsEigenfunction D (s • u) lam :=
  ⟨(H D).smul_mem s hu.1, smul_ne_zero hs hu.2.1, fun φ hφ => by
    rw [qf_smul_left, l2_smul_left, hu.2.2 φ hφ]; ring⟩

lemma IsContRep.smul {D : Set (RN N)} {v : Amb N} {f : RN N → ℝ} (h : IsContRep D v f)
    (s : ℝ) : IsContRep D (s • v) (fun x => s * f x) := by
  refine ⟨continuousOn_const.mul h.1, ?_⟩
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul s v.1), h.2] with x h1 h2
  simp only [Prod.smul_fst, h1, Pi.smul_apply, smul_eq_mul, h2]

lemma IsSpectralBasis.update_zero {D : Set (RN N)} {e : ℕ → Amb N} (he : IsSpectralBasis D e)
    {s : ℝ} (hs : s ^ 2 = 1) :
    IsSpectralBasis D (fun j => if j = 0 then s • e 0 else e j) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  refine ⟨fun j => ?_, fun i j => ?_, fun v hv => ?_⟩
  · by_cases hj : j = 0
    · subst hj; simpa using (he.1 0).smul hs0
    · simpa [hj] using he.1 j
  · by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi hj; simp only [if_true, l2_smul_left, l2_smul_right, he.2.1]; nlinarith
    · subst hi; simp [hj, he.2.1, Ne.symm hj]
    · subst hj; simp [hi, he.2.1]
    · simp [hi, hj, he.2.1]
  · have hsq : ∀ j, l2 v (if j = 0 then s • e 0 else e j) ^ 2 = l2 v (e j) ^ 2 := fun j => by
      by_cases hj : j = 0
      · subst hj; simp only [if_true, l2_smul_right]; rw [mul_pow, hs, one_mul]
      · simp [hj]
    simp only [hsq]
    exact he.2.2 v hv

/-- Existence of the contradictory configuration under the hypothesis `C_N λ₄ ≤ λ₅`. -/
lemma exists_setup (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N)
    {Ω : Set (RN N)} (hΩ : IsDomain Ω)
    (hgap : CN N * eigenvalue Ω 4 ≤ eigenvalue Ω 5) : ∃ S : Setup N, S.Ω = Ω := by
  classical
  obtain ⟨e, he⟩ := exists_spectralBasis hN hΩ.1
  obtain ⟨hsimp, u, g, hu, hg, hgpos⟩ := ground_state hN hΩ
  have h0 : IsEigenfunction Ω (e 0) (eigenvalue Ω 1) := by simpa using he.1 0
  obtain ⟨c, hc⟩ := hsimp u (e 0) hu h0
  have hc0 : c ≠ 0 := by rintro rfl; exact h0.2.1 (by simp [hc])
  set s : ℝ := if 0 < c then 1 else -1 with hs_def
  have hs2 : s ^ 2 = 1 := by by_cases h : 0 < c <;> simp [hs_def, h]
  have hsc : 0 < s * c := by
    by_cases h : 0 < c
    · simp [hs_def, h]
    · simp only [hs_def, h, if_false]
      exact mul_pos_of_neg_of_neg (by norm_num) (lt_of_le_of_ne (not_lt.mp h) hc0)
  set e' : ℕ → Amb N := fun j => if j = 0 then s • e 0 else e j with he'_def
  have he' : IsSpectralBasis Ω e' := he.update_zero hs2
  have hrep : ∀ j, ∃ f : RN N → ℝ, IsContRep Ω (e' j) f := fun j => by
    obtain ⟨f, -, hf⟩ := ext_analytic hΩ (he'.mem_H j) (he'.1 j).2.2
    exact ⟨f, hf⟩
  let f' : ℕ → RN N → ℝ := fun j => if j = 0 then fun x => s * c * g x else (hrep j).choose
  have hf' : ∀ j, IsContRep Ω (e' j) (f' j) := fun j => by
    by_cases hj : j = 0
    · subst hj
      have : e' 0 = s • c • u := by simp [he'_def, hc]
      rw [this]
      have := (hg.smul c).smul s
      simp only [f', if_true]
      convert this using 2
      ring
    · simp only [f', hj, if_false]
      exact (hrep j).choose_spec
  refine ⟨⟨hN, Ω, hΩ, e', he', f', hf', fun x hx => ?_, hgap, hppw, hppwEq⟩, rfl⟩
  simp only [f', if_true]
  exact mul_pos hsc (hgpos x hx)

end FourthRatio

end

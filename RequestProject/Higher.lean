module

public import RequestProject.MainStrict
public import RequestProject.DisjointCount

/-!
# The higher-ratio estimate `λ₄ < C_N λ₂` (External theorem 2.4), derived

The previously known higher-ratio estimate of Ashbaugh–Benguria is not assumed: it is derived
here from the PPW inequality and its equality case, nodal localization, the disjoint-union
counting identity and the ball–annulus lemma (Lemma 4.1).

Let `u` be a second eigenfunction of the domain `D`, `a = λ₂(D)`.  It changes sign, and nodal
components `G₊ ⊆ {u > 0}`, `G₋ ⊆ {u < 0}` have `λ₁(G±) = a`.  By PPW, `λ₂(G±) ≤ C_N a`.  If one
of these is an equality, the PPW equality case makes `G±` a ball of radius `j_{N/2-1,1}/√a` on
which `u` is a multiple of the Bessel profile, and the ball–annulus lemma gives
`λ₄(D) ≤ λ_{2N+2}(D) < C_N a`.  Otherwise `G₊ ∪ G₋` has four eigenvalues `< C_N a` and domain
monotonicity concludes.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- Two disjoint nonempty open subsets of `D` give `λ₄(D) ≤ max (λ₂(C₁)) (λ₂(C₂))`. -/
lemma eigenvalue_four_le_of_disjoint (hN : 2 ≤ N) {D C₁ C₂ : Set (RN N)} (hD : IsAdmissible D)
    (h₁ : IsOpen C₁) (h₂ : IsOpen C₂) (h₁D : C₁ ⊆ D) (h₂D : C₂ ⊆ D) (hd : Disjoint C₁ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    eigenvalue D 4 ≤ max (eigenvalue C₁ 2) (eigenvalue C₂ 2) := by
  classical
  set Df : Bool → Set (RN N) := fun b => cond b C₁ C₂ with hDf
  have hU : (⋃ b, Df b) = C₁ ∪ C₂ := by
    ext x; simp [Df, Bool.exists_bool, or_comm]
  have hUD : C₁ ∪ C₂ ⊆ D := Set.union_subset h₁D h₂D
  have hUadm : IsAdmissible (⋃ b, Df b) := by
    rw [hU]
    exact ⟨h₁.union h₂, hne₁.mono Set.subset_union_left, hD.2.2.subset hUD⟩
  have hadm₁ : IsAdmissible C₁ := ⟨h₁, hne₁, hD.2.2.subset h₁D⟩
  have hadm₂ : IsAdmissible C₂ := ⟨h₂, hne₂, hD.2.2.subset h₂D⟩
  set s := max (eigenvalue C₁ 2) (eigenvalue C₂ 2) with hs
  have hdisj : Pairwise (Disjoint on Df) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [Df, Function.onFun, hd.symm]
  have hcount := eigCount_iUnion hN Df (by intro b; cases b <;> assumption)
    (by intro b; cases b <;> assumption) hdisj hUadm s
  have m₁ := eigenvalue_mono hN hadm₁ le_rfl (by norm_num : 1 ≤ 2)
  have m₂ := eigenvalue_mono hN hadm₂ le_rfl (by norm_num : 1 ≤ 2)
  have s₁ : eigenvalue C₁ 2 ≤ s := le_max_left _ _
  have s₂ : eigenvalue C₂ 2 ≤ s := le_max_right _ _
  have h4 : ((4 : ℕ) : ℕ∞) ≤ eigCount (⋃ b, Df b) s := by
    rw [hcount]
    have hsub : (({(true, 1), (true, 2), (false, 1), (false, 2)} : Finset (Bool × ℕ)) :
        Set (Bool × ℕ)) ⊆ {p | 1 ≤ p.2 ∧ eigenvalue (Df p.1) p.2 ≤ s} := by
      intro p hp
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨le_rfl, m₁.trans s₁⟩
      · exact ⟨by norm_num, s₁⟩
      · exact ⟨le_rfl, m₂.trans s₂⟩
      · exact ⟨by norm_num, s₂⟩
    refine le_trans ?_ (Set.encard_le_encard hsub)
    rw [Set.encard_coe_eq_coe_finsetCard]
    rfl
  have := (le_eigCount_iff hN hUadm (by norm_num) s).mp h4
  calc eigenvalue D 4 ≤ eigenvalue (⋃ b, Df b) 4 :=
        eigenvalue_domain_mono hN hUadm (by rw [hU]; exact hUD) 4
    _ ≤ s := this

/-- An eigenfunction of a domain with eigenvalue `> λ₁` changes sign. -/
lemma sign_change_of_orth (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) {f : RN N → ℝ} (hf : IsContRep D (e 1) f) :
    (posSign D f).Nonempty ∧ (negSign D f).Nonempty := by
  have hDm : MeasurableSet D := hD.1.1.measurableSet
  obtain ⟨hsimp, p, g, hp, hg, hgpos⟩ := ground_state hN hD
  have h0 : IsEigenfunction D (e 0) (eigenvalue D 1) := by simpa using he.1 0
  obtain ⟨c, hc⟩ := hsimp (e 0) p h0 hp
  have horth : l2 (e 1) p = 0 := by
    rw [hc, l2_smul_right, he.2.1 1 0]; simp
  have hu := he.1 1
  constructor
  · by_contra hP
    rw [Set.not_nonempty_iff_eq_empty] at hP
    have hnn : ∀ x ∈ D, 0 ≤ (fun x => -f x) x := by
      intro x hx
      by_contra hlt
      have : x ∈ posSign D f := ⟨hx, by simp only [neg_nonneg, not_le] at hlt; exact hlt⟩
      rw [hP] at this
      exact this
    have := l2_pos_of_nonneg hD.1 ((H D).neg_mem hu.1) (neg_ne_zero.mpr hu.2.1)
      (ae_nonneg_of_contRep hDm ((H D).neg_mem hu.1) hf.neg hnn) hp.1 hg hgpos
    rw [l2_neg_left] at this
    linarith
  · by_contra hM
    rw [Set.not_nonempty_iff_eq_empty] at hM
    have hnn : ∀ x ∈ D, 0 ≤ f x := by
      intro x hx
      by_contra hlt
      have : x ∈ negSign D f := ⟨hx, lt_of_not_ge hlt⟩
      rw [hM] at this
      exact this
    have := l2_pos_of_nonneg hD.1 hu.1 hu.2.1 (ae_nonneg_of_contRep hDm hu.1 hf hnn) hp.1 hg
      hgpos
    linarith

/-- The equality case on a positive nodal component: if a nodal component `G` of `{u > 0}` has
`λ₂(G) = C_N a`, then `λ₄(D) < C_N a`. -/
lemma lam4_lt_of_comp_eq (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N) {D : Set (RN N)}
    (hD : IsDomain D) {u : Amb N} {a : ℝ}
    (ha : 0 < a) (hu : IsEigenfunction D u a) {f : RN N → ℝ} (hf : IsContRep D u f)
    (hpos : (posSign D f).Nonempty) (hneg : (negSign D f).Nonempty)
    {x : RN N} (hx : x ∈ posSign D f)
    (hG : IsEigenfunction (connectedComponentIn (posSign D f) x)
      (restrictTo (connectedComponentIn (posSign D f) x) (posPart u)) a)
    (hG1 : eigenvalue (connectedComponentIn (posSign D f) x) 1 = a)
    (hG2 : eigenvalue (connectedComponentIn (posSign D f) x) 2 = CN N * a) :
    eigenvalue D 4 < CN N * a := by
  set G := connectedComponentIn (posSign D f) x with hG_def
  have hPo : IsOpen (posSign D f) := isOpen_posSign hD.1.1 hf.1
  have hGo : IsOpen G := hPo.connectedComponentIn
  have hGD : G ⊆ D := (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  have hGdom : IsDomain G :=
    ⟨⟨hGo, ⟨x, mem_connectedComponentIn hx⟩, hD.1.2.2.subset hGD⟩,
      ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩⟩
  have hl2v : eigenvalue G 2 = CN N * eigenvalue G 1 := by rw [hG1, hG2]
  obtain ⟨y, R, hR0, hlB, hHB⟩ := hppwEq hGdom hl2v
  rw [hG1] at hlB
  have hRval := ball_radius_eq hN hR0 ha hlB
  obtain ⟨Φ, _, hΦprof, _, _, _, _, _, _, hball⟩ := ext_ball_basic hN ha
  obtain ⟨_, ⟨φ, hφeig, hφae⟩, _⟩ := hball y
  rw [← hRval] at hφeig hφae
  set w := restrictTo G (posPart u) with hw_def
  have hwB : IsEigenfunction (ball y R) w a := by
    simp only [IsEigenfunction] at hG ⊢
    rw [← hHB]; exact hG
  have hφ1 : IsEigenfunction (ball y R) φ (eigenvalue (ball y R) 1) := by rw [hlB]; exact hφeig
  have hw1 : IsEigenfunction (ball y R) w (eigenvalue (ball y R) 1) := by rw [hlB]; exact hwB
  obtain ⟨hsimpB, -⟩ := ground_state hN (isDomain_ball y hR0)
  obtain ⟨s, hs⟩ := hsimpB φ w hφ1 hw1
  have hs0 : s ≠ 0 := by rintro rfl; exact hwB.2.1 (by rw [hs, zero_smul])
  have hind : G.indicator (u.1 : RN N → ℝ) =ᵐ[volume] fun x =>
      s * (ball y R).indicator (fun x => besselProfile N a (x - y)) x := by
    have hne : ∀ᵐ x ∂(volume : Measure (RN N)), x ≠ y := by
      haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
      haveI : Nontrivial (RN N) := inferInstance
      rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]; exact measure_singleton y
    refine (indicator_eq_restrictTo_posPart hD.1.1.measurableSet hGo.measurableSet hf
      (connectedComponentIn_subset _ _)).trans ?_
    rw [← hw_def, hs]
    filter_upwards [Lp.coeFn_smul s φ.1, hφae, hne] with x h1 h2 h3
    simp only [Prod.smul_fst, h1, Pi.smul_apply, smul_eq_mul, h2]
    congr 1
    by_cases hx : x ∈ ball y R
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hΦprof _ (sub_ne_zero.mpr h3)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hlb := lemma_ball hN hD ha hu hf hpos hneg (G := G) (Or.inl ⟨x, hx, rfl⟩) y s hs0
    (by rw [← hRval]; exact hind)
  have h4 : eigenvalue D 4 ≤ eigenvalue D (2 * N + 2) :=
    eigenvalue_mono hN hD.1 (by norm_num) (by omega)
  linarith

/-- **Higher-ratio estimate (Ashbaugh–Benguria), derived.** For every bounded domain `D`,
`λ₄(D) < C_N λ₂(D)`. -/
theorem higher_ratio (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N)
    (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) :
    eigenvalue D 4 < CN N * eigenvalue D 2 := by
  obtain ⟨e, he⟩ := exists_spectralBasis hN hD.1
  set a := eigenvalue D 2 with ha_def
  have hu : IsEigenfunction D (e 1) a := he.1 1
  have ha : 0 < a := (eigenvalue_one_pos hN hD.1).trans (lam1_lt_lam2 hN hD he)
  obtain ⟨f, -, hrep, -, -, hcP, hcN⟩ := nodal hN hD.1 hu
  obtain ⟨⟨xp, hxp⟩, ⟨xn, hxn⟩⟩ := sign_change_of_orth hN hD he hrep
  obtain ⟨hGp, hGp1⟩ := hcP xp hxp
  obtain ⟨hGn, hGn1⟩ := hcN xn hxn
  have hPo : IsOpen (posSign D f) := isOpen_posSign hD.1.1 hrep.1
  have hNo : IsOpen (negSign D f) := isOpen_negSign hD.1.1 hrep.1
  set Gp := connectedComponentIn (posSign D f) xp with hGp_def
  set Gn := connectedComponentIn (negSign D f) xn with hGn_def
  have hGpo : IsOpen Gp := hPo.connectedComponentIn
  have hGno : IsOpen Gn := hNo.connectedComponentIn
  have hGpD : Gp ⊆ D := (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  have hGnD : Gn ⊆ D := (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  have hGpne : Gp.Nonempty := ⟨xp, mem_connectedComponentIn hxp⟩
  have hGnne : Gn.Nonempty := ⟨xn, mem_connectedComponentIn hxn⟩
  have hGpadm : IsAdmissible Gp := ⟨hGpo, hGpne, hD.1.2.2.subset hGpD⟩
  have hGnadm : IsAdmissible Gn := ⟨hGno, hGnne, hD.1.2.2.subset hGnD⟩
  have hdisj : Disjoint Gp Gn := Set.disjoint_left.mpr fun x hx hx' =>
    lt_asymm (show f x < 0 from (connectedComponentIn_subset _ _ hx').2)
      (show 0 < f x from (connectedComponentIn_subset _ _ hx).2)
  have hppwp := hppw.admissible hN hGpadm
  have hppwn := hppw.admissible hN hGnadm
  rw [hGp1] at hppwp
  rw [hGn1] at hppwn
  rcases hppwp.lt_or_eq with hp | hp
  · rcases hppwn.lt_or_eq with hn | hn
    · calc eigenvalue D 4 ≤ max (eigenvalue Gp 2) (eigenvalue Gn 2) :=
            eigenvalue_four_le_of_disjoint hN hD.1 hGpo hGno hGpD hGnD hdisj hGpne hGnne
        _ < CN N * a := max_lt hp hn
    · have hu' : IsEigenfunction D (-e 1) a :=
        ⟨(H D).neg_mem hu.1, neg_ne_zero.mpr hu.2.1, fun φ hφ => by
          simp only [qf_neg_left, l2_neg_left, hu.2.2 φ hφ]; ring⟩
      have e1 : negSign D f = posSign D (fun x => -f x) := negSign_eq_posSign_neg D f
      have hxn' : xn ∈ posSign D (fun x => -f x) := e1 ▸ hxn
      have hxp' : xp ∈ negSign D (fun x => -f x) := by
        rw [negSign_eq_posSign_neg]; simpa using hxp
      rw [hGn_def, e1] at hGn hGn1 hn
      exact lam4_lt_of_comp_eq hppwEq hN hD ha hu' hrep.neg ⟨xn, hxn'⟩ ⟨xp, hxp'⟩ hxn' hGn hGn1 hn
  · exact lam4_lt_of_comp_eq hppwEq hN hD ha hu hrep ⟨xp, hxp⟩ ⟨xn, hxn⟩ hxp hGp hGp1 hp

end FourthRatio

end

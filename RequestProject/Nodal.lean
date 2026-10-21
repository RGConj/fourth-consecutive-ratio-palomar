module

public import RequestProject.Truncation
public import RequestProject.DisjointUnion

/-!
# Nodal localization

The nodal localization theorem of Section 2 (`nodal`) is derived here from the remaining
external inputs instead of being assumed:

* restriction to a piece of a disjoint union of open sets maps `H(⋃ Dᵢ)` into `H(Dᵢ)`
  (`restrictTo_mem_H_piece`), a consequence of `H(⋃ Dᵢ) = closure (⨆ H(Dᵢ))` and the continuity
  of the restriction map; in particular this applies to connected components;
* smoothness (`eigenfunction_smooth_rep`): on each connected component the restriction of the
  eigenfunction is a weak solution, hence real analytic by `ext_analytic`, and the analytic
  representatives glue to a representative that is smooth on `D`;
* nodal components (`nodal_pos_comp`): the restriction of `u₊` to a component `G` of the
  positive set lies in `H_G` (Lemma 3.1 plus the restriction result), agrees with `u` on `G`,
  hence is a nonnegative eigenfunction of `G` with eigenvalue `λ`; pairing with the positive
  ground state of `G` (`ground_state`) gives `λ = λ₁(G)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Restriction to a measurable set -/

lemma restrictTo_add {G : Set (RN N)} (hG : MeasurableSet G) (v w : Amb N) :
    restrictTo G (v + w) = restrictTo G v + restrictTo G w := by
  simp only [restrictTo, dif_pos hG]
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [indL2_ae G hG (v + w).1, indL2_ae G hG v.1, indL2_ae G hG w.1,
      Lp.coeFn_add v.1 w.1, Lp.coeFn_add (indL2 G hG v.1) (indL2 G hG w.1)]
      with x h1 h2 h3 h4 h5
    simp only [Prod.fst_add, Prod.mk_add_mk] at h1 ⊢
    rw [h5, h1, Pi.add_apply, h2, h3]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx, h4,
        Pi.add_apply]
    · simp [Set.indicator_of_notMem hx]
  · filter_upwards [indL2v_ae G hG (v + w).2, indL2v_ae G hG v.2, indL2v_ae G hG w.2,
      Lp.coeFn_add v.2 w.2, Lp.coeFn_add (indL2v G hG v.2) (indL2v G hG w.2)]
      with x h1 h2 h3 h4 h5
    simp only [Prod.snd_add, Prod.mk_add_mk] at h1 ⊢
    rw [h5, h1, Pi.add_apply, h2, h3]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx, h4,
        Pi.add_apply]
    · simp [Set.indicator_of_notMem hx]

lemma restrictTo_smul {G : Set (RN N)} (hG : MeasurableSet G) (c : ℝ) (v : Amb N) :
    restrictTo G (c • v) = c • restrictTo G v := by
  simp only [restrictTo, dif_pos hG]
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [indL2_ae G hG (c • v).1, indL2_ae G hG v.1,
      Lp.coeFn_smul c v.1, Lp.coeFn_smul c (indL2 G hG v.1)] with x h1 h2 h3 h4
    simp only [Prod.smul_fst, Prod.smul_mk] at h1 ⊢
    rw [h4, h1, Pi.smul_apply, h2]
    by_cases hx : x ∈ G <;> simp [hx, h3]
  · filter_upwards [indL2v_ae G hG (c • v).2, indL2v_ae G hG v.2,
      Lp.coeFn_smul c v.2, Lp.coeFn_smul c (indL2v G hG v.2)] with x h1 h2 h3 h4
    simp only [Prod.smul_snd, Prod.smul_mk] at h1 ⊢
    rw [h4, h1, Pi.smul_apply, h2]
    by_cases hx : x ∈ G <;> simp [hx, h3]

lemma norm_restrictTo_le {G : Set (RN N)} (hG : MeasurableSet G) (v : Amb N) :
    ‖restrictTo G v‖ ≤ ‖v‖ := by
  simp only [restrictTo, dif_pos hG, Prod.norm_def]
  refine max_le_max ?_ ?_
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [indL2_ae G hG v.1] with x h
    rw [h]; exact norm_indicator_le_norm_self _ _
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [indL2v_ae G hG v.2] with x h
    rw [h]; exact norm_indicator_le_norm_self _ _

/-- Restriction to a measurable set as a continuous linear map. -/
def restrictCLM {G : Set (RN N)} (hG : MeasurableSet G) : Amb N →L[ℝ] Amb N :=
  LinearMap.mkContinuous
    { toFun := restrictTo G
      map_add' := restrictTo_add hG
      map_smul' := restrictTo_smul hG } 1
    (fun v => by simpa using norm_restrictTo_le hG v)

lemma restrictCLM_apply {G : Set (RN N)} (hG : MeasurableSet G) (v : Amb N) :
    restrictCLM hG v = restrictTo G v := rfl

lemma restrictTo_eq_self {G : Set (RN N)} (hG : MeasurableSet G) {v : Amb N}
    (hv : v ∈ vanishOn Gᶜ) : restrictTo G v = v := by
  obtain ⟨h1, h2⟩ := mem_vanishOn.mp hv
  rw [EventuallyEq, ae_restrict_iff' hG.compl] at h1 h2
  simp only [restrictTo, dif_pos hG]
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [indL2_ae G hG v.1, h1] with x h h'
    rw [h]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h' hx]; rfl
  · filter_upwards [indL2v_ae G hG v.2, h2] with x h h'
    rw [h]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h' hx]; rfl

lemma restrictTo_eq_zero {G S : Set (RN N)} (hG : MeasurableSet G) (hGS : G ⊆ S) {v : Amb N}
    (hv : v ∈ vanishOn S) : restrictTo G v = 0 := by
  obtain ⟨h1, h2⟩ := mem_vanishOn.mp hv
  have h1' := ae_restrict_of_ae_restrict_of_subset hGS h1
  have h2' := ae_restrict_of_ae_restrict_of_subset hGS h2
  rw [ae_restrict_iff' hG] at h1' h2'
  simp only [restrictTo, dif_pos hG]
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [indL2_ae G hG v.1, h1', Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))]
      with x h h' hz
    rw [h, Prod.fst_zero, hz]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, h' hx]
    · rw [Set.indicator_of_notMem hx]; rfl
  · filter_upwards [indL2v_ae G hG v.2, h2', Lp.coeFn_zero (RN N) 2 (volume : Measure (RN N))]
      with x h h' hz
    rw [h, Prod.snd_zero, hz]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, h' hx]
    · rw [Set.indicator_of_notMem hx]; rfl

/-- Restriction of an element of the form domain of a disjoint union of open sets to one of the
pieces lies in the form domain of that piece. -/
theorem restrictTo_mem_H_piece {ι : Type*} (D : ι → Set (RN N)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on D)) (i : ι) {v : Amb N} (hv : v ∈ H (⋃ i, D i)) :
    restrictTo (D i) v ∈ H (D i) := by
  have hm := (hD i).measurableSet
  rw [H_iUnion_of_disjoint D hD hdisj] at hv
  let S : Submodule ℝ (Amb N) := (H (D i)).comap (restrictCLM hm).toLinearMap
  have hS : IsClosed (S : Set (Amb N)) :=
    (Submodule.span ℝ (testGraph (D i))).isClosed_topologicalClosure.preimage
      (restrictCLM hm).continuous
  have hle : (⨆ i, H (D i)).topologicalClosure ≤ S := by
    refine Submodule.topologicalClosure_minimal _ (iSup_le fun k => ?_) hS
    intro w hw
    show restrictTo (D i) w ∈ H (D i)
    by_cases hk : k = i
    · subst hk
      rw [restrictTo_eq_self hm (H_le_vanishOn _ hw)]; exact hw
    · rw [restrictTo_eq_zero hm (Set.subset_compl_iff_disjoint_right.mpr (hdisj hk).symm)
        (H_le_vanishOn _ hw)]
      exact (H _).zero_mem
  exact hle hv

/-! ### Connected components -/

/-- The set of connected components of `D`. -/
def comps (D : Set (RN N)) : Set (Set (RN N)) := {C | ∃ x ∈ D, connectedComponentIn D x = C}

lemma mem_comps_props {D : Set (RN N)} (hD : IsOpen D) {C : Set (RN N)} (hC : C ∈ comps D) :
    IsOpen C ∧ C.Nonempty ∧ C ⊆ D ∧ IsConnected C := by
  obtain ⟨x, hx, rfl⟩ := hC
  exact ⟨hD.connectedComponentIn, ⟨x, mem_connectedComponentIn hx⟩,
    connectedComponentIn_subset _ _, isConnected_connectedComponentIn_iff.mpr hx⟩

lemma isDomain_of_mem_comps {D : Set (RN N)} (hD : IsAdmissible D) {C : Set (RN N)}
    (hC : C ∈ comps D) : IsDomain C :=
  have h := mem_comps_props hD.1 hC
  ⟨⟨h.1, h.2.1, hD.2.2.subset h.2.2.1⟩, h.2.2.2⟩

lemma comps_disjoint {D C C' : Set (RN N)} (hC : C ∈ comps D) (hC' : C' ∈ comps D)
    (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, rfl⟩ := hC'
  exact connectedComponentIn_disjoint_of_ne hne

lemma iUnion_comps (D : Set (RN N)) : ⋃ C : comps D, (C : Set (RN N)) = D := by
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨C, x, hx, rfl⟩, hz⟩
    exact connectedComponentIn_subset _ _ hz
  · intro hz
    exact ⟨⟨_, z, hz, rfl⟩, mem_connectedComponentIn hz⟩

lemma countable_comps {D : Set (RN N)} (hD : IsOpen D) : Countable (comps D) :=
  Pairwise.countable_of_isOpen_disjoint (s := fun C : comps D => (C : Set (RN N)))
    (fun C C' hne => comps_disjoint C.2 C'.2 (fun h => hne (Subtype.ext h)))
    (fun C => (mem_comps_props hD C.2).1) (fun C => (mem_comps_props hD C.2).2.1)

/-- Restriction of an element of `H_D` (`D` open) to a connected component of `D` lies in the
form domain of the component. -/
theorem restrictTo_mem_H_comp {D : Set (RN N)} (hD : IsOpen D) {C : Set (RN N)}
    (hC : C ∈ comps D) {v : Amb N} (hv : v ∈ H D) : restrictTo C v ∈ H C := by
  rw [← iUnion_comps D] at hv
  exact restrictTo_mem_H_piece (fun C : comps D => (C : Set (RN N)))
    (fun C => (mem_comps_props hD C.2).1)
    (fun C C' hne => comps_disjoint C.2 C'.2 (fun h => hne (Subtype.ext h))) ⟨C, hC⟩ hv

/-! ### Local agreement and the weak equation -/

/-- If `w` and `u` agree on `G` and `φ` vanishes off `G`, the forms agree. -/
lemma forms_eq_of_agree {G : Set (RN N)} (hG : MeasurableSet G) {φ : Amb N}
    (hφ : φ ∈ vanishOn Gᶜ) {w u : Amb N}
    (h1 : (w.1 : RN N → ℝ) =ᵐ[volume.restrict G] u.1)
    (h2 : (w.2 : RN N → RN N) =ᵐ[volume.restrict G] u.2) :
    qf w φ = qf u φ ∧ l2 w φ = l2 u φ := by
  obtain ⟨hφ1, hφ2⟩ := mem_vanishOn.mp hφ
  rw [EventuallyEq, ae_restrict_iff' hG.compl] at hφ1 hφ2
  rw [EventuallyEq, ae_restrict_iff' hG] at h1 h2
  constructor
  · rw [qf, qf, L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [h2, hφ2] with x hx hx'
    by_cases hxG : x ∈ G
    · rw [hx hxG]
    · simp [hx' hxG]
  · rw [l2, l2, L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [h1, hφ1] with x hx hx'
    by_cases hxG : x ∈ G
    · rw [hx hxG]
    · simp [hx' hxG]

/-- An element of `H_G` agreeing on `G ⊆ D` with a weak solution in `D` is a weak solution
in `G`. -/
lemma weak_of_agree {D G : Set (RN N)} (hG : MeasurableSet G) (hGD : G ⊆ D) {u w : Amb N}
    {lam : ℝ} (hu : ∀ φ ∈ H D, qf u φ = lam * l2 u φ)
    (h1 : (w.1 : RN N → ℝ) =ᵐ[volume.restrict G] u.1)
    (h2 : (w.2 : RN N → RN N) =ᵐ[volume.restrict G] u.2) :
    ∀ φ ∈ H G, qf w φ = lam * l2 w φ := by
  intro φ hφ
  obtain ⟨e1, e2⟩ := forms_eq_of_agree hG (H_le_vanishOn G hφ) h1 h2
  rw [e1, e2]
  exact hu φ (H_mono hGD hφ)

lemma restrictTo_agree {G : Set (RN N)} (hG : MeasurableSet G) (v : Amb N) :
    ((restrictTo G v).1 : RN N → ℝ) =ᵐ[volume.restrict G] v.1 ∧
    ((restrictTo G v).2 : RN N → RN N) =ᵐ[volume.restrict G] v.2 := by
  simp only [restrictTo, dif_pos hG]
  constructor
  · rw [EventuallyEq, ae_restrict_iff' hG]
    filter_upwards [indL2_ae G hG v.1] with x h hx
    rw [h, Set.indicator_of_mem hx]
  · rw [EventuallyEq, ae_restrict_iff' hG]
    filter_upwards [indL2v_ae G hG v.2] with x h hx
    rw [h, Set.indicator_of_mem hx]

lemma posPart_agree {D G : Set (RN N)} (hDm : MeasurableSet D) {v : Amb N} {f : RN N → ℝ}
    (hf : IsContRep D v f) (hG : MeasurableSet G) (hGP : G ⊆ posSign D f) :
    ((posPart v).1 : RN N → ℝ) =ᵐ[volume.restrict G] v.1 ∧
    ((posPart v).2 : RN N → RN N) =ᵐ[volume.restrict G] v.2 := by
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  constructor
  · rw [EventuallyEq, ae_restrict_iff' hG]
    filter_upwards [posPart_fst_ae v, hf2] with x h1 h2 hx
    rw [h1, h2 (hGP hx).1, max_eq_left (hGP hx).2.le]
  · rw [EventuallyEq, ae_restrict_iff' hG]
    filter_upwards [posPart_snd_ae v, hf2] with x h1 h2 hx
    have : x ∈ posSetL2 v.1 := by
      show 0 < (v.1 : RN N → ℝ) x
      rw [h2 (hGP hx).1]; exact (hGP hx).2
    rw [h1, Set.indicator_of_mem this]

/-! ### Nodal localization -/

/-- Positive nodal components: the restriction of `u₊` to a connected component `G` of `D₊(u)`
is a (nonnegative) eigenfunction of `G` with eigenvalue `λ`, and `λ = λ₁(G)`. -/
theorem nodal_pos_comp (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {u : Amb N}
    {lam : ℝ} (hu : IsEigenfunction D u lam) {f : RN N → ℝ} (hrep : IsContRep D u f)
    {x : RN N} (hx : x ∈ posSign D f) :
    IsEigenfunction (connectedComponentIn (posSign D f) x)
        (restrictTo (connectedComponentIn (posSign D f) x) (posPart u)) lam ∧
      eigenvalue (connectedComponentIn (posSign D f) x) 1 = lam := by
  set P := posSign D f with hPdef
  set G := connectedComponentIn P x with hGdef
  have hPo : IsOpen P := isOpen_posSign hD.1 hrep.1
  have hGc : G ∈ comps P := ⟨x, hx, rfl⟩
  obtain ⟨hGo, hGne, hGP, -⟩ := mem_comps_props hPo hGc
  have hGm : MeasurableSet G := hGo.measurableSet
  have hDm : MeasurableSet D := hD.1.measurableSet
  have hGdom : IsDomain G :=
    isDomain_of_mem_comps ⟨hPo, ⟨x, hx⟩, hD.2.2.subset (posSign_subset D f)⟩ hGc
  have hGD : G ⊆ D := hGP.trans (posSign_subset D f)
  have hpH : posPart u ∈ H P := posPart_mem_H_posSign hD hu.1 hrep
  set w := restrictTo G (posPart u) with hwdef
  have hwH : w ∈ H G := restrictTo_mem_H_comp hPo hGc hpH
  obtain ⟨r1, r2⟩ := restrictTo_agree hGm (posPart u)
  obtain ⟨p1, p2⟩ := posPart_agree hDm hrep hGm hGP
  have a1 : (w.1 : RN N → ℝ) =ᵐ[volume.restrict G] u.1 := r1.trans p1
  have a2 : (w.2 : RN N → RN N) =ᵐ[volume.restrict G] u.2 := r2.trans p2
  have hweak := weak_of_agree hGm hGD hu.2.2 a1 a2
  have hf2 := ae_restrict_of_ae_restrict_of_subset hGD hrep.2
  have hw0 : w ≠ 0 := by
    intro h0
    have hz : (w.1 : RN N → ℝ) =ᵐ[volume] 0 := by
      rw [h0]; exact Lp.coeFn_zero ℝ 2 volume
    have hfalse : ∀ᵐ y ∂volume.restrict G, False := by
      have hz' := ae_restrict_of_ae (s := G) hz
      have hpos : ∀ᵐ y ∂volume.restrict G, 0 < f y :=
        (ae_restrict_iff' hGm).mpr (Eventually.of_forall fun y hy => (hGP hy).2)
      filter_upwards [hz', a1, hf2, hpos] with y h1 h2 h3 h4
      rw [← h2, h1] at h3
      simp only [Pi.zero_apply] at h3
      linarith
    have hμ : volume G = 0 := by
      rw [ae_iff] at hfalse
      simpa using hfalse
    exact (hGo.measure_pos volume hGne).ne' hμ
  have hnn : 0 ≤ᵐ[volume] (w.1 : RN N → ℝ) := by
    simp only [hwdef, restrictTo, dif_pos hGm]
    filter_upwards [indL2_ae G hGm (posPart u).1, posPart_fst_ae u] with y h1 h2
    rw [h1, Pi.zero_apply]
    by_cases hy : y ∈ G
    · rw [Set.indicator_of_mem hy, h2]; exact le_max_right _ _
    · rw [Set.indicator_of_notMem hy]
  refine ⟨⟨hwH, hw0, hweak⟩, ?_⟩
  obtain ⟨-, q, g, hq, hg, hgpos⟩ := ground_state hN hGdom
  have hpos := l2_pos_of_nonneg hGdom.1 hwH hw0 hnn hq.1 hg hgpos
  have e1 := hweak q hq.1
  have e2 := hq.2.2 w hwH
  rw [qf_comm, l2_comm] at e2
  have : (lam - eigenvalue G 1) * l2 w q = 0 := by rw [sub_mul]; linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- Smoothness part of nodal localization: an eigenfunction has a smooth (indeed real
analytic on each component) representative on `D`. -/
theorem eigenfunction_smooth_rep {D : Set (RN N)} (hD : IsAdmissible D)
    {u : Amb N} {lam : ℝ} (hu : IsEigenfunction D u lam) :
    ∃ f : RN N → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f D ∧ IsContRep D u f := by
  have hex : ∀ C ∈ comps D, ∃ g : RN N → ℝ, AnalyticOnNhd ℝ g C ∧
      (u.1 : RN N → ℝ) =ᵐ[volume.restrict C] g := by
    intro C hC
    obtain ⟨hCo, -, hCD, -⟩ := mem_comps_props hD.1 hC
    have hCm := hCo.measurableSet
    obtain ⟨r1, r2⟩ := restrictTo_agree hCm u
    obtain ⟨g, hga, hgc⟩ := ext_analytic (isDomain_of_mem_comps hD hC)
      (restrictTo_mem_H_comp hD.1 hC hu.1) (weak_of_agree hCm hCD hu.2.2 r1 r2)
    exact ⟨g, hga, r1.symm.trans hgc.2⟩
  choose! g hga hgu using hex
  set F : RN N → ℝ := fun y => g (connectedComponentIn D y) y with hF
  have hcomp : ∀ y ∈ D, connectedComponentIn D y ∈ comps D := fun y hy => ⟨y, hy, rfl⟩
  have key : ∀ y, Set.EqOn F (g (connectedComponentIn D y)) (connectedComponentIn D y) := by
    intro y z hz
    simp only [hF]
    rw [← connectedComponentIn_eq hz]
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F D := by
    refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
    refine ⟨connectedComponentIn D y, hD.1.connectedComponentIn,
      mem_connectedComponentIn hy, ?_⟩
    refine (((hga _ (hcomp y hy)).contDiffOn (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      hD.1.connectedComponentIn.uniqueDiffOn).mono Set.inter_subset_right).congr ?_
    intro z hz
    exact key y hz.2
  refine ⟨F, hs, hs.continuousOn, ?_⟩
  haveI := countable_comps hD.1
  rw [← iUnion_comps D]
  refine (ae_restrict_iUnion_iff _ _).mpr fun C => ?_
  obtain ⟨C, y, hy, rfl⟩ := C
  have hm := (hD.1.connectedComponentIn (x := y)).measurableSet
  refine (hgu _ (hcomp y hy)).trans ?_
  rw [EventuallyEq, ae_restrict_iff' hm]
  exact Eventually.of_forall fun z hz => (key y hz).symm

/-- **Nodal localization (full statement).** An eigenfunction is smooth in `D`; its sign
truncations lie in the form domains of the sign sets, and the restrictions to the connected
components of the sign sets are (up to sign) positive first eigenfunctions with the same
eigenvalue.  (Derived from the external spectral package, the positive ground state, interior
analyticity, Lemma 3.1 and the disjoint-union form domain.) -/
theorem nodal (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {u : Amb N} {lam : ℝ}
    (hu : IsEigenfunction D u lam) :
    ∃ f : RN N → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f D ∧ IsContRep D u f ∧
      posPart u ∈ H (posSign D f) ∧ negPart u ∈ H (negSign D f) ∧
      (∀ x ∈ posSign D f,
        IsEigenfunction (connectedComponentIn (posSign D f) x)
          (restrictTo (connectedComponentIn (posSign D f) x) (posPart u)) lam ∧
        eigenvalue (connectedComponentIn (posSign D f) x) 1 = lam) ∧
      (∀ x ∈ negSign D f,
        IsEigenfunction (connectedComponentIn (negSign D f) x)
          (restrictTo (connectedComponentIn (negSign D f) x) (negPart u)) lam ∧
        eigenvalue (connectedComponentIn (negSign D f) x) 1 = lam) := by
  obtain ⟨f, hs, hrep⟩ := eigenfunction_smooth_rep hD hu
  obtain ⟨h1, h2, -, -⟩ := lemma_parts hD hu.1 hrep
  refine ⟨f, hs, hrep, h1, h2, fun x hx => nodal_pos_comp hN hD hu hrep hx, fun x hx => ?_⟩
  have hu' : IsEigenfunction D (-u) lam :=
    ⟨(H D).neg_mem hu.1, neg_ne_zero.mpr hu.2.1, fun φ hφ => by
      simp only [qf_neg_left, l2_neg_left, hu.2.2 φ hφ]; ring⟩
  rw [negSign_eq_posSign_neg] at hx ⊢
  exact nodal_pos_comp hN hD hu' hrep.neg hx

end FourthRatio

end

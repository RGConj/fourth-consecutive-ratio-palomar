module

public import RequestProject.Basic

/-!
# The spectral theorem for the Dirichlet form, abstract part

Let `X ≤ L² × L²` be a closed subspace on which the `L²` part is positive definite, which is
infinite dimensional, satisfies a Poincaré inequality `‖v‖² ≤ C q(v,v)` and embeds compactly into
`L²` (bounded sequences have `L²`-convergent subsequences).  Then the Rayleigh quotient
`q(v,v)/‖v‖²` has a complete `L²`-orthonormal sequence of eigenfunctions in `X`, built by
successive minimisation (direct method), whose eigenvalues are the min–max values, are positive,
nondecreasing, tend to `+∞`, and give the spectral expansions of `q` and of the `L²` norm.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The min–max values of the Rayleigh quotient over `j`-dimensional subspaces of `X`. -/
def minmax (X : Submodule ℝ (Amb N)) (j : ℕ) : ℝ :=
  sInf ((fun V : Submodule ℝ (Amb N) => sSup (rayleigh '' {v | v ∈ V ∧ v ≠ 0})) ''
    {V | V ≤ X ∧ Module.finrank ℝ V = j})

lemma eigenvalue_eq_minmax (D : Set (RN N)) (j : ℕ) : eigenvalue D j = minmax (H D) j := rfl

/-- Hypotheses of the abstract spectral theorem. -/
structure SpecHyp (X : Submodule ℝ (Amb N)) : Prop where
  closed : IsClosed (X : Set (Amb N))
  pos : ∀ v ∈ X, l2 v v = 0 → v = 0
  poinc : ∃ C, ∀ v ∈ X, l2 v v ≤ C * qf v v
  comp : ∀ v : ℕ → Amb N, (∀ n, v n ∈ X) → (∃ C, ∀ n, ‖v n‖ ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : L2 N, Tendsto (fun n => (v (φ n)).1) atTop (𝓝 f)
  infdim : ¬ FiniteDimensional ℝ X

lemma l2_self_eq_norm_sq (v : Amb N) : l2 v v = ‖v.1‖ ^ 2 := real_inner_self_eq_norm_sq _
lemma qf_self_eq_norm_sq (v : Amb N) : qf v v = ‖v.2‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- `u` minimises the Rayleigh quotient on `Y` and is normalised. -/
def IsMinimizer (Y : Submodule ℝ (Amb N)) (u : Amb N) : Prop :=
  u ∈ Y ∧ l2 u u = 1 ∧ ∀ v ∈ Y, qf u u * l2 v v ≤ qf v v

/-- Normalisation of a vector with positive `L²` norm. -/
lemma normalize_l2 {z : Amb N} (h : 0 < l2 z z) :
    l2 ((Real.sqrt (l2 z z))⁻¹ • z) ((Real.sqrt (l2 z z))⁻¹ • z) = 1 ∧
      qf ((Real.sqrt (l2 z z))⁻¹ • z) ((Real.sqrt (l2 z z))⁻¹ • z) = qf z z / l2 z z := by
  have hs : (Real.sqrt (l2 z z))⁻¹ * (Real.sqrt (l2 z z))⁻¹ = (l2 z z)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt h.le]
  simp only [l2_smul_left, l2_smul_right, qf_smul_left, qf_smul_right, ← mul_assoc, hs]
  exact ⟨inv_mul_cancel₀ h.ne', by rw [inv_mul_eq_div]⟩

/-- A minimising sequence converging in `L²` is Cauchy in `L² × L²` (parallelogram law). -/
lemma cauchySeq_of_minimizing {Y : Submodule ℝ (Amb N)} {μ : ℝ}
    (hlow : ∀ z ∈ Y, μ * l2 z z ≤ qf z z) (w : ℕ → Amb N) (hwY : ∀ n, w n ∈ Y)
    (hw1 : ∀ n, l2 (w n) (w n) = 1) (hq : Tendsto (fun n => qf (w n) (w n)) atTop (𝓝 μ))
    {f : L2 N} (hf : Tendsto (fun n => (w n).1) atTop (𝓝 f)) : CauchySeq w := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0, ← prod_atTop_atTop_eq]
  have h' : ∀ n, ‖(w n).1‖ = 1 := fun n => by
    have := hw1 n
    rw [l2_self_eq_norm_sq] at this
    have h0 := norm_nonneg (w n).1
    nlinarith
  have hf1 : ‖f‖ = 1 := by
    have h := (continuous_norm.tendsto f).comp hf
    simp only [Function.comp_def, h'] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  set g : ℕ × ℕ → ℝ := fun p => 2 * qf (w p.1) (w p.1) + 2 * qf (w p.2) (w p.2) -
    μ * ‖(w p.1).1 + (w p.2).1‖ ^ 2 with hgdef
  have hg : Tendsto g (atTop ×ˢ atTop) (𝓝 0) := by
    have h1 : Tendsto (fun p : ℕ × ℕ => (w p.1).1) (atTop ×ˢ atTop) (𝓝 f) := hf.comp tendsto_fst
    have h2 : Tendsto (fun p : ℕ × ℕ => (w p.2).1) (atTop ×ˢ atTop) (𝓝 f) := hf.comp tendsto_snd
    have h3 := ((h1.add h2).norm).pow 2
    have h4 := ((hq.comp tendsto_fst).const_mul 2).add ((hq.comp tendsto_snd).const_mul 2)
    have := h4.sub (h3.const_mul μ)
    have hlimit : 2 * μ + 2 * μ - μ * ‖f + f‖ ^ 2 = 0 := by
      rw [← two_smul ℝ f, norm_smul, hf1]
      norm_num
      ring
    simpa only [Function.comp_apply, hlimit] using this
  have hbound : ∀ p : ℕ × ℕ,
      dist (w p.1) (w p.2) ≤ ‖(w p.1).1 - (w p.2).1‖ + Real.sqrt (g p) := by
    intro p
    rw [dist_eq_norm]
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · simp only [Prod.fst_sub]
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    · have hpar : ‖(w p.1).2 - (w p.2).2‖ ^ 2 + ‖(w p.1).2 + (w p.2).2‖ ^ 2 =
          2 * ‖(w p.1).2‖ ^ 2 + 2 * ‖(w p.2).2‖ ^ 2 := by
        rw [norm_sub_sq_real, norm_add_sq_real]; ring
      have hl := hlow _ (Y.add_mem (hwY p.1) (hwY p.2))
      rw [l2_self_eq_norm_sq, qf_self_eq_norm_sq] at hl
      simp only [Prod.fst_add, Prod.snd_add] at hl
      have hle : ‖(w p.1).2 - (w p.2).2‖ ^ 2 ≤ g p := by
        simp only [g, qf_self_eq_norm_sq]; linarith
      have : ‖(w p.1).2 - (w p.2).2‖ ≤ Real.sqrt (g p) := Real.le_sqrt_of_sq_le hle
      simp only [Prod.snd_sub]
      exact this.trans (le_add_of_nonneg_left (norm_nonneg _))
  refine squeeze_zero (fun _ => dist_nonneg) hbound ?_
  have h1 : Tendsto (fun p : ℕ × ℕ => ‖(w p.1).1 - (w p.2).1‖) (atTop ×ˢ atTop) (𝓝 0) := by
    have := ((hf.comp tendsto_fst).sub (hf.comp tendsto_snd)).norm
    simpa using this
  have h2 : Tendsto (fun p => Real.sqrt (g p)) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hg
  simpa using h1.add h2

/-- Existence of a minimiser of the Rayleigh quotient on a nonzero closed subspace (direct
method: a minimising sequence is Cauchy, by compactness and the parallelogram law). -/
lemma exists_minimizer {X : Submodule ℝ (Amb N)} (hX : SpecHyp X) {Y : Submodule ℝ (Amb N)}
    (hYX : Y ≤ X) (hYc : IsClosed (Y : Set (Amb N))) (hY : Y ≠ ⊥) :
    ∃ u, IsMinimizer Y u := by
  set S : Set ℝ := (fun v => qf v v) '' {v | v ∈ Y ∧ l2 v v = 1} with hS
  have hposY : ∀ z ∈ Y, z ≠ 0 → 0 < l2 z z := fun z hz hz0 =>
    lt_of_le_of_ne (l2_self_nonneg _) (fun h => hz0 (hX.pos _ (hYX hz) h.symm))
  obtain ⟨w0, hw0Y, hw00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have hSne : S.Nonempty :=
    ⟨_, ⟨_, ⟨Y.smul_mem _ hw0Y, (normalize_l2 (hposY w0 hw0Y hw00)).1⟩, rfl⟩⟩
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨v, -, rfl⟩; exact qf_self_nonneg v⟩
  set μ := sInf S with hμ
  have hμ0 : 0 ≤ μ := le_csInf hSne (by rintro _ ⟨v, -, rfl⟩; exact qf_self_nonneg v)
  have hlow : ∀ z ∈ Y, μ * l2 z z ≤ qf z z := by
    intro z hz
    rcases (l2_self_nonneg z).eq_or_lt with h | h
    · rw [← h, mul_zero]; exact qf_self_nonneg z
    · have hn := normalize_l2 h
      have : μ ≤ qf z z / l2 z z := by
        rw [← hn.2]
        exact csInf_le hSbdd ⟨_, ⟨Y.smul_mem _ hz, hn.1⟩, rfl⟩
      rwa [le_div_iff₀ h] at this
  have hseq : ∀ n : ℕ, ∃ v, v ∈ Y ∧ l2 v v = 1 ∧ qf v v < μ + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨v, ⟨hvY, hv1⟩, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt hSne
        (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith : μ < μ + 1 / ((n : ℝ) + 1))
    exact ⟨v, hvY, hv1, hlt⟩
  choose v hvY hv1 hvq using hseq
  have hb : ∀ n, ‖v n‖ ≤ μ + 2 := by
    intro n
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · have := hv1 n
      rw [l2_self_eq_norm_sq] at this
      have h0 := norm_nonneg (v n).1
      nlinarith
    · have := hvq n
      rw [qf_self_eq_norm_sq] at this
      have h0 := norm_nonneg (v n).2
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith
  obtain ⟨φ, hφ, f, hf⟩ := hX.comp v (fun n => hYX (hvY n)) ⟨μ + 2, hb⟩
  set w := fun n => v (φ n) with hw
  have hq : Tendsto (fun n => qf (w n) (w n)) atTop (𝓝 μ) := by
    have hup : Tendsto (fun n => μ + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 μ) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_add μ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
      (fun n => (hvq (φ n)).le)
    have := hlow _ (hvY (φ n))
    rwa [hv1, mul_one] at this
  have hcau := cauchySeq_of_minimizing hlow w (fun n => hvY _) (fun n => hv1 _) hq hf
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcau
  have huY : u ∈ Y := hYc.mem_of_tendsto hu (Eventually.of_forall fun n => hvY _)
  have hu1 : l2 u u = 1 := by
    have h := (continuous_l2.tendsto (u, u)).comp (hu.prodMk_nhds hu)
    simp only [Function.comp_def] at h
    simp only [w, hv1] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have huq : qf u u = μ := by
    have h := (continuous_qf.tendsto (u, u)).comp (hu.prodMk_nhds hu)
    simp only [Function.comp_def] at h
    exact tendsto_nhds_unique h hq
  refine ⟨u, huY, hu1, fun z hz => ?_⟩
  rw [huq]
  exact hlow z hz

/-- Euler–Lagrange equation for a minimiser. -/
lemma IsMinimizer.euler {Y : Submodule ℝ (Amb N)} {u : Amb N} (hu : IsMinimizer Y u) :
    ∀ φ ∈ Y, qf u φ = qf u u * l2 u φ := by
  intro φ hφ
  obtain ⟨huY, hu1, hmin⟩ := hu
  set μ := qf u u
  set a := qf φ φ - μ * l2 φ φ
  set b := qf u φ - μ * l2 u φ
  have ha : 0 ≤ a := by have := hmin φ hφ; simp only [a]; linarith
  have key : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a := by
    intro t
    have h := hmin (u + t • φ) (Y.add_mem huY (Y.smul_mem t hφ))
    simp only [qf_add_left, qf_add_right, qf_smul_left, qf_smul_right, l2_add_left,
      l2_add_right, l2_smul_left, l2_smul_right, qf_comm φ u, l2_comm φ u, hu1] at h
    simp only [a, b]
    nlinarith
  have h := key (-b / (a + 1))
  have ha1 : 0 < a + 1 := by linarith
  have hb : b = 0 := by
    by_contra hb
    have hb2 : 0 < b ^ 2 := by positivity
    have : 2 * (-b / (a + 1)) * b + (-b / (a + 1)) ^ 2 * a = -(b ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
      field_simp
      ring
    rw [this] at h
    have : 0 < b ^ 2 * (a + 2) / (a + 1) ^ 2 := by positivity
    linarith [neg_div ((a + 1) ^ 2) (b ^ 2 * (a + 2))]
  simp only [b] at hb
  linarith

/-! ### Successive minimisation -/

/-- The subspace of `X` of vectors `L²`-orthogonal to a finite list. -/
def Yperp (X : Submodule ℝ (Amb N)) (S : List (Amb N)) : Submodule ℝ (Amb N) where
  carrier := {v | v ∈ X ∧ ∀ s ∈ S, l2 s v = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨X.add_mem ha hb, fun s hs => by simp [ha' s hs, hb' s hs]⟩
  zero_mem' := ⟨X.zero_mem, fun s _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨X.smul_mem c ha, fun s hs => by simp [ha' s hs]⟩

lemma mem_Yperp {X : Submodule ℝ (Amb N)} {S : List (Amb N)} {v : Amb N} :
    v ∈ Yperp X S ↔ v ∈ X ∧ ∀ s ∈ S, l2 s v = 0 := Iff.rfl

lemma Yperp_le (X : Submodule ℝ (Amb N)) (S : List (Amb N)) : Yperp X S ≤ X :=
  fun _ hv => hv.1

lemma isClosed_Yperp {X : Submodule ℝ (Amb N)} (hX : IsClosed (X : Set (Amb N)))
    (S : List (Amb N)) : IsClosed (Yperp X S : Set (Amb N)) := by
  have : (Yperp X S : Set (Amb N)) = (X : Set (Amb N)) ∩ ⋂ s ∈ S, {v | l2 s v = 0} := by
    ext v
    simp only [SetLike.mem_coe, mem_Yperp, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  have hclosed : ∀ s : Amb N, IsClosed {v : Amb N | l2 s v = 0} := by
    intro s
    have hc : Continuous (fun v : Amb N => l2 s v) := by
      change Continuous (fun v : Amb N => ⟪s.1, v.1⟫)
      exact continuous_const.inner continuous_fst
    exact isClosed_eq hc continuous_const
  exact hX.inter (isClosed_iInter fun s => isClosed_iInter fun _ => hclosed s)

lemma Yperp_ne_bot {X : Submodule ℝ (Amb N)} (hX : ¬ FiniteDimensional ℝ X) (S : List (Amb N)) :
    Yperp X S ≠ ⊥ := by
  intro hbot
  apply hX
  let T : X →ₗ[ℝ] (Fin S.length → ℝ) :=
    { toFun := fun v i => l2 (S.get i) v
      map_add' := by intro a b; ext i; simp
      map_smul' := by intro c a; ext i; simp }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (v : Amb N) ∈ Yperp X S := ⟨v.2, fun s hs => by
      obtain ⟨i, rfl⟩ := List.get_of_mem hs
      exact congrFun (LinearMap.mem_ker.mp hv) i⟩
    rw [hbot] at hv'
    exact Subtype.ext ((Submodule.mem_bot ℝ).mp hv')
  exact Module.Finite.of_injective T hinj

open Classical in
/-- A chosen minimiser (junk value `0` if there is none). -/
def minimizer (Y : Submodule ℝ (Amb N)) : Amb N :=
  if h : ∃ u, IsMinimizer Y u then h.choose else 0

lemma minimizer_spec {Y : Submodule ℝ (Amb N)} (h : ∃ u, IsMinimizer Y u) :
    IsMinimizer Y (minimizer Y) := by
  classical
  unfold minimizer
  rw [dif_pos h]
  exact h.choose_spec

/-- The list of the first `k` successive minimisers. -/
def eList (X : Submodule ℝ (Amb N)) : ℕ → List (Amb N)
  | 0 => []
  | k + 1 => eList X k ++ [minimizer (Yperp X (eList X k))]

/-- The `k`-th successive minimiser (the `(k+1)`-st eigenfunction). -/
def eseq (X : Submodule ℝ (Amb N)) (k : ℕ) : Amb N := minimizer (Yperp X (eList X k))

lemma mem_eList {X : Submodule ℝ (Amb N)} {k : ℕ} {x : Amb N} :
    x ∈ eList X k ↔ ∃ i < k, eseq X i = x := by
  induction k with
  | zero => simp [eList]
  | succ k ih =>
    simp only [eList, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨k, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr rfl

lemma mem_Yperp_eList {X : Submodule ℝ (Amb N)} {k : ℕ} {v : Amb N} :
    v ∈ Yperp X (eList X k) ↔ v ∈ X ∧ ∀ i < k, l2 (eseq X i) v = 0 := by
  rw [mem_Yperp]
  refine and_congr_right fun _ => ⟨fun h i hi => h _ (mem_eList.mpr ⟨i, hi, rfl⟩), ?_⟩
  intro h s hs
  obtain ⟨i, hi, rfl⟩ := mem_eList.mp hs
  exact h i hi

section seq

variable {X : Submodule ℝ (Amb N)} (hX : SpecHyp X)
include hX

lemma eseq_isMinimizer (k : ℕ) : IsMinimizer (Yperp X (eList X k)) (eseq X k) :=
  minimizer_spec (exists_minimizer hX (Yperp_le X _) (isClosed_Yperp hX.closed _)
    (Yperp_ne_bot hX.infdim _))

lemma eseq_mem (k : ℕ) : eseq X k ∈ X := ((eseq_isMinimizer hX k).1).1

lemma eseq_norm (k : ℕ) : l2 (eseq X k) (eseq X k) = 1 := (eseq_isMinimizer hX k).2.1

lemma eseq_low {k : ℕ} {v : Amb N} (hv : v ∈ X) (hperp : ∀ i < k, l2 (eseq X i) v = 0) :
    qf (eseq X k) (eseq X k) * l2 v v ≤ qf v v :=
  (eseq_isMinimizer hX k).2.2 v (mem_Yperp_eList.mpr ⟨hv, hperp⟩)

lemma eseq_orth (i j : ℕ) : l2 (eseq X i) (eseq X j) = if i = j then 1 else 0 := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg h.ne]
    exact (mem_Yperp_eList.mp (eseq_isMinimizer hX j).1).2 i h
  · rw [if_pos rfl, eseq_norm hX]
  · rw [if_neg h.ne', l2_comm]
    exact (mem_Yperp_eList.mp (eseq_isMinimizer hX i).1).2 j h

lemma eseq_mono : Monotone (fun k => qf (eseq X k) (eseq X k)) := by
  refine monotone_nat_of_le_succ fun k => ?_
  have h := eseq_low hX (k := k) (eseq_mem hX (k + 1)) (fun i hi => by
    rw [eseq_orth hX, if_neg (by omega)])
  rwa [eseq_norm hX, mul_one] at h

/-- Partial sums of the expansion in the first `k` eigenfunctions. -/
def psum (X : Submodule ℝ (Amb N)) (v : Amb N) (k : ℕ) : Amb N :=
  ∑ i ∈ Finset.range k, l2 (eseq X i) v • eseq X i

omit hX in
lemma psum_mem' {k : ℕ} {v : Amb N} (hmem : ∀ i, eseq X i ∈ X) : psum X v k ∈ X :=
  X.sum_mem fun i _ => X.smul_mem _ (hmem i)

lemma l2_eseq_psum {v : Amb N} {k j : ℕ} :
    l2 (eseq X j) (psum X v k) = if j < k then l2 (eseq X j) v else 0 := by
  simp only [psum, l2_sum_right, l2_smul_right, eseq_orth hX, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma sub_psum_perp {v : Amb N} {k : ℕ} (hv : v ∈ X) :
    v - psum X v k ∈ Yperp X (eList X k) := by
  refine mem_Yperp_eList.mpr ⟨X.sub_mem hv (psum_mem' (eseq_mem hX)), fun i hi => ?_⟩
  rw [l2_sub_right, l2_eseq_psum hX, if_pos hi, sub_self]

/-- The successive minimisers are eigenfunctions on all of `X`. -/
lemma eseq_eigen (k : ℕ) :
    ∀ φ ∈ X, qf (eseq X k) φ = qf (eseq X k) (eseq X k) * l2 (eseq X k) φ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro φ hφ
  have heul := (eseq_isMinimizer hX k).euler
  have h1 := heul _ (sub_psum_perp hX (k := k) hφ)
  have hq : qf (eseq X k) (psum X φ k) = 0 := by
    simp only [psum, qf_sum_right, qf_smul_right]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < k := Finset.mem_range.mp hi
    rw [qf_comm, ih i hi' _ (eseq_mem hX k), eseq_orth hX, if_neg hi'.ne]
    simp
  have hl : l2 (eseq X k) (psum X φ k) = 0 := by
    rw [l2_eseq_psum hX, if_neg (lt_irrefl k)]
  rw [qf_sub_right, l2_sub_right, hq, hl, sub_zero, sub_zero] at h1
  exact h1

lemma eseq_qf (i j : ℕ) :
    qf (eseq X i) (eseq X j) = if i = j then qf (eseq X i) (eseq X i) else 0 := by
  rw [eseq_eigen hX i _ (eseq_mem hX j), eseq_orth hX]
  split_ifs <;> simp

end seq

/-! ### Growth of the eigenvalues, expansions, min–max -/

section seq2

variable {X : Submodule ℝ (Amb N)} (hX : SpecHyp X)
include hX

lemma eseq_tendsto : Tendsto (fun k => qf (eseq X k) (eseq X k)) atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone (eseq_mono hX) ?_
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hb⟩ := hcon
  have hbd : ∀ k, ‖eseq X k‖ ≤ b + 2 := by
    intro k
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · have := eseq_norm hX k
      rw [l2_self_eq_norm_sq] at this
      have h0 := norm_nonneg (eseq X k).1
      have := qf_self_nonneg (eseq X 0)
      have := hb 0
      nlinarith
    · have := hb k
      rw [qf_self_eq_norm_sq] at this
      have h0 := norm_nonneg (eseq X k).2
      have := qf_self_nonneg (eseq X 0)
      have := hb 0
      nlinarith
  obtain ⟨φ, hφ, f, hf⟩ := hX.comp (eseq X) (eseq_mem hX) ⟨_, hbd⟩
  have h1 : Tendsto (fun n => ‖(eseq X (φ (n + 1))).1 - (eseq X (φ n)).1‖) atTop (𝓝 0) := by
    have := ((hf.comp (tendsto_add_atTop_nat 1)).sub hf).norm
    simpa using this
  have h2 : ∀ n, ‖(eseq X (φ (n + 1))).1 - (eseq X (φ n)).1‖ = Real.sqrt 2 := by
    intro n
    have hne : φ (n + 1) ≠ φ n := (hφ (Nat.lt_succ_self n)).ne'
    have : ‖(eseq X (φ (n + 1))).1 - (eseq X (φ n)).1‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real]
      have e1 := eseq_orth hX (φ (n + 1)) (φ (n + 1))
      have e2 := eseq_orth hX (φ n) (φ n)
      have e3 := eseq_orth hX (φ (n + 1)) (φ n)
      simp only [if_neg hne] at e1 e2 e3
      rw [l2_self_eq_norm_sq] at e1 e2
      rw [show ⟪(eseq X (φ (n + 1))).1, (eseq X (φ n)).1⟫ = 0 from e3, e1, e2]
      norm_num
    rw [← this, Real.sqrt_sq (norm_nonneg _)]
  simp only [h2] at h1
  have := tendsto_nhds_unique tendsto_const_nhds h1
  exact absurd this (by positivity)

lemma eseq_pos : 0 < qf (eseq X 0) (eseq X 0) := by
  obtain ⟨C, hC⟩ := hX.poinc
  have := hC _ (eseq_mem hX 0)
  rw [eseq_norm hX] at this
  rcases (qf_self_nonneg (eseq X 0)).eq_or_lt with h | h
  · rw [← h] at this; linarith
  · exact h

lemma eseq_pos' (k : ℕ) : 0 < qf (eseq X k) (eseq X k) :=
  (eseq_pos hX).trans_le (eseq_mono hX (Nat.zero_le k))

omit hX in
lemma qf_psum_right (w v : Amb N) (k : ℕ) :
    qf w (psum X v k) = ∑ i ∈ Finset.range k, l2 (eseq X i) v * qf w (eseq X i) := by
  simp only [psum, qf_sum_right, qf_smul_right]

omit hX in
lemma l2_psum_right (w v : Amb N) (k : ℕ) :
    l2 w (psum X v k) = ∑ i ∈ Finset.range k, l2 (eseq X i) v * l2 w (eseq X i) := by
  simp only [psum, l2_sum_right, l2_smul_right]

lemma qf_psum_self (v : Amb N) (k : ℕ) :
    qf (psum X v k) (psum X v k) =
      ∑ i ∈ Finset.range k, qf (eseq X i) (eseq X i) * l2 (eseq X i) v ^ 2 := by
  rw [qf_psum_right]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [qf_comm, eseq_eigen hX i _ (psum_mem' (eseq_mem hX)), l2_eseq_psum hX,
    if_pos (Finset.mem_range.mp hi)]
  ring

lemma l2_psum_self (v : Amb N) (k : ℕ) :
    l2 (psum X v k) (psum X v k) = ∑ i ∈ Finset.range k, l2 (eseq X i) v ^ 2 := by
  rw [l2_psum_right]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [l2_comm (psum X v k) (eseq X i), l2_eseq_psum hX, if_pos (Finset.mem_range.mp hi)]
  ring

lemma rem_perp {v : Amb N} (hv : v ∈ X) {m k : ℕ} (hmk : m ≤ k) :
    qf (v - psum X v k) (psum X v m) = 0 ∧ l2 (v - psum X v k) (psum X v m) = 0 := by
  have hr := mem_Yperp_eList.mp (sub_psum_perp hX (k := k) hv)
  constructor
  · rw [qf_psum_right]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < k := (Finset.mem_range.mp hi).trans_le hmk
    rw [qf_comm, eseq_eigen hX i _ hr.1, hr.2 i hi']
    ring
  · rw [l2_psum_right]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < k := (Finset.mem_range.mp hi).trans_le hmk
    rw [l2_comm (v - psum X v k) (eseq X i), hr.2 i hi']
    ring

lemma qf_split {v : Amb N} (hv : v ∈ X) (k : ℕ) :
    qf v v = qf (v - psum X v k) (v - psum X v k) +
      ∑ i ∈ Finset.range k, qf (eseq X i) (eseq X i) * l2 (eseq X i) v ^ 2 := by
  rw [← qf_psum_self hX]
  have h := (rem_perp hX hv (le_refl k)).1
  have e : v = (v - psum X v k) + psum X v k := by abel
  conv_lhs => rw [e]
  simp only [qf_add_left, qf_add_right, h, qf_comm (psum X v k) (v - psum X v k)]
  ring

lemma l2_split {v : Amb N} (hv : v ∈ X) (k : ℕ) :
    l2 v v = l2 (v - psum X v k) (v - psum X v k) +
      ∑ i ∈ Finset.range k, l2 (eseq X i) v ^ 2 := by
  rw [← l2_psum_self hX]
  have h := (rem_perp hX hv (le_refl k)).2
  have e : v = (v - psum X v k) + psum X v k := by abel
  conv_lhs => rw [e]
  simp only [l2_add_left, l2_add_right, h, l2_comm (psum X v k) (v - psum X v k)]
  ring

/-- Spectral expansions of `q` and of the `L²` norm. -/
lemma expansion {v : Amb N} (hv : v ∈ X) :
    HasSum (fun j => qf (eseq X j) (eseq X j) * l2 v (eseq X j) ^ 2) (qf v v) ∧
      HasSum (fun j => l2 v (eseq X j) ^ 2) (l2 v v) := by
  simp_rw [l2_comm v]
  set r := fun k => v - psum X v k with hr
  set a := fun k => l2 (r k) (r k) with ha
  set b := fun k => qf (r k) (r k) with hb
  have hsum_nonneg : ∀ k, 0 ≤ ∑ i ∈ Finset.range k,
      qf (eseq X i) (eseq X i) * l2 (eseq X i) v ^ 2 :=
    fun k => Finset.sum_nonneg fun i _ => mul_nonneg (qf_self_nonneg _) (sq_nonneg _)
  have hbv : ∀ k, b k ≤ qf v v := fun k => by
    have := qf_split hX hv k; have := hsum_nonneg k; simp only [b, r]; linarith
  have ha_le : ∀ k, a k ≤ qf v v / qf (eseq X k) (eseq X k) := fun k => by
    rw [le_div_iff₀ (eseq_pos' hX k), mul_comm]
    have hr' := mem_Yperp_eList.mp (sub_psum_perp hX (k := k) hv)
    exact (eseq_low hX hr'.1 hr'.2).trans (hbv k)
  have ha0 : Tendsto a atTop (𝓝 0) :=
    squeeze_zero (fun k => l2_self_nonneg _) ha_le
      (tendsto_const_nhds.div_atTop (eseq_tendsto hX))
  -- increments
  have hdiff : ∀ n m, n ≤ m → ‖(r n - r m).1‖ ^ 2 = a n - a m ∧
      ‖(r n - r m).2‖ ^ 2 = b n - b m := by
    intro n m hnm
    have hp := rem_perp hX hv (le_refl m)
    have hp' := rem_perp hX hv hnm
    have e2 : r n - r m = psum X v m - psum X v n := by simp only [r]; abel
    have hΔl : l2 (r m) (r n - r m) = 0 := by
      rw [e2, l2_sub_right]; simp only [r]; rw [hp.2, hp'.2, sub_zero]
    have hΔq : qf (r m) (r n - r m) = 0 := by
      rw [e2, qf_sub_right]; simp only [r]; rw [hp.1, hp'.1, sub_zero]
    have e : r n = r m + (r n - r m) := by abel
    constructor
    · rw [← l2_self_eq_norm_sq]
      have : a n = l2 (r m + (r n - r m)) (r m + (r n - r m)) := by simp only [a]; rw [← e]
      rw [this, l2_add_left, l2_add_right, l2_add_right, hΔl, l2_comm (r n - r m) (r m), hΔl]
      simp only [a]; ring
    · rw [← qf_self_eq_norm_sq]
      have : b n = qf (r m + (r n - r m)) (r m + (r n - r m)) := by simp only [b]; rw [← e]
      rw [this, qf_add_left, qf_add_right, qf_add_right, hΔq, qf_comm (r n - r m) (r m), hΔq]
      simp only [b]; ring
  have hb_anti : Antitone b := antitone_nat_of_succ_le fun n => by
    have := (hdiff n (n + 1) (Nat.le_succ n)).2
    have := sq_nonneg ‖(r n - r (n + 1)).2‖
    linarith
  have hbconv : ∃ B, Tendsto b atTop (𝓝 B) :=
    ⟨_, tendsto_atTop_ciInf hb_anti ⟨0, by rintro _ ⟨k, rfl⟩; exact qf_self_nonneg _⟩⟩
  obtain ⟨B, hB⟩ := hbconv
  have hacau := ha0.cauchySeq
  have hbcau := hB.cauchySeq
  have hrcau : CauchySeq r := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.mp hacau (ε ^ 2) (by positivity)
    obtain ⟨N2, hN2⟩ := Metric.cauchySeq_iff.mp hbcau (ε ^ 2) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hd := hdiff (max N1 N2) n hn
    have h1 := hN1 n (le_of_max_le_left hn) (max N1 N2) (le_max_left _ _)
    have h2 := hN2 n (le_of_max_le_right hn) (max N1 N2) (le_max_right _ _)
    rw [Real.dist_eq] at h1 h2
    rw [dist_comm, dist_eq_norm, Prod.norm_def, max_lt_iff]
    constructor
    · have : ‖(r (max N1 N2) - r n).1‖ ^ 2 < ε ^ 2 := by
        rw [hd.1]; linarith [(abs_sub_lt_iff.mp h1).2]
      exact lt_of_pow_lt_pow_left₀ 2 hε.le this
    · have : ‖(r (max N1 N2) - r n).2‖ ^ 2 < ε ^ 2 := by
        rw [hd.2]; linarith [(abs_sub_lt_iff.mp h2).2]
      exact lt_of_pow_lt_pow_left₀ 2 hε.le this
  obtain ⟨r0, hr0⟩ := cauchySeq_tendsto_of_complete hrcau
  have hr0X : r0 ∈ X := hX.closed.mem_of_tendsto hr0
    (Eventually.of_forall fun k => X.sub_mem hv (psum_mem' (eseq_mem hX)))
  have hr00 : r0 = 0 := by
    refine hX.pos r0 hr0X ?_
    have h := (continuous_l2.tendsto (r0, r0)).comp (hr0.prodMk_nhds hr0)
    exact tendsto_nhds_unique h ha0
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have h := (continuous_qf.tendsto (r0, r0)).comp (hr0.prodMk_nhds hr0)
    rw [hr00, qf_zero_left] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => mul_nonneg (qf_self_nonneg _) (sq_nonneg _))]
    have e : ∀ n, ∑ i ∈ Finset.range n, qf (eseq X i) (eseq X i) * l2 (eseq X i) v ^ 2 =
        qf v v - b n := fun n => by
      have := qf_split hX hv n; simp only [b, r]; linarith
    simp_rw [e]
    simpa using (tendsto_const_nhds (x := qf v v)).sub hb0
  · rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => sq_nonneg _)]
    have e : ∀ n, ∑ i ∈ Finset.range n, l2 (eseq X i) v ^ 2 = l2 v v - a n := fun n => by
      have := l2_split hX hv n; simp only [a, r]; linarith
    simp_rw [e]
    simpa using (tendsto_const_nhds (x := l2 v v)).sub ha0

end seq2

/-- On a finite-dimensional subspace on which the `L²` part is positive definite, the Rayleigh
quotient is bounded above. -/
lemma bddAbove_rayleigh {V : Submodule ℝ (Amb N)} [FiniteDimensional ℝ V]
    (hpos : ∀ v ∈ V, l2 v v = 0 → v = 0) :
    BddAbove (rayleigh '' {v | v ∈ V ∧ v ≠ 0}) := by
  by_cases hV : V = ⊥
  · refine ⟨0, ?_⟩
    rintro _ ⟨v, ⟨hv, hv0⟩, rfl⟩
    rw [hV] at hv
    exact absurd ((Submodule.mem_bot ℝ).mp hv) hv0
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  have hK : IsCompact (sphere (0 : V) 1) := isCompact_sphere 0 1
  have hKne : (sphere (0 : V) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : ContinuousOn (fun v : V => l2 (v : Amb N) v) (sphere 0 1) :=
    (continuous_l2.comp (continuous_subtype_val.prodMk continuous_subtype_val)).continuousOn
  obtain ⟨v0, hv0K, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hm : 0 < l2 (v0 : Amb N) v0 := by
    refine lt_of_le_of_ne (l2_self_nonneg _) (fun h => ?_)
    have h0 : (v0 : Amb N) = 0 := hpos _ v0.2 h.symm
    have : v0 = 0 := Subtype.ext h0
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at hv0K
    exact zero_ne_one hv0K
  refine ⟨1 / l2 (v0 : Amb N) v0, ?_⟩
  rintro _ ⟨v, ⟨hv, hv0⟩, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w : V, (w : Amb N) = v := ⟨⟨v, hv⟩, rfl⟩
  have hw0 : w ≠ 0 := fun h => hv0 (by rw [← hw_def, h]; rfl)
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = ‖w‖⁻¹ := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hc_def]; exact inv_ne_zero hn
  obtain ⟨u, hu_def⟩ : ∃ u : V, u = c • w := ⟨_, rfl⟩
  have hu : u ∈ sphere (0 : V) 1 := by
    rw [hu_def, mem_sphere_zero_iff_norm, norm_smul, hc_def, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hn]
  have hmu : l2 (v0 : Amb N) v0 ≤ l2 (u : Amb N) u := hmin hu
  have hqu : qf (u : Amb N) u ≤ 1 := by
    rw [qf_self_eq_norm_sq]
    have h1 : ‖(u : Amb N).2‖ ≤ 1 := by
      have := norm_snd_le (u : Amb N)
      rwa [← Submodule.coe_norm, mem_sphere_zero_iff_norm.mp hu] at this
    have h0 := norm_nonneg (u : Amb N).2
    nlinarith
  have hray : rayleigh v = rayleigh (u : Amb N) := by
    have : (u : Amb N) = c • v := by rw [hu_def, Submodule.coe_smul, hw_def]
    rw [this, rayleigh, rayleigh, qf_smul_left, qf_smul_right, l2_smul_left, l2_smul_right,
      ← mul_assoc, ← mul_assoc, mul_div_mul_left _ _ (mul_ne_zero hc hc)]
  rw [hray, rayleigh]
  exact div_le_div₀ zero_le_one hqu hm hmu

section seq3

variable {X : Submodule ℝ (Amb N)} (hX : SpecHyp X)
include hX

/-- The min–max values are the successive minima. -/
lemma minmax_eq (k : ℕ) : minmax X (k + 1) = qf (eseq X k) (eseq X k) := by
  set W := Submodule.span ℝ (Set.range fun i : Fin (k + 1) => eseq X i) with hW
  have hli : LinearIndependent ℝ (fun i : Fin (k + 1) => eseq X i) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h := congrArg (l2 (eseq X i)) hg
    rw [l2_sum_right, l2_zero_right] at h
    simp only [l2_smul_right, eseq_orth hX, mul_ite, mul_one, mul_zero] at h
    rw [Finset.sum_eq_single i (fun j _ hj => by
        rw [if_neg (fun h' => hj (Fin.ext h').symm)]) (fun h' => absurd hi h'), if_pos rfl] at h
    exact h
  have hWX : W ≤ X := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact eseq_mem hX i)
  have hWdim : Module.finrank ℝ W = k + 1 := by
    rw [hW, finrank_span_eq_card hli]; simp
  have hbdd : BddBelow ((fun V : Submodule ℝ (Amb N) =>
      sSup (rayleigh '' {v | v ∈ V ∧ v ≠ 0})) '' {V | V ≤ X ∧ Module.finrank ℝ V = k + 1}) :=
    ⟨0, by rintro _ ⟨V, -, rfl⟩; exact sSup_rayleigh_nonneg V⟩
  have hμ0 := (eseq_pos' hX k).le
  apply le_antisymm
  · refine (csInf_le hbdd ⟨W, ⟨hWX, hWdim⟩, rfl⟩).trans (Real.sSup_le ?_ hμ0)
    rintro _ ⟨v, ⟨hv, -⟩, rfl⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    have hcoef : ∀ j : Fin (k + 1), l2 (eseq X j) (∑ i, a i • eseq X i) = a j := by
      intro j
      rw [l2_sum_right]
      simp only [l2_smul_right, eseq_orth hX, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single j (fun i _ hij => by
          rw [if_neg (fun h' => hij (Fin.ext h').symm)]) (fun h' => absurd (Finset.mem_univ j) h'),
        if_pos rfl]
    have hmemX : (∑ i, a i • eseq X i) ∈ X := hWX hv
    have hq : qf (∑ i, a i • eseq X i) (∑ i, a i • eseq X i) =
        ∑ i : Fin (k + 1), qf (eseq X i) (eseq X i) * a i ^ 2 := by
      conv_lhs => rw [qf_sum_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [qf_smul_right, qf_comm, eseq_eigen hX i _ hmemX, hcoef]
      ring
    have hl : l2 (∑ i, a i • eseq X i) (∑ i, a i • eseq X i) = ∑ i : Fin (k + 1), a i ^ 2 := by
      conv_lhs => rw [l2_sum_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [l2_smul_right, l2_comm, hcoef]
      ring
    rcases (l2_self_nonneg (∑ i, a i • eseq X i)).eq_or_lt with h | h
    · rw [rayleigh, ← h, div_zero]; exact hμ0
    · rw [rayleigh, div_le_iff₀ h, hq, hl, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hm : qf (eseq X i) (eseq X i) ≤ qf (eseq X k) (eseq X k) :=
        eseq_mono hX (Nat.lt_succ_iff.mp i.2)
      nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg (a i))]
  · refine le_csInf ⟨_, ⟨W, ⟨hWX, hWdim⟩, rfl⟩⟩ ?_
    rintro _ ⟨V, ⟨hVX, hVdim⟩, rfl⟩
    haveI : Module.Free ℝ V := Module.Free.of_divisionRing ℝ V
    haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
    let T : V →ₗ[ℝ] (Fin k → ℝ) :=
      { toFun := fun v i => l2 (eseq X i) v
        map_add' := by intro a b; ext i; simp
        map_smul' := by intro c a; ext i; simp }
    have hker : LinearMap.ker T ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by rw [hVdim, Module.finrank_fin_fun]; omega)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hperp : ∀ i < k, l2 (eseq X i) v = 0 := fun i hi =>
      congrFun (LinearMap.mem_ker.mp hv) ⟨i, hi⟩
    have hvX : (v : Amb N) ∈ X := hVX v.2
    have hv0' : (v : Amb N) ≠ 0 := fun h => hv0 (Subtype.ext h)
    have hlpos : 0 < l2 (v : Amb N) v :=
      lt_of_le_of_ne (l2_self_nonneg _) (fun h => hv0' (hX.pos _ hvX h.symm))
    have hlow := eseq_low hX hvX hperp
    have : qf (eseq X k) (eseq X k) ≤ rayleigh (v : Amb N) := by
      rw [rayleigh, le_div_iff₀ hlpos]; exact hlow
    exact this.trans (le_csSup (bddAbove_rayleigh (fun w hw => hX.pos w (hVX hw)))
      ⟨v, ⟨v.2, hv0'⟩, rfl⟩)

/-- **Abstract spectral theorem.** -/
theorem spectral_abstract :
    ∃ e : ℕ → Amb N,
      (∀ j, e j ∈ X ∧ e j ≠ 0 ∧ ∀ φ ∈ X, qf (e j) φ = minmax X (j + 1) * l2 (e j) φ) ∧
      (∀ i j, l2 (e i) (e j) = if i = j then 1 else 0) ∧
      0 < minmax X 1 ∧
      Monotone (fun j => minmax X (j + 1)) ∧
      Tendsto (fun j => minmax X (j + 1)) atTop atTop ∧
      ∀ v ∈ X, HasSum (fun j => minmax X (j + 1) * l2 v (e j) ^ 2) (qf v v) ∧
        HasSum (fun j => l2 v (e j) ^ 2) (l2 v v) := by
  have hmm : (fun j => minmax X (j + 1)) = fun j => qf (eseq X j) (eseq X j) :=
    funext (minmax_eq hX)
  refine ⟨eseq X, fun j => ⟨eseq_mem hX j, fun h => ?_, ?_⟩, eseq_orth hX, ?_, ?_, ?_, ?_⟩
  · have := eseq_norm hX j
    rw [h, l2_zero_left] at this
    exact zero_ne_one this
  · rw [minmax_eq hX]; exact eseq_eigen hX j
  · rw [minmax_eq hX 0]; exact eseq_pos hX
  · rw [hmm]; exact eseq_mono hX
  · rw [hmm]; exact eseq_tendsto hX
  · intro v hv
    simp only [minmax_eq hX]
    exact expansion hX hv

end seq3

end FourthRatio

end

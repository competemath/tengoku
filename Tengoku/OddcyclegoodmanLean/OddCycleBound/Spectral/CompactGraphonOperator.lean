import Tengoku.OddcyclegoodmanLean.OddCycleBound.Spectral.GraphonL2Operator
import Tengoku.Seed.Analysis.InnerProductSpace.Rayleigh
import Tengoku.Seed.Analysis.InnerProductSpace.Spectrum
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mekty2012/OddCycleGoodman-lean@dbaea5a4d2c0, `OddCycleBound/Spectral/CompactGraphonOperator.lean`: removed 6 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

noncomputable section

open MeasureTheory

namespace OddCycleBound
namespace Spectral
namespace CompactSpectral

open Module End

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

structure CompactSelfAdjointSkeleton (T : E →L[𝕜] E) : Prop where
  orthogonal_family_eigenspaces :
    OrthogonalFamily 𝕜
      (fun μ => eigenspace (T : End 𝕜 E) μ)
      (fun μ => (eigenspace (T : End 𝕜 E) μ).subtypeₗᵢ)
  eigenspaces_complete :
    (⨆ μ, eigenspace (T : End 𝕜 E) μ)ᗮ = ⊥
  finite_dimensional_nonzero_eigenspace :
    ∀ μ : 𝕜, μ ≠ 0 -> FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ)
  zero_iff_only_zero_eigenvalue :
    (∀ μ : 𝕜, HasEigenvalue (T : End 𝕜 E) μ -> μ = 0) ↔ T = 0

theorem compactSelfAdjointSkeleton
    {T : E →L[𝕜] E}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    CompactSelfAdjointSkeleton T where
  orthogonal_family_eigenspaces :=
    LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : End 𝕜 E)) hsymm
  eigenspaces_complete :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hcompact hsymm
  finite_dimensional_nonzero_eigenspace :=
    fun μ hμ =>
      ContinuousLinearMap.finite_dimensional_eigenspace
        (T := T) hcompact μ hμ
  zero_iff_only_zero_eigenvalue :=
    ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
      hcompact hsymm

omit [CompleteSpace E] in

theorem symmetric_range_le_orthogonal_zero_eigenspace
    {T : E →L[𝕜] E}
    (hsymm : T.IsSymmetric) :
    LinearMap.range T.toLinearMap ≤
      (eigenspace (T : End 𝕜 E) 0)ᗮ := by
  intro y hy
  rw [Submodule.mem_orthogonal]
  rcases LinearMap.mem_range.mp hy with ⟨x, rfl⟩
  intro u hu
  have hTu : T u = 0 := by
    simpa using hu
  calc
    inner 𝕜 u (T x) = inner 𝕜 (T u) x := by
      simpa using (hsymm u x).symm
    _ = 0 := by simp [hTu]

theorem compactSelfAdjoint_nonzero_iSup_orthogonal_inf_zero_eigenspace_orthogonal_eq_bot
    {T : E →L[𝕜] E}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    ((⨆ lambda : {lambda : 𝕜 // lambda ≠ 0},
        eigenspace (T : End 𝕜 E) lambda.1)ᗮ ⊓
      (eigenspace (T : End 𝕜 E) 0)ᗮ) = ⊥ := by
  let N : Submodule 𝕜 E :=
    ⨆ lambda : {lambda : 𝕜 // lambda ≠ 0},
      eigenspace (T : End 𝕜 E) lambda.1
  let Z : Submodule 𝕜 E := eigenspace (T : End 𝕜 E) 0
  have hcover : N ⊔ Z = ⨆ lambda : 𝕜, eigenspace (T : End 𝕜 E) lambda := by
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · refine iSup_le ?_
        intro lambda
        exact le_iSup (fun lambda : 𝕜 =>
          eigenspace (T : End 𝕜 E) lambda) lambda.1
      · exact le_iSup (fun lambda : 𝕜 =>
          eigenspace (T : End 𝕜 E) lambda) 0
    · refine iSup_le ?_
      intro lambda
      by_cases hlambda : lambda = 0
      · subst lambda
        exact le_sup_right
      · have hleN :
            eigenspace (T : End 𝕜 E) lambda ≤ N :=
          le_iSup (fun lambda : {lambda : 𝕜 // lambda ≠ 0} =>
            eigenspace (T : End 𝕜 E) lambda.1) ⟨lambda, hlambda⟩
        exact hleN.trans le_sup_left
  calc
    ((⨆ lambda : {lambda : 𝕜 // lambda ≠ 0},
        eigenspace (T : End 𝕜 E) lambda.1)ᗮ ⊓
      (eigenspace (T : End 𝕜 E) 0)ᗮ)
        = Nᗮ ⊓ Zᗮ := by rfl
    _ = (N ⊔ Z)ᗮ := Submodule.inf_orthogonal N Z
    _ = (⨆ lambda : 𝕜, eigenspace (T : End 𝕜 E) lambda)ᗮ := by
      rw [hcover]
    _ = ⊥ :=
      (compactSelfAdjointSkeleton hcompact hsymm).eigenspaces_complete

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
  [CompleteSpace H]

omit [CompleteSpace H] in

theorem selfAdjoint_eigenvectors_orthogonal_of_ne
    {T : H →L[Real] H}
    (hsymm : T.IsSymmetric)
    {lambda mu : Real} (hneq : lambda ≠ mu) {v w : H}
    (hv : Module.End.HasEigenvector T.toLinearMap lambda v)
    (hw : Module.End.HasEigenvector T.toLinearMap mu w) :
    inner Real w v = 0 := by
  have horth :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : End Real H)) hsymm).pairwise hneq
  exact horth hv.1 w hw.1

omit [CompleteSpace H] in
private lemma dist_smul_orthonormal_sq
    {mode : Nat → H} (horth : Orthonormal Real mode)
    {i j : Nat} (hij : i ≠ j) (a b : Real) :
    dist (a • mode i) (b • mode j) ^ 2 = a ^ 2 + b ^ 2 := by
  have hinner_mode : inner Real (mode i) (mode j) = 0 :=
    horth.inner_eq_zero hij
  have hinner : inner Real (a • mode i) (b • mode j) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hinner_mode]
    ring
  have hnorm_i : ‖mode i‖ = 1 := horth.norm_eq_one i
  have hnorm_j : ‖mode j‖ = 1 := horth.norm_eq_one j
  calc
    dist (a • mode i) (b • mode j) ^ 2
        = ‖a • mode i - b • mode j‖ ^ 2 := by rw [dist_eq_norm]
    _ = ‖a • mode i‖ ^ 2 + ‖b • mode j‖ ^ 2 := by
        simpa [pow_two] using
          norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
    _ = a ^ 2 + b ^ 2 := by
        simp [norm_smul, Real.norm_eq_abs, hnorm_i, hnorm_j, sq_abs]

omit [CompleteSpace H] in
private lemma le_dist_smul_orthonormal_of_le_abs
    {mode : Nat → H} (horth : Orthonormal Real mode)
    {i j : Nat} (hij : i ≠ j) {eps a b : Real}
    (heps : 0 < eps) (ha : eps ≤ |a|) :
    eps ≤ dist (a • mode i) (b • mode j) := by
  by_contra hnot
  have hlt : dist (a • mode i) (b • mode j) < eps :=
    lt_of_not_ge hnot
  have hlt_sq :
      dist (a • mode i) (b • mode j) ^ 2 < eps ^ 2 := by
    refine sq_lt_sq.mpr ?_
    simpa [abs_of_nonneg dist_nonneg, abs_of_pos heps] using hlt
  have ha_sq : eps ^ 2 ≤ a ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_pos heps] using ha)
  have hdist_sq :=
    dist_smul_orthonormal_sq (H := H) horth hij a b
  have hdist_ge : eps ^ 2 ≤ dist (a • mode i) (b • mode j) ^ 2 := by
    rw [hdist_sq]
    nlinarith [sq_nonneg b]
  nlinarith

omit [CompleteSpace H] in

theorem compactOperator_no_orthonormal_eigen_subsequence_bounded_away
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    {mode : Nat → H} {eigen : Nat → Real}
    (horth : Orthonormal Real mode)
    (hdiag : ∀ n, T (mode n) = eigen n • mode n)
    {φ : Nat → Nat} (hφ : StrictMono φ)
    {eps : Real} (heps : 0 < eps)
    (hlower : ∀ n, eps ≤ |eigen (φ n)|) :
    False := by
  obtain ⟨K, hK, hsub⟩ := hcompact.image_closedBall_subset_compact 1
  let yseq : Nat → H := fun n => T (mode (φ n))
  have hyseq : ∀ n, yseq n ∈ K := by
    intro n
    apply hsub
    refine ⟨mode (φ n), ?_, rfl⟩
    simp [Metric.mem_closedBall, dist_eq_norm, horth.norm_eq_one (φ n)]
  obtain ⟨y, _hyK, ψ, hψ, hlim⟩ := hK.tendsto_subseq hyseq
  have hhalf : 0 < eps / 2 := by linarith
  have hev : ∀ᶠ n in Filter.atTop, yseq (ψ n) ∈ Metric.ball y (eps / 2) :=
    hlim (Metric.ball_mem_nhds y hhalf)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hN0 : dist (yseq (ψ N)) y < eps / 2 := by
    simpa [Metric.mem_ball] using hN N le_rfl
  have hN1 : dist (yseq (ψ (N + 1))) y < eps / 2 := by
    simpa [Metric.mem_ball] using hN (N + 1) (Nat.le_succ N)
  have hdist_lt : dist (yseq (ψ N)) (yseq (ψ (N + 1))) < eps := by
    calc
      dist (yseq (ψ N)) (yseq (ψ (N + 1)))
          ≤ dist (yseq (ψ N)) y + dist y (yseq (ψ (N + 1))) :=
            dist_triangle _ _ _
      _ = dist (yseq (ψ N)) y + dist (yseq (ψ (N + 1))) y := by
            rw [dist_comm y (yseq (ψ (N + 1)))]
      _ < eps := by linarith
  have hidx_ne : φ (ψ N) ≠ φ (ψ (N + 1)) := by
    exact ne_of_lt (hφ (hψ (Nat.lt_succ_self N)))
  have hdist_ge : eps ≤ dist (yseq (ψ N)) (yseq (ψ (N + 1))) := by
    have hbase :=
      le_dist_smul_orthonormal_of_le_abs
        (H := H) horth hidx_ne heps (hlower (ψ N))
        (b := eigen (φ (ψ (N + 1))))
    simpa [yseq, hdiag] using hbase
  exact not_lt_of_ge hdist_ge hdist_lt

omit [CompleteSpace H] in

private theorem exists_unit_eigenvector_of_hasEigenvalue
    {T : H →L[Real] H} {lambda : Real}
    (hlambda : Module.End.HasEigenvalue T.toLinearMap lambda) :
    ∃ v : H, v ≠ 0 ∧ ‖v‖ = 1 ∧ T v = lambda • v := by
  obtain ⟨v, hv⟩ := hlambda.exists_hasEigenvector
  let u : H := (‖v‖)⁻¹ • v
  have hvne : v ≠ 0 := hv.2
  have hvnorm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
  have hvact : T v = lambda • v := by
    simpa using hv.apply_eq_smul
  have hunorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvnorm_ne
  have huact : T u = lambda • u := by
    dsimp [u]
    calc
      T ((‖v‖)⁻¹ • v) = (‖v‖)⁻¹ • T v := by simp
      _ = (‖v‖)⁻¹ • (lambda • v) := by rw [hvact]
      _ = lambda • ((‖v‖)⁻¹ • v) := by
          rw [smul_smul, smul_smul]
          ring_nf
  have hune : u ≠ 0 := by
    intro hzero
    have : ‖u‖ = 0 := by simp [hzero]
    linarith
  exact ⟨u, hune, hunorm, huact⟩

omit [CompleteSpace H] in

theorem compactSelfAdjoint_no_distinct_eigenvalue_sequence_bounded_away
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {lambda : Nat → Real}
    (heigen :
      ∀ n, Module.End.HasEigenvalue T.toLinearMap (lambda n))
    (hdistinct : Pairwise fun i j => lambda i ≠ lambda j)
    {eps : Real} (heps : 0 < eps)
    (hlower : ∀ n, eps <= |lambda n|) :
    False := by
  classical
  choose mode hmode_ne hmode_norm hmode_diag using
    fun n => exists_unit_eigenvector_of_hasEigenvalue (T := T) (heigen n)
  have hhas_vec :
      ∀ n, Module.End.HasEigenvector T.toLinearMap (lambda n) (mode n) := by
    intro n
    refine ⟨?_, hmode_ne n⟩
    simpa [Module.End.mem_eigenspace_iff] using hmode_diag n
  have horth : Orthonormal Real mode := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hmode_norm i, inner_self_eq_norm_sq_to_K]
    · have hneqji : lambda j ≠ lambda i := (hdistinct hij).symm
      have hzero :
          inner Real (mode i) (mode j) = 0 :=
        selfAdjoint_eigenvectors_orthogonal_of_ne
          (T := T) hsymm hneqji (hhas_vec j) (hhas_vec i)
      simp [hij, hzero]
  exact
    compactOperator_no_orthonormal_eigen_subsequence_bounded_away
      (T := T) hcompact horth hmode_diag
      (φ := id) strictMono_id heps (by simpa using hlower)

omit [CompleteSpace H] in

theorem compactSelfAdjoint_finite_eigenvalues_abs_ge
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric)
    {eps : Real} (heps : 0 < eps) :
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ eps <= |lambda|}.Finite := by
  classical
  let s : Set Real :=
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ eps <= |lambda|}
  by_contra hfinite
  have hfinite' : ¬s.Finite := by
    intro hs
    exact hfinite (by simpa [s] using hs)
  have hinf : s.Infinite := by
    exact hfinite'
  let e : Nat ↪ s := Set.Infinite.natEmbedding s hinf
  let lambdaSeq : Nat → Real := fun n => (e n : Real)
  have heigen :
      ∀ n, Module.End.HasEigenvalue T.toLinearMap (lambdaSeq n) := by
    intro n
    exact (e n).property.1
  have hdistinct : Pairwise fun i j => lambdaSeq i ≠ lambdaSeq j := by
    intro i j hij heq
    exact hij (e.injective (Subtype.ext heq))
  have hlower : ∀ n, eps <= |lambdaSeq n| := by
    intro n
    exact (e n).property.2
  exact
    compactSelfAdjoint_no_distinct_eigenvalue_sequence_bounded_away
      (T := T) hcompact hsymm heigen hdistinct heps hlower

omit [CompleteSpace H] in

theorem compactSelfAdjoint_countable_nonzero_eigenvalues
    {T : H →L[Real] H}
    (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧ lambda ≠ 0}.Countable := by
  classical
  let shell : Nat -> Set Real := fun n =>
    {lambda : Real |
      Module.End.HasEigenvalue T.toLinearMap lambda ∧
        1 / ((n : Real) + 1) <= |lambda|}
  have hshell : ∀ n, (shell n).Countable := by
    intro n
    exact (compactSelfAdjoint_finite_eigenvalues_abs_ge
      (T := T) hcompact hsymm
      (eps := 1 / ((n : Real) + 1)) (by positivity)).countable
  have hUnion : (⋃ n : Nat, shell n).Countable :=
    Set.countable_iUnion hshell
  refine Set.Countable.mono ?_ hUnion
  intro lambda hlambda
  have habs_pos : 0 < |lambda| := abs_pos.mpr hlambda.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt habs_pos
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  exact ⟨hlambda.1, le_of_lt hn⟩

end Real


theorem isCompactOperator_of_range_le_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : ContinuousLinearMap (RingHom.id 𝕜) E F} {V : Submodule 𝕜 F}
    [FiniteDimensional 𝕜 V]
    (hV : forall x, (V : Set F) (T x)) :
    IsCompactOperator T := by
  let TV : ContinuousLinearMap (RingHom.id 𝕜) E V :=
    { T.toLinearMap.codRestrict V hV with
      cont := T.continuous.subtype_mk hV }
  haveI := FiniteDimensional.proper_rclike 𝕜 V
  have hTV : IsCompactOperator TV :=
    isCompactOperator_of_locallyCompactSpace_dom TV
  cases hTV with
  | intro C hC =>
      refine Exists.intro (V.subtypeL '' C) ?_
      refine And.intro (hC.1.image V.subtypeL.continuous) ?_
      filter_upwards [hC.2] with x hx
      exact Exists.intro (TV x) (And.intro hx rfl)


theorem isCompactOperator_of_tendsto_finiteDimensional_range
    {I F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F]
    {l : Filter I} [l.NeBot]
    {Tn : I -> ContinuousLinearMap (RingHom.id 𝕜) E F}
    {T : ContinuousLinearMap (RingHom.id 𝕜) E F}
    (hT : Filter.Tendsto Tn l (nhds T))
    (Vn : I -> Submodule 𝕜 F)
    [hVnFinite : forall i, FiniteDimensional 𝕜 (Vn i)]
    (hVn : forall i x, (Vn i : Set F) (Tn i x)) :
    IsCompactOperator T := by
  refine isCompactOperator_of_tendsto hT ?_
  refine Filter.Eventually.of_forall ?_
  intro i
  haveI := hVnFinite i
  exact isCompactOperator_of_range_le_finiteDimensional
    (T := Tn i) (V := Vn i) (hVn i)

section Graphon

universe u

variable {Omega : Type u} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu] {W : Omega -> Omega -> Real}


theorem kernelOpGoodKSimple_mem_span_of_finiteRank
    {ι : Type*} [Fintype ι]
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {a b : ι -> Omega -> Real}
    (ha : forall i, Good (a i)) (hb : forall i, Good (b i))
    (hsep : forall x y, K x y = ∑ i : ι, a i x * b i y)
    (s : Lp.simpleFunc Real 2 mu) :
    L2Kernel.kernelOpGoodKSimple (mu := mu) hK s ∈
      Submodule.span Real
        (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i)) := by
  classical
  let sf : Omega -> Real := Lp.simpleFunc.toSimpleFunc s
  let hs : Good sf := L2Kernel.simpleFunc_good (mu := mu) s
  let coeff : ι -> Real := fun i => ∫ y, b i y * sf y ∂mu
  let V : Submodule Real (Lp Real 2 mu) :=
    Submodule.span Real
      (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i))
  let v : Lp Real 2 mu :=
    ∑ i : ι, coeff i • L2Kernel.goodL2 (mu := mu) (ha i)
  have hv : v ∈ V := by
    dsimp [v, V]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (coeff i)
      (Submodule.subset_span (Set.mem_range_self i))
  have hterm_int :
      forall (x : Omega) (i : ι),
        Integrable (fun y => (a i x * b i y) * sf y) mu := by
    intro x i
    have hi : Integrable (fun y => b i y * sf y) mu :=
      (Good.mul (hb i) hs).integrable
    simpa [mul_assoc] using hi.const_mul (a i x)
  have hpoint : forall x : Omega,
      kernelOp K mu sf x = ∑ i : ι, coeff i * a i x := by
    intro x
    calc
      kernelOp K mu sf x
          = ∫ y, (∑ i : ι, a i x * b i y) * sf y ∂mu := by
            simp only [kernelOp]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp [hsep x y]
      _ = ∫ y, ∑ i : ι, (a i x * b i y) * sf y ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp [Finset.sum_mul]
      _ = ∑ i : ι, ∫ y, (a i x * b i y) * sf y ∂mu := by
            rw [integral_finsetSum]
            intro i _hi
            exact hterm_int x i
      _ = ∑ i : ι, a i x * coeff i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp only [coeff]
            rw [← integral_const_mul]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            ring
      _ = ∑ i : ι, coeff i * a i x := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
  have hright : (v : Omega -> Real) =ᵐ[mu]
      fun x => ∑ i : ι, coeff i * a i x := by
    have hsum :=
      Lp.coeFn_fun_finsetSum (μ := mu) (p := (2 : ENNReal))
        (Finset.univ) (fun i : ι =>
          coeff i • L2Kernel.goodL2 (mu := mu) (ha i))
    have hterms : forall i : ι,
        ((coeff i • L2Kernel.goodL2 (mu := mu) (ha i) :
            Lp Real 2 mu) : Omega -> Real) =ᵐ[mu]
          fun x => coeff i * a i x := by
      intro i
      filter_upwards
        [Lp.coeFn_smul (μ := mu) (p := (2 : ENNReal))
         (coeff i) (L2Kernel.goodL2 (mu := mu) (ha i)),
         L2Kernel.goodL2_ae_eq (mu := mu) (ha i)] with x hxsmul hxae
      rw [hxsmul]
      simp [Pi.smul_apply, smul_eq_mul, hxae]
    have hall : (∀ᵐ x ∂mu, forall i : ι,
        ((coeff i • L2Kernel.goodL2 (mu := mu) (ha i) :
            Lp Real 2 mu) : Omega -> Real) x = coeff i * a i x) := by
      rw [Filter.eventually_all]
      exact hterms
    filter_upwards [hsum, hall] with x hxsum hxterms
    rw [hxsum]
    exact Finset.sum_congr rfl (fun i _hi => hxterms i)
  have hop : L2Kernel.kernelOpGoodKSimple (mu := mu) hK s = v := by
    apply Lp.ext
    change
      ((L2Kernel.kernelOpL2OfGoodK (mu := mu) hK hs : Lp Real 2 mu) :
          Omega -> Real) =ᵐ[mu] (v : Omega -> Real)
    filter_upwards
      [L2Kernel.kernelOpL2OfGoodK_ae_eq (mu := mu) hK hs,
       hright] with x hxop hxv
    rw [hxop, hxv, hpoint x]
  rw [hop]
  exact hv


theorem kernelOpGoodKCLM_mem_span_of_finiteRank
    {ι : Type*} [Fintype ι]
    {K : Omega -> Omega -> Real}
    (hK : GoodK K)
    {C : Real} (hC0 : 0 <= C) (hKC : forall x y, |K x y| <= C)
    {a b : ι -> Omega -> Real}
    (ha : forall i, Good (a i)) (hb : forall i, Good (b i))
    (hsep : forall x y, K x y = ∑ i : ι, a i x * b i y)
    (f : Lp Real 2 mu) :
    L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC f ∈
      Submodule.span Real
        (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i)) := by
  classical
  let V : Submodule Real (Lp Real 2 mu) :=
    Submodule.span Real
      (Set.range fun i : ι => L2Kernel.goodL2 (mu := mu) (ha i))
  haveI : FiniteDimensional Real V :=
    FiniteDimensional.span_of_finite Real (Set.finite_range _)
  change
    L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC f ∈ V
  let T := L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC
  let e := L2Kernel.simpleFuncToL2 (mu := mu)
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange (E := Real) (p := (2 : ENNReal)) (μ := mu)
      (by norm_num)
  refine hdense.induction_on
    (p := fun f : Lp Real 2 mu => (V : Set (Lp Real 2 mu)) (T f))
    f ?closed ?simple
  · have hclosedV : IsClosed (V : Set (Lp Real 2 mu)) :=
      V.closed_of_finiteDimensional
    change IsClosed {f : Lp Real 2 mu | T f ∈ V}
    simpa [Set.preimage, T] using hclosedV.preimage
      (L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC).continuous
  · intro s
    change
      L2Kernel.kernelOpGoodKCLM (mu := mu) hK hC0 hKC
          (s : Lp Real 2 mu) ∈ V
    rw [L2Kernel.kernelOpGoodKCLM_simpleFunc (mu := mu) hK hC0 hKC s]
    exact kernelOpGoodKSimple_mem_span_of_finiteRank
      (mu := mu) hK ha hb hsep s


theorem canonicalGraphonCompact_of_hilbertSchmidt_finiteDimensional_approx
    {I : Type*} {l : Filter I} [l.NeBot]
    (hW : IsGraphon W mu)
    (K : I -> Omega -> Omega -> Real)
    (B : I -> Real)
    (hK : forall i, GoodK (K i))
    (hB0 : forall i, 0 <= B i)
    (hKB : forall i x y, |K i x y| <= B i)
    (hsqrt_tendsto :
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0))
    (V : I -> Submodule Real (Lp Real 2 mu))
    [hVFinite : forall i, FiniteDimensional Real (V i)]
    (hV : forall i f,
      (V i : Set (Lp Real 2 mu))
        (L2Kernel.kernelOpGoodKCLM (mu := mu)
          (hK i) (hB0 i) (hKB i) f)) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  have hTendsto :
      Filter.Tendsto
        (fun i =>
          L2Kernel.kernelOpGoodKCLM (mu := mu)
            (hK i) (hB0 i) (hKB i))
        l
        (nhds (L2Kernel.kernelOpCLM (mu := mu) hW)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) ?_ hsqrt_tendsto
    intro i
    have hSub0 : 0 <= B i + 1 := add_nonneg (hB0 i) zero_le_one
    have hSub : forall x y, |K i x y - W x y| <= B i + 1 := by
      intro x y
      calc
        |K i x y - W x y| <= |K i x y| + |W x y| := abs_sub _ _
        _ <= B i + 1 := by
              exact add_le_add (hKB i x y)
                (L2Kernel.graphon_abs_le_one (mu := mu) hW x y)
    calc
      ‖L2Kernel.kernelOpGoodKCLM (mu := mu)
          (hK i) (hB0 i) (hKB i) -
          L2Kernel.kernelOpCLM (mu := mu) hW‖
          =
        ‖L2Kernel.kernelOpGoodKCLM (mu := mu)
            (hK i) (hB0 i) (hKB i) -
            L2Kernel.kernelOpGoodKCLM (mu := mu)
              (goodK_of_isGraphon hW)
              zero_le_one (L2Kernel.graphon_abs_le_one (mu := mu) hW)‖ := by
            rw [L2Kernel.kernelOpCLM_eq_kernelOpGoodKCLM (mu := mu) hW]
      _ <=
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)) := by
            exact L2Kernel.norm_kernelOpGoodKCLM_sub_le_sqrt_kernelSqNorm
              (mu := mu)
              (hK i) (goodK_of_isGraphon hW)
              (hB0 i) (hKB i)
              zero_le_one (L2Kernel.graphon_abs_le_one (mu := mu) hW)
              hSub0 hSub
  exact isCompactOperator_of_tendsto_finiteDimensional_range
    (hT := hTendsto) V hV


theorem canonicalGraphonCompact_of_hilbertSchmidt_finiteRank_approx
    {I : Type*} {l : Filter I} [l.NeBot]
    (hW : IsGraphon W mu)
    (κ : I -> Type*) [hκ : forall i, Fintype (κ i)]
    (K : I -> Omega -> Omega -> Real)
    (B : I -> Real)
    (hK : forall i, GoodK (K i))
    (hB0 : forall i, 0 <= B i)
    (hKB : forall i x y, |K i x y| <= B i)
    (a b : forall i, κ i -> Omega -> Real)
    (ha : forall i j, Good (a i j))
    (hb : forall i j, Good (b i j))
    (hsep : forall i x y, K i x y = ∑ j : κ i, a i j x * b i j y)
    (hsqrt_tendsto :
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0)) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  classical
  let V : I -> Submodule Real (Lp Real 2 mu) := fun i =>
    Submodule.span Real
      (Set.range fun j : κ i => L2Kernel.goodL2 (mu := mu) (ha i j))
  haveI : forall i, FiniteDimensional Real (V i) := by
    intro i
    dsimp [V]
    exact FiniteDimensional.span_of_finite Real (Set.finite_range _)
  refine canonicalGraphonCompact_of_hilbertSchmidt_finiteDimensional_approx
    (mu := mu) hW K B hK hB0 hKB hsqrt_tendsto V ?_
  intro i f
  dsimp [V]
  exact kernelOpGoodKCLM_mem_span_of_finiteRank
    (mu := mu) (ι := κ i)
    (hK i) (hB0 i) (hKB i)
    (ha i) (hb i) (hsep i) f

def GraphonHilbertSchmidtFiniteRankApproxFor
    (_hW : IsGraphon W mu) : Prop :=
  exists (I : Type u) (l : Filter I),
    Filter.NeBot l /\
    exists (J : I -> Type u) (hJ : forall i, Fintype (J i))
      (K : I -> Omega -> Omega -> Real) (B : I -> Real)
      (a b : forall i, J i -> Omega -> Real),
      (forall i, GoodK (K i)) /\
      (forall i, 0 <= B i) /\
      (forall i x y, |K i x y| <= B i) /\
      (forall i j, Good (a i j)) /\
      (forall i j, Good (b i j)) /\
      (forall i x y,
        K i x y = (@Finset.univ (J i) (hJ i)).sum
          (fun j : J i => a i j x * b i j y)) /\
      Filter.Tendsto
        (fun i =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K i x y - W x y)))
        l (nhds 0)

theorem graphonHilbertSchmidtFiniteRankApproxFor
    (hW : IsGraphon W mu) :
    GraphonHilbertSchmidtFiniteRankApproxFor (mu := mu) hW := by
  classical
  let eps : Nat -> Real := fun n => (1 : Real) / (n + 1)
  have heps : forall n, 0 < eps n := by
    intro n
    dsimp [eps]
    positivity
  have hex :
      forall n : Nat,
        exists J : Type u, exists hJ : Fintype J,
        exists K : Omega -> Omega -> Real, exists B : Real,
        exists a b : J -> Omega -> Real,
          GoodK K /\
          0 <= B /\
          (forall x y, |K x y| <= B) /\
          (forall j, Good (a j)) /\
          (forall j, Good (b j)) /\
          (forall x y, K x y = (@Finset.univ J hJ).sum
            (fun j : J => a j x * b j y)) /\
          Real.sqrt (L2Kernel.kernelSqNorm mu
            (fun x y => K x y - W x y)) < eps n := by
    intro n
    exact L2Kernel.exists_finiteRank_kernel_sqrt_kernelSqNorm_sub_lt_of_goodK
      (mu := mu) (goodK_of_isGraphon hW) (heps n)
  choose J hJ K B a b hK hB0 hKB ha hb hsep hsqrt_lt using hex
  let I : Type u := ULift.{u} Nat
  let up : Nat -> I := fun n => ULift.up n
  let l : Filter I := Filter.map up Filter.atTop
  refine ⟨I, l, ?_, (fun i : I => J i.down), (fun i : I => hJ i.down),
    (fun i : I => K i.down), (fun i : I => B i.down),
    (fun i : I => a i.down), (fun i : I => b i.down),
    (fun i : I => hK i.down), (fun i : I => hB0 i.down),
    (fun i : I => hKB i.down), (fun i : I => ha i.down),
    (fun i : I => hb i.down), (fun i : I => hsep i.down), ?_⟩
  · dsimp [l]
    exact Filter.NeBot.map inferInstance up
  · have hNat :
        Filter.Tendsto
          (fun n : Nat =>
            Real.sqrt
              (L2Kernel.kernelSqNorm mu
                (fun x y => K n x y - W x y)))
          Filter.atTop (nhds 0) := by
      refine squeeze_zero
        (f := fun n : Nat =>
          Real.sqrt
            (L2Kernel.kernelSqNorm mu
              (fun x y => K n x y - W x y)))
        (g := eps)
        (fun n => Real.sqrt_nonneg _) ?_ ?_
      · intro n
        exact (hsqrt_lt n).le
      · simpa [eps] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    dsimp [l]
    rw [Filter.tendsto_map'_iff]
    simpa [Function.comp_def, up]
      using hNat

theorem canonicalGraphonCompact_of_hilbertSchmidtFiniteRankApproxFor
    (hW : IsGraphon W mu)
    (happrox : GraphonHilbertSchmidtFiniteRankApproxFor (mu := mu) hW) :
    IsCompactOperator (L2Kernel.kernelOpCLM (mu := mu) hW) := by
  rcases happrox with
    ⟨I, l, hl, J, hJ, K, B, a, b,
      hK, hB0, hKB, ha, hb, hsep, hsqrt_tendsto⟩
  letI : Filter.NeBot l := hl
  letI : forall i, Fintype (J i) := hJ
  exact
    canonicalGraphonCompact_of_hilbertSchmidt_finiteRank_approx
      (mu := mu) hW J K B hK hB0 hKB a b ha hb hsep hsqrt_tendsto

end Graphon

end CompactSpectral
end Spectral
end OddCycleBound

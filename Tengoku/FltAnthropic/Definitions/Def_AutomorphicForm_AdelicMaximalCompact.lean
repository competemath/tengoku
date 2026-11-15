import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicLsXi
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open NumberField NumberField.AdelicLevel MeasureTheory IsDedekindDomain
open AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

def adelicMaximalCompact : Subgroup (AdelicGL2 (𝓞 K) K) where
  carrier := {k | glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
    ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨?_, fun w => ?_⟩
    · rw [map_mul]; exact (finiteIntegralGL2 (𝓞 K) K).mul_mem ha.1 hb.1
    · rw [map_mul, map_mul]; exact (ha.2 w).mul (hb.2 w)
  one_mem' := by
    refine ⟨?_, fun w => ?_⟩
    · rw [map_one]; exact (finiteIntegralGL2 (𝓞 K) K).one_mem
    · rw [map_one, map_one]; exact isRowIsometry_one
  inv_mem' := fun {a} ha => by
    refine ⟨?_, fun w => ?_⟩
    · rw [map_inv]; exact (finiteIntegralGL2 (𝓞 K) K).inv_mem ha.1
    · rw [map_inv, map_inv]; exact (ha.2 w).inv

variable {K}

/--
@isnad1 id=iff.0h2v.s12.a2fd6bcddfc9 from=translated src=- shape=fe3213a4 vocab=0118b5b0
-/
theorem mem_adelicMaximalCompact_iff {k : AdelicGL2 (𝓞 K) K} :
    k ∈ adelicMaximalCompact K ↔
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
        ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k)) :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s12.0e6f8b83798a from=translated src=- shape=4a4ab4d8 vocab=1313c833
-/
theorem mem_adelicMaximalCompact_iff' {k : AdelicGL2 (𝓞 K) K} :
    k ∈ adelicMaximalCompact K ↔
      glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
        ∀ w : InfinitePlace K, archComponent K w (glArch (𝓞 K) K k) ∈ rowIsometrySubgroup w.Completion :=
  Iff.rfl

/--
@isnad1 id=mem.1h2v.s11.ec6d87a26a55 from=translated src=- shape=4509cc5d vocab=1b26d997
-/
theorem glFin_mem_finiteIntegralGL2 {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K := hk.1

/--
@isnad1 id=isrowiso.1h3v.s11.0a03ed90ccef from=translated src=- shape=5f45b2ae vocab=6b9787a8
-/
theorem isRowIsometry_archComponent {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (w : InfinitePlace K) : IsRowIsometry (archComponent K w (glArch (𝓞 K) K k)) := hk.2 w

/--
@isnad1 id=mem.1h3v.s11.74de1da40ebf from=translated src=- shape=603bd8c9 vocab=009d178d
-/
theorem archComponent_mem_rowIsometrySubgroup {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (w : InfinitePlace K) : archComponent K w (glArch (𝓞 K) K k) ∈ rowIsometrySubgroup w.Completion := hk.2 w

/--
@isnad1 id=and.1h5v.s12.ac92b782b19b from=translated src=- shape=bd8df52b vocab=d9f2b19b
-/
theorem valued_finComponent_apply_le_one {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    Valued.v ((finComponent (𝓞 K) K v (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 ∧
      Valued.v ((((finComponent (𝓞 K) K v (glFin (𝓞 K) K k))⁻¹ : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 := by
  have h := mem_finiteIntegralGL2_iff.1 hk.1
  refine ⟨?_, ?_⟩
  · rw [finComponent_apply]; exact valued_apply_le_one (h.1 i j) v
  · rw [← map_inv, finComponent_apply]; exact valued_apply_le_one (h.2 i j) v

/--
@isnad1 id=eq.1h3v.s11.ec962f0a4a78 from=translated src=- shape=d40ec4ac vocab=e492a2c7
-/
theorem valued_det_finComponent_eq_one {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (finComponent (𝓞 K) K v (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
  set g := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hg
  have hle : ∀ (m : GL (Fin 2) (v.adicCompletion K)),
      (∀ i j, Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1) →
      Valued.v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
    · exact mul_le_one' (hm 0 0) (hm 1 1)
    · exact mul_le_one' (hm 0 1) (hm 1 0)
  have h1 : Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 :=
    hle g fun i j => (valued_finComponent_apply_le_one hk v i j).1
  have h2 : Valued.v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 :=
    hle g⁻¹ fun i j => (valued_finComponent_apply_le_one hk v i j).2
  have hprod : Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det *
      Valued.v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
    rw [← Valuation.map_mul, ← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.det_one, Valuation.map_one]
  exact le_antisymm h1 (by
    calc (1 : _) = _ * _ := hprod.symm
      _ ≤ Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det * 1 :=
          mul_le_mul' le_rfl h2
      _ = _ := mul_one _)

variable (K)

/--
@isnad1 id=isclosed.0h1v.s7.8d5821626e30 from=translated src=- shape=a3b3e591 vocab=3e4103ef
-/
theorem isClosed_setOf_isRowIsometry (L : Type*) [NormedField L] :
    IsClosed {k : GL (Fin 2) L | IsRowIsometry k} := by
  have hval : Continuous fun k : GL (Fin 2) L => (k : Matrix (Fin 2) (Fin 2) L) :=
    Units.continuous_val
  have hent : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) L => (k : Matrix (Fin 2) (Fin 2) L) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hval)
  have h1 : IsClosed {k : GL (Fin 2) L | ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ = 1} := by
    refine isClosed_eq ?_ continuous_const
    exact continuous_norm.comp ((continuous_id.matrix_det).comp hval)
  have h2 : IsClosed {k : GL (Fin 2) L | ∀ x y : L,
      ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2
        + ‖x * (k : Matrix (Fin 2) (Fin 2) L) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
    fun_prop
  simpa only [IsRowIsometry, Set.ofPred_and] using h1.inter h2

/--
@isnad1 id=isclosed.0h1v.s9.e2be2b901c3a from=translated src=- shape=0cc2a23f vocab=82c10d16
-/
theorem isClosed_adelicMaximalCompact :
    IsClosed (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := by
  have h : (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) =
      (glFin (𝓞 K) K) ⁻¹' (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) ∩
        ⋂ w : InfinitePlace K, (fun k => archComponent K w (glArch (𝓞 K) K k)) ⁻¹'
          {k : GL (Fin 2) w.Completion | IsRowIsometry k} := by
    ext k
    simp only [SetLike.mem_coe, mem_adelicMaximalCompact_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  refine IsClosed.inter ((isClosed_finiteLevelZero (𝓞 K) K ⊤).preimage (continuous_glFin (𝓞 K) K)) ?_
  exact isClosed_iInter fun w => (isClosed_setOf_isRowIsometry w.Completion).preimage
    ((continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K))

variable {K} in

/--
@isnad1 id=le.1h4v.s7.50d38a9824e6 from=translated src=- shape=425d5400 vocab=69e5da6e
-/
theorem WindowedSiegel.IsRowIsometry.norm_apply_le_one {L : Type*} [NormedField L]
    {k : GL (Fin 2) L} (hk : IsRowIsometry k) (i j : Fin 2) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 := by
  have h0 := hk.2 1 0
  have h1 := hk.2 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, one_pow,
    zero_pow (two_ne_zero)] at h0 h1
  have hn := fun i j => sq_nonneg ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖
  have hsq : ∀ i j : Fin 2, ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ ^ 2 ≤ 1 := by
    rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
    exact ⟨⟨by linarith [hn 0 1], by linarith [hn 0 0]⟩, ⟨by linarith [hn 1 1], by linarith [hn 1 0]⟩⟩
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp (hsq i j)

omit [NumberField K] in

/--
@isnad1 id=iscompac.0h2v.s6.e5ed86e1a502 from=translated src=- shape=11ad09ef vocab=f93949aa
-/
theorem isCompact_setOf_norm_le_one_completion (w : InfinitePlace K) :
    IsCompact {x : w.Completion | ‖x‖ ≤ 1} := by
  have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce : Topology.IsClosedEmbedding (NumberField.InfinitePlace.Completion.extensionEmbedding w) :=
    hiso.isClosedEmbedding
  have hnorm : ∀ x : w.Completion,
      ‖NumberField.InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    hiso.norm_map_of_map_zero (map_zero _)
  have heq : {x : w.Completion | ‖x‖ ≤ 1} =
      (NumberField.InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hnorm]
  rw [heq]
  exact hce.isCompact_preimage (isCompact_closedBall 0 1)

/--
@isnad1 id=iscompac.0h1v.s7.28e994ddbe29 from=translated src=- shape=41a4629f vocab=36d35ceb
-/
theorem isCompact_setOf_integral_and_norm_le_one :
    IsCompact {a : AdeleRing (𝓞 K) K |
      a.2 ∈ integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ 1} := by
  have h : {a : AdeleRing (𝓞 K) K | a.2 ∈ integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ 1}
      = (Set.pi Set.univ fun w : InfinitePlace K => {x : w.Completion | ‖x‖ ≤ 1}) ×ˢ
          integralFiniteAdeles (𝓞 K) K := by
    ext a
    constructor
    · rintro ⟨h2, h1⟩
      exact ⟨Set.mem_univ_pi.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Set.mem_univ_pi.mp h1⟩
  rw [h]
  exact (isCompact_univ_pi fun w => isCompact_setOf_norm_le_one_completion K w).prod
    (isCompact_integralFiniteAdeles (𝓞 K) K)

/--
@isnad1 id=iscompac.0h1v.s9.8e2b5bcf6755 from=translated src=- shape=0cc2a23f vocab=d32ce5c9
-/
theorem isCompact_adelicMaximalCompact :
    IsCompact (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := by
  set A : Set (AdeleRing (𝓞 K) K) :=
    {a | a.2 ∈ integralFiniteAdeles (𝓞 K) K ∧ ∀ w : InfinitePlace K, ‖a.1 w‖ ≤ 1} with hA_def
  set C : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := {m | ∀ i j, m i j ∈ A} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_setOf_integral_and_norm_le_one K
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_adelicMaximalCompact K) ?_

  have hmemA : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ adelicMaximalCompact K →
      ∀ i j, (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ A := by
    intro k hk i j
    rw [mem_adelicMaximalCompact_iff] at hk
    refine ⟨?_, fun w => ?_⟩
    · exact (mem_finiteIntegralGL2_iff.1 hk.1).1 i j
    · exact (hk.2 w).norm_apply_le_one i j
  intro k hk
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  refine ⟨hmemA k hk, _, hmemA k⁻¹ ((adelicMaximalCompact K).inv_mem hk), rfl⟩

/--
@isnad1 id=compacts.0h1v.s10.b69afd125d3e from=translated src=- shape=e62cb228 vocab=c496d1f5
-/
instance compactSpace_adelicMaximalCompact : CompactSpace (adelicMaximalCompact K) :=
  isCompact_iff_compactSpace.mp (isCompact_adelicMaximalCompact K)

def maximalCompactHaar : Measure (adelicMaximalCompact K) := Measure.haarMeasure ⊤

/--
@isnad1 id=ishaarme.0h1v.s10.bc9c7b3d099a from=translated src=- shape=c90b176c vocab=8ddeeb0e
-/
instance isHaarMeasure_maximalCompactHaar : (maximalCompactHaar K).IsHaarMeasure := by
  rw [maximalCompactHaar]; infer_instance

/--
@isnad1 id=isprobab.0h1v.s10.a68302abd64a from=translated src=- shape=57d71c29 vocab=5081e783
-/
instance isProbabilityMeasure_maximalCompactHaar : IsProbabilityMeasure (maximalCompactHaar K) :=
  ⟨by rw [maximalCompactHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

/--
@isnad1 id=measurab.0h1v.s11.f7170685f15b from=translated src=- shape=70aa7325 vocab=047c1dd1
-/
theorem measurable_subtype_val_adelicMaximalCompact :
    @Measurable (adelicMaximalCompact K) (AdelicGL2 (𝓞 K) K) _ (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K)
      (fun k => (k : AdelicGL2 (𝓞 K) K)) := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  exact continuous_subtype_val.measurable

section Factors

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def maximalCompactAt : Subgroup (AdelicGL2 (𝓞 K) K) :=
  adelicMaximalCompact K ⊓
    ⨅ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ, ((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker

def maximalCompactAway : Subgroup (AdelicGL2 (𝓞 K) K) :=
  adelicMaximalCompact K ⊓ (glArch (𝓞 K) K).ker ⊓
    ⨅ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))), ((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker

variable {K S} in
/--
@isnad1 id=iff.0h3v.s12.12765f0938ca from=translated src=- shape=f495289b vocab=4d7d640d
-/
theorem mem_maximalCompactAt_iff {k : AdelicGL2 (𝓞 K) K} :
    k ∈ maximalCompactAt K S ↔
      k ∈ adelicMaximalCompact K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1 := by
  simp only [maximalCompactAt, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.coe_comp, Function.comp_apply, Set.mem_compl_iff, Finset.mem_coe]

variable {K S} in
/--
@isnad1 id=iff.0h3v.s12.320a54a762b4 from=translated src=- shape=8c7d95e3 vocab=12c7de38
-/
theorem mem_maximalCompactAway_iff {k : AdelicGL2 (𝓞 K) K} :
    k ∈ maximalCompactAway K S ↔
      k ∈ adelicMaximalCompact K ∧ glArch (𝓞 K) K k = 1 ∧
        ∀ v ∈ S, finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1 := by
  simp only [maximalCompactAway, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.coe_comp, Function.comp_apply, Finset.mem_coe, and_assoc]

/--
@isnad1 id=le.0h2v.s9.c34013a488d6 from=translated src=- shape=79c3f686 vocab=047de48f
-/
theorem maximalCompactAt_le : maximalCompactAt K S ≤ adelicMaximalCompact K := inf_le_left

/--
@isnad1 id=le.0h2v.s9.e1aa7352e0fe from=translated src=- shape=79c3f686 vocab=8f93e088
-/
theorem maximalCompactAway_le : maximalCompactAway K S ≤ adelicMaximalCompact K :=
  inf_le_left.trans inf_le_left

private theorem isClosed_ker_finComponent_comp_glFin (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) := by
  have : ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) = (fun k => finComponent (𝓞 K) K v (glFin (𝓞 K) K k)) ⁻¹' {1} := by
    ext k; simp [MonoidHom.mem_ker]
  rw [this]
  exact (isClosed_singleton).preimage
    ((continuous_finComponent (𝓞 K) K v).comp (continuous_glFin (𝓞 K) K))

/--
@isnad1 id=isclosed.0h2v.s9.207c3891783f from=translated src=- shape=5a79469f vocab=bd5d552e
-/
theorem isClosed_maximalCompactAt : IsClosed (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) := by
  have h : (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) =
      (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) ∩
        ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
          ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
            Set (AdelicGL2 (𝓞 K) K)) := by
    simp only [maximalCompactAt, Subgroup.coe_inf, Subgroup.coe_iInf]
  rw [h]
  exact (isClosed_adelicMaximalCompact K).inter
    (isClosed_biInter fun v _ => isClosed_ker_finComponent_comp_glFin K v)

/--
@isnad1 id=isclosed.0h2v.s9.3dbc7819277f from=translated src=- shape=5a79469f vocab=38a1dd33
-/
theorem isClosed_maximalCompactAway :
    IsClosed (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) := by
  have hker : IsClosed (((glArch (𝓞 K) K).ker : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by
    have : (((glArch (𝓞 K) K).ker : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) =
        (glArch (𝓞 K) K) ⁻¹' {1} := by
      ext k; simp [MonoidHom.mem_ker]
    rw [this]
    exact (isClosed_singleton).preimage (continuous_glArch (𝓞 K) K)
  have h : (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) =
      ((adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) ∩
          (((glArch (𝓞 K) K).ker : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K))) ∩
        ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K))),
          ((((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K)).ker : Subgroup (AdelicGL2 (𝓞 K) K)) :
            Set (AdelicGL2 (𝓞 K) K)) := by
    simp only [maximalCompactAway, Subgroup.coe_inf, Subgroup.coe_iInf]
  rw [h]
  exact ((isClosed_adelicMaximalCompact K).inter hker).inter
    (isClosed_biInter fun v _ => isClosed_ker_finComponent_comp_glFin K v)

/--
@isnad1 id=iscompac.0h2v.s9.e350f1f0a529 from=translated src=- shape=5a79469f vocab=905418d9
-/
theorem isCompact_maximalCompactAt : IsCompact (maximalCompactAt K S : Set (AdelicGL2 (𝓞 K) K)) :=
  (isCompact_adelicMaximalCompact K).of_isClosed_subset (isClosed_maximalCompactAt K S)
    (maximalCompactAt_le K S)

/--
@isnad1 id=iscompac.0h2v.s9.90f99fb33208 from=translated src=- shape=5a79469f vocab=dc5eae9c
-/
theorem isCompact_maximalCompactAway : IsCompact (maximalCompactAway K S : Set (AdelicGL2 (𝓞 K) K)) :=
  (isCompact_adelicMaximalCompact K).of_isClosed_subset (isClosed_maximalCompactAway K S)
    (maximalCompactAway_le K S)

/--
@isnad1 id=compacts.0h2v.s10.59b2762f1611 from=translated src=- shape=9b552b5b vocab=7a7ce034
-/
instance compactSpace_maximalCompactAt : CompactSpace (maximalCompactAt K S) :=
  isCompact_iff_compactSpace.mp (isCompact_maximalCompactAt K S)

/--
@isnad1 id=compacts.0h2v.s10.49eabbbcd0ad from=translated src=- shape=9b552b5b vocab=08a85cff
-/
instance compactSpace_maximalCompactAway : CompactSpace (maximalCompactAway K S) :=
  isCompact_iff_compactSpace.mp (isCompact_maximalCompactAway K S)

def maximalCompactAtHaar : Measure (maximalCompactAt K S) := Measure.haarMeasure ⊤

def maximalCompactAwayHaar : Measure (maximalCompactAway K S) := Measure.haarMeasure ⊤

/--
@isnad1 id=ishaarme.0h2v.s10.240fe2ff8dff from=translated src=- shape=33e5591a vocab=eccc5f0d
-/
instance isHaarMeasure_maximalCompactAtHaar : (maximalCompactAtHaar K S).IsHaarMeasure := by
  rw [maximalCompactAtHaar]; infer_instance

/--
@isnad1 id=isprobab.0h2v.s10.80f978f31e6c from=translated src=- shape=475c3680 vocab=a0bbe390
-/
instance isProbabilityMeasure_maximalCompactAtHaar : IsProbabilityMeasure (maximalCompactAtHaar K S) :=
  ⟨by rw [maximalCompactAtHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

/--
@isnad1 id=ishaarme.0h2v.s10.4c514b14d041 from=translated src=- shape=33e5591a vocab=9c1b69c1
-/
instance isHaarMeasure_maximalCompactAwayHaar : (maximalCompactAwayHaar K S).IsHaarMeasure := by
  rw [maximalCompactAwayHaar]; infer_instance

/--
@isnad1 id=isprobab.0h2v.s10.b3533dd49845 from=translated src=- shape=475c3680 vocab=4b461cf8
-/
instance isProbabilityMeasure_maximalCompactAwayHaar :
    IsProbabilityMeasure (maximalCompactAwayHaar K S) :=
  ⟨by rw [maximalCompactAwayHaar, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

end Factors

end AutomorphicForm

end

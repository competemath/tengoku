import Tengoku.FltAnthropic.Definitions.Def_AdelicDock_LocalEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdelicDock_isCompact_and_isOpen_localLevelOne.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdelicDock_isCompact_and_isOpen_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace AdelicDockLocalLevelOneTopology

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/--
@isnad1 id=eq.0h4v.s10.939088caae44 from=translated src=- shape=89af4d4f vocab=a566211f
-/
theorem setOf_isLocalLevelOne_eq (N : Ideal R) :
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m}
      = ((⋂ i, ⋂ j, (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m i j) ⁻¹'
            (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
          ∩ (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m 1 0) ⁻¹'
            {y | Valued.v y ≤ AdelicLevel.idealBound R N v})
        ∩ (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m 1 1 - 1) ⁻¹'
            {y | Valued.v y ≤ AdelicLevel.idealBound R N v} := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  exact ⟨fun h => ⟨⟨h.integral, h.lowerLeft⟩, h.lowerRight⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/--
@isnad1 id=isopen.0h3v.s7.a2b347a66b92 from=translated src=- shape=f3f00d90 vocab=303dc729
-/
theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring (v.adicCompletion K)

variable {N : Ideal R}

/--
@isnad1 id=isopen.1h4v.s7.e7188f56940c from=translated src=- shape=871ff33e vocab=c482f064
-/
theorem isOpen_setOf_isLocalLevelOne (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m} := by
  rw [setOf_isLocalLevelOne_eq]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_adicCompletionIntegers R K v).preimage (continuous_id.matrix_elem i j)
  · exact (AdelicLevel.isOpen_setOf_valued_le_idealBound v hN).preimage (continuous_id.matrix_elem 1 0)
  · exact (AdelicLevel.isOpen_setOf_valued_le_idealBound v hN).preimage
      ((continuous_id.matrix_elem 1 1).sub continuous_const)

variable (N)

/--
@isnad1 id=isclosed.0h4v.s7.ae09a877352b from=translated src=- shape=7b66fca2 vocab=0b49b6b6
-/
theorem isClosed_setOf_isLocalLevelOne :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m} := by
  rw [setOf_isLocalLevelOne_eq]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (AdelicLevel.isClosed_adicCompletionIntegers v).preimage (continuous_id.matrix_elem i j)
  · exact (AdelicLevel.isClosed_setOf_valued_le_idealBound v N).preimage (continuous_id.matrix_elem 1 0)
  · exact (AdelicLevel.isClosed_setOf_valued_le_idealBound v N).preimage
      ((continuous_id.matrix_elem 1 1).sub continuous_const)

/--
@isnad1 id=eq.0h4v.s10.a0aebaf541e7 from=translated src=- shape=6bb3d3d1 vocab=7fb05fc0
-/
theorem coe_localLevelOne_eq :
    (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K)))
      = (Units.val ⁻¹'
          {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m})
        ∩ ((fun g : GL (Fin 2) (v.adicCompletion K) =>
              ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
          {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m}) := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
  rfl

variable {N} in

/--
@isnad1 id=isopen.1h4v.s9.dd1776d57722 from=translated src=- shape=22db2b16 vocab=b8095d79
-/
theorem isOpen_localLevelOne (hN : N ≠ ⊥) :
    IsOpen (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_localLevelOne_eq]
  exact ((isOpen_setOf_isLocalLevelOne R K v hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLocalLevelOne R K v hN).preimage Units.continuous_coe_inv)

/--
@isnad1 id=isclosed.0h4v.s9.e2ce2de0a481 from=translated src=- shape=f1f8f911 vocab=d1aeb935
-/
theorem isClosed_localLevelOne :
    IsClosed (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_localLevelOne_eq]
  exact ((isClosed_setOf_isLocalLevelOne R K v N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLocalLevelOne R K v N).preimage Units.continuous_coe_inv)

section Compact

variable [Module.Free ℤ R] [Module.Finite ℤ R]

/--
@isnad1 id=iscompac.0h3v.s7.ac64864cc362 from=translated src=- shape=191aa23f vocab=748e0912
-/
theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers K)))

/--
@isnad1 id=iscompac.0h3v.s10.37b447ef16d9 from=translated src=- shape=5e82d344 vocab=b4d5482d
-/
theorem isCompact_setOf_integral :
    IsCompact {g : GL (Fin 2) (v.adicCompletion K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K} := by
  set C : Set (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    {m | ∀ i j, m i j ∈ v.adicCompletionIntegers K} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 2 =>
        Set.pi Set.univ fun _ : Fin 2 => (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers R K v
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : {g : GL (Fin 2) (v.adicCompletion K) |
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K}
      = (Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
        (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image, hC_def]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
    · rintro ⟨h1, m, hm, hm'⟩
      refine ⟨h1, ?_⟩
      have : m = ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        MulOpposite.op_injective hm'
      rw [← this]; exact hm
  rw [heq]; exact hK

/--
@isnad1 id=iscompac.0h4v.s9.beb322b3f253 from=translated src=- shape=5730e786 vocab=55903dcd
-/
theorem isCompact_localLevelOne :
    IsCompact (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) :=
  (isCompact_setOf_integral R K v).of_isClosed_subset (isClosed_localLevelOne R K v N) fun k hk => by
    rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff] at hk
    exact ⟨hk.1.integral, hk.2.integral⟩

end Compact

end AdelicDockLocalLevelOneTopology

/--
@isnad1 id=and.1h3v.s10.36edc66622aa from=translated src=- shape=aabb984f vocab=d00e6e22
-/
theorem solution (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    IsCompact (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) :=
  ⟨AdelicDockLocalLevelOneTopology.isCompact_localLevelOne (𝓞 K) K v N,
    AdelicDockLocalLevelOneTopology.isOpen_localLevelOne (𝓞 K) K v hN⟩

import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Tengoku.FltAnthropic.Definitions.Def_AdelicDock_LocalEmbedding
import Tengoku.FltAnthropic.Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_RankinSelberg_measure_setOf_mem_localLevelOne_top_pos_and_lt_top

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

namespace P2mUnipotentRangeHaar

section Range

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.0h2v.s8.1f8b195f26bf from=translated src=- shape=9528ce81 vocab=a5172173
-/
theorem unipotentGL2Hom_apply (x : Multiplicative R) :
    unipotentGL2Hom x = unipotentGL2 (Multiplicative.toAdd x) := rfl

/--
@isnad1 id=iff.0h2v.s9.c59a6379e4fd from=translated src=- shape=bb4397cf vocab=e54ddb9b
-/
theorem mem_range_unipotentGL2Hom_iff (g : GL (Fin 2) R) :
    g ∈ (unipotentGL2Hom (R := R)).range ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom_apply, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    refine Units.ext ?_
    rw [unipotentGL2Hom_apply, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h00.symm
    · simp
    · simpa using h10.symm
    · simpa using h11.symm

/--
@isnad1 id=isclosed.0h1v.s8.fc13c1e4c73a from=translated src=- shape=a73689e4 vocab=36100bc6
-/
theorem isClosed_range_unipotentGL2Hom [TopologicalSpace R] [T1Space R] :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  have hset : ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      ((fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]
  rw [hset]
  exact ((isClosed_singleton.preimage (Units.continuous_val.matrix_elem 0 0)).inter
    (isClosed_singleton.preimage (Units.continuous_val.matrix_elem 1 0))).inter
    (isClosed_singleton.preimage (Units.continuous_val.matrix_elem 1 1))

end Range

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

/--
@isnad1 id=and.0h1v.s10.c0c4c3781576 from=translated src=- shape=6c7e90b9 vocab=ec9d5f7f
-/
theorem isCompact_and_isOpen_localLevelOne_top :
    IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
  AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v ⊤ top_ne_bot

/--
@isnad1 id=isopen.0h1v.s13.348c9ac4111c from=translated src=- shape=59c7aeb2 vocab=173c1d86
-/
theorem isOpen_setOf_mem_localLevelOne_top :
    IsOpen {x : ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) |
      (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} :=
  (isCompact_and_isOpen_localLevelOne_top v).2.preimage continuous_subtype_val

/--
@isnad1 id=iscompac.0h1v.s13.998acf51b366 from=translated src=- shape=59c7aeb2 vocab=85c1e507
-/
theorem isCompact_setOf_mem_localLevelOne_top :
    IsCompact {x : ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) |
      (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} :=
  (isClosed_range_unipotentGL2Hom (R := v.adicCompletion ℚ)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_and_isOpen_localLevelOne_top v).1

/--
@isnad1 id=nonempty.0h1v.s12.2a133491d9a1 from=translated src=- shape=59c7aeb2 vocab=ebfee4d6
-/
theorem setOf_mem_localLevelOne_top_nonempty :
    {x : ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) |
      (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤}.Nonempty :=
  ⟨1, by
    rw [Set.mem_ofPred_eq, OneMemClass.coe_one]
    exact one_mem _⟩

end Local

end P2mUnipotentRangeHaar

/--
@isnad1 id=and.0h2v.s15.29677d2e4a5c from=translated src=- shape=ad7cae8f vocab=4f3a0d58
-/
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range)) [μN.IsHaarMeasure],
      0 < μN {x | (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} ∧
        μN {x | (x : GL (Fin 2) (v.adicCompletion ℚ)) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} < ⊤ := by
  intro μN _
  exact ⟨(P2mUnipotentRangeHaar.isOpen_setOf_mem_localLevelOne_top v).measure_pos μN
      (P2mUnipotentRangeHaar.setOf_mem_localLevelOne_top_nonempty v),
    (P2mUnipotentRangeHaar.isCompact_setOf_mem_localLevelOne_top v).measure_lt_top⟩

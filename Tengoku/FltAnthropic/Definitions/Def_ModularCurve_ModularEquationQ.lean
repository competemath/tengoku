import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section JLine

variable (K : Type*) [Field K] (M : ℕ) [NeZero M]

def jqNField : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqNModC K M}

/--
@isnad1 id=mem.0h2v.s7.b92cfe4c1d8a from=translated src=- shape=408ad163 vocab=87939276
-/
theorem jqNModC_mem_jqNField : jqNModC K M ∈ jqNField K M :=
  IntermediateField.subset_adjoin K _ (Set.mem_singleton _)

def jqNGen : jqNField K M :=
  ⟨jqNModC K M, jqNModC_mem_jqNField K M⟩

/--
@isnad1 id=eq.0h2v.s8.99b533e6cc47 from=translated src=- shape=5bc5f3ba vocab=1a9f2bac
-/
@[simp]
theorem coe_jqNGen : (jqNGen K M : LaurentSeries K) = jqNModC K M := rfl

end JLine

namespace ModularPolynomialData

variable {M : ℕ} [NeZero M] (data : ModularPolynomialData M) (K : Type*) [Field K]

def toJqNField : Polynomial (jqNField K M) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (jqNField K M)) (jqNGen K M))

/--
@isnad1 id=monic.0h3v.s10.2533d24d7604 from=translated src=- shape=4fcbd2ed vocab=f70c1c91
-/
theorem toJqNField_monic : (data.toJqNField K).Monic :=
  data.monic.map _

/--
@isnad1 id=eq.0h3v.s11.4ac3a328a2a1 from=translated src=- shape=b0c9deee vocab=96d18120
-/
theorem toJqNField_map :
    (data.toJqNField K).map (algebraMap (jqNField K M) (LaurentSeries K)) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K M (jqModC K))) := by
  rw [toJqNField, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, Polynomial.eval₂_X]
  rfl

def rootField : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (insert (jqNModC K M) ((data.toJqNField K).rootSet (LaurentSeries K)))

/--
@isnad1 id=le.0h3v.s8.ac7205c7102e from=translated src=- shape=6ea60405 vocab=4450d37e
-/
theorem jqNField_le_rootField : jqNField K M ≤ data.rootField K :=
  IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

/--
@isnad1 id=le.0h3v.s9.b07ac48fa398 from=translated src=- shape=f0ebe085 vocab=e6539826
-/
theorem rootSet_subset_rootField :
    (data.toJqNField K).rootSet (LaurentSeries K) ⊆ (data.rootField K : Set (LaurentSeries K)) :=
  (Set.subset_insert _ _).trans (IntermediateField.subset_adjoin K _)

end ModularPolynomialData

end ModularCurve

end

import Tengoku.ClosureResidueP3Lean.P3.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace P3

section Coupling

variable {V : Type*} [Fintype V] [DecidableEq V]

-- The coordinate realization of `D_N^0` is injective.
omit [DecidableEq V] in
/--
@isnad1 id=injectiv.0h1v.s10.442e25b3e4e3 from=translated src=- shape=c7cc5aab vocab=275f3592
-/
theorem diagZeroCoordinates_injective :
    Function.Injective (diagZeroCoordinates (V := V)) := by
  intro d e h
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℂ (V → ℂ)).injective
  ext i
  exact congrFun h i

/-- Restriction of the diagonal-coordinate map to the residue subspace,
with codomain restricted to its image.-/
def residueCoordinateMap
    (φ : Dynamics V) (k : ℕ) :
    ↥(residue φ k) →ₗ[ℂ] ↥(residueCoordinateSpace (V := V) φ k) where
  toFun r :=
    ⟨diagZeroCoordinates (V := V) r.1,
      ⟨r.1, r.2, rfl⟩⟩
  map_add' r s := by
    apply Subtype.ext
    exact LinearMap.map_add _ _ _
  map_smul' c r := by
    apply Subtype.ext
    exact LinearMap.map_smul _ _ _

/--
@isnad1 id=eq.0h4v.s14.3b749b2643f7 from=translated src=- shape=9c9f7fe1 vocab=e9ab1c43
-/
@[simp]
theorem residueCoordinateMap_apply
    (φ : Dynamics V) (k : ℕ)
    (r : ↥(residue φ k)) :
    (residueCoordinateMap (V := V) φ k r).1 =
      diagZeroCoordinates (V := V) r.1 := by
  rfl

/--
@isnad1 id=injectiv.0h3v.s13.7d99553290ed from=translated src=- shape=9c29c54f vocab=2dfbe740
-/
theorem residueCoordinateMap_injective
    (φ : Dynamics V) (k : ℕ) :
    Function.Injective (residueCoordinateMap (V := V) φ k) := by
  intro r s h
  apply Subtype.ext
  apply diagZeroCoordinates_injective (V := V)
  exact congrArg Subtype.val h

/--
@isnad1 id=surjecti.0h3v.s13.2a0c1dd5aaba from=translated src=- shape=9c29c54f vocab=a3be3536
-/
theorem residueCoordinateMap_surjective
    (φ : Dynamics V) (k : ℕ) :
    Function.Surjective (residueCoordinateMap (V := V) φ k) := by
  intro x
  rcases x.2 with ⟨r, hr, hcoord⟩
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  exact hcoord

/-- The residue subspace is linearly equivalent to its coordinate image.-/
noncomputable def residueCoordinateEquiv
    (φ : Dynamics V) (k : ℕ) :
    ↥(residue φ k) ≃ₗ[ℂ] ↥(residueCoordinateSpace (V := V) φ k) :=
  LinearEquiv.ofBijective
    (residueCoordinateMap (V := V) φ k)
    ⟨residueCoordinateMap_injective (V := V) φ k,
      residueCoordinateMap_surjective (V := V) φ k⟩

/-- Coordinate realization preserves the complex dimension of the residue.
@isnad1 id=eq.0h3v.s11.4ce5deb70be6 from=translated src=- shape=970c3112 vocab=bad513c9
-/
theorem finrank_residueCoordinateSpace
    (φ : Dynamics V) (k : ℕ) :
    Module.finrank ℂ ↥(residueCoordinateSpace (V := V) φ k) =
      Module.finrank ℂ ↥(residue φ k) := by
  exact (LinearEquiv.finrank_eq
    (residueCoordinateEquiv (V := V) φ k)).symm

/-- Graph saturation is an explicit additional condition:
the residue coordinates fill the full incidence space allowed by support.-/
def graphSaturated
    (φ : Dynamics V) (k : ℕ) : Prop :=
  residueCoordinateSpace (V := V) φ k =
    incidenceSpace (V := V) (supportGraph (V := V) φ k)

/--
@isnad1 id=iff.0h3v.s5.d35d19e79128 from=translated src=- shape=45cde401 vocab=f9c989fe
-/
theorem graphSaturated_iff
    (φ : Dynamics V) (k : ℕ) :
    graphSaturated (V := V) φ k ↔
      residueCoordinateSpace (V := V) φ k =
        incidenceSpace (V := V) (supportGraph (V := V) φ k) := by
  rfl

/-- H-stage saturation theorem:
under the explicit graph-saturation hypothesis, the residue rank is the
incidence rank of the support graph.
@isnad1 id=eq.1h3v.s11.18ffab211619 from=translated src=- shape=68698928 vocab=a1ea1d0e
-/
theorem finrank_residue_eq_card_sub_componentCount_of_graphSaturated
    (φ : Dynamics V) (k : ℕ)
    (hsat : graphSaturated (V := V) φ k) :
    Module.finrank ℂ ↥(residue φ k) =
      Fintype.card V -
        componentCount (V := V) (supportGraph (V := V) φ k) := by
  have hcoord :
      Module.finrank ℂ ↥(residueCoordinateSpace (V := V) φ k) =
        Fintype.card V -
          componentCount (V := V) (supportGraph (V := V) φ k) := by
    rw [hsat]
    exact incidence_rank (V := V) (supportGraph (V := V) φ k)
  rw [finrank_residueCoordinateSpace (V := V) φ k] at hcoord
  exact hcoord

end Coupling

end P3

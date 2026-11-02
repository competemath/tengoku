import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuadraticCharacterDescent
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms fixedCoordinates_bijective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedSpace_finrank` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedSpace_finiteDimensional` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Rank-two conclusion of the explicit character descent.
The fixed set is presented as a submodule to avoid uncached FieldTheory APIs.
It is also closed under field operations because tau is an algebra automorphism;
no identification of this fixed set with an Albert invariant field is assumed.
-/
noncomputable section
namespace AlbertLean.Generic.QuadraticCharacterDescent.Data

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω]
variable (D : QuadraticCharacterDescent.Data (k := k) (Ω := Ω))

/-- The actual tau-fixed elements of the ambient field, viewed linearly.-/
def fixedSpace : Submodule k Ω where
  carrier := {x | D.tau x = x}
  zero_mem' := map_zero D.tau
  add_mem' := by
    intro x y hx hy
    change D.tau (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change D.tau (r • x) = r • x
    rw [map_smul, hx]

/-- The even and odd scalar coefficients give an explicit linear map into
those fixed elements.-/
def fixedCoordinates : (k × k) →ₗ[k] D.fixedSpace where
  toFun v := ⟨algebraMap k Ω v.1 + algebraMap k Ω v.2 * D.u, by
    change D.tau (algebraMap k Ω v.1 + algebraMap k Ω v.2 * D.u) = _
    simp [D.tau_u]⟩
  map_add' v w := by
    apply Subtype.ext
    change algebraMap k Ω (v.1 + w.1) + algebraMap k Ω (v.2 + w.2) * D.u =
      (algebraMap k Ω v.1 + algebraMap k Ω v.2 * D.u) +
        (algebraMap k Ω w.1 + algebraMap k Ω w.2 * D.u)
    simp only [map_add]
    ring
  map_smul' r v := by
    apply Subtype.ext
    change algebraMap k Ω (r * v.1) + algebraMap k Ω (r * v.2) * D.u =
      r • (algebraMap k Ω v.1 + algebraMap k Ω v.2 * D.u)
    simp only [map_mul, Algebra.smul_def]
    ring

theorem fixedCoordinates_bijective : Function.Bijective D.fixedCoordinates := by
  constructor
  · intro v w h
    obtain ⟨q,_,hq⟩ := D.unique_tau_fixed
      (D.fixedCoordinates w).val (D.fixedCoordinates w).property
    exact (hq v (congrArg Subtype.val h)).trans (hq w rfl).symm
  · intro x
    obtain ⟨v,hv,_⟩ := D.unique_tau_fixed x.val x.property
    refine ⟨v, ?_⟩
    exact Subtype.ext hv

/-- An actual linear equivalence, not only a spanning or cardinality claim.-/
def fixedEquiv : (k × k) ≃ₗ[k] D.fixedSpace :=
  LinearEquiv.ofBijective D.fixedCoordinates D.fixedCoordinates_bijective

/-- The fixed subspace has exactly two dimensions over the given base field.-/
theorem fixedSpace_finrank : Module.finrank k D.fixedSpace = 2 := by
  rw [← D.fixedEquiv.finrank_eq]
  simp

/-- Explicit finiteness rules out interpreting a zero `finrank` from an
infinite-dimensional space as a degree bound.-/
theorem fixedSpace_finiteDimensional : FiniteDimensional k D.fixedSpace := by
  exact Module.finite_of_finrank_pos (by rw [D.fixedSpace_finrank]; decide)

end AlbertLean.Generic.QuadraticCharacterDescent.Data

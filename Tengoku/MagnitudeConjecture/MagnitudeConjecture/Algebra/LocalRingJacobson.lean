import Tengoku.Seed.Algebra.Group.Units.Opposite
import Tengoku.Seed.RingTheory.Jacobson.Ideal
import Tengoku.Seed.RingTheory.LocalRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Jacobson radical of a noncommutative local ring

In a Dedekind-finite local ring the nonunits form the unique maximal left
ideal, hence agree with the ring Jacobson radical.  Finite-dimensional
algebras over a field are Dedekind-finite.
-/

set_option autoImplicit false

namespace MagnitudeConjecture

/-- Reversing multiplication preserves the noncommutative local-ring
property.
@isnad1 id=islocalr.0h1v.s4.8f98199a2963 from=translated src=- shape=d96e9922 vocab=fff8f50e
-/
theorem mulOpposite_isLocalRing
    {R : Type*} [Ring R] [IsLocalRing R] : IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

variable (R : Type*) [Ring R] [IsDedekindFiniteMonoid R] [IsLocalRing R]

/-- The left ideal of nonunits.-/
def nonunitsIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := not_isUnit_zero
  add_mem' := IsLocalRing.nonunits_add
  smul_mem' _ _ hb := fun hab ↦ hb (isUnit_of_mul_isUnit_right hab)

/--
@isnad1 id=iff.0h2v.s6.86131bdf613a from=translated src=- shape=ed5be7fc vocab=621dbc8e
-/
@[simp]
theorem mem_nonunitsIdeal_iff_not_isUnit (x : R) :
    x ∈ nonunitsIdeal R ↔ ¬ IsUnit x :=
  Iff.rfl

/--
@isnad1 id=ismaxima.0h1v.s5.6b8aa8adcf73 from=translated src=- shape=456cb356 vocab=6acb95ab
-/
instance nonunitsIdeal_isMaximal : (nonunitsIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · change ¬ ¬ IsUnit (1 : R)
    exact not_not_intro isUnit_one
  · intro I x _ hx hIx
    change ¬ ¬ IsUnit x at hx
    rw [Classical.not_not] at hx
    obtain ⟨u, rfl⟩ := hx
    simpa using I.mul_mem_left (↑u⁻¹) hIx

/-- Every maximal left ideal is the ideal of nonunits.-/
theorem Ideal.IsMaximal.eq_nonunitsIdeal {I : Ideal R} (hI : I.IsMaximal) :
    I = nonunitsIdeal R := by
  apply hI.eq_of_le (Ideal.IsMaximal.ne_top (nonunitsIdeal_isMaximal R))
  intro x hx
  exact coe_subset_nonunits hI.ne_top hx

/-- The ring Jacobson radical is the ideal of nonunits.
@isnad1 id=eq.0h1v.s5.721837e515b8 from=translated src=- shape=2f3fa677 vocab=a8712242
-/
theorem ringJacobson_eq_nonunitsIdeal :
    Ring.jacobson R = nonunitsIdeal R := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  ext x
  constructor
  · intro hx
    exact Ideal.mem_sInf.mp hx (nonunitsIdeal_isMaximal R)
  · intro hx
    apply Ideal.mem_sInf.mpr
    intro I hI
    rw [MagnitudeConjecture.Ideal.IsMaximal.eq_nonunitsIdeal R hI]
    exact hx

/-- Jacobson-radical membership is failure to be a unit.
@isnad1 id=iff.0h2v.s6.445d718d6cdd from=translated src=- shape=ed5be7fc vocab=8718296b
-/
theorem mem_ringJacobson_iff_not_isUnit (x : R) :
    x ∈ Ring.jacobson R ↔ ¬ IsUnit x := by
  rw [ringJacobson_eq_nonunitsIdeal]
  exact mem_nonunitsIdeal_iff_not_isUnit R x

end MagnitudeConjecture

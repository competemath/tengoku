import Tengoku.Seed.FieldTheory.IsAlgClosed.Spectrum
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.LocalRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The residue scalar of a finite-dimensional local algebra

Let `E` be a finite-dimensional local algebra over an algebraically closed
field `k`.  Every element of `E` has a scalar in its spectrum.  Locality makes
that scalar unique, and the resulting function `E → k` is linear, surjective,
and has precisely the nonunits as its kernel.

This formulation applies to noncommutative endomorphism algebras; commutativity
of `E` is not assumed.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.LocalAlgebraResidue

variable {k E : Type*} [Field k] [Ring E] [Algebra k E]
  [IsAlgClosed k] [FiniteDimensional k E] [IsLocalRing E]

/-- A scalar whose subtraction from an algebra element is a nonunit.-/
def IsResidueScalar (k : Type*) {E : Type*} [Field k] [Ring E] [Algebra k E]
    (a : E) (c : k) : Prop :=
  ¬ IsUnit (a - algebraMap k E c)

/-- Every element has a residue scalar, by nonemptiness of its spectrum.
@isnad1 id=ex.0h3v.s6.1a7053b47758 from=translated src=- shape=0be05941 vocab=ed89417e
-/
theorem exists_isResidueScalar (k : Type*) {E : Type*} [Field k] [Ring E]
    [Algebra k E] [IsAlgClosed k] [FiniteDimensional k E] [IsLocalRing E]
    (a : E) : ∃ c : k, IsResidueScalar k a c := by
  obtain ⟨c, hc⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional k a
  rw [spectrum.mem_iff] at hc
  refine ⟨c, ?_⟩
  rw [IsResidueScalar, ← IsUnit.neg_iff]
  simpa only [neg_sub]

omit [IsAlgClosed k] [FiniteDimensional k E] in
/-- Locality makes the residue scalar unique.
@isnad1 id=eq.2h5v.s5.400650ab3585 from=translated src=- shape=a97d18be vocab=65eabe98
-/
theorem isResidueScalar_unique {a : E} {c d : k}
    (hc : IsResidueScalar k a c) (hd : IsResidueScalar k a d) : c = d := by
  by_contra hcd
  change ¬ IsUnit (a - algebraMap k E c) at hc
  change ¬ IsUnit (a - algebraMap k E d) at hd
  have hdneg : ¬ IsUnit (-(a - algebraMap k E d)) := by
    simpa only [IsUnit.neg_iff] using hd
  have hsum : ¬ IsUnit
      ((a - algebraMap k E c) + -(a - algebraMap k E d)) :=
    IsLocalRing.nonunits_add hc hdneg
  have heq :
      (a - algebraMap k E c) + -(a - algebraMap k E d) =
        algebraMap k E d - algebraMap k E c := by
    abel
  rw [heq] at hsum
  have hscalar : ¬ IsUnit (algebraMap k E (d - c)) := by
    simpa only [map_sub] using hsum
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  exact hscalar ((isUnit_iff_ne_zero.mpr hdc).map (algebraMap k E))

/-- The unique residue scalar of an element of a finite-dimensional local
algebra over an algebraically closed field.-/
def residueScalar (k : Type*) {E : Type*} [Field k] [Ring E] [Algebra k E]
    [IsAlgClosed k] [FiniteDimensional k E] [IsLocalRing E] (a : E) : k :=
  Classical.choose (exists_isResidueScalar k a)

/--
@isnad1 id=isresidu.0h3v.s6.17df21e8b700 from=translated src=- shape=7f0b6147 vocab=15884910
-/
theorem residueScalar_spec (a : E) :
    IsResidueScalar k a (residueScalar k a) :=
  Classical.choose_spec (exists_isResidueScalar k a)

/--
@isnad1 id=eq.1h4v.s6.1018555c624c from=translated src=- shape=3c30ce62 vocab=15884910
-/
theorem residueScalar_eq_of_isResidueScalar {a : E} {c : k}
    (hc : IsResidueScalar k a c) : residueScalar k a = c :=
  isResidueScalar_unique (residueScalar_spec a) hc

/--
@isnad1 id=eq.0h2v.s6.8c38d5e2ce42 from=translated src=- shape=5dd34ecd vocab=e0b38068
-/
@[simp]
theorem residueScalar_zero : residueScalar k (0 : E) = 0 := by
  apply residueScalar_eq_of_isResidueScalar
  simp [IsResidueScalar]

/--
@isnad1 id=eq.0h4v.s6.17bf2b0b3b1a from=translated src=- shape=1ac6b9af vocab=45a69e48
-/
theorem residueScalar_add (a b : E) :
    residueScalar k (a + b) = residueScalar k a + residueScalar k b := by
  apply residueScalar_eq_of_isResidueScalar
  have h := IsLocalRing.nonunits_add
    (residueScalar_spec (k := k) (E := E) a)
    (residueScalar_spec (k := k) (E := E) b)
  change ¬ IsUnit
    ((a + b) - algebraMap k E (residueScalar k a + residueScalar k b))
  change ¬ IsUnit
    ((a - algebraMap k E (residueScalar k a)) +
      (b - algebraMap k E (residueScalar k b))) at h
  simpa only [map_add, sub_add_sub_comm] using h

/--
@isnad1 id=eq.0h4v.s6.d73d717aa4f3 from=translated src=- shape=5c3f0fbb vocab=5e1e91d9
-/
theorem residueScalar_smul (c : k) (a : E) :
    residueScalar k (c • a) = c * residueScalar k a := by
  apply residueScalar_eq_of_isResidueScalar
  by_cases hc : c = 0
  · subst c
    simp [IsResidueScalar]
  · have hnonunit : ¬ IsUnit
        (algebraMap k E c *
          (a - algebraMap k E (residueScalar k a))) := by
      intro hproduct
      exact residueScalar_spec (k := k) (E := E) a
        ((Algebra.commute_algebraMap_left c
          (a - algebraMap k E (residueScalar k a))).isUnit_mul_iff.mp hproduct).2
    change ¬ IsUnit
      (c • a - algebraMap k E (c * residueScalar k a))
    simpa only [Algebra.smul_def, map_mul, mul_sub] using hnonunit

/-- The residue scalar as a linear map.-/
def residueLinearMap (k E : Type*) [Field k] [Ring E] [Algebra k E]
    [IsAlgClosed k] [FiniteDimensional k E] [IsLocalRing E] : E →ₗ[k] k where
  toFun := residueScalar k
  map_add' := residueScalar_add
  map_smul' := residueScalar_smul

/--
@isnad1 id=eq.0h3v.s7.bf3383b216ff from=translated src=- shape=a5c69342 vocab=50fbd5eb
-/
@[simp]
theorem residueLinearMap_apply (a : E) :
    residueLinearMap k E a = residueScalar k a :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.9b7280644717 from=translated src=- shape=5dfeb52a vocab=74da3a45
-/
@[simp]
theorem residueScalar_algebraMap (c : k) :
    residueScalar k (algebraMap k E c) = c := by
  apply residueScalar_eq_of_isResidueScalar
  simp [IsResidueScalar]

/-- The residue scalar is multiplicative.  Finite-dimensionality is used here
to make the possibly noncommutative algebra Dedekind-finite, so a product can
be a unit only when both its factors are units.
@isnad1 id=eq.0h4v.s6.6658cf906d91 from=translated src=- shape=1ac6b9af vocab=a168ba19
-/
theorem residueScalar_mul (a b : E) :
    residueScalar k (a * b) = residueScalar k a * residueScalar k b := by
  letI : IsArtinianRing E := IsArtinianRing.of_finite k E
  apply residueScalar_eq_of_isResidueScalar
  let α : k := residueScalar k a
  let β : k := residueScalar k b
  have ha : ¬ IsUnit (a - algebraMap k E α) := residueScalar_spec a
  have hb : ¬ IsUnit (b - algebraMap k E β) := residueScalar_spec b
  have hleft : ¬ IsUnit (a * (b - algebraMap k E β)) :=
    fun h ↦ hb (isUnit_of_mul_isUnit_right h)
  have hright : ¬ IsUnit ((a - algebraMap k E α) * algebraMap k E β) :=
    fun h ↦ ha (isUnit_of_mul_isUnit_left h)
  have hsum := IsLocalRing.nonunits_add hleft hright
  change ¬ IsUnit (a * b - algebraMap k E (α * β))
  rw [map_mul]
  convert hsum using 1
  noncomm_ring

/-- The residue scalar as a homomorphism of `k`-algebras.-/
def residueAlgHom (k E : Type*) [Field k] [Ring E] [Algebra k E]
    [IsAlgClosed k] [FiniteDimensional k E] [IsLocalRing E] : E →ₐ[k] k where
  toFun := residueScalar k
  map_zero' := residueScalar_zero
  map_one' := by simpa using residueScalar_algebraMap (k := k) (E := E) 1
  map_add' := residueScalar_add
  map_mul' := residueScalar_mul
  commutes' := residueScalar_algebraMap

/--
@isnad1 id=eq.0h3v.s7.dbb4ee724500 from=translated src=- shape=9cd8fbc8 vocab=ae51d918
-/
@[simp]
theorem residueAlgHom_apply (a : E) : residueAlgHom k E a = residueScalar k a :=
  rfl

/-- The residue map is the unique `k`-algebra homomorphism from the local
algebra to its algebraically closed coefficient field.
@isnad1 id=eq.0h3v.s6.e0d11c3b505f from=translated src=- shape=09d49ffa vocab=226a7020
-/
theorem algHom_eq_residueAlgHom (φ : E →ₐ[k] k) :
    φ = residueAlgHom k E := by
  ext a
  exact (residueScalar_eq_of_isResidueScalar (k := k) (E := E) <| by
    change ¬ IsUnit (a - algebraMap k E (φ a))
    intro hunit
    have hmapped := hunit.map φ
    have hzero : φ (a - algebraMap k E (φ a)) = 0 := by simp
    rw [hzero] at hmapped
    exact not_isUnit_zero hmapped).symm

/-- The residue map is onto the ground field.
@isnad1 id=surjecti.0h2v.s7.4e8a2906ff0b from=translated src=- shape=a3171a63 vocab=50164d89
-/
theorem residueLinearMap_surjective :
    Function.Surjective (residueLinearMap k E : E → k) := by
  intro c
  exact ⟨algebraMap k E c, residueScalar_algebraMap c⟩

/-- Its kernel is exactly the set of nonunits of the local algebra.
@isnad1 id=iff.0h3v.s7.833d6aa4eb21 from=translated src=- shape=61f9bd83 vocab=d2661c6f
-/
theorem mem_ker_residueLinearMap_iff (a : E) :
    a ∈ LinearMap.ker (residueLinearMap k E) ↔ ¬ IsUnit a := by
  rw [LinearMap.mem_ker]
  constructor
  · intro ha
    have h := residueScalar_spec (k := k) (E := E) a
    change ¬ IsUnit (a - algebraMap k E (residueScalar k a)) at h
    have ha' : residueScalar k a = 0 := ha
    rw [ha', map_zero, sub_zero] at h
    exact h
  · intro ha
    apply residueScalar_eq_of_isResidueScalar
    change ¬ IsUnit (a - algebraMap k E 0)
    simpa only [map_zero, sub_zero] using ha

end MagnitudeConjecture.LocalAlgebraResidue

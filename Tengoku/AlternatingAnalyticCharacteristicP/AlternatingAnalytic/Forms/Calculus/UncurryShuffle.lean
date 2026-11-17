import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Forms.Calculus.ShuffleIdentities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The algebraic Leibniz rule for the shuffle product

For a linear map `A : M → Alt^k(M; R)`, the signed sum `∑ᵢ (-1)^i A(vᵢ)(v₀, …, v̂ᵢ, …)` is
`alternatizeUncurryFin A`. These are the two algebraic identities behind the Leibniz rule
`d(η ∧ ζ) = dη ∧ ζ + (-1)^k η ∧ dζ`:
`∑ᵢ (-1)^i (A(vᵢ) ∧ ζ)(v̂ᵢ) = (alternatizeUncurryFin A ∧ ζ)(v)` (`sum_shuffle_left_removeNth`) and
`∑ᵢ (-1)^i (μ ∧ B(vᵢ))(v̂ᵢ) = (-1)^k (μ ∧ alternatizeUncurryFin B)(v)`
(`sum_shuffle_right_removeNth`). For `A = φ ⊗ μ` of rank one they follow from
`alternatizeUncurryFin_smulRight`, associativity and graded commutativity. The general case
pulls `A` back along `tupleMap v` to `Fin N → R`, where it is a finite sum of rank-one maps.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l : ℕ}

/-- Pullback of alternating maps along a linear map, as a linear map.-/
noncomputable def compLinearMapₗ {M' N : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N]
    [Module R N] {ι : Type*} (g : M' →ₗ[R] M) : (M [⋀^ι]→ₗ[R] N) →ₗ[R] (M' [⋀^ι]→ₗ[R] N) where
  toFun f := f.compLinearMap g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h7v.s9.098b461cfa3c from=translated src=- shape=52ae69be vocab=8de16fcd
-/
@[simp]
theorem compLinearMapₗ_apply {M' N : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N]
    [Module R N] {ι : Type*} (g : M' →ₗ[R] M) (f : M [⋀^ι]→ₗ[R] N) :
    compLinearMapₗ g f = f.compLinearMap g :=
  rfl

/-- `alternatizeUncurryFin` commutes with pullback along linear maps.
@isnad1 id=eq.0h6v.s9.401783851432 from=translated src=- shape=94d9ffbd vocab=6c952300
-/
theorem alternatizeUncurryFin_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (A : M →ₗ[R] M [⋀^Fin k]→ₗ[R] R) (g : M' →ₗ[R] M) :
    (AlternatingMap.alternatizeUncurryFin A).compLinearMap g =
      AlternatingMap.alternatizeUncurryFin (compLinearMapₗ g ∘ₗ A ∘ₗ g) := by
  ext w
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.comp_apply, compLinearMapₗ_apply]
  rfl

/-- Evaluation of a finite sum of alternating maps.
@isnad1 id=eq.0h8v.s7.2e3dec5c866a from=translated src=- shape=7531ad7d vocab=36d6df3d
-/
theorem alternatingMap_sum_apply {N : Type*} [AddCommGroup N] [Module R N] {ι κ : Type*}
    (s : Finset κ) (f : κ → M [⋀^ι]→ₗ[R] N) (v : ι → M) :
    (∑ j ∈ s, f j) v = ∑ j ∈ s, f j v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [Finset.sum_insert hj, AlternatingMap.add_apply, ih]

/-- `alternatizeUncurryFin` commutes with finite sums.
@isnad1 id=eq.0h6v.s9.522d6ddccd8e from=translated src=- shape=df4a70f7 vocab=ef30df38
-/
theorem alternatizeUncurryFin_sum {ι : Type*} (s : Finset ι)
    (f : ι → M →ₗ[R] M [⋀^Fin k]→ₗ[R] R) :
    AlternatingMap.alternatizeUncurryFin (∑ j ∈ s, f j) =
      ∑ j ∈ s, AlternatingMap.alternatizeUncurryFin (f j) :=
  map_sum AlternatingMap.alternatizeUncurryFinLM f s

/-- A linear map on `Fin N → R` is the sum of the rank-one maps given by its values on the
standard basis.
@isnad1 id=eq.0h4v.s9.b85e0edd588c from=translated src=- shape=57d34e0a vocab=9b3ec3dc
-/
theorem linearMap_eq_sum_smulRight {N : ℕ} {X : Type*} [AddCommGroup X] [Module R X]
    (A : (Fin N → R) →ₗ[R] X) :
    A = ∑ j, (LinearMap.proj j : (Fin N → R) →ₗ[R] R).smulRight (A (Pi.single j 1)) := by
  classical
  refine (Pi.basisFun R (Fin N)).ext fun i => ?_
  simp [Pi.single_apply]

end AlternatingAnalytic.Forms

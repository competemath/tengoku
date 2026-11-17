import Tengoku.PaperCLean.PaperC.Affine.Normalization
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two block-parity constraints on full-value relations

This is the finite linear-algebra and summation step in Proposition 3.26 of
Paper C v2.8.2. The full relation space is the existing `Affine.RelationSpace`.
A map `P` records the two block parities. Its kernel inside the full relation
space represents the relations satisfying both parity constraints.

`TwoWindowParity` identifies those constrained relations with the two actual
start trees. The uniform arithmetic estimate for their nonzero hosts remains
separate. No asymptotic estimate is asserted by this module.
-/

namespace PaperC.V282.ValueRelations

open Affine
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

noncomputable section

variable {V β : Type*} [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β]

/-- The two parity equations restricted to the full-value relation space.-/
def parityOnRelations (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) :
    RelationSpace A →ₗ[𝔽₂] (Fin 2 → 𝔽₂) :=
  P.comp (RelationSpace A).subtype

/-- Nullity after imposing both block-parity equations.-/
def parityNullity (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) : ℕ :=
  Module.finrank 𝔽₂ (LinearMap.ker (parityOnRelations A P))

/-- The defining condition keeps the two parity constraints explicit.
@isnad1 id=iff.0h5v.s12.ea2d65e29afa from=translated src=- shape=f090e9f9 vocab=44084f43
-/
@[simp]
theorem mem_parity_kernel_iff (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) (u : RelationSpace A) :
    u ∈ LinearMap.ker (parityOnRelations A P) ↔ P u = 0 :=
  Iff.rfl

/-- Imposing two parity equations cannot increase nullity.
@isnad1 id=le.0h4v.s8.20c23a1805be from=translated src=- shape=690497a7 vocab=f075f44c
-/
theorem parityNullity_le (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) :
    parityNullity A P ≤ relationRho A :=
  (LinearMap.ker (parityOnRelations A P)).finrank_le

/-- Removing two parity equations increases nullity by at most two.
@isnad1 id=le.0h4v.s8.e6406af51929 from=translated src=- shape=13025fa5 vocab=a33b6464
-/
theorem relationRho_le_parityNullity_add_two
    (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) :
    relationRho A ≤ parityNullity A P + 2 := by
  have hdim := (parityOnRelations A P).finrank_range_add_finrank_ker
  have hrange :
      Module.finrank 𝔽₂ (LinearMap.range (parityOnRelations A P)) ≤ 2 := by
    calc
      _ ≤ Module.finrank 𝔽₂ (Fin 2 → 𝔽₂) :=
        (LinearMap.range (parityOnRelations A P)).finrank_le
      _ = 2 := by simp [Module.finrank_fintype_fun_eq_card]
  unfold relationRho parityNullity
  omega

/-- The extra constant is paid only at a host with a nonzero full kernel.
@isnad1 id=le.0h4v.s9.4fd6a328f20d from=translated src=- shape=2c99708a vocab=e4d2adc7
-/
theorem relation_weight_le_four_parity_weight_add_host
    (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) :
    2 ^ relationRho A - 1 ≤
      4 * (2 ^ parityNullity A P - 1) +
        3 * (if relationRho A ≠ 0 then 1 else 0) := by
  classical
  by_cases hzero : relationRho A = 0
  · simp [hzero]
  · have hpow : 2 ^ relationRho A ≤ 2 ^ (parityNullity A P + 2) :=
      Nat.pow_le_pow_right (by omega) (relationRho_le_parityNullity_add_two A P)
    have hone : 1 ≤ 2 ^ parityNullity A P := one_le_pow₀ (by norm_num)
    rw [pow_add] at hpow
    norm_num at hpow
    simp only [ite_eq_left hzero]
    omega

/-- Finite form of (3.24), before the uniform host bound is applied.
@isnad1 id=le.0h6v.s9.00831605edea from=translated src=- shape=369573ad vocab=1e727cf2
-/
theorem sum_relation_weight_le_four_parity_weight_add_hosts
    {ι : Type*} (s : Finset ι)
    (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (P : ι → (β → 𝔽₂) →ₗ[𝔽₂] (Fin 2 → 𝔽₂)) :
    ∑ i ∈ s, (2 ^ relationRho (A i) - 1) ≤
      4 * (∑ i ∈ s, (2 ^ parityNullity (A i) (P i) - 1)) +
        3 * (s.filter fun i => relationRho (A i) ≠ 0).card := by
  classical
  calc
    _ ≤ ∑ i ∈ s,
        (4 * (2 ^ parityNullity (A i) (P i) - 1) +
          3 * (if relationRho (A i) ≠ 0 then 1 else 0)) :=
      Finset.sum_le_sum fun i _ =>
        relation_weight_le_four_parity_weight_add_host (A i) (P i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole]
      norm_cast

end
end PaperC.V282.ValueRelations

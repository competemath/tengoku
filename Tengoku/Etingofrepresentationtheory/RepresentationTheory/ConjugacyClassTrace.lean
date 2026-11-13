/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugacy-class trace maps
-/

open MonoidAlgebra

namespace RepresentationTheory.ConjugacyClassTrace

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

variable (k G) in
/-- An auxiliary scalar submodule of the group monoid algebra.-/
noncomputable def auxiliaryRelationSubmodule : Submodule k (MonoidAlgebra k G) :=
  Submodule.span k (Set.range (fun p : MonoidAlgebra k G × MonoidAlgebra k G =>
    p.1 * p.2 - p.2 * p.1))

variable (k G) in
/-- An auxiliary type associated with a field and a group.-/
noncomputable abbrev AuxiliaryClassQuotient : Type _ :=
  MonoidAlgebra k G ⧸ auxiliaryRelationSubmodule k G

variable (k G) in
/-- A linear map from the group monoid algebra to scalar-valued functions on conjugacy classes.-/
noncomputable def monoidAlgebraToClassFunctions :
    MonoidAlgebra k G →ₗ[k] (ConjClasses G → k) where
  toFun a := fun C' => ∑ g : G, if ConjClasses.mk g = C' then a.coeff g else 0
  map_add' a b := by
    funext C'
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by
      rw [show (a + b).coeff g = a.coeff g + b.coeff g from rfl]; split <;> simp
  map_smul' r a := by
    funext C'
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [show (r • a).coeff g = r • a.coeff g from rfl, smul_eq_mul]; split <;> simp

/-- A singleton monoid-algebra term maps to the function supported on its conjugacy class with the given coefficient.-/
lemma monoidAlgebraToClassFunctions_single (g : G) (c : k) :
    monoidAlgebraToClassFunctions k G (single g c) =
      fun C' => if ConjClasses.mk g = C' then c else 0 := by
  funext C'
  simp only [monoidAlgebraToClassFunctions, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single g]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_left rfl]
  · intro b _ hbg
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right (Ne.symm hbg), ite_self]
  · intro hg; exact absurd (Finset.mem_univ g) hg

variable (k G) in
/-- An auxiliary map from conjugacy classes into the auxiliary class quotient.-/
noncomputable def conjugacyClassToAuxiliary : ConjClasses G → AuxiliaryClassQuotient k G :=
  fun C' => Submodule.mkQ (auxiliaryRelationSubmodule k G) (single (Quotient.out C') 1)

omit [Fintype G] [DecidableEq G] in
/-- The difference of unit singleton terms at conjugate group elements belongs to the auxiliary relation submodule.-/
lemma single_sub_single_mem_auxiliaryRelationSubmodule_of_isConj {a b : G} (h : IsConj a b) :
    single a (1 : k) - single b 1 ∈ auxiliaryRelationSubmodule k G := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hrw : single (c⁻¹) (1 : k) * single (c * a) 1 - single (c * a) 1 * single (c⁻¹) 1
      = single a 1 - single b 1 := by
    rw [single_mul_single, single_mul_single, one_mul,
      show c⁻¹ * (c * a) = a by group, show c * a * c⁻¹ = b from hc]
  rw [← hrw]
  exact Submodule.subset_span ⟨(single (c⁻¹) 1, single (c * a) 1), rfl⟩

section TraceForm

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M] [Module.Finite k M]

omit [Fintype G] [DecidableEq G]

variable (k) in
/-- An algebra homomorphism from the group monoid algebra to the endomorphisms of a compatible module.-/
noncomputable def monoidAlgebraActionHom : MonoidAlgebra k G →ₐ[k] Module.End k M :=
  Algebra.lsmul k k M

omit [Module.Finite k M] in
/-- Evaluating the monoid-algebra action homomorphism agrees with scalar multiplication on the module.-/
@[simp] lemma monoidAlgebraActionHom_apply (x : MonoidAlgebra k G) (m : M) :
    monoidAlgebraActionHom k M x m = x • m := rfl

variable (k) in
/-- A linear functional from the group monoid algebra to the base field for a compatible module.-/
noncomputable def moduleTrace : MonoidAlgebra k G →ₗ[k] k :=
  (LinearMap.trace k M).comp (monoidAlgebraActionHom k M).toLinearMap

omit [Module.Finite k M] in
/-- The module trace functional evaluates an algebra element as the trace of its action endomorphism.-/
lemma moduleTrace_eq_trace_action (x : MonoidAlgebra k G) :
    moduleTrace k M x = LinearMap.trace k M (monoidAlgebraActionHom k M x) := rfl

omit [Module.Finite k M] in
/-- The module trace of a product is unchanged when the factors are reversed.-/
lemma moduleTrace_mul_comm (x y : MonoidAlgebra k G) :
    moduleTrace k M (x * y) = moduleTrace k M (y * x) := by
  simp only [moduleTrace_eq_trace_action, map_mul]
  exact LinearMap.trace_mul_comm k _ _

omit [Module.Finite k M] in
/-- The auxiliary relation submodule lies in the kernel of the module trace map.-/
lemma auxiliaryRelationSubmodule_le_ker_moduleTrace :
    auxiliaryRelationSubmodule k G ≤ LinearMap.ker (moduleTrace k M) := by
  rw [auxiliaryRelationSubmodule, Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, moduleTrace_mul_comm M x y, sub_self]

variable (k) in
/-- A linear functional from the auxiliary class quotient to the base field for a compatible module.-/
noncomputable def auxiliaryModuleTrace : AuxiliaryClassQuotient k G →ₗ[k] k :=
  Submodule.liftQ (auxiliaryRelationSubmodule k G) (moduleTrace k M)
    (auxiliaryRelationSubmodule_le_ker_moduleTrace M)

omit [Module.Finite k M] in
/-- The auxiliary module trace of a quotient image agrees with the module trace of its representative.-/
@[simp] lemma auxiliaryModuleTrace_mkQ (x : MonoidAlgebra k G) :
    auxiliaryModuleTrace k M (Submodule.mkQ (auxiliaryRelationSubmodule k G) x) =
      moduleTrace k M x :=
  Submodule.liftQ_apply _ _ _

omit [Module.Finite k M] in
/-- The auxiliary module trace of a quotient unit singleton equals the trace of its action.-/
lemma auxiliaryModuleTrace_mkQ_single_one (g : G) :
    auxiliaryModuleTrace k M
        (Submodule.mkQ (auxiliaryRelationSubmodule k G) (single g 1)) =
      LinearMap.trace k M (monoidAlgebraActionHom k M (single g (1 : k))) := by
  rw [auxiliaryModuleTrace_mkQ, moduleTrace_eq_trace_action]

end TraceForm

end RepresentationTheory.ConjugacyClassTrace

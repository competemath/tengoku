/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.NumberTheory.Padics.RingHoms
import Tengoku.Seed.Topology.Algebra.Module.Basic
import Tengoku.Seed.LinearAlgebra.Pi
import Tengoku.Seed.LinearAlgebra.Isomorphisms
import Tengoku.Seed.RingTheory.Finiteness.Finsupp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous additive maps of p-adic modules are p-adic linear

This is the density argument used explicitly in the local-field structure theory,
the field-unit structure theorem: compatibility with ordinary integral powers, together with
continuity of the p-adic scalar orbit, forces compatibility with every
p-adic scalar.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

/-- Turn a topological group equivalence whose source is an additive group
written multiplicatively into the inverse topological additive equivalence.-/
noncomputable def continuousAddEquivOfMultiplicativeSource
    {C G : Type*} [AddZeroClass C] [MulOneClass G]
    [TopologicalSpace C] [TopologicalSpace G]
    (e : Multiplicative C ≃ₜ* G) : Additive G ≃ₜ+ C :=
  { (MulEquiv.toAdditiveRight e.toMulEquiv).symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

/-- Turn a topological additive equivalence into the corresponding
topological multiplicative equivalence after tagging the source
multiplicatively.-/
noncomputable def continuousMulEquivOfAdditiveTarget
    {C G : Type*} [AddZeroClass C] [MulOneClass G]
    [TopologicalSpace C] [TopologicalSpace G]
    (e : C ≃ₜ+ Additive G) : Multiplicative C ≃ₜ* G :=
  { e.toAddEquiv.toMultiplicativeLeft with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

variable {p : ℕ} [Fact p.Prime]
variable {A B : Type*}
variable [TopologicalSpace A] [TopologicalSpace B]
variable [AddCommMonoid A] [AddCommMonoid B]
variable [Module ℤ_[p] A] [Module ℤ_[p] B]
variable [ContinuousSMul ℤ_[p] A] [ContinuousSMul ℤ_[p] B]
variable [T2Space B]

/-- A continuous additive homomorphism between topological `Z_p`-modules is
`Z_p`-linear.  The proof checks natural scalars and extends over the dense
copy of `ℕ` in `Z_p`.
@isnad1 id=eq.1h6v.s9.10c141565059 from=translated src=- shape=6981ebd4 vocab=bd7659d9
-/
theorem map_padicInt_smul_of_continuous
    (f : A →+ B) (hf : Continuous f) (a : ℤ_[p]) (x : A) :
    f (a • x) = a • f x := by
  have hleft : Continuous (fun z : ℤ_[p] => f (z • x)) :=
    hf.comp (continuous_id.smul continuous_const)
  have hright : Continuous (fun z : ℤ_[p] => z • f x) :=
    continuous_id.smul continuous_const
  have hclosed : IsClosed {z : ℤ_[p] | f (z • x) = z • f x} :=
    isClosed_eq hleft hright
  refine PadicInt.denseRange_natCast.induction_on a hclosed ?_
  intro n
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

/-- Package the preceding density argument as a linear equivalence.-/
noncomputable def padicLinearEquivOfContinuousAddEquiv
    (e : A ≃+ B) (he : Continuous e) : A ≃ₗ[ℤ_[p]] B :=
  { e with
    map_smul' := fun a x =>
      map_padicInt_smul_of_continuous e.toAddMonoidHom he a x }

end LocalFieldTheory.DiscreteValuationField

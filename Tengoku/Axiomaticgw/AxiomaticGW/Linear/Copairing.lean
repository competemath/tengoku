/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Linear.PerfectPairing
public import Tengoku.Seed.LinearAlgebra.Contraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical copairings

The copairing is the inverse image of the identity under the canonical
equivalence `V tensor V ~= End(V)` induced by a symmetric perfect pairing.

## Reading the Lean notation

* `V ⊗[R] V` is the tensor product over `R`.
* `x ⊗ₜ[R] y` is a pure tensor inside that tensor product.
* `Module.End R V` abbreviates the type of `R`-linear endomorphisms of `V`.
* `r • y` is scalar multiplication of `y` by `r`.
* The hypotheses `Module.Free` and `Module.Finite` provide the finite-free
  duality needed for `Vᵛ ⊗ V ≃ End(V)`.
-/

@[expose] public section

namespace AxiomaticGW

open Module TensorProduct

namespace SymmetricPerfectPairing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Contract the first tensor factor using the metric, identifying
`V tensor V` with `End(V)`.

The displayed definition is a composition of two equivalences.  First
`P.toDual` changes the first copy of `V` into `Vᵛ`.  Then mathlib's
`dualTensorHomEquiv` identifies `Vᵛ ⊗ V` with linear endomorphisms of `V`.-/
noncomputable def tensorEndEquiv (P : SymmetricPerfectPairing R V) :
    V ⊗[R] V ≃ₗ[R] Module.End R V :=
  -- Apply the metric isomorphism to the first tensor factor and do nothing to
  -- the second tensor factor.
  (TensorProduct.congr P.toDual (LinearEquiv.refl R V)).trans
    -- Interpret a dual vector tensored with a vector as a rank-one map.
    (dualTensorHomEquiv R V V)

/-- On a pure tensor, the associated endomorphism sends `z` to
`P.form x z • y`.  This formula fixes our convention for which tensor leg is
contracted.-/
@[simp]
theorem tensorEndEquiv_tmul (P : SymmetricPerfectPairing R V) (x y z : V) :
    P.tensorEndEquiv (x ⊗ₜ[R] y) z = P.form x z • y := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The inverse metric tensor, characterized by contraction to the identity
endomorphism.

`P.tensorEndEquiv.symm` is the inverse direction of the equivalence.  Applying
it to `LinearMap.id` therefore gives the unique tensor whose contraction is
the identity map.-/
noncomputable def copairing (P : SymmetricPerfectPairing R V) : V ⊗[R] V :=
  P.tensorEndEquiv.symm LinearMap.id

/-- The defining universal property of the copairing: mapping it forward gives
the identity endomorphism.-/
@[simp]
theorem tensorEndEquiv_copairing (P : SymmetricPerfectPairing R V) :
    P.tensorEndEquiv P.copairing = LinearMap.id := by
  simp only [copairing, LinearEquiv.apply_symm_apply]

/-- The preceding endomorphism equality evaluated at a vector `x`.  In basis
notation, if `copairing = ∑ᵢ uᵢ ⊗ vᵢ`, this says
`∑ᵢ P.form uᵢ x • vᵢ = x`.-/
theorem copairing_contract (P : SymmetricPerfectPairing R V) (x : V) :
    P.tensorEndEquiv P.copairing x = x := by
  simp only [tensorEndEquiv_copairing, LinearMap.id_coe, id_eq]

/-- Swapping a tensor before contracting exchanges the two vectors tested by
the pairing.

This technical lemma lets us prove symmetry of the copairing without choosing
a basis.  On a pure tensor `u ⊗ v`, both sides reduce to a product of the two
scalars `P.form u y` and `P.form v x`; the general result follows by linearity.-/
theorem form_tensorEndEquiv_comm (P : SymmetricPerfectPairing R V)
    (t : V ⊗[R] V) (x y : V) :
    P.form (P.tensorEndEquiv (TensorProduct.comm R V V t) x) y =
      P.form (P.tensorEndEquiv t y) x := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul u v =>
      simp only [comm_tmul, tensorEndEquiv_tmul, P.isSymm.eq, map_smul,
        LinearMap.smul_apply, smul_eq_mul, mul_comm]
  | add t₁ t₂ h₁ h₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) h₁ h₂

/-- The inverse metric is symmetric: exchanging its two tensor factors does
not change it.

This is the basis-free version of the familiar identity
`ηⁱʲ = ηʲⁱ`.  Later, it says that an internal edge of a TFT or CohFT does not
depend on an arbitrary orientation of that edge.-/
@[simp]
theorem copairing_comm (P : SymmetricPerfectPairing R V) :
    TensorProduct.comm R V V P.copairing = P.copairing := by
  apply P.tensorEndEquiv.injective
  apply LinearMap.ext
  intro x
  apply P.toDual.injective
  apply LinearMap.ext
  intro y
  simp only [toDual_apply]
  rw [form_tensorEndEquiv_comm]
  simp only [copairing_contract]
  exact P.isSymm.eq y x

end SymmetricPerfectPairing

end AxiomaticGW

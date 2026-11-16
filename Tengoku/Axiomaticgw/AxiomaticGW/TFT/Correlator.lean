/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.TFT.FiniteProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Correlators of a commutative Frobenius algebra

For a finite-free commutative Frobenius algebra `F`, the connected genus-`g`
correlator with finite label type `S` is

`ω(g,S)(a) = ε ((∏ s, a s) * E^g)`.

These correlators are defined for all genera and finite label types, including
the unstable arities. A later topological CohFT layer will restrict them to
stable pairs.
-/

@[expose] public section

namespace AxiomaticGW

open TFT

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The finite-labelled genus-`g` scalar correlator associated to a
commutative Frobenius algebra.-/
noncomputable def correlator (F : CommFrobeniusAlgebra R A) (g : ℕ)
    (S : Type*) [Fintype S] : MultilinearMap R (fun _ : S ↦ A) R :=
  (F.counit.comp (LinearMap.mulRight R (F.handleElement ^ g))).compMultilinearMap
    (MultilinearMap.mkPiAlgebra R S A)

/-- Evaluation formula for the Frobenius correlator.-/
@[simp]
theorem correlator_apply (F : CommFrobeniusAlgebra R A) (g : ℕ)
    {S : Type*} [Fintype S] (a : S → A) :
    F.correlator g S a = F.counit ((∏ s, a s) * F.handleElement ^ g) := rfl

/-- Correlators are natural under equivalences of their finite label types.-/
theorem correlator_domDomCongr (F : CommFrobeniusAlgebra R A) (g : ℕ)
    {S T : Type*} [Fintype S] [Fintype T] (e : S ≃ T) :
    (F.correlator g S).domDomCongr e = F.correlator g T := by
  simp only [correlator, LinearMap.compMultilinearMap_domDomCongr,
    TFT.mkPiAlgebra_domDomCongr]

/-- The correlator with no inputs is the partition function
`ε(E^g)`.-/
theorem correlator_empty_apply (F : CommFrobeniusAlgebra R A) (g : ℕ)
    (a : Empty → A) :
    F.correlator g Empty a = F.counit (F.handleElement ^ g) := by
  simp only [correlator_apply, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul]

/-- The genus-zero one-point correlator is the Frobenius counit.-/
theorem correlator_zero_punit_apply (F : CommFrobeniusAlgebra R A) (a : A) :
    F.correlator 0 PUnit (fun _ ↦ a) = F.counit a := by
  simp only [correlator_apply, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_const, Finset.card_singleton, pow_one, pow_zero, mul_one]

/-- The genus-zero ordered two-point correlator is the Frobenius
pairing.-/
theorem correlator_zero_fin_two_apply (F : CommFrobeniusAlgebra R A)
    (a : Fin 2 → A) :
    F.correlator 0 (Fin 2) a = F.pairing.form (a 0) (a 1) := by
  simp only [correlator_apply, Fin.prod_univ_two, pow_zero, mul_one, pairing_apply]

/-- The genus-zero ordered three-point correlator records
multiplication paired with the third input.-/
theorem correlator_zero_fin_three_apply (F : CommFrobeniusAlgebra R A)
    (a : Fin 3 → A) :
    F.correlator 0 (Fin 3) a = F.pairing.form (a 0 * a 1) (a 2) := by
  simp only [correlator_apply, Fin.prod_univ_three, pow_zero, mul_one, pairing_apply]

/-- Inserting the algebra unit at a new `Option` label leaves a correlator
unchanged.-/
theorem correlator_option_one_apply (F : CommFrobeniusAlgebra R A) (g : ℕ)
    {S : Type*} [Fintype S] (a : S → A) :
    F.correlator g (Option S) (fun | none => 1 | some s => a s) =
      F.correlator g S a := by
  simp only [correlator_apply, Fintype.prod_option, one_mul]

/-- Adding one handle is equivalent to inserting the handle element at one
new marked point.-/
theorem correlator_succ_eq_option_handle (F : CommFrobeniusAlgebra R A)
    (g : ℕ) {S : Type*} [Fintype S] (a : S → A) :
    F.correlator (g + 1) S a =
      F.correlator g (Option S)
        (fun | none => F.handleElement | some s => a s) := by
  simp only [correlator_apply, Fintype.prod_option, pow_add, pow_one]
  congr 1
  ac_rfl

end CommFrobeniusAlgebra

end AxiomaticGW

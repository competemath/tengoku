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

/-- Evaluation formula for the Frobenius correlator.
@isnad1 id=eq.0h6v.s8.20bba654271b from=translated src=- shape=bd32a729 vocab=e8a2350f
-/
@[simp]
theorem correlator_apply (F : CommFrobeniusAlgebra R A) (g : ℕ)
    {S : Type*} [Fintype S] (a : S → A) :
    F.correlator g S a = F.counit ((∏ s, a s) * F.handleElement ^ g) := rfl

/-- Correlators are natural under equivalences of their finite label types.
@isnad1 id=eq.0h7v.s7.ae19a67bd96c from=translated src=- shape=48c5842f vocab=2839b0a6
-/
theorem correlator_domDomCongr (F : CommFrobeniusAlgebra R A) (g : ℕ)
    {S T : Type*} [Fintype S] [Fintype T] (e : S ≃ T) :
    (F.correlator g S).domDomCongr e = F.correlator g T := by
  simp only [correlator, LinearMap.compMultilinearMap_domDomCongr,
    TFT.mkPiAlgebra_domDomCongr]

/-- The correlator with no inputs is the partition function
`ε(E^g)`.
@isnad1 id=eq.0h5v.s8.817d6d27de55 from=translated src=- shape=228b80f6 vocab=56191538
-/
theorem correlator_empty_apply (F : CommFrobeniusAlgebra R A) (g : ℕ)
    (a : Empty → A) :
    F.correlator g Empty a = F.counit (F.handleElement ^ g) := by
  simp only [correlator_apply, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul]

/-- The genus-zero one-point correlator is the Frobenius counit.
@isnad1 id=eq.0h4v.s8.d92a3374facf from=translated src=- shape=805e94e4 vocab=f6469cb5
-/
theorem correlator_zero_punit_apply (F : CommFrobeniusAlgebra R A) (a : A) :
    F.correlator 0 PUnit (fun _ ↦ a) = F.counit a := by
  simp only [correlator_apply, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_const, Finset.card_singleton, pow_one, pow_zero, mul_one]

/-- The genus-zero ordered two-point correlator is the Frobenius
pairing.
@isnad1 id=eq.0h4v.s9.31e0f71b28a5 from=translated src=- shape=6dddf0af vocab=0d7e806d
-/
theorem correlator_zero_fin_two_apply (F : CommFrobeniusAlgebra R A)
    (a : Fin 2 → A) :
    F.correlator 0 (Fin 2) a = F.pairing.form (a 0) (a 1) := by
  simp only [correlator_apply, Fin.prod_univ_two, pow_zero, mul_one, pairing_apply]

/-- The genus-zero ordered three-point correlator records
multiplication paired with the third input.
@isnad1 id=eq.0h4v.s9.84c7f1323a57 from=translated src=- shape=93515985 vocab=ceba0a0d
-/
theorem correlator_zero_fin_three_apply (F : CommFrobeniusAlgebra R A)
    (a : Fin 3 → A) :
    F.correlator 0 (Fin 3) a = F.pairing.form (a 0 * a 1) (a 2) := by
  simp only [correlator_apply, Fin.prod_univ_three, pow_zero, mul_one, pairing_apply]

/-- Inserting the algebra unit at a new `Option` label leaves a correlator
unchanged.
@isnad1 id=eq.0h6v.s8.bfac8955d331 from=translated src=- shape=66df521e vocab=cd7d2eb3
-/
theorem correlator_option_one_apply (F : CommFrobeniusAlgebra R A) (g : ℕ)
    {S : Type*} [Fintype S] (a : S → A) :
    F.correlator g (Option S) (fun | none => 1 | some s => a s) =
      F.correlator g S a := by
  simp only [correlator_apply, Fintype.prod_option, one_mul]

/-- Adding one handle is equivalent to inserting the handle element at one
new marked point.
@isnad1 id=eq.0h6v.s8.969c5eacb2a8 from=translated src=- shape=db975b0f vocab=77105563
-/
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

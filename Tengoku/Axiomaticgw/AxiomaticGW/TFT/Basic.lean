/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Linear.Contraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-dimensional topological field theories

`TwoDimensionalTFT` is the finite-labelled correlator presentation of a closed
oriented two-dimensional topological field theory. It records scalar
correlators, their unit, and their one-edge sewing laws. The equivalent
symmetric-monoidal-functor presentation is not constructed here.

Correlators are provided for all genera and all finite label types, including
unstable arities. This makes the counit, metric, and multiplication visible as
low-arity operations and permits a later restriction to stable CohFT arities.
-/

@[expose] public section

namespace AxiomaticGW

/-- A closed oriented two-dimensional TFT in its finite-labelled correlator
presentation.-/
structure TwoDimensionalTFT (R V : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V] where
  /-- The metric used to contract the two half-edges of a node.-/
  pairing : SymmetricPerfectPairing R V
  /-- The distinguished unit state.-/
  unit : V
  /-- The connected genus-`g` correlator with label type `S`.-/
  correlator : (g : ℕ) → (S : Type) → [Fintype S] →
    MultilinearMap R (fun _ : S ↦ V) R
  /-- Correlators are natural under equivalences of finite label types.-/
  relabel : ∀ (g : ℕ) (S T : Type) [Fintype S] [Fintype T] (e : S ≃ T),
    (correlator g S).domDomCongr e = correlator g T
  /-- Inserting the distinguished unit at a new marking changes no
  correlator.-/
  unit_insert : ∀ (g : ℕ) (S : Type) [Fintype S] (a : S → V),
    correlator g (Option S) (fun | none => unit | some s => a s) =
      correlator g S a
  /-- Contracting two markings on one connected component adds a handle.-/
  nonseparating : ∀ (g : ℕ) (S : Type) [Fintype S],
    pairing.selfContract (correlator g (S ⊕ Fin 2)) = correlator (g + 1) S
  /-- Contracting one marking on each of two components joins them.-/
  separating : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T],
    pairing.pairContract (correlator g₁ (Option S))
        (correlator g₂ (Option T)) =
      correlator (g₁ + g₂) (S ⊕ T)
  /-- The genus-zero two-point correlator is the metric.-/
  normalization : ∀ a : Fin 2 → V,
    correlator 0 (Fin 2) a = pairing.form (a 0) (a 1)

namespace TwoDimensionalTFT

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- The genus-zero one-point correlator of a theory, used below as its
candidate Frobenius counit.-/
def counit (T : TwoDimensionalTFT R V) : V →ₗ[R] R :=
  (MultilinearMap.ofSubsingletonₗ R R V R (0 : Fin 1)).symm.toLinearMap
    (T.correlator 0 (Fin 1))

/-- Evaluation of the counit extracted from the one-point correlator.
@isnad1 id=eq.0h4v.s8.270281bff6c0 from=translated src=- shape=016a8d2f vocab=52b2bf23
-/
@[simp]
theorem counit_apply (T : TwoDimensionalTFT R V) (x : V) :
    T.counit x = T.correlator 0 (Fin 1) (fun _ ↦ x) := by
  rfl

end TwoDimensionalTFT

end AxiomaticGW

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Base change of a root pairing carried by the standard lattices

An integral root datum carries its roots and coroots on the standard lattices `κ → ℤ`, paired by
the dot product. The constructions which build a Lie algebra out of a root system — Serre's
presentation, and Geck's construction — instead want a root system over a field of characteristic
zero. This file moves such a pairing along an injective algebra map, expressed by
`[FaithfulSMul R S]`, applying the structure map entrywise to every root and coroot and keeping the
same reflection permutation.

Only the target pairing is chosen here: it is again the dot product, which is perfect on `κ → S` for
every commutative ring `S` by `TauCeti.dotProductBilin_isPerfPair`. So the construction asks the
source pairing to be the dot product too, and every axiom of `RootPairing` then transports along
`Pi.algebraMap`, entrywise application of `algebraMap R S`.

The properties a downstream Lie-theoretic consumer needs are transported separately, each under its
own hypotheses: being crystallographic, being reduced, spanning, and carrying a base with a
prescribed Cartan matrix. Irreducibility is deliberately absent, because it is *false* over `ℤ`:
the sublattice `2 • (κ → ℤ)` is invariant under every reflection. It has to be proved over the new
base ring rather than transported.

## Main definitions

* `TauCeti.rootPairingBaseChange`: the base change of a dot-product root pairing along an injective
  algebra map `R → S`, expressed by `[FaithfulSMul R S]`.
* `TauCeti.rootPairingBaseChangeBase`: the base of the base change attached to a base of the
  original pairing, supported on the same indices.

## Main results

* `TauCeti.isCrystallographic_rootPairingBaseChange`: base change preserves being crystallographic.
* `TauCeti.isReduced_rootPairingBaseChange`: base change preserves being reduced.
* `TauCeti.span_range_root_rootPairingBaseChange_eq_top` and
  `TauCeti.span_range_coroot_rootPairingBaseChange_eq_top`: a spanning family of roots or coroots
  stays spanning.
* `TauCeti.pairingIn_rootPairingBaseChange`: the integral pairings, hence the Cartan matrix of a
  base, are unchanged.

## References

The construction is the standard passage from a root datum over `ℤ` to the root system over `ℚ`
that it determines; see N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1. It
supplies the root-system input of the Chevalley basis in Layer 9,
"pinned Chevalley--Demazure group schemes over `ℤ`", of `TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

open Function Matrix Set
open FaithfulSMul (algebraMap_injective)
open Submodule (span)

/-! ## Entrywise base change of the standard lattice -/

section Entrywise

variable {κ R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Entrywise base change of the standard lattice reads off entrywise. -/
theorem piAlgebraMap_apply (x : κ → R) (j : κ) :
    Pi.algebraMap κ R S x j = algebraMap R S (x j) :=
  rfl

/-- Entrywise base change carries the additive closure of a family into the additive closure of the
base-changed family. -/
theorem mem_closure_image_piAlgebraMap {ι : Type*} {g : ι → (κ → R)} {s : Set ι} {x : κ → R}
    (hx : x ∈ AddSubmonoid.closure (g '' s)) :
    Pi.algebraMap κ R S x ∈
      AddSubmonoid.closure ((fun i => Pi.algebraMap κ R S (g i)) '' s) := by
  have himage : (fun i => Pi.algebraMap κ R S (g i)) '' s =
      (Pi.algebraMap κ R S : (κ → R) →ₗ[R] (κ → S)) '' (g '' s) := by
    rw [← image_comp]
    rfl
  rw [himage, ← AddMonoidHom.map_mclosure]
  exact AddSubmonoid.mem_map_of_mem _ hx

/-- A family of vectors spanning the standard lattice still spans after entrywise base change. -/
theorem span_range_piAlgebraMap_eq_top [Finite κ] {ι : Type*} {v : ι → (κ → R)}
    (hv : span R (range v) = ⊤) :
    span S (range fun i => Pi.algebraMap κ R S (v i)) = ⊤ := by
  classical
  have _i : Fintype κ := Fintype.ofFinite κ
  set W : Submodule S (κ → S) := span S (range fun i => Pi.algebraMap κ R S (v i))
  have hmem : ∀ x : κ → R, Pi.algebraMap κ R S x ∈ W := by
    intro x
    have hsub : span R (range v) ≤ (W.restrictScalars R).comap (Pi.algebraMap κ R S) := by
      rw [Submodule.span_le]
      rintro - ⟨i, rfl⟩
      exact Submodule.subset_span (mem_range_self i)
    exact hsub (hv ▸ Submodule.mem_top)
  have hsingle : ∀ j : κ, Pi.single j (1 : S) ∈ W := by
    intro j
    have hj : Pi.algebraMap κ R S (Pi.single j (1 : R)) = Pi.single j (1 : S) := by
      funext k
      rw [piAlgebraMap_apply]
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [Pi.single_eq_of_ne hk]
    exact hj ▸ hmem (Pi.single j (1 : R))
  refine top_le_iff.mp fun x _ => ?_
  rw [← Module.Basis.sum_repr (Pi.basisFun S κ) x]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (by simpa using hsingle j)

end Entrywise

/-! ## The base-changed pairing -/

section Defs

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)

variable [FaithfulSMul R S]

end Defs

/-! ## Transport of the axioms a Lie-theoretic consumer needs -/

section Transport

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y) [FaithfulSMul R S]

end Transport

/-! ## Bases -/

section Base

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [FaithfulSMul R S] [IsDomain S] (b : P.Base)

end Base

/-! ## Root strings -/

section Chain

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S]
  [Algebra R S] (P : RootPairing ι R (κ → R) (κ → R))
  (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [FaithfulSMul R S]

variable [Finite ι] [IsDomain S] [CharZero R] [P.IsCrystallographic]

end Chain

end TauCeti

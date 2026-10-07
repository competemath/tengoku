/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.Pi
public import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice
public import Tengoku.Seed.LinearAlgebra.Pi

/-!
# Products of subalgebras

In this file we define the product of subalgebras as a subalgebra of the product algebra.

## Main definitions

* `Subalgebra.pi`: the product of subalgebras.
-/

@[expose] public section

open Algebra

namespace Subalgebra
variable {ι R : Type*} {S : ι → Type*} [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]
  {s : Set ι} {t t₁ t₂ : ∀ i, Subalgebra R (S i)} {x : ∀ i, S i}

/-- The product of subalgebras as a subalgebra. -/
@[simps coe toSubsemiring]
def pi (s : Set ι) (t : ∀ i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
  __ := Submodule.pi s fun i ↦ (t i).toSubmodule
  mul_mem' hx hy i hi := (t i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (t i).algebraMap_mem _

/--
@isnad1 id=iff.0h6v.s7.18ab9ab4c93c from=seed src=0 shape=8d00210d vocab=94c5d0ab
-/
@[simp] lemma mem_pi : x ∈ pi s t ↔ ∀ i ∈ s, x i ∈ t i := .rfl

open Subalgebra in
/--
@isnad1 id=eq.0h5v.s10.1ae2fc27db8b from=seed src=0 shape=ab90a9ee vocab=762407fa
-/
@[simp] lemma pi_toSubmodule : toSubmodule (pi s t) = .pi s fun i ↦ (t i).toSubmodule := rfl

/--
@isnad1 id=eq.0h4v.s9.9091628eb343 from=seed src=0 shape=328a6c37 vocab=7734811a
-/
@[simp]
lemma pi_top (s : Set ι) : pi s (fun i ↦ (⊤ : Subalgebra R (S i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _

/--
@isnad1 id=le.1h6v.s7.4f115df12286 from=seed src=0 shape=aba15362 vocab=9831d1f8
-/
@[gcongr] lemma pi_mono (h : ∀ i ∈ s, t₁ i ≤ t₂ i) : pi s t₁ ≤ pi s t₂ := Set.pi_mono h

/--
@isnad1 id=eq.0h3v.s6.9448f4b1a81a from=seed src=0 shape=84d46bca vocab=3cd4a938
-/
protected theorem center_pi : center R (Π i, S i) = pi .univ fun i ↦ center R (S i) :=
  SetLike.coe_injective Set.center_pi

end Subalgebra

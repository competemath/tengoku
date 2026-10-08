/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `WStarAlgebra M` is a C⋆ algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `VonNeumannAlgebra H` (where `H` is a Hilbert space)
is a \*-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a \*-closed subalgebra which is weakly closed.
-/

@[expose] public section


universe u v

/-- Sakai's definition of a von Neumann algebra as a C⋆ algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed \*-subalgebras of B(H)),
we name this definition `WStarAlgebra`.

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-\* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class WStarAlgebra (M : Type u) [CStarAlgebra M] : Prop where
  /-- There is a Banach space `X` whose dual is isometrically (conjugate-linearly) isomorphic
  to the `WStarAlgebra`. -/
  exists_predual :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X) (_ : CompleteSpace X),
      Nonempty (StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

-- TODO: Without this, `VonNeumannAlgebra` times out. Why?
/-- The double commutant definition of a von Neumann algebra,
as a \*-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `WStarAlgebra` for the abstract notion (a C⋆-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `VonNeumannAlgebra`
(although we will later construct the instance `WStarAlgebra (H →L[ℂ] H)`),
and instead will use `⊤ : VonNeumannAlgebra H`.
-/
structure VonNeumannAlgebra (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] extends StarSubalgebra ℂ (H →L[ℂ] H) where
  /-- The double commutant (a.k.a. centralizer) of a `VonNeumannAlgebra` is itself. -/
  centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a \*-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance instSetLike : SetLike (VonNeumannAlgebra H) (H →L[ℂ] H) where
  coe S := S.carrier
  coe_injective S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr

instance : PartialOrder (VonNeumannAlgebra H) := .ofSetLike (VonNeumannAlgebra H) (H →L[ℂ] H)

/--
@isnad1 id=starmemc.0h1v.s6.664254d77e6a from=seed src=0 shape=1753fb93 vocab=fc1f877b
-/
noncomputable instance instStarMemClass : StarMemClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  star_mem {s} := s.star_mem'

/--
@isnad1 id=subringc.0h1v.s7.82d8799b169a from=seed src=0 shape=1753fb93 vocab=27eb544f
-/
instance instSubringClass : SubringClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a ∈ s.toStarSubalgebra from neg_mem ha

/--
@isnad1 id=iff.0h3v.s10.b434603fafbb from=seed src=0 shape=da4a56cd vocab=f4cbbf97
-/
@[simp]
theorem mem_carrier {S : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ S.toStarSubalgebra ↔ x ∈ (S : Set (H →L[ℂ] H)) :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s9.0c77b20c564c from=seed src=0 shape=db8cd80b vocab=5f79dd94
-/
@[simp]
theorem coe_toStarSubalgebra (S : VonNeumannAlgebra H) :
    (S.toStarSubalgebra : Set (H →L[ℂ] H)) = S :=
  rfl

/--
@isnad1 id=eq.1h2v.s11.e29087268464 from=seed src=0 shape=89a77d57 vocab=2c43d0a2
-/
@[simp]
theorem coe_mk (S : StarSubalgebra ℂ (H →L[ℂ] H)) (h) :
    ((⟨S, h⟩ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = S :=
  rfl

/--
@isnad1 id=eq.1h3v.s8.0874e7e90bcc from=seed src=0 shape=7bbb476e vocab=a1896aa3
-/
@[ext]
theorem ext {S T : VonNeumannAlgebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/--
@isnad1 id=eq.0h2v.s8.53095453b035 from=seed src=0 shape=1d02b789 vocab=be4abded
-/
@[simp]
theorem centralizer_centralizer (S : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S :=
  S.centralizer_centralizer'

/-- The centralizer of a `VonNeumannAlgebra`, as a `VonNeumannAlgebra`. -/
noncomputable def commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by simp

/--
@isnad1 id=eq.0h2v.s8.b297ff2c739f from=seed src=0 shape=43d37824 vocab=7c49e1ce
-/
@[simp]
theorem coe_commutant (S : VonNeumannAlgebra H) :
    ↑S.commutant = Set.centralizer (S : Set (H →L[ℂ] H)) := by
  simp [commutant]

/--
@isnad1 id=iff.0h3v.s10.be9a53dca358 from=seed src=0 shape=ab35f89f vocab=08509d93
-/
@[simp]
theorem mem_commutant_iff {S : VonNeumannAlgebra H} {z : H →L[ℂ] H} :
    z ∈ S.commutant ↔ ∀ g ∈ S, g * z = z * g := by
  rw [← SetLike.mem_coe, coe_commutant]
  rfl

/--
@isnad1 id=eq.0h2v.s5.949814a72274 from=seed src=0 shape=74762cea vocab=1a71a480
-/
@[simp]
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
  SetLike.coe_injective <| by simp

open ContinuousLinearMap in
/-- An idempotent is an element in a von Neumann algebra if and only if
its range and kernel are invariant under the commutant.
@isnad1 id=iff.1h3v.s10.ff379e3bd91a from=seed src=0 shape=1c511c4c vocab=0a30253d
-/
theorem IsIdempotentElem.mem_iff {e : H →L[ℂ] H} (h : IsIdempotentElem e)
    (S : VonNeumannAlgebra H) :
    e ∈ S ↔ ∀ y ∈ S.commutant,
      e.range ∈ Module.End.invtSubmodule y ∧ e.ker ∈ Module.End.invtSubmodule y := by
  conv_rhs => simp [← h.commute_iff, Commute.symm_iff (a := e), commute_iff_eq, ← mem_commutant_iff]

open VonNeumannAlgebra ContinuousLinearMap in
/-- A star projection is an element in a von Neumann algebra if and only if
its range is invariant under the commutant.
@isnad1 id=iff.1h3v.s10.7d5edd882b2f from=seed src=0 shape=6bfd297f vocab=2e4dfe2f
-/
theorem IsStarProjection.mem_iff {e : H →L[ℂ] H} (he : IsStarProjection e)
    (S : VonNeumannAlgebra H) :
    e ∈ S ↔ ∀ y ∈ S.commutant, e.range ∈ Module.End.invtSubmodule y := by
  simp_rw [he.isIdempotentElem.mem_iff, he.isIdempotentElem.range_mem_invtSubmodule_iff,
    he.isIdempotentElem.ker_mem_invtSubmodule_iff, forall_and, and_iff_left_iff_imp, ← mul_def]
  intro h x hx
  simpa [he.isSelfAdjoint.star_eq] using! congr(star $(h _ (star_mem hx)))

end VonNeumannAlgebra

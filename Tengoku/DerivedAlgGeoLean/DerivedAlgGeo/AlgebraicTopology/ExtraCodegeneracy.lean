/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicTopology.AlternatingFaceMapComplex
import Tengoku.Seed.AlgebraicTopology.ExtraDegeneracy
import Tengoku.Seed.Algebra.Homology.Opposite
import Tengoku.Seed.Algebra.Homology.QuasiIso
import Tengoku.Seed.Algebra.Homology.SingleHomology
import Tengoku.Seed.CategoryTheory.Abelian.Opposite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The alternating coface complex is the opposite of an alternating face complex

Mathlib develops extra degeneracies, and the homotopy equivalence they induce, on the
**simplicial** side: `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` is stated
against `alternatingFaceMapComplex` and lands in `ChainComplex`. Čech cohomology, in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`, is built from
`alternatingCofaceMapComplex` and is **cosimplicial**. Nothing upstream connects the two, so
no Čech vanishing argument can reach the machinery that would prove it.

This file supplies the connection: for a cosimplicial object `Y` in a preadditive category,

```lean
((alternatingCofaceMapComplex A).obj Y).op ≅ (alternatingFaceMapComplex Aᵒᵖ).obj Y.op
```

Both sides are `Y.obj ⦋n⦌` in degree `n` — that much is `rfl` — and both differentials are
`∑ i, (-1) ^ i • δ i`. What is not `rfl` is that `HomologicalComplex.op` distributes over the
sum and the `zsmul`; that is the content, such as it is, and `op_sum` and `op_zsmul` supply
it.

## Why this is the useful direction

The alternative is to define an extra *co*degeneracy structure on augmented cosimplicial
objects and redo the homotopy from scratch, roughly duplicating
`Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`. With this isomorphism that is unnecessary:
a cosimplicial object in `A` is a simplicial object in `Aᵒᵖ`, the upstream extra-degeneracy
theory applies there verbatim, and the isomorphism carries its conclusion back. In
particular `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` — the Čech object of a
family has an extra degeneracy once the terminal object maps into one of its members — is
already upstream and can be used as it stands.

## The payoff

`exactAt_succ_of_extraDegeneracy` is what #13 consumes: an extra degeneracy on an augmented
simplicial object in `Aᵒᵖ` whose underlying object is `Y.op` forces the alternating coface
complex of `Y` to be exact in every positive degree. The chain is
`ExtraDegeneracy.homotopyEquiv` (upstream) → quasi-isomorphism → `exactAt_iff_of_quasiIsoAt`
→ `ChainComplex.exactAt_succ_single_obj`, carried across `opIso`.

`exactAt_succ_of_extraDegeneracy_map` adds the contravariant transport. `ExtraDegeneracy.map`
takes a covariant functor, while Čech cohomology applies `FormalCoproduct.evalOp` of a
presheaf, which is contravariant on the site; `Functor.rightOp` turns one into the other, and
this lemma is the composite in the form the caller wants.

## Not done here

An augmentation `ε` for `alternatingCofaceMapComplex`, dual to `AlternatingFaceMapComplex.ε`,
was expected to be needed and **is not**. The augmentation is handled on the simplicial side
by `homotopyEquiv`, and the coface complex only ever appears unaugmented, so adding one would
be dead weight. Recorded because the issue asked for it.

`DerivedAlgGeo/AlgebraicGeometry/Cohomology/Cech/Affine.lean` now supplies the remaining affine
argument: it identifies
the restriction maps degreewise as localizations and descends exactness from a finite
distinguished-open cover whose defining elements span the unit ideal.

The `Abelian A` hypothesis is stronger than the argument needs — `Preadditive`, a zero object
and homology would do — but the two `HasZeroMorphisms Aᵒᵖ` instances (`Preadditive`'s and
`Limits.hasZeroMorphismsOpposite`) are only definitionally equal, and `rw` sees through
neither. Assuming `Abelian` makes instance search pick one consistently. Every intended
caller is abelian.

## References

* `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean` — the simplicial theory this reaches
* `Mathlib/CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean` — the Čech object's
  extra degeneracy, already upstream
-/

universe v u

open CategoryTheory Opposite Simplicial

namespace AlgebraicTopology

namespace AlternatingCofaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The alternating coface map complex of a cosimplicial object `Y` in `A`, made opposite, is
the alternating face map complex of `Y` viewed as a simplicial object in `Aᵒᵖ`.

Degreewise both sides are `Y.obj ⦋n⦌`, and both differentials are `∑ i, (-1) ^ i • δ i`; the
proof is that `op` distributes over that sum.-/
noncomputable def opIso (Y : CosimplicialObject A) :
    ((alternatingCofaceMapComplex A).obj Y).op ≅ (alternatingFaceMapComplex Aᵒᵖ).obj Y.op :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : j + 1 = i)
    simp only [Iso.refl_hom, HomologicalComplex.op_d]
    simp [AlternatingFaceMapComplex.objD, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj,
      AlternatingCofaceMapComplex.objD, SimplicialObject.δ, CosimplicialObject.δ,
      CochainComplex.of_d, op_sum, op_zsmul]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/--
@isnad1 id=eq.0h3v.s9.6e3830a8fe6b from=translated src=- shape=89818d17 vocab=efcb7819
-/
@[simp]
lemma opIso_hom_f (Y : CosimplicialObject A) (n : ℕ) :
    (opIso Y).hom.f n = 𝟙 _ :=
  rfl

/--
@isnad1 id=eq.0h3v.s9.560b4596c69b from=translated src=- shape=441ae80b vocab=f150cb12
-/
@[simp]
lemma opIso_inv_f (Y : CosimplicialObject A) (n : ℕ) :
    (opIso Y).inv.f n = 𝟙 _ :=
  rfl

end AlternatingCofaceMapComplex

section Exactness

open SimplicialObject.Augmented

variable {A : Type u} [Category.{v} A] [Abelian A]

end Exactness

end AlgebraicTopology

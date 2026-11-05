/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Étale pairs in the image form and their disjoint unions

Kollár's étale equivalence of two hypersurfaces of maximal contact takes "étale surjections
`ψ, ψ' : U ⇉ X`" [Kol07, Definition 91]. Here surjectivity is replaced by the image form: the
images of `ψ` and `ψ'` each contain the relevant closed set (the cosupport of the marked ideal),
because surjective pairs need not exist. Kollár's construction ends with "The images of finitely
many of the `U(p)` cover `X`. We can take `U` to be their disjoint union" ([Kol07, 95], the proof
of Theorem 92).

* `EtaleImagePair X S`: étale `ψ, ψ' : U ⟶ X` whose images both contain `S`, the pair of
  [Kol07, Definition 91] in the image form. The étale equivalence of
  `Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquiv.lean` adds the conditions (91.1′)–(91.4′)
  to this pair.
* `EtaleImagePair.sigma`: the disjoint union `∐ W_i` of a finite family of pairs with
  `ψ := Sigma.desc ψ_i`, `ψ' := Sigma.desc ψ'_i`, étale because étaleness is local at the source
  (`IsZariskiLocalAtSource.sigmaDesc`), covering because each `ψ_i` factors through `ψ`.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- A pair of étale morphisms `ψ, ψ' : U ⟶ X` whose images both contain the set `S` (in the
application, the cosupport of a marked ideal): the "étale surjections `ψ, ψ' : U ⇉ X`" of
[Kol07, Definition 91], in the image form.-/
structure EtaleImagePair (X : Scheme.{u}) (S : Set X) where
  /-- The étale neighbourhood.-/
  U : Scheme.{u}
  /-- The first étale map.-/
  ψ : U ⟶ X
  /-- The second étale map.-/
  ψ' : U ⟶ X
  etale_ψ : Etale ψ
  etale_ψ' : Etale ψ'
  /-- The image of `ψ` contains `S` (the replacement for surjectivity).-/
  covers : S ⊆ Set.range ψ.base
  /-- The image of `ψ'` contains `S`.-/
  covers' : S ⊆ Set.range ψ'.base

attribute [instance] EtaleImagePair.etale_ψ EtaleImagePair.etale_ψ'

end AlgebraicGeometry

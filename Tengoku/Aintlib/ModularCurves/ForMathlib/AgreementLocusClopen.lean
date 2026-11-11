/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FormallyUnramified
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The agreement locus of two maps into an étale morphism is clopen (YFULL route γ)

For `f : X ⟶ S` formally unramified, locally of finite type, and separated (in
particular for `f` étale), and two `S`-maps `a b : Z ⟶ X` with `a ≫ f = b ≫ f`, the
scheme-theoretic **agreement locus** — the pullback of the relative diagonal
`pullback.diagonal f` along `pullback.lift a b` — includes into `Z` by a morphism that is
simultaneously an open immersion (the diagonal of an unramified morphism is an open
immersion) and a closed immersion (the diagonal of a separated morphism is a closed
immersion). Hence its range in `Z` is **clopen**.

This is the topological engine of the `Y(N)` clopen full-level locus (route γ): the locus
where two of the `N²` torsion sections `[a]P + [b]Q` coincide is the agreement locus of
two sections of the finite-étale `E[N] ×_S E[N] → S`, hence clopen; the full-level locus
is the complement of the union of these finitely many closed agreement loci, hence open.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S)

/-- The inclusion of the agreement locus of `a, b : Z ⟶ X` (over `f`) into `Z`: the
pullback of the relative diagonal `pullback.diagonal f` along `pullback.lift a b`.-/
noncomputable def agreementι (a b : Z ⟶ X) (hab : a ≫ f = b ≫ f) :
    pullback (pullback.lift a b hab) (pullback.diagonal f) ⟶ Z :=
  pullback.fst (pullback.lift a b hab) (pullback.diagonal f)

end AlgebraicGeometry

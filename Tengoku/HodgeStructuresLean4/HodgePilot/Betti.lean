import Tengoku.HodgeStructuresLean4.HodgePilot.Analytic
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sheaf cohomology of the constant sheaf ("Betti" cohomology)

For a topological space `X` this file packages the **sheaf cohomology of the
constant abelian sheaf** on `X`, with rational and complex coefficients, and
the coefficient-change map between them.  Following the standard abuse we call
this "Betti cohomology" of `X`; throughout, the word *Betti* is only ever used
as a gloss for the precise object, namely
`H^n(X, \underline{ℚ}) := \operatorname{Ext}^n(\underline{ℤ}, \underline{ℚ})`
computed in the category of abelian sheaves on `X` (Riou's `Sheaf.H`, i.e. the
Yoneda–Ext description of sheaf cohomology).

## Main definitions

* `bettiSheafQ X` / `bettiSheafC X` — the constant abelian sheaves with values
  `ULift ℚ` and `ULift ℂ` on `X` (the `ULift` keeps the coefficients in the
  same universe as the site).
* `bettiQ X n` / `bettiC X n` — their `n`-th sheaf cohomology groups, with their
  ambient `AddCommGroup` structure (synthesised automatically: on the small site
  `Opens X` the whole `HasSheafify`/`IsGrothendieckAbelian`/`HasExt` chain fires
  by instance resolution).
* `coeffHom` — the additive coefficient homomorphism `ULift ℚ → ULift ℂ`.
* `toComplexCoeffs X n : bettiQ X n →+ bettiC X n` — the induced coefficient
  change `H^n(X, ℚ) → H^n(X, ℂ)`.
* `analyticBettiQ A n` — for a commutative `ℂ`-algebra `A`, the sheaf-Betti
  cohomology of the analytic space of ℂ-points `CPoints A` (from
  `HodgePilot.Analytic`): `H^n(X(ℂ)_an, ℚ)` of an affine complex variety, a
  constructed object at this pin.
* `globalSectionsEquiv X` — the degree-zero identification
  `bettiQ X 0 ≃+ Γ(X, \underline{ℚ})` (the global sections of the constant sheaf),
  via `Sheaf.H.equiv₀` at the terminal open `⊤`.  No identification with `ℚ` is
  asserted: that requires a connectedness hypothesis and is deliberately omitted.

## Scope and claim discipline

This is *sheaf* cohomology of the *constant* sheaf.  **No agreement with singular
cohomology is asserted anywhere in this file**, and none is implied by the name
"Betti".  The program separately constructs a genuine singular-cohomology object
(in a sibling module); the two are distinct constructions, they coincide only
classically, and the statement identifying them
(`SingularSheafComparison`) is a *future, currently unproven* theorem — it is not
used here and nothing below depends on it.  In the language of the eventual
comparison bridge, this module builds the **sheaf-theoretic side**: sheaf
cohomology of constant coefficients on arbitrary topological spaces, with a
`ℚ → ℂ` coefficient change, instantiated on the analytic point-spaces of affine
complex algebras — the sheaf-theoretic side of a future comparison; no relation
to singular cohomology is asserted.

## References

* J. Riou, sheaf cohomology as `Ext` from the constant sheaf
  (`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`).
-/

open CategoryTheory Opposite AlgebraicGeometry HodgePilot.Analytic

universe u

noncomputable section

namespace HodgePilot.Betti

/-! ## 1. The constant sheaves and their cohomology groups -/

section Space

variable (X : TopCat.{u})

/-- The constant abelian sheaf with values `ℚ` on a topological space `X`
(coefficients lifted to the universe of the site).-/
def bettiSheafQ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (constantSheaf _ _).obj (AddCommGrpCat.of (ULift.{u} ℚ))

/-- The constant abelian sheaf with values `ℂ` on a topological space `X`.-/
def bettiSheafC : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (constantSheaf _ _).obj (AddCommGrpCat.of (ULift.{u} ℂ))

/-- Sheaf-theoretic Betti cohomology with **rational** coefficients:
`H^n(X, \underline{ℚ})`.-/
abbrev bettiQ (n : ℕ) : Type u := (bettiSheafQ X).H n

/-- Sheaf-theoretic Betti cohomology with **complex** coefficients:
`H^n(X, \underline{ℂ})`.-/
abbrev bettiC (n : ℕ) : Type u := (bettiSheafC X).H n

end Space

/-! ## 2. Coefficient change `ℚ → ℂ` -/

/-- The coefficient homomorphism `ULift ℚ → ULift ℂ` as a morphism of additive
groups.  Transported along `AddEquiv.ulift` in both directions (hand-rolling the
`ULift` map dies on definitional equality).-/
def coeffHom : AddCommGrpCat.of (ULift.{u} ℚ) ⟶ AddCommGrpCat.of (ULift.{u} ℂ) :=
  AddCommGrpCat.ofHom
    (AddEquiv.ulift.symm.toAddMonoidHom.comp
      (((Rat.castHom ℂ).toAddMonoidHom).comp AddEquiv.ulift.toAddMonoidHom))

section Space

variable (X : TopCat.{u})

/-- Coefficient change on Betti cohomology, `H^n(X, ℚ) → H^n(X, ℂ)`: a
constructed additive map, induced by the constant-sheaf functor applied to the
coefficient homomorphism `ℚ → ℂ`.-/
def toComplexCoeffs (n : ℕ) : bettiQ X n →+ bettiC X n :=
  Sheaf.H.map ((constantSheaf _ _).map (coeffHom.{u})) n

@[simp]
lemma toComplexCoeffs_zero (n : ℕ) : toComplexCoeffs X n 0 = 0 :=
  map_zero _

lemma toComplexCoeffs_add (n : ℕ) (x y : bettiQ X n) :
    toComplexCoeffs X n (x + y) = toComplexCoeffs X n x + toComplexCoeffs X n y :=
  map_add _ _ _

end Space

/-! ## 3. The analytic junction: `H^n(X(ℂ)_an, ℚ)` for an affine complex algebra -/

section Analytic

variable (A : Type u) [CommRing A] [Algebra ℂ A]

/-- The analytic space of ℂ-points of `Spec A`, as a `TopCat`.-/
def anTop : TopCat.{u} := TopCat.of (CPoints A)

/-- Sheaf-theoretic Betti cohomology of the analytic space of ℂ-points of an
affine complex algebra, with rational coefficients: `H^n(X(ℂ)_an, ℚ)`, a
constructed object at this pin.-/
abbrev analyticBettiQ (n : ℕ) : Type u := bettiQ (anTop A) n

/-- Its `ℚ → ℂ` coefficient change is likewise constructed.-/
abbrev analyticToComplexCoeffs (n : ℕ) : analyticBettiQ A n →+ bettiC (anTop A) n :=
  toComplexCoeffs (anTop A) n

end Analytic

/-! ## 4. Degree-zero sanity: global sections of the constant sheaf -/

section H0

variable (X : TopCat.{u})

/-- The top open `⊤ : Opens X` is a terminal object of the site `Opens X`
(a preorder category: the unique map is `homOfLE le_top`).-/
def opensTopTerminal : Limits.IsTerminal (⊤ : TopologicalSpace.Opens X) :=
  Limits.IsTerminal.ofUniqueHom (fun _ => homOfLE le_top)
    (fun _ _ => Subsingleton.elim _ _)

/-- Degree-zero identification: `H^0(X, \underline{ℚ})` is the group of global
sections of the constant sheaf `\underline{ℚ}`, via `Sheaf.H.equiv₀` at the
terminal open.  (This is `Γ(X, \underline{ℚ})`; no identification with `ℚ`
itself is claimed — that would require a connectedness hypothesis.)-/
def globalSectionsEquiv :
    bettiQ X 0 ≃+ (bettiSheafQ X).obj.obj (op (⊤ : TopologicalSpace.Opens X)) :=
  Sheaf.H.equiv₀ (bettiSheafQ X) (opensTopTerminal X)

end H0

end HodgePilot.Betti

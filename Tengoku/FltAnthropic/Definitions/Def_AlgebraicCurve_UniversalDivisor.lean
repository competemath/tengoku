import Tengoku.Seed.AlgebraicGeometry.Pullbacks
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Functorial
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatRank
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FiniteType
import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact
import Tengoku.Seed.AlgebraicGeometry.Properties

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]

structure RelEffDivisor (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) where
  I : (pullback c t).IdealSheafData
  isFinite : IsFinite (I.subschemeι ≫ pullback.snd c t)
  flat : Flat (I.subschemeι ≫ pullback.snd c t)
  finrank_eq : ∀ s : T, (I.subschemeι ≫ pullback.snd c t).finrank s = r

@[ext] lemma RelEffDivisor.ext {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {D₁ D₂ : RelEffDivisor C c r T t}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl

section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}

end transport

end AlgebraicCurve

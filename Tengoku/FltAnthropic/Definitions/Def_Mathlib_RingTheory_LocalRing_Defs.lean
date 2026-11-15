import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]

open IsLocalRing

/--
@isnad1 id=islocalr.0h2v.s5.665029a0ea7b from=translated src=- shape=563e20e0 vocab=e3311d38
-/
instance IsLocalRing.quot : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective

/--
@isnad1 id=islocalh.0h2v.s7.a1577d9f2662 from=translated src=- shape=302a2ce2 vocab=64440377
-/
instance IsLocalHom.quotient_mk : IsLocalHom (algebraMap R (R ⧸ I)) :=
  .of_surjective _ Ideal.Quotient.mk_surjective

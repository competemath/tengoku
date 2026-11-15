import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]

open IsLocalRing

instance IsLocalRing.quot : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective

instance IsLocalHom.quotient_mk : IsLocalHom (algebraMap R (R ⧸ I)) :=
  .of_surjective _ Ideal.Quotient.mk_surjective

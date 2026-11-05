module

public import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

@[simp]
lemma Ideal.quotientInfRingEquivPiQuotient_mk {R ι : Type*} [Finite ι] [CommRing R]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) (x : R) :
    Ideal.quotientInfRingEquivPiQuotient I hI x = fun _ ↦ Ideal.Quotient.mk _ x := rfl

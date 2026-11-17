import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.MillerTancer.Family
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.Gordon.Family

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two explicit Adian--Rabin constructions

This file is the statement-level interface for the two constructions
formalized in this project.  The Miller--Tancer construction is generic in
the number of generators and relators, subject to the normal-weight-one
hypothesis.  Gordon's Lemma 2.1 is generic in the host presentation and its
abelian-order data.
-/

namespace Undecidability.AdianRabin

/-- The compressed Miller--Tancer construction produces an Adian--Rabin
family with one additional generator and two additional relators when the
normal generator is a displayed presentation generator.
@isnad1 id=ex.2h4v.s6.29fe2951a4bb from=translated src=- shape=33ab4b2f vocab=b06dfd6e
-/
theorem exists_miller_tancer_family
    (P : FP n m) (k : Fin n)
    (hP : ¬ ComputablePred P.wordProblem)
    (hk : P.NormallyGenerates (Word.generator k)) :
    ∃ A : ℕ → FP (n + 1) (m + 2),
      FP.IsAdianRabinFamily A :=
  ⟨MillerTancer.Compressed.family P k,
    MillerTancer.Compressed.family_isAdianRabin P k hP hk⟩

end Undecidability.AdianRabin

import Tengoku.AdianRabin.GroupUndecidability.Presentation
import Tengoku.Seed.Computability.Reduce

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability

/-- A total computable enumeration of all words on `n` generators.-/
def wordOfNat (n : ℕ) (k : ℕ) : Word n :=
  (Encodable.decode k : Option (Word n)).getD []

/--
@isnad1 id=computab.0h1v.s4.c9b33b09b8cb from=translated src=- shape=0fc427d2 vocab=cea1ffb2
-/
theorem wordOfNat_computable (n : ℕ) :
    Computable (wordOfNat n) :=
  Computable.option_getD
    (@Computable.decode (Word n) _)
    (Computable.const ([] : Word n))

/--
@isnad1 id=eq.0h2v.s4.b334ffc5946b from=translated src=- shape=f4fd66d2 vocab=cf83a423
-/
@[simp]
theorem wordOfNat_encode (w : Word n) :
    wordOfNat n (Encodable.encode w) = w := by
  simp [wordOfNat]

/-- Undecidability transfers forward along a computable many-one reduction.
@isnad1 id=not.2h4v.s5.5febf0a87410 from=translated src=- shape=cd4b08bb vocab=21751851
-/
theorem not_computablePred_of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop}
    (hp : ¬ ComputablePred p) (hred : p ≤₀ q) :
    ¬ ComputablePred q := by
  intro hq
  exact hp (ComputablePred.computable_of_manyOneReducible hred hq)

/--
Turn a uniform word-indexed presentation construction into a natural-number
indexed Adian--Rabin family.
@isnad1 id=isadianr.3h6v.s6.95ad56808caf from=translated src=- shape=43ea1ab5 vocab=02f9714c
-/
theorem isAdianRabinFamily_of_wordProblem_reduction
    {n m n' m' : ℕ}
    (P : FP n m) (R : Word n → FP n' m')
    (hP : ¬ ComputablePred P.wordProblem)
    (hR : Computable₂ fun w i => (R w).relator i)
    (hiff : ∀ w, (R w).presentsTrivial ↔ P.wordProblem w) :
    FP.IsAdianRabinFamily (fun j => R (wordOfNat n j)) := by
  constructor
  · unfold FP.Effective
    exact hR.comp
      ((wordOfNat_computable n).comp Computable.fst)
      Computable.snd
  · apply not_computablePred_of_manyOneReducible hP
    refine ⟨Encodable.encode, Computable.encode, ?_⟩
    intro w
    simpa only [wordOfNat_encode] using (hiff w).symm

end Undecidability

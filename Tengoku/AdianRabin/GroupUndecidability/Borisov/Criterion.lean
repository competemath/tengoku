import Tengoku.AdianRabin.GroupUndecidability.Borisov.Construction
import Tengoku.AdianRabin.GroupUndecidability.Borisov.Mod5.Sparsity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borisov's simulation criterion

The forward implication is the relator calculation in `Construction.lean`.  The
converse is the complete normal-form argument, culminating in the mod-five
free-product syllable comparison that bounds a coefficient preimage by one
displayed rule letter.
-/

namespace Undecidability
namespace Borisov

/-- The deep normal-form direction in Borisov's simulation theorem.
@isnad1 id=thueeq.1h2v.s5.12b8c5ebaf93 from=translated src=- shape=a33881f7 vocab=89c7a2e2
-/
theorem criterion_converse
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (presentation datum).wordProblem (testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  BorisovModFiveSparsity.criterion_converse datum Q

/-- Borisov's simulation theorem, specialized to the standing datum.
@isnad1 id=iff.0h2v.s5.c5b504bfce39 from=translated src=- shape=c16a6ad7 vocab=89c7a2e2
-/
theorem criterion
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P ↔
      (presentation datum).wordProblem (testWord Q) :=
  ⟨criterion_forward datum Q, criterion_converse datum Q⟩

end Borisov
end Undecidability

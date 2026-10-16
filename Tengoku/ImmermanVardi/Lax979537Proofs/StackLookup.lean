import Tengoku.ImmermanVardi.Lax979537Proofs.StackRepeat

namespace Lax979537Proofs.StackLookup

open StackProgram StackTransfer StackRepeat

variable {K Aux : Type} [DecidableEq K]

def discard (table : K) : BitProgram K Aux :=
  .atom (.pop table (fun s _ => s))

def discardStore (table : K) (s : BitStore K Aux) : BitStore K Aux :=
  Op.apply (.pop table (fun s _ => s)) s

/-- Consume an index counter, skip that many table bits, and store the next
bit (or exhaustion) in auxiliary control. -/
def lookup (index table : K) : BitProgram K (Aux × Option Bool) :=
  .seq (repeatCount index (discard table))
    (.atom (.pop table (fun s b => ((s.1.1, b), none))))

theorem discard_working (base : K → List Bool) (index table : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    discardStore table (working base index table xs ys a scratch) =
      working base index table xs ys.tail a scratch := by
  apply Store.ext
  · rfl
  · funext k
    by_cases ht : k = table <;> simp_all [discardStore, Op.apply, working]

end Lax979537Proofs.StackLookup

import Tengoku.ImmermanVardi.Lax979537Proofs.StackProgram
import Tengoku

namespace Lax979537Proofs.StackTransfer

open StackProgram

variable {K Aux : Type}

abbrev BitStore (K Aux : Type) := Store (fun _ : K => Bool) (Aux × Option Bool)
abbrev BitProgram (K Aux : Type) := Program (fun _ : K => Bool) (Aux × Option Bool)

def read (src : K) : BitProgram K Aux :=
  .atom (.pop src (fun s b => (s.1, b)))

def transferBody (src dst : K) : BitProgram K Aux :=
  .seq (.atom (.push dst (fun s => s.2.getD false))) (read src)

def transferLoop (src dst : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (transferBody src dst)

/-- Move a bit string from one stack onto another, in reversed order.
The auxiliary finite state and every other stack are preserved. -/
def transfer (src dst : K) : BitProgram K Aux :=
  .seq (read src) (transferLoop src dst)

def working [DecidableEq K] (base : K → List Bool) (src dst : K)
    (xs ys : List Bool) (a : Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(a, scratch), Function.update (Function.update base src xs) dst ys⟩

theorem pop_working [DecidableEq K] (base : K → List Bool) (src dst : K)
    (hne : src ≠ dst) (xs ys : List Bool) (a : Aux) (scratch : Option Bool) :
    Op.apply (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base src dst xs ys a scratch) =
      working base src dst xs.tail ys a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working, hne]
  · funext k
    by_cases hs : k = src <;> by_cases hd : k = dst <;>
      simp_all [Op.apply, working]

theorem push_working [DecidableEq K] (base : K → List Bool) (src dst : K)
    (xs ys : List Bool) (a : Aux) (b : Bool) :
    Op.apply (.push dst (fun s : Aux × Option Bool => s.2.getD false))
      (working base src dst xs ys a (some b)) =
      working base src dst xs (b :: ys) a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hd : k = dst <;> simp_all [Op.apply, working, Function.update_apply]

theorem working_input (xs : List Bool) :
    working (fun _ : Bool => []) false true xs [] () none =
      ioStore false ((), none) xs := by
  apply Store.ext
  · rfl
  · funext k
    cases k <;> rfl

theorem working_output (xs : List Bool) :
    working (fun _ : Bool => []) false true [] xs () none =
      ioStore true ((), none) xs := by
  apply Store.ext
  · rfl
  · funext k
    cases k <;> rfl

end Lax979537Proofs.StackTransfer

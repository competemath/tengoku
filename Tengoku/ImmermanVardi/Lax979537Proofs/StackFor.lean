import Tengoku.ImmermanVardi.Lax979537Proofs.StackClear
import Tengoku.ImmermanVardi.Lax979537Proofs.StackCopy

namespace Lax979537Proofs.StackFor

open StackProgram StackTransfer

variable {K Aux α : Type} [DecidableEq K]

def pack (base : α → BitStore K Aux) (counter coord : K) (a : α)
    (i remaining : Nat) (scratch : Option Bool) : BitStore K Aux :=
  working (base a).stk counter coord (List.replicate remaining true) (List.replicate i true)
    (base a).state.1 scratch

def increment (coord : K) : BitProgram K Aux := .atom (.push coord (fun _ => true))

def loopBody (counter coord : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq body (.seq (increment coord) (read counter))

def loop (counter coord : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (loopBody counter coord body)

def forCount (counter coord : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (read counter) (loop counter coord body)

/-- A fixed structured program; the range bound is read from the domain
stack, never captured as an input-dependent program constant. -/
def forValues (domain counter coord tmp : K) (body : BitProgram K Aux) : BitProgram K Aux :=
  .seq (StackCopy.copy domain counter tmp)
    (.seq (forCount counter coord body) (StackClear.clear coord))

def foldRange (f : Nat → α → α) (start : Nat) : Nat → α → α
  | 0, a => a
  | n + 1, a => foldRange f (start + 1) n (f start a)

theorem pop_pack (base : α → BitStore K Aux) (counter coord : K) (hne : counter ≠ coord)
    (a : α) (i remaining : Nat) (scratch : Option Bool) :
    Op.apply (.pop counter (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (pack base counter coord a i remaining scratch) =
      pack base counter coord a i (remaining - 1) (if remaining = 0 then none else some true) := by
  have h := pop_working (base a).stk counter coord hne (List.replicate remaining true)
    (List.replicate i true) (base a).state.1 scratch
  cases remaining <;> simpa [pack, List.replicate_succ] using h

theorem increment_pack (base : α → BitStore K Aux) (counter coord : K)
    (a : α) (i remaining : Nat) (scratch : Option Bool) :
    Op.apply (.push coord (fun _ : Aux × Option Bool => true))
      (pack base counter coord a i remaining scratch) =
      pack base counter coord a (i + 1) remaining scratch := by
  apply Store.ext
  · rfl
  · funext key
    by_cases hk : key = coord <;> simp_all [pack, working, Op.apply, List.replicate_succ]

def reset (s : BitStore K Aux) : BitStore K Aux := ⟨(s.state.1, none), s.stk⟩

theorem foldRange_eq_foldl (f : Nat → α → α) (start count : Nat) (a : α) :
    foldRange f start count a = (List.range' start count).foldl (fun a i => f i a) a := by
  induction count generalizing start a with
  | zero => rfl
  | succ count ih => rw [foldRange, List.range'_succ, List.foldl_cons, ih]

theorem foldRange_zero_eq (f : Nat → α → α) (n : Nat) (a : α) :
    foldRange f 0 n a = (List.range n).foldl (fun a i => f i a) a := by
  rw [foldRange_eq_foldl, List.range_eq_range']

end Lax979537Proofs.StackFor

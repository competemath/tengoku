import Tengoku.ImmermanVardi.Lax979537Proofs.StackTransfer

namespace Lax979537Proofs.StackCopy

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def working3 (base : K → List Bool) (src left right : K)
    (xs ys zs : List Bool) (a : Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(a, scratch), Function.update (Function.update (Function.update base src xs) left ys)
    right zs⟩

def forkBody (src left right : K) : BitProgram K Aux :=
  .seq (.atom (.push left (fun s => s.2.getD false)))
    (.seq (.atom (.push right (fun s => s.2.getD false))) (read src))

def forkLoop (src left right : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (forkBody src left right)

/-- Consume a string, pushing its reverse onto each of two target stacks. -/
def fork (src left right : K) : BitProgram K Aux :=
  .seq (read src) (forkLoop src left right)

/--
@isnad1 id=eq.2h11v.s6.3ec8d68c1a11 from=translated src=- shape=b2a17556 vocab=a655e069
-/
theorem pop_working3 (base : K → List Bool) (src left right : K)
    (hl : src ≠ left) (hr : src ≠ right) (xs ys zs : List Bool)
    (a : Aux) (scratch : Option Bool) :
    Op.apply (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working3 base src left right xs ys zs a scratch) =
      working3 base src left right xs.tail ys zs a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working3, hl, hr]
  · funext k
    by_cases hs : k = src <;> by_cases hl : k = left <;> by_cases hr : k = right <;>
      simp_all [Op.apply, working3]

/--
@isnad1 id=eq.1h11v.s6.005c074a8b17 from=translated src=- shape=78b71757 vocab=8475e214
-/
theorem push_left (base : K → List Bool) (src left right : K)
    (h : left ≠ right) (xs ys zs : List Bool) (a : Aux) (b : Bool) :
    Op.apply (.push left (fun s : Aux × Option Bool => s.2.getD false))
      (working3 base src left right xs ys zs a (some b)) =
      working3 base src left right xs (b :: ys) zs a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hl : k = left <;> by_cases hr : k = right <;>
      simp_all [Op.apply, working3]

/--
@isnad1 id=eq.0h11v.s6.609578f504fa from=translated src=- shape=c732799c vocab=8475e214
-/
theorem push_right (base : K → List Bool) (src left right : K)
    (xs ys zs : List Bool) (a : Aux) (b : Bool) :
    Op.apply (.push right (fun s : Aux × Option Bool => s.2.getD false))
      (working3 base src left right xs ys zs a (some b)) =
      working3 base src left right xs ys (b :: zs) a (some b) := by
  apply Store.ext
  · rfl
  · funext k
    by_cases hr : k = right <;> simp_all [Op.apply, working3, Function.update_apply]

/-- Copy onto a target stack using an initially empty temporary stack.
The source string is restored in its original order. -/
def copy (src dst tmp : K) : BitProgram K Aux :=
  .seq (transfer src tmp) (fork tmp src dst)

end Lax979537Proofs.StackCopy

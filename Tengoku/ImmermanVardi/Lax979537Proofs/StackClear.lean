import Tengoku.ImmermanVardi.Lax979537Proofs.StackTransfer

namespace Lax979537Proofs.StackClear

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def clearLoop (src : K) : BitProgram K Aux :=
  .loop (fun s => s.2.isSome) (read src)

def clear (src : K) : BitProgram K Aux := .seq (read src) (clearLoop src)

def working (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(a, scratch), Function.update base src xs⟩

theorem pop_working (base : K → List Bool) (src : K) (xs : List Bool)
    (a : Aux) (scratch : Option Bool) :
    Op.apply (.pop src (fun s : Aux × Option Bool => fun b => (s.1, b)))
      (working base src xs a scratch) = working base src xs.tail a xs.head? := by
  apply Store.ext
  · simp [Op.apply, working]
  · funext k
    by_cases hk : k = src <;> simp_all [Op.apply, working]

end Lax979537Proofs.StackClear

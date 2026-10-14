/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Syntax.Formula
public import Tengoku

/-! # Coding -/

@[expose] public section

namespace LO
namespace FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)]

variable {ξ : Type*} [Encodable ξ]

open Encodable

namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
def toNat {n : ℕ} : Semiterm L ξ n → ℕ
  | #z                        => Nat.pair 0 z + 1
  | &x                        => Nat.pair 1 (encode x) + 1
  | func (arity := arity) f v =>
    (Nat.pair 2 <| Nat.pair arity <| Nat.pair (encode f) <| Matrix.vecToNat fun i ↦ toNat (v i)) + 1

def ofNat (n : ℕ) : ℕ → Option (Semiterm L ξ n)
  | 0 => none
  | e + 1 =>
    match e.unpair.1 with
    | 0 => if h : e.unpair.2 < n then some #⟨e.unpair.2, h⟩ else none
    | 1 => (decode e.unpair.2).map (&·)
    | 2 =>
      let arity := e.unpair.2.unpair.1
      let ef := e.unpair.2.unpair.2.unpair.1
      let ev := e.unpair.2.unpair.2.unpair.2
      match hv : ev.natToVec arity with
      | some v' =>
        (decode ef).bind fun f : L.Func arity ↦
        (Matrix.getM fun i ↦
          have : v' i < e + 1 :=
            Nat.lt_succ_iff.mpr
              <| le_trans (le_of_lt <| Nat.lt_of_eq_natToVec hv i)
              <| le_trans (Nat.unpair_right_le _)
              <| le_trans (Nat.unpair_right_le _)
              <| Nat.unpair_right_le _
          ofNat n (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦
        func f v
      | none => none
    | _ => none

/--
@isnad1 id=eq.0h4v.s5.7e1add67e86b from=translated src=- shape=cdd2cdbc vocab=b68c56ad
-/
lemma ofNat_toNat {n : ℕ} : ∀ t : Semiterm L ξ n, ofNat n (toNat t) = some t
  | #z => by simp [toNat, ofNat]
  | &x => by simp [toNat, ofNat]
  | func f v => by
      simp only [toNat, ofNat, Nat.unpair_pair]
      rw [Nat.unpair_pair, Nat.unpair_pair, Nat.unpair_pair, Nat.natToVec_vecToNat]
      simp only [encodek, Option.bind_some, Option.map_eq_some_iff, func.injEq, heq_eq_eq,
        true_and, exists_eq_right]
      have : (fun i ↦ ofNat n (toNat (v i))) = (fun i ↦ pure (v i)) :=
        funext <| fun i ↦ ofNat_toNat (v i)
      simp_all

instance encodable : Encodable (Semiterm L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat

end Semiterm

namespace Semiformula

variable [(k : ℕ) → Encodable (L.Rel k)]

/-- Imported declaration from the Incompleteness formalization. -/
def toNat : {n : ℕ} → Semiformula L ξ n → ℕ
  | _, rel (arity := arity) R v  =>
    (Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | _, nrel (arity := arity) R v =>
    (Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | _, ⊤                         => (Nat.pair 2 0) + 1
  | _, ⊥                         => (Nat.pair 3 0) + 1
  | _, φ ⋏ ψ                     => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1
  | _, φ ⋎ ψ                     => (Nat.pair 5 <| φ.toNat.pair ψ.toNat) + 1
  | _, ∀' φ                      => (Nat.pair 6 <| φ.toNat) + 1
  | _, ∃' φ                      => (Nat.pair 7 <| φ.toNat) + 1

end Semiformula

end FirstOrder
end LO

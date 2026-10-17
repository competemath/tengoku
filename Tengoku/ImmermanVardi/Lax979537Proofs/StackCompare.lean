import Tengoku.ImmermanVardi.Lax979537Proofs.StackClear

namespace Lax979537Proofs.StackCompare

open StackProgram StackTransfer

variable {K Aux : Type} [DecidableEq K]

def readPair (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (.atom (.pop left (fun s b => ((s.1.1, b.isSome), s.2)))) (read right)

def scanLoop (left right : K) : BitProgram K (Aux × Bool) :=
  .loop (fun s => s.1.2 && s.2.isSome) (readPair left right)

def scan (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (readPair left right) (scanLoop left right)

def less (left right : K) : BitProgram K (Aux × Bool) :=
  .seq (scan left right)
    (.seq (.atom (.load (fun s => ((s.1.1, !s.1.2 && s.2.isSome), none))))
      (.seq (StackClear.clear left) (StackClear.clear right)))

structure Residue where
  left : List Bool
  right : List Bool
  leftPresent : Bool
  rightHead : Option Bool

def residue : List Bool → List Bool → Residue
  | [], ys => ⟨[], ys.tail, false, ys.head?⟩
  | xs, [] => ⟨xs.tail, [], xs.head?.isSome, none⟩
  | _ :: xs, _ :: ys => residue xs ys

/--
@isnad1 id=eq.0h2v.s5.29474bb25931 from=translated src=- shape=465e6643 vocab=1ea723e4
-/
theorem residue_less (xs ys : List Bool) :
    (!(residue xs ys).leftPresent && (residue xs ys).rightHead.isSome) =
      decide (xs.length < ys.length) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [residue]
  | cons b bs ih => cases ys <;> simp [residue, ih]

/--
@isnad1 id=le.0h2v.s5.9a50d9b772f4 from=translated src=- shape=af1ce76c vocab=b0e01234
-/
theorem residue_size (xs ys : List Bool) :
    (residue xs ys).left.length + (residue xs ys).right.length ≤ xs.length + ys.length := by
  induction xs generalizing ys with
  | nil => simp [residue, List.length_tail]
  | cons b bs ih =>
      cases ys with
      | nil => simp [residue]
      | cons c cs => have h := ih cs; simp only [residue, List.length_cons]; omega

/--
@isnad1 id=executes.1h10v.s6.ab49d880031f from=translated src=- shape=8eb94421 vocab=5d8fe2dc
-/
theorem readPair_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) (flag : Bool) (scratch : Option Bool) :
    Executes (readPair left right) (working base left right xs ys (a, flag) scratch)
      (working base left right xs.tail ys.tail (a, xs.head?.isSome) ys.head?) 2 := by
  have hp := Executes.atom
    (.pop left (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.isSome), s.2)))
    (working base left right xs ys (a, flag) scratch)
  have he : Op.apply
      (.pop left (fun s : (Aux × Bool) × Option Bool => fun b => ((s.1.1, b.isSome), s.2)))
      (working base left right xs ys (a, flag) scratch) =
      working base left right xs.tail ys (a, xs.head?.isSome) scratch := by
    apply Store.ext
    · simp [Op.apply, working, hne]
    · funext k
      by_cases hl : k = left <;> by_cases hr : k = right <;> simp_all [Op.apply, working]
  rw [he] at hp
  have hq := Executes.atom
    (.pop right (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
    (working base left right xs.tail ys (a, xs.head?.isSome) scratch)
  have he' : Op.apply
      (.pop right (fun s : (Aux × Bool) × Option Bool => fun b => (s.1, b)))
      (working base left right xs.tail ys (a, xs.head?.isSome) scratch) =
      working base left right xs.tail ys.tail (a, xs.head?.isSome) ys.head? := by
    apply Store.ext
    · simp [Op.apply, working]
    · funext k
      by_cases hr : k = right <;> simp_all [Op.apply, working, Function.update_apply]
  rw [he'] at hq
  exact Executes.seq hp hq

/--
@isnad1 id=ex.1h8v.s7.79d6aca4e81d from=translated src=- shape=3e3118e2 vocab=03e4f45f
-/
theorem scanLoop_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) :
    ∃ c, c ≤ 3 * (xs.length + ys.length) + 1 ∧
      Executes (scanLoop left right)
        (working base left right xs.tail ys.tail (a, xs.head?.isSome) ys.head?)
        (working base left right (residue xs ys).left (residue xs ys).right
          (a, (residue xs ys).leftPresent) (residue xs ys).rightHead) c := by
  induction xs generalizing ys with
  | nil => exact ⟨1, by omega, Executes.loop_false rfl⟩
  | cons b bs ih =>
      cases ys with
      | nil => exact ⟨1, by omega, Executes.loop_false rfl⟩
      | cons d ds =>
          obtain ⟨c, hc, hh⟩ := ih ds
          refine ⟨2 + c + 1, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · exact Executes.loop_true rfl
              (readPair_executes base left right hne bs ds a true (some d)) hh

/--
@isnad1 id=ex.1h10v.s7.a67448ac008f from=translated src=- shape=1d581eac vocab=af564a2e
-/
theorem scan_executes (base : K → List Bool) (left right : K) (hne : left ≠ right)
    (xs ys : List Bool) (a : Aux) (flag : Bool) (scratch : Option Bool) :
    ∃ c, c ≤ 3 * (xs.length + ys.length) + 3 ∧
      Executes (scan left right) (working base left right xs ys (a, flag) scratch)
        (working base left right (residue xs ys).left (residue xs ys).right
          (a, (residue xs ys).leftPresent) (residue xs ys).rightHead) c := by
  obtain ⟨c, hc, hh⟩ := scanLoop_executes base left right hne xs ys a
  exact ⟨2 + c, by omega,
    Executes.seq (readPair_executes base left right hne xs ys a flag scratch) hh⟩

end Lax979537Proofs.StackCompare

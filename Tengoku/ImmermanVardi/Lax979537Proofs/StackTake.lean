import Tengoku.ImmermanVardi.Lax979537Proofs.StackRepeat

namespace Lax979537Proofs.StackTake

open StackProgram StackTransfer StackRepeat StackCopy

variable {K Aux : Type} [DecidableEq K]

/-- Fixed-length prefix, padding exhaustion with false. Padding keeps the
machine total; a separate sticky validity bit records insufficient input. -/
def paddedPrefix : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, xs => xs.head?.getD false :: paddedPrefix n xs.tail

/--
@isnad1 id=eq.0h2v.s3.c592b74657e7 from=translated src=- shape=ef227002 vocab=54ab5aed
-/
@[simp] theorem prefix_length (n : Nat) (xs : List Bool) : (paddedPrefix n xs).length = n := by
  induction n generalizing xs <;> simp [paddedPrefix, *]

/--
@isnad1 id=eq.1h2v.s4.ee70709faf8e from=translated src=- shape=849e526b vocab=abdc25e2
-/
theorem prefix_eq_take (n : Nat) (xs : List Bool) (h : n ≤ xs.length) :
    paddedPrefix n xs = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons b bs => simp only [paddedPrefix, List.head?_cons, Option.getD_some,
          List.tail_cons, List.take_succ_cons]; rw [ih bs (by simpa using h)]

def body (src dst : K) : BitProgram K (Aux × Bool) :=
  .seq (.atom (.pop src (fun s b => ((s.1.1, s.1.2 && b.isSome), b))))
    (.atom (.push dst (fun s => s.2.getD false)))

def bodyStore (src dst : K) (s : BitStore K (Aux × Bool)) : BitStore K (Aux × Bool) :=
  Op.apply (.push dst (fun s => s.2.getD false))
    (Op.apply (.pop src (fun s b => ((s.1.1, s.1.2 && b.isSome), b))) s)

/-- Extract a counted prefix in reverse order. The caller can transfer it
once more to put a dense relation table into canonical order. -/
def takeBits (counter src dst : K) : BitProgram K (Aux × Bool) :=
  repeatCount counter (body src dst)

/--
@isnad1 id=executes.0h5v.s5.c51996a95ca6 from=translated src=- shape=61a12cb3 vocab=6c2036c3
-/
theorem body_executes (src dst : K) (s : BitStore K (Aux × Bool)) :
    Executes (body src dst) s (bodyStore src dst s) 2 :=
  Executes.seq (Executes.atom _ _) (Executes.atom _ _)

/--
@isnad1 id=eq.1h12v.s6.9d135a75fc01 from=translated src=- shape=d6088607 vocab=bd482f19
-/
theorem body_working (base : K → List Bool) (counter src dst : K) (hsd : src ≠ dst)
    (xs ys zs : List Bool) (a : Aux) (valid : Bool) (scratch : Option Bool) :
    bodyStore src dst (working3 base counter src dst xs ys zs (a, valid) scratch) =
      working3 base counter src dst xs ys.tail (ys.head?.getD false :: zs)
        (a, valid && ys.head?.isSome) ys.head? := by
  apply Store.ext
  · simp [bodyStore, Op.apply, working3, hsd]
  · funext k
    by_cases hs : k = src <;> by_cases hd : k = dst <;>
      simp_all [bodyStore, Op.apply, working3]

end Lax979537Proofs.StackTake

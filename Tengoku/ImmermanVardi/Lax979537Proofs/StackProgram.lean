import Tengoku
import Lean.Elab.Tactic.Omega

/-!
Structured programs over the very same stacks and finite control as TM2.
The compiler uses a finite label type obtained from the syntax tree. Loops
jump back to their header; they do not allocate a runtime continuation stack.
The correctness theorem transfers a terminating structured execution to
actual TM2 steps, with no assumption of a compiler or composition theorem.
-/

namespace Lax979537Proofs.StackProgram

open Turing

variable {K : Type} (Γ : K → Type) (σ : Type)

structure Store where
  state : σ
  stk : (k : K) → List (Γ k)

/--
@isnad1 id=eq.2h5v.s5.2a835a9c3b83 from=translated src=- shape=4fead3cd vocab=550144ab
-/
theorem Store.ext {s t : Store Γ σ} (hs : s.state = t.state) (hk : s.stk = t.stk) :
    s = t := by
  cases s
  cases t
  cases hs
  cases hk
  rfl

inductive Op
  | push (k : K) (f : σ → Γ k)
  | pop (k : K) (f : σ → Option (Γ k) → σ)
  | peek (k : K) (f : σ → Option (Γ k) → σ)
  | load (f : σ → σ)

inductive Program
  | atom (o : Op Γ σ)
  | seq (p q : Program)
  | branch (b : σ → Bool) (p q : Program)
  | loop (b : σ → Bool) (p : Program)

variable {Γ σ}

def Op.apply [DecidableEq K] (o : Op Γ σ) (s : Store Γ σ) : Store Γ σ :=
  match o with
  | .push k f => ⟨s.state, Function.update s.stk k (f s.state :: s.stk k)⟩
  | .pop k f => ⟨f s.state (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
  | .peek k f => ⟨f s.state (s.stk k).head?, s.stk⟩
  | .load f => ⟨f s.state, s.stk⟩

def Labels : Program Γ σ → Type
  | .atom _ => Unit
  | .seq p q => Labels p ⊕ Labels q
  | .branch _ p q => Unit ⊕ (Labels p ⊕ Labels q)
  | .loop _ p => Unit ⊕ Labels p

instance labelsFintype (p : Program Γ σ) : Fintype (Labels p) :=
  match p with
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .seq p q => by
      letI := labelsFintype p
      letI := labelsFintype q
      exact inferInstanceAs (Fintype (Labels p ⊕ Labels q))
  | .branch _ p q => by
      letI := labelsFintype p
      letI := labelsFintype q
      exact inferInstanceAs (Fintype (Unit ⊕ (Labels p ⊕ Labels q)))
  | .loop _ p => by
      letI := labelsFintype p
      exact inferInstanceAs (Fintype (Unit ⊕ Labels p))

def entry : (p : Program Γ σ) → Labels p
  | .atom _ => ()
  | .seq p _ => .inl (entry p)
  | .branch _ _ _ | .loop _ _ => .inl ()

def jump {Λ : Type} (next : Option Λ) : TM2.Stmt Γ Λ σ :=
  match next with
  | none => .halt
  | some l => .goto (fun _ => l)

def Op.compile {Λ : Type} (o : Op Γ σ) (next : Option Λ) : TM2.Stmt Γ Λ σ :=
  match o with
  | .push k f => .push k f (jump next)
  | .pop k f => .pop k f (jump next)
  | .peek k f => .peek k f (jump next)
  | .load f => .load f (jump next)

def compile {Λ : Type} (p : Program Γ σ) (embed : Labels p → Λ)
    (next : Option Λ) : Labels p → TM2.Stmt Γ Λ σ :=
  match p with
  | .atom o => fun _ => o.compile next
  | .seq p q => Sum.elim
      (compile p (embed ∘ Sum.inl) (some (embed (.inr (entry q)))))
      (compile q (embed ∘ Sum.inr) next)
  | .branch b p q => Sum.elim
      (fun _ => .branch b (jump (some (embed (.inr (.inl (entry p))))))
        (jump (some (embed (.inr (.inr (entry q)))))))
      (Sum.elim (compile p (embed ∘ Sum.inr ∘ Sum.inl) next)
        (compile q (embed ∘ Sum.inr ∘ Sum.inr) next))
  | .loop b p => Sum.elim
      (fun _ => .branch b (jump (some (embed (.inr (entry p))))) (jump next))
      (compile p (embed ∘ Sum.inr) (some (embed (.inl ()))))

inductive Executes [DecidableEq K] :
    Program Γ σ → Store Γ σ → Store Γ σ → Nat → Prop
  | atom (o : Op Γ σ) (s : Store Γ σ) : Executes (.atom o) s (o.apply s) 1
  | seq {p q s u t a b} : Executes p s u a → Executes q u t b →
      Executes (.seq p q) s t (a + b)
  | branch_true {p q s t a} {b : σ → Bool} : b s.state = true →
      Executes p s t a → Executes (.branch b p q) s t (a + 1)
  | branch_false {p q s t a} {b : σ → Bool} : b s.state = false →
      Executes q s t a → Executes (.branch b p q) s t (a + 1)
  | loop_false {p s} {b : σ → Bool} : b s.state = false →
      Executes (.loop b p) s s 1
  | loop_true {p s u t a c} {b : σ → Bool} : b s.state = true →
      Executes p s u a → Executes (.loop b p) u t c →
      Executes (.loop b p) s t (a + c + 1)

def config {Λ : Type} (l : Option Λ) (s : Store Γ σ) : TM2.Cfg Γ Λ σ :=
  ⟨l, s.state, s.stk⟩

def Runs [DecidableEq K] {Λ : Type} (code : Λ → TM2.Stmt Γ Λ σ)
    (l : Option Λ) (s : Store Γ σ) (l' : Option Λ) (s' : Store Γ σ) (t : Nat) : Prop :=
  (fun c => c.bind (TM2.step code))^[t] (some (config l s)) = some (config l' s')

/--
@isnad1 id=runs.1h9v.s6.b29c160e7dc7 from=translated src=- shape=bc65fa6c vocab=c212776c
-/
theorem runs_one [DecidableEq K] {Λ : Type} (code : Λ → TM2.Stmt Γ Λ σ)
    (l : Λ) (s : Store Γ σ) (l' : Option Λ) (s' : Store Γ σ)
    (h : TM2.stepAux (code l) s.state s.stk = config l' s') :
    Runs code (some l) s l' s' 1 := by
  simpa only [Runs, Function.iterate_one, Option.bind_some, config, TM2.step] using
    congrArg some h

/--
@isnad1 id=runs.2h13v.s6.2b1a4c27d803 from=translated src=- shape=ec0f3b91 vocab=a55ba396
-/
theorem runs_trans [DecidableEq K] {Λ : Type} {code : Λ → TM2.Stmt Γ Λ σ}
    {l m n : Option Λ} {s u t : Store Γ σ} {a b : Nat}
    (h : Runs code l s m u a) (h' : Runs code m u n t b) :
    Runs code l s n t (a + b) := by
  unfold Runs at *
  rw [Nat.add_comm a b, Function.iterate_add_apply, h, h']

/--
@isnad1 id=eq.0h6v.s5.899afaa83f64 from=translated src=- shape=660f409b vocab=2326bc82
-/
theorem stepAux_jump [DecidableEq K] {Λ : Type} (next : Option Λ)
    (s : Store Γ σ) : TM2.stepAux (jump next) s.state s.stk = config next s := by
  cases next <;> rfl

/--
@isnad1 id=eq.0h7v.s6.c140402b2853 from=translated src=- shape=64c233ec vocab=82f100c4
-/
theorem stepAux_op [DecidableEq K] {Λ : Type} (o : Op Γ σ) (next : Option Λ)
    (s : Store Γ σ) :
    TM2.stepAux (o.compile next) s.state s.stk = config next (o.apply s) := by
  cases o <;> cases next <;> rfl

/-- The actual finite machine obtained by compiling a structured program. -/
def machine [DecidableEq K] [Fintype K] [Fintype σ]
    (p : Program Γ σ) (input output : K) [Fintype (Γ input)] (initial : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Λ := Labels p
  main := entry p
  σ := σ
  initialState := initial
  m := compile p id none

def ioStore [DecidableEq K] (port : K) (initial : σ) (w : List (Γ port)) :
    Store Γ σ where
  state := initial
  stk k := if h : k = port then (by rw [h]; exact w) else []

end Lax979537Proofs.StackProgram

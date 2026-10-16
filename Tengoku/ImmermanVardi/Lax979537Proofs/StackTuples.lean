import Tengoku.ImmermanVardi.Lax979537Proofs.StackFor
import Tengoku

namespace Lax979537Proofs.StackTuples

open StackProgram StackTransfer StackFor

variable {K Aux α : Type} [DecidableEq K]

def ports (slots : List (K × K)) : List K := slots.flatMap (fun p => [p.1, p.2])

def withScratch (s : BitStore K Aux) (scratch : Option Bool) : BitStore K Aux :=
  ⟨(s.state.1, scratch), s.stk⟩

/-- Install a tuple of unary coordinates and the loop counters surrounding
the callback. This definition follows the nesting order of the program. -/
def packTuple (base : α → BitStore K Aux) : List (K × K) → α →
    List Nat → List Nat → Option Bool → BitStore K Aux
  | [], a, _, _, scratch => withScratch (base a) scratch
  | (c, x) :: slots, a, values, remaining, scratch =>
      packTuple (fun a => pack base c x a (values.headD 0) (remaining.headD 0) scratch)
        slots a values.tail remaining.tail scratch

def clearScratch : BitProgram K Aux := .atom (.load (fun s => (s.1, none)))

/-- The number of nesting levels is fixed by the arity. No domain size is
captured in a control operation or in the program syntax. -/
def forTuples (domain tmp : K) (body : BitProgram K Aux) : List (K × K) → BitProgram K Aux
  | [] => .seq body clearScratch
  | (c, x) :: slots => forValues domain c x tmp (forTuples domain tmp body slots)

def tuples (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap (fun i => (tuples n k).map (i :: ·))

def foldTuples (n : Nat) : Nat → (List Nat → α → α) → α → α
  | 0, f, a => f [] a
  | k + 1, f, a => foldRange (fun i a => foldTuples n k (fun xs => f (i :: xs)) a) 0 n a

def cost (n B : Nat) : Nat → Nat
  | 0 => B + 1
  | k + 1 => (cost n B k + 12) * n + 8

noncomputable def costPolynomial (B : Polynomial Nat) : Nat → Polynomial Nat
  | 0 => B + 1
  | k + 1 => (costPolynomial B k + 12) * Polynomial.X + 8

theorem eval_costPolynomial (B : Polynomial Nat) (n k : Nat) :
    (costPolynomial B k).eval n = cost n (B.eval n) k := by
  induction k with
  | zero => simp [costPolynomial, cost]
  | succ k ih => simp [costPolynomial, cost, ih]

theorem pack_fresh (base : α → BitStore K Aux) (c x key : K)
    (hc : key ≠ c) (hx : key ≠ x) (a : α) (i remaining : Nat) (scratch : Option Bool) :
    (pack base c x a i remaining scratch).stk key = (base a).stk key := by
  simp [pack, working, hc, hx]

theorem packTuple_pack_scratch (base : α → BitStore K Aux) (counter coord : K)
    (i remaining : Nat) (initial : Option Bool) (slots : List (K × K))
    (a : α) (values counters : List Nat) (scratch : Option Bool) :
    packTuple (fun a => pack base counter coord a i remaining initial) slots a values counters scratch =
      packTuple (fun a => pack base counter coord a i remaining none) slots a values counters scratch := by
  cases slots <;> rfl

theorem foldTuples_eq_foldl (n k : Nat) (f : List Nat → α → α) (a : α) :
    foldTuples n k f a = (tuples n k).foldl (fun a xs => f xs a) a := by
  induction k generalizing f a with
  | zero => rfl
  | succ k ih =>
      simp only [foldTuples, foldRange_zero_eq, tuples, List.foldl_flatMap, List.foldl_map]
      congr 1
      funext a i
      exact ih (fun xs => f (i :: xs)) a

def tupleValues {n k : Nat} (v : Fin k → Fin n) : List Nat := List.ofFn (fun i => (v i).val)

theorem tupleValues_cons {n k : Nat} (i : Fin n) (v : Fin k → Fin n) :
    tupleValues (Fin.cons i v) = i.val :: tupleValues v := by
  simp [tupleValues, List.ofFn_succ]

theorem packTuple_const (s : BitStore K Aux) (slots : List (K × K))
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    packTuple (fun _ : α => s) slots a values remaining scratch =
      packTuple (fun _ : Unit => s) slots () values remaining scratch := by
  induction slots generalizing s values remaining with
  | nil => rfl
  | cons slot slots ih => exact ih _ _ _

theorem packTuple_state (base : α → BitStore K Aux) (slots : List (K × K))
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    (packTuple base slots a values remaining scratch).state = ((base a).state.1, scratch) := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih => exact ih _ _ _

theorem packTuple_stk_scratch (base : α → BitStore K Aux) (slots : List (K × K))
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    (packTuple base slots a values remaining scratch).stk =
      (packTuple base slots a values remaining none).stk := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih =>
      rw [packTuple, ih, packTuple_pack_scratch]
      rfl

theorem packTuple_fresh (base : α → BitStore K Aux) (slots : List (K × K))
    (key : K) (hfresh : key ∉ ports slots) (a : α) (values remaining : List Nat)
    (scratch : Option Bool) :
    (packTuple base slots a values remaining scratch).stk key = (base a).stk key := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih =>
      rcases slot with ⟨counter, coord⟩
      have h : key ≠ counter ∧ key ≠ coord ∧ key ∉ ports slots := by simpa [ports] using hfresh
      rw [packTuple, ih _ h.2.2, pack_fresh base counter coord key h.1 h.2.1]

def setStack (s : BitStore K Aux) (key : K) (bits : List Bool) : BitStore K Aux :=
  ⟨s.state, Function.update s.stk key bits⟩

theorem pack_setStack (base : α → BitStore K Aux) (counter coord key : K)
    (hcounter : key ≠ counter) (hcoord : key ≠ coord) (bits : α → List Bool)
    (a : α) (i remaining : Nat) (scratch : Option Bool) :
    pack (fun a => setStack (base a) key (bits a)) counter coord a i remaining scratch =
      setStack (pack base counter coord a i remaining scratch) key (bits a) := by
  apply Store.ext
  · rfl
  · funext j
    by_cases hj : j = key <;> simp_all [pack, working, setStack, Function.update_apply]

theorem packTuple_setStack (base : α → BitStore K Aux) (slots : List (K × K))
    (key : K) (hfresh : key ∉ ports slots) (bits : α → List Bool)
    (a : α) (values remaining : List Nat) (scratch : Option Bool) :
    packTuple (fun a => setStack (base a) key (bits a)) slots a values remaining scratch =
      setStack (packTuple base slots a values remaining scratch) key (bits a) := by
  induction slots generalizing base values remaining with
  | nil => rfl
  | cons slot slots ih =>
      rcases slot with ⟨counter, coord⟩
      have h : key ≠ counter ∧ key ≠ coord ∧ key ∉ ports slots := by simpa [ports] using hfresh
      simp only [packTuple, pack_setStack base counter coord key h.1 h.2.1]
      exact ih _ h.2.2 _ _

end Lax979537Proofs.StackTuples

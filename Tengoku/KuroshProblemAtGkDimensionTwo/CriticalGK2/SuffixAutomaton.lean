import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.WordSingleCoefficient
import Tengoku.Seed.Data.Fintype.Vector
import Tengoku.Seed.Data.Fintype.Sigma
import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Algebra.Polynomial.Coeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual finite suffix-trie automaton

A state consists of a destination head and a residual word of length less
than d.  At a head, the first letter chooses a complete generic monomial and
pays its coefficient times the power-counting variable.  Internal states
consume their residual word deterministically and then return to their
destination head.  Shared suffixes identify internal vertices; this changes
the number of states but preserves the actual weighted head paths.
-/

namespace CriticalGK2.Automaton

noncomputable section

abbrev Residual (d : ℕ) := {p : List Bool // p.length < d}

def residualEquivVectors (d : ℕ) :
    Residual d ≃ (Σ n : Fin d, List.Vector Bool n.val) where
  toFun p := ⟨⟨p.val.length, p.property⟩, ⟨p.val, rfl⟩⟩
  invFun v := ⟨v.2.val, by simpa only [v.2.property] using v.1.isLt⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv v := by
    rcases v with ⟨⟨n, hn⟩, ⟨p, hp⟩⟩
    dsimp at hp
    subst n
    rfl

instance residualFintype (d : ℕ) : Fintype (Residual d) :=
  Fintype.ofEquiv (Σ n : Fin d, List.Vector Bool n.val) (residualEquivVectors d).symm

def emptyResidual (d : ℕ) (hd : 0 < d) : Residual d := ⟨[], hd⟩

def tailResidual {d : ℕ} (p : Residual d) : Residual d :=
  ⟨p.val.tail, by
    have hle : p.val.tail.length ≤ p.val.length := by
      cases p.val <;> simp
    exact lt_of_le_of_lt hle p.property⟩

abbrev State (r d : ℕ) := Fin r × Residual d

def headState {r : ℕ} (d : ℕ) (hd : 0 < d) (a : Fin r) : State r d :=
  (a, emptyResidual d hd)

abbrev Coefficients (R : Type*) (r d : ℕ) :=
  Fin r → Fin r → Bool → Residual d → R

variable {R : Type*} [CommRing R] {r d : ℕ}

/-- Actual letter transition matrix over the actual polynomial coefficient
ring, with finite row and column state indices.-/
def letterTransition (c : Coefficients R r d) (α : Bool) :
    Matrix (State r d) (State r d) (Polynomial R) := fun s t =>
  if s.2.val = [] then Polynomial.monomial 1 (c s.1 t.1 α t.2)
  else if s.1 = t.1 ∧ s.2.val = α :: t.2.val then 1 else 0

/-- The actual product of the letter transition matrices in word order.-/
def wordTransition (c : Coefficients R r d) : List Bool →
    Matrix (State r d) (State r d) (Polynomial R)
  | [] => 1
  | α :: w => letterTransition c α * wordTransition c w

/--
@isnad1 id=eq.0h4v.s7.d81b5ba13616 from=translated src=- shape=4c3812f6 vocab=4149f196
-/
@[simp]
theorem wordTransition_nil (c : Coefficients R r d) : wordTransition c [] = 1 := rfl

/--
@isnad1 id=eq.0h6v.s7.1ca3e0879e45 from=translated src=- shape=c7d9fc02 vocab=cd58c3c8
-/
@[simp]
theorem wordTransition_cons (c : Coefficients R r d) (α : Bool) (w : List Bool) :
    wordTransition c (α :: w) = letterTransition c α * wordTransition c w := rfl

def headValue (c : Coefficients R r d) (hd : 0 < d)
    (w : List Bool) (a b : Fin r) : Polynomial R :=
  wordTransition c w (headState d hd a) (headState d hd b)

/--
@isnad1 id=eq.1h7v.s7.7edc4c388f95 from=translated src=- shape=9628bcf2 vocab=0698dc9f
-/
@[simp]
theorem letterTransition_head (c : Coefficients R r d) (hd : 0 < d)
    (α : Bool) (a : Fin r) (t : State r d) :
    letterTransition c α (headState d hd a) t =
      Polynomial.monomial 1 (c a t.1 α t.2) := by
  simp [letterTransition, headState, emptyResidual]

/-- Every non-head row has exactly the deterministic residual edge.
@isnad1 id=eq.1h10v.s7.0492ca44cbd8 from=translated src=- shape=7269fdc7 vocab=53684bb6
-/
theorem letterTransition_internal_row (c : Coefficients R r d)
    (α β : Bool) (a : Fin r) (p : Residual d) (q : List Bool)
    (hp : p.val = β :: q) (t : State r d) :
    letterTransition c α (a, p) t =
      if β = α then if t = (a, tailResidual p) then 1 else 0 else 0 := by
  rcases t with ⟨b, v⟩
  by_cases h : β = α
  · subst β
    simp [letterTransition, hp, tailResidual, Prod.ext_iff, Subtype.ext_iff, eq_comm]
  · simp [letterTransition, hp, h, Ne.symm h, List.cons.injEq]

/-- Matrix multiplication over the deterministic internal row consumes
one residual letter, without summing over further paths.
@isnad1 id=eq.2h11v.s7.6d9e102bc120 from=translated src=- shape=34edc573 vocab=9fb48d5c
-/
theorem wordTransition_internal_step (c : Coefficients R r d) (hd : 0 < d)
    (α β : Bool) (w : List Bool) (a b : Fin r)
    (p : Residual d) (q : List Bool) (hp : p.val = β :: q) :
    wordTransition c (α :: w) (a, p) (headState d hd b) =
      if β = α then wordTransition c w (a, tailResidual p) (headState d hd b) else 0 := by
  classical
  rw [wordTransition_cons, Matrix.mul_apply]
  simp_rw [letterTransition_internal_row c α β a p q hp]
  by_cases h : β = α <;> simp [h]

/-- Exact internal-state path identity.  An internal state must consume its
entire prescribed residual before any new generic monomial can be chosen.
@isnad1 id=eq.1h8v.s6.1cc68e21064b from=translated src=- shape=3e62e49d vocab=d8af9c4e
-/
theorem internal_state_consumption (c : Coefficients R r d) (hd : 0 < d)
    (p : Residual d) (w : List Bool) (a b : Fin r) :
    wordTransition c w (a, p) (headState d hd b) =
      afterConsume p.val w (fun t => headValue c hd t a b) := by
  induction w generalizing p with
  | nil =>
    cases hp : p.val with
    | nil =>
      have hpe : p = emptyResidual d hd := Subtype.ext hp
      subst p
      rfl
    | cons β q =>
      simp [wordTransition, Matrix.one_apply, headState, emptyResidual,
        afterConsume, consumePrefix, hp, Prod.ext_iff, Subtype.ext_iff]
  | cons α w ih =>
    cases hp : p.val with
    | nil =>
      have hpe : p = emptyResidual d hd := Subtype.ext hp
      subst p
      rfl
    | cons β q =>
      rw [wordTransition_internal_step c hd α β w a b p q hp]
      have htail : (tailResidual p).val = q := by simp [tailResidual, hp]
      by_cases h : β = α
      · subst β
        simpa [afterConsume, consumePrefix, hp, htail] using ih (tailResidual p)
      · simp [afterConsume, consumePrefix, hp, h]

/--
@isnad1 id=eq.1h6v.s6.360488cd04d0 from=translated src=- shape=d68dc06b vocab=e02f520b
-/
@[simp]
theorem headValue_nil (c : Coefficients R r d) (hd : 0 < d) (a b : Fin r) :
    headValue c hd [] a b = if a = b then 1 else 0 := by
  simp [headValue, wordTransition, Matrix.one_apply, headState]

/-- Exact head recurrence obtained from actual matrix multiplication and
the proved deterministic internal-state identity.
@isnad1 id=eq.1h8v.s8.1554811c64f7 from=translated src=- shape=61d46076 vocab=e57755ac
-/
theorem headValue_cons (c : Coefficients R r d) (hd : 0 < d)
    (α : Bool) (w : List Bool) (a b : Fin r) :
    headValue c hd (α :: w) a b =
      ∑ s : State r d, Polynomial.monomial 1 (c a s.1 α s.2) *
        afterConsume s.2.val w (fun t => headValue c hd t s.1 b) := by
  classical
  rw [headValue, wordTransition_cons, Matrix.mul_apply]
  simp_rw [letterTransition_head]
  apply Finset.sum_congr rfl
  rintro ⟨j, p⟩ _
  rw [internal_state_consumption c hd p w j b]

end

end CriticalGK2.Automaton

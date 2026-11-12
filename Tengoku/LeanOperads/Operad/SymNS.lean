/-
# The underlying non-symmetric operad of a symmetric operad

A symmetric operad `P` in the sense of `Operad.Sym` has inputs indexed by arbitrary finite types.
Restricting to the types `Fin n` and composing positionally gives a non-symmetric operad in the
convention of `Operad.Basic`,

  `comp a b x y = relabel (comp ⟨a⟩ x y)` along `insertEquiv a b n`,

where `insertEquiv a b n : Without (Fin (a+1+b)) a ⊕ Fin n ≃ Fin (a+n+b)` keeps the outer inputs
before the slot in place, puts the inserted inputs in the block `[a, a+n)`, and shifts the outer
inputs after the slot by `n - 1`. This is the forgetful functor from symmetric to non-symmetric
operads, and it is how a symmetric operad reaches the computational layer of the library.

Each non-symmetric axiom reduces, through the symmetric axiom of the same name and the
equivariance axiom, to an identity between two bijections of finite types, which is checked
pointwise by arithmetic on `Fin`. That is where all the positional bookkeeping lives, once.
-/
import Tengoku.LeanOperads.Operad.Sym
import Tengoku.LeanOperads.Operad.Constructions
import Tengoku.LeanOperads.Operad.Perm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

namespace Sym

/-! ## Positional bijections -/

/-- **The positional insertion bijection.** The inputs of `x ∘ₐ y`, for `x` with `a + 1 + b`
inputs and `y` with `n`, in their order: outer inputs before the slot, then the inserted ones, then
the outer inputs after the slot.-/
def insertEquiv (a b n : ℕ) :
    Without (Fin (a + 1 + b)) ⟨a, by omega⟩ ⊕ Fin n ≃ Fin (a + n + b) where
  toFun x :=
    match x with
    | Sum.inl k =>
        if h : (k.1 : ℕ) < a then ⟨k.1, by omega⟩
        else ⟨k.1 + n - 1, by
          have hk : (k.1 : ℕ) ≠ a := fun e => k.2 (Fin.ext e)
          have := k.1.isLt
          omega⟩
    | Sum.inr j => ⟨a + j, by have := j.isLt; omega⟩
  invFun m :=
    if h : (m : ℕ) < a then
      Sum.inl ⟨⟨m, by omega⟩, fun e => by
        have := congrArg Fin.val e; simp only at this; omega⟩
    else if h' : (m : ℕ) < a + n then Sum.inr ⟨m - a, by omega⟩
    else
      Sum.inl ⟨⟨m - n + 1, by have := m.isLt; omega⟩, fun e => by
        have := congrArg Fin.val e; simp only at this; omega⟩
  left_inv := by
    rintro (⟨⟨k, hk⟩, hne⟩ | ⟨j, hj⟩)
    · have hka : k ≠ a := fun e => hne (Fin.ext e)
      by_cases h : k < a
      · simp only [h, ↓reduceDIte]
      · have h1 : ¬ k + n - 1 < a := by omega
        have h2 : ¬ k + n - 1 < a + n := by omega
        simp only [h, h1, h2, ↓reduceDIte, Sum.inl.injEq, Subtype.mk.injEq, Fin.mk.injEq]
        omega
    · have h1 : ¬ a + j < a := by omega
      have h2 : a + j < a + n := by omega
      simp only [h1, h2, ↓reduceDIte, Sum.inr.injEq, Fin.mk.injEq]
      omega
  right_inv := by
    rintro ⟨m, hm⟩
    by_cases h : m < a
    · simp only [h, ↓reduceDIte]
    · by_cases h' : m < a + n
      · simp only [h, h', ↓reduceDIte, Fin.mk.injEq]
        omega
      · have h3 : ¬ m - n + 1 < a := by omega
        simp only [h, h', h3, ↓reduceDIte, Fin.mk.injEq]
        omega

lemma insertEquiv_inl_val (a b n : ℕ) (k : Without (Fin (a + 1 + b)) ⟨a, by omega⟩) :
    ((insertEquiv a b n (Sum.inl k) : Fin (a + n + b)) : ℕ)
      = if (k.1 : ℕ) < a then (k.1 : ℕ) else (k.1 : ℕ) + n - 1 := by
  show ((if h : (k.1 : ℕ) < a then _ else _ : Fin (a + n + b)) : ℕ) = _
  split_ifs <;> rfl

@[simp] lemma insertEquiv_inr_val (a b n : ℕ) (j : Fin n) :
    ((insertEquiv a b n (Sum.inr j) : Fin (a + n + b)) : ℕ) = a + j := rfl

end Sym

open Sym

namespace SymOperad

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-! ## Moving relabellings through a composition -/

section Moves

variable {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']

lemma comp_map_left (σ : A ≃ A') (i : A) (x : P A) (y : P B) :
    comp (R := R) (σ i) (map (R := R) σ x) y
      = map (R := R) (compEquiv σ (Equiv.refl B) i) (comp (R := R) i x y) := by
  rw [map_comp (R := R), map_refl (R := R)]

lemma comp_map_right (τ : B ≃ B') (i : A) (x : P A) (y : P B) :
    comp (R := R) i x (map (R := R) τ y)
      = map (R := R) (Equiv.sumCongr (Equiv.refl (Without A i)) τ) (comp (R := R) i x y) := by
  have h := map_comp (R := R) (P := P) (Equiv.refl A) τ i x y
  rw [map_refl (R := R)] at h
  have e : compEquiv (Equiv.refl A) τ i = Equiv.sumCongr (Equiv.refl (Without A i)) τ := by
    ext c; rcases c with a | b <;> rfl
  rw [e] at h
  exact h.symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
lemma comp_slot {i i' : A} (h : i = i') (x : P A) (y : P B) :
    comp (R := R) i' x y = map (R := R) (slotEquiv h) (comp (R := R) i x y) := by
  subst h
  have e : slotEquiv (B := B) (rfl : i = i) = Equiv.refl _ := by
    ext c; rcases c with ⟨a, ha⟩ | b <;> rfl
  rw [e, map_refl (R := R)]

end Moves

/-! ## The underlying non-symmetric operad -/

/-- **The underlying non-symmetric collection**: the components on the standard finite types.

A `def`, not an `abbrev`: for `P = Perm` the collection `n ↦ Fin n → R` is literally the
non-symmetric `Perm`, and an `abbrev` would let instance resolution pick that operad's structure
instead of this one.-/
def toNS (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) : ℕ → Type v :=
  fun n => P (Fin n)

instance (n : ℕ) : AddCommGroup (toNS P n) := inferInstanceAs (AddCommGroup (P (Fin n)))

instance (n : ℕ) : Module R (toNS P n) := inferInstanceAs (Module R (P (Fin n)))

/-- Positional composition: compose at the input `a`, then list the inputs in order.-/
def nsComp (a b : ℕ) {n : ℕ} :
    P (Fin (a + 1 + b)) →ₗ[R] P (Fin n) →ₗ[R] P (Fin (a + n + b)) :=
  (comp (R := R) (⟨a, by omega⟩ : Fin (a + 1 + b))).compr₂ (map (R := R) (insertEquiv a b n))

lemma nsComp_apply (a b : ℕ) {n : ℕ} (x : P (Fin (a + 1 + b))) (y : P (Fin n)) :
    nsComp (R := R) a b x y
      = map (R := R) (insertEquiv a b n) (comp (R := R) (⟨a, by omega⟩ : Fin (a + 1 + b)) x y) :=
  rfl

/-- The unit on the standard one-element type.-/
def nsOne : P (Fin 1) := map (R := R) unitFinOne (one R)

/-- Two relabellings of the same element agree as soon as the bijections do.-/
lemma map_eq_of_equiv_eq {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {e f : A ≃ B} (h : ∀ a, e a = f a) (x : P A) : map (R := R) e x = map (R := R) f x := by
  rw [Equiv.ext h]

end SymOperad

namespace Sym.Perm

variable (R : Type u) [CommRing R]

end Sym.Perm

end Operad

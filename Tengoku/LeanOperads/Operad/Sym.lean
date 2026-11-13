/-
# Symmetric operads, by partial composition over finite types

A symmetric operad here is a family of `R`-modules `P A` indexed by finite types, functorial in
bijections, with partial compositions

  `comp i : P A →ₗ P B →ₗ P (Without A i ⊕ B)`,        `Without A i = {a : A // a ≠ i}`,

inserting an operation with inputs `B` at the input `i` of an operation with inputs `A`, and a
unit in `P Unit`. Each axiom relates two elements living on *different* finite types, so each is
stated after relabelling along an explicit bijection: `seqEquiv` for sequential associativity,
`parEquiv` for parallel associativity, `compEquiv` for equivariance, `rightUnitEquiv` and
`leftUnitEquiv` for the units.

## Why this presentation

It is the README's species decision without the substitution product. Indexing by finite types
makes equivariance *naturality*: relabelling the two inputs relabels the composite, and the
classical `Σₙ`-equivariance axioms are the case of permutations. No block permutation is ever
constructed, and no arithmetic appears — every coherence is an identity of `Equiv`s. Partial
composition needs no partitions of the input set and no direct sum over a transported index, which
was the part of the substitution-product plan that never got finished.

The positional `NSOperad` stays the computational layer: every symmetric operad has an underlying
non-symmetric one on `Fin n`, built in `Operad.SymNS`.

## Conventions

Player-set-style conventions are fixed so that operads of functions on finite sets instantiate the
class with no translation: `Without A i` is a subtype of `A`, the composite input set is the sum
`Without A i ⊕ B` with the inserted inputs on the right, and each axiom relabels the left-hand
composite onto the right-hand one.
-/
import Tengoku.LeanOperads.Operad.Basic
import Tengoku.Seed.Data.Fintype.Sum
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

/-- The inputs of `A` other than `i`.-/
@[nolint unusedArguments]
abbrev Without (A : Type*) [DecidableEq A] (i : A) := {a : A // a ≠ i}

namespace Sym

/-! ## The five bijections

Each is the canonical identification of two composite input sets. -/

section Equivs

variable {A A' B B' D : Type} [DecidableEq A] [DecidableEq A']

/-- **Sequential associativity.** Nesting two compositions in the two possible ways:
`((A ∖ i) ⊔ B) ∖ j ⊔ D ≅ (A ∖ i) ⊔ ((B ∖ j) ⊔ D)` for `j ∈ B`.-/
def seqEquiv [DecidableEq B] (i : A) (j : B) (D : Type) :
    Without (Without A i ⊕ B) (Sum.inr j) ⊕ D ≃ Without A i ⊕ (Without B j ⊕ D) where
  toFun x :=
    match x with
    | Sum.inl ⟨Sum.inl a, _⟩ => Sum.inl a
    | Sum.inl ⟨Sum.inr b, hb⟩ => Sum.inr (Sum.inl ⟨b, fun h => hb (congrArg Sum.inr h)⟩)
    | Sum.inr d => Sum.inr (Sum.inr d)
  invFun y :=
    match y with
    | Sum.inl a => Sum.inl ⟨Sum.inl a, by simp⟩
    | Sum.inr (Sum.inl b) => Sum.inl ⟨Sum.inr b.1, by simpa using b.2⟩
    | Sum.inr (Sum.inr d) => Sum.inr d
  left_inv := by rintro (⟨(a | b), hb⟩ | d) <;> rfl
  right_inv := by rintro (a | (b | d)) <;> rfl

/--
@isnad1 id=eq.1h6v.s9.d347a126af4a from=translated src=- shape=d285fc9e vocab=2a22fb62
-/
@[simp] lemma seqEquiv_inl_inl [DecidableEq B] (i : A) (j : B) (a : Without A i) (h) :
    seqEquiv i j D (Sum.inl ⟨Sum.inl a, h⟩) = Sum.inl a := rfl

/--
@isnad1 id=eq.1h6v.s9.fbbdc66fca7d from=translated src=- shape=348e607f vocab=0ca0be6a
-/
@[simp] lemma seqEquiv_inl_inr [DecidableEq B] (i : A) (j : B) (b : B) (hb) :
    seqEquiv i j D (Sum.inl ⟨Sum.inr b, hb⟩)
      = Sum.inr (Sum.inl ⟨b, fun h => hb (congrArg Sum.inr h)⟩) := rfl

/--
@isnad1 id=eq.0h6v.s9.d4fcdb59a7e4 from=translated src=- shape=4c695672 vocab=b2dd218a
-/
@[simp] lemma seqEquiv_inr [DecidableEq B] (i : A) (j : B) (d : D) :
    seqEquiv i j D (Sum.inr d) = Sum.inr (Sum.inr d) := rfl

/--
@isnad1 id=eq.0h6v.s9.be4cb5512d45 from=translated src=- shape=b6688c90 vocab=2f0e2d33
-/
@[simp] lemma seqEquiv_symm_inl [DecidableEq B] (i : A) (j : B) (a : Without A i) :
    (seqEquiv i j D).symm (Sum.inl a) = Sum.inl ⟨Sum.inl a, by simp⟩ := rfl

/--
@isnad1 id=eq.0h6v.s9.982b22494437 from=translated src=- shape=be58ffd0 vocab=6ad28d4e
-/
@[simp] lemma seqEquiv_symm_inr_inl [DecidableEq B] (i : A) (j : B) (b : Without B j) :
    (seqEquiv i j D).symm (Sum.inr (Sum.inl b)) = Sum.inl ⟨Sum.inr b.1, by simpa using b.2⟩ :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.ea8c5687749b from=translated src=- shape=b8186910 vocab=0776b045
-/
@[simp] lemma seqEquiv_symm_inr_inr [DecidableEq B] (i : A) (j : B) (d : D) :
    (seqEquiv i j D).symm (Sum.inr (Sum.inr d)) = Sum.inr d := rfl

/-- **Parallel associativity.** Filling two distinct inputs `i ≠ k` of `A` in the two possible
orders: `((A ∖ i) ⊔ B) ∖ k ⊔ D ≅ ((A ∖ k) ⊔ D) ∖ i ⊔ B`.-/
def parEquiv {i k : A} (hik : i ≠ k) (B D : Type) [DecidableEq B] [DecidableEq D] :
    Without (Without A i ⊕ B) (Sum.inl ⟨k, Ne.symm hik⟩) ⊕ D
      ≃ Without (Without A k ⊕ D) (Sum.inl ⟨i, hik⟩) ⊕ B where
  toFun x :=
    match x with
    | Sum.inl ⟨Sum.inl a, ha⟩ =>
        Sum.inl ⟨Sum.inl ⟨a.1, fun h => ha (by simp [Subtype.ext_iff, h])⟩, by
          simp [Subtype.ext_iff, a.2]⟩
    | Sum.inl ⟨Sum.inr b, _⟩ => Sum.inr b
    | Sum.inr d => Sum.inl ⟨Sum.inr d, by simp⟩
  invFun y :=
    match y with
    | Sum.inl ⟨Sum.inl a, ha⟩ =>
        Sum.inl ⟨Sum.inl ⟨a.1, fun h => ha (by simp [Subtype.ext_iff, h])⟩, by
          simp [Subtype.ext_iff, a.2]⟩
    | Sum.inl ⟨Sum.inr d, _⟩ => Sum.inr d
    | Sum.inr b => Sum.inl ⟨Sum.inr b, by simp⟩
  left_inv := by rintro (⟨(a | b), ha⟩ | d) <;> rfl
  right_inv := by rintro (⟨(a | d), ha⟩ | b) <;> rfl

/--
@isnad1 id=eq.2h6v.s10.13009d549ad9 from=translated src=- shape=b0b724ef vocab=d0cb1912
-/
@[simp] lemma parEquiv_inl_inl [DecidableEq B] [DecidableEq D] {i k : A} (hik : i ≠ k)
    (a : Without A i) (ha : (Sum.inl a : Without A i ⊕ B) ≠ Sum.inl ⟨k, Ne.symm hik⟩) :
    parEquiv hik B D (Sum.inl ⟨Sum.inl a, ha⟩)
      = Sum.inl ⟨Sum.inl ⟨a.1, fun h => ha (by simp [Subtype.ext_iff, h])⟩, by
          simp [Subtype.ext_iff, a.2]⟩ := rfl

/--
@isnad1 id=eq.2h6v.s10.075ecca5c359 from=translated src=- shape=2ef921ec vocab=8fdc5e0a
-/
@[simp] lemma parEquiv_inl_inr [DecidableEq B] [DecidableEq D] {i k : A} (hik : i ≠ k) (b : B)
    (hb : (Sum.inr b : Without A i ⊕ B) ≠ Sum.inl ⟨k, Ne.symm hik⟩) :
    parEquiv hik B D (Sum.inl ⟨Sum.inr b, hb⟩) = Sum.inr b := rfl

/--
@isnad1 id=eq.1h6v.s10.74d9217145ff from=translated src=- shape=eb734e6b vocab=501ffc6f
-/
@[simp] lemma parEquiv_inr [DecidableEq B] [DecidableEq D] {i k : A} (hik : i ≠ k) (d : D) :
    parEquiv hik B D (Sum.inr d) = Sum.inl ⟨Sum.inr d, by simp⟩ := rfl

/--
@isnad1 id=eq.2h6v.s10.0fe02e3481b2 from=translated src=- shape=72058b48 vocab=016f2b1a
-/
@[simp] lemma parEquiv_symm_inl_inl [DecidableEq B] [DecidableEq D] {i k : A} (hik : i ≠ k)
    (a : Without A k) (ha : (Sum.inl a : Without A k ⊕ D) ≠ Sum.inl ⟨i, hik⟩) :
    (parEquiv hik B D).symm (Sum.inl ⟨Sum.inl a, ha⟩)
      = Sum.inl ⟨Sum.inl ⟨a.1, fun h => ha (by simp [Subtype.ext_iff, h])⟩, by
          simp [Subtype.ext_iff, a.2]⟩ := rfl

/--
@isnad1 id=eq.2h6v.s10.3246f8549fa3 from=translated src=- shape=feaac1c3 vocab=9f5c4ca2
-/
@[simp] lemma parEquiv_symm_inl_inr [DecidableEq B] [DecidableEq D] {i k : A} (hik : i ≠ k)
    (d : D) (hd : (Sum.inr d : Without A k ⊕ D) ≠ Sum.inl ⟨i, hik⟩) :
    (parEquiv hik B D).symm (Sum.inl ⟨Sum.inr d, hd⟩) = Sum.inr d := rfl

/--
@isnad1 id=eq.1h6v.s10.37656ec09ed7 from=translated src=- shape=bbe12652 vocab=64cbcc8a
-/
@[simp] lemma parEquiv_symm_inr [DecidableEq B] [DecidableEq D] {i k : A} (hik : i ≠ k) (b : B) :
    (parEquiv hik B D).symm (Sum.inr b) = Sum.inl ⟨Sum.inr b, by simp⟩ := rfl

/-- **Equivariance.** Relabelling the two input sets relabels the composite input set, the slot
moving from `i` to `σ i`: `(A ∖ i) ⊔ B ≅ (A' ∖ σ i) ⊔ B'`.-/
def compEquiv (σ : A ≃ A') (τ : B ≃ B') (i : A) : Without A i ⊕ B ≃ Without A' (σ i) ⊕ B' where
  toFun x :=
    match x with
    | Sum.inl a => Sum.inl ⟨σ a.1, fun h => a.2 (σ.injective h)⟩
    | Sum.inr b => Sum.inr (τ b)
  invFun y :=
    match y with
    | Sum.inl a => Sum.inl ⟨σ.symm a.1, fun h => a.2 (σ.symm_apply_eq.mp h)⟩
    | Sum.inr b => Sum.inr (τ.symm b)
  left_inv := by rintro (⟨a, ha⟩ | b) <;> simp
  right_inv := by rintro (⟨a, ha⟩ | b) <;> simp

/--
@isnad1 id=eq.0h8v.s8.2a5e2d87a653 from=translated src=- shape=6cc760bf vocab=6a193f0e
-/
@[simp] lemma compEquiv_inl (σ : A ≃ A') (τ : B ≃ B') (i : A) (a : Without A i) :
    compEquiv σ τ i (Sum.inl a) = Sum.inl ⟨σ a.1, fun h => a.2 (σ.injective h)⟩ := rfl

/--
@isnad1 id=eq.0h8v.s8.49da45f99db5 from=translated src=- shape=9e48d967 vocab=476ab97c
-/
@[simp] lemma compEquiv_inr (σ : A ≃ A') (τ : B ≃ B') (i : A) (b : B) :
    compEquiv σ τ i (Sum.inr b) = Sum.inr (τ b) := rfl

/--
@isnad1 id=eq.0h8v.s8.0bc7cbed9088 from=translated src=- shape=22c6df7e vocab=10854bf8
-/
@[simp] lemma compEquiv_symm_inl (σ : A ≃ A') (τ : B ≃ B') (i : A) (a : Without A' (σ i)) :
    (compEquiv σ τ i).symm (Sum.inl a)
      = Sum.inl ⟨σ.symm a.1, fun h => a.2 (σ.symm_apply_eq.mp h)⟩ := rfl

/--
@isnad1 id=eq.0h8v.s8.e8f1d6b89e9e from=translated src=- shape=c93a951f vocab=e12a96dc
-/
@[simp] lemma compEquiv_symm_inr (σ : A ≃ A') (τ : B ≃ B') (i : A) (b : B') :
    (compEquiv σ τ i).symm (Sum.inr b) = Sum.inr (τ.symm b) := rfl

/-- **The right unit.** Filling the input `i` with a single input leaves the input set alone:
`(A ∖ i) ⊔ Unit ≅ A`.-/
def rightUnitEquiv (i : A) : Without A i ⊕ Unit ≃ A where
  toFun x :=
    match x with
    | Sum.inl a => a.1
    | Sum.inr _ => i
  invFun x := if h : x = i then Sum.inr () else Sum.inl ⟨x, h⟩
  left_inv := by
    rintro (⟨a, ha⟩ | ⟨⟩)
    · simp [ha]
    · simp
  right_inv := by
    intro x
    by_cases h : x = i
    · simp [h]
    · simp [h]

/--
@isnad1 id=eq.0h3v.s6.46d72b0d0d31 from=translated src=- shape=577644f0 vocab=f8b1505c
-/
@[simp] lemma rightUnitEquiv_inl (i : A) (a : Without A i) :
    rightUnitEquiv i (Sum.inl a) = a.1 := rfl

/--
@isnad1 id=eq.0h3v.s6.06146845c776 from=translated src=- shape=96d041a6 vocab=81f21bf6
-/
@[simp] lemma rightUnitEquiv_inr (i : A) (u : Unit) : rightUnitEquiv i (Sum.inr u) = i := rfl

/-- **The left unit.** Composing into the single input of the unit leaves the input set alone:
`(Unit ∖ ()) ⊔ B ≅ B`, the first summand being empty.-/
def leftUnitEquiv (B : Type) : Without Unit () ⊕ B ≃ B where
  toFun x :=
    match x with
    | Sum.inl a => absurd (Subsingleton.elim a.1 ()) a.2
    | Sum.inr b => b
  invFun b := Sum.inr b
  left_inv := by
    rintro (⟨a, ha⟩ | b)
    · exact absurd (Subsingleton.elim a ()) ha
    · rfl
  right_inv := by intro b; rfl

/--
@isnad1 id=eq.0h2v.s5.522b820eff4a from=translated src=- shape=7a012433 vocab=1120f178
-/
@[simp] lemma leftUnitEquiv_inr (b : B) : leftUnitEquiv B (Sum.inr b) = b := rfl

/--
@isnad1 id=eq.0h2v.s6.44f6fb2b10e1 from=translated src=- shape=97f37653 vocab=4b9bd965
-/
@[simp] lemma leftUnitEquiv_symm_apply (b : B) : (leftUnitEquiv B).symm b = Sum.inr b := rfl

/-- The one-element type as the one-element `Fin`.-/
def unitFinOne : Unit ≃ Fin 1 where
  toFun _ := ⟨0, by omega⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv k := Fin.ext (by have := k.isLt; simp only; omega)

/-- Composing at two equal slots differ by the relabelling the equality induces.-/
def slotEquiv {A B : Type} [DecidableEq A] {i i' : A} (h : i = i') :
    Without A i ⊕ B ≃ Without A i' ⊕ B :=
  Equiv.sumCongr (Equiv.subtypeEquivRight fun a => by rw [h]) (Equiv.refl B)

/--
@isnad1 id=eq.1h5v.s7.147a109c5368 from=translated src=- shape=9a94f178 vocab=0dd4380f
-/
@[simp] lemma slotEquiv_inl {A B : Type} [DecidableEq A] {i i' : A} (h : i = i')
    (a : Without A i) : slotEquiv (B := B) h (Sum.inl a) = Sum.inl ⟨a.1, h ▸ a.2⟩ := rfl

/--
@isnad1 id=eq.1h5v.s6.40b504027494 from=translated src=- shape=d7ab6cd6 vocab=468ebcf5
-/
@[simp] lemma slotEquiv_inr {A B : Type} [DecidableEq A] {i i' : A} (h : i = i') (b : B) :
    slotEquiv (A := A) h (Sum.inr b) = Sum.inr b := rfl

/--
@isnad1 id=eq.0h2v.s6.e4ad80d71931 from=translated src=- shape=d95acd92 vocab=fcab4f4c
-/
lemma rightUnitEquiv_symm_self {A : Type} [DecidableEq A] (i : A) :
    (rightUnitEquiv i).symm i = Sum.inr () := by
  simp [rightUnitEquiv]

/--
@isnad1 id=eq.1h3v.s6.25160a8d7419 from=translated src=- shape=acc0e9d5 vocab=c6e3d9ae
-/
lemma rightUnitEquiv_symm_of_ne {A : Type} [DecidableEq A] {i x : A} (h : x ≠ i) :
    (rightUnitEquiv i).symm x = Sum.inl ⟨x, h⟩ := by
  simp [rightUnitEquiv, h]

end Equivs

end Sym

open Sym

/-! ## The class -/

/-- **A symmetric operad in `R`-modules**, by partial composition over finite types.-/
class SymOperad (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] where
  /-- Relabelling the inputs along a bijection.-/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → P A →ₗ[R] P B
  /-- Relabelling along the identity changes nothing.-/
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : P A) : map (Equiv.refl A) x = x
  /-- Relabelling is functorial.-/
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : P A) :
    map (e.trans f) x = map f (map e x)
  /-- The identity operation, with one input.-/
  one : P Unit
  /-- Insert an operation with inputs `B` at the input `i` of an operation with inputs `A`.-/
  comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    P A →ₗ[R] P B →ₗ[R] P (Without A i ⊕ B)
  /-- **Equivariance**: composition is natural in bijections of both input sets.-/
  map_comp {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (x : P A) (y : P B) :
    map (compEquiv σ τ i) (comp i x y) = comp (σ i) (map σ x) (map τ y)
  /-- The right unit: filling an input with the identity changes nothing.-/
  comp_one {A : Type} [Fintype A] [DecidableEq A] (i : A) (x : P A) :
    map (rightUnitEquiv i) (comp i x one) = x
  /-- The left unit: composing into the identity changes nothing.-/
  one_comp {B : Type} [Fintype B] [DecidableEq B] (y : P B) :
    map (leftUnitEquiv B) (comp () one y) = y
  /-- Sequential associativity: composing into an input that came from an earlier composition.-/
  comp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : P A) (y : P B) (z : P D) :
    map (seqEquiv i j D) (comp (Sum.inr j) (comp i x y) z) = comp i x (comp j y z)
  /-- Parallel associativity: filling two distinct inputs, in either order.-/
  comp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : P A) (y : P B) (z : P D) :
    map (parEquiv hik B D) (comp (Sum.inl ⟨k, Ne.symm hik⟩) (comp i x y) z)
      = comp (Sum.inl ⟨i, hik⟩) (comp k x z) y

namespace SymOperad

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-! ### Relabelling -/

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h4v.s7.b25b4ab94673 from=translated src=- shape=f7dd6603 vocab=c63c8cfc
-/
@[simp] lemma map_refl' (x : P A) : map (R := R) (Equiv.refl A) x = x := map_refl (R := R) x

omit [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h8v.s9.974a9a46a8e4 from=translated src=- shape=c3c46dd7 vocab=4cc0d96c
-/
lemma map_map (e : A ≃ B) (f : B ≃ C) (x : P A) :
    map (R := R) f (map (R := R) e x) = map (R := R) (e.trans f) x :=
  (map_trans (R := R) e f x).symm

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h6v.s8.136e9aef2644 from=translated src=- shape=89ae3416 vocab=2b9987dd
-/
@[simp] lemma map_symm_map (e : A ≃ B) (x : P A) :
    map (R := R) e.symm (map (R := R) e x) = x := by
  rw [map_map, Equiv.self_trans_symm, map_refl (R := R)]

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h6v.s8.ffb490e913f9 from=translated src=- shape=35604655 vocab=2b9987dd
-/
@[simp] lemma map_map_symm (e : A ≃ B) (y : P B) :
    map (R := R) e (map (R := R) e.symm y) = y := by
  rw [map_map, Equiv.symm_trans_self, map_refl (R := R)]

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=injectiv.0h5v.s8.6e9315abd8f5 from=translated src=- shape=67cefb41 vocab=e792603f
-/
lemma map_injective (e : A ≃ B) : Function.Injective (map (R := R) (P := P) e) :=
  fun x y h => by simpa using congrArg (map (R := R) e.symm) h

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/-- Relabelling along a bijection, as a linear equivalence.-/
def mapEquiv (e : A ≃ B) : P A ≃ₗ[R] P B :=
  LinearEquiv.ofLinearMap (map (R := R) e) (map (R := R) e.symm)
    (by ext y; exact map_map_symm (R := R) e y)
    (by ext x; exact map_symm_map (R := R) e x)

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h6v.s9.9648cdfef394 from=translated src=- shape=71295847 vocab=43d8d7cf
-/
@[simp] lemma mapEquiv_apply (e : A ≃ B) (x : P A) :
    mapEquiv (R := R) e x = map (R := R) e x := rfl

/-! ### The two classical equivariance axioms

Equivariance for permutations of the outer and of the inserted inputs are the cases of `map_comp`
with one of the two bijections the identity. -/

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h8v.s14.8fde037448a3 from=translated src=- shape=1fd76516 vocab=2ea309f5
-/
lemma map_comp_outer (σ : Equiv.Perm A) (i : A) (x : P A) (y : P B) :
    map (R := R) (compEquiv σ (Equiv.refl B) i) (comp (R := R) i x y)
      = comp (R := R) (σ i) (map (R := R) σ x) y := by
  rw [map_comp (R := R), map_refl (R := R)]

omit [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/--
@isnad1 id=eq.0h8v.s13.d1b373c66aab from=translated src=- shape=e8aa9788 vocab=2ea309f5
-/
lemma map_comp_inner (τ : Equiv.Perm B) (i : A) (x : P A) (y : P B) :
    map (R := R) (compEquiv (Equiv.refl A) τ i) (comp (R := R) i x y)
      = comp (R := R) i x (map (R := R) τ y) := by
  rw [map_comp (R := R), map_refl (R := R)]
  rfl

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/-- The right unit law, with the relabelling moved to the other side.
@isnad1 id=eq.0h5v.s12.af7fceba4d15 from=translated src=- shape=27deff8f vocab=11c04f74
-/
lemma comp_one' (i : A) (x : P A) :
    comp (R := R) i x (one R) = map (R := R) (rightUnitEquiv i).symm x := by
  apply map_injective (R := R) (rightUnitEquiv i)
  rw [comp_one (R := R), map_map_symm]

omit [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] in
/-- The left unit law, with the relabelling moved to the other side.
@isnad1 id=eq.0h4v.s12.0a6c4676b6eb from=translated src=- shape=22a2c75f vocab=4fe89e9f
-/
lemma one_comp' (y : P B) :
    comp (R := R) () (one R) y = map (R := R) (leftUnitEquiv B).symm y := by
  apply map_injective (R := R) (leftUnitEquiv B)
  rw [one_comp (R := R), map_map_symm]

end SymOperad

/-! ## Morphisms -/

/-- **A morphism of symmetric operads**: a family of linear maps commuting with relabelling, the
unit and composition.-/
structure SymOperadHom (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)]
    [SymOperad R P] [SymOperad R Q] where
  /-- The component at a finite input set.-/
  app (A : Type) [Fintype A] [DecidableEq A] : P A →ₗ[R] Q A
  /-- Components commute with relabelling.-/
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : P A) : app B (SymOperad.map (R := R) e x) = SymOperad.map (R := R) e (app A x)
  /-- The unit goes to the unit.-/
  app_one : app Unit (SymOperad.one R) = SymOperad.one R
  /-- Composition goes to composition.-/
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) (y : P B) :
    app (Without A i ⊕ B) (SymOperad.comp (R := R) i x y)
      = SymOperad.comp (R := R) i (app A x) (app B y)

namespace SymOperadHom

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- Two morphisms with the same components are equal.
@isnad1 id=eq.1h5v.s9.4d4cd45cf8a3 from=translated src=- shape=57282184 vocab=c4be18c2
-/
@[ext] lemma ext {φ ψ : SymOperadHom R P Q}
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A] (x : P A), φ.app A x = ψ.app A x) :
    φ = ψ := by
  obtain ⟨φa, _, _, _⟩ := φ
  obtain ⟨ψa, _, _, _⟩ := ψ
  have : @φa = @ψa := by
    funext A _ _
    exact LinearMap.ext (h A)
  subst this
  rfl

/-- The identity morphism.-/
def id : SymOperadHom R P P where
  app _ _ _ := LinearMap.id
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := rfl

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type*}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (S A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (S A)] [SymOperad R S]

/-- The composite of two morphisms.-/
def comp (ψ : SymOperadHom R Q S) (φ : SymOperadHom R P Q) : SymOperadHom R P S where
  app A _ _ := ψ.app A ∘ₗ φ.app A
  app_map e x := by simp only [LinearMap.comp_apply, φ.app_map, ψ.app_map]
  app_one := by simp only [LinearMap.comp_apply, φ.app_one, ψ.app_one]
  app_comp i x y := by simp only [LinearMap.comp_apply, φ.app_comp, ψ.app_comp]

/--
@isnad1 id=eq.0h8v.s9.31d36fe04a0d from=translated src=- shape=beb094e5 vocab=b74ad039
-/
@[simp] lemma comp_app (ψ : SymOperadHom R Q S) (φ : SymOperadHom R P Q)
    (A : Type) [Fintype A] [DecidableEq A] (x : P A) :
    (ψ.comp φ).app A x = ψ.app A (φ.app A x) := rfl

/-- **The inverse of a morphism with bijective components** is a morphism.-/
noncomputable def invOfBijective (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A)) :
    SymOperadHom R Q P where
  app A _ _ := (LinearEquiv.ofBijective (φ.app A) (h A)).symm.toLinearMap
  app_map e y := by
    apply (h _).1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply, φ.app_map]
  app_one := by
    apply (h _).1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply, φ.app_one]
  app_comp i x y := by
    apply (h _).1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply, φ.app_comp]

/--
@isnad1 id=eq.1h6v.s9.12e1f1c4b492 from=translated src=- shape=afcd2add vocab=82b92778
-/
lemma app_invOfBijective (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A))
    (A : Type) [Fintype A] [DecidableEq A] (y : Q A) :
    φ.app A ((φ.invOfBijective h).app A y) = y :=
  LinearEquiv.apply_ofBijective_symm_apply (φ.app A) (h := h A) y

/--
@isnad1 id=eq.1h6v.s9.b56d7d904819 from=translated src=- shape=c61fa914 vocab=82b92778
-/
lemma invOfBijective_app (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A))
    (A : Type) [Fintype A] [DecidableEq A] (x : P A) :
    (φ.invOfBijective h).app A (φ.app A x) = x :=
  (h A).1 (app_invOfBijective φ h A (φ.app A x))

/-- **Precomposition with a morphism with bijective components** is a bijection on morphisms out
of the target.-/
noncomputable def precompEquiv (φ : SymOperadHom R P Q)
    (h : ∀ (A : Type) [Fintype A] [DecidableEq A], Function.Bijective (φ.app A)) :
    SymOperadHom R Q S ≃ SymOperadHom R P S where
  toFun ψ := ψ.comp φ
  invFun χ := χ.comp (φ.invOfBijective h)
  left_inv ψ := by
    ext A _ _ y
    simp only [comp_app, app_invOfBijective]
  right_inv χ := by
    ext A _ _ x
    simp only [comp_app, invOfBijective_app]

end SymOperadHom

/-! ## The commutative operad

`Com R A = R` for every input set, the empty one included: one operation in each arity,
invariant under relabelling, with composition the product. Its algebras are the unital
commutative algebras. It is the target of every "evaluation". It is not terminal, even among
operads with one-dimensional components: for a unit `λ ≠ 1` of `R`, `x ↦ λ ^ (|A| - 1) • x` is an
endomorphism other than the identity. -/

namespace Sym

/-- `Com R A = R`.-/
@[nolint unusedArguments]
abbrev Com (R : Type u) [CommRing R] : (A : Type) → [Fintype A] → [DecidableEq A] → Type u :=
  fun _ _ _ => R

/-- **The commutative operad.**-/
instance instSymOperadCom (R : Type u) [CommRing R] : SymOperad R (Com R) where
  map _ := LinearMap.id
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  one := (1 : R)
  comp _ := LinearMap.mul R R
  map_comp _ _ _ _ _ := rfl
  comp_one _ x := mul_one x
  one_comp y := one_mul y
  comp_assoc_seq _ _ x y z := mul_assoc x y z
  comp_assoc_par _ x y z := by
    simp only [LinearMap.id_apply, LinearMap.mul_apply']
    ring

/--
@isnad1 id=eq.0h5v.s8.091974aae890 from=translated src=- shape=b97ec596 vocab=b421d8dc
-/
@[simp] lemma com_map (R : Type u) [CommRing R] {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (x : Com R A) :
    SymOperad.map (R := R) (P := Com R) e x = x := rfl

/--
@isnad1 id=eq.0h6v.s11.5cae16035679 from=translated src=- shape=e3fec0ba vocab=0b608788
-/
@[simp] lemma com_comp (R : Type u) [CommRing R] {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (i : A) (x : Com R A) (y : Com R B) :
    SymOperad.comp (R := R) (P := Com R) i x y = x * y := rfl

/--
@isnad1 id=eq.0h1v.s6.4489f97b7b90 from=translated src=- shape=e17bb385 vocab=278afd94
-/
@[simp] lemma com_one (R : Type u) [CommRing R] : (SymOperad.one R : Com R Unit) = (1 : R) := rfl

/-! ## The permutative operad

`Perm R A = A → R`, relabelled by transport, with the composite of `x` at `i` and `y` paying the
surviving outer inputs `x a · Σ y` and the inserted inputs `x i · y b`. This is Chapoton's operad;
the non-symmetric `Operad.Perm` is its restriction to `Fin n`, as `Operad.SymNS` shows. -/

/-- `Perm R A = A → R`.-/
@[nolint unusedArguments]
abbrev Perm (R : Type u) [CommRing R] : (A : Type) → [Fintype A] → [DecidableEq A] → Type u :=
  fun A _ _ => A → R

namespace Perm

variable {R : Type u} [CommRing R] {A B : Type}

/-- Relabelling a function along a bijection: `(e • x) b = x (e⁻¹ b)`.-/
def mapL (e : A ≃ B) : (A → R) →ₗ[R] (B → R) where
  toFun x b := x (e.symm b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h6v.s8.d2e687a5c889 from=translated src=- shape=5033aa04 vocab=5b019cec
-/
@[simp] lemma mapL_apply (e : A ≃ B) (x : A → R) (b : B) : mapL e x b = x (e.symm b) := rfl

/-- The composite of `x` at `i` with `y`, as a function on the composite input set.-/
def compFun [DecidableEq A] [Fintype B] (i : A) (x : A → R) (y : B → R) : Without A i ⊕ B → R
  | Sum.inl a => x a.1 * ∑ b, y b
  | Sum.inr b => x i * y b

/--
@isnad1 id=eq.0h7v.s6.d8444323a353 from=translated src=- shape=5446e66e vocab=b23877cb
-/
@[simp] lemma compFun_inl [DecidableEq A] [Fintype B] (i : A) (x : A → R) (y : B → R)
    (a : Without A i) :
    compFun i x y (Sum.inl a) = x a.1 * ∑ b, y b := rfl

/--
@isnad1 id=eq.0h7v.s6.cc6b914a9fa8 from=translated src=- shape=7869cb19 vocab=5ef60de7
-/
@[simp] lemma compFun_inr [DecidableEq A] [Fintype B] (i : A) (x : A → R) (y : B → R) (b : B) :
    compFun i x y (Sum.inr b) = x i * y b := rfl

/-- The composite is bilinear.-/
def compL [DecidableEq A] [Fintype B] (i : A) :
    (A → R) →ₗ[R] (B → R) →ₗ[R] (Without A i ⊕ B → R) :=
  LinearMap.mk₂ R (compFun i)
    (fun x x' y => by funext c; rcases c with a | b <;> simp [add_mul])
    (fun t x y => by funext c; rcases c with a | b <;> simp [mul_assoc])
    (fun x y y' => by funext c; rcases c with a | b <;> simp [Finset.sum_add_distrib, mul_add])
    (fun t x y => by
      funext c; rcases c with a | b <;> simp [Finset.mul_sum, mul_left_comm])

/--
@isnad1 id=eq.0h6v.s10.0d20e96a59c8 from=translated src=- shape=a60e9deb vocab=a428abd8
-/
@[simp] lemma compL_apply [DecidableEq A] [Fintype B] (i : A) (x : A → R) (y : B → R) :
    compL i x y = compFun i x y := rfl

/-- **The sum of a composite is the product of the sums.**
@isnad1 id=eq.0h6v.s7.4e81e19d01f6 from=translated src=- shape=a0d6170d vocab=681f530c
-/
theorem sum_compFun [Fintype A] [DecidableEq A] [Fintype B] (i : A) (x : A → R) (y : B → R) :
    ∑ c, compFun i x y c = (∑ a, x a) * ∑ b, y b := by
  rw [Fintype.sum_sum_type, Fintype.sum_eq_add_sum_subtype_ne x i, add_mul, add_comm]
  simp only [compFun_inl, compFun_inr, ← Finset.mul_sum, ← Finset.sum_mul]

end Perm

/-- **The permutative operad**, as a symmetric operad.-/
instance instSymOperadPerm (R : Type u) [CommRing R] : SymOperad R (Perm R) where
  map e := Perm.mapL e
  map_refl _ := rfl
  map_trans _ _ _ := rfl
  one := fun _ => 1
  comp i := Perm.compL i
  map_comp σ τ i x y := by
    funext c
    rcases c with a | b
    · simp only [Perm.mapL_apply, Perm.compL_apply, compEquiv_symm_inl, Perm.compFun_inl]
      congr 1
      exact (Equiv.sum_comp τ.symm y).symm
    · simp [Perm.mapL_apply, Perm.compL_apply, compEquiv_symm_inr, Perm.compFun_inr]
  comp_one i x := by
    funext a
    by_cases h : a = i
    · subst h
      simp [Perm.mapL_apply, rightUnitEquiv]
    · simp [Perm.mapL_apply, rightUnitEquiv, h]
  one_comp y := by
    funext b
    simp [Perm.mapL_apply]
  comp_assoc_seq i j x y z := by
    funext c
    rcases c with a | b | d
    · simp only [Perm.mapL_apply, Perm.compL_apply, seqEquiv_symm_inl, Perm.compFun_inl,
        Perm.sum_compFun]
      ring
    · simp only [Perm.mapL_apply, Perm.compL_apply, seqEquiv_symm_inr_inl, Perm.compFun_inl,
        Perm.compFun_inr]
      ring
    · simp only [Perm.mapL_apply, Perm.compL_apply, seqEquiv_symm_inr_inr, Perm.compFun_inr]
      ring
  comp_assoc_par hik x y z := by
    funext c
    rcases c with ⟨(a | d), ha⟩ | b
    · simp only [Perm.mapL_apply, Perm.compL_apply, parEquiv_symm_inl_inl, Perm.compFun_inl]
      ring
    · simp only [Perm.mapL_apply, Perm.compL_apply, parEquiv_symm_inl_inr, Perm.compFun_inl,
        Perm.compFun_inr]
      ring
    · simp only [Perm.mapL_apply, Perm.compL_apply, parEquiv_symm_inr, Perm.compFun_inl,
        Perm.compFun_inr]
      ring

/-- **Summing is a morphism `Perm → Com`.** The total of a composite is the product of the
totals, and relabelling does not change a total.-/
def Perm.sumHom (R : Type u) [CommRing R] : SymOperadHom R (Perm R) (Com R) where
  app A _ _ :=
    { toFun := fun x => ∑ a, x a
      map_add' := fun x y => Finset.sum_add_distrib
      map_smul' := fun t x => by simp [Finset.mul_sum] }
  app_map e x := by
    show ∑ b, x (e.symm b) = ∑ a, x a
    exact Equiv.sum_comp e.symm x
  app_one := by
    show ∑ _u : Unit, (1 : R) = 1
    simp
  app_comp i x y := Perm.sum_compFun i x y

end Sym

end Operad

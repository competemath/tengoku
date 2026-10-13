/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Circuits.BranchingProgram
public import Tengoku
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Toward Barrington's theorem: the group-theoretic core

Barrington's theorem builds a width-`5` permutation branching program for any
`NC¹` formula by representing a Boolean function through a fixed non-identity
permutation. This module formalizes the reusable, group-theoretic heart of that
construction, independent of the eventual `S₅` choice of
permutations.

The central notion is `BP.Computes σ p f`: the program `p` *represents* the
Boolean function `f` through the permutation `σ`, meaning it evaluates to `σ`
exactly when `f` holds and to `1` (the identity) otherwise. The closure lemmas
proved here are the moves in Barrington's inductive construction:

- **conjugation** changes the representing permutation, either by wrapping the
  program (`Computes_conj`) or pointwise with no length overhead
  (`Computes_conjugate`);
- **negation** flips the function while inverting the permutation, either by
  appending a constant (`Computes_not`) or by folding that constant into the
  final instruction (`Computes_not_compact`);
- the **commutator trick** (`Computes_and`) represents `f ∧ g` through the
  commutator `⁅σ, τ⁆` — choosing `σ, τ` to be `5`-cycles in `S₅` whose
  commutator is again a `5`-cycle is exactly what makes the `AND` gate work.

## Main definitions and results

- `BPInstr.inverse`, `BP.inverse`, `BP.eval_inverse` — inverting a program
  inverts the permutation it evaluates to.
- `BPInstr.const`, `BPInstr.eval_const` — constant instructions.
- `BPInstr.conjugate`, `BP.conjugate`, `BP.eval_conjugate` — length-preserving
  pointwise conjugation.
- `BPInstr.postMul`, `BP.postMul`, `BP.eval_postMul` — fold a final constant
  into the last instruction, adding an instruction only to the empty program.
- `BP.Computes`, `BP.Computes_conj`, `BP.Computes_not`,
  `BP.Computes_not_compact`, `BP.Computes_and`.
-/

@[expose] public section

open scoped commutatorElement

namespace Complexity

/-- Invert a branching-program instruction: keep the variable read, invert both
    branch permutations. -/
def BPInstr.inverse {w : ℕ} (ins : BPInstr w) : BPInstr w :=
  { var := ins.var, perm0 := ins.perm0⁻¹, perm1 := ins.perm1⁻¹ }

/-- Inverting an instruction inverts the permutation it selects.
@isnad1 id=eq.0h3v.s4.52c905694902 from=translated src=- shape=e0467db3 vocab=8fc6ed0f
-/
@[simp] theorem BPInstr.eval_inverse {w : ℕ} (α : ℕ → Bool) (ins : BPInstr w) :
    BPInstr.eval α (BPInstr.inverse ins) = (BPInstr.eval α ins)⁻¹ := by
  simp only [BPInstr.eval, BPInstr.inverse]
  by_cases h : α ins.var = true <;> simp [h]

/-- A constant instruction applies the permutation `c` regardless of the input. -/
def BPInstr.const {w : ℕ} (c : Equiv.Perm (Fin w)) : BPInstr w :=
  { var := 0, perm0 := c, perm1 := c }

/-- A constant instruction always evaluates to its permutation.
@isnad1 id=eq.0h3v.s4.8422fadbe424 from=translated src=- shape=6d1250fe vocab=7c470f90
-/
@[simp] theorem BPInstr.eval_const {w : ℕ} (α : ℕ → Bool) (c : Equiv.Perm (Fin w)) :
    BPInstr.eval α (BPInstr.const c) = c := by
  simp only [BPInstr.eval, BPInstr.const]
  by_cases h : α 0 = true <;> simp [h]

/-- Conjugate both branches of an instruction by the same permutation. -/
def BPInstr.conjugate {w : ℕ} (τ : Equiv.Perm (Fin w))
    (ins : BPInstr w) : BPInstr w :=
  { ins with
    perm0 := τ * ins.perm0 * τ⁻¹
    perm1 := τ * ins.perm1 * τ⁻¹ }

/-- Pointwise instruction conjugation realizes group conjugation.
@isnad1 id=eq.0h4v.s6.da8d527d290e from=translated src=- shape=d4a4f035 vocab=b44ffae0
-/
@[simp] theorem BPInstr.eval_conjugate {w : ℕ} (α : ℕ → Bool)
    (τ : Equiv.Perm (Fin w)) (ins : BPInstr w) :
    BPInstr.eval α (BPInstr.conjugate τ ins) =
      τ * BPInstr.eval α ins * τ⁻¹ := by
  simp only [BPInstr.eval, BPInstr.conjugate]
  by_cases h : α ins.var = true <;> simp [h]

/-- Right-multiply both branches of an instruction by a fixed permutation. -/
def BPInstr.postMul {w : ℕ} (ins : BPInstr w)
    (c : Equiv.Perm (Fin w)) : BPInstr w :=
  { ins with perm0 := ins.perm0 * c, perm1 := ins.perm1 * c }

/-- Right-multiplication commutes with selecting an instruction branch.
@isnad1 id=eq.0h4v.s5.7f9c8ca1e968 from=translated src=- shape=9e161b3d vocab=849fea0f
-/
@[simp] theorem BPInstr.eval_postMul {w : ℕ} (α : ℕ → Bool)
    (ins : BPInstr w) (c : Equiv.Perm (Fin w)) :
    BPInstr.eval α (BPInstr.postMul ins c) = BPInstr.eval α ins * c := by
  simp only [BPInstr.eval, BPInstr.postMul]
  by_cases h : α ins.var = true <;> simp [h]

/-- Conjugate every instruction of a branching program. Unlike wrapping with
constant instructions, this operation preserves length exactly. -/
def BP.conjugate {w : ℕ} (τ : Equiv.Perm (Fin w)) (p : BP w) : BP w :=
  p.map (BPInstr.conjugate τ)

/-- Pointwise conjugation conjugates the value of the whole program.
@isnad1 id=eq.0h4v.s6.b8c4a671d8ca from=translated src=- shape=d4a4f035 vocab=a8f11c88
-/
theorem BP.eval_conjugate {w : ℕ} (α : ℕ → Bool)
    (τ : Equiv.Perm (Fin w)) (p : BP w) :
    BP.eval α (BP.conjugate τ p) = τ * BP.eval α p * τ⁻¹ := by
  induction p with
  | nil => simp [BP.conjugate, BP.eval]
  | cons ins p ih =>
      rw [show BP.conjugate τ (ins :: p) =
        BPInstr.conjugate τ ins :: BP.conjugate τ p from rfl]
      rw [BP.eval_cons, BPInstr.eval_conjugate, ih, BP.eval_cons]
      simp only [mul_assoc, inv_mul_cancel_left]

/-- Pointwise conjugation preserves program length exactly.
@isnad1 id=eq.0h3v.s4.2309f09bea58 from=translated src=- shape=8890a5af vocab=c8f9dfe3
-/
@[simp] theorem BP.length_conjugate {w : ℕ}
    (τ : Equiv.Perm (Fin w)) (p : BP w) :
    (BP.conjugate τ p).length = p.length := by
  simp [BP.conjugate]

/-- Fold a final constant multiplication into the last instruction. The empty
program has no last instruction, so it becomes a singleton constant program. -/
def BP.postMul {w : ℕ} (p : BP w) (c : Equiv.Perm (Fin w)) : BP w :=
  if p = [] then [BPInstr.const c]
  else p.modifyLast fun ins => BPInstr.postMul ins c

/-- Folding a final constant into the last instruction right-multiplies the
program value.
@isnad1 id=eq.0h4v.s5.ec518b247c92 from=translated src=- shape=9e161b3d vocab=7c98353c
-/
theorem BP.eval_postMul {w : ℕ} (α : ℕ → Bool) (p : BP w)
    (c : Equiv.Perm (Fin w)) :
    BP.eval α (BP.postMul p c) = BP.eval α p * c := by
  induction p using List.reverseRecOn with
  | nil => simp [BP.postMul, BP.eval_singleton]
  | append_singleton p ins ih =>
      simp [BP.postMul, List.modifyLast_concat, BP.eval_append,
        BP.eval_singleton, mul_assoc]

/-- Folding a final constant uses the original length, except that an empty
program needs one instruction.
@isnad1 id=eq.0h3v.s4.abc14732458b from=translated src=- shape=8233c80a vocab=a656fbf9
-/
theorem BP.length_postMul {w : ℕ} (p : BP w)
    (c : Equiv.Perm (Fin w)) :
    (BP.postMul p c).length = max 1 p.length := by
  induction p using List.reverseRecOn with
  | nil => simp [BP.postMul]
  | append_singleton p ins ih =>
      simp [BP.postMul, List.modifyLast_concat]

/-- Invert a branching program: reverse the instruction list and invert each
    instruction. -/
def BP.inverse {w : ℕ} (p : BP w) : BP w := (p.map BPInstr.inverse).reverse

/-- **Inversion is correct**: the inverted program evaluates to the inverse of
    the original program's permutation.
@isnad1 id=eq.0h3v.s4.9bcae397f0c5 from=translated src=- shape=e0467db3 vocab=d9306b75
-/
theorem BP.eval_inverse {w : ℕ} (α : ℕ → Bool) (p : BP w) :
    BP.eval α (BP.inverse p) = (BP.eval α p)⁻¹ := by
  induction p with
  | nil => simp [BP.inverse, BP.eval]
  | cons ins p ih =>
    have hcons : BP.inverse (ins :: p) = BP.inverse p ++ [BPInstr.inverse ins] := by
      simp [BP.inverse, List.map_cons, List.reverse_cons]
    rw [hcons, BP.eval_append, ih, BP.eval_singleton, BPInstr.eval_inverse,
      BP.eval_cons, mul_inv_rev]

/-- `Computes σ p f` : the branching program `p` represents the Boolean function
    `f` through the permutation `σ` — it evaluates to `σ` when `f` holds and to
    the identity otherwise. -/
def BP.Computes {w : ℕ} (σ : Equiv.Perm (Fin w)) (p : BP w) (f : (ℕ → Bool) → Bool) : Prop :=
  ∀ α, BP.eval α p = if f α then σ else 1

/-- **Conjugation of the representing permutation.** Wrapping a program between a
    constant `τ` and a constant `τ⁻¹` conjugates the permutation it represents.
@isnad1 id=computes.1h5v.s7.fbc39b3ed445 from=translated src=- shape=5935ebbc vocab=cb17d56d
-/
theorem BP.Computes_conj {w : ℕ} {σ : Equiv.Perm (Fin w)} {p : BP w}
    {f : (ℕ → Bool) → Bool} (h : BP.Computes σ p f) (τ : Equiv.Perm (Fin w)) :
    BP.Computes (τ * σ * τ⁻¹) ([BPInstr.const τ] ++ p ++ [BPInstr.const τ⁻¹]) f := by
  intro α
  simp only [BP.eval_append, BP.eval_singleton, BPInstr.eval_const, h α]
  rcases Bool.eq_false_or_eq_true (f α) with hf | hf <;> simp [hf]

/-- **Length-preserving conjugation.** Conjugating every instruction changes
the representing permutation without adding constant instructions.
@isnad1 id=computes.1h5v.s6.66322a52b7fd from=translated src=- shape=398a2cf7 vocab=bb39c35b
-/
theorem BP.Computes_conjugate {w : ℕ} {σ : Equiv.Perm (Fin w)} {p : BP w}
    {f : (ℕ → Bool) → Bool} (h : BP.Computes σ p f)
    (τ : Equiv.Perm (Fin w)) :
    BP.Computes (τ * σ * τ⁻¹) (BP.conjugate τ p) f := by
  intro α
  rw [BP.eval_conjugate, h α]
  rcases Bool.eq_false_or_eq_true (f α) with hf | hf <;> simp [hf]

/-- **Negation.** Appending a constant `σ⁻¹` to a program that represents `f`
    through `σ` yields a program representing `¬f` through `σ⁻¹`.
@isnad1 id=computes.1h4v.s6.93ae290ddf60 from=translated src=- shape=4251a13f vocab=d3d00204
-/
theorem BP.Computes_not {w : ℕ} {σ : Equiv.Perm (Fin w)} {p : BP w}
    {f : (ℕ → Bool) → Bool} (h : BP.Computes σ p f) :
    BP.Computes σ⁻¹ (p ++ [BPInstr.const σ⁻¹]) (fun α => !f α) := by
  intro α
  simp only [BP.eval_append, BP.eval_singleton, BPInstr.eval_const, h α]
  rcases Bool.eq_false_or_eq_true (f α) with hf | hf <;> simp [hf]

/-- **Compact negation.** Multiplying the final selected permutation by `σ⁻¹`
represents `¬f` through `σ⁻¹`. The multiplication is folded into the last
instruction, so the length becomes only `max 1 p.length`.
@isnad1 id=computes.1h4v.s5.bc96464d0a88 from=translated src=- shape=1320edbf vocab=48d5f3eb
-/
theorem BP.Computes_not_compact {w : ℕ} {σ : Equiv.Perm (Fin w)} {p : BP w}
    {f : (ℕ → Bool) → Bool} (h : BP.Computes σ p f) :
    BP.Computes σ⁻¹ (BP.postMul p σ⁻¹) (fun α => !f α) := by
  intro α
  rw [BP.eval_postMul, h α]
  rcases Bool.eq_false_or_eq_true (f α) with hf | hf <;> simp [hf]

/-- **The commutator trick** (Barrington's `AND` gate). If `p` represents `f`
    through `σ` and `q` represents `g` through `τ`, then the commutator program
    `p q p⁻¹ q⁻¹` represents `f ∧ g` through the commutator `⁅σ, τ⁆`.

    When both `f` and `g` hold the four factors multiply to `σ τ σ⁻¹ τ⁻¹ = ⁅σ, τ⁆`;
    if either fails, the corresponding factor collapses to `1` and the product
    telescopes to the identity.
@isnad1 id=computes.2h7v.s6.836f0f7e435f from=translated src=- shape=c7ca3daa vocab=2171d603
-/
theorem BP.Computes_and {w : ℕ} {σ τ : Equiv.Perm (Fin w)} {p q : BP w}
    {f g : (ℕ → Bool) → Bool} (hp : BP.Computes σ p f) (hq : BP.Computes τ q g) :
    BP.Computes ⁅σ, τ⁆ (p ++ q ++ BP.inverse p ++ BP.inverse q) (fun α => f α && g α) := by
  intro α
  simp only [BP.eval_append, BP.eval_inverse, hp α, hq α]
  rw [commutatorElement_def]
  rcases Bool.eq_false_or_eq_true (f α) with hf | hf <;>
    rcases Bool.eq_false_or_eq_true (g α) with hg | hg <;>
    simp [hf, hg]

/-- **Base case — constant `false`.** The empty program represents the constant
    function `false` through any permutation (it always evaluates to the
    identity).
@isnad1 id=computes.0h2v.s4.8a8774d63a31 from=translated src=- shape=e6c60940 vocab=771f18c6
-/
theorem BP.Computes_false {w : ℕ} (σ : Equiv.Perm (Fin w)) :
    BP.Computes σ ([] : BP w) (fun _ => false) := by
  intro α
  simp

/-- **Base case — constant `true`.** A single constant-`σ` instruction represents
    the constant function `true` through `σ`.
@isnad1 id=computes.0h2v.s4.3b22d43b4e31 from=translated src=- shape=84492b66 vocab=2fad2837
-/
theorem BP.Computes_true {w : ℕ} (σ : Equiv.Perm (Fin w)) :
    BP.Computes σ [BPInstr.const σ] (fun _ => true) := by
  intro α
  simp [BP.eval_singleton]

/-- **Base case — a literal.** The single instruction reading variable `i`, which
    applies `σ` when the bit is `true` and the identity when it is `false`,
    represents the projection `fun α => α i` through `σ`.
@isnad1 id=computes.0h3v.s5.38ef7323d6f0 from=translated src=- shape=d57fa429 vocab=db5a4099
-/
theorem BP.Computes_var {w : ℕ} (σ : Equiv.Perm (Fin w)) (i : ℕ) :
    BP.Computes σ [⟨i, 1, σ⟩] (fun α => α i) := by
  intro α
  rw [BP.eval_singleton]
  rfl

/-- **Disjunction is representable.** By De Morgan (`f ∨ g = ¬(¬f ∧ ¬g)`), the
    negation and commutator constructions combine to represent `f ∨ g`. With the
    base cases (`Computes_false`, `Computes_true`, `Computes_var`) and negation,
    this gives a functionally complete set of moves for width-`w` permutation
    branching programs — the abstract engine of Barrington's induction.
@isnad1 id=ex.2h7v.s6.e0dfb9d293fc from=translated src=- shape=8b48e817 vocab=950b6734
-/
theorem BP.Computes_or {w : ℕ} {σ τ : Equiv.Perm (Fin w)} {p q : BP w}
    {f g : (ℕ → Bool) → Bool} (hp : BP.Computes σ p f) (hq : BP.Computes τ q g) :
    ∃ (μ : Equiv.Perm (Fin w)) (r : BP w), BP.Computes μ r (fun α => f α || g α) := by
  have h := BP.Computes_not (BP.Computes_and (BP.Computes_not hp) (BP.Computes_not hq))
  simp only [Bool.not_and, Bool.not_not] at h
  exact ⟨_, _, h⟩

end Complexity

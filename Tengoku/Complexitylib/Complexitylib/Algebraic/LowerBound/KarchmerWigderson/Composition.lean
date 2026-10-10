/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Basic
public import Tengoku.Complexitylib.Complexitylib.Algebraic.BooleanCube
public import Tengoku

/-!
# Composition of Boolean functions and the KRW conjecture

The composition `f ⋄ g` of `f` on `m` bits with `g` on `n` bits applies `f`
to the values of `g` on `m` disjoint blocks of `n` bits. Here depth and size
are the minimum depth and leaf count of a De Morgan formula (`formulaDepth`,
`formulaSize`). Substituting a formula for `g` into a formula for `f` gives,
for all `f` and `g`, `depth (f ⋄ g) ≤ depth f + depth g`
(`formulaDepth_compose_le`) and `size (f ⋄ g) ≤ size f · size g`
(`formulaSize_compose_le`). Projections give `depth g ≤ depth (f ⋄ g)` when
`f` is not constant and `depth f ≤ depth (f ⋄ g)` when `g` is not constant.

The Karchmer–Raz–Wigderson conjecture asserts that for non-constant `f` and
`g` the upper bounds are tight up to lower-order terms. It is stated here in
its strong form, with a constant slack. `KRWDepthWith c` says that
`depth f + depth g ≤ depth (f ⋄ g) + c` for all `m`, `n` and all non-constant
`f` and `g` (`NonConstant`), and `KRWSizeWith c` says that
`size f · size g ≤ c · size (f ⋄ g)` for all such `f` and `g`. The
conjectures `KRWDepth` and `KRWSize` say that some constant `c` works. They
are open, and nothing here proves them; forms whose slack grows with `m` or
`n` are not formalized.

Both non-constancy hypotheses are needed. If `f` or `g` is constant then
`f ⋄ g` is constant, and dropping either hypothesis from `KRWDepthWith c` or
`KRWSizeWith c` gives a false statement for every `c`
(`not_forall_depth_of_constant_inner`, `not_forall_depth_of_constant_outer`,
`not_forall_size_of_constant_inner`, `not_forall_size_of_constant_outer`).
-/

@[expose] public section

namespace Algebraic
namespace KW

open scoped Classical

variable {m n N : Nat}

/-! ### Relabeling and substitution -/

namespace Formula

/-- Relabel the variables of a formula. -/
def mapIndex (φ : Fin n → Fin N) : Formula n → Formula N
  | lit i b => lit (φ i) b
  | const b => const b
  | and l r => and (l.mapIndex φ) (r.mapIndex φ)
  | or l r => or (l.mapIndex φ) (r.mapIndex φ)

@[simp] theorem eval_mapIndex (φ : Fin n → Fin N) :
    ∀ (F : Formula n) (x : Fin N → Bool), (F.mapIndex φ).eval x = F.eval (x ∘ φ)
  | lit _ _, _ => rfl
  | const _, _ => rfl
  | and l r, x => by simp [mapIndex, eval_mapIndex φ l, eval_mapIndex φ r]
  | or l r, x => by simp [mapIndex, eval_mapIndex φ l, eval_mapIndex φ r]

@[simp] theorem depth_mapIndex (φ : Fin n → Fin N) :
    ∀ F : Formula n, (F.mapIndex φ).depth = F.depth
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [mapIndex, depth, depth_mapIndex φ l, depth_mapIndex φ r]
  | or l r => by simp [mapIndex, depth, depth_mapIndex φ l, depth_mapIndex φ r]

@[simp] theorem leaves_mapIndex (φ : Fin n → Fin N) :
    ∀ F : Formula n, (F.mapIndex φ).leaves = F.leaves
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [mapIndex, leaves, leaves_mapIndex φ l, leaves_mapIndex φ r]
  | or l r => by simp [mapIndex, leaves, leaves_mapIndex φ l, leaves_mapIndex φ r]

/-- Substitute a formula, or its negation, for every literal. -/
def subst (σ : Fin N → Formula n) : Formula N → Formula n
  | lit i b => if b then σ i else (σ i).neg
  | const b => const b
  | and l r => and (l.subst σ) (r.subst σ)
  | or l r => or (l.subst σ) (r.subst σ)

@[simp] theorem eval_subst (σ : Fin N → Formula n) :
    ∀ (F : Formula N) (x : Fin n → Bool), (F.subst σ).eval x = F.eval fun i => (σ i).eval x
  | lit i b, x => by
    cases b
    · simp only [subst, Bool.false_eq_true, ↓reduceIte, eval_neg, eval_lit]
      cases (σ i).eval x <;> rfl
    · simp only [subst, ↓reduceIte, eval_lit]
      cases (σ i).eval x <;> rfl
  | const _, _ => rfl
  | and l r, x => by simp [subst, eval_subst σ l, eval_subst σ r]
  | or l r, x => by simp [subst, eval_subst σ l, eval_subst σ r]

theorem depth_subst_le (σ : Fin N → Formula n) {d : Nat} (hσ : ∀ i, (σ i).depth ≤ d) :
    ∀ F : Formula N, (F.subst σ).depth ≤ F.depth + d
  | lit i b => by
    cases b <;> simp [subst, depth, hσ i]
  | const _ => by simp [subst, depth]
  | and l r => by
    simp only [subst, depth]
    have := depth_subst_le σ hσ l
    have := depth_subst_le σ hσ r
    omega
  | or l r => by
    simp only [subst, depth]
    have := depth_subst_le σ hσ l
    have := depth_subst_le σ hσ r
    omega

theorem leaves_subst_le (σ : Fin N → Formula n) {L : Nat} (hL : 1 ≤ L)
    (hσ : ∀ i, (σ i).leaves ≤ L) :
    ∀ F : Formula N, (F.subst σ).leaves ≤ F.leaves * L
  | lit i b => by
    cases b <;> simp [subst, leaves, hσ i]
  | const _ => by simpa [subst, leaves] using hL
  | and l r => by
    simp only [subst, leaves, Nat.add_mul]
    have := leaves_subst_le σ hL hσ l
    have := leaves_subst_le σ hL hσ r
    omega
  | or l r => by
    simp only [subst, leaves, Nat.add_mul]
    have := leaves_subst_le σ hL hσ l
    have := leaves_subst_le σ hL hσ r
    omega

end Formula

/-- An infimum of natural numbers in `ℕ∞` over a nonempty index type is attained. -/
theorem exists_iInf_natCast_eq {ι : Type*} [Nonempty ι] (u : ι → Nat) :
    ∃ i, (⨅ j, (u j : ℕ∞)) = u i := by
  obtain ⟨i, hi⟩ := Nat.sInf_mem (Set.range_nonempty u)
  refine ⟨i, le_antisymm (iInf_le _ i) (le_iInf fun j => ?_)⟩
  have : u i ≤ u j := hi ▸ Nat.sInf_le (Set.mem_range_self j)
  exact_mod_cast this

/-! ### Composition -/

/-- The position of coordinate `i` of block `j`. -/
def blockIndex (j : Fin m) (i : Fin n) : Fin (m * n) :=
  finProdFinEquiv (j, i)

theorem finProdFinEquiv_symm_blockIndex (j : Fin m) (i : Fin n) :
    finProdFinEquiv.symm (blockIndex j i) = (j, i) :=
  Equiv.symm_apply_apply _ _

namespace Formula

/-- Substitute a formula for `g` into a formula for `f`, block by block. -/
def compose (F : Formula m) (G : Formula n) : Formula (m * n) :=
  F.subst fun j => G.mapIndex (blockIndex j)

theorem eval_compose (F : Formula m) (G : Formula n) (z : Fin (m * n) → Bool) :
    (F.compose G).eval z = F.eval fun j => G.eval fun i => z (blockIndex j i) := by
  simp [Formula.compose, Function.comp_def]

theorem depth_compose_le (F : Formula m) (G : Formula n) :
    (F.compose G).depth ≤ F.depth + G.depth :=
  depth_subst_le _ (fun j => by rw [depth_mapIndex]) F

theorem leaves_compose_le (F : Formula m) (G : Formula n) :
    (F.compose G).leaves ≤ F.leaves * G.leaves :=
  leaves_subst_le _ (one_le_leaves G) (fun j => by rw [leaves_mapIndex]) F

end Formula

/-! ### Lower bounds by projection -/

/-! ### Non-constant functions -/

/-! ### The conjecture -/

/-! ### Both non-constancy hypotheses are needed

If `f` or `g` is constant then `f ⋄ g` is constant, of depth `0` and size `1`,
while the other function can have depth or size above any fixed slack. So
dropping either hypothesis from `KRWDepthWith c` or `KRWSizeWith c` gives a
false statement, whatever `c` is. The witness of large depth and size is the
conjunction of all `k` bits, whose formulas read every bit and so have at
least `k` leaves and depth at least `log₂ k`. -/

namespace Formula

/-- The coordinates read by some literal of a formula. -/
def vars : Formula n → Finset (Fin n)
  | lit i _ => {i}
  | const _ => ∅
  | and l r => l.vars ∪ r.vars
  | or l r => l.vars ∪ r.vars

theorem card_vars_le_leaves : ∀ F : Formula n, F.vars.card ≤ F.leaves
  | lit _ _ => by simp [vars, leaves]
  | const _ => by simp [vars, leaves]
  | and l r => by
    simp only [vars, leaves]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_vars_le_leaves l) (card_vars_le_leaves r))
  | or l r => by
    simp only [vars, leaves]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_vars_le_leaves l) (card_vars_le_leaves r))

/-- Changing a coordinate that a formula does not read leaves its value unchanged. -/
theorem eval_update_of_notMem_vars {i : Fin n} (b : Bool) (x : Fin n → Bool) :
    ∀ F : Formula n, i ∉ F.vars → F.eval (Function.update x i b) = F.eval x
  | lit j _, h => by
    have hji : j ≠ i := fun hji => h (by simp [vars, hji])
    simp [Function.update_of_ne hji]
  | const _, _ => rfl
  | and l r, h => by
    simp only [vars, Finset.mem_union, not_or] at h
    simp [eval_update_of_notMem_vars b x l h.1, eval_update_of_notMem_vars b x r h.2]
  | or l r, h => by
    simp only [vars, Finset.mem_union, not_or] at h
    simp [eval_update_of_notMem_vars b x l h.1, eval_update_of_notMem_vars b x r h.2]

theorem leaves_le_two_pow_depth : ∀ F : Formula n, F.leaves ≤ 2 ^ F.depth
  | lit _ _ => by simp [leaves, depth]
  | const _ => by simp [leaves, depth]
  | and l r => by
    simp only [leaves, depth, pow_succ]
    have hl := leaves_le_two_pow_depth l
    have hr := leaves_le_two_pow_depth r
    have hl' : 2 ^ l.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr' : 2 ^ r.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  | or l r => by
    simp only [leaves, depth, pow_succ]
    have hl := leaves_le_two_pow_depth l
    have hr := leaves_le_two_pow_depth r
    have hl' : 2 ^ l.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr' : 2 ^ r.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega

end Formula

end KW
end Algebraic

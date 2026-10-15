/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Exercise516
public import Tengoku

/-!
# Exercise 5.16 follow-up (Scott 1981, PRG-19, Lecture V) — the Thue–Morse
sequence `t`

The unfinished tail of Exercise 5.16. Returning to the domain `C` of
finite/infinite binary
sequences (Example 4.4), Scott studies the element

`t = 0·merge(neg t, tail t)`,

the least fixed point of `Φ(x) = 0·merge(neg x, tail x)`, and (Lambek's
observation) identifies its
`n`-th digit with the parity of the binary digits of `n` — the **Thue–Morse
sequence**.

This module formalizes:

* **Step 0 — the element and its unfolding.** `tElt := Φ.fixElement` and
`tElt_unfold` proving
  `t = 0·merge(neg t, tail t)`.
* **The Thue–Morse morphism `expand`** (the substitution `0 ↦ 01`, `1 ↦ 10`) and
the key bridge
  `Phi_strBot_expand`: applied to a partial element `(0σ)⊥`, the operator `Φ` is
  exactly `expand`.
  Consequently the finite approximants of the least fixed point are `Φⁿ⁺¹(⊥) =
  (expandⁿ[0])⊥`
  (`iterElem_succ_eq`).
* **The parity bit-function `tm`** with `tm n = ⊕ (binary digits of n)` (via
`Nat.bits`), its
  recurrences `tm (2n) = tm n`, `tm (2n+1) = ¬ tm n`, and the bridge
  `expand_iterate_eq` showing the
  approximant strings are precisely the Thue–Morse parity prefixes `tmList (2ⁿ)`.
* **Property (a) — the digit characterization.** `tElt_mem_cone_iff`: a finite
string `σ` is a prefix
  of `t` **iff** `σ` is the length-`σ.length` Thue–Morse prefix (`σ = tmList
  σ.length`); and the
  digit reading `tElt_digit : (tmList n ++ [tm n])⊥ ≤ t`, i.e. the `n`-th digit of
  `t` is `tm n`,
  the parity of the binary digits of `n` (Lambek).

The `tElt` *data* is choice-free; the `Prop`-level digit facts may use
`Classical.choice` (through the
project's `eq_of_toElementMap_principal` and the truth-domain primitives), exactly
like the existing
uniqueness lemmas. Overlap-freeness (property (b)) is a self-contained
word-combinatorics theorem and
lives in its own module.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise516

open Domain.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-! ### The Thue–Morse morphism `expand` (`0 ↦ 01`, `1 ↦ 10`). -/

/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b
(¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ

/--
@isnad1 id=eq.0h0v.s2.3c5c1966c69a from=translated src=- shape=d3545b1f vocab=0b418272
-/
@[simp] theorem expand_nil : expand [] = [] := rfl

/--
@isnad1 id=eq.0h2v.s4.c9cbdf4a61a5 from=translated src=- shape=9f2a6311 vocab=b78e8f6a
-/
@[simp] theorem expand_cons (b : Bool) (σ : Str) : expand (b :: σ) = b :: (!b) :: expand σ := rfl

/-- `expand` distributes over append (it is a monoid morphism `Σ* → Σ*`).
@isnad1 id=eq.0h2v.s4.d31817fe70df from=translated src=- shape=a13ca989 vocab=d853a3ec
-/
theorem expand_append (σ τ : Str) : expand (σ ++ τ) = expand σ ++ expand τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

/-! ### `Φ` on a partial element computes by interleaving — and equals `expand`. -/

/-- The second (total/partial-flag) component of an interleaving with a partial
first input is
always
`false`: a partial input keeps the output partial.
@isnad1 id=eq.0h3v.s4.ac2c44ca4b0c from=translated src=- shape=eb269659 vocab=1c89d034
-/
theorem mergeVal_snd_false : ∀ (σ τ : Str) (b₁ : Bool), (mergeVal σ false τ b₁).2 = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: σ, _ :: τ, b₁ => by simp only [mergeVal_cons_cons]; exact mergeVal_snd_false σ τ b₁

/-- The interleaving of `h :: flip ρ` with `ρ` (both starting after a common head
`h`) is
`h :: expand ρ`. This is the heart of why `Φ` *is* the Thue–Morse morphism on the
trajectory.
@isnad1 id=eq.0h2v.s4.537002645fb3 from=translated src=- shape=89480e51 vocab=f373053d
-/
theorem weave_head : ∀ (h : Bool) (
  ρ : Str), (mergeVal (h :: flip ρ) false ρ false).1 = h :: expand ρ
  | h, [] => rfl
  | h, c :: ρ => by
    simp only [flip_cons, mergeVal_cons_cons, expand_cons]
    rw [weave_head (!c) ρ]

/-- **Exercise 5.16 (the operator `Φ`).** `Φ(x) = 0·merge(neg x, tail x)` as an
approximable map. -/
def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))

/-- The value of `Φ` on a partial element `σ⊥` is `(0 · weave σ)⊥`, the leading
`0` prepended to the
interleaving of `(flip σ)⊥` and `(tail σ)⊥`.
@isnad1 id=eq.0h1v.s4.8eb6866dfb4d from=translated src=- shape=56e76a19 vocab=1e45e2f4
-/
theorem tmOp_strBot (σ : Str) :
    tmOp.toElementMap (strBot σ)
      = strBot (false :: (mergeVal (flip σ) false σ.tail false).1) := by
  unfold tmOp
  rw [toElementMap_comp, toElementMap_comp, toElementMap_paired, negMap_strBot, tailMap_strBot,
    show (strBot (flip σ)) = shapeElem false (flip σ) from rfl,
    show (strBot σ.tail) = shapeElem false σ.tail from rfl, mergeMap_pair, mergeElem,
    mergeVal_snd_false, shapeElem_false, consMap_strBot]

/-- **The Thue–Morse trajectory.** On a partial element whose string starts with
`0`, `Φ` acts
as the
Thue–Morse morphism `expand`.
@isnad1 id=eq.0h1v.s4.2aba9677713c from=translated src=- shape=2c30104a vocab=fe820a0c
-/
theorem tmOp_strBot_expand (ρ : Str) :
    tmOp.toElementMap (strBot (false :: ρ)) = strBot (expand (false :: ρ)) := by
  rw [tmOp_strBot]
  simp only [flip_cons, List.tail_cons, expand_cons]
  rw [weave_head (!false) ρ]

/-! ### The finite approximants of the least fixed point are the morphism
iterates. -/

/-- The base of the iterated bottom element: `f⁰(⊥) = ⊥`.
@isnad1 id=eq.0h3v.s4.b343239158a0 from=translated src=- shape=5550e632 vocab=1ce62c39
-/
theorem iterElem_zero' {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) :
    f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

/-- A one-step unfolding of the iterated bottom element: `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`.
@isnad1 id=eq.0h4v.s5.fd24a0b1b6be from=translated src=- shape=c413e239 vocab=94acb20f
-/
theorem iterElem_succ {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate]
  exact Function.iterate_succ_apply' f.toElementMap n V.bot

/-- Every iterate of `expand` from `[0]` starts with `0` (so `Φ` keeps acting as
`expand`).
@isnad1 id=ex.0h1v.s4.93cd209c836c from=translated src=- shape=bbe0a257 vocab=257873ab
-/
theorem iterate_expand_cons (k : ℕ) : ∃ ρ, (expand^[k] [false] : Str) = false :: ρ := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨true :: expand ρ, by rw [Function.iterate_succ_apply', hρ]; rfl⟩

/-- `⊥ = []⊥` in `C` (the cone of `Λ` is the master).
@isnad1 id=eq.0h0v.s3.b42c90d46af1 from=translated src=- shape=c67ce00d vocab=4a6fe66b
-/
theorem strBot_nil : strBot [] = C.bot := by
  apply Element.ext
  intro Y
  rw [strBot, mem_principal, mem_bot, cone_nil, C_master]
  exact ⟨fun h => Set.Subset.antisymm (Set.subset_univ _) h.2,
    fun h => ⟨h ▸ C.master_mem, h ▸ Set.Subset.refl _⟩⟩

/-- **Exercise 5.16 (the approximants).** The `(k+1)`-st approximant of the least
fixed point is the
partial element of the `k`-fold Thue–Morse morphism iterate of `[0]`:
`Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`.
@isnad1 id=eq.0h1v.s5.dfd338994328 from=translated src=- shape=efd6ec1d vocab=52c49e91
-/
theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero', ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']

/-! ### The parity bit-function `tm` and its prefixes. -/

/-- The Thue–Morse bit-function: `tm n = ⊕(binary digits of n)`, the parity of the
number of `1`s in
the binary expansion of `n` (Lambek's description). -/
def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false

/--
@isnad1 id=eq.0h0v.s3.c7d81dad1650 from=translated src=- shape=d3a93718 vocab=e1219a8a
-/
@[simp] theorem tm_zero : tm 0 = false := by simp [tm, Nat.zero_bits]

/-- The even recurrence `tm (2n) = tm n` (appending a `0`-digit does not change
the parity).
@isnad1 id=eq.0h1v.s4.965ce37e5547 from=translated src=- shape=48d9f9ac vocab=1d8f55c9
-/
theorem tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · simp only [tm, Nat.bit0_bits n (by omega : n ≠ 0), List.foldr_cons, Bool.false_xor]

/-- The odd recurrence `tm (2n+1) = ¬ tm n` (appending a `1`-digit flips the
parity).
@isnad1 id=eq.0h1v.s5.6286b267f237 from=translated src=- shape=f53f1fde vocab=6243a85c
-/
theorem tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = !tm n := by
  simp only [tm, Nat.bit1_bits n, List.foldr_cons, Bool.true_xor]

/-- The length-`n` Thue–Morse prefix `[tm 0, tm 1, …, tm (n-1)]`. -/
def tmList (n : ℕ) : Str := (List.range n).map tm

/--
@isnad1 id=eq.0h0v.s3.40b02d116d72 from=translated src=- shape=04794901 vocab=5cfc84a8
-/
@[simp] theorem tmList_zero : tmList 0 = [] := rfl

/--
@isnad1 id=eq.0h1v.s5.bdd7e659dc2c from=translated src=- shape=519e44a4 vocab=da4c430e
-/
theorem tmList_succ (n : ℕ) : tmList (n + 1) = tmList n ++ [tm n] := by
  simp only [tmList, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/--
@isnad1 id=eq.0h1v.s3.ff995b56ec44 from=translated src=- shape=c3f7ecf6 vocab=8c29476f
-/
theorem tmList_length (n : ℕ) : (tmList n).length = n := by
  rw [tmList, List.length_map, List.length_range]

/-- Thue–Morse prefixes are nested in the prefix order.
@isnad1 id=isprefix.1h2v.s4.55388d6581cf from=translated src=- shape=992e8d55 vocab=bff38361
-/
theorem tmList_prefix {n m : ℕ} (h : n ≤ m) : tmList n <+: tmList m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (by rw [tmList_succ]; exact List.prefix_append _ _)
    · exact List.prefix_rfl

/-- **The morphism step on prefixes.** `expand (tmList m) = tmList (2m)`: applying
the Thue–Morse
morphism to a length-`m` prefix yields the length-`2m` prefix — this is exactly
the even/odd parity
recurrence in disguise.
@isnad1 id=eq.0h1v.s4.63723ae19b82 from=translated src=- shape=ec20e67d vocab=58f6e480
-/
theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]

/-- **The bridge.** The `k`-fold morphism iterate of `[0]` is the Thue–Morse
parity prefix of length
`2ᵏ`: `expandᵏ[0] = tmList (2ᵏ)`.
@isnad1 id=eq.0h1v.s5.27d283420d1f from=translated src=- shape=1e1e0703 vocab=e295549f
-/
theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]

/-! ### Step 0 — the element `t` and its unfolding. -/

/-- **Exercise 5.16 (Scott 1981, PRG-19).** Scott's Thue–Morse element `t =
0·merge(neg t, tail t)`,
the least fixed point of `Φ`. -/
def tElt : C.Element := tmOp.fixElement

/-- **Exercise 5.16 — the defining unfolding.** `t = 0·merge(neg t, tail t)`.
@isnad1 id=eq.0h0v.s5.600e47b1b5c6 from=translated src=- shape=49b33011 vocab=3b82ae24
-/
theorem tElt_unfold :
    (consMap false).toElementMap
        (mergeMap.toElementMap (pair (negMap.toElementMap tElt) (tailMap.toElementMap tElt)))
      = tElt := by
  have h := toElementMap_fixElement tmOp
  rw [tmOp, toElementMap_comp, toElementMap_comp, toElementMap_paired] at h
  exact h

/-! ### Property (a) — the digit characterization. -/

/-- `(strBot τ)` has the cone of `σ` as a neighbourhood iff `σ` is a prefix of
`τ`.
@isnad1 id=iff.0h2v.s4.78b66c05d27c from=translated src=- shape=d8dc0791 vocab=9e601845
-/
theorem strBot_mem_cone {σ τ : Str} : (strBot τ).mem (cone σ) ↔ σ <+: τ := by
  rw [strBot, mem_principal]
  exact ⟨fun h => cone_subset_cone.mp h.2, fun h => ⟨memC_cone σ, cone_subset_cone.mpr h⟩⟩

/-- `σΣ* = Σ*` iff `σ = Λ`.
@isnad1 id=iff.0h1v.s3.c123471465be from=translated src=- shape=f050a2c4 vocab=10b488b1
-/
theorem cone_univ_iff {σ : Str} : cone σ = Set.univ ↔ σ = [] := by
  constructor
  · intro h
    exact List.prefix_nil.mp (mem_cone.mp (h ▸ Set.mem_univ ([] : Str)))
  · rintro rfl; exact cone_nil

/-- Each approximant is below the least fixed point.
@isnad1 id=le.0h4v.s5.0c4dcf93af72 from=translated src=- shape=0e372d7f vocab=79841113
-/
theorem iterElem_le_fixElement {α : Type*} {V : NeighborhoodSystem α} (f : ApproximableMap V V)
    (n : ℕ) : f.iterElem n ≤ f.fixElement := by
  rw [f.fixElement_eq_iSupDirected]
  intro Z hZ
  rw [mem_iSupDirected]
  exact ⟨n, hZ⟩

/-- **Property (a), prefix form.** Every Thue–Morse parity prefix is a prefix of
`t`:
`(tmList n)⊥ ⊑ t` for all `n`.
@isnad1 id=le.0h1v.s4.2cbd60f0e296 from=translated src=- shape=833408d1 vocab=f856def6
-/
theorem tmList_le_tElt (n : ℕ) : strBot (tmList n) ≤ tElt := by
  have hpre : tmList n <+: expand^[n] [false] := by
    rw [expand_iterate_eq]; exact tmList_prefix (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc strBot (tmList n) ≤ strBot (expand^[n] [false]) :=
        strBot_le_strBot_iff.mpr hpre
    _ = tmOp.iterElem (n + 1) := (iterElem_succ_eq n).symm
    _ ≤ tElt := iterElem_le_fixElement tmOp (n + 1)

/-- **Property (a) (Scott 1981, PRG-19; Lambek).** The finite-prefix
characterization of `t`: a
string `σ` is a prefix of `t` **iff** it is the length-`σ.length` Thue–Morse
parity prefix. Reading
off position `n`, the `n`-th digit of `t` is `tm n`, the parity of the binary
digits of `n`.
@isnad1 id=iff.0h1v.s4.a2798988dbd7 from=translated src=- shape=9ca1bb99 vocab=6a4ca4b8
-/
theorem tElt_mem_cone_iff (σ : Str) : tElt.mem (cone σ) ↔ σ = tmList σ.length := by
  constructor
  · intro hσ
    rw [show tElt = tmOp.fixElement from rfl, tmOp.fixElement_eq_iSupDirected,
      mem_iSupDirected] at hσ
    obtain ⟨n, hn⟩ := hσ
    -- `σ` is a prefix of some Thue–Morse prefix `tmList N`.
    obtain ⟨N, hpre⟩ : ∃ N, σ <+: tmList N := by
      cases n with
      | zero =>
        rw [iterElem_zero', mem_bot, C_master, cone_univ_iff] at hn
        exact ⟨0, by rw [hn]; exact List.nil_prefix⟩
      | succ k =>
        rw [iterElem_succ_eq, strBot_mem_cone, expand_iterate_eq] at hn
        exact ⟨2 ^ k, hn⟩
    -- Both `σ` and `tmList σ.length` are the length-`σ.length` prefix of `tmList
    -- N`.
    have hlen : σ.length ≤ N := hpre.length_le.trans_eq (tmList_length _)
    have h1 : σ = (tmList N).take σ.length := List.prefix_iff_eq_take.mp hpre
    have h2 : tmList σ.length = (tmList N).take σ.length := by
      have := List.prefix_iff_eq_take.mp (tmList_prefix hlen)
      rwa [tmList_length] at this
    exact h1.trans h2.symm
  · intro hσ
    have h := tmList_le_tElt σ.length
    have hmem : (strBot (tmList σ.length)).mem (cone σ) :=
      strBot_mem_cone.mpr (hσ ▸ List.prefix_rfl)
    exact h _ hmem

/-- **Property (a), digit form.** The `n`-th digit of `t` is `tm n` (the parity of
the binary digits
of `n`): the length-`(n+1)` prefix of `t` is `tmList n ++ [tm n]`.
@isnad1 id=le.0h1v.s5.7c6f2dbdae71 from=translated src=- shape=5656550d vocab=4ff25d4e
-/
theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h

end Domain.Neighborhood.Exercise516

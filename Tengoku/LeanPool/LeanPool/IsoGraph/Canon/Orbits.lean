/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.IsoGraph.Canon.Algorithm
import Tengoku.LeanPool.LeanPool.IsoGraph.ForMathlib.Array

/-!
# Orbit closure

`dfsChildren` skips a child that is marked in `orb.mark`, the set of children in the orbit of the
already-processed ones under the automorphisms fixing the node's path.  This file proves the one
fact that makes the skip legitimate: everything the closure marks is reachable from a seed by the
generators, in the form

* `orbitClosure_P` / `closureLoop_P` — if a predicate `P` holds on the seeds and is closed under
  the generators, then it holds on everything marked.

Instantiated with `P w := "the subtree below the child w is dominated"` and combined with
`Autos.reach_child_auto`, this says that skipping a marked child loses no leaf key.
-/

@[expose] public section

namespace IsoGraph
namespace Canon

/-! ### Orbit closure -/

variable {P : Nat → Prop}

/-- `mark` only ever flags points satisfying `P`. -/
def MarkP (P : Nat → Prop) (mark : Array Bool) : Prop := ∀ w, mark[w]! = true → P w

/-- Every entry of the frontier satisfies `P`. -/
def StackP (P : Nat → Prop) (stack : Array Nat) : Prop := ∀ i, i < stack.size → P stack[i]!

/--
@isnad1 id=markp.1h4v.s4.0976392247e5 from=translated src=- shape=20b198a8 vocab=766730ce
-/
theorem markP_set {mark : Array Bool} {w : Nat} (hm : MarkP P mark) (hw : P w) :
    MarkP P (mark.set! w true) := by
  intro x hx
  by_cases hxw : x = w
  · exact hxw ▸ hw
  · exact hm x (by rwa [getElemD_setD_ne hxw] at hx)

/--
@isnad1 id=stackp.1h4v.s4.f7acd71f2b68 from=translated src=- shape=35fd9577 vocab=558bb742
-/
theorem stackP_push {stack : Array Nat} {w : Nat} (hs : StackP P stack) (hw : P w) :
    StackP P (stack.push w) := by
  intro i hi
  rw [Array.size_push] at hi
  rcases Nat.lt_or_ge i stack.size with h1 | h1
  · rw [push_getElemD_lt stack w h1]; exact hs i h1
  · have : i = stack.size := by omega
    subst this
    rw [push_getElemD_eq]; exact hw

/--
@isnad1 id=stackp.1h2v.s4.9bac8c8cedf1 from=translated src=- shape=2d0da11f vocab=ddb4689e
-/
theorem stackP_pop {stack : Array Nat} (hs : StackP P stack) : StackP P stack.pop := by
  intro i hi
  rw [Array.size_pop] at hi
  have h1 : i < stack.size := by omega
  rw [getElem!_pos stack.pop i (by rw [Array.size_pop]; omega), Array.getElem_pop,
    ← getElem!_pos stack i h1]
  exact hs i h1

/--
@isnad1 id=and.2h6v.s8.a2ff84a6b64e from=translated src=- shape=69a8a1ba vocab=f2624674
-/
theorem closure_foldl_P {v : Nat} (hv : P v) :
    ∀ (l : List (Array Nat)) (ms : Array Bool × Array Nat), (∀ g ∈ l, P g[v]!) →
      MarkP P ms.1 → StackP P ms.2 →
      MarkP P (l.foldl (fun ms g =>
          let w := g[v]!
          if !ms.1[w]! then (ms.1.set! w true, ms.2.push w) else ms) ms).1
        ∧ StackP P (l.foldl (fun ms g =>
          let w := g[v]!
          if !ms.1[w]! then (ms.1.set! w true, ms.2.push w) else ms) ms).2
  | [], ms, _, hm, hs => ⟨hm, hs⟩
  | g :: l, ms, hgen, hm, hs => by
    rw [List.foldl_cons]
    refine closure_foldl_P hv l _ (fun g' hg' => hgen g' (List.mem_cons_of_mem _ hg')) ?_ ?_
    · dsimp only; split
      · exact markP_set hm (hgen g List.mem_cons_self)
      · exact hm
    · dsimp only; split
      · exact stackP_push hs (hgen g List.mem_cons_self)
      · exact hs

/-- **One closure step keeps the invariant.**  If `P` is closed under the generators, marking the
images of a point satisfying `P` only ever marks points satisfying `P`.
@isnad1 id=and.2h7v.s6.2c77609b03f4 from=translated src=- shape=89811ab5 vocab=ffd86181
-/
theorem closureStep_P {gens : Array (Array Nat)} {mark : Array Bool} {stack : Array Nat} {v : Nat}
    (hgen : ∀ g ∈ gens, ∀ w, P w → P g[w]!) (hm : MarkP P mark) (hs : StackP P stack) (hv : P v) :
    MarkP P (closureStep gens mark stack v).1 ∧ StackP P (closureStep gens mark stack v).2 := by
  rw [closureStep, ← Array.foldl_toList]
  exact closure_foldl_P hv gens.toList (mark, stack)
    (fun g hg => hgen g (by simpa using hg) v hv) hm hs

/-- **The closure loop keeps the invariant.**
@isnad1 id=markp.2h6v.s6.f31df1845522 from=translated src=- shape=ee741966 vocab=0186ac02
-/
theorem closureLoop_P {gens : Array (Array Nat)}
    (hgen : ∀ g ∈ gens, ∀ w, P w → P g[w]!) :
    ∀ (fuel : Nat) (mark : Array Bool) (stack : Array Nat), MarkP P mark → StackP P stack →
      MarkP P (closureLoop gens fuel mark stack)
  | 0, _, _, hm, _ => hm
  | fuel + 1, mark, stack, hm, hs => by
    rw [closureLoop]
    by_cases he : stack.isEmpty = true
    · simpa [he] using hm
    · have hne : stack.size ≠ 0 := by
        intro h; exact he (by simp [Array.isEmpty, h])
      have hv : P stack[stack.size - 1]! := hs _ (by omega)
      have := closureStep_P hgen hm (stackP_pop hs) hv
      simpa [he] using closureLoop_P hgen fuel _ _ this.1 this.2

/--
@isnad1 id=markp.0h2v.s3.79146fab4026 from=translated src=- shape=39119729 vocab=5c9a626b
-/
theorem markP_replicate {n : Nat} : MarkP P (Array.replicate n false) := by
  intro w hw
  by_cases h : w < n
  · rw [getElem!_pos (Array.replicate n false) w (by simpa using h)] at hw; simp at hw
  · rw [getElem!_neg (Array.replicate n false) w (by simpa using h)] at hw
    exact absurd hw (by simp)

/--
@isnad1 id=markp.1h4v.s5.e57f3b711cde from=translated src=- shape=2030038a vocab=497b5407
-/
theorem markP_seed_foldl :
    ∀ (l : List Nat) (mark : Array Bool), (∀ v ∈ l, P v) → MarkP P mark →
      MarkP P (l.foldl (fun mark v => mark.set! v true) mark)
  | [], _, _, hm => hm
  | v :: l, mark, hl, hm => by
    rw [List.foldl_cons]
    exact markP_seed_foldl l _ (fun w hw => hl w (List.mem_cons_of_mem _ hw))
      (markP_set hm (hl v List.mem_cons_self))

/-- **Orbit closure is sound.**  Everything `orbitClosure` marks satisfies any predicate that
holds on the seeds and is closed under the generators.  Instantiated with "the subtree below this
child is dominated", this is exactly what makes orbit pruning legitimate.
@isnad1 id=markp.0h6v.s6.30393a25f329 from=translated src=- shape=19e490c8 vocab=9fa34bca
-/
theorem orbitClosure_P {n : Nat} {gens : Array (Array Nat)} {seed : Array Nat}
    (hgen : ∀ g ∈ gens, ∀ w, P w → P g[w]!) (hseed : ∀ v ∈ seed, P v) :
    MarkP P (orbitClosure n gens seed) := by
  rw [orbitClosure]
  refine closureLoop_P hgen _ _ _ ?_ (fun i hi => hseed _ (getElemD_mem hi))
  rw [← Array.foldl_toList]
  exact markP_seed_foldl seed.toList _ (fun v hv => hseed v (by simpa using hv)) markP_replicate

end Canon
end IsoGraph

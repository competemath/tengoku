/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.SquareMesh
public import Tengoku.LeanPool.LeanPool.Schoenflies.JordanClosed

/-!
# The local windows `W_n(p)` of the stage recursion

The paragraph of `jordan_schoenflies.tex` between `thm:finite-transfer` and
`prop:local-grid-attachment` fixes, for each `p ∈ D` and each `n`,

```
r(p)   = dist_∞(p, C),
s_n(p) = r(p) - min(r(p)/2, ε_n),
W_n(p) = { x : ‖x - p‖_∞ ≤ s_n(p) },
```

and records `0 < s_n(p) < r(p)`, `r(p) - s_n(p) ≤ ε_n`, and `W_n(p) ⊆ D`. Those four lines and
the arithmetic that `prop:shrinking-stars` performs on them are all this module contains. It is
entirely metric: no cell structure, no graph, nothing from Part II. That is deliberate — the
window bookkeeping is the one part of the quantitative refinement that can be finished before
the recursion it serves exists, and getting the constants wrong later, inside a proof that also
has to manage cellulations, is expensive.

## Why an ℓ^∞ distance-to-a-set had to be built

`Plane` carries the Euclidean metric, so `Metric.infDist` is the *Euclidean* distance to a set
and `Schoenflies.Plane.supDist` is a bare two-argument function with no set version.
`Schoenflies.supRadius` is the ℓ^∞ distance to a compact set, defined as the infimum of the
attained values. Everything the blueprint uses of it is here: it is attained
(`exists_supRadius_eq`), it is positive off the set (`supRadius_pos`), it is 1-Lipschitz in the
ℓ^∞ metric (`supRadius_le_add`, `abs_supRadius_sub_le`) — *"the distance-to-`C` function is
1-Lipschitz in the ℓ^∞ metric"* — and the open ℓ^∞ ball of radius `r(p)` about a point of the
Jordan domain lies in the Jordan domain (`openSquare_supRadius_subset_inside`), which is the
blueprint's *"since `C = ∂D`, the open axis-parallel square of radius `r(p)` centred at `p`
lies in `D`"*.

The last one is not proved through `C = ∂D` but through the component characterisation: the
square is convex, hence connected, and misses `C` by the very definition of `r(p)`, so it lies
in the connected component of `Cᶜ` containing `p` — which is `inside C` by `thm:jordan`.

## What `prop:shrinking-stars` extracts from this

`Schoenflies.mem_openWindow_of_supDist_lt` is the whole first half of that proof's arithmetic,
with the blueprint's constants:

> Fix `x ∈ D` and put `d = dist_∞(x, C) > 0`. Choose `b ∈ B` with `‖b - x‖_∞ < d/8` … Since
> `r(·)` is 1-Lipschitz, `r(b) ≥ r(x) - ‖b - x‖_∞ > 7d/8`. Consequently
> `s_n(b) ≥ r(b) - ε_n > 3d/4`. Because `‖b - x‖_∞ < d/8`, the point `x` lies in the interior
> of `W_n(b)`.

Nothing here mentions the enumeration `b_1, b_2, …` of `B = ℚ² ∩ D` or the sequence
`ε_n = 2^{-n}`; `windowRadius` takes `ε` as a parameter, so the recursion may pick the sequence.
`Schoenflies.exists_mem_rat_supDist_lt` is the one fact about `B` the proof uses — that a dense
subset of the plane supplies a `b` as close to `x` as asked, inside `D`.

## Blueprint

* `Schoenflies.supRadius`, `.exists_supRadius_eq`, `.supRadius_le`, `.supRadius_nonneg`,
  `.supRadius_pos`, `.notMem_of_supDist_lt_supRadius` — `r(p) = dist_∞(p, C)`.
* `Schoenflies.supRadius_le_add`, `.abs_supRadius_sub_le` — *"the distance-to-`C` function is
  1-Lipschitz in the ℓ^∞ metric"*.
* `Schoenflies.openSquare_supRadius_subset_inside` — *"since `C = ∂D`, the open axis-parallel
  square of radius `r(p)` centred at `p` lies in `D`"*.
* `Schoenflies.windowRadius`, `Schoenflies.window`, `Schoenflies.openWindow` — `s_n(p)`,
  `W_n(p)`, and its interior.
* `Schoenflies.windowRadius_pos`, `.windowRadius_lt_supRadius`, `.sub_windowRadius_le`,
  `.window_subset_inside` — the three displayed inequalities and `W_n(p) ⊆ D`.
* `Schoenflies.mem_openWindow_of_supDist_lt` — the arithmetic of `prop:shrinking-stars`.
* `Schoenflies.exists_mem_rat_supDist_lt` — the only property of `B = ℚ² ∩ D` used.
* `Schoenflies.recur`, `.exists_le_recur_eq` — *"a sequence in which every point of `B` occurs
  infinitely often"*, and the consequence `prop:shrinking-stars` uses.
* `Schoenflies.tendsto_two_pow_neg`, `.two_pow_neg_pos` — `ε_n = 2^{-n}`.
-/

@[expose] public section

open Filter Metric Set

namespace Schoenflies

variable {C U : Set Plane} {p q x b : Plane} {r ε δ : ℝ}

/-! ### One missing fact about `supDist`

`Schoenflies/Square.lean` has the ℓ^∞ norm, the ℓ^∞ distance, the triangle inequality and the
two comparisons with the Euclidean norm, but not that `supDist` separates points. It is needed
once below, to see that `r(p) > 0` off a compact set. **It belongs in `Square.lean`**; it is
here because this is its first use. -/

/-- The ℓ^∞ distance separates points. -/
theorem Plane.eq_of_supDist_eq_zero (h : Plane.supDist p q = 0) : p = q := by
  have hle : ‖p - q‖ ≤ Real.sqrt 2 * Plane.supNorm (p - q) := Plane.norm_le_sqrt_two_mul_supNorm _
  rw [show Plane.supNorm (p - q) = Plane.supDist p q from rfl, h, mul_zero] at hle
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hle (norm_nonneg _)))

/-! ### The ℓ^∞ distance to a compact set -/

/-- **`r(p) = dist_∞(p, C)`**, the ℓ^∞ distance from a point to a set.

Defined as the infimum of the attained values rather than through `Metric.infDist`, which is
the *Euclidean* distance: `Plane` carries the Euclidean metric and the blueprint's windows are
axis-parallel squares. On a compact nonempty set the infimum is attained
(`exists_supRadius_eq`), which is all that is ever used. -/
noncomputable def supRadius (C : Set Plane) (p : Plane) : ℝ := sInf (Plane.supDist p '' C)

/--
@isnad1 id=continuo.0h1v.s5.ae5e539acf11 from=translated src=- shape=9bb0b988 vocab=4653e56f
-/
theorem supDist_continuousOn (p : Plane) : Continuous (Plane.supDist p) :=
  continuous_supNorm.comp (continuous_const.sub continuous_id)

/-- The ℓ^∞ distance to a nonempty compact set is attained.
@isnad1 id=ex.2h2v.s6.4f752e7914d3 from=translated src=- shape=81c4c83e vocab=87588882
-/
theorem exists_supRadius_eq (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) :
    ∃ q ∈ C, supRadius C p = Plane.supDist p q ∧
      ∀ z ∈ C, Plane.supDist p q ≤ Plane.supDist p z := by
  obtain ⟨q, hqC, hmin⟩ := hC.exists_isMinOn hCne (supDist_continuousOn p).continuousOn
  have hle : ∀ z ∈ C, Plane.supDist p q ≤ Plane.supDist p z := fun z hz => isMinOn_iff.1 hmin z hz
  refine ⟨q, hqC, ?_, hle⟩
  refine IsLeast.csInf_eq ⟨⟨q, hqC, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hle z hz

/-- Every point of the set is at least `r(p)` away, in the ℓ^∞ metric.
@isnad1 id=le.3h3v.s6.3cc350b985cb from=translated src=- shape=856bf4e3 vocab=87588882
-/
theorem supRadius_le (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) (hq : q ∈ C) :
    supRadius C p ≤ Plane.supDist p q := by
  obtain ⟨z, -, heq, hmin⟩ := exists_supRadius_eq hC hCne p
  rw [heq]; exact hmin q hq

/--
@isnad1 id=le.2h2v.s6.0c7dff28bbbf from=translated src=- shape=cea29c39 vocab=d0d35e89
-/
theorem supRadius_nonneg (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) :
    0 ≤ supRadius C p := by
  obtain ⟨z, -, heq, -⟩ := exists_supRadius_eq hC hCne p
  rw [heq]; exact Plane.supDist_nonneg _ _

/-- Off a compact set the ℓ^∞ distance to it is positive.
@isnad1 id=lt.3h2v.s6.53700ff6cc15 from=translated src=- shape=75c76db5 vocab=bbdff680
-/
theorem supRadius_pos (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C) :
    0 < supRadius C p := by
  obtain ⟨q, hqC, heq, -⟩ := exists_supRadius_eq hC hCne p
  rw [heq]
  rcases (Plane.supDist_nonneg p q).lt_or_eq with h | h
  · exact h
  · exact absurd (Plane.eq_of_supDist_eq_zero h.symm ▸ hqC) hp

/-- A point strictly nearer than `r(p)` is off the set: this is the definition read backwards,
and it is what makes the window miss `C`.
@isnad1 id=not.3h3v.s6.3c16be0d6dcc from=translated src=- shape=ed3a18e1 vocab=da4bd19f
-/
theorem notMem_of_supDist_lt_supRadius (hC : IsCompact C) (hCne : C.Nonempty)
    (h : Plane.supDist x p < supRadius C p) : x ∉ C := by
  intro hx
  exact absurd (supRadius_le hC hCne p hx) (not_le.2 (by rwa [Plane.supDist_comm p x]))

/-! ### 1-Lipschitz

*"The distance-to-`C` function is 1-Lipschitz in the ℓ^∞ metric."* Only the one-sided form is
used — `r(b) ≥ r(x) - ‖b - x‖_∞` — but both are recorded. -/

/-- `r(p) ≤ r(q) + ‖p - q‖_∞`.
@isnad1 id=le.2h3v.s6.1198809c0cfe from=translated src=- shape=08c556af vocab=b8ccb9af
-/
theorem supRadius_le_add (hC : IsCompact C) (hCne : C.Nonempty) (p q : Plane) :
    supRadius C p ≤ supRadius C q + Plane.supDist p q := by
  obtain ⟨z, hzC, heq, -⟩ := exists_supRadius_eq hC hCne q
  refine (supRadius_le hC hCne p hzC).trans ?_
  rw [heq, add_comm]
  exact Plane.supDist_triangle p q z

/-- The 1-Lipschitz property in its symmetric form.
@isnad1 id=le.2h3v.s6.45df6eeb19af from=translated src=- shape=11f626bf vocab=1003333a
-/
theorem abs_supRadius_sub_le (hC : IsCompact C) (hCne : C.Nonempty) (p q : Plane) :
    |supRadius C p - supRadius C q| ≤ Plane.supDist p q := by
  rw [abs_sub_le_iff]
  refine ⟨by linarith [supRadius_le_add hC hCne p q], ?_⟩
  have := supRadius_le_add hC hCne q p
  rw [Plane.supDist_comm q p] at this
  linarith

/-! ### The square of radius `r(p)` lies in the domain -/

/-- **"The open axis-parallel square of radius `r(p)` centred at `p` lies in `D`."** The square
is convex, hence connected; it misses `C` because every one of its points is nearer to `p` than
`r(p)`; and it contains `p`. So it lies in the connected component of `Cᶜ` through `p`, which
is `inside C` by `thm:jordan`.
@isnad1 id=le.4h2v.s6.2acaf86e71f1 from=translated src=- shape=184fd59f vocab=a32ec96f
-/
theorem openSquare_supRadius_subset_inside (hC : IsCompact C) (hCne : C.Nonempty)
    (hsep : IsSeparating C) (hp : p ∈ inside C) :
    Plane.openSquare p (supRadius C p) ⊆ inside C := by
  have hmiss : Plane.openSquare p (supRadius C p) ⊆ Cᶜ := fun x hx =>
    notMem_of_supDist_lt_supRadius hC hCne hx
  have hmem : p ∈ Plane.openSquare p (supRadius C p) := by
    have hpC : p ∉ C := fun h => (inside_subset_compl hp) h
    simpa [Plane.openSquare, Plane.supDist_self] using supRadius_pos hC hCne hpC
  have := (Plane.convex_openSquare p (supRadius C p)).isPreconnected.subset_connectedComponentIn
    hmem hmiss
  rwa [hsep.connectedComponentIn_eq_inside hp] at this

/-! ### The windows

`windowRadius ε p` is the blueprint's `s_n(p)` with `ε_n` a parameter: the recursion chooses the
sequence, and nothing here needs to know that it is `2^{-n}`. -/

/-- **`s_n(p) = r(p) - min(r(p)/2, ε_n)`.** -/
noncomputable def windowRadius (C : Set Plane) (ε : ℝ) (p : Plane) : ℝ :=
  supRadius C p - min (supRadius C p / 2) ε

/-- **`W_n(p)`**, the closed window. -/
noncomputable def window (C : Set Plane) (ε : ℝ) (p : Plane) : Set Plane :=
  Plane.closedSquare p (windowRadius C ε p)

/-- The interior of the window, which is where `lem:grid-star-estimate` places its point. -/
noncomputable def openWindow (C : Set Plane) (ε : ℝ) (p : Plane) : Set Plane :=
  Plane.openSquare p (windowRadius C ε p)

/-- **`0 < s_n(p)`.**
@isnad1 id=lt.3h3v.s6.fd21e8b9f467 from=translated src=- shape=486bbb4d vocab=bf55cd2d
-/
theorem windowRadius_pos (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C) :
    0 < windowRadius C ε p := by
  have hr := supRadius_pos hC hCne hp
  have : min (supRadius C p / 2) ε ≤ supRadius C p / 2 := min_le_left _ _
  rw [windowRadius]; linarith

/-- **`s_n(p) < r(p)`.**
@isnad1 id=lt.4h3v.s6.d76945f98287 from=translated src=- shape=70985841 vocab=2e1f68dd
-/
theorem windowRadius_lt_supRadius (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C)
    (hε : 0 < ε) : windowRadius C ε p < supRadius C p := by
  have hr := supRadius_pos hC hCne hp
  have : 0 < min (supRadius C p / 2) ε := lt_min (by linarith) hε
  rw [windowRadius]; linarith

/-- **`r(p) - s_n(p) ≤ ε_n`.**
@isnad1 id=le.0h3v.s4.22c47b4ffbe9 from=translated src=- shape=cb1fa9c8 vocab=adbb7093
-/
theorem sub_windowRadius_le (C : Set Plane) (ε : ℝ) (p : Plane) :
    supRadius C p - windowRadius C ε p ≤ ε := by
  rw [windowRadius]
  simp

/-- The lower bound `s_n(p) ≥ r(p) - ε_n`, which is the form `prop:shrinking-stars` uses.
@isnad1 id=le.0h3v.s4.0197c3363ff1 from=translated src=- shape=17c8c4a4 vocab=adbb7093
-/
theorem le_windowRadius (C : Set Plane) (ε : ℝ) (p : Plane) :
    supRadius C p - ε ≤ windowRadius C ε p := by
  have := sub_windowRadius_le C ε p; linarith

/-- **`W_n(p) ⊆ D`**: the closed window sits strictly inside the square of radius `r(p)`.
@isnad1 id=le.5h3v.s6.8739a931daa9 from=translated src=- shape=5c4a7f0d vocab=8898a402
-/
theorem window_subset_inside (hC : IsCompact C) (hCne : C.Nonempty) (hsep : IsSeparating C)
    (hp : p ∈ inside C) (hε : 0 < ε) : window C ε p ⊆ inside C := by
  have hpC : p ∉ C := fun h => (inside_subset_compl hp) h
  refine subset_trans (fun x hx => ?_) (openSquare_supRadius_subset_inside hC hCne hsep hp)
  exact lt_of_le_of_lt hx (windowRadius_lt_supRadius hC hCne hpC hε)

/-! ### The arithmetic of `prop:shrinking-stars` -/

/-- **The window-catching estimate.** If `b` is within `d/8` of `x` in the ℓ^∞ metric and the
mesh parameter `ε` is below `d/8`, where `d = dist_∞(x, C)`, then `x` lies in the *interior* of
the window `W(b)`.

This is the displayed chain of the proof of `prop:shrinking-stars`: `r(b) > 7d/8` by
1-Lipschitzness, hence `s(b) ≥ r(b) - ε > 3d/4`, and `‖b - x‖_∞ < d/8 < 3d/4`.
@isnad1 id=mem.4h4v.s6.6e513c76a7b8 from=translated src=- shape=0eca746c vocab=7b633f6f
-/
theorem mem_openWindow_of_supDist_lt (hC : IsCompact C) (hCne : C.Nonempty)
    (hbx : Plane.supDist b x < supRadius C x / 8) (hε : ε < supRadius C x / 8) :
    x ∈ openWindow C ε b := by
  set d := supRadius C x with hd
  -- `r(b) ≥ r(x) - ‖b - x‖_∞ > 7d/8`.
  have hlip : d ≤ supRadius C b + Plane.supDist x b := supRadius_le_add hC hCne x b
  rw [Plane.supDist_comm x b] at hlip
  have hrb : 7 * d / 8 < supRadius C b := by linarith
  -- `s(b) ≥ r(b) - ε > 7d/8 - d/8 = 3d/4`.
  have hsb : 3 * d / 4 < windowRadius C ε b :=
    lt_of_lt_of_le (by linarith) (le_windowRadius C ε b)
  -- and `x` is within `d/8` of `b`.
  have hxb : Plane.supDist x b < d / 8 := by rwa [Plane.supDist_comm x b]
  have hdpos : 0 < d := by linarith [Plane.supDist_nonneg b x]
  exact lt_trans hxb (by linarith)

/-! ### The two sequences the recursion fixes

*"Choose a sequence `b_1, b_2, …` in which every point of `B` occurs infinitely often, and put
`ε_n = 2^{-n}`."* Both are here, each with the one property `prop:shrinking-stars` uses: every
value of the enumeration recurs at arbitrarily large indices, and the mesh sequence is null. -/

/-- **An enumeration in which every value of `f` occurs infinitely often.** Cantor pairing, read
off the first component: the value `f k` reappears at `Nat.pair k m` for every `m`. -/
def recur {α : Type*} (f : ℕ → α) (n : ℕ) : α := f (Nat.unpair n).1

/-- **"The point `b` occurs at arbitrarily large indices."** This is the step of
`prop:shrinking-stars` that lets the mesh parameter be taken as small as the point requires: the
window centre is fixed first, and only then is a late enough stage chosen.
@isnad1 id=ex.0h4v.s4.bf2919e864f2 from=translated src=- shape=4e1d8ae9 vocab=b734a6db
-/
theorem exists_le_recur_eq {α : Type*} (f : ℕ → α) (k N : ℕ) :
    ∃ n, N ≤ n ∧ recur f n = f k :=
  ⟨Nat.pair k N, Nat.right_le_pair k N, by rw [recur, Nat.unpair_pair]⟩

/-- **`ε_n = 2^{-n}` is a null sequence.**
@isnad1 id=tendsto.0h0v.s5.51ee72e0df92 from=translated src=- shape=295419fc vocab=5034efeb
-/
theorem tendsto_two_pow_neg :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))

/--
@isnad1 id=lt.0h1v.s5.f48bdbdbe581 from=translated src=- shape=75b92053 vocab=346282d9
-/
theorem two_pow_neg_pos (n : ℕ) : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity

/-- The only property of `B = ℚ² ∩ D` that `prop:shrinking-stars` uses: an open set contains
points of a dense subset of the plane as close to any of its points as asked.
@isnad1 id=ex.4h4v.s7.e9e5ab18fd1f from=translated src=- shape=4bf000d9 vocab=882480f4
-/
theorem exists_mem_rat_supDist_lt {B : Set Plane} (hB : Dense B) (hU : IsOpen U)
    (hx : x ∈ U) (hδ : 0 < δ) : ∃ b ∈ B, b ∈ U ∧ Plane.supDist b x < δ := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨b, hbB, hbmem⟩ :=
    hB.exists_mem_open Metric.isOpen_ball ⟨x, mem_ball_self (lt_min hρ hδ)⟩
  refine ⟨b, hbB, hball (ball_subset_ball (min_le_left _ _) hbmem), ?_⟩
  refine lt_of_le_of_lt (Plane.supNorm_le_norm _) ?_
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le (mem_ball.1 hbmem) (min_le_right _ _)

end Schoenflies

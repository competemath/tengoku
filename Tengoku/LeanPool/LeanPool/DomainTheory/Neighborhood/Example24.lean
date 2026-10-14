/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Approximable
public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.ExampleB
public import Tengoku

/-!
# Example 2.4 (Scott 1981, PRG-19, §2) — eliminating the first run of `1`'s, `g :
B → B`

Scott's second approximable mapping reads a binary sequence left to right and
"eliminates the first
consecutive run of `1`'s while copying all the other digits." Thus

`g(0ⁿ 1ᵏ 0 x) = 0ⁿ⁺¹ x`   (for `k > 0`),   `g(1^∞) = ⊥`,   `g(0ⁿ 1^∞) = 0ⁿ`.

It is instructive because it turns *total* inputs (e.g. `1^∞`) into *partial*
outputs.

We give the **guaranteed finite output** `out : Σ* → Σ*` for each finite input
prefix via a two-state
scan: `out` copies leading `0`'s and, on the first `1`, hands over to `del`, which
swallows the run
of `1`'s and — on the terminating `0` — emits that single `0` and copies the rest
verbatim. The
elementwise value on the finite element `↑(σΣ*)` is `↑((out σ)Σ*)`, so the
neighbourhood relation is

`X g Y ↔ ∃ σ, X = σΣ* ∧ (out σ)Σ* ⊆ Y ∧ Y ∈ B`.

`out` is prefix-monotone (`out_mono`: `σ <+: σ' → out σ <+: out σ'`), which gives
Definition
2.1(iii); (i) and (ii) are the principal-filter facts for the cone `(out σ)Σ*`.
Constructive. -/

@[expose] public section

namespace Domain.Neighborhood.Example24

open Domain.Neighborhood NeighborhoodSystem ExampleB

/-- Inside the first run of `1`'s: swallow `1`'s; on the first `0`, emit it and
copy the rest. -/
def del : Str → Str
  | [] => []
  | true :: t => del t
  | false :: t => false :: t

/--
@isnad1 id=eq.0h0v.s2.557af4ee456e from=translated src=- shape=d3545b1f vocab=6a68a6a3
-/
@[simp] theorem del_nil : del [] = [] := rfl
/--
@isnad1 id=eq.0h1v.s3.d6dfe64be8dc from=translated src=- shape=66880677 vocab=f6d4416a
-/
@[simp] theorem del_true (t : Str) : del (true :: t) = del t := rfl
/--
@isnad1 id=eq.0h1v.s3.058021a66fe4 from=translated src=- shape=b8032b18 vocab=c9e87526
-/
@[simp] theorem del_false (t : Str) : del (false :: t) = false :: t := rfl

/-- The guaranteed output prefix: copy leading `0`'s; on the first `1`, eliminate
the run via `del`.
-/
def out : Str → Str
  | [] => []
  | false :: t => false :: out t
  | true :: t => del t

/--
@isnad1 id=eq.0h0v.s2.7c1610793d21 from=translated src=- shape=d3545b1f vocab=83154150
-/
@[simp] theorem out_nil : out [] = [] := rfl
/--
@isnad1 id=eq.0h1v.s3.404a019eeeb8 from=translated src=- shape=79c166c2 vocab=a678cbde
-/
@[simp] theorem out_false (t : Str) : out (false :: t) = false :: out t := rfl
/--
@isnad1 id=eq.0h1v.s3.da8227dd40f5 from=translated src=- shape=61dc95a6 vocab=d1b15116
-/
@[simp] theorem out_true (t : Str) : out (true :: t) = del t := rfl

/-- `del` only grows under extension: `del s <+: del (s ++ t)`.
@isnad1 id=isprefix.0h2v.s4.0d891cbc47bb from=translated src=- shape=91273a34 vocab=f1c90bcc
-/
theorem del_append (s t : Str) : del s <+: del (s ++ t) := by
  induction s with
  | nil => simp
  | cons c s₀ ih =>
    cases c with
    | true => simpa using ih
    | false => exact ⟨t, rfl⟩

/-- `out` only grows under extension: `out σ <+: out (σ ++ t)`.
@isnad1 id=isprefix.0h2v.s4.94ddc2c6e5c3 from=translated src=- shape=91273a34 vocab=fb64a2bb
-/
theorem out_append (σ t : Str) : out σ <+: out (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons c σ₀ ih =>
    cases c with
    | true => simpa using del_append σ₀ t
    | false =>
      simp_all

/-- **Prefix-monotonicity of the output.** Extending the input prefix can only
extend the guaranteed
output: `σ <+: σ' → out σ <+: out σ'`. This is the heart of Definition 2.1(iii)
for `g`.
@isnad1 id=isprefix.1h2v.s3.065403a23498 from=translated src=- shape=9a0a01eb vocab=94307897
-/
theorem out_mono {σ σ' : Str} (h : σ <+: σ') : out σ <+: out σ' := by
  obtain ⟨t, rfl⟩ := h
  exact out_append σ t

/-- **Example 2.4 — the run-eliminating mapping `g : B → B`.** `X g Y` iff `X =
σΣ*` and the cone of
the guaranteed output `(out σ)Σ*` approximates `Y`. Definition 2.1: (i) `out [] =
[]` so `Δ g Δ`;
(ii) a fixed cone has a unique prefix, and the value is the principal filter
`↑((out σ)Σ*)`, closed
under `∩`; (iii) `out_mono` shrinks the output cone as the input cone shrinks. -/
def runMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (out σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [out_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (out σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (out σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (out σ') ⊆ cone (out σ) := cone_subset_cone.mpr (out_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

end Domain.Neighborhood.Example24

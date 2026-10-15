/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Exercise419
public import Tengoku

/-!
# Exercise 5.16 (Scott 1981, PRG-19, Lecture V) — `neg`, `merge` and `d` on `C`

Returning to Example 4.4 (the domain `C` of finite or infinite binary sequences),
this module gives
fixed-point/recursive definitions of three maps and verifies their characterizing
equations:

* **`tail : C → C`** (`tail(bx) = x`, `tail(Λ) = ⊥`) — Scott's predecessor
analogue, the item left to
  the reader in Example 4.4, built here with the head-test combinator
  `Exercise419.liftC`.
* **`neg : C → C`** with `neg(0x) = 1·neg(x)`, `neg(1x) = 0·neg(x)` —
bit-complement. We solve the
  recursion in closed form via `liftC` (`neg(σ) = (flip σ)`, `flip = List.map
  not`), prove the
  recursion equations `neg_cons_false`/`neg_cons_true` (so it is *the* solution),
  and prove Scott's
  involution law **`neg(neg x) = x` for all `x ∈ |C|`** (`negMap_negMap`) — using
  that an approximable
  map is determined by its values on the finite elements `σ⊥`, `σ` (Exercise 2.8,
  `eq_of_toElementMap_principal`), so it suffices to check the two-fold complement
  on those, where it
  is `flip ∘ flip = id`.
* **`d : C → C`** (`d(Λ) = Λ`, `d(0x) = 00·d(x)`, `d(1x) = 11·d(x)`) — the
bit-doubling map of
  Example 4.4, again via `liftC` (`d(σ) = double σ`).
* **`merge : C × C → C`** with `merge(εx, δy) = ε·δ·merge(x, y)` —
bit-interleaving. Built directly as
  an approximable map out of `prod C C` from an explicit interleave value function
  `mergeVal`. The
  boundary that Scott flags (`merge(Λ, y)` etc.) is resolved by the unique
  *monotone* convention
  (`merge(Λ, y) = Λ`, `merge(εx, y) = ε⊥` once `y` runs out), the only choice
  compatible with
  approximability. We prove the recursion equation and **`merge(x, x) = d(x)`**
  (`mergeMap_diag`).

All *data* (`tail`, `negMap`, `dMap`, `mergeMap`) is **choice-free** (`#print
axioms ⊆ {propext,
Quot.sound}`); equalities of maps go through `eq_of_toElementMap_principal`
(classical, exactly like
the project's `ext_of_toElementMap`).

The Thue–Morse properties of `t = 0·merge(neg t, tail t)` (its digit-sum-mod-2
description and
overlap-freeness) are real combinatorics-on-words and are left as a separate
follow-up.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise516

open Domain.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-! ### List helpers: bit-complement `flip` and bit-doubling `double`. -/

/-- Complement every bit of a finite string. -/
abbrev flip (σ : Str) : Str := σ.map not

/--
@isnad1 id=eq.0h0v.s2.771eb9f13069 from=translated src=- shape=d3545b1f vocab=176540ea
-/
@[simp] theorem flip_nil : flip [] = [] := rfl
/--
@isnad1 id=eq.0h2v.s4.bd68eadebe61 from=translated src=- shape=7f96c692 vocab=5a40ff6e
-/
@[simp] theorem flip_cons (b : Bool) (σ : Str) : flip (b :: σ) = (!b) :: flip σ := rfl

/-- `flip` is an involution.
@isnad1 id=eq.0h1v.s3.345b10f00d24 from=translated src=- shape=47dcad53 vocab=faaf1b8a
-/
theorem flip_flip (σ : Str) : flip (flip σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

/-- `flip` preserves the prefix order.
@isnad1 id=isprefix.1h2v.s3.abf3babd7c7f from=translated src=- shape=9a0a01eb vocab=7c7ce6d7
-/
theorem flip_prefix {σ τ : Str} (h : σ <+: τ) : flip σ <+: flip τ := h.map _

/-- Double every bit of a finite string: `double (b :: σ) = b :: b :: double σ`. -/
def double : Str → Str
  | [] => []
  | b :: σ => b :: b :: double σ

/--
@isnad1 id=eq.0h0v.s2.55305b8d54c9 from=translated src=- shape=d3545b1f vocab=d838acde
-/
@[simp] theorem double_nil : double [] = [] := rfl
/--
@isnad1 id=eq.0h2v.s4.c7036e68aad1 from=translated src=- shape=e55dfe16 vocab=7f077672
-/
@[simp] theorem double_cons (b : Bool) (σ : Str) : double (b :: σ) = b :: b :: double σ := rfl

/-- `double` distributes over append.
@isnad1 id=eq.0h2v.s4.0a3601ae8b94 from=translated src=- shape=a13ca989 vocab=87985374
-/
theorem double_append (σ τ : Str) : double (σ ++ τ) = double σ ++ double τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [double, ih]

/-- `double` preserves the prefix order.
@isnad1 id=isprefix.1h2v.s3.6ed44c1fa73d from=translated src=- shape=9a0a01eb vocab=c6169564
-/
theorem double_prefix {σ τ : Str} (h : σ <+: τ) : double σ <+: double τ := by
  obtain ⟨ρ, rfl⟩ := h
  exact ⟨double ρ, (double_append σ ρ).symm⟩

/-! ### The approximation order on the finite elements `σ⊥` and `σ`. -/

/--
@isnad1 id=iff.0h2v.s4.2e6eac705f0d from=translated src=- shape=a8e24674 vocab=7ecf02a8
-/
theorem strBot_le_strBot_iff {σ τ : Str} : strBot σ ≤ strBot τ ↔ σ <+: τ := by
  rw [strBot, strBot, C.principal_le_iff, cone_subset_cone]

/--
@isnad1 id=iff.0h2v.s4.e6b9a5494288 from=translated src=- shape=b90444f0 vocab=640a1dec
-/
theorem strBot_le_strElem_iff {σ τ : Str} : strBot σ ≤ strElem τ ↔ σ <+: τ := by
  rw [strBot, strElem, C.principal_le_iff]
  exact singleton_subset_cone

/--
@isnad1 id=iff.0h2v.s4.2775f4041ab8 from=translated src=- shape=7ceb33a7 vocab=920de4c9
-/
theorem strElem_le_strElem_iff {σ τ : Str} : strElem σ ≤ strElem τ ↔ σ = τ := by
  rw [strElem, strElem, C.principal_le_iff, Set.singleton_subset_iff, Set.mem_singleton_iff,
    eq_comm]

/--
@isnad1 id=not.0h2v.s4.92cb7cb683d2 from=translated src=- shape=c0224fab vocab=264fe033
-/
theorem not_strElem_le_strBot {σ τ : Str} : ¬ strElem σ ≤ strBot τ := by
  rw [strElem, strBot, C.principal_le_iff]
  exact not_cone_subset_singleton τ σ

/-- A prefix relation descends to tails.
@isnad1 id=isprefix.1h2v.s4.c6fd76103a2e from=translated src=- shape=63b44f7c vocab=51ce5beb
-/
theorem tail_prefix {σ τ : Str} (h : σ <+: τ) : σ.tail <+: τ.tail := by
  obtain ⟨ρ, rfl⟩ := h
  cases σ with
  | nil => simp
  | cons a σ' => exact List.prefix_append σ' ρ

/-! ### Determination by finite elements: an equality criterion for maps `C → V`. -/

variable {β : Type*}

/-- Two approximable maps out of `C` agree as soon as they agree on every finite
element `σ⊥` and
`σ` (Exercise 2.8). This is the workhorse for the map equalities below.
@isnad1 id=eq.2h4v.s6.c367e6a31a30 from=translated src=- shape=40f05cf7 vocab=3255f041
-/
theorem map_ext_C {V : NeighborhoodSystem β} {f g : ApproximableMap C V}
    (hbot : ∀ σ, f.toElementMap (strBot σ) = g.toElementMap (strBot σ))
    (helem : ∀ σ, f.toElementMap (strElem σ) = g.toElementMap (strElem σ)) : f = g := by
  apply eq_of_toElementMap_principal
  intro X hX
  obtain (⟨σ, rfl⟩ | ⟨σ, rfl⟩) := (C_mem.mp hX)
  · exact hbot σ
  · exact helem σ

/-! ### `tail : C → C` — Scott's predecessor analogue (Example 4.4). -/

/-- The value of `tail` on a total element `σ`: `tail(Λ) = ⊥`, `tail(bσ') = σ'`. -/
def tailSing : Str → C.Element
  | [] => strBot []
  | _ :: σ' => strElem σ'

/--
@isnad1 id=le.1h2v.s5.577afa1661b1 from=translated src=- shape=78550e0f vocab=294b28ec
-/
theorem tail_hcone {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ strBot τ.tail :=
  strBot_le_strBot_iff.mpr (tail_prefix h)

/--
@isnad1 id=le.1h2v.s4.af1e842abd0f from=translated src=- shape=ea2429a8 vocab=78dda82a
-/
theorem tail_hsing {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ tailSing τ := by
  cases τ with
  | nil => obtain rfl := List.prefix_nil.mp h; exact le_refl _
  | cons a τ' =>
    refine strBot_le_strElem_iff.mpr ?_
    cases σ with
    | nil => exact List.nil_prefix
    | cons b σ' =>
      simp_all

/-- **Exercise 5.16 / Example 4.4 — `tail : C → C`.** Built with the head-test
combinator `liftC`:
on `σ⊥` it returns `(tail σ)⊥`, on `σ` the total `tail σ` (with `tail Λ = ⊥`). -/
def tailMap : ApproximableMap C C :=
  liftC C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing

/--
@isnad1 id=eq.0h1v.s4.8ae971948029 from=translated src=- shape=d4c90d88 vocab=e9e89a6e
-/
@[simp] theorem tailMap_strBot (σ : Str) :
    tailMap.toElementMap (strBot σ) = strBot σ.tail :=
  liftC_strBot C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

/--
@isnad1 id=eq.0h1v.s4.e4b12f874cab from=translated src=- shape=d754f160 vocab=56f501ae
-/
@[simp] theorem tailMap_strElem (σ : Str) :
    tailMap.toElementMap (strElem σ) = tailSing σ :=
  liftC_strElem C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

/-- `tail(b(σ⊥)) = σ⊥`.
@isnad1 id=eq.0h2v.s4.d2ffdf98d21b from=translated src=- shape=f8de12d3 vocab=0aad2547
-/
theorem tailMap_consMap_strBot (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strBot σ)) = strBot σ := by
  rw [consMap_strBot, tailMap_strBot]; rfl

/-- `tail(b(σ)) = σ`.
@isnad1 id=eq.0h2v.s4.0209c87f4aab from=translated src=- shape=f8de12d3 vocab=9b1d55b1
-/
theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl

/-! ### `neg : C → C` — bit complement, `neg(0x)=1·neg(x)`, `neg(1x)=0·neg(x)`. -/

/--
@isnad1 id=le.1h2v.s4.7eee7e69f17a from=translated src=- shape=939b6812 vocab=1280ca37
-/
theorem neg_hcone {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strBot (flip τ) :=
  strBot_le_strBot_iff.mpr (flip_prefix h)

/--
@isnad1 id=le.1h2v.s4.7757dc4fa6fc from=translated src=- shape=1fd0188c vocab=0d86a8a0
-/
theorem neg_hsing {σ τ : Str} (h : σ <+: τ) : strBot (flip σ) ≤ strElem (flip τ) :=
  strBot_le_strElem_iff.mpr (flip_prefix h)

/-- **Exercise 5.16 — `neg : C → C`.** The closed-form solution of Scott's
recursion, built with
`liftC`: `neg(σ⊥) = (flip σ)⊥` and `neg(σ) = flip σ`. -/
def negMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing

/--
@isnad1 id=eq.0h1v.s4.12d0094f3385 from=translated src=- shape=4709b023 vocab=35286a81
-/
@[simp] theorem negMap_strBot (σ : Str) :
    negMap.toElementMap (strBot σ) = strBot (flip σ) :=
  liftC_strBot C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ

/--
@isnad1 id=eq.0h1v.s4.22f3099e07a8 from=translated src=- shape=4709b023 vocab=2b6c2bac
-/
@[simp] theorem negMap_strElem (σ : Str) :
    negMap.toElementMap (strElem σ) = strElem (flip σ) :=
  liftC_strElem C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing σ

/-- **Exercise 5.16 — the recursion for `neg`, case `0`.** `neg(0·x) = 1·neg(x)`
as a map
identity.
@isnad1 id=eq.0h0v.s4.fa89ab8e706b from=translated src=- shape=e5c0f148 vocab=9c2b7d5a
-/
theorem neg_cons_false : negMap.comp (consMap false) = (consMap true).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl

/-- **Exercise 5.16 — the recursion for `neg`, case `1`.** `neg(1·x) = 0·neg(x)`
as a map
identity.
@isnad1 id=eq.0h0v.s4.2bd69be92406 from=translated src=- shape=e5c0f148 vocab=9c2b7d5a
-/
theorem neg_cons_true : negMap.comp (consMap true) = (consMap false).comp negMap := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, consMap_strBot, negMap_strBot, toElementMap_comp, negMap_strBot,
      consMap_strBot]
    rfl
  · intro σ
    rw [toElementMap_comp, consMap_strElem, negMap_strElem, toElementMap_comp, negMap_strElem,
      consMap_strElem]
    rfl

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg ∘ neg = id` as approximable maps:
it suffices to
check on the finite elements `σ⊥`, `σ`, where it is `flip ∘ flip = id`.
@isnad1 id=eq.0h0v.s4.bc6d5d5cfb20 from=translated src=- shape=c2740c2d vocab=2da4536e
-/
theorem negMap_comp_negMap : negMap.comp negMap = idMap C := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, negMap_strBot, negMap_strBot, flip_flip, toElementMap_idMap]
  · intro σ
    rw [toElementMap_comp, negMap_strElem, negMap_strElem, flip_flip, toElementMap_idMap]

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `neg(neg(x)) = x` for all `x ∈ |C|`.
@isnad1 id=eq.0h1v.s4.2fad1b08a7ae from=translated src=- shape=7f69676e vocab=f17e1757
-/
theorem negMap_negMap (x : C.Element) : negMap.toElementMap (negMap.toElementMap x) = x := by
  have h := negMap_comp_negMap
  rw [← toElementMap_comp, h, toElementMap_idMap]

/-! ### `d : C → C` — bit-doubling, `d(Λ)=Λ`, `d(0x)=00·d(x)`, `d(1x)=11·d(x)`. -/

/--
@isnad1 id=le.1h2v.s4.ad0140cbc519 from=translated src=- shape=939b6812 vocab=ccd75859
-/
theorem d_hcone {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strBot (double τ) :=
  strBot_le_strBot_iff.mpr (double_prefix h)

/--
@isnad1 id=le.1h2v.s4.9bd7f35daa58 from=translated src=- shape=1fd0188c vocab=06e8c258
-/
theorem d_hsing {σ τ : Str} (h : σ <+: τ) : strBot (double σ) ≤ strElem (double τ) :=
  strBot_le_strElem_iff.mpr (double_prefix h)

/-- **Exercise 5.16 / Example 4.4 — `d : C → C`.** The doubling map, closed form
via `liftC`:
`d(σ⊥) = (double σ)⊥`, `d(σ) = double σ`. -/
def dMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing

/--
@isnad1 id=eq.0h1v.s4.2054a43b0030 from=translated src=- shape=4709b023 vocab=c4cee864
-/
@[simp] theorem dMap_strBot (σ : Str) :
    dMap.toElementMap (strBot σ) = strBot (double σ) :=
  liftC_strBot C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

/--
@isnad1 id=eq.0h1v.s4.1615bfa9b103 from=translated src=- shape=4709b023 vocab=401dc77d
-/
@[simp] theorem dMap_strElem (σ : Str) :
    dMap.toElementMap (strElem σ) = strElem (double σ) :=
  liftC_strElem C (fun σ => strBot (double σ)) (fun σ => strElem (double σ)) d_hcone d_hsing σ

/-! ### `merge : C × C → C` — bit interleaving.

The principal elements of `C` are tagged strings `(b, σ)`: `b = true` is the
*total* `σ`, `b = false`
the *partial* `σ⊥`. We encode the corresponding neighbourhood (`shape`) and
element (`shapeElem`),
the partial order between them (`SLe`), and the interleaving value function
`mergeVal`. -/

/-- The neighbourhood of the tagged string `(b, σ)`: `{σ}` if total, `cone σ` if
partial. -/
def shape : Bool → Str → Set Str
  | true, σ => {σ}
  | false, σ => cone σ

/--
@isnad1 id=memc.0h2v.s3.879d6173259a from=translated src=- shape=c57da3d9 vocab=d80814b5
-/
theorem memC_shape : ∀ (b : Bool) (σ : Str), memC (shape b σ)
  | true, σ => memC_singleton σ
  | false, σ => memC_cone σ

/-- The element of the tagged string `(b, σ)`: total `σ` if `b`, partial `σ⊥`
otherwise. -/
def shapeElem (b : Bool) (σ : Str) : C.Element := C.principal (memC_shape b σ)

/--
@isnad1 id=eq.0h1v.s3.2065a8128fe8 from=translated src=- shape=50a5e0a8 vocab=26993839
-/
@[simp] theorem shapeElem_true (σ : Str) : shapeElem true σ = strElem σ := rfl
/--
@isnad1 id=eq.0h1v.s3.bc36d966d719 from=translated src=- shape=50a5e0a8 vocab=f2fd4dfb
-/
@[simp] theorem shapeElem_false (σ : Str) : shapeElem false σ = strBot σ := rfl

/--
@isnad1 id=and.1h4v.s4.e5a1f5c4faae from=translated src=- shape=0c5009d2 vocab=004d0c1b
-/
theorem shape_injective : ∀ {b b' : Bool} {σ σ' : Str}, shape b σ = shape b' σ' → b = b' ∧ σ = σ'
  | true, true, σ, σ', h => ⟨rfl, by rwa [shape, shape, Set.singleton_eq_singleton_iff] at h⟩
  | true, false, σ, σ', h => absurd h.symm (cone_ne_singleton σ' σ)
  | false, true, σ, σ', h => absurd h (cone_ne_singleton σ σ')
  | false, false, σ, σ', h => ⟨rfl, cone_injective h⟩

/-- The approximation order between tagged strings: `(b, σ) ⊑ (b', σ')`. A total
string is maximal
(only `⊑` itself); a partial string `σ⊥` is `⊑` anything extending `σ`. -/
def SLe : Bool → Str → Bool → Str → Prop
  | true, σ, b', σ' => b' = true ∧ σ = σ'
  | false, σ, _, σ' => σ <+: σ'

/-- `SLe` characterizes the element order on `shapeElem`.
@isnad1 id=iff.0h4v.s5.516a62b0e737 from=translated src=- shape=5ba012c7 vocab=80a425e8
-/
theorem shapeElem_le_iff {b b' : Bool} {σ σ' : Str} :
    shapeElem b σ ≤ shapeElem b' σ' ↔ SLe b σ b' σ' := by
  cases b <;> cases b' <;>
    simp only [shapeElem_true, shapeElem_false, SLe, strElem_le_strElem_iff,
      strBot_le_strBot_iff, strBot_le_strElem_iff, true_and]
  · exact ⟨fun h => absurd h not_strElem_le_strBot, fun h => absurd h (by simp)⟩

/-- The interleave value function: `mergeVal σ b₀ τ b₁` returns the interleaving
of the tagged
strings `(b₀, σ)` and `(b₁, τ)` as a tagged string. Boundary convention (the only
monotone one):
`merge(Λ, y) = Λ`, `merge(⊥, y) = ⊥`, and `merge(εx, y) = ε⊥` once `y` runs out. -/
def mergeVal : Str → Bool → Str → Bool → Str × Bool
  | [], b₀, _, _ => ([], b₀)
  | a :: _, _, [], _ => ([a], false)
  | a :: σ, b₀, b :: τ, b₁ => (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2)

/--
@isnad1 id=eq.0h3v.s4.b8eec38a2cfc from=translated src=- shape=c08da46d vocab=48d39ac5
-/
@[simp] theorem mergeVal_nil (b₀ : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal [] b₀ τ b₁ = ([], b₀) := rfl
/--
@isnad1 id=eq.0h4v.s4.e206d97506c4 from=translated src=- shape=df0b75e1 vocab=c7cb6880
-/
@[simp] theorem mergeVal_cons_nil (a : Bool) (σ : Str) (b₀ b₁ : Bool) :
    mergeVal (a :: σ) b₀ [] b₁ = ([a], false) := rfl
/--
@isnad1 id=eq.0h6v.s5.7b0c3bdd0741 from=translated src=- shape=e1ffc66b vocab=c3419337
-/
@[simp] theorem mergeVal_cons_cons (a : Bool) (σ : Str) (b₀ b : Bool) (τ : Str) (b₁ : Bool) :
    mergeVal (a :: σ) b₀ (b :: τ) b₁ =
      (a :: b :: (mergeVal σ b₀ τ b₁).1, (mergeVal σ b₀ τ b₁).2) := rfl

/-- The element produced by interleaving `(b₀, σ)` and `(b₁, τ)`. -/
def mergeElem (σ : Str) (b₀ : Bool) (τ : Str) (b₁ : Bool) : C.Element :=
  shapeElem (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1

/-! #### The monotonicity of `mergeVal` (the crux of approximability). -/

/-- Two equal head bits prepended preserve `SLe`.
@isnad1 id=sle.1h6v.s5.08462ba2b397 from=translated src=- shape=b130dfb7 vocab=626e9c5f
-/
theorem SLe_cons2 {p p' : Bool} {ρ ρ' : Str} (c d : Bool) (h : SLe p ρ p' ρ') :
    SLe p (c :: d :: ρ) p' (c :: d :: ρ') := by
  cases p with
  | true => obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | false =>
    exact List.cons_prefix_cons.mpr ⟨rfl, List.cons_prefix_cons.mpr ⟨rfl, h⟩⟩

/-- Invert `SLe` on a cons in the first string: the second string starts with the
same head.
@isnad1 id=ex.1h5v.s5.e509835d499c from=translated src=- shape=820b0496 vocab=68f6a49b
-/
theorem SLe_cons_inv {b₀ b₀' : Bool} {a : Bool} {σ₀ σ' : Str} (h : SLe b₀ (a :: σ₀) b₀' σ') :
    ∃ σ₀', σ' = a :: σ₀' ∧ SLe b₀ σ₀ b₀' σ₀' := by
  cases b₀ with
  | true =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨σ₀, rfl, rfl, rfl⟩
  | false =>
    cases σ' with
    | nil => exact absurd h (by simp [SLe])
    | cons a' σ₀' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact ⟨σ₀', rfl, h'⟩

/-- **The monotonicity of interleaving.** If `(b₀, σ) ⊑ (b₀', σ')` and `(b₁, τ) ⊑
(b₁', τ')`
then the
interleavings are `⊑`-ordered. The crux that makes `merge` approximable.
@isnad1 id=sle.2h8v.s5.224a4f6868c8 from=translated src=- shape=c5f24a42 vocab=75172f03
-/
theorem mergeVal_SLe : ∀ (σ : Str) (b₀ : Bool) (σ' : Str) (b₀' : Bool)
    (τ : Str) (b₁ : Bool) (τ' : Str) (b₁' : Bool),
    SLe b₀ σ b₀' σ' → SLe b₁ τ b₁' τ' →
    SLe (mergeVal σ b₀ τ b₁).2 (mergeVal σ b₀ τ b₁).1
      (mergeVal σ' b₀' τ' b₁').2 (mergeVal σ' b₀' τ' b₁').1
  | [], b₀, σ', b₀', τ, b₁, τ', b₁', h0, _ => by
    cases b₀ with
    | true =>
      obtain ⟨rfl, rfl⟩ := h0
      simp only [mergeVal_nil]; exact ⟨rfl, rfl⟩
    | false =>
      simp only [mergeVal_nil]; exact List.nil_prefix
  | a :: σ₀, b₀, σ', b₀', [], b₁, τ', b₁', h0, _ => by
    obtain ⟨σ₀', rfl, _⟩ := SLe_cons_inv h0
    simp only [mergeVal_cons_nil]
    cases τ' with
    | nil => simp only [mergeVal_cons_nil]; exact List.prefix_rfl
    | cons c τ₀' => simp only [mergeVal_cons_cons]; exact ⟨c :: _, rfl⟩
  | a :: σ₀, b₀, σ', b₀', b :: τ₀, b₁, τ', b₁', h0, h1 => by
    obtain ⟨σ₀', rfl, h0'⟩ := SLe_cons_inv h0
    obtain ⟨τ₀', rfl, h1'⟩ := SLe_cons_inv h1
    simp only [mergeVal_cons_cons]
    exact SLe_cons2 a b (mergeVal_SLe σ₀ b₀ σ₀' b₀' τ₀ b₁ τ₀' b₁' h0' h1')

/-- The element-order form of `mergeVal_SLe`.
@isnad1 id=le.2h8v.s6.e0b533fc9c45 from=translated src=- shape=ba01eae9 vocab=67bf361a
-/
theorem mergeElem_mono {σ σ' τ τ' : Str} {b₀ b₀' b₁ b₁' : Bool}
    (h0 : shapeElem b₀ σ ≤ shapeElem b₀' σ') (h1 : shapeElem b₁ τ ≤ shapeElem b₁' τ') :
    mergeElem σ b₀ τ b₁ ≤ mergeElem σ' b₀' τ' b₁' :=
  shapeElem_le_iff.mpr
    (mergeVal_SLe σ b₀ σ' b₀' τ b₁ τ' b₁' (shapeElem_le_iff.mp h0) (shapeElem_le_iff.mp h1))

/-- The diagonal value: interleaving `(s, σ)` with itself doubles.
@isnad1 id=eq.0h2v.s4.1fe1b3ed2588 from=translated src=- shape=81fcbcfe vocab=a8395a81
-/
theorem mergeVal_diag (s : Bool) (σ : Str) : mergeVal σ s σ s = (double σ, s) := by
  induction σ with
  | nil => rfl
  | cons a σ ih => simp [mergeVal_cons_cons, ih]

/-- On the diagonal `merge(⟨(s, σ), (s, σ)⟩)` doubles `σ`.
@isnad1 id=eq.0h2v.s4.4fc5b61860fd from=translated src=- shape=c28012fa vocab=4951ba19
-/
theorem mergeElem_diag (s : Bool) (σ : Str) : mergeElem σ s σ s = shapeElem s (double σ) := by
  simp [mergeElem, mergeVal_diag]

/-! #### A refinement lemma packaging both the representation and the order. -/

/--
@isnad1 id=ex.2h3v.s5.83efca3709cd from=translated src=- shape=b4acc09b vocab=1f7822ff
-/
theorem shape_refine {b : Bool} {σ : Str} {P : Set Str} (hP : memC P) (hsub : P ⊆ shape b σ) :
    ∃ (b' : Bool) (σ' : Str), P = shape b' σ' ∧ shapeElem b σ ≤ shapeElem b' σ' := by
  rcases hP with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact ⟨false, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape false ρ)).mpr hsub⟩
  · exact ⟨true, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape true ρ)).mpr hsub⟩

/-! #### The map `merge`. -/

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The interleaving map `merge : C × C →
C` with
`merge(εx, δy) = ε·δ·merge(x, y)`. Built directly as an approximable map: an input
neighbourhood
`shape b₀ σ ∪ shape b₁ τ` relates to the neighbourhoods of `mergeElem σ b₀ τ b₁`. -/
def mergeMap : ApproximableMap (prod C C) C where
  rel W Z := ∃ (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str),
    W = prodNbhd (shape b₀ σ) (shape b₁ τ) ∧ (mergeElem σ b₀ τ b₁).mem Z
  rel_dom := by
    rintro W Z ⟨b₀, σ, b₁, τ, rfl, _⟩
    exact prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ)
  rel_cod := by
    rintro W Z ⟨b₀, σ, b₁, τ, _, hZ⟩
    exact (mergeElem σ b₀ τ b₁).sub hZ
  master_rel := by
    refine ⟨false, [], false, [], ?_, (mergeElem [] false [] false).master_mem⟩
    show (prod C C).master = prodNbhd (shape false []) (shape false [])
    simp only [prod_master, shape, C_master, cone_nil]
  inter_right := by
    rintro W Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ ⟨b₀', σ', b₁', τ', heq, hZ'⟩
    obtain ⟨hX, hY⟩ := prodNbhd_injective heq
    obtain ⟨rfl, rfl⟩ := shape_injective hX
    obtain ⟨rfl, rfl⟩ := shape_injective hY
    exact ⟨b₀, σ, b₁, τ, rfl, (mergeElem σ b₀ τ b₁).inter_mem hZ hZ'⟩
  mono := by
    rintro W W₂ Z Z' ⟨b₀, σ, b₁, τ, rfl, hZ⟩ hW₂W hZZ' hW₂ hZ'
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hW₂
    obtain ⟨hPsub, hQsub⟩ := prodNbhd_subset_iff.mp hW₂W
    obtain ⟨b₀', σ', hPeq, hle0⟩ := shape_refine hP hPsub
    obtain ⟨b₁', τ', hQeq, hle1⟩ := shape_refine hQ hQsub
    subst hPeq; subst hQeq
    refine ⟨b₀', σ', b₁', τ', rfl, ?_⟩
    have hmono := mergeElem_mono hle0 hle1
    exact (mergeElem σ' b₀' τ' b₁').up_mem (hmono Z hZ) hZ' hZZ'

/-- `consMap b` shifts a tagged string: `b·(c, σ) = (c, b :: σ)`.
@isnad1 id=eq.0h3v.s4.72e96be99d5c from=translated src=- shape=906f067c vocab=bb87ee54
-/
@[simp] theorem consMap_shapeElem (b c : Bool) (σ : Str) :
    (consMap b).toElementMap (shapeElem c σ) = shapeElem c (b :: σ) := by
  cases c with
  | false => rw [shapeElem_false, consMap_strBot]; rfl
  | true => rw [shapeElem_true, consMap_strElem]; rfl

/-- **The value of `merge` on a pair of finite elements.** `merge(⟨(b₀, σ), (b₁,
τ)⟩) =
mergeElem σ b₀ τ b₁`. The analogue of `liftC_strBot`/`liftC_strElem` for the
product.
@isnad1 id=eq.0h4v.s5.0275ba9481ba from=translated src=- shape=1e0c7b01 vocab=37121487
-/
theorem mergeMap_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    mergeMap.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ)) = mergeElem σ b₀ τ b₁ := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W, hWmem, c₀, ρ, c₁, π, rfl, hZ⟩
    rw [mem_pair_prodNbhd] at hWmem
    obtain ⟨hmσ, hmτ⟩ := hWmem
    have hle0 : shapeElem c₀ ρ ≤ shapeElem b₀ σ :=
      (C.principal_le_iff (memC_shape c₀ ρ) (memC_shape b₀ σ)).mpr hmσ.2
    have hle1 : shapeElem c₁ π ≤ shapeElem b₁ τ :=
      (C.principal_le_iff (memC_shape c₁ π) (memC_shape b₁ τ)).mpr hmτ.2
    exact mergeElem_mono hle0 hle1 Z hZ
  · intro hZ
    refine ⟨prodNbhd (shape b₀ σ) (shape b₁ τ), ?_, b₀, σ, b₁, τ, rfl, hZ⟩
    exact mem_pair_prodNbhd.mpr ⟨⟨memC_shape b₀ σ, subset_rfl⟩, ⟨memC_shape b₁ τ, subset_rfl⟩⟩

/-! #### Extensionality for maps `C × C → C` via finite element pairs. -/

/--
@isnad1 id=ex.1h1v.s4.3ed2901a46d3 from=translated src=- shape=249dbf6e vocab=bbee0f38
-/
theorem memC_eq_shape {X : Set Str} (hX : memC X) : ∃ (b : Bool) (σ : Str), X = shape b σ := by
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨false, σ, rfl⟩
  · exact ⟨true, σ, rfl⟩

/--
@isnad1 id=eq.0h4v.s5.324e603531d6 from=translated src=- shape=4f7df75a vocab=c280661d
-/
theorem prod_principal_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    (prod C C).principal (prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ))
      = pair (shapeElem b₀ σ) (shapeElem b₁ τ) := by
  apply Element.ext
  intro P
  rw [mem_principal]
  constructor
  · rintro ⟨hP, hsub⟩
    obtain ⟨X', Y', hX', hY', rfl⟩ := hP
    obtain ⟨hsX, hsY⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
  · rintro ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
    exact ⟨prod_mem_prodNbhd hX' hY', prodNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩

/-- Two maps `C × C → C` agree as soon as they agree on every pair of finite
elements.
@isnad1 id=eq.1h2v.s6.1c56372f08a9 from=translated src=- shape=e3e30f58 vocab=0d133233
-/
theorem prodMap_ext {f g : ApproximableMap (prod C C) C}
    (h : ∀ b₀ σ b₁ τ, f.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))
      = g.toElementMap (pair (shapeElem b₀ σ) (shapeElem b₁ τ))) : f = g := by
  apply eq_of_toElementMap_principal
  intro W hW
  obtain ⟨b₀, σ, b₁, τ, rfl⟩ :
      ∃ b₀ σ b₁ τ, W = prodNbhd (shape b₀ σ) (shape b₁ τ) := by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    obtain ⟨b₀, σ, rfl⟩ := memC_eq_shape hX
    obtain ⟨b₁, τ, rfl⟩ := memC_eq_shape hY
    exact ⟨b₀, σ, b₁, τ, rfl⟩
  have heq : (prod C C).principal hW = pair (shapeElem b₀ σ) (shapeElem b₁ τ) :=
    prod_principal_pair b₀ σ b₁ τ
  rw [heq]; exact h b₀ σ b₁ τ

/-! #### The recursion equation and `merge(x, x) = d(x)`. -/

/-- **Exercise 5.16 (Scott 1981, PRG-19).** The defining recursion of `merge`:
`merge(εx, δy) = ε·δ·merge(x, y)` for all `x, y ∈ |C|` and bits `ε, δ`.
@isnad1 id=eq.0h4v.s6.97b79812c983 from=translated src=- shape=6ff08dda vocab=87bd6cb7
-/
theorem mergeMap_cons (ε δ : Bool) (x y : C.Element) :
    mergeMap.toElementMap
        (pair ((consMap ε).toElementMap x) ((consMap δ).toElementMap y))
      = (consMap ε).toElementMap
          ((consMap δ).toElementMap (mergeMap.toElementMap (pair x y))) := by
  have key :
      mergeMap.comp (paired ((consMap ε).comp (proj₀ C C)) ((consMap δ).comp (proj₁ C C)))
        = ((consMap ε).comp (consMap δ)).comp mergeMap := by
    apply prodMap_ext
    intro b₀ σ b₁ τ
    simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
      fst_pair, snd_pair, consMap_shapeElem, mergeMap_pair, mergeElem, mergeVal_cons_cons]
  have hx := congrArg (fun m : ApproximableMap (prod C C) C => m.toElementMap (pair x y)) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair] at hx
  exact hx

/-- **Exercise 5.16 (Scott 1981, PRG-19).** `merge(x, x) = d(x)` for all `x ∈ |C|`
(the doubling map
of Example 4.4).
@isnad1 id=eq.0h1v.s5.351c636803d9 from=translated src=- shape=9059e160 vocab=a8e055d4
-/
theorem mergeMap_diag (x : C.Element) :
    mergeMap.toElementMap (pair x x) = dMap.toElementMap x := by
  have key : mergeMap.comp (paired (idMap C) (idMap C)) = dMap := by
    apply map_ext_C
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strBot σ) (strBot σ) = pair (shapeElem false σ) (shapeElem false σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_false, dMap_strBot]
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strElem σ) (strElem σ) = pair (shapeElem true σ) (shapeElem true σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_true, dMap_strElem]
  have hx := congrArg (fun m : ApproximableMap C C => m.toElementMap x) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_idMap] at hx
  exact hx

end Domain.Neighborhood.Exercise516

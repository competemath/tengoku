module

public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
public import Tengoku.Seed.Data.ZMod.Basic
public import Tengoku.Seed.Tactic.IntervalCases
public import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ashby's Law of Requisite Variety — the counting half

W. Ross Ashby, *An Introduction to Cybernetics* (Chapman & Hall, 1961), chapter
11, sections 11/5, 11/7 and 11/9 in their combinatorial form: a regulator cannot
hold the outcome steadier than its own repertoire allows, counted in states.
`AISafetyAtlas.Control.RequisiteVariety` carries the same law's entropy form
(11/8) and imports this file.

## Why this is a file of its own

The two halves need different foundations. Counting needs `Finset` and `Fintype`
and nothing else; the entropy form needs PFR's `H[· ; ·]`. Held in one file, the
counting half is unusable without elaborating the entropy half's dependency —
which is what `AISafetyAtlas.Oversight.VarietyBound` would otherwise pay for the
single declaration it takes from here, `two_le_card_admittedOutcomes`, and what
`Oversight.VarietyCheck` and the `atlas-check` executable would pay through it.

**The separation is in the import graph, not in the package.** PFR is required at
Lake scope, so it is fetched whatever this file imports, and a project depending
on the atlas inherits it. What the separation buys is that reaching the counting
obstruction does not require elaborating it.

Both files are `namespace AISafetyAtlas.Control`, so the module a declaration
sits in is not part of its name, and `AISafetyAtlas.Control` re-exports both
halves.

## Explicit non-claims

- **Not** a new result. Every declaration below was in `RequisiteVariety` and is
  moved unchanged.
- **Not** a claim that the counting bound is sufficient. It is a necessary
  condition; see `AISafetyAtlas.Oversight.exists_cannotForce_false_and_forces`
  for a table where it is silent and forcing succeeds.
- **Not** independent of the entropy half's reading. The two are one law in two
  idioms, which is why they share a namespace and a provenance record
  (`docs/provenance/ashby-requisite-variety.md`).
-/

namespace AISafetyAtlas.Control

open Function

universe uD uR uE

/-! ## The regulation table

Ashby's Table 11/5/1: rows are disturbances, columns are the regulator's moves,
and the entry is the outcome. A *strategy* `ρ` picks one column per row, and the
outcomes it admits are the entries so selected. -/

section Counting

variable {D : Type uD} {R : Type uR} {E : Type uE}
variable [DecidableEq R] [DecidableEq E]

/--
The outcomes a strategy admits: `T d (ρ d)` as `d` ranges over the disturbances
in `s`. Ashby's "set of outcomes selected by R, one from each row".-/
@[expose] public def admittedOutcomes (T : D → R → E) (ρ : D → R) (s : Finset D) : Finset E :=
  s.image fun d => T d (ρ d)

/--
**The counting law, with Ashby's 11/9 multiplicity.** If no outcome-and-response
pair is produced by more than `k` disturbances, then the number of disturbances
is at most `k` times the number of admitted outcomes times the number of
responses used.

This is the one statement behind both 11/5 (`k = 1`) and 11/9 (general `k`).-/
public theorem card_le_mul_card_admittedOutcomes_mul (T : D → R → E) (ρ : D → R)
    (s : Finset D) (rs : Finset R) (k : ℕ)
    (hρ : ∀ d ∈ s, ρ d ∈ rs)
    (hk : ∀ (e : E) (r : R), (s.filter fun d => T d (ρ d) = e ∧ ρ d = r).card ≤ k) :
    s.card ≤ k * ((admittedOutcomes T ρ s).card * rs.card) := by
  have hmaps : ∀ d ∈ s, (fun d => (T d (ρ d), ρ d)) d ∈ admittedOutcomes T ρ s ×ˢ rs := by
    intro d hd
    exact Finset.mk_mem_product (Finset.mem_image_of_mem _ hd) (hρ d hd)
  have hfib : ∀ b ∈ admittedOutcomes T ρ s ×ˢ rs,
      (s.filter fun d => (T d (ρ d), ρ d) = b).card ≤ k := by
    rintro ⟨e, r⟩ -
    refine le_trans (le_of_eq ?_) (hk e r)
    congr 1
    exact Finset.filter_congr fun d _ => by simp [Prod.ext_iff]
  have := Finset.card_le_mul_card_image_of_maps_to hmaps k hfib
  rwa [Finset.card_product] at this

/--
**Ashby 11/5, the multiplied form.** With no outcome repeated in a column — that
is, with each response separating the disturbances it is used on — the number of
disturbances is at most the number of admitted outcomes times the number of
responses.

The hypothesis is `Set.InjOn` on the fibre `{d ∈ s | ρ d = r}` rather than
injectivity of the whole column: outcomes the strategy never selects are
irrelevant, which the printed condition does not exploit.-/
public theorem card_le_mul_card_admittedOutcomes (T : D → R → E) (ρ : D → R)
    (s : Finset D) (rs : Finset R)
    (hρ : ∀ d ∈ s, ρ d ∈ rs)
    (hcol : ∀ r : R, Set.InjOn (fun d => T d r) {d | d ∈ s ∧ ρ d = r}) :
    s.card ≤ (admittedOutcomes T ρ s).card * rs.card := by
  have h := card_le_mul_card_admittedOutcomes_mul T ρ s rs 1 hρ ?_
  · simpa using h
  · intro e r
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    obtain ⟨has, hae, har⟩ := ha
    obtain ⟨hbs, hbe, hbr⟩ := hb
    refine hcol r ⟨has, har⟩ ⟨hbs, hbr⟩ ?_
    have hab : T a (ρ a) = T b (ρ b) := by rw [hae, hbe]
    simpa [har, hbr] using hab

/--
**Ashby 11/5 verbatim.** "If no two elements in the same column are equal, and if
a set of outcomes is selected by `R`, one from each row, and if the table has
`r` rows and `c` columns, then the variety in the selected set of outcomes
cannot be fewer than `r/c`."

Rows are the disturbances, columns the responses. The quotient is taken in `ℚ`;
no nondegeneracy hypothesis is needed, because an empty response type forces an
empty disturbance type and the bound reads `0 ≤ 0`.-/
public theorem ashby_variety_ge [Fintype D] [Fintype R] (T : D → R → E) (ρ : D → R)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    (Fintype.card D : ℚ) / Fintype.card R
      ≤ ((admittedOutcomes T ρ Finset.univ).card : ℚ) := by
  have hmul : (Fintype.card D)
      ≤ (admittedOutcomes T ρ Finset.univ).card * Fintype.card R := by
    have := card_le_mul_card_admittedOutcomes T ρ Finset.univ Finset.univ
      (fun d _ => Finset.mem_univ _) (fun r => (hcol r).injOn)
    simpa [Finset.card_univ] using this
  rcases Nat.eq_zero_or_pos (Fintype.card R) with hR | hR
  · have : Fintype.card D = 0 := by simpa [hR] using hmul
    simp [this, hR]
  · rw [div_le_iff₀ (by exact_mod_cast hR)]
    exact_mod_cast hmul

/-! ## The bound is attained

Ashby's 11/6 says the regulator can reduce the variety of outcomes to `1/n` of
what it would otherwise be, "but not lower". The counting law above is the *not
lower* half. This section is the other half.

Two corrections to the naive reading are built in.

*The bound that is attained is the integer one.* Outcomes are counted, so
`⌈|D| / |R|⌉` is the real obstruction; the rational `|D| / |R|` of
`ashby_variety_ge` is not attainable when `|R|` does not divide `|D|`.
`card_ceilDiv_le_admittedOutcomes` proves the integer form and the witness meets
it — at `|D| = 5`, `|R| = 2` three outcomes must occur, and three do.

*This is an existence statement about one table.* No claim is made that every
table permits the reduction, and none is available: `T d r = d` has injective
columns and admits every outcome under every strategy.

The witness is a shift table. A disturbance `d` is read as the pair
`(d / c, d % c)`: the quotient is the part the regulator cannot touch, the
remainder the part it can. A move subtracts from the remainder, so the strategy
that plays the remainder cancels it and the outcome is `(d / c, 0)`. The
regulator absorbs exactly as much variety as it has moves, and no more. -/

section Sharpness

/-- The number of blocks of size `c` needed to cover `r` disturbances.-/
@[expose] public def blockCount (r c : ℕ) : ℕ := (r + c - 1) / c

/-- With at least one disturbance, the block count is one more than the last
block's index.-/
public theorem blockCount_eq {r c : ℕ} (hc : 0 < c) (hr : 0 < r) :
    blockCount r c = (r - 1) / c + 1 := by
  have hrw : r + c - 1 = (r - 1) + c := by omega
  rw [blockCount, hrw, Nat.add_div_right _ hc]

/-- Every disturbance lies in one of the blocks.-/
public theorem div_lt_blockCount {r c : ℕ} (hc : 0 < c) (d : Fin r) :
    (d : ℕ) / c < blockCount r c := by
  have hd : (d : ℕ) < r := d.isLt
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hd
  have hle : (d : ℕ) / c ≤ (r - 1) / c := Nat.div_le_div_right (by omega)
  rw [blockCount_eq hc hr]
  omega

/--
The witness table: the regulator's move shifts the disturbance's residue modulo
`c`, and leaves its block alone.-/
@[expose] public def shiftTable (r c : ℕ) (hc : 0 < c) :
    Fin r → ZMod c → Fin (blockCount r c) × ZMod c :=
  fun d k => (⟨(d : ℕ) / c, div_lt_blockCount hc d⟩, ((d : ℕ) : ZMod c) - k)

/-- The strategy that cancels the shift: answer each disturbance with its own
residue.-/
@[expose] public def shiftStrategy (r c : ℕ) : Fin r → ZMod c :=
  fun d => ((d : ℕ) : ZMod c)

end Sharpness

end Counting

end AISafetyAtlas.Control

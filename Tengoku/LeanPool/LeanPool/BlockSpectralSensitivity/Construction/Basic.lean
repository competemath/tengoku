/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku.LeanPool.LeanPool.BlockSpectralSensitivity.Defs.Sensitivity
public import Tengoku.LeanPool.LeanPool.BlockSpectralSensitivity.Defs.Subcube
public import Tengoku.LeanPool.LeanPool.BlockSpectralSensitivity.Defs.Tournament

/-!
# The construction

The coordinate set is `V = ι × Fin r`, where `ι` indexes the vertices of a tournament
(`Arc i j` says there is an arc `i → j`) and `Fin r` indexes the coordinates inside a
block.  For `i : ι` the *block* `B_i` is `{i} × Fin r`.

A *gate labelling* `γ : ι → ι → Fin r` picks, for every arc `i → j`, a coordinate
`gateCoord γ i j = (j, γ i j)` of the block `B_j`.

The certificate `C_i` is the subcube cut out by the partial assignment `cert Arc γ i`:

* every coordinate of `B_i` is fixed to `true`;
* for every arc `i → j`, the gate coordinate `(j, γ i j)` is fixed to `false`.

Finally `ind Arc γ` is the indicator of the union of the `C_i`.

This file only fixes the definitions and their basic combinatorics; the tournament
hypotheses are passed explicitly to the lemmas that need them, so that nothing here
depends on the particular (Paley) tournament used later.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda

namespace Construction

variable {ι : Type*} {r : ℕ}

/-! ### Coordinate blocks -/

/-- The coordinate set `V = ι × [r]` of the construction (Section 3). -/
abbrev Coord (ι : Type*) (r : ℕ) : Type _ := ι × Fin r

/-- The coordinate block `B_i = {i} × [r]` (Section 3). -/
def block (i : ι) : Finset (Coord ι r) := {i} ×ˢ Finset.univ

/--
@isnad1 id=iff.0h4v.s5.cffb6a454131 from=translated src=- shape=81d78359 vocab=17f1ffc6
-/
@[simp] lemma mem_block {i : ι} {v : Coord ι r} : v ∈ block i ↔ v.1 = i := by
  rw [block, Finset.mem_product]
  simp

/--
@isnad1 id=eq.0h3v.s4.fbcceffa6e35 from=translated src=- shape=48612997 vocab=e724ad7d
-/
@[simp] lemma card_block (i : ι) : (block i : Finset (Coord ι r)).card = r := by
  simp [block]

/--
@isnad1 id=nonempty.0h3v.s4.5c25a3440b5c from=translated src=- shape=7fc9bceb vocab=59fdd7d8
-/
lemma block_nonempty [NeZero r] (i : ι) : (block i : Finset (Coord ι r)).Nonempty :=
  (Finset.singleton_nonempty i).product Finset.univ_nonempty

/--
@isnad1 id=disjoint.1h4v.s5.9652f3d527d1 from=translated src=- shape=eb445815 vocab=cd123172
-/
lemma block_disjoint {i j : ι} (h : i ≠ j) :
    Disjoint (block i : Finset (Coord ι r)) (block j) :=
  Finset.disjoint_left.2 fun _ hv hv' ↦ h ((mem_block.1 hv).symm.trans (mem_block.1 hv'))

/-! ### Gate coordinates -/

/-- The gate coordinate `(j, γ(i,j))` selected by the arc `i → j` (Section 3.1). -/
def gateCoord (γ : ι → ι → Fin r) (i j : ι) : Coord ι r := (j, γ i j)

/--
@isnad1 id=eq.0h5v.s4.f68363624e3d from=translated src=- shape=531f810b vocab=8152df8a
-/
@[simp] lemma gateCoord_fst (γ : ι → ι → Fin r) (i j : ι) : (gateCoord γ i j).1 = j := rfl

/--
@isnad1 id=injectiv.0h4v.s4.b3c98473e56d from=translated src=- shape=53166a1d vocab=67f17c18
-/
lemma gateCoord_injective (γ : ι → ι → Fin r) (i : ι) :
    Function.Injective (gateCoord γ i) := fun _ _ h ↦ congrArg Prod.fst h

/-- A coordinate carrying the gate label of the arc `i → v.1` *is* that gate coordinate.
@isnad1 id=eq.1h5v.s5.7c1bbeda310d from=translated src=- shape=6eab6194 vocab=a19ee520
-/
lemma gateCoord_fst_eq_self {γ : ι → ι → Fin r} {i : ι} {v : Coord ι r} (h : v.2 = γ i v.1) :
    gateCoord γ i v.1 = v := Prod.ext rfl h.symm

/-! ### The certificates -/

section Cert

variable [DecidableEq ι]

/-- The partial assignment `P_i` cutting out the certificate `C_i` (Section 3.2):
the owner block `B_i` is fixed to `true`, and every outgoing gate coordinate is
fixed to `false`. -/
def cert (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) (i : ι) : PartialAssign (Coord ι r) :=
  fun v ↦ if v.1 = i then some true
    else if Arc i v.1 ∧ v.2 = γ i v.1 then some false else none

variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}

/-- The three-way case split describing `P_i`.
@isnad1 id=eq.0h6v.s7.2ffb6425df3f from=translated src=- shape=febf7624 vocab=a0a73531
-/
lemma cert_apply :
    cert Arc γ i v = if v.1 = i then some true
      else if Arc i v.1 ∧ v.2 = γ i v.1 then some false else none := rfl

/-- The literals of `P_i`: it fixes `v` to `true` on the owner block `B_i`, and to `false`
on the gate coordinate of an outgoing arc.  Every other lemma of this section is a
specialisation of this one.
@isnad1 id=iff.0h7v.s6.9251acc88370 from=translated src=- shape=19be7cde vocab=6b156b9a
-/
lemma cert_eq_some_iff :
    cert Arc γ i v = some b ↔
      (v.1 = i ∧ b = true) ∨ (v.1 ≠ i ∧ Arc i v.1 ∧ v.2 = γ i v.1 ∧ b = false) := by
  rw [cert_apply]
  split_ifs with h hg <;> simp_all

/-- Inside the owner block, `P_i` fixes the coordinate to `true`.
@isnad1 id=eq.1h6v.s5.f3ac10b83856 from=translated src=- shape=7cdcc5f7 vocab=afaf51d4
-/
lemma cert_apply_of_fst_eq (h : v.1 = i) : cert Arc γ i v = some true :=
  cert_eq_some_iff.2 (Or.inl ⟨h, rfl⟩)

/-- On a gate coordinate of an outgoing arc, `P_i` fixes the coordinate to `false`.
@isnad1 id=eq.2h6v.s5.93ddee3deee0 from=translated src=- shape=8ca99943 vocab=80688f0a
-/
lemma cert_apply_gateCoord (hji : j ≠ i) (hij : Arc i j) :
    cert Arc γ i (gateCoord γ i j) = some false :=
  cert_eq_some_iff.2 (Or.inr ⟨hji, hij, rfl, rfl⟩)

/-- Away from the owner block and from the outgoing gate coordinates, `P_i` is free.
@isnad1 id=eq.2h6v.s6.2f2b194752aa from=translated src=- shape=d17cdf0f vocab=5e06f972
-/
lemma cert_apply_eq_none (h₁ : v.1 ≠ i) (h₂ : ¬ (Arc i v.1 ∧ v.2 = γ i v.1)) :
    cert Arc γ i v = none := by
  simp [cert_apply, h₁, h₂]

/-- `P_i` never fixes a coordinate outside `B_i` to `true`.
@isnad1 id=ne.1h6v.s5.28d998f23e77 from=translated src=- shape=7cdcc5f7 vocab=afaf51d4
-/
lemma cert_ne_some_true_of_fst_ne (h : v.1 ≠ i) : cert Arc γ i v ≠ some true := by
  simp [cert_apply, h]

/-- Outside its owner block, the only coordinates `P_i` fixes are the gate coordinates
`(j, γ(i,j))` of its outgoing arcs `i → j`.
@isnad1 id=and.2h7v.s6.3c116556eb5c from=translated src=- shape=4fda9e9d vocab=9fbe4159
-/
lemma arc_and_snd_eq_of_cert_eq_some (h : v.1 ≠ i) (hb : cert Arc γ i v = some b) :
    Arc i v.1 ∧ v.2 = γ i v.1 := by
  obtain ⟨-, ha, hg, -⟩ := (cert_eq_some_iff.1 hb).resolve_left fun hc ↦ h hc.1
  exact ⟨ha, hg⟩

/-- Membership in the certificate subcube `C_i`, spelled out (Section 3.2).
@isnad1 id=iff.0h6v.s6.ea6fc416de20 from=translated src=- shape=0a4f54d6 vocab=a3a54f8c
-/
lemma sat_cert_iff {x : Input (Coord ι r)} :
    (cert Arc γ i).Sat x ↔
      (∀ a : Fin r, x (i, a) = true) ∧
        ∀ j, j ≠ i → Arc i j → x (gateCoord γ i j) = false := by
  refine ⟨fun hx ↦ ⟨fun a ↦ hx _ true (cert_apply_of_fst_eq rfl),
    fun j hji hij ↦ hx _ false (cert_apply_gateCoord hji hij)⟩, ?_⟩
  rintro ⟨h1, h2⟩ v b hv
  rcases cert_eq_some_iff.1 hv with ⟨h, rfl⟩ | ⟨h, ha, hg, rfl⟩
  · subst h
    simpa using h1 v.2
  · rw [← gateCoord_fst_eq_self hg]
    exact h2 v.1 h ha

end Cert

/-! ### The fixed coordinates of a certificate -/

section Fintype

variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}

/-- The set of coordinates fixed by `P_i`: the owner block together with the outgoing
gate coordinates (Section 3.2).  No irreflexivity hypothesis is needed; a self-arc `i → i`
would just put its gate coordinate in the owner block as well.
@isnad1 id=eq.0h5v.s6.17842b450ffa from=translated src=- shape=9194f386 vocab=23177df2
-/
lemma fixedSet_cert :
    (cert Arc γ i).fixedSet = block i ∪ (outNbrs Arc i).image (gateCoord γ i) := by
  ext v
  simp only [PartialAssign.mem_fixedSet_iff_ne_none, Finset.mem_union, mem_block,
    Finset.mem_image, mem_outNbrs]
  constructor
  · intro hv
    by_cases h₁ : v.1 = i
    · exact Or.inl h₁
    · by_cases h₂ : Arc i v.1 ∧ v.2 = γ i v.1
      · exact Or.inr ⟨v.1, h₂.1, gateCoord_fst_eq_self h₂.2⟩
      · exact absurd (cert_apply_eq_none h₁ h₂) hv
  · rintro (h | ⟨j, hj, rfl⟩)
    · simp [cert_apply_of_fst_eq h]
    · rcases eq_or_ne j i with rfl | hji
      · simp [cert_apply, gateCoord]
      · simp [cert_apply_gateCoord hji hj]

/-- The owner block `B_i` is disjoint from the outgoing gate coordinates: the gate
coordinate of the arc `i → j` lies in the block `B_j`, and `j ≠ i`.
@isnad1 id=disjoint.1h5v.s6.69077b51626f from=translated src=- shape=cdcd07ce vocab=cdb5f5fd
-/
lemma disjoint_block_image_gateCoord (hT : IsTournament Arc) :
    Disjoint (block i : Finset (Coord ι r)) ((outNbrs Arc i).image (gateCoord γ i)) := by
  refine Finset.disjoint_left.2 fun v hv hv' ↦ ?_
  simp only [Finset.mem_image, mem_outNbrs] at hv'
  obtain ⟨j, hj, rfl⟩ := hv'
  rw [mem_block, gateCoord_fst] at hv
  exact hT.ne_of_arc' hj hv

/-- The codimension of every certificate is `r + outdeg(i)` (Section 3.2: `c = r + d`).
@isnad1 id=eq.1h5v.s6.41a515d7a9d0 from=translated src=- shape=31a75bf4 vocab=8015f8a6
-/
lemma codim_cert (hT : IsTournament Arc) :
    (cert Arc γ i).codim = r + (outNbrs Arc i).card := by
  rw [PartialAssign.codim_eq_card_fixedSet, fixedSet_cert,
    Finset.card_union_of_disjoint (disjoint_block_image_gateCoord hT), card_block,
    Finset.card_image_of_injective _ (gateCoord_injective γ i)]

/-! ### The function `f`

`ind` is a distinct head symbol from `PartialAssign.indUnion`, so the `simp` lemmas of the
latter do not fire on it; the three lemmas below restate them for `ind`.
-/

/-- The Boolean function `f`: the indicator of the union of the certificate subcubes
`C_i` (Section 3.3). -/
def ind (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) : Input (Coord ι r) → Bool :=
  PartialAssign.indUnion (cert Arc γ)

variable {x : Input (Coord ι r)}

/-- A point is positive exactly when some certificate subcube contains it.
@isnad1 id=iff.0h5v.s5.104de1254273 from=translated src=- shape=88228e1e vocab=6855bc15
-/
@[simp] lemma ind_eq_true_iff : ind Arc γ x = true ↔ ∃ i, (cert Arc γ i).Sat x :=
  PartialAssign.indUnion_eq_true_iff

/-- A point is negative exactly when no certificate subcube contains it.
@isnad1 id=iff.0h5v.s5.e97a7a1ef107 from=translated src=- shape=377d0454 vocab=2f586915
-/
@[simp] lemma ind_eq_false_iff : ind Arc γ x = false ↔ ∀ i, ¬ (cert Arc γ i).Sat x :=
  PartialAssign.indUnion_eq_false_iff

/-- Every point of a certificate subcube is positive.
@isnad1 id=eq.1h6v.s5.f3293fbba4b3 from=translated src=- shape=f91fe948 vocab=6855bc15
-/
lemma ind_eq_true_of_sat (h : (cert Arc γ i).Sat x) : ind Arc γ x = true :=
  PartialAssign.indUnion_eq_true_of_sat h

end Fintype

end Construction

end BSLambda

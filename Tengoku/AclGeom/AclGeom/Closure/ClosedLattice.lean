/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Closure.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complete lattice of relatively algebraically closed intermediate fields

For a field extension `K/k`, this file defines:

* `IsRAC E`: the intermediate field `E` is relatively algebraically closed in
  `K` — every element of `K` algebraic over `E` lies in `E`;
* `ClosedIF k K`: the type of relatively algebraically closed intermediate
  fields, the lattice `𝒢(K/k)` of the blueprint;
* `ClosedIF.gi`: `racl` is a Galois insertion onto `ClosedIF k K`, from which
  the complete lattice structure is lifted. By construction, infima are
  intersections of intermediate fields and suprema are relative closures of
  composita (blueprint Prop `closed-complete-lattice`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the complete lattice and same-base transport are proved (M1, F3).
Compatible transport across different base fields is in `Closure.CrossBase`.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

/-- An intermediate field `E` of `K/k` is *relatively algebraically closed*
if every element of `K` algebraic over `E` already lies in `E`.-/
def IsRAC (E : IntermediateField k K) : Prop :=
  ∀ x : K, IsAlgebraic E x → x ∈ E

theorem IsRAC.mem_of_isAlgebraic {E : IntermediateField k K} (hE : IsRAC E) {x : K}
    (hx : IsAlgebraic E x) : x ∈ E := hE x hx

/-- A relatively algebraically closed intermediate field contains any element
some positive power of which it contains (via the annihilating polynomial
`X ^ m - C (x ^ m)`).-/
theorem IsRAC.mem_of_pow_mem {E : IntermediateField k K} (hE : IsRAC E) {x : K}
    {m : ℕ} (hm : m ≠ 0) (hx : x ^ m ∈ E) : x ∈ E := by
  refine hE x (isAlgebraic_of_coeff_mem
    (p := Polynomial.X ^ m - Polynomial.C (x ^ m))
    (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hm) _) (by simp) fun n ↦ ?_)
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  rcases eq_or_ne n m with rfl | hnm
  · simp [hm]
  · rcases eq_or_ne n 0 with rfl | hn0
    · simpa [hnm] using neg_mem hx
    · simp [hnm, hn0]

/-- `E` is relatively algebraically closed iff it is a fixed point of the
relative algebraic closure operator.-/
theorem isRAC_iff_racl_eq {E : IntermediateField k K} :
    IsRAC E ↔ racl k (E : Set K) = E := by
  constructor
  · intro hE
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ subset_racl k _ hx)
    rw [mem_racl_iff, adjoin_self] at hx
    exact hE x hx
  · intro hE x hx
    rw [← hE, mem_racl_iff, adjoin_self]
    exact hx

/-- The relative algebraic closure of any set is relatively algebraically
closed.-/
theorem isRAC_racl (S : Set K) : IsRAC (racl k S) := by
  intro x hx
  have : x ∈ racl k (racl k S : Set K) := by
    rw [mem_racl_iff, adjoin_self]
    exact hx
  rwa [racl_racl] at this

variable (k K) in
/-- The lattice `𝒢(K/k)` of relatively algebraically closed intermediate
fields of `K/k` (blueprint §Foundation II).-/
def ClosedIF := {E : IntermediateField k K // IsRAC E}

namespace ClosedIF

instance : SetLike (ClosedIF k K) K where
  coe E := (E.1 : Set K)
  coe_injective _ _ h := Subtype.ext (SetLike.coe_injective h)

@[simp] theorem mem_val {E : ClosedIF k K} {x : K} : x ∈ E.1 ↔ x ∈ E := Iff.rfl

@[simp] theorem coe_val (E : ClosedIF k K) : (E.1 : Set K) = (E : Set K) := rfl

instance : PartialOrder (ClosedIF k K) :=
  Subtype.partialOrder _

theorem le_iff {E F : ClosedIF k K} : E ≤ F ↔ E.1 ≤ F.1 := Iff.rfl

variable (k) in
/-- The relative algebraic closure, as a map from intermediate fields to
relatively algebraically closed intermediate fields. This is the lower adjoint
of the inclusion.-/
def close (E : IntermediateField k K) : ClosedIF k K :=
  ⟨racl k (E : Set K), isRAC_racl _⟩

/-- `close` and the inclusion form a Galois insertion; the complete lattice
structure on `ClosedIF k K` is lifted along it.-/
def gi : GaloisInsertion (close k (K := K)) Subtype.val where
  choice E hE := ⟨E, isRAC_iff_racl_eq.2 (le_antisymm hE (fun x hx ↦ subset_racl k _ hx))⟩
  gc E F := by
    rw [le_iff]
    constructor
    · intro h
      exact le_trans (fun x hx ↦ subset_racl k _ hx) h
    · intro h
      calc racl k (E : Set K) ≤ racl k (F.1 : Set K) := racl_mono h
      _ = F.1 := isRAC_iff_racl_eq.1 F.2
  le_l_u F := fun x hx ↦ subset_racl k _ hx
  choice_eq E hE := Subtype.ext
    (le_antisymm (fun x hx ↦ subset_racl k _ hx) hE)

instance : CompleteLattice (ClosedIF k K) :=
  gi.liftCompleteLattice

/-- Infima in `𝒢(K/k)` are intersections of intermediate fields
(blueprint Prop `closed-complete-lattice`).-/
@[simp] theorem coe_sInf (s : Set (ClosedIF k K)) :
    ((sInf s).1 : IntermediateField k K) = sInf (Subtype.val '' s) := rfl

@[simp] theorem coe_top : ((⊤ : ClosedIF k K).1 : IntermediateField k K) = ⊤ := rfl

/-- The bottom of `𝒢(K/k)` is the relative algebraic closure of the bottom
intermediate field, i.e. of (the image of) `k` itself. Under the standing
hypothesis that `k` is relatively algebraically closed in `K`, this is `k`.-/
theorem coe_bot : ((⊥ : ClosedIF k K).1 : IntermediateField k K) =
    racl k ((⊥ : IntermediateField k K) : Set K) := rfl

/-- Membership in the bottom of the closed lattice is algebraicity over the
base field. In particular, under the blueprint's hypothesis that `k` is
relatively algebraically closed in `K`, the bottom is the image of `k`.-/
theorem mem_bot_iff {x : K} :
    x ∈ (⊥ : ClosedIF k K) ↔ IsAlgebraic k x := by
  change x ∈ ((⊥ : ClosedIF k K)).1 ↔ _
  rw [coe_bot, mem_racl_iff, adjoin_self]
  constructor
  · intro h
    have hbot : Algebra.IsIntegral k (⊥ : IntermediateField k K) := by
      constructor
      intro y
      obtain ⟨z, hz⟩ := IntermediateField.mem_bot.1 y.2
      have : IsIntegral k (y : K) := hz ▸ isIntegral_algebraMap
      exact (isIntegral_algHom_iff (⊥ : IntermediateField k K).val
        Subtype.val_injective).1 this
    rw [isAlgebraic_iff_isIntegral] at h ⊢
    exact isIntegral_trans x h
  · intro h
    exact h.tower_top _

section Transport

variable {L : Type*} [Field L] [Algebra k L]

/-- Relative algebraic closedness is preserved by `k`-algebra isomorphisms.-/
theorem _root_.AclGeom.IsRAC.map {E : IntermediateField k K} (hE : IsRAC E)
    (σ : K ≃ₐ[k] L) : IsRAC (E.map σ.toAlgHom) := by
  rw [isRAC_iff_racl_eq] at hE ⊢
  calc racl k ((E.map σ.toAlgHom : IntermediateField k L) : Set L)
      = racl k (σ '' (E : Set K)) := by rw [IntermediateField.coe_map]; rfl
    _ = (racl k (E : Set K)).map σ.toAlgHom := (racl_map σ (E : Set K)).symm
    _ = E.map σ.toAlgHom := by rw [hE]

/-- Transport of the closed lattice along a `k`-algebra isomorphism of
extensions (blueprint Prop `closed-complete-lattice`, last clause). For
extensions over different base fields, use `CrossBase.closedIFMap` with
its explicit compatibility hypothesis.-/
def congr (σ : K ≃ₐ[k] L) : ClosedIF k K ≃o ClosedIF k L where
  toFun E := ⟨E.1.map σ.toAlgHom, E.2.map σ⟩
  invFun F := ⟨F.1.map σ.symm.toAlgHom, F.2.map σ.symm⟩
  left_inv E := Subtype.ext <| by
    ext x
    simp [IntermediateField.mem_map]
  right_inv F := Subtype.ext <| by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨σ.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' {E F} := by
    rw [le_iff, le_iff]
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h ⟨x, hx, rfl⟩
      rwa [← σ.injective hyx]
    · rintro h - ⟨x, hx, rfl⟩
      exact ⟨x, h hx, rfl⟩

end Transport

theorem mem_sInf {s : Set (ClosedIF k K)} {x : K} :
    x ∈ sInf s ↔ ∀ E ∈ s, x ∈ E := by
  change x ∈ (sInf s).1 ↔ _
  rw [coe_sInf, IntermediateField.mem_sInf]
  constructor
  · intro h E hE
    exact h E.1 ⟨E, hE, rfl⟩
  · rintro h - ⟨E, hE, rfl⟩
    exact h E hE

/-- The binary supremum is the relative algebraic closure of the union.-/
theorem coe_sup (E F : ClosedIF k K) :
    ((E ⊔ F).1 : IntermediateField k K) = racl k ((E : Set K) ∪ F) := by
  refine le_antisymm ?_ ?_
  · have h : E ⊔ F ≤ ⟨racl k ((E : Set K) ∪ F), isRAC_racl _⟩ := by
      refine sup_le (le_iff.2 ?_) (le_iff.2 ?_)
      · calc E.1 ≤ racl k (E : Set K) := fun x hx ↦ subset_racl k _ hx
          _ ≤ racl k ((E : Set K) ∪ F) := racl_mono Set.subset_union_left
      · calc F.1 ≤ racl k (F : Set K) := fun x hx ↦ subset_racl k _ hx
          _ ≤ racl k ((E : Set K) ∪ F) := racl_mono Set.subset_union_right
    exact le_iff.1 h
  · have hsub : (E : Set K) ∪ F ⊆ ((E ⊔ F).1 : Set K) :=
      Set.union_subset (le_iff.1 le_sup_left) (le_iff.1 le_sup_right)
    calc racl k ((E : Set K) ∪ F) ≤ racl k ((E ⊔ F).1 : Set K) :=
          racl_mono hsub
      _ = (E ⊔ F).1 := isRAC_iff_racl_eq.1 (E ⊔ F).2

/-- Membership in a binary supremum, via the closure of the union.-/
theorem mem_sup_iff {E F : ClosedIF k K} {x : K} :
    x ∈ E ⊔ F ↔ x ∈ racl k ((E : Set K) ∪ F) := by
  change x ∈ ((E ⊔ F).1 : IntermediateField k K) ↔ _
  rw [coe_sup]

/-- The set-level form of `coe_sup`, for rewriting inside `racl`
arguments.-/
theorem coe_set_sup (E F : ClosedIF k K) :
    ((E ⊔ F : ClosedIF k K) : Set K) =
      (racl k ((E : Set K) ∪ F) : Set K) := by
  have h := coe_sup E F
  calc ((E ⊔ F : ClosedIF k K) : Set K) = ((E ⊔ F).1 : Set K) := rfl
    _ = (racl k ((E : Set K) ∪ F) : Set K) := by rw [h]

/-- Membership in a binary infimum.-/
theorem mem_inf_iff {E F : ClosedIF k K} {x : K} :
    x ∈ E ⊓ F ↔ x ∈ E ∧ x ∈ F := by
  rw [← sInf_pair, mem_sInf]
  constructor
  · intro h
    exact ⟨h E (by simp), h F (by simp)⟩
  · rintro ⟨h1, h2⟩ G hG
    rcases Set.mem_insert_iff.1 hG with rfl | hG
    · exact h1
    · rw [Set.mem_singleton_iff.1 hG]
      exact h2

/-- Sandwich form: a closed element bounded above by the closure of `S`
and containing `S` has the closure of `S` as its underlying field.-/
theorem coe_eq_racl_of_le {E : ClosedIF k K} {S : Set K}
    (h1 : E ≤ ⟨racl k S, isRAC_racl _⟩) (h2 : S ⊆ (E : Set K)) :
    (E.1 : IntermediateField k K) = racl k S := by
  refine le_antisymm (le_iff.1 h1) ?_
  calc racl k S ≤ racl k (E : Set K) := racl_mono h2
    _ = E.1 := isRAC_iff_racl_eq.1 E.2

end ClosedIF

end

end AclGeom

/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DoubleCoset

/-!
# The arithmetic Hecke triple for `GL_n`

The canonical arithmetic Hecke triple in `GL_n(ℚ)`, following [Shimura][shimura1971] §3.2:
`H = SL_n(ℤ)` (embedded via `mapGL ℚ`) and `Δ` the submonoid of integral matrices with
positive determinant. The heart is **Shimura's Lemma 3.10**
(`posDetInt_le_commensurator`): `Δ` lies in the commensurator of `SL_n(ℤ)`, because for an
integral `α` with `det α = d ≠ 0` the congruence subgroup
`Γ(d) = ker(SL_n(ℤ) → SL_n(ℤ/dℤ))` has finite index and has conjugates in both directions
contained in `SL_n(ℤ)` — since `α⁻¹ = adj(α)/d` and `γ ≡ 1 mod d`.
The file ends with the resulting `IsHeckeTriple` instance, on which the Hecke ring
`𝕋 Δ SL_n(ℤ) ℤ` of `GL_n` is founded.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/Basic.lean`, Chris Birkbeck), realizing the Layer-2
substrate of the ModularForms roadmap (the `GL₂` case specializes to the Hecke operators on
modular forms); the AINTLIB `HeckePair` bundle is replaced by Mathlib's `IsHeckeTriple`.

## Main definitions

* `SLnZ`: `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`, via `mapGL ℚ`.
* `posDetInt`: integral matrices with positive determinant, Shimura's `Δ`.

## Main results

* `SLnZ_le_posDetInt`: `SL_n(ℤ) ≤ Δ`.
* `posDetInt_le_commensurator`: `Δ ≤ commensurator(SL_n(ℤ))` (Shimura's Lemma 3.10).
* `commensurable_map_SLnZ`: the image of a finite-index subgroup of `SL_n(ℤ)` is commensurable
  with `SL_n(ℤ)` — the step by which each congruence subgroup inherits Lemma 3.10 and so sits
  in a Hecke triple of its own.
* `mem_doubleCoset_of_intMatrix_eq_of_mem`: double-coset membership from an integral identity
  `τ * A * δ = B` between the witnesses, for any two subgroups containing the images of `τ` and
  `δ`. `mem_doubleCoset_SLnZ_of_intMatrix_eq` is its `SL_n(ℤ)` case, and
  `det_eq_of_mem_doubleCoset_of_le_SLnZ` extracts the determinant invariant in the other
  direction.
* the `IsHeckeTriple (posDetInt n) (SLnZ n) (SLnZ n)` instance, and the
  Hecke ring `IntegralHeckeRing n` it founds.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
-/

public section

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

section Embedding

/-- `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`, via `mapGL ℚ : SL(n, ℤ) →* GL(n, ℚ)`.
    Following mathlib's pattern for arithmetic subgroups. -/
noncomputable def SLnZ : Subgroup (GL (Fin n) ℚ) :=
  (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ).range

/-- Coercion from `SL_n(ℤ)` to `GL_n(ℚ)` via `mapGL ℚ`. -/
noncomputable scoped instance coeMapGLRat :
    Coe (SpecialLinearGroup (Fin n) ℤ) (GL (Fin n) ℚ) :=
  ⟨mapGL ℚ⟩

/-- The canonical membership: integral special-linear matrices land in `SL_n(ℤ)`. Not a
`simp` lemma: `mem_SLnZ_iff` subsumes it as a normal form. -/
lemma coe_mem_SLnZ (σ : SpecialLinearGroup (Fin n) ℤ) :
    (σ : GL (Fin n) ℚ) ∈ SLnZ n := ⟨σ, rfl⟩

/-- Membership in `SL_n(ℤ)` characterised by an integral special-linear witness: the
elimination principle paired with `coe_mem_SLnZ`. `SLnZ` is a sealed definition, so modules
downstream cannot unfold it to `MonoidHom.range`; this lemma is how they extract the witness. -/
@[simp] lemma mem_SLnZ_iff {g : GL (Fin n) ℚ} :
    g ∈ SLnZ n ↔ ∃ σ : SpecialLinearGroup (Fin n) ℤ, (σ : GL (Fin n) ℚ) = g := by
  rw [SLnZ, MonoidHom.mem_range]

/-- An element of `SL_n(ℤ)` has matrix determinant one over `ℚ`.

`SpecialLinearGroup.det_mapGL` is the same fact for `GeneralLinearGroup.det`, which is
`ℚˣ`-valued; every consumer needs the `Matrix.det` of the coerced matrix, so this is the
`Units.val` bridge rather than a second proof. -/
lemma det_eq_one_of_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    (↑g : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff n).mp hg
  exact congrArg Units.val (SpecialLinearGroup.det_mapGL (S := ℚ) σ)

/-- **Integral representatives survive two-sided integral translation.** If `A` represents
`g ∈ GL_n(ℚ)` entrywise over `ℤ`, then `τ * A * δ` represents `mapGL τ * g * mapGL δ` for any
`τ δ : SL_n(ℤ)`.

Nothing here is specific to a level or a dimension: it is the statement that the entrywise
`ℤ → ℚ` cast is multiplicative, packaged for the two-sided translations that every
change-of-representative argument performs. -/
lemma mapGL_mul_coe_eq_intMatrix (τ δ : SpecialLinearGroup (Fin n) ℤ)
    (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    (↑(mapGL ℚ τ * g * mapGL ℚ δ) : Matrix (Fin n) (Fin n) ℚ) =
      ((τ : Matrix (Fin n) (Fin n) ℤ) * A * (δ : Matrix (Fin n) (Fin n) ℤ)).map
        (Int.cast : ℤ → ℚ) := by
  have h₁ := map_mul (Int.castRingHom ℚ).mapMatrix
    ((τ : Matrix (Fin n) (Fin n) ℤ) * A) (δ : Matrix (Fin n) (Fin n) ℤ)
  have h₂ := map_mul (Int.castRingHom ℚ).mapMatrix (τ : Matrix (Fin n) (Fin n) ℤ) A
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h₁ h₂
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hA]
  rw [h₁, h₂]

-- Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
-- `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
-- `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`, declaration
-- `gl_eq_of_intMat_eq`. The source states it privately at `Fin 2` and proves it entrywise; at
-- general `n` it is a consequence of `mapGL_mul_coe_eq_intMatrix` above, and the double-coset
-- form its callers want is added alongside.
/-- **Lifting an integral equivalence to `GL_n(ℚ)`.** The converse reading of
`mapGL_mul_coe_eq_intMatrix`: if the integral witnesses of `g` and `h` are related by
`τ * A * δ = B` with `τ`, `δ` of determinant one, then `h` *is* the two-sided translate
of `g`.

`mapGL_mul_coe_eq_intMatrix` computes the matrix of a translate; this recovers the translate
from its matrix, which is what a change-of-representative argument actually needs — such an
argument produces an integral identity and must conclude an identity in `GL_n(ℚ)`. -/
lemma eq_mapGL_mul_mul_mapGL_of_intMatrix_eq (τ δ : SpecialLinearGroup (Fin n) ℤ)
    (g h : GL (Fin n) ℚ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (↑h : Matrix (Fin n) (Fin n) ℚ) = B.map (Int.cast : ℤ → ℚ))
    (hτδ : (τ : Matrix (Fin n) (Fin n) ℤ) * A * (δ : Matrix (Fin n) (Fin n) ℤ) = B) :
    h = mapGL ℚ τ * g * mapGL ℚ δ :=
  Units.ext (by rw [hB, ← hτδ, ← mapGL_mul_coe_eq_intMatrix n τ δ g A hA])

/-- **Double-coset membership from an integral equivalence.** Integral matrices of determinant
one relating the witnesses of `g` and `h` put `h` in the `H₁`-`H₂`-double coset of `g`, for any
two subgroups containing the images of those matrices.

This is the shape every "same double coset" argument ends in: the work is done over `ℤ`, by
exhibiting the two determinant-one factors, and this converts that into the membership
statement. Nothing forces the subgroups to be `SL_n(ℤ)` — all that is used is that each factor
lies in its own subgroup, which is a hypothesis here, so the lemma applies equally to images of
congruence subgroups.
`det_eq_of_mem_doubleCoset_of_le_SLnZ` is the companion in the other direction, extracting the
determinant invariant from such a membership. -/
lemma mem_doubleCoset_of_intMatrix_eq_of_mem {H₁ H₂ : Subgroup (GL (Fin n) ℚ)}
    (τ δ : SpecialLinearGroup (Fin n) ℤ) (hτ : mapGL ℚ τ ∈ H₁) (hδ : mapGL ℚ δ ∈ H₂)
    (g h : GL (Fin n) ℚ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (↑h : Matrix (Fin n) (Fin n) ℚ) = B.map (Int.cast : ℤ → ℚ))
    (hτδ : (τ : Matrix (Fin n) (Fin n) ℤ) * A * (δ : Matrix (Fin n) (Fin n) ℤ) = B) :
    h ∈ DoubleCoset.doubleCoset g H₁ H₂ :=
  DoubleCoset.mem_doubleCoset.mpr
    ⟨mapGL ℚ τ, hτ, mapGL ℚ δ, hδ,
      eq_mapGL_mul_mul_mapGL_of_intMatrix_eq n τ δ g h A B hA hB hτδ⟩

/-- The `SL_n(ℤ)` case of `mem_doubleCoset_of_intMatrix_eq_of_mem`, where the two factors lie in
the subgroups for free. -/
lemma mem_doubleCoset_SLnZ_of_intMatrix_eq (τ δ : SpecialLinearGroup (Fin n) ℤ)
    (g h : GL (Fin n) ℚ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (↑h : Matrix (Fin n) (Fin n) ℚ) = B.map (Int.cast : ℤ → ℚ))
    (hτδ : (τ : Matrix (Fin n) (Fin n) ℤ) * A * (δ : Matrix (Fin n) (Fin n) ℤ) = B) :
    h ∈ DoubleCoset.doubleCoset g (SLnZ n) (SLnZ n) :=
  mem_doubleCoset_of_intMatrix_eq_of_mem n τ δ (coe_mem_SLnZ n τ) (coe_mem_SLnZ n δ)
    g h A B hA hB hτδ

/-- The case of coefficient subgroups inside `SL_n(ℤ)`, which is how the congruence subgroups
get it. -/
lemma det_eq_of_mem_doubleCoset_of_le_SLnZ {H₁ H₂ : Subgroup (GL (Fin n) ℚ)}
    (h₁ : H₁ ≤ SLnZ n) (h₂ : H₂ ≤ SLnZ n) {a b : GL (Fin n) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a H₁ H₂) :
    (↑b : Matrix (Fin n) (Fin n) ℚ).det = (↑a : Matrix (Fin n) (Fin n) ℚ).det :=
  DoubleCoset.det_eq_of_mem_doubleCoset_of_det_eq_one
    (fun _ hγ ↦ det_eq_one_of_mem_SLnZ n (h₁ hγ)) (fun _ hγ ↦ det_eq_one_of_mem_SLnZ n (h₂ hγ)) hb

/-- The `SL_n(ℤ)` case of `det_eq_of_mem_doubleCoset_of_le_SLnZ`. -/
lemma det_eq_of_mem_doubleCoset_SLnZ {a b : GL (Fin n) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a (SLnZ n) (SLnZ n)) :
    (↑b : Matrix (Fin n) (Fin n) ℚ).det = (↑a : Matrix (Fin n) (Fin n) ℚ).det :=
  det_eq_of_mem_doubleCoset_of_le_SLnZ n le_rfl le_rfl hb

/-- The image in `GL_n(ℚ)` of a finite-index subgroup of `SL_n(ℤ)` is commensurable with
`SL_n(ℤ)`. Since `mapGL ℚ` is injective, both relative indices transport along it: one is the
index of `H`, finite by hypothesis, and the other is `1`.

This is the commensurability every congruence subgroup needs in order to sit in a Hecke
triple, so it is stated once here for an arbitrary finite-index subgroup rather than
re-proved at each of `Γ₀(N)`, `Γ₁(N)`, `Γ(N)`. -/
lemma commensurable_map_SLnZ (H : Subgroup (SpecialLinearGroup (Fin n) ℤ)) [H.FiniteIndex] :
    Subgroup.Commensurable (H.map (mapGL ℚ)) (SLnZ n) := by
  constructor
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, SLnZ, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, SLnZ, MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_left]
    exact one_ne_zero

end Embedding

section PosDetInt

/-- An element of `GL_n(ℚ)` has integer matrix entries if its underlying matrix
    is the image of an integer matrix under `ℤ → ℚ`. -/
def HasIntEntries (g : GL (Fin n) ℚ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℤ,
    (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ)

/-- Characteristic lemma for `HasIntEntries`: introduction and elimination via the
integer-matrix witness, without exposing the definition body. -/
@[simp]
lemma hasIntEntries_iff {g : GL (Fin n) ℚ} :
    HasIntEntries n g ↔ ∃ A : Matrix (Fin n) (Fin n) ℤ,
      (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ) :=
  (Iff.rfl)

lemma hasIntEntries_of_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    HasIntEntries n g :=
  let ⟨σ, hσ⟩ := hg
  ⟨σ.val, hσ ▸ by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

/-- The identity matrix has integer entries. -/
lemma hasIntEntries_one : HasIntEntries n (1 : GL (Fin n) ℚ) :=
  ⟨1, by ext i j; simp [Matrix.map_apply, Matrix.one_apply]⟩

/-- Product of integer-entry matrices has integer entries. -/
lemma HasIntEntries.mul {a b : GL (Fin n) ℚ} (ha : HasIntEntries n a) (hb : HasIntEntries n b) :
    HasIntEntries n (a * b) :=
  let ⟨A, hA⟩ := ha; let ⟨B, hB⟩ := hb
  ⟨A * B, by ext i j; simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]⟩

/-- The submonoid of `GL_n(ℚ)` with integer matrix entries. -/
noncomputable def intEntries : Submonoid (GL (Fin n) ℚ) where
  carrier := {g | HasIntEntries n g}
  one_mem' := hasIntEntries_one n
  mul_mem' := fun ha hb ↦ HasIntEntries.mul (n := n) ha hb

@[simp]
lemma mem_intEntries {g : GL (Fin n) ℚ} : g ∈ intEntries n ↔ HasIntEntries n g := (Iff.rfl)

/-- The submonoid of `GL_n(ℚ)` consisting of invertible matrices with integer entries
and positive determinant — Shimura's `Δ`, as the integral-entry part of Mathlib's
positive-determinant subgroup `Matrix.GLPos`. -/
noncomputable def posDetInt : Submonoid (GL (Fin n) ℚ) :=
  intEntries n ⊓ (Matrix.GLPos (Fin n) ℚ).toSubmonoid

/-- Membership in `Δ`: integer entries and positive determinant. -/
@[simp]
lemma mem_posDetInt_iff {g : GL (Fin n) ℚ} :
    g ∈ posDetInt n ↔
      HasIntEntries n g ∧ 0 < (↑g : Matrix (Fin n) (Fin n) ℚ).det := by
  simp [posDetInt, Submonoid.mem_inf, Matrix.mem_glpos,
    Matrix.GeneralLinearGroup.val_det_apply]

/-- `posDetInt n` is contained in the positive-determinant submonoid, forgetting integrality.
`posDetInt n` is defined as a meet, so this is one projection of it — but the meet is not visible
outside this file (`posDetInt` is not `@[expose]`), so consumers that need only positivity, and
not integrality, must go through this lemma. -/
lemma posDetInt_le_glpos : posDetInt n ≤ (Matrix.GLPos (Fin n) ℚ).toSubmonoid := inf_le_right

end PosDetInt

section Pair

/-- `SL_n(ℤ) ⊆ Δ`: elements of `SL_n(ℤ)` have integer entries and det = 1 > 0. -/
lemma SLnZ_le_posDetInt : (SLnZ n).toSubmonoid ≤ posDetInt n := by
  rintro g ⟨A, rfl⟩
  refine ⟨⟨A.val, by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩, ?_⟩
  simp

/-- `SL_n(ℤ)` has positive determinant, forgetting integrality — the composite of
`SLnZ_le_posDetInt` with `posDetInt_le_glpos`, for consumers that need only the determinant. -/
lemma SLnZ_le_glpos : SLnZ n ≤ Matrix.GLPos (Fin n) ℚ := fun _ h ↦
  posDetInt_le_glpos n (SLnZ_le_posDetInt n h)

variable [NeZero n]

end Pair

section API

open scoped HeckeCosetModule

/-- The Hecke ring of `GL_n` over `ℤ`: the Hecke ring of the arithmetic triple. -/
abbrev IntegralHeckeRing := 𝕋 (posDetInt n) (SLnZ n) ℤ

variable [NeZero n]

end API

end HeckeRing.GLn

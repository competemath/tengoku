/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Simplices

/-!
# Simplices that are uniquely codimensional one faces

Let `X` be a simplicial set. If `x : X _⦋d⦌` and `y : X _⦋d + 1⦌`,
we say that `x` is uniquely a `1`-codimensional face of `y` if there
exists a unique `i : Fin (d + 2)` such that `X.δ i y = x`. In this file,
we extend this to a predicate `IsUniquelyCodimOneFace` involving two terms
in the type `X.S` of simplices of `X`. This is used in the
file `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean` for the
study of strong (inner) anodyne extensions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet.S

variable {X : SSet.{u}} (x y : X.S)

/-- The property that a simplex is uniquely a `1`-codimensional face of another simplex -/
def IsUniquelyCodimOneFace : Prop :=
  y.dim = x.dim + 1 ∧ ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Mono f ∧ X.map f.op y.simplex = x.simplex

namespace IsUniquelyCodimOneFace

/--
@isnad1 id=iff.0h4v.s8.e23747f346d9 from=seed src=0 shape=0d0da4dc vocab=d5680e88
-/
lemma iff {d : ℕ} (x : X _⦋d⦌) (y : X _⦋d + 1⦌) :
    IsUniquelyCodimOneFace (S.mk x) (S.mk y) ↔
      ∃! (i : Fin (d + 2)), X.δ i y = x := by
  constructor
  · rintro ⟨_, ⟨f, ⟨_, h₁⟩, h₂⟩⟩
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    exact ⟨i, h₁, fun j hj ↦ SimplexCategory.δ_injective (h₂ _ ⟨inferInstance, hj⟩)⟩
  · rintro ⟨i, h₁, h₂⟩
    refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ ↦ ?_⟩
    obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    obtain rfl : j = i := h₂ _ h₄
    rfl

variable {x y} (hxy : IsUniquelyCodimOneFace x y)

include hxy in
/--
@isnad1 id=eq.1h3v.s5.fb23c84de582 from=seed src=0 shape=613e23f1 vocab=7b915206
-/
lemma dim_eq : y.dim = x.dim + 1 := hxy.1

section

variable {d : ℕ} (hd : x.dim = d)

/--
@isnad1 id=isunique.2h4v.s5.f15187722af3 from=seed src=0 shape=7139d54f vocab=7bb2ea4b
-/
lemma cast : IsUniquelyCodimOneFace (x.cast hd) (y.cast (d := d + 1) (by rw [hxy.dim_eq, hd])) := by
  simpa only [cast_eq_self]

/--
@isnad1 id=existsun.2h4v.s8.ff0fe2872b66 from=seed src=0 shape=e5f7c8cc vocab=5d97cae9
-/
lemma existsUnique_δ_cast_simplex :
    ∃! (i : Fin (d + 2)), X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex =
      (x.cast hd).simplex := by
  simpa only [S.cast, iff] using hxy.cast hd

include hxy in
/-- When a `d`-dimensional simplex `x` is a `1`-codimensional face of `y`, this is
the only `i : Fin (d + 2)`, such that `X.δ i y = x` (with an abuse of notation:
see `δ_index` and `δ_eq_iff` for well typed statements). -/
noncomputable def index : Fin (d + 2) :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose

/--
@isnad1 id=eq.2h4v.s8.8b5d2dc52dd7 from=seed src=0 shape=c1a4d825 vocab=e0555cb5
-/
lemma δ_index :
    X.δ (hxy.index hd) (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex :=
  (hxy.existsUnique_δ_cast_simplex hd).exists.choose_spec

/--
@isnad1 id=iff.2h5v.s8.7a35cc193e52 from=seed src=0 shape=b81555a5 vocab=2c0637e9
-/
lemma δ_eq_iff (i : Fin (d + 2)) :
    X.δ i (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex ↔
      i = hxy.index hd :=
  ⟨fun h ↦ (hxy.existsUnique_δ_cast_simplex hd).unique h (hxy.δ_index hd),
    by rintro rfl; apply δ_index⟩

include hxy in
/--
@isnad1 id=le.1h3v.s4.fbfd665c9da7 from=seed src=0 shape=3b276447 vocab=8e77aca4
-/
lemma le : x ≤ y := by
  have := hxy.δ_index rfl
  simp only [cast_simplex_rfl] at this
  rw [S.le_def, ← y.subcomplex_cast hxy.dim_eq, Subfunctor.ofSection_le_iff,
    ← this]
  exact ⟨(SimplexCategory.δ _).op, rfl⟩

set_option backward.defeqAttrib.useBackward true in
include hxy in
/--
@isnad1 id=eq.3h5v.s8.783d7657dbce from=seed src=0 shape=7dfbc8ed vocab=9bb673b0
-/
lemma unique (f : ⦋d⦌ ⟶ ⦋d + 1⦌) [Mono f]
    (hf : X.map f.op (y.cast (by rw [hxy.dim_eq, hd])).simplex = (x.cast hd).simplex) :
    f = SimplexCategory.δ (hxy.index hd) :=
  (hxy.cast hd).2.unique ⟨by dsimp; infer_instance, hf⟩
    ⟨by dsimp; infer_instance, hxy.δ_index hd⟩

end

include hxy in
/--
@isnad1 id=isunique.1h3v.s6.8cc3d2c7f019 from=seed src=0 shape=3e3347ce vocab=49ca37eb
-/
lemma op : (S.opEquiv.symm x).IsUniquelyCodimOneFace (S.opEquiv.symm y) := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  simp only [opEquiv_symm_apply, iff]
  refine ⟨(hxy.index rfl).rev, by simpa using hxy.δ_index rfl, fun i hi ↦ ?_⟩
  obtain ⟨i, rfl⟩ := i.rev_surjective
  simpa [← hxy.δ_eq_iff rfl] using hi

set_option backward.defeqAttrib.useBackward true in
include hxy in
/--
@isnad1 id=isunique.1h5v.s8.0d86a16d3add from=seed src=0 shape=7147c00d vocab=a8a7cb11
-/
lemma of_iso {Y : SSet.{u}} (e : X ≅ Y) :
    (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := hxy.dim_eq
  rw [iff] at hxy ⊢
  simpa [← SSet.δ_naturality_apply, dsimp% (e.app (Opposite.op ⦋d⦌)).toEquiv.apply_eq_iff_eq]

/--
@isnad1 id=iff.0h5v.s8.4685478f6316 from=seed src=0 shape=fe44668d vocab=a8a7cb11
-/
lemma iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) (x y : X.S) :
    (S.mk (e.hom.app _ x.simplex)).IsUniquelyCodimOneFace (S.mk (e.hom.app _ y.simplex)) ↔
      x.IsUniquelyCodimOneFace y :=
  ⟨fun hxy' ↦ by simpa using hxy'.of_iso e.symm, fun hxy ↦ hxy.of_iso e⟩

/--
@isnad1 id=eq.2h6v.s8.d7b18835b4f6 from=seed src=0 shape=91fcf670 vocab=99f118d4
-/
lemma index_of_iso {Y : SSet.{u}} (e : X ≅ Y) {d : ℕ} (hd : x.dim = d) :
    (hxy.of_iso e).index hd = hxy.index hd := by
  obtain ⟨dx, x, rfl⟩ := x.mk_surjective
  obtain ⟨dy, y, rfl⟩ := y.mk_surjective
  obtain rfl : dy = dx + 1 := hxy.dim_eq
  obtain rfl : dx = d := hd
  symm
  simp [← (hxy.of_iso e).δ_eq_iff rfl,
    ← SSet.δ_naturality_apply, dsimp% hxy.δ_index rfl]

end IsUniquelyCodimOneFace

end SSet.S

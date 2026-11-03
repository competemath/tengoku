import Tengoku.DgLean.DG.Category.Homotopy.Cone
import Tengoku.DgLean.DG.Category.Homotopy.HomShift
import Tengoku.DgLean.DG.Category.Homotopy.Homotopy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The mapping cone of dg modules over a dg category in terms of cochains

Let `f : M ⟶ N` be a morphism of dg modules over a dg category `C` and `cone f` its mapping cone
(`DG.CatModule.cone`). This file is a port of `DG.Homotopy.ConeCochain` (the case of a dg ring,
itself a port of Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`): it
describes the cone through cochains of the Hom complex, with Mathlib's names, degrees and
signs, in the namespace `DG.CatModule.cone`.

## Main definitions

* `DG.CatModule.cone.inl f : Cochain M (cone f) (-1)`, `x ↦ (x, 0)`;
* `DG.CatModule.cone.inr f : N ⟶ cone f`, `y ↦ (0, y)` (in `DG.Category.Homotopy.Cone`);
* `DG.CatModule.cone.fst f : Cocycle (cone f) M 1`, `(x, y) ↦ x`;
* `DG.CatModule.cone.snd f : Cochain (cone f) N 0`, `(x, y) ↦ y`;
* `descCochain`, `descCocycle`, `desc`: maps out of the cone; `liftCochain`, `liftCocycle`,
  `lift`: maps into the cone; `descHomotopy`, `liftHomotopy`: homotopies from cochain data;
* `DG.CatModule.cone.mapOfHomotopy`: the map of cones induced by a square commuting up to
  homotopy;
* `DG.CatModule.cone.homotopyToZeroOfId`, `DG.CatModule.cone.isContractible_id`: the cone of
  the identity is contractible.

## Main results

The relations `inl_fst`, `inl_snd`, `inr_fst`, `inr_snd`, `id`, the extensionality principles
`ext_to`, `ext_from`, `ext_cochain_to_iff`, `ext_cochain_from_iff`, `δ_inl`, `δ_snd`,
`δ_descCochain`, `δ_liftCochain`, the universal properties, `fstHom_eq`, and `map_eq_desc`,
`map_id`, `map_comp`.

## Conventions

As in the dg-ring version, all signs are Mathlib's; cochains compose in the usual order
(Mathlib's `γ₁.comp γ₂ h` is `γ₂.comp γ₁ h` here), morphisms of dg modules compose in
diagrammatic order `f ≫ g` (the dg-ring version's `g.comp f`), and the component lemmas are
stated on elements of the values `(cone f).obj X`.
-/

open scoped DG

open CategoryTheory

universe w v u

namespace DG

namespace CatModule

namespace cone

open DG.CatModule.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] {M N K L : CatModule.{w} C} (f : M ⟶ N)

/-! ### The structure maps -/

/-- The left inclusion `x ↦ (x, 0)` of `M` into the cone, as a cochain of degree `-1`
(Mathlib's `mappingCone.inl`).-/
def inl : Cochain M (cone f) (-1) where
  app X := (inlAddHom f X).comp (shift.mk 1).toAddMonoidHom
  map_mem' {X i x} hx := inlAddHom_mem (by rw [← sub_eq_add_neg]; exact shift.mk_mem_grading hx)
  map_smul' {X Y i g} hg x := by
    change inlAddHom f Y (shift.mk 1 (g • x)) = _ • (g • inlAddHom f X (shift.mk 1 x))
    rw [shift.mk_smul hg, Units.smul_def, map_zsmul, ← Units.smul_def, inlAddHom_smul, one_mul,
      neg_one_mul, koszulSign, koszulSign, Int.negOnePow_neg]

/-- The second projection `(x, y) ↦ y` from the cone to `N`, as a cochain of degree `0`
(Mathlib's `mappingCone.snd`).-/
def snd : Cochain (cone f) N 0 :=
  Cochain.ofHoms (sndAddHom f) sndAddHom_mem sndAddHom_smul

/-- The first projection `(x, y) ↦ x` from the cone to `M`, as a cocycle of degree `1`
(Mathlib's `mappingCone.fst`).-/
def fst : Cocycle (cone f) M 1 :=
  Cocycle.mk
    { app := fun X => (shift.unmk 1).toAddMonoidHom.comp ((fstHom f).app X)
      map_mem' := fun hp => shift.unmk_mem_grading ((fstHom f).map_mem hp)
      map_smul' := fun {X Y i g} hg p => by
        change shift.unmk 1 ((fstHom f).app Y (g • p)) = _ • (g • shift.unmk 1 ((fstHom f).app X p))
        rw [Hom.map_smul, shift.unmk_smul hg, one_mul] }
    2 one_add_one_eq_two (by
      ext X p
      rw [δ_apply 1 2 one_add_one_eq_two]
      change d (shift.unmk 1 ((fstHom f).app X p)) -
        koszulSign 1 • shift.unmk 1 ((fstHom f).app X (d p)) = 0
      rw [fstHom_d, shift.unmk_d, smul_smul, Int.units_mul_self, one_smul, sub_self])

variable {f} {X : C}

/--
@isnad1 id=eq.0h6v.s10.429d7b50b294 from=translated src=- shape=2712ad5d vocab=d3c0d186
-/
theorem fst_apply (p : (cone f).obj X) : (fst f).1.app X p = shift.unmk 1 ((fstHom f).app X p) :=
  rfl

/--
@isnad1 id=eq.0h6v.s9.aa93efc70fa4 from=translated src=- shape=928e1ac6 vocab=39ccdb19
-/
@[simp]
theorem inl_snd_apply (x : M.obj X) : (snd f).app X ((inl f).app X x) = 0 := rfl

/--
@isnad1 id=eq.0h6v.s9.06e899978b0f from=translated src=- shape=804bc0ba vocab=0ed884d2
-/
@[simp]
theorem inr_snd_apply (y : N.obj X) : (snd f).app X ((inr f).app X y) = y := rfl

/--
@isnad1 id=eq.0h6v.s10.b1e06a81ca42 from=translated src=- shape=98edab3e vocab=26562971
-/
@[simp]
theorem inl_fst_apply (x : M.obj X) : (fst f).1.app X ((inl f).app X x) = x := rfl

/--
@isnad1 id=eq.0h6v.s10.7e949fc81a84 from=translated src=- shape=1e0c80b0 vocab=ed5ab727
-/
@[simp]
theorem inr_fst_apply (y : N.obj X) : (fst f).1.app X ((inr f).app X y) = 0 := rfl

/-- Mathlib's `inr_f_d`.
@isnad1 id=eq.0h6v.s10.e75ccf94098d from=translated src=- shape=dd623fdc vocab=dd16b039
-/
theorem inr_d_apply (y : N.obj X) : d ((inr f).app X y) = (inr f).app X (d y) :=
  ((inr f).map_d y).symm

/-- Every element of the cone is `inl x + inr y` (Mathlib's `id_X`).
@isnad1 id=eq.0h6v.s11.c1a587220214 from=translated src=- shape=d5900f87 vocab=6a0b4259
-/
theorem id_X (p : (cone f).obj X) :
    (inl f).app X ((fst f).1.app X p) + (inr f).app X ((snd f).app X p) = p :=
  inlAddHom_fstHom_add_inr_sndAddHom p

/-- Two elements of the cone with the same projections are equal (Mathlib's `ext_to`).
@isnad1 id=eq.2h7v.s11.7dc013321c11 from=translated src=- shape=b2a89dd3 vocab=aa3dd5c7
-/
theorem ext_to {p q : (cone f).obj X} (h₁ : (fst f).1.app X p = (fst f).1.app X q)
    (h₂ : (snd f).app X p = (snd f).app X q) : p = q :=
  ext (shift.unmk_injective h₁) h₂

/-- Two additive maps out of the value of the cone at `X` agreeing on the images of `inl` and
`inr` are equal (Mathlib's `ext_from`).
@isnad1 id=eq.2h8v.s11.d981dc85ef99 from=translated src=- shape=43d6d244 vocab=da41902f
-/
theorem ext_from {P : Type*} [AddCommGroup P] {g₁ g₂ : (cone f).obj X →+ P}
    (h₁ : ∀ x, g₁ ((inl f).app X x) = g₂ ((inl f).app X x))
    (h₂ : ∀ y, g₁ ((inr f).app X y) = g₂ ((inr f).app X y)) : g₁ = g₂ :=
  AddMonoidHom.ext fun p => by rw [← id_X p, map_add, map_add, h₁, h₂]

/-! ### The differential of the cone -/

/-- Mathlib's `d_fst_v`.
@isnad1 id=eq.0h6v.s11.c203a7fb09f1 from=translated src=- shape=895296a4 vocab=5938ade0
-/
theorem d_fst_apply (p : (cone f).obj X) : (fst f).1.app X (d p) = -d ((fst f).1.app X p) := by
  rw [fst_apply, fst_apply, fstHom_d, shift.unmk_d, koszulSign, Int.negOnePow_one,
    Units.neg_smul, one_smul]

/-- Mathlib's `d_snd_v`.
@isnad1 id=eq.0h6v.s11.a27b098a71de from=translated src=- shape=7b54b505 vocab=c6b38a8c
-/
theorem d_snd_apply (p : (cone f).obj X) :
    (snd f).app X (d p) = f.app X ((fst f).1.app X p) + d ((snd f).app X p) :=
  sndAddHom_d p

/-- Mathlib's `inl_v_d`.
@isnad1 id=eq.0h6v.s11.11bddbe5292b from=translated src=- shape=5dc584c5 vocab=0f681fde
-/
theorem inl_d_apply (x : M.obj X) :
    d ((inl f).app X x) = (inr f).app X (f.app X x) - (inl f).app X (d x) := by
  refine ext_to ?_ ?_
  · rw [d_fst_apply, map_sub, inl_fst_apply, inr_fst_apply, inl_fst_apply, zero_sub]
  · rw [d_snd_apply, map_sub, inl_fst_apply, inl_snd_apply, inr_snd_apply, inl_snd_apply,
      d_zero, add_zero, sub_zero]

/-! ### Relations between the structure maps -/

variable (f)

/--
@isnad1 id=eq.0h4v.s7.455b0e391dd7 from=translated src=- shape=98933ff8 vocab=972366b2
-/
@[simp]
theorem inl_snd : (snd f).comp (inl f) (add_zero (-1)) = 0 := rfl

/--
@isnad1 id=eq.0h4v.s7.e7edb3958871 from=translated src=- shape=09ab3c2c vocab=de7c644d
-/
@[simp]
theorem inr_snd : (snd f).comp (ofHom (inr f)) (zero_add 0) = Cochain.id N := rfl

/--
@isnad1 id=eq.2h9v.s7.69d7eef003cc from=translated src=- shape=48048787 vocab=a1e1f979
-/
@[simp]
theorem inl_snd_assoc {d e g : ℤ} (γ : Cochain N K d) (he : 0 + d = e) (hg : -1 + e = g) :
    (γ.comp (snd f) he).comp (inl f) hg = 0 := by
  ext X x
  simp

/--
@isnad1 id=eq.1h8v.s7.0288b56959cf from=translated src=- shape=4823c327 vocab=6c745cfb
-/
@[simp]
theorem inr_snd_assoc {d e : ℤ} (γ : Cochain N K d) (he : 0 + d = e) :
    (γ.comp (snd f) he).comp (ofHom (inr f)) (by rw [← he, zero_add, zero_add]) = γ := by
  ext X y
  simp

/--
@isnad1 id=eq.0h4v.s8.f3f1b9166f20 from=translated src=- shape=6c81a55d vocab=931384f4
-/
@[simp]
theorem inl_fst : (fst f).1.comp (inl f) (neg_add_cancel 1) = Cochain.id M := rfl

/--
@isnad1 id=eq.0h4v.s8.0fc629733062 from=translated src=- shape=5fa7b014 vocab=f9c63b51
-/
@[simp]
theorem inr_fst : (fst f).1.comp (ofHom (inr f)) (zero_add 1) = 0 := rfl

/--
@isnad1 id=eq.1h8v.s8.b7d60cdb5c16 from=translated src=- shape=02e33daa vocab=e0a90660
-/
@[simp]
theorem inl_fst_assoc {d e : ℤ} (γ : Cochain M K d) (he : 1 + d = e) :
    (γ.comp (fst f).1 he).comp (inl f) (by rw [← he, neg_add_cancel_left]) = γ := rfl

/--
@isnad1 id=eq.2h9v.s9.077a6a5b9889 from=translated src=- shape=eec4c3ed vocab=7a9e9165
-/
@[simp]
theorem inr_fst_assoc {d e g : ℤ} (γ : Cochain M K d) (he : 1 + d = e) (hg : 0 + e = g) :
    (γ.comp (fst f).1 he).comp (ofHom (inr f)) hg = 0 := by
  ext X y
  simp

/--
@isnad1 id=iff.1h9v.s9.3da45b66fd5a from=translated src=- shape=7017c9f8 vocab=020a7ad3
-/
theorem ext_cochain_to_iff (i j : ℤ) (hij : i + 1 = j) {γ₁ γ₂ : Cochain K (cone f) i} :
    γ₁ = γ₂ ↔ (fst f).1.comp γ₁ hij = (fst f).1.comp γ₂ hij ∧
      (snd f).comp γ₁ (add_zero i) = (snd f).comp γ₂ (add_zero i) := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => Cochain.ext fun X x => ext_to ?_ ?_⟩
  · exact congrArg (fun γ : Cochain K M j => γ.app X x) h₁
  · exact congrArg (fun γ : Cochain K N i => γ.app X x) h₂

/--
@isnad1 id=iff.1h9v.s8.305eac2c0a6b from=translated src=- shape=a8e2226c vocab=bc2c3835
-/
theorem ext_cochain_from_iff (i j : ℤ) (hij : i + 1 = j) {γ₁ γ₂ : Cochain (cone f) K j} :
    γ₁ = γ₂ ↔ γ₁.comp (inl f) (show -1 + j = i by omega) = γ₂.comp (inl f) (by omega) ∧
      γ₁.comp (ofHom (inr f)) (zero_add j) = γ₂.comp (ofHom (inr f)) (zero_add j) := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => Cochain.ext fun X p => ?_⟩
  refine congrArg (fun g : (cone f).obj X →+ K.obj X => g p)
    (ext_from (g₁ := γ₁.app X) (g₂ := γ₂.app X) (fun x => ?_) (fun y => ?_))
  · exact congrArg (fun γ : Cochain M K i => γ.app X x) h₁
  · exact congrArg (fun γ : Cochain N K j => γ.app X y) h₂

/-- `inl ∘ fst + inr ∘ snd = id` (Mathlib's `mappingCone.id`).
@isnad1 id=eq.0h4v.s9.7cfda0541cbc from=translated src=- shape=3ba6806f vocab=e76f619b
-/
theorem id :
    (inl f).comp (fst f).1 (add_neg_cancel 1) + (ofHom (inr f)).comp (snd f) (add_zero 0) =
      Cochain.id (cone f) :=
  Cochain.ext fun _ => id_X

/-- The differential of `inl` (Mathlib's `δ_inl`): `inl` is a chain map up to `f ≫ inr f`.
@isnad1 id=eq.0h4v.s7.c38f1c23a79e from=translated src=- shape=9a91faaa vocab=3d0e2935
-/
@[simp]
theorem δ_inl : δ (-1) 0 (inl f) = ofHom (f ≫ inr f) := by
  refine Cochain.ext fun X x => ?_
  rw [δ_neg_one_apply, inl_d_apply, ofHom_apply, comp_app, sub_add_cancel]

/-- The differential of `snd` (Mathlib's `δ_snd`).
@isnad1 id=eq.0h4v.s8.cbce233377b7 from=translated src=- shape=c30e59bd vocab=4c84d431
-/
@[simp]
theorem δ_snd : δ 0 1 (snd f) = -(ofHom f).comp (fst f).1 (add_zero 1) := by
  ext X p
  rw [δ_zero_cochain_apply, d_snd_apply, Cochain.neg_apply, DG.CatModule.Cochain.comp_apply, ofHom_apply]
  abel

/-! ### Maps out of the cone -/

section Desc

variable {n m : ℤ}

/-- The cochain `Cochain (cone f) K n` given by `α : Cochain M K m` (with `m + 1 = n`) on
`M⟦1⟧` and `β : Cochain N K n` on `N`: `α ∘ fst + β ∘ snd` (Mathlib's `descCochain`).-/
def descCochain (α : Cochain M K m) (β : Cochain N K n) (h : m + 1 = n) :
    Cochain (cone f) K n :=
  α.comp (fst f).1 (by rw [← h, add_comm]) + β.comp (snd f) (zero_add n)

variable (α : Cochain M K m) (β : Cochain N K n) (h : m + 1 = n)

/--
@isnad1 id=eq.1h11v.s11.4c6a0c2d65a4 from=translated src=- shape=973136c9 vocab=d9d6c4b0
-/
theorem descCochain_apply (p : (cone f).obj X) :
    (descCochain f α β h).app X p = α.app X ((fst f).1.app X p) + β.app X ((snd f).app X p) :=
  rfl

/--
@isnad1 id=eq.1h9v.s7.1ffb8c4ae84e from=translated src=- shape=bf8488a0 vocab=6eb3deaa
-/
@[simp]
theorem inl_descCochain :
    (descCochain f α β h).comp (inl f) (by omega) = α := by
  ext X x
  simp [descCochain_apply]

/--
@isnad1 id=eq.1h9v.s7.759a128b7308 from=translated src=- shape=fe820884 vocab=d5a4cebb
-/
@[simp]
theorem inr_descCochain :
    (descCochain f α β h).comp (ofHom (inr f)) (zero_add n) = β := by
  ext X y
  simp [descCochain_apply]

/-- Mathlib's `inl_v_descCochain_v`.
@isnad1 id=eq.1h11v.s10.aface1ae8976 from=translated src=- shape=d3ede451 vocab=b9d91bf2
-/
@[simp]
theorem inl_descCochain_apply (x : M.obj X) :
    (descCochain f α β h).app X ((inl f).app X x) = α.app X x := by
  simp [descCochain_apply]

/-- Mathlib's `inr_f_descCochain_v`.
@isnad1 id=eq.1h11v.s10.59349042cc6c from=translated src=- shape=ca8f7a0a vocab=6a945388
-/
@[simp]
theorem inr_descCochain_apply (y : N.obj X) :
    (descCochain f α β h).app X ((inr f).app X y) = β.app X y := by
  simp [descCochain_apply]

/--
@isnad1 id=eq.2h10v.s9.31154a02ded9 from=translated src=- shape=eda78394 vocab=ba53bdad
-/
theorem δ_descCochain (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (descCochain f α β h) =
      (δ m n α + koszulSign n' • β.comp (ofHom f) (zero_add n)).comp (fst f).1
          (by omega) +
        (δ n n' β).comp (snd f) (zero_add n') := by
  ext X p
  have hm : koszulSign m = -koszulSign n := by
    rw [← h, koszulSign, koszulSign, Int.negOnePow_succ, neg_neg]
  have hn : koszulSign n' = -koszulSign n := by
    rw [← hn', koszulSign, koszulSign, Int.negOnePow_succ]
  simp only [δ_apply _ _ hn', δ_apply _ _ h, descCochain_apply, Cochain.add_apply, DG.CatModule.Cochain.comp_apply,
    units_smul_apply, Cochain.neg_apply, ofHom_apply, d_fst_apply, d_snd_apply, map_add, map_neg,
    hm, hn, Units.neg_smul, _root_.smul_add, _root_.smul_neg,
    sub_eq_add_neg, neg_neg]
  abel

end Desc

section DescCocycle

/-- The cocycle `Cocycle (cone f) K n` given by `α : Cochain M K m` (with `m + 1 = n`) and a
cocycle `β : Cocycle N K n` satisfying `δ α = (-1)^n • β ∘ f` (Mathlib's `descCocycle`).-/
@[simps!]
def descCocycle {n m : ℤ} (α : Cochain M K m) (β : Cocycle N K n) (h : m + 1 = n)
    (eq : δ m n α = koszulSign n • (β.1.comp (ofHom f) (zero_add n))) :
    Cocycle (cone f) K n :=
  Cocycle.mk (descCochain f α β.1 h) (n + 1) rfl (by
    simp [δ_descCochain _ _ _ _ _ rfl, eq, koszulSign, Int.negOnePow_succ])

section

variable (α : Cochain M K (-1)) (β : N ⟶ K) (eq : δ (-1) 0 α = ofHom (f ≫ β))

/-- The morphism `cone f ⟶ K` given by a `(-1)`-cochain `α : Cochain M K (-1)` and a morphism
`β : N ⟶ K` with `δ α = f ≫ β`: `(x, y) ↦ α x + β y` (Mathlib's `desc`).-/
def desc : cone f ⟶ K :=
  Cocycle.homOf (descCocycle f α (Cocycle.ofHom β) (neg_add_cancel 1)
    (by rw [eq, koszulSign, Int.negOnePow_zero, one_smul]; rfl))

/--
@isnad1 id=eq.1h7v.s8.c6ea7a956bb0 from=translated src=- shape=a21e89b3 vocab=934ed399
-/
@[simp]
theorem ofHom_desc : ofHom (desc f α β eq) = descCochain f α (ofHom β) (neg_add_cancel 1) := rfl

/-- Mathlib's `desc_f`.
@isnad1 id=eq.1h9v.s11.702ebdf3b07c from=translated src=- shape=41b861e7 vocab=de3ed8ff
-/
theorem desc_apply (p : (cone f).obj X) :
    (desc f α β eq).app X p = α.app X ((fst f).1.app X p) + β.app X ((snd f).app X p) := rfl

/-- Mathlib's `inl_v_desc_f`.
@isnad1 id=eq.1h9v.s10.cab5b429b339 from=translated src=- shape=b272d253 vocab=11ad1f89
-/
@[simp]
theorem inl_desc_apply (x : M.obj X) : (desc f α β eq).app X ((inl f).app X x) = α.app X x := by
  simp [desc_apply]

/--
@isnad1 id=eq.1h7v.s8.52622ccd7d42 from=translated src=- shape=676e85d0 vocab=e1aa269b
-/
theorem inl_desc : (ofHom (desc f α β eq)).comp (inl f) (add_zero _) = α := by
  ext X x
  simp

/-- Mathlib's `inr_f_desc_f`.
@isnad1 id=eq.1h9v.s10.d5d3e6cdb04c from=translated src=- shape=1331b311 vocab=5a3f9d2a
-/
@[simp]
theorem inr_desc_apply (y : N.obj X) : (desc f α β eq).app X ((inr f).app X y) = β.app X y := by
  simp [desc_apply]

/--
@isnad1 id=eq.1h7v.s8.3b8ed4ddbb22 from=translated src=- shape=838183fd vocab=709f4107
-/
@[simp]
theorem inr_desc : inr f ≫ desc f α β eq = β := by
  ext X y
  simp

end

/-- Constructor for homotopies between morphisms out of a mapping cone (Mathlib's
`descHomotopy`).-/
def descHomotopy (f₁ f₂ : cone f ⟶ K) (γ₁ : Cochain M K (-2)) (γ₂ : Cochain N K (-1))
    (h₁ : (ofHom f₁).comp (inl f) (add_zero (-1)) =
      δ (-2) (-1) γ₁ + γ₂.comp (ofHom f) (zero_add (-1)) +
        (ofHom f₂).comp (inl f) (add_zero (-1)))
    (h₂ : ofHom (inr f ≫ f₁) = δ (-1) 0 γ₂ + ofHom (inr f ≫ f₂)) :
    DGHomotopy f₁ f₂ where
  hom := descCochain f γ₁ γ₂ (by norm_num)
  ofHom_eq := by
    rw [ofHom_comp, ofHom_comp] at h₂
    rw [ext_cochain_from_iff f (-1) 0 (neg_add_cancel 1)]
    refine ⟨?_, ?_⟩
    · ext X x
      have := congrArg (fun γ : Cochain M K (-1) => γ.app X x) h₁
      simp only [DG.CatModule.Cochain.comp_apply, Cochain.add_apply] at this ⊢
      rw [this, δ_descCochain f γ₁ γ₂ (by norm_num) 0 (neg_add_cancel 1)]
      simp [koszulSign]
    · ext X y
      have := congrArg (fun γ : Cochain N K 0 => γ.app X y) h₂
      simp only [DG.CatModule.Cochain.comp_apply, Cochain.add_apply] at this ⊢
      rw [this, δ_descCochain f γ₁ γ₂ (by norm_num) 0 (neg_add_cancel 1)]
      simp

end DescCocycle

/-! ### Maps into the cone -/

section Lift

variable {n m : ℤ}

/-- The cochain `Cochain K (cone f) n` given by `α : Cochain K M m` (with `n + 1 = m`) and
`β : Cochain K N n`: `inl ∘ α + inr ∘ β` (Mathlib's `liftCochain`).-/
def liftCochain (α : Cochain K M m) (β : Cochain K N n) (h : n + 1 = m) :
    Cochain K (cone f) n :=
  (inl f).comp α (by omega) + (ofHom (inr f)).comp β (add_zero n)

variable (α : Cochain K M m) (β : Cochain K N n) (h : n + 1 = m)

/--
@isnad1 id=eq.1h11v.s10.337901442918 from=translated src=- shape=639fe2dd vocab=fb6f7d7c
-/
theorem liftCochain_apply (k : K.obj X) :
    (liftCochain f α β h).app X k = (inl f).app X (α.app X k) + (inr f).app X (β.app X k) := rfl

/--
@isnad1 id=eq.1h9v.s8.71a686a7a0da from=translated src=- shape=3858bf19 vocab=f1e4601e
-/
@[simp]
theorem liftCochain_fst : (fst f).1.comp (liftCochain f α β h) h = α := by
  ext X k
  simp [liftCochain_apply]

/--
@isnad1 id=eq.1h9v.s7.36ec2d7aabc4 from=translated src=- shape=3f37e454 vocab=5876043c
-/
@[simp]
theorem liftCochain_snd : (snd f).comp (liftCochain f α β h) (add_zero n) = β := by
  ext X k
  simp [liftCochain_apply]

/-- Mathlib's `liftCochain_v_fst_v`.
@isnad1 id=eq.1h11v.s10.41a57e65b6a1 from=translated src=- shape=e451757c vocab=dff5a61d
-/
@[simp]
theorem liftCochain_fst_apply (k : K.obj X) :
    (fst f).1.app X ((liftCochain f α β h).app X k) = α.app X k := by
  simp [liftCochain_apply]

/-- Mathlib's `liftCochain_v_snd_v`.
@isnad1 id=eq.1h11v.s10.f1ccece3a20c from=translated src=- shape=aa311458 vocab=a5958365
-/
@[simp]
theorem liftCochain_snd_apply (k : K.obj X) :
    (snd f).app X ((liftCochain f α β h).app X k) = β.app X k := by
  simp [liftCochain_apply]

/--
@isnad1 id=eq.2h10v.s8.4b4aa89cadca from=translated src=- shape=d3871808 vocab=8e6957b7
-/
theorem δ_liftCochain (m' : ℤ) (hm' : m + 1 = m') :
    δ n m (liftCochain f α β h) = -(inl f).comp (δ m m' α) (by omega) +
      (ofHom (inr f)).comp (δ n m β + (ofHom f).comp α (add_zero m)) (add_zero m) := by
  refine Cochain.ext fun X k => ?_
  have hm : koszulSign m = -koszulSign n := by
    rw [← h, koszulSign, koszulSign, Int.negOnePow_succ]
  refine ext_to ?_ ?_
  · simp only [δ_apply _ _ h, δ_apply _ _ hm', liftCochain_apply, Cochain.add_apply,
      Cochain.neg_apply, DG.CatModule.Cochain.comp_apply, map_add, map_sub, map_neg, map_units_smul,
      inl_d_apply, inr_d_apply, inl_fst_apply, inr_fst_apply, hm, Units.neg_smul,
      ofHom_apply, _root_.smul_zero, add_zero]
    abel
  · simp only [δ_apply _ _ h, δ_apply _ _ hm', liftCochain_apply, Cochain.add_apply,
      Cochain.neg_apply, DG.CatModule.Cochain.comp_apply, ofHom_apply, map_add, map_sub, map_neg,
      map_units_smul, inl_d_apply, inr_d_apply, inl_snd_apply, inr_snd_apply, zero_add,
      _root_.smul_zero]
    abel

end Lift

section LiftCocycle

/-- The cocycle `Cocycle K (cone f) n` given by a cocycle `α : Cocycle K M m` (with
`n + 1 = m`) and `β : Cochain K N n` satisfying `δ β + f ∘ α = 0` (Mathlib's
`liftCocycle`).-/
@[simps!]
def liftCocycle {n m : ℤ} (α : Cocycle K M m) (β : Cochain K N n) (h : n + 1 = m)
    (eq : δ n m β + (ofHom f).comp α.1 (add_zero m) = 0) :
    Cocycle K (cone f) n :=
  Cocycle.mk (liftCochain f α.1 β h) m h (by
    simp only [δ_liftCochain f α.1 β h (m + 1) rfl, eq, Cocycle.δ_eq_zero, Cochain.comp_zero,
      neg_zero, zero_add])

section

variable (α : Cocycle K M 1) (β : Cochain K N 0)
  (eq : δ 0 1 β + (ofHom f).comp α.1 (add_zero 1) = 0)

/-- The morphism `K ⟶ cone f` given by a `1`-cocycle `α : Cocycle K M 1` and a `0`-cochain
`β : Cochain K N 0` with `δ β + f ∘ α = 0`: `k ↦ (α k, β k)` (Mathlib's `lift`).-/
def lift : K ⟶ cone f :=
  Cocycle.homOf (liftCocycle f α β (zero_add 1) eq)

/--
@isnad1 id=eq.1h7v.s9.4ac9e2195582 from=translated src=- shape=e2ef9aa8 vocab=46cd8494
-/
@[simp]
theorem ofHom_lift : ofHom (lift f α β eq) = liftCochain f α.1 β (zero_add 1) := rfl

/-- Mathlib's `lift_f`.
@isnad1 id=eq.1h9v.s11.50023f38eba0 from=translated src=- shape=615b4e30 vocab=6958a24c
-/
theorem lift_apply (k : K.obj X) :
    (lift f α β eq).app X k = (inl f).app X (α.1.app X k) + (inr f).app X (β.app X k) := rfl

/-- Mathlib's `lift_f_fst_v`.
@isnad1 id=eq.1h9v.s10.5e726cece868 from=translated src=- shape=7fdffd43 vocab=53ac704f
-/
@[simp]
theorem lift_fst_apply (k : K.obj X) : (fst f).1.app X ((lift f α β eq).app X k) = α.1.app X k := by
  simp [lift_apply]

/--
@isnad1 id=eq.1h7v.s9.1ee91d2d363a from=translated src=- shape=540e61d8 vocab=2d115c95
-/
theorem lift_fst : (fst f).1.comp (ofHom (lift f α β eq)) (zero_add 1) = α.1 := by
  ext X k
  simp

/-- Mathlib's `lift_f_snd_v`.
@isnad1 id=eq.1h9v.s10.f14230a12b22 from=translated src=- shape=eb7b9314 vocab=d6946631
-/
@[simp]
theorem lift_snd_apply (k : K.obj X) : (snd f).app X ((lift f α β eq).app X k) = β.app X k := by
  simp [lift_apply]

/--
@isnad1 id=eq.1h7v.s9.3eba45277671 from=translated src=- shape=d8dd6231 vocab=2bc6f120
-/
theorem lift_snd : (snd f).comp (ofHom (lift f α β eq)) (zero_add 0) = β := by
  ext X k
  simp

end

/-- Constructor for homotopies between morphisms into a mapping cone (Mathlib's
`liftHomotopy`).-/
def liftHomotopy (f₁ f₂ : K ⟶ cone f) (α : Cochain K M 0) (β : Cochain K N (-1))
    (h₁ : (fst f).1.comp (ofHom f₁) (zero_add 1) =
      -δ 0 1 α + (fst f).1.comp (ofHom f₂) (zero_add 1))
    (h₂ : (snd f).comp (ofHom f₁) (zero_add 0) =
      δ (-1) 0 β + (ofHom f).comp α (zero_add 0) + (snd f).comp (ofHom f₂) (zero_add 0)) :
    DGHomotopy f₁ f₂ where
  hom := liftCochain f α β (neg_add_cancel 1)
  ofHom_eq := by
    rw [ext_cochain_to_iff f 0 1 (zero_add 1)]
    refine ⟨?_, ?_⟩
    · ext X k
      have := congrArg (fun γ : Cochain K M 1 => γ.app X k) h₁
      simp only [DG.CatModule.Cochain.comp_apply, Cochain.add_apply, Cochain.neg_apply] at this ⊢
      rw [this, δ_liftCochain f α β (neg_add_cancel 1) 1 (zero_add 1)]
      simp
    · ext X k
      have := congrArg (fun γ : Cochain K N 0 => γ.app X k) h₂
      simp only [DG.CatModule.Cochain.comp_apply, Cochain.add_apply] at this ⊢
      rw [this, δ_liftCochain f α β (neg_add_cancel 1) 1 (zero_add 1)]
      simp

end LiftCocycle

section

variable {n m : ℤ} (α : Cochain K M m) (β : Cochain K N n) {n' m' : ℤ}
  (α' : Cochain M L m') (β' : Cochain N L n') (h : n + 1 = m) (h' : m' + 1 = n') (p : ℤ)
  (hp : n + n' = p)

/-- Mathlib's `liftCochain_descCochain`.
@isnad1 id=eq.3h15v.s8.0f03fc7581ef from=translated src=- shape=f80b7586 vocab=3f763d36
-/
@[simp]
theorem liftCochain_descCochain :
    (descCochain f α' β' h').comp (liftCochain f α β h) hp =
      α'.comp α (by omega) + β'.comp β (by omega) := by
  ext X k
  simp [liftCochain_apply, descCochain_apply]

end

/-! ### Maps between cones -/

section Map

variable {M₁ N₁ M₂ N₂ M₃ N₃ : CatModule.{w} C}
  {f₁ : M₁ ⟶ N₁} {f₂ : M₂ ⟶ N₂} {f₃ : M₃ ⟶ N₃} {a : M₁ ⟶ M₂} {b : N₁ ⟶ N₂}

/-- The morphism `cone f₁ ⟶ cone f₂` induced by a square `f₁ ≫ b ≃ a ≫ f₂` commuting up to
a homotopy `H` (Mathlib's `mapOfHomotopy`): `(x, y) ↦ (a x, H x + b y)`.-/
def mapOfHomotopy (H : DGHomotopy (f₁ ≫ b) (a ≫ f₂)) : cone f₁ ⟶ cone f₂ :=
  desc f₁ ((inl f₂).comp (ofHom a) (zero_add _) + (ofHom (inr f₂)).comp H.hom (add_zero _))
    (b ≫ inr f₂) (by
      have hH : δ (-1) 0 H.hom = ofHom (f₁ ≫ b) - ofHom (a ≫ f₂) :=
        eq_sub_of_add_eq H.ofHom_eq.symm
      rw [δ_add, δ_ofHom_comp, δ_comp_ofHom, δ_inl, hH]
      refine Cochain.ext fun X x => ?_
      simp)

/--
@isnad1 id=eq.1h11v.s11.4bc8eeab5a4a from=translated src=- shape=84625abd vocab=de2cd0c3
-/
@[simp]
theorem map_fst_apply (h : f₁ ≫ b = a ≫ f₂) (p : (cone f₁).obj X) :
    (fst f₂).1.app X ((map a b h).app X p) = a.app X ((fst f₁).1.app X p) := rfl

/--
@isnad1 id=eq.1h11v.s10.af6b76443a7b from=translated src=- shape=e7e268ab vocab=2dd4ea5c
-/
@[simp]
theorem map_snd_apply (h : f₁ ≫ b = a ≫ f₂) (p : (cone f₁).obj X) :
    (snd f₂).app X ((map a b h).app X p) = b.app X ((snd f₁).app X p) := rfl

/-- Mathlib's `map_id`.
@isnad1 id=eq.0h4v.s7.6f6e9dbf6442 from=translated src=- shape=5382a225 vocab=4d3b3525
-/
@[simp]
theorem map_id : map (𝟙 M) (𝟙 N) (by rw [Category.comp_id, Category.id_comp]) = 𝟙 (cone f) :=
  rfl

end Map

/-! ### The cone of the identity -/

variable (M) in
/-- The mapping cone of the identity is contractible (Mathlib's `homotopyToZeroOfId`): the
homotopy is `inl ∘ snd`, `(x, y) ↦ (y, 0)`.-/
def homotopyToZeroOfId : DGHomotopy (𝟙 (cone (𝟙 M))) 0 :=
  descHomotopy (𝟙 M) _ _ 0 (inl (𝟙 M))
    (by refine Cochain.ext fun X x => ?_; simp) (by refine Cochain.ext fun X y => ?_; simp)

variable (M) in
/-- The mapping cone of the identity is contractible.
@isnad1 id=iscontra.0h2v.s6.8648fa1526e2 from=translated src=- shape=4430d840 vocab=05f573e0
-/
theorem isContractible_id : IsContractible (cone (𝟙 M)) :=
  ⟨homotopyToZeroOfId M⟩

end cone

end CatModule

end DG

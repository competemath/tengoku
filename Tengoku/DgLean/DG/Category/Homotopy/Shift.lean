import Tengoku.Seed.CategoryTheory.Shift.Basic
import Tengoku.DgLean.DG.Category.Homotopy.Hom
import Tengoku.DgLean.DG.Module.Shift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shifts of dg modules over a dg category

Let `C` be a dg category. This file defines the shift `M⟦n⟧` of a dg module `M` over `C` and
equips `DG.CatModule C` with a shift by `ℤ` (`CategoryTheory.HasShift`). It is a port of
`DG.Module.Shift` and of the first part of `DG.Homotopy.Shift` (the case of a dg ring), with
the same conventions, which are those of Mathlib's `CochainComplex.shiftFunctor`:

* `DG.CatModule.shift n M`: the dg module with values `(M⟦n⟧) X = DG.Shift n (M X)`, i.e.
  `((M⟦n⟧) X)ᵏ = (M X)ᵏ⁺ⁿ` with the differential `(-1)ⁿ d`, and the action twisted by the Koszul
  sign, `f • m = (-1)^{n |f|} (f • m)` for `f` homogeneous. The values are the shifts
  `DG.Shift n (M.obj X)` of dg abelian groups of `DG.Module.Shift`, so that the identifications
  `DG.Shift.mk`, `DG.Shift.unmk` and their lemmas apply objectwise.
* `DG.CatModule.twist n : (X ⟶ Y) →+ (X ⟶ Y)`, `f ↦ (-1)^{n |f|} f` on homogeneous morphisms,
  compatible with composition and identities (`DG.CatModule.twist_comp`); the action of
  `M⟦n⟧` is the action of `M` precomposed with it.
* `DG.CatModule.shiftMap n φ : M⟦n⟧ ⟶ N⟦n⟧`, the same underlying maps.
* `DG.CatModule.shiftZeroIso M : M⟦0⟧ ≅ M` and
  `DG.CatModule.shiftShiftIso a b c h M : M⟦c⟧ ≅ M⟦a⟧⟦b⟧` for `a + b = c`, the identity on
  elements.
* `DG.CatModule.hasShift`: the shift on `CatModule C`, built with Mathlib's `hasShiftMk`; the
  shift functors are additive.

The shift of a dg module over `C` is written `shift n M` (a term of `CatModule C`) rather than
`Shift n M` (the dg-ring version's type synonym), whose values it is.
-/

open scoped DG

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-! ### The twist of the morphisms -/

section Twist

variable (n : ℤ) {X Y : C}

/-- The additive map `f ↦ (-1)^{n |f|} f` on a Hom group of `C`, `f` homogeneous of degree
`|f|`.-/
def twist : (X ⟶ Y) →+ (X ⟶ Y) :=
  (DirectSum.toAddMonoid fun i : ℤ =>
    (DistribSMul.toAddMonoidHom (X ⟶ Y) (koszulSign (n * i))).comp
      (grading (M := X ⟶ Y) i).subtype).comp
    (decomposeAddEquiv (grading (M := X ⟶ Y))).toAddMonoidHom

variable {n}

/--
@isnad1 id=eq.1h6v.s9.81eaf8fdad9d from=translated src=- shape=b1dc38ca vocab=6e3fbcf0
-/
theorem twist_of_mem {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) :
    twist n f = koszulSign (n * i) • f := by
  simp only [twist, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    decomposeAddEquiv_apply, decompose_of_mem _ hf, toAddMonoid_of]
  rfl

/--
@isnad1 id=mem.1h6v.s9.60418a7033b0 from=translated src=- shape=47ba5877 vocab=eea4e6a8
-/
theorem twist_mem {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) : twist n f ∈ grading i := by
  rw [twist_of_mem hf]
  exact units_smul_mem_grading _ hf

/--
@isnad1 id=eq.0h4v.s8.18b07b62a2cc from=translated src=- shape=d250d4a2 vocab=1d52562d
-/
@[simp]
theorem twist_zero_apply (f : X ⟶ Y) : twist 0 f = f := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f => rw [twist_of_mem f.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add f f' hf hf' => rw [map_add, hf, hf']

/--
@isnad1 id=eq.0h6v.s9.ef845f135593 from=translated src=- shape=d73a55f0 vocab=8c7674a1
-/
theorem twist_twist (m : ℤ) (f : X ⟶ Y) : twist m (twist n f) = twist (m + n) f := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [twist_of_mem f.2, Units.smul_def, map_zsmul, ← Units.smul_def, twist_of_mem f.2,
      twist_of_mem f.2, smul_smul, ← koszulSign_add, add_mul, add_comm]
  | h_add f f' hf hf' => rw [map_add, map_add, hf, hf', map_add]

variable [DGCategory C]

/--
@isnad1 id=eq.0h3v.s8.c6bfd03b9be0 from=translated src=- shape=250ae9ec vocab=6f00a9d9
-/
@[simp]
theorem twist_id (X : C) : twist n (𝟙 X) = 𝟙 X := by
  rw [twist_of_mem (id_mem_grading X), mul_zero, koszulSign_zero, one_smul]

/--
@isnad1 id=eq.0h7v.s9.904b2c1abcf9 from=translated src=- shape=77f34313 vocab=404f2218
-/
theorem twist_comp {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : twist n (f ≫ g) = twist n f ≫ twist n g := by
  induction f using induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rename_i i
    induction g using induction_on with
    | h_zero => simp
    | h_homogeneous g =>
      rename_i j
      rw [twist_of_mem f.2, twist_of_mem g.2, twist_of_mem (comp_mem_grading f.2 g.2),
        comp_units_smul, units_smul_comp, smul_smul, ← koszulSign_add, mul_add, add_comm]
    | h_add g g' hg hg' => rw [Preadditive.comp_add, map_add, hg, hg', map_add,
        Preadditive.comp_add]
  | h_add f f' hf hf' => rw [Preadditive.add_comp, map_add, hf, hf', map_add, Preadditive.add_comp]

end Twist

/-! ### The shift of a dg module -/

section Shift

variable [DGCategory C]

open Shift

/-- The shift `M⟦n⟧` of a dg module over `C`: the values `DG.Shift n (M.obj X)`, with
`((M⟦n⟧) X)ᵏ = (M X)ᵏ⁺ⁿ`, the differential `(-1)ⁿ d`, and the action
`f • m = (-1)^{n |f|} (f • m)` for `f` homogeneous.-/
def shift (n : ℤ) (M : CatModule.{w} C) : CatModule.{w} C where
  obj X := Shift n (M.obj X)
  act :=
    { toFun := fun f => (Shift.mk n).toAddMonoidHom.comp
        ((M.act (twist n f)).comp (Shift.unmk n).toAddMonoidHom)
      map_zero' := by ext; simp
      map_add' := fun f g => by ext; simp [act_apply] }
  act_mem' {X Y i j f m} hf hm := by
    change twist n f • unmk n m ∈ grading (i + j + n)
    rw [add_assoc]
    exact smul_mem_grading (twist_mem hf) (unmk_mem_grading hm)
  act_id' X m := by
    change Shift.mk n (twist n (𝟙 X) • unmk n m) = m
    rw [twist_id, id_smul, mk_unmk]
  act_comp' f g m := by
    change Shift.mk n (twist n (f ≫ g) • unmk n m) = Shift.mk n (twist n g • twist n f • unmk n m)
    rw [twist_comp, comp_smul]
  d_act' {X Y i f} hf m := by
    obtain ⟨m, rfl⟩ := mk_surjective (n := n) m
    change d (Shift.mk n (twist n f • m)) =
      Shift.mk n (twist n (d f) • m) + koszulSign i • Shift.mk n (twist n f • (koszulSign n • d m))
    rw [twist_of_mem hf, twist_of_mem (d_mem hf)]
    simp only [d_mk, units_smul_smul, smul_units_smul, d_units_smul, d_smul hf, _root_.smul_add,
      smul_smul, ← koszulSign_add, ← mk_units_smul, ← mk_add, mk_inj]
    refine congrArg₂ (· + ·) (congrArg (· • _) (congrArg koszulSign (by ring)))
      (congrArg (· • _) (congrArg koszulSign (by ring)))

namespace shift

variable {n : ℤ} {M : CatModule.{w} C} {X : C}

variable (n) in
/-- The identity `M X → (M⟦n⟧) X`, as an additive equivalence (the map `DG.Shift.mk n`).-/
def mk : M.obj X ≃+ (shift n M).obj X := Shift.mk n

variable (n) in
/-- The identity `(M⟦n⟧) X → M X`, as an additive equivalence (the map `DG.Shift.unmk n`).-/
def unmk : (shift n M).obj X ≃+ M.obj X := Shift.unmk n

/--
@isnad1 id=eq.0h5v.s9.67c77fcb2f39 from=translated src=- shape=907ef4ea vocab=220be679
-/
@[simp] theorem unmk_mk (m : M.obj X) : unmk n (mk n m) = m := rfl
/--
@isnad1 id=eq.0h5v.s9.68461fb6b0c4 from=translated src=- shape=3d6af454 vocab=220be679
-/
@[simp] theorem mk_unmk (m : (shift n M).obj X) : mk n (unmk n m) = m := rfl
/--
@isnad1 id=eq.0h4v.s8.377968f5226b from=translated src=- shape=7a821981 vocab=a85fa20e
-/
@[simp] theorem mk_symm : (mk n (M := M) (X := X)).symm = unmk n := rfl
/--
@isnad1 id=eq.0h4v.s8.234bb43eccf8 from=translated src=- shape=e17aaf34 vocab=a85fa20e
-/
@[simp] theorem unmk_symm : (unmk n (M := M) (X := X)).symm = mk n := rfl

/--
@isnad1 id=surjecti.0h4v.s9.4c07ff1c9e71 from=translated src=- shape=5b7caf57 vocab=6fdf6155
-/
theorem mk_surjective : Function.Surjective (mk n (M := M) (X := X)) := (mk n).surjective
/--
@isnad1 id=injectiv.0h4v.s9.8efc51c89900 from=translated src=- shape=58879d50 vocab=a263d77a
-/
theorem unmk_injective : Function.Injective (unmk n (M := M) (X := X)) := (unmk n).injective

/--
@isnad1 id=iff.0h6v.s9.787727f9058c from=translated src=- shape=8bd9afb7 vocab=cb587e90
-/
@[simp] theorem mk_inj {m m' : M.obj X} : mk n m = mk n m' ↔ m = m' := (mk n).injective.eq_iff
/--
@isnad1 id=iff.0h6v.s10.4fe0ff53658d from=translated src=- shape=7b3e2112 vocab=15699011
-/
@[simp] theorem unmk_inj {m m' : (shift n M).obj X} : unmk n m = unmk n m' ↔ m = m' :=
  (unmk n).injective.eq_iff

/--
@isnad1 id=eq.0h6v.s10.1de6d73bf90c from=translated src=- shape=e5a452e1 vocab=2370f05d
-/
@[simp] theorem mk_units_smul (u : ℤˣ) (m : M.obj X) : mk n (u • m) = u • mk n m := rfl
/--
@isnad1 id=eq.0h6v.s10.782ee54492af from=translated src=- shape=3147bc4d vocab=38361f58
-/
@[simp] theorem unmk_units_smul (u : ℤˣ) (m : (shift n M).obj X) :
    unmk n (u • m) = u • unmk n m := rfl

/--
@isnad1 id=iff.0h6v.s9.905a51ee2c0a from=translated src=- shape=abb427e1 vocab=e5696cce
-/
theorem mem_grading_iff {k : ℤ} {m : M.obj X} : mk n m ∈ grading k ↔ m ∈ grading (k + n) :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s9.3b2de04e8775 from=translated src=- shape=b470562b vocab=3350f1ea
-/
theorem mem_grading_iff' {k : ℤ} {m : (shift n M).obj X} :
    m ∈ grading k ↔ unmk n m ∈ grading (k + n) := Iff.rfl

/--
@isnad1 id=mem.1h6v.s9.e61893aefdc6 from=translated src=- shape=32a0cffd vocab=56c2deff
-/
theorem mk_mem_grading {k : ℤ} {m : M.obj X} (hm : m ∈ grading k) : mk n m ∈ grading (k - n) :=
  mem_grading_iff.mpr (by rwa [sub_add_cancel])

/--
@isnad1 id=mem.1h6v.s9.5cabaa2bffe1 from=translated src=- shape=f4f43160 vocab=3350f1ea
-/
theorem unmk_mem_grading {k : ℤ} {m : (shift n M).obj X} (hm : m ∈ grading k) :
    unmk n m ∈ grading (k + n) :=
  mem_grading_iff'.mp hm

/--
@isnad1 id=eq.0h5v.s10.e29d51135ffe from=translated src=- shape=857a9c27 vocab=cd898f8d
-/
@[simp] theorem d_mk (m : M.obj X) : d (mk n m) = mk n (koszulSign n • d m) := rfl
/--
@isnad1 id=eq.0h5v.s10.555645b40ab8 from=translated src=- shape=df3fa6da vocab=6e2eb367
-/
@[simp] theorem unmk_d (m : (shift n M).obj X) : unmk n (d m) = koszulSign n • d (unmk n m) :=
  rfl

/--
@isnad1 id=eq.0h7v.s10.849251fd3ac3 from=translated src=- shape=4dbc26c9 vocab=f65fba94
-/
theorem smul_mk_eq {Y : C} (f : X ⟶ Y) (m : M.obj X) :
    f • mk n m = mk (M := M) n (twist n f • m) := rfl

/--
@isnad1 id=eq.0h7v.s10.346b7ad6d083 from=translated src=- shape=080acea7 vocab=197559ec
-/
theorem unmk_smul_eq {Y : C} (f : X ⟶ Y) (m : (shift n M).obj X) :
    unmk n (f • m) = twist n f • unmk n m := rfl

/--
@isnad1 id=eq.1h8v.s10.f159d4503467 from=translated src=- shape=c55d780a vocab=207b97d5
-/
theorem smul_mk {Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : M.obj X) :
    f • mk n m = mk (M := M) n (koszulSign (n * i) • (f • m)) := by
  rw [smul_mk_eq, twist_of_mem hf, units_smul_smul]

/--
@isnad1 id=eq.1h8v.s10.591f3fbe5ff8 from=translated src=- shape=cfb8703b vocab=e8919e3d
-/
theorem unmk_smul {Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : (shift n M).obj X) :
    unmk n (f • m) = koszulSign (n * i) • (f • unmk n m) := by
  rw [unmk_smul_eq, twist_of_mem hf, units_smul_smul]

/--
@isnad1 id=eq.1h8v.s10.2646a2237de5 from=translated src=- shape=5a7a0ad7 vocab=207b97d5
-/
theorem mk_smul {Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : M.obj X) :
    mk (M := M) n (f • m) = koszulSign (n * i) • (f • mk n m) := by
  rw [smul_mk hf, mk_units_smul, smul_smul, ← koszulSign_add, ← two_mul,
    koszulSign_even (even_two_mul _), one_smul]

end shift

/-! ### The shift of a morphism -/

variable {n : ℤ} {M N P : CatModule.{w} C}

variable (n) in
/-- The shift of a morphism of dg modules: the same underlying maps `M⟦n⟧ → N⟦n⟧`.-/
def shiftMap (φ : M ⟶ N) : shift n M ⟶ shift n N where
  app X := (shift.mk (M := N) (X := X) n).toAddMonoidHom.comp
    ((φ.app X).comp (shift.unmk (M := M) (X := X) n).toAddMonoidHom)
  map_mem' hm := φ.map_mem hm
  map_d' {X} m := by
    change shift.mk n (φ.app X (shift.unmk n (d m))) = d (shift.mk n (φ.app X (shift.unmk n m)))
    rw [shift.unmk_d, shift.d_mk, Units.smul_def, map_zsmul, ← Units.smul_def, Hom.map_d]
  map_smul' {X Y} f m := by
    change shift.mk n (φ.app Y (shift.unmk n (f • m))) = f • shift.mk n (φ.app X (shift.unmk n m))
    rw [shift.unmk_smul_eq, shift.smul_mk_eq, Hom.map_smul]

/--
@isnad1 id=eq.0h7v.s10.99b06ff7c93c from=translated src=- shape=1135ae27 vocab=853f02fe
-/
@[simp]
theorem shiftMap_app_mk (φ : M ⟶ N) {X : C} (m : M.obj X) :
    (shiftMap n φ).app X (shift.mk n m) = shift.mk n (φ.app X m) := rfl

/--
@isnad1 id=eq.0h7v.s10.22c2936a1db8 from=translated src=- shape=363f08c1 vocab=a79c3748
-/
theorem unmk_shiftMap_app (φ : M ⟶ N) {X : C} (m : (shift n M).obj X) :
    shift.unmk n ((shiftMap n φ).app X m) = φ.app X (shift.unmk n m) := rfl

variable (n M) in
/--
@isnad1 id=eq.0h3v.s7.9f9e64c8292d from=translated src=- shape=ce24f914 vocab=bb70d60a
-/
@[simp]
theorem shiftMap_id : shiftMap n (𝟙 M) = 𝟙 (shift n M) := rfl

/--
@isnad1 id=eq.0h7v.s7.bf9ab68c67d7 from=translated src=- shape=23a3e7bf vocab=a9e7e782
-/
@[simp]
theorem shiftMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    shiftMap n (φ ≫ ψ) = shiftMap n φ ≫ shiftMap n ψ := rfl

variable (n M N) in
/--
@isnad1 id=eq.0h4v.s8.ad507d0ba645 from=translated src=- shape=7593d41b vocab=1ace11d7
-/
@[simp] theorem shiftMap_zero : shiftMap n (0 : M ⟶ N) = 0 := rfl
/--
@isnad1 id=eq.0h6v.s8.b38e626a716f from=translated src=- shape=94c6a72c vocab=d30ca873
-/
@[simp] theorem shiftMap_add (φ ψ : M ⟶ N) : shiftMap n (φ + ψ) = shiftMap n φ + shiftMap n ψ :=
  rfl
/--
@isnad1 id=eq.0h5v.s7.00f86f861284 from=translated src=- shape=d4390f93 vocab=c175f010
-/
@[simp] theorem shiftMap_neg (φ : M ⟶ N) : shiftMap n (-φ) = -shiftMap n φ := rfl
/--
@isnad1 id=eq.0h6v.s8.f3590d55e613 from=translated src=- shape=94c6a72c vocab=6e401a94
-/
@[simp] theorem shiftMap_sub (φ ψ : M ⟶ N) : shiftMap n (φ - ψ) = shiftMap n φ - shiftMap n ψ :=
  rfl
/--
@isnad1 id=eq.0h6v.s8.9a240043b794 from=translated src=- shape=12e70835 vocab=f75e6f36
-/
@[simp] theorem shiftMap_units_smul (u : ℤˣ) (φ : M ⟶ N) :
    shiftMap n (u • φ) = u • shiftMap n φ := rfl

/-! ### The shift by `0` and the composition of shifts -/

variable (M) in
/-- The shift by `0` is the identity: `M⟦0⟧ ≅ M`, the identity on elements.-/
def shiftZeroIso : shift 0 M ≅ M :=
  isoMk (fun _ => shift.unmk 0) (fun {X k m} => by
      rw [shift.mem_grading_iff', add_zero])
    (fun m => by rw [shift.unmk_d, koszulSign_zero, one_smul])
    (fun f m => by rw [shift.unmk_smul_eq, twist_zero_apply])

/--
@isnad1 id=eq.0h4v.s10.008346f13e40 from=translated src=- shape=334cef69 vocab=aea70436
-/
@[simp]
theorem shiftZeroIso_hom_app {X : C} (m : (shift 0 M).obj X) :
    (shiftZeroIso M).hom.app X m = shift.unmk 0 m := rfl

/--
@isnad1 id=eq.0h4v.s10.7a014adaa743 from=translated src=- shape=ce1f6bbf vocab=7fe33c50
-/
@[simp]
theorem shiftZeroIso_inv_app {X : C} (m : M.obj X) :
    (shiftZeroIso M).inv.app X m = shift.mk 0 m := rfl

variable (M) in
/-- The identification `M⟦c⟧ ≅ M⟦a⟧⟦b⟧` when `a + b = c`, the identity on elements.-/
def shiftShiftIso (a b c : ℤ) (h : a + b = c) : shift c M ≅ shift b (shift a M) :=
  isoMk (fun _ => ((shift.unmk c).trans (shift.mk a)).trans (shift.mk b))
    (fun {X k m} => by
      change shift.mk b (shift.mk a (shift.unmk c m)) ∈ grading k ↔ m ∈ grading k
      rw [shift.mem_grading_iff, shift.mem_grading_iff, shift.mem_grading_iff' (n := c), ← h,
        add_assoc, add_comm b a])
    (fun m => by
      change shift.mk b (shift.mk a (shift.unmk c (d m))) =
        d (shift.mk b (shift.mk a (shift.unmk c m)))
      rw [shift.unmk_d, shift.d_mk, shift.d_mk, ← h, koszulSign_add, mul_comm, mul_smul]
      rfl)
    (fun f m => by
      change shift.mk b (shift.mk a (shift.unmk c (f • m))) =
        f • shift.mk b (shift.mk a (shift.unmk c m))
      rw [shift.unmk_smul_eq, shift.smul_mk_eq, shift.smul_mk_eq, twist_twist, ← h])

/--
@isnad1 id=eq.1h7v.s11.cdde74f6fa96 from=translated src=- shape=f70c622b vocab=70120c0b
-/
@[simp]
theorem shiftShiftIso_hom_app (a b c : ℤ) (h : a + b = c) {X : C} (m : (shift c M).obj X) :
    (shiftShiftIso M a b c h).hom.app X m = shift.mk b (shift.mk a (shift.unmk c m)) := rfl

/--
@isnad1 id=eq.1h7v.s11.5423e3aee225 from=translated src=- shape=cbbc8e9c vocab=d4a831a4
-/
@[simp]
theorem shiftShiftIso_inv_app (a b c : ℤ) (h : a + b = c) {X : C}
    (m : (shift b (shift a M)).obj X) :
    (shiftShiftIso M a b c h).inv.app X m = shift.mk c (shift.unmk a (shift.unmk b m)) := rfl

/-- The identification `M⟦a⟧⟦b⟧ ≅ M⟦b⟧⟦a⟧`, the identity on elements.-/
def shiftComm (a b : ℤ) : shift b (shift a M) ≅ shift a (shift b M) :=
  (shiftShiftIso M a b (a + b) rfl).symm ≪≫ shiftShiftIso M b a (a + b) (add_comm b a)

/--
@isnad1 id=eq.0h6v.s11.0f8fdd95d683 from=translated src=- shape=92b30588 vocab=05aab995
-/
@[simp]
theorem shiftComm_hom_app (a b : ℤ) {X : C} (m : (shift b (shift a M)).obj X) :
    (shiftComm (M := M) a b).hom.app X m =
      shift.mk a (shift.mk b (shift.unmk a (shift.unmk b m))) := rfl

end Shift

/-! ### The shift on dg modules -/

section HasShift

variable (C) [DGCategory C]

/-- The shift functor `M ↦ M⟦n⟧` on dg modules (auxiliary definition for
`DG.CatModule.hasShift`; use `shiftFunctor (CatModule C) n`).-/
@[simps obj]
def shiftFunctorAux (n : ℤ) : CatModule.{w} C ⥤ CatModule.{w} C where
  obj M := shift n M
  map φ := shiftMap n φ

/-- The shift by `0` is the identity (auxiliary definition for `DG.CatModule.hasShift`).-/
def shiftFunctorZeroAux : shiftFunctorAux.{w} C 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => shiftZeroIso M) fun _ => rfl

/-- The shift by `a + b` is the shift by `a` followed by the shift by `b` (auxiliary definition
for `DG.CatModule.hasShift`).-/
def shiftFunctorAddAux (a b : ℤ) :
    shiftFunctorAux.{w} C (a + b) ≅ shiftFunctorAux C a ⋙ shiftFunctorAux C b :=
  NatIso.ofComponents (fun M => shiftShiftIso M a b (a + b) rfl) fun _ => rfl

variable {C} in
/--
@isnad1 id=eq.2h6v.s11.30ca1ff4056d from=translated src=- shape=1dd32887 vocab=7ecafffe
-/
theorem eqToHom_shift_app {a b : ℤ} (h : a = b) (M : CatModule.{w} C)
    (p : (shiftFunctorAux C a).obj M = (shiftFunctorAux C b).obj M) {X : C}
    (x : (shift a M).obj X) :
    (eqToHom p).app X x = shift.mk b (shift.unmk a x) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The shift on dg modules over `C`: `M⟦n⟧ = shift n M`.-/
instance hasShift : HasShift (CatModule.{w} C) ℤ :=
  hasShiftMk _ _
    { F := shiftFunctorAux C
      zero := shiftFunctorZeroAux C
      add := shiftFunctorAddAux C
      assoc_hom_app := fun m₁ m₂ m₃ M => hom_ext fun X x => by
        rw [comp_app, comp_app, comp_app, eqToHom_shift_app (add_assoc m₁ m₂ m₃)]
        rfl
      zero_add_hom_app := fun n M => hom_ext fun X x => by
        rw [comp_app]
        dsimp only [Functor.id_obj]
        rw [eqToHom_shift_app (zero_add n)]
        rfl
      add_zero_hom_app := fun n M => hom_ext fun X x => by
        rw [comp_app]
        dsimp only [Functor.id_obj]
        rw [eqToHom_shift_app (add_zero n)]
        rfl }

variable {C}

/--
@isnad1 id=eq.0h3v.s6.13cb4eb9ba7d from=translated src=- shape=29ff935e vocab=cd78d43e
-/
@[simp]
theorem shiftFunctor_obj (n : ℤ) (M : CatModule.{w} C) :
    (shiftFunctor (CatModule.{w} C) n).obj M = shift n M := rfl

/--
@isnad1 id=eq.1h7v.s12.4ae3293d3464 from=translated src=- shape=d2ba3a34 vocab=baaa9c08
-/
theorem shiftFunctorAdd'_hom_app_app (a b c : ℤ) (h : a + b = c) (M : CatModule.{w} C)
    {X : C} (x : (shift c M).obj X) :
    ((shiftFunctorAdd' (CatModule.{w} C) a b c h).hom.app M).app X x =
      shift.mk b (shift.mk a (shift.unmk c x)) := by
  subst h
  rfl

/--
@isnad1 id=eq.1h7v.s12.fc216f8a92fb from=translated src=- shape=2269ecf5 vocab=cd33e9ad
-/
theorem shiftFunctorAdd'_inv_app_app (a b c : ℤ) (h : a + b = c) (M : CatModule.{w} C)
    {X : C} (x : (shift b (shift a M)).obj X) :
    ((shiftFunctorAdd' (CatModule.{w} C) a b c h).inv.app M).app X x =
      shift.mk c (shift.unmk a (shift.unmk b x)) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h6v.s12.93acc4fbf8e0 from=translated src=- shape=54fb4aad vocab=b166e176
-/
theorem shiftFunctorComm_hom_app_app (a b : ℤ) (M : CatModule.{w} C) {X : C}
    (x : (shift b (shift a M)).obj X) :
    ((shiftFunctorComm (CatModule.{w} C) a b).hom.app M).app X x =
      shift.mk a (shift.mk b (shift.unmk a (shift.unmk b x))) := by
  rw [shiftFunctorComm_eq _ a b _ rfl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    comp_app, shiftFunctorAdd'_inv_app_app, shiftFunctorAdd'_hom_app_app]
  rfl

/--
@isnad1 id=eq.0h4v.s9.b94af3ee34b0 from=translated src=- shape=e6a4d5ef vocab=e276f70f
-/
theorem shiftFunctorComm_hom_app_eq (a b : ℤ) (M : CatModule.{w} C) :
    (shiftFunctorComm (CatModule.{w} C) a b).hom.app M = (shiftComm (M := M) a b).hom :=
  hom_ext fun _ x => shiftFunctorComm_hom_app_app a b M x

instance (n : ℤ) : (shiftFunctor (CatModule.{w} C) n).Additive where
  map_add := rfl

end HasShift

end CatModule

end DG

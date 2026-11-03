import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts
import Tengoku.Seed.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Tengoku.DgLean.DG.Algebra.AddEquiv
import Tengoku.DgLean.DG.Category.Functor
import Tengoku.DgLean.DG.Module.PUnit
import Tengoku.DgLean.DG.Module.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dg modules over a dg category

Following `docs/CONVENTIONS.md`, a (left) dg module over a dg category `C` is a covariant dg
functor from `C` to dg abelian groups, described concretely: a family `M.obj X` of dg abelian
groups indexed by the objects of `C`, with actions `(X ⟶ Y) → M.obj X → M.obj Y`, written
`f • m`, which are biadditive, graded (`(X ⟶ Y)ⁱ • (M X)ʲ ⊆ (M Y)ⁱ⁺ʲ`), unital, associative in
the form `(f ≫ g) • m = g • (f • m)`, and satisfy the Leibniz rule
`d (f • m) = d f • m + (-1)^{|f|} • (f • d m)`.

For the one-object dg category `SingleObj A` of a dg ring these are exactly the left dg
`A`-modules (`DG.Category.Comparison`).

## Main definitions

* `DG.CatModule.{w} C`: dg modules over `C` with values in `Type w`, as a bundled structure. The
  action is `DG.CatModule.act`, with notation `f • m` (an `HSMul` instance).
* `DG.CatModule.Hom M N`: the morphisms, families of additive maps `M.obj X →+ N.obj X` of
  degree `0` commuting with the differentials and with the actions. `DG.CatModule.category`.
* `DG.CatModule.preadditive`, `DG.CatModule.hasZeroObject`, `DG.CatModule.hasFiniteBiproducts`:
  the category is preadditive with a zero object and finite biproducts (computed objectwise).
* `DG.CatModule.isIso_of_bijective`: a morphism which is objectwise bijective is an
  isomorphism.
* `DG.CatModule.precomp F : CatModule D ⥤ CatModule C`: restriction along a dg functor
  `F : C ⥤ D`, `(M ∘ F).obj X = M.obj (F.obj X)`.
-/

open scoped DG

open CategoryTheory CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂

namespace DG

/-- A left dg module over a category `C` with dg Hom groups (in the applications, a dg
category): dg abelian groups `obj X` for the objects `X` of `C`, with biadditive actions
`act f : obj X →+ obj Y` of the morphisms `f : X ⟶ Y`, which are graded, unital, associative
(`(f ≫ g) • m = g • (f • m)`), and satisfy the Leibniz rule
`d (f • m) = d f • m + (-1)^{|f|} • (f • d m)` for `f` homogeneous.-/
structure CatModule (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] where
  /-- The dg abelian group attached to an object.-/
  obj : C → Type w
  [isAddCommGroup : ∀ X, AddCommGroup (obj X)]
  [isDGAddCommGroup : ∀ X, DGAddCommGroup (obj X)]
  /-- The action of the morphisms of `C`, biadditive.-/
  act : ∀ {X Y : C}, (X ⟶ Y) →+ obj X →+ obj Y
  act_mem' : ∀ {X Y : C} {i j : ℤ} {f : X ⟶ Y} {m : obj X}, f ∈ grading i → m ∈ grading j →
    act f m ∈ grading (i + j)
  act_id' : ∀ (X : C) (m : obj X), act (𝟙 X) m = m
  act_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (m : obj X), act (f ≫ g) m = act g (act f m)
  d_act' : ∀ {X Y : C} {i : ℤ} {f : X ⟶ Y}, f ∈ grading i → ∀ m : obj X,
    d (act f m) = act (d f) m + koszulSign i • act f (d m)

attribute [instance] CatModule.isAddCommGroup CatModule.isDGAddCommGroup

namespace CatModule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section Action

variable (M : CatModule.{w} C)

/-- The action of the morphisms of `C` on a dg module, `f • m = M.act f m`.-/
instance instHSMul {X Y : C} : HSMul (X ⟶ Y) (M.obj X) (M.obj Y) :=
  ⟨fun f m => M.act f m⟩

variable {M}

/--
@isnad1 id=eq.0h6v.s11.5075e55ec3d0 from=translated src=- shape=87880c6f vocab=ae8fce26
-/
theorem act_apply {X Y : C} (f : X ⟶ Y) (m : M.obj X) : M.act f m = f • m := rfl

/--
@isnad1 id=mem.2h8v.s8.98d609ce8129 from=translated src=- shape=1c5fc7ad vocab=26f9162a
-/
theorem smul_mem_grading {X Y : C} {i j : ℤ} {f : X ⟶ Y} {m : M.obj X} (hf : f ∈ grading i)
    (hm : m ∈ grading j) : f • m ∈ grading (i + j) :=
  M.act_mem' hf hm

/--
@isnad1 id=eq.0h4v.s6.fbd00147ffcc from=translated src=- shape=1f523afc vocab=5b7dfd2b
-/
@[simp]
theorem id_smul {X : C} (m : M.obj X) : (𝟙 X) • m = m :=
  M.act_id' X m

/--
@isnad1 id=eq.0h8v.s7.5fd3783979e1 from=translated src=- shape=75034928 vocab=3506faff
-/
theorem comp_smul {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (m : M.obj X) :
    (f ≫ g) • m = g • f • m :=
  M.act_comp' f g m

/-- The Leibniz rule for the action.
@isnad1 id=eq.1h7v.s10.0cf6ddfd3b27 from=translated src=- shape=2b234e5d vocab=7e15e1be
-/
theorem d_smul {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (m : M.obj X) :
    d (f • m) = d f • m + koszulSign i • f • d m :=
  M.d_act' hf m

/--
@isnad1 id=eq.1h6v.s10.b14785e7ae30 from=translated src=- shape=5e0a086f vocab=b9bca501
-/
theorem d_smul_of_mem_zero {X Y : C} {f : X ⟶ Y} (hf : f ∈ grading 0) (m : M.obj X) :
    d (f • m) = d f • m + f • d m := by
  rw [d_smul hf, koszulSign_zero, one_smul]

/-- For a homogeneous cocycle `f` of degree `i`, `d (f • m) = (-1)^i • (f • d m)`.
@isnad1 id=eq.2h7v.s10.154fb9bdfcee from=translated src=- shape=b14240ba vocab=30a057a4
-/
theorem d_smul_of_d_eq_zero {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i) (hdf : d f = 0)
    (m : M.obj X) : d (f • m) = koszulSign i • f • d m := by
  rw [d_smul hf, hdf]
  change M.act 0 m + _ = _
  rw [map_zero, AddMonoidHom.zero_apply, zero_add]

/--
@isnad1 id=eq.0h7v.s8.98db87ce8c7d from=translated src=- shape=94f86be5 vocab=9b721676
-/
@[simp]
theorem add_smul {X Y : C} (f g : X ⟶ Y) (m : M.obj X) : (f + g) • m = f • m + g • m := by
  change M.act (f + g) m = M.act f m + M.act g m
  rw [map_add, AddMonoidHom.add_apply]

/--
@isnad1 id=eq.0h7v.s8.2c1deb3149b9 from=translated src=- shape=bbbd6b91 vocab=9b721676
-/
@[simp]
theorem smul_add {X Y : C} (f : X ⟶ Y) (m m' : M.obj X) : f • (m + m') = f • m + f • m' :=
  map_add (M.act f) m m'

/--
@isnad1 id=eq.0h5v.s7.1c6c25900cd8 from=translated src=- shape=30d97682 vocab=8adfea50
-/
@[simp]
theorem zero_smul {X Y : C} (m : M.obj X) : (0 : X ⟶ Y) • m = (0 : M.obj Y) := by
  change M.act 0 m = 0
  rw [map_zero, AddMonoidHom.zero_apply]

/--
@isnad1 id=eq.0h5v.s7.9b2298767a2a from=translated src=- shape=e18dc2ed vocab=8adfea50
-/
@[simp]
theorem smul_zero {X Y : C} (f : X ⟶ Y) : f • (0 : M.obj X) = (0 : M.obj Y) :=
  map_zero (M.act f)

/--
@isnad1 id=eq.0h6v.s7.ebbae89320c2 from=translated src=- shape=ddfca8c1 vocab=73590fd1
-/
@[simp]
theorem neg_smul {X Y : C} (f : X ⟶ Y) (m : M.obj X) : (-f) • m = -(f • m) := by
  change M.act (-f) m = -M.act f m
  rw [map_neg, AddMonoidHom.neg_apply]

/--
@isnad1 id=eq.0h6v.s7.3ce51facb12b from=translated src=- shape=78a92d33 vocab=73590fd1
-/
@[simp]
theorem smul_neg {X Y : C} (f : X ⟶ Y) (m : M.obj X) : f • (-m) = -(f • m) :=
  map_neg (M.act f) m

/--
@isnad1 id=eq.0h7v.s8.f2a82c3252ff from=translated src=- shape=94f86be5 vocab=b51dd536
-/
@[simp]
theorem sub_smul {X Y : C} (f g : X ⟶ Y) (m : M.obj X) : (f - g) • m = f • m - g • m := by
  rw [sub_eq_add_neg, add_smul, neg_smul, sub_eq_add_neg]

/--
@isnad1 id=eq.0h7v.s8.08ca9f0801ef from=translated src=- shape=bbbd6b91 vocab=b51dd536
-/
@[simp]
theorem smul_sub {X Y : C} (f : X ⟶ Y) (m m' : M.obj X) : f • (m - m') = f • m - f • m' :=
  map_sub (M.act f) m m'

/--
@isnad1 id=eq.0h7v.s8.4a697a90d524 from=translated src=- shape=6c226160 vocab=a5f2bd33
-/
@[simp]
theorem zsmul_smul {X Y : C} (n : ℤ) (f : X ⟶ Y) (m : M.obj X) : (n • f) • m = n • f • m := by
  change M.act (n • f) m = n • M.act f m
  rw [map_zsmul, AddMonoidHom.smul_apply]

/--
@isnad1 id=eq.0h7v.s8.db0419567c6f from=translated src=- shape=cbd2cfcb vocab=a5f2bd33
-/
@[simp]
theorem smul_zsmul {X Y : C} (f : X ⟶ Y) (n : ℤ) (m : M.obj X) : f • (n • m) = n • f • m :=
  map_zsmul (M.act f) n m

/--
@isnad1 id=eq.0h7v.s8.febef04c8244 from=translated src=- shape=64aaed47 vocab=5b0151e6
-/
@[simp]
theorem units_smul_smul {X Y : C} (u : ℤˣ) (f : X ⟶ Y) (m : M.obj X) :
    (u • f) • m = u • f • m := by
  rw [Units.smul_def, Units.smul_def, zsmul_smul]

/--
@isnad1 id=eq.0h7v.s8.dab32f2a169d from=translated src=- shape=9c7022f6 vocab=5b0151e6
-/
@[simp]
theorem smul_units_smul {X Y : C} (f : X ⟶ Y) (u : ℤˣ) (m : M.obj X) :
    f • (u • m) = u • f • m := by
  rw [Units.smul_def, Units.smul_def, smul_zsmul]

/-- If `m` is a cocycle then `d (f • m) = d f • m` for every `f`.
@isnad1 id=eq.1h6v.s10.a7af047b8e1d from=translated src=- shape=fbcf56e8 vocab=c3a21633
-/
theorem d_smul_of_d_eq_zero_right {X Y : C} {m : M.obj X} (hm : d m = 0) (f : X ⟶ Y) :
    d (f • m) = d f • m := by
  induction f using induction_on with
  | h_zero =>
    change d (M.act 0 m) = M.act (d 0) m
    rw [d_zero, map_zero, AddMonoidHom.zero_apply, d_zero]
  | h_homogeneous f => rw [d_smul f.2, hm, smul_zero, _root_.smul_zero, add_zero]
  | h_add f f' hf hf' =>
    change d (M.act (f + f') m) = M.act (d (f + f')) m
    rw [d_add, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, d_add]
    exact congrArg₂ (· + ·) hf hf'

/--
@isnad1 id=eq.0h8v.s7.cc2b81b6154c from=translated src=- shape=173a7bad vocab=e4529b9f
-/
theorem sum_smul {X Y : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) (m : M.obj X) :
    (∑ i ∈ s, f i) • m = ∑ i ∈ s, f i • m := by
  change M.act (∑ i ∈ s, f i) m = ∑ i ∈ s, M.act (f i) m
  rw [map_sum, AddMonoidHom.finsetSum_apply]

/--
@isnad1 id=eq.0h8v.s7.2f80a629c9df from=translated src=- shape=8d9b04c7 vocab=e4529b9f
-/
theorem smul_sum {X Y : C} {ι : Type*} (s : Finset ι) (f : X ⟶ Y) (m : ι → M.obj X) :
    f • (∑ i ∈ s, m i) = ∑ i ∈ s, f • m i :=
  map_sum (M.act f) m s

end Action

/-- A morphism of dg modules over `C`: a family of additive maps `M.obj X →+ N.obj X` of
degree `0` commuting with the differentials and with the actions.-/
structure Hom (M N : CatModule.{w} C) where
  /-- The component at an object.-/
  app : ∀ X : C, M.obj X →+ N.obj X
  map_mem' : ∀ {X : C} {n : ℤ} {m : M.obj X}, m ∈ grading n → app X m ∈ grading n
  map_d' : ∀ {X : C} (m : M.obj X), app X (d m) = d (app X m)
  map_smul' : ∀ {X Y : C} (f : X ⟶ Y) (m : M.obj X), app Y (f • m) = f • app X m

namespace Hom

variable {M N : CatModule.{w} C}

/--
@isnad1 id=eq.1h5v.s9.32945396ee99 from=translated src=- shape=573f0c13 vocab=386550a9
-/
@[ext]
theorem ext {φ ψ : Hom M N} (h : ∀ X m, φ.app X m = ψ.app X m) : φ = ψ := by
  obtain ⟨φ, _, _, _⟩ := φ
  obtain ⟨ψ, _, _, _⟩ := ψ
  congr
  funext X
  exact AddMonoidHom.ext (h X)

variable (φ : Hom M N)

/--
@isnad1 id=mem.1h7v.s9.9e57387a58d0 from=translated src=- shape=725fe356 vocab=2c56276e
-/
theorem map_mem {X : C} {n : ℤ} {m : M.obj X} (hm : m ∈ grading n) : φ.app X m ∈ grading n :=
  φ.map_mem' hm

/--
@isnad1 id=eq.0h6v.s10.b14fe6d103bb from=translated src=- shape=02e487eb vocab=67849f61
-/
@[simp]
theorem map_d {X : C} (m : M.obj X) : φ.app X (d m) = d (φ.app X m) :=
  φ.map_d' m

/--
@isnad1 id=eq.0h8v.s9.1fb3f9880cb8 from=translated src=- shape=d8ecc606 vocab=b66f0a3a
-/
@[simp]
theorem map_smul {X Y : C} (f : X ⟶ Y) (m : M.obj X) : φ.app Y (f • m) = f • φ.app X m :=
  φ.map_smul' f m

/-- The identity morphism.-/
def id (M : CatModule.{w} C) : Hom M M where
  app _ := AddMonoidHom.id _
  map_mem' hm := hm
  map_d' _ := rfl
  map_smul' _ _ := rfl

/-- Composition of morphisms.-/
def comp {P : CatModule.{w} C} (φ : Hom M N) (ψ : Hom N P) : Hom M P where
  app X := (ψ.app X).comp (φ.app X)
  map_mem' hm := ψ.map_mem (φ.map_mem hm)
  map_d' m := by simp
  map_smul' f m := by simp

end Hom

instance category : Category.{max u₁ w} (CatModule.{w} C) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp φ ψ := φ.comp ψ

section HomLemmas

variable {M N P : CatModule.{w} C}

/--
@isnad1 id=eq.1h5v.s9.b3b370ad43dd from=translated src=- shape=7a253a53 vocab=54aa9362
-/
@[ext]
theorem hom_ext {φ ψ : M ⟶ N} (h : ∀ X m, φ.app X m = ψ.app X m) : φ = ψ :=
  Hom.ext h

/--
@isnad1 id=eq.0h4v.s8.35aef65bd1c8 from=translated src=- shape=f9272431 vocab=7af75d24
-/
@[simp]
theorem id_app (M : CatModule.{w} C) (X : C) (m : M.obj X) : (𝟙 M : M ⟶ M).app X m = m := rfl

/--
@isnad1 id=eq.0h8v.s9.befd43d08ea7 from=translated src=- shape=207e459b vocab=0e33eaa0
-/
@[simp]
theorem comp_app (φ : M ⟶ N) (ψ : N ⟶ P) (X : C) (m : M.obj X) :
    (φ ≫ ψ).app X m = ψ.app X (φ.app X m) := rfl

/--
@isnad1 id=injectiv.0h3v.s7.6ee83f6e0e9b from=translated src=- shape=381c7cc9 vocab=e4ddebc7
-/
theorem hom_injective : Function.Injective (Hom.app : (M ⟶ N) → ∀ X, M.obj X →+ N.obj X) :=
  fun _ _ h => hom_ext fun X m => congrArg (fun φ => φ X m) h

end HomLemmas

/-! ### Preadditive structure -/

section Preadditive

variable {M N : CatModule.{w} C}

instance : Zero (M ⟶ N) :=
  ⟨{ app := fun _ => 0
     map_mem' := fun _ => zero_mem _
     map_d' := fun _ => by simp
     map_smul' := fun _ _ => by simp }⟩

instance : Add (M ⟶ N) :=
  ⟨fun φ ψ =>
    { app := fun X => φ.app X + ψ.app X
      map_mem' := fun hm => add_mem (φ.map_mem hm) (ψ.map_mem hm)
      map_d' := fun _ => by simp [d_add]
      map_smul' := fun _ _ => by simp }⟩

instance : Neg (M ⟶ N) :=
  ⟨fun φ =>
    { app := fun X => -φ.app X
      map_mem' := fun hm => neg_mem (φ.map_mem hm)
      map_d' := fun _ => by simp [d_neg]
      map_smul' := fun _ _ => by simp }⟩

instance : Sub (M ⟶ N) :=
  ⟨fun φ ψ =>
    { app := fun X => φ.app X - ψ.app X
      map_mem' := fun hm => sub_mem (φ.map_mem hm) (ψ.map_mem hm)
      map_d' := fun _ => by simp [d_sub]
      map_smul' := fun _ _ => by simp }⟩

instance : SMul ℕ (M ⟶ N) :=
  ⟨fun n φ =>
    { app := fun X => n • φ.app X
      map_mem' := fun hm => nsmul_mem (φ.map_mem hm) n
      map_d' := fun _ => by simp [d_nsmul]
      map_smul' := fun _ _ => by simp [← natCast_zsmul] }⟩

instance : SMul ℤ (M ⟶ N) :=
  ⟨fun n φ =>
    { app := fun X => n • φ.app X
      map_mem' := fun hm => zsmul_mem (φ.map_mem hm) n
      map_d' := fun _ => by simp [d_zsmul]
      map_smul' := fun _ _ => by simp }⟩

/--
@isnad1 id=eq.0h5v.s8.2092bd4fcb96 from=translated src=- shape=9a2485c4 vocab=54aa9362
-/
@[simp] theorem zero_app (X : C) (m : M.obj X) : (0 : M ⟶ N).app X m = 0 := rfl
/--
@isnad1 id=eq.0h7v.s10.17c3f0e6753a from=translated src=- shape=e6eaa577 vocab=73712ced
-/
@[simp] theorem add_app (φ ψ : M ⟶ N) (X : C) (m : M.obj X) :
    (φ + ψ).app X m = φ.app X m + ψ.app X m := rfl
/--
@isnad1 id=eq.0h6v.s9.8f95e211eb44 from=translated src=- shape=e2d95600 vocab=15c34e3b
-/
@[simp] theorem neg_app (φ : M ⟶ N) (X : C) (m : M.obj X) : (-φ).app X m = -φ.app X m := rfl
/--
@isnad1 id=eq.0h7v.s10.2ebf73a2c8e8 from=translated src=- shape=e6eaa577 vocab=73ca8cd6
-/
@[simp] theorem sub_app (φ ψ : M ⟶ N) (X : C) (m : M.obj X) :
    (φ - ψ).app X m = φ.app X m - ψ.app X m := rfl
/--
@isnad1 id=eq.0h7v.s9.1612815fb015 from=translated src=- shape=e1515f96 vocab=e12b6ed0
-/
@[simp] theorem nsmul_app (n : ℕ) (φ : M ⟶ N) (X : C) (m : M.obj X) :
    (n • φ).app X m = n • φ.app X m := rfl
/--
@isnad1 id=eq.0h7v.s9.8d1373f9858b from=translated src=- shape=e1515f96 vocab=281e68a2
-/
@[simp] theorem zsmul_app (n : ℤ) (φ : M ⟶ N) (X : C) (m : M.obj X) :
    (n • φ).app X m = n • φ.app X m := rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup Hom.app hom_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance preadditive : Preadditive (CatModule.{w} C) where
  add_comp _ _ _ _ _ _ := hom_ext fun _ _ => by simp
  comp_add _ _ _ _ _ _ := hom_ext fun _ _ => by simp

end Preadditive

/-! ### Isomorphisms -/

section Iso

variable {M N : CatModule.{w} C}

/-- An isomorphism of dg modules from objectwise additive equivalences of degree `0` commuting
with the differentials and the actions.-/
@[simps]
def isoMk (e : ∀ X, M.obj X ≃+ N.obj X)
    (he : ∀ {X : C} {n : ℤ} {m : M.obj X}, e X m ∈ grading n ↔ m ∈ grading n)
    (hd : ∀ {X : C} (m : M.obj X), e X (d m) = d (e X m))
    (hs : ∀ {X Y : C} (f : X ⟶ Y) (m : M.obj X), e Y (f • m) = f • e X m) : M ≅ N where
  hom :=
    { app := fun X => (e X).toAddMonoidHom
      map_mem' := fun hm => he.mpr hm
      map_d' := hd
      map_smul' := hs }
  inv :=
    { app := fun X => (e X).symm.toAddMonoidHom
      map_mem' := fun {X n m} hm => by
        rw [← he]
        simpa using hm
      map_d' := fun {X} m => (e X).injective (by simp [hd])
      map_smul' := fun {X Y} f m => (e Y).injective (by simp [hs]) }
  hom_inv_id := hom_ext fun _ _ => by simp
  inv_hom_id := hom_ext fun _ _ => by simp

/-- A morphism which is bijective at every object is an isomorphism.
@isnad1 id=isiso.1h4v.s8.6833d2eb7c1e from=translated src=- shape=5654ad54 vocab=60b5cc69
-/
theorem isIso_of_bijective (φ : M ⟶ N) (hφ : ∀ X, Function.Bijective (φ.app X)) : IsIso φ := by
  let e : ∀ X, M.obj X ≃+ N.obj X := fun X => AddEquiv.ofBijective (φ.app X) (hφ X)
  have he : ∀ {X : C} {n : ℤ} {m : M.obj X}, e X m ∈ grading n ↔ m ∈ grading n :=
    fun {X n m} => ⟨fun h => mem_grading_of_injective (φ.app X) (fun h => φ.map_mem h)
      (hφ X).injective h, fun h => φ.map_mem h⟩
  exact (isoMk e he (fun m => φ.map_d m) (fun f m => φ.map_smul f m)).isIso_hom

/-- A morphism of dg modules is an isomorphism if and only if it is bijective at every
object.
@isnad1 id=iff.0h4v.s8.325418d8dcdc from=translated src=- shape=ca726a82 vocab=60b5cc69
-/
theorem isIso_iff_bijective (φ : M ⟶ N) : IsIso φ ↔ ∀ X, Function.Bijective (φ.app X) := by
  refine ⟨fun _ X => ⟨fun a b h => ?_, fun b => ⟨(inv φ).app X b, ?_⟩⟩, isIso_of_bijective φ⟩
  · have := congrArg ((inv φ).app X) h
    rwa [← comp_app, ← comp_app, IsIso.hom_inv_id] at this
  · rw [← comp_app, IsIso.inv_hom_id, id_app]

end Iso

/-! ### The zero object -/

section Zero

/-- The zero dg module.-/
@[simps]
def zero : CatModule.{w} C where
  obj _ := PUnit
  act := 0
  act_mem' _ _ := trivial
  act_id' _ _ := rfl
  act_comp' _ _ _ := rfl
  d_act' _ _ := rfl

/--
@isnad1 id=iszero.0h2v.s5.14b72266b2d0 from=translated src=- shape=55b7a720 vocab=5ffd24ab
-/
theorem isZero_of_subsingleton (M : CatModule.{w} C) [∀ X, Subsingleton (M.obj X)] :
    IsZero M where
  unique_to N := ⟨⟨⟨0⟩, fun φ => hom_ext fun X m => by
    rw [Subsingleton.elim m 0, map_zero, map_zero]⟩⟩
  unique_from N := ⟨⟨⟨0⟩, fun _ => hom_ext fun _ _ => Subsingleton.elim _ _⟩⟩

instance : ∀ X : C, Subsingleton ((zero.{w} (C := C)).obj X) :=
  fun _ => inferInstanceAs (Subsingleton PUnit)

/--
@isnad1 id=iszero.0h1v.s5.94d58c6f5e7d from=translated src=- shape=28c2d72a vocab=1193ad60
-/
theorem isZero_zero : IsZero (zero.{w} (C := C)) :=
  isZero_of_subsingleton _

/--
@isnad1 id=haszeroo.0h1v.s5.c7f7f0b33030 from=translated src=- shape=37b11a11 vocab=5516917b
-/
instance hasZeroObject : HasZeroObject (CatModule.{w} C) :=
  ⟨⟨zero, isZero_zero⟩⟩

end Zero

/-! ### Finite biproducts -/

section Biproducts

variable (M N : CatModule.{w} C)

/-- The objectwise product of two dg modules.-/
def prod : CatModule.{w} C where
  obj X := M.obj X × N.obj X
  act := AddMonoidHom.mk' (fun f => AddMonoidHom.prodMap (M.act f) (N.act f)) fun f g => by
    ext <;> simp
  act_mem' hf hm := Prod.mem_grading.mpr
    ⟨smul_mem_grading hf (Prod.mem_grading.mp hm).1, smul_mem_grading hf (Prod.mem_grading.mp hm).2⟩
  act_id' _ _ := Prod.ext (id_smul _) (id_smul _)
  act_comp' _ _ _ := Prod.ext (comp_smul _ _ _) (comp_smul _ _ _)
  d_act' hf m := Prod.ext (d_smul (M := M) hf m.1) (d_smul (M := N) hf m.2)

/--
@isnad1 id=eq.0h7v.s7.00d7cbaab2ce from=translated src=- shape=5cdc1a77 vocab=e76ce66f
-/
@[simp]
theorem prod_smul_fst {X Y : C} (f : X ⟶ Y) (m : (prod M N).obj X) : (f • m).1 = f • m.1 := rfl

/--
@isnad1 id=eq.0h7v.s7.62a350e94450 from=translated src=- shape=e12bee45 vocab=f5abad3e
-/
@[simp]
theorem prod_smul_snd {X Y : C} (f : X ⟶ Y) (m : (prod M N).obj X) : (f • m).2 = f • m.2 := rfl

/-- The first projection out of the product.-/
@[simps]
def fst : prod M N ⟶ M where
  app _ := AddMonoidHom.fst _ _
  map_mem' hm := hm.1
  map_d' _ := rfl
  map_smul' _ _ := rfl

/-- The second projection out of the product.-/
@[simps]
def snd : prod M N ⟶ N where
  app _ := AddMonoidHom.snd _ _
  map_mem' hm := hm.2
  map_d' _ := rfl
  map_smul' _ _ := rfl

variable {M N} in
/-- The morphism into the product given by two morphisms.-/
@[simps]
def lift {P : CatModule.{w} C} (φ : P ⟶ M) (ψ : P ⟶ N) : P ⟶ prod M N where
  app X := AddMonoidHom.prod (φ.app X) (ψ.app X)
  map_mem' hm := ⟨φ.map_mem hm, ψ.map_mem hm⟩
  map_d' m := Prod.ext (φ.map_d m) (ψ.map_d m)
  map_smul' f m := Prod.ext (φ.map_smul f m) (ψ.map_smul f m)

/-- The binary product of two dg modules, computed objectwise.-/
def binaryProductLimitCone : LimitCone (pair M N) where
  cone := BinaryFan.mk (fst M N) (snd M N)
  isLimit := BinaryFan.isLimitMk (fun s => lift s.fst s.snd) (fun _ => rfl) (fun _ => rfl)
    fun s _ h₁ h₂ => hom_ext fun X x =>
      Prod.ext (congrArg (fun φ : s.pt ⟶ M => φ.app X x) h₁)
        (congrArg (fun φ : s.pt ⟶ N => φ.app X x) h₂)

instance : HasLimit (pair M N) :=
  HasLimit.mk (binaryProductLimitCone M N)

/--
@isnad1 id=hasbinar.0h1v.s5.d87aa5c9eba5 from=translated src=- shape=37b11a11 vocab=e856a2e0
-/
instance hasBinaryProducts : HasBinaryProducts (CatModule.{w} C) :=
  hasBinaryProducts_of_hasLimit_pair _

/--
@isnad1 id=hasfinit.0h1v.s5.302c6dfbbc6f from=translated src=- shape=37b11a11 vocab=ec5fbbb2
-/
instance hasFiniteProducts : HasFiniteProducts (CatModule.{w} C) :=
  hasFiniteProducts_of_has_binary_and_terminal

/--
@isnad1 id=hasbinar.0h1v.s5.f0f4b94a3d5b from=translated src=- shape=37b11a11 vocab=ce62311f
-/
instance hasBinaryBiproducts : HasBinaryBiproducts (CatModule.{w} C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/--
@isnad1 id=hasfinit.0h1v.s5.29d6efefdb26 from=translated src=- shape=37b11a11 vocab=91d752aa
-/
instance hasFiniteBiproducts : HasFiniteBiproducts (CatModule.{w} C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end Biproducts

/-! ### Restriction along dg functors -/

section Precomp

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.IsDGFunctor]

/-- The restriction of a dg module over `D` along a dg functor `F : C ⥤ D`:
`X ↦ M.obj (F.obj X)`, with `f • m = F.map f • m`.-/
@[simps]
def precompObj (M : CatModule.{w} D) : CatModule.{w} C where
  obj X := M.obj (F.obj X)
  act := M.act.comp F.mapAddHom
  act_mem' hf hm := smul_mem_grading (F.map_mem_grading hf) hm
  act_id' X m := by
    change F.map (𝟙 X) • m = m
    rw [F.map_id, id_smul]
  act_comp' f g m := by
    change F.map (f ≫ g) • m = F.map g • F.map f • m
    rw [F.map_comp, comp_smul]
  d_act' {X Y i f} hf m := by
    change d (F.map f • m) = F.map (d f) • m + koszulSign i • F.map f • d m
    rw [F.map_d, d_smul (F.map_mem_grading hf)]

/--
@isnad1 id=eq.0h8v.s11.9b5bc2a34d8e from=translated src=- shape=35dcdd65 vocab=f1616ddd
-/
theorem precompObj_smul (M : CatModule.{w} D) {X Y : C} (f : X ⟶ Y)
    (m : (precompObj F M).obj X) : f • m = M.act (F.map f) m :=
  rfl

/-- Restriction along a dg functor `F : C ⥤ D`, as a functor
`CatModule D ⥤ CatModule C`.-/
@[simps]
def precomp : CatModule.{w} D ⥤ CatModule.{w} C where
  obj M := precompObj F M
  map φ :=
    { app := fun X => φ.app (F.obj X)
      map_mem' := fun hm => φ.map_mem hm
      map_d' := fun m => φ.map_d m
      map_smul' := fun f m => φ.map_smul (F.map f) m }

instance : (precomp.{w} F).Additive where

end Precomp

end CatModule

end DG

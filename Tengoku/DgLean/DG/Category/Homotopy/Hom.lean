import Tengoku.DgLean.DG.Category.Module
import Tengoku.DgLean.DG.Module.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Hom complex of dg modules over a dg category

Let `C` be a category with dg Hom groups and `M`, `N` dg modules over `C`
(`DG.CatModule`). This file constructs the Hom complex `HOM_C(M, N)`, whose degree-`n` part
consists of the families of additive maps `M.obj X → N.obj X` of degree `n` which commute with
the action of `C` up to the Koszul sign, and whose differential is
`δ z = d ∘ z - (-1)^{|z|} z ∘ d`, objectwise. It is a port of `DG.Module.Hom` (the case of a dg
ring, i.e. of the one-object dg category), with the same names in the namespace
`DG.CatModule`, the same statements and the same signs; the single carrier of a dg module is
replaced by the family `M.obj X` and the action of the ring by the action of the morphisms of
`C`.

## Main definitions

* `DG.CatModule.Cochain M N n`: the cochains of degree `n`, families of additive maps
  `app X : M.obj X →+ N.obj X` sending `(M X)ⁱ` into `(N X)ⁱ⁺ⁿ` with
  `app Y (f • x) = (-1)^{n i} • (f • app X x)` for `f ∈ (X ⟶ Y)ⁱ`. These form an additive group.
* `DG.CatModule.Cochain.comp z₂ z₁ h`: the composition `z₂ ∘ z₁` (first `z₁`), a cochain of
  any degree `n₁₂` with `h : n₁ + n₂ = n₁₂`; `DG.CatModule.Cochain.id M`: the identity.
* `DG.CatModule.Cochain.ofHom φ`: the `0`-cochain of a morphism of dg modules `φ : M ⟶ N`.
* `DG.CatModule.δ n m z`: the differential of the Hom complex, a cochain of degree `m`, equal to
  `d ∘ z - (-1)^n • z ∘ d` if `n + 1 = m` and to `0` otherwise.
* `DG.CatModule.cocycle M N n`, `DG.CatModule.Cocycle M N n`: the cocycles of degree `n`, and
  `DG.CatModule.Cocycle.equivHom : (M ⟶ N) ≃+ Cocycle M N 0`.
* `DG.CatModule.HOM M N := ⨁ n, Cochain M N n`: the Hom complex as a dg abelian group.

## Main results

* `DG.CatModule.δ_δ`: `δ ∘ δ = 0`.
* `DG.CatModule.δ_comp`: the Leibniz rule `δ (z₂ ∘ z₁) = δ z₂ ∘ z₁ + (-1)^{n₂} • z₂ ∘ δ z₁`.
* `DG.CatModule.δ_ofHom`, `DG.CatModule.Cocycle.equivHom`: the degree-`0` cocycles are exactly
  the morphisms of dg modules.

## Conventions

As in `DG.Module.Hom`, cochains compose in the usual order (`z₂.comp z₁ h` applies `z₁` first)
and the differential agrees with Mathlib's `CochainComplex.HomComplex.δ`:
`δ z = d ∘ z + (-1)^m • z ∘ d` for `n + 1 = m` (`DG.CatModule.δ_apply'`).
-/

open scoped DG

open CategoryTheory DirectSum

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

section Defs

/-- A cochain of degree `n` from `M` to `N` (a homogeneous element of degree `n` of the Hom
complex `HOM_C(M, N)`): a family of additive maps of degree `n` commuting with the action of
`C` up to the Koszul sign, `app Y (f • x) = (-1)^{n i} • (f • app X x)` for `f ∈ (X ⟶ Y)ⁱ`.-/
structure Cochain (M N : CatModule.{w} C) (n : ℤ) where
  /-- The component at an object.-/
  app : ∀ X : C, M.obj X →+ N.obj X
  map_mem' : ∀ {X : C} {i : ℤ} {x : M.obj X}, x ∈ grading i → app X x ∈ grading (i + n)
  /-- The Koszul-signed linearity: `app Y (f • x) = (-1)^{n i} • (f • app X x)` for
  `f ∈ (X ⟶ Y)ⁱ`.-/
  map_smul' : ∀ {X Y : C} {i : ℤ} {f : X ⟶ Y}, f ∈ grading i → ∀ x : M.obj X,
    app Y (f • x) = koszulSign (n * i) • (f • app X x)

end Defs

namespace Cochain

variable {M N P Q : CatModule.{w} C}

section Basic

variable {n : ℤ}

/--
@isnad1 id=eq.1h6v.s9.6b64be55af6c from=translated src=- shape=63bb7a47 vocab=b78721e6
-/
@[ext]
theorem ext {z₁ z₂ : Cochain M N n} (h : ∀ X x, z₁.app X x = z₂.app X x) : z₁ = z₂ := by
  obtain ⟨_, _, _⟩ := z₁
  obtain ⟨_, _, _⟩ := z₂
  congr
  funext X
  exact AddMonoidHom.ext (h X)

/--
@isnad1 id=injectiv.0h4v.s7.0766c121fbde from=translated src=- shape=63db4304 vocab=cc0113e8
-/
theorem app_injective : Function.Injective (app : Cochain M N n → ∀ X, M.obj X →+ N.obj X) :=
  fun _ _ h => ext fun X x => congrArg (fun φ => φ X x) h

/--
@isnad1 id=mem.1h8v.s9.86fa5ac34f34 from=translated src=- shape=6234b879 vocab=e9ea8dcd
-/
theorem map_mem (z : Cochain M N n) {X : C} {i : ℤ} {x : M.obj X} (hx : x ∈ grading i) :
    z.app X x ∈ grading (i + n) :=
  z.map_mem' hx

/--
@isnad1 id=eq.1h10v.s9.9dfadff1d4b8 from=translated src=- shape=0bee081f vocab=9e49738e
-/
theorem map_smul (z : Cochain M N n) {X Y : C} {i : ℤ} {f : X ⟶ Y} (hf : f ∈ grading i)
    (x : M.obj X) : z.app Y (f • x) = koszulSign (n * i) • (f • z.app X x) :=
  z.map_smul' hf x

/--
@isnad1 id=eq.0h8v.s9.4fad4ab8c9e9 from=translated src=- shape=20d5e4e4 vocab=3c0ab285
-/
theorem map_units_smul (z : Cochain M N n) {X : C} (u : ℤˣ) (x : M.obj X) :
    z.app X (u • x) = u • z.app X x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- Two cochains of possibly different (but equal) degrees agreeing pointwise are
heterogeneously equal.
@isnad1 id=heq.2h7v.s9.0f09cfd698c8 from=translated src=- shape=1af54dda vocab=41701ea7
-/
theorem heq_of_forall {m n : ℤ} {z₁ : Cochain M N m} {z₂ : Cochain M N n} (hmn : m = n)
    (h : ∀ X x, z₁.app X x = z₂.app X x) : HEq z₁ z₂ := by
  subst hmn
  exact heq_of_eq (ext h)

end Basic

section AddCommGroup

variable {n : ℤ}

instance : Zero (Cochain M N n) :=
  ⟨{ app := fun _ => 0
     map_mem' := fun _ => zero_mem _
     map_smul' := fun _ _ => by simp }⟩

instance : Add (Cochain M N n) :=
  ⟨fun z₁ z₂ =>
    { app := fun X => z₁.app X + z₂.app X
      map_mem' := fun hx => add_mem (z₁.map_mem hx) (z₂.map_mem hx)
      map_smul' := fun hf x => by
        simp only [AddMonoidHom.add_apply, z₁.map_smul hf, z₂.map_smul hf, smul_add,
          _root_.smul_add] }⟩

instance : Neg (Cochain M N n) :=
  ⟨fun z =>
    { app := fun X => -z.app X
      map_mem' := fun hx => neg_mem (z.map_mem hx)
      map_smul' := fun hf x => by
        simp only [AddMonoidHom.neg_apply, z.map_smul hf, smul_neg,
          _root_.smul_neg] }⟩

instance : Sub (Cochain M N n) :=
  ⟨fun z₁ z₂ =>
    { app := fun X => z₁.app X - z₂.app X
      map_mem' := fun hx => sub_mem (z₁.map_mem hx) (z₂.map_mem hx)
      map_smul' := fun hf x => by
        simp only [AddMonoidHom.sub_apply, z₁.map_smul hf, z₂.map_smul hf, smul_sub,
          _root_.smul_sub] }⟩

instance : SMul ℕ (Cochain M N n) :=
  ⟨fun k z =>
    { app := fun X => k • z.app X
      map_mem' := fun hx => nsmul_mem (z.map_mem hx) k
      map_smul' := fun {X Y i f} hf x => by
        change k • z.app Y (f • x) = _ • (f • (k • z.app X x))
        rw [z.map_smul hf, show f • (k • z.app X x) = k • (f • z.app X x) from
          map_nsmul (N.act f) k _, smul_comm k] }⟩

instance : SMul ℤ (Cochain M N n) :=
  ⟨fun k z =>
    { app := fun X => k • z.app X
      map_mem' := fun hx => zsmul_mem (z.map_mem hx) k
      map_smul' := fun {X Y i f} hf x => by
        change k • z.app Y (f • x) = _ • (f • (k • z.app X x))
        rw [z.map_smul hf, smul_zsmul, smul_comm k] }⟩

/--
@isnad1 id=eq.0h5v.s9.dd2b4561e8b9 from=translated src=- shape=1829bc24 vocab=0d09daa0
-/
@[simp] theorem zero_app (X : C) : (0 : Cochain M N n).app X = 0 := rfl
/--
@isnad1 id=eq.0h7v.s9.ab1d1b02e041 from=translated src=- shape=fd8c481f vocab=1d1c0c31
-/
@[simp] theorem add_app (z₁ z₂ : Cochain M N n) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl
/--
@isnad1 id=eq.0h6v.s8.071d12914bdd from=translated src=- shape=2442afb4 vocab=c162694d
-/
@[simp] theorem neg_app (z : Cochain M N n) (X : C) : (-z).app X = -z.app X := rfl
/--
@isnad1 id=eq.0h7v.s9.71155611b177 from=translated src=- shape=fd8c481f vocab=5ad7fc59
-/
@[simp] theorem sub_app (z₁ z₂ : Cochain M N n) (X : C) :
    (z₁ - z₂).app X = z₁.app X - z₂.app X := rfl
/--
@isnad1 id=eq.0h7v.s9.01a24d530a1a from=translated src=- shape=83e2b985 vocab=ec7cf11e
-/
@[simp] theorem nsmul_app (k : ℕ) (z : Cochain M N n) (X : C) : (k • z).app X = k • z.app X :=
  rfl
/--
@isnad1 id=eq.0h7v.s9.ba66eb300038 from=translated src=- shape=ab2357a2 vocab=652c55ef
-/
@[simp] theorem zsmul_app (k : ℤ) (z : Cochain M N n) (X : C) : (k • z).app X = k • z.app X :=
  rfl

/--
@isnad1 id=eq.0h6v.s8.065c99de227a from=translated src=- shape=141c29a9 vocab=b78721e6
-/
theorem zero_apply {X : C} (x : M.obj X) : (0 : Cochain M N n).app X x = 0 := rfl
/--
@isnad1 id=eq.0h8v.s9.81704371aae4 from=translated src=- shape=0d1423ec vocab=5690bc86
-/
theorem add_apply (z₁ z₂ : Cochain M N n) {X : C} (x : M.obj X) :
    (z₁ + z₂).app X x = z₁.app X x + z₂.app X x := rfl
/--
@isnad1 id=eq.0h7v.s9.0f5769176936 from=translated src=- shape=1aecfdc3 vocab=deee07ba
-/
theorem neg_apply (z : Cochain M N n) {X : C} (x : M.obj X) : (-z).app X x = -z.app X x := rfl
/--
@isnad1 id=eq.0h8v.s9.0409549d93bb from=translated src=- shape=0d1423ec vocab=5a6e5bf1
-/
theorem sub_apply (z₁ z₂ : Cochain M N n) {X : C} (x : M.obj X) :
    (z₁ - z₂).app X x = z₁.app X x - z₂.app X x := rfl
/--
@isnad1 id=eq.0h8v.s9.8fb2ae556080 from=translated src=- shape=d5fabe6e vocab=b95427ba
-/
theorem nsmul_apply (k : ℕ) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (k • z).app X x = k • z.app X x := rfl
/--
@isnad1 id=eq.0h8v.s9.3caf93cf8453 from=translated src=- shape=689635b4 vocab=270c0073
-/
theorem zsmul_apply (k : ℤ) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (k • z).app X x = k • z.app X x := rfl

instance : AddCommGroup (Cochain M N n) :=
  app_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/--
@isnad1 id=eq.0h7v.s9.598677b7d4b7 from=translated src=- shape=341dee8b vocab=d9417d80
-/
@[simp] theorem units_smul_app (u : ℤˣ) (z : Cochain M N n) (X : C) :
    (u • z).app X = u • z.app X := rfl

/--
@isnad1 id=eq.0h8v.s9.ac91cb3e063f from=translated src=- shape=26fb97f9 vocab=3c0ab285
-/
theorem units_smul_apply (u : ℤˣ) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (u • z).app X x = u • z.app X x := rfl

end AddCommGroup

section Comp

/-- Composition of cochains: `z₂.comp z₁ h` is `z₂ ∘ z₁` (first `z₁`, then `z₂`).-/
def comp {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain N P n₂) (z₁ : Cochain M N n₁) (h : n₁ + n₂ = n₁₂) :
    Cochain M P n₁₂ where
  app X := (z₂.app X).comp (z₁.app X)
  map_mem' hx := by
    rw [← h, ← add_assoc]
    exact z₂.map_mem (z₁.map_mem hx)
  map_smul' {X Y i f} hf x := by
    change z₂.app Y (z₁.app Y _) = _ • (_ • z₂.app X (z₁.app X x))
    rw [z₁.map_smul hf, map_units_smul, z₂.map_smul hf, ← h, add_mul, koszulSign_add,
      mul_smul]

/--
@isnad1 id=eq.1h11v.s9.c1d8070789ea from=translated src=- shape=4eb7bf37 vocab=38299fd9
-/
@[simp]
theorem comp_apply {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain N P n₂) (z₁ : Cochain M N n₁)
    (h : n₁ + n₂ = n₁₂) {X : C} (x : M.obj X) : (z₂.comp z₁ h).app X x = z₂.app X (z₁.app X x) :=
  rfl

/-- Associativity of the composition of cochains.
@isnad1 id=eq.3h14v.s7.7201f16ac650 from=translated src=- shape=475d40fc vocab=a54da111
-/
theorem comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
    (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂) (z₃ : Cochain P Q n₃)
    (h₁₂ : n₁ + n₂ = n₁₂) (h₂₃ : n₂ + n₃ = n₂₃) (h₁₂₃ : n₁ + n₂ + n₃ = n₁₂₃) :
    z₃.comp (z₂.comp z₁ h₁₂) (show n₁₂ + n₃ = n₁₂₃ by rw [← h₁₂, h₁₂₃]) =
      (z₃.comp z₂ h₂₃).comp z₁ (by rw [← h₂₃, ← h₁₂₃, add_assoc]) :=
  rfl

/--
@isnad1 id=eq.1h8v.s7.3b7a98fffd31 from=translated src=- shape=bc77b499 vocab=5267a8f0
-/
@[simp]
protected theorem zero_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (h : n₁ + n₂ = n₁₂) :
    (0 : Cochain N P n₂).comp z₁ h = 0 := rfl

/--
@isnad1 id=eq.1h10v.s7.fe068b14b25a from=translated src=- shape=082e5f53 vocab=5267a8f0
-/
@[simp]
protected theorem add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ z₂' : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (z₂ + z₂').comp z₁ h = z₂.comp z₁ h + z₂'.comp z₁ h := rfl

/--
@isnad1 id=eq.1h10v.s7.9760f2d93836 from=translated src=- shape=b1aff66b vocab=0772331a
-/
@[simp]
protected theorem sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ z₂' : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (z₂ - z₂').comp z₁ h = z₂.comp z₁ h - z₂'.comp z₁ h := rfl

/--
@isnad1 id=eq.1h9v.s7.63d2e0aea82d from=translated src=- shape=60a2de40 vocab=c7bc61c6
-/
@[simp]
protected theorem neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : (-z₂).comp z₁ h = -z₂.comp z₁ h := rfl

/--
@isnad1 id=eq.1h10v.s7.c2c92008d761 from=translated src=- shape=3adaa417 vocab=ac3fc6ef
-/
@[simp]
protected theorem zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : (k • z₂).comp z₁ h = k • z₂.comp z₁ h := rfl

/--
@isnad1 id=eq.1h10v.s7.626a3e25d1d9 from=translated src=- shape=99951ed5 vocab=88420ced
-/
@[simp]
theorem units_smul_comp {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : (u • z₂).comp z₁ h = u • z₂.comp z₁ h := rfl

/--
@isnad1 id=eq.1h8v.s7.4de769ef4026 from=translated src=- shape=50a3c850 vocab=5267a8f0
-/
@[simp]
protected theorem comp_zero {n₁ n₂ n₁₂ : ℤ} (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) :
    z₂.comp (0 : Cochain M N n₁) h = 0 := ext fun X _ => map_zero (z₂.app X)

/--
@isnad1 id=eq.1h10v.s7.467ad7fb66d0 from=translated src=- shape=59ad2e6f vocab=5267a8f0
-/
@[simp]
protected theorem comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (z₁ + z₁') h = z₂.comp z₁ h + z₂.comp z₁' h :=
  ext fun X _ => map_add (z₂.app X) _ _

/--
@isnad1 id=eq.1h10v.s7.532406e21ddf from=translated src=- shape=a7a1a7b3 vocab=0772331a
-/
@[simp]
protected theorem comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (z₁ - z₁') h = z₂.comp z₁ h - z₂.comp z₁' h :=
  ext fun X _ => map_sub (z₂.app X) _ _

/--
@isnad1 id=eq.1h9v.s7.1b26fdd6a14a from=translated src=- shape=d1f3edda vocab=c7bc61c6
-/
@[simp]
protected theorem comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) : z₂.comp (-z₁) h = -z₂.comp z₁ h :=
  ext fun X _ => map_neg (z₂.app X) _

/--
@isnad1 id=eq.1h10v.s7.03fa255cf8f6 from=translated src=- shape=d5feba42 vocab=ac3fc6ef
-/
@[simp]
protected theorem comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : z₂.comp (k • z₁) h = k • z₂.comp z₁ h :=
  ext fun X _ => map_zsmul (z₂.app X) _ _

/--
@isnad1 id=eq.1h10v.s7.1cb06e1e11cf from=translated src=- shape=56a590aa vocab=88420ced
-/
@[simp]
theorem comp_units_smul {n₁ n₂ n₁₂ : ℤ} (u : ℤˣ) (z₁ : Cochain M N n₁)
    (z₂ : Cochain N P n₂) (h : n₁ + n₂ = n₁₂) : z₂.comp (u • z₁) h = u • z₂.comp z₁ h :=
  ext fun _ _ => map_units_smul z₂ _ _

variable (M) in
/-- The identity of `M` as a cochain of degree `0`.-/
def id : Cochain M M 0 where
  app X := AddMonoidHom.id _
  map_mem' {X i x} hx := by simpa using hx
  map_smul' _ x := by simp

/--
@isnad1 id=eq.0h4v.s8.26dd2f27e75a from=translated src=- shape=f09e0873 vocab=15bc69df
-/
@[simp]
theorem id_apply {X : C} (x : M.obj X) : (Cochain.id M).app X x = x := rfl

/--
@isnad1 id=eq.0h5v.s6.dee3e0322744 from=translated src=- shape=cd8a6c2a vocab=4eddcf97
-/
@[simp]
protected theorem comp_id {n : ℤ} (z : Cochain M N n) :
    z.comp (Cochain.id M) (zero_add n) = z := rfl

/--
@isnad1 id=eq.0h5v.s6.f1adf1f0c14f from=translated src=- shape=17156771 vocab=8b93e7f9
-/
@[simp]
protected theorem id_comp {n : ℤ} (z : Cochain M N n) :
    (Cochain.id N).comp z (add_zero n) = z := rfl

end Comp

section OfHom

/-- The `0`-cochain given by a family of additive maps preserving the degrees and commuting
with the action (not necessarily with the differentials).-/
def ofHoms (φ : ∀ X, M.obj X →+ N.obj X)
    (hφ : ∀ {X : C} {i : ℤ} {x : M.obj X}, x ∈ grading i → φ X x ∈ grading i)
    (hs : ∀ {X Y : C} (f : X ⟶ Y) (x : M.obj X), φ Y (f • x) = f • φ X x) :
    Cochain M N 0 where
  app := φ
  map_mem' hx := by simpa using hφ hx
  map_smul' _ x := by simp [hs]

/--
@isnad1 id=eq.2h6v.s10.0bab4b4ff8f4 from=translated src=- shape=9dbdbcc7 vocab=bbcd978c
-/
@[simp]
theorem ofHoms_apply (φ : ∀ X, M.obj X →+ N.obj X)
    (hφ : ∀ {X : C} {i : ℤ} {x : M.obj X}, x ∈ grading i → φ X x ∈ grading i)
    (hs : ∀ {X Y : C} (f : X ⟶ Y) (x : M.obj X), φ Y (f • x) = f • φ X x) {X : C}
    (x : M.obj X) : (ofHoms φ hφ hs).app X x = φ X x := rfl

/-- The `0`-cochain attached to a morphism of dg modules.-/
def ofHom (φ : M ⟶ N) : Cochain M N 0 := ofHoms φ.app φ.map_mem φ.map_smul

/--
@isnad1 id=eq.0h6v.s9.b2aa32277d3b from=translated src=- shape=bf446b86 vocab=ddd6176b
-/
@[simp]
theorem ofHom_apply (φ : M ⟶ N) {X : C} (x : M.obj X) : (ofHom φ).app X x = φ.app X x := rfl

variable (M N) in
/--
@isnad1 id=eq.0h3v.s7.831f6e3b1897 from=translated src=- shape=0bfa0850 vocab=de8ddab4
-/
@[simp]
theorem ofHom_zero : ofHom (0 : M ⟶ N) = 0 := rfl

/--
@isnad1 id=eq.0h5v.s8.5f81650ad606 from=translated src=- shape=61b1e1d0 vocab=20c0b833
-/
@[simp]
theorem ofHom_add (φ₁ φ₂ : M ⟶ N) : ofHom (φ₁ + φ₂) = ofHom φ₁ + ofHom φ₂ := rfl

/--
@isnad1 id=eq.0h5v.s8.cafad5fb1fba from=translated src=- shape=61b1e1d0 vocab=d1d90cf7
-/
@[simp]
theorem ofHom_sub (φ₁ φ₂ : M ⟶ N) : ofHom (φ₁ - φ₂) = ofHom φ₁ - ofHom φ₂ := rfl

/--
@isnad1 id=eq.0h4v.s7.1a038c044415 from=translated src=- shape=e899359d vocab=970fb037
-/
@[simp]
theorem ofHom_neg (φ : M ⟶ N) : ofHom (-φ) = -ofHom φ := rfl

/--
@isnad1 id=eq.0h5v.s7.7936072b4337 from=translated src=- shape=3f31b5e7 vocab=ac922d86
-/
theorem ofHom_zsmul (k : ℤ) (φ : M ⟶ N) : ofHom (k • φ) = k • ofHom φ := rfl

/--
@isnad1 id=eq.0h2v.s6.b9b13a64c861 from=translated src=- shape=b9ee7683 vocab=69d7ec7e
-/
@[simp]
theorem ofHom_id : ofHom (𝟙 M) = Cochain.id M := rfl

/--
@isnad1 id=eq.0h6v.s7.44fd16f24c67 from=translated src=- shape=3d8de2a9 vocab=4d5e824a
-/
@[simp]
theorem ofHom_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    ofHom (φ ≫ ψ) = (ofHom ψ).comp (ofHom φ) (zero_add 0) := rfl

/--
@isnad1 id=injectiv.0h3v.s6.5b59d69782e5 from=translated src=- shape=31e8031b vocab=1553299d
-/
theorem ofHom_injective : Function.Injective (ofHom : (M ⟶ N) → Cochain M N 0) :=
  fun _ _ h => hom_ext fun X x => congrArg (fun z : Cochain M N 0 => z.app X x) h

end OfHom

end Cochain

section Differential

variable {M N P : CatModule.{w} C}

open DG.CatModule.Cochain

/-- The differential of the Hom complex: for a cochain `z` of degree `n`, `δ n m z` is the
cochain `d ∘ z - (-1)^n • z ∘ d` (objectwise) of degree `m` if `n + 1 = m`, and `0` otherwise
(the convention of Mathlib's `CochainComplex.HomComplex.δ`). It commutes with the action of `C`
up to the Koszul sign by the Leibniz rules of `M` and `N`.-/
def δ (n m : ℤ) (z : Cochain M N n) : Cochain M N m :=
  if hnm : n + 1 = m then
    { app := fun X =>
        { toFun := fun x => d (z.app X x) - koszulSign n • z.app X (d x)
          map_zero' := by simp
          map_add' := fun x y => by
            simp only [map_add, _root_.smul_add]
            abel }
      map_mem' := fun {X i x} hx => by
        subst hnm
        refine sub_mem ?_ (units_smul_mem_grading _ ?_)
        · have := d_mem (z.map_mem hx)
          rwa [add_assoc] at this
        · have := z.map_mem (d_mem hx)
          rwa [add_right_comm, add_assoc] at this
      map_smul' := fun {X Y i f} hf x => by
        subst hnm
        have hdf := d_mem hf
        change d (z.app Y (f • x)) - koszulSign n • z.app Y (d (f • x)) =
          _ • (f • (d (z.app X x) - koszulSign n • z.app X (d x)))
        rw [z.map_smul hf, d_units_smul, d_smul hf, d_smul hf, map_add, map_units_smul,
          z.map_smul hf, z.map_smul hdf]
        rcases Int.units_eq_one_or (koszulSign n) with h₁ | h₁ <;>
        rcases Int.units_eq_one_or (koszulSign i) with h₂ | h₂ <;>
        rcases Int.units_eq_one_or (koszulSign (n * i)) with h₃ | h₃ <;>
        simp [add_mul, mul_add, koszulSign_add, h₁, h₂, h₃, smul_sub, smul_add] <;> abel }
  else 0

variable (n m : ℤ)

/--
@isnad1 id=eq.1h8v.s10.24e3739f48c3 from=translated src=- shape=ca8aaa27 vocab=a8dc35f7
-/
theorem δ_apply (hnm : n + 1 = m) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (δ n m z).app X x = d (z.app X x) - koszulSign n • z.app X (d x) := by
  unfold δ
  rw [dite_eq_left hnm]
  rfl

/-- The differential in the form used by Mathlib's `CochainComplex.HomComplex.δ`:
`δ z = d ∘ z + (-1)^m • z ∘ d`.
@isnad1 id=eq.1h8v.s10.0898dcfec67f from=translated src=- shape=c7c993ea vocab=2eb2b95f
-/
theorem δ_apply' (hnm : n + 1 = m) (z : Cochain M N n) {X : C} (x : M.obj X) :
    (δ n m z).app X x = d (z.app X x) + koszulSign m • z.app X (d x) := by
  subst hnm
  rw [δ_apply n _ rfl, koszulSign, koszulSign, Int.negOnePow_succ, Units.neg_smul,
    sub_eq_add_neg]

/--
@isnad1 id=eq.1h6v.s6.5d244dc9a9b9 from=translated src=- shape=9ae3edf5 vocab=25c628e7
-/
theorem δ_shape (hnm : ¬ n + 1 = m) (z : Cochain M N n) : δ n m z = 0 := by
  unfold δ
  rw [dite_eq_right hnm]

variable (M N) in
/-- The differential of the Hom complex, as an additive map.-/
@[simps]
def δ_hom : Cochain M N n →+ Cochain M N m where
  toFun := δ n m
  map_zero' := by
    by_cases h : n + 1 = m
    · ext X x
      simp [δ_apply n m h]
    · exact δ_shape n m h _
  map_add' z₁ z₂ := by
    by_cases h : n + 1 = m
    · ext X x
      simp only [δ_apply n m h, Cochain.add_apply, d_add, _root_.smul_add]
      abel
    · simp only [δ_shape n m h, add_zero]

/--
@isnad1 id=eq.0h7v.s7.a64192874ac5 from=translated src=- shape=397b9e44 vocab=25c628e7
-/
@[simp] theorem δ_add (z₁ z₂ : Cochain M N n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
  (δ_hom M N n m).map_add z₁ z₂

/--
@isnad1 id=eq.0h7v.s7.f2d143b048a7 from=translated src=- shape=397b9e44 vocab=93dff53d
-/
@[simp] theorem δ_sub (z₁ z₂ : Cochain M N n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
  (δ_hom M N n m).map_sub z₁ z₂

/--
@isnad1 id=eq.0h5v.s6.4459d534e38b from=translated src=- shape=d1ac0544 vocab=88a0244b
-/
@[simp] theorem δ_zero : δ n m (0 : Cochain M N n) = 0 := (δ_hom M N n m).map_zero

/--
@isnad1 id=eq.0h6v.s6.94c3780936fa from=translated src=- shape=da409745 vocab=8551938d
-/
@[simp] theorem δ_neg (z : Cochain M N n) : δ n m (-z) = -δ n m z :=
  (δ_hom M N n m).map_neg z

/--
@isnad1 id=eq.0h7v.s7.6dc89ec9b4fc from=translated src=- shape=647b47bb vocab=43c19aed
-/
@[simp] theorem δ_zsmul (k : ℤ) (z : Cochain M N n) : δ n m (k • z) = k • δ n m z :=
  (δ_hom M N n m).map_zsmul k z

/--
@isnad1 id=eq.0h7v.s7.7e260cabaa49 from=translated src=- shape=e5f488ec vocab=ebafd370
-/
@[simp] theorem δ_units_smul (u : ℤˣ) (z : Cochain M N n) : δ n m (u • z) = u • δ n m z := by
  rw [Units.smul_def, Units.smul_def, δ_zsmul]

/-- The differential of the Hom complex squares to zero.
@isnad1 id=eq.0h7v.s6.cd198943d9da from=translated src=- shape=323fed26 vocab=88a0244b
-/
theorem δ_δ (n₀ n₁ n₂ : ℤ) (z : Cochain M N n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂; swap
  · rw [δ_shape _ _ h₁₂]
  by_cases h₀₁ : n₀ + 1 = n₁; swap
  · rw [δ_shape _ _ h₀₁, δ_zero]
  ext X x
  rw [δ_apply _ _ h₁₂, δ_apply _ _ h₀₁, δ_apply _ _ h₀₁, Cochain.zero_apply, ← h₀₁]
  simp only [koszulSign, Int.negOnePow_succ, d_sub, d_units_smul, d_d, map_zero, _root_.smul_zero,
    sub_zero, zero_sub, Units.neg_smul, sub_neg_eq_add, neg_add_cancel]

/-- The Leibniz rule for the composition of cochains: for `z₁` of degree `n₁` and `z₂` of
degree `n₂`, `δ (z₂ ∘ z₁) = δ z₂ ∘ z₁ + (-1)^{n₂} • z₂ ∘ δ z₁`.
@isnad1 id=eq.4h12v.s8.d0d8d7cdb790 from=translated src=- shape=c16229e3 vocab=e61958ef
-/
theorem δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P n₂)
    (h : n₁ + n₂ = n₁₂) (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂ + 1 = m₁₂) (h₁ : n₁ + 1 = m₁)
    (h₂ : n₂ + 1 = m₂) :
    δ n₁₂ m₁₂ (z₂.comp z₁ h) =
      (δ n₂ m₂ z₂).comp z₁ (by rw [← h₁₂, ← h₂, ← h, add_assoc]) +
        koszulSign n₂ • z₂.comp (δ n₁ m₁ z₁)
          (by rw [← h₁₂, ← h₁, ← h, add_assoc, add_comm 1, add_assoc]) := by
  ext X x
  simp only [Cochain.add_apply, units_smul_apply, Cochain.comp_apply, δ_apply _ _ h₁₂, δ_apply _ _ h₁,
    δ_apply _ _ h₂, map_sub, map_units_smul, _root_.smul_sub, smul_smul, ← h, koszulSign_add,
    mul_comm (koszulSign n₁)]
  abel

/--
@isnad1 id=eq.1h8v.s8.57ff8245006d from=translated src=- shape=fa28eafc vocab=1487f9c7
-/
theorem δ_zero_cochain_comp {n₂ : ℤ} (z₁ : Cochain M N 0) (z₂ : Cochain N P n₂)
    (m₂ : ℤ) (h₂ : n₂ + 1 = m₂) :
    δ n₂ m₂ (z₂.comp z₁ (zero_add n₂)) =
      (δ n₂ m₂ z₂).comp z₁ (zero_add m₂) +
        koszulSign n₂ • z₂.comp (δ 0 1 z₁) (by rw [add_comm, h₂]) :=
  δ_comp z₁ z₂ (zero_add n₂) 1 m₂ m₂ h₂ (zero_add 1) h₂

/--
@isnad1 id=eq.1h8v.s7.510f5a9499bc from=translated src=- shape=0596d1ad vocab=715158be
-/
theorem δ_comp_zero_cochain {n₁ : ℤ} (z₁ : Cochain M N n₁) (z₂ : Cochain N P 0)
    (m₁ : ℤ) (h₁ : n₁ + 1 = m₁) :
    δ n₁ m₁ (z₂.comp z₁ (add_zero n₁)) =
      (δ 0 1 z₂).comp z₁ h₁ + z₂.comp (δ n₁ m₁ z₁) (add_zero m₁) := by
  simp only [δ_comp z₁ z₂ (add_zero n₁) m₁ 1 m₁ h₁ h₁ (zero_add 1), koszulSign,
    Int.negOnePow_zero, one_smul]

/--
@isnad1 id=eq.0h6v.s10.31e331783896 from=translated src=- shape=57dc30d2 vocab=80a4f71c
-/
@[simp]
theorem δ_zero_cochain_apply (z : Cochain M N 0) {X : C} (x : M.obj X) :
    (δ 0 1 z).app X x = d (z.app X x) - z.app X (d x) := by
  rw [δ_apply 0 1 (zero_add 1), koszulSign, Int.negOnePow_zero, one_smul]

/--
@isnad1 id=eq.0h5v.s6.68ae22c6e6a8 from=translated src=- shape=652a6f3e vocab=37f376bd
-/
@[simp]
theorem δ_ofHom {p : ℤ} (φ : M ⟶ N) : δ 0 p (Cochain.ofHom φ) = 0 := by
  by_cases h : 0 + 1 = p
  · ext X x
    rw [δ_apply 0 p h, Cochain.zero_apply, ofHom_apply, ofHom_apply, Hom.map_d, koszulSign,
      Int.negOnePow_zero, one_smul, sub_self]
  · exact δ_shape _ _ h _

end Differential

section Cocycle

variable (M N : CatModule.{w} C) {P : CatModule.{w} C}

/-- The subgroup of cocycles in `Cochain M N n`: the kernel of `δ n (n + 1)`.-/
def cocycle (n : ℤ) : AddSubgroup (Cochain M N n) :=
  (δ_hom M N n (n + 1)).ker

/-- The type of `n`-cocycles from `M` to `N`.-/
abbrev Cocycle (n : ℤ) : Type _ := cocycle M N n

namespace Cocycle

variable {M N}

/--
@isnad1 id=iff.1h6v.s7.4d8291692afb from=translated src=- shape=d84adaa7 vocab=b36cadf5
-/
theorem mem_iff {n : ℤ} (m : ℤ) (hnm : n + 1 = m) (z : Cochain M N n) :
    z ∈ cocycle M N n ↔ δ n m z = 0 := by
  subst hnm; rfl

/--
@isnad1 id=eq.1h6v.s8.66bbcb1331d9 from=translated src=- shape=894b67eb vocab=2634c31b
-/
@[ext]
theorem ext {n : ℤ} {z₁ z₂ : Cocycle M N n} (h : (z₁ : Cochain M N n) = z₂) : z₁ = z₂ :=
  Subtype.ext h

/-- Constructor for `Cocycle M N n`, from `z : Cochain M N n`, an integer `m` with
`n + 1 = m`, and the relation `δ n m z = 0`.-/
@[simps]
def mk {n : ℤ} (z : Cochain M N n) (m : ℤ) (hnm : n + 1 = m) (h : δ n m z = 0) :
    Cocycle M N n :=
  ⟨z, (mem_iff m hnm z).2 h⟩

/--
@isnad1 id=eq.0h6v.s7.7aad1fc15289 from=translated src=- shape=3efb13c1 vocab=c23e5bc1
-/
@[simp]
theorem δ_eq_zero {n : ℤ} (z : Cocycle M N n) (m : ℤ) : δ n m (z : Cochain M N n) = 0 := by
  by_cases h : n + 1 = m
  · exact (mem_iff m h _).1 z.2
  · exact δ_shape n m h _

/-- The `0`-cocycle associated to a morphism of dg modules.-/
@[simps!]
def ofHom (φ : M ⟶ N) : Cocycle M N 0 :=
  mk (Cochain.ofHom φ) 1 (zero_add 1) (δ_ofHom φ)

/-- A `0`-cocycle commutes with the action of all (not only homogeneous) morphisms.
@isnad1 id=eq.0h8v.s9.0ca4d6d2be96 from=translated src=- shape=5e92a10e vocab=0ae841f9
-/
theorem map_smul (z : Cocycle M N 0) {X Y : C} (f : X ⟶ Y) (x : M.obj X) :
    (z : Cochain M N 0).app Y (f • x) = f • (z : Cochain M N 0).app X x := by
  induction f using DG.induction_on with
  | h_zero => simp
  | h_homogeneous f =>
    rw [(z : Cochain M N 0).map_smul f.2, zero_mul, koszulSign, Int.negOnePow_zero, one_smul]
  | h_add f f' hf hf' => rw [add_smul, map_add, hf, hf', add_smul]

/--
@isnad1 id=eq.0h6v.s10.59ebd0b1d2d6 from=translated src=- shape=5a8088fe vocab=ba369abb
-/
theorem map_d (z : Cocycle M N 0) {X : C} (x : M.obj X) :
    (z : Cochain M N 0).app X (d x) = d ((z : Cochain M N 0).app X x) := by
  have h := congrArg (fun c : Cochain M N 1 => c.app X x) (z.δ_eq_zero 1)
  simp only [δ_zero_cochain_apply, Cochain.zero_apply, sub_eq_zero] at h
  exact h.symm

/-- The morphism of dg modules associated to a `0`-cocycle.-/
def homOf (z : Cocycle M N 0) : M ⟶ N where
  app := (z : Cochain M N 0).app
  map_mem' hx := by simpa using (z : Cochain M N 0).map_mem hx
  map_d' := z.map_d
  map_smul' := z.map_smul

/--
@isnad1 id=eq.0h6v.s9.7aa097fed6a3 from=translated src=- shape=577a862b vocab=02143cab
-/
@[simp]
theorem homOf_app (z : Cocycle M N 0) {X : C} (x : M.obj X) :
    (homOf z).app X x = (z : Cochain M N 0).app X x := rfl

/--
@isnad1 id=eq.0h4v.s6.ac9ebb78468c from=translated src=- shape=8e15b3eb vocab=73a1e4aa
-/
@[simp]
theorem homOf_ofHom_eq_self (φ : M ⟶ N) : homOf (ofHom φ) = φ := rfl

/--
@isnad1 id=eq.0h4v.s6.39f660a98d3b from=translated src=- shape=d86c2c13 vocab=e780d38d
-/
@[simp]
theorem ofHom_homOf_eq_self (z : Cocycle M N 0) : ofHom (homOf z) = z := rfl

/--
@isnad1 id=eq.0h4v.s8.ad2fc379ddef from=translated src=- shape=cebf1872 vocab=e72e0f98
-/
@[simp]
theorem cochain_ofHom_homOf_eq_coe (z : Cocycle M N 0) :
    Cochain.ofHom (homOf z) = (z : Cochain M N 0) := rfl

variable (M N)

/-- The additive equivalence between morphisms of dg modules `M ⟶ N` and `0`-cocycles of the
Hom complex.-/
@[simps]
def equivHom : (M ⟶ N) ≃+ Cocycle M N 0 where
  toFun := ofHom
  invFun := homOf
  left_inv := homOf_ofHom_eq_self
  right_inv := ofHom_homOf_eq_self
  map_add' _ _ := rfl

end Cocycle

variable {M N}

/--
@isnad1 id=eq.0h8v.s8.78d31215a8a9 from=translated src=- shape=a51a582e vocab=fbbbd769
-/
@[simp]
theorem δ_comp_zero_cocycle {n : ℤ} (z₁ : Cochain M N n) (z₂ : Cocycle N P 0) (m : ℤ) :
    δ n m ((z₂ : Cochain N P 0).comp z₁ (add_zero n)) =
      (z₂ : Cochain N P 0).comp (δ n m z₁) (add_zero m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_comp_zero_cochain _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

/--
@isnad1 id=eq.0h8v.s7.9a4571ab9f81 from=translated src=- shape=5d694bc0 vocab=a00375ef
-/
@[simp]
theorem δ_comp_ofHom {n : ℤ} (z₁ : Cochain M N n) (f : N ⟶ P) (m : ℤ) :
    δ n m ((Cochain.ofHom f).comp z₁ (add_zero n)) =
      (Cochain.ofHom f).comp (δ n m z₁) (add_zero m) :=
  δ_comp_zero_cocycle z₁ (Cocycle.ofHom f) m

/--
@isnad1 id=eq.0h8v.s8.dabff67e1c61 from=translated src=- shape=afeb31ce vocab=05ac6a8d
-/
@[simp]
theorem δ_zero_cocycle_comp {n : ℤ} (z₁ : Cocycle M N 0) (z₂ : Cochain N P n) (m : ℤ) :
    δ n m (z₂.comp (z₁ : Cochain M N 0) (zero_add n)) =
      (δ n m z₂).comp (z₁ : Cochain M N 0) (zero_add m) := by
  by_cases hnm : n + 1 = m
  · simp [δ_zero_cochain_comp _ _ _ hnm]
  · simp [δ_shape _ _ hnm]

/--
@isnad1 id=eq.0h8v.s7.2dcf306aae8e from=translated src=- shape=cdc09d81 vocab=d92522ac
-/
@[simp]
theorem δ_ofHom_comp {n : ℤ} (f : M ⟶ N) (z : Cochain N P n) (m : ℤ) :
    δ n m (z.comp (Cochain.ofHom f) (zero_add n)) =
      (δ n m z).comp (Cochain.ofHom f) (zero_add m) :=
  δ_zero_cocycle_comp (Cocycle.ofHom f) z m

end Cocycle

/-! ### The Hom complex -/

section HOM

variable (M N : CatModule.{w} C)

/-- The Hom complex `HOM_C(M, N) = ⨁ n, Cochain M N n` of two dg modules over `C`. Its grading
(`DG.summand`) and differential (induced by `DG.CatModule.δ`) are given by the instance
`DG.CatModule.HOM.instDGAddCommGroup`.-/
abbrev HOM : Type _ := ⨁ n : ℤ, Cochain M N n

namespace HOM

variable {M N}

/--
@isnad1 id=eq.2h7v.s10.08ad8c9c5618 from=translated src=- shape=b3394da1 vocab=7281ee89
-/
theorem of_congr {i j : ℤ} (h : i = j) {f : Cochain M N i} {g : Cochain M N j}
    (hfg : ∀ X x, f.app X x = g.app X x) :
    (DirectSum.of (fun n => Cochain M N n) i f : HOM M N) = DirectSum.of _ j g := by
  subst h
  rw [Cochain.ext hfg]

/--
@isnad1 id=eq.0h6v.s10.3546a0ce7209 from=translated src=- shape=9d850beb vocab=d8b7ca7b
-/
theorem of_units_smul (i : ℤ) (u : ℤˣ) (f : Cochain M N i) :
    (DirectSum.of (fun n => Cochain M N n) i (u • f) : HOM M N) =
      u • DirectSum.of (fun n => Cochain M N n) i f := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

variable (M N)

/-- The differential of the Hom complex, `δ n (n + 1)` on the degree-`n` summand.-/
def dHom : HOM M N →+ HOM M N :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => Cochain M N n) (n + 1)).comp (δ_hom M N n (n + 1))

variable {M N}

/--
@isnad1 id=eq.0h5v.s10.7d5d5f0c538c from=translated src=- shape=2e4d6f98 vocab=3ec7c6e7
-/
theorem dHom_of (n : ℤ) (z : Cochain M N n) :
    dHom M N (DirectSum.of _ n z) = DirectSum.of _ (n + 1) (δ n (n + 1) z) := by
  simp [dHom]

variable (M N)

/-- The Hom complex is a dg abelian group: it is graded by its summands and its differential
is `δ`.-/
noncomputable instance instDGAddCommGroup : DGAddCommGroup (HOM M N) where
  grading := summand fun n => Cochain M N n
  d := dHom M N
  d_mem' := by
    rintro n _ ⟨z, rfl⟩
    rw [dHom_of]
    exact of_mem_summand _ _
  d_d' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n z => simp [dHom_of, δ_δ]
    | add x y hx hy => simp [hx, hy]

variable {M N}

/--
@isnad1 id=eq.0h4v.s7.03d7fa3edbd4 from=translated src=- shape=a7b0d0da vocab=171db5c2
-/
theorem grading_eq (n : ℤ) :
    grading (M := HOM M N) n = summand (fun n => Cochain M N n) n := rfl

/--
@isnad1 id=eq.0h5v.s11.f91fcaedc0d6 from=translated src=- shape=a16701bc vocab=9693c609
-/
theorem d_of (n : ℤ) (z : Cochain M N n) :
    d (DirectSum.of (fun n => Cochain M N n) n z : HOM M N) =
      DirectSum.of _ (n + 1) (δ n (n + 1) z) :=
  dHom_of n z

end HOM

end HOM

end CatModule

end DG

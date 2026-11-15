import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

def sres {U V : X.affineOpens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom

def sresTop (U : X.affineOpens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom

/--
@isnad1 id=eq.1h4v.s12.686ad04bc9cf from=translated src=- shape=28bafc51 vocab=599a9fa9
-/
lemma sres_apply {U V : X.affineOpens} (h : V ≤ U) (s : Γ(X, U)) :
    sres h s = (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom s := rfl

/--
@isnad1 id=eq.0h3v.s13.d457cb8edf09 from=translated src=- shape=fac3e57a vocab=f0e85bbe
-/
lemma sresTop_apply (U : X.affineOpens) (s : Γ(X, ⊤)) :
    sresTop U s = (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op).hom s := rfl

/--
@isnad1 id=eq.1h4v.s13.7e8d4ac1d4be from=translated src=- shape=aaec0909 vocab=29a7da1d
-/
@[simp] lemma sres_sresTop {U V : X.affineOpens} (h : V ≤ U) (s : Γ(X, ⊤)) :
    sres h (sresTop U s) = sresTop V s := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← X.presheaf.map_comp]; rfl

/--
@isnad1 id=eq.2h5v.s13.1f7143c8748a from=translated src=- shape=64af7857 vocab=fb4b8b99
-/
@[simp] lemma sres_sres {U V W : X.affineOpens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    sres h (sres h' s) = sres (h.trans h') s := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← X.presheaf.map_comp]; rfl

def resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U) :
    I.ideal V :=
  ⟨sres h (x : Γ(X, U)), I.ideal_le_comap_ideal h x.2⟩

/--
@isnad1 id=eq.1h5v.s13.92d26c805ea7 from=translated src=- shape=fdc084c4 vocab=32f36053
-/
@[simp] lemma coe_resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U)
    (x : I.ideal U) : (I.resLE h x : Γ(X, V)) = sres h (x : Γ(X, U)) := rfl

structure IdealHom (I J : X.IdealSheafData) : Type u where

  app : ∀ U : X.affineOpens, I.ideal U →ₗ[Γ(X, U)] J.ideal U

  coe_app_resLE : ∀ {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U),
    ((app V (I.resLE h x) : J.ideal V) : Γ(X, V)) = sres h ((app U x : J.ideal U) : Γ(X, U))

namespace IdealHom

variable {I J K : X.IdealSheafData}

/--
@isnad1 id=eq.1h5v.s14.a6692397ccd2 from=translated src=- shape=dc97cabf vocab=0199aee1
-/
@[ext]
lemma ext {φ ψ : IdealHom I J} (h : φ.app = ψ.app) : φ = ψ := by
  cases φ; cases ψ; congr

instance : Zero (IdealHom I J) := ⟨⟨fun _ => 0, fun h x => by simp⟩⟩
instance : Add (IdealHom I J) :=
  ⟨fun φ ψ => ⟨fun U => φ.app U + ψ.app U, fun h x => by
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, φ.coe_app_resLE h x,
      ψ.coe_app_resLE h x]⟩⟩
instance : Neg (IdealHom I J) :=
  ⟨fun φ => ⟨fun U => -φ.app U, fun h x => by
    simp only [LinearMap.neg_apply, Submodule.coe_neg, map_neg, φ.coe_app_resLE h x]⟩⟩
instance : Sub (IdealHom I J) :=
  ⟨fun φ ψ => ⟨fun U => φ.app U - ψ.app U, fun h x => by
    simp only [LinearMap.sub_apply, Submodule.coe_sub, map_sub, φ.coe_app_resLE h x,
      ψ.coe_app_resLE h x]⟩⟩
instance : SMul ℕ (IdealHom I J) :=
  ⟨fun n φ => ⟨fun U => n • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_nsmul,
      φ.coe_app_resLE h x]⟩⟩
instance : SMul ℤ (IdealHom I J) :=
  ⟨fun n φ => ⟨fun U => n • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, Submodule.coe_smul_of_tower, map_zsmul,
      φ.coe_app_resLE h x]⟩⟩

/--
@isnad1 id=eq.0h4v.s16.bb3b318fea5c from=translated src=- shape=555f16bb vocab=0199aee1
-/
@[simp] lemma zero_app (U : X.affineOpens) : (0 : IdealHom I J).app U = 0 := rfl
/--
@isnad1 id=eq.0h6v.s16.c7454dfe098f from=translated src=- shape=216f0391 vocab=9156df45
-/
@[simp] lemma add_app (φ ψ : IdealHom I J) (U : X.affineOpens) :
    (φ + ψ).app U = φ.app U + ψ.app U := rfl
/--
@isnad1 id=eq.0h5v.s15.84715e1975e2 from=translated src=- shape=1fc15575 vocab=b2840bb9
-/
@[simp] lemma neg_app (φ : IdealHom I J) (U : X.affineOpens) : (-φ).app U = -φ.app U := rfl
/--
@isnad1 id=eq.0h6v.s16.a3772e20227b from=translated src=- shape=216f0391 vocab=4db3e4f9
-/
@[simp] lemma sub_app (φ ψ : IdealHom I J) (U : X.affineOpens) :
    (φ - ψ).app U = φ.app U - ψ.app U := rfl
/--
@isnad1 id=eq.0h6v.s16.6cef14ef8152 from=translated src=- shape=29bd6a04 vocab=d83f95a6
-/
@[simp] lemma nsmul_app (n : ℕ) (φ : IdealHom I J) (U : X.affineOpens) :
    (n • φ).app U = n • φ.app U := rfl
/--
@isnad1 id=eq.0h6v.s17.f3d2ba092efb from=translated src=- shape=29bd6a04 vocab=53e298a9
-/
@[simp] lemma zsmul_app (n : ℤ) (φ : IdealHom I J) (U : X.affineOpens) :
    (n • φ).app U = n • φ.app U := rfl

instance : AddCommGroup (IdealHom I J) :=
  Function.Injective.addCommGroup (fun φ : IdealHom I J => φ.app)
    (fun _ _ h => ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : SMul Γ(X, ⊤) (IdealHom I J) :=
  ⟨fun s φ => ⟨fun U => sresTop U s • φ.app U, fun h x => by
    simp only [LinearMap.smul_apply, SetLike.val_smul, smul_eq_mul, map_mul,
      φ.coe_app_resLE h x, sres_sresTop]⟩⟩

/--
@isnad1 id=eq.0h6v.s16.a6e572917634 from=translated src=- shape=a4c3ac98 vocab=b9e3a04e
-/
@[simp] lemma smul_app (s : Γ(X, ⊤)) (φ : IdealHom I J) (U : X.affineOpens) :
    (s • φ).app U = sresTop U s • φ.app U := rfl

instance : Module Γ(X, ⊤) (IdealHom I J) where
  one_smul φ := by ext U x; simp
  mul_smul r s φ := by ext U x; simp [mul_smul]
  smul_zero r := by ext U x; simp
  smul_add r φ ψ := by ext U x; simp
  add_smul r s φ := by ext U x; simp [add_smul]
  zero_smul φ := by ext U x; simp

def ofLE (h : I ≤ J) : IdealHom I J where
  app U := Submodule.inclusion (le_def.mp h U)
  coe_app_resLE _ _ := rfl

/--
@isnad1 id=eq.1h5v.s15.f2ae5bf3e4ee from=translated src=- shape=6bf2f900 vocab=cfb86409
-/
@[simp] lemma coe_ofLE_app (h : I ≤ J) (U : X.affineOpens) (x : I.ideal U) :
    ((ofLE h).app U x : Γ(X, U)) = x := rfl

protected def id (I : X.IdealSheafData) : IdealHom I I := ofLE le_rfl

/--
@isnad1 id=eq.0h4v.s15.3ce9feab04ac from=translated src=- shape=9300c665 vocab=db9c4b1f
-/
@[simp] lemma id_app (I : X.IdealSheafData) (U : X.affineOpens) (x : I.ideal U) :
    (IdealHom.id I).app U x = x := rfl

def comp (ψ : IdealHom J K) (φ : IdealHom I J) : IdealHom I K where
  app U := ψ.app U ∘ₗ φ.app U
  coe_app_resLE := by
    intro U V h x
    have h₁ : φ.app V (I.resLE h x) = J.resLE h (φ.app U x) := Subtype.ext (φ.coe_app_resLE h x)
    simp only [LinearMap.coe_comp, Function.comp_apply, h₁, ψ.coe_app_resLE h]

/--
@isnad1 id=eq.0h8v.s17.59f5c44edaff from=translated src=- shape=46389f8e vocab=cdf9f268
-/
@[simp] lemma comp_app (ψ : IdealHom J K) (φ : IdealHom I J) (U : X.affineOpens)
    (x : I.ideal U) : (ψ.comp φ).app U x = ψ.app U (φ.app U x) := rfl

def mulRight (I J : X.IdealSheafData) (s : Γ(X, ⊤))
    (hs : ∀ U : X.affineOpens, sresTop U s ∈ J.ideal U) : IdealHom I (I * J) where
  app U :=
    { toFun := fun x => ⟨x * sresTop U s, by rw [ideal_mul]; exact Ideal.mul_mem_mul x.2 (hs U)⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (mul_assoc _ _ _) }
  coe_app_resLE := by
    intro U V h x
    show sres h (x : Γ(X, U)) * sresTop V s = sres h ((x : Γ(X, U)) * sresTop U s)
    rw [map_mul, sres_sresTop]

/--
@isnad1 id=eq.1h6v.s16.29a64133f2b0 from=translated src=- shape=40fa9d66 vocab=9da8e1c7
-/
@[simp] lemma coe_mulRight_app (I J : X.IdealSheafData) (s : Γ(X, ⊤))
    (hs : ∀ U : X.affineOpens, sresTop U s ∈ J.ideal U) (U : X.affineOpens) (x : I.ideal U) :
    ((mulRight I J s hs).app U x : Γ(X, U)) = x * sresTop U s :=
  rfl

end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme

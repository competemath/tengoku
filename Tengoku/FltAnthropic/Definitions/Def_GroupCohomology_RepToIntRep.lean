import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type} [CommRing k] [Group G]

def toIntRepρ (M : Rep k G) : Representation ℤ G M.V where
  toFun g := (M.ρ g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp

/--
@isnad1 id=eq.0h5v.s11.2292aae1c97c from=translated src=- shape=52fe2659 vocab=318abe9c
-/
@[simp] lemma toIntRepρ_apply_apply (M : Rep k G) (g : G) (x : M.V) : M.toIntRepρ g x = M.ρ g x := rfl

def toIntRep (M : Rep k G) : Rep ℤ G := Rep.of M.toIntRepρ

/--
@isnad1 id=eq.0h3v.s5.fa1e7d8e9243 from=translated src=- shape=58b6ca6e vocab=b69ffc6a
-/
lemma coe_toIntRep (M : Rep k G) : (M.toIntRep : Type) = M.V := rfl

/--
@isnad1 id=eq.0h3v.s6.fd762ff39d7d from=translated src=- shape=1b8806e0 vocab=77b606ec
-/
@[simp] lemma toIntRep_ρ (M : Rep k G) : M.toIntRep.ρ = M.toIntRepρ := rfl

def toIntRepMap {M N : Rep k G} (φ : M ⟶ N) : M.toIntRep ⟶ N.toIntRep :=
  Rep.ofHom ⟨φ.hom.toAddMonoidHom.toIntLinearMap, fun g => LinearMap.ext fun x => Rep.hom_comm_apply φ g x⟩

/--
@isnad1 id=eq.0h6v.s9.d057c69fef78 from=translated src=- shape=9af02a0a vocab=f1f00941
-/
@[simp] lemma toIntRepMap_hom_apply {M N : Rep k G} (φ : M ⟶ N) (x : M.V) : (toIntRepMap φ).hom x = φ.hom x := rfl

/--
@isnad1 id=eq.0h3v.s7.af0bbe07a9bf from=translated src=- shape=0cda7da6 vocab=f34dd78b
-/
lemma toIntRepMap_id (M : Rep k G) : toIntRepMap (𝟙 M) = 𝟙 M.toIntRep := by ext x; rfl

/--
@isnad1 id=eq.0h7v.s8.893fa19b9dba from=translated src=- shape=05fed237 vocab=e9954bbd
-/
lemma toIntRepMap_comp {M N P : Rep k G} (φ : M ⟶ N) (ψ : N ⟶ P) :
    toIntRepMap (φ ≫ ψ) = toIntRepMap φ ≫ toIntRepMap ψ := by ext x; rfl

variable (k G) in

def toIntRepFunctor : Rep k G ⥤ Rep ℤ G where
  obj M := M.toIntRep
  map φ := toIntRepMap φ
  map_id M := toIntRepMap_id M
  map_comp φ ψ := toIntRepMap_comp φ ψ

end Rep

end

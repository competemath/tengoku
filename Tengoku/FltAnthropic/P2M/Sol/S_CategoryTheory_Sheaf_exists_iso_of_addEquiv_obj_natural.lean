import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

/--
@isnad1 id=ex.1h5v.s12.f416e8cdf9f7 from=translated src=- shape=56932003 vocab=b85e851f
-/
theorem solution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F G : Sheaf J Ab.{w}) (e : ∀ U : Cᵒᵖ, F.obj.obj U ≃+ G.obj.obj U)
    (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (s : F.obj.obj U), e V (F.obj.map k s) = G.obj.map k (e U s)) :
    ∃ φ : F ≅ G, ∀ (U : Cᵒᵖ) (s : F.obj.obj U), φ.hom.hom.app U s = e U s := by
  let α : F.obj ≅ G.obj := NatIso.ofComponents (fun U => (e U).toAddCommGrpIso) (by
    intro U V k
    ext s
    simpa using he k s)
  refine ⟨(sheafToPresheaf J Ab.{w}).preimageIso α, fun U s => ?_⟩
  have : ((sheafToPresheaf J Ab.{w}).preimageIso α).hom.hom = α.hom := by
    have h := (sheafToPresheaf J Ab.{w}).map_preimage α.hom
    simpa using h
  rw [this]
  rfl

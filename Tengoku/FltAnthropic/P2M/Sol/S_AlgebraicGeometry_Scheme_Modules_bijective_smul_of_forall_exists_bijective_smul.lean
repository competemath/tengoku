import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FrameLocalSol

variable {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤))

noncomputable abbrev res (W : X.Opens) : Γ(M, W) := M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ

/--
@isnad1 id=eq.0h6v.s11.294af228dbcc from=translated src=- shape=cd6636b1 vocab=7337ffdb
-/
theorem res_map {W W' : X.Opens} (i : W' ⟶ W) : M.presheaf.map i.op (res M σ W) = res M σ W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/--
@isnad1 id=eq.0h7v.s13.3d38251780f9 from=translated src=- shape=c689d986 vocab=ae6864a2
-/
theorem smul_res {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M σ W) = X.presheaf.map i.op g • res M σ W' := by
  rw [Scheme.Modules.map_smul, res_map]

noncomputable def abSheaf : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

/--
@isnad1 id=bijectiv.1h4v.s13.b91e8ae39345 from=translated src=- shape=5d4da774 vocab=e1b839c8
-/
theorem main (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • res M σ W) :
    Function.Bijective fun g : Γ(X, V) => g • res M σ V := by
  classical
  choose U hxU hU using fun x : V => h x.1 x.2
  let W : V → X.Opens := fun x => V ⊓ U x
  have hWV : ∀ x, W x ≤ V := fun x => inf_le_left
  have hWU : ∀ x, W x ≤ U x := fun x => inf_le_right
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxU ⟨y, hy⟩⟩⟩
  constructor
  · intro g₁ g₂ hg
    have hg' : g₁ • res M σ V = g₂ • res M σ V := hg
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun x => homOfLE (hWV x)) hcover
    intro x
    apply (hU x (W x) (hWU x)).1
    show X.presheaf.map (homOfLE (hWV x)).op g₁ • res M σ (W x) =
      X.presheaf.map (homOfLE (hWV x)).op g₂ • res M σ (W x)
    rw [← smul_res, ← smul_res, hg']
  · intro s
    have hloc : ∀ x, ∃! g : Γ(X, W x), g • res M σ (W x) = M.presheaf.map (homOfLE (hWV x)).op s :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hU x (W x) (hWU x)) _
    choose gx hgx hgx_uniq using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W gx := by
      intro x y
      apply (hU x (W x ⊓ W y) (inf_le_left.trans (hWU x))).1
      show X.presheaf.map (Opens.infLELeft (W x) (W y)).op (gx x) • res M σ (W x ⊓ W y) =
        X.presheaf.map (Opens.infLERight (W x) (W y)).op (gx y) • res M σ (W x ⊓ W y)
      rw [← smul_res M σ (Opens.infLELeft (W x) (W y)), hgx x, ← smul_res M σ (Opens.infLERight (W x) (W y)),
        hgx y, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp]
      rfl
    obtain ⟨g, hg, -⟩ : ∃! g : Γ(X, V), ∀ x, X.presheaf.map (homOfLE (hWV x)).op g = gx x :=
      TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun x => homOfLE (hWV x)) hcover gx hcompat
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (abSheaf M) W V (fun x => homOfLE (hWV x)) hcover
    intro x
    show M.presheaf.map (homOfLE (hWV x)).op (g • res M σ V) = M.presheaf.map (homOfLE (hWV x)).op s
    rw [smul_res, ← hgx x]
    exact congrArg (· • res M σ (W x)) (hg x)

end FrameLocalSol

/--
@isnad1 id=bijectiv.1h4v.s13.1247b3426bd5 from=translated src=- shape=75a66e17 vocab=3f6d59d1
-/
theorem solution
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V)) :=
  FrameLocalSol.main M σ V h

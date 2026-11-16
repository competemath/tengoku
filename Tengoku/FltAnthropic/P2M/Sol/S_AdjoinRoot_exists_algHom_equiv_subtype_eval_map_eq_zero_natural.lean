import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdjoinRoot_exists_algHom_equiv_subtype_eval_map_eq_zero_natural.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdjoinRoot_exists_algHom_equiv_subtype_eval_map_eq_zero_natural

set_option autoImplicit false

universe u v w

open Polynomial

namespace AdjoinRootPointsAux

variable (W₀ : Type u) {S : Type v} [CommRing W₀] [CommRing S] [Algebra W₀ S] (g : S[X])
  (T : Type w) [CommRing T] [Algebra W₀ T]

abbrev Pts : Type _ := {p : (S →ₐ[W₀] T) × T // (g.map (p.1 : S →+* T)).eval p.2 = 0}

variable {T}

/--
@isnad1 id=eq.0h5v.s8.15b5ffb86ebb from=translated src=- shape=f1c9bd3a vocab=afaac6a0
-/
theorem eval_map_apply_root (χ : AdjoinRoot g →ₐ[W₀] T) :
    (g.map ((χ.comp (AdjoinRoot.ofAlgHom W₀ g) : S →ₐ[W₀] T) : S →+* T)).eval (χ (AdjoinRoot.root g)) = 0 := by
  rw [← Polynomial.eval₂_eq_eval_map]
  show g.eval₂ ((χ : AdjoinRoot g →+* T).comp (AdjoinRoot.of g)) ((χ : AdjoinRoot g →+* T) (AdjoinRoot.root g)) = 0
  rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

noncomputable def toPts (χ : AdjoinRoot g →ₐ[W₀] T) : Pts W₀ g T :=
  ⟨(χ.comp (AdjoinRoot.ofAlgHom W₀ g), χ (AdjoinRoot.root g)), eval_map_apply_root W₀ g χ⟩

/--
@isnad1 id=eq.0h5v.s9.2b9ac5cf1917 from=translated src=- shape=335a162d vocab=454280ec
-/
theorem eval₂_eq_zero_of_pts (p : Pts W₀ g T) : g.eval₂ (p.1.1 : S →ₐ[W₀] T) p.1.2 = 0 := by
  have := p.2
  rwa [← Polynomial.eval₂_eq_eval_map] at this

noncomputable def ofPts (p : Pts W₀ g T) : AdjoinRoot g →ₐ[W₀] T :=
  AdjoinRoot.liftAlgHom g p.1.1 p.1.2 (eval₂_eq_zero_of_pts W₀ g p)

/--
@isnad1 id=eq.0h6v.s8.1b080c42d1d3 from=translated src=- shape=7067c225 vocab=4e2745e3
-/
theorem ofPts_of (p : Pts W₀ g T) (s : S) : ofPts W₀ g p (AdjoinRoot.of g s) = p.1.1 s :=
  AdjoinRoot.liftAlgHom_of g _ _ _ s

/--
@isnad1 id=eq.0h5v.s8.a6484f5a9143 from=translated src=- shape=e98d84a0 vocab=35dc13d9
-/
theorem ofPts_root (p : Pts W₀ g T) : ofPts W₀ g p (AdjoinRoot.root g) = p.1.2 :=
  AdjoinRoot.liftAlgHom_root g _ _ _

/--
@isnad1 id=eq.0h5v.s7.e94734c689db from=translated src=- shape=cf23f766 vocab=b597aaf1
-/
theorem ofPts_toPts (χ : AdjoinRoot g →ₐ[W₀] T) : ofPts W₀ g (toPts W₀ g χ) = χ := by
  refine AdjoinRoot.algHom_ext' ?_ ?_
  · ext s
    exact ofPts_of W₀ g (toPts W₀ g χ) s
  · exact ofPts_root W₀ g (toPts W₀ g χ)

/--
@isnad1 id=eq.0h5v.s6.0de15823acbd from=translated src=- shape=e043eb32 vocab=6ed02de5
-/
theorem toPts_ofPts (p : Pts W₀ g T) : toPts W₀ g (ofPts W₀ g p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · ext s
    exact ofPts_of W₀ g p s
  · exact ofPts_root W₀ g p

noncomputable def equiv : (AdjoinRoot g →ₐ[W₀] T) ≃ Pts W₀ g T where
  toFun := toPts W₀ g
  invFun := ofPts W₀ g
  left_inv := ofPts_toPts W₀ g
  right_inv := toPts_ofPts W₀ g

end AdjoinRootPointsAux

/--
@isnad1 id=ex.0h3v.s12.6ca32b752204 from=translated src=- shape=652cff6d vocab=afc0a633
-/
theorem solution
    {Λ : Type u} [CommRing Λ] (S : Type v) [CommRing S] [Algebra Λ S] (g : S[X]) :
    ∃ η : ∀ (T : Type w) [CommRing T] [Algebra Λ T],
        ((AdjoinRoot g →ₐ[Λ] T) ≃ {p : (S →ₐ[Λ] T) × T // (g.map (p.1 : S →+* T)).eval p.2 = 0}),
      (∀ (T : Type w) [CommRing T] [Algebra Λ T] (φ : AdjoinRoot g →ₐ[Λ] T),
        ((η T φ).1 : (S →ₐ[Λ] T) × T) =
          (φ.comp (IsScalarTower.toAlgHom Λ S (AdjoinRoot g)), φ (AdjoinRoot.root g))) ∧
      ∀ (T : Type w) [CommRing T] [Algebra Λ T] (T' : Type w) [CommRing T'] [Algebra Λ T']
        (f : T →ₐ[Λ] T') (φ : AdjoinRoot g →ₐ[Λ] T),
        ((η T' (f.comp φ)).1 : (S →ₐ[Λ] T') × T') = (f.comp (η T φ).1.1, f (η T φ).1.2) :=
  ⟨fun T _ _ => AdjoinRootPointsAux.equiv Λ g (T := T),
    fun T _ _ φ => rfl,
    fun T _ _ T' _ _ f φ => rfl⟩

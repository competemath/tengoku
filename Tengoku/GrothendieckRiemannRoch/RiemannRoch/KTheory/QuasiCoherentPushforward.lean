/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.AlgebraicGeometry.Modules.Tilde
import Tengoku.Seed.AlgebraicGeometry.AffineScheme

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quasi-coherent pushforward along quasi-compact open immersions

Main results (namespace `QCPushforward`):
* `isQuasicoherent_pushforward_opens_ι`: for `X` a scheme whose underlying space is
  quasi-separated, `U ⊆ X` a quasi-compact open and `F` a quasi-coherent `𝒪_U`-module,
  `j_* F` (`Scheme.Modules.pushforward U.ι`) is quasi-coherent.
* `isQuasicoherent_pushforward_ι`: the affine case `X = Spec R`.
* `isQuasicoherent_of_restrict`: affine criterion — a module on `Spec R` which is
  quasi-coherent on a quasi-compact open `V` and "only sees `V`" is quasi-coherent.
* `isQuasicoherent_of_affine_cover`: quasi-coherence is local on affine opens.

The affine argument is EGA I 1.4.1 (conditions d1/d2). The Mathlib versions of the auxiliary
structure `Aux` and its lemmas are `private` in `Mathlib.AlgebraicGeometry.Modules.Tilde`; they
are copied here (`Aux`, `Aux.of_le`, `aux_top_of_isLocalizing`, `aux_basicOpen_of_aux_restrict`),
and `Aux.of_eq_iSup_basicOpen` is generalised to `gaux_of_eq_iSup_basicOpen`, which drops the
containment `D(f) ≤ V`.
-/

noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite PrimeSpectrum

namespace QCPushforward

variable {R : CommRingCat.{u}}

/-- Generalised version: the restriction `Γ(M, V) → Γ(M, V ⊓ D(f))` is localisation at `f`
for every `f : R` (no containment `D(f) ≤ V`).-/
structure GAux (M : (Spec R).Modules) (V : (Spec R).Opens) : Prop where
  /-- Every section over `V ⊓ D(f)` extends to `V` after multiplying by a power of `f`.-/
  existence (f : R) (s : Γ(M, V ⊓ basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE inf_le_left).op t = f ^ n • s
  /-- A section over `V` vanishing on `V ⊓ D(f)` is killed by a power of `f`.-/
  uniqueness (f : R) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE (inf_le_left : V ⊓ basicOpen f ≤ V)) t = 0 →
    ∃ (n : ℕ), f ^ n • t = 0

set_option backward.isDefEq.respectTransparency false in
/-- `GAux` on `V`, plus the fact that `M` "only sees `V`", gives the localising property.
@isnad1 id=islocali.2h3v.s10.b3ca6cfdf164 from=translated src=- shape=ed0f67e4 vocab=ffd120cd
-/
theorem isLocalizing_of_gaux (M : (Spec R).Modules) (V : (Spec R).Opens) (h : GAux M V)
    (hV : ∀ (W W' : (Spec R).Opens) (hW : W' ≤ W), V ⊓ W ≤ W' →
      Function.Bijective (M.presheaf.map (homOfLE hW).op)) :
    IsLocalizing (modulesSpecToSheaf.obj M) := by
  intro f
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl) ?_ ?_
  · intro (x : Γ(M, basicOpen f))
    obtain ⟨n, t, ht⟩ := h.existence f
      (M.presheaf.map (homOfLE (inf_le_right : V ⊓ basicOpen f ≤ basicOpen f)).op x)
    obtain ⟨T, hT⟩ := (hV ⊤ V le_top inf_le_left).2 t
    refine ⟨n, T, ?_⟩
    apply (hV (basicOpen f) (V ⊓ basicOpen f) inf_le_right le_rfl).1
    show M.presheaf.map (homOfLE inf_le_right).op (f ^ n • x) =
      M.presheaf.map (homOfLE inf_le_right).op (M.presheaf.map (basicOpen f).leTop.op T)
    rw [M.map_smul_Spec, ← ht, ← hT, ← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
    rfl
  · intro (x : Γ(M, ⊤)) hx
    have hx' : M.presheaf.map (basicOpen f).leTop.op x = 0 := hx
    obtain ⟨n, hn⟩ := h.uniqueness f (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op x) (by
      have : M.presheaf.map (homOfLE (inf_le_left : V ⊓ basicOpen f ≤ V)).op
          (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op x) =
          M.presheaf.map (homOfLE (inf_le_right : V ⊓ basicOpen f ≤ basicOpen f)).op
            (M.presheaf.map (basicOpen f).leTop.op x) := by
        rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
        rfl
      rw [this, hx', map_zero])
    refine ⟨n, (hV ⊤ V le_top inf_le_left).1 ?_⟩
    rw [M.map_smul_Spec, hn, map_zero]

/-! ### Local-to-global for quasi-coherence -/

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent sheaf on an affine `Spec R` has a global presentation.-/
def presentationOfIsQuasicoherentSpec (N : (Spec R).Modules) [N.IsQuasicoherent] :
    N.Presentation :=
  haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  SheafOfModules.Presentation.ofIsIso N.fromTildeΓ
    (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _))

set_option backward.isDefEq.respectTransparency false in
/-- Transport a presentation of `M.restrict hW.fromSpec` to `M.restrict W.ι`.-/
def presentationRestrictι {X : Scheme.{u}} (M : X.Modules) {W : X.Opens} (hW : IsAffineOpen W)
    (P : (M.restrict hW.fromSpec).Presentation) : (M.restrict W.ι).Presentation :=
  have h : hW.isoSpec.hom ≫ hW.fromSpec = W.ι := by
    rw [← hW.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  SheafOfModules.Presentation.ofIsIso
    (((Scheme.Modules.restrictFunctorComp hW.isoSpec.hom hW.fromSpec).app M).inv ≫
      ((Scheme.Modules.restrictFunctorCongr h).app M).hom)
    (Scheme.Modules.presentationRestrict hW.isoSpec.hom P)

set_option backward.isDefEq.respectTransparency false in
/-- Transport a presentation of `M.restrict W.ι` to `M.over W`.-/
def presentationOver {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (P : (M.restrict W.ι).Presentation) : (M.over W).Presentation :=
  SheafOfModules.Presentation.ofIsIso
    (((Scheme.Modules.overEquiv W).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv W).app M).symm ≪≫
      ((Scheme.Modules.overEquiv W).unitIso.app _).symm).hom)
    (P.map (Scheme.Modules.overEquiv W).inverse
      (W.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm)

/-- **Quasi-coherence is local**: if every point has an affine open neighbourhood `W` on which
`M` (transported to `Spec Γ(X, W)`) is quasi-coherent, then `M` is quasi-coherent.
@isnad1 id=isquasic.1h2v.s11.6d608c6be8e2 from=translated src=- shape=7f7a53a4 vocab=c81dd100
-/
theorem isQuasicoherent_of_affine_cover {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (W : X.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (M.restrict hW.fromSpec).IsQuasicoherent) :
    M.IsQuasicoherent := by
  choose W hW hxW hq using h
  let q : SheafOfModules.QuasicoherentData (R := X.ringCatSheaf) M :=
    { I := X
      X := W
      coversTop := by
        rw [Opens.coversTop_iff]
        exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩
      presentation := fun x => presentationOver M (W x) (presentationRestrictι M (hW x)
        (haveI := hq x; presentationOfIsQuasicoherentSpec _)) }
  exact q.isQuasicoherent

end QCPushforward

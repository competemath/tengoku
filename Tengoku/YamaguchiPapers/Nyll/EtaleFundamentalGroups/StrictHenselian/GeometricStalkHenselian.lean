/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Tengoku.Seed.Algebra.Polynomial.Degree.Operations
import Tengoku.Seed.Algebra.Polynomial.Derivative
import Tengoku.Seed.Algebra.Polynomial.Eval.Coeff
import Tengoku.Seed.Algebra.Polynomial.Monic
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.RingHomProperties
import Tengoku.Seed.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Tengoku.Seed.RingTheory.Etale.StandardEtale
import Tengoku.Seed.RingTheory.Henselian
import Tengoku.Seed.RingTheory.RingHom.Etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Henselianity of the constructed geometric étale stalk

The ring in `GeometricStalk` is the actual filtered colimit over pointed étale
neighborhoods. A monic polynomial descends to one neighborhood because it has
only finitely many coefficients. A simple root at the geometric point then
defines a further neighborhood using the concrete standard étale algebra
`R[X,Y]/(f, Y f' - 1)`. Its universal root gives the required root in the colimit.

The resulting Henselian property is proved, not added as a field of a putative
strict henselization. Identification of its residue field and comparison with
the inertia group in the manuscript still require separate arguments.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- A simple root at the geometric point lifts by the actual standard étale
neighborhood obtained by adjoining a root and inverting its derivative.-/
theorem geometricStalk_lift_simpleRoot (W : S.Etale)
    (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)
    (q : Γ(W.left, ⊤)[X]) (hq : q.Monic) (α : Ω)
    (hroot : (q.map (t.left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom).eval α = 0)
    (hderivative : (q.derivative.map (t.left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom).eval α ≠ 0) :
    ∃ a : geometricStalk s,
      (q.map (geometricStalkGerm s W t).hom).IsRoot a ∧
      geometricStalkEvaluation s a = α := by
  let R : CommRingCat.{u} := Γ(W.left, ⊤)
  let φ : R ⟶ CommRingCat.of Ω :=
    t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
  let : Algebra R Ω := φ.hom.toAlgebra
  let P : StandardEtalePair R :=
    { f := q
      monic_f := hq
      g := q.derivative
      cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩ }
  have hα : P.HasMap α := by
    constructor
    · change q.eval₂ φ.hom α = 0
      rw [eval₂_eq_eval_map]
      exact hroot
    · change IsUnit (q.derivative.eval₂ φ.hom α)
      rw [eval₂_eq_eval_map]
      exact isUnit_iff_ne_zero.mpr hderivative
  let B : CommRingCat.{u} := .of P.Ring
  let base : R ⟶ B := CommRingCat.ofHom (algebraMap R P.Ring)
  let ψ : B ⟶ CommRingCat.of Ω := CommRingCat.ofHom (P.lift α hα).toRingHom
  have hbaseψ : base ≫ ψ = φ := by
    apply CommRingCat.hom_ext
    exact (P.lift α hα).comp_algebraMap
  have hpoint : t.left ≫ W.left.toSpecΓ = Spec.map ψ ≫ Spec.map base := by
    have hnatural : t.left ≫ W.left.toSpecΓ =
        (Spec (CommRingCat.of Ω)).toSpecΓ ≫ Spec.map t.left.appTop :=
      Scheme.toSpecΓ_naturality t.left
    have hφ : (Spec (CommRingCat.of Ω)).toSpecΓ ≫ Spec.map t.left.appTop =
        Spec.map φ := by
      change (Spec (CommRingCat.of Ω)).toSpecΓ ≫ Spec.map t.left.appTop =
        Spec.map (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom)
      rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    have hcomp : Spec.map φ = Spec.map ψ ≫ Spec.map base := by
      rw [← Spec.map_comp, hbaseψ]
    exact hnatural.trans (hφ.trans hcomp)
  have : Etale (Spec.map base) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let V : Scheme.{u} := pullback W.left.toSpecΓ (Spec.map base)
  let j : V ⟶ W.left := pullback.fst W.left.toSpecΓ (Spec.map base)
  let k : V ⟶ Spec B := pullback.snd W.left.toSpecΓ (Spec.map base)
  let l : Spec (CommRingCat.of Ω) ⟶ V := pullback.lift t.left (Spec.map ψ) hpoint
  have hlj : l ≫ j = t.left := pullback.lift_fst _ _ _
  have hlk : l ≫ k = Spec.map ψ := pullback.lift_snd _ _ _
  let T : S.Etale := Scheme.Etale.mk (j ≫ W.hom)
  let f : T ⟶ W := MorphismProperty.Over.homMk j rfl
  let tT : (Scheme.pointEtaleNeighborhoods s).fiber.obj T := Over.homMk l (by
    change l ≫ (j ≫ W.hom) = s
    rw [← Category.assoc, hlj]
    exact Over.w t)
  have htT : (Scheme.pointEtaleNeighborhoods s).fiber.map f tT = t := by
    apply Over.OverMorphism.ext
    exact hlj
  let h : B ⟶ Γ(V, ⊤) := (Scheme.ΓSpecIso B).inv ≫ k.appTop
  have hbase : base ≫ h = j.appTop := by
    change base ≫ (Scheme.ΓSpecIso B).inv ≫ k.appTop = j.appTop
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso R).inv ≫
      (pullback.snd W.left.toSpecΓ (Spec.map base) ≫ Spec.map base).appTop = j.appTop
    rw [← pullback.condition, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_assoc]
  let germ : Γ(V, ⊤) ⟶ geometricStalk s := geometricStalkGerm s T tT
  have hgerm : j.appTop ≫ germ = geometricStalkGerm s W t := by
    have heq := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w f tT (etaleSections S)
    rw [htT] at heq
    exact heq
  have hgermEvaluation : germ ≫ geometricStalkEvaluation s =
      l.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom :=
    geometricStalkGerm_evaluation s T tT
  let e : B ⟶ geometricStalk s := h ≫ germ
  have he : e.hom.comp (algebraMap R P.Ring) =
      (geometricStalkGerm s W t).hom := by
    change (base ≫ e).hom = (geometricStalkGerm s W t).hom
    change (base ≫ (h ≫ germ)).hom = (geometricStalkGerm s W t).hom
    rw [← Category.assoc, hbase, hgerm]
  have heval : e ≫ geometricStalkEvaluation s = ψ := by
    change ((Scheme.ΓSpecIso B).inv ≫ k.appTop ≫ germ) ≫
      geometricStalkEvaluation s = ψ
    rw [Category.assoc, Category.assoc, hgermEvaluation]
    rw [← Category.assoc k.appTop, ← Scheme.Hom.comp_appTop, hlk,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  refine ⟨e P.X, ?_, ?_⟩
  · change (q.map (geometricStalkGerm s W t).hom).eval (e P.X) = 0
    rw [eval_map, ← he, ← Polynomial.hom_eval₂]
    have hPX : q.eval₂ (algebraMap R P.Ring) P.X = 0 := P.hasMap_X.1
    rw [hPX, map_zero]
  · exact (ConcreteCategory.congr_hom heval P.X).trans (P.lift_X α hα)

/-- The maximal ideal of the constructed stalk is exactly the kernel of its
evaluation at the geometric point.-/
theorem geometricStalk_mem_maximalIdeal_iff (a : geometricStalk s) :
    a ∈ IsLocalRing.maximalIdeal (geometricStalk s) ↔
      geometricStalkEvaluation s a = 0 := by
  classical
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, geometricStalk_isUnit_iff]
  exact not_not

end EtaleFundamentalGroups.StrictHenselian

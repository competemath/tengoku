/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.QuasiIso
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Splitting
public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Dimension
public import Tengoku.Seed.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Tengoku.Seed.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Computing homology using nondegenerate simplices

In this file, we introduce the normalized chain complex `X.normalizedChainComplex R`
of a simplicial set `X` with coefficients in `R` (where `R` is an object of a
preadditive category `C` with coproducts). The `n`-chains of this complex
identify to the coproduct of copies of `R` indexed by the nondegenerate
`n`-simplices of `X`. In particular, we deduce that the homology is zero in degree `≥ d`
when `X` has dimension `< d`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex Simplicial
  AlgebraicTopology.DoldKan

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X Y : SSet.{w}) (f : X ⟶ Y) (R : C)

/-- The normalized chain complex of a simplicial set `X` with coefficients in `R`.
In degree `n`, it consists of a coproduct of copies of `R` indexed by the
nondegenerate `n`-simplices of `X`. -/
noncomputable def normalizedChainComplex : ChainComplex C ℕ :=
  (X.splitting.map (sigmaConst.obj R)).nondegComplex

/-- The split epi `X.chainComplex R ⟶ X.normalizedChainComplex R`. -/
noncomputable def toNormalizedChainComplex : X.chainComplex R ⟶ X.normalizedChainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).toNondegComplex

/-- The split mono `X.normalizedChainComplex R ⟶ X.chainComplex R`. -/
noncomputable def fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

/--
@isnad1 id=eq.0h3v.s9.65276dc20c70 from=seed src=0 shape=066dd933 vocab=6a134913
-/
@[reassoc (attr := simp)]
lemma PInfty_toNormalizedChainComplex :
    PInfty ≫ X.toNormalizedChainComplex R = X.toNormalizedChainComplex R :=
  SimplicialObject.Splitting.PInfty_toNondegComplex _

instance : IsSplitEpi (X.toNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

instance : IsSplitMono (X.fromNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

/--
@isnad1 id=eq.0h3v.s8.218a63f6aaca from=seed src=0 shape=15d8a0e9 vocab=6f0709a0
-/
@[reassoc (attr := simp)]
lemma fromNormalizedChainComplex_toNormalizedChainComplex :
    X.fromNormalizedChainComplex R ≫ X.toNormalizedChainComplex R = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

/--
@isnad1 id=eq.0h4v.s8.a3c3c885d917 from=seed src=0 shape=edfb5461 vocab=81748a0e
-/
@[reassoc (attr := simp)]
lemma fromNormalizedChainComplex_f_toNormalizedChainComplex_f (n : ℕ) :
    (X.fromNormalizedChainComplex R).f n ≫ (X.toNormalizedChainComplex R).f n = 𝟙 _ := by
  simp [← HomologicalComplex.comp_f]

/--
@isnad1 id=eq.0h3v.s8.0f0ef2eecd6e from=seed src=0 shape=e610ef1c vocab=05b2bf7d
-/
@[reassoc (attr := simp)]
lemma toNormalizedChainComplex_fromNormalizedChainComplex :
    X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R = PInfty :=
  SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

/--
@isnad1 id=eq.0h4v.s9.034368af8440 from=seed src=0 shape=631004be vocab=530f26e5
-/
@[reassoc (attr := simp)]
lemma toNormalizedChainComplex_f_fromNormalizedChainComplex_f (n : ℕ) :
    (X.toNormalizedChainComplex R).f n ≫ (X.fromNormalizedChainComplex R).f n = PInfty.f n := by
  simp [← HomologicalComplex.comp_f]

/-- The homotopy equivalence from `X.chainComplex R` to `X.normalizedChainComplex R`. -/
noncomputable def homotopyEquivNormalizedChainComplex :
    HomotopyEquiv (X.chainComplex R) (X.normalizedChainComplex R) :=
  SimplicialObject.Splitting.homotopyEquivNondegComplex _

/--
@isnad1 id=eq.0h3v.s7.91d1d497c504 from=seed src=0 shape=2089ab0a vocab=2d5a5108
-/
@[simp]
lemma homotopyEquivNormalizedChainComplex_hom :
    (X.homotopyEquivNormalizedChainComplex R).hom = X.toNormalizedChainComplex R := rfl

/--
@isnad1 id=eq.0h3v.s7.2ab6f5c16dd4 from=seed src=0 shape=b4b5f4e9 vocab=c87f63f8
-/
@[simp]
lemma homotopyEquivNormalizedChainComplex_inv :
    (X.homotopyEquivNormalizedChainComplex R).inv = X.fromNormalizedChainComplex R := rfl

section

variable {R} {n : ℕ}

/-- The map `R ⟶ (X.normalizedChainComplex R).X n` for any `x : X _⦋n⦌`. Note that
this is zero if `x` is a degenerate simplex, see `ιNormalizedChainComplex_eq_zero`. -/
@[no_expose]
noncomputable def ιNormalizedChainComplex (x : X _⦋n⦌) :
    R ⟶ (X.normalizedChainComplex R).X n :=
  X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n

/--
@isnad1 id=eq.0h5v.s7.516cda7ebc09 from=seed src=0 shape=479767af vocab=5d27cf68
-/
@[reassoc (attr := simp)]
lemma ιChainComplex_toNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n =
    X.ιNormalizedChainComplex x := by
  rfl

/--
@isnad1 id=eq.0h5v.s9.d6cb2a60d527 from=seed src=0 shape=cdf0f647 vocab=89538abf
-/
@[reassoc (attr := simp)]
lemma ιNormalizedChainComplex_d {n : ℕ} (x : X _⦋n + 1⦌) :
    X.ιNormalizedChainComplex x ≫ (X.normalizedChainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιNormalizedChainComplex (X.δ i x) := by
  simp [ιNormalizedChainComplex, Preadditive.sum_comp,
    -ιChainComplex_toNormalizedChainComplex_f]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h5v.s9.fc637ecc6d0e from=seed src=0 shape=89da7ce7 vocab=498c6f12
-/
@[reassoc]
lemma ιNormalizedChainComplex_fromNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (X.fromNormalizedChainComplex R).f n =
      X.ιChainComplex x ≫ (PInfty).f n := by
  dsimp [ιNormalizedChainComplex]
  rw [Category.assoc, toNormalizedChainComplex_f_fromNormalizedChainComplex_f]

/--
@isnad1 id=eq.1h5v.s7.0ff5ba1ec491 from=seed src=0 shape=1875b8ac vocab=04b8efb1
-/
lemma ιNormalizedChainComplex_eq_zero (x : X _⦋n⦌) (hx : x ∈ X.degenerate n) :
    X.ιNormalizedChainComplex (R := R) x = 0 := by
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), zero_comp,
    ιNormalizedChainComplex_fromNormalizedChainComplex_f]
  obtain _ | n := n
  · simp at hx
  · simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    let X' := ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X
    obtain ⟨i, y, rfl⟩ := hx
    trans X.ιChainComplex y ≫ X'.σ i ≫ (PInfty (X := X')).f _
    · simp [ιChainComplex, X']
    · simp

variable (R n) in
/-- The cofan given by the inclusions
`X.ιNormalizedChainComplex x : R ⟶ (X.normalizedChainComplex R).X n` for all
nondegenerate `n`-simplices `x` of a simplicial set `X`. -/
noncomputable abbrev cofanNormalizedChainComplex : Cofan (fun (_ : X.nonDegenerate n) ↦ R) :=
  Cofan.mk _ (fun x ↦ X.ιNormalizedChainComplex x.val)

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
private lemma ιNormalizedChainComplex_eq_ι (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    X.ιNormalizedChainComplex (R := R) x =
      Sigma.ι (fun (_ : X.nonDegenerate n) ↦ R) ⟨x, hx⟩ := by
  dsimp [ιNormalizedChainComplex, ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), Category.assoc,
    toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
/-- `(X.normalizedChainComplex R).X n` identifies to the coproduct of copies
of `R` indexed by the nondegenerate `n`-simplices of the simplicial set `X`. -/
@[no_expose]
noncomputable def isColimitCofanNormalizedChainComplex :
    IsColimit (X.cofanNormalizedChainComplex R n) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) (fun ⟨x, hx⟩ ↦ by
      simpa using (X.ιNormalizedChainComplex_eq_ι R n x hx).symm))

/--
@isnad1 id=eq.1h7v.s8.ec2d9a5f926e from=seed src=0 shape=bd9c812e vocab=83807822
-/
@[ext]
lemma normalizedChainComplex_hom_ext {T : C} {f g : (X.normalizedChainComplex R).X n ⟶ T}
    (h : ∀ (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate n),
      X.ιNormalizedChainComplex x ≫ f = X.ιNormalizedChainComplex x ≫ g) :
    f = g :=
  (X.isColimitCofanNormalizedChainComplex R n).hom_ext (fun ⟨x, hx⟩ ↦ h x hx)

end

/--
@isnad1 id=iszero.0h6v.s6.1f1891871f08 from=seed src=0 shape=9bce8e60 vocab=e82b198f
-/
lemma isZero_normalizedChainComplex_X_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero ((X.normalizedChainComplex R).X n) := by
  rw [IsZero.iff_id_eq_zero]
  ext x hx
  exact (h.not_gt (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ d)).elim

section

variable {X Y}

/--
@isnad1 id=eq.0h5v.s10.6c5af2c04dad from=seed src=0 shape=83f2b081 vocab=1d52fd45
-/
@[reassoc]
lemma chainComplexMap_PInfty :
    chainComplexMap f R ≫ PInfty = PInfty ≫ chainComplexMap f R :=
  (natTransPInfty _).naturality _

/-- The morphism `X.normalizedChainComplex R ⟶ Y.normalizedChainComplex R` induced
by a morphism a simplicial sets `X ⟶ Y`. -/
noncomputable def normalizedChainComplexMap :
    X.normalizedChainComplex R ⟶ Y.normalizedChainComplex R :=
  X.fromNormalizedChainComplex R ≫ chainComplexMap f R ≫ Y.toNormalizedChainComplex R

/--
@isnad1 id=eq.0h5v.s8.35140cc88ee8 from=seed src=0 shape=ce168d09 vocab=f3823b03
-/
@[reassoc (attr := simp)]
lemma toNormalizedChainComplex_normalizedChainComplexMap :
    X.toNormalizedChainComplex R ≫ normalizedChainComplexMap f R =
      chainComplexMap f R ≫ Y.toNormalizedChainComplex R := by
  simp [normalizedChainComplexMap, ← chainComplexMap_PInfty_assoc]

/--
@isnad1 id=eq.0h7v.s8.1539cdf12348 from=seed src=0 shape=84ce3dc4 vocab=e350c00b
-/
@[reassoc (attr := simp)]
lemma ι_normalizedChainComplexMap_f {n : ℕ} (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (normalizedChainComplexMap f R).f n =
      Y.ιNormalizedChainComplex (f.app _ x) := by
  simpa only [comp_f, eval_map, ιNormalizedChainComplex,
    ιChainComplex_toNormalizedChainComplex_f_assoc, ι_chainComplexMap_f_assoc] using
    X.ιChainComplex x ≫=
      (eval _ _ n).congr_map (toNormalizedChainComplex_normalizedChainComplexMap f R)

/-- Given `R : C`, this is the functor `SSet.{w} ⥤ ChainComplex C ℕ` which sends
a simplicial set `X` to `X.normalizedChainComplex R`. -/
@[simps]
noncomputable def normalizedChainComplexFunctorObj : SSet.{w} ⥤ ChainComplex C ℕ where
  obj X := X.normalizedChainComplex R
  map f := normalizedChainComplexMap f R

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `X.toNormalizedChainComplex R` for any simplicial set `X`,
as a natural transformation. -/
@[simps]
noncomputable def toNormalizedChainComplexNatTrans :
    (chainComplexFunctor C).obj R ⟶ normalizedChainComplexFunctorObj R where
  app X := X.toNormalizedChainComplex R

end

section

variable [CategoryWithHomology C]

instance : QuasiIso (X.toNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom

instance : QuasiIso (X.fromNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv

/--
@isnad1 id=exactat.0h6v.s6.09a605efcdc1 from=seed src=0 shape=18f0ec20 vocab=17cab1f2
-/
lemma exactAt_chainComplex_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    (X.chainComplex R).ExactAt n := by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)

/--
@isnad1 id=iszero.0h6v.s5.205438f11c16 from=seed src=0 shape=6908e5bd vocab=e53acd72
-/
lemma isZero_homology_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero (X.homology R n) := by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

end

end SSet

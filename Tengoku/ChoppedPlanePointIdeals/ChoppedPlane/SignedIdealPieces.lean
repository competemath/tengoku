module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.GradedPresentation
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HilbertDifference

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Actual ideal pieces with signed degrees

Canonical degree transport and the comparison with natural homogeneous
pieces preserve the underlying polynomial of every representative.
-/
noncomputable section
namespace ChoppedPlane

variable {K : Type*} [Field K] {n : ℕ}

/-- The genuine ideal piece inside the signed homogeneous form space.-/
def signedIdealPiece (I : Ideal (Poly K n)) (t : ℤ) :
    Submodule K (signedForms K n t) :=
  (I.restrictScalars K).comap (signedForms K n t).subtype

/-- The actual residual ideal quotient in a signed homogeneous degree.-/
abbrev signedIdealResidualPiece (J I : Ideal (Poly K n)) (t : ℤ) :=
  nestedSubmoduleQuotient (signedIdealPiece J t) (signedIdealPiece I t)

/-- Equal signed degrees canonically identify the ideal pieces.-/
def signedIdealPieceEquivOfEq (I : Ideal (Poly K n)) {t u : ℤ} (h : t = u) :
    signedIdealPiece I t ≃ₗ[K] signedIdealPiece I u := by
  subst u
  exact LinearEquiv.refl K _

/--
@isnad1 id=eq.1h6v.s14.f7f1e9f38ba4 from=translated src=- shape=34ad1361 vocab=68b9ca7b
-/
@[simp] theorem signedIdealPieceEquivOfEq_val (I : Ideal (Poly K n))
    {t u : ℤ} (h : t = u) (f : signedIdealPiece I t) :
    ((signedIdealPieceEquivOfEq I h f).val).val = f.val.val := by
  subst u
  rfl

/-- At a natural degree, signed and ordinary ideal pieces canonically agree.-/
def signedIdealPieceNatEquiv (I : Ideal (Poly K n)) (t : ℕ) :
    signedIdealPiece I (t : ℤ) ≃ₗ[K] idealFormPiece I t where
  toFun f := ⟨⟨f.val.val, by simpa only [signedForms_nat] using f.val.property⟩, f.property⟩
  invFun f := ⟨⟨f.val.val, by simpa only [signedForms_nat] using f.val.property⟩, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h5v.s14.0b5d168d297b from=translated src=- shape=bc9b801c vocab=43bfeb4f
-/
@[simp] theorem signedIdealPieceNatEquiv_val (I : Ideal (Poly K n))
    (t : ℕ) (f : signedIdealPiece I (t : ℤ)) :
    ((signedIdealPieceNatEquiv I t f).val).val = f.val.val := rfl

/--
@isnad1 id=eq.0h5v.s15.78b56d2084c6 from=translated src=- shape=bbc3673d vocab=95111a26
-/
@[simp] theorem signedIdealPieceNatEquiv_symm_val (I : Ideal (Poly K n))
    (t : ℕ) (f : idealFormPiece I t) :
    (((signedIdealPieceNatEquiv I t).symm f).val).val = f.val.val := rfl

/-- Transport a signed ideal piece to an ordinary piece whenever its degree
is equal to the corresponding natural degree.-/
def signedIdealPieceEquivNatOfEq (I : Ideal (Poly K n))
    {u : ℤ} (t : ℕ) (h : u = (t : ℤ)) :
    signedIdealPiece I u ≃ₗ[K] idealFormPiece I t :=
  (signedIdealPieceEquivOfEq I h).trans (signedIdealPieceNatEquiv I t)

/--
@isnad1 id=eq.1h6v.s14.29aead162c5f from=translated src=- shape=a1dfb080 vocab=45d84dc4
-/
@[simp] theorem signedIdealPieceEquivNatOfEq_val (I : Ideal (Poly K n))
    {u : ℤ} (t : ℕ) (h : u = (t : ℤ)) (f : signedIdealPiece I u) :
    ((signedIdealPieceEquivNatOfEq I t h f).val).val = f.val.val := by
  simp [signedIdealPieceEquivNatOfEq]

/-- The natural comparison carries the actual residual submodule onto the
ordinary residual submodule.
@isnad1 id=eq.0h5v.s14.22b4fcef47df from=translated src=- shape=ee9c95b4 vocab=f6e15d7f
-/
theorem signedIdealPieceNatEquiv_map_residual (J I : Ideal (Poly K n)) (t : ℕ) :
    ((signedIdealPiece J (t : ℤ)).comap (signedIdealPiece I (t : ℤ)).subtype).map
      (signedIdealPieceNatEquiv I t).toLinearMap =
      (idealFormPiece J t).comap (idealFormPiece I t).subtype := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hf
    refine ⟨(signedIdealPieceNatEquiv I t).symm f, hf, ?_⟩
    exact (signedIdealPieceNatEquiv I t).apply_symm_apply f

/-- The actual signed residual quotient is canonically equivalent to the
ordinary residual quotient in every natural degree.-/
def signedIdealResidualPieceNatEquiv (J I : Ideal (Poly K n)) (t : ℕ) :
    signedIdealResidualPiece J I (t : ℤ) ≃ₗ[K] idealResidualPiece J I t :=
  Submodule.Quotient.equiv _ _ (signedIdealPieceNatEquiv I t)
    (signedIdealPieceNatEquiv_map_residual J I t)

/-- This quotient comparison sends each class to the class represented by the
same polynomial in the ordinary homogeneous space.
@isnad1 id=eq.0h6v.s16.91ee07ad7bd1 from=translated src=- shape=742547b0 vocab=ca1974fc
-/
@[simp] theorem signedIdealResidualPieceNatEquiv_mk (J I : Ideal (Poly K n))
    (t : ℕ) (f : signedIdealPiece I (t : ℤ)) :
    signedIdealResidualPieceNatEquiv J I t (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (signedIdealPieceNatEquiv I t f) := rfl

/-- Equal signed target degrees canonically identify the residual quotients.-/
def signedIdealResidualPieceEquivOfEq (J I : Ideal (Poly K n))
    {t u : ℤ} (h : t = u) :
    signedIdealResidualPiece J I t ≃ₗ[K] signedIdealResidualPiece J I u := by
  subst u
  exact LinearEquiv.refl K _

/-- Transport a signed residual quotient to an ordinary one at an equal
natural target degree.-/
def signedIdealResidualPieceEquivNatOfEq (J I : Ideal (Poly K n))
    {u : ℤ} (t : ℕ) (h : u = (t : ℤ)) :
    signedIdealResidualPiece J I u ≃ₗ[K] idealResidualPiece J I t :=
  (signedIdealResidualPieceEquivOfEq J I h).trans
    (signedIdealResidualPieceNatEquiv J I t)

/--
@isnad1 id=eq.0h5v.s14.5d48809b2f6e from=translated src=- shape=f4983300 vocab=b98303d8
-/
@[simp] theorem finrank_signedIdealResidualPiece_nat (J I : Ideal (Poly K n)) (t : ℕ) :
    Module.finrank K (signedIdealResidualPiece J I (t : ℤ)) =
      Module.finrank K (idealResidualPiece J I t) :=
  (signedIdealResidualPieceNatEquiv J I t).finrank_eq

/-- Nested genuine ideals induce nested signed homogeneous pieces.
@isnad1 id=le.1h5v.s10.b7985115893b from=translated src=- shape=92b40bfe vocab=9816365a
-/
theorem signedIdealPiece_mono {J I : Ideal (Poly K n)} (hJI : J ≤ I) (t : ℤ) :
    signedIdealPiece J t ≤ signedIdealPiece I t := fun _ hf => hJI hf

end ChoppedPlane

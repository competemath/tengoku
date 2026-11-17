import Tengoku.StringDiagramsLean.StringDiagrams.Examples.TemperleyLieb
import Tengoku.StringDiagramsLean.StringDiagrams.Monoidal
import Tengoku.Seed.CategoryTheory.Monoidal.Rigid.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Temperley–Lieb category is monoidal, and one strand is self-dual

The Temperley–Lieb signature is monoidal and even, so the presented category
`TemperleyLieb.TL R δ` is a strict monoidal `R`-linear category. The tensor product of objects
adds numbers of strands (`TL.obj_tensor`).

The cup `𝟙_ ⟶ X ⊗ X` and the cap `X ⊗ X ⟶ 𝟙_` on one strand `X` form an exact pairing
(`TemperleyLieb.exactPairing`, Mathlib's `ExactPairing X X`): the two axioms of an exact
pairing are the zigzag relations of the presentation. In particular `X` is its own left and
right dual.
-/

noncomputable section

namespace StringDiagrams.TemperleyLieb

open CategoryTheory MonoidalCategory

instance : Inhabited sig.Region := ⟨()⟩

instance : sig.IsEven := ⟨fun _ => rfl⟩

variable (R : Type*) [CommRing R] (δ : R)

/-- The Temperley–Lieb category with loop value `δ`.-/
abbrev TL : Type _ := (pres R δ).Presented

/-- The object of `n` strands in `TL R δ`.-/
abbrev TL.obj (n : ℕ) : TL R δ := (pres R δ).obj (strands n)

set_option backward.isDefEq.respectTransparency false in
/-- Tensor product of objects adds numbers of strands.
@isnad1 id=eq.0h4v.s6.6235740d4299 from=translated src=- shape=84025777 vocab=ce3bf07a
-/
theorem TL.obj_tensor (m n : ℕ) : TL.obj R δ m ⊗ TL.obj R δ n = TL.obj R δ (m + n) := by
  rw [TL.obj, TL.obj, Presentation.obj_tensor]
  congr 1
  exact obj_ext (by simp [strands, Obj.tensor])

/-- The unit object is the empty object.
@isnad1 id=eq.0h2v.s5.62e8b88eea99 from=translated src=- shape=acf6527a vocab=0fd8ae63
-/
theorem TL.obj_zero : 𝟙_ (TL R δ) = TL.obj R δ 0 := rfl

/-- The cup `∅ → 1 ⊗ 1` in the free 2-category.-/
def cupD : (Obj.unit : Obj sig) ⟶ (strands 1).tensor (strands 1) :=
  dcup (m := 0) (i := 0) le_rfl

/-- The cap `1 ⊗ 1 → ∅` in the free 2-category.-/
def capD : (strands 1).tensor (strands 1) ⟶ (Obj.unit : Obj sig) :=
  dcap (m := 0) (i := 0) le_rfl

/--
@isnad1 id=eq.0h0v.s4.a9705ac914c4 from=translated src=- shape=8a51f230 vocab=dae37f68
-/
theorem strands_one_tensor_unit : (strands 1).tensor Obj.unit = strands 1 := rfl

/--
@isnad1 id=eq.0h0v.s4.6356d86bd96b from=translated src=- shape=0d913f39 vocab=dae37f68
-/
theorem unit_tensor_strands_one : (Obj.unit : Obj sig).tensor (strands 1) = strands 1 := rfl

/-- The zigzag `(1 ⊗ cup) ≫ (cap ⊗ 1) = 1` in the form required by `ExactPairing`.
@isnad1 id=eq.0h2v.s9.bc5d39a1713e from=translated src=- shape=362d5624 vocab=e25d96a7
-/
theorem coevaluation_evaluation :
    (pres R δ).wL (strands 1) ((pres R δ).diag cupD) ≫
        eqToHom (congrArg (pres R δ).obj
          (Obj.tensor_assoc (strands 1) (strands 1) (strands 1)).symm) ≫
          (pres R δ).wR ((pres R δ).diag capD) (strands 1) =
      eqToHom (congrArg (pres R δ).obj (Obj.tensor_unit (strands 1))) ≫
        eqToHom (congrArg (pres R δ).obj (Obj.unit_tensor (strands 1))).symm := by
  simp only [Presentation.wL_diag, Presentation.wR_diag, (pres R δ).eqToHom_obj,
    ← Presentation.diag_comp]
  rw [(pres R δ).diag_eq_of_layers_eq' _ (dcup (m := 1) (i := 1) le_rfl ≫
      dcap (m := 1) (i := 0) zero_le_one) strands_one_tensor_unit unit_tensor_strands_one ?_,
    Presentation.diag_comp, zigzagA_at δ le_rfl]
  · simp [Presentation.diag_eqToHom]
  · rfl

/-- The zigzag `(cup ⊗ 1) ≫ (1 ⊗ cap) = 1` in the form required by `ExactPairing`.
@isnad1 id=eq.0h2v.s9.7fe51079c8d6 from=translated src=- shape=14f62ce1 vocab=e25d96a7
-/
theorem evaluation_coevaluation :
    (pres R δ).wR ((pres R δ).diag cupD) (strands 1) ≫
        eqToHom (congrArg (pres R δ).obj
          (Obj.tensor_assoc (strands 1) (strands 1) (strands 1))) ≫
          (pres R δ).wL (strands 1) ((pres R δ).diag capD) =
      eqToHom (congrArg (pres R δ).obj (Obj.unit_tensor (strands 1))) ≫
        eqToHom (congrArg (pres R δ).obj (Obj.tensor_unit (strands 1))).symm := by
  simp only [Presentation.wL_diag, Presentation.wR_diag, (pres R δ).eqToHom_obj,
    ← Presentation.diag_comp]
  rw [(pres R δ).diag_eq_of_layers_eq' _ (dcup (m := 1) (i := 0) zero_le_one ≫
      dcap (m := 1) (i := 1) le_rfl) unit_tensor_strands_one strands_one_tensor_unit ?_,
    Presentation.diag_comp, zigzagB_at δ le_rfl]
  · simp [Presentation.diag_eqToHom]
  · rfl

/-- One strand is self-dual: the cup and the cap form an exact pairing.-/
instance exactPairing : ExactPairing (TL.obj R δ 1) (TL.obj R δ 1) where
  coevaluation' := (pres R δ).diag cupD
  evaluation' := (pres R δ).diag capD
  coevaluation_evaluation' := coevaluation_evaluation R δ
  evaluation_coevaluation' := evaluation_coevaluation R δ

/-- The coevaluation of the exact pairing is the cup.
@isnad1 id=eq.0h2v.s8.6fe20588d2fe from=translated src=- shape=0a68ba33 vocab=2995dbae
-/
theorem coevaluation_eq : η_ (TL.obj R δ 1) (TL.obj R δ 1) = (pres R δ).diag cupD := rfl

/-- The evaluation of the exact pairing is the cap.
@isnad1 id=eq.0h2v.s8.44bef5d52e53 from=translated src=- shape=3a8a5b0e vocab=5436af45
-/
theorem evaluation_eq : ε_ (TL.obj R δ 1) (TL.obj R δ 1) = (pres R δ).diag capD := rfl

/-- The loop value: evaluation after coevaluation is `δ`.
@isnad1 id=eq.0h2v.s11.386586255363 from=translated src=- shape=63062da7 vocab=d071f340
-/
theorem coevaluation_comp_evaluation :
    η_ (TL.obj R δ 1) (TL.obj R δ 1) ≫ ε_ (TL.obj R δ 1) (TL.obj R δ 1) = δ • 𝟙 (𝟙_ (TL R δ)) :=
  loop_at δ (m := 0) (i := 0) le_rfl

end StringDiagrams.TemperleyLieb

end

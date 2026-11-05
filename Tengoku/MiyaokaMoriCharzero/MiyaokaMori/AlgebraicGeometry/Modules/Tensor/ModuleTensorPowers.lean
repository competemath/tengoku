import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Tensor powers and coefficient modules on the same scheme

The tensor module is the sheafification of Mathlib's sectionwise tensor presheaf.
Its canonical unit sends a pure tensor of sections to a section of that sheaf and
commutes with restriction. This does not assert that every section is a pure tensor.

Natural powers start with the actual structure module. Negative powers mean natural
powers of the existing `moduleSheafDual`, and the coefficient module is the tensor
of the given target module with this negative power. Pullback coefficients use the
actual `Scheme.Modules.pullback` functor. These constructions make sense for every
scheme and every module sheaf, including zero modules and the empty scheme.

The section formulas concern the specified sections themselves. Local freeness,
evaluation isomorphisms, the extraction of coefficients from a jet, and all degree
comparisons remain separate obligations. No statement about degrees is imported.

Sources: Stacks Project, `modules.tex`,
`section-tensor-product` (the tensor presheaf and its associated sheaf), and the
dual construction in `section-internal-hom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}}

/-- The actual tensor presheaf of the two modules over the same structure sheaf.-/
def moduleTensorPresheaf (M N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val

/-- The tensor module is the associated sheaf of the sectionwise tensor presheaf.-/
def moduleTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (moduleTensorPresheaf M N)

/-- The canonical unit from the tensor presheaf into its own sheafification.-/
def moduleTensorSheafificationUnit (M N : X.Modules) :
    moduleTensorPresheaf M N ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        ((Scheme.Modules.toPresheafOfModules X).obj (moduleTensor M N)) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (moduleTensorPresheaf M N)

variable {M N : X.Modules}

/-- Send a pure tensor of sections to the tensor module using its sheafification unit.-/
def moduleTensorSection {U : X.Opens} (s : Γ(M, U)) (t : Γ(N, U)) :
    Γ(moduleTensor M N, U) :=
  (moduleTensorSheafificationUnit M N).app (op U) (s ⊗ₜ[Γ(X, U)] t)

/-- Restricting the tensor section restricts both of its original factors.
@isnad1 id=eq.0h8v.s12.059f6afb33a2 from=translated src=- shape=aba4b747 vocab=9778c16d
-/
@[simp]
theorem moduleTensorSection_restrict {U V : X.Opens} (j : V ⟶ U)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (moduleTensor M N).presheaf.map j.op (moduleTensorSection s t) =
      moduleTensorSection (M.presheaf.map j.op s) (N.presheaf.map j.op t) := by
  exact (PresheafOfModules.naturality_apply (moduleTensorSheafificationUnit M N)
    j.op (s ⊗ₜ[Γ(X, U)] t)).symm

/-- The tensor section is additive in its first factor.
@isnad1 id=eq.0h7v.s11.d389c7dbd48b from=translated src=- shape=fec4dde0 vocab=f9f89587
-/
theorem moduleTensorSection_add_left {U : X.Opens}
    (s s' : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorSection (s + s') t = moduleTensorSection s t + moduleTensorSection s' t := by
  unfold moduleTensorSection
  erw [TensorProduct.add_tmul]
  exact ((moduleTensorSheafificationUnit M N).app (op U)).hom.map_add _ _

/-- The tensor section is additive in its second factor.
@isnad1 id=eq.0h7v.s11.4da9f23aa69f from=translated src=- shape=6889d699 vocab=f9f89587
-/
theorem moduleTensorSection_add_right {U : X.Opens}
    (s : Γ(M, U)) (t t' : Γ(N, U)) :
    moduleTensorSection s (t + t') = moduleTensorSection s t + moduleTensorSection s t' := by
  unfold moduleTensorSection
  erw [TensorProduct.tmul_add]
  exact ((moduleTensorSheafificationUnit M N).app (op U)).hom.map_add _ _

/-- Multiplying the original two factors multiplies the tensor section by the product.
@isnad1 id=eq.0h8v.s14.0e6eb004bc4e from=translated src=- shape=c5e50f52 vocab=9cdb0669
-/
theorem moduleTensorSection_smul {U : X.Opens} (a b : Γ(X, U))
    (s : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorSection (a • s) (b • t) = (a * b) • moduleTensorSection s t := by
  unfold moduleTensorSection
  change ((moduleTensorSheafificationUnit M N).app (op U)).hom
      ((a • s) ⊗ₜ[Γ(X, U)] (b • t)) = _
  erw [TensorProduct.smul_tmul_smul]
  exact ((moduleTensorSheafificationUnit M N).app (op U)).hom.map_smul _ _

/-- Tensoring a zero section in the first factor gives the zero section.
@isnad1 id=eq.0h5v.s11.e81db674024d from=translated src=- shape=d5da7b45 vocab=708f1082
-/
@[simp]
theorem moduleTensorSection_zero_left {U : X.Opens} (t : Γ(N, U)) :
    moduleTensorSection (0 : Γ(M, U)) t = 0 := by
  unfold moduleTensorSection
  erw [TensorProduct.zero_tmul]
  exact ((moduleTensorSheafificationUnit M N).app (op U)).hom.map_zero

/-- Tensoring a zero section in the second factor gives the zero section.
@isnad1 id=eq.0h5v.s11.67032ad26d59 from=translated src=- shape=58d2b912 vocab=708f1082
-/
@[simp]
theorem moduleTensorSection_zero_right {U : X.Opens} (s : Γ(M, U)) :
    moduleTensorSection s (0 : Γ(N, U)) = 0 := by
  unfold moduleTensorSection
  erw [TensorProduct.tmul_zero]
  exact ((moduleTensorSheafificationUnit M N).app (op U)).hom.map_zero

/-- Natural tensor powers, with the structure module as the zeroth power.-/
def moduleTensorPower (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | q + 1 => moduleTensor M (moduleTensorPower M q)

/-- The negative power uses the existing canonical dual of the same module.-/
def moduleNegativePower (L : X.Modules) (q : ℕ) : X.Modules :=
  moduleTensorPower (moduleSheafDual L) q

/-- The module containing order-`q` coefficients with target module `B` and source module `L`.-/
def coefficientLineModule (B L : X.Modules) (q : ℕ) : X.Modules :=
  moduleTensor B (moduleNegativePower L q)

/-- The coefficient module formed using the actual pullback along the given scheme map.-/
def pullbackCoefficientLineModule (ρ : X ⟶ Y) (A : Y.Modules)
    (L : X.Modules) (q : ℕ) : X.Modules :=
  coefficientLineModule ((Scheme.Modules.pullback ρ).obj A) L q

/-- The tensor power of one section, with the section `1` in degree zero.-/
def moduleTensorPowerSection {U : X.Opens} (s : Γ(M, U)) :
    (q : ℕ) → Γ(moduleTensorPower M q, U)
  | 0 => (1 : Γ(X, U))
  | q + 1 => moduleTensorSection s (moduleTensorPowerSection s q)

/-- The tensor power of a section commutes with its actual restriction.
@isnad1 id=eq.0h7v.s11.d0f7ce75319b from=translated src=- shape=20661153 vocab=31685c5a
-/
@[simp]
theorem moduleTensorPowerSection_restrict {U V : X.Opens} (j : V ⟶ U)
    (s : Γ(M, U)) (q : ℕ) :
    (moduleTensorPower M q).presheaf.map j.op (moduleTensorPowerSection s q) =
      moduleTensorPowerSection (M.presheaf.map j.op s) q := by
  induction q with
  | zero => exact PresheafOfModules.unit_map_one X.ringCatSheaf.obj j.op
  | succ q ih =>
    change (moduleTensor M (moduleTensorPower M q)).presheaf.map j.op
      (moduleTensorSection s (moduleTensorPowerSection s q)) = _
    rw [moduleTensorSection_restrict, ih]
    rfl

/-- A scalar in a section's `q`th tensor power occurs to the same power `q`.
@isnad1 id=eq.0h6v.s13.bdec1db5902a from=translated src=- shape=ef93a62d vocab=206f77a6
-/
theorem moduleTensorPowerSection_smul {U : X.Opens}
    (a : Γ(X, U)) (s : Γ(M, U)) (q : ℕ) :
    moduleTensorPowerSection (a • s) q = a ^ q • moduleTensorPowerSection s q := by
  induction q with
  | zero =>
    simp only [moduleTensorPowerSection, pow_zero]
    exact (one_smul _ _).symm
  | succ q ih =>
    change moduleTensorSection (a • s) (moduleTensorPowerSection (a • s) q) =
      a ^ (q + 1) • moduleTensorSection s (moduleTensorPowerSection s q)
    rw [ih, moduleTensorSection_smul, pow_succ']

/-- A target section and a section of the same source dual give a coefficient-module section.-/
def coefficientLineSection {B L : X.Modules} {U : X.Opens}
    (b : Γ(B, U)) (α : Γ(moduleSheafDual L, U)) (q : ℕ) :
    Γ(coefficientLineModule B L q, U) :=
  moduleTensorSection b (moduleTensorPowerSection α q)

/-- The coefficient-module section restricts its specified target and dual sections.
@isnad1 id=eq.0h9v.s12.59faf8263bc1 from=translated src=- shape=5db8e3cb vocab=2cd224db
-/
@[simp]
theorem coefficientLineSection_restrict {B L : X.Modules} {U V : X.Opens}
    (j : V ⟶ U) (b : Γ(B, U)) (α : Γ(moduleSheafDual L, U)) (q : ℕ) :
    (coefficientLineModule B L q).presheaf.map j.op (coefficientLineSection b α q) =
      coefficientLineSection (B.presheaf.map j.op b)
        ((moduleSheafDual L).presheaf.map j.op α) q := by
  unfold coefficientLineSection
  change (moduleTensor B (moduleTensorPower (moduleSheafDual L) q)).presheaf.map j.op
      (moduleTensorSection b (moduleTensorPowerSection α q)) = _
  erw [moduleTensorSection_restrict, moduleTensorPowerSection_restrict]
  rfl

/-- The coefficient-module section has the target weight and the `q`th dual weight.
@isnad1 id=eq.0h9v.s14.7ebe53c0fb7e from=translated src=- shape=10e4b14d vocab=3493f877
-/
theorem coefficientLineSection_smul {B L : X.Modules} {U : X.Opens}
    (v u : Γ(X, U)) (b : Γ(B, U)) (α : Γ(moduleSheafDual L, U)) (q : ℕ) :
    coefficientLineSection (v • b) (u • α) q =
      (v * u ^ q) • coefficientLineSection b α q := by
  unfold coefficientLineSection
  erw [moduleTensorPowerSection_smul, moduleTensorSection_smul]
  rfl

/-- For actual rescaled target and dual sections, the inverse source unit has weight `-q`.

This is an equality of specified sections; it does not assert that they are local frames.
@isnad1 id=eq.0h9v.s14.4738ff8b941f from=translated src=- shape=f4908f5b vocab=5ba54e89
-/
theorem coefficientLineSection_unit_change {B L : X.Modules} {U : X.Opens}
    (u v : Γ(X, U)ˣ) (b : Γ(B, U)) (α : Γ(moduleSheafDual L, U)) (q : ℕ) :
    coefficientLineSection ((v : Γ(X, U)) • b) (((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) • α) q =
      ((v : Γ(X, U)) * ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) ^ q) •
        coefficientLineSection b α q :=
  coefficientLineSection_smul _ _ b α q

end AlgebraicGeometry.Scheme.Modules

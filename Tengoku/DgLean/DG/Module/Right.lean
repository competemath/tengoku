import Tengoku.DgLean.DG.Module.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Right differential graded modules and bimodules

Following Mathlib, a right `A`-module is a module over the multiplicative opposite,
`Module Aᵐᵒᵖ M`, the right action `m • a` being written `MulOpposite.op a • m`. This file
defines the corresponding dg notions as `Prop`-valued mixins on the same data as left modules.

* `DGRightModule A M`: for `[Module Aᵐᵒᵖ M] [DGAddCommGroup M]`, the action is graded
  (`Mʲ • Aⁱ ⊆ Mʲ⁺ⁱ`) and satisfies the right-handed Leibniz rule
  `d (m • a) = d m • a + (-1)^{|m|} • (m • d a)`, i.e. in opposite notation
  `d (op a • m) = op a • d m + (-1)^{|m|} • (op (d a) • m)` for `m` homogeneous of degree
  `|m|`.
* `DGBimodule A B M`: a left dg `A`-module structure and a right dg `B`-module structure whose
  actions commute (`SMulCommClass A Bᵐᵒᵖ M`).

A dg ring is a right dg module over itself and a dg bimodule over itself. If `A` is a dg
`R`-algebra and the right action extends the `R`-action (`IsScalarTower R Aᵐᵒᵖ M`), then `d`
is `R`-linear and the graded pieces are `R`-submodules.

The identification of right dg `A`-modules with left dg modules over the (signed) opposite dg
ring `Aᵒᵖ` is not part of this file.
-/

open scoped DG

open DirectSum MulOpposite

namespace DG

/-- A right differential graded module over a dg ring `A`: a dg abelian group `M` with a right
`A`-module structure (`Module Aᵐᵒᵖ M`, the action `m • a` being `op a • m`) such that the
action is graded, `Mʲ • Aⁱ ⊆ Mʲ⁺ⁱ`, and satisfies the right-handed signed Leibniz rule
`d (m • a) = d m • a + (-1)^{|m|} • (m • d a)`, written with the opposite action as
`d (op a • m) = op a • d m + (-1)^{|m|} • (op (d a) • m)`.-/
class DGRightModule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [AddCommGroup M]
    [DGAddCommGroup M] [Module Aᵐᵒᵖ M] : Prop where
  op_smul_mem' : ∀ {i j : ℤ} {a : A} {m : M}, a ∈ grading i → m ∈ grading j →
    op a • m ∈ grading (j + i)
  d_op_smul' : ∀ {j : ℤ} {m : M}, m ∈ grading j → ∀ a : A,
    d (op a • m) = op a • d m + koszulSign j • (op (d a) • m)

section DGRightModule

variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module Aᵐᵒᵖ M] [DGRightModule A M]

/-- The right action is graded: `Mʲ • Aⁱ ⊆ Mʲ⁺ⁱ`.
@isnad1 id=mem.2h6v.s7.2de7d37d62d6 from=translated src=- shape=75b8de60 vocab=972cc380
-/
theorem op_smul_mem_grading {i j : ℤ} {a : A} {m : M} (ha : a ∈ grading i)
    (hm : m ∈ grading j) : op a • m ∈ grading (j + i) :=
  DGRightModule.op_smul_mem' ha hm

/-- The right action is graded, with the degrees added in the other order.
@isnad1 id=mem.2h6v.s7.756e7dafb011 from=translated src=- shape=3191e8e4 vocab=972cc380
-/
theorem op_smul_mem_grading' {i j : ℤ} {a : A} {m : M} (ha : a ∈ grading i)
    (hm : m ∈ grading j) : op a • m ∈ grading (i + j) := by
  rw [add_comm]; exact op_smul_mem_grading ha hm

/-- The right-handed signed Leibniz rule, `d (m • a) = d m • a + (-1)^{|m|} • (m • d a)`.
@isnad1 id=eq.1h5v.s9.e9eb44124a36 from=translated src=- shape=45238b45 vocab=53d2fd4a
-/
theorem d_op_smul {j : ℤ} {m : M} (hm : m ∈ grading j) (a : A) :
    d (op a • m) = op a • d m + koszulSign j • (op (d a) • m) :=
  DGRightModule.d_op_smul' hm a

/--
@isnad1 id=eq.2h5v.s8.efdf4170454e from=translated src=- shape=53e669fe vocab=937258a2
-/
theorem d_op_smul_of_even {j : ℤ} {m : M} (hm : m ∈ grading j) (hj : Even j) (a : A) :
    d (op a • m) = op a • d m + op (d a) • m := by
  rw [d_op_smul hm, koszulSign_even hj, one_smul]

/--
@isnad1 id=eq.2h5v.s8.e72b3661a764 from=translated src=- shape=53e669fe vocab=b6df4a00
-/
theorem d_op_smul_of_odd {j : ℤ} {m : M} (hm : m ∈ grading j) (hj : Odd j) (a : A) :
    d (op a • m) = op a • d m - op (d a) • m := by
  rw [d_op_smul hm, koszulSign_odd hj, Units.neg_smul, one_smul, sub_eq_add_neg]

/--
@isnad1 id=eq.1h4v.s8.0d021c9081eb from=translated src=- shape=6b4a4148 vocab=49bc22fb
-/
theorem d_op_smul_of_mem_zero {m : M} (hm : m ∈ grading 0) (a : A) :
    d (op a • m) = op a • d m + op (d a) • m :=
  d_op_smul_of_even hm Even.zero a

/-- For a cocycle `a`, `d (m • a) = d m • a`.
@isnad1 id=eq.2h5v.s8.04cfca734f06 from=translated src=- shape=ae835680 vocab=e2298d65
-/
theorem d_op_smul_of_d_eq_zero {j : ℤ} {m : M} (hm : m ∈ grading j) {a : A} (hda : d a = 0) :
    d (op a • m) = op a • d m := by
  rw [d_op_smul hm, hda, op_zero, zero_smul, smul_zero, add_zero]

/-- For a cocycle `a`, `d (m • a) = d m • a` for every `m` (not necessarily homogeneous).
@isnad1 id=eq.1h4v.s8.246f2e5fb650 from=translated src=- shape=5ab23f14 vocab=5dd8f146
-/
theorem d_op_smul_of_d_eq_zero' {a : A} (hda : d a = 0) (m : M) :
    d (op a • m) = op a • d m := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous m => exact d_op_smul_of_d_eq_zero m.2 hda
  | h_add m m' hm hm' => rw [smul_add, d_add, hm, hm', d_add, smul_add]

/-- A dg ring is a right dg module over itself, via `op a • b = b * a`.
@isnad1 id=dgrightm.0h1v.s4.2de45e555d3b from=translated src=- shape=85c10a67 vocab=b04c09f4
-/
instance DGRightModule.regular {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] :
    DGRightModule A A where
  op_smul_mem' ha hb := by rw [op_smul_eq_mul]; exact mul_mem_grading hb ha
  d_op_smul' hb a := by simp only [op_smul_eq_mul]; exact d_mul hb a

end DGRightModule

section Ground

variable (R : Type*) (A : Type*) {M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [DGAddCommGroup A] [DGRing A] [DGAlgebra R A] [AddCommGroup M] [DGAddCommGroup M]
  [Module Aᵐᵒᵖ M] [DGRightModule A M] [Module R M] [IsScalarTower R Aᵐᵒᵖ M]

include A

variable {R} in
/--
@isnad1 id=mem.1h6v.s8.2cf5d2bfb902 from=translated src=- shape=4a1a579a vocab=07cba186
-/
theorem DGRightModule.ground_smul_mem {n : ℤ} (r : R) {m : M} (hm : m ∈ grading n) :
    r • m ∈ grading n := by
  rw [← algebraMap_smul Aᵐᵒᵖ r m, MulOpposite.algebraMap_apply]
  simpa using op_smul_mem_grading (algebraMap_mem_grading R (A := A) r) hm

variable {R} in
/-- The differential of a right dg module over a dg `R`-algebra is `R`-linear.
@isnad1 id=eq.0h5v.s8.b7dc8c7d35bf from=translated src=- shape=c912e12f vocab=f8a0dc49
-/
theorem DGRightModule.d_ground_smul (r : R) (m : M) : d (r • m) = r • d m := by
  rw [← algebraMap_smul Aᵐᵒᵖ r m, MulOpposite.algebraMap_apply,
    d_op_smul_of_d_eq_zero' (d_algebraMap R r), ← MulOpposite.algebraMap_apply, algebraMap_smul]

variable (M)

/-- The graded pieces of a right dg module over a dg `R`-algebra, as `R`-submodules.-/
def DGRightModule.gradingSubmodule (n : ℤ) : Submodule R M where
  __ := grading (M := M) n
  smul_mem' r _ hm := DGRightModule.ground_smul_mem A r hm

/--
@isnad1 id=iff.0h5v.s8.63e7e8bfcfe7 from=translated src=- shape=4a71a468 vocab=a046e5b5
-/
@[simp]
theorem DGRightModule.mem_gradingSubmodule {n : ℤ} {m : M} :
    m ∈ DGRightModule.gradingSubmodule R A M n ↔ m ∈ grading n :=
  Iff.rfl

instance DGRightModule.decompositionSubmodule :
    DirectSum.Decomposition (DGRightModule.gradingSubmodule R A M) where
  decompose' := DirectSum.decompose (grading (M := M))
  left_inv := DirectSum.Decomposition.left_inv (ℳ := grading (M := M))
  right_inv := DirectSum.Decomposition.right_inv (ℳ := grading (M := M))

/-- The differential of a right dg module over a dg `R`-algebra as an `R`-linear map.-/
def DGRightModule.dLinear : M →ₗ[R] M where
  __ := (d : M →+ M)
  map_smul' := DGRightModule.d_ground_smul A

/--
@isnad1 id=eq.0h4v.s8.9ad99df72f34 from=translated src=- shape=a7d94848 vocab=4abdcce6
-/
@[simp]
theorem DGRightModule.dLinear_apply (m : M) : DGRightModule.dLinear R A M m = d m := rfl

end Ground

/-- A differential graded `(A, B)`-bimodule: a left dg `A`-module and a right dg `B`-module
(`Module Bᵐᵒᵖ M`) whose actions commute, `a • (m • b) = (a • m) • b`.-/
class DGBimodule (A : Type*) (B : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [Ring B]
    [DGAddCommGroup B] [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] : Prop
    extends DGModule A M, DGRightModule B M, SMulCommClass A Bᵐᵒᵖ M

section DGBimodule

variable {A : Type*} {B : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [Ring B]
  [DGAddCommGroup B] [AddCommGroup M] [DGAddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]

/-- A left dg `A`-module and a right dg `B`-module with commuting actions form a dg
`(A, B)`-bimodule.
@isnad1 id=dgbimodu.0h3v.s7.40dc06d8b823 from=translated src=- shape=0c8024d2 vocab=27af726c
-/
theorem DGBimodule.mk' [DGModule A M] [DGRightModule B M] [SMulCommClass A Bᵐᵒᵖ M] :
    DGBimodule A B M :=
  { (inferInstance : DGModule A M), (inferInstance : DGRightModule B M),
    (inferInstance : SMulCommClass A Bᵐᵒᵖ M) with }

/--
@isnad1 id=eq.0h6v.s8.4609c71d2ccf from=translated src=- shape=564a3918 vocab=51d045d7
-/
theorem DGBimodule.smul_op_smul [DGBimodule A B M] (a : A) (b : B) (m : M) :
    a • (op b • m) = op b • (a • m) :=
  smul_comm a (op b) m

/-- A dg ring is a dg bimodule over itself.
@isnad1 id=dgbimodu.0h1v.s5.0095bbd1df61 from=translated src=- shape=753a43af vocab=15024465
-/
instance DGBimodule.regular {A : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] :
    DGBimodule A A A :=
  DGBimodule.mk'

end DGBimodule

end DG

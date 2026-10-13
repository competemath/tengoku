/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Renaming.Defs
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Renaming.Internal

/-!
# Capture-avoiding relation renaming

Arity-preserving relation renaming preserves satisfaction under the pulled-back
environment, exact syntactic size, FO matrices, and existential SO prefixes.
Identity and composition hold as equalities of formulas. Weakening inserts an
unused relation binder, which is the basic operation for merging SO witnesses.
-/

public section

namespace Complexity.DescriptiveComplexity

namespace RelRenaming

/-- A relation renaming is determined by its map on indices.
@isnad1 id=eq.1h4v.s5.ebae4b5801ef from=translated src=- shape=7e3d1ed7 vocab=4cbca5ca
-/
@[ext] theorem ext {rctx sctx : List Nat} (f g : RelRenaming rctx sctx)
    (h : f.index = g.index) : f = g := relRenaming_ext_internal f g h

/-- Lifting fixes the identity renaming.
@isnad1 id=eq.0h2v.s4.a353ba6b3c0b from=translated src=- shape=9f0b413e vocab=82f2b339
-/
@[simp] theorem lift_id (rctx : List Nat) (k : Nat) :
    (RelRenaming.id rctx).lift k = RelRenaming.id (k :: rctx) := lift_id_internal rctx k

/-- Lifting commutes with composition.
@isnad1 id=eq.0h6v.s5.8166e2bad4b4 from=translated src=- shape=7edf5c16 vocab=51261316
-/
theorem lift_comp {rctx sctx tctx : List Nat} (g : RelRenaming sctx tctx)
    (f : RelRenaming rctx sctx) (k : Nat) :
    (g.comp f).lift k = (g.lift k).comp (f.lift k) := lift_comp_internal g f k

/-- Pulling an environment through the identity does nothing.
@isnad1 id=eq.0h3v.s4.7535c0702373 from=translated src=- shape=bc8f2578 vocab=548f4018
-/
@[simp] theorem pull_id {card : Nat} {rctx : List Nat} (ρ : REnv card rctx) :
    (RelRenaming.id rctx).pull ρ = ρ := rfl

/-- Pullback reverses the order of composition.
@isnad1 id=eq.0h7v.s5.ea34a18020bf from=translated src=- shape=574dcdba vocab=38c8002e
-/
theorem pull_comp {rctx sctx tctx : List Nat} (g : RelRenaming sctx tctx)
    (f : RelRenaming rctx sctx) {card : Nat} (ρ : REnv card tctx) :
    (g.comp f).pull ρ = f.pull (g.pull ρ) := rfl

/-- A lifted renaming preserves the freshly bound relation.
@isnad1 id=eq.0h7v.s6.5d6d40d9b0d6 from=translated src=- shape=9743fd53 vocab=198d8b41
-/
@[simp] theorem pull_lift_rCons {rctx sctx : List Nat} (f : RelRenaming rctx sctx)
    {card k : Nat} (S : (Fin k → Fin card) → Prop) (ρ : REnv card sctx) :
    (f.lift k).pull (rCons S ρ) = rCons S (f.pull ρ) := pull_lift_internal f S ρ

/-- Weakening ignores the freshly bound relation.
@isnad1 id=eq.0h5v.s5.e6a9adf873aa from=translated src=- shape=ba6a7f9e vocab=d9d74c0e
-/
@[simp] theorem pull_weaken_rCons {rctx : List Nat} {card k : Nat}
    (S : (Fin k → Fin card) → Prop) (ρ : REnv card rctx) :
    (RelRenaming.weaken rctx k).pull (rCons S ρ) = ρ := pull_weaken_internal S ρ

end RelRenaming

namespace SOFormula

variable {V : Vocabulary} {rctx sctx tctx : List Nat} {n : Nat}

/-- Satisfaction after relation renaming is satisfaction in the pulled-back environment.
@isnad1 id=iff.0h9v.s6.e06f0ef3fc90 from=translated src=- shape=eef1919e vocab=96e14c25
-/
theorem renameRel_sat (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx)
    (A : FinStruct V) (σ : Env A.card n) (ρ : REnv A.card sctx) :
    (φ.renameRel f).Sat A σ ρ ↔ φ.Sat A σ (f.pull ρ) :=
  renameRel_sat_internal φ f A σ ρ

/-- Inserting an unused relation variable leaves satisfaction unchanged.
@isnad1 id=iff.0h9v.s6.99313335eaca from=translated src=- shape=c1f9695b vocab=1d24ed77
-/
theorem renameRel_weaken_sat (φ : SOFormula V rctx n) (A : FinStruct V)
    (σ : Env A.card n) (ρ : REnv A.card rctx) {k : Nat}
    (S : (Fin k → Fin A.card) → Prop) :
    (φ.renameRel (RelRenaming.weaken rctx k)).Sat A σ (rCons S ρ) ↔ φ.Sat A σ ρ := by
  rw [renameRel_sat, RelRenaming.pull_weaken_rCons]

/-- Relation renaming leaves the number of syntax nodes unchanged.
@isnad1 id=eq.0h6v.s5.8a8e05aec792 from=translated src=- shape=b13422a6 vocab=16c9afb2
-/
@[simp] theorem size_renameRel (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).size = φ.size := size_renameRel_internal φ f

/-- Relation renaming preserves and reflects being an FO matrix.
@isnad1 id=iff.0h6v.s5.3764f4e1b25c from=translated src=- shape=3ba465c3 vocab=bb99ff64
-/
@[simp] theorem isFOMatrix_renameRel (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).IsFOMatrix ↔ φ.IsFOMatrix := isFOMatrix_renameRel_internal φ f

/-- Relation renaming preserves and reflects existential SO prefix form.
@isnad1 id=iff.0h6v.s5.d4419aeed075 from=translated src=- shape=3ba465c3 vocab=c38e06d6
-/
@[simp] theorem isExistSO_renameRel (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).IsExistSO ↔ φ.IsExistSO := isExistSO_renameRel_internal φ f

/-- Identity renaming fixes the formula exactly.
@isnad1 id=eq.0h4v.s4.4c8302e3a2d4 from=translated src=- shape=c346728c vocab=40862a19
-/
@[simp] theorem renameRel_id (φ : SOFormula V rctx n) :
    φ.renameRel (RelRenaming.id rctx) = φ := renameRel_id_internal φ

/-- Successive relation renamings equal their composite.
@isnad1 id=eq.0h8v.s5.e9c7e4b474a9 from=translated src=- shape=0bfcf5da vocab=0a2b24cd
-/
theorem renameRel_comp (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx)
    (g : RelRenaming sctx tctx) :
    (φ.renameRel f).renameRel g = φ.renameRel (g.comp f) := renameRel_comp_internal φ f g

end SOFormula

end Complexity.DescriptiveComplexity

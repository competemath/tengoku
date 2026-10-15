/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.Correlation
public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000Relaxation

open scoped BigOperators

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Witness
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Distributed2Coloring.LowerBound.Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var

noncomputable instance : Fintype G := by infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev LabelTriple := N1000000Witness.LabelTriple

instance : NeZero n := ⟨by
  -- `n = 10^6`.
  decide⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def symOfNat (k : Nat) : SymN :=
  Fin.ofNat n k

/--
@isnad1 id=eq.3h2v.s4.da06b73eab05 from=translated src=- shape=fce08944 vocab=53da9dd2
-/
lemma symOfNat_injective_of_lt {a b : Nat} (ha : a < n) (hb : b < n) :
    symOfNat a = symOfNat b → a = b := by
  intro hab
  have hval : a % n = b % n := by simpa [symOfNat] using congrArg Fin.val hab
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hval

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def labelGet (t : LabelTriple) (i : Fin 3) : SymN :=
  match i.1 with
  | 0 => symOfNat t.1
  | 1 => symOfNat t.2.1
  | _ => symOfNat t.2.2

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def tupleOfLabels (t : LabelTriple) : Tuple 3 n :=
  fun i => labelGet t i

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def labelGetNat (t : LabelTriple) (i : Fin 3) : Nat :=
  match i.1 with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

/--
@isnad1 id=eq.0h2v.s4.781b3a62ad70 from=translated src=- shape=c9c1d1f3 vocab=ae7f523c
-/
lemma labelGet_eq_symOfNat_labelGetNat (t : LabelTriple) (i : Fin 3) :
    labelGet t i = symOfNat (labelGetNat t i) := by
  fin_cases i <;> rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LabelsDistinct (t : LabelTriple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance (t : LabelTriple) : Decidable (LabelsDistinct t) := by
  unfold LabelsDistinct
  infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def LabelsInRange (t : LabelTriple) : Prop :=
  t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n

instance (t : LabelTriple) : Decidable (LabelsInRange t) := by
  unfold LabelsInRange
  infer_instance

/--
@isnad1 id=lt.1h2v.s4.29f6d56fca7a from=translated src=- shape=03cef256 vocab=c05133e0
-/
lemma labelGetNat_lt (t : LabelTriple) (hr : LabelsInRange (t := t)) (i : Fin 3) :
    labelGetNat t i < n := by
  fin_cases i
  · simpa [labelGetNat] using hr.1
  · simpa [labelGetNat] using hr.2.1
  · simpa [labelGetNat] using hr.2.2

/--
@isnad1 id=injectiv.1h1v.s3.b94b2ab9330a from=translated src=- shape=bace3479 vocab=d66cd1d2
-/
lemma labelGetNat_injective_of_labelsDistinct (t : LabelTriple) (h : LabelsDistinct t) :
    Function.Injective (labelGetNat t) := by
  intro i j hij
  obtain ⟨h1, h2, h3⟩ := h
  fin_cases i <;> fin_cases j <;>
    simp_all [labelGetNat, eq_comm]

/--
@isnad1 id=injectiv.2h1v.s4.36b268f66ea8 from=translated src=- shape=f09e0ad6 vocab=75b89189
-/
lemma tupleOfLabels_injective_of_labelsDistinct (t : LabelTriple) (h : LabelsDistinct t)
    (hr : LabelsInRange (t := t)) :
    Function.Injective (tupleOfLabels t) := by
  intro i j hij
  have hijSym : symOfNat (labelGetNat t i) = symOfNat (labelGetNat t j) := by
    simpa [tupleOfLabels, labelGet_eq_symOfNat_labelGetNat] using hij
  exact labelGetNat_injective_of_labelsDistinct (t := t) h
    (symOfNat_injective_of_lt (labelGetNat_lt (t := t) hr i) (labelGetNat_lt (t := t) hr j) hijSym)

/--
@isnad1 id=injectiv.0h1v.s5.4ccb39c06a31 from=translated src=- shape=87a02855 vocab=02568d65
-/
theorem varRepU_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepU[i.1]!)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

/--
@isnad1 id=injectiv.0h1v.s5.cee57c0f42c3 from=translated src=- shape=87a02855 vocab=cfaffbde
-/
theorem varRepV_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepV[i.1]!)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepUAt (i : Var) : LabelTriple :=
  varRepU[i.1]!

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev varRepVAt (i : Var) : LabelTriple :=
  varRepV[i.1]!

/--
@isnad1 id=labelsdi.0h1v.s2.88b884accfc1 from=translated src=- shape=76a08d12 vocab=61b666bd
-/
theorem varRepUAt_labelsDistinct (i : Var) : LabelsDistinct (varRepUAt i) := by
  fin_cases i <;> decide

/--
@isnad1 id=labelsdi.0h1v.s2.f8a2255d4942 from=translated src=- shape=76a08d12 vocab=18933efa
-/
theorem varRepVAt_labelsDistinct (i : Var) : LabelsDistinct (varRepVAt i) := by
  fin_cases i <;> decide

/--
@isnad1 id=labelsin.0h1v.s2.e2e967c44211 from=translated src=- shape=76a08d12 vocab=98e3fcac
-/
theorem varRepUAt_labelsInRange (i : Var) : LabelsInRange (varRepUAt i) := by fin_cases i <;> decide

/--
@isnad1 id=labelsin.0h1v.s2.9fbd58422b14 from=translated src=- shape=76a08d12 vocab=f03da991
-/
theorem varRepVAt_labelsInRange (i : Var) : LabelsInRange (varRepVAt i) := by fin_cases i <;> decide

/--
@isnad1 id=injectiv.0h1v.s3.4eb8ff8bb4ba from=translated src=- shape=9fb9fa4f vocab=ab4a50d0
-/
theorem varRepUAt_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepUAt i)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

/--
@isnad1 id=injectiv.0h1v.s3.1db5ee4b90ad from=translated src=- shape=9fb9fa4f vocab=7c093a9d
-/
theorem varRepVAt_injective : ∀ i : Var, Function.Injective (tupleOfLabels (varRepVAt i)) := by
  intro i
  fin_cases i <;> exact tupleOfLabels_injective_of_labelsDistinct _ (by decide) (by decide)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varRepVertexU (i : Var) : Vertex n :=
  ⟨tupleOfLabels (varRepUAt i), varRepUAt_injective i⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def varRepVertexV (i : Var) : Vertex n :=
  ⟨tupleOfLabels (varRepVAt i), varRepVAt_injective i⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def xFromColoring (f : Coloring n) : Var → Q :=
  fun i => corrAvg (n := n) f (varRepVertexU i) (varRepVertexV i)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeVarVar : Var :=
  ⟨edgeVar, by decide⟩

-- A concrete representative edge `((3,0,1) -> (0,1,2))`, encoded as a 4-tuple `(3,0,1,2)`.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeRepTuple : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => symOfNat 3
    | 1 => symOfNat 0
    | 2 => symOfNat 1
    | _ => symOfNat 2

/--
@isnad1 id=injectiv.0h0v.s3.07600ce6b00d from=translated src=- shape=b032868b vocab=90d2199b
-/
lemma edgeRepTuple_injective : Function.Injective edgeRepTuple := by
  intro i j hij
  have hmod0 : (0 : Nat) % n = 0 := Nat.mod_eq_of_lt (by decide : (0 : Nat) < n)
  have hmod1 : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt (by decide : (1 : Nat) < n)
  have hmod2 : (2 : Nat) % n = 2 := Nat.mod_eq_of_lt (by decide : (2 : Nat) < n)
  have hmod3 : (3 : Nat) % n = 3 := Nat.mod_eq_of_lt (by decide : (3 : Nat) < n)
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exact absurd (congrArg Fin.val hij)
        (by simp [edgeRepTuple, symOfNat, hmod0, hmod1, hmod2, hmod3]))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def edgeRep : Edge n :=
  ⟨edgeRepTuple, edgeRepTuple_injective⟩

/--
@isnad1 id=eq.0h0v.s3.ac669a85a094 from=translated src=- shape=2c256329 vocab=968ca03c
-/
theorem edgeRep_src : Edge.src edgeRep = varRepVertexV edgeVarVar := by
  have hV : varRepVAt edgeVarVar = (3, 0, 1) := by decide
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.src, Edge.srcIndex, edgeRep, edgeRepTuple, varRepVertexV, varRepVAt, tupleOfLabels,
      Distributed2Coloring.LowerBound.N1000000Relaxation.labelGet,
      Distributed2Coloring.LowerBound.N1000000Relaxation.symOfNat, hV]

/--
@isnad1 id=eq.0h0v.s3.29554e0f32bd from=translated src=- shape=2c256329 vocab=903facd9
-/
theorem edgeRep_dst : Edge.dst edgeRep = varRepVertexU edgeVarVar := by
  have hU : varRepUAt edgeVarVar = (0, 1, 2) := by decide
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [Edge.dst, Edge.dstIndex, edgeRep, edgeRepTuple, varRepVertexU, varRepUAt, tupleOfLabels,
      Distributed2Coloring.LowerBound.N1000000Relaxation.labelGet,
      Distributed2Coloring.LowerBound.N1000000Relaxation.symOfNat, hU]

/-!
This file currently defines the reduced orbit variables `xFromColoring` and the concrete edge
representative `edgeRep`.  The remaining objective link

`xEdge (xFromColoring f) = edgeCorrelation f`

is deferred to a separate module (it uses orbit-stabilizer / pretransitivity for the action of
`Sym(n)` on `Edge n`).
-/

end N1000000Relaxation

end Distributed2Coloring.LowerBound

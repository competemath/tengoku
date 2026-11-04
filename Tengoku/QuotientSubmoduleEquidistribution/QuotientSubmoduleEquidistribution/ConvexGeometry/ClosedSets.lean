import Tengoku.Seed.Order.Grade
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The lattice of closed sets

Every closure system is a complete lattice.  For a finite anti-exchange
closure system, cardinality is a grading: every cover adds exactly one
point.
-/

open Set

namespace QuotientSubmoduleEquidistribution.SetClosure

variable {E : Type*}

/-- The complete lattice structure transported along the Galois insertion
from closed sets to all subsets.-/
noncomputable instance instCompleteLatticeCloseds (c : SetClosure E) :
    CompleteLattice c.Closeds :=
  c.gi.liftCompleteLattice

variable {c : SetClosure E}

/-- A point closure, regarded as an element of the closed-set lattice.-/
def pointClosure (c : SetClosure E) (x : E) : c.Closeds :=
  c.toCloseds ({x} : Set E)

/--
@isnad1 id=eq.0h3v.s6.81f2c2442dd7 from=translated src=- shape=0ae09a6d vocab=37a0cb61
-/
@[simp]
theorem coe_pointClosure (c : SetClosure E) (x : E) :
    (c.pointClosure x : Set E) = c ({x} : Set E) :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.8c2acb1425bc from=translated src=- shape=602a4e80 vocab=d6ec56b6
-/
@[simp]
theorem coe_bot (c : SetClosure E) :
    ((⊥ : c.Closeds) : Set E) = c ∅ :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.d9084bf3f2a9 from=translated src=- shape=6797ab69 vocab=fa7fe34e
-/
@[simp]
theorem coe_top (c : SetClosure E) :
    ((⊤ : c.Closeds) : Set E) = Set.univ :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.b8d490642ffc from=translated src=- shape=4bee63b0 vocab=e15cbe37
-/
@[simp]
theorem coe_inf (C D : c.Closeds) :
    ((C ⊓ D : c.Closeds) : Set E) = (C : Set E) ∩ (D : Set E) :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.a560fe6e9d31 from=translated src=- shape=683eef72 vocab=54213b0a
-/
@[simp]
theorem coe_sup (C D : c.Closeds) :
    ((C ⊔ D : c.Closeds) : Set E) = c ((C : Set E) ∪ (D : Set E)) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.a7891f79b4ba from=translated src=- shape=9590bf97 vocab=42fd1941
-/
@[simp]
theorem coe_iSup {ι : Sort*} (f : ι → c.Closeds) :
    ((⨆ i, f i : c.Closeds) : Set E) = c (⋃ i, (f i : Set E)) :=
  congrArg Subtype.val (c.gi.l_iSup_u f).symm

/--
@isnad1 id=eq.0h4v.s7.1aaeeb6afc87 from=translated src=- shape=e0100b0e vocab=3f2e1c4b
-/
@[simp]
theorem coe_iInf {ι : Sort*} (f : ι → c.Closeds) :
    ((⨅ i, f i : c.Closeds) : Set E) = ⋂ i, (f i : Set E) :=
  c.gi.gc.u_iInf

/--
@isnad1 id=eq.0h3v.s8.c46dd424de0e from=translated src=- shape=974f80e3 vocab=f0ee3df1
-/
@[simp]
theorem coe_sSup (S : Set c.Closeds) :
    ((sSup S : c.Closeds) : Set E) =
      c (⋃ C : S, (C.1 : Set E)) := by
  rw [sSup_eq_iSup' S, coe_iSup]

/-- A point closure lies below a closed set exactly when the point lies in
that set.
@isnad1 id=iff.0h4v.s6.f3b46772c31d from=translated src=- shape=60d8fcc2 vocab=b50afcd9
-/
theorem pointClosure_le_iff {x : E} {C : c.Closeds} :
    c.pointClosure x ≤ C ↔ x ∈ (C : Set E) := by
  change c ({x} : Set E) ⊆ (C : Set E) ↔ _
  rw [C.2.closure_le_iff, singleton_subset_iff]

/-- Distinct ground points give distinct point closures, now as elements
of the closed-set lattice.
@isnad1 id=injectiv.2h2v.s5.aff3d69f900b from=translated src=- shape=73e150b8 vocab=07db8254
-/
theorem pointClosure_injective_closeds
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    Function.Injective c.pointClosure := by
  intro x y hxy
  apply pointClosure_injective hae hempty
  exact congrArg Subtype.val hxy

/-- Every closed set is the supremum of the point closures of its
elements.
@isnad1 id=eq.0h3v.s8.c4a139e366f0 from=translated src=- shape=d36395db vocab=10d21ef4
-/
theorem iSup_pointClosure (C : c.Closeds) :
    (⨆ x : (C : Set E), c.pointClosure x.1) = C := by
  apply Subtype.ext
  rw [coe_iSup]
  have hunion :
      (⋃ x : (C : Set E), ({x.1} : Set E)) = (C : Set E) := by
    ext x
    simp
  change c (⨆ x : (C : Set E), c ({x.1} : Set E)) = (C : Set E)
  rw [c.closure_iSup_closure]
  change c (⋃ x : (C : Set E), ({x.1} : Set E)) = (C : Set E)
  rw [hunion, C.2.closure_eq]

/-- In a finite anti-exchange closure system, a cover of closed sets adds
one point.
@isnad1 id=ex.2h4v.s7.14d167d16f6e from=translated src=- shape=27ee5f8b vocab=cdd1a25c
-/
theorem covBy_eq_insert [Finite E]
    (hae : c.IsAntiExchange) {C D : c.Closeds} (hCD : C ⋖ D) :
    ∃ x : E, x ∉ (C : Set E) ∧ (D : Set E) = insert x (C : Set E) := by
  have hlt := hCD.lt
  change (C : Set E) ⊂ (D : Set E) at hlt
  obtain ⟨x, hxDC, hdel, hCdel⟩ :=
    exists_closed_sdiff_singleton_between hae C.2 D.2 hlt
  let D' : c.Closeds := ⟨(D : Set E) \ {x}, hdel⟩
  have hCD' : C ≤ D' := hCdel
  have hD'D : D' ≤ D := sdiff_subset
  have hD'ne : D' ≠ D := by
    intro heq
    have hxD' : x ∈ (D' : Set E) := by
      rw [heq]
      exact hxDC.1
    exact hxD'.2 rfl
  have hD'eq : D' = C :=
    (hCD.eq_or_eq hCD' hD'D).resolve_right hD'ne
  have hdiff : (D : Set E) \ {x} = (C : Set E) :=
    congrArg Subtype.val hD'eq
  refine ⟨x, hxDC.2, ?_⟩
  calc
    (D : Set E) = insert x ((D : Set E) \ {x}) :=
      (insert_sdiff_self_of_mem hxDC.1).symm
    _ = insert x (C : Set E) := congrArg (insert x) hdiff

/-- Cardinality increases by one across every cover.
@isnad1 id=eq.2h4v.s7.006adc035759 from=translated src=- shape=ef056ae3 vocab=cdeb6a88
-/
theorem ncard_add_one_eq_of_covBy [Finite E]
    (hae : c.IsAntiExchange) {C D : c.Closeds} (hCD : C ⋖ D) :
    (C : Set E).ncard + 1 = (D : Set E).ncard := by
  obtain ⟨x, hxC, hD⟩ := covBy_eq_insert hae hCD
  rw [hD]
  exact (ncard_insert_of_notMem hxC).symm

/-- Cardinality supplies the grading of the finite closed-set lattice.-/
@[reducible] noncomputable def gradeOrder [Finite E]
    (hae : c.IsAntiExchange) : GradeOrder ℕ c.Closeds where
  grade C := (C : Set E).ncard
  grade_strictMono := by
    intro C D hCD
    exact Set.ncard_strictMono hCD
  covBy_grade := by
    intro C D hCD
    rw [Nat.covBy_iff_add_one_eq]
    exact ncard_add_one_eq_of_covBy hae hCD

end QuotientSubmoduleEquidistribution.SetClosure

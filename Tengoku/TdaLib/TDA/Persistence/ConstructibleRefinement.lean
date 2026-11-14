import Tengoku.TdaLib.TDA.Persistence.Constructible
import Tengoku.TdaLib.TDA.Persistence.RealInterleaving
import Tengoku.Seed.Data.Finset.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Common refinements and shifted constructibility grids

A refinement retains every old critical value. Sorted finite unions construct common
grids, and finer cells lie in coarser cells. Positive evaluation shifts translate
critical values to the left, preserving the zero left tail and unbounded final cell.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits RealShift
open scoped Classical NNReal

variable {n m l : ℕ}

/-- A refinement contains every critical value of the original grid.-/
def Refines (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) : Prop := Set.range c ⊆ Set.range d

/-- Every grid refines itself.
@isnad1 id=refines.0h2v.s3.59187f5020f8 from=translated src=- shape=9ffd717f vocab=74920b8e
-/
theorem Refines.refl (c : Fin n ↪o ℝ) : Refines c c := Set.Subset.refl _

/-- Critical-value inclusion is transitive.
@isnad1 id=refines.2h6v.s5.d898247ffa9a from=translated src=- shape=dbe8c208 vocab=74920b8e
-/
theorem Refines.trans {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ} {e : Fin l ↪o ℝ}
    (h : Refines c d) (h' : Refines d e) : Refines c e := Set.Subset.trans h h'

/-- Refinement determines the increasing positions of the old critical values.-/
noncomputable def Refines.embedding {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    (h : Refines c d) : Fin n ↪o Fin m :=
  OrderEmbedding.ofStrictMono (fun i => Classical.choose (h ⟨i, rfl⟩)) (by
    intro i j hij
    apply d.lt_iff_lt.mp
    simpa only [Classical.choose_spec (h ⟨i, rfl⟩),
      Classical.choose_spec (h ⟨j, rfl⟩)] using c.strictMono hij)

/-- The derived embedding selects the same real value.
@isnad1 id=eq.1h5v.s6.84ccf0f50b37 from=translated src=- shape=f6257452 vocab=1e0f2a1e
-/
@[simp] theorem Refines.embedding_value {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    (h : Refines c d) (i : Fin n) : d (h.embedding i) = c i :=
  Classical.choose_spec (h ⟨i, rfl⟩)

/-- Strict increase makes the positions of old critical values unique.
@isnad1 id=eq.2h5v.s7.8c54c21493c8 from=translated src=- shape=5601e43c vocab=1e0f2a1e
-/
theorem Refines.embedding_unique {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    (h : Refines c d) (e : Fin n ↪o Fin m) (he : ∀ i, d (e i) = c i) : e = h.embedding := by
  apply DFunLike.ext
  intro i
  apply d.injective
  rw [he, h.embedding_value]

/-- The finite set of critical values, with no sentinel grade.-/
noncomputable def criticalValues (c : Fin n ↪o ℝ) : Finset ℝ := Finset.univ.image c

/-- The sorted union grid identifies values shared by the two input grids.-/
noncomputable def commonGrid (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) :
    Fin (criticalValues c ∪ criticalValues d).card ↪o ℝ :=
  (criticalValues c ∪ criticalValues d).orderEmbOfFin rfl

/-- The common grid contains exactly the union, rather than any extra endpoint.
@isnad1 id=eq.0h4v.s7.a552852e4cc5 from=translated src=- shape=80817580 vocab=bbaeb8f4
-/
theorem range_commonGrid (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) :
    Set.range (commonGrid c d) = Set.range c ∪ Set.range d := by
  rw [commonGrid, Finset.range_orderEmbOfFin]
  ext x
  simp [criticalValues]

/-- The sorted union refines the first grid.
@isnad1 id=refines.0h4v.s5.a5cc011abe3e from=translated src=- shape=b50b75e9 vocab=71e5c4a9
-/
theorem refines_commonGrid_left (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) :
    Refines c (commonGrid c d) := by
  intro x hx
  rw [range_commonGrid]
  exact Or.inl hx

/-- The sorted union refines the second grid.
@isnad1 id=refines.0h4v.s5.4b8e8d526438 from=translated src=- shape=0380e8bb vocab=71e5c4a9
-/
theorem refines_commonGrid_right (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) :
    Refines d (commonGrid c d) := by
  intro x hx
  rw [range_commonGrid]
  exact Or.inr hx

/-- Equality of fine cells implies equality of coarse cells, including both tails.
@isnad1 id=eq.2h6v.s9.730afc9fee50 from=translated src=- shape=7ae11b34 vocab=14ecac9b
-/
theorem cellIndex_eq_of_refines {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    (h : Refines c d) {s t : ℝ} (hd : cellIndex d s = cellIndex d t) :
    cellIndex c s = cellIndex c t := by
  have hp (i : Fin n) : c i ≤ s ↔ c i ≤ t := by
    rw [← h.embedding_value i, ← lt_cellIndex_iff d (h.embedding i) s,
      ← lt_cellIndex_iff d (h.embedding i) t, hd]
  apply Fin.ext
  change (Finset.univ.filter (fun i => c i ≤ s)).card =
    (Finset.univ.filter (fun i => c i ≤ t)).card
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hp i

variable {R : Type u} [Ring R] {M N : PModule.{u,0,w} R ℝ}

/-- Adding critical values preserves constructibility.
@isnad1 id=isconstr.2h6v.s5.1304072e6898 from=translated src=- shape=f9c68e94 vocab=67b37f91
-/
theorem IsConstructible.refine {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    (hM : IsConstructible c M) (h : Refines c d) : IsConstructible d M where
  zero_left t ht := hM.zero_left t (fun i => by
    simpa only [h.embedding_value] using ht (h.embedding i))
  isIso_map s t hst hd := hM.isIso_map s t hst (cellIndex_eq_of_refines h hd)

/-- Positive evaluation by `t+ε` moves critical values to `c_i-ε`.-/
def shiftGrid (ε : ℝ≥0) (c : Fin n ↪o ℝ) : Fin n ↪o ℝ where
  toFun i := c i - (ε : ℝ)
  inj' _ _ h := c.injective (by
    have he := congrArg (fun x : ℝ => x + (ε : ℝ)) h
    simpa only [sub_add_cancel] using he)
  map_rel_iff' := by intro i j; exact (sub_le_sub_iff_right (ε : ℝ)).trans c.le_iff_le

/-- The shifted grid has the declared negative critical-value displacement.
@isnad1 id=eq.0h4v.s6.d51420bdbffe from=translated src=- shape=b9f7f42c vocab=7ed1a68e
-/
@[simp] theorem shiftGrid_apply (ε : ℝ≥0) (c : Fin n ↪o ℝ) (i : Fin n) :
    shiftGrid ε c i = c i - (ε : ℝ) := rfl

/-- Zero shift preserves the critical grid.
@isnad1 id=eq.0h2v.s4.88c66c0cad49 from=translated src=- shape=ecd5e601 vocab=4c2c4555
-/
@[simp] theorem shiftGrid_zero (c : Fin n ↪o ℝ) : shiftGrid 0 c = c := by
  ext i
  simp

/-- Cell counts commute with the positive-evaluation shift at every parameter.
@isnad1 id=eq.0h4v.s8.9c1ccf81ddbd from=translated src=- shape=7829fc88 vocab=c3cf1994
-/
theorem cellIndex_shiftGrid (ε : ℝ≥0) (c : Fin n ↪o ℝ) (t : ℝ) :
    cellIndex (shiftGrid ε c) t = cellIndex c (t + (ε : ℝ)) := by
  apply Fin.ext
  change (Finset.univ.filter (fun i => c i - (ε : ℝ) ≤ t)).card =
    (Finset.univ.filter (fun i => c i ≤ t + (ε : ℝ))).card
  congr 1
  ext i
  simp

/-- The shifted module is constructible on the grid translated to the left.
@isnad1 id=isconstr.1h5v.s6.3f78f27ec733 from=translated src=- shape=f12270a5 vocab=f3408e8d
-/
theorem IsConstructible.shift {c : Fin n ↪o ℝ}
    (hM : IsConstructible c M) (ε : ℝ≥0) :
    IsConstructible (shiftGrid ε c) ((shift ε).obj M) where
  zero_left t ht := hM.zero_left (t + (ε : ℝ)) (fun i =>
    (lt_sub_iff_add_lt).mp (ht i))
  isIso_map s t hst hd := by
    change IsIso (structureMap M (add_le_add hst le_rfl))
    apply hM.isIso_map
    simpa only [cellIndex_shiftGrid] using hd

/-- The constructed union gives a genuine shared grid for a module and shifted target.
@isnad1 id=and.2h8v.s7.382c2c973da2 from=translated src=- shape=55c536f9 vocab=ba634e93
-/
theorem common_shift_constructible {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}
    (hM : IsConstructible c M) (hN : IsConstructible d N) (ε : ℝ≥0) :
    IsConstructible (commonGrid c (shiftGrid ε d)) M ∧
      IsConstructible (commonGrid c (shiftGrid ε d)) ((shift ε).obj N) :=
  ⟨hM.refine (refines_commonGrid_left _ _),
    (hN.shift ε).refine (refines_commonGrid_right _ _)⟩

end TDA.Persistence.FiniteConstructible

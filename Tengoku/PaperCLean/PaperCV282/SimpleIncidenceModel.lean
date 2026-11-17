import Tengoku.PaperCLean.PaperC.Combinatorics.PinnedGraphResolution
import Tengoku.Seed.LinearAlgebra.Matrix.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The actual finite binary incidence matrix

Rows of weight two define a simple graph, and rows of weight one pin their
column. Repeated pins and zero rows or columns are retained. Incidence mass
counts entries equal to one, rather than rows.
-/
namespace PaperC.V282.SimpleIncidenceModel

open Matrix Finset SimpleGraph

noncomputable section

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-- The support of an actual row.-/
def rowSupport (H : Matrix R V F₂) (r : R) : Finset V :=
  Finset.univ.filter (fun v => H r v ≠ 0)

/-- The support of an actual column.-/
def columnSupport (H : Matrix R V F₂) (v : V) : Finset R :=
  Finset.univ.filter (fun r => H r v ≠ 0)

/-- The literal number of nonzero binary entries.-/
def incidenceMass (H : Matrix R V F₂) : ℕ := ∑ r, (rowSupport H r).card

/-- Two active entries in one row form an edge.-/
def incidenceGraph (H : Matrix R V F₂) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ r, rowSupport H r = {u,v}
  symm := ⟨by
    rintro u v ⟨hne,r,hr⟩
    exact ⟨hne.symm,r,hr.trans (Finset.pair_comm _ _)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableIncidenceAdj (H : Matrix R V F₂) : DecidableRel (incidenceGraph H).Adj :=
  Classical.decRel _

/-- A column is pinned when some row has precisely that support.-/
def pinnedColumns (H : Matrix R V F₂) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ r, rowSupport H r = {v})

omit [Fintype R] [DecidableEq V] in
/--
@isnad1 id=iff.0h5v.s5.a46f39078329 from=translated src=- shape=59665156 vocab=b0f288b9
-/
theorem mem_rowSupport (H : Matrix R V F₂) (r : R) (v : V) :
    v ∈ rowSupport H r ↔ H r v ≠ 0 := by simp [rowSupport]

omit [Fintype V] [DecidableEq V] in
/--
@isnad1 id=iff.0h5v.s5.40edc7c9bd65 from=translated src=- shape=bd452652 vocab=b1dc8179
-/
theorem mem_columnSupport (H : Matrix R V F₂) (r : R) (v : V) :
    r ∈ columnSupport H v ↔ H r v ≠ 0 := by simp [columnSupport]

/--
@isnad1 id=iff.0h4v.s5.c3f62f463844 from=translated src=- shape=273ff296 vocab=ecc5d939
-/
theorem mem_pinnedColumns (H : Matrix R V F₂) (v : V) :
    v ∈ pinnedColumns H ↔ ∃ r, rowSupport H r = {v} := by
  classical
  simp [pinnedColumns]

/--
@isnad1 id=eq.1h1v.s5.f18caf134268 from=translated src=- shape=23aa8b17 vocab=f40c9e1f
-/
theorem binary_eq_one_of_ne_zero {a : F₂} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

omit [Fintype R] [DecidableEq V] in
/-- Matrix multiplication reads each nonzero entry as the binary coefficient one.
@isnad1 id=eq.0h5v.s8.766804486c2a from=translated src=- shape=6ff99894 vocab=7116eb1d
-/
theorem mulVecLin_apply_eq_support_sum (H : Matrix R V F₂) (f : V → F₂) (r : R) :
    (H.mulVecLin f) r = ∑ v ∈ rowSupport H r, f v := by
  classical
  change (∑ v, H r v * f v) = _
  rw [rowSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : H r v = 0
  · simp [hv]
  · simp [binary_eq_one_of_ne_zero hv]

omit [Fintype R] in
/-- All row shapes allowed by the hypothesis, including the zero row.
@isnad1 id=or.1h4v.s6.cb0001f5d275 from=translated src=- shape=3956986b vocab=51dbeb66
-/
theorem row_shapes (H : Matrix R V F₂) (r : R) (hrow : (rowSupport H r).card ≤ 2) :
    rowSupport H r = ∅ ∨ (∃ v, rowSupport H r = {v}) ∨
      ∃ u v, u ≠ v ∧ rowSupport H r = {u,v} := by
  by_cases hzero : (rowSupport H r).card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  by_cases hone : (rowSupport H r).card = 1
  · exact Or.inr (Or.inl (Finset.card_eq_one.mp hone))
  exact Or.inr (Or.inr (Finset.card_eq_two.mp (by omega)))

omit [DecidableEq V] in
/-- The same incidence mass is obtained by summing actual column weights.
@isnad1 id=eq.0h3v.s5.64aea6ec458b from=translated src=- shape=75469183 vocab=a6f1ecdf
-/
theorem incidenceMass_eq_sum_columnSupport (H : Matrix R V F₂) :
    incidenceMass H = ∑ v, (columnSupport H v).card := by
  classical
  simp only [incidenceMass, rowSupport, columnSupport, Finset.card_filter]
  exact Finset.sum_comm

end
end PaperC.V282.SimpleIncidenceModel

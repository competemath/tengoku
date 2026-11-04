import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Reindex
import Tengoku.Seed.Data.Fin.Tuple.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite distributions can be sorted and placed in a countable alphabet without
changing either entropy or objective. No assertion about infinite sorting is assumed. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector

/-- Sort the finite masses in decreasing order.-/
noncomputable def sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) :
    ProbabilityVector (Fin n) := by
  classical
  exact reindex (Tuple.sort (α := ℝᵒᵈ) (fun i => (p.coord i : ℝᵒᵈ))).symm p

/--
@isnad1 id=eq.0h3v.s5.95d9dea8b254 from=translated src=- shape=ae4b772b vocab=9a9457f3
-/
@[simp] theorem coord_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) (i : Fin n) :
    (sortedFinite p).coord i = p.coord (Tuple.sort (α := ℝᵒᵈ) (fun j => (p.coord j : ℝᵒᵈ)) i) := by
  classical
  simp [sortedFinite]

/--
@isnad1 id=antitone.0h2v.s4.292f768b9ce8 from=translated src=- shape=f67d5a65 vocab=e6624253
-/
theorem antitone_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) :
    Antitone (sortedFinite p).coord := by
  classical
  intro i j hij
  simp only [coord_sortedFinite]
  exact Tuple.monotone_sort (α := ℝᵒᵈ) (fun i => (p.coord i : ℝᵒᵈ)) hij

/--
@isnad1 id=eq.0h2v.s4.4d0add4e7268 from=translated src=- shape=715e287e vocab=9821f04c
-/
@[simp] theorem entropy_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) :
    (sortedFinite p).entropy = p.entropy := entropy_reindex _ _

/--
@isnad1 id=eq.0h3v.s4.743c2d3c2a84 from=translated src=- shape=5cdd86aa vocab=4d0f8df3
-/
@[simp] theorem objective_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) (t : ℕ) :
    (sortedFinite p).objective t = p.objective t := objective_reindex _ _ _

/-- Append zero atoms after the sorted finite distribution.-/
noncomputable def sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) : ProbabilityVector ℕ :=
  zeroExtend ⟨Fin.val, Fin.val_injective⟩ (sortedFinite p)

/--
@isnad1 id=eq.1h3v.s5.fe8c2761d8e3 from=translated src=- shape=796f8a29 vocab=16d6f3b1
-/
@[simp] theorem coord_sortedNat_lt {n : ℕ} (p : ProbabilityVector (Fin n)) (i : ℕ) (hi : i < n) :
    (sortedNat p).coord i = (sortedFinite p).coord ⟨i, hi⟩ :=
  coord_zeroExtend_apply (⟨Fin.val, Fin.val_injective⟩ : Fin n ↪ ℕ) (sortedFinite p) ⟨i, hi⟩

/--
@isnad1 id=eq.1h3v.s4.3696958c9035 from=translated src=- shape=85e94ea0 vocab=e15f0652
-/
@[simp] theorem coord_sortedNat_ge {n : ℕ} (p : ProbabilityVector (Fin n)) (i : ℕ) (hi : n ≤ i) :
    (sortedNat p).coord i = 0 := by
  apply coord_zeroExtend_of_not_mem_range
  rintro ⟨j, rfl⟩
  exact (Nat.not_lt_of_ge hi) j.isLt

/--
@isnad1 id=antitone.0h2v.s4.9095137ca7c9 from=translated src=- shape=afb35c08 vocab=48a2a5a9
-/
theorem antitone_sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) :
    Antitone (sortedNat p).coord := by
  intro i j hij
  by_cases hj : j < n
  · have hi := lt_of_le_of_lt hij hj
    rw [coord_sortedNat_lt p i hi, coord_sortedNat_lt p j hj]
    exact antitone_sortedFinite p hij
  · rw [coord_sortedNat_ge p j (Nat.le_of_not_gt hj)]
    exact (sortedNat p).coord_nonneg i

/--
@isnad1 id=eq.0h2v.s4.c5cb1931d3a2 from=translated src=- shape=d1aaa032 vocab=533be86e
-/
@[simp] theorem entropy_sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) :
    (sortedNat p).entropy = p.entropy := by simp [sortedNat]

/--
@isnad1 id=eq.0h3v.s4.dfbf31f8a59d from=translated src=- shape=762a1ac4 vocab=be1a2171
-/
@[simp] theorem objective_sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) (t : ℕ) :
    (sortedNat p).objective t = p.objective t := by simp [sortedNat]

end EntropyConstrainedMissingMass.ProbabilityVector

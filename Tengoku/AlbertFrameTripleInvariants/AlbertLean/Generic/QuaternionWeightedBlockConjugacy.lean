import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionCyclicBlockNormalizer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms all_blocks_conjugate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_common_conjugator` (it only prints; the queue checks the axioms of every declaration). -/

/-! Propagation of the rational cyclic comparison to all nine weighted blocks.
The consumer is the actual two-frame conjugation through the weighted bases. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedBlockConjugacy
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
open AlbertLean.Generic.QuaternionRow.WeightedBlockEquations
open AlbertLean.Generic.QuaternionRow.CyclicBlockNormalizer
variable {K : Type*} [Field K] [CharZero K]

/-- Once the pivot blocks are conjugate, the weighted linear equations force
all nine blocks to have the same conjugation.
@isnad1 id=eq.10h9v.s10.95190e03295c from=translated src=- shape=394a9c75 vocab=e4425e24
-/
theorem all_blocks_conjugate (B C : Fin 3 → Fin 3 → Mat2 K)
    (p q : Fin 3 → K) (hp1 : p 1 ≠ 0) (hp2 : p 2 ≠ 0)
    (hdB : ∀ i, B i i = q i • (1 : Mat2 K))
    (hrB : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hcB : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hdC : ∀ i, C i i = q i • (1 : Mat2 K))
    (hrC : ∀ i, C i 0 + C i 1 + C i 2 = 0)
    (hcC : ∀ j, p 0 • C 0 j + p 1 • C 1 j + p 2 • C 2 j = 0)
    (T S : Mat2 K) (hTS : T * S = 1)
    (hX : B 0 1 * T = T * C 0 1) :
    ∀ i j, B i j = T * C i j * S := by
  let D : Fin 3 → Fin 3 → Mat2 K := fun i j => T * C i j * S
  have hdiag (i : Fin 3) : D i i = q i • (1 : Mat2 K) := by
    simp only [D, hdC, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hTS]
  have hrow (i : Fin 3) : D i 0 + D i 1 + D i 2 = 0 := by
    change T * C i 0 * S + T * C i 1 * S + T * C i 2 * S = 0
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add,
      hrC, Matrix.mul_zero, Matrix.zero_mul]
  have hcol (j : Fin 3) : p 0 • D 0 j + p 1 • D 1 j + p 2 • D 2 j = 0 := by
    change p 0 • (T * C 0 j * S) + p 1 • (T * C 1 j * S) +
      p 2 • (T * C 2 j * S) = 0
    have h := congrArg (fun X : Mat2 K => T * X * S) (hcC j)
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_zero, Matrix.zero_mul] using h
  have hpivot : B 0 1 = D 0 1 := by
    change B 0 1 = T * C 0 1 * S
    calc
      B 0 1 = (B 0 1 * T) * S := by rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
      _ = T * C 0 1 * S := by rw [hX]
  have h := blocks_eq_of_pivot_eq B D p q hp1 hp2 hdB hrB hcB hdiag hrow hcol hpivot
  intro i j
  exact congrFun (congrFun h i) j

/-- An explicit root-free common-block conjugator for equal pivot trace and
determinant on the two cyclic charts.
@isnad1 id=ex.12h5v.s11.7d680b68dec7 from=translated src=- shape=88005713 vocab=29be5213
-/
theorem exists_common_conjugator (B C : Fin 3 → Fin 3 → Mat2 K)
    (p q : Fin 3 → K) (hp1 : p 1 ≠ 0) (hp2 : p 2 ≠ 0)
    (hdB : ∀ i, B i i = q i • (1 : Mat2 K))
    (hrB : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hcB : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hdC : ∀ i, C i i = q i • (1 : Mat2 K))
    (hrC : ∀ i, C i 0 + C i 1 + C i 2 = 0)
    (hcC : ∀ j, p 0 • C 0 j + p 1 • C 1 j + p 2 • C 2 j = 0)
    (hB : B 0 1 0 1 ≠ 0) (hC : C 0 1 0 1 ≠ 0)
    (ht : trace2 (B 0 1) = trace2 (C 0 1))
    (hd : determinant (B 0 1) = determinant (C 0 1)) :
    ∃ T S : Mat2 K, T * S = 1 ∧ S * T = 1 ∧
      ∀ i j, B i j = T * C i j * S := by
  obtain ⟨hTS, hST, hX⟩ := rational_intertwiner (B 0 1) (C 0 1) hB hC ht hd
  exact ⟨_, _, hTS, hST,
    all_blocks_conjugate B C p q hp1 hp2 hdB hrB hcB hdC hrC hcC _ _ hTS hX⟩

end AlbertLean.Generic.QuaternionRow.WeightedBlockConjugacy

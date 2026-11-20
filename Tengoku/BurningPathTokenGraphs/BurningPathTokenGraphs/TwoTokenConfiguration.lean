import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetric
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenModel
import Tengoku.Seed.Data.Int.NatAbs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-token configurations as ordered coordinate pairs

This file connects two-element path-token configurations to the one-based integer pairs used by
the parity-triangle model.
-/

namespace BurningPath

/-- A strictly increasing pair of vertices of `Fin n`.-/
def OrderedFinPair (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2}

/-- Read a two-element order embedding at its two coordinates.-/
def finTwoOrderEmbeddingToOrderedFinPair {n : ℕ} (f : Fin 2 ↪o Fin n) :
    OrderedFinPair n :=
  ⟨(f 0, f 1), f.strictMono (by decide)⟩

/-- Build the two-element order embedding represented by a strictly increasing pair.-/
def orderedFinPairToFinTwoOrderEmbedding {n : ℕ} (p : OrderedFinPair n) :
    Fin 2 ↪o Fin n :=
  OrderEmbedding.ofStrictMono (Fin.cases p.1.1 fun _ ↦ p.1.2) <| by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    exact p.2

/-- Two-element order embeddings are equivalently strictly increasing pairs.-/
def finTwoOrderEmbeddingEquivOrderedFinPair (n : ℕ) :
    (Fin 2 ↪o Fin n) ≃ OrderedFinPair n where
  toFun := finTwoOrderEmbeddingToOrderedFinPair
  invFun := orderedFinPairToFinTwoOrderEmbedding
  left_inv f := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- A two-token configuration is equivalently its two increasing `Fin n` coordinates.-/
noncomputable def configurationEquivOrderedFinPair (n : ℕ) :
    Configuration (Fin n) 2 ≃ OrderedFinPair n :=
  (configurationEquivOrderEmbedding (Fin n) 2).trans
    (finTwoOrderEmbeddingEquivOrderedFinPair n)

@[simp]
theorem configurationEquivOrderedFinPair_fst {n : ℕ} (A : Configuration (Fin n) 2) :
    (configurationEquivOrderedFinPair n A).1.1 = coordinate A 0 :=
  rfl

@[simp]
theorem configurationEquivOrderedFinPair_snd {n : ℕ} (A : Configuration (Fin n) 2) :
    (configurationEquivOrderedFinPair n A).1.2 = coordinate A 1 :=
  rfl

/-- Recover a zero-based `Fin n` coordinate from a legal one-based integer coordinate.-/
def finOfOneBasedInt {n : ℕ} (x : ℤ) (hx : 1 ≤ x) (hxn : x ≤ n) : Fin n :=
  ⟨(x - 1).toNat, (Int.toNat_lt (by omega)).2 (by omega)⟩

@[simp]
theorem finOfOneBasedInt_val {n : ℕ} (x : ℤ) (hx : 1 ≤ x) (hxn : x ≤ n) :
    ((finOfOneBasedInt x hx hxn).val : ℤ) + 1 = x := by
  simp only [finOfOneBasedInt]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Convert an ordered `Fin n` pair to the one-based integer convention of `TwoPathPoint`.-/
def orderedFinPairToTwoPathPoint {n : ℕ} (p : OrderedFinPair n) : TwoPathPoint n := by
  refine ⟨(((p.1.1.val : ℤ) + 1), ((p.1.2.val : ℤ) + 1)), ?_⟩
  have hx := p.1.1.isLt
  have hy := p.1.2.isLt
  constructor
  · omega
  constructor
  · have hxy := p.2
    change (p.1.1.val : ℤ) + 1 < (p.1.2.val : ℤ) + 1
    omega
  · omega

@[simp]
theorem orderedFinPairToTwoPathPoint_fst {n : ℕ} (p : OrderedFinPair n) :
    (orderedFinPairToTwoPathPoint p).1.1 = (p.1.1.val : ℤ) + 1 :=
  rfl

@[simp]
theorem orderedFinPairToTwoPathPoint_snd {n : ℕ} (p : OrderedFinPair n) :
    (orderedFinPairToTwoPathPoint p).1.2 = (p.1.2.val : ℤ) + 1 :=
  rfl

/-- Recover the ordered `Fin n` pair represented by a legal one-based integer pair.-/
def twoPathPointToOrderedFinPair {n : ℕ} (p : TwoPathPoint n) : OrderedFinPair n := by
  have hx : 1 ≤ p.1.1 := p.2.1
  have hxy : p.1.1 < p.1.2 := p.2.2.1
  have hy : p.1.2 ≤ n := p.2.2.2
  have hy1 : 1 ≤ p.1.2 := by omega
  have hxn : p.1.1 ≤ n := by omega
  refine
    ⟨(finOfOneBasedInt p.1.1 hx hxn,
      finOfOneBasedInt p.1.2 hy1 hy), ?_⟩
  change (p.1.1 - 1).toNat < (p.1.2 - 1).toNat
  exact (Int.toNat_lt_toNat (by omega)).2 (by omega)

@[simp]
theorem twoPathPointToOrderedFinPair_fst_val {n : ℕ} (p : TwoPathPoint n) :
    (((twoPathPointToOrderedFinPair p).1.1.val : ℤ) + 1) = p.1.1 := by
  have hx : 1 ≤ p.1.1 := p.2.1
  have hxy : p.1.1 < p.1.2 := p.2.2.1
  have hy : p.1.2 ≤ n := p.2.2.2
  have hxn : p.1.1 ≤ n := by omega
  change ((finOfOneBasedInt p.1.1 hx hxn).val : ℤ) + 1 = p.1.1
  exact finOfOneBasedInt_val p.1.1 hx hxn

@[simp]
theorem twoPathPointToOrderedFinPair_snd_val {n : ℕ} (p : TwoPathPoint n) :
    (((twoPathPointToOrderedFinPair p).1.2.val : ℤ) + 1) = p.1.2 := by
  have hx : 1 ≤ p.1.1 := p.2.1
  have hxy : p.1.1 < p.1.2 := p.2.2.1
  have hy : p.1.2 ≤ n := p.2.2.2
  have hy1 : 1 ≤ p.1.2 := by omega
  change ((finOfOneBasedInt p.1.2 hy1 hy).val : ℤ) + 1 = p.1.2
  exact finOfOneBasedInt_val p.1.2 hy1 hy

/-- Strictly increasing finite pairs are equivalent to legal one-based path positions.-/
def orderedFinPairEquivTwoPathPoint (n : ℕ) :
    OrderedFinPair n ≃ TwoPathPoint n where
  toFun := orderedFinPairToTwoPathPoint
  invFun := twoPathPointToOrderedFinPair
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have h :=
        twoPathPointToOrderedFinPair_fst_val (orderedFinPairToTwoPathPoint p)
      simp only [orderedFinPairToTwoPathPoint_fst] at h
      omega
    · apply Fin.ext
      have h :=
        twoPathPointToOrderedFinPair_snd_val (orderedFinPairToTwoPathPoint p)
      simp only [orderedFinPairToTwoPathPoint_snd] at h
      omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact twoPathPointToOrderedFinPair_fst_val p
    · exact twoPathPointToOrderedFinPair_snd_val p

/-- The equivalence between two-token configurations and ordered arithmetic pairs.-/
noncomputable def twoConfigurationEquivTwoPathPoint (n : ℕ) :
    Configuration (Fin n) 2 ≃ TwoPathPoint n :=
  (configurationEquivOrderedFinPair n).trans (orderedFinPairEquivTwoPathPoint n)

@[simp]
theorem twoConfigurationEquivTwoPathPoint_fst {n : ℕ} (A : Configuration (Fin n) 2) :
    (twoConfigurationEquivTwoPathPoint n A).1.1 = ((coordinate A 0).val : ℤ) + 1 :=
  rfl

@[simp]
theorem twoConfigurationEquivTwoPathPoint_snd {n : ℕ} (A : Configuration (Fin n) 2) :
    (twoConfigurationEquivTwoPathPoint n A).1.2 = ((coordinate A 1).val : ℤ) + 1 :=
  rfl

/--
For two-token configurations, the ordered-coordinate distance is the `ℓ₁` distance between the
corresponding one-based integer pairs.-/
theorem pathConfigurationDist_eq_twoPathPoint {n : ℕ}
    (A B : Configuration (Fin n) 2) :
    pathConfigurationDist A B =
      ((twoConfigurationEquivTwoPathPoint n A).1.1 -
          (twoConfigurationEquivTwoPathPoint n B).1.1).natAbs +
        ((twoConfigurationEquivTwoPathPoint n A).1.2 -
          (twoConfigurationEquivTwoPathPoint n B).1.2).natAbs := by
  simp only [pathConfigurationDist, Fin.sum_univ_two,
    twoConfigurationEquivTwoPathPoint_fst, twoConfigurationEquivTwoPathPoint_snd]
  rw [natDist_eq_natAbs_intSub, natDist_eq_natAbs_intSub]
  congr 1 <;> omega

/-- The shifted two-token coordinates have `ℓ∞` distance equal to `pathConfigurationDist`.-/
theorem twoTokenPhi_configuration_isometry {n : ℕ}
    (A B : Configuration (Fin n) 2) :
    max
        ((twoTokenPhi (twoConfigurationEquivTwoPathPoint n A)).1 -
          (twoTokenPhi (twoConfigurationEquivTwoPathPoint n B)).1).natAbs
        ((twoTokenPhi (twoConfigurationEquivTwoPathPoint n A)).2 -
          (twoTokenPhi (twoConfigurationEquivTwoPathPoint n B)).2).natAbs =
      pathConfigurationDist A B := by
  rw [twoTokenPhi_isometry, pathConfigurationDist_eq_twoPathPoint]

end BurningPath

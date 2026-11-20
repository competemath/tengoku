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

/--
@isnad1 id=eq.0h2v.s7.6ba9c856b00a from=translated src=- shape=c22f91ad vocab=d8870942
-/
@[simp]
theorem configurationEquivOrderedFinPair_fst {n : ℕ} (A : Configuration (Fin n) 2) :
    (configurationEquivOrderedFinPair n A).1.1 = coordinate A 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.8cbfc861ac45 from=translated src=- shape=dfc90c12 vocab=d8870942
-/
@[simp]
theorem configurationEquivOrderedFinPair_snd {n : ℕ} (A : Configuration (Fin n) 2) :
    (configurationEquivOrderedFinPair n A).1.2 = coordinate A 1 :=
  rfl

/-- Recover a zero-based `Fin n` coordinate from a legal one-based integer coordinate.-/
def finOfOneBasedInt {n : ℕ} (x : ℤ) (hx : 1 ≤ x) (hxn : x ≤ n) : Fin n :=
  ⟨(x - 1).toNat, (Int.toNat_lt (by omega)).2 (by omega)⟩

/--
@isnad1 id=eq.2h2v.s5.590383c71320 from=translated src=- shape=e9aafff8 vocab=aa7adbf3
-/
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

/--
@isnad1 id=eq.0h2v.s6.06d83302f903 from=translated src=- shape=270290ad vocab=087f6ae4
-/
@[simp]
theorem orderedFinPairToTwoPathPoint_fst {n : ℕ} (p : OrderedFinPair n) :
    (orderedFinPairToTwoPathPoint p).1.1 = (p.1.1.val : ℤ) + 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.9fba973015a7 from=translated src=- shape=67ceb08e vocab=087f6ae4
-/
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

/--
@isnad1 id=eq.0h2v.s6.7b8d4122918e from=translated src=- shape=3493c593 vocab=a61e4aea
-/
@[simp]
theorem twoPathPointToOrderedFinPair_fst_val {n : ℕ} (p : TwoPathPoint n) :
    (((twoPathPointToOrderedFinPair p).1.1.val : ℤ) + 1) = p.1.1 := by
  have hx : 1 ≤ p.1.1 := p.2.1
  have hxy : p.1.1 < p.1.2 := p.2.2.1
  have hy : p.1.2 ≤ n := p.2.2.2
  have hxn : p.1.1 ≤ n := by omega
  change ((finOfOneBasedInt p.1.1 hx hxn).val : ℤ) + 1 = p.1.1
  exact finOfOneBasedInt_val p.1.1 hx hxn

/--
@isnad1 id=eq.0h2v.s6.9ed15be504e6 from=translated src=- shape=97e8dc0b vocab=a61e4aea
-/
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

/--
@isnad1 id=eq.0h2v.s7.1597d84274a6 from=translated src=- shape=a2c4db11 vocab=269ecd1c
-/
@[simp]
theorem twoConfigurationEquivTwoPathPoint_fst {n : ℕ} (A : Configuration (Fin n) 2) :
    (twoConfigurationEquivTwoPathPoint n A).1.1 = ((coordinate A 0).val : ℤ) + 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.abe98947cd2c from=translated src=- shape=30062053 vocab=269ecd1c
-/
@[simp]
theorem twoConfigurationEquivTwoPathPoint_snd {n : ℕ} (A : Configuration (Fin n) 2) :
    (twoConfigurationEquivTwoPathPoint n A).1.2 = ((coordinate A 1).val : ℤ) + 1 :=
  rfl

/--
For two-token configurations, the ordered-coordinate distance is the `ℓ₁` distance between the
corresponding one-based integer pairs.
@isnad1 id=eq.0h3v.s8.dc59297d844f from=translated src=- shape=ddf06357 vocab=10e67cf0
-/
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

/-- The shifted two-token coordinates have `ℓ∞` distance equal to `pathConfigurationDist`.
@isnad1 id=eq.0h3v.s8.217a51e0cf1f from=translated src=- shape=59061962 vocab=4767b434
-/
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

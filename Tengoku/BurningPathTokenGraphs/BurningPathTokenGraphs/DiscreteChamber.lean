import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetric
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The discrete ordered chamber

Subtracting the coordinate index turns a strictly increasing token configuration into a weakly
increasing point of the discrete chamber. Adding the index gives the inverse transformation.
-/

open scoped BigOperators

namespace BurningPath

/-- The weakly ordered integer chamber `0 ≤ z₁ ≤ ⋯ ≤ zₖ ≤ N`, represented in `ℕ`.-/
def Gamma (N k : ℕ) :=
  {z : Fin k → ℕ // Monotone z ∧ ∀ i, z i ≤ N}

/-- The chamber's restricted `ℓ₁` distance.-/
def gammaL1Dist {N k : ℕ} (z w : Gamma N k) : ℕ :=
  ∑ i, Nat.dist (z.1 i) (w.1 i)

private theorem finOrderEmbedding_index_le {n k : ℕ} (f : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (f i).val := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
          have hstep := f.strictMono (Fin.castSucc_lt_succ : i.castSucc < i.succ)
          simp only [Fin.val_castSucc, Fin.val_succ] at ih hstep ⊢
          omega

private theorem finOrderEmbedding_shift_monotone {n k : ℕ} (f : Fin k ↪o Fin n) :
    Monotone fun i ↦ (f i).val - i.val := by
  cases k with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ k =>
      rw [Fin.monotone_iff_le_succ]
      intro i
      have hindex := finOrderEmbedding_index_le f i.castSucc
      have hstep := f.strictMono (Fin.castSucc_lt_succ : i.castSucc < i.succ)
      simp only [Fin.val_castSucc, Fin.val_succ] at hindex hstep ⊢
      omega

private theorem finOrderEmbedding_shift_le {n k : ℕ} (hk : k ≤ n)
    (f : Fin k ↪o Fin n) (i : Fin k) :
    (f i).val - i.val ≤ n - k := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
      have hmono := finOrderEmbedding_shift_monotone f
      have hi := hmono (Fin.le_last i)
      have hlast := (f (Fin.last k)).isLt
      simp only [Fin.val_last] at hi hlast
      omega

/-- Subtracting each index sends an order embedding into the discrete chamber.-/
def finOrderEmbeddingToGamma {n k : ℕ} (hk : k ≤ n) (f : Fin k ↪o Fin n) :
    Gamma (n - k) k :=
  ⟨fun i ↦ (f i).val - i.val, finOrderEmbedding_shift_monotone f,
    finOrderEmbedding_shift_le hk f⟩

/-- Adding each index sends a chamber point back to a strict order embedding.-/
def gammaToFinOrderEmbedding {n k : ℕ} (hk : k ≤ n) (z : Gamma (n - k) k) :
    Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦
      ⟨z.1 i + i.val, by
        have hz := z.2.2 i
        omega⟩)
    (by
      intro i j hij
      have hz := z.2.1 hij.le
      change z.1 i + i.val < z.1 j + j.val
      omega)

/-- Order embeddings `Fin k ↪o Fin n` are exactly the points of `Γ_(n-k),k`.-/
def finOrderEmbeddingEquivGamma {n k : ℕ} (hk : k ≤ n) :
    (Fin k ↪o Fin n) ≃ Gamma (n - k) k where
  toFun := finOrderEmbeddingToGamma hk
  invFun := gammaToFinOrderEmbedding hk
  left_inv f := by
    ext i
    change ((f i).val - i.val) + i.val = (f i).val
    exact Nat.sub_add_cancel (finOrderEmbedding_index_le f i)
  right_inv z := by
    apply Subtype.ext
    funext i
    change (z.1 i + i.val) - i.val = z.1 i
    exact Nat.add_sub_cancel_right (z.1 i) i.val

/-- The exact discrete-chamber encoding of a path-token configuration.-/
noncomputable def configurationEquivGamma {n k : ℕ} (hk : k ≤ n) :
    Configuration (Fin n) k ≃ Gamma (n - k) k :=
  (configurationEquivOrderEmbedding (Fin n) k).trans (finOrderEmbeddingEquivGamma hk)

/--
@isnad1 id=eq.1h4v.s7.9b59aa7014de from=translated src=- shape=3afa08ce vocab=8ac73084
-/
@[simp]
theorem configurationEquivGamma_apply {n k : ℕ} (hk : k ≤ n)
    (A : Configuration (Fin n) k) (i : Fin k) :
    (configurationEquivGamma hk A).1 i = (coordinate A i).val - i.val :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.04857df99a01 from=translated src=- shape=2cd0a3e1 vocab=9ce378cb
-/
@[simp]
theorem coordinate_configurationEquivGamma_symm {n k : ℕ} (hk : k ≤ n)
    (z : Gamma (n - k) k) (i : Fin k) :
    (coordinate ((configurationEquivGamma hk).symm z) i).val = z.1 i + i.val := by
  change
    ((configurationEquivOrderEmbedding (Fin n) k
      ((configurationEquivOrderEmbedding (Fin n) k).symm
        (gammaToFinOrderEmbedding hk z))) i).val =
      z.1 i + i.val
  rw [Equiv.apply_symm_apply]
  rfl

/-- The chamber encoding preserves the ordered-coordinate `ℓ₁` distance exactly.
@isnad1 id=eq.1h4v.s7.932b8ba5af86 from=translated src=- shape=38c77ff6 vocab=a9b33848
-/
theorem pathConfigurationDist_eq_gammaL1Dist {n k : ℕ} (hk : k ≤ n)
    (A B : Configuration (Fin n) k) :
    pathConfigurationDist A B =
      gammaL1Dist (configurationEquivGamma hk A) (configurationEquivGamma hk B) := by
  unfold pathConfigurationDist gammaL1Dist
  apply Finset.sum_congr rfl
  intro i hi
  simp only [configurationEquivGamma_apply]
  have hA :=
    finOrderEmbedding_index_le (configurationEquivOrderEmbedding (Fin n) k A) i
  have hB :=
    finOrderEmbedding_index_le (configurationEquivOrderEmbedding (Fin n) k B) i
  simpa only [coordinate, Nat.sub_add_cancel hA, Nat.sub_add_cancel hB] using
    Nat.dist_add_add_right ((coordinate A i).val - i.val) i.val
      ((coordinate B i).val - i.val)

/-- Equivalently, applying the inverse chamber equivalence also preserves distance.
@isnad1 id=eq.1h4v.s8.a5db5560b0b7 from=translated src=- shape=9a726266 vocab=ca032ce1
-/
theorem gammaL1Dist_eq_pathConfigurationDist {n k : ℕ} (hk : k ≤ n)
    (z w : Gamma (n - k) k) :
    gammaL1Dist z w =
      pathConfigurationDist ((configurationEquivGamma hk).symm z)
        ((configurationEquivGamma hk).symm w) := by
  rw [pathConfigurationDist_eq_gammaL1Dist hk]
  simp

end BurningPath

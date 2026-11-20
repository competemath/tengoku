import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.BoundedComposition
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenModel
import Tengoku.Seed.Data.Int.ModEq
import Tengoku.Seed.Data.List.Chain
import Tengoku.Seed.Data.List.ChainOfFn
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parity caps and square shelves

This file introduces the discrete cap geometry and proves the terminal apex
branch and residual-cap bookkeeping for nonterminal shelves.
-/

namespace BurningPath

/-- The parity cap `𝒞_(h,z)^(σ)`.-/
def parityCap (h z : ℕ) (σ : ℤ) : Set (ℤ × ℤ) :=
  {p |
    (h : ℤ) ≤ p.2 ∧ p.2 ≤ h + z ∧
      |p.1| ≤ (h + z : ℕ) - p.2 ∧ p.1 - p.2 ≡ σ [ZMOD 2]}

/-- The parity triangle is the height-zero special case of a parity cap.-/
theorem parityCap_zero (z : ℕ) (σ : ℤ) :
    parityCap 0 z σ = parityTriangle z σ := by
  ext p
  simp [parityCap, parityTriangle]

/-- Integer-valued `ℓ∞` distance.-/
def intLinfDist (p c : ℤ × ℤ) : ℤ :=
  max |p.1 - c.1| |p.2 - c.2|

/-- The closed axis-parallel integer square of radius `r`.-/
def integerSquare (c : ℤ × ℤ) (r : ℕ) : Set (ℤ × ℤ) :=
  {p | intLinfDist p c ≤ r}

@[simp]
theorem mem_integerSquare {c p : ℤ × ℤ} {r : ℕ} :
    p ∈ integerSquare c r ↔ intLinfDist p c ≤ r :=
  Iff.rfl

/-- The cap apex.-/
def parityCapApex (h z : ℕ) : ℤ × ℤ :=
  (0, h + z)

/-- If the apex parity is `σ`, the apex is a legal cap center.-/
theorem parityCapApex_mem {h z : ℕ} {σ : ℤ}
    (hσ : (h + z : ℕ) ≡ σ [ZMOD 2]) :
    parityCapApex h z ∈ parityCap h z σ := by
  simp only [parityCapApex, parityCap, Set.mem_ofPred_eq, abs_zero, Nat.cast_add]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · rw [Int.modEq_iff_dvd] at hσ ⊢
    obtain ⟨a, ha⟩ := hσ
    refine ⟨a + h + z, ?_⟩
    omega

/-- The radius-`z` square centered at the apex covers the entire cap.-/
theorem parityCap_subset_apex_square (h z : ℕ) (σ : ℤ) :
    parityCap h z σ ⊆ integerSquare (parityCapApex h z) z := by
  intro p hp
  rcases hp with ⟨hY, hYtop, hX, hpar⟩
  simp only [integerSquare, intLinfDist, parityCapApex, Set.mem_ofPred_eq, max_le_iff]
  constructor
  · simpa only [sub_zero] using hX.trans (by omega)
  · rw [abs_le]
    constructor <;> omega

/-- Radius `w-1` covers the cap whenever `z ≤ w-1`.-/
theorem parityCap_subset_terminal_square {h z w : ℕ} (σ : ℤ) (hz : z ≤ w - 1) :
    parityCap h z σ ⊆ integerSquare (parityCapApex h z) (w - 1) :=
  fun p hp ↦ by
    have hbase := parityCap_subset_apex_square h z σ hp
    change intLinfDist p (parityCapApex h z) ≤ (z : ℤ) at hbase
    change intLinfDist p (parityCapApex h z) ≤ ((w - 1 : ℕ) : ℤ)
    exact hbase.trans (by exact_mod_cast hz)

/--
A chain of radius-`a` intervals whose consecutive centers are at distance at most `2a`
covers the interval from the first left endpoint to the last right endpoint.-/
theorem exists_mem_abs_sub_le_of_chain (a : ℕ) (x : ℤ) (xs : List ℤ)
    (hchain : (x :: xs).IsChain fun u v ↦ v - u ≤ 2 * (a : ℤ)) {X : ℤ}
    (hleft : x - (a : ℤ) ≤ X)
    (hright : X ≤ (x :: xs).getLast (by simp) + (a : ℤ)) :
    ∃ c ∈ x :: xs, |X - c| ≤ (a : ℤ) := by
  induction xs generalizing x with
  | nil =>
      refine ⟨x, by simp, ?_⟩
      have hright' : X ≤ x + (a : ℤ) := by
        simpa using hright
      rw [abs_le]
      constructor <;> omega
  | cons y ys ih =>
      have hparts :
          y - x ≤ 2 * (a : ℤ) ∧
            (y :: ys).IsChain (fun u v ↦ v - u ≤ 2 * (a : ℤ)) :=
        List.isChain_cons_cons.mp hchain
      by_cases hX : X ≤ x + a
      · refine ⟨x, by simp, ?_⟩
        rw [abs_le]
        constructor <;> omega
      · have hrightTail :
            X ≤ (y :: ys).getLast (by simp) + (a : ℤ) := by
          simpa using hright
        obtain ⟨c, hc, hdist⟩ :=
          ih y hparts.2 (by omega) hrightTail
        exact ⟨c, by simp [hc], hdist⟩

/--
Finite-function form of `exists_mem_abs_sub_le_of_chain`.-/
theorem exists_fin_abs_sub_le_of_chain (a q : ℕ) (hq : 0 < q) (f : Fin q → ℤ)
    (hstep :
      ∀ i (hi : i + 1 < q),
        f ⟨i + 1, hi⟩ - f ⟨i, by omega⟩ ≤ 2 * (a : ℤ))
    {X : ℤ}
    (hleft : f ⟨0, hq⟩ - (a : ℤ) ≤ X)
    (hright : X ≤ f ⟨q - 1, by omega⟩ + (a : ℤ)) :
    ∃ i : Fin q, |X - f i| ≤ (a : ℤ) := by
  induction q using Nat.strong_induction_on generalizing X with
  | h q ih =>
      cases q with
      | zero => omega
      | succ q =>
          cases q with
          | zero =>
              have hright0 :
                  X ≤ f ⟨0, by omega⟩ + (a : ℤ) := by
                simpa using hright
              refine ⟨⟨0, by omega⟩, ?_⟩
              rw [abs_le]
              constructor <;> omega
          | succ q =>
              let first : Fin (q + 2) := ⟨0, by omega⟩
              have hleftFirst : f first - (a : ℤ) ≤ X := by
                simpa [first] using hleft
              by_cases hX : X ≤ f first + (a : ℤ)
              · refine ⟨first, ?_⟩
                rw [abs_le]
                constructor <;> omega
              · let tail : Fin (q + 1) → ℤ := fun i ↦ f i.succ
                have htailStep :
                    ∀ i (hi : i + 1 < q + 1),
                      tail ⟨i + 1, hi⟩ - tail ⟨i, by omega⟩ ≤
                        2 * (a : ℤ) := by
                  intro i hi
                  simpa [tail] using hstep (i + 1) (by omega)
                have hgap :
                    f ⟨1, by omega⟩ - f first ≤ 2 * (a : ℤ) := by
                  simpa [first] using hstep 0 (by omega)
                have htailLeft :
                    tail ⟨0, by omega⟩ - (a : ℤ) ≤ X := by
                  change f ⟨1, by omega⟩ - (a : ℤ) ≤ X
                  omega
                have htailRight :
                    X ≤ tail ⟨q, by omega⟩ + (a : ℤ) := by
                  simpa [tail] using hright
                obtain ⟨i, hi⟩ :=
                  ih (q + 1) (by omega) (by omega) tail htailStep
                    htailLeft htailRight
                exact ⟨i.succ, by simpa [tail] using hi⟩

/--
The pointwise shelf construction. The `i`-th center, indexed from zero,
uses radius `w - (i + 1)`, so the radii are exactly `w-q, …, w-1`.-/
theorem exists_shelf_centers {h z w q : ℕ} {σ : ℤ}
    (hσ : (h + z : ℕ) ≡ σ [ZMOD 2])
    (hw : 3 ≤ w) (hz : w - 1 < z)
    (hq2 : 2 ≤ q) (hqw : q < w) (hcapacity : z ≤ q * (w - q)) :
    ∃ centers : Fin q → ℤ × ℤ,
      (∀ i, centers i ∈ parityCap h z σ) ∧
        ∀ p ∈ parityCap h z σ,
          p.2 ≤ (h + 2 * (w - q) : ℕ) →
            ∃ i, p ∈ integerSquare (centers i) (w - (i.val + 1)) := by
  classical
  let a := w - q
  have haPos : 0 < a := by omega
  have hzW : w ≤ z := by omega
  have haZ : a ≤ z := by omega
  have hqa : q * a = (q - 1) * a + a := by
    calc
      q * a = ((q - 1) + 1) * a := by congr 1; omega
      _ = (q - 1) * a + a := by rw [Nat.add_mul]; simp
  have hallocation : z - a ≤ (q - 1) * a := by
    change z ≤ q * a at hcapacity
    omega
  obtain ⟨e, heBound, heSum⟩ :=
    exists_fin_bounded_composition (q - 1) a (z - a) hallocation
  let eNat : ℕ → ℕ := fun j ↦ if hj : j < q - 1 then e ⟨j, hj⟩ else 0
  have heNatBound (j : ℕ) : eNat j ≤ a := by
    by_cases hj : j < q - 1
    · simpa [eNat, hj] using heBound ⟨j, hj⟩
    · simp [eNat, hj]
  have heNatSum :
      ∑ j ∈ Finset.range (q - 1), eNat j = z - a := by
    rw [← heSum, Finset.sum_fin_eq_sum_range]
  let partialSum : Fin q → ℕ :=
    fun i ↦ ∑ j ∈ Finset.range i.val, eNat j
  let ξ : Fin q → ℤ :=
    fun i ↦ -(z : ℤ) + (a : ℤ) + 2 * (partialSum i : ℤ)
  let centers : Fin q → ℤ × ℤ :=
    fun i ↦ (ξ i, (h + a : ℕ))
  have hpartialSum_le (i : Fin q) : partialSum i ≤ z - a := by
    calc
      partialSum i ≤ ∑ j ∈ Finset.range (q - 1), eNat j := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.range_mono (by omega)
      _ = z - a := heNatSum
  have hξBounds (i : Fin q) :
      -((z - a : ℕ) : ℤ) ≤ ξ i ∧ ξ i ≤ ((z - a : ℕ) : ℤ) := by
    have hp := hpartialSum_le i
    have hcast : ((z - a : ℕ) : ℤ) = (z : ℤ) - a := by
      omega
    simp only [ξ]
    rw [hcast]
    constructor <;> omega
  have hlegal (i : Fin q) : centers i ∈ parityCap h z σ := by
    have hbounds := hξBounds i
    simp only [centers, parityCap, Set.mem_ofPred_eq]
    constructor
    · push_cast
      omega
    constructor
    · push_cast
      omega
    constructor
    · have hza :
          ((h + z : ℕ) : ℤ) - ((h + a : ℕ) : ℤ) =
            ((z - a : ℕ) : ℤ) := by
        omega
      rw [hza]
      rw [abs_le]
      exact hbounds
    · rw [Int.modEq_iff_dvd] at hσ ⊢
      obtain ⟨d, hd⟩ := hσ
      refine ⟨d + h + z - partialSum i, ?_⟩
      simp only [ξ]
      push_cast
      omega
  have hξStep :
      ∀ j (hj : j + 1 < q),
        ξ ⟨j + 1, hj⟩ - ξ ⟨j, by omega⟩ ≤ 2 * (a : ℤ) := by
    intro j hj
    have he := heNatBound j
    simp only [ξ, partialSum, Finset.sum_range_succ]
    push_cast
    omega
  have hξFirst : ξ ⟨0, by omega⟩ = -(z : ℤ) + a := by
    simp [ξ, partialSum]
  have hξLast : ξ ⟨q - 1, by omega⟩ = (z : ℤ) - a := by
    have hsum :
        partialSum ⟨q - 1, by omega⟩ = z - a := by
      exact heNatSum
    simp only [ξ, hsum]
    exact_mod_cast (show -(z : ℤ) + a + 2 * (z - a) = z - a by omega)
  refine ⟨centers, hlegal, ?_⟩
  intro p hp hpY
  have hpBottom : (h : ℤ) ≤ p.2 := hp.1
  have hpSide : |p.1| ≤ (h + z : ℕ) - p.2 := hp.2.2.1
  have hpX : -(z : ℤ) ≤ p.1 ∧ p.1 ≤ (z : ℤ) := by
    rw [abs_le] at hpSide
    constructor <;> omega
  have hleft : ξ ⟨0, by omega⟩ - (a : ℤ) ≤ p.1 := by
    rw [hξFirst]
    omega
  have hright : p.1 ≤ ξ ⟨q - 1, by omega⟩ + (a : ℤ) := by
    rw [hξLast]
    omega
  obtain ⟨i, hiX⟩ :=
    exists_fin_abs_sub_le_of_chain a q (by omega) ξ hξStep hleft hright
  refine ⟨i, ?_⟩
  simp only [integerSquare, intLinfDist, centers, Set.mem_ofPred_eq, max_le_iff]
  have hiY : |p.2 - (h + a : ℕ)| ≤ (a : ℤ) := by
    rw [abs_le]
    push_cast at hpY ⊢
    constructor <;> omega
  have haRadius : a ≤ w - (i.val + 1) := by
    simp only [a]
    omega
  constructor
  · exact hiX.trans (by exact_mod_cast haRadius)
  · exact hiY.trans (by exact_mod_cast haRadius)

/--
Removing a bottom band of height `2a` leaves a cap with the same apex and parity parameter.
The bottom boundary is retained, allowing overlap between consecutive shelves.-/
theorem mem_residual_parityCap {h z a : ℕ} {σ : ℤ} {p : ℤ × ℤ}
    (ha : 2 * a ≤ z) (hp : p ∈ parityCap h z σ) (hY : (h + 2 * a : ℕ) ≤ p.2) :
    p ∈ parityCap (h + 2 * a) (z - 2 * a) σ := by
  rcases hp with ⟨hpBottom, hpTop, hpSide, hpParity⟩
  have hapex : h + 2 * a + (z - 2 * a) = h + z := by omega
  have hapexInt :
      ((h + 2 * a : ℕ) : ℤ) + ((z - 2 * a : ℕ) : ℤ) = (h : ℤ) + z := by
    exact_mod_cast hapex
  simp only [parityCap, Set.mem_ofPred_eq]
  constructor
  · exact_mod_cast hY
  constructor
  · rw [hapexInt]
    exact hpTop
  constructor
  · rw [hapex]
    exact hpSide
  · exact hpParity

/-- If the first shelf reaches the apex, the centers cover the whole cap.-/
theorem exists_shelf_centers_cover_cap {h z w q : ℕ} {σ : ℤ}
    (hσ : (h + z : ℕ) ≡ σ [ZMOD 2])
    (hw : 3 ≤ w) (hz : w - 1 < z)
    (hq2 : 2 ≤ q) (hqw : q < w) (hcapacity : z ≤ q * (w - q))
    (hterminal : z ≤ 2 * (w - q)) :
    ∃ centers : Fin q → ℤ × ℤ,
      (∀ i, centers i ∈ parityCap h z σ) ∧
        ∀ p ∈ parityCap h z σ,
          ∃ i, p ∈ integerSquare (centers i) (w - (i.val + 1)) := by
  obtain ⟨centers, hlegal, hband⟩ :=
    exists_shelf_centers hσ hw hz hq2 hqw hcapacity
  refine ⟨centers, hlegal, ?_⟩
  intro p hp
  apply hband p hp
  have hpTop : p.2 ≤ (h + z : ℕ) := hp.2.1
  exact hpTop.trans (by exact_mod_cast Nat.add_le_add_left hterminal h)

/--
In the nonterminal case, every point not covered by the first shelf belongs
to the residual cap with unchanged apex and parity.-/
theorem exists_shelf_centers_with_residual {h z w q : ℕ} {σ : ℤ}
    (hσ : (h + z : ℕ) ≡ σ [ZMOD 2])
    (hw : 3 ≤ w) (hz : w - 1 < z)
    (hq2 : 2 ≤ q) (hqw : q < w) (hcapacity : z ≤ q * (w - q))
    (hnonterminal : 2 * (w - q) < z) :
    ∃ centers : Fin q → ℤ × ℤ,
      (∀ i, centers i ∈ parityCap h z σ) ∧
        (∀ p ∈ parityCap h z σ,
          p.2 ≤ (h + 2 * (w - q) : ℕ) →
            ∃ i, p ∈ integerSquare (centers i) (w - (i.val + 1))) ∧
        ∀ p ∈ parityCap h z σ,
          (∀ i, p ∉ integerSquare (centers i) (w - (i.val + 1))) →
            p ∈ parityCap (h + 2 * (w - q)) (z - 2 * (w - q)) σ := by
  obtain ⟨centers, hlegal, hband⟩ :=
    exists_shelf_centers hσ hw hz hq2 hqw hcapacity
  refine ⟨centers, hlegal, hband, ?_⟩
  intro p hp huncovered
  have hpAbove :
      ((h + 2 * (w - q) : ℕ) : ℤ) ≤ p.2 := by
    by_contra hnot
    have hpY : p.2 ≤ ((h + 2 * (w - q) : ℕ) : ℤ) := by omega
    obtain ⟨i, hi⟩ := hband p hp hpY
    exact huncovered i hi
  exact mem_residual_parityCap (by omega) hp hpAbove

end BurningPath

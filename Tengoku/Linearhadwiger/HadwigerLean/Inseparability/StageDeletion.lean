import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.ConnectedGluing
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.Stages
import Tengoku.Linearhadwiger.HadwigerLean.Woven.DoubleFanCost
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deleting the old model tangencies from a chromatic region

Deleting `d` vertices from a `k`-connected induced region retains every
connectivity guarantee `ℓ` with `d+ℓ≤k`, and costs at most `d` colors.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/--
@isnad1 id=vertexco.3h6v.s6.69f71101b03a from=translated src=- shape=f0b31600 vocab=a2e38803
-/
theorem vertexConnected_induce_sdiff
    (A D : Finset V) (k ℓ : ℕ)
    (hconn : VertexConnected (G.induce (A : Set V)) k)
    (hDA : D ⊆ A) (hbudget : D.card + ℓ ≤ k) :
    VertexConnected (G.induce ((A \ D : Finset V) : Set V)) ℓ := by
  classical
  let R : Finset V := A \ D
  have hRcard : Fintype.card (R : Set V) = R.card := by
    apply Fintype.card_of_finset' R
    intro x
    rfl
  have hAcard : Fintype.card (A : Set V) = A.card := by
    apply Fintype.card_of_finset' A
    intro x
    rfl
  have hsplit := Finset.card_sdiff_add_card_eq_card hDA
  refine ⟨?_, ?_⟩
  · rw [hRcard]
    have hAorder := hconn.order_gt
    rw [hAcard] at hAorder
    change ℓ < R.card
    dsimp [R]
    omega
  · intro U hU
    let E : Finset V := D ∪ U.image Subtype.val
    have hEcard : E.card < k := by
      have h1 := Finset.card_union_le D (U.image Subtype.val)
      have h2 := Finset.card_image_le (s := U) (f := Subtype.val)
      dsimp [E]
      omega
    have hconnE : (G.induce ((A \ E : Finset V) : Set V)).Connected :=
      connected_induce_sdiff_of_vertexConnected A E k hconn hEcard
    have hdiff : A \ E = R \ U.image Subtype.val := by
      ext v
      dsimp only [E, R]
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hconnR :
        (G.induce ((R \ U.image Subtype.val : Finset V) : Set V)).Connected := by
      rw [← hdiff]
      exact hconnE
    exact (deletionIso G R U).connected_iff.mpr hconnR

/--
@isnad1 id=le.1h4v.s6.7b7197cf7b8e from=translated src=- shape=4a703eaf vocab=12404429
-/
theorem chromatic_induce_le_sdiff_add_card
    (G : SimpleGraph V) (A D : Finset V) (hDA : D ⊆ A) :
    chromatic (G.induce (A : Set V)) ≤
      chromatic (G.induce ((A \ D : Finset V) : Set V)) + D.card := by
  have h := Woven.chromatic_induce_le_add_remainder G
    (A : Set V) (D : Set V)
  have hdiff : (A : Set V) \ (D : Set V) =
      ((A \ D : Finset V) : Set V) := by
    ext v
    simp
  rw [hdiff] at h
  have hD : chromatic (G.induce (D : Set V)) ≤ D.card := by
    simpa using chromatic_le_card (G.induce (D : Set V))
  omega

/-- The chromatic and connectivity budgets available after deleting a set
from the stage region.
@isnad1 id=and.2h9v.s7.97b424946a68 from=translated src=- shape=4e69add7 vocab=6735baca
-/
theorem StageState.after_delete
    {s k m coreBound : ℕ}
    (S : StageState G s k m coreBound)
    (D : Finset V) (hD : D ⊆ S.region)
    (ℓ : ℕ) (hbudget : D.card + ℓ ≤ k) :
    VertexConnected (G.induce ((S.region \ D : Finset V) : Set V)) ℓ ∧
    chromatic G ≤
      chromatic (G.induce ((S.region \ D : Finset V) : Set V)) +
        m + D.card := by
  constructor
  · exact vertexConnected_induce_sdiff S.region D k ℓ
      S.region_connected hD hbudget
  · have hχ := chromatic_induce_le_sdiff_add_card G S.region D hD
    have hres := S.chromatic_reserve
    omega

end Inseparability
end HadwigerLean

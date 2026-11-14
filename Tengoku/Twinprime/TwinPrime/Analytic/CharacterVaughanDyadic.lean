import Tengoku.Twinprime.TwinPrime.Analytic.CharacterVaughan
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicBilinearPartition
import Tengoku.Twinprime.TwinPrime.Analytic.VaughanActiveBoxes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact dyadic assembly of the Vaughan Type II term

The coefficient support gives an exact global box partition. Discarded
boxes vanish identically; the finite Type II maximum is bounded by the sum
of the actual box maxima over the remaining active family.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.1h6v.s6.4acd408be0bb from=translated src=- shape=77c706bd vocab=6ec33d6f
-/
theorem characterVaughanII_eq_dyadic_boxes {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    characterVaughanII U V t χ =
      ∑ k ∈ range (dyadicNatDepth T), ∑ j ∈ range (dyadicNatDepth T),
        characterProductCutoffSum χ (vaughanBoxA U T) (vaughanBoxB V T)
          (2 ^ k) (2 ^ j) k j t := by
  rw [characterVaughanII_eq_masked_double_sum U V t T χ ht]
  change (∑ m ∈ Ioc 0 T, ∑ n ∈ Ioc 0 T with m * n ≤ t,
    vaughanBoxA U T m * vaughanBoxB V T n * χ (m * n)) = _
  simp only [characterProductCutoffSum, sum_filter]
  apply sum_Ioc_product_eq_dyadic_of_support _ T
  intro m n h
  rcases h with hm | hn
  · simp [vaughanBoxA_eq_zero_of_gt U T m hm]
  · simp [vaughanBoxB_eq_zero_of_gt V T n hn]

/--
@isnad1 id=eq.1h6v.s6.56d5480e8915 from=translated src=- shape=fa063804 vocab=6e20fb59
-/
theorem characterVaughanII_eq_active_boxes {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    characterVaughanII U V t χ =
      ∑ p ∈ activeVaughanBoxes U V T,
        characterProductCutoffSum χ (vaughanBoxA U T) (vaughanBoxB V T)
          (2 ^ p.1) (2 ^ p.2) p.1 p.2 t := by
  rw [characterVaughanII_eq_dyadic_boxes U V t T χ ht,
    ← sum_product (f := fun p : ℕ × ℕ =>
      characterProductCutoffSum χ (vaughanBoxA U T) (vaughanBoxB V T)
        (2 ^ p.1) (2 ^ p.2) p.1 p.2 t)]
  symm
  apply sum_subset (filter_subset _ _)
  intro p hp hnot
  exact vaughanBox_characterProductCutoffSum_eq_zero_of_not_mem χ U V T p.1 p.2 t ht
    (mem_range.mp (mem_product.mp hp).1) (mem_range.mp (mem_product.mp hp).2) hnot

/--
@isnad1 id=le.1h6v.s6.251d31912798 from=translated src=- shape=eb44a714 vocab=0be67e46
-/
theorem norm_characterVaughanII_le_active_max {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterVaughanII U V t χ‖ ≤
      ∑ p ∈ activeVaughanBoxes U V T,
        characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
          (2 ^ p.1) (2 ^ p.2) p.1 p.2 T := by
  rw [characterVaughanII_eq_active_boxes U V t T χ ht]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p _
  exact Finset.le_sup' (f := fun t => ‖characterProductCutoffSum χ
    (vaughanBoxA U T) (vaughanBoxB V T) (2 ^ p.1) (2 ^ p.2) p.1 p.2 t‖)
    (mem_Icc.mpr ⟨Nat.zero_le t, ht⟩)

/-- The finite endpoint maximum of the full Type II character sum.-/
def characterVaughanIIMax {q : ℕ} (U V T : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Icc 0 T).sup' ⟨0, mem_Icc.mpr ⟨le_rfl, Nat.zero_le T⟩⟩
    (fun t => ‖characterVaughanII U V t χ‖)

/--
@isnad1 id=le.1h6v.s5.1ffd36ed39bc from=translated src=- shape=0931819d vocab=7c80d9e3
-/
theorem norm_characterVaughanII_le_max {q : ℕ} (U V t T : ℕ)
    (χ : DirichletCharacter ℂ q) (ht : t ≤ T) :
    ‖characterVaughanII U V t χ‖ ≤ characterVaughanIIMax U V T χ :=
  Finset.le_sup' (f := fun t => ‖characterVaughanII U V t χ‖)
    (mem_Icc.mpr ⟨Nat.zero_le t, ht⟩)

/--
@isnad1 id=le.0h5v.s5.91c33a0678d8 from=translated src=- shape=98587e5f vocab=b9187acc
-/
theorem characterVaughanIIMax_nonneg {q : ℕ} (U V T : ℕ)
    (χ : DirichletCharacter ℂ q) : 0 ≤ characterVaughanIIMax U V T χ :=
  (norm_nonneg _).trans (norm_characterVaughanII_le_max U V 0 T χ (Nat.zero_le T))

/--
@isnad1 id=le.0h5v.s6.ab14930544a2 from=translated src=- shape=90aafbc0 vocab=9ed6cd28
-/
theorem characterVaughanIIMax_le_active_max {q : ℕ} (U V T : ℕ)
    (χ : DirichletCharacter ℂ q) :
    characterVaughanIIMax U V T χ ≤
      ∑ p ∈ activeVaughanBoxes U V T,
        characterProductCutoffMax χ (vaughanBoxA U T) (vaughanBoxB V T)
          (2 ^ p.1) (2 ^ p.2) p.1 p.2 T := by
  unfold characterVaughanIIMax
  apply Finset.sup'_le
  intro t ht
  exact norm_characterVaughanII_le_active_max U V t T χ (mem_Icc.mp ht).2

end TwinPrime.Analytic

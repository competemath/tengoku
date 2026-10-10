module

public import Tengoku

@[expose] public section

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

namespace IsApproximateSubgroup

open Set in
@[to_additive]
lemma pi {ι : Type*} {G : ι → Type*} [Fintype ι] [∀ i, Group (G i)] {A : ∀ i, Set (G i)} {K : ι → ℝ}
    (hA : ∀ i, IsApproximateSubgroup (K i) (A i)) :
    IsApproximateSubgroup (∏ i, K i) (univ.pi A) where
  one_mem i _ := (hA i).one_mem
  inv_eq_self := by simp [(hA _).inv_eq_self]
  sq_covBySMul := by
    choose F hF hFS using fun i ↦ (hA i).sq_covBySMul
    classical
    refine ⟨Fintype.piFinset F, ?_, ?_⟩
    · calc
        #(Fintype.piFinset F) = ∏ i, (#(F i) : ℝ) := by simp
        _ ≤ ∏ i, K i := by gcongr; exact hF _
    · simp_rw [subset_def, pow_two, mem_mul, mem_univ_pi]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      choose f hfF a ha hfa using fun i ↦ hFS i <| by
        simpa [pow_two] using mul_mem_mul (hx i) (hy i)
      refine ⟨f, by simpa using hfF, a, by simpa using ha, ?_⟩
      ext i
      simpa using hfa i

end IsApproximateSubgroup

import Tengoku.EgzFormalProof.EGZ.Decomposition.Basic
import Tengoku.Seed.Order.Iterate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Growth functions for completeness refinements

One step of the width sequence dominates the requested width after changing
to the bounded lattice coordinates. The same sequence bounds every possible
number of added directions up to the ambient dimension.
-/

namespace EGZ

def refinementGrowth (A g : ℕ → ℕ) (n : ℕ) : ℕ := max (n + 1) (g (A n))

/--
@isnad1 id=isgrowin.2h2v.s4.322bb85b235c from=translated src=- shape=468ff12c vocab=93e01af9
-/
theorem refinementGrowth_isGrowing {A g : ℕ → ℕ} (hA : Monotone A) (hg : Monotone g) :
    IsGrowing (refinementGrowth A g) := by
  constructor
  · intro a b hab
    exact max_le_max (Nat.add_le_add_right hab 1) (hg (hA hab))
  · intro n
    exact (Nat.lt_succ_self n).trans_le (le_max_left _ _)

def refinementWidth (A g : ℕ → ℕ) (K i : ℕ) : ℕ := (refinementGrowth A g)^[i] K

/--
@isnad1 id=eq.0h3v.s4.09200ee4e115 from=translated src=- shape=52ac882e vocab=6bb6d3c7
-/
@[simp]
theorem refinementWidth_zero (A g : ℕ → ℕ) (K : ℕ) : refinementWidth A g K 0 = K := rfl

/--
@isnad1 id=eq.0h4v.s5.6d3d87e9a06e from=translated src=- shape=c1713496 vocab=24babe9f
-/
theorem refinementWidth_succ (A g : ℕ → ℕ) (K i : ℕ) :
    refinementWidth A g K (i + 1) = refinementGrowth A g (refinementWidth A g K i) :=
  Function.iterate_succ_apply' _ _ _

/--
@isnad1 id=monotone.0h3v.s4.6a11da6dfdb6 from=translated src=- shape=61a317ad vocab=a19f757a
-/
theorem refinementWidth_mono (A g : ℕ → ℕ) (K : ℕ) : Monotone (refinementWidth A g K) := by
  intro i j hij
  exact Function.monotone_iterate_of_id_le
    (fun n ↦ (Nat.le_succ n).trans (le_max_left _ _)) hij K

/--
@isnad1 id=le.0h4v.s4.f59e94cc745c from=translated src=- shape=27f30736 vocab=408224cb
-/
theorem le_refinementWidth (A g : ℕ → ℕ) (K i : ℕ) : K ≤ refinementWidth A g K i :=
  refinementWidth_mono A g K (Nat.zero_le i)

/--
@isnad1 id=le.0h4v.s5.41413e00da36 from=translated src=- shape=a5abf9a7 vocab=579a5cb6
-/
theorem desired_width_le_refinementWidth_succ (A g : ℕ → ℕ) (K i : ℕ) :
    g (A (refinementWidth A g K i)) ≤ refinementWidth A g K (i + 1) := by
  rw [refinementWidth_succ]
  exact le_max_right _ _

/--
@isnad1 id=le.1h5v.s5.860006fec8cd from=translated src=- shape=57021525 vocab=408224cb
-/
theorem refinementWidth_le_of_index_le (A g : ℕ → ℕ) (K : ℕ) {i d : ℕ} (hi : i ≤ d) :
    refinementWidth A g K i ≤ refinementWidth A g K d := refinementWidth_mono A g K hi

/--
@isnad1 id=monotone.2h3v.s5.85d14d021d1b from=translated src=- shape=5f15ae78 vocab=a19f757a
-/
theorem refinementWidth_mono_initial {A g : ℕ → ℕ} (hA : Monotone A) (hg : Monotone g)
    (i : ℕ) : Monotone (fun K ↦ refinementWidth A g K i) :=
  (refinementGrowth_isGrowing hA hg).1.iterate i

end EGZ

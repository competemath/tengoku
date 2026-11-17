import Tengoku.SingularityCompleteLean.Singularity.WalkKernel
import Tengoku.Seed.Algebra.Group.Submonoid.Membership

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reachability and strict positivity of the Green kernel

The support must generate as a semigroup (equivalently here, as a submonoid),
and every listed jump has strictly positive weight. Group generation alone is
not used as a substitute for this hypothesis. Green convergence still uses the
operator spectral-gap hypothesis.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Every element in the generated submonoid is the endpoint of a finite jump word.
@isnad1 id=ex.1h3v.s6.1cd0639c9060 from=translated src=- shape=cddb550e vocab=3cbef816
-/
theorem exists_walkWord_of_mem_closure (s : Finset Γ) {g : Γ}
    (hg : g ∈ Submonoid.closure (s : Set Γ)) :
    ∃ (n : ℕ) (w : WalkWord s n), walkEndpoint s n 1 w = g := by
  induction hg using Submonoid.closure_induction_left with
  | one => exact ⟨0, PUnit.unit, rfl⟩
  | mul_left a ha b _ ih =>
    obtain ⟨n, w, hw⟩ := ih
    refine ⟨n + 1, (⟨a, ha⟩, w), ?_⟩
    change walkEndpoint s n (1 * a) w = a * b
    rw [one_mul, ← mul_one a, walkEndpoint_left, hw, mul_one]

/-- Semigroup generation gives a permitted finite path between every pair of states.
@isnad1 id=ex.1h4v.s6.e1927bf82697 from=translated src=- shape=9eefbc8e vocab=33a76c7e
-/
theorem exists_walkWord_between (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    ∃ (n : ℕ) (w : WalkWord s n), walkEndpoint s n x w = y := by
  have hg : x⁻¹ * y ∈ Submonoid.closure (s : Set Γ) := by rw [hgen]; trivial
  obtain ⟨n, w, hw⟩ := exists_walkWord_of_mem_closure s hg
  refine ⟨n, w, ?_⟩
  rw [← mul_one x, walkEndpoint_left, hw, mul_inv_cancel_left]

omit [Group Γ] in
/-- A finite word of strictly positive-weight jumps has strictly positive weight.
@isnad1 id=lt.1h5v.s6.19d7ee198c7e from=translated src=- shape=ef8c2a1f vocab=72f08ea5
-/
theorem walkWeight_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (n : ℕ) (w : WalkWord s n) :
    0 < walkWeight s μ n w := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hμ w.1 w.1.property) (ih w.2)

/-- The weight of any permitted path is bounded by the transition coefficient it contributes to.
@isnad1 id=le.1h6v.s6.b3aca316927e from=translated src=- shape=8a37d99b vocab=4ae02e8c
-/
theorem walkWeight_le_transition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (n : ℕ) (w : WalkWord s n) (x : Γ) :
    walkWeight s μ n w ≤ transitionWeight s μ n x (walkEndpoint s n x w) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun v : WalkWord s n => if walkEndpoint s n x v = walkEndpoint s n x w
      then walkWeight s μ n v else 0)
    (fun v _ => by split_ifs; exact walkWeight_nonneg s μ hμ n v; exact le_rfl)
    (Finset.mem_univ w)
  simpa only [ite_true, transitionWeight] using h

/-- Any positive path gives a positive transition coefficient.
@isnad1 id=lt.2h7v.s6.bfcd618e92c1 from=translated src=- shape=1958b945 vocab=305eeaab
-/
theorem transitionWeight_pos_of_path (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (n : ℕ) (w : WalkWord s n) (x y : Γ)
    (hw : walkEndpoint s n x w = y) : 0 < transitionWeight s μ n x y := by
  subst y
  exact (walkWeight_pos s μ hμ n w).trans_le
    (walkWeight_le_transition s μ (fun g hg => (hμ g hg).le) n w x)

/-- The finite-step transition kernel is irreducible under semigroup generation.
@isnad1 id=ex.2h5v.s6.4a47f15fe291 from=translated src=- shape=232e1da9 vocab=75350f8e
-/
theorem exists_transitionWeight_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    ∃ n, 0 < transitionWeight s μ n x y := by
  obtain ⟨n, w, hw⟩ := exists_walkWord_between s hgen x y
  exact ⟨n, transitionWeight_pos_of_path s μ hμ n w x y hw⟩

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- A positive transition coefficient gives a strictly positive convergent Green entry.
@isnad1 id=lt.3h6v.s12.b7de3f84980c from=translated src=- shape=4b95a103 vocab=36c1a734
-/
theorem walkGreen_pos_of_transition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (x y : Γ) {n : ℕ} (hn : 0 < transitionWeight s μ n x y) : 0 < walkGreen s μ x y :=
  hn.trans_le ((walkGreen_summable s μ hgap x y).le_tsum n
    (fun k _ => transitionWeight_nonneg s μ hμ k x y))

/-- Every Green entry is positive under the actual semigroup-generation hypothesis.
@isnad1 id=lt.3h5v.s12.56103541710e from=translated src=- shape=e58dd290 vocab=ad5d08c1
-/
theorem walkGreen_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) : 0 < walkGreen s μ x y := by
  obtain ⟨n, hn⟩ := exists_transitionWeight_pos s μ hμ hgen x y
  exact walkGreen_pos_of_transition s μ (fun g hg => (hμ g hg).le) hgap x y hn

/-- In particular the canonical Green normalizers never vanish.
@isnad1 id=ne.3h5v.s12.d0224d893d24 from=translated src=- shape=c1daaa48 vocab=ad5d08c1
-/
theorem walkGreen_ne_zero (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) : walkGreen s μ x y ≠ 0 :=
  ne_of_gt (walkGreen_pos s μ hμ hgen hgap x y)

end Singularity

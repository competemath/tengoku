import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1WordBlocks
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry
import Tengoku.Seed.Analysis.Normed.Module.Completion
import Tengoku.Seed.Analysis.Analytic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Synthesis from bounded word coefficients

A bounded family of vectors in a Banach space defines a bounded linear map on ℓ¹. Applied to
the scaled coefficients `s^n p_n(e_{a_1}, …, e_{a_n})` of a power series, this gives the map
`T` in the proof of Theorem 4.5(2), with values in the completion of `H`, and `T` recovers
each homogeneous term on its word block. The scalar field need not be complete.
-/

open scoped BigOperators lp
open Filter Topology

noncomputable section

namespace L1Coordinates

variable {K J W : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup W] [NormedSpace K W]

local instance : DecidableEq J := Classical.decEq J

variable [CompleteSpace W]

/-- The bounded linear map on ℓ¹ sending each basis vector `e_j` to `c j`.-/
def linearOfBounded (c : J → W) (M : ℝ) (hc : ∀ j, ‖c j‖ ≤ M) :
    lp (fun _ : J => K) 1 →L[K] W :=
  continuousMultilinearCurryFin1 K (lp (fun _ : J => K) 1) W
    (continuousMultilinearOfBounded (fun a : Fin 1 → J => c (a 0)) M (fun a => hc (a 0)))

/--
@isnad1 id=eq.1h6v.s12.762b2dba29b6 from=translated src=- shape=4c32ca8f vocab=7082af68
-/
@[simp]
theorem linearOfBounded_single (c : J → W) (M : ℝ) (hc : ∀ j, ‖c j‖ ≤ M) (j : J) :
    linearOfBounded (K := K) c M hc (lp.single 1 j (1 : K)) = c j := by
  classical
  have hs : Fin.snoc 0 (lp.single (E := fun _ : J => K) 1 j (1 : K)) =
      fun _ : Fin 1 => lp.single 1 j (1 : K) := by
    ext i
    fin_cases i
    rfl
  simp only [linearOfBounded, continuousMultilinearCurryFin1_apply, hs]
  exact continuousMultilinearOfBounded_single _ _ _ (fun _ => j)

section WordSynthesis

variable {I H : Type*} [NormedAddCommGroup H] [NormedSpace K H]

local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (Σ n : ℕ, Fin n → I) := Classical.decEq _

/-- The coefficient `s^n p_n(e_{a_1}, …, e_{a_n})` of the word `a`, in the completion of `H`.-/
def wordCoefficient (p : FormalMultilinearSeries K (lp (fun _ : I => K) 1) H)
    (s : K) (j : Σ n : ℕ, Fin n → I) : UniformSpace.Completion H :=
  s ^ j.1 • ((p j.1 (fun i => lp.single 1 (j.2 i) (1 : K)) : H) :
    UniformSpace.Completion H)

/--
@isnad1 id=le.1h7v.s12.b58eb5c57724 from=translated src=- shape=1f9e65dd vocab=2a338912
-/
theorem norm_wordCoefficient_le
    (p : FormalMultilinearSeries K (lp (fun _ : I => K) 1) H) (s : K) (M : ℝ)
    (hp : ∀ n, ‖p n‖ * ‖s‖ ^ n ≤ M) (j : Σ n : ℕ, Fin n → I) :
    ‖wordCoefficient p s j‖ ≤ M := by
  rw [wordCoefficient, norm_smul, norm_pow, UniformSpace.Completion.norm_coe]
  have hbound : ‖p j.1 (fun i => lp.single 1 (j.2 i) (1 : K))‖ ≤ ‖p j.1‖ := by
    simpa using (p j.1).le_opNorm (fun i => lp.single 1 (j.2 i) (1 : K))
  calc
    ‖s‖ ^ j.1 * ‖p j.1 (fun i => lp.single 1 (j.2 i) (1 : K))‖
        ≤ ‖s‖ ^ j.1 * ‖p j.1‖ := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ M := by simpa only [mul_comm] using hp j.1

/-- The bounded linear map on ℓ¹(Words I, K) given by the word coefficients.-/
def wordSynthesis (p : FormalMultilinearSeries K (lp (fun _ : I => K) 1) H)
    (s : K) (M : ℝ) (hp : ∀ n, ‖p n‖ * ‖s‖ ^ n ≤ M) :
    lp (fun _ : (Σ n : ℕ, Fin n → I) => K) 1 →L[K] UniformSpace.Completion H :=
  linearOfBounded (wordCoefficient p s) M (norm_wordCoefficient_le p s M hp)

/--
@isnad1 id=eq.1h8v.s14.c61ec56ed72a from=translated src=- shape=fb1a2c6a vocab=8874a398
-/
@[simp]
theorem wordSynthesis_single
    (p : FormalMultilinearSeries K (lp (fun _ : I => K) 1) H)
    (s : K) (M : ℝ) (hp : ∀ n, ‖p n‖ * ‖s‖ ^ n ≤ M) (n : ℕ) (a : Fin n → I) :
    wordSynthesis p s M hp (lp.single 1 ⟨n, a⟩ (1 : K)) =
      s ^ n • ((p n (fun i => lp.single 1 (a i) (1 : K)) : H) :
        UniformSpace.Completion H) := by
  exact linearOfBounded_single _ _ _ _

end WordSynthesis

end L1Coordinates

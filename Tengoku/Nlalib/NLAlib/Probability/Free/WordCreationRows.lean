import Tengoku.Nlalib.NLAlib.Probability.Free.WordWickNormalOrder
import Tengoku.Seed.Analysis.Normed.Lp.LpEquiv
import Tengoku.Seed.Data.Fintype.Vector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Orthogonal rows of actual fixed-length word creations

The row map is the native orthogonal-family Hilbert-sum isometry composed
with the native finite `lp`/`PiLp` isometry. Empty alphabets and index sets
are included, so its bounded-operator norm is bounded by one uniformly.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct ENNReal

namespace NLAlib

variable {ι : Type*}
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W

/-- The actual isometry prepending a whole word.-/
def wordPrefixIsometry (w : List ι) : W →ₗᵢ[ℂ] W :=
  lp.embeddingLinearIsometry ⟨(w ++ ·), List.append_right_injective w⟩

/-- The whole-word isometry is exactly the ordered creation product.
@isnad1 id=eq.0h2v.s11.e9a62ea87611 from=translated src=- shape=650a6945 vocab=bcec23a2
-/
theorem wordPrefixIsometry_toContinuousLinearMap (w : List ι) :
    (wordPrefixIsometry w).toContinuousLinearMap = wordCreationProduct w := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro v
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    LinearIsometry.coe_toContinuousLinearMap, wordPrefixIsometry]
  calc
    _ = (lp.single 2 (w ++ v) z : W) := by
      convert! lp.embeddingLinearIsometry_apply_single (𝕜 := ℂ)
        (⟨(w ++ ·), List.append_right_injective w⟩ : List ι ↪ List ι) v z using 1
      · congr 1
        ext q
        by_cases hq : q = v <;> simp [lp.single_apply, hq]
      · ext q
        by_cases hq : q = w ++ v <;> simp [lp.single_apply, hq]
    _ = _ := (wordCreationProduct_apply_single w v z).symm

/-- The prefix isometry has the actual ordered-operator action.
@isnad1 id=eq.0h3v.s12.817ea630284b from=translated src=- shape=e15bd0f3 vocab=44a69d57
-/
theorem wordPrefixIsometry_apply (w : List ι) (x : W) :
    wordPrefixIsometry w x = wordCreationProduct w x :=
  congrArg (fun T : B => T x) (wordPrefixIsometry_toContinuousLinearMap w)

/-- Fixed-length creation words have mutually orthogonal ranges; their
actual adjoint products are the Kronecker identity.
@isnad1 id=eq.1h3v.s14.e960bd5a2815 from=translated src=- shape=8f67cede vocab=55b0ba28
-/
theorem star_wordCreationProduct_mul_of_length_eq (u v : List ι)
    (hlen : u.length = v.length) :
    star (wordCreationProduct u) * wordCreationProduct v = if u = v then 1 else 0 := by
  induction u generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    subst v
    simp
  | cons i u hu =>
    cases v with
    | nil => simp at hlen
    | cons j v =>
      have hlen' : u.length = v.length := Nat.succ.inj hlen
      rw [wordCreationProduct_cons, wordCreationProduct_cons, star_mul]
      calc
        _ = star (wordCreationProduct u) *
            (star (wordCreation i).toContinuousLinearMap *
              (wordCreation j).toContinuousLinearMap) * wordCreationProduct v := by
          noncomm_ring
        _ = _ := by
          rw [star_wordCreation_mul_wordCreation]
          by_cases hij : i = j
          · subst j
            simp [hu v hlen']
          · simp [hij]

/-- The actual creation isometries belonging to distinct words of one
fixed length form a native orthogonal family.
@isnad1 id=orthogon.0h2v.s9.ebe69f41b313 from=translated src=- shape=78b4e767 vocab=6f05a4e8
-/
theorem orthogonalFamily_wordPrefixIsometry (m : ℕ) :
    OrthogonalFamily ℂ (fun _ : List.Vector ι m => W)
      (fun w => wordPrefixIsometry w.toList) := by
  intro u v huv x y
  have huv' : u.toList ≠ v.toList := fun h => huv (Subtype.ext h)
  have hzero : star (wordCreationProduct u.toList) * wordCreationProduct v.toList = 0 := by
    rw [star_wordCreationProduct_mul_of_length_eq u.toList v.toList (by simp),
      ite_eq_right huv']
  have h := congrArg (fun T : B => T y) hzero
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.star_eq_adjoint, zero_apply] at h
  rw [← LinearIsometry.coe_toContinuousLinearMap, wordPrefixIsometry_toContinuousLinearMap,
    ← LinearIsometry.coe_toContinuousLinearMap, wordPrefixIsometry_toContinuousLinearMap,
    ← ContinuousLinearMap.adjoint_inner_right, h, inner_zero_right]

/-- The genuine fixed-length creation row from the finite Hilbert direct
sum. It uses the existing orthogonal-family isometry without a new norm.-/
def wordCreationRow [Fintype ι] (m : ℕ) :
    PiLp 2 (fun _ : List.Vector ι m => W) →ₗᵢ[ℂ] W :=
  (orthogonalFamily_wordPrefixIsometry (ι := ι) m).linearIsometry.comp
    (lpPiLpₗᵢ (fun _ : List.Vector ι m => W) ℂ).symm.toLinearIsometry

/-- A fixed-length row acts by the literal finite sum of prefix creations.
@isnad1 id=eq.0h3v.s13.1c4b819d5988 from=translated src=- shape=d3039865 vocab=c8f95292
-/
theorem wordCreationRow_apply [Fintype ι] (m : ℕ)
    (x : PiLp 2 (fun _ : List.Vector ι m => W)) :
    wordCreationRow m x = ∑ w, wordCreationProduct w.toList (x w) := by
  change (orthogonalFamily_wordPrefixIsometry (ι := ι) m).linearIsometry
    ((lpPiLpₗᵢ (fun _ : List.Vector ι m => W) ℂ).symm x) = _
  rw [OrthogonalFamily.linearIsometry_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro w _
  change wordPrefixIsometry w.toList (x w) = wordCreationProduct w.toList (x w)
  exact congrArg (fun T : B => T (x w)) (wordPrefixIsometry_toContinuousLinearMap w.toList)

/-- The native creation row has norm at most one, including empty rows.
@isnad1 id=le.0h2v.s12.ee3191093e5b from=translated src=- shape=da24d6ec vocab=40c6f406
-/
theorem norm_wordCreationRow_le_one [Fintype ι] (m : ℕ) :
    ‖(wordCreationRow (ι := ι) m).toContinuousLinearMap‖ ≤ 1 :=
  (wordCreationRow m).norm_toContinuousLinearMap_le

end NLAlib

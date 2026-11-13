import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardPrelim
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardTaylor
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardSteps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sard's theorem: the main induction

`Submission.sard_pi`: for any `p q : ℕ`, an open `U ⊆ ℝ^p` (as `Fin p → ℝ`) and
a `C^∞` map `f : ℝ^p → ℝ^q` on `U`, the set of critical values
`f '' {x ∈ U | ¬Surjective (fderiv ℝ f x)}` is Lebesgue-null.

This is Milnor's induction on `p`: the critical set is decomposed as
`(C \ C₁) ∪ ⋃ᵢ (Cᵢ \ Cᵢ₊₁) ∪ C_{p}`, and the three kinds of pieces are handled
by `step1_local`, `step2_local` and `step3` respectively.
-/

namespace Submission

noncomputable section

open Function MeasureTheory Metric Set Filter
open scoped ContDiff Topology

/-- If `P 0` holds and `P m` fails, there is a last index where `P` holds.
@isnad1 id=ex.1h3v.s5.a718c72124af from=translated src=- shape=c5a50918 vocab=13a96747
-/
theorem exists_last_true {P : ℕ → Prop} {m : ℕ} (h0 : P 0) (hm : ¬P m) :
    ∃ i < m, P i ∧ ¬P (i + 1) := by
  induction m with
  | zero => exact absurd h0 hm
  | succ m IH =>
    by_cases hPm : P m
    · exact ⟨m, Nat.lt_succ_self m, hPm, hm⟩
    · obtain ⟨i, hi, h⟩ := IH hPm
      exact ⟨i, by omega, h⟩

/-- Maps into the zero-dimensional space have no critical points.
@isnad1 id=eq.0h3v.s5.01c2aefe72fa from=translated src=- shape=4b7fdd66 vocab=854e4c63
-/
theorem critSet_target_zero {p : ℕ} (U : Set (Fin p → ℝ))
    (f : (Fin p → ℝ) → Fin 0 → ℝ) : critSet U f = ∅ := by
  ext x
  simp only [critSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and,
    not_not]
  intro _ y
  exact ⟨0, Subsingleton.elim _ _⟩

/-- **Sard's theorem** for `C^∞` maps between the concrete Euclidean spaces
`Fin p → ℝ` and `Fin q → ℝ` (with an open domain of definition).
@isnad1 id=eq.2h4v.s8.ae4133caab3b from=translated src=- shape=e9f9daad vocab=a696e796
-/
theorem sard_pi :
    ∀ (p q : ℕ) (U : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → Fin q → ℝ),
      IsOpen U → ContDiffOn ℝ ∞ f U → volume (f '' critSet U f) = 0 := by
  intro p
  induction p with
  | zero =>
    intro q U f _ _
    cases q with
    | zero =>
      rw [critSet_target_zero, image_empty, measure_empty]
    | succ q' =>
      have hsub : f '' critSet U f ⊆ {f default} := by
        rintro _ ⟨x, _, rfl⟩
        have hx : x = default := Subsingleton.elim x default
        rw [hx]
        exact mem_singleton _
      exact measure_mono_null hsub (volume_singleton_pi _)
  | succ n IHn =>
    intro q U f hU hf
    cases q with
    | zero =>
      rw [critSet_target_zero, image_empty, measure_empty]
    | succ q' =>
      -- decompose the critical set
      have hcover : f '' critSet U f ⊆
          (⋃ i : ℕ, f '' (critSet U f
            ∩ (vanishSet U f i \ vanishSet U f (i + 1))))
          ∪ f '' vanishSet U f (n + 1) := by
        rintro _ ⟨x, hxC, rfl⟩
        by_cases hK : x ∈ vanishSet U f (n + 1)
        · exact Or.inr ⟨x, hK, rfl⟩
        · left
          have h0 : x ∈ vanishSet U f 0 :=
            ⟨hxC.1, fun j hj1 hj0 => absurd (hj1.trans hj0) (by omega)⟩
          obtain ⟨i, _, hPi, hPi1⟩ :=
            exists_last_true (P := fun i => x ∈ vanishSet U f i) h0 hK
          exact mem_iUnion.2 ⟨i, ⟨x, ⟨hxC, hPi, hPi1⟩, rfl⟩⟩
      refine measure_mono_null hcover (measure_union_null ?_ ?_)
      · -- steps 1 and 2
        rw [measure_iUnion_null_iff]
        intro i
        cases i with
        | zero =>
          -- Step 1: `C \ C₁`
          apply image_null_of_locally_image_null
          intro x hx
          have hxC : x ∈ critSet U f := hx.1
          have hxK1 : x ∉ vanishSet U f 1 := hx.2.2
          have hfd : fderiv ℝ f x ≠ 0 := by
            intro h0
            apply hxK1
            refine ⟨hxC.1, fun j hj1 hj2 => ?_⟩
            have hj : j = 1 := by omega
            subst hj
            refine ContinuousMultilinearMap.ext fun m => ?_
            rw [iteratedFDeriv_one_apply, h0]
            simp
          obtain ⟨V, hV, hnull⟩ := step1_local hU hf
            (fun U' g hU' hg => IHn q' U' g hU' hg) hxC.1 hfd
          refine ⟨V, hV, measure_mono_null (Set.image_mono ?_) hnull⟩
          exact inter_subset_inter_left _ fun y hy => hy.1
        | succ i =>
          -- Step 2: `C_{i+1} \ C_{i+2}`
          apply image_null_of_locally_image_null
          intro x hx
          obtain ⟨V, hV, hnull⟩ := step2_local hU hf
            (Nat.succ_le_succ (Nat.zero_le i))
            (fun U' g hU' hg => IHn (q' + 1) U' g hU' hg) hx.2.1 hx.2.2
          refine ⟨V, hV, measure_mono_null (Set.image_mono ?_) hnull⟩
          exact inter_subset_inter_left _ fun y hy => hy.2.1
      · -- Step 3: `C_{n+1}`
        refine step3 hU hf ?_
        calc n + 1 + 1 = (n + 1 + 1) * 1 := by ring
          _ ≤ (n + 1 + 1) * (q' + 1) := by
            exact Nat.mul_le_mul_left _ (by omega)

end

end Submission

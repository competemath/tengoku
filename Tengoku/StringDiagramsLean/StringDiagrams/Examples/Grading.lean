import Tengoku.StringDiagramsLean.StringDiagrams.Grading
import Tengoku.StringDiagramsLean.StringDiagrams.Examples.FreeDots
import Tengoku.StringDiagramsLean.StringDiagrams.Examples.TemperleyLieb

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples of graded presentations

* The free-dots presentation (`StringDiagrams.Examples.FreeDots`) is homogeneous for the
  grading with a dot in degree `2`. Consequently the endomorphism algebra of `n` strands is a
  `ℤ`-graded `R`-algebra (`FreeDots.gradedAlgebra`), with `x n i` of degree `2` and its
  `k`-th power of degree `2 k` (`FreeDots.x_pow_mem_endDeg`).
* The Temperley–Lieb presentation is homogeneous for the grading with a cup in degree `t` and
  a cap in degree `-t`, for every `t : ℤ` (the zigzag relations force the degrees of cup and cap
  to be opposite). The generators `e m i` have degree `0`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

/-! ## Free commuting dots -/

namespace FreeDots

/-- The grading of the free-dots signature with a dot in degree `2`.-/
def deg : Gen → ℤ
  | .dot => 2

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h2v.s4.2b605597a879 from=translated src=- shape=a0979343 vocab=c955898f
-/
@[simp] theorem degree_dlay {n i : ℕ} (h : i < n) :
    Diagram.degree (S := sig) deg (dlay h) = 2 := by
  simp [dlay, lay, deg]

variable (R : Type*) [CommRing R]

/-- The free-dots presentation is homogeneous (it has no relations).
@isnad1 id=ishomoge.0h1v.s3.e1a8bc687e43 from=translated src=- shape=5bb0bbb5 vocab=50f17290
-/
theorem pres_isHomogeneous : (pres R).IsHomogeneous (S := sig) deg :=
  fun r => r.elim

/-- A dot has degree `2`.
@isnad1 id=mem.0h3v.s8.63c400fcf7f0 from=translated src=- shape=b3e9f918 vocab=09ad8d80
-/
theorem x_mem_endDeg (n i : ℕ) : x R n i ∈ (pres R).endDeg deg (strands n) 2 := by
  unfold x
  split_ifs with h
  · exact Presentation.diag_mem_homDeg' (degree_dlay h)
  · exact Submodule.zero_mem _

set_option backward.isDefEq.respectTransparency false in
/-- A product of `k` dots has degree `2 k`.
@isnad1 id=mem.0h4v.s8.7e7e5a842e64 from=translated src=- shape=e89e4060 vocab=60588509
-/
theorem x_pow_mem_endDeg (n i k : ℕ) :
    x R n i ^ k ∈ (pres R).endDeg deg (strands n) (2 * k) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    exact SetLike.GradedOne.one_mem
  | succ k ih =>
    rw [pow_succ, show (2 : ℤ) * ↑(k + 1) = 2 * k + 2 by push_cast; ring]
    exact SetLike.GradedMul.mul_mem ih (x_mem_endDeg R n i)

/-- The endomorphism algebra of `n` strands is a `ℤ`-graded `R`-algebra.-/
@[instance_reducible]
def gradedAlgebra (n : ℕ) : GradedAlgebra ((pres R).endDeg deg (strands n)) :=
  (pres R).gradedAlgebra (pres_isHomogeneous R) (strands n)

/-- Every Hom-space is the direct sum of its homogeneous parts.
@isnad1 id=isintern.0h3v.s9.fe312d2fbdcb from=translated src=- shape=6d5d8f9c vocab=8e94c305
-/
theorem isInternal_homDeg (a b : Obj sig) :
    DirectSum.IsInternal ((pres R).homDeg deg a b) :=
  (pres R).isInternal_homDeg (pres_isHomogeneous R) a b

end FreeDots

/-! ## The Temperley–Lieb category -/

namespace TemperleyLieb

/-- The grading of the Temperley–Lieb signature with a cup in degree `t` and a cap in degree
`-t`.-/
def deg (t : ℤ) : Gen → ℤ
  | .cup => t
  | .cap => -t

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s5.37eb64bed474 from=translated src=- shape=f1fba6fd vocab=430d6701
-/
@[simp] theorem degree_dcup (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    Diagram.degree (S := sig) (deg t) (dcup h) = t := by
  simp [dcup, lay, deg]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h3v.s5.5083fb679af6 from=translated src=- shape=2e667a23 vocab=56b324c5
-/
@[simp] theorem degree_dcap (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    Diagram.degree (S := sig) (deg t) (dcap h) = -t := by
  simp [dcap, lay, deg]

variable {R : Type*} [CommRing R] (δ : R)

set_option backward.isDefEq.respectTransparency false in
/-- The Temperley–Lieb presentation is homogeneous for every grading `deg t`.
@isnad1 id=ishomoge.0h3v.s4.55cd1ffe66c6 from=translated src=- shape=baac44a0 vocab=ab1369ea
-/
theorem pres_isHomogeneous (t : ℤ) : (pres R δ).IsHomogeneous (S := sig) (deg t) := by
  intro r
  refine ⟨0, ?_⟩
  cases r with
  | loop =>
    exact Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp))
      (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _)))
  | zigzagA =>
    exact Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp))
      (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _))
  | zigzagB =>
    exact Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (by simp))
      (LinDiagram.of_mem_homDeg' (Diagram.degree_id _ _))

/-- A cup has degree `t`.
@isnad1 id=mem.1h5v.s10.0ca5090d68c7 from=translated src=- shape=43210e92 vocab=d0d7abe4
-/
theorem diag_dcup_mem_homDeg (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    (pres R δ).diag (dcup h) ∈ (pres R δ).homDeg (deg t) (strands m) (strands (m + 2)) t :=
  Presentation.diag_mem_homDeg' (degree_dcup t h)

/-- A cap has degree `-t`.
@isnad1 id=mem.1h5v.s10.e8fb14fe9ea1 from=translated src=- shape=4432305d vocab=8a466cab
-/
theorem diag_dcap_mem_homDeg (t : ℤ) {m i : ℕ} (h : i ≤ m) :
    (pres R δ).diag (dcap h) ∈ (pres R δ).homDeg (deg t) (strands (m + 2)) (strands m) (-t) :=
  Presentation.diag_mem_homDeg' (degree_dcap t h)

/-- The Temperley–Lieb generators have degree `0`.
@isnad1 id=mem.0h5v.s8.20a12385cf3b from=translated src=- shape=31b36768 vocab=df6a953a
-/
theorem e_mem_endDeg (t : ℤ) (m i : ℕ) :
    e δ m i ∈ (pres R δ).endDeg (deg t) (strands (m + 2)) 0 := by
  unfold e
  split_ifs with h
  · have :=
      Presentation.comp_mem_homDeg (diag_dcap_mem_homDeg δ t h) (diag_dcup_mem_homDeg δ t h)
    rwa [neg_add_cancel] at this
  · exact Submodule.zero_mem _

end TemperleyLieb

end StringDiagrams

end

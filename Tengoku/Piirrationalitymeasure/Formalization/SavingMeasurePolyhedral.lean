import Tengoku.Piirrationalitymeasure.Formalization.LocalPolyhedral
import Tengoku.Piirrationalitymeasure.Formalization.SavingCellPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual translated saving measure has an exact local polyhedral model. -/

namespace PiIrrationality

open Filter
open scoped Topology

namespace LocalPolyhedral

noncomputable def affine_plane (d s t : ℝ) :
    LocalPolyhedral (fun z : ℝ × ℝ => d + s * z.1 + t * z.2) := by
  let l : (ℝ × ℝ) →L[ℝ] ℝ :=
    s • ContinuousLinearMap.fst ℝ ℝ ℝ + t • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact (affine d l).congr (Eventually.of_forall (by
    intro z
    change d + (s * z.1 + t * z.2) = _
    ring))

noncomputable def affine_plane_div (d s t r : ℝ) :
    LocalPolyhedral (fun z : ℝ × ℝ => (d + s * z.1 + t * z.2) / r) := by
  exact (affine_plane (d / r) (s / r) (t / r)).congr
    (Eventually.of_forall (by intro z; ring))

end LocalPolyhedral

noncomputable def savingCellThresholdPolyhedral (a b c : ℝ) (i j k : ℤ) :
    LocalPolyhedral (fun z => savingCellThreshold a b c z i j k) := by
  exact (LocalPolyhedral.affine_plane_div
    ((i : ℝ) + 2 * j - k - 1 / 2) (-1) (-2) (a + 2 * b - c)).congr
      (Eventually.of_forall (by intro z; unfold savingCellThreshold; ring))

noncomputable def savingCellLowerPolyhedral (a b c : ℝ) (i j k : ℤ) :
    LocalPolyhedral (fun z => savingCellLower a b c z i j k) := by
  classical
  have A : LocalPolyhedral (fun z : ℝ × ℝ => ((i : ℝ) - 1 / 2 - z.1) / a) :=
    (LocalPolyhedral.affine_plane_div ((i : ℝ) - 1 / 2) (-1) 0 a).congr
      (Eventually.of_forall (by intro z; ring))
  have B : LocalPolyhedral (fun z : ℝ × ℝ => ((j : ℝ) - z.2) / b) :=
    (LocalPolyhedral.affine_plane_div j 0 (-1) b).congr
      (Eventually.of_forall (by intro z; ring))
  have Q : LocalPolyhedral (fun z =>
      if a + 2 * b - c < 0 then savingCellThreshold a b c z i j k else 0) := by
    by_cases hq : a + 2 * b - c < 0
    · simpa only [hq, ite_true] using savingCellThresholdPolyhedral a b c i j k
    · simpa only [hq, ite_false] using (LocalPolyhedral.const (E := ℝ × ℝ) 0)
  exact (LocalPolyhedral.const 0).max (A.max (B.max ((LocalPolyhedral.const ((k : ℝ) / c)).max Q)))

noncomputable def savingCellUpperPolyhedral (a b c : ℝ) (i j k : ℤ) :
    LocalPolyhedral (fun z => savingCellUpper a b c z i j k) := by
  classical
  have A : LocalPolyhedral (fun z : ℝ × ℝ => ((i : ℝ) + 1 / 2 - z.1) / a) :=
    (LocalPolyhedral.affine_plane_div ((i : ℝ) + 1 / 2) (-1) 0 a).congr
      (Eventually.of_forall (by intro z; ring))
  have B : LocalPolyhedral (fun z : ℝ × ℝ => ((j : ℝ) + 1 - z.2) / b) :=
    (LocalPolyhedral.affine_plane_div ((j : ℝ) + 1) 0 (-1) b).congr
      (Eventually.of_forall (by intro z; ring))
  have Q : LocalPolyhedral (fun z =>
      if 0 < a + 2 * b - c then savingCellThreshold a b c z i j k else 1) := by
    by_cases hq : 0 < a + 2 * b - c
    · simpa only [hq, ite_true] using savingCellThresholdPolyhedral a b c i j k
    · simpa only [hq, ite_false] using (LocalPolyhedral.const (E := ℝ × ℝ) 1)
  exact (LocalPolyhedral.const 1).min
    (A.min (B.min ((LocalPolyhedral.const (((k : ℝ) + 1) / c)).min Q)))

noncomputable def savingMeasurePolyhedral {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0) :
    LocalPolyhedral (translatedSavingMeasure a b c) := by
  let F := fun p : ℤ × ℤ × ℤ => fun z : ℝ × ℝ =>
    max 0 (savingCellUpper a b c z p.1 p.2.1 p.2.2 -
      savingCellLower a b c z p.1 p.2.1 p.2.2)
  have M (p : ℤ × ℤ × ℤ) : LocalPolyhedral (F p) :=
    (LocalPolyhedral.const 0).max
      ((savingCellUpperPolyhedral a b c p.1 p.2.1 p.2.2).sub
        (savingCellLowerPolyhedral a b c p.1 p.2.1 p.2.2))
  apply (LocalPolyhedral.sum (savingCellIndices a b c) F (fun p _ => M p)).congr
  have hn : ContinuousAt parameterNormOne (0 : ℝ × ℝ) := by
    unfold parameterNormOne
    fun_prop
  have he : ∀ᶠ z : ℝ × ℝ in 𝓝 0, parameterNormOne z < 1 :=
    hn.eventually_lt continuousAt_const (by norm_num [parameterNormOne])
  filter_upwards [he] with z hz
  exact (translatedSavingMeasure_eq_cell_sum ha hb hc hq hz.le).symm

end PiIrrationality

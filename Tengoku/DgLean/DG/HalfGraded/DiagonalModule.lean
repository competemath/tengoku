import Tengoku.DgLean.DG.HalfGraded.Diagonal
import Tengoku.DgLean.DG.Category.WeightComparison
import Tengoku.Seed.Algebra.Module.GradedModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordinary dg modules in the diagonal half-grading

The original module action induces an action on the half-regraded direct sums.
The resulting bigraded dg module gives a module over the weight dg category of
`HalfGradedDGRing.ofDGRing A`. No field or boundedness hypothesis is needed.
-/

open scoped DG

open DirectSum

namespace DG.Diagonal

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A M : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]

/-- The half-regraded diagonal ordinary module, with all periodic copies retained.-/
abbrev RegradedModule := HalfRegrade (grading M) 2

/--
@isnad1 id=gradedsm.0h2v.s7.ac78c0e2de14 from=translated src=- shape=bd8acb96 vocab=c10729fc
-/
instance gradedSMul : SetLike.GradedSMul
    (halfGrading (HalfGradedDGRing.ofDGRing A).hgrading 2)
    (halfGrading (grading M) 2) where
  smul_mem p q a m ha hm := by
    change a • m ∈ grading M (halfDegree 2 (p + q))
    rw [map_add]
    exact smul_mem ha hm

instance instModule : Module (HalfGradedDGRing.ofDGRing A).Regraded (RegradedModule M) :=
  inferInstanceAs (Module
    (⨁ p : ℤ × ℤ, ↥(halfGrading (HalfGradedDGRing.ofDGRing A).hgrading 2 p))
    (⨁ p : ℤ × ℤ, ↥(halfGrading (grading M) 2 p)))

variable {A M}

/-- The regraded action is the original action on each pair of homogeneous generators.
@isnad1 id=eq.2h6v.s10.139c3527c4f0 from=translated src=- shape=8aa4e152 vocab=6605a1b5
-/
theorem place_smul_mk {p q : ℤ × ℤ} {a : A} {m : M}
    (ha : a ∈ grading A (halfDegree 2 p)) (hm : m ∈ grading M (halfDegree 2 q)) :
    (HalfGradedDGRing.ofDGRing A).place p a ha • HalfRegrade.mk (grading M) 2 q m hm =
      HalfRegrade.mk (grading M) 2 (p + q) (a • m)
        (by rw [map_add]; exact smul_mem ha hm) :=
  DirectSum.Gmodule.of_smul_of
    (fun p => ↥(halfGrading (HalfGradedDGRing.ofDGRing A).hgrading 2 p))
    (fun p => ↥(halfGrading (grading M) 2 p)) ⟨a, ha⟩ ⟨m, hm⟩

variable (M)

instance instDGAddCommGroup : DGAddCommGroup (RegradedModule M) where
  grading := HalfRegrade.cohGrading (grading M) 2
  decomposition := HalfRegrade.instDecompositionCohGrading _ _
  d := HalfRegrade.dHom (grading M) 2 d (fun hm => d_mem hm)
  d_mem' := HalfRegrade.dHom_mem_cohGrading _ _
  d_d' := HalfRegrade.dHom_dHom _ _ DG.d_d

instance instInternalGrading : InternalGrading (RegradedModule M) where
  wgrading := HalfRegrade.weightGrading (grading M) 2
  wdecomposition := HalfRegrade.instDecompositionWeightGrading _ _
  isHomogeneous_grading' := HalfRegrade.isHomogeneous_cohGrading
  d_mem_wgrading' := HalfRegrade.dHom_mem_weightGrading _ _ (hd := fun hm => d_mem hm)

variable {M}

/--
@isnad1 id=eq.1h3v.s10.d14c0b898eac from=translated src=- shape=7c326f41 vocab=d9bbb07f
-/
@[simp] theorem d_mk (p : ℤ × ℤ) (m : M) (hm : m ∈ grading M (halfDegree 2 p)) :
    d (HalfRegrade.mk (grading M) 2 p m hm) =
      HalfRegrade.mk (grading M) 2 (p + (1, 0)) (d m)
        (by rw [halfDegree_add_one_zero]; exact d_mem hm) :=
  HalfRegrade.dHom_mk _ _ (hd := fun hm => d_mem hm) _ _ _

private theorem mk_add_of_eq {p₁ p₂ p : ℤ × ℤ} (h₁ : p₁ = p) (h₂ : p₂ = p)
    {m m' : M} (hm : m ∈ grading M (halfDegree 2 p₁))
    (hm' : m' ∈ grading M (halfDegree 2 p₂)) :
    HalfRegrade.mk (grading M) 2 p₁ m hm + HalfRegrade.mk (grading M) 2 p₂ m' hm' =
      HalfRegrade.mk (grading M) 2 p (m + m')
        (by subst h₁ h₂; exact add_mem hm hm') := by
  subst h₁ h₂
  exact (HalfRegrade.mk_add _ hm hm').symm

variable (A M)

/--
@isnad1 id=dgmodule.0h2v.s6.2106acd62613 from=translated src=- shape=17a38ff3 vocab=ba402b72
-/
instance instDGModule : DGModule (HalfGradedDGRing.ofDGRing A).Regraded (RegradedModule M) where
  smul_mem i j x y hx hy := by
    refine HalfGradedDGRing.grading_induction
      (P := fun x => x • y ∈ DG.grading (i + j)) (by simp)
      (fun w a ha => ?_) (fun _ _ h h' => by rw [add_smul]; exact add_mem h h') hx
    refine HalfRegrade.cohGrading_induction
      (P := fun y => (HalfGradedDGRing.ofDGRing A).place (i, w) a ha • y ∈ DG.grading (i + j))
      (by simp) (fun w' m hm => ?_)
      (fun _ _ h h' => by rw [smul_add]; exact add_mem h h') hy
    rw [place_smul_mk]
    exact HalfRegrade.mk_mem_cohGrading ((i, w) + (j, w')) _
  d_smul' {n x} hx y := by
    refine HalfGradedDGRing.grading_induction
      (P := fun x => d (x • y) = d x • y + koszulSign n • (x • d y))
      (by simp) (fun w a ha => ?_)
      (fun x x' h h' => by
        rw [add_smul, d_add, h, h', d_add, add_smul, add_smul, smul_add]; abel) hx
    induction y using HalfRegrade.induction_on with
    | zero => simp
    | mk q m hm =>
      rw [place_smul_mk, d_mk, HalfGradedDGRing.d_place, d_mk,
        place_smul_mk, place_smul_mk, ← HalfRegrade.mk_units_smul]
      have h₁ : (n, w) + (1, 0) + q = (n, w) + q + (1, 0) := by abel
      have h₂ : (n, w) + (q + (1, 0)) = (n, w) + q + (1, 0) := by abel
      simp only [HalfGradedDGRing.ofDGRing_hd]
      rw [mk_add_of_eq h₁ h₂]
      exact HalfRegrade.mk_congr rfl (d_smul ha m) _ _
    | add y y' hy hy' =>
      rw [smul_add, d_add, hy, hy', d_add, smul_add, smul_add, smul_add]; abel

/--
@isnad1 id=bigraded.0h2v.s7.cb4f47721a7b from=translated src=- shape=e37f8c29 vocab=ff27fe2a
-/
instance instBigradedDGModule :
    BigradedDGModule (HalfGradedDGRing.ofDGRing A).Regraded (RegradedModule M) where
  smul_mem i j x y hx hy := by
    refine HalfGradedDGRing.wgrading_induction
      (P := fun x => x • y ∈ wgrading (i + j)) (by simp)
      (fun n a ha => ?_) (fun _ _ h h' => by rw [add_smul]; exact add_mem h h') hx
    refine HalfRegrade.weightGrading_induction
      (P := fun y => (HalfGradedDGRing.ofDGRing A).place (n, i) a ha • y ∈ wgrading (i + j))
      (by simp) (fun n' m hm => ?_)
      (fun _ _ h h' => by rw [smul_add]; exact add_mem h h') hy
    rw [place_smul_mk]
    exact HalfRegrade.mk_mem_weightGrading ((n, i) + (n', j)) _

/-- An ordinary dg module as a module over the diagonal half-graded weight category.-/
def toCatModuleObj : CatModule (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded) :=
  BigradedDGModuleCat.toCatModuleObj
    (BigradedDGModuleCat.of (HalfGradedDGRing.ofDGRing A).Regraded (RegradedModule M))

/-- At weight zero the component in cohomological degree `n` is exactly `Mⁿ`.
@isnad1 id=eq.0h2v.s5.1331ffccf775 from=translated src=- shape=7cf67515 vocab=ca5392f3
-/
theorem halfGrading_zero_weight (n : ℤ) :
    halfGrading (grading M) 2 (n, 0) = DG.grading (M := M) n := by
  change grading M (halfDegree 2 (n, 0)) = _
  simpa only [halfDegree_apply, diagonalDegree_apply, zero_add, mul_comm] using
    grading_diagonal (M := M) n

/-- An original homogeneous element as an element of the weight-zero module.-/
def toWeightZero (n : ℤ) : DG.grading (M := M) n →+
    (toCatModuleObj A M).obj ⟨0⟩ where
  toFun m := ⟨HalfRegrade.mk (grading M) 2 (n, 0) m
      (by change m.1 ∈ halfGrading (grading M) 2 (n, 0)
          rw [halfGrading_zero_weight]; exact m.2),
    HalfRegrade.mk_mem_weightGrading (n, 0) _⟩
  map_zero' := Subtype.ext (HalfRegrade.mk_zero _)
  map_add' m m' := Subtype.ext (HalfRegrade.mk_add _ _ _)

end

end DG.Diagonal

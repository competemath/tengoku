import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.OrdinaryStructure

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

def diagonalSymbols : StarSubalgebra ℂ (Base → ℤ → ℂ) where
  carrier := {a | (∀ j, Measurable (fun x => a x j)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x j, ‖a x j‖ ≤ C}
  zero_mem' := ⟨fun _ => measurable_const, 0, le_rfl, by simp⟩
  one_mem' := ⟨fun _ => measurable_const, 1, zero_le_one, by simp⟩
  add_mem' := by
    rintro a b ⟨ha,C,hC,hCa⟩ ⟨hb,D,hD,hDb⟩
    exact ⟨fun j => (ha j).add (hb j), C+D, add_nonneg hC hD,
      fun x j => (norm_add_le _ _).trans (add_le_add (hCa x j) (hDb x j))⟩
  mul_mem' := by
    rintro a b ⟨ha,C,hC,hCa⟩ ⟨hb,D,hD,hDb⟩
    refine ⟨fun j => (ha j).mul (hb j), C*D, mul_nonneg hC hD, fun x j => ?_⟩
    change ‖a x j * b x j‖ ≤ C*D
    rw [norm_mul]
    exact mul_le_mul (hCa x j) (hDb x j) (norm_nonneg _) hC
  algebraMap_mem' c := ⟨fun _ => measurable_const, ‖c‖, norm_nonneg c, fun _ _ => le_rfl⟩
  star_mem' := by
    rintro a ⟨ha,C,hC,hCa⟩
    refine ⟨fun j => continuous_star.measurable.comp (ha j), C,hC, fun x j => ?_⟩
    simpa using hCa x j
abbrev DiagonalSymbol := ↥diagonalSymbols
namespace DiagonalSymbol
instance : CoeFun DiagonalSymbol (fun _ => Base → ℤ → ℂ) := ⟨fun a => a.val⟩
/--
@isnad1 id=measurab.0h2v.s8.8ec8af1a3a83 from=translated src=- shape=22b83929 vocab=db84f08d
-/
lemma measurable (a : DiagonalSymbol) (j : ℤ) : Measurable (fun x => a x j) := a.property.1 j
noncomputable def bound (a : DiagonalSymbol) : ℝ := a.property.2.choose
/--
@isnad1 id=le.0h1v.s3.d7d3443e8665 from=translated src=- shape=b9369acb vocab=c8800c60
-/
lemma bound_nonneg (a : DiagonalSymbol) : 0 ≤ a.bound := a.property.2.choose_spec.1
/--
@isnad1 id=le.0h3v.s8.92d2d1c051c4 from=translated src=- shape=c1e44ece vocab=d6a2ddb7
-/
lemma norm_le_bound (a : DiagonalSymbol) (x : Base) (j : ℤ) : ‖a x j‖ ≤ a.bound :=
  a.property.2.choose_spec.2 x j
/--
@isnad1 id=eq.0h2v.s9.e18626aab139 from=translated src=- shape=abb59879 vocab=c34a94d2
-/
@[simp] lemma zero_apply (x : Base) (j : ℤ) : (0 : DiagonalSymbol) x j = 0 := rfl
/--
@isnad1 id=eq.0h2v.s9.26449884349b from=translated src=- shape=abb59879 vocab=c34a94d2
-/
@[simp] lemma one_apply (x : Base) (j : ℤ) : (1 : DiagonalSymbol) x j = 1 := rfl
/--
@isnad1 id=eq.0h4v.s10.309fd6f2afa3 from=translated src=- shape=41603bf9 vocab=50a010d1
-/
@[simp] lemma add_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a+b) x j = a x j + b x j := rfl
/--
@isnad1 id=eq.0h4v.s10.729c75d3e19e from=translated src=- shape=41603bf9 vocab=9cd098eb
-/
@[simp] lemma mul_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a*b) x j = a x j * b x j := rfl
/--
@isnad1 id=eq.0h4v.s10.40ecd22e5db8 from=translated src=- shape=41603bf9 vocab=d84b84bc
-/
@[simp] lemma sub_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a-b) x j = a x j - b x j := rfl
/--
@isnad1 id=eq.0h3v.s9.9d9a4f0929d6 from=translated src=- shape=e2158286 vocab=ada2275b
-/
@[simp] lemma star_apply (a : DiagonalSymbol) (x : Base) (j : ℤ) : (star a) x j = star (a x j) := rfl
/--
@isnad1 id=eq.0h4v.s9.c8f8b1410897 from=translated src=- shape=8d7abe82 vocab=436a7ff5
-/
@[simp] lemma smul_apply (c : ℂ) (a : DiagonalSymbol) (x : Base) (j : ℤ) : (c • a) x j = c * a x j := rfl
/--
@isnad1 id=eq.0h3v.s10.e76c28742520 from=translated src=- shape=560639ac vocab=5056510a
-/
@[simp] lemma algebraMap_apply (c : ℂ) (x : Base) (j : ℤ) :
    algebraMap ℂ DiagonalSymbol c x j = c := rfl
/--
@isnad1 id=eq.0h4v.s9.fc37c4595389 from=translated src=- shape=c59a626c vocab=99ad65f5
-/
@[simp] lemma pow_apply (a : DiagonalSymbol) (n : ℕ) (x : Base) (j : ℤ) :
    (a^n) x j = (a x j)^n := by induction n <;> simp_all [pow_succ]
end DiagonalSymbol

def diagonalFiber (a : DiagonalSymbol) (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberMultiplier (a x) a.bound a.bound_nonneg (a.norm_le_bound x)
/--
@isnad1 id=eq.0h4v.s12.6d5586357d22 from=translated src=- shape=2e4b5e7b vocab=174d95a3
-/
@[simp] lemma diagonalFiber_apply (a : DiagonalSymbol) (x : Base) (v : Fiber) (j : ℤ) :
    diagonalFiber a x v j = a x j*v j := rfl
/--
@isnad1 id=le.0h2v.s11.fdc0fe890986 from=translated src=- shape=1f9244de vocab=012890e7
-/
lemma diagonalFiber_norm (a : DiagonalSymbol) (x : Base) : ‖diagonalFiber a x‖ ≤ a.bound :=
  fiberMultiplier_norm_le _ _ _ _
/--
@isnad1 id=aestrong.1h2v.s12.e1394d58a7b1 from=translated src=- shape=e3099cdd vocab=6b573324
-/
lemma diagonalFiber_measurable (a : DiagonalSymbol) (f : Base → Fiber)
    (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => diagonalFiber a x (f x)) baseMeasure :=
  weightedPermutation_aestronglyMeasurable (Equiv.refl ℤ) a a.bound a.bound_nonneg
    a.norm_le_bound a.measurable hf

def diagonalOperator (a : DiagonalSymbol) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator (diagonalFiber a) a.bound a.bound_nonneg (diagonalFiber_norm a)
    (diagonalFiber_measurable a)
/--
@isnad1 id=eventual.0h2v.s17.0268b5ad5a8b from=translated src=- shape=9ca96fdd vocab=9b23e121
-/
lemma diagonalOperator_ae (a : DiagonalSymbol) (f : GlobalHilbert) :
    diagonalOperator a f =ᵐ[baseMeasure] fun x => diagonalFiber a x (f x) :=
  fieldOperator_ae _ _ _ _ _ _
/--
@isnad1 id=eventual.0h2v.s17.c80aaac20c3a from=translated src=- shape=d5dd487a vocab=9c26a55a
-/
lemma diagonalOperator_coord (a : DiagonalSymbol) (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j, diagonalOperator a f x j = a x j*f x j := by
  filter_upwards [diagonalOperator_ae a f] with x hx j
  rw [hx]; rfl
/--
@isnad1 id=eq.0h0v.s18.7ff8901e62f4 from=translated src=- shape=fd051f38 vocab=5866ffb6
-/
lemma diagonalOperator_zero : diagonalOperator 0 = 0 := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord 0 f,Lp.coeFn_zero Fiber 2 baseMeasure] with x hx h0
  ext j
  change diagonalOperator 0 f x j = (0 : GlobalHilbert) x j
  rw [hx,h0]; simp
/--
@isnad1 id=eq.0h0v.s18.4a777e778bbf from=translated src=- shape=fd051f38 vocab=5866ffb6
-/
lemma diagonalOperator_one : diagonalOperator 1 = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord 1 f] with x hx
  ext j
  simpa using hx j
/--
@isnad1 id=eq.0h2v.s18.56b0ea52ff69 from=translated src=- shape=c8faeec4 vocab=50e9c3c2
-/
lemma diagonalOperator_add (a b : DiagonalSymbol) :
    diagonalOperator (a+b) = diagonalOperator a + diagonalOperator b := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (a+b) f, diagonalOperator_coord a f,
    diagonalOperator_coord b f, Lp.coeFn_add (diagonalOperator a f) (diagonalOperator b f)] with x hab ha hb hs
  ext j
  change diagonalOperator (a+b) f x j = (diagonalOperator a f + diagonalOperator b f) x j
  rw [hs,Pi.add_apply,lp.coeFn_add,Pi.add_apply,hab,ha,hb,DiagonalSymbol.add_apply,add_mul]
/--
@isnad1 id=eq.0h2v.s18.401373c24772 from=translated src=- shape=c8faeec4 vocab=b99a6bf5
-/
lemma diagonalOperator_mul (a b : DiagonalSymbol) :
    diagonalOperator (a*b) = diagonalOperator a * diagonalOperator b := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (a*b) f, diagonalOperator_coord a (diagonalOperator b f),
    diagonalOperator_coord b f] with x hab ha hb
  ext j
  change diagonalOperator (a*b) f x j = diagonalOperator a (diagonalOperator b f) x j
  rw [hab,ha,hb,DiagonalSymbol.mul_apply,mul_assoc]
/--
@isnad1 id=eq.0h2v.s18.eb8372e8d3a7 from=translated src=- shape=3a7299bf vocab=5a4e1afb
-/
lemma diagonalOperator_smul (c : ℂ) (a : DiagonalSymbol) :
    diagonalOperator (c • a) = c • diagonalOperator a := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (c • a) f, diagonalOperator_coord a f,
    Lp.coeFn_smul c (diagonalOperator a f)] with x hca ha hs
  ext j
  change diagonalOperator (c • a) f x j = (c • diagonalOperator a f) x j
  rw [hs,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,hca,ha,DiagonalSymbol.smul_apply,smul_eq_mul,mul_assoc]
/--
@isnad1 id=eq.0h4v.s13.d93b9d6a9e92 from=translated src=- shape=0183abca vocab=02639a83
-/
lemma diagonalFiber_inner (a : DiagonalSymbol) (x : Base) (v z : Fiber) :
    inner ℂ (diagonalFiber a x v) z = inner ℂ v (diagonalFiber (star a) x z) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  simp only [diagonalFiber_apply,DiagonalSymbol.star_apply,RCLike.inner_apply,map_mul,starRingEnd_apply]
  ring
/--
@isnad1 id=eq.0h1v.s17.e3e91239603f from=translated src=- shape=67d4884e vocab=459dd1eb
-/
lemma diagonalOperator_star (a : DiagonalSymbol) :
    diagonalOperator (star a) = star (diagonalOperator a) := by
  ext1 f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (diagonalOperator (star a) f) = inner ℂ g ((diagonalOperator a).adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diagonalOperator_ae (star a) f, diagonalOperator_ae a g] with x hf hg
  rw [hf,hg,diagonalFiber_inner]

def diagonalRepresentation : DiagonalSymbol →⋆ₐ[ℂ] (GlobalHilbert →L[ℂ] GlobalHilbert) where
  toFun := diagonalOperator
  map_zero' := diagonalOperator_zero
  map_one' := diagonalOperator_one
  map_add' := diagonalOperator_add
  map_mul' := diagonalOperator_mul
  map_star' := diagonalOperator_star
  commutes' c := by
    have he : algebraMap ℂ DiagonalSymbol c = c • (1 : DiagonalSymbol) := by
      apply Subtype.ext
      funext x j
      simp
    rw [he,diagonalOperator_smul,diagonalOperator_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm

def fullMultiplierAlgebra : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) :=
  diagonalRepresentation.range

end
end BackwardIntertwiners

end OAI

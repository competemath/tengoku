import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Group.Ultra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ultrametric hull through the bidual, and descent of scalar forms

For a normed space `V` over a nontrivially normed field `K`, let `j : V → V**` be evaluation.
Every scalar `k`-linear form satisfies `‖g v‖ ≤ ‖g‖ ∏ₐ ‖j (v a)‖`
(`norm_le_mul_prod_bidualEval`), so scalar forms only see the seminorm `x ↦ ‖j x‖`. When `K` is
nonarchimedean, `V**` is ultrametric, and the image of `j` plays the role of the ultrametric
hull `V^u` in the proof of Proposition I.1, without a separation quotient or a completion.
Along any surjection `p : V → M` that dominates scalar forms in this way, scalar multilinear and
alternating forms descend to `M` with norm at most one (`descend`, `descendAlt`).
-/

noncomputable section

open scoped BigOperators

namespace AlternatingAnalytic.CountableType

section Ultrametric

variable {K E F : Type*} [NontriviallyNormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]

/-- Operators into an ultrametric space are ultrametric for the operator norm.
@isnad1 id=isultram.0h3v.s7.668f81f29c69 from=translated src=- shape=bcb27e21 vocab=d7f66239
-/
theorem isUltrametricDist_continuousLinearMap : IsUltrametricDist (E →L[K] F) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => by
    refine (f + g).opNorm_le_bound (le_max_of_le_left (norm_nonneg f)) fun x => ?_
    calc ‖(f + g) x‖ = ‖f x + g x‖ := rfl
      _ ≤ max ‖f x‖ ‖g x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max ‖f‖ ‖g‖ * ‖x‖ := by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
        exact max_le_max (f.le_opNorm x) (g.le_opNorm x)

end Ultrametric

variable {K V M : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
  [NormedAddCommGroup M] [NormedSpace K M]

variable (K V) in
/-- Evaluation of a normed space in its bidual.-/
abbrev bidualEval : V →L[K] ((V →L[K] K) →L[K] K) := ContinuousLinearMap.apply K K

/--
@isnad1 id=le.0h3v.s12.7cc553a3acaf from=translated src=- shape=b80c9e11 vocab=d1b7b72f
-/
theorem norm_bidualEval_le (x : V) : ‖bidualEval K V x‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun φ => by
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact φ.le_opNorm x

/-- Scalar multilinear forms are bounded by the bidual seminorms of their arguments.
@isnad1 id=le.0h5v.s12.28931dc35901 from=translated src=- shape=0a225536 vocab=f611a517
-/
theorem norm_le_mul_prod_bidualEval (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K) (v : Fin k → V) :
    ‖g v‖ ≤ ‖g‖ * ∏ a, ‖bidualEval K V (v a)‖ := by
  induction k with
  | zero => exact (g.le_opNorm v).trans_eq (by simp)
  | succ k ih =>
    have h1 : ∀ (x : V) (w : Fin k → V),
        ‖g (Fin.cons x w)‖ ≤ ‖bidualEval K V x‖ * (‖g‖ * ∏ a, ‖w a‖) := by
      intro x w
      let φ : V →L[K] K :=
        (ContinuousMultilinearMap.apply K (fun _ : Fin k => V) K w).comp g.curryLeft
      have hφ : ‖φ‖ ≤ ‖g‖ * ∏ a, ‖w a‖ := by
        refine φ.opNorm_le_bound (by positivity) fun y => ?_
        change ‖g.curryLeft y w‖ ≤ _
        rw [ContinuousMultilinearMap.curryLeft_apply]
        calc ‖g (Fin.cons y w)‖ ≤ ‖g‖ * ∏ a, ‖(Fin.cons y w : Fin (k + 1) → V) a‖ :=
              g.le_opNorm _
          _ = (‖g‖ * ∏ a, ‖w a‖) * ‖y‖ := by
              rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              ring
      have heq : g (Fin.cons x w) = bidualEval K V x φ := by
        change g (Fin.cons x w) = g.curryLeft x w
        rw [ContinuousMultilinearMap.curryLeft_apply]
      rw [heq]
      exact ((bidualEval K V x).le_opNorm φ).trans
        (mul_le_mul_of_nonneg_left hφ (norm_nonneg _))
    have h2 : ∀ x : V, ‖g.curryLeft x‖ ≤ ‖bidualEval K V x‖ * ‖g‖ := fun x =>
      ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => by
        rw [ContinuousMultilinearMap.curryLeft_apply, mul_assoc]
        exact h1 x w
    have hv : g v = g.curryLeft (v 0) (Fin.tail v) := by
      rw [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
    rw [hv, Fin.prod_univ_succ]
    calc ‖g.curryLeft (v 0) (Fin.tail v)‖
        ≤ ‖g.curryLeft (v 0)‖ * ∏ a, ‖bidualEval K V (Fin.tail v a)‖ := ih _ _
      _ ≤ ‖bidualEval K V (v 0)‖ * ‖g‖ * ∏ a, ‖bidualEval K V (Fin.tail v a)‖ :=
          mul_le_mul_of_nonneg_right (h2 _) (by positivity)
      _ = ‖g‖ * (‖bidualEval K V (v 0)‖ * ∏ a : Fin k, ‖bidualEval K V (v a.succ)‖) := by
          simp only [Fin.tail]; ring

/-- A multilinear form that vanishes as soon as one argument lies in `ker p` only depends on
the images of its arguments under `p`.
@isnad1 id=eq.2h8v.s10.db170c8f718c from=translated src=- shape=14ea468e vocab=3d667735
-/
theorem map_eq_of_forall_map_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : V →ₗ[K] M)
    (g : MultilinearMap K (fun _ : ι => V) K) (hg : ∀ v : ι → V, ∀ a, p (v a) = 0 → g v = 0)
    {v w : ι → V} (h : ∀ a, p (v a) = p (w a)) : g v = g w := by
  have hw : g w = g (v + (w - v)) := by congr 1; abel
  rw [hw, g.map_add_univ, Finset.sum_eq_single Finset.univ]
  · simp
  · intro s _ hs
    obtain ⟨a, ha⟩ : ∃ a, a ∉ s := by
      by_contra hcon
      push Not at hcon
      exact hs (Finset.eq_univ_of_forall hcon)
    apply hg _ a
    rw [Finset.piecewise_eq_of_notMem _ _ _ ha]
    simp [h a]
  · intro hu; exact absurd (Finset.mem_univ _) hu

variable (p : V →L[K] M) (hp : Function.Surjective p) {k : ℕ}
  (hbound : ∀ (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K) (v : Fin k → V),
    ‖g v‖ ≤ ‖g‖ * ∏ a, ‖p (v a)‖)

include hbound in
/--
@isnad1 id=eq.2h8v.s10.ac33da1cbe4c from=translated src=- shape=d46f0970 vocab=910ad547
-/
theorem map_eq_of_forall_apply_eq (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K)
    {v w : Fin k → V} (h : ∀ a, p (v a) = p (w a)) : g v = g w := by
  classical
  refine map_eq_of_forall_map_eq p.toLinearMap g.toMultilinearMap (fun v a ha => ?_) h
  have hb := hbound g v
  rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simpa using ha), mul_zero] at hb
  exact norm_le_zero_iff.mp hb

/-- The descended form, before continuity.-/
def descendMultilinear (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K) :
    MultilinearMap K (fun _ : Fin k => M) K where
  toFun y := g fun a => Function.surjInv hp (y a)
  map_update_add' y a u w := by
    have e : ∀ z : M, (fun c => Function.surjInv hp (Function.update y a z c)) =
        Function.update (fun c => Function.surjInv hp (y c)) a (Function.surjInv hp z) :=
      fun z => funext fun c => Function.apply_update (fun _ => Function.surjInv hp) y a z c
    simp only [e]
    rw [← g.map_update_add]
    apply map_eq_of_forall_apply_eq p hbound
    intro c
    by_cases hc : c = a
    · subst hc
      simp [Function.surjInv_eq hp]
    · simp [Function.update_of_ne hc]
  map_update_smul' y a r u := by
    have e : ∀ z : M, (fun c => Function.surjInv hp (Function.update y a z c)) =
        Function.update (fun c => Function.surjInv hp (y c)) a (Function.surjInv hp z) :=
      fun z => funext fun c => Function.apply_update (fun _ => Function.surjInv hp) y a z c
    simp only [e]
    rw [← g.map_update_smul]
    apply map_eq_of_forall_apply_eq p hbound
    intro c
    by_cases hc : c = a
    · subst hc
      simp [Function.surjInv_eq hp]
    · simp [Function.update_of_ne hc]

/--
@isnad1 id=le.2h7v.s10.0aadae1e13cb from=translated src=- shape=2ebb643e vocab=96fb1ff7
-/
theorem norm_descendMultilinear_le (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K)
    (y : Fin k → M) : ‖descendMultilinear p hp hbound g y‖ ≤ ‖g‖ * ∏ a, ‖y a‖ := by
  have h := hbound g fun a => Function.surjInv hp (y a)
  change ‖g fun a => Function.surjInv hp (y a)‖ ≤ _
  simpa only [Function.surjInv_eq hp] using h

/-- Descent of scalar `k`-linear forms along `p`, a linear contraction.-/
def descend : ContinuousMultilinearMap K (fun _ : Fin k => V) K →L[K]
    ContinuousMultilinearMap K (fun _ : Fin k => M) K :=
  LinearMap.mkContinuous
    { toFun := fun g => (descendMultilinear p hp hbound g).mkContinuous ‖g‖
        (norm_descendMultilinear_le p hp hbound g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun g => by
      rw [one_mul]
      exact MultilinearMap.mkContinuous_norm_le (descendMultilinear p hp hbound g) (norm_nonneg g)
        (norm_descendMultilinear_le p hp hbound g))

/--
@isnad1 id=eq.2h7v.s11.17322bd026a4 from=translated src=- shape=9398f568 vocab=4ad68a88
-/
theorem descend_apply (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K) (y : Fin k → M) :
    descend p hp hbound g y = g fun a => Function.surjInv hp (y a) := rfl

/--
@isnad1 id=eq.2h7v.s11.13df25fa972a from=translated src=- shape=6a5b03ff vocab=51d6a03a
-/
theorem descend_apply_comp (g : ContinuousMultilinearMap K (fun _ : Fin k => V) K)
    (v : Fin k → V) : descend p hp hbound g (fun a => p (v a)) = g v := by
  rw [descend_apply]
  exact map_eq_of_forall_apply_eq p hbound g fun a => Function.surjInv_eq hp _

/-- Descent of scalar alternating forms along `p`.-/
def descendAlt (g : V [⋀^Fin k]→L[K] K) : M [⋀^Fin k]→L[K] K where
  toContinuousMultilinearMap := descend p hp hbound g.toContinuousMultilinearMap
  map_eq_zero_of_eq' y _ _ hy hne :=
    g.map_eq_zero_of_eq (fun c => Function.surjInv hp (y c)) (congrArg _ hy) hne

/--
@isnad1 id=eq.2h6v.s11.a98cb3774cf1 from=translated src=- shape=e042afe0 vocab=cd5fc80a
-/
theorem descendAlt_toContinuousMultilinearMap (g : V [⋀^Fin k]→L[K] K) :
    (descendAlt p hp hbound g).toContinuousMultilinearMap =
      descend p hp hbound g.toContinuousMultilinearMap := rfl

/--
@isnad1 id=eq.2h7v.s10.4865183202df from=translated src=- shape=70294efb vocab=2456470f
-/
theorem descendAlt_apply_comp (g : V [⋀^Fin k]→L[K] K) (v : Fin k → V) :
    descendAlt p hp hbound g (fun a => p (v a)) = g v :=
  descend_apply_comp p hp hbound g.toContinuousMultilinearMap v

end AlternatingAnalytic.CountableType

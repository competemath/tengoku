import Tengoku.OpenaiMath.OAI.Combinatorics.EuclideanRamsey.PathWords

namespace OAI

universe uModule uIndex uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

open Filter
namespace EuclideanRamsey
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

section Ultrafilters
variable {M : Type uModule} [Monoid M]
@[simp] lemma pure_mul_ultra (x : M) (V : Ultrafilter M) :
    (pure x : Ultrafilter M)*V = V.map (x*·) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]
@[simp] lemma mul_pure_ultra (U : Ultrafilter M) (y : M) :
    U*(pure y : Ultrafilter M) = U.map (·*y) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]

def ultrafilterMonoid : Monoid (Ultrafilter M) where
  toSemigroup := Ultrafilter.semigroup
  one := pure 1
  one_mul U := by
    change (pure (1:M) : Ultrafilter M)*U=U
    rw [pure_mul_ultra]
    simp
  mul_one U := by
    change U*(pure (1:M) : Ultrafilter M)=U
    rw [mul_pure_ultra]
    simp

end Ultrafilters

inductive UltraColumn (ι : Type uIndex) (M : Type uModule)
  | common (U : Ultrafilter M)
  | principal (x : ι → M)

namespace UltraColumn
variable {ι : Type uIndex} {M : Type uModule}
def value : UltraColumn ι M → ι → Ultrafilter M
  | .common U,_ => U
  | .principal x,i => pure (x i)
def Realizes : UltraColumn ι M → (ι → M) → Prop
  | .common _,x => ∃ y,∀ i,x i=y
  | .principal y,x => x=y

lemma choose [Finite ι] (q : UltraColumn ι M) (p : ι → M → Prop)
    (h : ∀ i,∀ᶠ x in (q.value i : Filter M),p i x) :
    ∃ x : ι → M,q.Realizes x ∧ ∀ i,p i (x i) := by
  cases q with
  | common U =>
    have hh : ∀ᶠ x in (U : Filter M),∀ i,p i x := Filter.eventually_all.mpr h
    obtain ⟨x,hx⟩ := hh.exists
    exact ⟨fun _ => x,⟨x,fun _ => rfl⟩,hx⟩
  | principal x =>
    refine ⟨x,rfl,?_⟩
    intro i
    simpa [value] using h i

end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

inductive ColumnPath (a : ι → FiniteEuclidean) : List (UltraColumn ι Strings) → ℝ → Prop
  | nil : ColumnPath a [] 0
  | common (U : Ultrafilter Strings) : ColumnPath a [.common U] 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      ColumnPath a [.principal (fun i => FreeMonoid.of (b i))] u
  | append {p q u v} : ColumnPath a p u → ColumnPath a q v → ColumnPath a (p++q) (u+v)

lemma ColumnPath.realizes {a : ι → FiniteEuclidean} {qs u} (h : ColumnPath a qs u)
    (xs : List (ι → Strings)) (hx : List.Forall₂ UltraColumn.Realizes qs xs) :
    StringFamily a u (fun i => (xs.map (fun x => x i)).prod) := by
  induction h generalizing xs with
  | nil =>
    cases hx
    simpa using StringFamily.common a 1
  | common U =>
    cases hx with
    | cons hx hn =>
      cases hn
      obtain ⟨x,hx⟩ := hx
      simpa [hx] using StringFamily.common a x
  | copy b hb =>
    cases hx with
    | cons hx hn =>
      cases hn
      change _ = _ at hx
      subst hx
      simpa using StringFamily.single hb
  | @append p q u v _ _ ihp ihq =>
    have hp : List.Forall₂ UltraColumn.Realizes p (xs.take p.length) := by
      have hh := List.forall₂_take p.length hx
      simpa only [List.take_left] using hh
    have hq : List.Forall₂ UltraColumn.Realizes q (xs.drop p.length) := by
      have hh := List.forall₂_drop p.length hx
      simpa only [List.drop_left] using hh
    have hmul := (ihp (xs.take p.length) hp).mul (ihq (xs.drop p.length) hq)
    have he : (fun i => ((xs.take p.length).map (fun x => x i)).prod) *
        (fun i => ((xs.drop p.length).map (fun x => x i)).prod) =
        (fun i => (xs.map (fun x => x i)).prod) := by
      funext i
      simp only [Pi.mul_apply,← List.prod_append,← List.map_append,List.take_append_drop]
    rwa [he] at hmul

lemma ColumnPath.flatten {α : Type uAlpha} {a : ι → FiniteEuclidean} (l : List α)
    (qs : α → List (UltraColumn ι Strings)) (u : α → ℝ)
    (h : ∀ j∈l,ColumnPath a (qs j) (u j)) :
    ColumnPath a ((l.map qs).flatten) ((l.map u).sum) := by
  induction l with
  | nil => simpa using (ColumnPath.nil (a:=a))
  | cons j l ih =>
    simpa only [List.map_cons,List.flatten_cons,List.sum_cons] using
      (h j (by simp)).append (ih (fun k hk => h k (by simp [hk])))

end EuclideanRamsey

end

end OAI

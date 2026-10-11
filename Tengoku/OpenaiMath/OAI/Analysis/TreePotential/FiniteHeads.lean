import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.TreeTests

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section CompletedHeads
open scoped Classical
variable {I : Type*}

def coordinateFunctional (K : TestFamily I) (i : I) : TestCompletion K →L[ℝ] ℝ :=
  completedTestFunctional K ⟨_, K.singleton_mem i⟩

@[simp] lemma coordinateFunctional_coe (K : TestFamily I) (i : I) (x : TestVector K) :
    coordinateFunctional K i (x : TestCompletion K) = (testVectorEquiv K x) i := by
  rw [coordinateFunctional, completedTestFunctional_coe]
  change finitePairing _ ((testVectorEquiv K) x) = _
  convert finitePairing_single_test ((testVectorEquiv K) x) i using 1

def coordinateVector (K : TestFamily I) (i : I) : TestCompletion K :=
  ((testVectorEquiv K).symm (Finsupp.single i 1) : TestVector K)

@[simp] lemma norm_coordinateVector (K : TestFamily I) (i : I) :
    ‖coordinateVector K i‖ = 1 := by
  simp only [coordinateVector, UniformSpace.Completion.norm_coe, norm_test_single]

@[simp] lemma coordinateFunctional_vector (K : TestFamily I) (i j : I) :
    coordinateFunctional K i (coordinateVector K j) = if i = j then 1 else 0 := by
  simp only [coordinateVector, coordinateFunctional_coe, LinearEquiv.apply_symm_apply]
  simp [Finsupp.single_apply, eq_comm]

def completedHead (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] TestCompletion K :=
  ∑ i ∈ B, (coordinateFunctional K i).smulRight (coordinateVector K i)

@[simp] lemma completedHead_apply (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedHead K B x = ∑ i ∈ B, coordinateFunctional K i x • coordinateVector K i := by
  simp [completedHead]

lemma finiteHead_eq_sum (B : Finset I) (x : I →₀ ℝ) :
    Finsupp.filter (fun i => i ∈ B) x = ∑ i ∈ B, x i • Finsupp.single i 1 := by
  ext j
  simp only [Finsupp.filter_apply
    ]
  by_cases hj : j ∈ B <;> simp [Finsupp.single_apply, hj, eq_comm]

lemma completedHead_coe (K : TestFamily I) (B : Finset I) (x : TestVector K) :
    completedHead K B (x : TestCompletion K) =
      ((testVectorEquiv K).symm (Finsupp.filter (fun i => i ∈ B) (testVectorEquiv K x)) : TestCompletion K) := by
  rw [finiteHead_eq_sum]
  simp only [map_sum, map_smul]
  change completedHead K B (x : TestCompletion K) =
    (UniformSpace.Completion.toComplL : TestVector K →L[ℝ] TestCompletion K) (∑ i ∈ B, (testVectorEquiv K x) i • (testVectorEquiv K).symm (Finsupp.single i 1))
  simp only [map_sum, map_smul, completedHead_apply, coordinateFunctional_coe, coordinateVector]
  rfl

def headCoordinates (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] (B → ℝ) :=
  ContinuousLinearMap.pi (fun i => coordinateFunctional K i.val)

/-- Closed finite-codimensional coordinate tail, with no topological assumption
    on an arbitrary algebraic complement. -/
def coordinateTail (K : TestFamily I) (B : Finset I) : Submodule ℝ (TestCompletion K) :=
  (headCoordinates K B).ker

lemma mem_coordinateTail (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    x ∈ coordinateTail K B ↔ ∀ i ∈ B, coordinateFunctional K i x = 0 := by
  change (headCoordinates K B x = 0) ↔ _
  simp only [headCoordinates, ContinuousLinearMap.pi_apply, funext_iff, Pi.zero_apply, Subtype.forall]

def completedTail (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] TestCompletion K :=
  ContinuousLinearMap.id ℝ (TestCompletion K) - completedHead K B

@[simp] lemma completedTail_apply (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedTail K B x = x - completedHead K B x := rfl

lemma completedTail_coe (K : TestFamily I) (B : Finset I) (x : TestVector K) :
    completedTail K B (x : TestCompletion K) =
      ((testVectorEquiv K).symm ((testVectorEquiv K x) - Finsupp.filter (fun i => i ∈ B) (testVectorEquiv K x)) : TestCompletion K) := by
  simp only [completedTail_apply, completedHead_coe, map_sub, LinearEquiv.symm_apply_apply,
    UniformSpace.Completion.coe_sub]

end CompletedHeads

namespace TreeCalculus
open scoped Classical

def coordinateHead (r : Bool) (D : Finset Node) : Finset (TreeCoordinate r) :=
  D.subtype (fun s => r = true ∨ s ≠ [])

@[simp] lemma mem_coordinateHead (r : Bool) (D : Finset Node) (s : TreeCoordinate r) :
    s ∈ coordinateHead r D ↔ s.val ∈ D := by simp [coordinateHead]

def initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) : Finset Node :=
  insert [] (x.support.biUnion (fun s => s.val.inits.toFinset))

end TreeCalculus

end BoundedTreePotentials

end

end OAI

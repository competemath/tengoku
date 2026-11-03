import Tengoku.AlbertFrameTripleInvariants.OneBit.Closeout.MarginalRigidity
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CommutatorGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The triple-trace tensor and its marginals

`tripleForm x y z = tr(x ∘ (y ∘ z))` is invariant under all permutations of its
arguments (`tripleForm_perm`, from commutativity of ∘ and associativity of the trace
form). `tensor X a` is the 3×3×3 array of triple traces of a configuration, `relabel σ π`
the action of a frame permutation and within-frame permutations on its index. Summing the
tensor over one index yields a pair trace, because each frame sums to 1
(`tripleForm_sum*`, `family_sum`). `tensor_stabilizer_trivial`: a relabelling that fixes
the tensor of the first configuration fixes its pair-trace matrices, hence is trivial by
`MarginalRigidity`.
-/

namespace OneBit.Closeout
open AlbertLean
open AlbertLean.Generic.CommutatorGeometry
open scoped BigOperators

def tripleForm (x y z : Coord) : ℚ := traceForm x (structuredProduct y z)

theorem tripleForm_swap23 (x y z : Coord) : tripleForm x y z = tripleForm x z y := by
  unfold tripleForm
  rw [productCommutative y z]

theorem tripleForm_cycle (x y z : Coord) : tripleForm x y z = tripleForm z x y := by
  unfold tripleForm
  rw [← traceFormAssociative, traceForm_symmetric]

theorem tripleForm_perm (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → Coord) :
    tripleForm (x (σ 0)) (x (σ 1)) (x (σ 2)) = tripleForm (x 0) (x 1) (x 2) := by
  have h01 := σ.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := σ.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := σ.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  generalize σ 0 = a at *
  generalize σ 1 = b at *
  generalize σ 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> try contradiction
  · rfl
  · exact tripleForm_swap23 _ _ _
  · exact (tripleForm_swap23 _ _ _).trans (tripleForm_cycle _ _ _)
  · exact tripleForm_cycle _ _ _
  · exact (tripleForm_cycle _ _ _).symm
  · exact (tripleForm_cycle _ _ _).trans (tripleForm_swap23 _ _ _)

def tensor (X : WitnessTriple) (a : Fin 3 → Fin 3) : ℚ :=
  tripleForm (family X 0 (a 0)) (family X 1 (a 1)) (family X 2 (a 2))

/-- Push an assignment forward: b(σ r) = π r (a r).-/
def relabel (σ : Equiv.Perm (Fin 3)) (π : Fin 3 → Equiv.Perm (Fin 3))
    (a : Fin 3 → Fin 3) (s : Fin 3) : Fin 3 := π (σ.symm s) (a (σ.symm s))

theorem tensor_relabel (X : WitnessTriple) (σ : Equiv.Perm (Fin 3))
    (π : Fin 3 → Equiv.Perm (Fin 3)) (a : Fin 3 → Fin 3) :
    tensor X (relabel σ π a) =
      tripleForm (family X (σ 0) (π 0 (a 0)))
        (family X (σ 1) (π 1 (a 1))) (family X (σ 2) (π 2 (a 2))) := by
  simpa [tensor, relabel] using tripleForm_perm σ.symm
    (fun r => family X (σ r) (π r (a r)))

theorem family_sum (X : WitnessTriple) (hX : LawfulFrameTriple X) (r : Fin 3) :
    (∑ i, family X r i) = one := by
  simpa [Fin.sum_univ_succ, family, add_assoc] using (hX r).2.2.2.1

theorem family_sum_perm (X : WitnessTriple) (hX : LawfulFrameTriple X)
    (r : Fin 3) (π : Equiv.Perm (Fin 3)) : (∑ i, family X r (π i)) = one := by
  rw [Equiv.sum_comp π, family_sum X hX]

theorem tripleForm_sum3 (x y : Coord) (z : Fin 3 → Coord) :
    (∑ i, tripleForm x y (z i)) = tripleForm x y (∑ i, z i) := by
  change (∑ i, tracePairing x ((leftMulLinear productQBilinear y) (z i))) =
    tracePairing x ((leftMulLinear productQBilinear y) (∑ i, z i))
  rw [map_sum, map_sum]

theorem tripleForm_one3 (x y : Coord) : tripleForm x y one = traceForm x y := by
  unfold tripleForm
  rw [(unitLaw y).2]

theorem tripleForm_sum1 (x : Fin 3 → Coord) (y z : Coord) :
    (∑ i, tripleForm (x i) y z) = tripleForm (∑ i, x i) y z := by
  change (∑ i, (tracePairing (x i)) (structuredProduct y z)) =
    (tracePairing (∑ i, x i)) (structuredProduct y z)
  simp only [map_sum, LinearMap.sum_apply]

theorem tripleForm_sum2 (x z : Coord) (y : Fin 3 → Coord) :
    (∑ i, tripleForm x (y i) z) = tripleForm x (∑ i, y i) z := by
  calc
    _ = ∑ i, tripleForm x z (y i) := Finset.sum_congr rfl (fun i _ => tripleForm_swap23 _ _ _)
    _ = tripleForm x z (∑ i, y i) := tripleForm_sum3 _ _ _
    _ = _ := tripleForm_swap23 _ _ _

theorem tripleForm_one1 (y z : Coord) : tripleForm one y z = traceForm y z := by
  rw [tripleForm_cycle, tripleForm_swap23, tripleForm_one3, traceForm_symmetric]

theorem tripleForm_one2 (x z : Coord) : tripleForm x one z = traceForm z x := by
  rw [tripleForm_swap23, tripleForm_one3, traceForm_symmetric]

/-- Every pair trace is a marginal of the raw tensor, so tensor symmetry forces
symmetry of the numerical marginal matrices.-/
theorem tensor_stabilizer_trivial (σ : Equiv.Perm (Fin 3))
    (π : Fin 3 → Equiv.Perm (Fin 3))
    (h : ∀ a, tensor witnessTheta1 a = tensor witnessTheta1 (relabel σ π a)) :
    σ = Equiv.refl _ ∧ ∀ r, π r = Equiv.refl _ := by
  have h01 (i j : Fin 3) :
      pair witnessTheta1 0 1 i j = pair witnessTheta1 (σ 0) (σ 1) (π 0 i) (π 1 j) := by
    have hs := congrArg (fun f : Fin 3 → ℚ => ∑ l, f l) (funext (fun l => h ![i,j,l]))
    simp only [tensor_relabel] at hs
    simp only [tensor, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at hs
    rw [tripleForm_sum3, tripleForm_sum3, family_sum _ witnessTheta1Lawful,
      family_sum_perm _ witnessTheta1Lawful, tripleForm_one3, tripleForm_one3] at hs
    exact hs
  have h12 (j l : Fin 3) :
      pair witnessTheta1 1 2 j l = pair witnessTheta1 (σ 1) (σ 2) (π 1 j) (π 2 l) := by
    have hs := congrArg (fun f : Fin 3 → ℚ => ∑ i, f i) (funext (fun i => h ![i,j,l]))
    simp only [tensor_relabel] at hs
    simp only [tensor, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at hs
    rw [tripleForm_sum1, tripleForm_sum1, family_sum _ witnessTheta1Lawful,
      family_sum_perm _ witnessTheta1Lawful, tripleForm_one1, tripleForm_one1] at hs
    exact hs
  have h20 (l i : Fin 3) :
      pair witnessTheta1 2 0 l i = pair witnessTheta1 (σ 2) (σ 0) (π 2 l) (π 0 i) := by
    have hs := congrArg (fun f : Fin 3 → ℚ => ∑ j, f j) (funext (fun j => h ![i,j,l]))
    simp only [tensor_relabel] at hs
    simp only [tensor, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at hs
    rw [tripleForm_sum2, tripleForm_sum2, family_sum _ witnessTheta1Lawful,
      family_sum_perm _ witnessTheta1Lawful, tripleForm_one2, tripleForm_one2] at hs
    exact hs
  apply marginal_stabilizer_trivial σ π
  intro r s hrs i j
  rw [← pair_eq_marginal r s i j hrs,
    ← pair_eq_marginal (σ r) (σ s) (π r i) (π s j) (σ.injective.ne hrs)]
  fin_cases r <;> fin_cases s <;> try contradiction
  · exact h01 i j
  · exact (traceForm_symmetric _ _).trans ((h20 j i).trans (traceForm_symmetric _ _))
  · exact (traceForm_symmetric _ _).trans ((h01 j i).trans (traceForm_symmetric _ _))
  · exact h12 i j
  · exact h20 i j
  · exact (traceForm_symmetric _ _).trans ((h12 j i).trans (traceForm_symmetric _ _))

end OneBit.Closeout

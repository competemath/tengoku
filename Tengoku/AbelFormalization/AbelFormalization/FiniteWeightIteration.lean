import Tengoku.AbelFormalization.AbelFormalization.FiniteWeightInitialLength
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Nat.SuccPred
import Tengoku.Seed.Order.SuccPred.Archimedean
import Tengoku.Seed.Order.Monotone.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Actual finite-length triangular iteration

The iteration is literally `N ↦ initial(JN)` in
an actual finite product of weight modules. Its bounded natural potential
is the sum of the proper-prefix lengths. Initial-length preservation and
triangular invariance detection are proved in the two imported modules.
A maximum of the actual potential range yields a permanent fixed point.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [Ring R] {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The actual descent step, using the full initial submodule of all
elements of the image under J.-/
def finiteWeightDescentStep (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i)) : Submodule R (∀ i, M i) :=
  finiteWeightInitial (N.map J.toLinearMap)

/-- The actual iteration in the finite product module.-/
def finiteWeightDescentIterate (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N₀ : Submodule R (∀ i, M i)) : ℕ → Submodule R (∀ i, M i)
  | 0 => N₀
  | j + 1 => finiteWeightDescentStep J (finiteWeightDescentIterate J N₀ j)

/--
@isnad1 id=eq.0h5v.s7.c57fe3d7ab19 from=translated src=- shape=e7de5bab vocab=246820c9
-/
@[simp]
theorem finiteWeightDescentIterate_zero
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i)) (N₀ : Submodule R (∀ i, M i)) :
    finiteWeightDescentIterate J N₀ 0 = N₀ := rfl

/--
@isnad1 id=eq.0h6v.s8.1d264a3b5793 from=translated src=- shape=089efb6f vocab=02236e6e
-/
@[simp]
theorem finiteWeightDescentIterate_succ
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i)) (N₀ : Submodule R (∀ i, M i)) (j : ℕ) :
    finiteWeightDescentIterate J N₀ (j + 1) =
      finiteWeightDescentStep J (finiteWeightDescentIterate J N₀ j) := rfl

/-- Every step after initialization is homogeneous, and homogeneous
initial data therefore give homogeneity throughout the iteration.
@isnad1 id=mem.2h8v.s9.c878b64703cd from=translated src=- shape=858ea911 vocab=adc13a66
-/
theorem finiteWeightDescentIterate_homogeneous
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i)) (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) (j : ℕ) :
    ∀ x ∈ finiteWeightDescentIterate J N₀ j, ∀ i,
      Pi.single i (x i) ∈ finiteWeightDescentIterate J N₀ j := by
  cases j with
  | zero => exact hN₀
  | succ j =>
    exact finiteWeightInitial_homogeneous
      ((finiteWeightDescentIterate J N₀ j).map J.toLinearMap)

/-- A homogeneous J-invariant submodule is an actual fixed point of the
full descent step.
@isnad1 id=eq.2h5v.s9.98f17c49b699 from=translated src=- shape=6b9e1958 vocab=17e15bef
-/
theorem finiteWeightDescentStep_eq_self_of_invariant
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i)) (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hJN : N.map J.toLinearMap = N) : finiteWeightDescentStep J N = N := by
  rw [finiteWeightDescentStep, hJN, finiteWeightInitial_eq_of_homogeneous N hN]

/-- Once an actual iterate is invariant, every later iterate equals it.
@isnad1 id=eq.3h7v.s9.e46be1eb6400 from=translated src=- shape=240b8dd5 vocab=d9d49ce4
-/
theorem finiteWeightDescentIterate_permanent
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i)) (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) (j₀ : ℕ)
    (hJN : (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
      finiteWeightDescentIterate J N₀ j₀) :
    ∀ j, j₀ ≤ j → finiteWeightDescentIterate J N₀ j = finiteWeightDescentIterate J N₀ j₀ := by
  have hfixed := finiteWeightDescentStep_eq_self_of_invariant J
    (finiteWeightDescentIterate J N₀ j₀)
    (finiteWeightDescentIterate_homogeneous J N₀ hN₀ j₀) hJN
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [finiteWeightDescentIterate_succ, ih, hfixed]

variable [IsArtinian R (∀ i, M i)] [IsNoetherian R (∀ i, M i)]

/-- The natural length of an actual prefix image. Finiteness is supplied
by the finite-length ambient module.-/
def finiteWeightPrefixLengthNat (N : Submodule R (∀ i, M i)) (k : ℕ) : ℕ :=
  (Module.length R (finiteWeightPrefixImage N k)).toNat

/-- The finite potential sums all proper prefixes, including the harmless
zero prefix. Prefix n would be the preserved total length.-/
def finiteWeightPrefixPotential (N : Submodule R (∀ i, M i)) : ℕ :=
  ∑ k : Fin n, finiteWeightPrefixLengthNat N k.val

/--
@isnad1 id=le.0h5v.s7.474940e887f3 from=translated src=- shape=ce33858b vocab=3007ed9c
-/
theorem finiteWeightPrefixLengthNat_le_ambient (N : Submodule R (∀ i, M i)) (k : ℕ) :
    finiteWeightPrefixLengthNat N k ≤ (Module.length R (∀ i, M i)).toNat := by
  apply ENat.toNat_le_toNat
  · exact Module.length_le_of_injective (finiteWeightPrefixImage N k).subtype
      (Submodule.subtype_injective _)
  · exact Module.length_ne_top

/-- A single ambient bound applies to the potential of every submodule.
@isnad1 id=le.0h4v.s7.1ad28d22ffa6 from=translated src=- shape=3edd41db vocab=2edb0d7a
-/
theorem finiteWeightPrefixPotential_le (N : Submodule R (∀ i, M i)) :
    finiteWeightPrefixPotential N ≤ n * (Module.length R (∀ i, M i)).toNat := by
  classical
  calc
    finiteWeightPrefixPotential N ≤
        ∑ _k : Fin n, (Module.length R (∀ i, M i)).toNat :=
      Finset.sum_le_sum fun k _ => finiteWeightPrefixLengthNat_le_ambient N k.val
    _ = _ := by simp

/--
@isnad1 id=le.2h6v.s10.fb4d81b4537d from=translated src=- shape=30707534 vocab=76dae9a0
-/
theorem finiteWeightPrefixLengthNat_le_step
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N) (k : ℕ) :
    finiteWeightPrefixLengthNat N k ≤
      finiteWeightPrefixLengthNat (finiteWeightDescentStep J N) k := by
  apply ENat.toNat_le_toNat
  · rw [finiteWeightDescentStep, finiteWeightInitial_prefix_length]
    exact finiteWeightPrefix_length_le_map J htri N hN k
  · exact Module.length_ne_top

/-- The potential weakly increases at every homogeneous descent step.
@isnad1 id=le.2h5v.s10.41a5b985e7c0 from=translated src=- shape=97422835 vocab=4f74a970
-/
theorem finiteWeightPrefixPotential_le_step
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N) :
    finiteWeightPrefixPotential N ≤ finiteWeightPrefixPotential (finiteWeightDescentStep J N) := by
  apply Finset.sum_le_sum
  intro k hk
  exact finiteWeightPrefixLengthNat_le_step J htri N hN k.val

private theorem submodule_length_eq_of_toNat_eq {A B : Submodule R (∀ i, M i)}
    (h : (Module.length R A).toNat = (Module.length R B).toNat) :
    Module.length R A = Module.length R B := by
  calc
    Module.length R A = ((Module.length R A).toNat : ℕ∞) :=
      (ENat.natCast_toNat (Module.length_ne_top (R := R) (M := A))).symm
    _ = ((Module.length R B).toNat : ℕ∞) := congrArg (fun t : ℕ => (t : ℕ∞)) h
    _ = Module.length R B := ENat.natCast_toNat (Module.length_ne_top (R := R) (M := B))

/-- An unchanged potential forces equality of every prefix length, hence
actual triangular invariance of the old submodule.
@isnad1 id=eq.3h5v.s10.7310aa94b2a8 from=translated src=- shape=633812b9 vocab=7abead07
-/
theorem triangular_invariant_of_finiteWeightPrefixPotential_eq
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hpot : finiteWeightPrefixPotential (finiteWeightDescentStep J N) =
      finiteWeightPrefixPotential N) : N.map J.toLinearMap = N := by
  classical
  have hcoords : ∀ k : Fin n,
      finiteWeightPrefixLengthNat N k.val =
        finiteWeightPrefixLengthNat (finiteWeightDescentStep J N) k.val := by
    intro k
    exact (Finset.sum_eq_sum_iff_of_le
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        finiteWeightPrefixLengthNat_le_step J htri N hN i.val)).mp hpot.symm k
          (Finset.mem_univ k)
  apply triangular_invariant_of_finiteWeightPrefix_lengths_eq J htri N hN
  intro k
  change Module.length R (finiteWeightPrefixImage (N.map J.toLinearMap) k) =
    Module.length R (finiteWeightPrefixImage N k)
  by_cases hk : k < n
  · have hlength := submodule_length_eq_of_toNat_eq
      (A := finiteWeightPrefixImage N k)
      (B := finiteWeightPrefixImage (finiteWeightDescentStep J N) k)
      (hcoords ⟨k, hk⟩)
    rw [finiteWeightDescentStep, finiteWeightInitial_prefix_length] at hlength
    exact hlength.symm
  · have hnk : n ≤ k := le_of_not_gt hk
    rw [finiteWeightPrefixImage_eq_self_of_le _ hnk,
      finiteWeightPrefixImage_eq_self_of_le _ hnk, length_map_linearEquiv]

/-- Every failure of invariance forces a strict increase of the bounded
natural potential.
@isnad1 id=lt.3h5v.s10.bee30a4fc257 from=translated src=- shape=034880e0 vocab=970c4d78
-/
theorem finiteWeightPrefixPotential_lt_step_of_not_invariant
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hne : N.map J.toLinearMap ≠ N) :
    finiteWeightPrefixPotential N < finiteWeightPrefixPotential (finiteWeightDescentStep J N) := by
  apply (lt_iff_le_and_ne).mpr
  refine ⟨finiteWeightPrefixPotential_le_step J htri N hN, ?_⟩
  intro heq
  exact hne (triangular_invariant_of_finiteWeightPrefixPotential_eq J htri N hN heq.symm)

/--
@isnad1 id=monotone.2h5v.s10.59a1c00c0b2b from=translated src=- shape=fb69b7ff vocab=a0acde9a
-/
theorem finiteWeightDescentIterate_potential_monotone
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    Monotone (fun j => finiteWeightPrefixPotential (finiteWeightDescentIterate J N₀ j)) := by
  apply monotone_nat_of_le_succ
  intro j
  exact finiteWeightPrefixPotential_le_step J htri (finiteWeightDescentIterate J N₀ j)
    (finiteWeightDescentIterate_homogeneous J N₀ hN₀ j)

/-- The actual finite-product finite-length triangular descent eventually
stabilizes at a J-invariant submodule. The only hypotheses are the
structural triangularity, finite length of the ambient module, and
homogeneity of the initial submodule.
@isnad1 id=ex.2h5v.s10.5c7c880fa17a from=translated src=- shape=220ea454 vocab=ec701036
-/
theorem exists_finiteWeightDescent_stabilizes
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ, (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ j₀ ∧
      ∀ j, j₀ ≤ j → finiteWeightDescentIterate J N₀ j = finiteWeightDescentIterate J N₀ j₀ := by
  let f : ℕ → ℕ := fun j => finiteWeightPrefixPotential (finiteWeightDescentIterate J N₀ j)
  have hbounded : BddAbove (Set.range f) := by
    refine ⟨n * (Module.length R (∀ i, M i)).toNat, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact finiteWeightPrefixPotential_le (finiteWeightDescentIterate J N₀ j)
  obtain ⟨v, hv⟩ := hbounded.exists_isGreatest_of_nonempty
    (show (Set.range f).Nonempty from ⟨f 0, ⟨0, rfl⟩⟩)
  obtain ⟨j₀, hj₀⟩ := hv.1
  have hmax : f (j₀ + 1) ≤ f j₀ := by
    rw [hj₀]
    exact hv.2 ⟨j₀ + 1, rfl⟩
  have hmon : f j₀ ≤ f (j₀ + 1) :=
    finiteWeightPrefixPotential_le_step J htri (finiteWeightDescentIterate J N₀ j₀)
      (finiteWeightDescentIterate_homogeneous J N₀ hN₀ j₀)
  have hfixed := triangular_invariant_of_finiteWeightPrefixPotential_eq J htri
    (finiteWeightDescentIterate J N₀ j₀)
    (finiteWeightDescentIterate_homogeneous J N₀ hN₀ j₀) (le_antisymm hmax hmon)
  exact ⟨j₀, hfixed, finiteWeightDescentIterate_permanent J N₀ hN₀ j₀ hfixed⟩

end AbelFormalization

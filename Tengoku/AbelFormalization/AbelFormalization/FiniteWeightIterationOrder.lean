import Tengoku.AbelFormalization.AbelFormalization.FiniteWeightIteration
import Tengoku.AbelFormalization.AbelFormalization.FiniteWeightQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Order lemmas for finite-weight descent

The finite-weight descent step is monotone.  Consequently, its iterates are
monotone in the initial submodule, fixed points remain fixed, and any iterate
starting between two fixed points remains between them.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [Ring R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The finite-weight descent step is monotone in its input submodule.
@isnad1 id=le.1h6v.s9.c2916e47bcd9 from=translated src=- shape=c4ac76c9 vocab=41224167
-/
theorem finiteWeightDescentStep_mono
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    {U V : Submodule R (∀ i, M i)} (hUV : U ≤ V) :
    finiteWeightDescentStep J U ≤ finiteWeightDescentStep J V := by
  unfold finiteWeightDescentStep
  exact finiteWeightInitial_mono (Submodule.map_mono hUV)

/-- Every finite-weight descent iterate is monotone in the initial
submodule.
@isnad1 id=le.1h7v.s9.3e53f0325213 from=translated src=- shape=f5d527e0 vocab=90a7662b
-/
theorem finiteWeightDescentIterate_mono
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    {U V : Submodule R (∀ i, M i)} (hUV : U ≤ V) (j : ℕ) :
    finiteWeightDescentIterate J U j ≤
      finiteWeightDescentIterate J V j := by
  induction j with
  | zero => exact hUV
  | succ j ih =>
      change finiteWeightDescentStep J
          (finiteWeightDescentIterate J U j) ≤
        finiteWeightDescentStep J
          (finiteWeightDescentIterate J V j)
      exact finiteWeightDescentStep_mono J ih

/-- Restarting the iteration at time `a` and running for `b` more steps is
the same as running the original iteration for `a + b` steps.
@isnad1 id=eq.0h7v.s8.2b74ac17c376 from=translated src=- shape=ce178c64 vocab=11d23aa2
-/
theorem finiteWeightDescentIterate_add
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i)) (a b : ℕ) :
    finiteWeightDescentIterate J N (a + b) =
      finiteWeightDescentIterate J
        (finiteWeightDescentIterate J N a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ]
      change finiteWeightDescentStep J
          (finiteWeightDescentIterate J N (a + b)) =
        finiteWeightDescentStep J
          (finiteWeightDescentIterate J
            (finiteWeightDescentIterate J N a) b)
      rw [ih]

/-- An actual fixed point of the descent step stays fixed under every
iterate.
@isnad1 id=eq.1h6v.s8.f3b1836aeb85 from=translated src=- shape=ef5b38ef vocab=69f0bbfd
-/
theorem finiteWeightDescentIterate_eq_self_of_fixed
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i))
    (hfixed : finiteWeightDescentStep J N = N) (j : ℕ) :
    finiteWeightDescentIterate J N j = N := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change finiteWeightDescentStep J
        (finiteWeightDescentIterate J N j) = N
      rw [ih, hfixed]

/-- A homogeneous `J`-invariant submodule stays fixed under every descent
iterate.
@isnad1 id=eq.2h6v.s9.e771cfd44bea from=translated src=- shape=b3c78680 vocab=d4e5dfd9
-/
theorem finiteWeightDescentIterate_eq_self_of_invariant
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hJN : N.map J.toLinearMap = N) (j : ℕ) :
    finiteWeightDescentIterate J N j = N := by
  exact finiteWeightDescentIterate_eq_self_of_fixed J N
    (finiteWeightDescentStep_eq_self_of_invariant J N hN hJN) j

/-- If the initial submodule lies between two fixed points, then every
iterate lies between the same fixed points.
@isnad1 id=and.4h8v.s10.c2a5ef346993 from=translated src=- shape=0014aff4 vocab=70d4b137
-/
theorem finiteWeightDescentIterate_between_fixed
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (D N K : Submodule R (∀ i, M i))
    (hDfixed : finiteWeightDescentStep J D = D)
    (hKfixed : finiteWeightDescentStep J K = K)
    (hDN : D ≤ N) (hNK : N ≤ K) (j : ℕ) :
    D ≤ finiteWeightDescentIterate J N j ∧
      finiteWeightDescentIterate J N j ≤ K := by
  constructor
  · calc
      D = finiteWeightDescentIterate J D j :=
        (finiteWeightDescentIterate_eq_self_of_fixed J D hDfixed j).symm
      _ ≤ finiteWeightDescentIterate J N j :=
        finiteWeightDescentIterate_mono J hDN j
  · calc
      finiteWeightDescentIterate J N j ≤
          finiteWeightDescentIterate J K j :=
        finiteWeightDescentIterate_mono J hNK j
      _ = K := finiteWeightDescentIterate_eq_self_of_fixed J K hKfixed j

/-- If the initial submodule lies between two homogeneous `J`-invariant
submodules, then every iterate lies between those submodules.
@isnad1 id=and.6h8v.s11.3d83286ea855 from=translated src=- shape=a9f0935f vocab=d9d49ce4
-/
theorem finiteWeightDescentIterate_between
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (D N K : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D)
    (hJD : D.map J.toLinearMap = D)
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (hDN : D ≤ N) (hNK : N ≤ K) (j : ℕ) :
    D ≤ finiteWeightDescentIterate J N j ∧
      finiteWeightDescentIterate J N j ≤ K := by
  exact finiteWeightDescentIterate_between_fixed J D N K
    (finiteWeightDescentStep_eq_self_of_invariant J D hD hJD)
    (finiteWeightDescentStep_eq_self_of_invariant J K hK hJK)
    hDN hNK j

end AbelFormalization

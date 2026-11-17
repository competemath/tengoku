import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero

set_option autoImplicit false

namespace IharaLemmaSolCorner

open IharaLemma

/--
@isnad1 id=eq.2h6v.s8.2638f026c164 from=translated src=- shape=14bf27cd vocab=45f87462
-/
theorem smul_eq_zero_of_notMem {B : Type} [CommRing B] (S : IdempotentSplitting B) {M : Type}
    [AddCommGroup M] [Module B M] {u : B} {y : M} (huy : u • y = 0) {j : Fin S.n} (hu : u ∉ S.𝔪 j) :
    S.e j • y = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.coi.idem j) (S.𝔪 j)
    (fun J hJ hne => S.mem_of_isMaximal_of_ne j J hJ hne) hu
  rw [← ht, mul_right_comm, mul_smul, huy, smul_zero]

end IharaLemmaSolCorner

/--
@isnad1 id=eq.2h6v.s8.1803ed403bbe from=translated src=- shape=d7da6d6a vocab=45f87462
-/
theorem solution {B : Type} [CommRing B]
    (S : IharaLemma.IdempotentSplitting B) {M : Type} [AddCommGroup M] [Module B M]
    {u : B} {y : M} (huy : u • y = 0) (i₀ : Fin S.n) (hu : ∀ j, j ≠ i₀ → u ∉ S.𝔪 j) :
    y = S.e i₀ • y := by
  have hsum : (∑ j, S.e j) • y = y := by rw [S.coi.complete, one_smul]
  conv_lhs => rw [← hsum, Finset.sum_smul]
  rw [Finset.sum_eq_single i₀ (fun j _ hj => IharaLemmaSolCorner.smul_eq_zero_of_notMem S huy (hu j hj))
    (fun h => absurd (Finset.mem_univ i₀) h)]

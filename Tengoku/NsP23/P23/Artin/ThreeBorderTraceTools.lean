import Tengoku.NsP23.P23.Artin.CanonicalRelations
import Tengoku.NsP23.P23.Artin.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Symbolic no-preimage coefficient vanishing, for the three-border proofs. -/
namespace P23.Artin
noncomputable section
open P23.OneTie
variable {a b c : ℕ} [NeZero a] {k : Type*} [Field k]

/--
@isnad1 id=eq.1h8v.s8.c18c8c7ef0db from=translated src=- shape=3330e037 vocab=7ac107a0
-/
theorem coeffAt_X_mul_eq_zero_of_not_dvd (S : Finset (Normal a b c))
    (m t : MonomialIndex S) (hnt : ¬m.1 ∣ t.1) (v : MonomialArtin k S) :
    coeffAt (k := k) S t (X (k := k) S m.1 m.2 * v) = 0 := by
  classical
  induction v using MonomialArtin.induction_linear with
  | zero => simp
  | add v w hv hw => rw [mul_add,map_add,hv,hw,add_zero]
  | single q r =>
    rw [← MonomialArtin.smul_X (k := k) r S q.1 q.2, MonomialArtin.mul_smul_comm']
    have hprod : t.1 ≠ m.1 * q.1 := fun he => hnt ⟨q.1,he⟩
    by_cases hs : m.1 * q.1 ∈ standardFinset S
    · have hi : t ≠ (⟨m.1 * q.1,hs⟩ : MonomialIndex S) :=
        fun he => hprod (congrArg Subtype.val he)
      simp [MonomialArtin.X_mul_X,hs,coeffAt_apply,MonomialArtin.coeff_X,hi,hprod]
    · simp [MonomialArtin.X_mul_X,hs]

/--
@isnad1 id=eq.3h9v.s10.ffff2529b1f4 from=translated src=- shape=32b39247 vocab=b761bc49
-/
theorem root_coeff_zero_of_nondvd_and_surviving_product (S : Finset (Normal a b c))
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b c) (hs : s ∈ S) (l e : MonomialIndex S)
    (hn : ¬l.1 ∣ s) (hp : l.1 * e.1 ∈ standardFinset S) :
    coeffAt (k := k) S e (F (U (k := k) S (rootIndex S s hs))) = 0 := by
  apply coeff_eq_zero_of_annihilator S F l e ⟨l.1 * e.1,hp⟩ (rootIndex S s hs)
    ((X_smul_rootDual_eq_zero_iff S s hs l).mpr hn)
  rfl
end
end P23.Artin

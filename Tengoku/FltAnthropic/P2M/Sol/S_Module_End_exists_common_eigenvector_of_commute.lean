import Tengoku.FltAnthropic.Theorems.Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
import Tengoku.Seed.LinearAlgebra.Eigenspace.Pi
import Tengoku.Seed.LinearAlgebra.Eigenspace.Triangularizable
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_End_exists_common_eigenvector_of_commute.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_End_exists_common_eigenvector_of_commute

set_option autoImplicit false

open Module Algebra
open scoped IsMulCommutative

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  classical

  let A : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range T)

  haveI : IsMulCommutative A := isMulCommutative_adjoin K
    (fun a ⟨i, hi⟩ b ⟨j, hj⟩ => hi ▸ hj ▸ (hcomm i j).eq)
  letI : CommRing A := inferInstance

  haveI : SMulCommClass A K V := Subalgebra.smulCommClass_left A
  haveI : FaithfulSMul A V := inferInstance

  haveI : Nontrivial A :=
    ⟨⟨0, 1, fun h => (zero_ne_one (α := Module.End K V)) (Subtype.ext_iff.mp h)⟩⟩

  obtain ⟨⟨𝔭, h𝔭⟩⟩ := Ideal.nonempty_minimalPrimes (R := A) (I := ⊥) bot_ne_top
  have h𝔭' : 𝔭 ∈ minimalPrimes A := h𝔭

  obtain ⟨χ, -, v, hv0, -, -, heig⟩ :=
    DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
      (K := K) (V := V) (T := A) h𝔭'

  have hTmem : ∀ i, T i ∈ A := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  refine ⟨fun i => χ ⟨T i, hTmem i⟩, v, hv0, fun i => ?_⟩

  have : (⟨T i, hTmem i⟩ : A) • v = χ ⟨T i, hTmem i⟩ • v := heig _
  simp at this ⊢
  exact this

import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Localization
import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Localization
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.Algebra.Algebra.Tower
import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.RingTheory.Ideal.NatInt
import Tengoku.Seed.RingTheory.TensorProduct.Free
import Tengoku.Seed.RingTheory.TensorProduct.Maps
import Tengoku.Seed.LinearAlgebra.FreeModule.PID
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_exists_prime_natCast_mem_of_isMaximal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_exists_prime_natCast_mem_of_isMaximal

open Ideal

/--
@isnad1 id=ex.1h2v.s6.93e53f2b7818 from=translated src=- shape=ed427fc3 vocab=630836da
-/
theorem solution {T : Type*} [CommRing T] [Module.Finite ℤ T] (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal) : ∃ p : ℕ, p.Prime ∧ (p : T) ∈ 𝔪 := by
  classical
  haveI := h𝔪
  haveI : Algebra.IsIntegral ℤ T := inferInstance
  have hmax : (𝔪.comap (algebraMap ℤ T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
  set P := 𝔪.comap (algebraMap ℤ T) with hP
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P = Ideal.span {n} :=
    ⟨Submodule.IsPrincipal.generator P, (Ideal.span_singleton_generator P).symm⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hbot : P = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hmax Int.not_isField hbot
  have hprime : Prime n := (Ideal.span_singleton_prime hn0).mp (hn ▸ hmax.isPrime)
  refine ⟨n.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  have hmemP : (n.natAbs : ℤ) ∈ P := by
    rw [hn, Ideal.mem_span_singleton]
    exact Int.dvd_natAbs_self
  have := Ideal.mem_comap.mp hmemP
  simpa using this

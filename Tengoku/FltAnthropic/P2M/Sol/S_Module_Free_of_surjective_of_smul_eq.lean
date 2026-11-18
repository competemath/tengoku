import Tengoku.Seed.LinearAlgebra.FreeModule.Basic
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.Seed.Algebra.Module.Torsion.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_Free_of_surjective_of_smul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_Free_of_surjective_of_smul_eq

theorem FrobChareqDock.bijective_aux {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Function.Bijective g := by
  refine ⟨?_, hsurj⟩
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro s hs
  have hann : s ∈ Module.annihilator S N := Module.mem_annihilator.mpr fun n => by
    rw [← hg s n, RingHom.mem_ker.mp hs, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := S) (M := N)).mpr inferInstance] at hann

theorem solution {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Module.Free T N := by
  rcases subsingleton_or_nontrivial N with _ | _
  · infer_instance
  · exact Module.Free.of_basis <| (Module.Free.chooseBasis S N).mapCoeffs
      (RingEquiv.ofBijective g (FrobChareqDock.bijective_aux g hg hsurj)) (fun c x => hg c x)

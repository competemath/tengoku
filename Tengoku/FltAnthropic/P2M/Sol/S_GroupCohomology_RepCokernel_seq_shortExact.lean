import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepCokernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GroupCohomology_RepCokernel_seq_shortExact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GroupCohomology_RepCokernel_seq_shortExact

set_option autoImplicit false
universe u
open CategoryTheory

theorem solution {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) : (GroupCohomology.RepCokernel.seq f).ShortExact where
  exact := (forget₂ (Rep.{u} k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
        obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
        exact ⟨a, ha⟩
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open IsLocalRing in

/--
@isnad1 id=and.4h9v.s12.e9a6617a5f1a from=translated src=- shape=b215240e vocab=4f8792b4
-/
theorem IsLocalRing.isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
    (O : Type u) [CommRing O] [IsLocalRing O]
    (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
    (resA' : A' →+* ResidueField O) (hc' : resA'.comp (algebraMap O A') = residue O)
    (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
    (resA'' : A'' →+* ResidueField O) (hc'' : resA''.comp (algebraMap O A'') = residue O)
    (A : Type u) [CommRing A] [Algebra O A] (resA : A →+* ResidueField O)
    (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
    (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA'') :
    IsLocalRing ↥(AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))) ∧
    IsArtinianRing ↥(AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))) ∧
    Function.Surjective (resA'.comp ((AlgHom.fst O A' A'').comp
      (AlgHom.equalizer (q'.comp (AlgHom.fst O A' A'')) (q''.comp (AlgHom.snd O A' A''))).val).toRingHom) := by exact @_root_.P2MW.S_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue.solution O _ _ A' _ _ _ _ resA' hc' A'' _ _ _ _ resA'' hc'' A _ _ resA q' hq' q'' hq''

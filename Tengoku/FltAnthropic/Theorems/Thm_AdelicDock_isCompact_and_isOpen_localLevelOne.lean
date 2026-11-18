import Tengoku.FltAnthropic.Definitions.Def_AdelicDock_LocalEmbedding
import Tengoku.FltAnthropic.P2M.Sol.S_AdelicDock_isCompact_and_isOpen_localLevelOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AdelicDock_isCompact_and_isOpen_localLevelOne.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsDedekindDomain NumberField

/--
@isnad1 id=and.1h3v.s10.36edc66622aa from=translated src=- shape=aabb984f vocab=d00e6e22
-/
theorem AdelicDock.isCompact_and_isOpen_localLevelOne (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    IsCompact (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by exact @_root_.P2MW.S_AdelicDock_isCompact_and_isOpen_localLevelOne.solution K _ _ v N hN

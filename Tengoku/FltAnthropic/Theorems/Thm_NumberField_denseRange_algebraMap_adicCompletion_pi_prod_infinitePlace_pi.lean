import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
theorem NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    DenseRange (fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
       (fun w : NumberField.InfinitePlace K => algebraMap K w.Completion x))) := by exact @_root_.P2MW.S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.solution K _ _ S

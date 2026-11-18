import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsSMulRegular_tensorProduct_of_flat_quotSMulTop.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct

universe u v w

theorem IsSMulRegular.tensorProduct_of_flat_quotSMulTop
    {A : Type u} [CommRing A] (t : A) {B : Type v} [AddCommGroup B] [Module A B]
    {M : Type w} [AddCommGroup M] [Module A M]
    (htA : IsSMulRegular A t) (htB : IsSMulRegular B t) (htM : IsSMulRegular M t)
    [Module.Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t B)] :
    IsSMulRegular (M ⊗[A] B) t := by exact @_root_.P2MW.S_IsSMulRegular_tensorProduct_of_flat_quotSMulTop.solution A _ t B _ _ M _ _ htA htB htM _

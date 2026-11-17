import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem MvPolynomial.mem_span_map_of_aeval_X_pow_mem_span_map
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K] {σ : Type*} (n : ℕ)
    (f : MvPolynomial σ (ZMod p)) (hf : Prime f) (g : MvPolynomial σ K)
    (hg : MvPolynomial.aeval (fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ p ^ n) g ∈
      Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f}) :
    g ∈ Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f} := by exact @_root_.P2MW.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map.solution p _ K _ _ σ n f hf g hg

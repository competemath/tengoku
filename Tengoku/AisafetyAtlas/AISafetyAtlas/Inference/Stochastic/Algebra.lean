module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Stochastic.Gibbs
public import Tengoku.Seed.Data.Finset.Lattice.Fold
public import Tengoku.Seed.Tactic.NormNum
public import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proposition 6's algebra, with no probability in it

Everything Proposition 6 does after the four conditional-expectation identities is
arithmetic: `H` is the unit hypercube, `k`, `m`, `n` are differences of its
coordinates, and the bound at `α = β = 1/2` is a closed form in them.

None of it mentions a measure, a device, or a universe. It therefore lives here,
where the `FinPMF` layer and the general measure layer both reach it and neither
depends on the other — the same reason `Gibbs.lean` exists.
-/

namespace AISafetyAtlas.Inference

public theorem sup'_eq_max_of_eq_pair {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) (h : α → ℝ) {a b : α} (hsab : s = {a, b}) :
    s.sup' hs h = max (h a) (h b) := by
  subst hsab
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun c hc => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' h (by simp)) (Finset.le_sup' h (by simp))

/-- The paper's `z⃗ ∈ H`: the four conditional probabilities
`zᵢ = P(g = 1 ∣ x₁, x₂)`. `H` is the **unit** hypercube, since the `zᵢ` are
probabilities.-/
public structure Prop6Quadruple where
  /-- `P(g = 1 ∣ x₁ = −1, x₂ = −1)`.-/
  z1 : ℝ
  /-- `P(g = 1 ∣ x₁ = −1, x₂ = +1)`.-/
  z2 : ℝ
  /-- `P(g = 1 ∣ x₁ = +1, x₂ = −1)`.-/
  z3 : ℝ
  /-- `P(g = 1 ∣ x₁ = +1, x₂ = +1)`.-/
  z4 : ℝ
  z1_mem : 0 ≤ z1 ∧ z1 ≤ 1
  z2_mem : 0 ≤ z2 ∧ z2 ≤ 1
  z3_mem : 0 ≤ z3 ∧ z3 ≤ 1
  z4_mem : 0 ≤ z4 ∧ z4 ≤ 1

/-- `k(z⃗) = z₁ + z₄ − z₂ − z₃`.-/
@[expose] public def Prop6Quadruple.k (z : Prop6Quadruple) : ℝ :=
  z.z1 + z.z4 - z.z2 - z.z3

/-- `m(z⃗) = z₂ − z₄`.-/
@[expose] public def Prop6Quadruple.m (z : Prop6Quadruple) : ℝ := z.z2 - z.z4

/-- `n(z⃗) = z₃ − z₄`.-/
@[expose] public def Prop6Quadruple.n (z : Prop6Quadruple) : ℝ := z.z3 - z.z4

/-- The source's right-hand side at a point of `H`.-/
@[expose] public def prop6Expr (α β : ℝ) (z : Prop6Quadruple) : ℝ :=
  |α * β * (z.k) ^ 2 + α * z.k * z.m + β * z.k * z.n + z.m * z.n|

/-- The source's own maximizer: *"One is when `z₁ = 1`, and `z₂, z₃, z₄` all equal
`0`."*-/
@[expose] public def prop6Maximizer : Prop6Quadruple where
  z1 := 1
  z2 := 0
  z3 := 0
  z4 := 0
  z1_mem := ⟨by norm_num, le_refl 1⟩
  z2_mem := ⟨le_refl 0, by norm_num⟩
  z3_mem := ⟨le_refl 0, by norm_num⟩
  z4_mem := ⟨le_refl 0, by norm_num⟩

/-! ### The maximum over `M` exists

Wolpert 2018 Proposition 11 prints its bound as `ε₁ε₂ ≤ max_{z⃗ ∈ M} |…|`, with
`M` the unit hypercube — which is exactly `Prop6Quadruple`, whose membership
conditions are bundled into the structure. Writing that maximum in Lean needs the
family to be bounded above, which is what these two give.
-/

end AISafetyAtlas.Inference

import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.ChainSpaces.Space
import Tengoku.Seed.Analysis.Normed.Operator.Bilinear
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operators between chain-limit spaces

The operators used in the proof of Theorem F.1, for residual maps `ρ`, `ρ'` on `V`,
`V'`, between the chain-limit spaces `E = chainSpace ρ` and `E' = chainSpace ρ'`:
* `singleVec ρ i v = v_{[i]}` (the family equal to `v` at the word `i`), `evalAt ρ i x = x_i`;
* `singleOp ρ ρ' i g = g_{[i]}`, the operator `x ↦ (g x_i)_{[i]}`;
* `evalForm ρ' δ i = δ'_i`, the alternating form `z ↦ δ(z_{1,i}, …, z_{k,i})` on `E'`;
* along a `j`-chain sequence `s`: `chainVec` (`t ↦ t · x`, where `x` equals a vector of
  `ker (ρ j)` on the chain) and `chainOp` (`t ↦ u_t`, with `(u_t x)_w = t_w g(x_w)` on the chain),
  both continuous linear in `t ∈ ℓ^∞(List L, K)`.
The membership criterion is `mem_chainSpace_of_supported_tendsto`: a family supported on a
`j`-chain whose `j`-residual tends to zero along the chain lies in the chain-limit space.
-/

open Filter Topology
open scoped ENNReal

namespace AlternatingAnalytic.ChainSpaces

variable {K : Type*} [NontriviallyNormedField K] {L : Type*}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
  {V' : Type*} [NormedAddCommGroup V'] [NormedSpace K V']

section Bounded

/-- A bounded family as an element of `ℓ^∞`.-/
def ofBound (f : List L → V) (C : ℝ) (hf : ∀ w, ‖f w‖ ≤ C) : lp (fun _ : List L => V) ∞ :=
  ⟨f, memℓp_infty ⟨C, by
    rintro _ ⟨w, rfl⟩
    exact hf w⟩⟩

@[simp]
theorem coe_ofBound (f : List L → V) (C : ℝ) (hf : ∀ w, ‖f w‖ ≤ C) :
    ⇑(ofBound f C hf) = f :=
  rfl

theorem norm_ofBound_le {f : List L → V} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ w, ‖f w‖ ≤ C) :
    ‖ofBound f C hf‖ ≤ C :=
  lp.norm_le_of_forall_le hC hf

/-- A family supported on the words of a sequence, tending to zero along it, tends to zero along
the cofinite filter.-/
theorem tendsto_cofinite_of_supported {f : List L → V} {s : ℕ → List L}
    (hsupp : ∀ w, w ∉ Set.range s → f w = 0)
    (hf : Tendsto (fun n => f (s n)) atTop (𝓝 0)) : Tendsto f cofinite (𝓝 0) := by
  intro U hU
  rw [← Nat.cofinite_eq_atTop] at hf
  have h1 : {n | f (s n) ∈ U}ᶜ.Finite := hf hU
  show {w | f w ∈ U}ᶜ.Finite
  refine (h1.image s).subset fun w hw => ?_
  by_cases hw' : w ∈ Set.range s
  · obtain ⟨n, rfl⟩ := hw'
    exact ⟨n, hw, rfl⟩
  · exact absurd (show f w ∈ U by rw [hsupp w hw']; exact mem_of_mem_nhds hU) hw

/-- If `ρ j` is idempotent, a bounded family supported on the words of a
`j`-chain sequence `s` whose `j`-residual tends to zero along `s` lies in the chain-limit space.-/
theorem mem_chainSpace_of_supported_tendsto (ρ : L → V →L[K] V) {j : L} {s : ℕ → List L}
    (hs : IsChainSeq j s) (hidem : ∀ v, ρ j (ρ j v) = ρ j v) {y : lp (fun _ : List L => V) ∞}
    (hsupp : ∀ w, w ∉ Set.range s → y w = 0)
    (hy : Tendsto (fun n => ρ j (y (s n))) atTop (𝓝 0)) : y ∈ chainSpace ρ := by
  have hb : ∀ w, ‖y w‖ ≤ ‖y‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero y
  let a := ofBound (fun w => y w - ρ j (y w)) ((1 + ‖ρ j‖) * ‖y‖) fun w => by
    calc ‖y w - ρ j (y w)‖ ≤ ‖y w‖ + ‖ρ j (y w)‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + ‖ρ j‖ * ‖y‖ := add_le_add (hb w)
          (((ρ j).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _)))
      _ = (1 + ‖ρ j‖) * ‖y‖ := by ring
  let b := ofBound (fun w => ρ j (y w)) (‖ρ j‖ * ‖y‖) fun w =>
    ((ρ j).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _))
  have hab : y = a + b := lp.ext <| funext fun w => by
    rw [lp.coeFn_add, Pi.add_apply]
    exact (sub_add_cancel _ _).symm
  rw [hab]
  refine add_mem (mem_chainSpace_of_supported ρ hs (fun w => ?_) (fun w hw => ?_))
    (mem_chainSpace_of_tendsto ρ ?_)
  · simp only [a, coe_ofBound, map_sub, hidem, sub_self]
  · simp only [a, coe_ofBound, hsupp w hw, map_zero, sub_zero]
  · exact tendsto_cofinite_of_supported
      (fun w hw => by simp only [b, coe_ofBound, hsupp w hw, map_zero]) hy

end Bounded

section Eval

variable (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V')

/-- Evaluation at a word, on the chain-limit space.-/
noncomputable def evalAt (i : List L) : chainSpace ρ →L[K] V :=
  (lp.evalCLM K (fun _ : List L => V) ∞ i).comp (chainSpace ρ).subtypeL

@[simp]
theorem evalAt_apply (i : List L) (x : chainSpace ρ) :
    evalAt ρ i x = (x : lp (fun _ : List L => V) ∞) i :=
  rfl

/-- `δ'_i`: the alternating form `z ↦ δ(z_{1,i}, …, z_{k,i})` on `E'`.-/
noncomputable def evalForm {ι : Type*} [Fintype ι] (δ : V' [⋀^ι]→L[K] K) (i : List L) :
    chainSpace ρ' [⋀^ι]→L[K] K :=
  δ.compContinuousLinearMap (evalAt ρ' i)

end Eval

section Single

variable [DecidableEq L] (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V')

theorem single_mem_chainSpace (i : List L) (v : V) : lp.single ∞ i v ∈ chainSpace ρ := by
  refine mem_chainSpace_of_tendsto ρ (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_cofinite_ne i] with w hw
  exact (lp.single_apply_ne (E := fun _ : List L => V) ∞ i v hw).symm

/-- `v ↦ v_{[i]}`: the family equal to `v` at the word `i` and zero elsewhere.-/
noncomputable def singleVec (i : List L) : V →L[K] chainSpace ρ :=
  (lp.singleContinuousLinearMap K (fun _ : List L => V) ∞ i).codRestrict (chainSpace ρ)
    (single_mem_chainSpace ρ i)

@[simp]
theorem coe_singleVec_apply (i : List L) (v : V) :
    (singleVec ρ i v : lp (fun _ : List L => V) ∞) = lp.single ∞ i v :=
  rfl

end Single

section ChainMaps

variable (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V')

theorem norm_indicator_smul_le (s : ℕ → List L) (t : lp (fun _ : List L => K) ∞) (v : V)
    (w : List L) : ‖(Set.range s).indicator (fun w => t w • v) w‖ ≤ ‖t‖ * ‖v‖ :=
  (norm_indicator_le_norm_self _ _).trans <| by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero t w)
      (norm_nonneg _)

theorem indicator_smul_add (s : ℕ → List L) (t t' : List L → K) (f : List L → V) (w : List L) :
    (Set.range s).indicator (fun w => (t w + t' w) • f w) w =
      (Set.range s).indicator (fun w => t w • f w) w +
        (Set.range s).indicator (fun w => t' w • f w) w := by
  by_cases hw : w ∈ Set.range s <;> simp [hw, add_smul]

theorem indicator_smul_add_right (s : ℕ → List L) (t : List L → K) (f f' : List L → V)
    (w : List L) :
    (Set.range s).indicator (fun w => t w • (f w + f' w)) w =
      (Set.range s).indicator (fun w => t w • f w) w +
        (Set.range s).indicator (fun w => t w • f' w) w := by
  by_cases hw : w ∈ Set.range s <;> simp [hw, smul_add]

/-- The family `t · x`, where `x` equals `v` on the words of `s` and zero elsewhere.-/
noncomputable def chainVecLp (s : ℕ → List L) (v : V) (t : lp (fun _ : List L => K) ∞) :
    lp (fun _ : List L => V) ∞ :=
  ofBound ((Set.range s).indicator (fun w => t w • v)) (‖t‖ * ‖v‖)
    (norm_indicator_smul_le s t v)

theorem chainVecLp_mem {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) {v : V} (hv : ρ j v = 0)
    (t : lp (fun _ : List L => K) ∞) : chainVecLp s v t ∈ chainSpace ρ := by
  refine mem_chainSpace_of_supported ρ hs (fun w => ?_) (fun w hw => ?_)
  · by_cases hw : w ∈ Set.range s <;> simp [chainVecLp, hw, hv]
  · simp [chainVecLp, hw]

/-- `t ↦ t · x` as a continuous linear map `ℓ^∞(List L, K) → E`, where `x` equals `v ∈ ker (ρ j)`
on the words of the `j`-chain sequence `s` and zero elsewhere.-/
noncomputable def chainVec {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) {v : V}
    (hv : ρ j v = 0) : lp (fun _ : List L => K) ∞ →L[K] chainSpace ρ :=
  LinearMap.mkContinuous
    { toFun := fun t => ⟨chainVecLp s v t, chainVecLp_mem ρ hs hv t⟩
      map_add' := fun t t' => Subtype.ext <| lp.ext <| funext fun w => by
        simp only [chainVecLp, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, coe_ofBound]
        exact indicator_smul_add s t t' (fun _ => v) w
      map_smul' := fun c t => Subtype.ext <| lp.ext <| funext fun w => by
        by_cases hw : w ∈ Set.range s <;>
          simp [chainVecLp, hw, lp.coeFn_smul, mul_smul] }
    ‖v‖ fun t => by
      refine lp.norm_le_of_forall_le (by positivity) fun w => ?_
      rw [mul_comm]
      exact norm_indicator_smul_le s t v w

/-- The family `(u_t x)_w = t_w g(x_w)` on the words of `s`, zero elsewhere.-/
noncomputable def chainOpLp (s : ℕ → List L) (g : V →L[K] V') (t : lp (fun _ : List L => K) ∞)
    (x : lp (fun _ : List L => V) ∞) : lp (fun _ : List L => V') ∞ :=
  ofBound ((Set.range s).indicator (fun w => t w • g (x w))) (‖t‖ * (‖g‖ * ‖x‖)) fun w =>
    (norm_indicator_le_norm_self _ _).trans <| by
      rw [norm_smul]
      exact mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero t w)
        ((g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x w) (norm_nonneg _)))
        (norm_nonneg _) (norm_nonneg _)

theorem chainOpLp_mem {j : L} {s : ℕ → List L} (hs : IsChainSeq j s)
    (hidem : ∀ v, ρ j (ρ j v) = ρ j v) (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v)
    {g : V →L[K] V'} (hg : ∀ v, ρ j v = 0 → ρ' j (g v) = 0)
    (t : lp (fun _ : List L => K) ∞) (x : chainSpace ρ) :
    chainOpLp s g t x ∈ chainSpace ρ' := by
  refine mem_chainSpace_of_supported_tendsto ρ' hs hidem' (fun w hw => by simp [chainOpLp, hw]) ?_
  have hres : ∀ v, ρ' j (g v) = ρ' j (g (ρ j v)) := fun v => by
    have := hg (v - ρ j v) (by rw [map_sub, hidem, sub_self])
    rwa [map_sub, map_sub, sub_eq_zero] at this
  have hx : Tendsto (fun n => ρ j ((x : lp (fun _ : List L => V) ∞) (s n))) atTop (𝓝 0) :=
    x.2 j s hs
  have h1 : Tendsto (fun n => ρ' j (g (ρ j ((x : lp (fun _ : List L => V) ∞) (s n)))))
      atTop (𝓝 0) := by
    simpa only [map_zero, Function.comp_def, ContinuousLinearMap.comp_apply] using
      (((ρ' j).comp g).continuous.tendsto 0).comp hx
  have h2 : Tendsto (fun n => ‖t‖ * ‖ρ' j (g (ρ j ((x : lp (fun _ : List L => V) ∞) (s n))))‖)
      atTop (𝓝 0) := by
    have := h1.norm.const_mul ‖t‖
    rwa [norm_zero, mul_zero] at this
  refine squeeze_zero_norm (fun n => ?_) h2
  simp only [chainOpLp, coe_ofBound, Set.indicator_of_mem (Set.mem_range_self n), map_smul,
    norm_smul]
  rw [hres]
  exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero t (s n))
    (norm_nonneg _)

/-- `t ↦ u_t` as a continuous linear map `ℓ^∞(List L, K) → L(E, E')`, where
`(u_t x)_w = t_w g(x_w)` on the words of the `j`-chain sequence `s` and zero elsewhere; here `g`
maps `ker (ρ j)` into `ker (ρ' j)`.-/
noncomputable def chainOp {j : L} {s : ℕ → List L} (hs : IsChainSeq j s)
    (hidem : ∀ v, ρ j (ρ j v) = ρ j v) (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v)
    {g : V →L[K] V'} (hg : ∀ v, ρ j v = 0 → ρ' j (g v) = 0) :
    lp (fun _ : List L => K) ∞ →L[K] (chainSpace ρ →L[K] chainSpace ρ') :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ K (fun t x => ⟨chainOpLp s g t x, chainOpLp_mem ρ ρ' hs hidem hidem' hg t x⟩)
      (fun t t' x => Subtype.ext <| lp.ext <| funext fun w => by
        simp only [chainOpLp, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, coe_ofBound]
        exact indicator_smul_add s t t' (fun w => g ((x : lp (fun _ : List L => V) ∞) w)) w)
      (fun c t x => Subtype.ext <| lp.ext <| funext fun w => by
        by_cases hw : w ∈ Set.range s <;>
          simp [chainOpLp, hw, lp.coeFn_smul, mul_smul])
      (fun t x x' => Subtype.ext <| lp.ext <| funext fun w => by
        simp only [chainOpLp, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, coe_ofBound, map_add]
        exact indicator_smul_add_right s t (fun w => g ((x : lp (fun _ : List L => V) ∞) w))
          (fun w => g ((x' : lp (fun _ : List L => V) ∞) w)) w)
      (fun c t x => Subtype.ext <| lp.ext <| funext fun w => by
        by_cases hw : w ∈ Set.range s <;>
          simp [chainOpLp, hw, lp.coeFn_smul, smul_comm (t w) c]))
    ‖g‖ fun t x => by
      calc ‖(⟨chainOpLp s g t x, chainOpLp_mem ρ ρ' hs hidem hidem' hg t x⟩ : chainSpace ρ')‖
          = ‖chainOpLp s g t x‖ := rfl
        _ ≤ ‖t‖ * (‖g‖ * ‖(x : lp (fun _ : List L => V) ∞)‖) := norm_ofBound_le (by positivity) _
        _ = ‖g‖ * ‖t‖ * ‖x‖ := by
          rw [show ‖x‖ = ‖(x : lp (fun _ : List L => V) ∞)‖ from rfl]
          ring

end ChainMaps

end AlternatingAnalytic.ChainSpaces

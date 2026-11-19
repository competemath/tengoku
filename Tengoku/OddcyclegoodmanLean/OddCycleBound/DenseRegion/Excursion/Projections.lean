import Tengoku.OddcyclegoodmanLean.OddCycleBound.Excursion.Tuples
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.GraphonKrylovBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projection words and their evaluation (Section 3)

For a graphon `V` (later `V = U = 1 - W` and `V = W`) the integral operator `T_V` splits as
`T_V = P T_V + Q T_V` with `P` the projection onto constants and `Q = I - P`. Both summands are
integral operators, with kernels

* `kerP V (x, y) = d_V(y)` (the kernel of `P M_V`), and
* `kerQ V (x, y) = V(x, y) - d_V(y)` (the kernel of `Q M_V`).

A word `R₁ ⋯ R_m` in `P` (`false`) and `Q` (`true`) gives the kernel of `R₁ M_V ⋯ R_m M_V`
(`wordKer`). Expanding the `m`-fold kernel product gives the sum over all words
(`compPow_eq_sum_listKer`, equation `eq:trace-projection-expansion`). Traces of words are invariant
under rotation (cyclicity of the trace). Words are evaluated through their blocks, using the
vector form: `R M_V` acting on functions is `f ↦ (∫ d_V f) 1` for `R = P` and the compression
`f ↦ T_V f - (∫ T_V f) 1` for `R = Q`, so a block `P M_V (Q M_V)^{β+1}` contributes
`gᵀ A^β g = specMoment V μ β`, and an internal `P` step contributes `q = edgeDensity V μ`.
-/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

open Excursion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Ω → Ω → ℝ}

/-! ### The kernels of `P M_V` and `Q M_V` -/

/-- The kernel of `P M_V`: `(x, y) ↦ d_V(y)`.-/
noncomputable def kerP (V : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → Ω → ℝ := fun _ y => degree V μ y

/-- The kernel of `Q M_V`: `(x, y) ↦ V(x, y) - d_V(y)`.-/
noncomputable def kerQ (V : Ω → Ω → ℝ) (μ : Measure Ω) : Ω → Ω → ℝ :=
  fun x y => V x y - degree V μ y

/-- The kernel of `R M_V` for a letter `R` (`false = P`, `true = Q`).-/
noncomputable def letterKer (V : Ω → Ω → ℝ) (μ : Measure Ω) (b : Bool) : Ω → Ω → ℝ :=
  if b then kerQ V μ else kerP V μ

/-- The kernel of `R_b M_V R_{l₁} M_V ⋯` for the nonempty word `b :: l`.-/
noncomputable def wordKer (V : Ω → Ω → ℝ) (μ : Measure Ω) : Bool → List Bool → Ω → Ω → ℝ
  | b, [] => letterKer V μ b
  | b, c :: l => comp μ (letterKer V μ b) (wordKer V μ c l)

/-- The kernel of a word given as a list (the empty word does not occur).-/
noncomputable def listKer (V : Ω → Ω → ℝ) (μ : Measure Ω) : List Bool → Ω → Ω → ℝ
  | [] => fun _ _ => 0
  | b :: l => wordKer V μ b l

omit [IsProbabilityMeasure μ] in
lemma kerP_add_kerQ (x y : Ω) : kerP V μ x y + kerQ V μ x y = V x y := by
  simp only [kerP, kerQ]; ring

lemma goodK_kerP (hV : IsGraphon V μ) : GoodK (kerP V μ) := by
  obtain ⟨C, hC0, hC⟩ := (good_degree hV).bdd
  exact ⟨(good_degree hV).meas.measurable.comp measurable_snd, ⟨C, hC0, fun _ y => hC y⟩⟩

lemma goodK_kerQ (hV : IsGraphon V μ) : GoodK (kerQ V μ) := by
  obtain ⟨C, hC0, hC⟩ := (good_degree hV).bdd
  refine ⟨hV.meas.sub ((good_degree hV).meas.measurable.comp measurable_snd),
    ⟨1 + C, by positivity, fun x y => ?_⟩⟩
  simp only [kerQ]
  have h1 : |V x y| ≤ 1 := by
    rw [abs_of_nonneg (hV.nonneg x y)]; exact hV.le_one x y
  calc |V x y - degree V μ y| ≤ |V x y| + |degree V μ y| := abs_sub _ _
    _ ≤ 1 + C := add_le_add h1 (hC y)

lemma goodK_letterKer (hV : IsGraphon V μ) (b : Bool) : GoodK (letterKer V μ b) := by
  cases b
  · exact goodK_kerP hV
  · exact goodK_kerQ hV

lemma goodK_wordKer (hV : IsGraphon V μ) : ∀ (b : Bool) (l : List Bool), GoodK (wordKer V μ b l)
  | b, [] => goodK_letterKer hV b
  | b, c :: l => goodK_comp (goodK_letterKer hV b) (goodK_wordKer hV c l)

lemma goodK_listKer (hV : IsGraphon V μ) : ∀ l : List Bool, GoodK (listKer V μ l)
  | [] => goodK_zero
  | b :: l => goodK_wordKer hV b l

/-! ### Kernel algebra over finite sums -/

lemma comp_finset_sum_right {ι : Type*} (s : Finset ι) {K : Ω → Ω → ℝ} (hK : GoodK K)
    {L : ι → Ω → Ω → ℝ} (hL : ∀ i ∈ s, GoodK (L i)) :
    comp μ K (fun x y => ∑ i ∈ s, L i x y) = fun x y => ∑ i ∈ s, comp μ K (L i) x y := by
  funext x y
  simp only [comp, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_KL hK (hL i hi) x y

lemma trace_finset_sum {ι : Type*} (s : Finset ι) {L : ι → Ω → Ω → ℝ}
    (hL : ∀ i ∈ s, GoodK (L i)) :
    trace μ (fun x y => ∑ i ∈ s, L i x y) = ∑ i ∈ s, trace μ (L i) := by
  simp only [trace]
  exact integral_finsetSum s fun i hi => (hL i hi).diag_integrable

/-! ### Expansion of kernel powers over words -/

lemma comp_eq_kerP_add_kerQ (hV : IsGraphon V μ) {L : Ω → Ω → ℝ} (hL : GoodK L) :
    comp μ V L = fun x y => comp μ (kerP V μ) L x y + comp μ (kerQ V μ) L x y := by
  rw [← comp_add_left (goodK_kerP hV) (goodK_kerQ hV) hL]
  congr 1
  funext x y
  exact (kerP_add_kerQ x y).symm

omit [IsProbabilityMeasure μ] in
lemma listKer_cons_cons (b c : Bool) (l : List Bool) :
    listKer V μ (b :: c :: l) = comp μ (letterKer V μ b) (listKer V μ (c :: l)) := rfl

/-- **Equation `eq:trace-projection-expansion`** at the level of kernels: the `(n+1)`-fold kernel
product of `V` is the sum, over all words of length `n + 1`, of the word kernels.-/
theorem compPow_eq_sum_listKer (hV : IsGraphon V μ) : ∀ n : ℕ,
    compPow μ V n = fun x y => ∑ w ∈ allWords (n + 1), listKer V μ w x y
  | 0 => by
      funext x y
      rw [sum_allWords_succ]
      simp only [allWords, listsOf, Finset.sum_singleton]
      exact (kerP_add_kerQ x y).symm
  | n + 1 => by
      have hGV := goodK_of_isGraphon hV
      have hmem : ∀ w ∈ allWords (n + 1), GoodK (listKer V μ w) :=
        fun w _ => goodK_listKer hV w
      show comp μ V (compPow μ V n) = _
      rw [compPow_eq_sum_listKer hV n, comp_finset_sum_right _ hGV hmem]
      funext x y
      rw [sum_allWords_succ (n + 1)]
      refine Finset.sum_congr rfl fun w hw => ?_
      obtain ⟨c, l, rfl⟩ : ∃ c l, w = c :: l := by
        have := (mem_allWords.mp hw)
        cases w with
        | nil => simp at this
        | cons c l => exact ⟨c, l, rfl⟩
      rw [listKer_cons_cons, listKer_cons_cons, comp_eq_kerP_add_kerQ hV (goodK_listKer hV _)]
      rfl

/-- The cycle density as a sum over words (`eq:trace-projection-expansion`).-/
theorem cycleDensity_eq_sum_words (hV : IsGraphon V μ) {m : ℕ} (hm : 1 ≤ m) :
    cycleDensity μ V m = ∑ w ∈ allWords m, trace μ (listKer V μ w) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [cycleDensity, Nat.add_sub_cancel, compPow_eq_sum_listKer hV n,
    trace_finset_sum _ fun w _ => goodK_listKer hV w]

/-! ### Cyclicity of the trace -/

lemma wordKer_append_single (hV : IsGraphon V μ) (b : Bool) :
    ∀ (c : Bool) (l : List Bool),
      wordKer V μ c (l ++ [b]) = comp μ (wordKer V μ c l) (letterKer V μ b)
  | c, [] => rfl
  | c, d :: l => by
      show comp μ (letterKer V μ c) (wordKer V μ d (l ++ [b])) = _
      rw [wordKer_append_single hV b d l, ← comp_assoc (goodK_letterKer hV c)
        (goodK_wordKer hV d l) (goodK_letterKer hV b)]
      rfl

lemma trace_listKer_rotate_one (hV : IsGraphon V μ) (l : List Bool) :
    trace μ (listKer V μ (l.rotate 1)) = trace μ (listKer V μ l) := by
  match l with
  | [] => rfl
  | [b] => rw [List.rotate_singleton]
  | b :: c :: l =>
      rw [List.rotate_cons_succ, List.rotate_zero, List.cons_append]
      show trace μ (wordKer V μ c (l ++ [b])) = trace μ (comp μ (letterKer V μ b)
        (wordKer V μ c l))
      rw [wordKer_append_single hV b c l,
        trace_comp_comm (goodK_wordKer hV c l) (goodK_letterKer hV b)]

lemma ofFn_rot_one {n : ℕ} (v : Fin (n + 1) → Bool) :
    List.ofFn (rot 1 v) = (List.ofFn v).rotate 1 := by
  rw [List.ofFn_succ' (rot 1 v), List.ofFn_succ, List.rotate_cons_succ, List.rotate_zero,
    List.concat_eq_append]
  simp only [rot, Fin.coeSucc_eq_succ, Fin.last_add_one]

lemma trace_listKer_ofFn_rot (hV : IsGraphon V μ) {n : ℕ} (j : Fin (n + 1))
    (v : Fin (n + 1) → Bool) :
    trace μ (listKer V μ (List.ofFn (rot j v))) = trace μ (listKer V μ (List.ofFn v)) := by
  induction j using Fin.induction with
  | zero => rw [rot_zero]
  | succ k ih =>
      rw [← Fin.coeSucc_eq_succ, ← rot_rot, ofFn_rot_one, trace_listKer_rotate_one hV, ih]

/-! ### Evaluation of words in vector form -/

/-- `applyWord w f`: apply the operators `R M_V` of the word `w` to `f`, rightmost first.-/
noncomputable def applyWord (V : Ω → Ω → ℝ) (μ : Measure Ω) : List Bool → (Ω → ℝ) → Ω → ℝ
  | [], f => f
  | b :: l, f => kernelOp (letterKer V μ b) μ (applyWord V μ l f)

omit [IsProbabilityMeasure μ] in
lemma applyWord_append (l₁ l₂ : List Bool) (f : Ω → ℝ) :
    applyWord V μ (l₁ ++ l₂) f = applyWord V μ l₁ (applyWord V μ l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons b l₁ ih => simp only [List.cons_append, applyWord, ih]

lemma good_applyWord (hV : IsGraphon V μ) {f : Ω → ℝ} (hf : Good f) :
    ∀ l : List Bool, Good (applyWord V μ l f)
  | [] => hf
  | b :: l => Spectral.L2Kernel.good_kernelOp_goodK (goodK_letterKer hV b) (good_applyWord hV hf l)

lemma integral_comp_row' {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) (x : Ω) :
    ∫ y, comp μ K L x y ∂μ = kernelOp K μ (fun z => ∫ y, L z y ∂μ) x := by
  obtain ⟨CK, _, hCK⟩ := hK.bdd
  obtain ⟨CL, _, hCL⟩ := hL.bdd
  have hint : Integrable (Function.uncurry fun y z => K x z * L z y) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun y z => K x z * L z y) :=
      (hK.meas.comp (measurable_const.prodMk measurable_snd)).mul
        (hL.meas.comp (measurable_snd.prodMk measurable_fst))
    refine (integrable_const (CK * CL)).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hCK _ _) (hCL _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hCK x p.2))
  calc ∫ y, comp μ K L x y ∂μ = ∫ y, ∫ z, K x z * L z y ∂μ ∂μ := rfl
    _ = ∫ z, ∫ y, K x z * L z y ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ z, K x z * ∫ y, L z y ∂μ ∂μ :=
        integral_congr_ae (ae_of_all _ fun z => integral_const_mul _ _)
    _ = kernelOp K μ (fun z => ∫ y, L z y ∂μ) x := rfl

/-- Row sums of word kernels are words applied to the constant function `1`.-/
lemma rowIntegral_wordKer (hV : IsGraphon V μ) : ∀ (b : Bool) (l : List Bool),
    (fun x => ∫ y, wordKer V μ b l x y ∂μ) = applyWord V μ (b :: l) (fun _ => 1)
  | b, [] => by
      funext x
      simp only [wordKer, applyWord, kernelOp, mul_one]
  | b, c :: l => by
      funext x
      show ∫ y, comp μ (letterKer V μ b) (wordKer V μ c l) x y ∂μ = _
      rw [integral_comp_row' (goodK_letterKer hV b) (goodK_wordKer hV c l),
        rowIntegral_wordKer hV c l]
      rfl

omit [IsProbabilityMeasure μ] in
lemma kernelOp_kerP (f : Ω → ℝ) :
    kernelOp (kerP V μ) μ f = fun _ => ∫ y, degree V μ y * f y ∂μ := rfl

/-- `P M_V` acting on functions: `f ↦ (∫ d_V f) · 1`. The trace of a word that starts with `P`
is the constant value of the word applied to `1`.-/
lemma applyWord_false_cons (hV : IsGraphon V μ) (l : List Bool) :
    applyWord V μ (false :: l) (fun _ => 1) = fun _ => trace μ (listKer V μ (false :: l)) := by
  funext x
  cases l with
  | nil =>
      show ∫ y, degree V μ y * 1 ∂μ = ∫ x, degree V μ x ∂μ
      simp
  | cons c l =>
      have hW := goodK_wordKer hV c l
      obtain ⟨C, _, hC⟩ := hW.bdd
      obtain ⟨Cd, _, hCd⟩ := (good_degree hV).bdd
      have hint : Integrable (Function.uncurry fun x z => degree V μ z * wordKer V μ c l z x)
          (μ.prod μ) := by
        have hm : Measurable (Function.uncurry fun x z => degree V μ z * wordKer V μ c l z x) :=
          ((good_degree hV).meas.measurable.comp measurable_snd).mul
            (hW.meas.comp (measurable_snd.prodMk measurable_fst))
        refine (integrable_const (Cd * C)).mono' hm.aestronglyMeasurable
          (ae_of_all _ fun p => ?_)
        simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCd _) (hC _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hCd p.2))
      show kernelOp (kerP V μ) μ (applyWord V μ (c :: l) fun _ => 1) x =
        ∫ x, comp μ (kerP V μ) (wordKer V μ c l) x x ∂μ
      rw [← rowIntegral_wordKer hV c l, kernelOp_kerP]
      simp only [comp, kerP]
      rw [integral_integral_swap hint]
      exact integral_congr_ae (ae_of_all _ fun z => (integral_const_mul _ _).symm)

/-- `Q M_V` acting on functions is the compression `f ↦ T_V f - (∫ T_V f) 1`.-/
lemma kernelOp_kerQ (hV : IsGraphon V μ) {f : Ω → ℝ} (hf : Good f) :
    kernelOp (kerQ V μ) μ f = compress V μ f := by
  funext x
  have h1 : ∫ y, degree V μ y * f y ∂μ = mean μ (kernelOp V μ f) := by
    have hs := kernelOp_symm hV good_one hf
    rw [kernelOp_one hV] at hs
    simp only [one_mul] at hs
    rw [mean, ← hs]
  show ∫ y, (V x y - degree V μ y) * f y ∂μ = kernelOp V μ f x - mean μ (kernelOp V μ f)
  have e : (fun y => (V x y - degree V μ y) * f y) =
      fun y => V x y * f y - degree V μ y * f y := by funext y; ring
  rw [e, integral_sub (integrable_Uf hV hf x) ((good_degree hV).mul hf).integrable, h1]
  rfl

lemma kernelOp_eq_kerP_add_kerQ (hV : IsGraphon V μ) {f : Ω → ℝ} (hf : Good f) (x : Ω) :
    kernelOp V μ f x = kernelOp (kerP V μ) μ f x + kernelOp (kerQ V μ) μ f x := by
  simp only [kernelOp]
  rw [← integral_add (Spectral.L2Kernel.integrable_Kf (goodK_kerP hV) hf x)
    (Spectral.L2Kernel.integrable_Kf (goodK_kerQ hV) hf x)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [kerP, kerQ]; ring

/-! ### Block evaluation -/

omit [IsProbabilityMeasure μ] in
lemma applyWord_replicate_false (hV : IsGraphon V μ) (c : ℝ) : ∀ a : ℕ,
    applyWord V μ (List.replicate a false) (fun _ => c) = fun _ => edgeDensity V μ ^ a * c
  | 0 => by funext x; simp [applyWord]
  | a + 1 => by
      rw [List.replicate_succ]
      show kernelOp (kerP V μ) μ (applyWord V μ (List.replicate a false) fun _ => c) = _
      rw [applyWord_replicate_false hV c a, kernelOp_kerP]
      funext x
      rw [integral_mul_const]
      change edgeDensity V μ * (edgeDensity V μ ^ a * c) = _
      ring

omit [IsProbabilityMeasure μ] in
lemma compress_one (hV : IsGraphon V μ) :
    compress V μ (fun _ => 1) = compressIter V μ 0 := by
  funext x
  show kernelOp V μ (fun _ => 1) x - mean μ (kernelOp V μ fun _ => 1) = degCentered V μ x
  rw [kernelOp_one hV]
  rfl

/-- A `Q`-block of length `β + 1`, applied to a constant `c`, gives `c · A^β g`.-/
lemma applyWord_replicate_true (hV : IsGraphon V μ) (c : ℝ) : ∀ β : ℕ,
    applyWord V μ (List.replicate (β + 1) true) (fun _ => c) =
      fun x => c * compressIter V μ β x
  | 0 => by
      show kernelOp (kerQ V μ) μ (fun _ => c) = _
      rw [kernelOp_kerQ hV ⟨stronglyMeasurable_const, ⟨|c|, abs_nonneg c, fun _ => le_rfl⟩⟩]
      have : (fun _ : Ω => c) = fun y => c * (fun _ : Ω => (1 : ℝ)) y := by funext; ring
      rw [this, compress_const_mul, compress_one hV]
  | β + 1 => by
      rw [List.replicate_succ]
      show kernelOp (kerQ V μ) μ (applyWord V μ (List.replicate (β + 1) true) fun _ => c) = _
      rw [applyWord_replicate_true hV c β,
        kernelOp_kerQ hV (f := fun x => c * compressIter V μ β x)
          (good_smul c (good_compressIter hV β)), compress_const_mul]
      rfl

/-- The block identity `P M_V (Q M_V)^{β+1}` on a constant `c`: the excursion contributes
`gᵀ A^β g = specMoment V μ β`.-/
lemma kernelOp_kerP_compressIter (hV : IsGraphon V μ) (c : ℝ) (β : ℕ) :
    kernelOp (kerP V μ) μ (fun x => c * compressIter V μ β x) =
      fun _ => c * specMoment V μ β := by
  rw [kernelOp_kerP]
  funext x
  have e : (fun y => degree V μ y * (c * compressIter V μ β y)) =
      fun y => c * (edgeDensity V μ * compressIter V μ β y) +
        c * (degCentered V μ y * compressIter V μ β y) := by
    funext y; rw [degree_eq y]; ring
  rw [e, integral_add (((good_compressIter hV β).integrable.const_mul _).const_mul _)
      (((good_degCentered hV).mul (good_compressIter hV β)).integrable.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
  have h0 : ∫ y, compressIter V μ β y ∂μ = 0 := mean_compressIter hV β
  rw [h0]
  show c * (edgeDensity V μ * 0) + c * specMoment V μ β = _
  ring

/-- The pair of blocks `P^{α+1} Q^{β+1}` multiplies a constant by `q^α · gᵀ A^β g`.-/
lemma applyWord_blk (hV : IsGraphon V μ) (p : ℕ × ℕ) (c : ℝ) :
    applyWord V μ (blk p) (fun _ => c) =
      fun _ => edgeDensity V μ ^ p.1 * specMoment V μ p.2 * c := by
  rw [blk, applyWord_append, applyWord_replicate_true hV c p.2, List.replicate_succ',
    applyWord_append]
  show applyWord V μ (List.replicate p.1 false)
    (kernelOp (kerP V μ) μ fun x => c * compressIter V μ p.2 x) = _
  rw [kernelOp_kerP_compressIter hV, applyWord_replicate_false hV]
  funext x; ring

/-- **Equation `eq:excursion-length-weight`** in vector form: the word `blockWord t ++ P^a`
applied to `1` is the constant `q^a ∏ q^{αᵢ} gᵀ A^{βᵢ} g`.-/
lemma applyWord_blockWord (hV : IsGraphon V μ) (a : ℕ) : ∀ t : List (ℕ × ℕ),
    applyWord V μ (blockWord t ++ List.replicate a false) (fun _ => 1) =
      fun _ => edgeDensity V μ ^ a * tupleWeight (edgeDensity V μ) (specMoment V μ) t
  | [] => by
      rw [blockWord_nil, List.nil_append, applyWord_replicate_false hV]
      simp
  | p :: t => by
      rw [blockWord_cons, List.append_assoc, applyWord_append, applyWord_blockWord hV a t,
        applyWord_blk hV, tupleWeight_cons]
      funext x; ring

end OddCycleBound.DenseRegion

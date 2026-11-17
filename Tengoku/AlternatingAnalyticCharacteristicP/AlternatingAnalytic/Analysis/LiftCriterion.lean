import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Analytic.CPolynomial
import Tengoku.Seed.Analysis.Analytic.Composition
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Tengoku.Seed.Analysis.Calculus.ContDiff.CPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded lifts and analyticity of precomposition

The precomposition map `Q f = (m ↦ m ∘ (f, …, f))` on continuous alternating maps is analytic at
one point if and only if it has a bounded `k`-linear lift, and then it is a continuous polynomial
everywhere (Proposition 3.3). Lifts also transfer along conjugation, source equivalences, target
retracts, reindexing, and from `(E × 𝕜, E' × 𝕜)` to `(E, E')`. Neither completeness nor a
hypothesis on the characteristic is used.

## Main results

* `tfae_Q`: bounded lift, polynomial everywhere, analytic somewhere, `C^ω` are equivalent.
* `hasBoundedLift_of_hasBoundedLift_succ`: a lift in degree `n + 1` on `(E × 𝕜, E' × 𝕜, F)`
  gives a lift in degree `n` on `(E, E', F)`.
* `hasBoundedLift_reindex`: the lift property depends only on the number of arguments.
-/

open scoped ContDiff

namespace LiftCriterion

/-! ## The top coefficient of a power series along lines -/

section Extraction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The one-variable formal power series of `t ↦ ∑_{r ≤ k} t ^ r • b r`.-/
noncomputable def polySeries (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (k : ℕ) (b : ℕ → Z) :
    FormalMultilinearSeries 𝕜 𝕜 Z :=
  fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (if n ≤ k then b n else 0)

lemma polySeries_apply (k : ℕ) (b : ℕ → Z) (n : ℕ) (m : Fin n → 𝕜) :
    polySeries 𝕜 k b n m = (∏ i, m i) • (if n ≤ k then b n else 0) :=
  ContinuousMultilinearMap.mkPiRing_apply _ _

lemma polySeries_eq_zero_of_gt (k : ℕ) (b : ℕ → Z) {n : ℕ} (hn : k < n) :
    polySeries 𝕜 k b n = 0 := by
  have hb : (if n ≤ k then b n else 0) = 0 := by simp [Nat.not_le.mpr hn]
  rw [polySeries, hb]
  exact ContinuousMultilinearMap.mkPiRing_zero

lemma hasFPowerSeriesAt_polySeries (k : ℕ) (b : ℕ → Z) :
    HasFPowerSeriesAt (fun t : 𝕜 => ∑ r ∈ Finset.range (k + 1), t ^ r • b r)
      (polySeries 𝕜 k b) 0 := by
  have H : HasFiniteFPowerSeriesOnBall
      (fun t : 𝕜 => ∑ r ∈ Finset.range (k + 1), t ^ r • b r) (polySeries 𝕜 k b) 0 (k + 1) ⊤ := by
    refine HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
    · intro m hm
      exact polySeries_eq_zero_of_gt k b (by omega)
    · intro y _
      have : ∀ r ∈ Finset.range (k + 1),
          polySeries 𝕜 k b r (fun _ => y) = y ^ r • b r := by
        intro r hr
        rw [polySeries_apply]
        have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        simp [hrk]
      rw [Finset.sum_congr rfl this]
      simp
  exact H.hasFiniteFPowerSeriesAt.hasFPowerSeriesAt

/-- Shift a power series statement from base point `x₀` to base point `0`, keeping the series.-/
lemma hasFPowerSeriesAt_shift {Q : X → Z} {x₀ : X} {p : FormalMultilinearSeries 𝕜 X Z}
    (hp : HasFPowerSeriesAt Q p x₀) : HasFPowerSeriesAt (fun z => Q (x₀ + z)) p 0 := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, { r_le := hr.r_le, r_pos := hr.r_pos,
              hasSum := fun {y} hy => by simpa using hr.hasSum hy }⟩

/-- If `Q` has power series `p` at `x₀` and `Q (x₀ + t • x) = ∑_{r ≤ k} t ^ r • B r x`, then the
`k`-th term of `p` has diagonal `B k`.-/
theorem coeff_eq_of_hasFPowerSeriesAt (Q : X → Z) (x₀ : X) (k : ℕ) (B : ℕ → X → Z)
    (hB : ∀ (t : 𝕜) (x : X), Q (x₀ + t • x) = ∑ r ∈ Finset.range (k + 1), t ^ r • B r x)
    (p : FormalMultilinearSeries 𝕜 X Z) (hp : HasFPowerSeriesAt Q p x₀) :
    ∀ x, p k (fun _ => x) = B k x := by
  intro y
  have hp0 : HasFPowerSeriesAt (fun z => Q (x₀ + z)) p 0 := hasFPowerSeriesAt_shift hp
  obtain ⟨u, huapp⟩ : ∃ u : 𝕜 →L[𝕜] X, ∀ t : 𝕜, u t = t • y :=
    ⟨(ContinuousLinearMap.id 𝕜 𝕜).smulRight y, fun _ => rfl⟩
  have hp0' : HasFPowerSeriesAt (fun z => Q (x₀ + z)) p (u 0) := by
    rw [huapp, zero_smul]; exact hp0
  have h1 : HasFPowerSeriesAt ((fun z => Q (x₀ + z)) ∘ u) (p.compContinuousLinearMap u) 0 :=
    hp0'.compContinuousLinearMap
  have h2 : ((fun z => Q (x₀ + z)) ∘ u) =
      fun t : 𝕜 => ∑ r ∈ Finset.range (k + 1), t ^ r • B r y := by
    funext t
    simp only [Function.comp_apply, huapp, hB]
  rw [h2] at h1
  have heq := h1.eq_formalMultilinearSeries (hasFPowerSeriesAt_polySeries k (fun r => B r y))
  have key : (p.compContinuousLinearMap u) k (fun _ => (1 : 𝕜))
      = polySeries 𝕜 k (fun r => B r y) k (fun _ => (1 : 𝕜)) := by rw [heq]
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply, polySeries_apply] at key
  simp only [Function.comp_def, huapp, one_smul, Finset.prod_const_one] at key
  simpa using key

/-- Version of `coeff_eq_of_hasFPowerSeriesAt` where the line expansion holds only after an
injective map `j : Z →L W`, with top coefficient `j ∘ Qtop`.-/
theorem coeff_eq_of_ambient (Q : X → Z) (x₀ : X) (k : ℕ) (B : ℕ → X → W) (j : Z →L[𝕜] W)
    (hj : Function.Injective j) (Qtop : X → Z)
    (hB : ∀ (t : 𝕜) (x : X), j (Q (x₀ + t • x)) = ∑ r ∈ Finset.range (k + 1), t ^ r • B r x)
    (htop : ∀ x, B k x = j (Qtop x))
    (p : FormalMultilinearSeries 𝕜 X Z) (hp : HasFPowerSeriesAt Q p x₀) :
    ∀ x, p k (fun _ => x) = Qtop x := by
  have hjp : HasFPowerSeriesAt (j ∘ Q) (j.compFormalMultilinearSeries p) x₀ := by
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, j.comp_hasFPowerSeriesOnBall hr⟩
  have h := coeff_eq_of_hasFPowerSeriesAt (j ∘ Q) x₀ k B
    (by intro t x; simpa using hB t x) (j.compFormalMultilinearSeries p) hjp
  intro x
  apply hj
  have h1 := h x
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply] at h1
  simpa [htop x] using h1

end Extraction

/-! ## Line expansion of a multilinear map on the diagonal -/

section LineExpansion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `r`-th coefficient of `t ↦ A (x₀ + t • h, …, x₀ + t • h)`: the sum over all `r`-element
sets `s` of slots of `A` evaluated with `h` in the slots of `s` and `x₀` elsewhere.-/
noncomputable def lineCoeff (A : ContinuousMultilinearMap 𝕜 (fun _ : ι => X) W) (x₀ : X)
    (r : ℕ) (h : X) : W :=
  ∑ s ∈ (Finset.univ : Finset (Finset ι)).filter (fun s => s.card = r),
    A (s.piecewise (fun _ => h) (fun _ => x₀))

/-- Expansion of `t ↦ A (x₀ + t • h, …, x₀ + t • h)` in powers of `t`.-/
theorem map_diag_add_smul (A : ContinuousMultilinearMap 𝕜 (fun _ : ι => X) W) (x₀ h : X)
    (t : 𝕜) :
    A (fun _ => x₀ + t • h) =
      ∑ r ∈ Finset.range (Fintype.card ι + 1), t ^ r • lineCoeff A x₀ r h := by
  have h1 : (fun _ : ι => x₀ + t • h) = (fun _ : ι => t • h) + (fun _ : ι => x₀) := by
    funext i; simp [add_comm]
  rw [h1, A.map_add_univ]
  have h2 : ∀ s : Finset ι, A (s.piecewise (fun _ => t • h) (fun _ => x₀)) =
      t ^ s.card • A (s.piecewise (fun _ => h) (fun _ => x₀)) := by
    intro s
    have := A.map_piecewise_smul (fun _ => t) (s.piecewise (fun _ => h) (fun _ => x₀)) s
    rw [Finset.prod_const] at this
    rw [← this]
    congr 1
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  simp_rw [h2]
  unfold lineCoeff
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset ι)))
    (t := Finset.range (Fintype.card ι + 1)) (g := Finset.card)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [(Finset.mem_filter.mp hs).2]
  · intro s _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ s))

/-- The top line coefficient is `A` on the diagonal, independently of the base point.-/
theorem lineCoeff_card (A : ContinuousMultilinearMap 𝕜 (fun _ : ι => X) W) (x₀ h : X) :
    lineCoeff A x₀ (Fintype.card ι) h = A (fun _ => h) := by
  unfold lineCoeff
  have : (Finset.univ : Finset (Finset ι)).filter (fun s => s.card = Fintype.card ι) =
      {Finset.univ} := by
    ext s
    simp [Finset.card_eq_iff_eq_univ]
  rw [this, Finset.sum_singleton, Finset.piecewise_univ]

end LineExpansion

/-! ## Bounded lifts and analyticity -/

section T1

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 ι E E' F) in
/-- The precomposition map `Q f m = m ∘ (f, …, f)` (Mathlib's `compContinuousLinearMapCLM`).-/
noncomputable abbrev Q : (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  compContinuousLinearMapCLM

variable (𝕜 ι E E' F) in
/-- Post-composition with the isometric inclusion `ι_* : Alt(E,F) → Mult(E,F)`.-/
noncomputable def jAmb : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) →L[𝕜]
    ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :=
  ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) (E [⋀^ι]→L[𝕜] F)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (toContinuousMultilinearMapCLM 𝕜)

lemma jAmb_apply_apply (T : (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) (m : E' [⋀^ι]→L[𝕜] F) :
    jAmb 𝕜 ι E E' F T m = (T m).toContinuousMultilinearMap := rfl

lemma jAmb_injective : Function.Injective (jAmb 𝕜 ι E E' F) := by
  intro T₁ T₂ h
  refine ContinuousLinearMap.ext fun m => toContinuousMultilinearMap_injective ?_
  have := congrArg (fun T => T m) h
  simpa only [jAmb_apply_apply] using this

variable (𝕜 ι E E' F) in
/-- The multilinear lift `(f₁, …, f_k) ↦ (m ↦ m ∘ (f₁, …, f_k))`, valued in
`L(Alt(E',F), Mult(E,F))`.-/
noncomputable def ambLift : ContinuousMultilinearMap 𝕜 (fun _ : ι => E →L[𝕜] E')
    ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :=
  ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F) (ContinuousMultilinearMap 𝕜 (fun _ : ι => E') F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)).flip
      (toContinuousMultilinearMapCLM 𝕜)).compContinuousMultilinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
      (fun _ : ι => E) (fun _ => E') F)

lemma ambLift_diag (f : E →L[𝕜] E') :
    ambLift 𝕜 ι E E' F (fun _ => f) = jAmb 𝕜 ι E E' F (Q 𝕜 ι E E' F f) := by
  ext m x
  rfl

variable (𝕜 ι E E' F) in
/-- `Q` admits a bounded `card ι`-linear lift.-/
def HasBoundedLift : Prop :=
  ∃ P : ContinuousMultilinearMap 𝕜 (fun _ : Fin (Fintype.card ι) => E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)),
    ∀ f, P (fun _ => f) = Q 𝕜 ι E E' F f

/-- A bounded lift of any arity makes `Q` a continuous polynomial at every point.-/
theorem cpolynomialAt_of_lift {n : ℕ} (P : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))
    (hP : ∀ f, P (fun _ => f) = Q 𝕜 ι E E' F f) (f₀ : E →L[𝕜] E') :
    CPolynomialAt 𝕜 (Q 𝕜 ι E E' F) f₀ := by
  have hQ : Q 𝕜 ι E E' F = P ∘ (fun f => fun _ : Fin n => f) := funext fun f => (hP f).symm
  rw [hQ]
  exact CPolynomialAt.comp (g := ⇑P) (f := fun f : E →L[𝕜] E' => fun _ : Fin n => f)
    (ContinuousMultilinearMap.cpolynomialAt _)
    (ContinuousLinearMap.cpolynomialAt
      (ContinuousLinearMap.pi fun _ : Fin n => ContinuousLinearMap.id 𝕜 (E →L[𝕜] E')) f₀)

/-- The lift may equally be indexed by `ι` itself.-/
theorem hasBoundedLift_iff_exists_ι :
    HasBoundedLift 𝕜 ι E E' F ↔
      ∃ P : ContinuousMultilinearMap 𝕜 (fun _ : ι => E →L[𝕜] E')
          ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)),
        ∀ f, P (fun _ => f) = Q 𝕜 ι E E' F f := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.domDomCongr (Fintype.equivFin ι).symm, fun f => hP f⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.domDomCongr (Fintype.equivFin ι), fun f => hP f⟩

end T1

/-! ## Lowering the degree by one -/

section T2

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

variable (𝕜 E' F n) in
/-- `S m ((y₀,t₀),…,(yₙ,tₙ)) = ∑ᵢ (-1)^i • tᵢ • m(y₀,…,ŷᵢ,…,yₙ)`, the wedge with the last
coordinate, built from Mathlib's `alternatizeUncurryFin`. It involves no division.-/
noncomputable def Smap : (E' [⋀^Fin n]→L[𝕜] F) →L[𝕜] ((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) :=
  (alternatizeUncurryFinCLM 𝕜 (E' × 𝕜) F).comp
    ((ContinuousLinearMap.smulRightL 𝕜 (E' × 𝕜) ((E' × 𝕜) [⋀^Fin n]→L[𝕜] F)
        (ContinuousLinearMap.snd 𝕜 E' 𝕜)).comp
      (compContinuousLinearMapCLM (ContinuousLinearMap.fst 𝕜 E' 𝕜)))

lemma Smap_apply (m : E' [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 1) → E' × 𝕜) :
    Smap 𝕜 E' F n m v =
      ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • ((v i).2 • m (fun j => (i.removeNth v j).1)) := by
  simp [Smap, alternatizeUncurryFin_apply]
  rfl

variable (𝕜 E F n) in
/-- `R M (x₁,…,xₙ) = M((0,1),(x₁,0),…,(xₙ,0))`.-/
noncomputable def Rmap : ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F) :=
  (compContinuousLinearMapCLM (ContinuousLinearMap.inl 𝕜 E 𝕜)).comp
    ((ContinuousLinearMap.apply 𝕜 ((E × 𝕜) [⋀^Fin n]→L[𝕜] F) ((0 : E), (1 : 𝕜))).comp
      (curryLeftLI (𝕜 := 𝕜) (E := E × 𝕜) (F := F) (n := n)).toContinuousLinearMap)

lemma Rmap_apply (M : (E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) (x : Fin n → E) :
    Rmap 𝕜 E F n M x = M (Matrix.vecCons ((0 : E), (1 : 𝕜)) (fun j => (x j, (0 : 𝕜)))) := rfl

/-- `R ∘ S = id`.-/
theorem Rmap_Smap (m : E' [⋀^Fin n]→L[𝕜] F) : Rmap 𝕜 E' F n (Smap 𝕜 E' F n m) = m := by
  ext x
  rw [Rmap_apply, Smap_apply, Fin.sum_univ_succ]
  simp

variable (𝕜 E E' F n) in
/-- `Γ T = R ∘ T ∘ S`.-/
noncomputable def Γ : (((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)) →L[𝕜]
    ((E' [⋀^Fin n]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :=
  (ContinuousLinearMap.compL 𝕜 (E' [⋀^Fin n]→L[𝕜] F) ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)
      (E [⋀^Fin n]→L[𝕜] F) (Rmap 𝕜 E F n)).comp
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^Fin n]→L[𝕜] F) ((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)
      ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F)).flip (Smap 𝕜 E' F n))

lemma Γ_apply (T : ((E' × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] ((E × 𝕜) [⋀^Fin (n + 1)]→L[𝕜] F))
    (m : E' [⋀^Fin n]→L[𝕜] F) : Γ 𝕜 E E' F n T m = Rmap 𝕜 E F n (T (Smap 𝕜 E' F n m)) := rfl

variable (𝕜 E E') in
/-- `φ f = f ⊕ 0 : E × 𝕜 → E' × 𝕜`, linear in `f`.-/
noncomputable def φ : (E →L[𝕜] E') →L[𝕜] (E × 𝕜 →L[𝕜] E' × 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 (E × 𝕜) E' (E' × 𝕜) (ContinuousLinearMap.inl 𝕜 E' 𝕜)).comp
    ((ContinuousLinearMap.compL 𝕜 (E × 𝕜) E E').flip (ContinuousLinearMap.fst 𝕜 E 𝕜))

lemma φ_apply (f : E →L[𝕜] E') (x : E × 𝕜) : φ 𝕜 E E' f x = (f x.1, 0) := rfl

variable (𝕜 E E') in
/-- `j = 0 ⊕ id_𝕜`.-/
noncomputable def jj : E × 𝕜 →L[𝕜] E' × 𝕜 :=
  (ContinuousLinearMap.inr 𝕜 E' 𝕜).comp (ContinuousLinearMap.snd 𝕜 E 𝕜)

lemma jj_apply (x : E × 𝕜) : jj 𝕜 E E' x = (0, x.2) := rfl

/-- `R ∘ Q_{n+1}(f ⊕ id) ∘ S = Q_n(f)`.-/
theorem Γ_Q_succ (f : E →L[𝕜] E') :
    Γ 𝕜 E E' F n (Q 𝕜 (Fin (n + 1)) (E × 𝕜) (E' × 𝕜) F (φ 𝕜 E E' f + jj 𝕜 E E')) =
      Q 𝕜 (Fin n) E E' F f := by
  ext m x
  rw [Γ_apply, Rmap_apply]
  simp only [Q, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply]
  rw [Smap_apply, Fin.sum_univ_succ]
  simp [φ_apply, jj_apply]
  congr 1
  funext j
  simp [Fin.tail, φ_apply, jj_apply]

end T2

/-! ## Transfer along conjugation -/

section Conjugation

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι ι₁ : Type*} [Fintype ι] [Fintype ι₁]
  {E E' F E₁ E₁' F₁ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₁'] [NormedSpace 𝕜 E₁'] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]

end Conjugation

/-! ## Adding a line in the same degree

Adding a line to both sources in the same degree cannot create a lift: apply
`hasBoundedLift_of_eq_comp` with `A = φ` and `Ψ T = inl^* ∘ T ∘ fst^*`. -/

section SameDegree

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

end SameDegree

/-! ## All higher degrees -/

section Iterate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

end Iterate

/-! ## Reindexing -/

section Reindex

open ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι ι₁ : Type*} [Fintype ι] [Fintype ι₁]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Reindexing a continuous alternating map along `σ : ι ≃ ι₁`.-/
def reindexAlt (σ : ι ≃ ι₁) (m : E [⋀^ι]→L[𝕜] F) : E [⋀^ι₁]→L[𝕜] F where
  toContinuousMultilinearMap := m.toContinuousMultilinearMap.domDomCongr σ
  map_eq_zero_of_eq' v i j hv hij := by
    change m (fun k => v (σ k)) = 0
    exact m.map_eq_zero_of_eq (fun k => v (σ k)) (i := σ.symm i) (j := σ.symm j)
      (by simpa using hv) (by simpa using hij)

omit [Fintype ι] [Fintype ι₁] in
lemma reindexAlt_apply (σ : ι ≃ ι₁) (m : E [⋀^ι]→L[𝕜] F) (v : ι₁ → E) :
    reindexAlt σ m v = m (fun k => v (σ k)) := rfl

variable (𝕜 E F) in
/-- Reindexing as a continuous linear map (of norm `≤ 1`).-/
noncomputable def reindexCLM (σ : ι ≃ ι₁) : (E [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι₁]→L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := reindexAlt σ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun m => by
      rw [one_mul]
      change ‖(m.toContinuousMultilinearMap.domDomCongr σ)‖ ≤ ‖m.toContinuousMultilinearMap‖
      exact (ContinuousMultilinearMap.norm_domDomCongr 𝕜 E F σ _).le)

lemma reindexCLM_apply (σ : ι ≃ ι₁) (m : E [⋀^ι]→L[𝕜] F) (v : ι₁ → E) :
    reindexCLM 𝕜 E F σ m v = m (fun k => v (σ k)) := rfl

end Reindex

end LiftCriterion

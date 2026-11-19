import Tengoku.BezoutCounterexampleLean.BezoutCounterexample.RealPoints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Section 2: the topological obstruction

* The identities (2.1): `det M = -Δ` (`det_M`), `(1 + x, y, 1 - x) = A₀` (`span_entries_M`,
  via `(1 + x) + (1 - x) = 2`), `M² - 2M = Δ I₂` (`M_sq`).
* `Mreal a b`: the real matrix `M(a, b)`. For continuous `X, Y : K → ℝ` with `X² + Y² = 1`, the
  matrix `½ M(X z, Y z)` is an idempotent of rank one (`half_Mreal_idempotent`,
  `half_Mreal_rank`).
* `lineBundle X Y z`: the line `L_{X,Y}(z) ⊆ ℝ²`, the image of `½ M(X z, Y z)`
  (`finrank_lineBundle`). These fibres form a line subbundle of `K × ℝ²`: locally there are
  continuous nowhere-zero sections (`lineBundle_locally_trivial`).
* `IsOrientable X Y`: `L_{X,Y}` admits a continuous nowhere-zero section. The pullback of
  `L_{X,Y}` along `q : K' → K` is `L_{X ∘ q, Y ∘ q}` (`lineBundle_comp`, by definition).
* `K₀ = {z : z(Δ) = 0}`, the unit circle via `z ↦ (z x, z y)` (`K₀_homeomorph_circle`), and
  `L₀ = L_{x,y}`. The half-angle formula (2.2) is `Mreal_cos_sin`; `L₀_not_isOrientable`: `L₀` is
  the Möbius line bundle, which is nonorientable.
* **Lemma 2.1** (`lem:orientation-descent`): `orientation_descent`; equivalently,
  nonorientability pulls back along monotone surjections (`not_isOrientable_comp`).
* **Lemma 2.2** (`lem:monotone-composition`): `IsMonotoneSurjection.comp`, using
  `IsMonotoneSurjection.isConnected_preimage`.
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology Matrix

/-! ## The identities (2.1) -/

/-- (2.1): `det M = -Δ`.
@isnad1 id=eq.0h0v.s6.243d5f5160b7 from=translated src=- shape=b433547d vocab=05580af8
-/
theorem det_M : M.det = -Δ := by
  simp [M, Δ, Matrix.det_fin_two]
  ring

/-- `(1 + x) + (1 - x) = 2`, a unit of `ℚ`.
@isnad1 id=eq.0h0v.s8.8e3f80a329dc from=translated src=- shape=b335ca02 vocab=b2f9e957
-/
theorem one_add_x_add_one_sub_x : (1 + x) + (1 - x) = (MvPolynomial.C (2 : ℚ) : A₀) := by
  rw [map_ofNat]; ring

/-- (2.1): `(1 + x, y, 1 - x) = A₀`.
@isnad1 id=eq.0h0v.s8.1eca563aa641 from=translated src=- shape=c6f25376 vocab=44a53cc5
-/
theorem span_entries_M : (Ideal.span {1 + x, y, 1 - x} : Ideal A₀) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2 : MvPolynomial.C (1 / 2 : ℚ) * (1 + x) + MvPolynomial.C (1 / 2 : ℚ) * (1 - x) =
      (1 : A₀) := by
    rw [← mul_add, one_add_x_add_one_sub_x, ← map_mul]
    norm_num
  have hmem : MvPolynomial.C (1 / 2 : ℚ) * (1 + x) + MvPolynomial.C (1 / 2 : ℚ) * (1 - x) ∈
      (Ideal.span {1 + x, y, 1 - x} : Ideal A₀) :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  rwa [h2] at hmem

/-- (2.1): `M² - 2M = Δ I₂`.
@isnad1 id=eq.0h0v.s9.193428f91375 from=translated src=- shape=f9e5e491 vocab=6564741c
-/
theorem M_sq : M * M - (2 : A₀) • M = Δ • (1 : Matrix (Fin 2) (Fin 2) A₀) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [M, Δ] <;> ring

/-! ## The real matrices `M(a, b)` -/

/-- The real matrix `M(a, b) = [[1 + a, b], [b, 1 - a]]`, obtained from `M` by substituting `a`
and `b` for `x` and `y`.-/
def Mreal (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + a, b; b, 1 - a]

/-- Evaluating (the image of) `M` at a real point gives `M(z x, z y)`.
@isnad1 id=eq.0h3v.s8.64de08bebc67 from=translated src=- shape=597070b7 vocab=6e2f0858
-/
theorem M_map (A : Type*) [CommRing A] (ι : A₀ →+* A) (z : A →+* ℝ) :
    (M.map ι).map z = Mreal (z (ι x)) (z (ι y)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Mreal]

/--
@isnad1 id=eq.0h3v.s7.04306d4412f0 from=translated src=- shape=c78e4d9c vocab=6fd773e2
-/
lemma Mreal_mulVec (a b : ℝ) (w : Fin 2 → ℝ) :
    (Mreal a b).mulVec w = ![(1 + a) * w 0 + b * w 1, b * w 0 + (1 - a) * w 1] := by
  ext i
  fin_cases i <;> simp [Mreal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s6.d800ed96a7aa from=translated src=- shape=694fcf9c vocab=1ac076ff
-/
theorem Mreal_det (a b : ℝ) : (Mreal a b).det = 1 - a ^ 2 - b ^ 2 := by
  simp [Mreal, Matrix.det_fin_two]; ring

/--
@isnad1 id=eq.0h2v.s5.ef79a9a4d830 from=translated src=- shape=07e2c022 vocab=7f2ad339
-/
theorem Mreal_trace (a b : ℝ) : (Mreal a b).trace = 2 := by
  simp [Mreal, Matrix.trace_fin_two]; ring

/-- On the circle, `½ M(a, b)` is an idempotent (by (2.1)).
@isnad1 id=isidempo.1h2v.s7.bac03cccde4b from=translated src=- shape=f28ecbc9 vocab=54e7f473
-/
theorem half_Mreal_idempotent {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    IsIdempotentElem ((1 / 2 : ℝ) • Mreal a b) := by
  unfold IsIdempotentElem
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mreal, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hab]

/--
@isnad1 id=lt.1h1v.s6.19f0ed34a418 from=translated src=- shape=388c2e78 vocab=7044eccd
-/
lemma rank_pos_of_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A ≠ 0) : 0 < A.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h0
  simpa [Matrix.mulVec_single] using this

/-- On the circle, `½ M(a, b)` has rank one.
@isnad1 id=eq.1h2v.s7.c52bf6c21e3a from=translated src=- shape=a904749d vocab=35b35529
-/
theorem half_Mreal_rank {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ((1 / 2 : ℝ) • Mreal a b).rank = 1 := by
  set P := (1 / 2 : ℝ) • Mreal a b with hPdef
  have hP : P * P = P := half_Mreal_idempotent hab
  have h1 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero h1
  have htr : P.trace = 1 := by
    rw [hPdef, Matrix.trace_smul, Mreal_trace, smul_eq_mul]; norm_num
  have hP0 : P ≠ 0 := by
    intro h; rw [h, Matrix.trace_zero] at htr; exact zero_ne_one htr
  have hQ0 : (1 - P) ≠ 0 := by
    intro h
    have := congrArg Matrix.trace h
    rw [Matrix.trace_sub, htr, Matrix.trace_one, Matrix.trace_zero] at this
    norm_num at this
  have r1 := rank_pos_of_ne_zero hP0
  have r2 := rank_pos_of_ne_zero hQ0
  simp only [Fintype.card_fin] at hsum
  omega

/-! ## The line bundle `L_{X,Y}` -/

section LineBundle

variable {K : Type*} [TopologicalSpace K]

/-- The fibre `L_{X,Y}(z) ⊆ ℝ²`: the image of `½ M(X z, Y z)`.-/
def lineBundle (X Y : K → ℝ) (z : K) : Submodule ℝ (Fin 2 → ℝ) :=
  LinearMap.range (Matrix.mulVecLin ((1 / 2 : ℝ) • Mreal (X z) (Y z)))

omit [TopologicalSpace K] in
/--
@isnad1 id=iff.0h5v.s8.041196ca9838 from=translated src=- shape=7619e830 vocab=32f0576e
-/
lemma mem_lineBundle_iff {X Y : K → ℝ} {z : K} {w : Fin 2 → ℝ} :
    w ∈ lineBundle X Y z ↔ w ∈ Set.range (Mreal (X z) (Y z)).mulVec := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(1 / 2 : ℝ) • u, by simp [Matrix.mulVec_smul]⟩
  · rintro ⟨u, rfl⟩
    refine ⟨(2 : ℝ) • u, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul]
    norm_num

omit [TopologicalSpace K] in
/-- For `X² + Y² = 1`, every fibre `L_{X,Y}(z)` is a line.
@isnad1 id=eq.1h4v.s8.0ca63e83664d from=translated src=- shape=076580b7 vocab=ba004711
-/
theorem finrank_lineBundle {X Y : K → ℝ} (hXY : ∀ z, X z ^ 2 + Y z ^ 2 = 1) (z : K) :
    Module.finrank ℝ (lineBundle X Y z) = 1 :=
  half_Mreal_rank (hXY z)

omit [TopologicalSpace K] in
/-- The pullback of `L_{X,Y}` along `q : K' → K` is `L_{X ∘ q, Y ∘ q}`.
@isnad1 id=eq.0h6v.s6.96dd03ea0c01 from=translated src=- shape=cf56222a vocab=324dddde
-/
theorem lineBundle_comp {K' : Type*} (X Y : K → ℝ) (q : K' → K) (z : K') :
    lineBundle (X ∘ q) (Y ∘ q) z = lineBundle X Y (q z) := rfl

/-- `L_{X,Y}` is *orientable* if it admits a continuous nowhere-zero section, that is, a
continuous map `v : K → ℝ²` with `0 ≠ v z ∈ L_{X,Y}(z)` for every `z`.-/
def IsOrientable (X Y : K → ℝ) : Prop :=
  ∃ v : K → Fin 2 → ℝ, Continuous v ∧ ∀ z, v z ≠ 0 ∧ v z ∈ lineBundle X Y z

/-- **The fibres form a line subbundle**: for continuous `X, Y` with `X² + Y² = 1`, every point
has a neighbourhood on which `L_{X,Y}` has a continuous nowhere-zero section (one of the two
columns of `M(X, Y)`; they cannot both vanish since `(1 + X) + (1 - X) = 2`).
@isnad1 id=ex.2h4v.s8.3e2cbd803391 from=translated src=- shape=a0c10faa vocab=df54575d
-/
theorem lineBundle_locally_trivial {X Y : K → ℝ} (hX : Continuous X) (hY : Continuous Y)
    (z₀ : K) : ∃ U ∈ 𝓝 z₀, ∃ v : K → Fin 2 → ℝ, Continuous v ∧
      ∀ z ∈ U, v z ≠ 0 ∧ v z ∈ lineBundle X Y z := by
  have hcol : ∀ (j : Fin 2) (z : K), (fun i => Mreal (X z) (Y z) i j) ∈ lineBundle X Y z :=
    fun j z => mem_lineBundle_iff.2 ⟨Pi.single j 1, by
      ext i; simp [Matrix.mulVec_single]⟩
  by_cases h : 1 + X z₀ ≠ 0
  · refine ⟨{z | 1 + X z ≠ 0}, (isOpen_ne_fun (continuous_const.add hX)
      continuous_const).mem_nhds h, fun z i => Mreal (X z) (Y z) i 0, ?_, fun z hz => ⟨?_, hcol 0 z⟩⟩
    · refine continuous_pi fun i => ?_
      fin_cases i <;> simp [Mreal] <;> fun_prop
    · intro h0
      have := congrFun h0 0
      simp [Mreal] at this
      exact hz this
  · have h1 : 1 - X z₀ ≠ 0 := by
      have hx : 1 + X z₀ = 0 := not_ne_iff.1 h
      intro h'; linarith
    refine ⟨{z | 1 - X z ≠ 0}, (isOpen_ne_fun (continuous_const.sub hX)
      continuous_const).mem_nhds h1, fun z i => Mreal (X z) (Y z) i 1, ?_,
      fun z hz => ⟨?_, hcol 1 z⟩⟩
    · refine continuous_pi fun i => ?_
      fin_cases i <;> simp [Mreal] <;> fun_prop
    · intro h0
      have := congrFun h0 1
      simp [Mreal] at this
      exact hz this

end LineBundle

/-! ## Linear algebra of `M(a, b)` on the circle -/

/-- Two vectors in the image of `M(a,b)`, where `a² + b² = 1`, are parallel.
@isnad1 id=eq.3h4v.s8.9e531791acd2 from=translated src=- shape=549675a8 vocab=b1933cde
-/
lemma cross_eq_zero_of_mem_range {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {p q : Fin 2 → ℝ}
    (hp : p ∈ range (Mreal a b).mulVec) (hq : q ∈ range (Mreal a b).mulVec) :
    p 0 * q 1 - p 1 * q 0 = 0 := by
  obtain ⟨w, rfl⟩ := hp
  obtain ⟨w', rfl⟩ := hq
  simp only [Mreal_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(w 0 * w' 1 - w 1 * w' 0)) * hab

/-- If `p ≠ 0` and `p, q` are parallel, then `q` is a scalar multiple of `p`.
@isnad1 id=ex.2h2v.s7.bcfa9de30d4c from=translated src=- shape=bfc28232 vocab=fe66b49a
-/
lemma exists_smul_of_cross_eq_zero {p q : Fin 2 → ℝ} (hp : p ≠ 0)
    (h : p 0 * q 1 - p 1 * q 0 = 0) : ∃ t : ℝ, q = t • p := by
  by_cases h0 : p 0 = 0
  · have h1 : p 1 ≠ 0 := by
      intro h1
      apply hp
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨q 1 / p 1, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, h0, mul_zero]
      have : p 1 * q 0 = 0 := by rw [h0] at h; linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' h1
      · exact h'
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨q 0 / p 0, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith

/-- A line `L_{X,Y}(z)` contains exactly two unit vectors: two unit vectors (for any norm) in the
image of `M(a,b)`, `a² + b² = 1`, agree up to sign.-/
lemma eq_or_eq_neg_of_mem_range {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {p q : Fin 2 → ℝ}
    (hp : p ∈ range (Mreal a b).mulVec) (hq : q ∈ range (Mreal a b).mulVec)
    (hp1 : ‖p‖ = 1) (hq1 : ‖q‖ = 1) : q = p ∨ q = -p := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp1
  obtain ⟨t, rfl⟩ := exists_smul_of_cross_eq_zero hp0 (cross_eq_zero_of_mem_range hab hp hq)
  rw [norm_smul, hp1, mul_one, Real.norm_eq_abs] at hq1
  rcases abs_eq (zero_le_one' ℝ) |>.1 hq1 with rfl | rfl
  · left; simp
  · right; simp

/--
@isnad1 id=mem.1h3v.s7.5c37974727c1 from=translated src=- shape=2c657888 vocab=eab74e1c
-/
lemma smul_mem_range {A : Matrix (Fin 2) (Fin 2) ℝ} {p : Fin 2 → ℝ} (hp : p ∈ range A.mulVec)
    (c : ℝ) : c • p ∈ range A.mulVec := by
  obtain ⟨w, rfl⟩ := hp
  exact ⟨c • w, Matrix.mulVec_smul A c w⟩

/-! ## Lemma 2.1: orientation descent -/

/-- **Lemma 2.1** (`lem:orientation-descent`). Let `q : K' → K` be a monotone surjection from a
compact space to a Hausdorff space, and let `X, Y : K → ℝ` be continuous with `X² + Y² = 1`. If
`L_{X ∘ q, Y ∘ q}` is orientable, then `L_{X,Y}` is orientable.

Proof: normalize a section `v` to `u = v / ‖v‖`; `u` takes values in the two unit vectors of the
line on each connected fibre, so it is constant there, `u = ū ∘ q`; `q` is closed, hence a
quotient map, so `ū` is continuous.
@isnad1 id=isorient.5h5v.s7.ea689645192d from=translated src=- shape=a8590218 vocab=8e02f3f1
-/
theorem orientation_descent {K' K : Type*} [TopologicalSpace K'] [TopologicalSpace K]
    [CompactSpace K'] [T2Space K] {q : K' → K} (hq : IsMonotoneSurjection q)
    (X Y : K → ℝ) (_hX : Continuous X) (_hY : Continuous Y) (hXY : ∀ z, X z ^ 2 + Y z ^ 2 = 1)
    (h : IsOrientable (X ∘ q) (Y ∘ q)) : IsOrientable X Y := by
  obtain ⟨v, hvc, hv⟩ := h
  -- normalize the section: `u = v / ‖v‖`
  set u : K' → Fin 2 → ℝ := fun z => ‖v z‖⁻¹ • v z with hu_def
  have hnorm : ∀ z, ‖v z‖ ≠ 0 := fun z => norm_ne_zero_iff.2 (hv z).1
  have huc : Continuous u :=
    ((hvc.norm).inv₀ hnorm).smul hvc
  have hu1 : ∀ z, ‖u z‖ = 1 := fun z => by
    simp only [hu_def, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hnorm z)
  have hurange : ∀ z, u z ∈ range (Mreal (X (q z)) (Y (q z))).mulVec := fun z =>
    smul_mem_range (mem_lineBundle_iff.1 (hv z).2) _
  -- the line `L_{X,Y}(z)` contains exactly two unit vectors, so `u` is constant on the
  -- connected fibres of `q`
  have hconst : ∀ z₁ z₂, q z₁ = q z₂ → u z₁ = u z₂ := by
    intro z₁ z₂ h12
    have hF : IsPreconnected (q ⁻¹' {q z₁}) := (hq.isConnected_fiber (q z₁)).isPreconnected
    have hT : IsDiscrete ({u z₁, -u z₁} : Set (Fin 2 → ℝ)) :=
      (Set.toFinite _).isDiscrete
    refine hF.constant_of_mapsTo hT huc.continuousOn ?_ (mem_preimage.2 rfl)
      (mem_preimage.2 h12.symm)
    intro z hz
    have hz' : q z = q z₁ := hz
    have h1 := hurange z
    have h2 := hurange z₁
    rw [hz'] at h1
    rcases eq_or_eq_neg_of_mem_range (hXY (q z₁)) h2 h1 (hu1 z₁) (hu1 z) with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  -- hence `u = ū ∘ q`; `q` is closed, hence a quotient map, so `ū` is continuous
  have hqs := hq.surjective
  let σ : K → K' := Function.surjInv hqs
  have hσ : ∀ z, q (σ z) = z := Function.surjInv_eq hqs
  have hquot : IsQuotientMap q :=
    IsClosedMap.isQuotientMap (hq.continuous.isClosedMap) hq.continuous hqs
  refine ⟨fun z => u (σ z), ?_, fun z => ⟨?_, ?_⟩⟩
  · rw [hquot.continuous_iff]
    convert huc using 1
    funext z
    exact hconst _ _ (hσ (q z))
  · intro h0
    have h0' : u (σ z) = 0 := h0
    have := hu1 (σ z)
    rw [h0', norm_zero] at this
    exact zero_ne_one this
  · have := hurange (σ z)
    rw [hσ z] at this
    exact mem_lineBundle_iff.2 this

/-- Lemma 2.1, equivalently: nonorientability pulls back along monotone surjections from compact
spaces to Hausdorff spaces.
@isnad1 id=not.5h5v.s7.86f3915e625b from=translated src=- shape=e03d6fe2 vocab=8e02f3f1
-/
theorem not_isOrientable_comp {K' K : Type*} [TopologicalSpace K'] [TopologicalSpace K]
    [CompactSpace K'] [T2Space K] {q : K' → K} (hq : IsMonotoneSurjection q)
    (X Y : K → ℝ) (hX : Continuous X) (hY : Continuous Y) (hXY : ∀ z, X z ^ 2 + Y z ^ 2 = 1)
    (h : ¬ IsOrientable X Y) : ¬ IsOrientable (X ∘ q) (Y ∘ q) :=
  fun h' => h (orientation_descent hq X Y hX hY hXY h')

/-! ## Lemma 2.2: composites of monotone surjections -/

/-- If `q : K' → K` is a monotone surjection from a compact space to a Hausdorff space and
`C ⊆ K` is closed and connected, then `q⁻¹(C)` is connected.

Proof: otherwise `q⁻¹(C) = F ∐ G` with `F, G` nonempty and closed; each (connected) fibre meets
at most one of `F` and `G`, so the compact sets `q(F)` and `q(G)` are disjoint nonempty closed
sets with union `C`.
@isnad1 id=isconnec.3h4v.s5.eff40cd35a57 from=translated src=- shape=6f14af29 vocab=0d79093e
-/
theorem IsMonotoneSurjection.isConnected_preimage_of_isClosed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {q : X → Y} (hq : IsMonotoneSurjection q)
    {C : Set Y} (hC : IsClosed C) (hCc : IsConnected C) : IsConnected (q ⁻¹' C) := by
  have hCl : IsClosed (q ⁻¹' C) := hC.preimage hq.continuous
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := hCc.nonempty
    obtain ⟨z, rfl⟩ := hq.surjective c
    exact ⟨z, hc⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hCl]
  intro F G hF hG hsub hdisj
  -- each fibre over `C` lies in `F` or in `G`
  have hfib : ∀ c ∈ C, q ⁻¹' {c} ⊆ F ∨ q ⁻¹' {c} ⊆ G := by
    intro c hc
    have hsub' : q ⁻¹' {c} ⊆ F ∪ G := fun z hz =>
      hsub (show q z ∈ C by rw [show q z = c from hz]; exact hc)
    exact (isPreconnected_iff_subset_of_fully_disjoint_closed
      (isClosed_singleton.preimage hq.continuous)).1 (hq.isConnected_fiber c).isPreconnected
      F G hF hG hsub' hdisj
  -- the images `q(F ∩ q⁻¹ C)` and `q(G ∩ q⁻¹ C)` are closed, disjoint and cover `C`
  set F' := q '' (F ∩ q ⁻¹' C)
  set G' := q '' (G ∩ q ⁻¹' C)
  have hF' : IsClosed F' :=
    ((hF.inter hCl).isCompact.image hq.continuous).isClosed
  have hG' : IsClosed G' :=
    ((hG.inter hCl).isCompact.image hq.continuous).isClosed
  have hcov : C ⊆ F' ∪ G' := by
    intro c hc
    obtain ⟨z, rfl⟩ := hq.surjective c
    rcases hsub (show z ∈ q ⁻¹' C from hc) with h | h
    · exact Or.inl ⟨z, ⟨h, hc⟩, rfl⟩
    · exact Or.inr ⟨z, ⟨h, hc⟩, rfl⟩
  have hdisj' : Disjoint F' G' := by
    rw [Set.disjoint_left]
    rintro c ⟨z, ⟨hzF, hzC⟩, rfl⟩ ⟨w, ⟨hwG, -⟩, hw⟩
    rcases hfib (q z) hzC with h | h
    · exact Set.disjoint_left.1 hdisj (h (show q w = q z from hw)) hwG
    · exact Set.disjoint_left.1 hdisj hzF (h rfl)
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hC).1 hCc.isPreconnected
      F' G' hF' hG' hcov hdisj' with h | h
  · left
    intro z hz
    obtain ⟨w, ⟨hwF, -⟩, hw⟩ := h hz
    rcases hfib (q z) hz with h' | h'
    · exact h' rfl
    · exact absurd (h' (show q w = q z from hw)) (Set.disjoint_left.1 hdisj hwF)
  · right
    intro z hz
    obtain ⟨w, ⟨hwG, -⟩, hw⟩ := h hz
    rcases hfib (q z) hz with h' | h'
    · exact absurd hwG (Set.disjoint_left.1 hdisj (h' (show q w = q z from hw)))
    · exact h' rfl

/-- The observation in the proof of Lemma 2.2: if `q : K' → K` is a monotone surjection from a
compact space to a Hausdorff space and `C ⊆ K` is compact and connected, then `q⁻¹(C)` is
connected.
@isnad1 id=isconnec.3h4v.s5.8825f0390a56 from=translated src=- shape=6f14af29 vocab=8b53cb12
-/
theorem IsMonotoneSurjection.isConnected_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {q : X → Y} (hq : IsMonotoneSurjection q)
    {C : Set Y} (hC : IsCompact C) (hCc : IsConnected C) : IsConnected (q ⁻¹' C) :=
  hq.isConnected_preimage_of_isClosed hC.isClosed hCc

/-- **Lemma 2.2** (`lem:monotone-composition`). A composite of monotone surjections between
compact Hausdorff spaces is monotone. (Only the compactness of the source and the Hausdorff
property of the other two spaces are used: apply the observation above to the connected fibres of
`q₂`.)
@isnad1 id=ismonoto.2h5v.s5.157afea77b17 from=translated src=- shape=501a302a vocab=268a4a71
-/
theorem IsMonotoneSurjection.comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace X] [T2Space Y] [T2Space Z] {q₁ : X → Y} {q₂ : Y → Z}
    (h₂ : IsMonotoneSurjection q₂) (h₁ : IsMonotoneSurjection q₁) :
    IsMonotoneSurjection (q₂ ∘ q₁) where
  continuous := h₂.continuous.comp h₁.continuous
  surjective := h₂.surjective.comp h₁.surjective
  isConnected_fiber z := by
    rw [preimage_comp]
    exact h₁.isConnected_preimage_of_isClosed (isClosed_singleton.preimage h₂.continuous)
      (h₂.isConnected_fiber z)

/-- Lemma 2.2 for restrictions: if `f : K'' → K'` and `g : K' → K` are monotone surjections,
`K''` is compact and the ambient spaces of `K'` and `K` are Hausdorff, then `g ∘ f : K'' → K` is a
monotone surjection.
@isnad1 id=ismonoto.3h8v.s6.e23ca39d3423 from=translated src=- shape=05153ee4 vocab=7828ec0b
-/
theorem IsMonotoneSurjOn.trans {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space Y] [T2Space Z] {f : X → Y} {g : Y → Z}
    {K'' : Set X} {K' : Set Y} {K : Set Z} (hK'' : IsCompact K'')
    (hg : IsMonotoneSurjOn g K' K) (hf : IsMonotoneSurjOn f K'' K') :
    IsMonotoneSurjOn (g ∘ f) K'' K := by
  obtain ⟨mg, sg⟩ := hg
  obtain ⟨mf, sf⟩ := hf
  refine ⟨mg.comp mf, ?_⟩
  have := isCompact_iff_compactSpace.1 hK''
  have heq : (mg.comp mf).restrict (g ∘ f) K'' K = (mg.restrict g K' K) ∘ (mf.restrict f K'' K') := by
    funext z; rfl
  rw [heq]
  exact sg.comp sf

/-! ## The circle `K₀` and the Möbius line bundle `L₀` -/

/-- The circle `K₀ = {z ∈ Spec(A₀)(ℝ) : z(Δ) = 0}`.-/
def K₀ : Set (RealPt A₀) := {z | z Δ = 0}

/--
@isnad1 id=eq.0h1v.s7.f1fdebde886b from=translated src=- shape=1c0b7f96 vocab=fe1c6a7c
-/
lemma Δ_eval (z : RealPt A₀) : z Δ = z x ^ 2 + z y ^ 2 - 1 := by
  simp [Δ, map_sub, map_add, map_pow, map_one]

/--
@isnad1 id=eq.1h1v.s8.9e51785476d3 from=translated src=- shape=b685bd7a vocab=9d8846a8
-/
lemma K₀_circle {z : RealPt A₀} (hz : z ∈ K₀) : z x ^ 2 + z y ^ 2 = 1 := by
  have : z Δ = 0 := hz
  rw [Δ_eval] at this
  linarith

/-- Evaluation of `A₀ = ℚ[x, y]` at a point of `ℝ²`.-/
def evalPt (p : Fin 2 → ℝ) : RealPt A₀ :=
  RealPt.ofHom (MvPolynomial.aeval p : A₀ →ₐ[ℚ] ℝ).toRingHom

/--
@isnad1 id=eq.0h1v.s6.7e77057ed615 from=translated src=- shape=24d20296 vocab=7cf42fea
-/
@[simp] lemma evalPt_x (p : Fin 2 → ℝ) : evalPt p x = p 0 := by simp [evalPt, x]

/--
@isnad1 id=eq.0h1v.s6.124a8898e0fc from=translated src=- shape=24d20296 vocab=438e247f
-/
@[simp] lemma evalPt_y (p : Fin 2 → ℝ) : evalPt p y = p 1 := by simp [evalPt, y]

/--
@isnad1 id=continuo.0h0v.s6.5db6d837b25b from=translated src=- shape=e2b5be61 vocab=fe807245
-/
lemma continuous_evalPt : Continuous evalPt := by
  rw [RealPt.continuous_iff]
  intro q
  have : (fun p => evalPt p q) =
      fun p : Fin 2 → ℝ => MvPolynomial.eval p (MvPolynomial.map (algebraMap ℚ ℝ) q) := by
    funext p
    simp [evalPt, MvPolynomial.aeval_def, MvPolynomial.eval_map]
  rw [this]
  exact MvPolynomial.continuous_eval _

/-- Every real point of `A₀` is determined by the images of `x` and `y`.
@isnad1 id=eq.2h2v.s8.0c9a59b58fb7 from=translated src=- shape=96db82f2 vocab=84697e35
-/
lemma realPt_A₀_ext {z w : RealPt A₀} (hx : z x = w x) (hy : z y = w y) : z = w := by
  have : RealPt.toHom z = RealPt.toHom w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := eq_ratCast ((RealPt.toHom z).comp MvPolynomial.C) r
      have h2 := eq_ratCast ((RealPt.toHom w).comp MvPolynomial.C) r
      simp only [RingHom.comp_apply] at h1 h2
      rw [h1, h2]
    · intro i
      fin_cases i
      · exact hx
      · exact hy
  exact this

/--
@isnad1 id=eq.0h1v.s7.8867dfc71e00 from=translated src=- shape=bb8eea62 vocab=be3d334f
-/
lemma evalPt_eval (z : RealPt A₀) : evalPt ![z x, z y] = z :=
  realPt_A₀_ext (by simp) (by simp)

/-- The unit circle in `ℝ²`.-/
def unitCircle : Set (Fin 2 → ℝ) := {p | p 0 ^ 2 + p 1 ^ 2 = 1}

/-- `K₀` is the unit circle via `z ↦ (z x, z y)`.-/
def K₀HomeomorphCircle : K₀ ≃ₜ unitCircle where
  toFun z := ⟨![z.1 x, z.1 y], by simpa [unitCircle] using K₀_circle z.2⟩
  invFun p := ⟨evalPt p.1, by
    show evalPt p.1 Δ = 0
    rw [Δ_eval, evalPt_x, evalPt_y]
    have := p.2
    simp only [unitCircle, mem_ofPred_eq] at this
    linarith⟩
  left_inv z := Subtype.ext (evalPt_eval z.1)
  right_inv p := Subtype.ext (by ext i; fin_cases i <;> simp)
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    fin_cases i
    · exact (RealPt.continuous_eval x).comp continuous_subtype_val
    · exact (RealPt.continuous_eval y).comp continuous_subtype_val
  continuous_invFun := (continuous_evalPt.comp continuous_subtype_val).subtype_mk fun p => by
    show evalPt p.1 Δ = 0
    rw [Δ_eval, evalPt_x, evalPt_y]
    have := p.2
    simp only [unitCircle, mem_ofPred_eq] at this
    linarith

/--
@isnad1 id=eq.0h1v.s10.84a6cb233cc7 from=translated src=- shape=09c6ec9a vocab=b21ebcc6
-/
@[simp] lemma K₀HomeomorphCircle_apply (z : K₀) :
    (K₀HomeomorphCircle z : Fin 2 → ℝ) = ![z.1 x, z.1 y] := rfl

/-- The circle `K₀` is compact.
@isnad1 id=iscompac.0h0v.s5.f654c88f494b from=translated src=- shape=545db28e vocab=8ffb1c92
-/
theorem isCompact_K₀ : IsCompact K₀ := by
  have hS : IsCompact unitCircle := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun p hp => ?_⟩
      simp only [unitCircle, mem_ofPred_eq] at hp
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  have := isCompact_iff_compactSpace.1 hS
  rw [isCompact_iff_compactSpace]
  exact K₀HomeomorphCircle.symm.compactSpace

/-- The half-angle formula (2.2): for `(x,y) = (cos θ, sin θ)`,
`M = 2 (cos(θ/2), sin(θ/2))ᵀ (cos(θ/2), sin(θ/2))`.
@isnad1 id=eq.0h1v.s7.e54a188ecc46 from=translated src=- shape=e3fdecf0 vocab=880730d5
-/
lemma Mreal_cos_sin (θ : ℝ) :
    Mreal (Real.cos θ) (Real.sin θ) =
      (2 : ℝ) • Matrix.vecMulVec ![Real.cos (θ / 2), Real.sin (θ / 2)]
        ![Real.cos (θ / 2), Real.sin (θ / 2)] := by
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h1 := Real.sin_sq_add_cos_sq (θ / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mreal, hc, hs] <;> nlinarith [h1]

/--
@isnad1 id=eq.0h3v.s8.127fdc225c74 from=translated src=- shape=d92f6bf5 vocab=9c3100ad
-/
lemma mulVec_two_vecMulVec (c s : ℝ) (u : Fin 2 → ℝ) :
    ((2 : ℝ) • Matrix.vecMulVec ![c, s] ![c, s]).mulVec u =
      (2 * (c * u 0 + s * u 1)) • ![c, s] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The point `(cos θ, sin θ)` of the circle, as a real point of `A₀`.-/
def circlePt (θ : ℝ) : RealPt A₀ := evalPt ![Real.cos θ, Real.sin θ]

/--
@isnad1 id=eq.0h1v.s6.8cb79adc1930 from=translated src=- shape=7099d8a9 vocab=d540440c
-/
@[simp] lemma circlePt_x (θ : ℝ) : circlePt θ x = Real.cos θ := by
  simp [circlePt]

/--
@isnad1 id=eq.0h1v.s6.0f528bee00cd from=translated src=- shape=7099d8a9 vocab=88018921
-/
@[simp] lemma circlePt_y (θ : ℝ) : circlePt θ y = Real.sin θ := by
  simp [circlePt]

/--
@isnad1 id=mem.0h1v.s6.c6161527a7e0 from=translated src=- shape=44d305d3 vocab=d53f3bc9
-/
lemma circlePt_mem (θ : ℝ) : circlePt θ ∈ K₀ := by
  show circlePt θ Δ = 0
  rw [Δ_eval, circlePt_x, circlePt_y, Real.cos_sq_add_sin_sq]; ring

/--
@isnad1 id=continuo.0h0v.s5.b75123003b9f from=translated src=- shape=4b736592 vocab=9d5ad64b
-/
lemma continuous_circlePt : Continuous circlePt := by
  refine continuous_evalPt.comp (continuous_pi fun i => ?_)
  fin_cases i
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin

/--
@isnad1 id=eq.0h0v.s5.1de33937bede from=translated src=- shape=aba72ab4 vocab=b15c5de3
-/
lemma circlePt_two_pi : circlePt (2 * Real.pi) = circlePt 0 :=
  realPt_A₀_ext (by simp) (by simp)

/-- The functions `x, y` on `K₀`; `L₀ = L_{x,y}` is `lineBundle X₀ Y₀`.-/
def X₀ : K₀ → ℝ := fun z => z.1 x

/-- The function `y` on `K₀`.-/
def Y₀ : K₀ → ℝ := fun z => z.1 y

/-- **`L₀` is the Möbius line bundle, which is nonorientable**: a continuous nowhere-zero
section, pulled back to `[0, 2π]`, would have the form `f(θ) (cos(θ/2), sin(θ/2))` for a
continuous nowhere-zero function `f` with `f(2π) = -f(0)`, contradicting the intermediate value
theorem.
@isnad1 id=not.0h0v.s7.ce09ca74d3c6 from=translated src=- shape=9b7a4bfa vocab=46ae87d0
-/
theorem L₀_not_isOrientable : ¬ IsOrientable X₀ Y₀ := by
  rintro ⟨v, hvc, hv⟩
  let γ : ℝ → K₀ := fun θ => ⟨circlePt θ, circlePt_mem θ⟩
  have hγ : Continuous γ := continuous_circlePt.subtype_mk _
  let w : ℝ → Fin 2 → ℝ := fun θ => ![Real.cos (θ / 2), Real.sin (θ / 2)]
  let f : ℝ → ℝ := fun θ => v (γ θ) ⬝ᵥ w θ
  have hfc : Continuous f := by
    simp only [f, dotProduct, Fin.sum_univ_two]
    fun_prop
  -- by (2.2), the section is `f θ • w θ`
  have hvw : ∀ θ, v (γ θ) = f θ • w θ := by
    intro θ
    obtain ⟨u, hu⟩ := mem_lineBundle_iff.1 (hv (γ θ)).2
    have hM : Mreal (X₀ (γ θ)) (Y₀ (γ θ)) = Mreal (Real.cos θ) (Real.sin θ) := by
      simp [γ, X₀, Y₀]
    rw [hM, Mreal_cos_sin, mulVec_two_vecMulVec] at hu
    have h1 := Real.sin_sq_add_cos_sq (θ / 2)
    have hfθ : f θ = 2 * (Real.cos (θ / 2) * u 0 + Real.sin (θ / 2) * u 1) := by
      show v (γ θ) ⬝ᵥ w θ = _
      rw [← hu]
      simp only [w, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (2 * (Real.cos (θ / 2) * u 0 + Real.sin (θ / 2) * u 1)) * h1
    rw [hfθ, ← hu]
  have hf0 : ∀ θ, f θ ≠ 0 := by
    intro θ h
    apply (hv (γ θ)).1
    rw [hvw θ, h, zero_smul]
  -- equality at the endpoints forces `f(2π) = -f(0)`
  have hγ2 : γ (2 * Real.pi) = γ 0 := Subtype.ext circlePt_two_pi
  have hw2 : w (2 * Real.pi) = -w 0 := by
    ext i
    fin_cases i <;> simp [w]
  have hf2 : f (2 * Real.pi) = -f 0 := by
    simp only [f, hγ2, hw2, dotProduct_neg]
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rcases lt_or_gt_of_ne (hf0 0) with hneg | hpos
  · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc h2pi hfc.continuousOn
      (show (0 : ℝ) ∈ Icc (f 0) (f (2 * Real.pi)) by rw [hf2]; constructor <;> linarith)
    exact hf0 θ hθ
  · obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' h2pi hfc.continuousOn
      (show (0 : ℝ) ∈ Icc (f (2 * Real.pi)) (f 0) by rw [hf2]; constructor <;> linarith)
    exact hf0 θ hθ

/-- Nonorientability of `L_{a,b}` is preserved under pullback along a monotone surjection
`K' → K` of compact sets of real points (Lemma 2.1, in the form used for (5.2)).
@isnad1 id=not.4h7v.s8.ed5cde7f06f8 from=translated src=- shape=d3f34224 vocab=3be731c5
-/
theorem not_isOrientable_pullback {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (a b : A) {K : Set (RealPt A)} {K' : Set (RealPt B)} (hK' : IsCompact K')
    (hmono : IsMonotoneSurjOn (RealPt.comap f) K' K) (hcirc : ∀ z ∈ K, z a ^ 2 + z b ^ 2 = 1)
    (h : ¬ IsOrientable (fun z : K => z.1 a) (fun z : K => z.1 b)) :
    ¬ IsOrientable (fun z : K' => z.1 (f a)) (fun z : K' => z.1 (f b)) := by
  obtain ⟨hmaps, hq⟩ := hmono
  have := isCompact_iff_compactSpace.1 hK'
  exact not_isOrientable_comp hq (fun z : K => z.1 a) (fun z : K => z.1 b)
    ((RealPt.continuous_eval a).comp continuous_subtype_val)
    ((RealPt.continuous_eval b).comp continuous_subtype_val) (fun z => hcirc z.1 z.2) h

end BezoutCounterexample

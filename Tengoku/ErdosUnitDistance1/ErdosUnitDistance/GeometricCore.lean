/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Tengoku.ErdosUnitDistance1.ErdosUnitDistance.Counting

/-!
# The geometric core

Grid-pigeonhole packing and doubling bounds for additive subgroups of
`ι → ℂ` in polydisc boxes, and the translation argument producing many
unit distances after projection to one coordinate.  No measure theory.
-/

open scoped Classical

namespace Erdos

/-! ## Geometric core

Everything in this section is about an additive subgroup `Λ ≤ (ι → ℂ)`
(`ι` finite: in the application, the set of infinite places, with
`Fintype.card ι = 2^g`), a "radius vector" `r : ι → ℝ`, and the polydisc
boxes `box r c`.  All bounds are by grid pigeonhole: each coordinate disc
`{‖w‖ ≤ 2 * r i}` is partitioned into at most `(4 * 2/ε)²` half-open square
cells of diameter at most `ε * r i`, so the polydisc splits into at most
`(8/ε)^(2·#ι)` cells, on each of which all pairwise coordinate differences
have modulus at most `ε * r i`. -/

section GeometricCore

variable {ι : Type} [Fintype ι]

/-- The closed polydisc box of polyradius `c • r` in `ι → ℂ`. -/
def box (r : ι → ℝ) (c : ℝ) : Set (ι → ℂ) :=
  {x | ∀ i, ‖x i‖ ≤ c * r i}

omit [Fintype ι] in
theorem box_mono {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {c c' : ℝ} (h : c ≤ c') :
    box r c ⊆ box r c' :=
  fun x hx i => (hx i).trans (by have := hr i; nlinarith)

private lemma cell_index_mem {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {t : ℝ} (ht : |t| ≤ c * ri) :
    ⌊(t + c * ri) / (ε * ri / Real.sqrt 2)⌋ ∈
      Finset.Icc (0 : ℤ) ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℤ) := by
  refine' Finset.mem_Icc.mpr ⟨ Int.floor_nonneg.mpr _, Int.le_of_lt_add_one ( Int.floor_lt.mpr _ ) ⟩;
  · exact div_nonneg ( by linarith [ abs_le.mp ht ] ) ( by positivity );
  · rw [ div_lt_iff₀ ] <;> norm_num;
    · rw [ ← mul_div_assoc, lt_div_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( 2 * Real.sqrt 2 * c / ε ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_pos hε hri, mul_div_cancel₀ ( 2 * Real.sqrt 2 * c ) hε.ne', abs_le.mp ht ];
    · positivity

/-
Helper: two real coordinates with the same cell index differ by less than the
cell side `ε*ri/√2`.
-/
private lemma cell_index_diff {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {a b : ℝ}
    (h : ⌊(a + c * ri) / (ε * ri / Real.sqrt 2)⌋
        = ⌊(b + c * ri) / (ε * ri / Real.sqrt 2)⌋) :
    |a - b| < ε * ri / Real.sqrt 2 := by
  rw [ Int.floor_eq_iff ] at h;
  rw [ abs_lt ] ; constructor <;> nlinarith [ Int.floor_le ( ( b + c * ri ) / ( ε * ri / Real.sqrt 2 ) ), Int.lt_floor_add_one ( ( b + c * ri ) / ( ε * ri / Real.sqrt 2 ) ), show 0 < ε * ri / Real.sqrt 2 by positivity, mul_div_cancel₀ ( a + c * ri ) ( show ε * ri / Real.sqrt 2 ≠ 0 by positivity ), mul_div_cancel₀ ( b + c * ri ) ( show ε * ri / Real.sqrt 2 ≠ 0 by positivity ) ] ;

/-
Helper: a complex number whose real and imaginary parts are each `< d` in
absolute value has norm `< d * √2`.
-/
private lemma norm_lt_of_re_im_bound {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hre : |z.re| < d) (him : |z.im| < d) : ‖z‖ < d * Real.sqrt 2 := by
  rw [ ← Real.sqrt_sq ( show 0 ≤ d by assumption ) ];
  rw [ ← Real.sqrt_mul <| by positivity ] ; refine' Real.sqrt_lt_sqrt _ _;
  · exact Complex.normSq_nonneg _;
  · nlinarith [ abs_lt.mp hre, abs_lt.mp him, Complex.normSq_apply z ]

/-
Helper: the per-axis cell count `⌊2√2 c/ε⌋₊ + 1` is at most `4c/ε`
(using `ε ≤ c`, i.e. `c/ε ≥ 1`).
-/
private lemma cellCount_le {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℝ) + 1 ≤ 4 * c / ε := by
  by_contra h_contra;
  exact h_contra <| by have := Nat.floor_le ( show 0 ≤ 2 * Real.sqrt 2 * c / ε by exact div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two <| Real.sqrt_nonneg _ ) <| by linarith ) <| by linarith ) ; rw [ le_div_iff₀ <| by linarith ] at *; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ ( 2 * Real.sqrt 2 * c ) <| ne_of_gt hε ] ;

/-
[medium] **Grid pigeonhole.**  A subset of the polydisc `box r c` whose
distinct elements are `ε`-separated in some coordinate (relative to `r`)
is finite, of cardinality at most `(4 * c / ε) ^ (2 * #ι)`.
Sketch: partition each coordinate disc of radius `c * r i` into half-open
square cells of side `ε * r i / √2`; there are at most
`⌈2√2 * c/ε⌉² ≤ (4c/ε)²` cells per coordinate (using `ε ≤ c`).  Map each
point to its tuple of cell indices: two points with the same tuple differ
by at most `ε * r i` in every coordinate, contradicting separation; so the
map into `ι → (Fin M × Fin M)` is injective.
-/
/-- [medium] **Grid pigeonhole.**  A subset of the polydisc `box r c` whose
distinct elements are `ε`-separated in some coordinate (relative to `r`)
is finite, of cardinality at most `(4 * c / ε) ^ (2 * #ι)`.
Sketch: partition each coordinate disc of radius `c * r i` into half-open
square cells of side `ε * r i / √2`; there are at most
`⌈2√2 * c/ε⌉² ≤ (4c/ε)²` cells per coordinate (using `ε ≤ c`).  Map each
point to its tuple of cell indices: two points with the same tuple differ
by at most `ε * r i` in every coordinate, contradicting separation; so the
map into `ι → (Fin M × Fin M)` is injective. -/
theorem finite_and_card_le_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c)
    {S : Set (ι → ℂ)} (hS : S ⊆ box r c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * c / ε) ^ (2 * Fintype.card ι) := by
  -- Let's define the cell map and the finite codomain.
  set δ : ι → ℝ := fun i => ε * r i / Real.sqrt 2
  set K : ℤ := (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℤ)
  set T : Finset (ι → ℤ × ℤ) := Fintype.piFinset (fun _ : ι => (Finset.Icc (0:ℤ) K) ×ˢ (Finset.Icc (0:ℤ) K));
  -- Define the cell map `g` and show that it maps `S` into `T`.
  set g : (ι → ℂ) → (ι → ℤ × ℤ) := fun x i => (⌊((x i).re + c * r i) / δ i⌋, ⌊((x i).im + c * r i) / δ i⌋)
  have hg : ∀ x ∈ S, g x ∈ T := by
    intro x hx;
    simp +zetaDelta at *;
    intro i; exact ⟨ ⟨ cell_index_mem hε ( hr i ) ( show |( x i |> Complex.re )| ≤ c * r i from by simpa using Complex.abs_re_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.left, cell_index_mem hε ( hr i ) ( show |( x i |> Complex.re )| ≤ c * r i from by simpa using Complex.abs_re_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.right ⟩, ⟨ cell_index_mem hε ( hr i ) ( show |( x i |> Complex.im )| ≤ c * r i from by simpa using Complex.abs_im_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.left, cell_index_mem hε ( hr i ) ( show |( x i |> Complex.im )| ≤ c * r i from by simpa using Complex.abs_im_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.right ⟩ ⟩ ;
  -- Show that `g` is injective on `S`.
  have hg_inj : Set.InjOn g S := by
    intros x hx y hy hxy
    by_contra hxy_ne
    obtain ⟨i, hi⟩ := hsep x hx y hy hxy_ne
    have h_diff : ‖x i - y i‖ < δ i * Real.sqrt 2 := by
      apply norm_lt_of_re_im_bound;
      · exact div_nonneg ( mul_nonneg hε.le ( le_of_lt ( hr i ) ) ) ( Real.sqrt_nonneg _ );
      · convert! cell_index_diff hε ( hr i ) _ using 1;
        exacts [ c, by simpa using! congr_arg Prod.fst ( congr_fun hxy i ) ];
      · convert! cell_index_diff hε ( hr i ) _ using 1;
        exacts [ c, by simpa using! congr_arg Prod.snd ( congr_fun hxy i ) ];
    rw [ div_mul_cancel₀ _ ( by positivity ) ] at h_diff ; linarith;
  -- Conclude that `S` is finite and its cardinality is bounded by `T.card`.
  have h_finite : S.Finite := by
    exact Set.Finite.of_finite_image ( Set.Finite.subset ( Finset.finite_toSet T ) ( Set.image_subset_iff.mpr hg ) ) hg_inj
  have h_card : (S.ncard : ℝ) ≤ T.card := by
    have := Set.InjOn.ncard_image hg_inj;
    exact_mod_cast this ▸ Set.ncard_le_ncard ( show g '' S ⊆ T from Set.image_subset_iff.mpr hg ) |> le_trans <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ;
  refine ⟨ h_finite, h_card.trans ?_ ⟩;
  convert pow_le_pow_left₀ ( by positivity ) ( cellCount_le hε hεc ) ( 2 * Fintype.card ι ) using 1 ; norm_num [ Finset.card_univ, pow_mul ];
  erw [ Fintype.card_piFinset ] ; norm_num [ pow_mul ];
  norm_cast ; ring_nf!
  rw [ pow_mul' ] ; norm_cast ; ring_nf!

/-- [easy given `finite_and_card_le_of_separated`] **Lattice points in the
box.**  If every nonzero element of `Λ` escapes the small polydisc
`box r ρ`, then `Λ ∩ box r 2` is finite of cardinality at most
`(8/ρ)^(2·#ι)`.  Sketch: differences of distinct elements of `Λ ∩ box r 2`
are nonzero elements of `Λ`, so the separation hypothesis of the grid
pigeonhole holds with `c = 2`, `ε = ρ`. -/
theorem lattice_inter_box_finite_card (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖) :
    ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite ∧
      (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
        (8 / ρ) ^ (2 * Fintype.card ι) := by
  convert finite_and_card_le_of_separated r hr ( show 0 < ρ by linarith ) ( show ρ ≤ 2 by linarith ) ( show ( Λ : Set ( ι → ℂ ) ) ∩ box r 2 ⊆ box r 2 by exact Set.inter_subset_right ) _ using 1;
  · norm_num;
  · exact fun x hx y hy hxy => hsep ( x - y ) ( Λ.sub_mem hx.1 hy.1 ) ( sub_ne_zero_of_ne hxy ) |> fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi ⟩

variable (i₀ : ι)

/-- Projection of a polydisc point to the distinguished coordinate `i₀`,
rescaled so that the repeated distance becomes exactly `1`. -/
noncomputable def proj (r : ι → ℝ) (i₀ : ι) (x : ι → ℂ) : ℂ :=
  x i₀ / (r i₀ : ℂ)

/-- [medium] **Translation produces unit distances.**  Let `Z` be a finite
set of elements of `Λ` whose coordinates have modulus *exactly* `r i`.
Then the projection `P ⊆ ℂ` of `Λ ∩ box r 2` to the (rescaled) `i₀`-th
coordinate satisfies `#P = #(Λ ∩ box r 2)` and has at least
`#Z · #(Λ ∩ box r 1)` ordered unit-distance pairs.
Sketch: (1) `proj` is injective on `Λ` by `hinj` (two preimages differ by
an element of `Λ` vanishing at `i₀`), giving the cardinality statement.
(2) For `a ∈ Λ ∩ box r 1` and `z ∈ Z`, the translate `a + z` lies in
`Λ ∩ box r 2` (triangle inequality coordinatewise), and
`dist (proj a) (proj (a + z)) = ‖z i₀‖ / r i₀ = 1`.  The assignment
`(a, z) ↦ (proj a, proj (a + z))` is injective into ordered pairs (recover
`a` from the first component by injectivity, then `z i₀`, then `z`), and
each image pair is a distinct-points pair at distance one. -/
theorem le_unitPairsC_of_translates (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ))
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0)
    (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite)
    (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ)
    (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    (hfin.toFinset.image (proj r i₀)).card = ((Λ : Set (ι → ℂ)) ∩ box r 2).ncard ∧
      Z.card * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard ≤
        unitPairsC (hfin.toFinset.image (proj r i₀)) := by
  refine' ⟨ _, _ ⟩;
  · rw [ Finset.card_image_of_injOn, ← Set.ncard_coe_finset, hfin.coe_toFinset ];
    intro x hx y hy; specialize hinj ( x - y ) ; simp_all +decide [ sub_eq_zero ] ;
    simp_all +decide [ proj, div_eq_iff, ne_of_gt ( hr i₀ ) ];
    exact fun h => hinj ( Λ.sub_mem hx.1 hy.1 ) h;
  · refine' le_trans _ ( Finset.card_mono _ );
    rotate_left;
    exact Finset.image ( fun p : ( ι → ℂ ) × ( ι → ℂ ) => ( p.2 i₀ / r i₀, ( p.2 + p.1 ) i₀ / r i₀ ) ) ( Z ×ˢ ( hfin.toFinset.filter fun x => ∀ i, ‖x i‖ ≤ r i ) );
    · intro; simp +decide [ dist_eq_norm ] ;
      rintro x y hx hy hxy hy' rfl; simp_all +decide [ proj, box ] ;
      refine' ⟨ ⟨ ⟨ y, ⟨ hy, hxy ⟩, rfl ⟩, ⟨ y + x, ⟨ Λ.add_mem hy ( hZΛ x hx ), fun i => _ ⟩, _ ⟩, _ ⟩, _ ⟩ <;> simp_all +decide [ add_div, ne_of_gt ];
      · exact le_trans ( norm_add_le _ _ ) ( by linarith [ hy' i, hZr x hx i ] );
      · exact fun h => by have := hZr x hx i₀; norm_num [ h ] at this; linarith [ hr i₀ ] ;
      · rw [ abs_of_pos ( hr i₀ ), div_self ( ne_of_gt ( hr i₀ ) ) ];
    · rw [ Finset.card_image_of_injOn ];
      · simp +zetaDelta at *;
        gcongr;
        rw [ ← Set.ncard_coe_finset ];
        fapply Set.ncard_le_ncard;
        · simp +contextual [ Set.subset_def, box ];
          exact fun x hx hx' i => le_trans ( hx' i ) ( le_mul_of_one_le_left ( le_of_lt ( hr i ) ) ( by norm_num ) );
        · exact hfin.toFinset.finite_toSet.subset fun x hx => by aesop;
      · intro p hp q hq h; simp_all +decide [ div_eq_iff, ne_of_gt ( hr _ ) ] ;
        have h_eq : p.1 = q.1 := by
          specialize hinj ( p.1 - q.1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact hinj ( by simpa using Λ.sub_mem ( hZΛ _ hp.1 ) ( hZΛ _ hq.1 ) ) ( by aesop );
        specialize hinj ( p.2 - q.2 ) ; simp_all +decide [ sub_eq_iff_eq_add ];
        exact Prod.ext h_eq ( hinj ( Λ.sub_mem hp.1.1 hq.2.1.1 ) )

end GeometricCore

end Erdos

import Tengoku.Cliffordchain.Clifford.Classify
import Tengoku.Cliffordchain.Clifford.Bridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Layer 14: Mathlib-only restatements and witnesses for the Clifford chain

`CliffordChain n` is a recursive predicate (`Chain`, levels alternating between points and
generalized circles). Its meaning for `n = 4` and `n = 5` is restated below in Mathlib-only terms,
and so is the refutation for `n = 6`:
* `l14_cliffordChain_four`: four Mathlib spheres through a point `M`; any second intersections
  `Pᵢⱼ ≠ M`; each triple non-collinear. Then the four circles through the triples have a common
  point (`Cospherical`). The library's extra general-position condition "centres not collinear"
  (`GenTriple`, `triP ≠ 0`) is **derived** (`l14b_genTriple`, via `cross_second`), so it is not an
  extra hypothesis here.
* `l14_cliffordChain_five`: likewise for five circles. The five Clifford points lie on a circle
  or a line.
* `l14_not_cliffordChain_six`: there are six circles through `0` in general position (all stated
  with `Collinear` / `Metric.sphere`) such that no point lies on a generalized circle
  (a `Metric.sphere` or a `line[ℝ, a, b]`, `a ≠ b`) through the Clifford points of every
  five-circle subfamily. A Clifford point of four circles is any point on the four circles through
  the second intersections of the triples. The configuration is the library's `Counter6.cx`.
For general `n` (`cliffordChain_iff`, `not_cliffordChain_of_six_le`) the recursive definition
is not restated (see the report); witnesses for them are the configurations above.
-/

namespace Clifford

open EuclideanGeometry ComplexConjugate Complex

/-! ### Bridges -/

/-- A point `≠ 0` on the two circles through `0` with centres `c ≠ d` is `second c d`.
@isnad1 id=eq.4h3v.s6.a76c04bcf5cc from=translated src=- shape=5225f4ae vocab=dcf02dd0
-/
theorem l14b_second_eq {c d z : ℂ} (hcd : c ≠ d) (hz : z ≠ 0) (h1 : dist z c = ‖c‖)
    (h2 : dist z d = ‖d‖) : z = second c d := by
  have k1 : (z - c) * conj (z - c) = c * conj c := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      ← Complex.dist_eq, h1]
  have k2 : (z - d) * conj (z - d) = d * conj d := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      ← Complex.dist_eq, h2]
  have hA : conj c - conj d ≠ 0 := conj_sub_ne_zero hcd
  simp only [map_sub] at k1 k2
  have key : z * (z * (conj c - conj d) - (conj c * d - c * conj d)) = 0 := by
    linear_combination (d - z) * k1 + (z - c) * k2
  have h := (mul_eq_zero.1 key).resolve_left hz
  unfold second
  rw [eq_div_iff hA]
  linear_combination h

/-- A point `P ≠ M` on two spheres through `M` with distinct centres is the library's `second`
(after translating `M` to `0`), and the two translated centres are `Transversal`.
@isnad1 id=and.4h4v.s7.45d9f54d6772 from=translated src=- shape=f93e02b9 vocab=f90b4bdf
-/
theorem l14b_second {M : ℂ} {s t : Sphere ℂ} (hs : M ∈ s) (ht : M ∈ t)
    (hst : s.center ≠ t.center) {P : ℂ} (h : P ∈ s ∧ P ∈ t ∧ P ≠ M) :
    P - M = second (s.center - M) (t.center - M) ∧ Transversal (s.center - M) (t.center - M) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [mem_sphere] at hs ht h1 h2
  have e : ∀ c : ℂ, dist (P - M) (c - M) = dist P c := fun c => by
    rw [Complex.dist_eq, Complex.dist_eq]; ring_nf
  have f : ∀ c : ℂ, ‖c - M‖ = dist M c := fun c => by rw [Complex.dist_eq, norm_sub_rev]
  have hz : P - M ≠ 0 := sub_ne_zero.2 h3
  have eq := l14b_second_eq (c := s.center - M) (d := t.center - M)
    (fun h => hst (sub_left_injective h)) hz (by rw [e, f, h1, hs]) (by rw [e, f, h2, ht])
  refine ⟨eq, fun e0 => hz ?_⟩
  rw [eq]; unfold second; rw [e0, sub_self, zero_div]

/-- Non-collinear second intersections force non-collinear centres, hence `GenTriple`.
@isnad1 id=gentripl.4h3v.s7.227e3749eb0c from=translated src=- shape=f79eeae8 vocab=b6e5a76e
-/
theorem l14b_genTriple {a b c : ℂ} (hab : Transversal a b) (hac : Transversal a c)
    (hbc : Transversal b c)
    (hn : ¬ Collinear ℝ ({second a b, second a c, second b c} : Set ℂ)) : GenTriple a b c := by
  have htri : ¬ Collinear ℝ ({a, b, c} : Set ℂ) := by
    intro hcol
    have ht : triP a b c (conj a) (conj b) (conj c) = 0 := by
      by_contra h; exact ((triP_ne_zero_iff a b c).1 h) hcol
    have key := cross_second hab.ne hac.ne hbc.ne
    have k2 : (conj (second a c - second a b) * (second b c - second a b) -
        (second a c - second a b) * conj (second b c - second a b)) *
        ((conj a - conj b) * (conj a - conj c) * (conj b - conj c) *
          ((a - b) * (a - c) * (b - c))) = 0 := by rw [key, ht]; ring
    have hprod : (conj a - conj b) * (conj a - conj c) * (conj b - conj c) *
        ((a - b) * (a - c) * (b - c)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (conj_sub_ne_zero hab.ne) (conj_sub_ne_zero hac.ne))
        (conj_sub_ne_zero hbc.ne)) (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hab.ne)
          (sub_ne_zero.2 hac.ne)) (sub_ne_zero.2 hbc.ne))
    apply hn
    rw [collinear_iff_conj_mul]
    linear_combination (mul_eq_zero.1 k2).resolve_right hprod
  exact (genTriple_iff hab hac hbc).2 ⟨htri, hn⟩

/--
@isnad1 id=collinea.1h4v.s7.528eeb1ae8ba from=translated src=- shape=11f5d092 vocab=be53c61d
-/
theorem l14b_collinear_sub {a b c M : ℂ} (h : Collinear ℝ ({a - M, b - M, c - M} : Set ℂ)) :
    Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a - M) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  refine ⟨v, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · obtain ⟨r, hr⟩ := hv (p - M) (by simp)
    refine ⟨r, ?_⟩
    rw [vadd_eq_add, Complex.real_smul] at hr ⊢
    linear_combination hr
  · obtain ⟨r, hr⟩ := hv (p - M) (by simp)
    refine ⟨r, ?_⟩
    rw [vadd_eq_add, Complex.real_smul] at hr ⊢
    linear_combination hr

/--
@isnad1 id=cospheri.1h2v.s5.c2b0dfbc7657 from=translated src=- shape=9fb70899 vocab=1d0d65e8
-/
theorem l14b_cospherical_add {s : Set ℂ} (M : ℂ) (h : Cospherical s) :
    Cospherical ((· + M) '' s) := by
  obtain ⟨c, r, hr⟩ := h
  refine ⟨c + M, r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [dist_add_right]; exact hr x hx

/--
@isnad1 id=collinea.1h2v.s7.53dfde476bd3 from=translated src=- shape=2bc20189 vocab=d9d6d8e4
-/
theorem l14b_collinear_add {s : Set ℂ} (M : ℂ) (h : Collinear ℝ s) :
    Collinear ℝ ((· + M) '' s) := by
  obtain ⟨p, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).1 h
  refine (collinear_iff_exists_forall_eq_smul_vadd _).2 ⟨p + M, v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, rfl⟩ := hv x hx
  exact ⟨r, by simp only [vadd_eq_add]; ring⟩

/--
@isnad1 id=cospheri.1h5v.s6.e938dd2bd6b7 from=translated src=- shape=9f41c8a3 vocab=db008e71
-/
theorem l14b_cosph_tr {x y z w M : ℂ}
    (h : Cospherical ({x - M, y - M, z - M, w} : Set ℂ)) :
    Cospherical ({x, y, z, w + M} : Set ℂ) := by
  have hs : ({x, y, z, w + M} : Set ℂ) = (· + M) '' {x - M, y - M, z - M, w} := by
    simp only [Set.image_insert_eq, Set.image_singleton, sub_add_cancel]
  rw [hs]; exact l14b_cospherical_add M h

/--
@isnad1 id=not.4h7v.s7.79a08507fdef from=translated src=- shape=3d27097c vocab=be53c61d
-/
theorem l14b_nc {a b c x y z M : ℂ} (ea : a - M = x) (eb : b - M = y) (ec : c - M = z)
    (hn : ¬ Collinear ℝ ({a, b, c} : Set ℂ)) : ¬ Collinear ℝ ({x, y, z} : Set ℂ) :=
  fun h => hn (l14b_collinear_sub (by rw [ea, eb, ec]; exact h))

/-- The four `Γ`-circle facts for a subfamily, in the original (untranslated) coordinates.
@isnad1 id=and.7h11v.s8.9fdc3129f3f7 from=translated src=- shape=f4c86569 vocab=5710d270
-/
theorem l14b_four {M a b c d Pab Pac Pad Pbc Pbd Pcd : ℂ} (G : GenPos4 a b c d)
    (eab : Pab - M = second a b) (eac : Pac - M = second a c) (ead : Pad - M = second a d)
    (ebc : Pbc - M = second b c) (ebd : Pbd - M = second b d) (ecd : Pcd - M = second c d) :
    Cospherical ({Pab, Pac, Pbc, miquel a b c d + M} : Set ℂ) ∧
      Cospherical ({Pab, Pad, Pbd, miquel a b c d + M} : Set ℂ) ∧
      Cospherical ({Pac, Pad, Pcd, miquel a b c d + M} : Set ℂ) ∧
      Cospherical ({Pbc, Pbd, Pcd, miquel a b c d + M} : Set ℂ) := by
  obtain ⟨x1, x2, x3, x4⟩ := clifford_one G
  unfold OnCircle3 at x1 x2 x3 x4
  rw [← eab, ← eac, ← ebc] at x1
  rw [← eab, ← ead, ← ebd] at x2
  rw [← eac, ← ead, ← ecd] at x3
  rw [← ebc, ← ebd, ← ecd] at x4
  exact ⟨l14b_cosph_tr x1, l14b_cosph_tr x2, l14b_cosph_tr x3, l14b_cosph_tr x4⟩

/--
@isnad1 id=eq.0h6v.s7.70ffc3648af4 from=translated src=- shape=354bdd0b vocab=3189007d
-/
theorem l14b_img5 (M x₁ x₂ x₃ x₄ x₅ : ℂ) :
    ({x₅ + M, x₄ + M, x₃ + M, x₂ + M, x₁ + M} : Set ℂ) = (· + M) '' {x₁, x₂, x₃, x₄, x₅} := by
  simp only [Set.image_insert_eq, Set.image_singleton]
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ### `CliffordChain 4`, Mathlib-only -/

/-- The meaning of `CliffordChain 4`, Mathlib-only (Clifford's first theorem).
@isnad1 id=ex.17h11v.s9.7b6080b27e4b from=translated src=- shape=caf8fd86 vocab=70fe7177
-/
theorem l14_cliffordChain_four (M : ℂ) (s₁ s₂ s₃ s₄ : Sphere ℂ)
    (hM : M ∈ s₁ ∧ M ∈ s₂ ∧ M ∈ s₃ ∧ M ∈ s₄)
    (d12 : s₁.center ≠ s₂.center) (d13 : s₁.center ≠ s₃.center) (d14 : s₁.center ≠ s₄.center)
    (d23 : s₂.center ≠ s₃.center) (d24 : s₂.center ≠ s₄.center) (d34 : s₃.center ≠ s₄.center)
    (P12 P13 P14 P23 P24 P34 : ℂ)
    (m12 : P12 ∈ s₁ ∧ P12 ∈ s₂ ∧ P12 ≠ M) (m13 : P13 ∈ s₁ ∧ P13 ∈ s₃ ∧ P13 ≠ M)
    (m14 : P14 ∈ s₁ ∧ P14 ∈ s₄ ∧ P14 ≠ M) (m23 : P23 ∈ s₂ ∧ P23 ∈ s₃ ∧ P23 ≠ M)
    (m24 : P24 ∈ s₂ ∧ P24 ∈ s₄ ∧ P24 ≠ M) (m34 : P34 ∈ s₃ ∧ P34 ∈ s₄ ∧ P34 ≠ M)
    (n123 : ¬ Collinear ℝ ({P12, P13, P23} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({P12, P14, P24} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({P13, P14, P34} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({P23, P24, P34} : Set ℂ)) :
    ∃ P : ℂ, Cospherical ({P12, P13, P23, P} : Set ℂ) ∧ Cospherical ({P12, P14, P24, P} : Set ℂ) ∧
      Cospherical ({P13, P14, P34, P} : Set ℂ) ∧ Cospherical ({P23, P24, P34, P} : Set ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  obtain ⟨e12, t12⟩ := l14b_second h1 h2 d12 m12
  obtain ⟨e13, t13⟩ := l14b_second h1 h3 d13 m13
  obtain ⟨e14, t14⟩ := l14b_second h1 h4 d14 m14
  obtain ⟨e23, t23⟩ := l14b_second h2 h3 d23 m23
  obtain ⟨e24, t24⟩ := l14b_second h2 h4 d24 m24
  obtain ⟨e34, t34⟩ := l14b_second h3 h4 d34 m34
  have G : GenPos4 (s₁.center - M) (s₂.center - M) (s₃.center - M) (s₄.center - M) :=
    ⟨t12, t13, t14, t23, t24, t34,
      l14b_genTriple t12 t13 t23 (l14b_nc e12 e13 e23 n123),
      l14b_genTriple t12 t14 t24 (l14b_nc e12 e14 e24 n124),
      l14b_genTriple t13 t14 t34 (l14b_nc e13 e14 e34 n134),
      l14b_genTriple t23 t24 t34 (l14b_nc e23 e24 e34 n234)⟩
  exact ⟨_, l14b_four G e12 e13 e14 e23 e24 e34⟩

/-! ### `CliffordChain 5`, Mathlib-only -/

/-- The meaning of `CliffordChain 5`, Mathlib-only (Clifford's second theorem).
@isnad1 id=ex.31h16v.s11.3dfd20019742 from=translated src=- shape=8f4fca42 vocab=70fe7177
-/
theorem l14_cliffordChain_five (M : ℂ) (s₁ s₂ s₃ s₄ s₅ : Sphere ℂ)
    (hM : M ∈ s₁ ∧ M ∈ s₂ ∧ M ∈ s₃ ∧ M ∈ s₄ ∧ M ∈ s₅)
    (d12 : s₁.center ≠ s₂.center) (d13 : s₁.center ≠ s₃.center) (d14 : s₁.center ≠ s₄.center)
    (d15 : s₁.center ≠ s₅.center) (d23 : s₂.center ≠ s₃.center) (d24 : s₂.center ≠ s₄.center)
    (d25 : s₂.center ≠ s₅.center) (d34 : s₃.center ≠ s₄.center) (d35 : s₃.center ≠ s₅.center)
    (d45 : s₄.center ≠ s₅.center)
    (P12 P13 P14 P15 P23 P24 P25 P34 P35 P45 : ℂ)
    (m12 : P12 ∈ s₁ ∧ P12 ∈ s₂ ∧ P12 ≠ M) (m13 : P13 ∈ s₁ ∧ P13 ∈ s₃ ∧ P13 ≠ M)
    (m14 : P14 ∈ s₁ ∧ P14 ∈ s₄ ∧ P14 ≠ M) (m15 : P15 ∈ s₁ ∧ P15 ∈ s₅ ∧ P15 ≠ M)
    (m23 : P23 ∈ s₂ ∧ P23 ∈ s₃ ∧ P23 ≠ M) (m24 : P24 ∈ s₂ ∧ P24 ∈ s₄ ∧ P24 ≠ M)
    (m25 : P25 ∈ s₂ ∧ P25 ∈ s₅ ∧ P25 ≠ M) (m34 : P34 ∈ s₃ ∧ P34 ∈ s₄ ∧ P34 ≠ M)
    (m35 : P35 ∈ s₃ ∧ P35 ∈ s₅ ∧ P35 ≠ M) (m45 : P45 ∈ s₄ ∧ P45 ∈ s₅ ∧ P45 ≠ M)
    (n123 : ¬ Collinear ℝ ({P12, P13, P23} : Set ℂ)) (n124 : ¬ Collinear ℝ ({P12, P14, P24} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({P12, P15, P25} : Set ℂ)) (n134 : ¬ Collinear ℝ ({P13, P14, P34} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({P13, P15, P35} : Set ℂ)) (n145 : ¬ Collinear ℝ ({P14, P15, P45} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({P23, P24, P34} : Set ℂ)) (n235 : ¬ Collinear ℝ ({P23, P25, P35} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({P24, P25, P45} : Set ℂ)) (n345 : ¬ Collinear ℝ ({P34, P35, P45} : Set ℂ)) :
    ∃ Q₁ Q₂ Q₃ Q₄ Q₅ : ℂ,
      (Cospherical ({P23, P24, P34, Q₁} : Set ℂ) ∧ Cospherical ({P23, P25, P35, Q₁} : Set ℂ) ∧
        Cospherical ({P24, P25, P45, Q₁} : Set ℂ) ∧ Cospherical ({P34, P35, P45, Q₁} : Set ℂ)) ∧
      (Cospherical ({P13, P14, P34, Q₂} : Set ℂ) ∧ Cospherical ({P13, P15, P35, Q₂} : Set ℂ) ∧
        Cospherical ({P14, P15, P45, Q₂} : Set ℂ) ∧ Cospherical ({P34, P35, P45, Q₂} : Set ℂ)) ∧
      (Cospherical ({P12, P14, P24, Q₃} : Set ℂ) ∧ Cospherical ({P12, P15, P25, Q₃} : Set ℂ) ∧
        Cospherical ({P14, P15, P45, Q₃} : Set ℂ) ∧ Cospherical ({P24, P25, P45, Q₃} : Set ℂ)) ∧
      (Cospherical ({P12, P13, P23, Q₄} : Set ℂ) ∧ Cospherical ({P12, P15, P25, Q₄} : Set ℂ) ∧
        Cospherical ({P13, P15, P35, Q₄} : Set ℂ) ∧ Cospherical ({P23, P25, P35, Q₄} : Set ℂ)) ∧
      (Cospherical ({P12, P13, P23, Q₅} : Set ℂ) ∧ Cospherical ({P12, P14, P24, Q₅} : Set ℂ) ∧
        Cospherical ({P13, P14, P34, Q₅} : Set ℂ) ∧ Cospherical ({P23, P24, P34, Q₅} : Set ℂ)) ∧
      (Cospherical ({Q₁, Q₂, Q₃, Q₄, Q₅} : Set ℂ) ∨ Collinear ℝ ({Q₁, Q₂, Q₃, Q₄, Q₅} : Set ℂ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hM
  obtain ⟨e12, t12⟩ := l14b_second h1 h2 d12 m12
  obtain ⟨e13, t13⟩ := l14b_second h1 h3 d13 m13
  obtain ⟨e14, t14⟩ := l14b_second h1 h4 d14 m14
  obtain ⟨e15, t15⟩ := l14b_second h1 h5 d15 m15
  obtain ⟨e23, t23⟩ := l14b_second h2 h3 d23 m23
  obtain ⟨e24, t24⟩ := l14b_second h2 h4 d24 m24
  obtain ⟨e25, t25⟩ := l14b_second h2 h5 d25 m25
  obtain ⟨e34, t34⟩ := l14b_second h3 h4 d34 m34
  obtain ⟨e35, t35⟩ := l14b_second h3 h5 d35 m35
  obtain ⟨e45, t45⟩ := l14b_second h4 h5 d45 m45
  have G : GenPos5 (s₁.center - M) (s₂.center - M) (s₃.center - M) (s₄.center - M)
      (s₅.center - M) :=
    ⟨t12, t13, t14, t15, t23, t24, t25, t34, t35, t45,
      l14b_genTriple t12 t13 t23 (l14b_nc e12 e13 e23 n123),
      l14b_genTriple t12 t14 t24 (l14b_nc e12 e14 e24 n124),
      l14b_genTriple t12 t15 t25 (l14b_nc e12 e15 e25 n125),
      l14b_genTriple t13 t14 t34 (l14b_nc e13 e14 e34 n134),
      l14b_genTriple t13 t15 t35 (l14b_nc e13 e15 e35 n135),
      l14b_genTriple t14 t15 t45 (l14b_nc e14 e15 e45 n145),
      l14b_genTriple t23 t24 t34 (l14b_nc e23 e24 e34 n234),
      l14b_genTriple t23 t25 t35 (l14b_nc e23 e25 e35 n235),
      l14b_genTriple t24 t25 t45 (l14b_nc e24 e25 e45 n245),
      l14b_genTriple t34 t35 t45 (l14b_nc e34 e35 e45 n345)⟩
  have A := l14b_four G.pos4_bcde e23 e24 e25 e34 e35 e45
  have B := l14b_four G.pos4_acde e13 e14 e15 e34 e35 e45
  have C := l14b_four G.pos4_abde e12 e14 e15 e24 e25 e45
  have D := l14b_four G.pos4_abce e12 e13 e15 e23 e25 e35
  have E := l14b_four G.pos4_abcd e12 e13 e14 e23 e24 e34
  refine ⟨_, _, _, _, _, A, B, C, D, E, ?_⟩
  rw [l14b_img5]
  rcases clifford_two_clean G with h | h
  · exact Or.inl (l14b_cospherical_add M h)
  · exact Or.inr (l14b_collinear_add M h)

/-! ### Witnesses -/

/--
@isnad1 id=mem.1h3v.s6.a2ede69d5ed4 from=translated src=- shape=61d9a5a4 vocab=118b9f27
-/
theorem l14b_mem {z c : ℂ} {r : ℝ} (h : (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 = r) :
    z ∈ (⟨c, Real.sqrt r⟩ : Sphere ℂ) := by
  rw [mem_sphere, Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [sub_re, sub_im]
  linear_combination h

/--
@isnad1 id=cospheri.1h3v.s6.e434192fc0a7 from=translated src=- shape=f38f5685 vocab=5359e907
-/
theorem l14b_cosph {s : Set ℂ} (o : ℂ) (r : ℝ)
    (h : ∀ x ∈ s, (x.re - o.re) ^ 2 + (x.im - o.im) ^ 2 = r) : Cospherical s :=
  ⟨o, Real.sqrt r, fun x hx => l14b_mem (h x hx)⟩

/--
@isnad1 id=not.1h3v.s7.f9a12a532a87 from=translated src=- shape=aab1fa82 vocab=92cbca22
-/
theorem l14b_not_collinear {a b c : ℂ}
    (h : (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re) ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_re, add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Witness for `l14_cliffordChain_four`: four circles through `M = 0` with centres `3 - i`, `1 + 3i`,
`-1 + 3i`, `-3 - i`; the six second intersections `4+2i, 2+2i, -2i, 6i, -2+2i, -4+2i`; the four
`Γ` circles with centres `3+5i, 1+i, -1+i, -3+5i`; the Clifford point `4i`, distinct from all six
second intersections.
@isnad1 id=and.0h0v.s11.0422b5826df8 from=translated src=- shape=440b0d41 vocab=99a839c8
-/
theorem l14w_cliffordChain_four :
    ((⟨0, 0⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ)) ∧
    ((⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center ≠ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ).center) ∧
    (((⟨4, 2⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨4, 2⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨4, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨2, 2⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨2, 2⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨2, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, -2⟩ : ℂ) ∈ (⟨(⟨3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, 6⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 6⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨0, 6⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-2, 2⟩ : ℂ) ∈ (⟨(⟨1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-2, 2⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-2, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-4, 2⟩ : ℂ) ∈ (⟨(⟨-1, 3⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-4, 2⟩ : ℂ) ∈ (⟨(⟨-3, -1⟩ : ℂ), Real.sqrt 10⟩ : Sphere ℂ) ∧ (⟨-4, 2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (¬ Collinear ℝ ({(⟨4, 2⟩ : ℂ), (⟨2, 2⟩ : ℂ), (⟨0, 6⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨4, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-2, 2⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨2, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-4, 2⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, 6⟩ : ℂ), (⟨-2, 2⟩ : ℂ), (⟨-4, 2⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨4, 2⟩ : ℂ), (⟨2, 2⟩ : ℂ), (⟨0, 6⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨4, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-2, 2⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨2, 2⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-4, 2⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, 6⟩ : ℂ), (⟨-2, 2⟩ : ℂ), (⟨-4, 2⟩ : ℂ), (⟨0, 4⟩ : ℂ)} : Set ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨4, 2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨2, 2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨0, 6⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨-2, 2⟩ : ℂ)) ∧
    ((⟨0, 4⟩ : ℂ) ≠ (⟨-4, 2⟩ : ℂ)) := by
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num)⟩) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_cosph (⟨3, 5⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨1, 1⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-1, 1⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 5⟩ : ℂ) (10 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  exact by norm_num [Complex.ext_iff]

/-- Witness for `l14_cliffordChain_five`: five circles through `M = 0` with centres `-3-2i, -i, -1-2i, -2-i, -2+3i`; all ten second intersections, the ten `Γ` circles (explicit centre and squared radius), the five Clifford points `Q₁ … Q₅` (pairwise distinct, distinct from every second intersection) and the Clifford circle (centre `(-16 - 81i)/17`); the `Q`'s are not collinear, so the conclusion holds through its `Cospherical` branch.
@isnad1 id=and.0h0v.s13.72345ae92bb4 from=translated src=- shape=0a68f391 vocab=9560d768
-/
theorem l14w_cliffordChain_five :
    ((⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, 0⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ)) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center ≠ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    ((⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ).center ≠ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ).center) ∧
    (((⟨3/5, -9/5⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨3/5, -9/5⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨3/5, -9/5⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, -4⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨0, -4⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, -4⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-1, 1⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-1, 1⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-1, 1⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-5, 1⟩ : ℂ) ∈ (⟨(⟨-3, -2⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-5, 1⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-5, 1⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨1, -1⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨1, -1⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨1, -1⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨0, -2⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨0, -2⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-4/5, -2/5⟩ : ℂ) ∈ (⟨(⟨0, -1⟩ : ℂ), Real.sqrt 1⟩ : Sphere ℂ) ∧ (⟨-4/5, -2/5⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-4/5, -2/5⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-3, -3⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-3, -3⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-3, -3⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-35/13, -7/13⟩ : ℂ) ∈ (⟨(⟨-1, -2⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-35/13, -7/13⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-35/13, -7/13⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (((⟨-4, 0⟩ : ℂ) ∈ (⟨(⟨-2, -1⟩ : ℂ), Real.sqrt 5⟩ : Sphere ℂ) ∧ (⟨-4, 0⟩ : ℂ) ∈ (⟨(⟨-2, 3⟩ : ℂ), Real.sqrt 13⟩ : Sphere ℂ) ∧ (⟨-4, 0⟩ : ℂ) ≠ (⟨0, 0⟩ : ℂ))) ∧
    (¬ Collinear ℝ ({(⟨3/5, -9/5⟩ : ℂ), (⟨0, -4⟩ : ℂ), (⟨1, -1⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨3/5, -9/5⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨0, -2⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨3/5, -9/5⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, -4⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨-3, -3⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, -4⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨-1, 1⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4, 0⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨1, -1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-3, -3⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨1, -1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨0, -2⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-4, 0⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨-3, -3⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-4, 0⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨0, -4⟩ : ℂ), (⟨1, -1⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨0, -4⟩ : ℂ), (⟨1, -1⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨3/5, -9/5⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-1, 1⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -2⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-1, 1⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -4⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-1, 1⟩ : ℂ), (⟨-5, 1⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-3, -3⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨0, -2⟩ : ℂ), (⟨-3, -3⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨1, -1⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨0, -2⟩ : ℂ), (⟨-4/5, -2/5⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-3, -3⟩ : ℂ), (⟨-35/13, -7/13⟩ : ℂ), (⟨-4, 0⟩ : ℂ), (⟨-91/17, -41/17⟩ : ℂ)} : Set ℂ)) ∧
    (Cospherical ({(⟨-91/17, -41/17⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ), (⟨20/17, -158/17⟩ : ℂ), (⟨24/17, -6/17⟩ : ℂ)} : Set ℂ)) ∧
    (¬ Collinear ℝ ({(⟨-91/17, -41/17⟩ : ℂ), (⟨-52/17, -4/17⟩ : ℂ), (⟨-29/17, 3/17⟩ : ℂ)} : Set ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨3/5, -9/5⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨0, -4⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-1, 1⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-5, 1⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨1, -1⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨0, -2⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-4/5, -2/5⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-3, -3⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-35/13, -7/13⟩ : ℂ)) ∧
    ((⟨-91/17, -41/17⟩ : ℂ) ≠ (⟨-4, 0⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨20/17, -158/17⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-29/17, 3/17⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-52/17, -4/17⟩ : ℂ)) ∧
    ((⟨24/17, -6/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-29/17, 3/17⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-52/17, -4/17⟩ : ℂ)) ∧
    ((⟨20/17, -158/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-52/17, -4/17⟩ : ℂ)) ∧
    ((⟨-29/17, 3/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) ∧
    ((⟨-52/17, -4/17⟩ : ℂ) ≠ (⟨-91/17, -41/17⟩ : ℂ)) := by
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num), l14b_mem (by norm_num)⟩) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (⟨l14b_mem (by norm_num), l14b_mem (by norm_num), by norm_num [Complex.ext_iff]⟩) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (l14b_cosph (⟨8, -5⟩ : ℂ) (65 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-1/5, -2/5⟩ : ℂ) (13/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-6/7, -11/7⟩ : ℂ) (325/49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (25 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨8, -5⟩ : ℂ) (65 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-5, -6⟩ : ℂ) (49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-10, -9⟩ : ℂ) (125 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-7/5, -26/5⟩ : ℂ) (117/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-1/5, -2/5⟩ : ℂ) (13/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-5, -6⟩ : ℂ) (49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-8/3, -7/3⟩ : ℂ) (65/9 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-6/7, -11/7⟩ : ℂ) (325/49 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-10, -9⟩ : ℂ) (125 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-43/11, -18/11⟩ : ℂ) (325/121 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-3, 2⟩ : ℂ) (25 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-7/5, -26/5⟩ : ℂ) (117/5 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-8/3, -7/3⟩ : ℂ) (65/9 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-43/11, -18/11⟩ : ℂ) (325/121 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_cosph (⟨-16/17, -81/17⟩ : ℂ) (25 : ℝ) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; norm_num)) ?_
  refine And.intro (l14b_not_collinear (by norm_num)) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  refine And.intro (by norm_num [Complex.ext_iff]) ?_
  exact by norm_num [Complex.ext_iff]

/-! ### `¬ CliffordChain 6`, Mathlib-only -/

/-- A line `line[ℝ, a, b]` (`a ≠ b`) is a generalized circle in the library's sense.
@isnad1 id=isgcircl.1h2v.s8.237854550cd5 from=translated src=- shape=c5b21520 vocab=c879da88
-/
theorem l14b_isGCircle_line {a b : ℂ} (h : a ≠ b) : IsGCircle (line[ℝ, a, b] : Set ℂ) := by
  refine Or.inr ⟨a, b - a, sub_ne_zero.2 h.symm, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq, mem_affineSpan_pair_iff_exists_lineMap_eq,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, by ring⟩
  · rintro ⟨t, rfl⟩; exact ⟨t, by ring⟩

/--
@isnad1 id=isgcircl.1h1v.s8.d1f7dc52580f from=translated src=- shape=7be1c060 vocab=bbcbc968
-/
theorem l14b_isGCircle {Y : Set ℂ}
    (h : (∃ o : ℂ, ∃ r : ℝ, Y = Metric.sphere o r) ∨ ∃ a b : ℂ, a ≠ b ∧ Y = line[ℝ, a, b]) :
    IsGCircle Y := by
  rcases h with h | ⟨a, b, hab, rfl⟩
  · exact Or.inl h
  · exact l14b_isGCircle_line hab

/-- **The Clifford chain fails at `n = 6`**, Mathlib-only statement. There are six circles through
`0` (centres `c i`, `Metric.sphere (c i) ‖c i‖`) in general position, such that for every choice
`S` of second intersection points: (a) every triple of second intersections is non-collinear,
and (b) there is no point `p` that lies, for every five-circle subfamily `i`, on a generalized
circle `Y` (a sphere, or a line `line[ℝ, a, b]` with `a ≠ b`) containing, for each four-circle
sub-subfamily `j`, a point `q` on the four circles through the second intersections of its
triples `k`.
@isnad1 id=ex.0h0v.s10.5a76d46fe9a3 from=translated src=- shape=953669ed vocab=6ed315c6
-/
theorem l14_not_cliffordChain_six :
    ∃ c : Fin 6 → ℂ,
      (∀ i j, i ≠ j → ¬ Collinear ℝ ({0, c i, c j} : Set ℂ)) ∧
      (∀ i j k, i < j → j < k → ¬ Collinear ℝ ({c i, c j, c k} : Set ℂ)) ∧
      ∀ S : ℂ → ℂ → ℂ,
        (∀ i j, i ≠ j → S (c i) (c j) ∈ Metric.sphere (c i) ‖c i‖ ∧
          S (c i) (c j) ∈ Metric.sphere (c j) ‖c j‖ ∧ S (c i) (c j) ≠ 0) →
        (∀ i j k, i < j → j < k →
          ¬ Collinear ℝ ({S (c i) (c j), S (c i) (c k), S (c j) (c k)} : Set ℂ)) ∧
        ¬ ∃ p : ℂ, ∀ i : Fin 6, ∃ Y : Set ℂ,
          ((∃ o : ℂ, ∃ r : ℝ, Y = Metric.sphere o r) ∨ ∃ a b : ℂ, a ≠ b ∧ Y = line[ℝ, a, b]) ∧
          p ∈ Y ∧ ∀ j : Fin 5, ∃ q ∈ Y, ∀ k : Fin 4,
            Cospherical ({S (c (i.succAbove (j.succAbove (k.succAbove 0))))
                (c (i.succAbove (j.succAbove (k.succAbove 1)))),
              S (c (i.succAbove (j.succAbove (k.succAbove 0))))
                (c (i.succAbove (j.succAbove (k.succAbove 2)))),
              S (c (i.succAbove (j.succAbove (k.succAbove 1))))
                (c (i.succAbove (j.succAbove (k.succAbove 2)))), q} : Set ℂ) := by
  have G := Counter6.cx_genPosN
  refine ⟨Counter6.cx, fun i j h => (transversal_iff _ _).1 (G.1 i j h),
    fun i j k h1 h2 => ((genTriple_iff (G.1 i j (ne_of_lt h1)) (G.1 i k (ne_of_lt (h1.trans h2)))
      (G.1 j k (ne_of_lt h2))).1 (G.2 i j k h1 h2)).1, fun S hS => ?_⟩
  have hS' : ∀ a b, a ≠ b → S (Counter6.cx a) (Counter6.cx b) =
      second (Counter6.cx a) (Counter6.cx b) := fun a b hab => by
    obtain ⟨h1, h2, h3⟩ := hS a b hab
    exact l14b_second_eq (G.1 a b hab).ne h3 (Metric.mem_sphere.1 h1) (Metric.mem_sphere.1 h2)
  refine ⟨fun i j k h1 h2 => ?_, ?_⟩
  · rw [hS' _ _ (ne_of_lt h1), hS' _ _ (ne_of_lt (h1.trans h2)), hS' _ _ (ne_of_lt h2)]
    exact ((genTriple_iff (G.1 i j (ne_of_lt h1)) (G.1 i k (ne_of_lt (h1.trans h2)))
      (G.1 j k (ne_of_lt h2))).1 (G.2 i j k h1 h2)).2
  rintro ⟨p, hp⟩
  have key : ∀ σ : Fin 3 → Fin 6, Function.Injective σ → ∀ q : ℂ,
      Cospherical ({S (Counter6.cx (σ 0)) (Counter6.cx (σ 1)),
        S (Counter6.cx (σ 0)) (Counter6.cx (σ 2)), S (Counter6.cx (σ 1)) (Counter6.cx (σ 2)), q} :
          Set ℂ) →
      OnCircle3 (second (Counter6.cx (σ 0)) (Counter6.cx (σ 1)))
        (second (Counter6.cx (σ 0)) (Counter6.cx (σ 2)))
        (second (Counter6.cx (σ 1)) (Counter6.cx (σ 2))) q := by
    intro σ hσ q h
    rw [hS' _ _ (hσ.ne (by decide)), hS' _ _ (hσ.ne (by decide)),
      hS' _ _ (hσ.ne (by decide))] at h
    exact h
  apply Counter6.not_chain6 (X := {p})
  show ∃ p', ({p} : Set ℂ) = {p'} ∧
    ∀ i : Fin 6, ∃ Y, Chain 5 (Counter6.cx ∘ i.succAbove) Y ∧ p' ∈ Y
  refine ⟨p, rfl, fun i => ?_⟩
  obtain ⟨Y, hY, hpY, hq⟩ := hp i
  refine ⟨Y, ?_, hpY⟩
  show IsGCircle Y ∧ ∀ j : Fin 5, ∃ q, Chain 4 ((Counter6.cx ∘ i.succAbove) ∘ j.succAbove) {q} ∧
    q ∈ Y
  refine ⟨l14b_isGCircle hY, fun j => ?_⟩
  obtain ⟨q, hqY, hk⟩ := hq j
  refine ⟨q, ?_, hqY⟩
  show ∃ p', ({q} : Set ℂ) = {p'} ∧ ∀ k : Fin 4,
    ∃ Y', Chain 3 (((Counter6.cx ∘ i.succAbove) ∘ j.succAbove) ∘ k.succAbove) Y' ∧ p' ∈ Y'
  refine ⟨q, rfl, fun k => chain3_of _ q ?_⟩
  exact key (i.succAbove ∘ j.succAbove ∘ k.succAbove)
    (Fin.succAbove_right_injective.comp (Fin.succAbove_right_injective.comp
      Fin.succAbove_right_injective)) q (hk k)

/-- Non-vacuity of `l14_not_cliffordChain_six`: the hypothesis on `S` is satisfiable, by the
explicit formula `S a b = (conj a * b - a * conj b) / (conj a - conj b)`.
@isnad1 id=and.1h2v.s9.6837ba5f72e2 from=translated src=- shape=404e883f vocab=3122a02b
-/
theorem l14w_not_cliffordChain_six :
    ∀ i j : Fin 6, i ≠ j →
      (fun a b : ℂ => (conj a * b - a * conj b) / (conj a - conj b)) (Counter6.cx i) (Counter6.cx j)
          ∈ Metric.sphere (Counter6.cx i) ‖Counter6.cx i‖ ∧
      (fun a b : ℂ => (conj a * b - a * conj b) / (conj a - conj b)) (Counter6.cx i) (Counter6.cx j)
          ∈ Metric.sphere (Counter6.cx j) ‖Counter6.cx j‖ ∧
      (fun a b : ℂ => (conj a * b - a * conj b) / (conj a - conj b)) (Counter6.cx i) (Counter6.cx j)
          ≠ 0 := by
  intro i j h
  have G := Counter6.cx_genPosN
  exact ⟨(onCircleM_iff_mem_sphere _ _).1 (second_onCircleM_left (G.1 i j h).ne),
    (onCircleM_iff_mem_sphere _ _).1 (second_onCircleM_right (G.1 i j h).ne),
    second_ne_zero (G.1 i j h)⟩

end Clifford

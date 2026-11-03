import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.NestedReciprocalField
import Tengoku.Seed.LinearAlgebra.Dimension.Finite
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms fixed_iff_mem_invariantField` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedCoordinatesEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms invariantField_degree_two` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The fixed field of `T ↦ m/T`

For `Ω = Frac(B[T])`, put `s = T + m/T` and `E = B(s)`.  The elementary
quadratic relation `T² = sT-m` makes `Ω = E ⊕ E T`.  Conjugation then proves
that this two-term span is closed under inverses, and the nontrivial reciprocal
map kills the `T` coefficient of every fixed element.
-/

noncomputable section

namespace AlbertLean.Generic.NestedReciprocalField

open Polynomial

universe u

variable (B : Type u) [Field B]
variable (m : B) (hm : m ≠ 0)

abbrev σ : Omega B ≃+* Omega B := reciprocalEquiv B m hm

def S : Omega B := T B + algebraMap B (Omega B) m / T B

def invariantField : Subfield (Omega B) :=
  Subfield.closure (Set.range (algebraMap B (Omega B)) ∪ {S B m})

@[simp] theorem sigma_base (b : B) : σ B m hm (algebraMap B (Omega B) b) =
    algebraMap B (Omega B) b := reciprocalHom_base B m hm b

@[simp] theorem sigma_S : σ B m hm (S B m) = S B m := by
  simp only [S, map_add, map_div₀, sigma_base, reciprocalEquiv_T]
  rw [div_div_cancel₀ ((map_ne_zero (algebraMap B (Omega B))).mpr hm)]
  ac_rfl

theorem invariantField_fixed (x : Omega B) (hx : x ∈ invariantField B m) :
    σ B m hm x = x := by
  refine Subfield.closure_induction (p := fun x _ => σ B m hm x = x)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · rintro x (⟨b, rfl⟩ | hx)
    · exact sigma_base B m hm b
    · simpa only [Set.mem_singleton_iff.mp hx] using sigma_S B m hm
  · exact map_one _
  · intro x y _ _ hx hy; simpa only [map_add, hx, hy]
  · intro x _ hx; simpa only [map_neg, hx]
  · intro x _ hx; simpa only [map_inv₀, hx]
  · intro x y _ _ hx hy; simpa only [map_mul, hx, hy]

@[simp] theorem sigma_invariantField_coe (a : invariantField B m) :
    σ B m hm (a : Omega B) = a :=
  invariantField_fixed B m hm a a.property

theorem T_quadratic :
    T B ^ 2 = S B m * T B - algebraMap B (Omega B) m := by
  rw [S]
  field_simp [T_ne_zero B]
  ring

theorem sigma_T_sub : σ B m hm (T B) = S B m - T B := by
  rw [reciprocalEquiv_T, S]
  ring

theorem sigma_T_ne_T : σ B m hm (T B) ≠ T B := by
  intro h
  rw [reciprocalEquiv_T] at h
  field_simp [T_ne_zero B] at h
  apply branchPolynomial_ne_zero B m
  exact sub_eq_zero.mpr h.symm

/-- Elements having an `E + E*T` expression.  This is packaged as a subfield;
the inverse formula uses `(a+bT)⁻¹ = (a+b(S-T))/(a²+abS+b²m)`.-/
def quadraticSpan : Subfield (Omega B) where
  carrier := {x | ∃ a b : invariantField B m,
    x = (a : Omega B) + (b : Omega B) * T B}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a+c, b+d, by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨a,b,rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  mul_mem' := by
    rintro x y ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a*c - b*d*⟨algebraMap B (Omega B) m,
        Subfield.subset_closure (Or.inl ⟨m,rfl⟩)⟩,
      a*d+b*c+b*d*⟨S B m, Subfield.subset_closure
        (Or.inr (Set.mem_singleton _))⟩, ?_⟩
    push_cast
    linear_combination (b : Omega B) * (d : Omega B) * T_quadratic B m
  inv_mem' := by
    rintro x ⟨a,b,rfl⟩
    let c : invariantField B m := a + b * ⟨S B m,
      Subfield.subset_closure (Or.inr (Set.mem_singleton _))⟩
    let n : invariantField B m := a*c + b*b*⟨algebraMap B (Omega B) m,
      Subfield.subset_closure (Or.inl ⟨m,rfl⟩)⟩
    by_cases hx : (a : Omega B) + (b : Omega B) * T B = 0
    · exact ⟨0,0, by simp [hx]⟩
    · have hn : n ≠ 0 := by
        intro hn0
        have hc : (a : Omega B) + (b : Omega B) * (S B m - T B) = 0 := by
          have : ((a : Omega B) + (b : Omega B) * T B) *
              ((a : Omega B) + (b : Omega B) * (S B m - T B)) = (n : Omega B) := by
            dsimp [n, c]
            push_cast
            linear_combination -(b : Omega B) ^ 2 * T_quadratic B m
          have hnOmega : (n : Omega B) = 0 := congrArg Subtype.val hn0
          exact (mul_eq_zero.mp (this.trans hnOmega)).resolve_left hx
        have := congrArg (σ B m hm) hc
        simp only [map_add, map_sub, map_mul, map_zero,
          sigma_invariantField_coe B m hm, sigma_S B m hm,
          sigma_T_sub B m hm] at this
        exact hx (by linear_combination this)
      refine ⟨c / n, -b / n, ?_⟩
      have hnOmega : (n : Omega B) ≠ 0 := by
        intro h
        exact hn (Subtype.ext h)
      have hprod : ((a : Omega B) + (b : Omega B) * T B) *
          ((c : Omega B) - (b : Omega B) * T B) = (n : Omega B) := by
        dsimp [n, c]
        push_cast
        linear_combination -(b : Omega B) ^ 2 * T_quadratic B m
      have hi : ((a : Omega B) + (b : Omega B) * T B)⁻¹ =
          ((c : Omega B) - (b : Omega B) * T B) / (n : Omega B) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_div_assoc, hprod, div_self hnOmega]
      rw [hi]
      push_cast
      ring

theorem polynomialMap_mem_quadraticSpan (p : Polynomial B) :
    algebraMap (Polynomial B) (Omega B) p ∈ quadraticSpan B m hm := by
  rw [← evalT_eq_algebraMap B]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using Subfield.add_mem _ hp hq
  | monomial n b =>
      change (Polynomial.monomial n b).eval₂ (algebraMap B (Omega B)) (T B) ∈ _
      rw [eval₂_monomial]
      apply Subfield.mul_mem
      · exact ⟨⟨algebraMap B (Omega B) b,
          Subfield.subset_closure (Or.inl ⟨b,rfl⟩)⟩, 0, by simp⟩
      · exact (quadraticSpan B m hm).pow_mem
          (show T B ∈ quadraticSpan B m hm from ⟨0,1,by simp⟩) n

theorem quadraticSpan_eq_top : quadraticSpan B m hm = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨p,q,hq,rfl⟩ := IsFractionRing.div_surjective (Polynomial B) x
  apply Subfield.div_mem
  · exact polynomialMap_mem_quadraticSpan B m hm p
  · exact polynomialMap_mem_quadraticSpan B m hm q

include hm in theorem exists_two_coefficients (x : Omega B) :
    ∃ a b : invariantField B m,
      x = (a : Omega B) + (b : Omega B) * T B := by
  have hx : x ∈ quadraticSpan B m hm := by rw [quadraticSpan_eq_top B m hm]; trivial
  exact hx

include hm in theorem unique_two_coefficients (x : Omega B) :
    ∃! ab : invariantField B m × invariantField B m,
      x = (ab.1 : Omega B) + (ab.2 : Omega B) * T B := by
  obtain ⟨a,b,h⟩ := exists_two_coefficients B m hm x
  refine ⟨(a,b),h,?_⟩
  rintro ⟨c,d⟩ hcd
  have he : ((a-c : invariantField B m) : Omega B) +
      ((b-d : invariantField B m) : Omega B) * T B = 0 := by
    push_cast
    linear_combination hcd - h
  have hσ := congrArg (σ B m hm) he
  simp only [map_add, map_sub, map_mul, map_zero,
    sigma_invariantField_coe B m hm, sigma_T_sub B m hm] at hσ
  have hb : b = d := by
    apply Subtype.ext
    have hz : (((b-d : invariantField B m) : Omega B) *
        (σ B m hm (T B) - T B)) = 0 := by
      rw [sigma_T_sub B m hm]
      linear_combination hσ - he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr
      (sigma_T_ne_T B m hm)))
  have ha : a = c := by
    apply Subtype.ext
    rw [hb] at he
    exact sub_eq_zero.mp (by simpa using he)
  exact Prod.ext ha.symm hb.symm

/-- Exact fixed-field identification, with no assumed fixed-field premise.-/
theorem fixed_iff_mem_invariantField (x : Omega B) :
    σ B m hm x = x ↔ x ∈ invariantField B m := by
  constructor
  · intro hx
    obtain ⟨a,b,h⟩ := exists_two_coefficients B m hm x
    have hσ := congrArg (σ B m hm) h
    simp only [map_add, map_mul, sigma_invariantField_coe B m hm,
      sigma_T_sub B m hm, hx] at hσ
    have hb : b = 0 := by
      apply Subtype.ext
      have hz : ((b : Omega B) * (σ B m hm (T B) - T B)) = 0 := by
        rw [sigma_T_sub B m hm]
        linear_combination h - hσ
      exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr
        (sigma_T_ne_T B m hm))
    rw [h, hb]
    simpa using a.property
  · intro hx
    exact invariantField_fixed B m hm x hx

/-- The coefficient map for the normal form `a+bT`.-/
def fixedCoordinates :
    (invariantField B m × invariantField B m) →ₗ[invariantField B m] Omega B where
  toFun ab := (ab.1 : Omega B) + (ab.2 : Omega B) * T B
  map_add' x y := by
    change (((x.1 + y.1 : invariantField B m) : Omega B) +
      ((x.2 + y.2 : invariantField B m) : Omega B) * T B) =
      ((x.1 : Omega B) + (x.2 : Omega B) * T B) +
      ((y.1 : Omega B) + (y.2 : Omega B) * T B)
    push_cast
    ring
  map_smul' r x := by
    change (((r * x.1 : invariantField B m) : Omega B) +
      ((r * x.2 : invariantField B m) : Omega B) * T B) =
      (r : Omega B) * ((x.1 : Omega B) + (x.2 : Omega B) * T B)
    push_cast
    ring

include hm in theorem fixedCoordinates_bijective :
    Function.Bijective (fixedCoordinates B m) := by
  constructor
  · intro x y hxy
    have hu := unique_two_coefficients B m hm (fixedCoordinates B m x)
    exact hu.unique rfl hxy
  · intro x
    obtain ⟨a,b,h⟩ := exists_two_coefficients B m hm x
    exact ⟨(a,b), h.symm⟩

def fixedCoordinatesEquiv (hm : m ≠ 0) :
    (invariantField B m × invariantField B m) ≃ₗ[invariantField B m] Omega B :=
  LinearEquiv.ofBijective (fixedCoordinates B m) (fixedCoordinates_bijective B m hm)

theorem invariantField_degree_two (hm : m ≠ 0) :
    Module.finrank (invariantField B m) (Omega B) = 2 := by
  rw [← (fixedCoordinatesEquiv B m hm).finrank_eq]
  simp

end AlbertLean.Generic.NestedReciprocalField

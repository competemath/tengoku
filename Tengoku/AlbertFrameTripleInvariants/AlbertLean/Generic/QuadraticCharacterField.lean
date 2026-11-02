import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuadraticCharacterFixedSpace
import Tengoku.Seed.Algebra.Field.Subfield.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms fixedField_finrank` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedField_finiteDimensional` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedField_generated_by_u` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms radicand_not_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms generator_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms radicand_factorization` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deck_generator` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deck_fixed_iff` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Field packaging of the verified character decomposition.
The only additional import is the cached elementary Subfield API.
This is the generic-point algebra of the product of two quadratic directions:
tau reverses both chosen roots and fixes u; delta reverses u. No scheme torsor,
chart coverage, or actual Albert ledger-field equality is asserted here.
-/
noncomputable section
namespace AlbertLean.Generic.QuadraticCharacterDescent.Data

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω]
variable (D : QuadraticCharacterDescent.Data (k := k) (Ω := Ω))

/-- Actual subfield of tau-fixed elements of the ambient field.-/
def fixedField : Subfield Ω :=
  (D.tau : Ω →+* Ω).eqLocusField (RingHom.id Ω)

@[simp] theorem mem_fixedField (x : Ω) : x ∈ D.fixedField ↔ D.tau x = x := Iff.rfl

/-- The base field maps into the fixed field because tau is a k-algebra map.-/
def baseToFixed : k →+* D.fixedField where
  toFun a := ⟨algebraMap k Ω a, D.tau.commutes a⟩
  map_zero' := Subtype.ext (map_zero (algebraMap k Ω))
  map_one' := Subtype.ext (map_one (algebraMap k Ω))
  map_add' a b := Subtype.ext (map_add (algebraMap k Ω) a b)
  map_mul' a b := Subtype.ext (map_mul (algebraMap k Ω) a b)

instance fixedFieldAlgebra : Algebra k D.fixedField := D.baseToFixed.toAlgebra

/-- The field and the already verified fixed submodule have the same scalar
structure; the map is the identity on ambient elements.-/
def fixedFieldEquivSpace : D.fixedField ≃ₗ[k] D.fixedSpace where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := by
    apply Subtype.ext
    change algebraMap k Ω r * (x : Ω) = r • (x : Ω)
    exact (Algebra.smul_def r (x : Ω)).symm

/-- The degree statement now concerns an actual field extension.-/
theorem fixedField_finrank : Module.finrank k D.fixedField = 2 := by
  rw [D.fixedFieldEquivSpace.finrank_eq, D.fixedSpace_finrank]

theorem fixedField_finiteDimensional : FiniteDimensional k D.fixedField := by
  exact Module.finite_of_finrank_pos (by rw [D.fixedField_finrank]; decide)

/-- Explicit field generation, expressed using cached Subfield.closure.-/
theorem fixedField_generated_by_u :
    Subfield.closure (Set.range (algebraMap k Ω) ∪ {D.u}) = D.fixedField := by
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    intro x hx
    rcases hx with ⟨a,rfl⟩ | hx
    · exact D.tau.commutes a
    · have hx' : x = D.u := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact D.tau_u
  · intro x hx
    obtain ⟨a,d,h⟩ := (D.tau_fixed_iff x).mp hx
    rw [h]
    apply Subfield.add_mem
    · exact Subfield.subset_closure (Or.inl ⟨a,rfl⟩)
    · apply Subfield.mul_mem
      · exact Subfield.subset_closure (Or.inl ⟨d,rfl⟩)
      · exact Subfield.subset_closure (Or.inr (Set.mem_singleton _))

private theorem u_sq_in_base : ∃ r : k, algebraMap k Ω r = D.u ^ 2 := by
  apply (D.joint_fixed (D.u ^ 2)).mp
  constructor <;> simp [map_pow, D.tau_u, D.delta_u]

/-- The chosen sheet generator determines a base-field radicand.-/
def radicand : k := Classical.choose D.u_sq_in_base

theorem radicand_spec : algebraMap k Ω D.radicand = D.u ^ 2 :=
  Classical.choose_spec D.u_sq_in_base

/-- The product class is nontrivial because the actual deck map reverses a
nonzero generator. Nontriviality is proved, not inferred from a class formula.-/
theorem radicand_not_square : ¬ IsSquare D.radicand := by
  rintro ⟨a,ha⟩
  have hs : (algebraMap k Ω a) ^ 2 = D.u ^ 2 := by
    rw [← D.radicand_spec, ha, map_mul, pow_two]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact D.u_not_base ⟨a,h⟩
  · apply D.u_not_base
    refine ⟨-a,?_⟩
    rw [map_neg, h, neg_neg]

/-- The equation lives inside the actual fixed field.-/
def generator : D.fixedField := ⟨D.u,D.tau_u⟩

theorem generator_square : D.generator ^ 2 = algebraMap k D.fixedField D.radicand := by
  apply Subtype.ext
  change D.u ^ 2 = algebraMap k Ω D.radicand
  exact D.radicand_spec.symm

/-- Delta restricts to an actual algebra automorphism of the tau-fixed field.
It is the surviving deck operation; tau itself fixes this field pointwise.-/
def deck : D.fixedField ≃ₐ[k] D.fixedField where
  toFun x := ⟨D.delta x.val, by
    change D.tau (D.delta x.val) = D.delta x.val
    rw [D.commute x.val]
    exact congrArg D.delta (show D.tau x.val = x.val from x.property)⟩
  invFun x := ⟨D.delta x.val, by
    change D.tau (D.delta x.val) = D.delta x.val
    rw [D.commute x.val]
    exact congrArg D.delta (show D.tau x.val = x.val from x.property)⟩
  left_inv x := Subtype.ext (D.delta_involutive x.val)
  right_inv x := Subtype.ext (D.delta_involutive x.val)
  map_add' x y := Subtype.ext (map_add D.delta x.val y.val)
  map_mul' x y := Subtype.ext (map_mul D.delta x.val y.val)
  commutes' a := Subtype.ext (D.delta.commutes a)

theorem deck_generator : D.deck D.generator = -D.generator :=
  Subtype.ext D.delta_u

/-- Exact base fixed-field equality for the restricted deck operation.-/
theorem deck_fixed_iff (x : D.fixedField) : D.deck x = x ↔
    ∃ a : k, algebraMap k D.fixedField a = x := by
  constructor
  · intro hx
    have hδ : D.delta x.val = x.val := congrArg Subtype.val hx
    obtain ⟨a,ha⟩ := (D.joint_fixed x.val).mp ⟨x.property,hδ⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,rfl⟩
    exact D.deck.commutes a

/-- At the generic point the two chosen quadratic directions multiply:
kappa^2=a, eta^2=b, u^2=ab. The preceding theorem supplies nontriviality
of this product; no freeness of an odd line on an entire base scheme follows.-/
theorem radicand_factorization : ∃ a b : k,
    algebraMap k Ω a = D.kappa ^ 2 ∧
    algebraMap k Ω b = D.eta ^ 2 ∧ D.radicand = a * b := by
  have hk : ∃ a : k, algebraMap k Ω a = D.kappa ^ 2 := by
    apply (D.joint_fixed _).mp
    constructor <;> simp [map_pow, D.tau_kappa, D.delta_kappa]
  have he : ∃ b : k, algebraMap k Ω b = D.eta ^ 2 := by
    apply (D.joint_fixed _).mp
    constructor <;> simp [map_pow, D.tau_eta, D.delta_eta]
  obtain ⟨a,ha⟩ := hk
  obtain ⟨b,hb⟩ := he
  refine ⟨a,b,ha,hb,?_⟩
  apply (algebraMap k Ω).injective
  rw [D.radicand_spec, map_mul, ha, hb, u, mul_pow]

end AlbertLean.Generic.QuadraticCharacterDescent.Data

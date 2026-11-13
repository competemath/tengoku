/-
# The convolution algebra of a cooperad and an operad

Given a cooperad `C` and an operad `P`, the *convolution algebra* is the collection of degreewise
linear maps

`Conv R C P = ∀ n, C n →ₗ[R] P n`,

with the product that decomposes in `C`, applies the two maps, and recomposes in `P`. It is the
object the rest of the library's deformation theory is about: `PreLie` proves that the total space
of an operad is pre-Lie, `GradedPreLie` and `TotalSpaceS` carry the suspension signs, and
`Cohomology` computes with a differential `[Θ, −]`. This file builds the ungraded convolution
algebra. It carries no suspension signs and no differential, so its Maurer–Cartan elements are
*not* twisting morphisms. Twisting morphisms `C → P` live on the graded convolution operad
`ConvOp` (`Operad.ConvOperad`, `Operad.Twisting`, `Operad.TwistingDG`).

## The product

In the positional convention a decomposition of `m` is a triple `m = a + n + b`, and the
contribution of that triple to `f ⋆ g` is

`C m ≃ C (a+n+b) --decomp--> C (a+1+b) ⊗ C n --f ⊗ g--> P (a+1+b) ⊗ P n --comp--> P (a+n+b) ≃ P m`.

`f ⋆ g` is the sum over all such triples.

The sum is taken over `range (m+1)` three times, with `convTerm` defined to be `0` unless the
triple is a decomposition of `m`. This is deliberate: the honest index set is the subtype of
triples summing to `m`, but carrying that subtype would put the equation inside the type, and the
library's standing lesson is to keep index data out of types — the `dite` puts it in a hypothesis
instead, where `omega` can reach it. Every triple that contributes has each entry at most `m`, so
nothing is lost.

## What is here, and what is next

Here: the algebra, the product, its bilinearity in both arguments, the bracket and its
antisymmetry, and an encoding check — for `C = P = Ass` the term of a decomposition is computed in
closed form, which a mis-ordered composite would fail.

**The pre-Lie identity is proved in `Operad.ConvolutionPreLie`**, which also makes `ConvAlg` a
Lie algebra. The plan it followed, as first written here: The route is
the one `PreLie.lean` already walks. The associator of `⋆` splits into a nested part and a disjoint
part; the nested part cancels by `decomp_assoc_seq` against `comp_assoc_seq`, and the disjoint part
is symmetric in the last two arguments by `decomp_assoc_par` against `comp_assoc_par`. The one new
difficulty is that the cooperad axioms are equalities of *linear maps* rather than of elements, so
the bookkeeping cannot be done pointwise; `swapLast` is what the parallel case will need.
-/
import Tengoku.LeanOperads.Operad.Basic
import Tengoku.LeanOperads.Operad.Cooperad
import Tengoku.Seed.LinearAlgebra.TensorProduct.Map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

open scoped TensorProduct

section Convolution

variable {R : Type u} [CommRing R]
variable {C : ℕ → Type v} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [NSCooperad R C]
variable {P : ℕ → Type w} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- **The convolution algebra**: degreewise linear maps from the cooperad to the operad.

An `abbrev`, so that the `Pi` module structure and every `rw` about it transfer without an
instance mismatch — the same reason `Free` is one.-/
abbrev Conv (R : Type u) [CommRing R] (C : ℕ → Type v) (P : ℕ → Type w)
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] : Type (max v w) :=
  ∀ n, C n →ₗ[R] P n

namespace Conv

/-- Partial composition, as a map out of the tensor product.  This is the only thing the operad
side contributes to the convolution product.-/
noncomputable def compT (a b : ℕ) {n : ℕ} :
    P (a + 1 + b) ⊗[R] P n →ₗ[R] P (a + n + b) :=
  TensorProduct.lift (NSOperad.comp a b)

/--
@isnad1 id=eq.0h7v.s11.c6fcf982c81c from=translated src=- shape=a9aa3457 vocab=9c66e969
-/
@[simp] lemma compT_tmul (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    compT (R := R) a b (α ⊗ₜ[R] β) = NSOperad.comp (R := R) a b α β := rfl

/-- The contribution of one decomposition `m = a + n + b` to the convolution product: decompose in
`C`, apply `f` to the outer part and `g` to the inner one, recompose in `P`.  Zero if the triple is
not a decomposition of `m`.-/
noncomputable def convTerm (f g : Conv R C P) (m a n b : ℕ) : C m →ₗ[R] P m :=
  if h : a + n + b = m then
    (reindex R P h).toLinearMap ∘ₗ compT a b ∘ₗ
      TensorProduct.map (f (a + 1 + b)) (g n) ∘ₗ NSCooperad.decomp a b n ∘ₗ
      (reindex R C h.symm).toLinearMap
  else 0

/--
@isnad1 id=eq.1h9v.s8.5146c6d2979f from=translated src=- shape=9fd17098 vocab=e77e9317
-/
lemma convTerm_of_ne (f g : Conv R C P) {m a n b : ℕ} (h : a + n + b ≠ m) :
    convTerm f g m a n b = 0 := dite_eq_right h

/--
@isnad1 id=eq.1h9v.s11.b414b0998441 from=translated src=- shape=4bf30196 vocab=4f21dacb
-/
lemma convTerm_of_eq (f g : Conv R C P) {m a n b : ℕ} (h : a + n + b = m) :
    convTerm f g m a n b
      = (reindex R P h).toLinearMap ∘ₗ compT a b ∘ₗ
          TensorProduct.map (f (a + 1 + b)) (g n) ∘ₗ NSCooperad.decomp a b n ∘ₗ
          (reindex R C h.symm).toLinearMap := dite_eq_left h

/-- **The convolution product.**  Sum over all decompositions of the arity.-/
noncomputable def star (f g : Conv R C P) : Conv R C P := fun m =>
  ∑ a ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
    convTerm f g m a n b

@[inherit_doc] scoped infixl:70 " ⋆c " => star

/--
@isnad1 id=eq.0h6v.s9.bd1c8858d6eb from=translated src=- shape=930ce885 vocab=1e181ecb
-/
lemma star_apply (f g : Conv R C P) (m : ℕ) :
    (f ⋆c g) m = ∑ a ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1),
      ∑ b ∈ Finset.range (m + 1), convTerm f g m a n b := rfl

/-! ## Bilinearity

Each of the four laws holds termwise, because `TensorProduct.map` is bilinear in its two
arguments and everything else in `convTerm` is a fixed composite. -/

/--
@isnad1 id=eq.0h10v.s9.f0fc6c3ba96c from=translated src=- shape=cbd99b9c vocab=e77e9317
-/
lemma convTerm_add_left (f₁ f₂ g : Conv R C P) (m a n b : ℕ) :
    convTerm (f₁ + f₂) g m a n b = convTerm f₁ g m a n b + convTerm f₂ g m a n b := by
  by_cases h : a + n + b = m
  · rw [convTerm_of_eq _ _ h, convTerm_of_eq _ _ h, convTerm_of_eq _ _ h]
    show _ = _
    rw [show (f₁ + f₂) (a + 1 + b) = f₁ (a + 1 + b) + f₂ (a + 1 + b) from rfl,
      TensorProduct.map_add_left]
    ext x
    simp [LinearMap.add_comp, LinearMap.comp_add]
  · rw [convTerm_of_ne _ _ h, convTerm_of_ne _ _ h, convTerm_of_ne _ _ h, add_zero]

/--
@isnad1 id=eq.0h10v.s9.5863ab57d12b from=translated src=- shape=b16f7b4b vocab=e77e9317
-/
lemma convTerm_add_right (f g₁ g₂ : Conv R C P) (m a n b : ℕ) :
    convTerm f (g₁ + g₂) m a n b = convTerm f g₁ m a n b + convTerm f g₂ m a n b := by
  by_cases h : a + n + b = m
  · rw [convTerm_of_eq _ _ h, convTerm_of_eq _ _ h, convTerm_of_eq _ _ h]
    rw [show (g₁ + g₂) n = g₁ n + g₂ n from rfl, TensorProduct.map_add_right]
    ext x
    simp [LinearMap.add_comp, LinearMap.comp_add]
  · rw [convTerm_of_ne _ _ h, convTerm_of_ne _ _ h, convTerm_of_ne _ _ h, add_zero]

/--
@isnad1 id=eq.0h10v.s9.bcfcfd834032 from=translated src=- shape=6d204eb5 vocab=6e40127e
-/
lemma convTerm_smul_left (r : R) (f g : Conv R C P) (m a n b : ℕ) :
    convTerm (r • f) g m a n b = r • convTerm f g m a n b := by
  by_cases h : a + n + b = m
  · rw [convTerm_of_eq _ _ h, convTerm_of_eq _ _ h]
    rw [show (r • f) (a + 1 + b) = r • f (a + 1 + b) from rfl, TensorProduct.map_smul_left]
    ext x
    simp [LinearMap.smul_comp, LinearMap.comp_smul]
  · rw [convTerm_of_ne _ _ h, convTerm_of_ne _ _ h, smul_zero]

/--
@isnad1 id=eq.0h10v.s9.31e67dca8720 from=translated src=- shape=8727dd62 vocab=6e40127e
-/
lemma convTerm_smul_right (r : R) (f g : Conv R C P) (m a n b : ℕ) :
    convTerm f (r • g) m a n b = r • convTerm f g m a n b := by
  by_cases h : a + n + b = m
  · rw [convTerm_of_eq _ _ h, convTerm_of_eq _ _ h]
    rw [show (r • g) n = r • g n from rfl, TensorProduct.map_smul_right]
    ext x
    simp [LinearMap.smul_comp, LinearMap.comp_smul]
  · rw [convTerm_of_ne _ _ h, convTerm_of_ne _ _ h, smul_zero]

/--
@isnad1 id=eq.0h6v.s8.309199d6a1a8 from=translated src=- shape=7b332932 vocab=fcd29fcf
-/
theorem star_add_left (f₁ f₂ g : Conv R C P) : (f₁ + f₂) ⋆c g = f₁ ⋆c g + f₂ ⋆c g := by
  funext m
  simp only [star_apply, convTerm_add_left, Finset.sum_add_distrib]
  rfl

/--
@isnad1 id=eq.0h6v.s8.e512e213615e from=translated src=- shape=860ce9dc vocab=fcd29fcf
-/
theorem star_add_right (f g₁ g₂ : Conv R C P) : f ⋆c (g₁ + g₂) = f ⋆c g₁ + f ⋆c g₂ := by
  funext m
  simp only [star_apply, convTerm_add_right, Finset.sum_add_distrib]
  rfl

omit [NSCooperad R C] [NSOperad R P] in
/-- Pulling a scalar out of a sum of degreewise maps.  `Finset.smul_sum` is stated for
`DistribSMul` and will not match a `Module` action here, so the library's standing idiom is to go
through `LinearMap.lsmul`.-/
private lemma smul_sum_conv (r : R) (m : ℕ) (s : Finset ℕ) (F : ℕ → (C m →ₗ[R] P m)) :
    r • (∑ i ∈ s, F i) = ∑ i ∈ s, r • F i :=
  map_sum (LinearMap.lsmul R (C m →ₗ[R] P m) r) F s

/--
@isnad1 id=eq.0h6v.s8.093307111544 from=translated src=- shape=62b0754f vocab=7ee75bd5
-/
theorem star_smul_left (r : R) (f g : Conv R C P) : (r • f) ⋆c g = r • (f ⋆c g) := by
  funext m
  show ∑ a ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
      convTerm (r • f) g m a n b
    = r • (∑ a ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1),
        ∑ b ∈ Finset.range (m + 1), convTerm f g m a n b)
  rw [smul_sum_conv]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_sum_conv]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_sum_conv]
  exact Finset.sum_congr rfl fun b _ => convTerm_smul_left r f g m a n b

/--
@isnad1 id=eq.0h6v.s8.a10d6250f879 from=translated src=- shape=320332ce vocab=7ee75bd5
-/
theorem star_smul_right (r : R) (f g : Conv R C P) : f ⋆c (r • g) = r • (f ⋆c g) := by
  funext m
  show ∑ a ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
      convTerm f (r • g) m a n b
    = r • (∑ a ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 1),
        ∑ b ∈ Finset.range (m + 1), convTerm f g m a n b)
  rw [smul_sum_conv]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_sum_conv]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_sum_conv]
  exact Finset.sum_congr rfl fun b _ => convTerm_smul_right r f g m a n b

/--
@isnad1 id=eq.0h4v.s8.f943f50652f5 from=translated src=- shape=340f4c67 vocab=22a51322
-/
@[simp] theorem star_zero_left (g : Conv R C P) : (0 : Conv R C P) ⋆c g = 0 := by
  have h := star_smul_left (0 : R) (0 : Conv R C P) g
  rwa [zero_smul, zero_smul] at h

/--
@isnad1 id=eq.0h4v.s8.ec5d63236fd0 from=translated src=- shape=47a1c8f7 vocab=22a51322
-/
@[simp] theorem star_zero_right (f : Conv R C P) : f ⋆c (0 : Conv R C P) = 0 := by
  have h := star_smul_right (0 : R) f 0
  rwa [zero_smul, zero_smul] at h

/-! ## The bracket -/

/-- The commutator of the convolution product.  Once the pre-Lie identity is proved this is a Lie
bracket; for now it is the antisymmetrisation.-/
noncomputable def bracket (f g : Conv R C P) : Conv R C P := f ⋆c g - g ⋆c f

/--
@isnad1 id=eq.0h5v.s7.b5e796f93683 from=translated src=- shape=abf6edb7 vocab=0609aab6
-/
theorem bracket_antisymm (f g : Conv R C P) : bracket f g = - bracket g f := by
  rw [bracket, bracket, neg_sub]

/--
@isnad1 id=eq.0h4v.s7.e0ce6d9e0c2e from=translated src=- shape=23145056 vocab=99a1c326
-/
@[simp] theorem bracket_self (f : Conv R C P) : bracket f f = 0 := by
  rw [bracket, sub_self]

/--
@isnad1 id=eq.0h6v.s8.d5edccdc336c from=translated src=- shape=7b332932 vocab=53a97db9
-/
theorem bracket_add_left (f₁ f₂ g : Conv R C P) :
    bracket (f₁ + f₂) g = bracket f₁ g + bracket f₂ g := by
  rw [bracket, bracket, bracket, star_add_left, star_add_right]
  abel

/--
@isnad1 id=eq.0h6v.s8.3687c6fb0c05 from=translated src=- shape=860ce9dc vocab=53a97db9
-/
theorem bracket_add_right (f g₁ g₂ : Conv R C P) :
    bracket f (g₁ + g₂) = bracket f g₁ + bracket f g₂ := by
  rw [bracket, bracket, bracket, star_add_left, star_add_right]
  abel

end Conv

end Convolution

/-! ## The encoding check

`convTerm` is a composite of five maps, and a wrong order or a transposed tensor factor would
still typecheck.  For `C = P = Ass` every piece is explicit — the decomposition is `r ↦ r ⊗ 1`,
composition is multiplication, and reindexing is the identity — so the term can be computed in
closed form, and only the intended composite gives this answer. -/

namespace Conv

section AssCheck

variable {R : Type u} [CommRing R]

/-- In the associative case the contribution of a decomposition is the outer map applied to the
argument, times the inner map at the unit.
@isnad1 id=eq.1h8v.s10.aaf561a4d141 from=translated src=- shape=c2c6299a vocab=64630b1e
-/
theorem convTerm_ass (f g : Conv R (Ass R) (Ass R)) {m a n b : ℕ} (h : a + n + b = m) (x : R) :
    convTerm f g m a n b x = f (a + 1 + b) x * g n 1 := by
  rw [convTerm_of_eq _ _ h]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, reindex_ass]
  show compT a b (TensorProduct.map (f (a + 1 + b)) (g n) ((TensorProduct.rid R R).symm x)) = _
  rw [TensorProduct.rid_symm_apply, TensorProduct.map_tmul, compT_tmul]
  rfl

end AssCheck

end Conv

end Operad

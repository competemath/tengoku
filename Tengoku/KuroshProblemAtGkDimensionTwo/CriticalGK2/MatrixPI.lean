import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A universal matrix polynomial identity

The alternating product of more than `k * k` matrices vanishes over every
commutative coefficient ring. The proof uses the standard matrix basis
and a pigeonhole argument.
-/

namespace CriticalGK2

open scoped BigOperators

/-- The ordinary noncommutative alternating product, bundled as an alternating map.-/
noncomputable def alternatingProduct (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] (p : ℕ) : AlternatingMap R A A (Fin p) :=
  (MultilinearMap.mkPiAlgebraFin R p A).alternatization

/-- Every alternating map on `p > k²` matrix arguments vanishes.

`Matrix.stdBasis` has the index type `Fin k × Fin k`.  An injective family of
`p` different basis elements would force `p ≤ k²`, contradicting the hypothesis.
@isnad1 id=eq.1h4v.s9.f7405feae9cc from=translated src=- shape=f737d56d vocab=b92b3232
-/
theorem alternating_matrix_map_eq_zero (R : Type*) [CommRing R]
    (k p : ℕ) (hp : k * k < p)
    (f : AlternatingMap R (Matrix (Fin k) (Fin k) R)
      (Matrix (Fin k) (Fin k) R) (Fin p)) : f = 0 := by
  classical
  apply (Matrix.stdBasis R (Fin k) (Fin k)).ext_alternating
  intro v hv
  have hcard := Fintype.card_le_of_injective v hv
  simp only [Fintype.card_fin, Fintype.card_prod] at hcard
  omega

/-- The signed product sum is zero over an arbitrary commutative ring.

The result includes characteristic two and rings with zero divisors.
@isnad1 id=eq.1h4v.s8.5a88382713ef from=translated src=- shape=5b3c3af1 vocab=125a8e9f
-/
theorem matrix_alternating_product_eq_zero (R : Type*) [CommRing R]
    (k p : ℕ) (hp : k * k < p)
    (v : Fin p → Matrix (Fin k) (Fin k) R) :
    alternatingProduct R (Matrix (Fin k) (Fin k) R) p v = 0 := by
  have hf := alternating_matrix_map_eq_zero R k p hp
    (alternatingProduct R (Matrix (Fin k) (Fin k) R) p)
  exact congrArg (fun g => g v) hf

/-- A length-`p` binary codeword for `i`, with its unique `true` bit at `i`.

Each codeword has length `p`. The resulting polynomial degree depends
only on `p`, as required by sparse scheduling.-/
def oneHotCode (p : ℕ) (i : Fin p) : List Bool :=
  List.ofFn fun j : Fin p => decide (j = i)

/--
@isnad1 id=eq.0h2v.s3.a06c745d99f3 from=translated src=- shape=37d26c04 vocab=689997ea
-/
@[simp]
theorem oneHotCode_length (p : ℕ) (i : Fin p) : (oneHotCode p i).length = p := by
  simp [oneHotCode]

/--
@isnad1 id=injectiv.0h1v.s3.82f46301fa07 from=translated src=- shape=995c1cb5 vocab=4273ffff
-/
theorem oneHotCode_injective (p : ℕ) : Function.Injective (oneHotCode p) := by
  intro i j h
  change List.ofFn (fun a : Fin p => decide (a = i)) =
    List.ofFn (fun a : Fin p => decide (a = j)) at h
  have hi : decide (i = j) = true := by
    simpa using (congrFun (List.ofFn_injective h) i).symm
  exact of_decide_eq_true hi

/-- A positive fixed-length injective code induces an injective encoding of lists.
@isnad1 id=injectiv.3h4v.s5.e063bb7468cb from=translated src=- shape=04f37351 vocab=052775a9
-/
theorem fixedLength_flatMap_injective {ι α : Type*} (code : ι → List α)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hlen : ∀ i, (code i).length = ℓ)
    (hinj : Function.Injective code) : Function.Injective (fun l : List ι => l.flatMap code) := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons b bs =>
          have hl := congrArg List.length h
          simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
            List.length_append, hlen] at hl
          omega
  | cons a as ih =>
      intro l' h
      cases l' with
      | nil =>
          have hl := congrArg List.length h
          simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
            List.length_append, hlen] at hl
          omega
      | cons b bs =>
          have hhead : code a = code b := by
            have ht := congrArg (List.take ℓ) h
            simpa only [List.flatMap_cons, List.take_left' (hlen a),
              List.take_left' (hlen b)] using ht
          have hab := hinj hhead
          subst b
          have htail : as.flatMap code = bs.flatMap code := by
            apply List.append_cancel_left
            simpa only [List.flatMap_cons] using h
          exact congrArg (List.cons a) (ih htail)

/-- The binary word associated to a permutation of the coded variables.-/
def encodedPermutation (p : ℕ) (σ : Equiv.Perm (Fin p)) : FreeMonoid Bool :=
  FreeMonoid.ofList ((List.ofFn fun i => σ i).flatMap (oneHotCode p))

/-- Different permutations yield different binary words, by fixed-length decoding.
@isnad1 id=injectiv.1h1v.s4.0e9ba309ffe0 from=translated src=- shape=aa6bc867 vocab=e1501a9d
-/
theorem encodedPermutation_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (encodedPermutation p) := by
  intro σ τ h
  have hlist : (List.ofFn fun i => σ i).flatMap (oneHotCode p) =
      (List.ofFn fun i => τ i).flatMap (oneHotCode p) :=
    congrArg FreeMonoid.toList h
  have hfn := List.ofFn_injective
    (fixedLength_flatMap_injective (oneHotCode p) p hp
      (oneHotCode_length p) (oneHotCode_injective p) hlist)
  exact Equiv.ext fun i => congrFun hfn i

/-- Encoding a list with length-`ℓ` blocks multiplies its length by `ℓ`.
@isnad1 id=eq.1h5v.s5.ec4212f565c5 from=translated src=- shape=0b9c2ff3 vocab=c3cabb6f
-/
theorem fixedLength_flatMap_length {ι α : Type*} (code : ι → List α)
    (ℓ : ℕ) (hlen : ∀ i, (code i).length = ℓ) (l : List ι) :
    (l.flatMap code).length = l.length * ℓ := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.flatMap_cons, List.length_append, hlen, ih, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

/--
@isnad1 id=eq.0h2v.s4.a79c3bfe8e19 from=translated src=- shape=90a0750e vocab=a40cd311
-/
@[simp]
theorem encodedPermutation_length (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (encodedPermutation p σ).length = p * p := by
  change ((List.ofFn fun i => σ i).flatMap (oneHotCode p)).length = p * p
  rw [fixedLength_flatMap_length (oneHotCode p) p (oneHotCode_length p)]
  simp

/-- The free associative algebra on the two-element alphabet `Bool`.-/
abbrev BinaryFreeAlgebra (R : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid Bool)

/-- The coded alternating polynomial, over any commutative coefficient ring.-/
noncomputable def codedMatrixPI (R : Type*) [CommRing R] (p : ℕ) : BinaryFreeAlgebra R :=
  ∑ σ : Equiv.Perm (Fin p),
    Equiv.Perm.sign σ • MonoidAlgebra.single (encodedPermutation p σ) (1 : R)

/-- Evaluation of the free binary algebra at two algebra elements.-/
noncomputable def binaryEvaluation (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] (v : Bool → A) : BinaryFreeAlgebra R →ₐ[R] A :=
  MonoidAlgebra.lift R A (FreeMonoid Bool) (FreeMonoid.lift v)

/-- Word evaluation respects a concatenation of code blocks.
@isnad1 id=eq.0h5v.s8.9c39d48f99c8 from=translated src=- shape=7578d6f3 vocab=7a70bad4
-/
theorem wordEvaluation_flatMap {ι A : Type*} [Monoid A]
    (v : Bool → A) (code : ι → List Bool) (l : List ι) :
    FreeMonoid.lift v (FreeMonoid.ofList (l.flatMap code)) =
      (l.map fun i => FreeMonoid.lift v (FreeMonoid.ofList (code i))).prod := by
  induction l with
  | nil => simp [FreeMonoid.lift_ofList]
  | cons a as ih =>
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons]
      change FreeMonoid.lift v (FreeMonoid.ofList (code a) *
        FreeMonoid.ofList (as.flatMap code)) = _
      rw [map_mul, ih]

end CriticalGK2

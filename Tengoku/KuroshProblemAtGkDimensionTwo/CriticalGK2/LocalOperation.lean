import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.MatrixPI

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A local PI operation with an arbitrary linear-combination stem

The stem is an arbitrary coefficient vector on binary words of a fixed length.
Its nonzero coefficient yields a retraction of the free block substitution.
The block alphabet is then injected into the actual two-letter free algebra by
fixed-length decoding.
-/

namespace CriticalGK2

open scoped BigOperators

/-- Words of a fixed length, represented without quotienting or variable lengths.-/
abbrev StemWord (n : ℕ) := Fin n → Bool

/-- A physical block consists of a length-`n` stem word followed by one letter.-/
abbrev BlockAlphabet (n : ℕ) := StemWord n × Bool

abbrev BlockFreeAlgebra (F : Type*) [Field F] (n : ℕ) :=
  MonoidAlgebra F (FreeMonoid (BlockAlphabet n))

/-- The actual free letter in the binary monoid algebra.-/
noncomputable def binaryLetter (F : Type*) [CommRing F] (b : Bool) : BinaryFreeAlgebra F :=
  MonoidAlgebra.single (FreeMonoid.of b) 1

/-- The block generator `t ⊗ b`, expanded in the genuine block-word basis.-/
noncomputable def stemBlock (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (b : Bool) : BlockFreeAlgebra F n :=
  ∑ a : StemWord n, t a • MonoidAlgebra.single (FreeMonoid.of (a, b)) 1

/-- Substitution of the two free letters by the two stem blocks.-/
noncomputable def stemSubstitution (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : BinaryFreeAlgebra F →ₐ[F] BlockFreeAlgebra F n :=
  MonoidAlgebra.lift F (BlockFreeAlgebra F n) (FreeMonoid Bool)
    (FreeMonoid.lift (stemBlock F n t))

/-- A chosen nonzero stem coefficient gives an explicit decoding algebra map.-/
noncomputable def stemRetraction (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (a₀ : StemWord n) : BlockFreeAlgebra F n →ₐ[F] BinaryFreeAlgebra F :=
  MonoidAlgebra.lift F (BinaryFreeAlgebra F) (FreeMonoid (BlockAlphabet n))
    (FreeMonoid.lift fun g =>
      if g.1 = a₀ then (t a₀)⁻¹ • binaryLetter F g.2 else 0)

/-- The binary word corresponding to one physical block.-/
def blockWordCode (n : ℕ) (g : BlockAlphabet n) : List Bool :=
  List.ofFn g.1 ++ [g.2]

@[simp]
theorem blockWordCode_length (n : ℕ) (g : BlockAlphabet n) :
    (blockWordCode n g).length = n + 1 := by
  simp [blockWordCode]

/-- A physical block can be decoded uniquely into its stem and last letter.-/
theorem blockWordCode_injective (n : ℕ) : Function.Injective (blockWordCode n) := by
  intro g g' h
  rcases g with ⟨a, b⟩
  rcases g' with ⟨a', b'⟩
  change List.ofFn a ++ [b] = List.ofFn a' ++ [b'] at h
  have hhead : List.ofFn a = List.ofFn a' := by
    have ht := congrArg (List.take n) h
    have hl : (List.ofFn a ++ [b]).take n = List.ofFn a :=
      List.take_left' (by simp)
    have hr : (List.ofFn a' ++ [b']).take n = List.ofFn a' :=
      List.take_left' (by simp)
    exact hl.symm.trans (ht.trans hr)
  have ha := List.ofFn_injective hhead
  subst a'
  have hb : b = b' := List.singleton_injective (List.append_cancel_left h)
  subst b'
  rfl

/-- Flattening genuine fixed-length block words into binary words.-/
def flattenBlocks (n : ℕ) : FreeMonoid (BlockAlphabet n) →* FreeMonoid Bool where
  toFun w := FreeMonoid.ofList (w.toList.flatMap (blockWordCode n))
  map_one' := rfl
  map_mul' a b := by
    change (a.toList ++ b.toList).flatMap (blockWordCode n) =
      a.toList.flatMap (blockWordCode n) ++ b.toList.flatMap (blockWordCode n)
    simp only [List.flatMap_append]

/-- Equal-length parsing proves that flattening loses no block-word information.-/
theorem flattenBlocks_injective (n : ℕ) : Function.Injective (flattenBlocks n) := by
  intro u v h
  apply FreeMonoid.toList.injective
  apply fixedLength_flatMap_injective (blockWordCode n) (n + 1) (by omega)
    (blockWordCode_length n) (blockWordCode_injective n)
  exact congrArg FreeMonoid.toList h

/-- The linear and multiplicative block embedding into the actual binary free algebra.-/
noncomputable def flattenBlockAlgebra (F : Type*) [Field F] (n : ℕ) :
    BlockFreeAlgebra F n →ₐ[F] BinaryFreeAlgebra F :=
  MonoidAlgebra.mapDomainAlgHom F F (flattenBlocks n)

/-- Flattening is injective on all linear combinations, over the original field.-/
theorem flattenBlockAlgebra_injective (F : Type*) [Field F] (n : ℕ) :
    Function.Injective (flattenBlockAlgebra F n) := by
  exact MonoidAlgebra.mapDomain_injective (flattenBlocks_injective n)

/-- The actual arbitrary-stem substitution into the two-letter ambient free algebra.-/
noncomputable def stemEmbedding (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : BinaryFreeAlgebra F →ₐ[F] BinaryFreeAlgebra F :=
  (flattenBlockAlgebra F n).comp (stemSubstitution F n t)

/-- The genuine local zero-evaluation block in the ambient two-letter algebra.-/
noncomputable def localPIBlock (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) : BinaryFreeAlgebra F :=
  stemEmbedding F n t (codedMatrixPI F (k * k + 1) * MonoidAlgebra.single u 1)

end CriticalGK2

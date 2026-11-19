import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.QuadraticModels

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MagicSquares.Certificates

/-- An explicit center-zero square of cubes over the field of order 49.
@isnad1 id=ismagico.0h0v.s9.52cf7e0bdb32 from=translated src=- shape=5a5174db vocab=5a604e5b
-/
theorem cube_witness_49 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨3, 2⟩ : Field49)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field49 := ![⟨4, 6⟩, ⟨2, 4⟩, ⟨4, 0⟩, ⟨1, 6⟩, ⟨0, 0⟩, ⟨3, 4⟩, ⟨6, 0⟩, ⟨3, 6⟩, ⟨5, 4⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨3, 2⟩ : Field49)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field121 := QuadraticAlgebra (ZMod 11) 2 0
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 11, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 121.
@isnad1 id=ismagico.0h0v.s9.eb825a1218e0 from=translated src=- shape=7c8a98c4 vocab=49317074
-/
theorem cube_witness_121 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨3, 0⟩ : Field121)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field121 := ![⟨1, 9⟩, ⟨8, 6⟩, ⟨5, 10⟩, ⟨9, 7⟩, ⟨0, 0⟩, ⟨2, 7⟩, ⟨6, 10⟩, ⟨3, 6⟩, ⟨10, 9⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨3, 0⟩ : Field121)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field169 := QuadraticAlgebra (ZMod 13) 2 0
instance : Fact (Nat.Prime 13) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 13, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 169.
@isnad1 id=ismagico.0h0v.s9.7f1171e1e255 from=translated src=- shape=7c8a98c4 vocab=49317074
-/
theorem cube_witness_169 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨5, 5⟩ : Field169)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field169 := ![⟨4, 6⟩, ⟨1, 12⟩, ⟨9, 0⟩, ⟨1, 6⟩, ⟨0, 0⟩, ⟨4, 11⟩, ⟨12, 0⟩, ⟨4, 9⟩, ⟨3, 11⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨5, 5⟩ : Field169)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field289 := QuadraticAlgebra (ZMod 17) 3 0
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 17, r ^ 2 ≠ 3 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 289.
@isnad1 id=ismagico.0h0v.s9.4fb924fb5081 from=translated src=- shape=7c8a98c4 vocab=37eb4f89
-/
theorem cube_witness_289 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨3, 0⟩ : Field289)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field289 := ![⟨5, 14⟩, ⟨15, 9⟩, ⟨8, 15⟩, ⟨4, 16⟩, ⟨0, 0⟩, ⟨13, 16⟩, ⟨9, 15⟩, ⟨2, 9⟩, ⟨12, 14⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨3, 0⟩ : Field289)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field361 := QuadraticAlgebra (ZMod 19) 2 0
instance : Fact (Nat.Prime 19) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 19, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 361.
@isnad1 id=ismagico.0h0v.s9.fbdbd79fe5e2 from=translated src=- shape=7c8a98c4 vocab=49317074
-/
theorem cube_witness_361 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨0, 2⟩ : Field361)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field361 := ![⟨0, 11⟩, ⟨2, 17⟩, ⟨11, 0⟩, ⟨17, 17⟩, ⟨0, 0⟩, ⟨14, 14⟩, ⟨18, 0⟩, ⟨5, 14⟩, ⟨0, 18⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨0, 2⟩ : Field361)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field529 := QuadraticAlgebra (ZMod 23) 5 0
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 23, r ^ 2 ≠ 5 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 529.
@isnad1 id=ismagico.0h0v.s9.a39bced490c3 from=translated src=- shape=7c8a98c4 vocab=697a6be5
-/
theorem cube_witness_529 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨3, 0⟩ : Field529)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field529 := ![⟨17, 12⟩, ⟨13, 20⟩, ⟨11, 22⟩, ⟨8, 16⟩, ⟨0, 0⟩, ⟨15, 16⟩, ⟨12, 22⟩, ⟨10, 20⟩, ⟨6, 12⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨3, 0⟩ : Field529)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field841 := QuadraticAlgebra (ZMod 29) 2 0
instance : Fact (Nat.Prime 29) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 29, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 841.
@isnad1 id=ismagico.0h0v.s9.6bb36a1b05df from=translated src=- shape=7c8a98c4 vocab=49317074
-/
theorem cube_witness_841 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨3, 0⟩ : Field841)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field841 := ![⟨20, 26⟩, ⟨19, 16⟩, ⟨14, 24⟩, ⟨13, 15⟩, ⟨0, 0⟩, ⟨16, 15⟩, ⟨15, 24⟩, ⟨10, 16⟩, ⟨9, 26⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨3, 0⟩ : Field841)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

abbrev Field961 := QuadraticAlgebra (ZMod 31) 3 0
instance : Fact (Nat.Prime 31) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 31, r ^ 2 ≠ 3 + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 961.
@isnad1 id=ismagico.0h0v.s9.b71308a5ab57 from=translated src=- shape=7c8a98c4 vocab=37eb4f89
-/
theorem cube_witness_961 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨7, 1⟩ : Field961)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field961 := ![⟨21, 25⟩, ⟨13, 25⟩, ⟨25, 0⟩, ⟨6, 19⟩, ⟨0, 0⟩, ⟨1, 29⟩, ⟨30, 0⟩, ⟨28, 30⟩, ⟨19, 30⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨7, 1⟩ : Field961)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

/-- The quadratic extension of `Field25` with `β² = α`.-/
abbrev Field625 := QuadraticAlgebra Field25 ⟨0, 1⟩ 0
instance : Fact (∀ r : Field25, r ^ 2 ≠ ⟨0, 1⟩ + 0 * r) := ⟨by decide +kernel⟩

/-- An explicit center-zero square of cubes over the field of order 625.
@isnad1 id=ismagico.0h0v.s11.031056589bf8 from=translated src=- shape=1a7fe73b vocab=c962fe0f
-/
theorem cube_witness_625 :
    IsMagicOfPowers 3 (Square3.centerZero (⟨⟨3, 2⟩, ⟨3, 1⟩⟩ : Field625)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → Field625 := ![⟨⟨3, 0⟩, ⟨4, 4⟩⟩, ⟨⟨2, 2⟩, ⟨3, 3⟩⟩, ⟨⟨2, 3⟩, ⟨0, 0⟩⟩, ⟨⟨4, 4⟩, ⟨3, 4⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨3, 0⟩, ⟨0, 3⟩⟩, ⟨⟨3, 3⟩, ⟨0, 0⟩⟩, ⟨⟨3, 2⟩, ⟨2, 3⟩⟩, ⟨⟨4, 4⟩, ⟨1, 4⟩⟩]
  have hroots : ∀ k, roots k ^ 3 =
      (Square3.centerZero (⟨⟨3, 2⟩, ⟨3, 1⟩⟩ : Field625)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

end MagicSquares.Certificates

import Tengoku.MagicSquaresFieldsLean.MagicSquares.PrunedSearch
import Tengoku.MagicSquaresFieldsLean.MagicSquares.FieldTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Explicit witnesses, checked by kernel reduction of all nine entry tests. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MagicSquares.Certificates

theorem cube_witness_11 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 11)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 11 := ![9, 6, 1, 4, 0, 7, 10, 5, 2]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 11)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_17 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 17)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 17 := ![7, 4, 1, 9, 0, 8, 16, 13, 10]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 17)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_23 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 23)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 23 := ![12, 20, 1, 7, 0, 16, 22, 3, 11]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 23)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_29 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 29)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 29 := ![18, 20, 1, 3, 0, 26, 28, 9, 11]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 29)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_41 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 41)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 41 := ![27, 16, 1, 36, 0, 5, 40, 25, 14]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 41)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_47 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 47)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 47 := ![28, 29, 1, 26, 0, 21, 46, 18, 19]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 47)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_53 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 53)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 53 := ![33, 47, 1, 35, 0, 18, 52, 6, 20]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 53)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_59 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 59)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 59 := ![49, 31, 1, 21, 0, 38, 58, 28, 10]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 59)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_71 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 71)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 71 := ![6, 13, 1, 22, 0, 49, 70, 58, 65]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 71)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_73 :
    IsMagicOfPowers 3 (Square3.centerZero (8 : ZMod 73)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 73 := ![55, 37, 64, 60, 0, 31, 72, 69, 71]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (8 : ZMod 73)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_83 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 83)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 83 := ![11, 73, 1, 33, 0, 50, 82, 10, 72]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 83)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_89 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 89)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 89 := ![29, 11, 1, 73, 0, 16, 88, 78, 60]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 89)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_97 :
    IsMagicOfPowers 3 (Square3.centerZero (19 : ZMod 97)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 97 := ![37, 42, 61, 53, 0, 85, 96, 82, 71]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (19 : ZMod 97)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_101 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 101)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 101 := ![53, 31, 1, 75, 0, 26, 100, 70, 48]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 101)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_103 :
    IsMagicOfPowers 3 (Square3.centerZero (9 : ZMod 103)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 103 := ![82, 97, 56, 101, 0, 92, 102, 70, 43]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (9 : ZMod 103)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_107 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 107)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 107 := ![25, 71, 1, 101, 0, 6, 106, 36, 82]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 107)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_109 :
    IsMagicOfPowers 3 (Square3.centerZero (33 : ZMod 109)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 109 := ![101, 78, 63, 42, 0, 79, 108, 100, 68]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (33 : ZMod 109)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_113 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 113)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 113 := ![33, 106, 1, 32, 0, 81, 112, 7, 80]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 113)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_131 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 131)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 131 := ![46, 97, 1, 77, 0, 54, 130, 34, 85]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 131)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_137 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 137)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 137 := ![29, 123, 1, 39, 0, 98, 136, 14, 108]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 137)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_139 :
    IsMagicOfPowers 3 (Square3.centerZero (63 : ZMod 139)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 139 := ![80, 135, 96, 113, 0, 133, 138, 106, 115]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (63 : ZMod 139)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_149 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 149)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 149 := ![72, 17, 1, 79, 0, 70, 148, 132, 77]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 149)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_151 :
    IsMagicOfPowers 3 (Square3.centerZero (27 : ZMod 151)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 151 := ![96, 90, 118, 137, 0, 146, 150, 140, 148]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (27 : ZMod 151)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_157 :
    IsMagicOfPowers 3 (Square3.centerZero (28 : ZMod 157)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 157 := ![135, 150, 144, 154, 0, 118, 156, 84, 107]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (28 : ZMod 157)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_163 :
    IsMagicOfPowers 3 (Square3.centerZero (22 : ZMod 163)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 163 := ![91, 155, 104, 147, 0, 113, 162, 138, 153]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (22 : ZMod 163)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_167 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 167)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 167 := ![72, 67, 1, 10, 0, 157, 166, 100, 95]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 167)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_173 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 173)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 173 := ![166, 29, 1, 12, 0, 161, 172, 144, 7]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 173)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_179 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 179)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 179 := ![47, 37, 1, 121, 0, 58, 178, 142, 132]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 179)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_181 :
    IsMagicOfPowers 3 (Square3.centerZero (6 : ZMod 181)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 181 := ![127, 149, 132, 172, 0, 102, 180, 88, 69]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (6 : ZMod 181)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_191 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 191)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 191 := ![48, 165, 1, 44, 0, 147, 190, 26, 143]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 191)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_193 :
    IsMagicOfPowers 3 (Square3.centerZero (68 : ZMod 193)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 193 := ![188, 162, 108, 93, 0, 185, 192, 95, 154]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (68 : ZMod 193)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_197 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 197)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 197 := ![117, 150, 1, 176, 0, 21, 196, 47, 80]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 197)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_199 :
    IsMagicOfPowers 3 (Square3.centerZero (60 : ZMod 199)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 199 := ![83, 181, 106, 102, 0, 168, 198, 117, 157]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (60 : ZMod 199)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_211 :
    IsMagicOfPowers 3 (Square3.centerZero (12 : ZMod 211)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 211 := ![110, 174, 196, 186, 0, 139, 210, 96, 173]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (12 : ZMod 211)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_223 :
    IsMagicOfPowers 3 (Square3.centerZero (14 : ZMod 223)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 223 := ![144, 198, 183, 133, 0, 191, 222, 115, 185]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (14 : ZMod 223)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_227 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 227)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 227 := ![70, 95, 1, 141, 0, 86, 226, 132, 157]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 227)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_229 :
    IsMagicOfPowers 3 (Square3.centerZero (16 : ZMod 229)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 229 := ![196, 108, 134, 161, 0, 209, 228, 184, 125]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (16 : ZMod 229)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_233 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 233)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 233 := ![35, 157, 1, 141, 0, 92, 232, 76, 198]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 233)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_239 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 239)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 239 := ![50, 148, 1, 42, 0, 197, 238, 91, 189]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 239)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_241 :
    IsMagicOfPowers 3 (Square3.centerZero (26 : ZMod 241)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 241 := ![101, 238, 225, 145, 0, 235, 240, 193, 172]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (26 : ZMod 241)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_251 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 251)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 251 := ![121, 10, 1, 201, 0, 50, 250, 241, 130]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 251)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_257 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 257)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 257 := ![147, 193, 1, 8, 0, 249, 256, 64, 110]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 257)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_263 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 263)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 263 := ![102, 167, 1, 126, 0, 137, 262, 96, 161]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 263)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_269 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 269)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 269 := ![102, 38, 1, 85, 0, 184, 268, 231, 167]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 269)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_271 :
    IsMagicOfPowers 3 (Square3.centerZero (9 : ZMod 271)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 271 := ![139, 190, 242, 269, 0, 213, 270, 100, 237]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (9 : ZMod 271)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_277 :
    IsMagicOfPowers 3 (Square3.centerZero (60 : ZMod 277)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 277 := ![242, 142, 160, 194, 0, 261, 276, 271, 182]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (60 : ZMod 277)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_281 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 281)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 281 := ![15, 170, 1, 162, 0, 119, 280, 111, 266]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 281)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_283 :
    IsMagicOfPowers 3 (Square3.centerOne (28 : ZMod 283) 31) := by
  refine ⟨Square3.centerOne_isMagic _ _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 283 := ![228, 150, 217, 250, 238, 163, 271, 251, 280]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerOne (28 : ZMod 283) 31).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_293 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 293)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 293 := ![208, 26, 1, 248, 0, 45, 292, 267, 85]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 293)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_307 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 307)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 307 := ![228, 166, 289, 255, 0, 292, 306, 248, 115]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 307)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_311 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 311)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 311 := ![63, 152, 1, 266, 0, 45, 310, 159, 248]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 311)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_313 :
    IsMagicOfPowers 3 (Square3.centerZero (6 : ZMod 313)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 313 := ![278, 141, 214, 270, 0, 145, 312, 267, 300]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (6 : ZMod 313)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_317 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 317)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 317 := ![78, 34, 1, 56, 0, 261, 316, 283, 239]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 317)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_331 :
    IsMagicOfPowers 3 (Square3.centerZero (116 : ZMod 331)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 331 := ![264, 291, 299, 186, 0, 325, 330, 247, 173]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (116 : ZMod 331)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_337 :
    IsMagicOfPowers 3 (Square3.centerZero (6 : ZMod 337)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 337 := ![222, 313, 208, 322, 0, 235, 336, 274, 330]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (6 : ZMod 337)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_347 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 347)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 347 := ![225, 7, 1, 149, 0, 198, 346, 340, 122]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 347)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_349 :
    IsMagicOfPowers 3 (Square3.centerZero (36 : ZMod 349)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 349 := ![255, 245, 226, 275, 0, 321, 348, 124, 304]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (36 : ZMod 349)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_353 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 353)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 353 := ![114, 162, 1, 292, 0, 61, 352, 191, 239]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 353)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_359 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 359)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 359 := ![214, 257, 1, 183, 0, 176, 358, 102, 145]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 359)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_367 :
    IsMagicOfPowers 3 (Square3.centerZero (8 : ZMod 367)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 367 := ![199, 295, 283, 330, 0, 195, 366, 191, 365]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (8 : ZMod 367)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_373 :
    IsMagicOfPowers 3 (Square3.centerZero (18 : ZMod 373)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 373 := ![201, 234, 284, 318, 0, 364, 372, 311, 358]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (18 : ZMod 373)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_379 :
    IsMagicOfPowers 3 (Square3.centerZero (40 : ZMod 379)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 379 := ![318, 359, 327, 356, 0, 320, 378, 262, 239]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (40 : ZMod 379)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_383 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 383)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 383 := ![306, 233, 1, 240, 0, 143, 382, 150, 77]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 383)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_389 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 389)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 389 := ![371, 122, 1, 338, 0, 51, 388, 267, 18]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 389)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_397 :
    IsMagicOfPowers 3 (Square3.centerZero (16 : ZMod 397)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 397 := ![260, 236, 362, 288, 0, 155, 396, 320, 366]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (16 : ZMod 397)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_401 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 401)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 401 := ![304, 218, 1, 298, 0, 103, 400, 183, 97]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 401)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_409 :
    IsMagicOfPowers 3 (Square3.centerZero (64 : ZMod 409)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 409 := ![212, 157, 355, 325, 0, 372, 408, 298, 405]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (64 : ZMod 409)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_419 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 419)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 419 := ![395, 182, 1, 198, 0, 221, 418, 237, 24]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 419)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_421 :
    IsMagicOfPowers 3 (Square3.centerZero (7 : ZMod 421)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 421 := ![300, 419, 400, 198, 0, 369, 420, 379, 406]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (7 : ZMod 421)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_431 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 431)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 431 := ![290, 419, 1, 359, 0, 72, 430, 12, 141]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 431)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_433 :
    IsMagicOfPowers 3 (Square3.centerZero (74 : ZMod 433)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 433 := ![324, 278, 234, 178, 0, 349, 432, 380, 392]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (74 : ZMod 433)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_439 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 439)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 439 := ![401, 270, 267, 426, 0, 398, 438, 364, 352]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 439)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_443 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 443)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 443 := ![236, 322, 1, 432, 0, 11, 442, 121, 207]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 443)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_449 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 449)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 449 := ![42, 82, 1, 230, 0, 219, 448, 367, 407]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 449)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_457 :
    IsMagicOfPowers 3 (Square3.centerZero (21 : ZMod 457)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 457 := ![342, 221, 323, 417, 0, 293, 456, 366, 214]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (21 : ZMod 457)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_461 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 461)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 461 := ![52, 158, 1, 426, 0, 35, 460, 303, 409]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 461)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_463 :
    IsMagicOfPowers 3 (Square3.centerZero (56 : ZMod 463)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 463 := ![384, 203, 441, 424, 0, 356, 462, 367, 270]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (56 : ZMod 463)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_467 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 467)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 467 := ![28, 76, 1, 381, 0, 86, 466, 391, 439]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 467)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_479 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 479)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 479 := ![365, 265, 1, 94, 0, 385, 478, 214, 114]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 479)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_487 :
    IsMagicOfPowers 3 (Square3.centerZero (26 : ZMod 487)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 487 := ![372, 484, 254, 479, 0, 395, 486, 275, 477]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (26 : ZMod 487)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_491 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 491)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 491 := ![17, 335, 1, 107, 0, 384, 490, 156, 474]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 491)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_499 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 499)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 499 := ![363, 399, 359, 489, 0, 392, 498, 471, 441]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 499)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_503 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 503)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 503 := ![189, 239, 1, 362, 0, 141, 502, 264, 314]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 503)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_509 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 509)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 509 := ![8, 420, 1, 366, 0, 143, 508, 89, 501]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 509)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_521 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 521)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 521 := ![195, 433, 1, 296, 0, 225, 520, 88, 326]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 521)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_523 :
    IsMagicOfPowers 3 (Square3.centerZero (42 : ZMod 523)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 523 := ![203, 297, 462, 469, 0, 367, 522, 485, 372]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (42 : ZMod 523)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_541 :
    IsMagicOfPowers 3 (Square3.centerZero (7 : ZMod 541)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 541 := ![211, 539, 411, 471, 0, 374, 540, 281, 380]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (7 : ZMod 541)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_547 :
    IsMagicOfPowers 3 (Square3.centerZero (9 : ZMod 547)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 547 := ![520, 397, 506, 545, 0, 465, 546, 530, 534]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (9 : ZMod 547)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_557 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 557)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 557 := ![311, 448, 1, 465, 0, 92, 556, 109, 246]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 557)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_563 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 563)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 563 := ![548, 216, 1, 318, 0, 245, 562, 347, 15]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 563)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_569 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 569)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 569 := ![472, 411, 1, 36, 0, 533, 568, 158, 97]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 569)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_571 :
    IsMagicOfPowers 3 (Square3.centerZero (7 : ZMod 571)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 571 := ![358, 569, 461, 551, 0, 467, 570, 351, 552]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (7 : ZMod 571)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_577 :
    IsMagicOfPowers 3 (Square3.centerZero (87 : ZMod 577)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 577 := ![562, 502, 363, 519, 0, 282, 576, 396, 310]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (87 : ZMod 577)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_587 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 587)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 587 := ![311, 274, 1, 30, 0, 557, 586, 313, 276]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 587)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_593 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 593)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 593 := ![195, 425, 1, 120, 0, 473, 592, 168, 398]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 593)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_599 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 599)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 599 := ![566, 451, 1, 429, 0, 170, 598, 148, 33]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 599)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_601 :
    IsMagicOfPowers 3 (Square3.centerZero (63 : ZMod 601)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 601 := ![440, 597, 576, 309, 0, 513, 600, 501, 258]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (63 : ZMod 601)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_607 :
    IsMagicOfPowers 3 (Square3.centerZero (7 : ZMod 607)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 607 := ![524, 605, 396, 539, 0, 319, 606, 420, 434]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (7 : ZMod 607)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_613 :
    IsMagicOfPowers 3 (Square3.centerZero (9 : ZMod 613)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 613 := ![492, 459, 547, 611, 0, 481, 612, 257, 596]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (9 : ZMod 613)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_617 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 617)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 617 := ![390, 51, 1, 242, 0, 375, 616, 566, 227]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 617)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_619 :
    IsMagicOfPowers 3 (Square3.centerZero (43 : ZMod 619)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 619 := ![288, 461, 366, 512, 0, 347, 618, 261, 466]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (43 : ZMod 619)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_631 :
    IsMagicOfPowers 3 (Square3.centerZero (39 : ZMod 631)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 631 := ![578, 553, 587, 309, 0, 595, 630, 354, 386]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (39 : ZMod 631)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_641 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 641)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 641 := ![476, 400, 1, 125, 0, 516, 640, 241, 165]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 641)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_643 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 643)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 643 := ![440, 458, 465, 582, 0, 509, 642, 595, 566]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 643)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_647 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 647)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 647 := ![108, 482, 1, 298, 0, 349, 646, 165, 539]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 647)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_653 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 653)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 653 := ![366, 47, 1, 528, 0, 125, 652, 606, 287]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 653)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_659 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 659)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 659 := ![507, 215, 1, 282, 0, 377, 658, 444, 152]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 659)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_661 :
    IsMagicOfPowers 3 (Square3.centerZero (8 : ZMod 661)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 661 := ![592, 650, 364, 640, 0, 373, 660, 612, 659]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (8 : ZMod 661)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_673 :
    IsMagicOfPowers 3 (Square3.centerZero (79 : ZMod 673)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 673 := ![304, 643, 417, 647, 0, 573, 672, 396, 548]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (79 : ZMod 673)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_677 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 677)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 677 := ![31, 81, 1, 443, 0, 234, 676, 596, 646]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 677)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_683 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 683)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 683 := ![571, 427, 1, 16, 0, 667, 682, 256, 112]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 683)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_691 :
    IsMagicOfPowers 3 (Square3.centerZero (20 : ZMod 691)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 691 := ![677, 465, 437, 583, 0, 375, 690, 640, 590]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (20 : ZMod 691)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_701 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 701)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 701 := ![278, 91, 1, 416, 0, 285, 700, 610, 423]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 701)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_709 :
    IsMagicOfPowers 3 (Square3.centerZero (124 : ZMod 709)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 709 := ![369, 704, 481, 621, 0, 497, 708, 426, 608]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (124 : ZMod 709)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_719 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 719)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 719 := ![54, 398, 1, 607, 0, 112, 718, 321, 665]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 719)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_727 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 727)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 727 := ![531, 646, 445, 718, 0, 370, 726, 422, 707]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 727)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_733 :
    IsMagicOfPowers 3 (Square3.centerZero (39 : ZMod 733)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 733 := ![447, 541, 425, 533, 0, 705, 732, 304, 605]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (39 : ZMod 733)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_739 :
    IsMagicOfPowers 3 (Square3.centerZero (26 : ZMod 739)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 739 := ![379, 736, 418, 673, 0, 428, 738, 515, 655]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (26 : ZMod 739)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_743 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 743)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 743 := ![46, 378, 1, 629, 0, 114, 742, 365, 697]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 743)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_751 :
    IsMagicOfPowers 3 (Square3.centerZero (7 : ZMod 751)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 751 := ![369, 749, 678, 601, 0, 315, 750, 605, 652]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (7 : ZMod 751)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_757 :
    IsMagicOfPowers 3 (Square3.centerZero (27 : ZMod 757)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 757 := ![673, 505, 729, 290, 0, 550, 756, 748, 754]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (27 : ZMod 757)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_761 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 761)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 761 := ![430, 385, 1, 85, 0, 676, 760, 376, 331]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 761)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_769 :
    IsMagicOfPowers 3 (Square3.centerZero (26 : ZMod 769)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 769 := ![592, 766, 408, 400, 0, 597, 768, 455, 699]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (26 : ZMod 769)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_773 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 773)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 773 := ![128, 549, 1, 421, 0, 352, 772, 224, 645]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 773)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_787 :
    IsMagicOfPowers 3 (Square3.centerZero (71 : ZMod 787)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 787 := ![622, 532, 407, 401, 0, 699, 786, 688, 362]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (71 : ZMod 787)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_797 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 797)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 797 := ![290, 499, 1, 230, 0, 567, 796, 298, 507]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 797)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_809 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 809)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 809 := ![749, 393, 1, 35, 0, 774, 808, 416, 60]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 809)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_811 :
    IsMagicOfPowers 3 (Square3.centerZero (15 : ZMod 811)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 811 := ![433, 765, 680, 464, 0, 770, 810, 462, 764]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (15 : ZMod 811)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_821 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 821)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 821 := ![359, 691, 1, 581, 0, 240, 820, 130, 462]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 821)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_823 :
    IsMagicOfPowers 3 (Square3.centerZero (26 : ZMod 823)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 823 := ![422, 820, 648, 489, 0, 806, 822, 522, 642]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (26 : ZMod 823)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_827 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 827)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 827 := ![44, 180, 1, 340, 0, 487, 826, 647, 783]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 827)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_829 :
    IsMagicOfPowers 3 (Square3.centerZero (11 : ZMod 829)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 829 := ![572, 505, 703, 738, 0, 598, 828, 708, 778]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (11 : ZMod 829)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_839 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 839)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 839 := ![324, 409, 1, 679, 0, 160, 838, 430, 515]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 839)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_853 :
    IsMagicOfPowers 3 (Square3.centerZero (8 : ZMod 853)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 853 := ![440, 319, 632, 701, 0, 528, 852, 619, 851]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (8 : ZMod 853)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_857 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 857)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 857 := ![19, 477, 1, 645, 0, 212, 856, 380, 838]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 857)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_859 :
    IsMagicOfPowers 3 (Square3.centerZero (35 : ZMod 859)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 859 := ![692, 779, 598, 714, 0, 810, 858, 595, 470]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (35 : ZMod 859)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_863 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 863)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 863 := ![366, 719, 1, 851, 0, 12, 862, 144, 497]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 863)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_877 :
    IsMagicOfPowers 3 (Square3.centerZero (27 : ZMod 877)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 877 := ![846, 702, 594, 753, 0, 865, 876, 464, 874]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (27 : ZMod 877)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_881 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 881)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 881 := ![151, 788, 1, 521, 0, 360, 880, 93, 730]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 881)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_883 :
    IsMagicOfPowers 3 (Square3.centerZero (46 : ZMod 883)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 883 := ![360, 842, 545, 670, 0, 412, 882, 572, 709]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (46 : ZMod 883)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_887 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 887)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 887 := ![708, 865, 1, 645, 0, 242, 886, 22, 179]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 887)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_907 :
    IsMagicOfPowers 3 (Square3.centerZero (11 : ZMod 907)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 907 := ![866, 671, 522, 539, 0, 727, 906, 831, 541]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (11 : ZMod 907)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_911 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 911)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 911 := ![367, 254, 1, 538, 0, 373, 910, 657, 544]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 911)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_919 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 919)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 919 := ![786, 584, 866, 894, 0, 513, 918, 878, 483]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 919)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_929 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 929)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 929 := ![109, 376, 1, 845, 0, 84, 928, 553, 820]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 929)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_937 :
    IsMagicOfPowers 3 (Square3.centerZero (64 : ZMod 937)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 937 := ![582, 895, 614, 927, 0, 518, 936, 489, 933]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (64 : ZMod 937)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_941 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 941)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 941 := ![495, 152, 1, 681, 0, 260, 940, 789, 446]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 941)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_947 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 947)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 947 := ![168, 50, 1, 644, 0, 303, 946, 897, 779]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 947)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_953 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 953)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 953 := ![152, 284, 1, 651, 0, 302, 952, 669, 801]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 953)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_967 :
    IsMagicOfPowers 3 (Square3.centerZero (9 : ZMod 967)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 967 := ![410, 759, 824, 965, 0, 681, 966, 526, 767]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (9 : ZMod 967)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_971 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 971)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 971 := ![696, 570, 1, 678, 0, 293, 970, 401, 275]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 971)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_977 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 977)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 977 := ![151, 157, 1, 865, 0, 112, 976, 820, 826]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 977)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_983 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 983)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 983 := ![777, 694, 1, 17, 0, 966, 982, 289, 206]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 983)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_991 :
    IsMagicOfPowers 3 (Square3.centerZero (78 : ZMod 991)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 991 := ![972, 955, 877, 828, 0, 581, 990, 851, 807]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (78 : ZMod 991)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_997 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 997)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 997 := ![938, 962, 692, 883, 0, 758, 996, 670, 987]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 997)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_1009 :
    IsMagicOfPowers 3 (Square3.centerZero (43 : ZMod 1009)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 1009 := ![427, 616, 634, 722, 0, 384, 1008, 948, 733]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (43 : ZMod 1009)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_1013 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 1013)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 1013 := ![37, 704, 1, 377, 0, 636, 1012, 309, 976]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 1013)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_1019 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 1019)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 1019 := ![856, 270, 1, 234, 0, 785, 1018, 749, 163]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 1019)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_1021 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 1021)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 1021 := ![478, 965, 652, 862, 0, 547, 1020, 777, 770]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 1021)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_1031 :
    IsMagicOfPowers 3 (Square3.centerZero (3 : ZMod 1031)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 1031 := ![917, 354, 1, 233, 0, 798, 1030, 677, 114]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (3 : ZMod 1031)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem cube_witness_1033 :
    IsMagicOfPowers 3 (Square3.centerZero (7 : ZMod 1033)) := by
  refine ⟨Square3.centerZero_isMagic _, by unfold Square3.PairwiseDistinct; decide +kernel, ?_⟩
  let roots : Fin 9 → ZMod 1033 := ![530, 1031, 837, 977, 0, 590, 1032, 641, 983]
  have hroots : ∀ k, roots k ^ 3 = (Square3.centerZero (7 : ZMod 1033)).entries k := by decide +kernel
  exact fun k => ⟨roots k, hroots k⟩

theorem square_witness_29 : letI : Fact (Nat.Prime 29) := ⟨by decide⟩;
    IsMagicOfPowers 2 (Square3.centerZero (5 : ZMod 29)) := by
  letI : Fact (Nat.Prime 29) := ⟨by decide⟩
  apply (normalizedPowerConditions_iff (by decide : 0 < 2) (Square3.centerZero_isMagic _)).mp
  decide +kernel

theorem square_witness_37 : letI : Fact (Nat.Prime 37) := ⟨by decide⟩;
    IsMagicOfPowers 2 (Square3.centerZero (10 : ZMod 37)) := by
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply (normalizedPowerConditions_iff (by decide : 0 < 2) (Square3.centerZero_isMagic _)).mp
  decide +kernel

theorem square_witness_41 : letI : Fact (Nat.Prime 41) := ⟨by decide⟩;
    IsMagicOfPowers 2 (Square3.centerZero (9 : ZMod 41)) := by
  letI : Fact (Nat.Prime 41) := ⟨by decide⟩
  apply (normalizedPowerConditions_iff (by decide : 0 < 2) (Square3.centerZero_isMagic _)).mp
  decide +kernel

theorem square_witness_53 : letI : Fact (Nat.Prime 53) := ⟨by decide⟩;
    IsMagicOfPowers 2 (Square3.centerZero (10 : ZMod 53)) := by
  letI : Fact (Nat.Prime 53) := ⟨by decide⟩
  apply (normalizedPowerConditions_iff (by decide : 0 < 2) (Square3.centerZero_isMagic _)).mp
  decide +kernel

theorem square_witness_61 : letI : Fact (Nat.Prime 61) := ⟨by decide⟩;
    IsMagicOfPowers 2 (Square3.centerZero (4 : ZMod 61)) := by
  letI : Fact (Nat.Prime 61) := ⟨by decide⟩
  apply (normalizedPowerConditions_iff (by decide : 0 < 2) (Square3.centerZero_isMagic _)).mp
  decide +kernel

theorem square_witness_73 : letI : Fact (Nat.Prime 73) := ⟨by decide⟩;
    IsMagicOfPowers 2 (Square3.centerZero (3 : ZMod 73)) := by
  letI : Fact (Nat.Prime 73) := ⟨by decide⟩
  apply (normalizedPowerConditions_iff (by decide : 0 < 2) (Square3.centerZero_isMagic _)).mp
  decide +kernel

end MagicSquares.Certificates

import Tengoku.DeletionCodesLean.DeletionCode.CatalogueWords
import Tengoku.DeletionCodesLean.DeletionCode.EditRigidity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms substring_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms local_word_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms local_vertex_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bubble_vertices_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms deletion_vertices_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms insertion_vertices_injective` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Substring uniqueness and simple local de Bruijn paths after an actual fixed
edit of a k-unique source. Local words are tied to the full edited word by
bounded letter agreement. The bubble corollaries use exactly the longer and
shorter grammar words, including both endpoint vertices of each local path.
Neither simplicity nor an endpoint-intersection condition is assumed.
-/
namespace DeletionCode.BubblePathSimplicity

open Windows HeaderRecovery CatalogueWords SingleEditOrigins

/-- Uniqueness restricts to any actual in-bounds substring.
@isnad1 id=kunique.3h6v.s5.91729086a810 from=translated src=- shape=2404e99d vocab=75c956aa
-/
theorem substring_unique (full word : Letters) (n len r s : ℕ)
    (hfull : KUnique full n r) (hbound : s + len ≤ n)
    (hocc : Agree word 0 full s len) : KUnique word len r := by
  intro a b ha hb hag
  have heq : s + a = s + b := hfull (s + a) (s + b) (by omega) (by omega) (by
    intro i hi
    calc
      full (s + a + i) = word (a + i) := by
        simpa only [Nat.zero_add, Nat.add_assoc] using
          (hocc (a + i) (by omega)).symm
      _ = word (b + i) := hag i hi
      _ = full (s + b + i) := by
        simpa only [Nat.zero_add, Nat.add_assoc] using hocc (b + i) (by omega))
  omega

/-- A concrete local list in a valid one-edit output inherits (L-1)-uniqueness.
@isnad1 id=kunique.5h6v.s6.272c8d9aad97 from=translated src=- shape=ca74dd2f vocab=b6bd6bbf
-/
theorem local_word_unique {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n)
    (word : List Bool) (s : ℕ)
    (hbound : s + word.length ≤ e.outputLength n)
    (hocc : Agree (listLetters word) 0 (e.word x) s word.length) :
    KUnique (listLetters word) word.length (windowLength k - 1) :=
  substring_unique (e.word x) (listLetters word) (e.outputLength n) word.length
    (windowLength k - 1) s (EditRigidity.one_edit_unique hk x hx e he) hbound hocc

/-- All vertices of such a local path, including its terminal vertex, are distinct.
@isnad1 id=injectiv.6h6v.s7.4013bcf96b93 from=translated src=- shape=574fa6af vocab=d1c2f63c
-/
theorem local_vertex_injective {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n)
    (word : List Bool) (s : ℕ)
    (hbound : s + word.length ≤ e.outputLength n)
    (hocc : Agree (listLetters word) 0 (e.word x) s word.length)
    (hlength : windowLength k ≤ word.length) :
    Function.Injective (fun i : Fin (word.length - windowLength k + 2) =>
      SpectrumPath.vertexAt (listLetters word) (windowLength k) i.val) :=
  SpectrumPath.vertex_path_injective (listLetters word) word.length (windowLength k)
    (by unfold windowLength; omega) hlength
    (local_word_unique hk x hx e he word s hbound hocc)

/-- The grammar lengths give exactly the two vertex-index types in the paper.
@isnad1 id=and.2h2v.s7.e6b6ae15d0b2 from=translated src=- shape=130385f7 vocab=7f78b7c3
-/
theorem bubble_vertices_injective {k : ℕ} (bubble : BubbleWord k)
    (hlong : KUnique (listLetters bubble.longWord) bubble.longWord.length (windowLength k - 1))
    (hshort : KUnique (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k - 1)) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  have hlonglen : bubble.longWord.length = 2 * windowLength k - bubble.rho := by
    simpa only [longLength, BubbleWord.header] using bubble.longWord_length
  have hshortlen : bubble.shortWord.length = 2 * windowLength k - bubble.rho - 1 := by
    simpa only [shortLength, longLength, BubbleWord.header] using bubble.shortWord_length
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hlongbound : windowLength k ≤ bubble.longWord.length := by
    unfold windowLength at *
    omega
  have hshortbound : windowLength k ≤ bubble.shortWord.length := by
    unfold windowLength at *
    omega
  have hlongcount : bubble.longWord.length - windowLength k + 2 =
      windowLength k - bubble.rho + 2 := by
    unfold windowLength at *
    omega
  have hshortcount : bubble.shortWord.length - windowLength k + 2 =
      windowLength k - bubble.rho + 1 := by
    unfold windowLength at *
    omega
  constructor
  · intro i j heq
    apply Fin.ext
    apply hlong i.val j.val
    · have hi := i.isLt
      omega
    · have hj := j.isLt
      omega
    · intro r hr
      exact congrFun heq ⟨r, hr⟩
  · intro i j heq
    apply Fin.ext
    apply hshort i.val j.val
    · have hi := i.isLt
      omega
    · have hj := j.isLt
      omega
    · intro r hr
      exact congrFun heq ⟨r, hr⟩

/-- The actual longer source substring and shorter deletion substring both
spell simple paths, with exactly the manuscript's long and short vertex ranges.
@isnad1 id=and.7h6v.s8.33d0abe97012 from=translated src=- shape=8919e9a9 vocab=0eb85511
-/
theorem deletion_vertices_injective {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (hpos : pos < n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n)
    (hslength : s + bubble.shortWord.length ≤ n - 1)
    (hlong : Agree (listLetters bubble.longWord) 0 x s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 (deleteAt x pos) s bubble.shortWord.length) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) :=
  bubble_vertices_injective bubble
    (local_word_unique hk x hx .unchanged trivial bubble.longWord s hlength hlong)
    (local_word_unique hk x hx (.delete pos) hpos bubble.shortWord s hslength hshort)

/-- The actual longer insertion substring and shorter source substring both
spell simple paths. The inserted bit is the actual bit used in the full edit.
@isnad1 id=and.7h7v.s8.e4f6cff01e9c from=translated src=- shape=dc3c0224 vocab=a844118e
-/
theorem insertion_vertices_injective {n k : ℕ} (hk : 1 ≤ k) (bubble : BubbleWord k)
    (x : Letters) (hx : KUnique x n k) (pos : ℕ) (bit : Bool) (hpos : pos ≤ n) (s : ℕ)
    (hlength : s + bubble.longWord.length ≤ n + 1)
    (hslength : s + bubble.shortWord.length ≤ n)
    (hlong : Agree (listLetters bubble.longWord) 0 (insertAt x pos bit) s bubble.longWord.length)
    (hshort : Agree (listLetters bubble.shortWord) 0 x s bubble.shortWord.length) :
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 2) =>
      SpectrumPath.vertexAt (listLetters bubble.longWord) (windowLength k) i.val) ∧
    Function.Injective (fun i : Fin (windowLength k - bubble.rho + 1) =>
      SpectrumPath.vertexAt (listLetters bubble.shortWord) (windowLength k) i.val) :=
  bubble_vertices_injective bubble
    (local_word_unique hk x hx (.insert pos bit) hpos bubble.longWord s hlength hlong)
    (local_word_unique hk x hx .unchanged trivial bubble.shortWord s hslength hshort)

end DeletionCode.BubblePathSimplicity

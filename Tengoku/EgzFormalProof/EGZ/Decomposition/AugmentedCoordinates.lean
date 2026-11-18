import Tengoku.EgzFormalProof.EGZ.Decomposition.ScalarExtension
import Tengoku.EgzFormalProof.EGZ.Decomposition.CenteredLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Adding slab coordinates to a flag fibre

The completeness refinement augments a fibre by finitely many affine
functionals. These coordinate maps project to the old fibre, retain the
additional coordinates along lower transitions, and commute with scalar
extension and reduction modulo every modulus.
-/

namespace EGZ

namespace Coord

variable {R : Type*} [CommRing R]

def first (m k : ℕ) : (Fin (m + k) → R) →ₗ[R] (Fin m → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Fin.castAdd k i)

def last (m k : ℕ) : (Fin (m + k) → R) →ₗ[R] (Fin k → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Fin.natAdd m i)

/--
@isnad1 id=eq.0h5v.s8.c496ce2da570 from=translated src=- shape=d1b304cd vocab=17be12a9
-/
@[simp]
theorem first_apply {m k : ℕ} (q : Fin (m + k) → R) (i : Fin m) :
    first m k q i = q (Fin.castAdd k i) := rfl

/--
@isnad1 id=eq.0h5v.s8.c33cd5669679 from=translated src=- shape=1e26e33f vocab=c9cf17e9
-/
@[simp]
theorem last_apply {m k : ℕ} (q : Fin (m + k) → R) (i : Fin k) :
    last m k q i = q (Fin.natAdd m i) := rfl

section Append

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Append the outputs of two affine maps in the standard finite coordinates.-/
def append {m k : ℕ} (A : V →ᵃ[R] (Fin m → R)) (B : V →ᵃ[R] (Fin k → R)) :
    V →ᵃ[R] (Fin (m + k) → R) :=
  AffineMap.pi (Fin.addCases
    (fun i ↦ (AffineMap.proj i).comp A) (fun i ↦ (AffineMap.proj i).comp B))

/--
@isnad1 id=eq.0h8v.s9.d159fbd17445 from=translated src=- shape=11d94723 vocab=73868530
-/
@[simp]
theorem append_castAdd {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) (i : Fin m) :
    append A B v (Fin.castAdd k i) = A v i := by
  simp [append]

/--
@isnad1 id=eq.0h8v.s9.6e74e124883c from=translated src=- shape=ec913447 vocab=7ac27ac6
-/
@[simp]
theorem append_natAdd {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) (i : Fin k) :
    append A B v (Fin.natAdd m i) = B v i := by
  simp [append]

/--
@isnad1 id=eq.0h7v.s9.f110402aa8c7 from=translated src=- shape=e2c8b603 vocab=cb7603ca
-/
@[simp]
theorem first_append {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) : first m k (append A B v) = A v := by
  ext i
  simp

/--
@isnad1 id=eq.0h7v.s9.9ecb0e5e4fb8 from=translated src=- shape=16690f6c vocab=d859f406
-/
@[simp]
theorem last_append {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) : last m k (append A B v) = B v := by
  ext i
  simp

end Append

/-- Extend an affine map while leaving additional coordinates fixed.-/
def extend {m n : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R)) (k : ℕ) :
    (Fin (m + k) → R) →ᵃ[R] (Fin (n + k) → R) :=
  append (A.comp (first m k).toAffineMap) (last m k).toAffineMap

/--
@isnad1 id=eq.0h6v.s10.202059096c36 from=translated src=- shape=7e7e78aa vocab=954789e9
-/
@[simp]
theorem first_extend {m n k : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (q : Fin (m + k) → R) : first n k (extend A k q) = A (first m k q) := by
  simp [extend]

/--
@isnad1 id=eq.0h6v.s10.41da4b0b7f8f from=translated src=- shape=8f0d4cbb vocab=f9d784ec
-/
@[simp]
theorem last_extend {m n k : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (q : Fin (m + k) → R) : last n k (extend A k q) = last m k q := by
  simp [extend]

/--
@isnad1 id=eq.2h5v.s10.2992ac09bfd5 from=translated src=- shape=a6c6c8fb vocab=27a71590
-/
theorem ext_first_last {m k : ℕ} {q r : Fin (m + k) → R}
    (hfirst : first m k q = first m k r) (hlast : last m k q = last m k r) : q = r := by
  funext i
  refine Fin.addCases (fun i ↦ congrFun hfirst i) (fun i ↦ congrFun hlast i) i

/--
@isnad1 id=eq.0h3v.s8.5e475dcf1d37 from=translated src=- shape=406ed315 vocab=11eb0183
-/
theorem extend_id (m k : ℕ) :
    extend (AffineMap.id R (Fin m → R)) k = AffineMap.id R _ := by
  ext q i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [extend]

/--
@isnad1 id=eq.0h7v.s9.2863940b110e from=translated src=- shape=74d17c24 vocab=57c45e24
-/
theorem extend_comp {l m n : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (B : (Fin l → R) →ᵃ[R] (Fin m → R)) (k : ℕ) :
    extend (A.comp B) k = (extend A k).comp (extend B k) := by
  apply AffineMap.ext
  intro q
  apply ext_first_last <;> simp

end Coord

namespace IntegralAffineMap

/-- Forget the extra coordinates of an augmented lattice fibre.-/
def first (m k : ℕ) : IntegralAffineMap (m + k) m where
  real := (Coord.first m k).toAffineMap
  integer := Coord.first m k
  modp _ := (Coord.first m k).toAffineMap
  real_integer _ := rfl
  mod_integer _ _ := rfl

/-- Apply an old transition and keep the newly added slab coordinates.-/
noncomputable def extend {m n : ℕ} (A : IntegralAffineMap m n) (k : ℕ) :
    IntegralAffineMap (m + k) (n + k) where
  real := Coord.extend A.real k
  integer := Coord.extend A.toIntAffineMap k
  modp p := Coord.extend (A.modp p) k
  real_integer q := by
    apply Coord.ext_first_last
    · change Coord.first n k (Coord.extend A.real k q.real) =
        Coord.first n k (IntCoord.real (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      change A.real (IntCoord.real (Coord.first m k q)) =
        IntCoord.real (Coord.first n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      exact A.real_integer _
    · change Coord.last n k (Coord.extend A.real k q.real) =
        Coord.last n k (IntCoord.real (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]
      change IntCoord.real (Coord.last m k q) =
        IntCoord.real (Coord.last n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]
  mod_integer p q := by
    apply Coord.ext_first_last
    · change Coord.first n k (Coord.extend (A.modp p) k (q.mod p)) =
        Coord.first n k (IntCoord.mod p (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      change A.modp p (IntCoord.mod p (Coord.first m k q)) =
        IntCoord.mod p (Coord.first n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      exact A.mod_integer _ _
    · change Coord.last n k (Coord.extend (A.modp p) k (q.mod p)) =
        Coord.last n k (IntCoord.mod p (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]
      change IntCoord.mod p (Coord.last m k q) =
        IntCoord.mod p (Coord.last n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]

/--
@isnad1 id=eq.0h4v.s6.a680f834f100 from=translated src=- shape=d1416fbb vocab=316a28b2
-/
theorem first_comp_extend {m n : ℕ} (A : IntegralAffineMap m n) (k : ℕ) :
    (first n k).comp (A.extend k) = A.comp (first m k) := by
  apply ext_integer
  funext q
  exact Coord.first_extend A.toIntAffineMap q

/--
@isnad1 id=eq.0h2v.s5.fed7a0455a50 from=translated src=- shape=e6541e89 vocab=27485caf
-/
theorem extend_id (m k : ℕ) : (id m).extend k = id (m + k) := by
  apply ext_integer
  funext q
  change Coord.extend (id m).toIntAffineMap k q = q
  rw [toIntAffineMap_id, Coord.extend_id]
  rfl

/--
@isnad1 id=eq.0h6v.s6.c127e8ebc450 from=translated src=- shape=a1914c8a vocab=9572bc98
-/
theorem extend_comp {l m n : ℕ} (A : IntegralAffineMap m n)
    (B : IntegralAffineMap l m) (k : ℕ) :
    (A.comp B).extend k = (A.extend k).comp (B.extend k) := by
  apply ext_integer
  funext q
  change Coord.extend (A.comp B).toIntAffineMap k q =
    Coord.extend A.toIntAffineMap k (Coord.extend B.toIntAffineMap k q)
  rw [toIntAffineMap_comp, Coord.extend_comp]
  rfl

end IntegralAffineMap

/--
@isnad1 id=le.2h4v.s9.297169fbf36b from=translated src=- shape=e5128bbb vocab=6540f7ed
-/
theorem latticeSupNorm_le_of_first_last {m k B : ℕ} (q : IntCoord (m + k))
    (hfirst : latticeSupNorm (Coord.first m k q) ≤ B)
    (hlast : latticeSupNorm (Coord.last m k q) ≤ B) : latticeSupNorm q ≤ B := by
  apply Finset.sup_le
  intro i _
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · exact (Finset.le_sup (f := fun i ↦ ((Coord.first m k q) i).natAbs)
      (Finset.mem_univ j)).trans hfirst
  · exact (Finset.le_sup (f := fun i ↦ ((Coord.last m k q) i).natAbs)
      (Finset.mem_univ j)).trans hlast

end EGZ

namespace EGZ.Coord

variable {R : Type*} [CommRing R]

/-- Keep the initial coordinates of a finite coordinate vector.-/
def prefixMap (es et : ℕ) (h : et ≤ es) : (Fin es → R) →ₗ[R] (Fin et → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Fin.castLE h i)

/--
@isnad1 id=eq.1h5v.s8.af4ef11a9812 from=translated src=- shape=6d61e883 vocab=f131efac
-/
@[simp]
theorem prefixMap_apply {es et : ℕ} (h : et ≤ es) (q : Fin es → R) (i : Fin et) :
    prefixMap es et h q i = q (Fin.castLE h i) := rfl

/--
@isnad1 id=eq.0h3v.s8.6f0898a6419e from=translated src=- shape=962a0acd vocab=f29f9b9c
-/
@[simp]
theorem prefixMap_refl (e : ℕ) (q : Fin e → R) : prefixMap e e le_rfl q = q := by
  ext i
  rfl

/--
@isnad1 id=eq.2h5v.s9.de82b584885a from=translated src=- shape=199dfb9f vocab=6b030c91
-/
@[simp]
theorem prefixMap_comp {es em et : ℕ} (hm : em ≤ es) (ht : et ≤ em) (q : Fin es → R) :
    prefixMap em et ht (prefixMap es em hm q) = prefixMap es et (ht.trans hm) q := rfl

/-- Apply an affine map to the old coordinates and keep an initial segment
of the additional coordinates.-/
def extendPrefix {m n : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (es et : ℕ) (h : et ≤ es) : (Fin (m + es) → R) →ᵃ[R] (Fin (n + et) → R) :=
  append (A.comp (first m es).toAffineMap)
    ((prefixMap es et h).toAffineMap.comp (last m es).toAffineMap)

/--
@isnad1 id=eq.1h7v.s10.d8d1162b8880 from=translated src=- shape=c421b922 vocab=a8f778c4
-/
@[simp]
theorem first_extendPrefix {m n es et : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (h : et ≤ es) (q : Fin (m + es) → R) :
    first n et (extendPrefix A es et h q) = A (first m es q) := by simp [extendPrefix]

/--
@isnad1 id=eq.1h7v.s10.7f941a179024 from=translated src=- shape=fd60def2 vocab=3a5a2d5c
-/
@[simp]
theorem last_extendPrefix {m n es et : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (h : et ≤ es) (q : Fin (m + es) → R) :
    last n et (extendPrefix A es et h q) = prefixMap es et h (last m es q) := by
  simp [extendPrefix]

/--
@isnad1 id=eq.0h3v.s8.c3d48ce9f2f1 from=translated src=- shape=203ec568 vocab=11f05147
-/
theorem extendPrefix_id (m e : ℕ) :
    extendPrefix (AffineMap.id R (Fin m → R)) e e le_rfl = AffineMap.id R _ := by
  apply AffineMap.ext
  intro q
  apply ext_first_last <;> simp

/--
@isnad1 id=eq.2h9v.s9.b0d2c2fb3eab from=translated src=- shape=2d54f0ec vocab=d21fc8d9
-/
theorem extendPrefix_comp {l m n es em et : ℕ}
    (A : (Fin m → R) →ᵃ[R] (Fin n → R)) (B : (Fin l → R) →ᵃ[R] (Fin m → R))
    (hm : em ≤ es) (ht : et ≤ em) :
    extendPrefix (A.comp B) es et (ht.trans hm) =
      (extendPrefix A em et ht).comp (extendPrefix B es em hm) := by
  apply AffineMap.ext
  intro q
  apply ext_first_last <;> simp

end EGZ.Coord

namespace EGZ.IntegralAffineMap

/-- Extend an integral-affine map while retaining an initial segment of its
additional coordinates.-/
noncomputable def extendPrefix {m n : ℕ} (A : IntegralAffineMap m n)
    (es et : ℕ) (h : et ≤ es) : IntegralAffineMap (m + es) (n + et) where
  real := Coord.extendPrefix A.real es et h
  integer := Coord.extendPrefix A.toIntAffineMap es et h
  modp p := Coord.extendPrefix (A.modp p) es et h
  real_integer q := by
    apply Coord.ext_first_last
    · change Coord.first n et (Coord.extendPrefix A.real es et h q.real) =
        Coord.first n et (IntCoord.real (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      change A.real (IntCoord.real (Coord.first m es q)) =
        IntCoord.real (Coord.first n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      exact A.real_integer _
    · change Coord.last n et (Coord.extendPrefix A.real es et h q.real) =
        Coord.last n et (IntCoord.real (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]
      change IntCoord.real (Coord.prefixMap es et h (Coord.last m es q)) =
        IntCoord.real (Coord.last n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]
  mod_integer p q := by
    apply Coord.ext_first_last
    · change Coord.first n et (Coord.extendPrefix (A.modp p) es et h (q.mod p)) =
        Coord.first n et (IntCoord.mod p (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      change A.modp p (IntCoord.mod p (Coord.first m es q)) =
        IntCoord.mod p (Coord.first n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      exact A.mod_integer _ _
    · change Coord.last n et (Coord.extendPrefix (A.modp p) es et h (q.mod p)) =
        Coord.last n et (IntCoord.mod p (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]
      change IntCoord.mod p (Coord.prefixMap es et h (Coord.last m es q)) =
        IntCoord.mod p (Coord.last n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]

/--
@isnad1 id=eq.1h5v.s6.41dfb9288208 from=translated src=- shape=b2abf5d7 vocab=5df7529e
-/
theorem first_comp_extendPrefix {m n : ℕ} (A : IntegralAffineMap m n)
    (es et : ℕ) (h : et ≤ es) :
    (first n et).comp (A.extendPrefix es et h) = A.comp (first m es) := by
  apply ext_integer
  funext q
  exact Coord.first_extendPrefix A.toIntAffineMap h q

/--
@isnad1 id=eq.0h2v.s5.596ed21af645 from=translated src=- shape=def9a4da vocab=c3e95e9c
-/
theorem extendPrefix_id (m e : ℕ) : (id m).extendPrefix e e le_rfl = id (m + e) := by
  apply ext_integer
  funext q
  change Coord.extendPrefix (id m).toIntAffineMap e e le_rfl q = q
  rw [toIntAffineMap_id, Coord.extendPrefix_id]
  rfl

/--
@isnad1 id=eq.2h8v.s6.73c5c536fd9e from=translated src=- shape=d1cbd5f4 vocab=740d217e
-/
theorem extendPrefix_comp {l m n es em et : ℕ} (A : IntegralAffineMap m n)
    (B : IntegralAffineMap l m) (hm : em ≤ es) (ht : et ≤ em) :
    (A.comp B).extendPrefix es et (ht.trans hm) =
      (A.extendPrefix em et ht).comp (B.extendPrefix es em hm) := by
  apply ext_integer
  funext q
  change Coord.extendPrefix (A.comp B).toIntAffineMap es et (ht.trans hm) q =
    Coord.extendPrefix A.toIntAffineMap em et ht (Coord.extendPrefix B.toIntAffineMap es em hm q)
  rw [toIntAffineMap_comp, Coord.extendPrefix_comp _ _ hm ht]
  rfl

end EGZ.IntegralAffineMap

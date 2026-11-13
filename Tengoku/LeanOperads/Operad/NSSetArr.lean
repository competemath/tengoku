/-
# Planar calculus without reindexing

In the positional convention an equation between two composites of a non-symmetric operad holds
only after reindexing along an equality of arities, and a calculation with several steps
accumulates those reindexings. Packaging an operation with its arity, as an element of
`Arr S = Σ n, S n`, removes them: the composite `X.comp a Y` of `Arr S` inserts `Y` at the input
`a` of `X` (numbered from zero), the arities take care of themselves, and the operad axioms become
four equations (`comp_one`, `one_comp`, `comp_comp_nested`, `comp_comp_disjoint`) with side
conditions on positions that `omega` discharges.

On top of this, `bin g X Y` fills the two inputs of a binary operation, and a relation between
two-fold composites of binary operations holds generically once it holds with identities in the
leaves (`bin_bin_of_left_right`, `bin_right_of`, `bin_left_of`).
-/
import Tengoku.LeanOperads.Operad.NSSetPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe v w

namespace Operad

namespace NSSetOperad

variable {S : ℕ → Type v} [NSSetOperad S]

/-- **Operations of all arities.**-/
abbrev Arr (S : ℕ → Type v) := Σ n, S n

namespace Arr

/-- The identity operation.-/
def one : Arr S := ⟨1, NSSetOperad.one⟩

/-- **Compose `Y` into the input `a` of `X`**; `X` itself when `a` is out of range.-/
def comp (X : Arr S) (a : ℕ) (Y : Arr S) : Arr S :=
  if h : a < X.1 then
    ⟨a + Y.1 + (X.1 - a - 1),
      NSSetOperad.comp a (X.1 - a - 1) (reindexS S (by omega) X.2) Y.2⟩
  else X

omit [NSSetOperad S] in
/--
@isnad1 id=eq.1h4v.s5.4174b5b464fb from=translated src=- shape=3a772377 vocab=20f62bfd
-/
lemma mk_reindexS {m n : ℕ} (h : m = n) (x : S m) :
    (⟨n, reindexS S h x⟩ : Arr S) = ⟨m, x⟩ := by
  subst h
  rfl

omit [NSSetOperad S] in
/--
@isnad1 id=iff.0h4v.s5.89240ab226f3 from=translated src=- shape=d2fab0e9 vocab=34d1bc9d
-/
lemma mk_eq_mk_iff {n : ℕ} {x y : S n} : (⟨n, x⟩ : Arr S) = ⟨n, y⟩ ↔ x = y :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => h ▸ rfl⟩

omit [NSSetOperad S] in
private lemma mk_congr (a b b' : ℕ) (hb : b' = b) {n : ℕ} (h : a + 1 + b = a + 1 + b')
    (x : S (a + 1 + b)) (y : S n) (f : ∀ b'', S (a + 1 + b'') → S n → S (a + n + b'')) :
    (⟨a + n + b', f b' (reindexS S h x) y⟩ : Arr S) = ⟨a + n + b, f b x y⟩ := by
  subst hb
  rfl

/-- A composite of operations in positional form.
@isnad1 id=eq.0h6v.s6.79fdb42ef9ca from=translated src=- shape=5412676c vocab=785c6d45
-/
lemma mk_comp (a b : ℕ) {n : ℕ} (x : S (a + 1 + b)) (y : S n) :
    comp (⟨_, x⟩ : Arr S) a ⟨n, y⟩ = ⟨a + n + b, NSSetOperad.comp a b x y⟩ := by
  unfold comp
  rw [dite_eq_left (by simp only; omega)]
  exact mk_congr a b _ (by simp only; omega) _ x y (fun b'' => NSSetOperad.comp a b'')

/--
@isnad1 id=eq.1h4v.s6.1efa536671a8 from=translated src=- shape=b09e3b89 vocab=df942780
-/
lemma comp_fst {X : Arr S} {a : ℕ} (h : a < X.1) (Y : Arr S) :
    (comp X a Y).1 = X.1 + Y.1 - 1 := by
  unfold comp
  rw [dite_eq_left h]
  simp only
  omega

omit [NSSetOperad S] in
/-- Every operation with an input `a` has positional form around it.
@isnad1 id=ex.1h3v.s6.aafd3b253335 from=translated src=- shape=9ba8bbb7 vocab=3dc1c2b8
-/
lemma exists_mk (X : Arr S) {a : ℕ} (h : a < X.1) : ∃ (b : ℕ) (x : S (a + 1 + b)), X = ⟨_, x⟩ := by
  obtain ⟨n, x⟩ := X
  obtain ⟨b, rfl⟩ : ∃ b, n = a + 1 + b := ⟨n - a - 1, by simp only at h; omega⟩
  exact ⟨b, x, rfl⟩

/-! ### The axioms -/

/--
@isnad1 id=eq.1h3v.s5.3587ecb2e7b3 from=translated src=- shape=dda56d00 vocab=8fa0285e
-/
theorem comp_one {X : Arr S} {a : ℕ} (h : a < X.1) : comp X a one = X := by
  obtain ⟨b, x, rfl⟩ := exists_mk X h
  rw [one, mk_comp, NSSetOperad.comp_one_right]

/--
@isnad1 id=eq.0h2v.s4.8743ebd19f2b from=translated src=- shape=accc90fb vocab=353ad6fb
-/
theorem one_comp (Y : Arr S) : comp (one : Arr S) 0 Y = Y := by
  obtain ⟨n, y⟩ := Y
  rw [one, show (⟨1, NSSetOperad.one⟩ : Arr S) = ⟨0 + 1 + 0, NSSetOperad.one⟩ from rfl, mk_comp,
    ← mk_reindexS (show 0 + n + 0 = n by omega), NSSetOperad.comp_one_left]

/-- **Nested associativity**: composing into an input that came from `Y`.
@isnad1 id=eq.2h6v.s6.c63e4f61ce70 from=translated src=- shape=88a3ce08 vocab=0614ecf2
-/
theorem comp_comp_nested {X Y : Arr S} (Z : Arr S) {a c : ℕ} (ha : a < X.1) (hc : c < Y.1) :
    comp (comp X a Y) (a + c) Z = comp X a (comp Y c Z) := by
  obtain ⟨b, x, rfl⟩ := exists_mk X ha
  obtain ⟨d, y, rfl⟩ := exists_mk Y hc
  obtain ⟨p, z⟩ := Z
  rw [mk_comp, mk_comp, mk_comp]
  have e1 : a + (c + 1 + d) + b = a + c + 1 + (d + b) := by omega
  rw [← mk_reindexS e1, mk_comp,
    ← mk_reindexS (show a + c + p + (d + b) = a + (c + p + d) + b by omega),
    NSSetOperad.comp_assoc_seq]

/-- **Disjoint associativity**: composing into two different inputs of `X`, in either order.
@isnad1 id=eq.2h6v.s6.d2cb97168e8a from=translated src=- shape=79f89233 vocab=df942780
-/
theorem comp_comp_disjoint {X : Arr S} (Y Z : Arr S) {a e : ℕ} (hae : a < e) (he : e < X.1) :
    comp (comp X a Y) (e + Y.1 - 1) Z = comp (comp X e Z) a Y := by
  obtain ⟨n, x⟩ := X
  obtain ⟨m, y⟩ := Y
  obtain ⟨p, z⟩ := Z
  simp only at he ⊢
  obtain ⟨b, rfl⟩ : ∃ b, e = a + 1 + b := ⟨e - a - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = a + 1 + b + 1 + c := ⟨n - (a + 1 + b) - 1, by omega⟩
  conv_lhs =>
    rw [← mk_reindexS (show a + 1 + b + 1 + c = a + 1 + (b + 1 + c) by omega) x, mk_comp,
      show a + 1 + b + m - 1 = a + m + b by omega,
      ← mk_reindexS (show a + m + (b + 1 + c) = a + m + b + 1 + c by omega), mk_comp,
      ← mk_reindexS (show a + m + b + p + c = a + m + (b + p + c) by omega)]
  conv_rhs =>
    rw [mk_comp, ← mk_reindexS (show a + 1 + b + p + c = a + 1 + (b + p + c) by omega), mk_comp]
  rw [NSSetOperad.comp_assoc_par]

/-! ### Filling a binary operation -/

/--
@isnad1 id=eq.0h1v.s4.e0eccabfa79b from=translated src=- shape=13658419 vocab=14e472e4
-/
@[simp] lemma one_fst : (one : Arr S).1 = 1 := rfl

/-- **Fill the two inputs of a binary operation.**-/
def bin (g : S 2) (X Y : Arr S) : Arr S := comp (comp ⟨2, g⟩ 1 Y) 0 X

private lemma fst_comp_two (g : S 2) (Y : Arr S) : (comp ⟨2, g⟩ 1 Y).1 = Y.1 + 1 := by
  rw [comp_fst (by show 1 < 2; omega)]
  show 2 + Y.1 - 1 = Y.1 + 1
  omega

/--
@isnad1 id=eq.0h4v.s5.3a37642093af from=translated src=- shape=7d6ffa9b vocab=ec81ca78
-/
@[simp] lemma bin_fst (g : S 2) (X Y : Arr S) : (bin g X Y).1 = X.1 + Y.1 := by
  unfold bin
  rw [comp_fst (by rw [fst_comp_two]; omega), fst_comp_two]
  omega

/-- Composing into the first argument.
@isnad1 id=eq.1h6v.s6.88da03d6c174 from=translated src=- shape=b7d501c3 vocab=ca184eaa
-/
theorem comp_bin_left (g : S 2) (X Y W : Arr S) {a : ℕ} (ha : a < X.1) :
    comp (bin g X Y) a W = bin g (comp X a W) Y := by
  have h := comp_comp_nested (X := comp ⟨2, g⟩ 1 Y) W (a := 0) (c := a)
    (by rw [fst_comp_two]; omega) ha
  rw [Nat.zero_add] at h
  exact h

/-- Composing into the second argument, at its input `c`.
@isnad1 id=eq.2h7v.s6.248a5d4ccbea from=translated src=- shape=4af49c13 vocab=2998f853
-/
theorem comp_bin_right (g : S 2) (X Y W : Arr S) {a c : ℕ} (h : a = X.1 + c) (hc : c < Y.1) :
    comp (bin g X Y) a W = bin g X (comp Y c W) := by
  subst h
  have h1 := comp_comp_disjoint (X := comp ⟨2, g⟩ 1 Y) X W (a := 0) (e := 1 + c)
    (by omega) (by rw [fst_comp_two]; omega)
  rw [show 1 + c + X.1 - 1 = X.1 + c by omega] at h1
  have h2 := comp_comp_nested (X := ⟨2, g⟩) W (a := 1) (c := c) (by show 1 < 2; omega) hc
  unfold bin
  rw [h1, h2]

/--
@isnad1 id=eq.0h2v.s5.42a16f229a13 from=translated src=- shape=0ef82325 vocab=a8b430d3
-/
theorem bin_one_one (g : S 2) : bin g one one = ⟨2, g⟩ := by
  unfold bin
  rw [comp_one (a := 1) (by show 1 < 2; omega), comp_one (by show 0 < 2; omega)]

/-! ### Relations between two-fold composites hold generically -/

/-- The left comb `p (q (·, ·), ·)`.-/
def leftComb (p q : S 2) : Arr S := bin p (bin q one one) one

/-- The right comb `p (·, q (·, ·))`.-/
def rightComb (p q : S 2) : Arr S := bin p one (bin q one one)

/--
@isnad1 id=eq.0h6v.s6.63b0fd15fa8a from=translated src=- shape=b7e13bd7 vocab=84540e32
-/
lemma subst_leftComb (p q : S 2) (X Y Z : Arr S) :
    comp (comp (comp (leftComb p q) 2 Z) 1 Y) 0 X = bin p (bin q X Y) Z := by
  unfold leftComb
  rw [comp_bin_right p (bin q one one) one Z (c := 0) (by simp) (by simp), one_comp,
    comp_bin_left p (bin q one one) Z Y (by simp),
    comp_bin_right q one one Y (c := 0) (by simp) (by simp), one_comp,
    comp_bin_left p (bin q one Y) Z X (by simp only [bin_fst, one_fst]; omega),
    comp_bin_left q one Y X (by simp), one_comp]

/--
@isnad1 id=eq.0h6v.s6.7ebbefcc36cb from=translated src=- shape=daa8c939 vocab=1c8a99d1
-/
lemma subst_rightComb (p q : S 2) (X Y Z : Arr S) :
    comp (comp (comp (rightComb p q) 2 Z) 1 Y) 0 X = bin p X (bin q Y Z) := by
  unfold rightComb
  rw [comp_bin_right p one (bin q one one) Z (c := 1) (by simp) (by simp),
    comp_bin_right q one one Z (c := 0) (by simp) (by simp), one_comp,
    comp_bin_right p one (bin q one Z) Y (c := 0) (by simp)
      (by simp only [bin_fst, one_fst]; omega),
    comp_bin_left q one Z Y (by simp), one_comp,
    comp_bin_left p one (bin q Y Z) X (by simp), one_comp]

/-- **An associativity-shaped relation holds generically.**
@isnad1 id=eq.1h8v.s6.1bc2e5b49cf1 from=translated src=- shape=90d080f0 vocab=fb760135
-/
theorem bin_bin_of_left_right {p q p' q' : S 2} (h : leftComb p q = rightComb p' q')
    (X Y Z : Arr S) : bin p (bin q X Y) Z = bin p' X (bin q' Y Z) := by
  rw [← subst_leftComb, ← subst_rightComb, h]

/-- **A relation between right combs holds generically.**
@isnad1 id=eq.1h8v.s6.6c4548c16ac3 from=translated src=- shape=f29ab575 vocab=95251f00
-/
theorem bin_right_of {p q p' q' : S 2} (h : rightComb p q = rightComb p' q') (X Y Z : Arr S) :
    bin p X (bin q Y Z) = bin p' X (bin q' Y Z) := by
  rw [← subst_rightComb, ← subst_rightComb, h]

/-- **A relation between left combs holds generically.**
@isnad1 id=eq.1h8v.s6.91ff4ce6ba31 from=translated src=- shape=403d3a42 vocab=e71bc99b
-/
theorem bin_left_of {p q p' q' : S 2} (h : leftComb p q = leftComb p' q') (X Y Z : Arr S) :
    bin p (bin q X Y) Z = bin p' (bin q' X Y) Z := by
  rw [← subst_leftComb, ← subst_leftComb, h]

/--
@isnad1 id=eq.0h3v.s6.04f94ca3d9aa from=translated src=- shape=9d9ba5c2 vocab=ac38076b
-/
lemma leftComb_eq (p q : S 2) : leftComb p q = ⟨0 + 2 + 1, NSSetOperad.comp 0 1 p q⟩ := by
  unfold leftComb
  rw [bin_one_one]
  unfold bin
  rw [comp_one (by show 1 < 2; omega)]
  exact mk_comp 0 1 p q

/--
@isnad1 id=eq.0h3v.s6.798b85c29837 from=translated src=- shape=9d9ba5c2 vocab=ee6e4777
-/
lemma rightComb_eq (p q : S 2) : rightComb p q = ⟨1 + 2 + 0, NSSetOperad.comp 1 0 p q⟩ := by
  unfold rightComb
  rw [bin_one_one]
  unfold bin
  rw [comp_one (by rw [fst_comp_two]; omega)]
  exact mk_comp 1 0 p q

/-! ### Right combs -/

/-- **The right comb** `g₀ (·, g₁ (·, … gₖ (·, ·)))` of a list of binary operations, and the
identity for the empty list.-/
def rcomb : List (S 2) → Arr S
  | [] => one
  | g :: l => bin g one (rcomb l)

/--
@isnad1 id=eq.0h1v.s4.4c584ea350ab from=translated src=- shape=fdf15abf vocab=703cc5c7
-/
@[simp] lemma rcomb_nil : rcomb ([] : List (S 2)) = one := rfl

/--
@isnad1 id=eq.0h3v.s5.90f8e2a0e5f0 from=translated src=- shape=b9849d6a vocab=10f671f7
-/
lemma rcomb_cons (g : S 2) (l : List (S 2)) : rcomb (g :: l) = bin g one (rcomb l) := rfl

/--
@isnad1 id=eq.0h2v.s5.8a1caa798d06 from=translated src=- shape=10acd918 vocab=ce125584
-/
@[simp] lemma rcomb_fst (l : List (S 2)) : (rcomb l).1 = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [rcomb_cons, bin_fst, ih, one_fst, List.length_cons]; omega

/--
@isnad1 id=eq.0h2v.s5.26aa5ef21972 from=translated src=- shape=fdec0f75 vocab=292f8147
-/
lemma rcomb_singleton (g : S 2) : rcomb [g] = ⟨2, g⟩ := bin_one_one g

section RightComb

variable (G : Set (S 2))

/-- `G` is **closed under rotation** when every left comb of two operations of `G` is a right comb
of two.-/
def RotClosed : Prop := ∀ g ∈ G, ∀ h ∈ G, ∃ g' ∈ G, ∃ h' ∈ G, leftComb g h = rightComb g' h'

/-- The right combs of operations of `G`.-/
def IsRComb (X : Arr S) : Prop := ∃ l : List (S 2), (∀ g ∈ l, g ∈ G) ∧ X = rcomb l

variable {G}

/--
@isnad1 id=isrcomb.0h2v.s4.72378fb47018 from=translated src=- shape=a30a0072 vocab=7e22f0c0
-/
lemma isRComb_one : IsRComb G one := ⟨[], by simp, rfl⟩

/--
@isnad1 id=isrcomb.1h3v.s6.616d7ae84884 from=translated src=- shape=c2d5cec0 vocab=3ab870a6
-/
lemma isRComb_of_mem {g : S 2} (hg : g ∈ G) : IsRComb G ⟨2, g⟩ :=
  ⟨[g], by simpa using hg, (rcomb_singleton g).symm⟩

/-- **A right comb grafted onto the first input of an operation of `G`** is a right comb.
@isnad1 id=isrcomb.4h5v.s6.1c381961d97f from=translated src=- shape=b488be69 vocab=7306b49f
-/
theorem isRComb_bin (hG : RotClosed G) {g : S 2} (hg : g ∈ G) {X Y : Arr S} (hX : IsRComb G X)
    (hY : IsRComb G Y) : IsRComb G (bin g X Y) := by
  obtain ⟨l, hl, rfl⟩ := hX
  obtain ⟨m, hm, rfl⟩ := hY
  induction l generalizing g with
  | nil => exact ⟨g :: m, List.forall_mem_cons.2 ⟨hg, hm⟩, rfl⟩
  | cons h l ih =>
    obtain ⟨g', hg', h', hh', e⟩ := hG g hg h (List.forall_mem_cons.1 hl).1
    obtain ⟨k, hk, hk'⟩ := ih hh' (List.forall_mem_cons.1 hl).2
    refine ⟨g' :: k, List.forall_mem_cons.2 ⟨hg', hk⟩, ?_⟩
    rw [rcomb_cons, bin_bin_of_left_right e, hk', rcomb_cons]

/-- **Composites of right combs are right combs.**
@isnad1 id=isrcomb.4h5v.s6.1035acd77c7e from=translated src=- shape=35b8890d vocab=2f06e287
-/
theorem isRComb_comp (hG : RotClosed G) {X Y : Arr S} (hX : IsRComb G X) (hY : IsRComb G Y)
    {a : ℕ} (ha : a < X.1) : IsRComb G (comp X a Y) := by
  obtain ⟨l, hl, rfl⟩ := hX
  induction l generalizing a with
  | nil =>
    obtain rfl : a = 0 := by simp only [rcomb_fst, List.length_nil] at ha; omega
    rw [rcomb_nil, one_comp]
    exact hY
  | cons g l ih =>
    have hg := (List.forall_mem_cons.1 hl).1
    have hl' := (List.forall_mem_cons.1 hl).2
    simp only [rcomb_fst, List.length_cons] at ha
    rw [rcomb_cons]
    cases a with
    | zero =>
      rw [comp_bin_left _ _ _ _ (by simp), one_comp]
      exact isRComb_bin hG hg hY ⟨l, hl', rfl⟩
    | succ a =>
      rw [comp_bin_right _ _ _ _ (c := a) (by simp only [one_fst]; omega)
        (by simp only [rcomb_fst]; omega)]
      obtain ⟨k, hk, hk'⟩ := ih hl' (a := a) (by simp only [rcomb_fst]; omega)
      exact ⟨g :: k, List.forall_mem_cons.2 ⟨hg, hk⟩, by rw [hk', rcomb_cons]⟩

end RightComb

/-! ### Morphisms -/

section Map

variable {T : ℕ → Type w} [NSSetOperad T]

/-- A morphism, on operations of all arities.-/
def map (φ : NSSetOperadHom S T) (X : Arr S) : Arr T := ⟨X.1, φ.app X.1 X.2⟩

/--
@isnad1 id=eq.0h4v.s5.0c9df36c1b14 from=translated src=- shape=37be3b93 vocab=22e8175c
-/
@[simp] lemma map_fst (φ : NSSetOperadHom S T) (X : Arr S) : (map φ X).1 = X.1 := rfl

/--
@isnad1 id=eq.0h5v.s5.dc67da5da579 from=translated src=- shape=e91dc14d vocab=9a42df9d
-/
lemma map_mk (φ : NSSetOperadHom S T) {n : ℕ} (x : S n) :
    map φ ⟨n, x⟩ = ⟨n, φ.app n x⟩ := rfl

/--
@isnad1 id=eq.0h3v.s5.d2f89fc6f708 from=translated src=- shape=7772ac6a vocab=7b325222
-/
@[simp] lemma map_one (φ : NSSetOperadHom S T) : map φ one = one := by
  rw [one, map_mk, φ.app_one]
  rfl

/--
@isnad1 id=eq.0h6v.s5.a41bbd1571a2 from=translated src=- shape=c4f7cec7 vocab=2a76bea2
-/
@[simp] lemma map_comp (φ : NSSetOperadHom S T) (X : Arr S) (a : ℕ) (Y : Arr S) :
    map φ (comp X a Y) = comp (map φ X) a (map φ Y) := by
  by_cases h : a < X.1
  · obtain ⟨b, x, rfl⟩ := exists_mk X h
    obtain ⟨n, y⟩ := Y
    rw [mk_comp, map_mk, map_mk, map_mk, mk_comp, φ.app_comp]
  · have h' : ¬ a < (map φ X).1 := h
    unfold comp
    rw [dite_eq_right h, dite_eq_right h']

/--
@isnad1 id=eq.0h6v.s6.931f9337c1a5 from=translated src=- shape=1b9f2abc vocab=0b2a013c
-/
@[simp] lemma map_bin (φ : NSSetOperadHom S T) (g : S 2) (X Y : Arr S) :
    map φ (bin g X Y) = bin (φ.app 2 g) (map φ X) (map φ Y) := by
  unfold bin
  rw [map_comp, map_comp]
  rfl

/--
@isnad1 id=eq.0h4v.s6.6043ea18f0c5 from=translated src=- shape=9c552150 vocab=24ee5651
-/
@[simp] lemma map_rcomb (φ : NSSetOperadHom S T) (l : List (S 2)) :
    map φ (rcomb l) = rcomb (l.map (φ.app 2)) := by
  induction l with
  | nil => exact map_one φ
  | cons g l ih => rw [rcomb_cons, map_bin, map_one, ih, List.map_cons, rcomb_cons]

end Map

/-! ### Presented operads -/

section Pres

variable {T : ℕ → Type w} {ρ : ∀ n : ℕ, NSSyn T n → NSSyn T n → Prop}

/-- **Induction over a presented operad**: a property of operations that holds for the identity
and the generators and is stable under composition holds for all operations.
@isnad1 id=var.0h7v.s6.518b72ff1469 from=translated src=- shape=778b5cf9 vocab=eed88b5c
-/
theorem pres_induction {P : Arr (NSPres T ρ) → Prop} (h_one : P one)
    (h_gen : ∀ (n : ℕ) (g : T n), P ⟨n, NSPres.gen g⟩)
    (h_comp : ∀ (X : Arr (NSPres T ρ)) (a : ℕ) (Y : Arr (NSPres T ρ)), a < X.1 → P X → P Y →
      P (comp X a Y))
    (X : Arr (NSPres T ρ)) : P X := by
  obtain ⟨n, x⟩ := X
  obtain ⟨s, rfl⟩ := NSPres.mk_surjective x
  induction s with
  | one => exact h_one
  | gen g => exact h_gen _ g
  | comp a b s t ihs iht =>
    have := h_comp _ a _ (by show a < a + 1 + b; omega) ihs iht
    rwa [mk_comp, NSPres.comp_mk] at this

/-- **Right-comb normal forms**: if every generator is a right comb of operations of `G`, and `G`
is closed under rotation, every operation is a right comb of operations of `G`.
@isnad1 id=isrcomb.2h4v.s6.e7a81625f970 from=translated src=- shape=e37a4046 vocab=47b55ed7
-/
theorem pres_isRComb {G : Set (NSPres T ρ 2)} (hG : RotClosed G)
    (hgen : ∀ (n : ℕ) (g : T n), IsRComb G ⟨n, NSPres.gen g⟩) (X : Arr (NSPres T ρ)) :
    IsRComb G X :=
  pres_induction isRComb_one hgen (fun _ _ _ ha hX hY => isRComb_comp hG hX hY ha) X

end Pres

end Arr

end NSSetOperad

end Operad

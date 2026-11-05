import Tengoku.NsP23.P23.OneTie.TopDeletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Type-three pure fibre products

This is the direct combinatorial replacement for the paper's two-variable
Koszul/Tor count.  Two incomparable plane roots are put in increasing
`x`-order; liveness forces their `y`-coordinates into the single wrapped
strip.  The exact five-point border is then checked symbolically.
-/

namespace P23.OneTie

variable {a b px py qx qy k : ℕ} [NeZero a]

private theorem fibre_a_pos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)

def fibrePlaneLeft (px py : ℕ) (hpx : px < a) : Normal a b 0 :=
  ⟨px, py, 0, hpx⟩

def fibrePlaneRight (qx qy : ℕ) (hqx : qx < a) : Normal a b 0 :=
  ⟨qx, qy, 0, hqx⟩

def fibreZRoot (k : ℕ) : Normal a b 0 := ⟨0, 0, k, fibre_a_pos⟩

def fibreMiddleBorder (px qy : ℕ) (hpx : px + 1 < a) : Normal a b 0 :=
  ⟨px + 1, qy + 1, 0, hpx⟩

def fibreXZ (ha : 2 ≤ a) : Normal a b 0 := ⟨1, 0, 1, by omega⟩
def fibreYZ : Normal a b 0 := ⟨0, 1, 1, fibre_a_pos⟩
def fibreZNext (k : ℕ) : Normal a b 0 := ⟨0, 0, k + 1, fibre_a_pos⟩

def pureFibreProductSocles (px py qx qy k : ℕ)
    (hpx : px < a) (hqx : qx < a) : Finset (Normal a b 0) :=
  {fibrePlaneLeft px py hpx, fibrePlaneRight qx qy hqx, fibreZRoot k}

def fibreOuterBorder (py qx qy : ℕ) (hqx : qx < a) : Normal a b 0 :=
  if hlast : qx < a - 1 then
    ⟨qx + 1, py + 1 - b, 0, by omega⟩
  else
    ⟨0, py + 1, 0, fibre_a_pos⟩

def pureFibreProductExpectedBorder (px py qx qy k : ℕ)
    (ha : 2 ≤ a) (hpx : px + 1 < a) (hqx : qx < a) : Finset (Normal a b 0) :=
  {fibreMiddleBorder px qy hpx,
    fibreOuterBorder py qx qy hqx,
    (fibreXZ (a := a) (b := b) ha),
    (fibreYZ (a := a) (b := b)),
    fibreZNext k}

private def fibreStd (b px py qx qy k x y z : ℕ) : Prop :=
  ((x ≤ px ∧ y ≤ py ∧ z = 0) ∨
    (px < x ∧ y + b ≤ py ∧ z = 0)) ∨
  ((x ≤ qx ∧ y ≤ qy ∧ z = 0) ∨
    (qx < x ∧ y + b ≤ qy ∧ z = 0)) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ k)

private def fibreBorder (a b px py qx qy k x y z : ℕ) : Prop :=
  (x = px + 1 ∧ y = qy + 1 ∧ z = 0) ∨
  ((qx < a - 1 ∧ x = qx + 1 ∧ y = py + 1 - b ∧ z = 0) ∨
    (¬qx < a - 1 ∧ x = 0 ∧ y = py + 1 ∧ z = 0)) ∨
  (x = 1 ∧ y = 0 ∧ z = 1) ∨
  (x = 0 ∧ y = 1 ∧ z = 1) ∨
  (x = 0 ∧ y = 0 ∧ z = k + 1)

set_option maxHeartbeats 6400000 in
private theorem fibre_border_arithmetic
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpxq : px < qx) (hqyp : qy < py) (hstrip : py < qy + b)
    (hlive : b ≤ py) (hk : 1 ≤ k)
    (x y z : ℕ) (hxlt : x < a) :
    ((¬fibreStd b px py qx qy k x y z ∧
      (if 0 < x then fibreStd b px py qx qy k (x - 1) y z
       else if b ≤ y ∧ 0 ≤ z then
         fibreStd b px py qx qy k (a - 1) (y - b) z
       else True) ∧
      (0 < y → fibreStd b px py qx qy k x (y - 1) z) ∧
      (0 < z → fibreStd b px py qx qy k x y (z - 1))) ↔
      fibreBorder a b px py qx qy k x y z) := by
  by_cases hx : 0 < x <;> by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
    by_cases hqxlast : qx < a - 1 <;>
    simp [fibreStd, fibreBorder, hx, hy, hz, hqxlast] <;>
    grind (splits := 64)

/--
@isnad1 id=eq.9h7v.s7.2c568e60b575 from=translated src=- shape=fa9bc404 vocab=31a9fab6
-/
theorem pureFibreProduct_border_exact
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpx : px < a) (hqx : qx < a)
    (hpxq : px < qx) (hqyp : qy < py) (hstrip : py < qy + b)
    (hlive : b ≤ py) (hk : 1 ≤ k) :
    borderFinset (pureFibreProductSocles (a := a) (b := b)
      px py qx qy k hpx hqx) =
      pureFibreProductExpectedBorder (a := a) (b := b)
        px py qx qy k ha (by omega) hqx := by
  let S := pureFibreProductSocles (a := a) (b := b)
    px py qx qy k hpx hqx
  let G := pureFibreProductExpectedBorder (a := a) (b := b)
    px py qx qy k ha (by omega) hqx
  apply borderFinset_eq_expected_of_nat S G
    (fibreStd b px py qx qy k) (fibreBorder a b px py qx qy k)
  · simp [S, pureFibreProductSocles]
  · intro p
    rcases p with ⟨x, y, z, hx⟩
    simp [S, pureFibreProductSocles, fibrePlaneLeft, fibrePlaneRight,
      fibreZRoot, standardSet, Normal.exact_divides_iff,
      Normal.DividesCriterion, fibreStd]
    omega
  · intro m
    rcases m with ⟨x, y, z, hx⟩
    by_cases hlast : qx < a - 1 <;>
      simp [G, pureFibreProductExpectedBorder, fibreMiddleBorder,
        fibreOuterBorder, fibreXZ, fibreYZ, fibreZNext, fibreBorder, hlast,
        Normal.mk.injEq]
  · exact fibre_border_arithmetic ha hb hpxq hqyp hstrip hlive hk

/--
@isnad1 id=eq.9h7v.s7.9e959c2b9b7d from=translated src=- shape=c556f4c8 vocab=5c7a32cd
-/
theorem pureFibreProduct_border_card
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpx : px < a) (hqx : qx < a)
    (hpxq : px < qx) (hqyp : qy < py) (hstrip : py < qy + b)
    (hlive : b ≤ py) (hk : 1 ≤ k) :
    (borderFinset (pureFibreProductSocles (a := a) (b := b)
      px py qx qy k hpx hqx)).card = 5 := by
  rw [pureFibreProduct_border_exact ha hb hpx hqx hpxq hqyp hstrip hlive hk]
  unfold pureFibreProductExpectedBorder
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
  · simp
  all_goals
    by_cases hlast : qx < a - 1 <;>
      simp [fibreMiddleBorder, fibreOuterBorder, fibreXZ, fibreYZ,
        fibreZNext, hlast, Normal.mk.injEq] <;> omega

/--
@isnad1 id=ne.9h7v.s7.e8ac3edb8414 from=translated src=- shape=c556f4c8 vocab=5c7a32cd
-/
theorem pureFibreProduct_border_card_ne_four
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hpx : px < a) (hqx : qx < a)
    (hpxq : px < qx) (hqyp : qy < py) (hstrip : py < qy + b)
    (hlive : b ≤ py) (hk : 1 ≤ k) :
    (borderFinset (pureFibreProductSocles (a := a) (b := b)
      px py qx qy k hpx hqx)).card ≠ 4 := by
  rw [pureFibreProduct_border_card ha hb hpx hqx hpxq hqyp hstrip hlive hk]
  omega

/-- The frozen abstract fibre-product shape has exactly two plane roots; the
antichain and live-tie hypotheses put them in the ordered strip used above.
@isnad1 id=ex.5h3v.s7.9a4c29b3a4c8 from=translated src=- shape=c43f6542 vocab=a1261e6e
-/
theorem pureFibreProduct_ordered_parameters
    {S : Finset (Normal a b 0)}
    (hb : 2 ≤ b) (hcard : S.card = 3)
    (hshape : IsPureFibreProduct S)
    (hanti : IsRootAntichain S) (hlive : IsLiveTie S) :
    ∃ px py qx qy k hpx hqx,
      1 ≤ k ∧ px < qx ∧ qy < py ∧ py < qy + b ∧ b ≤ py ∧
      S = pureFibreProductSocles (a := a) (b := b)
        px py qx qy k hpx hqx := by
  rcases hshape with ⟨_, k, hk, hZS, hplane⟩
  let Z : Normal a b 0 := fibreZRoot (a := a) (b := b) k
  have hZdef : Z = (⟨0, 0, k, fibre_a_pos⟩ : Normal a b 0) := rfl
  have hZmem : Z ∈ S := by simpa [Z, fibreZRoot] using hZS
  have heraseCard : (S.erase Z).card = 2 := by
    rw [Finset.card_erase_of_mem hZmem, hcard]
  rcases Finset.card_eq_two.mp heraseCard with ⟨P, Q, hPQ, herase⟩
  have hPS : P ∈ S := Finset.mem_of_mem_erase (by rw [herase]; simp)
  have hQS : Q ∈ S := Finset.mem_of_mem_erase (by rw [herase]; simp)
  have hPZ : P ≠ Z := Finset.ne_of_mem_erase (by rw [herase]; simp)
  have hQZ : Q ≠ Z := Finset.ne_of_mem_erase (by rw [herase]; simp)
  have hPz : P.z = 0 := hplane P hPS (by simpa [Z, fibreZRoot] using hPZ)
  have hQz : Q.z = 0 := hplane Q hQS (by simpa [Z, fibreZRoot] using hQZ)
  have hxne : P.x ≠ Q.x := by
    intro hx
    by_cases hy : P.y ≤ Q.y
    · exact (hanti P hPS Q hQS hPQ) ((Normal.exact_divides_iff P Q).2 (by
        simp [Normal.DividesCriterion, hx, hPz, hQz, hy]))
    · exact (hanti Q hQS P hPS hPQ.symm) ((Normal.exact_divides_iff Q P).2 (by
        simp [Normal.DividesCriterion, hx, hPz, hQz]
        omega))
  have hLiveY := hlive.2.2.2
  rcases (mem_standardSet_iff S liveTiePoint).1 hLiveY with ⟨R, hRS, hdiv⟩
  have hRcases : R = Z ∨ R = P ∨ R = Q := by
    have hSin : S = insert Z (S.erase Z) := (Finset.insert_erase hZmem).symm
    rw [hSin, herase] at hRS
    simpa using hRS
  have hrootLive : b ≤ P.y ∨ b ≤ Q.y := by
    rcases hRcases with hRZ | hRP | hRQ
    · rw [hRZ] at hdiv
      have hd := (Normal.exact_divides_iff liveTiePoint Z).1 hdiv
      simp [liveTiePoint, Z, fibreZRoot, Normal.DividesCriterion] at hd
      omega
    · left
      rw [hRP] at hdiv
      have hd := (Normal.exact_divides_iff liveTiePoint P).1 hdiv
      simp [liveTiePoint, Normal.DividesCriterion] at hd
      omega
    · right
      rw [hRQ] at hdiv
      have hd := (Normal.exact_divides_iff liveTiePoint Q).1 hdiv
      simp [liveTiePoint, Normal.DividesCriterion] at hd
      omega
  have hSinsert : S = ({P, Q, Z} : Finset (Normal a b 0)) := by
    rw [show S = insert Z (S.erase Z) from (Finset.insert_erase hZmem).symm,
      herase]
    ext X
    simp [or_assoc, or_left_comm, or_comm]
  by_cases hx : P.x < Q.x
  · have hy : Q.y < P.y := by
      by_contra h
      have hle : P.y ≤ Q.y := by omega
      exact (hanti P hPS Q hQS hPQ) ((Normal.exact_divides_iff P Q).2 (by
        simp [Normal.DividesCriterion, hPz, hQz, hle]
        omega))
    have hstrip : P.y < Q.y + b := by
      by_contra h
      have hle : Q.y + b ≤ P.y := by omega
      exact (hanti Q hQS P hPS hPQ.symm) ((Normal.exact_divides_iff Q P).2 (by
        simp [Normal.DividesCriterion, hPz, hQz, hle]
        omega))
    have hbP : b ≤ P.y := by rcases hrootLive with h | h <;> omega
    refine ⟨P.x, P.y, Q.x, Q.y, k, P.x_lt, Q.x_lt, hk, hx, hy,
      hstrip, hbP, ?_⟩
    rw [hSinsert]
    ext R
    simp [pureFibreProductSocles, fibrePlaneLeft, fibrePlaneRight,
      Z, fibreZRoot, hPz, hQz, Normal.ext_iff]
  · have hx' : Q.x < P.x := by omega
    have hy : P.y < Q.y := by
      by_contra h
      have hle : Q.y ≤ P.y := by omega
      exact (hanti Q hQS P hPS hPQ.symm) ((Normal.exact_divides_iff Q P).2 (by
        simp [Normal.DividesCriterion, hPz, hQz, hle]
        omega))
    have hstrip : Q.y < P.y + b := by
      by_contra h
      have hle : P.y + b ≤ Q.y := by omega
      exact (hanti P hPS Q hQS hPQ) ((Normal.exact_divides_iff P Q).2 (by
        simp [Normal.DividesCriterion, hPz, hQz, hle]
        omega))
    have hbQ : b ≤ Q.y := by rcases hrootLive with h | h <;> omega
    refine ⟨Q.x, Q.y, P.x, P.y, k, Q.x_lt, P.x_lt, hk, hx', hy,
      hstrip, hbQ, ?_⟩
    rw [hSinsert]
    ext R
    simp [pureFibreProductSocles, fibrePlaneLeft, fibrePlaneRight,
      Z, fibreZRoot, hPz, hQz, Normal.ext_iff, or_left_comm]

/--
@isnad1 id=ex.6h3v.s7.9f0cba924bfa from=translated src=- shape=53f48d3f vocab=076e512f
-/
theorem pureFibreProductShape_border_exact
    {S : Finset (Normal a b 0)}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hcard : S.card = 3)
    (hshape : IsPureFibreProduct S)
    (hanti : IsRootAntichain S) (hlive : IsLiveTie S) :
    ∃ (px py qx qy k : ℕ) (hpx : px < a) (hqx : qx < a)
        (hpxq : px < qx),
      S = pureFibreProductSocles (a := a) (b := b)
          px py qx qy k hpx hqx ∧
      borderFinset S = pureFibreProductExpectedBorder (a := a) (b := b)
          px py qx qy k ha (by omega) hqx := by
  rcases pureFibreProduct_ordered_parameters hb hcard hshape hanti hlive with
    ⟨px, py, qx, qy, k, hpx, hqx, hk, hpxq, hqyp, hstrip, hliveP, rfl⟩
  exact ⟨px, py, qx, qy, k, hpx, hqx, hpxq, rfl,
    pureFibreProduct_border_exact ha hb hpx hqx hpxq hqyp hstrip hliveP hk⟩

/--
@isnad1 id=eq.6h3v.s6.61d2569dd0cd from=translated src=- shape=d393f8df vocab=b153a13f
-/
theorem pureFibreProductShape_border_card
    {S : Finset (Normal a b 0)}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hcard : S.card = 3)
    (hshape : IsPureFibreProduct S)
    (hanti : IsRootAntichain S) (hlive : IsLiveTie S) :
    (borderFinset S).card = 5 := by
  rcases pureFibreProduct_ordered_parameters hb hcard hshape hanti hlive with
    ⟨px, py, qx, qy, k, hpx, hqx, hk, hpxq, hqyp, hstrip, hliveP, rfl⟩
  exact pureFibreProduct_border_card ha hb hpx hqx hpxq hqyp hstrip hliveP hk

/--
@isnad1 id=ne.6h3v.s6.d45e1c5d009b from=translated src=- shape=4f9b7a3b vocab=b153a13f
-/
theorem pureFibreProductShape_border_card_ne_four
    {S : Finset (Normal a b 0)}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hcard : S.card = 3)
    (hshape : IsPureFibreProduct S)
    (hanti : IsRootAntichain S) (hlive : IsLiveTie S) :
    (borderFinset S).card ≠ 4 := by
  rw [pureFibreProductShape_border_card ha hb hcard hshape hanti hlive]
  omega

end P23.OneTie

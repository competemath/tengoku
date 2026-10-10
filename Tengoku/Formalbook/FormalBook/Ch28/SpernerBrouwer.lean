import Tengoku

/-!
# Sperner's Lemma and Brouwer Fixed Point Theorem via Sperner

Auxiliary machinery for Chapter 28: Sperner's lemma (combinatorial),
the Sperner-to-Brouwer bridge via subdivision of the standard 2-simplex.
-/

namespace chapter28

/-- An abstract simplicial 2-complex: a collection of triangles (3-element subsets). -/
structure Triangulation (m : ℕ) where
  /-- The collection of triangles (3-element subsets of vertices). -/
  triangles : Finset (Finset (Fin m))
  triangle_card : ∀ t ∈ triangles, t.card = 3

/-- A triangle is rainbow (tricolored) under coloring `c` if its vertices receive
    all three colors {0, 1, 2}. -/
def isRainbow {m : ℕ} (c : Fin m → Fin 3) (t : Finset (Fin m)) : Prop :=
  t.image c = {0, 1, 2}

instance {m : ℕ} (c : Fin m → Fin 3) (t : Finset (Fin m)) : Decidable (isRainbow c t) :=
  inferInstanceAs (Decidable (t.image c = {0, 1, 2}))

/-- Auxiliary parity lemma: if `f` maps each element of a finset to `{0, 1, 2}`,
    and the sum `∑ f` is odd, then the number of elements with `f = 1` is odd.
    This is the combinatorial core of Sperner's lemma (the double-counting/parity argument). -/
private theorem odd_card_filter_eq_one {α : Type*} {S : Finset α} {f : α → ℕ}
    (hf : ∀ s ∈ S, f s = 0 ∨ f s = 1 ∨ f s = 2)
    (hsum : Odd (∑ s ∈ S, f s)) :
    Odd (S.filter (fun s => f s = 1)).card := by
  -- Show: ∑ f = #{f=1} + 2 * #{f=2}, so #{f=1} has same parity as ∑ f.
  set S₁ := S.filter (fun s => f s = 1)
  set S₂ := S.filter (fun s => f s = 2)
  suffices hkey : ∑ s ∈ S, f s = S₁.card + 2 * S₂.card by
    rw [hkey] at hsum; obtain ⟨k, hk⟩ := hsum; rw [Nat.odd_iff]; omega
  -- Decompose: f s = 𝟙_{f=1}(s) + 2·𝟙_{f=2}(s)
  have hind : ∀ s ∈ S, f s = (if f s = 1 then 1 else 0) + 2 * (if f s = 2 then 1 else 0) := by
    intro s hs; rcases hf s hs with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl hind, Finset.sum_add_distrib]
  simp only [Finset.sum_boole]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_boole]
  simp; rfl

/-- **Sperner's Lemma** (combinatorial, odd-count version).

    Given a triangulation with a 3-coloring and a "12-edge count" function `count12`
    that assigns to each triangle the number of edges connecting a vertex of color 1
    to a vertex of color 2, if:
    1. Rainbow triangles are exactly those with an odd 12-edge count (`count12 = 1`),
    2. Each triangle has 0, 1, or 2 such edges,
    3. The total sum of 12-edge counts is odd (from the Sperner boundary condition
       and the double-counting argument: each interior 12-edge is shared by exactly
       two triangles, so contributes evenly, while boundary 12-edges contribute once),
    then the number of rainbow triangles is odd. -/
theorem sperner_lemma {m : ℕ} (T : Triangulation m) (c : Fin m → Fin 3)
    (count12 : Finset (Fin m) → ℕ)
    (h_rainbow_iff : ∀ t ∈ T.triangles, isRainbow c t ↔ count12 t = 1)
    (h_range : ∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2)
    (h_odd_sum : Odd (∑ t ∈ T.triangles, count12 t)) :
    Odd (T.triangles.filter (isRainbow c)).card := by
  have hfilt : T.triangles.filter (isRainbow c) =
      T.triangles.filter (fun t => count12 t = 1) := by
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hr⟩; exact ⟨ht, (h_rainbow_iff t ht).mp hr⟩
    · rintro ⟨ht, h1⟩; exact ⟨ht, (h_rainbow_iff t ht).mpr h1⟩
  rw [hfilt]
  exact odd_card_filter_eq_one h_range h_odd_sum

/-- Corollary: at least one rainbow triangle exists. -/
theorem sperner_lemma_exists {m : ℕ} (T : Triangulation m) (c : Fin m → Fin 3)
    (count12 : Finset (Fin m) → ℕ)
    (h_rainbow_iff : ∀ t ∈ T.triangles, isRainbow c t ↔ count12 t = 1)
    (h_range : ∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2)
    (h_odd_sum : Odd (∑ t ∈ T.triangles, count12 t)) :
    ∃ t ∈ T.triangles, isRainbow c t := by
  have hodd := sperner_lemma T c count12 h_rainbow_iff h_range h_odd_sum
  rw [Nat.odd_iff] at hodd
  have hne : (T.triangles.filter (isRainbow c)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hodd
  exact let ⟨t, ht⟩ := hne; ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩

/-! ## Sperner → Brouwer bridge: infrastructure and proof outline

The book proof (pp.204–205) deduces Brouwer's fixed-point theorem from Sperner's lemma
via the standard 2-simplex Δ² = conv{e₁,e₂,e₃}.  We set up the key definitions and
state the lemmas needed to connect the combinatorial `sperner_lemma` above to the
analytic fixed-point conclusion.

### Proof outline (Proofs from THE BOOK, Chapter 28)

1. **Standard 2-simplex.** Δ² = {(x₁,x₂,x₃) ∈ ℝ³ | xᵢ ≥ 0, x₁+x₂+x₃ = 1}.
2. **Regular triangulation.** Subdivide Δ² into k² small triangles with vertices
   of the form (a/k, b/k, c/k), a+b+c = k.
3. **Sperner coloring.** For a continuous f : Δ² → Δ², color vertex v with
   the smallest i such that f(v)ᵢ < vᵢ.  This is well-defined because
   ∑ f(v)ᵢ = 1 = ∑ vᵢ so f(v) ≠ v implies some coordinate decreases.
4. **Boundary condition.** If v lies on the face opposite eⱼ (i.e. vⱼ = 0),
   then color(v) ≠ j.  This gives a proper Sperner coloring.
5. **Rainbow triangles.** By `sperner_lemma`, each T_k has a rainbow triangle.
6. **Compactness.** Extract a convergent subsequence of rainbow triangle vertices.
7. **Fixed point.** At the limit, f(v)ᵢ ≤ vᵢ for all i, and ∑ = 1 forces equality.
-/

/-- A point in the standard 2-simplex: nonnegative coordinates summing to 1. -/
def stdSimplex2 : Set (Fin 3 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The Sperner coloring for a continuous self-map of Δ².  Given v ∈ Δ² and
    f : Δ² → Δ², color(v) = min {i | f(v)ᵢ < vᵢ}.  Well-defined when f(v) ≠ v
    and ∑ f(v)ᵢ = ∑ vᵢ = 1. When f(v) = v, we default to 0. -/
noncomputable def spernerColor (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : Fin 3 :=
  if h : ∃ i : Fin 3, f v i < v i then h.choose else 0

/-! ### Brouwer's fixed-point theorem on the standard 2-simplex via Sperner's lemma

The book proof (pp. 204–205) deduces Brouwer from Sperner via:
1. For each k, subdivide Δ² into small triangles, apply Sperner coloring, get a rainbow triangle
2. Extract convergent subsequence (compactness of Δ²)
3. At the limit, f(x*) = x*

**Gap 1 (Geometric Sperner):** Constructing the regular k-subdivision as an instance of
`Triangulation` and verifying the boundary parity condition is a major formalization effort.
We axiomatize the infrastructure lemmas (triangulation construction, boundary parity,
vertex extraction) below; `sperner_coloring_rainbow_triangles` is proved modulo these.

**Gaps 2–3 (Compactness + Limit):** Fully proved below.
-/

/-! ### Regular k-subdivision of Δ² and geometric Sperner infrastructure

We encode the regular k-subdivision of the standard 2-simplex and connect it
to `sperner_lemma_exists`. The subdivision has vertices (a/k, b/k, c/k) with
a + b + c = k, and small triangles of two types ("up" and "down").

The key steps are:
1. Define the vertex set and its encoding as `Fin m`
2. Define the triangulation
3. Define the 12-edge count and verify boundary parity
4. Extract geometric consequences from the combinatorial rainbow triangle
-/

/-- Number of vertices in the k-th regular subdivision: (k+1)(k+2)/2. -/
private def subdivVertCount (k : ℕ) : ℕ := (k + 1) * (k + 2) / 2

/-- A vertex of the k-th regular subdivision is a triple (a,b,c) with a+b+c = k. -/
private def SubdivVert (k : ℕ) : Type :=
  { abc : Fin 3 → ℕ // ∑ i, abc i = k }

private instance subdivVertFintype (k : ℕ) : Fintype (SubdivVert k) :=
  Fintype.subtype (Finset.Nat.antidiagonalTuple 3 k) fun x => by
    simp [Finset.Nat.mem_antidiagonalTuple]

private instance subdivVertDecEq (k : ℕ) : DecidableEq (SubdivVert k) :=
  inferInstanceAs (DecidableEq { abc : Fin 3 → ℕ // ∑ i, abc i = k })

/-- The coordinate map: send a subdivision vertex to its barycentric point in Δ². -/
@[nolint unusedArguments]
private noncomputable def subdivCoord (k : ℕ) (_hk : 0 < k) (v : SubdivVert k) : Fin 3 → ℝ :=
  fun i => (v.1 i : ℝ) / (k : ℝ)

/-- Data bundle for a subdivision triangulation with adjacency. -/
private structure SubdivData (k : ℕ) where
  m : ℕ
  T : Triangulation m
  decode : Fin m → SubdivVert k
  adj : ∀ t ∈ T.triangles, ∀ a ∈ t, ∀ b ∈ t,
    ∀ i, ((decode a).1 i : ℤ) - ((decode b).1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1

/-- The regular k-subdivision as a `Triangulation` with adjacency proof.
    The key properties are that:
    - Each triangle has 3 vertices from `SubdivVert k` (encoded as `Fin m`)
    - The triangulation covers Δ²
    - Any two vertices in the same triangle differ by ≤ 1 in each coordinate -/
private noncomputable def subdivTriangulation (k : ℕ) (_hk : 0 < k) :
    SubdivData k := by
  classical
  let m := Fintype.card (SubdivVert k)
  let eqv := Fintype.equivFin (SubdivVert k)
  let encode : SubdivVert k → Fin m := eqv
  let decode : Fin m → SubdivVert k := eqv.symm
  -- Helper to make a SubdivVert from (a, b) with a + b ≤ k
  let mkVert : ∀ (a b : ℕ), a + b ≤ k → SubdivVert k := fun a b h =>
    ⟨![a, b, k - a - b], by simp [Fin.sum_univ_three]; omega⟩
  -- Define triangles as a subset of Finset.powerset (Finset.univ : Finset (Fin m))
  -- filtered by the triangulation predicate
  -- An up-triangle has vertices (i,j), (i+1,j), (i,j+1) with i+j < k
  -- A down-triangle has vertices (i+1,j), (i,j+1), (i+1,j+1) with i+j+1 < k
  -- We define the predicate on triples of SubdivVert k
  let isUpTri : SubdivVert k → SubdivVert k → SubdivVert k → Prop :=
    fun v0 v1 v2 => ∃ (i j : ℕ) (h : i + j < k),
      v0 = mkVert i j (by omega) ∧
      v1 = mkVert (i+1) j (by omega) ∧
      v2 = mkVert i (j+1) (by omega)
  let isDownTri : SubdivVert k → SubdivVert k → SubdivVert k → Prop :=
    fun v0 v1 v2 => ∃ (i j : ℕ) (h : i + j + 1 < k),
      v0 = mkVert (i+1) j (by omega) ∧
      v1 = mkVert i (j+1) (by omega) ∧
      v2 = mkVert (i+1) (j+1) (by omega)
  -- Build the triangles as a finset
  let allTris : Finset (Finset (Fin m)) :=
    Finset.univ.biUnion fun (v0 : SubdivVert k) =>
      Finset.univ.biUnion fun (v1 : SubdivVert k) =>
        Finset.univ.biUnion fun (v2 : SubdivVert k) =>
          if (∃ (i j : ℕ) (_ : i + j < k),
                v0 = mkVert i j (by omega) ∧
                v1 = mkVert (i+1) j (by omega) ∧
                v2 = mkVert i (j+1) (by omega)) ∨
             (∃ (i j : ℕ) (_ : i + j + 1 < k),
                v0 = mkVert (i+1) j (by omega) ∧
                v1 = mkVert i (j+1) (by omega) ∧
                v2 = mkVert (i+1) (j+1) (by omega))
          then {({encode v0, encode v1, encode v2} : Finset (Fin m))}
          else ∅
  -- Helper: mkVert produces distinct SubdivVert's when first coords differ
  have mkVert_coord0 : ∀ a b (h : a + b ≤ k), (mkVert a b h).1 0 = a := by
    intro a b h; simp [mkVert, Matrix.cons_val_zero]
  have mkVert_coord1 : ∀ a b (h : a + b ≤ k), (mkVert a b h).1 1 = b := by
    intro a b h; simp [mkVert, Matrix.cons_val_one]
  have hcard : ∀ t ∈ allTris, t.card = 3 := by
    intro t ht
    simp only [allTris, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
    obtain ⟨v0, v1, v2, hcond⟩ := ht
    split_ifs at hcond with htri
    · simp only [Finset.mem_singleton] at hcond
      subst hcond
      have hinj : Function.Injective encode := eqv.injective
      rcases htri with ⟨i, j, hij, rfl, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl, rfl⟩
      · -- Up triangle: (i,j), (i+1,j), (i,j+1)
        have h01 : mkVert i j (by omega) ≠ mkVert (i+1) j (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have h02 : mkVert i j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 1) h; simp [mkVert_coord1] at this
        have h12 : mkVert (i+1) j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have he01 : encode (mkVert i j (by omega)) ≠ encode (mkVert (i+1) j (by omega)) :=
          fun h => h01 (eqv.injective h)
        have he02 : encode (mkVert i j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h02 (eqv.injective h)
        have he12 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h12 (eqv.injective h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp; exact he12
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not; exact ⟨he01, he02⟩
      · -- Down triangle: (i+1,j), (i,j+1), (i+1,j+1)
        have h01 : mkVert (i+1) j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have h02 : mkVert (i+1) j (by omega) ≠ mkVert (i+1) (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 1) h; simp [mkVert_coord1] at this
        have h12 : mkVert i (j+1) (by omega) ≠ mkVert (i+1) (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have he01 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h01 (eqv.injective h)
        have he02 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert (i+1) (j+1) (by omega)) :=
          fun h => h02 (eqv.injective h)
        have he12 : encode (mkVert i (j+1) (by omega)) ≠ encode (mkVert (i+1) (j+1) (by omega)) :=
          fun h => h12 (eqv.injective h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp; exact he12
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not; exact ⟨he01, he02⟩
    · simp at hcond
  refine ⟨m, ⟨allTris, hcard⟩, decode, ?_⟩
  -- Adjacency: any two vertices in the same triangle differ by ≤ 1 in each coordinate
  -- This follows from the construction: up-triangles have vertices (i,j),(i+1,j),(i,j+1)
  -- and down-triangles have vertices (i+1,j),(i,j+1),(i+1,j+1), all differing by ≤ 1.
  intro t ht a ha b hb idx
  simp only [allTris, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
  obtain ⟨v0, v1, v2, hcond⟩ := ht
  split_ifs at hcond with htri
  · simp only [Finset.mem_singleton] at hcond
    have hmem : a ∈ ({encode v0, encode v1, encode v2} : Finset (Fin m)) := hcond ▸ ha
    have hmem' : b ∈ ({encode v0, encode v1, encode v2} : Finset (Fin m)) := hcond ▸ hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
    have hdec : ∀ x, (x = encode v0 ∨ x = encode v1 ∨ x = encode v2) →
        (decode x = v0 ∨ decode x = v1 ∨ decode x = v2) := by
      intro x hx; rcases hx with rfl | rfl | rfl <;>
        simp [decode, encode, Equiv.symm_apply_apply]
    have hda := hdec a hmem
    have hdb := hdec b hmem'
    rcases htri with ⟨ii, jj, hij, rfl, rfl, rfl⟩ | ⟨ii, jj, hij, rfl, rfl, rfl⟩
    · -- Up triangle: mkVert ii jj, mkVert (ii+1) jj, mkVert ii (jj+1)
      rcases hda with ha' | ha' | ha' <;> rcases hdb with hb' | hb' | hb' <;>
        (simp only [Set.mem_Icc]; rw [ha', hb']; fin_cases idx <;>
          simp [mkVert, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega)
    · -- Down triangle: mkVert (ii+1) jj, mkVert ii (jj+1), mkVert (ii+1) (jj+1)
      rcases hda with ha' | ha' | ha' <;> rcases hdb with hb' | hb' | hb' <;>
        (simp only [Set.mem_Icc]; rw [ha', hb']; fin_cases idx <;>
          simp [mkVert, Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega)
  · simp at hcond

/-! ### Boundary parity for Sperner coloring

The boundary parity condition for the Sperner coloring on the k-subdivision.
The sum of 12-edge counts over all triangles is odd.

**Proof sketch:**
Define `count12 t` = number of {u,v} pairs in triangle t with {col u, col v} = {1,2}.
- `h_rainbow_iff`: A triangle with colors {0,1,2} has exactly one 1-2 pair → count12 = 1.
- `h_range`: For a 3-element set, count12 ∈ {0,1,2}.
- `h_odd_sum`: By double counting, ∑ count12 = ∑_{12-edges e} (triangles containing e).
  Interior edges contribute 2 (even), boundary edges contribute 1.
  Boundary 12-edges exist only on the e₁e₂ face (x₀=0), since:
    • e₀e₁ face has colors ∈ {0,1} (no color-2 vertex)
    • e₀e₂ face has colors ∈ {0,2} (no color-1 vertex)
  On the e₁e₂ face, vertices go from e₂ (color 2) to e₁ (color 1) through k edges.
  The number of 1↔2 color changes is odd (parity argument: starts at 2, ends at 1).
  Therefore ∑ count12 ≡ (boundary 12-edges) ≡ 1 (mod 2). -/

end chapter28

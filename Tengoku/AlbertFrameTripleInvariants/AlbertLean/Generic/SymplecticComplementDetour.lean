import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticComplementFixing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_detour_orthogonal_one_pair` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_detour_orthogonal_two_pairs` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/--
@isnad1 id=ex.10h7v.s12.bd0d56ed4782 from=translated src=- shape=06071fb8 vocab=dc8be386
-/
theorem exists_detour_orthogonal_one_pair
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (e f x y : V) (hef : omega e f = 1)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : omega e x = 0) (hfx : omega f x = 0)
    (hye : omega y e = 0) (hyf : omega y f = 0) :
    ∃ z, omega z x ≠ 0 ∧ omega y z ≠ 0 ∧
      omega z e = 0 ∧ omega z f = 0 := by
  obtain ⟨zx, hzx⟩ := hleft x hx
  obtain ⟨zy, hzy⟩ := hright y hy
  let px := projectPair omega e f zx
  let py := projectPair omega e f zy
  have hpxx : omega px x ≠ 0 := by
    rw [projectPair_pairing_right omega e f zx x hex hfx]
    exact hzx
  have hypy : omega y py ≠ 0 := by
    rw [projectPair_pairing_left omega e f zy y hye hyf]
    exact hzy
  obtain ⟨z, hzmem, hzx', hyz'⟩ :=
    common_detour_of_two_witnesses omega x y px py hpxx hypy
  refine ⟨z, hzx', hyz', ?_⟩
  have hpx : omega px e = 0 ∧ omega px f = 0 := by
    dsimp [px]
    exact projectPair_orthogonal omega halt e f zx hef
  have hpy : omega py e = 0 ∧ omega py f = 0 := by
    dsimp [py]
    exact projectPair_orthogonal omega halt e f zy hef
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hzmem
  rcases hzmem with rfl | rfl | rfl
  · exact hpx
  · exact hpy
  · constructor <;>
      simp only [map_add, LinearMap.add_apply, hpx.1, hpx.2, hpy.1, hpy.2,
        zero_add]

/--
@isnad1 id=ex.19h9v.s13.c662b69041b0 from=translated src=- shape=6f0539ed vocab=dc8be386
-/
theorem exists_detour_orthogonal_two_pairs
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (e0 f0 e1 f1 x y : V) (hef0 : omega e0 f0 = 1)
    (hef1 : omega e1 f1 = 1) (hx : x ≠ 0) (hy : y ≠ 0)
    (h10e : omega e1 e0 = 0) (h10f : omega f1 e0 = 0)
    (h11e : omega e1 f0 = 0) (h11f : omega f1 f0 = 0)
    (he0x : omega e0 x = 0) (hf0x : omega f0 x = 0)
    (he1x : omega e1 x = 0) (hf1x : omega f1 x = 0)
    (hye0 : omega y e0 = 0) (hyf0 : omega y f0 = 0)
    (hye1 : omega y e1 = 0) (hyf1 : omega y f1 = 0) :
    ∃ z, omega z x ≠ 0 ∧ omega y z ≠ 0 ∧
      omega z e0 = 0 ∧ omega z f0 = 0 ∧
      omega z e1 = 0 ∧ omega z f1 = 0 := by
  obtain ⟨zx, hzx⟩ := hleft x hx
  obtain ⟨zy, hzy⟩ := hright y hy
  let proj : V → V := fun c =>
    projectPair omega e1 f1 (projectPair omega e0 f0 c)
  have proj_pairing_right (c : V) : omega (proj c) x = omega c x := by
    rw [projectPair_pairing_right omega e1 f1 _ x he1x hf1x,
      projectPair_pairing_right omega e0 f0 c x he0x hf0x]
  have proj_pairing_left (c : V) : omega y (proj c) = omega y c := by
    rw [projectPair_pairing_left omega e1 f1 _ y hye1 hyf1,
      projectPair_pairing_left omega e0 f0 c y hye0 hyf0]
  have proj_orthogonal (c : V) :
      omega (proj c) e0 = 0 ∧ omega (proj c) f0 = 0 ∧
        omega (proj c) e1 = 0 ∧ omega (proj c) f1 = 0 := by
    have hfirst := projectPair_orthogonal omega halt e0 f0 c hef0
    have hsecond := projectPair_orthogonal omega halt e1 f1
      (projectPair omega e0 f0 c) hef1
    refine ⟨?_, ?_, hsecond.1, hsecond.2⟩
    · rw [projectPair_pairing_right omega e1 f1 _ e0 h10e h10f]
      exact hfirst.1
    · rw [projectPair_pairing_right omega e1 f1 _ f0 h11e h11f]
      exact hfirst.2
  have hpxx : omega (proj zx) x ≠ 0 := by rw [proj_pairing_right]; exact hzx
  have hypy : omega y (proj zy) ≠ 0 := by rw [proj_pairing_left]; exact hzy
  obtain ⟨z, hzmem, hzx', hyz'⟩ := common_detour_of_two_witnesses omega x y
    (proj zx) (proj zy) hpxx hypy
  refine ⟨z, hzx', hyz', ?_⟩
  have hpx := proj_orthogonal zx
  have hpy := proj_orthogonal zy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hzmem
  rcases hzmem with rfl | rfl | rfl
  · exact hpx
  · exact hpy
  · constructor
    · simp only [map_add, LinearMap.add_apply, hpx.1, hpy.1, zero_add]
    constructor
    · simp only [map_add, LinearMap.add_apply, hpx.2.1, hpy.2.1, zero_add]
    constructor
    · simp only [map_add, LinearMap.add_apply, hpx.2.2.1, hpy.2.2.1, zero_add]
    · simp only [map_add, LinearMap.add_apply, hpx.2.2.2, hpy.2.2.2, zero_add]

end AlbertLean.Generic.SymplecticTransvection

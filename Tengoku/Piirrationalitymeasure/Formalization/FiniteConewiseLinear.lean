import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite closed polyhedral cone covers, with a linear formula on every cone. -/

namespace PiIrrationality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearCone (S : Finset (E →L[ℝ] ℝ)) : Set E :=
  {x | ∀ l ∈ S, 0 ≤ l x}

def FiniteConewiseLinear (f : E → ℝ) : Prop :=
  ∃ S : Finset (Finset (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ)),
    (∀ x : E, ∃ p ∈ S, x ∈ linearCone p.1) ∧
    ∀ p ∈ S, ∀ x ∈ linearCone p.1, f x = p.2 x

theorem linearCone_closed (S : Finset (E →L[ℝ] ℝ)) : IsClosed (linearCone S) := by
  simp only [linearCone, Set.ofPred_forall]
  exact isClosed_iInter (fun l => isClosed_iInter (fun _ =>
    isClosed_le continuous_const l.continuous))

theorem linearCone_convex (S : Finset (E →L[ℝ] ℝ)) : Convex ℝ (linearCone S) := by
  intro x hx y hy a b ha hb hab l hl
  simpa only [map_add, map_smul, smul_eq_mul] using
    add_nonneg (mul_nonneg ha (hx l hl)) (mul_nonneg hb (hy l hl))

theorem linearCone_smul (S : Finset (E →L[ℝ] ℝ)) {x : E} (hx : x ∈ linearCone S)
    {t : ℝ} (ht : 0 ≤ t) : t • x ∈ linearCone S := by
  intro l hl
  simpa only [map_smul, smul_eq_mul] using mul_nonneg ht (hx l hl)

namespace FiniteConewiseLinear

theorem linear (l : E →L[ℝ] ℝ) : FiniteConewiseLinear (fun x => l x) := by
  classical
  refine ⟨{(∅, l)}, ?_, ?_⟩
  · intro x
    exact ⟨(∅, l), by simp, by simp [linearCone]⟩
  · intro p hp x hx
    simpa using congrArg (fun p : Finset (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) => p.2 x)
      (Finset.mem_singleton.mp hp).symm

theorem add {f g : E → ℝ} (hf : FiniteConewiseLinear f) (hg : FiniteConewiseLinear g) :
    FiniteConewiseLinear (fun x => f x + g x) := by
  classical
  obtain ⟨S, hSc, hSf⟩ := hf
  obtain ⟨T, hTc, hTg⟩ := hg
  let pair := fun p q : Finset (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) =>
    (p.1 ∪ q.1, p.2 + q.2)
  refine ⟨S.image₂ pair T, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, hpx⟩ := hSc x
    obtain ⟨q, hq, hqx⟩ := hTc x
    refine ⟨pair p q, Finset.mem_image₂.mpr ⟨p, hp, q, hq, rfl⟩, ?_⟩
    intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact hpx l hl
    · exact hqx l hl
  · intro r hr x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_image₂.mp hr
    have hpx : x ∈ linearCone p.1 := fun l hl => hx l (Finset.mem_union_left _ hl)
    have hqx : x ∈ linearCone q.1 := fun l hl => hx l (Finset.mem_union_right _ hl)
    simp only [hSf p hp x hpx, hTg q hq x hqx, pair, add_apply]

theorem neg {f : E → ℝ} (hf : FiniteConewiseLinear f) :
    FiniteConewiseLinear (fun x => -f x) := by
  classical
  obtain ⟨S, hSc, hSf⟩ := hf
  let flip := fun p : Finset (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) => (p.1, -p.2)
  refine ⟨S.image flip, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, hx⟩ := hSc x
    exact ⟨flip p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hx⟩
  · intro p hp x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simp only [hSf q hq x hx, flip, neg_apply]

theorem max {f g : E → ℝ} (hf : FiniteConewiseLinear f) (hg : FiniteConewiseLinear g) :
    FiniteConewiseLinear (fun x => max (f x) (g x)) := by
  classical
  obtain ⟨S, hSc, hSf⟩ := hf
  obtain ⟨T, hTc, hTg⟩ := hg
  let left := fun p q : Finset (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) =>
    (insert (p.2 - q.2) (p.1 ∪ q.1), p.2)
  let right := fun p q : Finset (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) =>
    (insert (q.2 - p.2) (p.1 ∪ q.1), q.2)
  refine ⟨S.image₂ left T ∪ S.image₂ right T, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, hpx⟩ := hSc x
    obtain ⟨q, hq, hqx⟩ := hTc x
    by_cases hle : q.2 x ≤ p.2 x
    · refine ⟨left p q, Finset.mem_union_left _
        (Finset.mem_image₂.mpr ⟨p, hp, q, hq, rfl⟩), ?_⟩
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · simpa using sub_nonneg.mpr hle
      · rcases Finset.mem_union.mp hl with hl | hl
        · exact hpx l hl
        · exact hqx l hl
    · refine ⟨right p q, Finset.mem_union_right _
        (Finset.mem_image₂.mpr ⟨p, hp, q, hq, rfl⟩), ?_⟩
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · simpa using sub_nonneg.mpr (le_of_not_ge hle)
      · rcases Finset.mem_union.mp hl with hl | hl
        · exact hpx l hl
        · exact hqx l hl
  · intro r hr x hx
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_image₂.mp hr
      have hpx : x ∈ linearCone p.1 := fun l hl =>
        hx l (Finset.mem_insert_of_mem (Finset.mem_union_left _ hl))
      have hqx : x ∈ linearCone q.1 := fun l hl =>
        hx l (Finset.mem_insert_of_mem (Finset.mem_union_right _ hl))
      have hle : q.2 x ≤ p.2 x := sub_nonneg.mp (by
        simpa using hx (p.2 - q.2) (Finset.mem_insert_self _ _))
      exact (congrArg₂ Max.max (hSf p hp x hpx) (hTg q hq x hqx)).trans
        (max_eq_left hle)
    · obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_image₂.mp hr
      have hpx : x ∈ linearCone p.1 := fun l hl =>
        hx l (Finset.mem_insert_of_mem (Finset.mem_union_left _ hl))
      have hqx : x ∈ linearCone q.1 := fun l hl =>
        hx l (Finset.mem_insert_of_mem (Finset.mem_union_right _ hl))
      have hle : p.2 x ≤ q.2 x := sub_nonneg.mp (by
        simpa using hx (q.2 - p.2) (Finset.mem_insert_self _ _))
      exact (congrArg₂ Max.max (hSf p hp x hpx) (hTg q hq x hqx)).trans
        (max_eq_right hle)

end FiniteConewiseLinear

end PiIrrationality

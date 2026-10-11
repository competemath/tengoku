import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.Symmetry

namespace OAI

universe uE uI uV uW

open MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

abbrev FaceIndex := Fin 3 × (Fin 3 → Bool)

def QuarterFace (c : Vertex) (n : ℕ) (f : FaceIndex) : Set Vertex :=
  {x | x f.1 = c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ)) ∧
    ∀ i, i ≠ f.1 → if f.2 i then c i ≤ x i ∧ x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ x i ∧ x i ≤ c i}

def canonicalFace : FaceIndex := (0, fun _ => true)

theorem quarterFace_subset_boundary (c : Vertex) (n : ℕ) (f : FaceIndex) :
    QuarterFace c n f ⊆ cubeBoundary c n := by
  intro x hx
  refine ⟨?_,f.1,?_⟩
  · rw [mem_cube]
    intro i
    by_cases hi : i = f.1
    · subst i
      rw [hx.1]
      cases f.2 f.1 <;> simp
      omega
    · have h := hx.2 i hi
      cases hf : f.2 i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · rw [hx.1]
    cases f.2 f.1 <;> simp [sub_eq_add_neg]

theorem boundary_eq_union_quarterFace (c : Vertex) (n : ℕ) :
    cubeBoundary c n = ⋃ f : FaceIndex, QuarterFace c n f := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx,i,hi⟩
    rw [Set.mem_iUnion]
    let signs : Fin 3 → Bool := fun j => decide (c j ≤ x j)
    refine ⟨(i,signs),?_,?_⟩
    · change x i = c i + (if signs i then (n : ℤ) else -(n : ℤ))
      by_cases h : c i ≤ x i <;> simp [signs,h]
      all_goals rcases hi with hi | hi <;> omega
    · intro j _
      have hh := (mem_cube.mp hx) j
      change if signs j then c j ≤ x j ∧ x j ≤ c j + (n : ℤ)
        else c j - (n : ℤ) ≤ x j ∧ x j ≤ c j
      by_cases h : c j ≤ x j <;> simp [signs,h]
      all_goals omega
  · exact Set.iUnion_subset (quarterFace_subset_boundary c n)

theorem rtg_equiv_iff {V : Type uV} {W : Type uW} (e : V ≃ W) {r : V → V → Prop} {s : W → W → Prop}
    (h : ∀ x y, r x y ↔ s (e x) (e y)) (x y : V) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · intro hp
    exact Relation.ReflTransGen.lift e (fun a b h' => (h a b).mp h') x y hp
  · intro hp
    have hp' := Relation.ReflTransGen.lift e.symm (fun a b h' =>
      (h (e.symm a) (e.symm b)).mpr (by simpa only [Equiv.apply_symm_apply] using h'))
      (e x) (e y) hp
    simpa only [Function.onFun,Equiv.symm_apply_apply] using hp'

namespace SignedSymmetry

theorem bondWithin_map (S : SignedSymmetry) (ω : BondConfig) (c : Vertex) (n : ℕ) (x y : Vertex) :
    Within (cube c n) (BondOpen (fun e => ω (S.bond e))) x y ↔
      Within (cube (S.vertex c) n) (BondOpen ω) (S.vertex x) (S.vertex y) := by
  simp only [Within,S.cube_map c x n,S.cube_map c y n,S.bondOpen_map]

theorem siteWithin_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (n : ℕ) (x y : Vertex) :
    Within (cube c n) (SiteOpen (fun e => ω (S.vertex e))) x y ↔
      Within (cube (S.vertex c) n) (SiteOpen ω) (S.vertex x) (S.vertex y) := by
  simp only [Within,S.cube_map c x n,S.cube_map c y n,S.siteOpen_map]

theorem bondSeedReaches_map (S : SignedSymmetry) (ω : BondConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.bond e)) ∈ bondSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ bondSeedReaches (S.vertex c) m n T := by
  change (∃ x ∈ cube c m, ∃ y, S.vertex y ∈ T ∧ _) ↔ _
  simp_rw [rtg_equiv_iff S.vertex (S.bondWithin_map ω c n)]
  constructor
  · rintro ⟨x,hx,y,hy,hp⟩
    exact ⟨S.vertex x,(S.cube_map c x m).mp hx,S.vertex y,hy,hp⟩
  · rintro ⟨x,hx,y,hy,hp⟩
    refine ⟨S.vertex.symm x,?_,S.vertex.symm y,?_,?_⟩
    · exact (S.cube_map c _ m).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · simpa only [Equiv.apply_symm_apply] using hy
    · simpa only [Equiv.apply_symm_apply] using hp

theorem siteSeedReaches_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ siteSeedReaches (S.vertex c) m n T := by
  change (∃ x ∈ cube c m, ω (S.vertex x) = true ∧ ∃ y, S.vertex y ∈ T ∧ _) ↔ _
  simp_rw [rtg_equiv_iff S.vertex (S.siteWithin_map ω c n)]
  constructor
  · rintro ⟨x,hx,hw,y,hy,hp⟩
    exact ⟨S.vertex x,(S.cube_map c x m).mp hx,hw,S.vertex y,hy,hp⟩
  · rintro ⟨x,hx,hw,y,hy,hp⟩
    refine ⟨S.vertex.symm x,?_,?_,S.vertex.symm y,?_,?_⟩
    · exact (S.cube_map c _ m).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · simpa only [Equiv.apply_symm_apply] using hw
    · simpa only [Equiv.apply_symm_apply] using hy
    · simpa only [Equiv.apply_symm_apply] using hp

end SignedSymmetry

def faceSymmetry (c : Vertex) (f : FaceIndex) : SignedSymmetry :=
  ⟨Equiv.swap f.1 0, f.2, c⟩

@[simp] theorem faceSymmetry_zero (c : Vertex) (f : FaceIndex) :
    (faceSymmetry c f).vertex 0 = c := by
  funext i
  simp [faceSymmetry,SignedSymmetry.vertex]

theorem quarterFace_preimage (c : Vertex) (n : ℕ) (f : FaceIndex) :
    (faceSymmetry c f).vertex ⁻¹' QuarterFace c n f = QuarterFace 0 n canonicalFace := by
  ext x
  simp only [Set.mem_preimage,QuarterFace,Set.mem_ofPred_eq,canonicalFace,
    Pi.zero_apply,zero_add,ite_true]
  have hn : (faceSymmetry c f).vertex x f.1 =
      c f.1 + if f.2 f.1 then x 0 else -x 0 := by
    simp [faceSymmetry,SignedSymmetry.vertex]
  rw [hn]
  have hnormal : (c f.1 + (if f.2 f.1 then x 0 else -x 0) =
      c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ))) ↔ x 0 = (n : ℤ) := by
    cases f.2 f.1 <;> simp
  rw [hnormal]
  apply and_congr_right
  intro _
  have hi (i : Fin 3) :
      (if f.2 i then c i ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i) ↔
      (0 ≤ x (Equiv.swap f.1 0 i) ∧ x (Equiv.swap f.1 0 i) ≤ (n : ℤ)) := by
    change (if f.2 i then c i ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i) ↔ _
    cases f.2 i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [hi]
  constructor
  · intro h i hi
    have hh := h (Equiv.swap f.1 0 i)
    simp only [Equiv.swap_apply_self] at hh
    apply hh
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_left] at this
    exact hi this
  · intro h i hi
    apply h
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
    exact hi this

end CriticalZ3

namespace ProductCylinder

end ProductCylinder

namespace CriticalZ3
open Classical

theorem measurableSet_bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    MeasurableSet (bondSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (bondSeedReaches_determined c m n T)

theorem measurableSet_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    MeasurableSet (siteSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (siteSeedReaches_determined c m n hmn T)

theorem bondBoundary_eq_union_reachesFaces (c : Vertex) (m n : ℕ) :
    bondSeedReaches c m n (cubeBoundary c n) = ⋃ f : FaceIndex, bondSeedReaches c m n (QuarterFace c n f) := by
  ext ω
  simp only [bondSeedReaches,boundary_eq_union_quarterFace,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x,hx,y,⟨f,hf⟩,hp⟩
    exact ⟨f,x,hx,y,hf,hp⟩
  · rintro ⟨f,x,hx,y,hf,hp⟩
    exact ⟨x,hx,y,⟨f,hf⟩,hp⟩

theorem siteBoundary_eq_union_reachesFaces (c : Vertex) (m n : ℕ) :
    siteSeedReaches c m n (cubeBoundary c n) = ⋃ f : FaceIndex, siteSeedReaches c m n (QuarterFace c n f) := by
  ext ω
  simp only [siteSeedReaches,boundary_eq_union_quarterFace,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x,hx,hw,y,⟨f,hf⟩,hp⟩
    exact ⟨f,x,hx,hw,y,hf,hp⟩
  · rintro ⟨f,x,hx,hw,y,hf,hp⟩
    exact ⟨x,hx,hw,y,⟨f,hf⟩,hp⟩

theorem card_faceIndex : Fintype.card FaceIndex = 24 := by
  norm_num [FaceIndex,Fintype.card_prod,Fintype.card_fun]

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

theorem continuous_parameter : Continuous parameter := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem continuous_bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Continuous (fun p => (bondLaw p).real (bondSeedReaches c m n T)) :=
  (ProductCylinder.continuous_probability _ _ (bondSeedReaches_determined c m n T)).comp
    (continuous_pi (fun _ => continuous_parameter))

theorem continuous_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    Continuous (fun p => (siteLaw p).real (siteSeedReaches c m n T)) :=
  (ProductCylinder.continuous_probability _ _ (siteSeedReaches_determined c m n hmn T)).comp
    (continuous_pi (fun _ => continuous_parameter))

theorem continuous_bondSeedMiss (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Continuous (fun p => (bondLaw p).real (bondSeedReaches c m n T)ᶜ) := by
  simp_rw [measureReal_compl (measurableSet_bondSeedReaches c m n T),probReal_univ]
  exact continuous_const.sub (continuous_bondSeedReaches _ _ _ _)

theorem continuous_siteSeedMiss (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    Continuous (fun p => (siteLaw p).real (siteSeedReaches c m n T)ᶜ) := by
  simp_rw [measureReal_compl (measurableSet_siteSeedReaches c m n hmn T),probReal_univ]
  exact continuous_const.sub (continuous_siteSeedReaches _ _ _ hmn _)

/-- A single strictly lower parameter preserves simultaneous finite strict bounds. -/
theorem exists_lower_forall {I : Type uI} [Finite I] {p γ : ℝ} (hp : 0 < p)
    (g : I → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (hgp : ∀ i, g i p < γ) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ i, g i q < γ := by
  have ho : IsOpen {q | ∀ i, g i q < γ} := by
    have he : {q | ∀ i, g i q < γ} = ⋂ i, (g i) ⁻¹' Set.Iio γ := by ext q; simp
    rw [he]
    exact isOpen_iInter_of_finite (fun i => isOpen_Iio.preimage (hg i))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho p hgp
  let a : ℝ := min (p/4) (ε/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hap : a ≤ p/4 := min_le_left _ _
  have hae : a ≤ ε/2 := min_le_right _ _
  refine ⟨p-a,⟨by linarith,by linarith⟩,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos ha]
  linarith

end CriticalZ3

end OAI

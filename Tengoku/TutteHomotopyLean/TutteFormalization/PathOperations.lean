import Tengoku.TutteHomotopyLean.TutteFormalization.PathRanks
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The concrete path operations used by the source induction, PT-01/PT-02/PT-04/PT-09.
The protected finite-sequence representation is unchanged. Appending one vertex
is enough for the source proof; no injectivity of the sequence is imposed.
-/

namespace TutteFormalization

variable {α : Type*} {M : Matroid α}

namespace TuttePath

/-- PT-01: a one-vertex path has no edge conditions.-/
def constant (H : Set α) (hH : IsHyperplane M H) : TuttePath M where
  length := 0
  vertex := fun _ => H
  isHyperplane := fun _ => hH
  adjacent := fun i => Fin.elim0 i

/--
@isnad1 id=eq.1h3v.s4.a148d6f91a96 from=translated src=- shape=1f8d0d3b vocab=6d9d5eeb
-/
@[simp] theorem constant_origin (H : Set α) (hH : IsHyperplane M H) :
    (constant H hH).origin = H := rfl

/--
@isnad1 id=eq.1h3v.s4.ef356fac0797 from=translated src=- shape=1f8d0d3b vocab=a46048b4
-/
@[simp] theorem constant_terminus (H : Set α) (hH : IsHyperplane M H) :
    (constant H hH).terminus = H := rfl

/--
@isnad1 id=on.2h4v.s5.c696d8cc4f46 from=translated src=- shape=6d3d2dcb vocab=92ced449
-/
theorem constant_on {H F : Set α} (hH : IsHyperplane M H) (hF : F ⊆ H) :
    (constant H hH).On F := fun _ => hF

/--
@isnad1 id=off.2h4v.s5.751cbb3596e4 from=translated src=- shape=bef8096c vocab=9ef5422a
-/
theorem constant_off {H : Set α} {Γ : Set (Set α)} (hH : IsHyperplane M H)
    (hΓ : H ∉ Γ) : (constant H hH).Off Γ := fun _ => hΓ

/-- PT-04: a path on a larger flat is also on any subset of that flat.
@isnad1 id=on.2h5v.s5.422f37e65705 from=translated src=- shape=707bc179 vocab=33d5e0bd
-/
theorem On.mono {p : TuttePath M} {F G : Set α} (h : p.On G) (hFG : F ⊆ G) :
    p.On F := fun i => hFG.trans (h i)

/-- PT-09: append a hyperplane joined to the old terminus by a Tutte edge.-/
def snoc (p : TuttePath M) (H : Set α) (hH : IsHyperplane M H)
    (hEdge : TutteAdjacent M p.terminus H) : TuttePath M where
  length := p.length + 1
  vertex := Fin.snoc (α := fun _ => Set α) p.vertex H
  isHyperplane := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hH
    · simpa using p.isHyperplane j
  adjacent := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [terminus] using hEdge
    · simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc] using p.adjacent j

/--
@isnad1 id=eq.2h4v.s5.bedc92faf9c9 from=translated src=- shape=a9fb221f vocab=dd00ec8b
-/
@[simp] theorem snoc_origin (p : TuttePath M) (H : Set α) (hH : IsHyperplane M H)
    (hEdge : TutteAdjacent M p.terminus H) : (p.snoc H hH hEdge).origin = p.origin := by
  change Fin.snoc (α := fun _ => Set α) p.vertex H (Fin.castSucc 0) = p.vertex 0
  rw [Fin.snoc_castSucc]

/--
@isnad1 id=eq.2h4v.s5.6bd8436b9857 from=translated src=- shape=87feba96 vocab=99087cec
-/
@[simp] theorem snoc_terminus (p : TuttePath M) (H : Set α) (hH : IsHyperplane M H)
    (hEdge : TutteAdjacent M p.terminus H) : (p.snoc H hH hEdge).terminus = H := by
  simp [snoc, terminus]

/--
@isnad1 id=on.4h5v.s5.7f56b7261fd2 from=translated src=- shape=86d31649 vocab=313be9c9
-/
theorem On.snoc {p : TuttePath M} {F H : Set α} (h : p.On F)
    (hH : IsHyperplane M H) (hEdge : TutteAdjacent M p.terminus H) (hFH : F ⊆ H) :
    (p.snoc H hH hEdge).On F := by
  change ∀ i : Fin (p.length + 1 + 1), F ⊆ Fin.snoc (α := fun _ => Set α) p.vertex H i
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [TuttePath.snoc] using hFH
  · simpa [TuttePath.snoc] using h j

/--
@isnad1 id=off.4h5v.s5.45be460750cd from=translated src=- shape=167d57be vocab=89495822
-/
theorem Off.snoc {p : TuttePath M} {Γ : Set (Set α)} {H : Set α} (h : p.Off Γ)
    (hH : IsHyperplane M H) (hEdge : TutteAdjacent M p.terminus H) (hHoff : H ∉ Γ) :
    (p.snoc H hH hEdge).Off Γ := by
  change ∀ i : Fin (p.length + 1 + 1), Fin.snoc (α := fun _ => Set α) p.vertex H i ∉ Γ
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [TuttePath.snoc] using hHoff
  · simpa [TuttePath.snoc] using h j

end TuttePath

/-- PT-01: the constant case with the full endpoint and On/Off conclusions.
@isnad1 id=ex.3h5v.s6.08bc7ae4c737 from=translated src=- shape=04f3246f vocab=e13c6b59
-/
theorem exists_constant_path {F X : Set α} {Γ : Set (Set α)}
    (hX : IsHyperplane M X) (hFX : F ⊆ X) (hXoff : X ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = X ∧ p.On F ∧ p.Off Γ :=
  ⟨TuttePath.constant X hX, rfl, rfl, TuttePath.constant_on hX hFX,
    TuttePath.constant_off hX hXoff⟩

/-- PT-02: a single edge, with all finite-sequence and vertex constraints.
@isnad1 id=ex.7h6v.s6.abe020a6be35 from=translated src=- shape=6ff3911d vocab=8317da66
-/
theorem exists_edge_path {F X Y : Set α} {Γ : Set (Set α)}
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : TutteAdjacent M X Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  let p := TuttePath.constant X hX
  have hEdge : TutteAdjacent M p.terminus Y := hXY
  refine ⟨p.snoc Y hY hEdge, ?_, ?_, ?_, ?_⟩
  · simp [p]
  · simp
  · exact (TuttePath.constant_on hX hFX).snoc hY hEdge hFY
  · exact (TuttePath.constant_off hX hXoff).snoc hY hEdge hYoff

/-- PT-02: complete corank-two base path, including equal endpoints.
@isnad1 id=ex.8h6v.s6.2fd8b3a14593 from=translated src=- shape=dcfa4674 vocab=cdcdf26c
-/
theorem exists_path_of_corankTwo [M.Finite] {F X Y : Set α} {Γ : Set (Set α)}
    (hF : Indecomposable M F) (hc : CorankTwo M F)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  by_cases hXY : X = Y
  · subst Y
    exact exists_constant_path hX hFX hXoff
  exact exists_edge_path hX hY (tutteAdjacent_of_corankTwo hF hc hX hY hXY hFX hFY)
    hFX hFY hXoff hYoff

end TutteFormalization

import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/- An external connected carrier has either two distinct cycle attachments or
   all of its cycle boundary is concentrated at one root. The carrier,
   separation, and boundary hypotheses are kept explicit for later block
   arguments. -/
/--
@isnad1 id=or.4h5v.s7.15e896eb8ab1 from=translated src=- shape=458a1afb vocab=1628c04d
-/
theorem external_carrier_two_attachments_or_unique_root
    {V : Type u} {G : SimpleGraph V} {s : V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {C : G.Walk s s} (hC : C.IsCycle) (K : Set V)
    (hKconn : (G.induce K).Connected)
    (hK_external : ∀ v, v ∈ K → v ∉ C.support)
    (hattach :
      ∃ a, a ∈ C.support ∧ ∃ x, x ∈ K ∧ G.Adj a x) :
    (∃ a b x y, a ∈ C.support ∧ b ∈ C.support ∧ a ≠ b ∧
      x ∈ K ∧ y ∈ K ∧ G.Adj a x ∧ G.Adj b y) ∨
      ∃ r, r ∈ C.support ∧
        ∀ b, b ∈ C.support →
          ((∃ y, y ∈ K ∧ G.Adj b y) ↔ b = r) := by
  by_cases htwo :
      ∃ a b x y, a ∈ C.support ∧ b ∈ C.support ∧ a ≠ b ∧
        x ∈ K ∧ y ∈ K ∧ G.Adj a x ∧ G.Adj b y
  · exact Or.inl htwo
  · right
    obtain ⟨r, hrC, x, hxK, hrx⟩ := hattach
    refine ⟨r, hrC, ?_⟩
    intro b hbC
    constructor
    · rintro ⟨y, hyK, hby⟩
      by_contra hbr
      exact htwo ⟨r, b, x, y, hrC, hbC, Ne.symm hbr, hxK, hyK, hrx, hby⟩
    · intro hbr
      subst b
      exact ⟨x, hxK, hrx⟩

/- In a carrier whose boundary is rooted at `root`, every non-root carrier
   vertex keeps all of its ambient neighbors inside the carrier. -/
/--
@isnad1 id=mem.6h6v.s6.33d3a844fcbd from=translated src=- shape=073a307b vocab=5e529d27
-/
theorem LeafBlock.neighbor_mem_of_mem_of_ne_root
    {V : Type u} {G : SimpleGraph V} (K : Set V)
    (hKconn : (G.induce K).Connected) {root v w : V}
    (hroot : root ∈ K)
    (hboundary :
      ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → x = root)
    (hv : v ∈ K) (hvroot : v ≠ root) (hvw : G.Adj v w) :
    w ∈ K := by
  by_contra hw
  exact hvroot (hboundary v hv w hw hvw)

end Erdos64

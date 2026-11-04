import Tengoku.ErdosLean.ErdosLean.Erdos612.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612: the two concrete periodic families and their `decide` checks

* `cssPre/cssPer/cssSuf`: Czabarka–Singgih–Székely, J. Combin. Theory Ser. B 151 (2021)
  38–45, doi:10.1016/j.jctb.2021.06.001; numbering as in the preprint arXiv:2009.02611v1
  (*On the maximum diameter of k-colorable graphs*), §3, Figure 1, Lemma 5 and Theorem 6,
  with `r = 2`, `s = r - 1 = 1`, `δ = 24` (so `⌊δ/2s⌋ = 12`, remainder `0`):
  the block `C_{1,24}` has layers `1 | 12,11 | 12 | 1 | 12 | 12,11 | 1`; the first and last
  blocks carry the `+1` modification.  The blow-up is `3`-colourable, hence `K₄`-free.
* `ccPre/ccPer/ccSuf`: H. Chen–Y. Chen (arXiv:2609.03346v1, §2, the graph `J_{p,r}` of
  Theorem 2.7) with `r = 4`,
  `δ = 8778 = 6(6r-5)(2r-1)(3r-1)`: `τ = 7`, `x = δ/τ = 1254`, `λ = ⌈δ/11⌉ = 798`,
  `a₁ = a₃ = 1254`, `η = 7973`, `z = 1703`, `g = 5`, `b_i = δ - 1254 i`, `c_i = 1254 (i+1)`.
  Weights inside a layer are the balanced split (`⌈·⌉` first).  The blow-up is
  `8`-colourable, hence `K₉`-free.
All checks are kernel `decide` (no compiled evaluation).
-/

namespace Erdos612

/-- CSS21 first (modified) block, `δ = 24`.-/
def cssPre : Layers := [[1], [12, 12], [12], [1], [12], [12, 11], [1]]
/-- CSS21 repeated block `C_{1,24}`.-/
def cssPer : Layers := [[1], [12, 11], [12], [1], [12], [12, 11], [1]]
/-- CSS21 last (modified) block.-/
def cssSuf : Layers := [[1], [12, 11], [12], [1], [12], [12, 12], [1]]

/-- CC26 prefix `L₁, L₂` (`r = 4`, `δ = 8778`).-/
def ccPre : Layers := [List.replicate 7 8778, [8778]]
/-- CC26 period `L₃, …, L₂₁` (`19 = 6r - 5` layers).-/
def ccPer : Layers :=
  [[1], List.replicate 6 1254, [1254, 1254], [1], List.replicate 5 1254,
    [1254, 1254, 1254], [1], [1254, 1254, 1254, 1254], [1254, 1254, 1254, 1254], [1],
    [1254, 1254, 1254], List.replicate 5 1254, [1], [1254, 1254], List.replicate 6 1254,
    [1], [418, 418, 418], [1595, 1595, 1595, 1594, 1594], [418, 418, 418]]
/-- CC26 suffix: right-hand junction, `L_{19p+4}`, `L_{19p+5}`.-/
def ccSuf : Layers := [[1], [8778], List.replicate 7 8778]

/--
@isnad1 id=eq.0h0v.s3.17cdd6944ce4 from=translated src=- shape=4cc4e2d2 vocab=1d13c016
-/
theorem cssPer_len : cssPer.length = 7 := rfl
/--
@isnad1 id=eq.0h0v.s4.8dcf7c1e5393 from=translated src=- shape=a5f17017 vocab=d4af1d23
-/
theorem cssPer_sum : (cssPer.map List.sum).sum = 73 := by decide
/--
@isnad1 id=eq.0h0v.s4.7ef9dcc18740 from=translated src=- shape=a5f17017 vocab=d615b075
-/
theorem cssPre_sum : (cssPre.map List.sum).sum = 74 := by decide
/--
@isnad1 id=eq.0h0v.s4.45432e9f301f from=translated src=- shape=a5f17017 vocab=f0fa065d
-/
theorem cssSuf_sum : (cssSuf.map List.sum).sum = 74 := by decide
/--
@isnad1 id=eq.0h0v.s3.9e81aa57aa1a from=translated src=- shape=4cc4e2d2 vocab=da7077a2
-/
theorem ccPer_len : ccPer.length = 19 := rfl
/--
@isnad1 id=eq.0h0v.s4.c969ca37c1ee from=translated src=- shape=a5f17017 vocab=f447c34e
-/
theorem ccPer_sum : (ccPer.map List.sum).sum = 60647 := by decide
/--
@isnad1 id=eq.0h0v.s4.675679e787ae from=translated src=- shape=a5f17017 vocab=ec99ff4f
-/
theorem ccPre_sum : (ccPre.map List.sum).sum = 70224 := by decide
/--
@isnad1 id=eq.0h0v.s4.41dff9f035a6 from=translated src=- shape=a5f17017 vocab=923821eb
-/
theorem ccSuf_sum : (ccSuf.map List.sum).sum = 70225 := by decide

/--
@isnad1 id=allwin.0h0v.s3.dd0b446a42b3 from=translated src=- shape=63e294f8 vocab=7709b26e
-/
theorem css_pos : AllWin PosQ (fam cssPre cssPer cssSuf 2) := by decide
/--
@isnad1 id=allwin.0h0v.s4.49250b08a156 from=translated src=- shape=1dcef046 vocab=a618d3e1
-/
theorem css_deg : AllWin (DegQ 24) (fam cssPre cssPer cssSuf 2) := by decide
/--
@isnad1 id=somewin.0h0v.s4.a465ecd8f913 from=translated src=- shape=1dcef046 vocab=76424464
-/
theorem css_tight : SomeWin (TightQ 24) (fam cssPre cssPer cssSuf 2) := by decide
/--
@isnad1 id=allwin.0h0v.s4.21964f8686a4 from=translated src=- shape=1dcef046 vocab=4cc6ebdf
-/
theorem css_cliq : AllWin (CliqQ 4) (fam cssPre cssPer cssSuf 2) := by decide

/--
@isnad1 id=allwin.0h0v.s3.ab6d2890a940 from=translated src=- shape=63e294f8 vocab=1aa8ead9
-/
theorem cc_pos : AllWin PosQ (fam ccPre ccPer ccSuf 2) := by decide
/--
@isnad1 id=allwin.0h0v.s4.a07518b63f1d from=translated src=- shape=1dcef046 vocab=18ad56f5
-/
theorem cc_deg : AllWin (DegQ 8778) (fam ccPre ccPer ccSuf 2) := by decide
/--
@isnad1 id=somewin.0h0v.s4.fac7b81f37b5 from=translated src=- shape=1dcef046 vocab=703864f7
-/
theorem cc_tight : SomeWin (TightQ 8778) (fam ccPre ccPer ccSuf 2) := by decide
/--
@isnad1 id=allwin.0h0v.s4.d68288f6deb6 from=translated src=- shape=1dcef046 vocab=fbb20390
-/
theorem cc_cliq : AllWin (CliqQ 9) (fam ccPre ccPer ccSuf 2) := by decide

end Erdos612

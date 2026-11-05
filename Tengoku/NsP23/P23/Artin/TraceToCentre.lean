import Tengoku.NsP23.P23.Artin.Trace
import Tengoku.NsP23.P23.OneTie.Phase1GeometryClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace sources give directional centres in the direct finite model

This module converts the Run-08 selected-root coefficient witness into the
frozen Phase-1 directional-centre predicate.  It remains internal to the
finite standard-monomial model and asserts no polynomial-quotient bridge.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

/-- Generic predecessor exactness, shared by ordinary and wrapped branches.
@isnad1 id=eq.1h6v.s6.ad8c15f1102a from=translated src=- shape=3be64595 vocab=791b6c7e
-/
theorem predecessor_mul_generator {r q : Normal a b c} (e : Direction)
    (hpred : Normal.predecessor e r = some q) :
    q * e.generator = r :=
  (Normal.predecessor_eq_some_iff_mul e r q).1 hpred

/-- Every existing directional predecessor divides its root.
@isnad1 id=dvd.1h6v.s5.feb0324e071d from=translated src=- shape=a55545aa vocab=0fed60ba
-/
theorem predecessor_dvd_root {r q : Normal a b c} (e : Direction)
    (hpred : Normal.predecessor e r = some q) : q ∣ r :=
  ⟨e.generator, (predecessor_mul_generator e hpred).symm⟩

/-- A predecessor of a selected root survives in the standard set.
@isnad1 id=mem.2h7v.s6.74f13d113781 from=translated src=- shape=af659209 vocab=4eb9ae56
-/
theorem predecessor_mem_standardSet (S : Finset (Normal a b c))
    {r q : Normal a b c} (hr : r ∈ S) (e : Direction)
    (hpred : Normal.predecessor e r = some q) : q ∈ standardSet S :=
  (mem_standardSet_iff S q).2 ⟨r, hr, predecessor_dvd_root e hpred⟩

/-- A predecessor of a selected root has a standard-finset index.
@isnad1 id=mem.2h7v.s6.07c48b235df0 from=translated src=- shape=50f4359c vocab=c0445199
-/
theorem predecessor_mem_standardFinset (S : Finset (Normal a b c))
    {r q : Normal a b c} (hr : r ∈ S) (e : Direction)
    (hpred : Normal.predecessor e r = some q) : q ∈ standardFinset S :=
  (mem_standardFinset_iff_standardSet S q).2
    (predecessor_mem_standardSet S hr e hpred)

/-- A selected root has its canonical surviving index.
@isnad1 id=mem.1h5v.s6.b6ea0d3bf910 from=translated src=- shape=934ad3c4 vocab=19d871b5
-/
theorem root_mem_standardFinset (S : Finset (Normal a b c))
    {r : Normal a b c} (hr : r ∈ S) : r ∈ standardFinset S :=
  (rootIndex S r hr).2

/-- A nonzero variable coefficient in a selected-root image makes that source
root a directional centre.  The proof treats ordinary and wrapped
predecessors through the same generic predecessor theorem.
@isnad1 id=isdirect.3h8v.s10.6d82a9e83578 from=translated src=- shape=4cd94298 vocab=6ca32997
-/
theorem rootSource_isDirectionalCentre
    (S : Finset (Normal a b c)) (e : Direction)
    (heS : e.generator ∈ standardFinset S)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b c) (hs : s ∈ S)
    (hcoeff : coeffAt (k := k) S ⟨e.generator, heS⟩
      (F (U (k := k) S (rootIndex S s hs))) ≠ 0) :
    IsDirectionalCentre S e s := by
  refine ⟨hs, ?_⟩
  intro r hr q hpred
  let qi : MonomialIndex S :=
    ⟨q, predecessor_mem_standardFinset S hr e hpred⟩
  let ei : MonomialIndex S := ⟨e.generator, heS⟩
  let ri : MonomialIndex S := rootIndex S r hr
  have hmul : qi.1 * ei.1 = ri.1 := by
    simpa [qi, ei, ri, rootIndex] using predecessor_mul_generator e hpred
  by_contra hnotmem
  have hnotdiv : ¬q ∣ s := by
    intro hdiv
    apply hnotmem
    exact (Normal.mem_divisorDownset_iff q s).2
      ((Normal.exact_divides_iff q s).1 hdiv)
  have hann :
      X (k := k) S qi.1 qi.2 • U (k := k) S (rootIndex S s hs) = 0 :=
    (X_smul_rootDual_eq_zero_iff (k := k) S s hs qi).2 (by
      simpa [qi] using hnotdiv)
  have hzero : X (k := k) S qi.1 qi.2 *
      F (U (k := k) S (rootIndex S s hs)) = 0 := by
    calc
      X (k := k) S qi.1 qi.2 * F (U (k := k) S (rootIndex S s hs)) =
          X (k := k) S qi.1 qi.2 • F (U (k := k) S (rootIndex S s hs)) := by
            simp [smul_eq_mul]
      _ = F (X (k := k) S qi.1 qi.2 •
          U (k := k) S (rootIndex S s hs)) := by
            symm
            exact F.map_smul _ _
      _ = 0 := by rw [hann]; simp
  have hc := congrArg (coeffAt (k := k) S ri) hzero
  rw [coeffAt_X_mul (k := k) S qi ei ri hmul] at hc
  have : coeffAt (k := k) S ei
      (F (U (k := k) S (rootIndex S s hs))) = 0 := by
    simpa using hc
  exact hcoeff (by simpa [ei] using this)

/-- Trace membership of a surviving variable produces a directional centre.
@isnad1 id=ex.6h6v.s8.6e7826d5cfb9 from=translated src=- shape=13a971f2 vocab=cf7c4e43
-/
theorem exists_directionalCentre_of_variable_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (e : Direction)
    (heS : e.generator ∈ standardFinset S)
    (htrace : X (k := k) S e.generator heS ∈ TraceSubmodule k S) :
    ∃ s ∈ S, IsDirectionalCentre S e s := by
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS hcard
      hanti hdom e heS htrace
  exact ⟨s, hs, rootSource_isDirectionalCentre (k := k) S e heS F s hs hcoeff⟩

/--
@isnad1 id=ex.6h5v.s8.c7a07d63f52d from=translated src=- shape=3a660bbc vocab=f95e87f5
-/
theorem exists_x_directionalCentre_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : X (k := k) S Normal.xGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.1) ∈ TraceSubmodule k S) :
    ∃ s ∈ S, IsDirectionalCentre S .x s :=
  exists_directionalCentre_of_variable_mem_trace (k := k) S hS hcard
    hanti hdom .x _ htrace

/--
@isnad1 id=ex.6h5v.s8.0155b8c587ba from=translated src=- shape=3a660bbc vocab=c0273c64
-/
theorem exists_y_directionalCentre_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : X (k := k) S Normal.yGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.2.1) ∈ TraceSubmodule k S) :
    ∃ s ∈ S, IsDirectionalCentre S .y s :=
  exists_directionalCentre_of_variable_mem_trace (k := k) S hS hcard
    hanti hdom .y _ htrace

/--
@isnad1 id=ex.6h5v.s8.1f055f8ed964 from=translated src=- shape=3a660bbc vocab=43796bd8
-/
theorem exists_z_directionalCentre_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : X (k := k) S Normal.zGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1) ∈ TraceSubmodule k S) :
    ∃ s ∈ S, IsDirectionalCentre S .z s :=
  exists_directionalCentre_of_variable_mem_trace (k := k) S hS hcard
    hanti hdom .z _ htrace

/-- The direct-model H3/DC bridge.  The three returned centres may be
different selected roots.
@isnad1 id=hasdirec.6h5v.s6.84b9558ff886 from=translated src=- shape=61dfa3ff vocab=32e39478
-/
theorem hasDirectionalCentres_of_variablesInTrace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : VariablesInTrace k S hlive) : HasDirectionalCentres S := by
  intro e
  cases e with
  | x =>
      obtain ⟨s, _hs, hcentre⟩ :=
        exists_x_directionalCentre_of_mem_trace (k := k) S hS hcard
          hanti hdom hlive htrace.1
      exact ⟨s, hcentre⟩
  | y =>
      obtain ⟨s, _hs, hcentre⟩ :=
        exists_y_directionalCentre_of_mem_trace (k := k) S hS hcard
          hanti hdom hlive htrace.2.1
      exact ⟨s, hcentre⟩
  | z =>
      obtain ⟨s, _hs, hcentre⟩ :=
        exists_z_directionalCentre_of_mem_trace (k := k) S hS hcard
          hanti hdom hlive htrace.2.2
      exact ⟨s, hcentre⟩

/-- Mixed type-three four-border trace geometry, through the stable Phase-1
API only.
@isnad1 id=ex.8h5v.s7.3a2f1d5f7740 from=translated src=- shape=2c079ffd vocab=5e3998c9
-/
theorem mixed_four_border_trace_has_dominant
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (htrace : VariablesInTrace k S hlive)
    (hborder : (borderFinset S).card = 4) :
    ∃ C ∈ S, IsDominantRoot S C := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : 2 ≤ S.card := by omega
  have hdom : IsLiveParameterDomain a b c := ⟨ha, Or.inl ⟨hb, hc⟩⟩
  have hcentres := hasDirectionalCentres_of_variablesInTrace (k := k) S hS
    hcard hanti hdom hlive htrace
  exact phaseOne_four_border_geometry.mixed a b c S ha hb hc hcardS hlive
    hanti hcentres hborder

/-- Pure type-three four-border trace geometry, through the stable Phase-1
API only.
@isnad1 id=or.7h4v.s7.0c6417ddaf41 from=translated src=- shape=b9c5b39c vocab=4aeed46f
-/
theorem pure_four_border_trace_dominant_or_residual
    (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (htrace : VariablesInTrace k S hlive)
    (hborder : (borderFinset S).card = 4) :
    (∃ C ∈ S, IsDominantRoot S C) ∨ IsPureResidualFourBorderShape S := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : 2 ≤ S.card := by omega
  have hdom : IsLiveParameterDomain a b 0 := ⟨ha, Or.inr ⟨hb, rfl⟩⟩
  have hcentres := hasDirectionalCentres_of_variablesInTrace (k := k) S hS
    hcard hanti hdom hlive htrace
  exact phaseOne_four_border_geometry.pure a b S ha hb hcardS hlive hanti
    hcentres hborder

/-- Stable import boundary for the two trace/four-border geometry conclusions.-/
structure TraceFourBorderGeometry (k : Type*) [Field k] : Prop where
  mixed : ∀ (a b c : ℕ) [NeZero a] (S : Finset (Normal a b c)),
    2 ≤ a → 1 ≤ b → 1 ≤ c → S.card = 3 →
    ∀ hlive : IsLiveTie S, IsRootAntichain S → VariablesInTrace k S hlive →
    (borderFinset S).card = 4 → ∃ C ∈ S, IsDominantRoot S C
  pure : ∀ (a b : ℕ) [NeZero a] (S : Finset (Normal a b 0)),
    2 ≤ a → 2 ≤ b → S.card = 3 →
    ∀ hlive : IsLiveTie S, IsRootAntichain S → VariablesInTrace k S hlive →
    (borderFinset S).card = 4 →
      (∃ C ∈ S, IsDominantRoot S C) ∨ IsPureResidualFourBorderShape S

/--
@isnad1 id=tracefou.0h1v.s3.97fe43ba92be from=translated src=- shape=c6850a32 vocab=641c8e1e
-/
theorem trace_four_border_geometry : TraceFourBorderGeometry k where
  mixed := by
    intro a b c _ S ha hb hc hcard hlive hanti htrace hborder
    exact mixed_four_border_trace_has_dominant (k := k) S ha hb hc hcard
      hlive hanti htrace hborder
  pure := by
    intro a b _ S ha hb hcard hlive hanti htrace hborder
    exact pure_four_border_trace_dominant_or_residual (k := k) S ha hb hcard
      hlive hanti htrace hborder

end

end P23.Artin

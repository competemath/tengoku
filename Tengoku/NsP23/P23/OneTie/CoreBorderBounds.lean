import Tengoku.NsP23.P23.OneTie.GeometryClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Thin border consequences of the frozen exact H5 core root families. -/
namespace P23.OneTie
noncomputable section
open Classical
variable {a b c : ℕ} [NeZero a]

private theorem card_four_le {α : Type*} [DecidableEq α] (p q r s : α) :
    ({p,q,r,s} : Finset α).card ≤ 4 := by
  simp only [Finset.card_insert_eq_ite,Finset.card_singleton]
  split_ifs <;> omega

private theorem card_three_le {α : Type*} [DecidableEq α] (p q r : α) :
    ({p,q,r} : Finset α).card ≤ 3 := by
  simp only [Finset.card_insert_eq_ite,Finset.card_singleton]
  split_ifs <;> omega

-- One uniform generic predecessor API, including wrapped x; no H5 case split.
private theorem border_scalar {S : Finset (Normal a b c)}
    (hS : S.Nonempty) (Std : ℕ → ℕ → ℕ → Prop)
    (hstd : ∀ p, p ∈ standardSet S ↔ Std p.x p.y p.z)
    (m : Normal a b c) (hm : m ∈ borderFinset S) :
    ¬Std m.x m.y m.z ∧
    (if 0<m.x then Std (m.x-1) m.y m.z
     else if b≤m.y ∧ c≤m.z then Std (a-1) (m.y-b) (m.z-c) else True) ∧
    (0<m.y → Std m.x (m.y-1) m.z) ∧
    (0<m.z → Std m.x m.y (m.z-1)) := by
  rw [mem_borderFinset_iff hS] at hm
  rcases m with ⟨x,y,z,hxlt⟩
  by_cases hx : 0<x
  · simpa [IsMinimalBorder,ApplicablePredecessorsSurvive,hstd,Normal.predecessor,
      Normal.xPredecessor,Normal.yPredecessor,Normal.zPredecessor,hx] using hm
  · have hx0 : x=0 := by omega
    by_cases hy : b≤y <;> by_cases hz : c≤z <;>
      simpa [IsMinimalBorder,ApplicablePredecessorsSurvive,hstd,Normal.predecessor,
        Normal.wrappedXPredecessor,Normal.yPredecessor,Normal.zPredecessor,hx,hx0,hy,hz] using hm

private def pairStd (p q : Normal a b c) (x y z : ℕ) : Prop :=
  (y≤p.y ∧ z≤p.z ∧ (x≤p.x ∨ (y+b≤p.y ∧ z+c≤p.z))) ∨
  (y≤q.y ∧ z≤q.z ∧ (x≤q.x ∨ (y+b≤q.y ∧ z+c≤q.z)))

private theorem pair_standard (p q m : Normal a b c) :
    m ∈ standardSet {p,q} ↔ pairStd p q m.x m.y m.z := by
  simp [standardSet,Normal.exact_divides_iff,Normal.DividesCriterion,pairStd]

private def m2CoreStd (r u v x y z : ℕ) : Prop :=
  y≤u ∧ z≤v ∧ (x≤r ∨ y<u) ∧ (x≤r+1 ∨ z<v)

private theorem m2_core_standard (ha : 2≤a) (hu : 1≤u) (hv : 1≤v)
    (hr : r≤a-2) (p : Normal a 1 1) :
    p ∈ standardSet (m2Socles ha r u v hr) ↔ m2CoreStd r u v p.x p.y p.z := by
  simp [m2Socles,standardSet,Normal.exact_divides_iff,Normal.DividesCriterion,
    m2Core,m2Partner,m2CoreStd]
  omega

private theorem m2_scalar (r u v x y z : ℕ)
    (hn : ¬(y≤u ∧ z≤v ∧ (x≤r ∨ y<u) ∧ (x≤r+1 ∨ z<v)))
    (hx : 0<x → y≤u ∧ z≤v ∧ (x≤r+1 ∨ y<u) ∧ (x≤r+2 ∨ z<v))
    (hy : 0<y → y≤u+1 ∧ z≤v ∧ (x≤r ∨ y-1<u) ∧ (x≤r+1 ∨ z<v))
    (hz : 0<z → y≤u ∧ z≤v+1 ∧ (x≤r ∨ y<u) ∧ (x≤r+1 ∨ z-1<v)) :
    (x=0 ∧ y=u+1 ∧ z=0) ∨ (x=0 ∧ y=0 ∧ z=v+1) ∨
    (x=r+1 ∧ y=u ∧ z=0) ∨ (x=r+2 ∧ y=0 ∧ z=v) := by
  by_cases hx0 : x=0
  · subst x
    have hout : u<y ∨ v<z := by omega
    rcases hout with h | h
    · have hyp := hy (by omega)
      have hz0 : z=0 := by
        by_contra hh
        have hzp := hz (by omega)
        omega
      exact Or.inl ⟨rfl,by omega,hz0⟩
    · have hzp := hz (by omega)
      have hy0 : y=0 := by
        by_contra hh
        have hyp := hy (by omega)
        omega
      exact Or.inr (Or.inl ⟨rfl,hy0,by omega⟩)
  · have hxp := hx (by omega)
    have hout : (r<x ∧ u≤y) ∨ (r+1<x ∧ v≤z) := by
      clear hx hy hz
      omega
    rcases hout with h | h
    · have hz0 : z=0 := by
        by_contra hh
        have hzp := hz (by omega)
        omega
      exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega,hz0⟩))
    · have hy0 : y=0 := by
        by_contra hh
        have hyp := hy (by omega)
        omega
      exact Or.inr (Or.inr (Or.inr ⟨by omega,hy0,by omega⟩))

/--
@isnad1 id=le.4h4v.s6.c8e5622dd694 from=translated src=- shape=3fe8715a vocab=818180d5
-/
theorem m2_core_border_card_le_four (ha : 2≤a) (hu : 1≤u) (hv : 1≤v)
    (hr : r≤a-2) : (borderFinset (m2Socles (a:=a) ha r u v hr)).card ≤ 4 := by
  by_cases hlast : r=a-2
  · let G : Finset (Normal a 1 1) := {⟨0,u+1,0,by omega⟩,
      ⟨0,0,v+1,by omega⟩,⟨r+1,u,0,by omega⟩}
    have hs : borderFinset (m2Socles (a:=a) ha r u v hr) ⊆ G := by
      intro m hm
      have hh := border_scalar (by simp [m2Socles]) (m2CoreStd r u v)
        (m2_core_standard ha hu hv hr) m hm
      clear hm
      rcases m with ⟨x,y,z,hxlt⟩
      simp [m2CoreStd] at hh
      simp [G,Normal.mk.injEq]
      have hp := m2_scalar r u v x y z (by simpa using hh.1)
        (by intro hx; simpa [hx] using hh.2.1) hh.2.2.1 hh.2.2.2
      clear hh
      rcases hp with hp | hp | hp | hp <;> omega
    have hc := Finset.card_le_card hs
    have hg : G.card≤3 := card_three_le _ _ _
    omega
  · let G : Finset (Normal a 1 1) := {⟨0,u+1,0,by omega⟩,
      ⟨0,0,v+1,by omega⟩,⟨r+1,u,0,by omega⟩,⟨r+2,0,v,by omega⟩}
    have hs : borderFinset (m2Socles (a:=a) ha r u v hr) ⊆ G := by
      intro m hm
      have hh := border_scalar (by simp [m2Socles]) (m2CoreStd r u v)
        (m2_core_standard ha hu hv hr) m hm
      clear hm
      rcases m with ⟨x,y,z,hxlt⟩
      simp [m2CoreStd] at hh
      simp [G,Normal.mk.injEq]
      have hp := m2_scalar r u v x y z (by simpa using hh.1)
        (by intro hx; simpa [hx] using hh.2.1) hh.2.2.1 hh.2.2.2
      clear hh
      exact hp
    exact le_trans (Finset.card_le_card hs) (card_four_le _ _ _ _)

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.4h4v.s6.e43f319a23b1 from=translated src=- shape=ca085078 vocab=9785cf33
-/
theorem m3_core_border_card_le_four (ha : 2≤a) (hb : 1≤b) (hc : 1≤c)
    (hv : c≤v) : (borderFinset (m3Socles (a:=a) (b:=b) (c:=c) v)).card ≤ 4 := by
  let G : Finset (Normal a b c) := {⟨0,b+1,0,by omega⟩,
    ⟨0,0,v+2,by omega⟩,⟨1,1,0,by omega⟩,⟨1,0,v+1-c,by omega⟩}
  have hs : borderFinset (m3Socles (a:=a) (b:=b) (c:=c) v) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [m3Socles])
      (pairStd (m3KCore v) (m3KPartner v))
      (by intro p; exact pair_standard _ _ _) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [pairStd,m3KCore,m3KPartner] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  exact le_trans (Finset.card_le_card hs) (card_four_le _ _ _ _)

private def m4CoreStd (u v x y z : ℕ) : Prop :=
  y≤u ∧ z≤v+1 ∧ (x=0 ∨ z≤v)

private theorem m4_core_standard (ha : 2≤a) (u v : ℕ) (p : Normal a 1 1) :
    p ∈ standardSet (m4Socles ha u v) ↔ m4CoreStd u v p.x p.y p.z := by
  have hx := p.x_lt
  simp [m4Socles,standardSet,Normal.exact_divides_iff,Normal.DividesCriterion,
    m4YCore,m4YPartner,m4CoreStd]
  omega

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.2h3v.s6.9fe04b1dae61 from=translated src=- shape=fd741e2e vocab=64790186
-/
theorem m4_core_border_card_le_four (ha : 2≤a) (hu : 1≤u) :
    (borderFinset (m4Socles (a:=a) ha u v)).card ≤ 4 := by
  let G : Finset (Normal a 1 1) := {⟨0,u+1,0,by omega⟩,
    ⟨0,0,v+2,by omega⟩,⟨1,0,v+1,by omega⟩}
  have hs : borderFinset (m4Socles (a:=a) ha u v) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [m4Socles])
      (m4CoreStd u v) (m4_core_standard ha u v) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [m4CoreStd] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  have hh := le_trans (Finset.card_le_card hs) (card_three_le _ _ _)
  omega

private def m5CoreStd (b c v x y z : ℕ) : Prop :=
  (y=0 ∧ z≤v) ∨ (x=0 ∧ y≤b ∧ z<v+c)

private theorem m5_core_standard (ha : 2≤a) (hb : 1≤b) (hc : 1≤c)
    (v : ℕ) (p : Normal a b c) :
    p ∈ standardSet (m5Socles ha v) ↔ m5CoreStd b c v p.x p.y p.z := by
  have hx := p.x_lt
  simp [m5Socles,standardSet,Normal.exact_divides_iff,Normal.DividesCriterion,
    m5Core,m5Partner,m5CoreStd]
  omega

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.4h4v.s6.7be9738133fa from=translated src=- shape=bf2b6dfa vocab=ce345b0d
-/
theorem m5_core_border_card_le_four (ha : 2≤a) (hb : 1≤b) (hc : 1≤c)
    (hv : 1≤v) : (borderFinset (m5Socles (a:=a) (b:=b) (c:=c) ha v)).card ≤ 4 := by
  let G : Finset (Normal a b c) := {⟨0,b+1,0,by omega⟩,
    ⟨0,0,v+c,by omega⟩,⟨1,1,0,by omega⟩,⟨1,0,v+1,by omega⟩}
  have hs : borderFinset (m5Socles (a:=a) (b:=b) (c:=c) ha v) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [m5Socles])
      (m5CoreStd b c v) (m5_core_standard ha hb hc v) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [m5CoreStd] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  exact le_trans (Finset.card_le_card hs) (card_four_le _ _ _ _)

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.2h3v.s6.12b1738035eb from=translated src=- shape=73f15168 vocab=9f254a9d
-/
theorem p3_core_border_card_le_four (ha : 2≤a) (hb : 2≤b) :
    (borderFinset (p3Socles (a:=a) (b:=b) v)).card ≤ 4 := by
  let G : Finset (Normal a b 0) := {⟨1,1,0,by omega⟩,
    ⟨0,0,v+2,by omega⟩,⟨1,0,v+1,by omega⟩}
  have hs : borderFinset (p3Socles (a:=a) (b:=b) v) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [p3Socles])
      (pairStd (⟨0,b,v,by omega⟩ : Normal a b 0) ⟨0,b-1,v+1,by omega⟩)
      (by intro p; exact pair_standard _ _ _) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [pairStd] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  have hh := le_trans (Finset.card_le_card hs) (card_three_le _ _ _)
  omega

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.3h3v.s6.ceeb159d7984 from=translated src=- shape=f22c54aa vocab=215af806
-/
theorem p4_core_border_card_le_four (ha : 2≤a) (hb : 2≤b) (hV : 1≤V) :
    (borderFinset (p4Socles (a:=a) (b:=b) V)).card ≤ 4 := by
  let G : Finset (Normal a b 0) := {⟨1,1,0,by omega⟩,
    ⟨1,0,1,by omega⟩,⟨0,0,V+1,by omega⟩}
  have hs : borderFinset (p4Socles (a:=a) (b:=b) V) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [p4Socles])
      (pairStd (⟨0,b,0,by omega⟩ : Normal a b 0) ⟨0,b-1,V,by omega⟩)
      (by intro p; exact pair_standard _ _ _) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [pairStd] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  have hh := le_trans (Finset.card_le_card hs) (card_three_le _ _ _)
  omega

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.3h3v.s6.0accf7ea824c from=translated src=- shape=7a5a3dcb vocab=cf6983f5
-/
theorem p5_core_border_card_le_four (ha : 2≤a) (hb : 2≤b) (hv : 1≤v) :
    (borderFinset (p5Socles (a:=a) (b:=b) ha v)).card ≤ 4 := by
  let G : Finset (Normal a b 0) := {⟨1,1,0,by omega⟩,
    ⟨0,1,1,by omega⟩,⟨0,0,v+1,by omega⟩}
  have hs : borderFinset (p5Socles (a:=a) (b:=b) ha v) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [p5Socles])
      (pairStd (⟨a-1,0,v,by omega⟩ : Normal a b 0) ⟨0,b,0,by omega⟩)
      (by intro p; exact pair_standard _ _ _) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [pairStd] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  have hh := le_trans (Finset.card_le_card hs) (card_three_le _ _ _)
  omega

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.3h3v.s6.abae4e00b9ec from=translated src=- shape=7a5a3dcb vocab=4de9cb75
-/
theorem p6_core_border_card_le_four (ha : 2≤a) (hb : 2≤b) (hv : 1≤v) :
    (borderFinset (p6Socles (a:=a) (b:=b) ha v)).card ≤ 4 := by
  let G : Finset (Normal a b 0) := {⟨1,1,0,by omega⟩,
    ⟨0,1,v,by omega⟩,⟨0,0,v+1,by omega⟩}
  have hs : borderFinset (p6Socles (a:=a) (b:=b) ha v) ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp [p6Socles])
      (pairStd (⟨a-1,0,v,by omega⟩ : Normal a b 0) ⟨0,b,v-1,by omega⟩)
      (by intro p; exact pair_standard _ _ _) m hm
    clear hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [pairStd] at hh
    simp [G,Normal.mk.injEq]
    rcases hh with ⟨hn,hxp,hyp,hzp⟩
    by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
    all_goals
      try have hy' := hyp hy
      try have hz' := hzp hz
      clear hyp hzp
      split_ifs at hxp
      all_goals
        try { have hx' := hxp (by omega) (by omega); clear hxp }
        try { have hx' := hxp (by omega); clear hxp }
        omega
  have hh := le_trans (Finset.card_le_card hs) (card_three_le _ _ _)
  omega

set_option maxHeartbeats 400000 in
/--
@isnad1 id=le.5h5v.s7.947f6e9fa5e4 from=translated src=- shape=8fc3d9da vocab=9dcf3b19
-/
theorem pure_fibre_pair_border_card_le_four (ha : 2≤a) (hb : 2≤b)
    (r u k : ℕ) (hr : r<a) (hu : b≤u) (hk : 1≤k) :
    (borderFinset ({⟨r,u,0,hr⟩,⟨0,0,k,by omega⟩} : Finset (Normal a b 0))).card ≤ 4 := by
  let C : Normal a b 0 := ⟨r,u,0,hr⟩
  let Z : Normal a b 0 := ⟨0,0,k,by omega⟩
  let G : Finset (Normal a b 0) := {pureH r u hr,
    ⟨1,0,1,by omega⟩,⟨0,1,1,by omega⟩,⟨0,0,k+1,by omega⟩}
  have hs : borderFinset {C,Z} ⊆ G := by
    intro m hm
    have hh := border_scalar (by simp) (pairStd C Z)
      (by intro p; exact pair_standard _ _ _) m hm
    rcases m with ⟨x,y,z,hxlt⟩
    simp [pairStd,C,Z] at hh
    by_cases hlast : r<a-1
    · simp [G,pureH,hlast,Normal.mk.injEq]
      rcases hh with ⟨hn,hxp,hyp,hzp⟩
      by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
      all_goals
        try have hy' := hyp hy
        try have hz' := hzp hz
        clear hyp hzp
        split_ifs at hxp
        all_goals
          try { have hx' := hxp (by omega) (by omega); clear hxp }
          try { have hx' := hxp (by omega); clear hxp }
          omega
    · simp [G,pureH,hlast,Normal.mk.injEq]
      rcases hh with ⟨hn,hxp,hyp,hzp⟩
      by_cases hx : 0<x <;> by_cases hy : 0<y <;> by_cases hz : 0<z
      all_goals
        try have hy' := hyp hy
        try have hz' := hzp hz
        clear hyp hzp
        split_ifs at hxp
        all_goals
          try { have hx' := hxp (by omega) (by omega); clear hxp }
          try { have hx' := hxp (by omega); clear hxp }
          omega
  exact le_trans (Finset.card_le_card hs) (card_four_le _ _ _ _)

/--
@isnad1 id=le.5h3v.s6.04507935632d from=translated src=- shape=4e209760 vocab=2a8138b0
-/
theorem pureFibreProduct_two_border_card_le_four
    {S : Finset (Normal a b 0)} (ha : 2≤a) (hb : 2≤b)
    (h2 : S.card=2) (hshape : IsPureFibreProduct S) (hlive : IsLiveTie S) :
    (borderFinset S).card ≤ 4 := by
  rcases hshape with ⟨_,k,hk,hZ,hplane⟩
  let Z : Normal a b 0 := ⟨0,0,k,by omega⟩
  have hZm : Z∈S := hZ
  have hec : (S.erase Z).card=1 := by rw [Finset.card_erase_of_mem hZm,h2]
  obtain ⟨P,hP⟩ := Finset.card_eq_one.mp hec
  have hPm : P∈S := Finset.mem_of_mem_erase (by rw [hP]; simp)
  have hPZ : P≠Z := Finset.ne_of_mem_erase (by rw [hP]; simp)
  have hpz := hplane P hPm hPZ
  have he : S={P,Z} := by
    rw [← Finset.insert_erase hZm,hP]
    ext m; simp; tauto
  have hu : b≤P.y := by
    have ht := hlive.2.2.2
    rw [he] at ht
    simp [standardSet,Normal.exact_divides_iff,Normal.DividesCriterion,liveTiePoint,Z] at ht
    omega
  rw [he]
  rcases P with ⟨r,u,z,hr⟩
  dsimp at hpz
  subst z
  exact pure_fibre_pair_border_card_le_four ha hb r u k hr hu hk

end
end P23.OneTie

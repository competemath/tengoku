/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 7).
@isnad1 id=eq.0h0v.s5.1beaab5e91b8 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_07 :
    branchClaimRootValidB 0 7 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 25).
@isnad1 id=eq.0h0v.s5.7b44aa712ee1 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_25 :
    branchClaimRootValidB 4 25 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 28).
@isnad1 id=eq.0h0v.s5.cef0959f632b from=translated src=- shape=e9e0773c vocab=737c1103
-/
theorem coverageBranchRoot_1_28 :
    branchClaimRootValidB 1 28 (.search branchClaims1Row28) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 29).
@isnad1 id=eq.0h0v.s5.af17197ef472 from=translated src=- shape=e9e0773c vocab=53eaba24
-/
theorem coverageBranchRoot_1_29 :
    branchClaimRootValidB 1 29 (.search branchClaims1Row29) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 28), starting at 0.
@isnad1 id=eq.0h0v.s3.ed031195b701 from=translated src=- shape=6f582f20 vocab=9cfa1bfc
-/
theorem coverageBranchNodes_1_28_00000 :
    nodeClaimChunkValidB branchClaims1Row28 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 28), starting at 64.
@isnad1 id=eq.0h0v.s3.8d5091f73db9 from=translated src=- shape=6f582f20 vocab=9cfa1bfc
-/
theorem coverageBranchNodes_1_28_00064 :
    nodeClaimChunkValidB branchClaims1Row28 64 56 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 29), starting at 0.
@isnad1 id=eq.0h0v.s3.d7e3d2f97b4e from=translated src=- shape=6f582f20 vocab=1c6706f0
-/
theorem coverageBranchNodes_1_29_00000 :
    nodeClaimChunkValidB branchClaims1Row29 0 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 29), starting at 32.
@isnad1 id=eq.0h0v.s3.fb5395e0c599 from=translated src=- shape=6f582f20 vocab=1c6706f0
-/
theorem coverageBranchNodes_1_29_00032 :
    nodeClaimChunkValidB branchClaims1Row29 32 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

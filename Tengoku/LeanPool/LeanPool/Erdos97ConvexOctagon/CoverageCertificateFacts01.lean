/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 1).
@isnad1 id=eq.0h0v.s5.b38ca874f5a8 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_01 :
    branchClaimRootValidB 0 1 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 19).
@isnad1 id=eq.0h0v.s5.446c2e6462da from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_19 :
    branchClaimRootValidB 4 19 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 6).
@isnad1 id=eq.0h0v.s5.fbfe8539ad47 from=translated src=- shape=e9e0773c vocab=ad382fa5
-/
theorem coverageBranchRoot_1_06 :
    branchClaimRootValidB 1 6 (.search branchClaims1Row6) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 7).
@isnad1 id=eq.0h0v.s5.b322b8701f86 from=translated src=- shape=e9e0773c vocab=fcea00d2
-/
theorem coverageBranchRoot_1_07 :
    branchClaimRootValidB 1 7 (.search branchClaims1Row7) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 6), starting at 0.
@isnad1 id=eq.0h0v.s3.b7f1a13b9e84 from=translated src=- shape=6f582f20 vocab=81ef1be9
-/
theorem coverageBranchNodes_1_06_00000 :
    nodeClaimChunkValidB branchClaims1Row6 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 6), starting at 64.
@isnad1 id=eq.0h0v.s3.55ef49a1a932 from=translated src=- shape=6f582f20 vocab=81ef1be9
-/
theorem coverageBranchNodes_1_06_00064 :
    nodeClaimChunkValidB branchClaims1Row6 64 57 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 7), starting at 0.
@isnad1 id=eq.0h0v.s3.6ee404d781ae from=translated src=- shape=6f582f20 vocab=080f1afe
-/
theorem coverageBranchNodes_1_07_00000 :
    nodeClaimChunkValidB branchClaims1Row7 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 7), starting at 64.
@isnad1 id=eq.0h0v.s3.30d8ca5b0ad1 from=translated src=- shape=6f582f20 vocab=080f1afe
-/
theorem coverageBranchNodes_1_07_00064 :
    nodeClaimChunkValidB branchClaims1Row7 64 51 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

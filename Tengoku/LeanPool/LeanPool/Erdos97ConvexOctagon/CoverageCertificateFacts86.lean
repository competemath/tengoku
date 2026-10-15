/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 10).
@isnad1 id=eq.0h0v.s5.dbaede87578f from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_10 :
    branchClaimRootValidB 4 10 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 25).
@isnad1 id=eq.0h0v.s5.7197d813d3b6 from=translated src=- shape=e9e0773c vocab=1b68acd4
-/
theorem coverageBranchRoot_6_25 :
    branchClaimRootValidB 6 25 (.search branchClaims6Row25) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 25), starting at 0.
@isnad1 id=eq.0h0v.s3.34e499f7e7a8 from=translated src=- shape=6f582f20 vocab=1301213a
-/
theorem coverageBranchNodes_6_25_00000 :
    nodeClaimChunkValidB branchClaims6Row25 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 25), starting at 64.
@isnad1 id=eq.0h0v.s3.efa9a6dcbf78 from=translated src=- shape=6f582f20 vocab=1301213a
-/
theorem coverageBranchNodes_6_25_00064 :
    nodeClaimChunkValidB branchClaims6Row25 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 25), starting at 128.
@isnad1 id=eq.0h0v.s3.abc5d422f795 from=translated src=- shape=6f582f20 vocab=1301213a
-/
theorem coverageBranchNodes_6_25_00128 :
    nodeClaimChunkValidB branchClaims6Row25 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 25), starting at 192.
@isnad1 id=eq.0h0v.s3.6cc2ec9f36d7 from=translated src=- shape=6f582f20 vocab=1301213a
-/
theorem coverageBranchNodes_6_25_00192 :
    nodeClaimChunkValidB branchClaims6Row25 192 19 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

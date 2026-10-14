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

/-- Root audit for fixed branch (4, 12).
@isnad1 id=eq.0h0v.s5.119f0ebe254c from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_12 :
    branchClaimRootValidB 4 12 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 27).
@isnad1 id=eq.0h0v.s5.c3585ba15cf9 from=translated src=- shape=e9e0773c vocab=2f749478
-/
theorem coverageBranchRoot_6_27 :
    branchClaimRootValidB 6 27 (.search branchClaims6Row27) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 27), starting at 0.
@isnad1 id=eq.0h0v.s3.dac4947c1655 from=translated src=- shape=6f582f20 vocab=5c766bf7
-/
theorem coverageBranchNodes_6_27_00000 :
    nodeClaimChunkValidB branchClaims6Row27 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 27), starting at 64.
@isnad1 id=eq.0h0v.s3.07e0ac0d0678 from=translated src=- shape=6f582f20 vocab=5c766bf7
-/
theorem coverageBranchNodes_6_27_00064 :
    nodeClaimChunkValidB branchClaims6Row27 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 27), starting at 128.
@isnad1 id=eq.0h0v.s3.bf12d3f07da5 from=translated src=- shape=6f582f20 vocab=5c766bf7
-/
theorem coverageBranchNodes_6_27_00128 :
    nodeClaimChunkValidB branchClaims6Row27 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 27), starting at 192.
@isnad1 id=eq.0h0v.s3.29d120905ed0 from=translated src=- shape=6f582f20 vocab=5c766bf7
-/
theorem coverageBranchNodes_6_27_00192 :
    nodeClaimChunkValidB branchClaims6Row27 192 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

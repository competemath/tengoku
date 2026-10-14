/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 0).
@isnad1 id=eq.0h0v.s5.5cc5e289dac1 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_00 :
    branchClaimRootValidB 3 0 (.patternThree 1) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 24), starting at 64.
@isnad1 id=eq.0h0v.s3.9746a6895a14 from=translated src=- shape=6f582f20 vocab=438d7098
-/
theorem coverageBranchNodes_5_24_00064 :
    nodeClaimChunkValidB branchClaims5Row24 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 24), starting at 128.
@isnad1 id=eq.0h0v.s3.0128175e5651 from=translated src=- shape=6f582f20 vocab=438d7098
-/
theorem coverageBranchNodes_5_24_00128 :
    nodeClaimChunkValidB branchClaims5Row24 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 24), starting at 192.
@isnad1 id=eq.0h0v.s3.1f55dfeaaa4c from=translated src=- shape=6f582f20 vocab=438d7098
-/
theorem coverageBranchNodes_5_24_00192 :
    nodeClaimChunkValidB branchClaims5Row24 192 25 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 24), starting at 217.
@isnad1 id=eq.0h0v.s3.fa62dec4731b from=translated src=- shape=6f582f20 vocab=438d7098
-/
theorem coverageBranchNodes_5_24_00217 :
    nodeClaimChunkValidB branchClaims5Row24 217 25 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

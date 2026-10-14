/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 9).
@isnad1 id=eq.0h0v.s5.0a3ffe7c69c7 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_09 :
    branchClaimRootValidB 3 9 (.patternThree 5) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 27).
@isnad1 id=eq.0h0v.s5.4e375d59907c from=translated src=- shape=e9e0773c vocab=f6541479
-/
theorem coverageBranchRoot_5_27 :
    branchClaimRootValidB 5 27 (.search branchClaims5Row27) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 26), starting at 192.
@isnad1 id=eq.0h0v.s3.18f4a3da7a28 from=translated src=- shape=6f582f20 vocab=bb88c2f5
-/
theorem coverageBranchNodes_5_26_00192 :
    nodeClaimChunkValidB branchClaims5Row26 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 26), starting at 256.
@isnad1 id=eq.0h0v.s3.7911e6bf7ce0 from=translated src=- shape=6f582f20 vocab=bb88c2f5
-/
theorem coverageBranchNodes_5_26_00256 :
    nodeClaimChunkValidB branchClaims5Row26 256 7 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 0.
@isnad1 id=eq.0h0v.s3.a91dc6cbfa73 from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00000 :
    nodeClaimChunkValidB branchClaims5Row27 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 64.
@isnad1 id=eq.0h0v.s3.15a3ea9b6939 from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00064 :
    nodeClaimChunkValidB branchClaims5Row27 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

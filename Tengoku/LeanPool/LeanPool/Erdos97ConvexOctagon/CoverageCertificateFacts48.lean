/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 23).
@isnad1 id=eq.0h0v.s5.11ef7f3dbd78 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_23 :
    branchClaimRootValidB 1 23 (.patternThree 179) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 8).
@isnad1 id=eq.0h0v.s5.8e301858c1e1 from=translated src=- shape=e9e0773c vocab=13eff45e
-/
theorem coverageBranchRoot_5_08 :
    branchClaimRootValidB 5 8 (.search branchClaims5Row8) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 9).
@isnad1 id=eq.0h0v.s5.2924b72aad4f from=translated src=- shape=e9e0773c vocab=34928697
-/
theorem coverageBranchRoot_5_09 :
    branchClaimRootValidB 5 9 (.search branchClaims5Row9) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 7), starting at 64.
@isnad1 id=eq.0h0v.s3.e5fd27d21eb1 from=translated src=- shape=6f582f20 vocab=85116444
-/
theorem coverageBranchNodes_5_07_00064 :
    nodeClaimChunkValidB branchClaims5Row7 64 35 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 8), starting at 0.
@isnad1 id=eq.0h0v.s3.59373594c9a4 from=translated src=- shape=6f582f20 vocab=c63600e7
-/
theorem coverageBranchNodes_5_08_00000 :
    nodeClaimChunkValidB branchClaims5Row8 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 8), starting at 64.
@isnad1 id=eq.0h0v.s3.bb266e35622f from=translated src=- shape=6f582f20 vocab=c63600e7
-/
theorem coverageBranchNodes_5_08_00064 :
    nodeClaimChunkValidB branchClaims5Row8 64 25 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 9), starting at 0.
@isnad1 id=eq.0h0v.s3.71b3ae1915d3 from=translated src=- shape=6f582f20 vocab=683c499f
-/
theorem coverageBranchNodes_5_09_00000 :
    nodeClaimChunkValidB branchClaims5Row9 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

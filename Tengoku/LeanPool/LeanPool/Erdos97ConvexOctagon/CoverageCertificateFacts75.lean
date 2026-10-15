/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 34).
@isnad1 id=eq.0h0v.s5.78b34f53e7c3 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_34 :
    branchClaimRootValidB 3 34 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 5).
@isnad1 id=eq.0h0v.s5.c6656d072d97 from=translated src=- shape=e9e0773c vocab=cca77614
-/
theorem coverageBranchRoot_6_05 :
    branchClaimRootValidB 6 5 (.search branchClaims6Row5) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 6).
@isnad1 id=eq.0h0v.s5.bc2ecb80fa3d from=translated src=- shape=e9e0773c vocab=1efebf91
-/
theorem coverageBranchRoot_6_06 :
    branchClaimRootValidB 6 6 (.search branchClaims6Row6) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 7).
@isnad1 id=eq.0h0v.s5.c152ad4832cf from=translated src=- shape=e9e0773c vocab=006eb9b3
-/
theorem coverageBranchRoot_6_07 :
    branchClaimRootValidB 6 7 (.search branchClaims6Row7) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 5), starting at 0.
@isnad1 id=eq.0h0v.s3.c8a4d9135198 from=translated src=- shape=6f582f20 vocab=cbef37a2
-/
theorem coverageBranchNodes_6_05_00000 :
    nodeClaimChunkValidB branchClaims6Row5 0 40 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 6), starting at 0.
@isnad1 id=eq.0h0v.s3.61c5a52d3484 from=translated src=- shape=6f582f20 vocab=75985bfd
-/
theorem coverageBranchNodes_6_06_00000 :
    nodeClaimChunkValidB branchClaims6Row6 0 35 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 7), starting at 0.
@isnad1 id=eq.0h0v.s3.5592e5f1d761 from=translated src=- shape=6f582f20 vocab=7ef094b5
-/
theorem coverageBranchNodes_6_07_00000 :
    nodeClaimChunkValidB branchClaims6Row7 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 7), starting at 64.
@isnad1 id=eq.0h0v.s3.7da399b5b743 from=translated src=- shape=6f582f20 vocab=7ef094b5
-/
theorem coverageBranchNodes_6_07_00064 :
    nodeClaimChunkValidB branchClaims6Row7 64 39 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage

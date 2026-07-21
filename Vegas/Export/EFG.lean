/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Export.FOSG
import Vegas.Export.KernelGame
import Vegas.Presentation.EFG.FromCore

/-!
# EFG export handles

In-Lean export handles for checked-program extensive-form presentations. The
EFG object itself comes from `Vegas.Presentation.EFG`; the payoff-facing kernel
game is packaged with its source FOSG presentation and a profile-translation
adequacy law. The strategy carrier is behavioral and is therefore not a finite
pure-strategy table; finite analysis remains on the pure frontier export
surface.
-/

namespace Vegas

namespace Export

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Checked-program EFG export handle: serialized EFG plus a certified
payoff-facing kernel game over the same behavioral presentation. The
`payoffGame_udist_sourceFOSG` law is the load-bearing field: the kernel game is
not an arbitrary side object, but a utility-distribution faithful
serialization of the accompanying FOSG presentation. -/
structure EFGExport (P : Type) [DecidableEq P] [Fintype P] where
  efg : EFG.EFGGame
  playerEquiv : P ≃ efg.inf.Player
  sourceFOSG : FOSGExport P
  efgTranslateProfile :
    sourceFOSG.historyGame.Profile →
      (KernelGame.reindex playerEquiv efg.toKernelGame).Profile
  efgOutcomeMap :
    (KernelGame.reindex playerEquiv efg.toKernelGame).Outcome →
      sourceFOSG.historyGame.Outcome
  efgOutcomeKernel_sourceFOSG :
    ∀ profile,
      PMF.map efgOutcomeMap
        ((KernelGame.reindex playerEquiv efg.toKernelGame).outcomeKernel
          (efgTranslateProfile profile)) =
        sourceFOSG.historyGame.outcomeKernel profile
  efgUdist_sourceFOSG :
    ∀ profile,
      (KernelGame.reindex playerEquiv efg.toKernelGame).udist
          (efgTranslateProfile profile) =
        sourceFOSG.historyGame.udist profile
  payoffGame : KernelGame P
  translateProfile : sourceFOSG.historyGame.Profile → payoffGame.Profile
  payoffGame_udist_sourceFOSG :
    ∀ profile,
      payoffGame.udist (translateProfile profile) =
        sourceFOSG.historyGame.udist profile

/-- Export handle for a checked program's payoff-facing serialized frontier
EFG. -/
noncomputable def frontierPlainEFG
    (program : WFProgram P L) [FiniteDomains program] :
    EFGExport P where
  efg := program.frontierPlainEFG
  playerEquiv := by
    change P ≃ Fin (Fintype.card P)
    exact FOSG.AugmentedEFGBridge.playerEquiv (ι := P)
  sourceFOSG := frontierFOSG program
  efgTranslateProfile := by
    exact program.frontierPlainEFGTranslateProfile
  efgOutcomeMap := by
    intro history
    exact history
  efgOutcomeKernel_sourceFOSG := by
    intro profile
    change PMF.map id
      ((KernelGame.reindex
            (FOSG.AugmentedEFGBridge.playerEquiv (ι := P))
            program.frontierPlainEFG.toKernelGame).outcomeKernel
          (program.frontierPlainEFGTranslateProfile profile)) =
        (frontierFOSG program).historyGame.outcomeKernel profile
    rw [PMF.map_id]
    exact
      program.frontierSemantics
        |>.plainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg profile
  efgUdist_sourceFOSG := by
    intro profile
    change
      (KernelGame.reindex
            (FOSG.AugmentedEFGBridge.playerEquiv (ι := P))
            program.frontierPlainEFG.toKernelGame).udist
          (program.frontierPlainEFGTranslateProfile profile) =
        (frontierFOSG program).historyGame.udist profile
    unfold KernelGame.udist
    rw [show
      (KernelGame.reindex
            (FOSG.AugmentedEFGBridge.playerEquiv (ι := P))
            program.frontierPlainEFG.toKernelGame).outcomeKernel
          (program.frontierPlainEFGTranslateProfile profile) =
        program.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
          profile by
          exact
            program.frontierSemantics
              |>.plainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg
                profile]
    congr 1
    funext history
    congr 1
    funext player
    simp [KernelGame.reindex, WFProgram.frontierPlainEFG,
      EFG.EFGGame.toKernelGame,
      ToEventGraph.FrontierGameSemantics.plainEFG,
      Machine.RoundView.toPlainEFGMachinePayoff,
      frontierFOSG,
      FOSG.AugmentedEFGBridge.origPlayer_playerEquiv]
    rfl
  payoffGame := program.frontierPlainEFGMachinePayoffKernelGame
  translateProfile := by
    exact program.frontierPlainEFGTranslateProfile
  payoffGame_udist_sourceFOSG := by
    intro profile
    exact
      program.frontierPlainEFGMachinePayoffKernelGame_udist_eq_fosg profile

/-- The export handle's certified profile translation preserves the joint
utility distribution of its source FOSG history game. -/
theorem frontierPlainEFG_payoffGame_udist_sourceFOSG
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    (frontierPlainEFG program).payoffGame.udist
        ((frontierPlainEFG program).translateProfile profile) =
      (frontierPlainEFG program).sourceFOSG.historyGame.udist profile :=
  (frontierPlainEFG program).payoffGame_udist_sourceFOSG profile

/-- The raw serialized EFG, reindexed back to the source player type, has the
same outcome law as the export handle's source FOSG history game. -/
theorem frontierPlainEFG_efgOutcomeKernel_sourceFOSG
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    PMF.map (frontierPlainEFG program).efgOutcomeMap
        ((KernelGame.reindex
            (frontierPlainEFG program).playerEquiv
            (frontierPlainEFG program).efg.toKernelGame).outcomeKernel
          ((frontierPlainEFG program).efgTranslateProfile profile)) =
      (frontierPlainEFG program).sourceFOSG.historyGame.outcomeKernel
        profile :=
  (frontierPlainEFG program).efgOutcomeKernel_sourceFOSG profile

/-- The raw serialized EFG, reindexed back to the source player type, preserves
the joint utility distribution of the export handle's source FOSG history
game. -/
theorem frontierPlainEFG_efgUdist_sourceFOSG
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    (KernelGame.reindex
          (frontierPlainEFG program).playerEquiv
          (frontierPlainEFG program).efg.toKernelGame).udist
        ((frontierPlainEFG program).efgTranslateProfile profile) =
      (frontierPlainEFG program).sourceFOSG.historyGame.udist profile :=
  (frontierPlainEFG program).efgUdist_sourceFOSG profile

/-- The raw serialized EFG and the payoff-facing export kernel induce the same
joint utility distribution under their certified translations from the source
FOSG history game. -/
theorem frontierPlainEFG_efgUdist_payoffGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    (KernelGame.reindex
          (frontierPlainEFG program).playerEquiv
          (frontierPlainEFG program).efg.toKernelGame).udist
        ((frontierPlainEFG program).efgTranslateProfile profile) =
      (frontierPlainEFG program).payoffGame.udist
        ((frontierPlainEFG program).translateProfile profile) := by
  rw [frontierPlainEFG_efgUdist_sourceFOSG,
    frontierPlainEFG_payoffGame_udist_sourceFOSG]

/-- Translate a native behavioral frontier profile into the payoff-facing EFG
profile carried by the export handle. -/
noncomputable def frontierPlainEFGProfile
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierPlainEFG program).payoffGame.Profile := by
  classical
  simpa [frontierPlainEFG] using
    program.frontierPlainEFGTranslateProfile
      (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon (fun _ => 0)
        profile).extend

/-- Translate a native pure frontier profile into the payoff-facing EFG profile
carried by the export handle, via the degenerate behavioral embedding. -/
noncomputable def frontierPlainEFGPureProfile
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    (frontierPlainEFG program).payoffGame.Profile := by
  classical
  simpa [frontierPlainEFG] using
    program.frontierPlainEFGTranslateProfile
      (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
        program.frontierSemantics.behavioral.view
        program.frontierSemantics.horizon (fun _ => 0)
        ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
          program.frontierSemantics.horizon profile)).extend

/-- Translate a product mixed-pure frontier profile into the payoff-facing EFG
profile carried by the export handle, via the canonical Kuhn
mixed-pure-to-behavioral realization. -/
noncomputable def frontierPlainEFGMixedPureProfile
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) :
    (frontierPlainEFG program).payoffGame.Profile := by
  classical
  exact
    frontierPlainEFGProfile program
      (program.mixedPureToBehavioralFrontierProfile profile)

/-- Translate a payoff-facing FOSG profile into the payoff-facing EFG profile
carried by the export handle. -/
noncomputable def frontierPlainEFGProfileOfFOSG
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    (frontierPlainEFG program).payoffGame.Profile := by
  classical
  simpa [frontierPlainEFG] using
    program.frontierPlainEFGTranslateProfile profile

/-- The payoff-facing EFG export has the same joint utility distribution as
the payoff-facing FOSG presentation. -/
theorem frontierPlainEFG_payoffGame_udist_fosg
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    (frontierPlainEFG program).payoffGame.udist
        (frontierPlainEFGProfileOfFOSG program profile) =
      program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile := by
  simpa [frontierPlainEFG, frontierPlainEFGProfileOfFOSG] using
    program.frontierPlainEFGMachinePayoffKernelGame_udist_eq_fosg profile

/-- The payoff-facing EFG export has the same joint utility distribution as
the native behavioral frontier game. -/
theorem frontierPlainEFG_payoffGame_udist_behavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierPlainEFG program).payoffGame.udist
        (frontierPlainEFGProfile program profile) =
      program.behavioralFrontierGame.udist profile := by
  simpa [frontierPlainEFG, frontierPlainEFGProfile] using
    program.frontierPlainEFGMachinePayoffKernelGame_udist_behavioralGame
      profile

/-- The payoff-facing EFG export has the same joint utility distribution as
the native pure frontier game under degenerate behavioral play. -/
theorem frontierPlainEFG_payoffGame_udist_pureGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    (frontierPlainEFG program).payoffGame.udist
        (frontierPlainEFGPureProfile program profile) =
      program.pureFrontierGame.udist profile := by
  simpa [frontierPlainEFG, frontierPlainEFGPureProfile] using
    program.frontierPlainEFGMachinePayoffKernelGame_udist_pureGame profile

/-- The payoff-facing EFG export has the same joint utility distribution as
the product mixed-pure frontier game under the canonical Kuhn
mixed-pure-to-behavioral realization. -/
theorem frontierPlainEFG_payoffGame_udist_mixedPureGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.MixedPureFrontierProfile) :
    (frontierPlainEFG program).payoffGame.udist
        (frontierPlainEFGMixedPureProfile program profile) =
      program.mixedPureFrontierGame.udist profile := by
  unfold frontierPlainEFGMixedPureProfile
  rw [frontierPlainEFG_payoffGame_udist_behavioralGame]
  unfold KernelGame.udist
  rw [program.mixedPureToBehavioralFrontierProfile_outcomeKernel profile]
  rfl

end Export

end Vegas

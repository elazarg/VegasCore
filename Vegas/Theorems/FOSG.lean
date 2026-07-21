/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Export.FOSG

/-!
# FOSG adequacy surface

The canonical frontier game has a bounded FOSG presentation.  The faithful
payoff-facing FOSG object is the machine-payoff history kernel: its histories
are FOSG histories, while its utility is the compiled machine payoff at the
corresponding terminal frontier state.
-/

namespace Vegas

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

noncomputable local instance instTheoremsFrontierFOSGTerminalDecidable
    (program : WFProgram P L) [FiniteDomains program] :
    DecidablePred program.frontierFOSG.terminal :=
  Classical.decPred _

/-- The canonical frontier FOSG is bounded by the completed-frontier horizon. -/
theorem frontierFOSG_bounded
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierFOSG.BoundedHorizon program.frontierSemantics.horizon :=
  program.frontierFOSG_boundedHorizon

/-- The active-player set of the FOSG presentation is the native bounded
frontier active-player set. -/
theorem frontierFOSG_active_eq_native
    (program : WFProgram P L) [FiniteDomains program]
    (state :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon) :
    program.frontierFOSG.active state =
      (program.frontierSemantics.behavioral.view).boundedActive
        program.frontierSemantics.horizon state := by
  rfl

/-- FOSG legal actions at a bounded state use the same player-local action
sets as the native frontier round view. -/
theorem frontierFOSG_availableActions_eq_native
    (program : WFProgram P L) [FiniteDomains program]
    (state :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon)
    (player : P) :
    program.frontierFOSG.availableActions state player =
      (program.frontierSemantics.behavioral.view).boundedAvailableActions
        program.frontierSemantics.horizon state player := by
  rfl

/-- FOSG private observations are the native machine observations of the
target bounded state. -/
theorem frontierFOSG_privateObservation_eq_native
    (program : WFProgram P L) [FiniteDomains program]
    (player : P)
    (state :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon)
    (action : program.frontierFOSG.LegalAction state)
    (dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon) :
    program.frontierFOSG.privObs player state action dst =
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).observe player dst.state := by
  rfl

/-- FOSG public observations are the native machine public observations of the
target bounded state. -/
theorem frontierFOSG_publicObservation_eq_native
    (program : WFProgram P L) [FiniteDomains program]
    (state :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon)
    (action : program.frontierFOSG.LegalAction state)
    (dst :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon) :
    program.frontierFOSG.pubObs state action dst =
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).publicView dst.state := by
  rfl

/-- Behavioral frontier runs in the FOSG presentation are exactly native
frontier histories repackaged as FOSG histories. -/
theorem frontierFOSG_behavioralRun_eq_nativeMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    (steps : Nat) :
    PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0))
        ((program.frontierSemantics.behavioral.view).runDist
          program.frontierSemantics.horizon steps profile) =
      program.frontierFOSG.runDist steps
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend :=
  program.frontierFOSG_runDist_eq_map_behavioralHistory profile steps

/-- Pure frontier profiles run through the FOSG presentation by first applying
the native pure-to-behavioral realization of the same frontier round view. -/
theorem frontierFOSG_pureRun_eq_nativeMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile)
    (steps : Nat) :
    PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0))
        ((program.frontierSemantics.behavioral.view).runDist
          program.frontierSemantics.horizon steps
          ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
            program.frontierSemantics.horizon profile)) =
      program.frontierFOSG.runDist steps
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
              program.frontierSemantics.horizon profile)).extend :=
  program.frontierFOSG_runDist_eq_map_pureHistory profile steps

/-- The payoff-facing FOSG history kernel has the native behavioral frontier
history law after translating behavioral profiles to FOSG profiles. -/
theorem frontierFOSG_payoffKernel_eq_nativeHistoryMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0))
        ((program.frontierSemantics.behavioral.view).runDist
          program.frontierSemantics.horizon
          program.frontierSemantics.horizon profile) :=
  program
    |>.frontierFOSGMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
      profile

/-- Any payoff-facing FOSG profile restricts to a native reachable behavioral
frontier profile with the same completed history law, after repackaging native
histories as FOSG histories. -/
theorem frontierFOSG_payoffKernel_eq_restrictedNativeHistoryMap
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
        profile =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0))
        ((program.frontierSemantics.behavioral.view).runDist
          program.frontierSemantics.horizon
          program.frontierSemantics.horizon
          (program.behavioralFrontierProfileOfFOSGProfile profile)) :=
  program
    |>.frontierFOSGMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_restrictedBehavioralHistory
      profile

/-- The payoff-facing FOSG history kernel and the native behavioral frontier
game induce the same utility distribution. -/
theorem frontierFOSG_payoff_udist_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      program.behavioralFrontierGame.udist profile :=
  program.frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralGame
    profile

/-- Arbitrary payoff-facing FOSG profiles are payoff-equivalent to their
restricted native reachable frontier profile. -/
theorem frontierFOSG_payoff_udist_restrictedBehavioral
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile =
      program.behavioralFrontierGame.udist
        (program.behavioralFrontierProfileOfFOSGProfile profile) :=
  program
    |>.frontierFOSGMachinePayoffHistoryKernelGame_udist_restrictedBehavioralGame
      profile

/-- The payoff-facing FOSG denotation is Kuhn-compatible with the induced
product mixed pure frontier profile at the utility-distribution level. -/
theorem frontierFOSG_payoff_udist_inducedMixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure profile) := by
  rw [program.frontierFOSG_payoff_udist_behavioral profile,
    program.behavioralFrontier_to_mixedPure_udist profile]

/-- Arbitrary payoff-facing FOSG profiles are Kuhn-compatible with the product
mixed pure frontier profile induced by their native reachable restriction. -/
theorem frontierFOSG_payoff_udist_restrictedInducedMixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure
          (program.behavioralFrontierProfileOfFOSGProfile profile)) := by
  rw [program.frontierFOSG_payoff_udist_restrictedBehavioral profile,
    program.behavioralFrontier_to_mixedPure_udist
      (program.behavioralFrontierProfileOfFOSGProfile profile)]

/-- Every supported payoff-facing FOSG history has a native completed frontier
history witness and a primitive-event batch replay to a terminal graph state. -/
theorem frontierFOSG_supportedHistory_nativeReplay
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    {history : program.frontierFOSGMachinePayoffHistoryKernelGame.Outcome}
    (hsupport :
      history ∈
        (program.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend).support) :
    ∃ nativeHistory : program.BehavioralFrontierHistory,
      nativeHistory ∈
        ((program.frontierSemantics.behavioral.view).runDist
          program.frontierSemantics.horizon
          program.frontierSemantics.horizon profile).support ∧
      Machine.RoundView.ToFOSG.historyOfBoundedHistory
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          nativeHistory = history ∧
      EventGraph.Terminal (ToEventGraph.compile program.core).graph
        nativeHistory.lastState.state.1 ∧
      (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (ToEventGraph.PrimitiveMachine
            (ToEventGraph.compile program.core))
          program.frontierSemantics.horizon).state)
        ((program.frontierSemantics.behavioral.view).boundedHistoryEventBatches
          program.frontierSemantics.horizon nativeHistory)
        nativeHistory.lastState.state :=
  program.frontierFOSGMachinePayoffHistoryKernelGame_support_nativeHistory
    profile hsupport

end WFProgram

namespace Export

/-- Exported FOSG history games preserve native behavioral frontier
utility distributions. -/
theorem frontierFOSGExport_historyGame_udist_behavioral
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.udist
        (frontierFOSGProfile program profile) =
      program.behavioralFrontierGame.udist profile :=
  frontierFOSG_historyGame_udist_behavioralGame program profile

/-- Exported FOSG history games are Kuhn-compatible with the induced
product mixed pure frontier profile at the utility-distribution level. -/
theorem frontierFOSGExport_historyGame_udist_inducedMixedPure
    {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.udist
        (frontierFOSGProfile program profile) =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure profile) := by
  rw [frontierFOSGExport_historyGame_udist_behavioral program profile,
    program.behavioralFrontier_to_mixedPure_udist profile]

end Export

end Vegas

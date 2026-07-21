import Vegas.Export.EFG

/-!
# EFG adequacy surface

Checked frontier programs have a payoff-facing serialized EFG presentation.
The strategic denotation remains the native completed frontier/FOSG surface;
this module records the utility-preserving EFG serialization facts used when a
plain extensive-form presentation is needed.
-/

namespace Vegas

namespace Theorems
namespace EFG

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

namespace WFProgram

/-- The payoff-facing EFG serialization has the same joint utility
distribution as the payoff-facing FOSG history game. -/
theorem frontier_plain_efg_payoff_udist_fosg
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile profile) =
      program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile :=
  program.frontierPlainEFGMachinePayoffKernelGame_udist_eq_fosg profile

/-- The payoff-facing EFG serialization has the same joint utility
distribution as the native behavioral completed-frontier game. -/
theorem frontier_plain_efg_payoff_udist_behavioral
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      program.behavioralFrontierGame.udist profile :=
  program.frontierPlainEFGMachinePayoffKernelGame_udist_behavioralGame
    profile

/-- Pure frontier profiles run through the payoff-facing EFG by first using
the degenerate behavioral embedding, preserving the joint utility law. -/
theorem frontier_plain_efg_payoff_udist_pure
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
              program.frontierSemantics.horizon profile)).extend) =
      program.pureFrontierGame.udist profile :=
  program.frontierPlainEFGMachinePayoffKernelGame_udist_pureGame profile

/-- Every supported payoff-facing EFG history is backed by a native completed
frontier history and an executable primitive-event replay. -/
theorem frontier_plain_efg_supported_history_native_replay
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile)
    {history : program.frontierPlainEFGMachinePayoffKernelGame.Outcome}
    (hsupport :
      history ∈
        (program.frontierPlainEFGMachinePayoffKernelGame.outcomeKernel
          (program.frontierPlainEFGTranslateProfile
            (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
              program.frontierSemantics.behavioral.view
              program.frontierSemantics.horizon (fun _ => 0)
              profile).extend)).support) :
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
  program.frontierPlainEFGMachinePayoffKernelGame_support_nativeHistory
    profile hsupport

/-- Export handles expose the same payoff-facing EFG/FOSG utility law as the
checked-program theorem surface. -/
theorem exported_frontier_plain_efg_payoff_udist_fosg
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    (Export.frontierPlainEFG program).payoffGame.udist
        (Export.frontierPlainEFGProfileOfFOSG program profile) =
      program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile :=
  Export.frontierPlainEFG_payoffGame_udist_fosg program profile

/-- Export handles carry their own FOSG source presentation and certified
profile-translation adequacy law. -/
theorem exported_frontier_plain_efg_payoff_udist_sourceFOSG
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile :
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    (Export.frontierPlainEFG program).payoffGame.udist
        ((Export.frontierPlainEFG program).translateProfile profile) =
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.udist
        profile :=
  Export.frontierPlainEFG_payoffGame_udist_sourceFOSG program profile

/-- The raw serialized EFG field of the export handle has the same outcome
law as the handle's source FOSG history game, after reindexing players back to
the checked program's player type. -/
theorem exported_frontier_plain_efg_outcomeKernel_sourceFOSG
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile :
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    PMF.map (Export.frontierPlainEFG program).efgOutcomeMap
        ((KernelGame.reindex
            (Export.frontierPlainEFG program).playerEquiv
            (Export.frontierPlainEFG program).efg.toKernelGame).outcomeKernel
          ((Export.frontierPlainEFG program).efgTranslateProfile profile)) =
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.outcomeKernel
        profile :=
  Export.frontierPlainEFG_efgOutcomeKernel_sourceFOSG program profile

/-- The raw serialized EFG field of the export handle preserves the source
FOSG history game's joint utility distribution. -/
theorem exported_frontier_plain_efg_udist_sourceFOSG
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile :
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    (KernelGame.reindex
          (Export.frontierPlainEFG program).playerEquiv
          (Export.frontierPlainEFG program).efg.toKernelGame).udist
        ((Export.frontierPlainEFG program).efgTranslateProfile profile) =
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.udist
        profile :=
  Export.frontierPlainEFG_efgUdist_sourceFOSG program profile

/-- The raw serialized EFG field and the payoff-facing export kernel have the
same joint utility distribution under their certified source-FOSG profile
translations. -/
theorem exported_frontier_plain_efg_udist_payoffGame
    (program : Vegas.WFProgram P L) [FiniteDomains program]
    (profile :
      (Export.frontierPlainEFG program).sourceFOSG.historyGame.Profile) :
    (KernelGame.reindex
          (Export.frontierPlainEFG program).playerEquiv
          (Export.frontierPlainEFG program).efg.toKernelGame).udist
        ((Export.frontierPlainEFG program).efgTranslateProfile profile) =
      (Export.frontierPlainEFG program).payoffGame.udist
        ((Export.frontierPlainEFG program).translateProfile profile) :=
  Export.frontierPlainEFG_efgUdist_payoffGame program profile

end WFProgram

end EFG
end Theorems

end Vegas

import Vegas.Presentation.FOSG.FromCore

/-!
# FOSG denotation handles

Checked frontier programs have a bounded FOSG denotation. The export handle
packages the dependent FOSG object together with the payoff-faithful strategic
history kernel. Histories come from the FOSG presentation; utility comes from
the compiled program payoff.
-/

namespace Vegas
namespace Export

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- A checked program's bounded FOSG presentation and canonical payoff-facing
history kernel. -/
structure FOSGExport (P : Type) [DecidableEq P] [Fintype P] where
  World : Type
  Act : P → Type
  PrivObs : P → Type
  PubObs : Type
  game : FOSG P World Act PrivObs PubObs
  horizon : Nat
  bounded : game.BoundedHorizon horizon
  actionFintype : ∀ player, Fintype (Option (Act player))
  terminalDecidable : DecidablePred game.terminal
  historyUtility : game.History → Payoff P

namespace FOSGExport

/-- Payoff-facing history kernel derived from an exported FOSG. Outcomes are
realized FOSG histories, and utility is the export's final-history payoff. -/
noncomputable def historyGame (handle : FOSGExport P) : KernelGame P := by
  classical
  letI : ∀ player, Fintype (Option (handle.Act player)) :=
    handle.actionFintype
  letI : DecidablePred handle.game.terminal :=
    handle.terminalDecidable
  exact
    { Strategy := fun player =>
        handle.game.LegalBehavioralStrategy player
      Outcome := handle.game.History
      utility := handle.historyUtility
      outcomeKernel := fun profile =>
        handle.game.runDist handle.horizon profile }

@[simp] theorem historyGame_utility
    (handle : FOSGExport P)
    (history : handle.historyGame.Outcome) :
    handle.historyGame.utility history =
      handle.historyUtility history := by
  rfl

end FOSGExport

/-- Export the checked frontier FOSG denotation of a finite-domain program. -/
noncomputable def frontierFOSG
    (program : WFProgram P L) [FiniteDomains program] :
    FOSGExport P where
  World :=
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)).BoundedState
        program.frontierSemantics.horizon
  Act := program.frontierSemantics.behavioral.view.Act
  PrivObs :=
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)).Obs
  PubObs :=
    (ToEventGraph.PrimitiveMachine
      (ToEventGraph.compile program.core)).Public
  game := program.frontierFOSG
  horizon := program.frontierSemantics.horizon
  bounded := program.frontierFOSG_boundedHorizon
  actionFintype := by
    intro player
    exact program.frontierSemantics.games.kuhnOptionalMoveFintype player
  terminalDecidable := Classical.decPred _
  historyUtility := fun history =>
    fun player =>
      Machine.RoundView.optionOutcomeUtility
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))
        (fun _ => 0)
        ((ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core)).outcome history.lastState.state)
        player

/-- The exported history kernel uses the same outcome law as the program's
canonical payoff-facing FOSG history kernel. -/
theorem frontierFOSG_historyGame_outcomeKernel_eq_program
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierFOSG program).historyGame.Profile) :
    (frontierFOSG program).historyGame.outcomeKernel profile =
      program.frontierFOSGMachinePayoffHistoryKernelGame.outcomeKernel
        profile := by
  rfl

/-- The exported history kernel uses the same final-history utility as the
program's canonical payoff-facing FOSG history kernel. -/
theorem frontierFOSG_historyGame_utility_eq_program
    (program : WFProgram P L) [FiniteDomains program]
    (history : (frontierFOSG program).historyGame.Outcome) :
    (frontierFOSG program).historyGame.utility history =
      program.frontierFOSGMachinePayoffHistoryKernelGame.utility history := by
  rfl

/-- Translate a native behavioral frontier profile into the payoff-facing FOSG
profile carried by the export handle. -/
noncomputable def frontierFOSGProfile
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.Profile := by
  classical
  exact
    (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
      program.frontierSemantics.behavioral.view
      program.frontierSemantics.horizon (fun _ => 0)
      profile).extend

/-- Restrict a payoff-facing exported FOSG profile back to the native reachable
frontier behavioral profile it induces. -/
noncomputable def frontierFOSGRestrictedProfile
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierFOSG program).historyGame.Profile) :
    program.BehavioralFrontierProfile := by
  exact program.behavioralFrontierProfileOfFOSGProfile profile

/-- The FOSG export has the same joint utility distribution as
the native behavioral frontier game. -/
theorem frontierFOSG_historyGame_udist_behavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.udist
        (frontierFOSGProfile program profile) =
      program.behavioralFrontierGame.udist profile := by
  exact
    program.frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralGame
      profile

/-- The exported FOSG history game has the source payoff utility law of the
native behavioral frontier game. -/
theorem frontierFOSG_sourcePayoffGame_udist_behavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.udist
        (frontierFOSGProfile program profile) =
      program.behavioralFrontierGame.udist profile :=
  frontierFOSG_historyGame_udist_behavioralGame program profile

/-- Every exported FOSG profile has the same joint utility
distribution as its native reachable frontier restriction. -/
theorem frontierFOSG_historyGame_udist_restrictedBehavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierFOSG program).historyGame.Profile) :
    (frontierFOSG program).historyGame.udist profile =
      program.behavioralFrontierGame.udist
        (frontierFOSGRestrictedProfile program profile) := by
  exact
    program
      |>.frontierFOSGMachinePayoffHistoryKernelGame_udist_restrictedBehavioralGame
        profile

/-- Every exported FOSG profile has the source payoff utility law of its
native reachable frontier restriction. -/
theorem frontierFOSG_sourcePayoffGame_udist_restrictedBehavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierFOSG program).historyGame.Profile) :
    (frontierFOSG program).historyGame.udist profile =
      program.behavioralFrontierGame.udist
        (frontierFOSGRestrictedProfile program profile) :=
  frontierFOSG_historyGame_udist_restrictedBehavioralGame program profile

/-- The FOSG export has the same joint utility distribution as
the product mixed pure frontier profile induced by Kuhn realization. -/
theorem frontierFOSG_historyGame_udist_inducedMixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.udist
        (frontierFOSGProfile program profile) =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure profile) := by
  rw [frontierFOSG_historyGame_udist_behavioralGame
      program profile,
    program.behavioralFrontier_to_mixedPure_udist profile]

/-- Every exported FOSG profile is Kuhn-compatible with the product mixed pure
frontier profile induced by its native reachable restriction. -/
theorem frontierFOSG_historyGame_udist_restrictedInducedMixedPure
    (program : WFProgram P L) [FiniteDomains program]
    (profile : (frontierFOSG program).historyGame.Profile) :
    (frontierFOSG program).historyGame.udist profile =
      program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure
          (frontierFOSGRestrictedProfile program profile)) := by
  rw [
    frontierFOSG_historyGame_udist_restrictedBehavioralGame
      program profile,
    program.behavioralFrontier_to_mixedPure_udist
      (frontierFOSGRestrictedProfile program profile)]

/-- The FOSG export has the same joint utility distribution as
the native behavioral history kernel game. -/
theorem frontierFOSG_historyGame_udist_behavioralHistoryGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    (frontierFOSG program).historyGame.udist
        (frontierFOSGProfile program profile) =
      program.behavioralFrontierHistoryKernelGame.udist profile := by
  exact
    program
      |>.frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralHistoryKernelGame
        profile

end Export
end Vegas

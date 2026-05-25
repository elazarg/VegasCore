import Vegas.Core.ToEventGraph.Games
import Vegas.GameBridge.FOSG.RoundViewEquiv

/-!
# Program frontier games as FOSGs

The canonical behavioral denotation of a checked finite program is a bounded
factored-observation stochastic game at the frontier checkpoint level.  The
native `Machine.RoundView` construction supplies the executable round kernel;
the FOSG object is the standard game-form surface used for paper-facing
strategic statements.
-/

namespace Vegas

open GameTheory

namespace ToEventGraph

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
variable {program : WFProgram P L} [FiniteDomains program]

namespace FrontierGameSemantics

/-- FOSG denotation of the canonical behavioral frontier round view.  The zero
cutoff is off the support of completed frontier runs; malformed cutoff states
are still assigned an explicit payoff vector by the generic FOSG reward
interface. -/
noncomputable def fosg
    (semantics : FrontierGameSemantics program) :=
  (semantics.behavioral.view).toFOSG semantics.horizon (fun _ => 0)

/-- The frontier FOSG terminates within the completion horizon. -/
theorem fosg_boundedHorizon
    (semantics : FrontierGameSemantics program) :
    semantics.fosg.BoundedHorizon semantics.horizon :=
  Machine.RoundView.toFOSG_boundedHorizon
    semantics.behavioral.view semantics.horizon (fun _ => 0)

noncomputable local instance instFosgTerminalDecidable
    (semantics : FrontierGameSemantics program) :
    DecidablePred semantics.fosg.terminal :=
  Classical.decPred _

/-- Running the frontier FOSG under the translated behavioral profile is the
native bounded frontier run, with native histories repackaged as FOSG
histories. -/
theorem fosg_runDist_eq_map_behavioralHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile)
    (steps : Nat) :
    PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))
        ((semantics.behavioral.view).runDist
          semantics.horizon steps profile) =
      semantics.fosg.runDist steps
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            profile).extend := by
  classical
  simpa [fosg] using
    Machine.RoundView.ToFOSG.runDist_historyOfBoundedHistory
      (view := semantics.behavioral.view)
      (horizon := semantics.horizon)
      (cutoff := fun _ => 0)
      profile steps

/-- Pure frontier profiles run through the FOSG presentation by first applying
the native pure-to-behavioral realization of the same frontier round view. -/
theorem fosg_runDist_eq_map_pureHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.pureGame.Profile)
    (steps : Nat) :
    PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))
        ((semantics.behavioral.view).runDist
          semantics.horizon steps
          ((semantics.behavioral.view).legalPureToBehavioral
            semantics.horizon profile)) =
      semantics.fosg.runDist steps
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            ((semantics.behavioral.view).legalPureToBehavioral
              semantics.horizon profile)).extend := by
  simpa using
    semantics.fosg_runDist_eq_map_behavioralHistory
      ((semantics.behavioral.view).legalPureToBehavioral
        semantics.horizon profile) steps

/-- Transition-reward history kernel induced by the bounded frontier FOSG.
Outcomes are FOSG histories; profiles are legal FOSG behavioral profiles. -/
noncomputable def fosgHistoryKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  Machine.RoundView.ToFOSG.historyKernelGame
    semantics.behavioral.view semantics.horizon (fun _ => 0)

/-- The FOSG history-kernel outcome law agrees with the native behavioral
frontier run after translating profiles and repackaging histories. -/
theorem fosgHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.fosgHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          semantics.behavioral.view semantics.horizon (fun _ => 0)
          profile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))
        ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon profile) := by
  simpa [fosgHistoryKernelGame] using
    Machine.RoundView.ToFOSG.historyKernelGame_outcomeKernel_eq_map_runDist
      (view := semantics.behavioral.view)
      (horizon := semantics.horizon)
      (cutoff := fun _ => 0)
      profile

/-- Payoff-faithful FOSG history kernel whose utility is the final compiled
machine payoff, not the cumulative FOSG transition reward.  This is the
strategic FOSG denotation for compiled frontier games. -/
noncomputable def fosgMachinePayoffHistoryKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P :=
  Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame
    semantics.behavioral.view semantics.horizon (fun _ => 0)

/-- Restrict a payoff-facing FOSG behavioral profile back to the native
bounded frontier profile it induces on reachable information states. -/
noncomputable def behavioralProfileOfFOSGProfile
    (semantics : FrontierGameSemantics program)
    (profile : semantics.fosgMachinePayoffHistoryKernelGame.Profile) :
    semantics.behavioralGame.Profile :=
  Machine.RoundView.ToFOSG.boundedBehavioralProfileOfLegalBehavioralProfile
    semantics.behavioral.view semantics.horizon (fun _ => 0) profile

theorem fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          semantics.behavioral.view semantics.horizon (fun _ => 0)
          profile).extend =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))
        ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon profile) := by
  simpa [fosgMachinePayoffHistoryKernelGame] using
    Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame_outcomeKernel_eq_map_runDist
      (view := semantics.behavioral.view)
      (horizon := semantics.horizon)
      (cutoff := fun _ => 0)
      profile

/-- Every payoff-facing FOSG profile is run-equivalent to its native reachable
frontier restriction. -/
theorem fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_restrictedBehavioralHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.fosgMachinePayoffHistoryKernelGame.Profile) :
    semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel profile =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))
        ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon
          (semantics.behavioralProfileOfFOSGProfile profile)) := by
  simpa [fosgMachinePayoffHistoryKernelGame,
    behavioralProfileOfFOSGProfile] using
    Machine.RoundView.ToFOSG.runDist_eq_map_boundedBehavioralProfileOfLegalBehavioralProfile
      (view := semantics.behavioral.view)
      (horizon := semantics.horizon)
      (cutoff := fun _ => 0)
      profile semantics.horizon

/-- The payoff-facing FOSG history kernel and the native behavioral completed
history kernel induce the same joint utility distribution. -/
theorem fosgMachinePayoffHistoryKernelGame_udist_behavioralHistoryKernelGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.fosgMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          semantics.behavioral.view semantics.horizon (fun _ => 0)
          profile).extend =
      semantics.behavioralHistoryKernelGame.udist profile := by
  change
    (semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            profile).extend).bind
        (fun h =>
          PMF.pure (semantics.fosgMachinePayoffHistoryKernelGame.utility h)) =
      (semantics.behavioralHistoryKernel profile).bind
        (fun h => PMF.pure (semantics.behavioralHistoryUtility h))
  rw [semantics.fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
    profile]
  change
    (((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon profile).map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))).bind
        (fun h =>
          PMF.pure (semantics.fosgMachinePayoffHistoryKernelGame.utility h)) =
      ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon profile).bind
        (fun h => PMF.pure (semantics.behavioralHistoryUtility h))
  rw [PMF.bind_map]
  congr
  funext history
  apply congrArg PMF.pure
  funext who
  simp [fosgMachinePayoffHistoryKernelGame,
    Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame,
    FrontierGameSemantics.behavioralHistoryUtility,
    FrontierGameSemantics.optionOutcomePayoff]
  cases ((PrimitiveMachine (compile program.core)).outcome
    history.lastState.state) <;> rfl

/-- For arbitrary payoff-facing FOSG profiles, restricting the profile to the
native reachable frontier surface preserves the joint utility distribution. -/
theorem fosgMachinePayoffHistoryKernelGame_udist_restrictedBehavioralHistoryKernelGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.fosgMachinePayoffHistoryKernelGame.Profile) :
    semantics.fosgMachinePayoffHistoryKernelGame.udist profile =
      semantics.behavioralHistoryKernelGame.udist
        (semantics.behavioralProfileOfFOSGProfile profile) := by
  change
    (semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel profile).bind
        (fun h =>
          PMF.pure (semantics.fosgMachinePayoffHistoryKernelGame.utility h)) =
      (semantics.behavioralHistoryKernel
          (semantics.behavioralProfileOfFOSGProfile profile)).bind
        (fun h => PMF.pure (semantics.behavioralHistoryUtility h))
  rw [
    semantics.fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_restrictedBehavioralHistory
      profile]
  change
    (((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon
          (semantics.behavioralProfileOfFOSGProfile profile)).map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))).bind
        (fun h =>
          PMF.pure (semantics.fosgMachinePayoffHistoryKernelGame.utility h)) =
      ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon
          (semantics.behavioralProfileOfFOSGProfile profile)).bind
        (fun h => PMF.pure (semantics.behavioralHistoryUtility h))
  rw [PMF.bind_map]
  congr
  funext history
  apply congrArg PMF.pure
  funext who
  simp [fosgMachinePayoffHistoryKernelGame,
    Machine.RoundView.ToFOSG.machinePayoffHistoryKernelGame,
    FrontierGameSemantics.behavioralHistoryUtility,
    FrontierGameSemantics.optionOutcomePayoff]
  cases ((PrimitiveMachine (compile program.core)).outcome
    history.lastState.state) <;> rfl

/-- The payoff-facing FOSG history kernel and the native behavioral frontier
game induce the same joint utility distribution. -/
theorem fosgMachinePayoffHistoryKernelGame_udist_behavioralGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.fosgMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          semantics.behavioral.view semantics.horizon (fun _ => 0)
          profile).extend =
      semantics.behavioralGame.udist profile := by
  rw [semantics.fosgMachinePayoffHistoryKernelGame_udist_behavioralHistoryKernelGame
    profile]
  exact semantics.behavioralHistoryKernelGame_udist profile

/-- Arbitrary payoff-facing FOSG profiles have the same joint utility
distribution as their native reachable frontier restriction. -/
theorem fosgMachinePayoffHistoryKernelGame_udist_restrictedBehavioralGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.fosgMachinePayoffHistoryKernelGame.Profile) :
    semantics.fosgMachinePayoffHistoryKernelGame.udist profile =
      semantics.behavioralGame.udist
        (semantics.behavioralProfileOfFOSGProfile profile) := by
  rw [
    semantics.fosgMachinePayoffHistoryKernelGame_udist_restrictedBehavioralHistoryKernelGame
      profile]
  exact
    semantics.behavioralHistoryKernelGame_udist
      (semantics.behavioralProfileOfFOSGProfile profile)

/-- Every supported payoff-facing FOSG history is backed by a native completed
frontier history, a terminal graph checkpoint, and executable primitive event
batches. -/
theorem fosgMachinePayoffHistoryKernelGame_support_nativeHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile)
    {history : semantics.fosgMachinePayoffHistoryKernelGame.Outcome}
    (hsupport :
      history ∈
        (semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            profile).extend).support) :
    ∃ nativeHistory : semantics.BehavioralHistory,
      nativeHistory ∈
        ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon profile).support ∧
      Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0)
          nativeHistory = history ∧
      EventGraph.Terminal (compile program.core).graph
        nativeHistory.lastState.state.1 ∧
      (PrimitiveMachine (compile program.core)).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine (compile program.core))
          semantics.horizon).state)
        ((semantics.behavioral.view).boundedHistoryEventBatches
          semantics.horizon nativeHistory)
        nativeHistory.lastState.state := by
  classical
  letI :
      ∀ player,
        Fintype
          (Option
            ((frontierRoundView
              (compile program.core)
              (frontierPresentation
                (compile program.core)
                (compile_guardLive program))
              semantics.behavioral.semantics).Act player)) := by
    intro player
    simpa [FrontierGameSemantics.behavioral,
      CompletedFrontierBehavioralKernelGame.view] using
      semantics.games.kuhnOptionalMoveFintype player
  have hmap := hsupport
  rw [semantics.fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
    profile] at hmap
  rcases (PMF.mem_support_map_iff _ _ _).mp hmap with
    ⟨nativeHistory, hnative, hhistory⟩
  have hterminal :
      EventGraph.Terminal (compile program.core).graph
        nativeHistory.lastState.state.1 := by
    simpa [FrontierGameSemantics.behavioral,
      FrontierGameSemantics.horizon] using
      ToEventGraph.FrontierRoundSemantics.runDist_support_terminal_of_completionBound
        semantics.behavioral.semantics profile hnative
  have hrun :
      (PrimitiveMachine (compile program.core)).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine (compile program.core))
          semantics.horizon).state)
        ((semantics.behavioral.view).boundedHistoryEventBatches
          semantics.horizon nativeHistory)
        nativeHistory.lastState.state := by
    simpa [FrontierGameSemantics.behavioral,
      FrontierGameSemantics.horizon] using
      ToEventGraph.FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
        semantics.behavioral.semantics nativeHistory
  exact ⟨nativeHistory, hnative, hhistory, hterminal, hrun⟩

end FrontierGameSemantics
end ToEventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- FOSG denotation of a checked program's canonical frontier game. -/
noncomputable def frontierFOSG
    (program : WFProgram P L) [FiniteDomains program] :=
  program.frontierSemantics.fosg

/-- The program frontier FOSG is bounded by the canonical completion horizon. -/
theorem frontierFOSG_boundedHorizon
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierFOSG.BoundedHorizon program.frontierSemantics.horizon :=
  program.frontierSemantics.fosg_boundedHorizon

noncomputable local instance instFrontierFOSGTerminalDecidable
    (program : WFProgram P L) [FiniteDomains program] :
    DecidablePred program.frontierFOSG.terminal :=
  Classical.decPred _

/-- Program-facing execution law for the FOSG presentation of the canonical
behavioral frontier game. -/
theorem frontierFOSG_runDist_eq_map_behavioralHistory
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
            profile).extend := by
  simpa [frontierFOSG, ToEventGraph.FrontierGameSemantics.fosg,
    ToEventGraph.FrontierGameSemantics.horizon,
    BehavioralFrontierProfile] using
    program.frontierSemantics
      |>.fosg_runDist_eq_map_behavioralHistory profile steps

/-- Program-facing pure-profile execution law for the FOSG presentation of the
canonical frontier game. -/
theorem frontierFOSG_runDist_eq_map_pureHistory
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
              program.frontierSemantics.horizon profile)).extend := by
  simpa [frontierFOSG, ToEventGraph.FrontierGameSemantics.fosg,
    ToEventGraph.FrontierGameSemantics.horizon,
    PureFrontierProfile] using
    program.frontierSemantics
      |>.fosg_runDist_eq_map_pureHistory profile steps

/-- Program-facing transition-reward FOSG history kernel of the canonical
frontier game. -/
noncomputable def frontierFOSGHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.fosgHistoryKernelGame

/-- Program-facing FOSG history-kernel outcome law for behavioral frontier
profiles. -/
theorem frontierFOSGHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGHistoryKernelGame.outcomeKernel
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
          program.frontierSemantics.horizon profile) := by
  simpa [frontierFOSGHistoryKernelGame, BehavioralFrontierProfile] using
    program.frontierSemantics
      |>.fosgHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
        profile

/-- Program-facing payoff-faithful FOSG history kernel with final machine
payoff utility. -/
noncomputable def frontierFOSGMachinePayoffHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.fosgMachinePayoffHistoryKernelGame

/-- Restrict a payoff-facing FOSG behavioral profile to the native reachable
frontier profile it induces. -/
noncomputable def behavioralFrontierProfileOfFOSGProfile
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.BehavioralFrontierProfile :=
  program.frontierSemantics.behavioralProfileOfFOSGProfile profile

theorem frontierFOSGMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
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
          program.frontierSemantics.horizon profile) := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    BehavioralFrontierProfile] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
        profile

theorem frontierFOSGMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_restrictedBehavioralHistory
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
          (program.behavioralFrontierProfileOfFOSGProfile profile)) := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    behavioralFrontierProfileOfFOSGProfile,
    BehavioralFrontierProfile] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_restrictedBehavioralHistory
        profile

theorem frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      program.behavioralFrontierHistoryKernelGame.udist profile := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    BehavioralFrontierProfile, behavioralFrontierHistoryKernelGame] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_udist_behavioralHistoryKernelGame
        profile

theorem frontierFOSGMachinePayoffHistoryKernelGame_udist_behavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      program.behavioralFrontierGame.udist profile := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    BehavioralFrontierProfile, behavioralFrontierGame] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_udist_behavioralGame profile

theorem frontierFOSGMachinePayoffHistoryKernelGame_udist_restrictedBehavioralHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile =
      program.behavioralFrontierHistoryKernelGame.udist
        (program.behavioralFrontierProfileOfFOSGProfile profile) := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    behavioralFrontierProfileOfFOSGProfile, BehavioralFrontierProfile,
    behavioralFrontierHistoryKernelGame] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_udist_restrictedBehavioralHistoryKernelGame
        profile

theorem frontierFOSGMachinePayoffHistoryKernelGame_udist_restrictedBehavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist profile =
      program.behavioralFrontierGame.udist
        (program.behavioralFrontierProfileOfFOSGProfile profile) := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    behavioralFrontierProfileOfFOSGProfile, BehavioralFrontierProfile,
    behavioralFrontierGame] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_udist_restrictedBehavioralGame
        profile

/-- Program-facing runtime witness for supported payoff-facing FOSG histories:
each such FOSG history comes from a native completed frontier history with
primitive event batches reaching a terminal graph checkpoint. -/
theorem frontierFOSGMachinePayoffHistoryKernelGame_support_nativeHistory
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
        nativeHistory.lastState.state := by
  simpa [frontierFOSGMachinePayoffHistoryKernelGame,
    BehavioralFrontierProfile, BehavioralFrontierHistory] using
    program.frontierSemantics
      |>.fosgMachinePayoffHistoryKernelGame_support_nativeHistory
        profile hsupport

end WFProgram

end Vegas

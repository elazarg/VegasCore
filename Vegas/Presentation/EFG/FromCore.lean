import Vegas.Presentation.EFG.FromRoundView
import Vegas.Presentation.FOSG.FromCore
import Vegas.EventGraph.FiniteState

/-!
# Program frontier games as EFGs

The checked frontier game already has a bounded FOSG presentation.  Since
reachable event-graph configurations are finite via graph snapshots, the same
bounded round view can be serialized to a plain extensive-form game through
the shared FOSG-to-EFG bridge.
-/

namespace Vegas

open GameTheory

namespace ToEventGraph

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
variable {program : WFProgram P L} [FiniteDomains program]

namespace FrontierGameSemantics

namespace EFGInstances

variable (semantics : FrontierGameSemantics program)

@[reducible] noncomputable def primitiveStateFintype
    (_semantics : FrontierGameSemantics program) :
    Fintype (PrimitiveMachine (compile program.core)).State := by
  letI :
      ∀ field : Fin (compile program.core).graph.fieldCount,
        Fintype (L.Val ((compile program.core).graph.fieldRow field).ty) :=
    _semantics.games.fieldFintype
  exact
    EventGraph.StateSnapshot.reachableConfigFintype
      (compile program.core).graph (compile program.core).graphWF

noncomputable scoped instance actFintype (player : P) :
    Fintype (semantics.behavioral.view.Act player) := by
  classical
  letI :
      ∀ node : Fin (compile program.core).graph.nodeCount,
        Fintype (L.Val ((compile program.core).graph.nodeRow node).ty) :=
    semantics.games.nodeFintype
  dsimp [FrontierGameSemantics.behavioral,
    CompletedFrontierBehavioralKernelGame.view,
    CompletedFrontierKuhnGames.behavioral,
    CompletedFrontierKuhnGames.view, frontierRoundView,
    EventGraph.frontierRoundView, EventGraph.FrontierAct]
  infer_instance

noncomputable scoped instance actDecidableEq (player : P) :
    DecidableEq (semantics.behavioral.view.Act player) :=
  Classical.decEq _

noncomputable scoped instance obsFintype (player : P) :
    Fintype ((PrimitiveMachine (compile program.core)).Obs player) := by
  classical
  letI :
      ∀ field : Fin (compile program.core).graph.fieldCount,
        Fintype (L.Val ((compile program.core).graph.fieldRow field).ty) :=
    semantics.games.fieldFintype
  dsimp [PrimitiveMachine, primitiveMachineSpec,
    EventGraph.PrimitiveMachineOf, EventGraph.ToMachine.primitiveMachine]
  infer_instance

noncomputable scoped instance obsDecidableEq (player : P) :
    DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
  Classical.decEq _

noncomputable scoped instance publicFintype :
    Fintype (PrimitiveMachine (compile program.core)).Public := by
  classical
  letI :
      ∀ field : Fin (compile program.core).graph.fieldCount,
        Fintype (L.Val ((compile program.core).graph.fieldRow field).ty) :=
    semantics.games.fieldFintype
  dsimp [PrimitiveMachine, primitiveMachineSpec,
    EventGraph.PrimitiveMachineOf, EventGraph.ToMachine.primitiveMachine]
  infer_instance

noncomputable scoped instance publicDecidableEq :
    DecidableEq (PrimitiveMachine (compile program.core)).Public :=
  Classical.decEq _

end EFGInstances

open scoped EFGInstances

/-- Bounded FOSG package used as the source of EFG serialization. -/
noncomputable def boundedFOSGPresentation
    (semantics : FrontierGameSemantics program) :
    Languages.Expressiveness.BoundedFOSGPresentation P := by
  classical
  letI := EFGInstances.primitiveStateFintype semantics
  letI := EFGInstances.actFintype semantics
  letI :
      ∀ player, DecidableEq (semantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.obsFintype semantics
  letI :
      ∀ player,
        DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.publicFintype semantics
  letI : DecidableEq (PrimitiveMachine (compile program.core)).Public :=
    Classical.decEq _
  exact
    semantics.behavioral.view.boundedFOSGPresentation
      semantics.horizon (fun _ => 0)

/-- Plain EFG serialization of the canonical behavioral frontier game. -/
noncomputable def plainEFG
    (semantics : FrontierGameSemantics program) :
    EFG.EFGGame := by
  classical
  letI := EFGInstances.primitiveStateFintype semantics
  letI := EFGInstances.actFintype semantics
  letI :
      ∀ player, DecidableEq (semantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.obsFintype semantics
  letI :
      ∀ player,
        DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.publicFintype semantics
  letI : DecidableEq (PrimitiveMachine (compile program.core)).Public :=
    Classical.decEq _
  exact
    semantics.behavioral.view.toPlainEFGMachinePayoff
      semantics.horizon (fun _ => 0)

/-- Payoff-facing EFG kernel game for the canonical behavioral frontier game. -/
noncomputable def plainEFGMachinePayoffKernelGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P := by
  classical
  letI := EFGInstances.primitiveStateFintype semantics
  letI := EFGInstances.actFintype semantics
  letI :
      ∀ player, DecidableEq (semantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.obsFintype semantics
  letI :
      ∀ player,
        DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.publicFintype semantics
  letI : DecidableEq (PrimitiveMachine (compile program.core)).Public :=
    Classical.decEq _
  exact
    semantics.behavioral.view.toPlainEFGMachinePayoffKernelGame
      semantics.horizon (fun _ => 0)

/-- Translate a legal FOSG behavioral profile to the corresponding behavioral
profile of the serialized EFG. -/
noncomputable def plainEFGTranslateProfile
    (semantics : FrontierGameSemantics program) :
    semantics.fosgMachinePayoffHistoryKernelGame.Profile →
      semantics.plainEFGMachinePayoffKernelGame.Profile := by
  classical
  letI := EFGInstances.primitiveStateFintype semantics
  letI := EFGInstances.actFintype semantics
  letI :
      ∀ player, DecidableEq (semantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.obsFintype semantics
  letI :
      ∀ player,
        DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.publicFintype semantics
  letI : DecidableEq (PrimitiveMachine (compile program.core)).Public :=
    Classical.decEq _
  exact (semantics.boundedFOSGPresentation).translateProfile

/-- The final-payoff EFG outcome law is the final-payoff FOSG history outcome
law after translating behavioral profiles. -/
theorem plainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg
    (semantics : FrontierGameSemantics program)
    (profile : semantics.fosgMachinePayoffHistoryKernelGame.Profile) :
    semantics.plainEFGMachinePayoffKernelGame.outcomeKernel
        (semantics.plainEFGTranslateProfile profile) =
      semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel profile := by
  classical
  letI := EFGInstances.primitiveStateFintype semantics
  letI := EFGInstances.actFintype semantics
  letI :
      ∀ player, DecidableEq (semantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.obsFintype semantics
  letI :
      ∀ player,
        DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.publicFintype semantics
  letI : DecidableEq (PrimitiveMachine (compile program.core)).Public :=
    Classical.decEq _
  simpa [plainEFGMachinePayoffKernelGame, plainEFGTranslateProfile,
    boundedFOSGPresentation,
    FrontierGameSemantics.fosgMachinePayoffHistoryKernelGame] using
    semantics.behavioral.view.toPlainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg
      semantics.horizon (fun _ => 0) profile

/-- The payoff-facing EFG has the same joint utility law as the payoff-facing
FOSG history kernel after translating behavioral profiles. -/
theorem plainEFGMachinePayoffKernelGame_udist_eq_fosg
    (semantics : FrontierGameSemantics program)
    (profile : semantics.fosgMachinePayoffHistoryKernelGame.Profile) :
    semantics.plainEFGMachinePayoffKernelGame.udist
        (semantics.plainEFGTranslateProfile profile) =
      semantics.fosgMachinePayoffHistoryKernelGame.udist profile := by
  classical
  letI := EFGInstances.primitiveStateFintype semantics
  letI := EFGInstances.actFintype semantics
  letI :
      ∀ player, DecidableEq (semantics.behavioral.view.Act player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.obsFintype semantics
  letI :
      ∀ player,
        DecidableEq ((PrimitiveMachine (compile program.core)).Obs player) :=
    fun _ => Classical.decEq _
  letI := EFGInstances.publicFintype semantics
  letI : DecidableEq (PrimitiveMachine (compile program.core)).Public :=
    Classical.decEq _
  change
    (semantics.plainEFGMachinePayoffKernelGame.outcomeKernel
          (semantics.plainEFGTranslateProfile profile)).bind
        (fun h => PMF.pure
          (semantics.plainEFGMachinePayoffKernelGame.utility h)) =
      (semantics.fosgMachinePayoffHistoryKernelGame.outcomeKernel profile).bind
        (fun h => PMF.pure
          (semantics.fosgMachinePayoffHistoryKernelGame.utility h))
  rw [semantics.plainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg profile]
  congr

/-- Native behavioral frontier profiles run through the EFG presentation by
first translating them to the equivalent FOSG behavioral profile. -/
theorem plainEFGMachinePayoffKernelGame_outcomeKernel_eq_map_behavioralHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.plainEFGMachinePayoffKernelGame.outcomeKernel
        (semantics.plainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            profile).extend) =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          semantics.behavioral.view semantics.horizon (fun _ => 0))
        ((semantics.behavioral.view).runDist
          semantics.horizon semantics.horizon profile) := by
  rw [semantics.plainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg]
  exact semantics.fosgMachinePayoffHistoryKernelGame_outcomeKernel_eq_map_behavioralHistory
    profile

/-- The payoff-facing EFG and native behavioral completed-history game induce
the same joint utility distribution under the profile translation. -/
theorem plainEFGMachinePayoffKernelGame_udist_behavioralHistoryKernelGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.plainEFGMachinePayoffKernelGame.udist
        (semantics.plainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            profile).extend) =
      semantics.behavioralHistoryKernelGame.udist profile := by
  rw [semantics.plainEFGMachinePayoffKernelGame_udist_eq_fosg]
  exact semantics.fosgMachinePayoffHistoryKernelGame_udist_behavioralHistoryKernelGame
    profile

/-- The payoff-facing EFG and native behavioral frontier game induce the same
joint utility distribution under the profile translation. -/
theorem plainEFGMachinePayoffKernelGame_udist_behavioralGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.plainEFGMachinePayoffKernelGame.udist
        (semantics.plainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            profile).extend) =
      semantics.behavioralGame.udist profile := by
  rw [semantics.plainEFGMachinePayoffKernelGame_udist_eq_fosg]
  exact semantics.fosgMachinePayoffHistoryKernelGame_udist_behavioralGame
    profile

/-- Pure frontier profiles run through the EFG presentation by first embedding
them as behavioral frontier profiles. -/
theorem plainEFGMachinePayoffKernelGame_udist_pureGame
    (semantics : FrontierGameSemantics program)
    (profile : semantics.pureGame.Profile) :
    semantics.plainEFGMachinePayoffKernelGame.udist
        (semantics.plainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            semantics.behavioral.view semantics.horizon (fun _ => 0)
            ((semantics.behavioral.view).legalPureToBehavioral
              semantics.horizon profile)).extend) =
      semantics.pureGame.udist profile := by
  rw [semantics.plainEFGMachinePayoffKernelGame_udist_behavioralGame]
  exact semantics.pureToBehavioralUdist profile

/-- Every supported payoff-facing EFG history is backed by a native completed
frontier history with executable primitive event batches. -/
theorem plainEFGMachinePayoffKernelGame_support_nativeHistory
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile)
    {history : semantics.plainEFGMachinePayoffKernelGame.Outcome}
    (hsupport :
      history ∈
        (semantics.plainEFGMachinePayoffKernelGame.outcomeKernel
          (semantics.plainEFGTranslateProfile
            (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
              semantics.behavioral.view semantics.horizon (fun _ => 0)
              profile).extend)).support) :
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
  have hfosg := hsupport
  rw [semantics.plainEFGMachinePayoffKernelGame_outcomeKernel_eq_fosg] at hfosg
  exact semantics.fosgMachinePayoffHistoryKernelGame_support_nativeHistory
    profile hfosg

end FrontierGameSemantics
end ToEventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Plain EFG serialization of a checked program's canonical frontier game. -/
noncomputable def frontierPlainEFG
    (program : WFProgram P L) [FiniteDomains program] :
    EFG.EFGGame :=
  program.frontierSemantics.plainEFG

/-- Payoff-facing EFG kernel game of a checked program's canonical frontier
game. -/
noncomputable def frontierPlainEFGMachinePayoffKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.plainEFGMachinePayoffKernelGame

/-- Translate FOSG behavioral profiles to behavioral profiles of the serialized
EFG. -/
noncomputable def frontierPlainEFGTranslateProfile
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierFOSGMachinePayoffHistoryKernelGame.Profile →
      program.frontierPlainEFGMachinePayoffKernelGame.Profile :=
  program.frontierSemantics.plainEFGTranslateProfile

/-- Program-facing EFG/FOSG utility-distribution equivalence. -/
theorem frontierPlainEFGMachinePayoffKernelGame_udist_eq_fosg
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.frontierFOSGMachinePayoffHistoryKernelGame.Profile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile profile) =
      program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        profile := by
  simpa [frontierPlainEFGMachinePayoffKernelGame,
    frontierPlainEFGTranslateProfile,
    frontierFOSGMachinePayoffHistoryKernelGame] using
    program.frontierSemantics
      |>.plainEFGMachinePayoffKernelGame_udist_eq_fosg profile

theorem frontierPlainEFGMachinePayoffKernelGame_outcomeKernel_eq_map_behavioralHistory
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.outcomeKernel
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      PMF.map
        (Machine.RoundView.ToFOSG.historyOfBoundedHistory
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0))
        ((program.frontierSemantics.behavioral.view).runDist
          program.frontierSemantics.horizon
          program.frontierSemantics.horizon profile) := by
  simpa [frontierPlainEFGMachinePayoffKernelGame,
    frontierPlainEFGTranslateProfile, BehavioralFrontierProfile] using
    program.frontierSemantics
      |>.plainEFGMachinePayoffKernelGame_outcomeKernel_eq_map_behavioralHistory
        profile

theorem frontierPlainEFGMachinePayoffKernelGame_udist_behavioralHistoryKernelGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      program.behavioralFrontierHistoryKernelGame.udist profile := by
  simpa [frontierPlainEFGMachinePayoffKernelGame,
    frontierPlainEFGTranslateProfile, BehavioralFrontierProfile,
    behavioralFrontierHistoryKernelGame] using
    program.frontierSemantics
      |>.plainEFGMachinePayoffKernelGame_udist_behavioralHistoryKernelGame
        profile

theorem frontierPlainEFGMachinePayoffKernelGame_udist_behavioralGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      program.behavioralFrontierGame.udist profile := by
  simpa [frontierPlainEFGMachinePayoffKernelGame,
    frontierPlainEFGTranslateProfile, BehavioralFrontierProfile,
    behavioralFrontierGame] using
    program.frontierSemantics
      |>.plainEFGMachinePayoffKernelGame_udist_behavioralGame profile

theorem frontierPlainEFGMachinePayoffKernelGame_udist_pureGame
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            ((program.frontierSemantics.behavioral.view).legalPureToBehavioral
              program.frontierSemantics.horizon profile)).extend) =
      program.pureFrontierGame.udist profile := by
  simpa [frontierPlainEFGMachinePayoffKernelGame,
    frontierPlainEFGTranslateProfile, PureFrontierProfile,
    pureFrontierGame] using
    program.frontierSemantics
      |>.plainEFGMachinePayoffKernelGame_udist_pureGame profile

theorem frontierPlainEFGMachinePayoffKernelGame_support_nativeHistory
    (program : WFProgram P L) [FiniteDomains program]
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
        nativeHistory.lastState.state := by
  simpa [frontierPlainEFGMachinePayoffKernelGame,
    frontierPlainEFGTranslateProfile, BehavioralFrontierProfile,
    BehavioralFrontierHistory] using
    program.frontierSemantics
      |>.plainEFGMachinePayoffKernelGame_support_nativeHistory
        profile hsupport

end WFProgram

end Vegas

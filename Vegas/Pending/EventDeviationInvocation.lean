/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventDeviationPotential
import Vegas.Pending.EventPolicyCoherence
import Vegas.Pending.EventPolicyService

/-! # Deviation-potential conservation across player invocations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Public message commands do not alter the event application state before
their packets are separately included. -/
theorem playerStep_nonprivate_deviationContinuation
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (focal who : Player) (execution : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (nonprivate : ∀ privateCommand, command ≠ .privateCommand privateCommand) :
    (runtime.application.playerStep who execution command).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  cases command with
  | privateCommand command => exact False.elim (nonprivate command rfl)
  | submit payload =>
      rw [runtime.application.playerStep_submit_eq, FinDist.pure_bind]
      rfl
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.PlayerCommand.toAction,
        MessageApplication.advance, FinDist.pure_bind]

/-- A private command whose first-write table is unchanged at every prescribed
opponent event preserves the focal-erased continuation. -/
theorem playerStep_private_deviationContinuation_of_remembered
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (focal who : Player) (execution : runtime.application.PolicyExecution)
    (command : PrivateCommand graph)
    (remembered : ∀ event, graph.actor? event ≠ some focal →
      (privateStep execution.native.application who command).remembered event =
        execution.native.application.remembered event) :
    (runtime.application.playerStep who execution (.privateCommand command)).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  rw [runtime.application.playerStep_private_eq, FinDist.pure_bind]
  apply State.deviationContinuation_congr _ _ profile focal
  · exact (privateStep_facts execution.native.application who command).1
  · intro event unfinished other
    exact remembered event other

/-- Preparation never changes remembered actions, and first-write remembering
is inert once the addressed action is already cached. -/
theorem playerStep_private_deviationContinuation_of_cached
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (focal who : Player) (execution : runtime.application.PolicyExecution)
    (command : PrivateCommand graph)
    (cached : ∀ event action, command = .remember event action →
      execution.native.application.remembered event ≠ none) :
    (runtime.application.playerStep who execution (.privateCommand command)).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  apply runtime.playerStep_private_deviationContinuation_of_remembered profile focal who
    execution command
  intro event other
  cases command with
  | prepare serial raw => rfl
  | remember query action =>
      have present := cached query action rfl
      cases remembered : execution.native.application.remembered query with
      | none => exact False.elim (present remembered)
      | some saved =>
          by_cases owned : graph.actor? query = some who
          · simp [privateStep, owned, remembered]
          · simp [privateStep, owned]

/-- An arbitrary focal-player invocation preserves the continuation after the
focal player's implementation state has been erased from the potential. -/
theorem focalPlayer_invoke_deviationContinuation
    (runtime : EventGraphRuntime graph) (profile : graph.BehavioralProfile)
    (focal : Player) (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution) :
    (runtime.application.invoke players environment execution (.player focal)).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  simp only [MessageApplication.invoke, FinDist.bind_bind]
  calc
    _ = (players focal (execution.principalHistory focal)
        (MessageApplication.State.observe runtime.application execution.native focal)).bind
          (fun _ => execution.native.application.deviationContinuation profile focal) := by
      apply FinDist.bind_congr
      intro command _
      exact runtime.playerStep_focal_deviationContinuation profile focal execution command
    _ = _ := FinDist.bind_const _ _

/-- An invocation of an unchanged opponent's compiled graph policy conserves
the continuation with the focal player's private cache erased. -/
theorem compiledOpponent_invoke_deviationContinuation
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (focal owner : Player)
    (other : owner ≠ focal)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution)
    (coherent : PolicyCoherentAll runtime execution owner)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy owner (profile owner)) :
    (runtime.application.invoke players environment execution (.player owner)).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  simp only [MessageApplication.invoke, ownerCompiled, FinDist.bind_bind]
  unfold compilePlayerPolicy
  cases grant :
      (MessageApplication.State.observe runtime.application execution.native
        owner).application.publicView.serviceGrant with
  | none =>
      rw [FinDist.pure_bind]
      exact runtime.playerStep_nonprivate_deviationContinuation profile focal owner execution
        .wait (by simp)
  | some event =>
      simp only
      split
      · rw [FinDist.pure_bind]
        exact runtime.playerStep_nonprivate_deviationContinuation profile focal owner execution
          .wait (by simp)
      · split
        · rename_i viewOwner
          split
          · rename_i readyView
            have ready : execution.native.application.config.cut.Ready event :=
              (State.publicView_eventReady _ _).mp readyView
            split
            · rename_i actor
              cases view : nodeView graph event with
              | sample payload law outputEq codeEq =>
                  rw [FinDist.pure_bind]
                  exact runtime.playerStep_nonprivate_deviationContinuation profile focal owner
                    execution .wait (by simp)
              | bind nodeOwner payload outputEq codeEq =>
                  simp only
                  cases stageEq : stagingCount (execution.principalHistory owner) event with
                  | zero =>
                      simp only [FinDist.bind_map]
                      change ((graph.normalizePolicy owner (profile owner) event actor
                        (graph.playerObserve owner execution.native.application.config)).bind
                          fun action =>
                            (runtime.application.playerStep owner execution
                              (.privateCommand (.remember event action))).bind fun next =>
                                next.native.application.deviationContinuation profile focal) = _
                      exact runtime.playerStep_opponent_remember_deviationContinuation ordered
                        profile focal owner other execution event ready actor
                        ((coherent event actor).empty_iff.mp stageEq)
                  | succ n =>
                      cases n with
                      | zero =>
                          obtain ⟨action, cached⟩ :=
                            (coherent event actor).cached_of_stage (by omega)
                          have viewCached :
                              (MessageApplication.State.observe runtime.application
                                execution.native owner).application.remembered event =
                                some action := by
                            change (State.playerView execution.native.application
                              owner).remembered event = some action
                            simpa [State.playerView, actor] using cached
                          rw [viewCached, FinDist.pure_bind]
                          unfold bindingStageCommand
                          generalize cast (congrArg EventField.Action outputEq) action = result
                          cases result with
                          | failure =>
                              apply runtime.playerStep_private_deviationContinuation_of_cached
                                profile focal owner execution (.remember event action)
                              intro query selected same
                              injection same with queryEq
                              subst query
                              simp [cached]
                          | success value =>
                              apply runtime.playerStep_private_deviationContinuation_of_cached
                                profile focal owner execution (.prepare event.val ⟨payload, value⟩)
                              intro query selected impossible
                              contradiction
                      | succ later =>
                          rw [FinDist.pure_bind]
                          exact runtime.playerStep_nonprivate_deviationContinuation profile focal
                            owner execution (.submit (.commitment event (owner, eventSlot event)))
                            (by simp)
              | resolve nodeOwner payload binding checks outputEq codeEq =>
                  simp only
                  cases stageEq : stagingCount (execution.principalHistory owner) event with
                  | zero =>
                      simp only [FinDist.bind_map]
                      change ((graph.normalizePolicy owner (profile owner) event actor
                        (graph.playerObserve owner execution.native.application.config)).bind
                          fun action =>
                            (runtime.application.playerStep owner execution
                              (.privateCommand (.remember event action))).bind fun next =>
                                next.native.application.deviationContinuation profile focal) = _
                      exact runtime.playerStep_opponent_remember_deviationContinuation ordered
                        profile focal owner other execution event ready actor
                        ((coherent event actor).empty_iff.mp stageEq)
                  | succ n =>
                      cases n with
                      | zero =>
                          obtain ⟨action, cached⟩ :=
                            (coherent event actor).cached_of_stage (by omega)
                          have viewCached :
                              (MessageApplication.State.observe runtime.application
                                execution.native owner).application.remembered event =
                                some action := by
                            change (State.playerView execution.native.application
                              owner).remembered event = some action
                            simpa [State.playerView, actor] using cached
                          rw [viewCached, FinDist.pure_bind]
                          apply runtime.playerStep_private_deviationContinuation_of_cached
                            profile focal owner execution (.remember event action)
                          intro query selected same
                          injection same with queryEq
                          subst query
                          simp [cached]
                      | succ later =>
                          cases memory :
                              (MessageApplication.State.observe runtime.application
                                execution.native owner).application.remembered event with
                          | none =>
                              rw [FinDist.pure_bind]
                              exact runtime.playerStep_nonprivate_deviationContinuation profile
                                focal owner execution (.submit (.withhold event)) (by simp)
                          | some action =>
                              rw [FinDist.pure_bind]
                              apply runtime.playerStep_nonprivate_deviationContinuation profile
                                focal owner execution
                                (runtime.resolutionSubmission owner event payload binding checks
                                  outputEq action
                                  (MessageApplication.State.observe runtime.application
                                    execution.native owner))
                              intro privateCommand
                              simp [resolutionSubmission]
            · rw [FinDist.pure_bind]
              exact runtime.playerStep_nonprivate_deviationContinuation profile focal owner
                execution .wait (by simp)
          · rw [FinDist.pure_bind]
            exact runtime.playerStep_nonprivate_deviationContinuation profile focal owner execution
              .wait (by simp)
        · rename_i notOwner
          exact False.elim (notOwner rfl)

end Vegas.EventGraphRuntime

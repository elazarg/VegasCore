/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventReplayEnvironment

/-! # Initialization of paired event-service executions

Equal endpoint observations identify only the focal player's visible initial
fields. Foreign initial candidate meanings remain unrelated.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A player's initial candidate catalogue is determined by its graph
observation, including failed initial bindings. -/
theorem State.initial_candidates_eq_of_observation (focal : Player)
    (left right : graph.Inputs)
    (observations : graph.playerObserve focal (Config.initial left) =
      graph.playerObserve focal (Config.initial right)) :
    (fun slot => (State.initial left).candidates.lookup (focal, slot)) =
      fun slot => (State.initial right).candidates.lookup (focal, slot) := by
  funext slot
  rw [State.initial_candidate, State.initial_candidate]
  cases slot with
  | prepared serial => rfl
  | initial input =>
      have inputsEqual (visible : (graph.inputLayout input).VisibleTo focal) :
          left input = right input := by
        have stored := store_eq_of_playerObserve_eq focal (Config.initial left)
          (Config.initial right) observations (.inl input) visible
        exact Option.some.inj stored
      have candidateCongr (kind : EventField Player L) (x y : kind.Value)
          (same : kind.VisibleTo focal → x = y) :
          State.candidateOfValue focal kind x = State.candidateOfValue focal kind y := by
        cases kind with
        | publicData payload | publication payload => rfl
        | binding owner payload =>
            by_cases owned : owner = focal
            · rw [same (by simp [EventField.VisibleTo, owned])]
            · simp only [State.candidateOfValue, if_neg owned]
      exact candidateCongr _ _ _ inputsEqual

/-- Initial application metadata and focal private candidates are determined
by the focal graph observation. -/
theorem NativeReplay.initial (runtime : EventGraphRuntime graph) (focal : Player)
    (left right : graph.Inputs)
    (observations : graph.playerObserve focal (Config.initial left) =
      graph.playerObserve focal (Config.initial right)) :
    NativeReplay runtime focal
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial left)))
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial right))) := by
  have publicObservation := publicObserve_eq_of_playerObserve_eq focal
    (Config.initial left) (Config.initial right) observations
  refine
    { publicView := ?_
      observation := observations
      remembered := rfl
      candidates := State.initial_candidates_eq_of_observation focal left right observations
      pool := rfl
      receipts := rfl
      focalHistory := rfl
      environmentHistory := rfl
      stagingCount_other := fun _ _ _ => rfl
      submittedAt_other := fun _ _ _ => rfl }
  change (State.initial left).publicView = (State.initial right).publicView
  unfold State.publicView
  congr 1

/-- Endpoint equality initializes replay across distinct private setup
draws. The endpoint is used only by this proof, never by a native policy. -/
theorem NativeReplay.initial_of_endpoint (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (event : graph.EventId) (left right : graph.Inputs)
    (leftEnd rightEnd : ServiceControl runtime)
    (leftPath : ServiceControlPath runtime roster reactionRounds players wire order
      { epochs := runtime.serviceEpochs, plan := []
        execution := MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial left)) }
      leftEnd)
    (rightPath : ServiceControlPath runtime roster reactionRounds players wire order
      { epochs := runtime.serviceEpochs, plan := []
        execution := MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial right)) }
      rightEnd)
    (endpoints : graph.normalizeObservation event focal
        (graph.playerObserve focal leftEnd.execution.native.application.config) =
      graph.normalizeObservation event focal
        (graph.playerObserve focal rightEnd.execution.native.application.config)) :
    NativeReplay runtime focal
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial left)))
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial right))) := by
  apply NativeReplay.initial runtime focal left right
  exact leftPath.playerObserve_eq_of_endpoint runtime roster reactionRounds players wire order
    focal event rightPath rfl endpoints

end Vegas.EventGraphRuntime

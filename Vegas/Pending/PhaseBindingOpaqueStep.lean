/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpaqueHandle
import Interaction.ReactiveRoundTrace

/-! # Literal same-command inclusion and histories for all-value phase shadows -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The joint physical channel outside one owner's private local state and
response word. Full networks and scheduler recall are retained. -/
def phaseExternalObservation (hidden : Player) (execution : (app).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall,
    execution.observeEnvironment app,
    fun who => if who = hidden then none else
      some (execution.recall who, execution.observe app who))

private theorem externalObservation_congr (left right : (app).Execution) (hidden : Player)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (application : left.application.publicView = right.application.publicView)
    (views : ∀ who, who ≠ hidden →
      left.application.playerView who = right.application.playerView who)
    (recalled : ∀ who, who ≠ hidden → left.recall who = right.recall who) :
    phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right := by
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application]
    rfl
  unfold phaseExternalObservation
  refine Prod.ext network (Prod.ext receipts (Prod.ext service (Prod.ext environment ?_)))
  funext who
  by_cases same : who = hidden
  · simp only [same, ite_true]
  · simp only [same, ite_false]
    apply congrArg some
    apply Prod.ext (recalled who same)
    change (⟨left.network.observe who, left.application.playerView who, left.receipts⟩ :
      (app).PlayerView) = ⟨_, _, _⟩
    rw [network, receipts, views who same]
    rfl

/-- The actual physical include operation has the same entire external
channel for an existing all-value shadow. No successful-store restriction or
target handler, acceptance or normalization equation is assumed. -/
theorem phase_include_opaque_external_congr (memory : BindingShadow graph) (hidden : Player)
    (owned : memory.OwnBindings hidden) (left right : (app).Execution)
    (application : left.application = memory.phased hidden right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (clear : right.application.current.excluded = ∅)
    (bindingPhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (id : MessageId Player) :
    phaseExternalObservation runtime leaks hidden (left.includePending app id) =
      phaseExternalObservation runtime leaks hidden (right.includePending app id) := by
  classical
  have publics : left.application.publicView = right.application.publicView := by
    rw [application]
    exact BindingShadow.phased_publicView owned _
  have beforeViews (who : Player) (different : who ≠ hidden) :
      left.application.playerView who = right.application.playerView who := by
    rw [application]
    exact BindingShadow.phased_playerView_other owned _ who different
  have fields := congrArg PhasePublicView.retired publics
  have opaqueLeft : ∀ phase ∈ left.application.phases.head?, phase.kind = .commitment := by
    simpa only [application, BindingShadow.phased] using bindingPhase
  have handling (message : Message Player (CommitAttemptPacket graph)) :=
    PhaseRuntimeState.handle_opaque_external_congr runtime left.application right.application
      hidden (by rw [application]; rfl) (by rw [application]; rfl) fields
      (by rw [application]; exact BindingShadow.native_publicView owned _)
      (by intro who different; rw [application];
          exact BindingShadow.native_playerView_other owned _ who different)
      (by rw [application]; exact clear) clear opaqueLeft message
  have pools : (left.network.includePending id).2 = (right.network.includePending id).2 :=
    congrArg (fun pool => (pool.includePending id).2) network
  cases found : left.network.lookup id with
  | none =>
      have otherFound : right.network.lookup id = none := network ▸ found
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, otherFound] using externalObservation_congr runtime leaks left right hidden
          network receipts service publics beforeViews recalled
  | some message =>
      have otherFound : right.network.lookup id = some message := network ▸ found
      have paired := handling message
      change ((app).handle left.application message).map _ =
        ((app).handle right.application message).map _ at paired
      have results :
          (((app).handle left.application message).getD left.application).publicView =
            (((app).handle right.application message).getD right.application).publicView ∧
          (∀ who, who ≠ hidden →
            (((app).handle left.application message).getD left.application).playerView who =
              (((app).handle right.application message).getD right.application).playerView who) ∧
          ((app).handle left.application message).isSome =
            ((app).handle right.application message).isSome := by
        cases first : (app).handle left.application message with
        | none =>
            cases second : (app).handle right.application message with
            | none => exact ⟨publics, beforeViews, rfl⟩
            | some next =>
                simp only [first, second, Option.map_none, Option.map_some] at paired
                cases paired
        | some firstNext =>
            cases second : (app).handle right.application message with
            | none =>
                simp only [first, second, Option.map_none, Option.map_some] at paired
                cases paired
            | some secondNext =>
                have same := Option.some.inj
                  (by simpa only [first, second, Option.map_some] using paired)
                refine ⟨congrArg Prod.fst same, ?_, rfl⟩
                intro who different
                have observed := congrFun (congrArg Prod.snd same) who
                simpa only [different, ite_false, Option.some.injEq, Option.getD_some]
                  using observed
      have updatedReceipts :
          left.receipts ++ [(id, ((app).handle left.application message).isSome)] =
          right.receipts ++ [(id, ((app).handle right.application message).isSome)] := by
        rw [receipts, results.2.2]
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, otherFound] using externalObservation_congr runtime leaks
          ({left with
            application := ((app).handle left.application message).getD left.application
            network := (left.network.includePending id).2
            receipts := left.receipts ++ [(id, ((app).handle left.application message).isSome)]})
          ({right with
            application := ((app).handle right.application message).getD right.application
            network := (right.network.includePending id).2
            receipts := right.receipts ++ [(id, ((app).handle right.application message).isSome)]})
          hidden pools updatedReceipts service results.1 results.2.1 recalled

/-- The same supported scheduler command constructs both genuine successor
histories and the exact joint conditional observation law. Prior image legality
is the induction invariant; no target successor or kernel equation is assumed. -/
theorem phase_opaque_include_trace (memory : BindingShadow graph) (hidden : Player)
    (owned : memory.OwnBindings hidden) (left right : (app).Execution)
    (application : left.application = memory.phased hidden right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ hidden → left.recall who = right.recall who)
    (clear : right.application.current.excluded = ∅)
    (bindingPhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (menu : (app).ResponseMenu) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat)
    (firstTrace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, left⟩))
    (secondTrace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, right⟩))
    (id : MessageId Player)
    (selected : (ReactiveApplication.Command.include id) ∈
      (scheduler left.environmentRecall (left.observeEnvironment app)).support) :
    let firstNext := {left.includePending app id with environmentRecall :=
      left.environmentRecall ++ [⟨left.observeEnvironment app, .include id⟩]}
    let secondNext := {right.includePending app id with environmentRecall :=
      right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩]}
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, firstNext⟩)) ∧
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, secondNext⟩)) ∧
    ((left.environmentStep app (.include id)).map
      (phaseExternalObservation runtime leaks hidden)) =
      ((right.environmentStep app (.include id)).map
        (phaseExternalObservation runtime leaks hidden)) := by
  classical
  intro firstNext secondNext
  have before := externalObservation_congr runtime leaks left right hidden network receipts service
    (by rw [application]; exact BindingShadow.phased_publicView owned _)
    (by intro who different; rw [application];
        exact BindingShadow.phased_playerView_other owned _ who different) recalled
  have environment : left.observeEnvironment app = right.observeEnvironment app :=
    congrArg (fun data => data.2.2.2.1) before
  have chosen : (ReactiveApplication.Command.include id) ∈
      (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
    rw [← service, ← environment]
    exact selected
  have firstMoved : firstNext ∈ (left.environmentStep app (.include id)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff, firstNext]
  have secondMoved : secondNext ∈ (right.environmentStep app (.include id)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff, secondNext]
  refine ⟨menu.trace_environment initial horizon scheduler remaining left firstNext (.include id)
    firstTrace selected firstMoved,
    menu.trace_environment initial horizon scheduler remaining right secondNext (.include id)
      secondTrace chosen secondMoved, ?_⟩
  have included := phase_include_opaque_external_congr runtime leaks memory hidden owned left right
    application network receipts service recalled clear bindingPhase id
  have logs : left.environmentRecall ++ [⟨left.observeEnvironment app,
      (ReactiveApplication.Command.include id)⟩] =
      right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩] := by
    rw [service, environment]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  apply congrArg PMF.pure
  change phaseExternalObservation runtime leaks hidden firstNext =
    phaseExternalObservation runtime leaks hidden secondNext
  have replaced := congrArg (fun data =>
    (data.1, data.2.1, left.environmentRecall ++ [⟨left.observeEnvironment app,
      (ReactiveApplication.Command.include id)⟩], data.2.2.2.1, data.2.2.2.2)) included
  rw [logs] at replaced
  dsimp only [phaseExternalObservation, firstNext, secondNext]
  rw [logs]
  simpa only [phaseExternalObservation, ReactiveApplication.Execution.observeEnvironment,
    ReactiveApplication.Execution.observe] using replaced

end Vegas.EventGraphRuntime

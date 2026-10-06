/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOwnerWindow
import Vegas.Pending.ReactiveOpeningLikelihood

/-! # The owner's information through its own complete service phase

The owner of an event may follow any policy during the event's roster, while
every other player is silent. The protected inclusion then includes the
owner's latest packet for the event, if any, and the deadline settles the
event. Two executions with equal owner traffic have equal owner traffic laws
at the end of the phase: every included packet is the owner's own, so its
handling is read from the owner's view.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The protected inclusion of the owner's latest packet preserves equal
owner traffic. -/
theorem bindingTraffic_includeLatest_owner (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (owner : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks owner left = runtime.bindingTraffic leaks owner right) :
    (runtime.interactionStep leaks players network (.includeLatest event owner) left).map
        (runtime.bindingTraffic leaks owner) =
      (runtime.interactionStep leaks players network (.includeLatest event owner) right).map
        (runtime.bindingTraffic leaks owner) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall owner = right.recall owner :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView owner = right.application.playerView owner :=
    congrArg (fun value => value.2.2.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have environment : left.observeEnvironment (runtime.reactiveApplication leaks) =
      right.observeEnvironment (runtime.reactiveApplication leaks) := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  have waiting : (runtime.reactiveApplication leaks).resume players none = PMF.pure := rfl
  have command : runtime.reactiveLatest leaks event owner
        (right.observeEnvironment (runtime.reactiveApplication leaks)) =
        .wait ∨
      ∃ message ∈ right.network.pending, message.sender = owner ∧
        runtime.reactiveLatest leaks event owner
          (right.observeEnvironment (runtime.reactiveApplication leaks)) =
          ReactiveApplication.Command.include message.id := by
    unfold reactiveLatest
    split
    · exact Or.inl rfl
    · rename_i message found
      right
      have holds := List.find?_some found
      have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
      simp only [decide_eq_true_eq] at holds
      exact ⟨message, member, holds.1, rfl⟩
  simp only [interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch, environment]
  rcases command with wait | ⟨message, _, sender, chosen⟩
  · rw [wait]
    simp only [ReactiveApplication.Execution.environmentStep, ReactiveApplication.Command.actor?,
      waiting, PMF.pure_map, PMF.bind_pure]
    rw [environment]
    apply congrArg PMF.pure
    dsimp only [bindingTraffic]
    rw [networks, receipts, environments, recalled, views, publics]
  · rw [chosen]
    simp only [ReactiveApplication.Execution.environmentStep, ReactiveApplication.Command.actor?,
      waiting, PMF.pure_map, PMF.bind_pure]
    have included : runtime.bindingTraffic leaks owner
          (left.includePending (runtime.reactiveApplication leaks) message.id) =
        runtime.bindingTraffic leaks owner
          (right.includePending (runtime.reactiveApplication leaks) message.id) := by
      cases found : left.network.lookup message.id with
      | none =>
          have rightFound : right.network.lookup message.id = none := networks ▸ found
          simp only [bindingTraffic, ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found, rightFound]
          exact Prod.ext (by rw [networks]) (Prod.ext receipts
            (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
      | some envelope =>
          have identity : envelope.id = message.id := by
            have holds := List.find?_some found
            simpa only [decide_eq_true_eq] using holds
          have author : envelope.id.1 = owner := by
            rw [identity]
            exact sender
          apply bindingTraffic_include_of_handler runtime leaks left right owner same
            message.id envelope found
          simp only [reactiveApplication_handle]
          split
          · exact handle_playerView_congr_of_sender runtime left.application right.application
              owner ⟨envelope.id, envelope.payload.call⟩ views author
          · rfl
    rw [environment]
    apply congrArg PMF.pure
    dsimp only [bindingTraffic] at included ⊢
    rw [environments]
    exact congrArg (fun read => (read.1, read.2.1,
      right.environmentRecall ++ [⟨right.observeEnvironment (runtime.reactiveApplication leaks),
        ReactiveApplication.Command.include message.id⟩],
        read.2.2.2)) included

/-- **The owner's complete phase.** With every other player silent, any owner
policy over the roster, the protected inclusion of its latest packet and the
deadline settlement give equal owner traffic laws from equal owner traffic. -/
theorem owner_phase_focal_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (owner : Player)
    (policy : (runtime.reactiveApplication leaks).Policy) (event : graph.EventId) (ticks : Nat)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (same : runtime.bindingTraffic leaks owner left = runtime.bindingTraffic leaks owner right) :
    let players := Function.update (fun _ => (runtime.reactiveApplication leaks).silentPolicy)
      owner policy
    let phase := roster.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    (runtime.runInteractionPlan leaks players network phase left).map
        (runtime.bindingTraffic leaks owner) =
      (runtime.runInteractionPlan leaks players network phase right).map
        (runtime.bindingTraffic leaks owner) := by
  intro players phase
  have windows := runtime.owner_window_focal_law leaks network roster owner policy left right
    leftRecall rightRecall same
  dsimp only [phase]
  rw [runInteractionPlan_append, runInteractionPlan_append, PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ windows
  intro before _ after _ equal
  simp only [List.cons_append, runInteractionPlan, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _
    (runtime.bindingTraffic_includeLatest_owner leaks players network event owner before after
      equal)
  intro included _ other _ matched
  exact runtime.settlement_focal_law leaks players network event ticks included other owner
    matched

end Vegas.EventGraphRuntime

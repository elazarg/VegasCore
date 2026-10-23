/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingResponseWitness
import Interaction.ReactiveRecordedResponse
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseOpeningMenuShape

/-! # Owned emission prefixes in an actual surviving attempt

Same-attempt semantic persistence supplies order without clearing inherited
exclusions. Remembered raw submission material is retained literally.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Retained ready callbacks of the same owner respect source rank inside
their actual attempt, even if other players have already been excluded. -/
theorem phase_ready_owner_rank_le_of_same_attempt_prefix
    (ordered : graph.RevealRelaxedOrdered) (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior trace) (nativeOrdered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt)
    (owner : Player) (first second : graph.EventId)
    (firstActor : graph.actor? first = some owner)
    (secondActor : graph.actor? second = some owner)
    (firstReady : before.execution.application.current.native.config.cut.Ready first)
    (secondReady : after.execution.application.current.native.config.cut.Ready second) :
    first.val ≤ second.val := by
  have extension := phase_prefix_semantic_extension runtime leaks menu initial horizon scheduler
    before after prior trace kept nativeOrdered same
  have visible := ordered.ready_visible_iff before.execution.application.current.native.config.cut
    firstReady firstActor (EventCode.output_visible_of_actor (graph.nodes second) owner secondActor)
      (IndependentReveals.not_of_actor_eq (by rw [secondActor, firstActor]))
      (IndependentReveals.not_of_actor_eq (by rw [secondActor, firstActor]))
  by_contra reversed
  have completed := visible.mpr (show second.val < first.val by omega)
  have remembered :=
    (before.execution.application.current.native.config.history_exact second).mpr completed
  obtain ⟨entry, member, named⟩ := List.mem_map.mp remembered
  apply secondReady.1
  apply (after.execution.application.current.native.config.history_exact second).mp
  exact List.mem_map.mpr ⟨entry, extension.2.subset member, named⟩

section Counted

variable [Fintype Player] (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A literal remembered binding SEND has a genuine owned ready callback,
without imposing an empty excluded set on the remembered or final state. -/
theorem phase_recorded_binding_request
    (ordered : graph.RevealRelaxedOrdered) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (event : graph.EventId) (candidate : Handle graph)
    (named : material.call.packet = .commitment event candidate) :
    ∃ (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = some owner ∧
        entry.beforeView = before.execution.observe app owner ∧
        before.execution.application.SeedRequest owner
          ⟨before.execution.application.attempt, event⟩ := by
  obtain ⟨before, prior, retained, acting, viewed, offered, _suffix⟩ :=
    (menu).recorded_response_prefix initial horizon scheduler control trace owner entry recorded
  have action : entry.action = (⟨some material⟩ : (app).Action) := by
    cases selected : entry.action with
    | mk transmission =>
        rw [selected] at transmitted
        exact congrArg ReactiveApplication.Action.mk transmitted
  have offeredMaterial : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (before.execution.recall owner)
        (before.execution.observe app owner) := by rwa [action] at offered
  rcases before with ⟨remaining, actor, execution⟩
  cases acting
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler remaining owner execution prior material offeredMaterial
  have eventName := PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
    horizon scheduler remaining owner execution prior coordinate request material offeredMaterial
  rw [named] at eventName
  change some event = some coordinate.event at eventName
  have eventEq : event = coordinate.event := Option.some.inj eventName
  have coordinateEq : coordinate = ⟨execution.application.attempt, event⟩ := by
    cases coordinate with
    | mk attempt selected =>
        congr 1
        · exact request.1
        · exact eventEq.symm
  exact ⟨⟨remaining, some owner, execution⟩, prior, retained, rfl, viewed,
    coordinateEq ▸ request⟩

/-- Every literal earlier SEND in the current namespace lies strictly before
a genuinely unsent owned request. This proves the absence of a locked focal
descendant without assuming an empty permanent excluded set. -/
theorem phase_recorded_binding_rank_lt_of_unsent_request
    (ordered : graph.RevealRelaxedOrdered) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (entry : (app).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (event : graph.EventId) (candidate : Handle graph)
    (named : material.call.packet = .commitment event candidate)
    (sameAttempt : entry.beforeView.application.2.attempt = control.execution.application.attempt)
    (selected : graph.EventId)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩) :
    event.val < selected.val := by
  obtain ⟨before, prior, kept, _acting, viewed, previousRequest⟩ :=
    phase_recorded_binding_request runtime leaks bounds plan inputs horizon ordered scheduler
      trace owner entry recorded material transmitted event candidate named
  have same : before.execution.application.attempt = control.execution.application.attempt := by
    rw [viewed] at sameAttempt
    exact sameAttempt
  have beforeRaw := (menu).toRawTrace initial horizon scheduler prior
  have beforeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler (by
      intro state member
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_ordered plan draw) beforeRaw
  have lower := phase_ready_owner_rank_le_of_same_attempt_prefix runtime leaks ordered menu initial
    horizon scheduler before control prior trace kept beforeOrdered same owner event selected
      previousRequest.2.2.2.1 request.2.2.2.1 previousRequest.2.2.1 request.2.2.1
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨message, emitted, _sender, packet⟩ := PhaseCount.recalled_submission_emitted runtime leaks
    initial horizon scheduler raw owner entry recorded material transmitted
  have ownOutput : message ∈ (app).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
  have emittedAttempt := phase_recalled_emission_attempt runtime leaks initial horizon scheduler
    raw owner entry recorded message emitted
  have attempt : message.payload.attempt = control.execution.application.attempt := by
    rw [viewed] at emittedAttempt
    exact emittedAttempt.trans same
  have different : event ≠ selected := by
    intro equal
    apply unsent message ownOutput
    simp only [PhaseCount.event?, packet, named, equal, Payload.event?, Option.map_some, attempt]
  have unequal : event.val ≠ selected.val := fun equal => different (Fin.ext equal)
  omega

end Counted

end Vegas.EventGraphRuntime

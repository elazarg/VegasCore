/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingSilence
import Vegas.Pending.PhaseProposalLostRecallReplay
import Vegas.Pending.PhaseBindingMemoryCallback

/-! # Reference-factor cancellation after a lost preparation

The sender has no unsent current request before its original closing omission.
Actual image input recall reconstructs the same old wire packet even though
the sender's private inert evidence alias is allowed to differ.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- Every legal behavioral policy assigns mass one to the unique WAIT response. -/
theorem phase_singleton_wait_atom
    (initialLaw : PMF (app).State) (scheduler : (app).Scheduler) (owner : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (singleton : PhaseCount.onePacketActions runtime leaks bounds owner past view = {⟨none⟩})
    (policy : ((menu).information initialLaw horizon scheduler).BehavioralPolicy owner) :
    (((policy (some (past, view))).map Subtype.val) (some (⟨none⟩ : (app).Action))).toReal = 1 := by
  classical
  let model := (menu).information initialLaw horizon scheduler
  have singletonMenu : (menu).actions owner past view = {⟨none⟩} := singleton
  let wait : model.Choice owner (some (past, view)) :=
    ⟨some ⟨none⟩, ⟨⟨none⟩, by rw [singletonMenu]; exact Finset.mem_singleton_self _, rfl⟩⟩
  have unique (choice : model.Choice owner (some (past, view))) : choice = wait := by
    apply Subtype.ext
    obtain ⟨response, offered, equal⟩ := choice.2
    rw [singletonMenu] at offered
    exact equal.trans (congrArg some (Finset.mem_singleton.mp offered))
  let : Subsingleton (model.Choice owner (some (past, view))) :=
    ⟨fun left right => (unique left).trans (unique right).symm⟩
  rw [eq_pure_of_subsingleton (policy (some (past, view))) wait, PMF.pure_map]
  change ((PMF.pure (some (⟨none⟩ : (app).Action))) (some ⟨none⟩)).toReal = 1
  rw [PMF.pure_apply_self, ENNReal.toReal_one]

/-- Original owner order and the real closing omission rule out an unsent
request, without using the availability of a particular target response. -/
theorem phase_lost_binding_no_unsent_before_close
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (prior : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (closing : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (retained : TracePrefix prior trace)
    (same : execution.application.attempt = closing.execution.application.attempt)
    (after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after current)
    (phase : RuntimePhase graph) (installed : closing.execution.application.phases.head? = some
      phase)
    (kind : phase.kind = .commitment) (omitted : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout omitted = .binding owner payload)
    (inside : omitted ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr omitted) = none)
    (entry : (app).PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (material : WitnessedSubmission graph) (transmitted : entry.action.transmission = some material)
    (candidate : Handle graph) (named : material.call.packet = .commitment omitted candidate)
    (sameEntry : entry.beforeView.application.2.attempt = execution.application.attempt) :
    ¬∃ coordinate, execution.application.SeedRequest owner coordinate ∧
      ∀ message ∈ (app).outputs (execution.recall owner),
        PhaseCount.event? message.payload ≠ some coordinate := by
  rintro ⟨coordinate, request, unsent⟩
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have nativeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler prior)
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler ⟨remaining, some owner, execution⟩ closing prior trace retained nativeOrdered same
  have phases : execution.application.phases = closing.execution.application.phases :=
    congrArg Prod.fst metadata
  have currentInstalled : execution.application.phases.head? = some phase := by
    rw [phases]
    exact installed
  obtain ⟨actualPhase, head, member⟩ := request.2.1
  have phaseEq : actualPhase = phase := Option.some.inj
    ((Option.mem_def.mp head).symm.trans currentInstalled)
  subst actualPhase
  obtain ⟨lower, upper⟩ := (phase.mem_events coordinate.event).mp member
  have field := phase.fields coordinate.event lower upper
  rw [kind] at field
  obtain ⟨actor, ty, eventBinding⟩ := field
  have actorEq : actor = owner := Option.some.inj
    ((actor?_of_outputLayout_binding graph eventBinding).symm.trans request.2.2.2.1)
  subst actor
  have coordinateEq : coordinate = ⟨execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
        congr 1
        exact request.1
  rw [coordinateEq] at request unsent
  have later := phase_recorded_binding_rank_lt_of_unsent_request runtime leaks bounds plan inputs
    horizon ordered scheduler prior owner entry recorded material transmitted omitted candidate
      named sameEntry coordinate.event request unsent
  exact (phase_closing_unaccepted_no_later_owned_request runtime leaks bounds plan inputs horizon
    scheduler ordered ⟨remaining, some owner, execution⟩ closing prior trace retained same after
      current effect phase currentInstalled owner omitted coordinate.event payload ty binding
        eventBinding inside unaccepted request) later

/-- Actual input recall, not the erased private recall alone, transports
the sender's already-sent condition to its genuine counterpart callback. -/
theorem phase_lost_binding_image_wait
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (remaining : Nat) (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (original image : (app).Execution)
    (prior : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, original⟩))
    (imageTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, image⟩))
    (paired : image.eraseRecall app owner =
      ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution original).eraseRecall
        app owner)
    (noUnsent : ¬∃ coordinate, original.application.SeedRequest owner coordinate ∧
      ∀ message ∈ (app).outputs (original.recall owner),
        PhaseCount.event? message.payload ≠ some coordinate) :
    PhaseCount.onePacketActions runtime leaks bounds owner (image.recall owner)
      (image.observe app owner) = {⟨none⟩} := by
  have sourceRecall := (app).history_inputRecall initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler prior)
  have targetRecall := (app).history_inputRecall initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler imageTrace)
  have network : image.network = original.network := by
    have retained := congrArg (fun execution : (app).Execution => execution.network) paired
    exact retained
  have outputs : (app).outputs (image.recall owner) =
      (app).outputs (original.recall owner) := by
    rw [← targetRecall owner, ← sourceRecall owner, network]
  apply PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds plan ordered
    inputs horizon scheduler remaining owner image imageTrace
  rintro ⟨coordinate, request, unsent⟩
  apply noUnsent
  refine ⟨coordinate, ?_, ?_⟩
  · have application := congrArg (fun execution : (app).Execution => execution.application) paired
    change image.application =
      original.application.swap (HiddenSwap.preparationOnly (owner, slot) first second)
        at application
    rw [application] at request
    exact request
  · rwa [outputs] at unsent

end Vegas.EventGraphRuntime

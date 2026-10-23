/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalObservation
import Vegas.Source.ProposalRecoveryObservation

/-! # Typed source proposals computed from physical submitted openings

Physical coordinates use the same phase, generation and absolute event rank as
the source recovery address. Only openings whose wire tag matches a publication
field become source proposals. Receipt status and guard acceptance are not
consulted. The result is a canonical finite set, not the physical packet order.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A physical coordinate's semantic source address has no packet identifier. -/
def sourceAddress (coordinate : CommitAttemptEvent graph) : ProposalRecoveryAddress :=
  ⟨coordinate.attempt.phase, coordinate.attempt.generation, coordinate.event.val⟩

omit [DecidableEq Player] in
theorem sourceAddress_injective : Function.Injective (sourceAddress (graph := graph)) := by
  rintro ⟨⟨firstPhase, firstGeneration⟩, firstEvent⟩
    ⟨⟨secondPhase, secondGeneration⟩, secondEvent⟩ same
  have phase : firstPhase = secondPhase := congrArg ProposalRecoveryAddress.phase same
  have generation : firstGeneration = secondGeneration :=
    congrArg ProposalRecoveryAddress.generation same
  have event : firstEvent = secondEvent :=
    Fin.ext (congrArg ProposalRecoveryAddress.event same)
  cases phase
  cases generation
  cases event
  rfl

/-- Read a typed source proposal from an actual publication-field opening. -/
def sourceProposal? (proposal : Proposal graph) : Option (ProposalRecoveryProposal L) :=
  match graph.outputLayout proposal.1.event with
  | .publication payload => (proposal.2.as? payload).map fun value =>
      ⟨sourceAddress proposal.1, payload, value⟩
  | .binding .. | .privateInput .. | .publicData .. => none

omit [DecidableEq Player] in
theorem sourceProposal?_publication (coordinate : CommitAttemptEvent graph)
    (payload : L.Ty) (publication : graph.outputLayout coordinate.event = .publication payload)
    (value : L.Val payload) :
    sourceProposal? (coordinate, ⟨payload, value⟩) =
      some ⟨sourceAddress coordinate, payload, value⟩ := by
  simp only [sourceProposal?, publication, Raw.as?_mk, Option.map_some]

omit [DecidableEq Player] in
theorem sourceProposal?_address (proposal : Proposal graph)
    (typed : ProposalRecoveryProposal L) (decoded : sourceProposal? proposal = some typed) :
    typed.address = sourceAddress proposal.1 := by
  unfold sourceProposal? at decoded
  split at decoded
  · obtain ⟨value, _, equal⟩ := Option.map_eq_some_iff.mp decoded
    exact congrArg ProposalRecoveryProposal.address equal.symm
  all_goals cases decoded

/-- The canonical typed archive of submitted publication proposals. -/
def sourceArchive (messages : List (Message Player (CommitAttemptPacket graph))) :
    Finset (ProposalRecoveryProposal L) :=
  (archive messages).biUnion fun proposal => (sourceProposal? proposal).toFinset

theorem mem_sourceArchive (messages : List (Message Player (CommitAttemptPacket graph)))
    (typed : ProposalRecoveryProposal L) :
    typed ∈ sourceArchive messages ↔
      ∃ proposal ∈ archive messages, sourceProposal? proposal = some typed := by
  simp only [sourceArchive, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]

theorem sourceArchive_congr
    (first second : List (Message Player (CommitAttemptPacket graph)))
    (same : ∀ message, message ∈ first ↔ message ∈ second) :
    sourceArchive first = sourceArchive second := by
  unfold sourceArchive
  rw [archive_congr first second same]

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The source archive is computed from literal local recall and observation. -/
def observedSourceArchive (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    Finset (ProposalRecoveryProposal L) :=
  sourceArchive (ReactiveApplication.ResponseMenu.knownPackets past view)

/-- Complete observation reconstructs all typed source proposals, including
negative-receipt openings and openings whose application guards failed. -/
theorem observedSourceArchive_eq_submitted
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who) :
    observedSourceArchive runtime leaks (control.execution.recall who)
        (control.execution.observe (app) who) =
      sourceArchive control.execution.network.inputs := by
  exact sourceArchive_congr _ _ (mem_knownPackets_iff_submitted runtime leaks complete
    initial horizon scheduler control trace who active)

/-- Typed proposal extraction is constant on an actual complete-input fiber. -/
theorem sourceArchive_eq_of_completeInput
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat)
    (leftScheduler rightScheduler : (app).Scheduler) (left right : (app).Control)
    (leftTrace : ((app).protocol initial horizon leftScheduler).Trace (some left))
    (rightTrace : ((app).protocol initial horizon rightScheduler).Trace (some right))
    (who : Player) (leftActive : left.actor = some who) (rightActive : right.actor = some who)
    (recalled : left.execution.recall who = right.execution.recall who)
    (observed : left.execution.observe (app) who = right.execution.observe (app) who) :
    sourceArchive left.execution.network.inputs = sourceArchive right.execution.network.inputs := by
  exact sourceArchive_congr _ _ ((app).complete_decision_inputs_congr complete initial horizon
    leftScheduler rightScheduler left right leftTrace rightTrace who leftActive rightActive
      recalled observed)

/-- Expiry, rejection and phase retirement leave the submitted typed archive
unchanged, even when the current semantic source checkpoint changes. -/
theorem sourceArchive_environmentStep (execution next : (app).Execution) (command : (app).Command)
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    sourceArchive next.network.inputs = sourceArchive execution.network.inputs := by
  rw [(app).environmentStep_inputs execution next command reached]

end Vegas.EventGraphRuntime.PhaseProposal

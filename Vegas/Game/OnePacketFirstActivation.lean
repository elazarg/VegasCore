/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCanonicalAcceptance
import Vegas.Game.SourceServiceFirstTurnOpportunity
import Vegas.Pending.ReactiveOwnerOpportunity

/-! # Sending at the first activation succeeds surely

A response appends one entry to its author's recall
(`Vegas.respondEntry`), and every later transition keeps that entry in place
(`Vegas.recordsEntry_transition`): at every later history the author's recall
splits around it (`Vegas.RecordsEntry`).

Under the asynchronous contract and the timeliness margin, the owner's first
activation for an event comes within the reaction delay of the event's
activation, so a packet sent then is included before the deadline whenever its
inclusion takes at most the inclusion bound
(`Vegas.firstActivation_inclusionFits`). The canonical decision sent at the
first activation is therefore a fresh call, and at every later history of the
one-packet game, under any responses of everyone and any scheduler, it has an
accepting receipt once the bound has passed and whenever the event has
completed (`Vegas.firstActivation_canonical_settles`). Under terminal play
from any history recording it, the event completes and the packet is accepted
on every terminal history: sending at the first activation fails with
probability zero (`Vegas.firstActivation_canonical_accepted`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- The envelope a response transmitting `material` emits. -/
def sentEnvelope (execution : (application setup leaks).Execution) (who : Player)
    (material : (application setup leaks).Submission) :
    Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, execution.network.nextSerial who),
    (application setup leaks).packet
      ((application setup leaks).submit execution.application who material) who
      (execution.network.known who) material⟩

variable (setup leaks) in
/-- The recall entry a response appends: the view it was made from, the
response, and the envelope it emits. -/
def respondEntry (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) : (application setup leaks).PlayerEntry :=
  ⟨execution.observe (application setup leaks) who, response,
    response.transmission.map (sentEnvelope setup leaks execution who)⟩

variable (setup leaks) in
/-- The recall of `who` at the protocol state splits around `entry`. -/
def RecordsEntry (who : Player) (entry : (application setup leaks).PlayerEntry) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ earlier later, control.execution.recall who = earlier ++ entry :: later

/-- A response records its own entry. -/
theorem recordsEntry_respond (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) (remaining : Nat)
    (actor : Option Player) :
    RecordsEntry setup leaks who (respondEntry setup leaks execution who response)
      (some ⟨remaining, actor, execution.respond (application setup leaks) who response⟩) := by
  refine ⟨execution.recall who, [], ?_⟩
  rw [respond_recall, ite_eq_left rfl]
  rfl

/-- **Recorded entries stay recorded.** Every protocol transition, under
arbitrary responses and scheduler choices, keeps a recorded entry in place. -/
theorem recordsEntry_transition (who : Player) (entry : (application setup leaks).PlayerEntry)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (holds : RecordsEntry setup leaks who entry before)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler before
      joint).support) :
    RecordsEntry setup leaks who entry after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨earlier, later, split⟩ := holds
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some responder =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          change ∃ earlier later, (execution.respond (application setup leaks) responder
            ((joint responder).getD ⟨none⟩)).recall who = earlier ++ entry :: later
          rw [respond_recall]
          split
          · rename_i same
            subst same
            change execution.recall who = _ at split
            rw [split]
            exact ⟨earlier, _, List.append_assoc _ _ _⟩
          · exact ⟨earlier, later, split⟩
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact ⟨earlier, later, split⟩
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              refine ⟨earlier, later, ?_⟩
              change next.recall who = _
              rw [(application setup leaks).environmentStep_recall execution next command
                supported]
              exact split

/-- A decision state is reached from an idle state by activating its actor,
which changes neither the application state nor any recall. -/
theorem decision_predecessor {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {state : (application setup leaks).ProtocolState}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      state)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : state = some ⟨remaining, some who, execution⟩) :
    ∃ previous : (application setup leaks).Execution,
      Nonempty (((application setup leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some ⟨remaining + 1, none, previous⟩)) ∧
      previous.application = execution.application ∧ previous.recall = execution.recall := by
  match state, trace, current with
  | _, .start, current => cases current
  | _, .extend (source := before) prior joint _ realized, current =>
      subst current
      cases before with
      | none =>
          obtain ⟨_, _, same⟩ := PMF.support_map .. ▸ realized
          cases same
      | some control =>
          rcases control with ⟨priorRemaining, actor, priorExecution⟩
          cases actor with
          | some responder => cases (PMF.mem_support_pure_iff _ _).mp realized
          | none =>
              cases priorRemaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp realized
              | succ priorRemaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                  obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
                  cases command with
                  | activate activated =>
                      cases same
                      obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
                      exact ⟨priorExecution, ⟨prior⟩, rfl, rfl⟩
                  | «include» id => cases same
                  | wait => cases same
                  | application command => cases same

/-- **The first activation fits.** Under the asynchronous contract and the
timeliness margin, at a decision of `who` at its turn `event` such that `event`
was its turn at none of its recalled views, a packet included within
`bound event` slots is included before the deadline. -/
theorem firstActivation_inclusionFits {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {state : (application setup leaks).ProtocolState}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      state)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : state = some ⟨remaining, some who, execution⟩) (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry) :
    execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  obtain ⟨previous, ⟨previousTrace⟩, application, recallEq⟩ := decision_predecessor trace current
  have spec := PublicView.ownTurn?_spec _ who event turn
  have ready := (execution.application.publicView_eventReady event).mp spec.1
  have strategic : ((graph setup).actor? event).isSome = true := by rw [spec.2]; rfl
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler
    previousTrace).1
  rw [application] at invariant
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
    strategic
  apply PublicView.inclusionFitsDeadline_of_response_delay (runtime setup) delay bound timely _
    event entered strategic activated
  by_contra late
  push Not at late
  have since := contract.opportunity ⟨remaining + 1, none, previous⟩ previousTrace event who
    entered spec.2 (by rw [application]; exact spec.1) (by rw [application]; exact activated)
    (by rw [application]; exact late)
  obtain ⟨before, _, _, response, member, viewed, beforeTurn, _⟩ :=
    (runtime setup).owner_response_within_delay leaks (initialLaw setup) horizon scheduler delay
      contract.opportunity (serviceGraph_revealRelaxedOrdered setup .sequential)
      ⟨remaining + 1, none, previous⟩ previousTrace rfl event who entered spec.2 since
  apply never response (recallEq ▸ member)
  change response.beforeView.application.publicView.ownTurn? who = some event
  rw [viewed]
  exact beforeTurn

section OnePacket

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [Fintype Player] in
/-- The entry of a transmitting response records its envelope. -/
theorem respondEntry_of_transmission (execution : (application setup leaks).Execution)
    (who : Player) (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) :
    respondEntry setup leaks execution who response =
      ⟨execution.observe (application setup leaks) who, response,
        some (sentEnvelope setup leaks execution who material)⟩ := by
  unfold respondEntry
  rw [submits]
  rfl

/-- **The canonical packet sent at the first activation settles.** Under the
asynchronous contract and the timeliness margin, let `who` send the canonical
decision at its first activation for `event`, at a history of the one-packet
game. At every later history of the one-packet game recording that response,
under any responses of everyone and any scheduler, the packet has an accepting
receipt once the inclusion bound has passed since it was sent, and whenever the
event has completed. -/
theorem firstActivation_canonical_settles {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    {control : (application setup leaks).Control}
    (later : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (records : RecordsEntry setup leaks who (respondEntry setup leaks execution who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)) (some control)) :
    (execution.application.publicView.clock + bound event < control.execution.application.clock →
      ((sentEnvelope setup leaks execution who material).id, true) ∈
        control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        ((sentEnvelope setup leaks execution who material).id, true) ∈
          control.execution.receipts) := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have fits := firstActivation_inclusionFits contract timely rawTrace rfl event turn never
  have call := canonical_freshCall (control := ⟨remaining, some who, execution⟩) rawTrace bound
    who event turn fits action material submits
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  obtain ⟨earlier, rest, split⟩ := records
  rw [respondEntry_of_transmission execution who _ material submits] at split
  exact onePacket_freshCall_settles bounds contract.inclusion later who event owned earlier rest
    _ _ split call

/-- **Sending at the first activation fails with probability zero.** Under the
asynchronous contract and the timeliness margin, let `who` send the canonical
decision at its first activation for `event`, at a history of the one-packet
game. From every history of the one-packet game recording that response, under
terminal play of any players, the event has completed and the packet has an
accepting receipt on every terminal history. -/
theorem firstActivation_canonical_accepted {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (records : RecordsEntry setup leaks who (respondEntry setup leaks execution who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)) history.state) :
    ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralTerminalFrom certificate players history).support,
      ∃ control, final.state = some control ∧
        event ∈ control.execution.application.config.cut.completed ∧
        ((sentEnvelope setup leaks execution who material).id, true) ∈
          control.execution.receipts := by
  intro final supported
  have recorded := ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
    horizon scheduler).runBehavioralTerminalFrom_support_closed certificate players
    (RecordsEntry setup leaks who (respondEntry setup leaks execution who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)))
    (fun state joint _ target holds reached =>
      recordsEntry_transition who _ (initialLaw setup) horizon scheduler state target joint holds
        reached)
    history records final supported
  have stopped := ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
    horizon scheduler).runBehavioralTerminalFrom_support_terminal certificate players history
    final supported
  cases state : final.state with
  | none =>
      rw [state] at recorded
      exact recorded.elim
  | some control =>
      rw [state] at recorded stopped
      have finalTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
          horizon scheduler).Trace (some control) := state ▸ final.trace
      have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some control) :=
        (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          scheduler finalTrace
      have terminal := contract.completes control rawTrace stopped
      have completed : event ∈ control.execution.application.config.cut.completed := by
        rw [terminal]
        exact Finset.mem_univ _
      exact ⟨control, rfl, completed, (firstActivation_canonical_settles bounds contract timely
        trace event turn never action material submits finalTrace recorded).2 completed⟩

end OnePacket

end Vegas

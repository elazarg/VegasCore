/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAuthorizationBreach
import Vegas.Pending.PacketNodeKind

/-! # Final rejection of packets addressed to the wrong event constructor

Commitments can be accepted only at binding nodes. Openings and withholding
can be accepted only at resolution nodes. This public graph check is fixed
under every later response and scheduler command, independently of tokens,
private material and evidence capability.

Actual accepting receipts certify this check. Envelope identity then rules
out a receipt for an actually emitted incompatible packet, including a valid
token and evidence-free withholding addressed to a binding. Complete actual
settlement supplies final forbiddenness; authentic partial observation and
conditional report delivery retain the existing collection contract.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A signed call whose public event node has another constructor. Tokens
and certificates may be valid; no private capability is classified. -/
def ServiceNodeKindBreach
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  ¬ message.payload.call.MatchesNode

/-- The same graph check is certified by every accepting receipt on actual
legal histories, under arbitrary responses and scheduler commands. -/
theorem matchesNode_receipts_history
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    control.execution.ReceiptsSound (application setup leaks)
      (fun packet => packet.call.MatchesNode) := by
  let app := application setup leaks
  have invariant : app.Invariant (fun _ => True) :=
    ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  have receipts := app.receiptServiceInvariant (fun _ => True)
    (fun packet => packet.call.MatchesNode) invariant
    (fun state message next _ accepted =>
      (runtime setup).handle_matchesNode state next ⟨message.id, message.payload.call⟩
        (reactiveHandle_call accepted)) scheduler
  exact (receipts.history (initialLaw setup) horizon
    (fun state _ => ⟨trivial, app.receiptsSound_initial _ state⟩) trace).2

/-- A wrong-kind packet cannot have an accepting receipt for its actual
emitted envelope. The receipt invariant and authentic envelope identity are
both derived from the initialized legal trace. -/
theorem ServiceNodeKindBreach.not_accepted_history
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks control.execution message)
    (breach : ServiceNodeKindBreach message) :
    (message.id, true) ∉ control.execution.receipts := by
  intro accepted
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  have sound := matchesNode_receipts_history trace
  obtain ⟨index, identified⟩ := List.mem_iff_get.mp accepted
  have leftBound : index.val < control.execution.network.ledger.length := by
    rw [sound.length_eq]
    exact index.isLt
  let other := control.execution.network.ledger.get ⟨index.val, leftBound⟩
  have checked := sound.get leftBound index.isLt
  rw [identified] at checked
  have otherEmitted : Emitted setup leaks control.execution other :=
    facts.carried.ledger other (List.get_mem _ _)
  have same := facts.emitted_unique otherEmitted emitted checked.1.symm
  have matched : other.payload.call.MatchesNode := checked.2 rfl
  rw [same] at matched
  exact breach matched

/-- At a complete legal settlement, an actually emitted incompatible packet
is forbidden under every later response and scheduler choice. -/
theorem ServiceNodeKindBreach.forbidden_history
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    {message : Message Player (WitnessedPacket (graph setup))}
    (emitted : Emitted setup leaks control.execution message)
    (breach : ServiceNodeKindBreach message)
    (complete : control.execution.application.config.cut.Terminal) :
    ((runtime setup).settledRecord leaks control.execution).permits message = false := by
  have rejected := breach.not_accepted_history trace emitted
  cases named : message.payload.call.event? (graph setup) with
  | none => exact SettledRecord.permits_eq_false_of_none _ message named
  | some event =>
      apply SettledRecord.permits_eq_false_of_settled _ message event named ?_
        (fun accepted => rejected (by
          simpa only [SettledRecord.Accepts, settledRecord] using accepted.1))
      apply (control.execution.application.config.history_exact event).mpr
      rw [complete]
      exact Finset.mem_univ event

/-- Every fresh canonical envelope has the packet constructor expected by
its public event node, independently of private commitment material. -/
theorem ServiceNodeKindBreach.not_freshServiceEnvelope
    {message : Message Player (WitnessedPacket (graph setup))}
    (breach : ServiceNodeKindBreach message)
    (view : PublicView (graph setup)) :
    ¬ (runtime setup).freshServiceEnvelope view message := by
  intro conform
  apply breach
  cases call : message.payload.call with
  | malformed raw => simp only [Payload.MatchesNode]
  | commitment event candidate =>
      cases node : nodeView (graph setup) event with
      | bind owner payload outputEq codeEq => simp only [Payload.MatchesNode, node]
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [freshServiceEnvelope, call, PublicView.BindingIncludable, node,
            and_false, false_and] at conform
      | sample payload law outputEq codeEq =>
          simp only [freshServiceEnvelope, call, PublicView.BindingIncludable, node,
            and_false, false_and] at conform
  | opening event candidate raw | withhold event =>
      cases node : nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [Payload.MatchesNode, node]
      | bind owner payload outputEq codeEq =>
          simp only [freshServiceEnvelope, call, node, and_false] at conform
      | sample payload law outputEq codeEq =>
          simp only [freshServiceEnvelope, call, node, and_false] at conform

/-- Valid-token evidence-free withholding at an owned binding is a concrete
wrong-kind breach, despite passing the constructor and authorization classes. -/
theorem withhold_binding_nodeKindBreach
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial : Nat) :
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(owner, serial), ⟨.withhold event, none, some ⟨event⟩⟩⟩
    ServiceNodeKindBreach message ∧ ¬ SignedContentBreach message ∧
      ¬ ServiceAuthorizationBreach message := by
  have actor := nodeView_bind_actor outputEq codeEq
  simp [ServiceNodeKindBreach, Payload.MatchesNode, node, SignedContentBreach,
    ServiceAuthorizationBreach, Payload.event?, actor, Message.sender]

/-- A bare commitment at an owned resolution is likewise rejected solely
by the immutable constructor check when its token and author are valid. -/
theorem commitment_resolution_nodeKindBreach
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (serial slot : Nat) :
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨(owner, serial), ⟨.commitment event (owner, .prepared slot), none, some ⟨event⟩⟩⟩
    ServiceNodeKindBreach message ∧ ¬ SignedContentBreach message ∧
      ¬ ServiceAuthorizationBreach message := by
  have actor := nodeView_resolve_actor outputEq codeEq
  simp [ServiceNodeKindBreach, Payload.MatchesNode, node, SignedContentBreach,
    ServiceAuthorizationBreach, Payload.event?, actor, Message.sender]

variable [Fintype Player]

/-- A wrong-kind signed call is excluded from the clear risk menu using
actual initialized slot resources and canonical envelope conformance. -/
theorem serviceNodeKindBreach_risk_excluded
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (breach : ServiceNodeKindBreach
      ⟨(who, execution.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit execution.application who material) who
          (execution.network.known who) material⟩) :
    response ∉ bounds.riskActions (runtime setup) leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) := by
  intro member
  rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear] at member
  have persistent := ((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_history bounds bound _ trace who persistent
  obtain ⟨event, action, turn, _, _, timely, unrecorded, _, decided⟩ :=
    bounds.canonicalActions_submission (runtime setup) leaks who _ _ response member material
      transmission
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have fresh := canonicalSlot_fresh_of_used rawTrace who atTurn slots event turn unrecorded
  have conform := canonicalServiceDecision_freshServiceEnvelope rawTrace event turn timely fresh
    action material (by rw [← decided]; exact transmission)
  exact breach.not_freshServiceEnvelope execution.application.publicView conform

end Vegas

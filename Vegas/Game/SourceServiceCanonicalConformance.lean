/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCanonicalSlots
import Vegas.Game.SourceServiceCanonicalAcceptance
import Vegas.Pending.ReactiveCompiledResolution

/-! # Prescribed fresh calls conform to the audit

On the support of the turn-counted policy, deferral trembles included and under
every scheduler, every fresh submission of a player following the policy
satisfies the audit's public conformance rule
(`Vegas.EventGraphRuntime.freshServiceEnvelope`) on the view it was made from
(`Vegas.sourceServiceTurnPolicy_freshServiceEnvelope`). A commitment names the
counted slot, which is fresh there (`Vegas.canonicalSlot_fresh_of_used`), and
the inclusion gate keeps every fresh call within its event's deadline.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

section Decision

variable {setup leaks}

/-- **A canonical decision conforms.** At a legal history where `event` is the
turn of `who`, within its deadline, with the counted slot fresh, every fresh
call of the canonical decision satisfies the audit's conformance rule on the
current public view. -/
theorem canonicalServiceDecision_freshServiceEnvelope {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {who : Player} {middle : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    (event : (serviceGraph setup mode).EventId)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (within : middle.application.publicView.WithinDeadline
        (serviceRuntime setup mode deadline) event)
    (fresh : middle.application.candidates.lookup
      (who, .prepared (middle.application.publicView.bindingCount who)) = .fresh)
    (action : (serviceGraph setup mode).Action event)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (submits :
        ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who (middle.recall who)
        (middle.observe (serviceApplication setup mode deadline leaks) who) event
        action).transmission = some material) :
    (serviceRuntime setup mode deadline).freshServiceEnvelope middle.application.publicView
      ⟨(who, middle.network.nextSerial who), (serviceApplication setup mode deadline leaks).packet
        ((serviceApplication setup mode deadline leaks).submit middle.application who material) who
        (middle.network.known who) material⟩ := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  have acceptable := canonicalServiceDecision_freshServiceAcceptable trace who event turn within
    action material submits
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have active := runtime.canonicalServiceDecision_active leaks who (middle.recall who)
    (middle.observe app who) event action material submits
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      have ownerless := nodeView_sample_actor outputEq codeEq
      rw [owned] at ownerless
      cases ownerless
  | bind actor payload outputEq codeEq =>
      have same : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actor
      obtain ⟨choice, rfl⟩ : ∃ choice : Option (PublicationResult (L.Val payload)),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases choice with
      | none =>
          rw [runtime.canonicalServiceDecision_binding_none leaks who (middle.recall who)
            (middle.observe app who) event who payload outputEq codeEq node] at submits
          cases submits
      | some result =>
          have canonical := canonicalFreshSlot_canonical who (middle.observe app who).application
            fresh
          rw [runtime.canonicalServiceDecision_binding leaks who (middle.recall who)
            (middle.observe app who) event payload outputEq codeEq node active _ canonical result]
            at submits
          cases Option.some.inj submits
          exact ⟨acceptable.1, rfl, rfl, acceptable.2⟩
  | resolve actor payload binding checks outputEq codeEq =>
      obtain ⟨choice, rfl⟩ : ∃ choice : Bool,
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks who (middle.recall who)
        (middle.observe app who) event _
        (fun _ _ _ _ different => by rw [node] at different; cases different)] at submits
      rcases runtime.serviceDecision_resolution_cases leaks who (middle.recall who)
        (middle.observe app who) event actor payload binding checks outputEq codeEq node choice
        with silent | ⟨candidate, value, evidence, _, _, _, responseEq⟩
      · rw [silent] at submits
        cases submits
      · rw [responseEq] at submits
        cases Option.some.inj submits
        exact acceptable

end Decision

section Support

/-- Every fresh call of `who` conforms to the audit on the view it was made
from. -/
def FreshCallsConform (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) : Prop := ∀ entry ∈ execution.recall who, ∀ material message,
    entry.action.transmission = some material → entry.emitted = some message →
    (serviceRuntime setup mode deadline).freshServiceEnvelope
    entry.beforeView.application.publicView message

variable {setup leaks}

/-- One round keeps the fresh calls of a player following the turn-counted
policy conforming. -/
theorem freshCallsConform_round {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {who : Player}
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {timing : TurnTiming setup turns mode}
    {profile : BehavioralProfile setup.program}
    (follows : players who = serviceTurnPolicy setup mode deadline leaks bound turns timing
        profile who)
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    FreshCallsConform setup leaks next who := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have conformMiddle : FreshCallsConform setup leaks middle who := by
    unfold FreshCallsConform
    rw [recallEq]
    exact conform
  have atMiddle : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have validMiddle := canonicalSlotsUsed_environment moved who valid
  rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, chosen, rfl⟩
  · exact conformMiddle
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
        scheduler remaining execution middle command trace selected moved
    rw [active] at middleTrace
    by_cases same : responder = who
    · subst responder
      rw [follows] at chosen
      obtain ⟨emittedOption, recalled, _⟩ := respond_recall_self setup leaks middle who response
      intro entry member material message submitted emitted
      rw [recalled] at member
      rcases List.mem_append.mp member with old | new
      · exact conformMiddle entry old material message submitted emitted
      · rw [List.mem_singleton] at new
        subst new
        change response.transmission = some material at submitted
        obtain ⟨event, action, turn, unrecorded, fits, decided⟩ :=
          sourceServiceTurnPolicy_submission chosen submitted
        have responseEq : response = ⟨some material⟩ := by
          rcases response with ⟨transmission⟩
          change transmission = _ at submitted
          rw [submitted]
        subst responseEq
        have submitRecall : (middle.respond app who ⟨some material⟩).recall who =
            middle.recall who ++ [⟨middle.observe app who, ⟨some material⟩,
              some ⟨(who, middle.network.nextSerial who),
                app.packet (app.submit middle.application who material) who
                  (middle.network.known who) material⟩⟩] := by
          simp [ReactiveApplication.Execution.respond, MessageNetwork.submit]
        rw [recalled] at submitRecall
        have lastEq := List.append_cancel_left submitRecall
        simp only [List.cons.injEq, ReactiveApplication.PlayerEntry.mk.injEq, true_and,
          and_true] at lastEq
        change emittedOption = some message at emitted
        rw [lastEq.2] at emitted
        cases emitted
        have fresh := canonicalSlot_fresh_of_used middleTrace who atMiddle validMiddle event turn
          unrecorded
        exact canonicalServiceDecision_freshServiceEnvelope middleTrace event turn
          fits.withinDeadline fresh action material
          (congrArg ReactiveApplication.Action.transmission decided.symm)
    · have different : who ≠ responder := fun equal => same equal.symm
      unfold FreshCallsConform
      rw [app.respond_recall_other middle responder who different response]
      exact conformMiddle

/-- **Prescribed fresh calls conform to the audit.** Under every scheduler, in
every profile in which `who` follows the turn-counted policy, deferral
trembles included, every fresh submission of `who` satisfies the audit's
public conformance rule on the view it was made from. -/
theorem sourceServiceTurnPolicy_freshServiceEnvelope
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player)
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    (follows : players who = serviceTurnPolicy setup mode deadline leaks bound turns timing
        profile who)
    (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler players count).support)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (member : entry ∈ execution.recall who)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (fresh : entry.action.transmission = some material)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (emitted : entry.emitted = some message) :
    (serviceRuntime setup mode deadline).freshServiceEnvelope
    entry.beforeView.application.publicView message := by
  let app := serviceApplication setup mode deadline leaks
  suffices conform : FreshCallsConform setup leaks execution who from
    conform entry member material message fresh emitted
  clear member
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro entry member
      cases member
  | succ count ih =>
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨atTurn, valid⟩ := canonicalSlots_roundsFrom scheduler players who timing profile
        follows count prior priorMem
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) (count + 1)
          scheduler players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact freshCallsConform_round follows trace atTurn valid (ih prior priorMem) moved

end Support

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalSlots

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
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Decision

variable {setup leaks}

/-- An opening prepared by the resolution decision discloses the owner-locally
validated value under the accepted handle of the player's own binding. -/
theorem reactiveResolutionPacket_opening {owner : Player} (who : Player)
    (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (action : (graph setup).Action event) (view : ReactivePlayerView (graph setup))
    (named : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (opened : reactiveResolutionPacket who event payload binding checks outputEq action view =
      some (.opening named candidate raw)) :
    (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true ∧
      ∃ value, EventGraph.EventCode.resolveOutput? binding checks true view.observation.store =
          some (.success value) ∧
        view.publicView.accepted binding.field = some candidate ∧ candidate.1 = who ∧
        raw = ⟨payload, value⟩ := by
  unfold reactiveResolutionPacket at opened
  dsimp only at opened
  split at opened
  · rename_i disclose
    split at opened
    · rename_i value resolved
      split at opened
      · rename_i handle accepted
        split at opened
        · rename_i owned
          cases opened
          exact ⟨disclose, value, resolved, accepted, owned, rfl⟩
        · cases opened
      · cases opened
    · cases opened
    · cases opened
  · cases opened

/-- **A canonical decision conforms.** At a legal history where `event` is the
turn of `who`, within its deadline, with the counted slot fresh, every fresh
call of the canonical decision satisfies the audit's conformance rule on the
current public view. -/
theorem canonicalServiceDecision_freshServiceEnvelope {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {who : Player} {middle : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (event : (graph setup).EventId)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (within : middle.application.publicView.WithinDeadline (runtime setup) event)
    (fresh : middle.application.candidates.lookup
      (who, .prepared (middle.application.publicView.bindingCount who)) = .fresh)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (middle.recall who)
      (middle.observe (application setup leaks) who) event action).transmission =
        some material) :
    (runtime setup).freshServiceEnvelope middle.application.publicView
      ⟨(who, middle.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit middle.application who material) who
        (middle.network.known who) material⟩ := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (middle.application.publicView_eventReady event).mp readyView
  have deadline : (match middle.application.activatedAt event with
      | none => False
      | some entered => middle.application.clock - entered <
          (runtime setup).deadline event) := within
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      have canonical := canonicalFreshSlot_canonical actor (middle.observe app actor).application
        fresh
      rw [(runtime setup).canonicalServiceDecision_binding leaks actor (middle.recall actor)
        (middle.observe app actor) event payload outputEq codeEq node _ canonical choice]
        at submits
      cases Option.some.inj submits
      have vacant : middle.application.accepted (.inr event) = none := by
        cases associated : middle.application.accepted (.inr event) with
        | none => rfl
        | some candidate =>
            exact False.elim (ready.1
              (facts.binding.toAssociationInvariant.accepted_complete event candidate
                associated))
      have unused : middle.application.HandleUnused
          (actor, .prepared (middle.application.publicView.bindingCount actor)) :=
        fun field associated => facts.binding.accepted_fixed field _ associated fresh
      rw [reactiveApplication_packet_none,
        middle.application.publicView_tokenFor_of_ready _ event rfl ready]
      apply ((runtime setup).freshServiceEnvelope_binding_iff middle.application.publicView
        (actor, middle.network.nextSerial actor) event
        (actor, .prepared (middle.application.publicView.bindingCount actor)) none _).mpr
      refine ⟨?_, rfl, rfl, rfl⟩
      simp only [PublicView.BindingIncludable, node]
      exact ⟨readyView, deadline, by trivial, by trivial, vacant, unused⟩
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks actor
        (middle.recall actor) (middle.observe app actor) event action
        (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
      unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
      simp only [node] at submits
      rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
          (middle.observe app actor).application with ⟨candidate, raw, packet⟩ | packet
      · obtain ⟨isTrue, value, localResolved, associated, handleOwner, rawEq⟩ :=
          reactiveResolutionPacket_opening actor event payload binding checks outputEq action
            (middle.observe app actor).application event candidate raw packet
        subst rawEq
        have resolved : EventGraph.EventCode.resolveOutput? binding checks true
            middle.application.config.store = some (.success value) := by
          have local' := localResolved
          change EventGraph.EventCode.resolveOutput? binding checks true
            ((graph setup).playerStore actor middle.application.config.store) = _ at local'
          rwa [EventGraph.EventCode.resolveOutput?_playerStore] at local'
        have stored := EventGraph.EventCode.binding_success_of_resolve_success binding checks
          true middle.application.config.store value resolved
        obtain ⟨handle, associatedHandle, _, fixed⟩ :=
          facts.binding.success_provenance binding value stored
        have handleEq : handle = candidate := by
          have same : middle.application.accepted binding.field = some candidate := associated
          rw [associatedHandle] at same
          exact Option.some.inj same
        subst handleEq
        have actionEq : action =
            cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
          rw [← isTrue, cast_cast, cast_eq]
        subst actionEq
        have decision := (runtime setup).serviceDecision_successful_opening leaks middle
          facts.inputs actor event payload binding checks outputEq codeEq node handle value
          associatedHandle handleOwner fixed resolved
        have materialEq : material =
            (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor (app.observePlayer middle.application actor) (middle.network.known actor) := by
          have transmission := congrArg ReactiveApplication.Action.transmission decision
          unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision
            at transmission
          simp only [node] at transmission
          rw [transmission] at submits
          cases submits
          rfl
        subst materialEq
        have packetEq : app.packet (app.submit middle.application actor
            ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor (app.observePlayer middle.application actor) (middle.network.known actor)))
            actor (middle.network.known actor)
            ((disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive
              actor (app.observePlayer middle.application actor) (middle.network.known actor)) =
              ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
                middle.application.publicView.tokenFor (.opening event handle ⟨payload, value⟩)⟩
              := by
          have emitted := WitnessedSubmission.normalizeReactive_emit (runtime setup) leaks
            middle.application actor (middle.network.known actor)
              (disclosureSubmission (.opening event handle ⟨payload, value⟩))
          have packet := (runtime setup).windowOpening_packet leaks actor event handle
            ⟨payload, value⟩ middle.application (middle.network.known actor) handleOwner fixed
          exact emitted.trans packet
        rw [packetEq, middle.application.publicView_tokenFor_of_ready _ event rfl ready]
        apply ((runtime setup).freshServiceEnvelope_opening_iff middle.application.publicView
          (actor, middle.network.nextSerial actor) event actor payload binding checks outputEq
          codeEq node handle ⟨payload, value⟩ (some ⟨handle, ⟨payload, value⟩⟩) _).mpr
        refine ⟨readyView, deadline, by simp only [certifiedOpening, decide_true], ?_, rfl,
          handleOwner, associatedHandle, rfl, rfl⟩
        apply (middle.application.publicView.openingGuardsAccepted_iff actor event payload
          binding checks outputEq codeEq node handle ⟨payload, value⟩ _).mpr
        refine ⟨value, rfl, ?_⟩
        change EventGraph.GuardCheck.allAccepted? checks
          ((graph setup).publicStore middle.application.config.store) (.success value) =
            some true
        rw [EventGraph.GuardCheck.allAccepted?_publicStore]
        exact EventGraph.EventCode.guards_pass_of_resolve_success binding checks true
          middle.application.config.store value resolved
      · rw [packet] at submits
        cases submits

end Decision

section Support

/-- Every fresh call of `who` conforms to the audit on the view it was made
from. -/
def FreshCallsConform (execution : (application setup leaks).Execution) (who : Player) :
    Prop :=
  ∀ entry ∈ execution.recall who, ∀ material message,
    entry.action.transmission = some material → entry.emitted = some message →
      (runtime setup).freshServiceEnvelope entry.beforeView.application.publicView message

variable {setup leaks}

/-- One round keeps the fresh calls of a player following the turn-counted
policy conforming. -/
theorem freshCallsConform_round {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} {who : Player}
    {bound : (graph setup).EventId → Nat} {turns : Nat} {timing : TurnTiming setup turns}
    {profile : BehavioralProfile setup.program}
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    {execution next : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (conform : FreshCallsConform setup leaks execution who)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    FreshCallsConform setup leaks next who := by
  let app := application setup leaks
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
  · obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
      remaining execution middle command trace selected moved
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
        have submitRecall := respond_submit_recall middle who material
        rw [recalled] at submitRecall
        have lastEq := List.append_cancel_left submitRecall
        simp only [List.cons.injEq, ReactiveApplication.PlayerEntry.mk.injEq, true_and,
          and_true] at lastEq
        change emittedOption = some message at emitted
        rw [lastEq] at emitted
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
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    {bound : (graph setup).EventId → Nat} {turns : Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns timing profile who)
    (count : Nat) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall who)
    (material : (application setup leaks).Submission)
    (fresh : entry.action.transmission = some material)
    (message : Message Player (WitnessedPacket (graph setup)))
    (emitted : entry.emitted = some message) :
    (runtime setup).freshServiceEnvelope entry.beforeView.application.publicView message := by
  let app := application setup leaks
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
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) (count + 1) scheduler
        players count (Nat.le_succ count) prior priorMem
      rw [show count + 1 - count = 0 + 1 by omega] at trace
      exact freshCallsConform_round follows trace atTurn valid (ih prior priorMem) moved

end Support

end Vegas

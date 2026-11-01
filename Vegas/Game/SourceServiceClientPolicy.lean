/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncServiceSpec
import Vegas.Game.SourceServiceCanonicalSlots
import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Source.DisclosureBehavioral
import Vegas.Game.SourceServiceRetainedPolicy
import Interaction.ReactiveRecovery

/-! # Bounded turn-counted client policies

Completing a client by silence after its own off-policy responses preserves
its execution law. On histories consistent with the prescribed client, used
prepared slots remain canonical and the next response fits the finite raw
menu. Binding omission is silence; opaque admission and covered successful
bindings are submitted separately. Authentic openings are bounded independently
of their eventual public guard result.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Menu

variable [Fintype Player]

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
  (bounds : MessageBounds (serviceGraph setup mode))

/-- Every source action, including omission and opaque binding admission, has a
bounded canonical response when the counted prepared slot is available. -/
theorem sourceServiceCanonicalDecision_canonical_of_slots
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
      bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (who : Player)
    {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (event : (serviceGraph setup mode).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (timely : execution.application.publicView.WithinDeadline
      (serviceRuntime setup mode deadline) event)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks
      (execution.recall who) event = false)
    (choice : (serviceGraph setup mode).Action event) :
    (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) event choice ∈
      bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who) := by
  classical
  have rawTrace := (bounds.rawMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
    (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨counted, fresh, selected⟩ := canonicalSlot_resources_of_used bounds capacity
    rawTrace who atTurn valid event turn unsent
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have values := bounds.candidateValues_raw_history (serviceRuntime setup mode deadline) leaks
    (serviceInitialLaw setup mode) horizon scheduler initialCovered trace
  have boundedTrace := trace
  rw [serviceInitialLaw_eq_inputs] at boundedTrace
  have handles := bounds.executionHandles_raw_history (serviceRuntime setup mode deadline) leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler boundedTrace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  by_cases inactive : who ∈ execution.application.config.defaulted
  · rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_defaulted leaks who
      (execution.recall who) (execution.observe (serviceApplication setup mode deadline leaks) who)
      event choice inactive]
    exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      have ownerless := nodeView_sample_actor outputEq codeEq
      rw [owned] at ownerless
      cases ownerless
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨result, rfl⟩ : ∃ result : Option (PublicationResult (L.Val payload)),
          choice = cast (congrArg EventGraph.EventField.Action outputEq.symm) result :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice, by simp⟩
      cases result with
      | none =>
          rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_binding_none leaks
            actor _ _ event actor payload outputEq codeEq node]
          exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks actor _ _
      | some result =>
          apply bounds.canonical_decision_retained (serviceRuntime setup mode deadline) leaks
            actor _ _ event _ turn owned readyView timely unsent
          · simp only [MessageBounds.canonicalChoices, node]
            apply Finset.mem_image.mpr
            refine ⟨some result, ?_, rfl⟩
            cases result with
            | failure => simp [MessageBounds.bindingChoices]
            | success value =>
                apply Finset.mem_union_right
                apply Finset.mem_image.mpr
                refine ⟨value, (bounds.typedValues_mem payload value).mpr ?_, rfl⟩
                refine ⟨⟨payload, value⟩, ?_, Raw.as?_mk payload value⟩
                have all := covered event
                rw [outputEq] at all
                exact all value
          · rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks actor
              (execution.recall actor)
              (execution.observe (serviceApplication setup mode deadline leaks) actor) event payload
              outputEq codeEq node inactive _ selected result]
            rw [← (serviceRuntime setup mode deadline).reactiveBinding_normal_of_fresh leaks actor
              (execution.recall actor)
              (execution.observe (serviceApplication setup mode deadline leaks) actor) event payload
              result _ (canonicalFreshSlot_spec actor _ _ selected)]
            apply bounds.binding_normalized_available (serviceRuntime setup mode deadline) leaks
              actor _ _ event payload result _ counted
            intro value _
            have all := covered event
            rw [outputEq] at all
            exact all value
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
          choice = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice, by simp⟩
      apply bounds.canonical_resolution_retained (serviceRuntime setup mode deadline) leaks
        actor _ _ event actor payload binding checks outputEq codeEq node turn owned readyView
          timely unsent disclose
      exact sourceService_resolutionPacket_allowed bounds execution facts.binding values handles.1
        actor event payload binding checks outputEq _


/-- Turn-counted clients of unrestricted source profiles use bounded canonical
responses wherever their own previous responses follow the client. -/
theorem sourceServiceTurnPolicy_canonical_of_slots
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
      bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (valid : CanonicalSlotsUsed setup leaks execution who)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceTurnPolicy setup mode deadline leaks bound turns timing
      profile who (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
      (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) := by
  cases sent : response.transmission with
  | none =>
      have silent : response = ⟨none⟩ := congrArg
        (fun transmission => (⟨transmission⟩ :
          (serviceApplication setup mode deadline leaks).Action)) sent
      rw [silent]
      exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _
  | some material =>
      obtain ⟨event, choice, turn, unsent, fits, rfl⟩ :=
        sourceServiceTurnPolicy_submission supported sent
      exact sourceServiceCanonicalDecision_canonical_of_slots bounds covered initialCovered
        capacity who
        execution trace atTurn valid event turn fits.withinDeadline unsent choice

private abbrev ConsistentSlots (bound : (serviceGraph setup mode).EventId → Nat) (turns
  : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  ∀ who, (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who).Consistent
      (execution.recall who) →
    OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who

private theorem consistentSlots_transition
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (before after : (serviceApplication setup mode deadline leaks).ProtocolState)
    (prior :
        ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace before)
    (joint : Player → Option (serviceApplication setup mode deadline leaks).Action)
    (valid : ReactiveApplication.serviceInvariant
      (ConsistentSlots bound turns timing profile) before)
    (reached : after ∈
        ((serviceApplication setup mode deadline leaks).transition (serviceInitialLaw setup mode)
        horizon scheduler before joint).support) :
    ReactiveApplication.serviceInvariant (ConsistentSlots bound turns timing profile)
      after := by
  let app := serviceApplication setup mode deadline leaks
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      intro who _
      exact ⟨fun entry member => (by cases member), fun serial used => (by cases used)⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          intro player consistent
          by_cases same : player = who
          · subst same
            obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks execution player
              ((joint player).getD ⟨none⟩)
            change (serviceTurnPolicy setup mode deadline leaks bound turns timing profile
              player).Consistent ((execution.respond app player
                ((joint player).getD ⟨none⟩)).recall player) at consistent
            rw [recalled, ReactiveApplication.Policy.consistent_snoc_iff] at consistent
            obtain ⟨atTurn, slots⟩ := valid player consistent.1
            have rawTrace := (bounds.rawMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
              (serviceInitialLaw setup mode) horizon scheduler prior
            refine ⟨?_, canonicalSlotsUsed_respond rawTrace
              (serviceTurnPolicy_submitsCanonically bound turns timing profile player)
              consistent.2 atTurn slots⟩
            intro entry present event submitted
            rw [recalled] at present
            rcases List.mem_append.mp present with old | fresh
            · exact atTurn entry old event submitted
            · obtain rfl := List.mem_singleton.mp fresh
              exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns timing profile
                player _ _ _ consistent.2 event submitted
          · have recallEq := app.respond_recall_other execution who player same
              ((joint who).getD ⟨none⟩)
            change (serviceTurnPolicy setup mode deadline leaks bound turns timing profile
              player).Consistent ((execution.respond app who ((joint who).getD ⟨none⟩)).recall
                player) at consistent
            rw [recallEq] at consistent
            obtain ⟨atTurn, slots⟩ := valid player consistent
            refine ⟨?_, canonicalSlotsUsed_respond_other execution same _ slots⟩
            unfold OwnSubmissionsAtTurn
            rw [recallEq]
            exact atTurn
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              intro player consistent
              have recallEq := app.environmentStep_recall execution next command supported
              change (serviceTurnPolicy setup mode deadline leaks bound turns timing profile
                player).Consistent (next.recall player) at consistent
              rw [recallEq] at consistent
              obtain ⟨atTurn, slots⟩ := valid player consistent
              refine ⟨?_, canonicalSlotsUsed_environment supported player slots⟩
              unfold OwnSubmissionsAtTurn
              rw [recallEq]
              exact atTurn

/-- **Consistent clients keep canonical slots.** On every bounded raw history,
a player whose recorded responses all follow the turn-counted policy has
submitted only at its own turns, and its used prepared slots stay canonical,
whatever bounded responses the other players gave. -/
theorem sourceServiceTurnPolicy_consistent_slots
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} :
    ∀ {state}
        (_trace :
            ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
            (serviceInitialLaw setup mode) horizon scheduler).Trace state),
        ReactiveApplication.serviceInvariant
        (fun execution => ∀ who,
            (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who).Consistent
            (execution.recall who) → OwnSubmissionsAtTurn setup leaks execution who ∧
            CanonicalSlotsUsed setup leaks execution who) state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      consistentSlots_transition bounds bound turns
        timing profile
        _ _ prior joint
        (sourceServiceTurnPolicy_consistent_slots bound turns
          timing profile prior) reached

/-- **The client policies are bounded raw responses.** For every source
profile, including failed binding choices, each player's client policy is
admissible in the bounded raw response menu under every scheduler: where its
own recorded responses all follow the turn-counted policy, its canonical
decisions fit the bounds; elsewhere it is silent. -/
theorem sourceServiceClientPolicy_raw_admissible
    (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
      bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (who : Player) :
    (bounds.rawMenu (serviceRuntime setup mode deadline) leaks).Admissible
      (serviceInitialLaw setup mode) horizon scheduler who
      (serviceClientPolicy setup mode deadline leaks bound turns timing profile who) := by
  intro control trace active response supported
  by_cases consistent : (serviceTurnPolicy setup mode deadline leaks bound turns timing profile
    who).Consistent (control.execution.recall who)
  · rw [serviceClientPolicy, ReactiveApplication.Policy.recover_eq _ _ _ _ consistent]
      at supported
    obtain ⟨atTurn, slots⟩ := sourceServiceTurnPolicy_consistent_slots bounds bound turns timing
      profile trace who consistent
    have actorTrace : ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨control.remaining, some who, control.execution⟩) := by
      simpa only [← active] using trace
    have member := sourceServiceTurnPolicy_canonical_of_slots bounds covered initialCovered capacity
      bound turns timing profile who control.execution actorTrace atTurn slots response supported
    have effective := bounds.canonicalActions_effective (serviceRuntime setup mode deadline) leaks
      who _ _ member
    obtain ⟨original, allowed, normal⟩ :=
      ((serviceRuntime setup mode deadline).reactiveNormalization leaks).menu_mem
        (bounds.rawMenu (serviceRuntime setup mode deadline) leaks) who _ _ response |>.mp effective
    rw [← normal]
    exact bounds.rawMenu_closed (serviceRuntime setup mode deadline) leaks who _ _ original allowed
  · rw [serviceClientPolicy,
      ReactiveApplication.Policy.recover_eq_recovery _ _ _ _ consistent] at supported
    exact canonicalMenu_in_raw bounds who _ _
      (bounds.silent_canonical (serviceRuntime setup mode deadline) leaks who _ _ response
          supported)


end Menu

namespace AsyncServiceSpec

variable [Fintype Player] (service : AsyncServiceSpec Player L)
  (admission : CommitmentInterface service.setup.program)

/-- **The bounded raw menu admits every profile's clients.** For every turn
timing and every source profile, each player's client policy is admissible in
the bounded raw response menu. -/
theorem rawMenu_admits {turns : Nat}
    (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature) (who : Player) :
    service.rawMenu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler who
      (serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
        turns timing
        (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
          admission source)) who) :=
  sourceServiceClientPolicy_raw_admissible service.bounds service.values service.initialValues
    service.capacity service.bound turns timing _ service.horizon service.scheduler who

end AsyncServiceSpec

end Vegas

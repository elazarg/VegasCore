/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTurnSettlement
import Vegas.Game.SourceServiceRetainedPolicy
import Interaction.ReactiveRecovery

/-! # Turn-counted clients completed after their own off-policy responses

The client policy (`Vegas.sourceServiceClientPolicy`) is the turn-counted
policy, completed by silence at every history where the player's own recorded
responses do not all follow it. Completion changes no execution law, against
arbitrary other players (`Vegas.sourceServiceClientPolicy_roundsFrom`,
`Vegas.sourceServiceClientPolicy_deviation_roundsFrom`), so the client policy
inherits the settlement law of the turn-counted policy
(`Vegas.sourceServiceClients_clientPolicy_settlement_lawError`).

Failed binding choices send a conformant opaque commitment without an opening,
so they fit the same bounded response domain as successful value bindings.
The completion makes the clients admissible in the bounded raw response menu
(`Vegas.sourceServiceClientPolicy_raw_admissible`). On every bounded raw
history, a player whose recorded responses all follow the turn-counted policy
has submitted only at its own turns and used only canonical prepared slots
(`Vegas.sourceServiceTurnPolicy_consistent_slots`), whatever the other players
did; its next canonical decision then fits the bounds. The turn-counted policy
itself is not admissible there in general: after a player's own earlier
bounded responses have used up its prepared slots, its canonical decision
selects a slot beyond the candidate count.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- **The client policy.** The turn-counted policy, completed by silence at
every history where the player's own recorded responses do not all follow
it. -/
def serviceClientPolicy (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) : (serviceApplication setup mode deadline leaks).Policy :=
  (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who).recover
    (serviceApplication setup mode deadline leaks).silentPolicy

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The client policy on the default runtime. -/
abbrev sourceServiceClientPolicy : ((graph setup).EventId → Nat) → (turns : Nat) →
    TurnTiming setup turns → BehavioralProfile setup.program → Player →
      (application setup leaks).Policy :=
  serviceClientPolicy setup .sequential (rankDeadline setup .sequential) leaks

section Configured

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The client policies have the execution law of the turn-counted policies. -/
theorem sourceServiceClientPolicy_roundsFrom (scheduler : (serviceApplication setup mode deadline
    leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat) (timing : TurnTiming setup
      turns mode)
    (profile : BehavioralProfile setup.program) (count : Nat) :
    (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler
        (serviceClientPolicy setup mode deadline leaks bound turns timing profile) count =
      (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) count := by
  unfold ReactiveApplication.roundsFrom
  congr 1
  funext state
  have completed := ReactiveApplication.Policy.recoverWhere_runRounds
    (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) (fun _ => True)
    (fun _ => (serviceApplication setup mode deadline leaks).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks) state)
      (fun _ _ => .nil)
  simp only [ite_true] at completed
  exact completed

/-- Against a unilateral deviation, the other players' client policies have the
execution law of their turn-counted policies. -/
theorem sourceServiceClientPolicy_deviation_roundsFrom
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (bound : (serviceGraph
      setup mode).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (serviceApplication setup mode deadline leaks).Policy) (count :
      Nat) :
    (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler
        (Function.update (serviceClientPolicy setup mode deadline leaks bound turns timing profile)
          who
          alternative) count =
      (serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler
        (deviatedTurnProfile bound turns timing profile who alternative) count := by
  have shape : Function.update (serviceClientPolicy setup mode deadline leaks bound turns timing
    profile)
      who alternative = fun player => if player ≠ who then
        (deviatedTurnProfile bound turns timing profile who alternative player).recover
          (serviceApplication setup mode deadline leaks).silentPolicy
      else deviatedTurnProfile bound turns timing profile who alternative player := by
    funext player
    by_cases same : player = who
    · subst same
      simp only [Function.update_self, ne_eq, not_true_eq_false, ↓reduceIte]
    · simp only [Function.update_of_ne same, ne_eq, same, not_false_eq_true, ↓reduceIte]
      rfl
  unfold ReactiveApplication.roundsFrom
  rw [shape]
  congr 1
  funext state
  exact ReactiveApplication.Policy.recoverWhere_runRounds
    (deviatedTurnProfile bound turns timing profile who alternative) (fun player => player ≠ who)
    (fun _ => (serviceApplication setup mode deadline leaks).silentPolicy) scheduler count
    (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks) state)
      (fun _ _ => .nil)

end Configured

variable {setup leaks}

section Menu

variable [Fintype Player]

/-- **Honest execution of the client policies, for every source profile.**
Under the asynchronous contract with `delay + bound < deadline`, for every turn
timing and every source profile whose clients' first-turn limit has its source
outcome law, the client policies of the profile's turn-counted clients, restricted to a response
menu that admits them, have the profile's source joint law of typed outcome and
realized payoffs within the total deferral weight in total variation, for every
authentic partial audit and every deposit. -/
theorem sourceServiceClients_clientPolicy_settlement_lawError
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (timing : TurnTiming setup turns mode) (original : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns
      (sourceServiceClientProfile setup original))
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (serviceInitialLaw setup mode) horizon scheduler who
      (serviceClientPolicy setup mode deadline leaks bound turns timing
        (sourceServiceClientProfile setup original) who))
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
      ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
      (serviceSourceAudit setup mode deadline leaks sample) deposit
    PMF.WithinTV (∑ event, timing.deferral event)
      (((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
          (serviceClientPolicy setup mode deadline leaks bound turns timing
            (sourceServiceClientProfile setup original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs => (serviceSourceReadout setup mode deadline leaks
            final.state, payoffs)))
      ((setup.run original).map (fun state => (some state, utility state))) := by
  intro settle
  let app := serviceApplication setup mode deadline leaks
  let clients := sourceServiceClientProfile setup original
  have physical := menu.run_restrict_eq_finish (serviceInitialLaw setup mode) horizon scheduler
    (serviceClientPolicy setup mode deadline leaks bound turns timing clients) covered
    (2 * horizon + 1) (menu.protocol (serviceInitialLaw setup mode) horizon scheduler).initHistory
    le_rfl
  have states : ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
        (serviceClientPolicy setup mode deadline leaks bound turns timing clients who))
      (2 * horizon + 1)).map (fun final => final.state) =
        (serviceInitialLaw setup mode).bind (fun state =>
          (app.runRounds scheduler
            (serviceClientPolicy setup mode deadline leaks bound turns timing clients) horizon
            (ReactiveApplication.Execution.initial app state)).map app.finished) := by
    rw [InformationModel.runBehavioral]
    exact physical
  have native : ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
        (serviceClientPolicy setup mode deadline leaks bound turns timing clients who))
      (2 * horizon + 1)).bind (fun final =>
        (settle final.state).map fun payoffs =>
          (serviceSourceReadout setup mode deadline leaks final.state, payoffs)) =
      (app.roundsFrom (serviceInitialLaw setup mode) scheduler
        (serviceClientPolicy setup mode deadline leaks bound turns timing clients) horizon).bind
          (fun execution => (settle (app.finished execution)).map
            fun payoffs => (serviceSourceReadout setup mode deadline leaks
              (app.finished execution), payoffs)) := by
    have joint := congrArg (fun law : PMF app.ProtocolState =>
      law.bind fun final =>
        (settle final).map fun payoffs =>
          (serviceSourceReadout setup mode deadline leaks final, payoffs)) states
    simp only [PMF.bind_map, PMF.bind_bind] at joint
    refine joint.trans ?_
    unfold ReactiveApplication.roundsFrom
    simp only [PMF.bind_bind, Function.comp_def]
    rfl
  rw [native, sourceServiceClientPolicy_roundsFrom, ← sourceServiceClientProfile_run original]
  exact sourceServiceTurnPolicy_execution_settlement_lawError contract timely timing
    clients terminal sample authentic utility deposit

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
  (bounds : MessageBounds (serviceGraph setup mode))

/-- Every source binding choice, including failure, has a bounded effective
canonical response when the counted prepared slot is available. -/
theorem sourceServiceCanonicalDecision_clear_of_slots
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
      bounds.clearActions (serviceRuntime setup mode deadline) leaks who
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
  have effective : (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
    (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) event choice ∈
      (bounds.menu (serviceRuntime setup mode deadline) leaks).actions who (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who) := by
    cases node : nodeView (serviceGraph setup mode) event with
    | sample payload law outputEq codeEq =>
        have ownerless := nodeView_sample_actor outputEq codeEq
        rw [owned] at ownerless
        cases ownerless
    | bind actor payload outputEq codeEq =>
        have actorEq : actor = who :=
          Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
        subst actorEq
        obtain ⟨result, rfl⟩ : ∃ result : PublicationResult (L.Val payload),
            choice = cast (congrArg EventGraph.EventField.Action outputEq.symm) result :=
          ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice,
            ((cast_cast (congrArg EventGraph.EventField.Action outputEq)
              (congrArg EventGraph.EventField.Action outputEq.symm) choice).trans
                (cast_eq _ choice)).symm⟩
        have same := ((serviceRuntime setup mode deadline).canonicalServiceDecision_binding
          leaks actor (execution.recall actor)
          (execution.observe (serviceApplication setup mode deadline leaks) actor) event payload
          outputEq codeEq node _ selected result).trans
          (((serviceRuntime setup mode deadline).reactiveBinding_normal_of_fresh leaks actor
            (execution.recall actor)
            (execution.observe (serviceApplication setup mode deadline leaks) actor) event payload
            result _ (canonicalFreshSlot_spec actor _ _ selected)).symm)
        have available := bounds.binding_normalized_available (serviceRuntime setup mode deadline)
          leaks actor (execution.recall actor)
          (execution.observe (serviceApplication setup mode deadline leaks) actor) event payload
          result _ counted (fun value _ => by
            have all := covered event
            rw [outputEq] at all
            exact all value)
        exact same.symm ▸ available
    | resolve actor payload binding checks outputEq codeEq =>
        have actorEq : actor = who :=
          Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
        subst actorEq
        obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
            choice = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose :=
          ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice,
            ((cast_cast (congrArg EventGraph.EventField.Action outputEq)
              (congrArg EventGraph.EventField.Action outputEq.symm) choice).trans
                (cast_eq _ choice)).symm⟩
        apply bounds.canonicalActions_effective (serviceRuntime setup mode deadline) leaks actor _ _
        apply bounds.canonical_resolution_retained (serviceRuntime setup mode deadline) leaks
          actor _ _ event actor payload
          binding checks outputEq codeEq node turn owned readyView timely unsent disclose
        exact sourceService_resolutionPacket_allowed bounds execution facts.binding values handles.1
          actor event payload binding checks outputEq _
  rcases (serviceRuntime setup mode deadline).canonicalServiceDecision_cases leaks who
    (execution.recall who)
    (execution.observe (serviceApplication setup mode deadline leaks) who) event choice with
      silent | named
  · rw [silent]
    exact bounds.canonicalActions_subset_clear (serviceRuntime setup mode deadline) leaks who _ _
      (bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _)
  · obtain ⟨material, sent⟩ : ∃ material,
        ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who (execution.recall
          who)
          (execution.observe (serviceApplication setup mode deadline leaks) who) event
            choice).transmission = some material := by
      unfold EventGraphRuntime.submittedEvent? at named
      split at named
      · exact ⟨_, ‹_›⟩
      · cases named
    apply Finset.mem_union_right
    apply (bounds.mem_conformantActions (serviceRuntime setup mode deadline) leaks who _ _ _).mpr
    refine ⟨effective, material, sent,
      (serviceRuntime setup mode deadline).canonicalServiceDecision_firstSubmission leaks who _ _
        event choice unsent, ?_⟩
    rw [localEnvelope_actual rawTrace who material]
    exact canonicalServiceDecision_freshServiceEnvelope rawTrace event turn timely fresh
      choice material sent


/-- Turn-counted clients of unrestricted source profiles use bounded clear
responses wherever their own previous responses follow the client. -/
theorem sourceServiceTurnPolicy_clear_of_slots
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
    response ∈ bounds.clearActions (serviceRuntime setup mode deadline) leaks who
      (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) := by
  cases sent : response.transmission with
  | none =>
      have silent : response = ⟨none⟩ := congrArg
        (fun transmission => (⟨transmission⟩ :
          (serviceApplication setup mode deadline leaks).Action)) sent
      rw [silent]
      exact bounds.canonicalActions_subset_clear (serviceRuntime setup mode deadline) leaks who _ _
        (bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _)
  | some material =>
      obtain ⟨event, choice, turn, unsent, fits, rfl⟩ :=
        sourceServiceTurnPolicy_submission supported sent
      exact sourceServiceCanonicalDecision_clear_of_slots bounds covered initialCovered capacity who
        execution trace atTurn valid event turn fits.withinDeadline unsent choice

private abbrev ConsistentSlots (bound : (serviceGraph setup mode).EventId → Nat) (turns
  : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  ∀ who, (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who).Consistent
      (execution.recall who) →
    OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who

private theorem consistentSlots_transition (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
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
            have member := sourceServiceTurnPolicy_clear_of_slots bounds covered initialCovered
              capacity bound turns timing profile player execution prior atTurn slots _ consistent.2
            have rawTrace := (bounds.rawMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
                (serviceInitialLaw setup mode) horizon scheduler prior
            exact ⟨retainedOwnSubmissionsAtTurn_respond bounds execution player _ member atTurn,
              retainedCanonicalSlots_respond bounds rawTrace member atTurn slots⟩
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
theorem sourceServiceTurnPolicy_consistent_slots (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
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
      consistentSlots_transition bounds covered initialCovered capacity bound turns
        timing profile
        _ _ prior joint
        (sourceServiceTurnPolicy_consistent_slots covered initialCovered capacity bound turns
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
    obtain ⟨atTurn, slots⟩ := sourceServiceTurnPolicy_consistent_slots bounds covered
      initialCovered capacity bound turns timing profile trace who consistent
    have actorTrace : ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨control.remaining, some who, control.execution⟩) := by
      simpa only [← active] using trace
    have member := sourceServiceTurnPolicy_clear_of_slots bounds covered initialCovered capacity
      bound turns timing profile who control.execution actorTrace atTurn slots response supported
    have effective := bounds.clearActions_effective (serviceRuntime setup mode deadline) leaks
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

end Vegas

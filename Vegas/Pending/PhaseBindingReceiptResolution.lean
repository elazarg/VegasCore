/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseExclusionOrigin
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveServiceRounds
import Interaction.ReactiveReceipts
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseResolutionPersistence

/-! # Actual binding receipts resolve their immutable physical attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- A successful phase call authenticates its original full namespace. -/
theorem handle_attempt_eq (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next) :
    message.payload.attempt = state.attempt := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rename_i permitted
    have parts := Bool.and_eq_true_iff.mp permitted
    have tokenAndCall := Bool.and_eq_true_iff.mp parts.1
    have token := Bool.and_eq_true_iff.mp tokenAndCall.1
    exact of_decide_eq_true token.1
  · cases accepted

/-- No successfully handled packet can name an already resolved coordinate. -/
theorem handle_event_unresolved (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (named : message.payload.packet.call.event? graph = some event)
    (accepted : state.handle runtime message = some next) :
    ¬ (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph).Resolved state := by
  have attemptEq := handle_attempt_eq runtime state next message accepted
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, _normalized⟩ := Option.map_eq_some_iff.mp accepted
    obtain ⟨actual, addressed, unfinished, _completed⟩ := handle_completes runtime
      state.current.native native ⟨message.id, message.payload.packet.call⟩ handled
    have same : actual = event := Option.some.inj (addressed.symm.trans named)
    subst actual
    intro resolved
    rcases resolved with generation | phase | ⟨_current, completed⟩
    · exact Nat.lt_irrefl _ (by simpa only [attemptEq] using generation)
    · exact Nat.lt_irrefl _ (by simpa only [attemptEq] using phase)
    · exact unfinished completed
  · cases accepted

/-- A successful native call resolves its original attempt coordinate,
even when that very inclusion closes the phase and restores the live store. -/
theorem handle_event_resolved (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (state next : PhaseRuntimeState graph) (ordered : state.Ordered)
    (message : Message Player (CommitAttemptPacket graph)) (event : graph.EventId)
    (named : message.payload.packet.call.event? graph = some event)
    (accepted : state.handle runtime message = some next) :
    (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph).Resolved next := by
  have attemptEq := handle_attempt_eq runtime state next message accepted
  have progress := (phaseApplication_namespace_progress runtime leaks).handle
    state message next accepted ordered
  apply CommitAttemptEvent.Resolved.of_step _ state next attemptEq progress
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    obtain ⟨actual, addressed, _unfinished, completed⟩ := handle_completes runtime
      state.current.native native ⟨message.id, message.payload.packet.call⟩ handled
    have same : actual = event := Option.some.inj (addressed.symm.trans named)
    subst actual
    simpa only [attemptEq, normalize, attempt] using
      settle_resolves state.phases state.generation state.entry
      (state.current.inclusionResult message.payload.packet.call native) state.retired ordered
        event completed
  · cases accepted

end PhaseRuntimeState

namespace PhaseService

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every true binding receipt refers to a coordinate that is permanently
resolved, rather than necessarily remaining in the live post-reset store. -/
def BindingReceiptResolution (execution : (app).Execution) : Prop :=
  execution.ReceiptsSound app fun packet => ∀ event,
    packet.packet.call.event? graph = some event →
      (⟨packet.attempt, event⟩ : CommitAttemptEvent graph).Resolved execution.application

private theorem receiptResolution_rebase (before after : (app).Execution)
    (sound : BindingReceiptResolution runtime leaks before)
    (ledger : after.network.ledger = before.network.ledger)
    (receipts : after.receipts = before.receipts)
    (preserved : ∀ coordinate : CommitAttemptEvent graph,
      coordinate.Resolved before.application → coordinate.Resolved after.application) :
    BindingReceiptResolution runtime leaks after := by
  unfold BindingReceiptResolution ReactiveApplication.Execution.ReceiptsSound at sound ⊢
  rw [ledger, receipts]
  apply sound.imp
  intro message receipt related
  refine ⟨related.1, ?_⟩
  intro accepted event named
  exact preserved _ (related.2 accepted event named)

private theorem receiptResolution_includePending (execution : (app).Execution)
    {draw : graph.Inputs} (valid : execution.application.Invariant draw)
    (ordered : execution.application.Ordered)
    (sound : BindingReceiptResolution runtime leaks execution) (id : MessageId Player) :
    BindingReceiptResolution runtime leaks (execution.includePending app id) := by
  classical
  have preserved (coordinate : CommitAttemptEvent graph) :=
    (phaseApplication_resolution runtime leaks coordinate).includePending execution id
      draw valid ordered
  have old : List.Forall₂ (fun message receipt => receipt.1 = message.id ∧
      (receipt.2 = true → ∀ event,
        message.payload.packet.call.event? graph = some event →
          (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph).Resolved
            (execution.includePending app id).application))
      execution.network.ledger execution.receipts := by
    apply sound.imp
    intro message receipt related
    exact ⟨related.1, fun accepted event named =>
      preserved _ (related.2 accepted event named)⟩
  unfold BindingReceiptResolution ReactiveApplication.Execution.ReceiptsSound
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending at old ⊢
  cases found : execution.network.lookup id with
  | none =>
    simpa only [found, Option.getD_none, BindingReceiptResolution,
      ReactiveApplication.Execution.ReceiptsSound] using sound
  | some message =>
    have addressed : message.id = id := by
      have identified := (List.find?_eq_some_iff_append.mp found).1
      simpa only [decide_eq_true_eq] using identified
    simp only [found] at old ⊢
    apply List.rel_append old
    refine List.Forall₂.cons ⟨addressed.symm, ?_⟩ List.Forall₂.nil
    intro accepted event named
    obtain ⟨next, handled⟩ := Option.isSome_iff_exists.mp accepted
    simpa only [handled, Option.getD_some] using
      PhaseRuntimeState.handle_event_resolved runtime leaks execution.application next ordered
        message event named handled

/-- Resolution certified by every actual true binding receipt survives all
primitive operations, including rollback, exhaustion and arbitrary raw play. -/
theorem bindingReceiptResolution_invariant (scheduler : (app).Scheduler) :
    (app).ServiceInvariant scheduler (fun execution =>
      (∃ draw, execution.application.Invariant draw) ∧ execution.application.Ordered ∧
        BindingReceiptResolution runtime leaks execution) where
  respond execution owner action invariant := by
    obtain ⟨⟨draw, valid⟩, ordered, sound⟩ := invariant
    refine ⟨⟨draw, (phaseApplication_invariant runtime leaks draw).respond
      execution owner action valid⟩,
      (phaseApplication_seedOrder runtime leaks).respond execution owner action ordered, ?_⟩
    exact receiptResolution_rebase runtime leaks execution (execution.respond app owner action)
      sound (by cases action with | mk transmission => cases transmission <;> rfl)
      ((app).respond_receipts execution owner action)
      (fun coordinate => (phaseApplication_resolution runtime leaks coordinate).respond
        execution owner action draw valid ordered)
  environment execution next command invariant _selected reached := by
    obtain ⟨⟨draw, valid⟩, ordered, sound⟩ := invariant
    refine ⟨⟨draw, (phaseApplication_invariant runtime leaks draw).environmentStep
      execution next command valid reached⟩,
      (phaseApplication_seedOrder runtime leaks).environmentStep execution next command
        ordered reached, ?_⟩
    cases command with
    | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff ..).mp reached
      exact sound
    | activate owner =>
      obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ selected
      exact sound
    | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff ..).mp reached
      exact receiptResolution_includePending runtime leaks execution valid ordered sound id
    | application operation =>
      obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ selected
      exact receiptResolution_rebase runtime leaks execution _ sound rfl rfl
        (fun coordinate => (phaseApplication_resolution runtime leaks coordinate).environment
          execution.application operation state moved draw valid ordered)

/-- Actual accepting receipts certify their physical namespace resolution on
every initialized raw history, with no clearance or delivery-policy premise. -/
theorem bindingReceiptResolution_history (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) : BindingReceiptResolution runtime leaks control.execution :=
  ((bindingReceiptResolution_invariant runtime leaks scheduler).history _ horizon
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨⟨draw, (PhaseRuntimeState.initial_invariant plan draw).1⟩,
        PhaseRuntimeState.initial_ordered plan draw,
        (app).receiptsSound_initial _ _⟩) trace).2.2

private theorem receipt_payload {predicate : CommitAttemptPacket graph → Prop}
    (execution : (app).Execution) (sound : execution.ReceiptsSound app predicate)
    (id : MessageId Player) (accepted : (id, true) ∈ execution.receipts) :
    ∃ message ∈ execution.network.ledger, message.id = id ∧ predicate message.payload := by
  change List.Forall₂ _ _ _ at sound
  generalize execution.network.ledger = messages at sound ⊢
  generalize execution.receipts = receipts at sound accepted
  induction sound with
  | nil => cases accepted
  | @cons message receipt messages receipts related tail ih =>
    rcases List.mem_cons.mp accepted with same | later
    · cases same
      exact ⟨message, List.mem_cons_self, related.1.symm, related.2 rfl⟩
    · obtain ⟨found, member, named, valid⟩ := ih later
      exact ⟨found, List.mem_cons_of_mem _ member, named, valid⟩

/-- A true receipt in an actual raw history resolves the full original
coordinate, including when another owner has already failed. -/
theorem bindingAccepted_resolved (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (accepted : BindingAccepted runtime leaks coordinate owner control.execution) :
    coordinate.Resolved control.execution.application := by
  obtain ⟨message, input, _sender, attemptEq, named, receipt⟩ := accepted
  obtain ⟨actual, ledger, sameId, resolved⟩ := receipt_payload runtime leaks control.execution
    (bindingReceiptResolution_history runtime leaks plan inputs horizon scheduler trace)
      message.id receipt
  have identical := ((app).uniqueIds_history scheduler _ horizon control trace).inputs
    message input
  have same := identical.ledger actual ledger sameId
  subst actual
  simpa only [attemptEq] using resolved coordinate.event named

/-- A genuine ready request has not already received a true acceptance,
regardless of failures elsewhere in the current attempt. -/
theorem not_bindingAccepted_of_request (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : control.execution.application.SeedRequest owner coordinate) :
    ¬ BindingAccepted runtime leaks coordinate owner control.execution := by
  intro accepted
  exact (bindingAccepted_resolved runtime leaks plan inputs horizon scheduler trace coordinate
    owner accepted).not_request _ _ owner request

private theorem resolved_no_receipt_invariant (scheduler : (app).Scheduler)
    (coordinate : CommitAttemptEvent graph) (draw : graph.Inputs) :
    (app).ServiceInvariant scheduler (fun execution =>
      (execution.application.Invariant draw ∧ execution.application.Ordered ∧
        coordinate.Resolved execution.application) ∧
      execution.ReceiptsSound app (fun packet => ¬ (packet.attempt = coordinate.attempt ∧
        packet.packet.call.event? graph = some coordinate.event))) := by
  refine (app).receiptServiceInvariant
    (fun state => state.Invariant draw ∧ state.Ordered ∧ coordinate.Resolved state)
    (fun packet => ¬ (packet.attempt = coordinate.attempt ∧
      packet.packet.call.event? graph = some coordinate.event)) ?_ ?_ scheduler
  · constructor
    · intro state owner material valid
      exact ⟨(phaseApplication_invariant runtime leaks draw).submit state owner material valid.1,
        (phaseApplication_seedOrder runtime leaks).submit state owner material valid.2.1,
        (phaseApplication_resolution runtime leaks coordinate).submit state owner material
          draw valid.1 valid.2.1 valid.2.2⟩
    · intro state message next valid accepted
      exact ⟨(phaseApplication_invariant runtime leaks draw).handle state message next
          valid.1 accepted,
        (phaseApplication_seedOrder runtime leaks).handle state message next valid.2.1 accepted,
        (phaseApplication_resolution runtime leaks coordinate).handle state message next
          accepted draw valid.1 valid.2.1 valid.2.2⟩
    · intro state command next valid reached
      exact ⟨(phaseApplication_invariant runtime leaks draw).environment state command next
          valid.1 reached,
        (phaseApplication_seedOrder runtime leaks).environment state command next valid.2.1 reached,
        (phaseApplication_resolution runtime leaks coordinate).environment state command next
          reached draw valid.1 valid.2.1 valid.2.2⟩
  · intro state message next valid accepted ⟨same, named⟩
    apply PhaseRuntimeState.handle_event_unresolved runtime state next message coordinate.event
      named accepted
    simpa only [same] using valid.2.2

private theorem resolved_no_receipt_prefix (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (coordinate : CommitAttemptEvent graph) (draw : graph.Inputs)
    (start final : (app).Control)
    (startTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some start))
    (finalTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some final))
    (retained : TracePrefix startTrace finalTrace)
    (valid : start.execution.application.Invariant draw)
    (ordered : start.execution.application.Ordered)
    (resolved : coordinate.Resolved start.execution.application)
    (sound : start.execution.ReceiptsSound app (fun packet =>
      ¬ (packet.attempt = coordinate.attempt ∧
        packet.packet.call.event? graph = some coordinate.event))) (owner : Player) :
    ¬ BindingAccepted runtime leaks coordinate owner final.execution := by
  let invariant := resolved_no_receipt_invariant runtime leaks scheduler coordinate draw
  have along : ∀ {target} {targetTrace : ((app).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace target},
      TracePrefix startTrace targetTrace → ∃ current : (app).Control, target = some current ∧
        (current.execution.application.Invariant draw ∧ current.execution.application.Ordered ∧
          coordinate.Resolved current.execution.application) ∧
        current.execution.ReceiptsSound app (fun packet =>
          ¬ (packet.attempt = coordinate.attempt ∧
            packet.packet.call.event? graph = some coordinate.event)) := by
    intro target targetTrace kept
    induction kept with
    | refl => exact ⟨start, rfl, ⟨valid, ordered, resolved⟩, sound⟩
    | @extend source target earlier kept joint legal realized ih =>
      obtain ⟨current, rfl, native, receipts⟩ := ih
      have moved : target ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
          horizon scheduler (some current) joint).support := realized
      rcases current with ⟨remaining, actor, execution⟩
      cases actor with
      | some acting =>
        cases (PMF.mem_support_pure_iff ..).mp moved
        exact ⟨_, rfl, invariant.respond execution acting _ ⟨native, receipts⟩⟩
      | none =>
        cases remaining with
        | zero =>
          cases (PMF.mem_support_pure_iff ..).mp moved
          exact ⟨_, rfl, native, receipts⟩
        | succ remaining =>
          obtain ⟨command, selected, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
          obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨_, rfl, invariant.environment execution next command ⟨native, receipts⟩
            selected stepped⟩
  obtain ⟨current, stateEq, _native, finalSound⟩ := along retained
  cases Option.some.inj stateEq
  intro accepted
  obtain ⟨message, input, _sender, sameAttempt, named, receipt⟩ := accepted
  obtain ⟨actual, ledger, sameId, forbidden⟩ := receipt_payload runtime leaks final.execution
    finalSound message.id receipt
  have same := (((app).uniqueIds_history scheduler _ horizon final finalTrace).inputs
    message input).ledger actual ledger sameId
  subst actual
  exact forbidden ⟨sameAttempt, named⟩

/-- If packet inclusion protects this active owner, a newly excluded
successor must come from an actual environment application command. -/
theorem new_exclusion_application_command (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control) (joint : Player → Option (app).Action)
    (moved : some after ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) joint).support)
    (owner : Player) (active : owner ∉ before.execution.application.current.excluded)
    (excluded : owner ∈ after.execution.application.current.excluded)
    (preserves : ∀ message next, before.execution.application.handle runtime message = some next →
      owner ∉ next.current.excluded) :
    ∃ command, after.execution ∈
      (before.execution.environmentStep app (.application command)).support := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some acting =>
    cases (PMF.mem_support_pure_iff ..).mp moved
    generalize actionEq : (joint acting).getD ({ transmission := none } : (app).Action) = action
      at excluded
    rcases action with ⟨transmission⟩
    cases transmission <;> exact (active excluded).elim
  | none =>
    cases remaining with
    | zero =>
      cases (PMF.mem_support_pure_iff ..).mp moved
      exact (active excluded).elim
    | succ remaining =>
      obtain ⟨command, _selected, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨next, stepped, equal⟩ := PMF.support_map .. ▸ supported
      cases Option.some.inj equal
      cases command with
      | application operation => exact ⟨operation, stepped⟩
      | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at stepped
        cases (PMF.mem_support_pure_iff ..).mp stepped
        exact (active excluded).elim
      | activate acting =>
        obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ stepped
        obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ selected
        exact (active excluded).elim
      | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at stepped
        cases (PMF.mem_support_pure_iff ..).mp stepped
        change owner ∈ (execution.includePending app id).application.current.excluded at excluded
        unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
          at excluded
        cases found : execution.network.lookup id with
        | none =>
          simp only [found] at excluded
          exact (active excluded).elim
        | some message =>
          simp only [found] at excluded
          change owner ∈ ((execution.application.handle runtime message).getD
            execution.application).current.excluded at excluded
          cases handled : execution.application.handle runtime message with
          | none =>
            simp only [handled, Option.getD_none] at excluded
            exact (active excluded).elim
          | some next =>
            simp only [handled, Option.getD_some] at excluded
            exact (preserves message next handled excluded).elim

/-- The first actual exclusion of an active commitment owner identifies an
old physical event which cannot have an accepting receipt at any later
actual endpoint. Other owners may already be excluded, and the transition
may immediately archive or exhaust the original attempt. -/
theorem not_bindingAccepted_after_commitment_exclusion (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before after final : (app).Control)
    (beforeTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some before))
    (joint : Player → Option (app).Action)
    (legal : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Legal (some before) joint)
    (moved : some after ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) joint).support)
    (finalTrace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some final))
    (retained : TracePrefix (beforeTrace.extend joint legal moved) finalTrace)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (owner : Player)
    (active : owner ∉ before.execution.application.current.excluded)
    (excluded : owner ∈ after.execution.application.current.excluded) :
    ∃ event ∈ phase.events,
      before.execution.application.SeedRequest owner
        ⟨before.execution.application.attempt, event⟩ ∧
      ¬ BindingAccepted runtime leaks ⟨before.execution.application.attempt, event⟩ owner
        final.execution := by
  classical
  obtain ⟨command, stepped⟩ := new_exclusion_application_command runtime leaks plan inputs horizon
    scheduler before after joint moved owner active excluded (by
      intro message next handled
      have same := PhaseRuntimeState.handle_commitment_phase_excluded runtime
        before.execution.application next phase installed commitment message handled
      exact fun chosen => active (same ▸ chosen))
  obtain ⟨updated, selected, equal⟩ := PMF.support_map .. ▸ stepped
  obtain ⟨native, supported, stateEq⟩ := PMF.support_map .. ▸ selected
  have afterApplication : after.execution.application = native := by
    exact (congrArg (fun execution : (app).Execution => execution.application) equal).symm.trans
      (congrArg (fun execution : (app).Execution => execution.application) stateEq).symm
  obtain ⟨event, completedNative, _commandEq, inside, request, _nativeStep, completed,
    normalized⟩ :=
    PhaseRuntimeState.environment_new_exclusion_request runtime before.execution.application native
      phase installed command supported owner active
        (by simpa only [afterApplication] using excluded)
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    beforeTrace
  have ordered := (phaseApplication_seedOrder runtime leaks).history
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler (by
      intro state member
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_ordered plan input) beforeTrace
  have afterReceipts : after.execution.receipts = before.execution.receipts := by
    exact (congrArg (fun execution : (app).Execution => execution.receipts) equal).symm.trans
      (congrArg (fun execution : (app).Execution => execution.receipts) stateEq).symm
  have afterLedger : after.execution.network.ledger = before.execution.network.ledger := by
    exact (congrArg (fun execution : (app).Execution => execution.network.ledger)
      equal).symm.trans
      (congrArg (fun execution : (app).Execution => execution.network.ledger) stateEq).symm
  have progress := (phaseApplication_namespace_progress runtime leaks).environment
    before.execution.application command native supported ordered
  have resolved :
      (⟨before.execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
        after.execution.application := by
    rw [afterApplication]
    apply CommitAttemptEvent.Resolved.of_step _ before.execution.application native rfl progress
    rw [normalized]
    simpa only [PhaseRuntimeState.normalize, PhaseRuntimeState.attempt] using
      PhaseRuntimeState.settle_resolves before.execution.application.phases
        before.execution.application.generation before.execution.application.entry
        (before.execution.application.current.environmentResult (.expire event) completedNative)
        before.execution.application.retired ordered event completed
  have sound :=
    bindingReceiptResolution_history runtime leaks plan inputs horizon scheduler beforeTrace
  have noReceipt : after.execution.ReceiptsSound app (fun packet =>
      ¬ (packet.attempt = before.execution.application.attempt ∧
        packet.packet.call.event? graph = some event)) := by
    unfold ReactiveApplication.Execution.ReceiptsSound
    rw [afterReceipts, afterLedger]
    apply sound.imp
    intro message receipt related
    refine ⟨related.1, ?_⟩
    intro accepted ⟨same, named⟩
    have resolved := related.2 accepted event named
    have atCoordinate : (⟨before.execution.application.attempt, event⟩ :
        CommitAttemptEvent graph).Resolved before.execution.application := by
      simpa only [same] using resolved
    exact atCoordinate.not_request _ _ owner request
  refine ⟨event, inside, request, ?_⟩
  apply resolved_no_receipt_prefix runtime leaks plan inputs horizon scheduler
    ⟨before.execution.application.attempt, event⟩ draw after final
      (beforeTrace.extend joint legal moved) finalTrace retained
  · rw [afterApplication]
    exact (phaseApplication_invariant runtime leaks draw).environment
      before.execution.application command native valid supported
  · rw [afterApplication]
    exact (phaseApplication_seedOrder runtime leaks).environment
      before.execution.application command native ordered supported
  · exact resolved
  · exact noReceipt

/-- Expiring a genuine request makes later acceptance impossible, even after
rollback or exhaustion. This uses the original receipt ledger and the actual
reactive rounds, without a globally clear state or an assumed delivery event. -/
theorem not_bindingAccepted_runRounds_after_expire (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : control.execution.application.SeedRequest owner coordinate)
    (due : runtime.deadline coordinate.event ≤ control.execution.application.current.native.clock -
      (control.execution.application.current.native.activatedAt coordinate.event).getD
        control.execution.application.current.native.clock)
    (expired : (app).Execution)
    (expiry : expired ∈ (control.execution.environmentStep app
      (.application (.expire coordinate.event))).support)
    (players : Player → (app).Policy) (count : Nat) (final : (app).Execution)
    (reached : final ∈ ((app).runRounds scheduler players count expired).support) :
    ¬ BindingAccepted runtime leaks coordinate owner final := by
  classical
  obtain ⟨draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler trace
  have ordered := (phaseApplication_seedOrder runtime leaks).history
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler (by
      intro state supported
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input) trace
  have sound := bindingReceiptResolution_history runtime leaks plan inputs horizon scheduler trace
  have old : control.execution.ReceiptsSound app (fun packet =>
      ¬ (packet.attempt = coordinate.attempt ∧
        packet.packet.call.event? graph = some coordinate.event)) := by
    apply sound.imp
    intro message receipt related
    refine ⟨related.1, ?_⟩
    intro accepted ⟨same, named⟩
    have resolved := related.2 accepted coordinate.event named
    have atCoordinate : coordinate.Resolved control.execution.application := by
      simpa only [same] using resolved
    exact atCoordinate.not_request _ _ owner request
  obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ expiry
  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ selected
  let current : (app).Execution :=
    { control.execution with
      application := next
      environmentRecall := control.execution.environmentRecall ++
        [⟨control.execution.observeEnvironment app, .application (.expire coordinate.event)⟩] }
  have continued : final ∈ ((app).runRounds scheduler players count current).support := reached
  have progress := (phaseApplication_namespace_progress runtime leaks).environment
    control.execution.application (.expire coordinate.event) next moved ordered
  have resolved := CommitAttemptEvent.Resolved.of_step coordinate control.execution.application
    next request.1 progress (control.execution.application.expire_resolves_of_request runtime next
      valid ordered request due moved)
  have after := (resolved_no_receipt_invariant runtime leaks scheduler coordinate draw).runRounds
    players count current final
      ⟨⟨(phaseApplication_invariant runtime leaks draw).environment control.execution.application
        (.expire coordinate.event) next valid moved,
        (phaseApplication_seedOrder runtime leaks).environment control.execution.application
          (.expire coordinate.event) next ordered moved, resolved⟩, old⟩ continued
  have identity := ((app).messageIdentityInvariant scheduler).runRounds players count current final
    (((app).messageIdentityInvariant scheduler).history _ horizon
      (fun _ _ => ⟨MessageNetwork.SerialsBeforeNext.empty, MessageNetwork.UniqueIds.empty⟩)
        trace) continued
  intro accepted
  obtain ⟨message, input, _sender, sameAttempt, named, receipt⟩ := accepted
  obtain ⟨actual, ledger, sameId, forbidden⟩ := receipt_payload runtime leaks final after.2
    message.id receipt
  have same := (identity.2.inputs message input).ledger actual ledger sameId
  subst actual
  exact forbidden ⟨sameAttempt, named⟩

end PhaseService
end Vegas.EventGraphRuntime

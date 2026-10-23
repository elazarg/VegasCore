/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPublicationWord
import Vegas.Game.ReservedEpochPublicationOwnerChain
import Vegas.Game.PhaseProposalReplayCoverage

/-! # Canonical source comparison at an actual publication boundary -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The literal closing primitive and its real phase drain are reachable
from the SAME initialized native draw. No normalized successor replaces them. -/
theorem publication_closing_image_reachable {graph : Vegas.EventGraph Player L}
    (runtime : EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (after : (phaseApplication runtime leaks).Execution) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution after raw)
    (phase : RuntimePhase graph) :
    ∃ draw, (phase.drain raw).native.config.Reachable draw := by
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    trace
  refine ⟨draw, phase.drain_reachable raw ?_⟩
  rcases effect with included | applied
  · obtain ⟨_id, message, native, _found, _actual, handled, rfl⟩ := included
    exact (handle_invariant runtime _ native ⟨message.id, message.payload.packet.call⟩
      valid.active handled).reachable
  · obtain ⟨command, native, _actual, supported, rfl⟩ := applied
    exact (environmentStep_invariant runtime _ native command valid.active supported).reachable

omit [DecidableEq Player] in
private theorem publication_false_value {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {kind : EventField Player L}
    {owner : Player} {payload : L.Ty} (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (node : EventCode layout kind)
    (publication : kind = .publication payload)
    (code : cast (congrArg (EventCode layout) publication) node =
      .resolve owner payload binding checks) (store : Store layout)
    (available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (store field).isSome = true)
    (action : kind.Action) (withheld : cast (congrArg EventField.Action publication) action = false)
    (law : PMF kind.Value) (value : kind.Value)
    (evaluated : node.eval? action store = some law) (supported : value ∈ law.support) :
    cast (congrArg EventField.Value publication) value = .failure := by
  cases publication
  simp only [cast_eq] at code withheld ⊢
  subst node
  subst action
  rw [EventCode.resolve_eval?, EventCode.resolveOutput?_false_eq_failure binding checks store
    available] at evaluated
  have pure : law = PMF.pure (.failure : PublicationResult (L.Val payload)) :=
    (Option.some.inj evaluated).symm
  rwa [pure, PMF.mem_support_pure_iff] at supported

omit [DecidableEq Player] in
/-- A literal FALSE action at a reachable publication is an actual public
failure. The argument reads its original recorded evaluator output; a TRUE
guard rejection is never inverted into this case. -/
theorem publication_recorded_false_failure {graph : Vegas.EventGraph Player L}
    (native : EventGraphRuntime.State graph) {inputs : graph.Inputs}
    (reachable : native.config.Reachable inputs) (event : graph.EventId)
    (owner : Player) (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (publication : graph.outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode graph.layout) publication) (graph.nodes event) =
      .resolve owner payload binding checks)
    (action : (graph.outputLayout event).Action)
    (recorded : (⟨event, action⟩ : graph.Completion) ∈ native.config.history)
    (withheld : cast (congrArg EventField.Action publication) action = false) :
    native.PublicFailure event := by
  classical
  have completed := (native.config.history_exact event).mp
    (List.mem_map.mpr ⟨⟨event, action⟩, recorded, rfl⟩)
  have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (native.config.store field).isSome = true := by
    intro field read
    have actualRead : field ∈ (graph.nodes event).readFields := by
      rw [← EventCode.readFields_cast publication (graph.nodes event), code]
      exact read
    cases field with
    | inl input => rfl
    | inr producer =>
        exact (native.config.output_available producer).mpr
          (native.config.cut.predecessor_closed completed
            (graph.reads_available event (.inr producer) actualRead))
  obtain ⟨law, value, stored, evaluated, supported⟩ :=
    reachable.history_output_semantics ⟨event, action⟩ recorded
  have failed := publication_false_value binding checks (graph.nodes event) publication code
    native.config.store available action withheld law value evaluated supported
  have read : (⟨.inr event, publication⟩ : FieldRef graph.layout (.publication payload)).get?
      native.config.store = some (.failure : PublicationResult (L.Val payload)) := by
    change cast (congrArg (fun kind => Option kind.Value) publication)
      (native.config.outputs event) = _
    rw [stored]
    have castSome : ∀ {first second : EventField Player L} (equal : first = second)
        (value : first.Value), cast (congrArg (fun kind => Option kind.Value) equal) (some value) =
          some (cast (congrArg EventField.Value equal) value) := by
      intro first second equal value
      cases equal
      rfl
    rw [castSome publication value, failed]
  exact (publication_failure_iff_read native event binding checks publication code .failure
    read).mpr rfl

omit [DecidableEq Player] in
/-- Survival in the original phase image forces TRUE disclosure at every
owned publication row. This follows from native failure coverage and the
literal action, independently of policy, service timing, and guard inversion. -/
theorem publication_survivor_disclosure_true {graph : Vegas.EventGraph Player L}
    (image : RecoveryState graph) {inputs : graph.Inputs}
    (reachable : image.native.config.Reachable inputs) (coverage : image.FailureCoverage)
    (event : graph.EventId) (owner : Player) (acting : graph.actor? event = some owner)
    (survives : owner ∉ image.excluded)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (publication : graph.outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode graph.layout) publication) (graph.nodes event) =
      .resolve owner payload binding checks)
    (action : (graph.outputLayout event).Action)
    (recorded : (⟨event, action⟩ : graph.Completion) ∈ image.native.config.history) :
    cast (congrArg EventField.Action publication) action = true := by
  classical
  by_contra silent
  have withheld := Bool.eq_false_of_not_eq_true silent
  have failed := publication_recorded_false_failure image.native reachable event owner payload
    binding checks publication code action recorded withheld
  exact survives (coverage.covered event owner acting failed)

/-- A source-active unfinished row also has an active owner at the actual
anchor. Any already physical exclusion has an earlier owned failure, so it
would already occur in the canonical prefix scan. Later physical exclusions
are not equated with the current source exclusion set. -/
theorem publication_unfinished_source_active_anchor_active
    {graph : Vegas.EventGraph Player L} [Fintype Player]
    (ordered : graph.RevealRelaxedOrdered) (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (kind : phase.kind = .reveal)
    (record : SuffixExclusionRecord phase.low state.entry.excluded state.current)
    (within : state.current.native.config.cut.Within phase.low phase.high)
    (native : EventGraphRuntime.State graph) (kept : KeepsStore state.current.native native)
    (event : graph.EventId) (owner : Player) (acting : graph.actor? event = some owner)
    (unfinished : event ∉ state.current.native.config.cut.completed)
    (inherited : owner ∉ state.entry.excluded)
    (scan : owner ∉ native.failureOwnersBefore event.val) : owner ∉ state.current.excluded := by
  classical
  intro excluded
  rcases (record.excluded owner).mp excluded with old | ⟨prior, lower, priorActor, failed⟩
  · exact inherited old
  · have earlier : prior.val < event.val := by
      by_contra notEarlier
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt notEarlier) with equal | later
      · have same : prior = event := Fin.ext equal.symm
        exact unfinished (same ▸ failed.completed)
      · have predecessor : event ∈ graph.order.predecessors prior := ordered prior event
          ((mem_barrierOrder graph.outputLayout event prior).mpr ⟨later,
            EventCode.barrierRelated_of_visible (graph.nodes prior) owner priorActor _
              (graph.nodes event) (EventCode.output_visible_of_actor (graph.nodes event) owner
                acting)⟩)
          (IndependentReveals.not_of_actor_eq (acting.trans priorActor.symm))
        exact unfinished (state.current.native.config.cut.predecessor_closed failed.completed
          predecessor)
    obtain ⟨payload, publication⟩ := kind ▸ phase.fields prior lower
      (within.2 prior failed.completed)
    have retained := (PhaseProposal.publication_failure_kept kept prior payload publication
      failed.completed).mpr failed
    exact scan (Finset.mem_filter.mpr ⟨Finset.mem_univ owner,
      ⟨prior, earlier, priorActor, retained⟩⟩)

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs

/-- Every fresh source-active proper opening row has physical disclosure TRUE.
Guard acceptance is decided separately by the actual deterministic source step. -/
theorem phaseProposalUnflagged_fresh_opening_disclosure
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor⟩))
    (closing ending : (app).Control)
    (closingTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some closing))
    (joint : Player → Option (app).Action)
    (legal : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some closing) joint)
    (realized : some ending ∈ ((app).transition ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some closing) joint).support)
    (fromStart : TracePrefix trace closingTrace)
    (same : closing.execution.application.attempt = anchor.application.attempt)
    (changed : ending.execution.application.attempt ≠ anchor.application.attempt)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution ending.execution raw)
    (coverage : (phase.drain raw).FailureCoverage)
    (excludedEq : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (owner : Player)
    (acting : (graph).actor? event = some owner)
    (active : owner ∉ anchor.application.current.excluded)
    (payload : L.Ty) (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (locked : binding.get? anchor.application.current.native.config.store = some (.success value))
    (scan : owner ∉ (phase.drain raw).native.failureOwnersBefore event.val)
    (action : ((graph).outputLayout event).Action)
    (recorded : (⟨event, action⟩ : (graph).Completion) ∈ (phase.drain raw).native.config.history)
    (fresh : ¬ (anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩ ∧
      PhaseCount.ResponseRecorded runtime leaks owner ⟨anchor.application.attempt, event⟩
        (anchor.recall owner))) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let ordinary := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let players := ReactiveApplication.anchoredPolicy anchor ordinary
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let E := (menu).protocol initial horizon scheduler
    let N := (menu).information initial horizon scheduler
    let stopped := fun history : E.History => match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (N.runBehavioralUntil ((menu).bounded _ horizon scheduler).wellFoundedHistories
      profile stopped ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      final.state = some ending →
      TracePrefix (closingTrace.extend joint legal realized) final.trace →
        cast (congrArg EventField.Action outputEq) action = true := by
  classical
  intro initial horizon scheduler ordinary players profile E N stopped final supported finalState
    closedKept
  by_cases disclosed : cast (congrArg EventField.Action outputEq) action = true
  · exact disclosed
  · have withheld : cast (congrArg EventField.Action outputEq) action = false :=
      Bool.eq_false_of_not_eq_true disclosed
    obtain ⟨_draw, reachable⟩ := publication_closing_image_reachable runtime leaks plan inputs
      horizon
      scheduler closing ((menu).toRawTrace initial horizon scheduler closingTrace)
        ending.execution raw effect phase
    have failed := publication_recorded_false_failure (phase.drain raw).native reachable event
      owner payload binding checks outputEq codeEq action recorded withheld
    have silent : PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = false :=
      (PhaseProposal.publicationDiscloses_cast outputEq action).symm.trans withheld
    have old := phaseProposalUnflagged_stopped_false_opening_old_request setup mode runtime leaks
      bounds plan coveredValues maximal ordered values tape activationGap processingGap gaps margin
        remaining anchor trace closing ending closingTrace joint legal realized fromStart same
          changed phase installed kind raw effect coverage excludedEq event inside owner acting
            active payload binding checks outputEq codeEq node value locked failed scan action
              recorded silent
              final (by
                convert supported using 1
                congr 2
                funext history
                dsimp only [stopped]
                cases history.state <;> rfl) finalState closedKept
    exact (fresh old).elim

end Vegas

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- At any initially unresolved publication row, physical receipt is exactly
the recorded action Boolean, including truthful openings rejected by their guard. -/
theorem publication_unresolved_receipt_iff_recorded (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (start before ending : (app).Control)
    (startTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some start))
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (physicalJoint : Player → Option (app).Action)
    (legal : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Legal
        (some before) physicalJoint)
    (realized : some ending ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) physicalJoint).support)
    (fromStart : TracePrefix startTrace prior)
    (same : start.execution.application.attempt = before.execution.application.attempt)
    (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (event : graph.EventId)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (inside : event ∈ phase.events) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (ordered : graph.RevealRelaxedOrdered)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (action : (graph.outputLayout event).Action)
    (recorded : (⟨event, action⟩ : graph.Completion) ∈ (phase.drain raw).native.config.history)
    (owner : Player)
    (unresolved : ¬ (⟨start.execution.application.attempt, event⟩ :
      CommitAttemptEvent graph).Resolved start.execution.application)
    (owned : graph.actor? event = some owner)
 :
    PhaseService.BindingAccepted runtime leaks ⟨start.execution.application.attempt, event⟩
      owner ending.execution ↔ cast (congrArg EventField.Action publication) action = true := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let closed := prior.extend physicalJoint legal realized
  have rawStart := menu.toRawTrace initial horizon scheduler startTrace
  have rawClosed := menu.toRawTrace initial horizon scheduler closed
  have closedKept : TracePrefix startTrace closed := .extend fromStart physicalJoint legal realized
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) closed
  have disclosed := PhaseProposal.publicationDiscloses_cast publication action
  constructor
  · rintro ⟨message, input, sender, address, named, receipt⟩
    have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
    have opening : ∃ candidate value,
        message.payload.packet.call = .opening event candidate value := by
      cases call : message.payload.packet.call with
      | malformed raw => rw [call] at named; cases named
      | commitment other candidate =>
          have sameEvent : other = event := Option.some.inj (by
            simpa only [call, Payload.event?] using named)
          subst other
          simp only [CountCallCorrect, PhaseCount.nativeMessage, call, bindingOwnedBy, publication,
            Bool.false_eq_true, false_and] at correct
      | opening other candidate value =>
          have sameEvent : other = event := Option.some.inj (by
            simpa only [call, Payload.event?] using named)
          subst other
          exact ⟨candidate, value, rfl⟩
    obtain ⟨candidate, value, call⟩ := opening
    have absent : (message.id, true) ∉ start.execution.receipts := by
      intro old
      have identifiers := (app).receipt_identifiers_history initial horizon scheduler start rawStart
      have oldId : message.id ∈ start.execution.network.ledger.map Message.id := by
        rw [← identifiers]
        exact List.mem_map.mpr ⟨(message.id, true), old, rfl⟩
      obtain ⟨other, ledger, otherId⟩ := List.mem_map.mp oldId
      have oldInput := (app).ledger_subset_inputs_history initial horizon scheduler start rawStart
        ledger
      have finalInput := input_mem_prefix runtime leaks menu initial horizon scheduler start ending
        startTrace closed closedKept other oldInput
      have identity : other = message := (app).input_identifier_injective_history initial horizon
        scheduler ending rawClosed other message finalInput input otherId
      subst other
      exact unresolved (PhaseService.bindingAccepted_resolved runtime leaks plan inputs horizon
        scheduler rawStart ⟨start.execution.application.attempt, event⟩ owner
          ⟨message, oldInput, sender, address, named, old⟩)
    have physical := original_opening_receipt_iff_recorded runtime leaks bounds plan inputs horizon
      scheduler start before ending startTrace prior physicalJoint legal realized fromStart same raw
        effect message input event candidate value call address absent phase installed inside
          payload publication ordered changed
    obtain ⟨otherAction, otherRecorded, otherDisclosed⟩ := physical.mp receipt
    have identity : (⟨event, otherAction⟩ : graph.Completion) = ⟨event, action⟩ :=
      List.inj_on_of_nodup_map (phase.drain raw).native.config.history_nodup otherRecorded recorded
        rfl
    cases identity
    exact disclosed.trans otherDisclosed
  · intro chosen
    obtain ⟨message, candidate, value, input, address, call, receipt⟩ :=
      closing_disclosure_has_receipt runtime leaks bounds plan ordered inputs horizon scheduler
        before prior ending.execution raw changed effect phase installed event inside payload
          publication action recorded chosen
    have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
    have actualOwner := countCallCorrect_owned_event _ (PhaseCount.nativeMessage message)
      permitted.2.1 (by
        change Payload.event? graph message.payload.packet.call = some event
        rw [call]
        rfl)
    have sender : message.sender = owner := Option.some.inj (actualOwner.symm.trans owned)
    exact ⟨message, input, sender, address.trans same.symm, by rw [call]; rfl, receipt⟩


end Vegas.EventGraphRuntime.ReservedEpoch

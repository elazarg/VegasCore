/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseObservableDomainWord
import Vegas.Game.PhaseCountServiceTableGood
import Vegas.Game.CommitRecoveryDomainPlan
import Vegas.Pending.PhaseReadyBindingDeclaration
import Vegas.Pending.PhaseProposalEmissionOrder

/-! # Original domain declarations in the counted service experiment

A non-RAW sending atom retains the exact domain-table answer, independently
of its physical fresh slot. The original domain table is fixed throughout;
neither a later binding request nor a retry initializes another source draw.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- The immutable preparation at each original static binding occurrence,
read from its owner's permanent recall. Physical SEND interleaving and later
restoration do not supply the indexing of this word. -/
def phaseStaticBindingWord (attempt : CommitAttemptId)
    (past : List (phaseApplication runtime leaks).PlayerEntry) (event : graph.EventId) :
    Option (Option (Raw L)) :=
  (past.filterMap fun entry =>
    if entry.beforeView.application.2.attempt = attempt then
      match entry.action.transmission with
      | none => none
      | some material => match material.call.packet with
        | .commitment actual _ => if actual = event then some material.call.opening else none
        | _ => none
    else none).head?

/-- A selected static declaration is an actual remembered SEND, with its
original attempt and submitted preparation; it is not a latent source draw. -/
theorem phaseStaticBindingWord_origin (attempt : CommitAttemptId)
    (past : List (phaseApplication runtime leaks).PlayerEntry) (event : graph.EventId)
    (opening : Option (Raw L)) (selected : phaseStaticBindingWord runtime leaks attempt past event =
      some opening) :
    ∃ entry ∈ past, ∃ (material : WitnessedSubmission graph) (candidate : Handle graph),
      entry.beforeView.application.2.attempt = attempt ∧
      entry.action.transmission = some material ∧
      material.call.packet = .commitment event candidate ∧ material.call.opening = opening := by
  unfold phaseStaticBindingWord at selected
  obtain ⟨tail, head⟩ := List.head?_eq_some_iff.mp selected
  have present : opening ∈ past.filterMap (fun entry =>
      if entry.beforeView.application.2.attempt = attempt then
        match entry.action.transmission with
        | none => none
        | some material => match material.call.packet with
          | .commitment actual _ => if actual = event then some material.call.opening else none
          | _ => none
      else none) := by
    rw [head]
    exact List.mem_cons_self
  obtain ⟨entry, recorded, decoded⟩ := List.mem_filterMap.mp present
  split at decoded
  · rename_i tag
    split at decoded
    · cases decoded
    · rename_i material sent
      split at decoded
      · rename_i actual candidate named
        split at decoded
        · rename_i same
          subst actual
          exact ⟨entry, recorded, material, candidate, tag, sent, named,
            Option.some.inj decoded⟩
        · cases decoded
      · cases decoded
  · cases decoded

/-- Every actual remembered addressed SEND makes its static declaration
available, including at an endpoint that restored the native store. -/
theorem phaseStaticBindingWord_present (attempt : CommitAttemptId)
    (past : List (phaseApplication runtime leaks).PlayerEntry) (event : graph.EventId)
    (entry : (phaseApplication runtime leaks).PlayerEntry) (recorded : entry ∈ past)
    (material : WitnessedSubmission graph) (candidate : Handle graph)
    (tag : entry.beforeView.application.2.attempt = attempt)
    (sent : entry.action.transmission = some material)
    (named : material.call.packet = .commitment event candidate) :
    ∃ opening, phaseStaticBindingWord runtime leaks attempt past event = some opening := by
  have present : material.call.opening ∈ past.filterMap (fun entry =>
      if entry.beforeView.application.2.attempt = attempt then
        match entry.action.transmission with
        | none => none
        | some material => match material.call.packet with
          | .commitment actual _ => if actual = event then some material.call.opening else none
          | _ => none
      else none) := List.mem_filterMap.mpr ⟨entry, recorded, by simp only [tag, sent, named,
        ↓reduceIte]⟩
  unfold phaseStaticBindingWord
  generalize entriesEq : past.filterMap _ = entries at present ⊢
  cases entries with
  | nil => cases present
  | cons opening tail => exact ⟨opening, rfl⟩

open Classical in
/-- Static original binding occurrences belonging to the initially active
foreign owners, read from permanent recall rather than the restored store. -/
def phaseForeignStaticBindingWord (start : (phaseApplication runtime leaks).Control)
    (phase : RuntimePhase graph) (focal : Player)
    (final : (phaseApplication runtime leaks).Control) :
    Player → graph.EventId → Option (Option (Raw L)) :=
  fun owner event =>
    if owner ≠ focal ∧ owner ∉ start.execution.application.current.excluded ∧
        event ∈ phase.events ∧ graph.actor? event = some owner then
      phaseStaticBindingWord runtime leaks start.execution.application.attempt
        (final.execution.recall owner) event
    else none

/-- A true receipt for an original binding recovers its immutable remembered
commitment even after normalization retired that attempt. No current native
accepted handle or current-namespace equality is required. -/
theorem phase_bindingAccepted_declaration [Fintype Player] (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (attempt : CommitAttemptId) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (accepted : PhaseService.BindingAccepted runtime leaks ⟨attempt, event⟩ owner
      control.execution) :
    ∃ entry ∈ control.execution.recall owner, ∃ (material : WitnessedSubmission graph)
      (candidate : Handle graph), entry.beforeView.application.2.attempt = attempt ∧
      entry.action.transmission = some material ∧
      material.call.packet = .commitment event candidate := by
  classical
  obtain ⟨message, input, sender, tag, named, _received⟩ := accepted
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    (inputs.map (PhaseRuntimeState.initial plan)) horizon
    (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
  have called : ∃ candidate, message.payload.packet.call = .commitment event candidate := by
    cases call : message.payload.packet.call with
    | malformed bytes =>
        simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
    | commitment actual candidate =>
        have same : actual = event := Option.some.inj (by simpa only [call, Payload.event?]
          using named)
        subst actual
        exact ⟨candidate, rfl⟩
    | opening actual candidate value =>
        have same : actual = event := Option.some.inj (by simpa only [call, Payload.event?]
          using named)
        subst actual
        simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
        cases node : nodeView graph event with
        | bind actor ty kind code => simp only [node, and_false] at correct
        | resolve actor ty bound checks kind code => cases kind.symm.trans binding
        | sample ty law kind code => cases kind.symm.trans binding
  obtain ⟨candidate, call⟩ := called
  obtain ⟨entry, retained, material, transmitted, emitted, state, known, packet⟩ :=
    ((phaseApplication runtime leaks).history_provenance _ horizon scheduler raw).inputs
      message input
  rw [sender] at retained
  have actualTag := phase_recalled_emission_attempt runtime leaks _ horizon scheduler raw owner
    entry retained message emitted
  have exactCall := phase_emit_call state message.sender known material
  change state.emit message.sender known material = message.payload at packet
  exact ⟨entry, retained, material, candidate, actualTag.symm.trans tag, transmitted,
    exactCall.symm.trans ((congrArg (fun output => output.packet.call) packet).trans call)⟩

private theorem same_attempt_metadata :
    (phaseApplication runtime leaks).StepRelation (fun before after => before.Ordered →
      before.attempt = after.attempt →
      (after.phases, after.retired) = (before.phases, before.retired)) where
  refl _ _ _ := rfl
  submit _ _ _ _ _ := rfl
  handle state message next accepted ordered same := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have settled := PhaseRuntimeState.settle_of_same_namespace
        state.phases state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native) state.retired ordered
        same
      have archived := congrArg (fun state => (state.phases, state.retired)) settled
      exact archived
    · cases accepted
  environment state command next reached ordered same := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      have settled := PhaseRuntimeState.settle_of_same_namespace
        state.phases state.generation state.entry (state.current.environmentResult command native)
        state.retired ordered same
      have archived := congrArg (fun state => (state.phases, state.retired)) settled
      exact archived
    · cases (PMF.mem_support_pure_iff ..).mp reached
      rfl

/-- An actual prefix that retains its original attempt keeps both its
installed descriptors and its archived attempts. Namespace monotonicity
rules out an intervening reset. -/
theorem phase_attempt_metadata_of_prefix
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace) (ordered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    (before.execution.application.phases, before.execution.application.retired) =
      (after.execution.application.phases, after.execution.application.retired) := by
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix prior targetTrace → ∃ next : (phaseApplication runtime leaks).Control,
        target = some next ∧ next.execution.application.Ordered ∧
        (before.execution.application.attempt = next.execution.application.attempt →
          (next.execution.application.phases, next.execution.application.retired) =
            (before.execution.application.phases, before.execution.application.retired)) := by
    intro target targetTrace kept
    induction kept with
    | refl => exact ⟨before, rfl, ordered, fun _ => rfl⟩
    | @extend source target earlier kept joint legal reached ih =>
        obtain ⟨middle, rfl, middleOrdered, previous⟩ := ih
        have realized : target ∈ ((phaseApplication runtime leaks).transition initial horizon
            scheduler (some middle) joint).support := reached
        obtain ⟨next, rfl, _recalled⟩ := (phaseApplication runtime leaks).transition_recall_prefix
          initial horizon scheduler middle target joint realized
        have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
          scheduler initialized (some middle) (some next) joint middleOrdered realized
        refine ⟨next, rfl, nextOrdered, ?_⟩
        intro finalSame
        have lower := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
          horizon scheduler before middle prior earlier kept ordered
        have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
          horizon scheduler middle next joint realized middleOrdered
        have intermediate : before.execution.application.attempt =
            middle.execution.application.attempt := by
          have generation := congrArg CommitAttemptId.generation finalSame
          have phase := congrArg CommitAttemptId.phase finalSame
          cases first : before.execution.application.attempt with
          | mk firstPhase firstGeneration =>
              cases second : middle.execution.application.attempt with
              | mk secondPhase secondGeneration =>
                  simp only [first, second] at lower progress generation phase ⊢
                  congr 1 <;> omega
        exact ((same_attempt_metadata runtime leaks).transition initial horizon scheduler middle
          next joint realized middleOrdered (intermediate.symm.trans finalSame)).trans
            (previous intermediate)
  obtain ⟨next, equality, _ordered, result⟩ := along retained
  cases Option.some.inj equality
  exact (result same).symm

/-- An emitted binding has no gap in its owner's earlier static binding
prefix. Every earlier row in the same attempt already has an actual emitted
packet, including when another owner was excluded before this attempt. -/
theorem phase_recorded_binding_earlier_output [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (ordered : graph.RevealRelaxedOrdered) (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (owner : Player) (entry : (phaseApplication runtime leaks).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (event : graph.EventId) (candidate : Handle graph)
    (named : material.call.packet = .commitment event candidate)
    (sameAttempt : entry.beforeView.application.2.attempt = control.execution.application.attempt)
    (payload : L.Ty) (binding : graph.outputLayout event = .binding owner payload)
    (earlier : graph.EventId) (priorPayload : L.Ty)
    (priorBinding : graph.outputLayout earlier = .binding owner priorPayload)
    (inside : earlier ∈ phase.events) (rank : earlier.val < event.val) :
    ∃ (priorCandidate : Handle graph) (message : Message Player (CommitAttemptPacket graph)),
      message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall owner) ∧
      message.payload.attempt = control.execution.application.attempt ∧
      message.payload.packet.call = .commitment earlier priorCandidate := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨before, prior, kept, _acting, viewed, request⟩ :=
    phase_recorded_binding_request runtime leaks bounds plan inputs horizon ordered scheduler
      trace owner entry recorded material transmitted event candidate named
  have same : before.execution.application.attempt = control.execution.application.attempt := by
    rw [viewed] at sameAttempt
    exact sameAttempt
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have raw := menu.toRawTrace initial horizon scheduler prior
  have beforeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    scheduler initialized raw
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler before control prior trace kept beforeOrdered same
  have beforeInstalled : before.execution.application.phases.head? = some phase :=
    (congrArg (fun pair => pair.1.head?) metadata).trans installed
  obtain ⟨priorCandidate, owned, accepted, _read⟩ := phase_ready_earlier_binding_read runtime leaks
    bounds plan inputs horizon scheduler prior ordered phase beforeInstalled owner event payload
      binding request.2.2.1 request.2.2.2.2 earlier priorPayload priorBinding inside rank
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  have lower := ((phase.mem_events earlier).mp inside).1
  have address : before.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, beforeInstalled, Option.map_some, Option.getD_some]
  rcases stamped earlier priorCandidate accepted with old | ⟨message, member, _, packet, attempt⟩
  · rw [address] at old
    omega
  · rw [owned] at member
    obtain ⟨recalled, remembered, emitted⟩ := List.mem_filterMap.mp member
    have retainedRecall := (phaseApplication runtime leaks).reaches_recall_prefix initial horizon
      scheduler (menu.reaches_raw initial horizon scheduler kept.reachesWithin)
        before control rfl rfl owner
    exact ⟨priorCandidate, message,
      List.mem_filterMap.mpr ⟨recalled, retainedRecall.subset remembered, emitted⟩,
      attempt.trans same, packet⟩

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

private theorem encoder_sending_result (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (result : PublicationResult (L.Val payload)) (selected : values past view = PMF.pure result)
    (action : (phaseApplication runtime leaks).Action)
    (supported : action ∈ (bindingResultEncoder runtime leaks bounds owner event payload values
      slotWeight slotNonnegative slotBounded past view).support)
    (sending : action ≠ ⟨none⟩) :
    ∃ serial, action = phaseBindingResponse runtime leaks owner event payload result serial := by
  classical
  have decode (serial : Nat)
      (present : action ∈ ((values past view).map
        (phaseBindingResponse runtime leaks owner event payload · serial)).support) :
      ∃ serial, action = phaseBindingResponse runtime leaks owner event payload result serial := by
    simp only [selected, PMF.pure_map] at present
    exact ⟨serial, (PMF.mem_support_pure_iff ..).mp present⟩
  rcases support_mix_subset _ _ _ _ _ supported with slot | canonical
  · unfold phaseBindingSlotPolicy at slot
    split at slot
    · obtain ⟨serial, _chosen, encoded⟩ := (PMF.mem_support_bind_iff ..).mp slot
      exact decode serial encoded
    · exact (sending ((PMF.mem_support_pure_iff ..).mp slot)).elim
  · unfold phaseBindingPolicy at canonical
    split at canonical
    · exact (sending ((PMF.mem_support_pure_iff ..).mp canonical)).elim
    · split at canonical
      · exact decode _ canonical
      · exact (sending ((PMF.mem_support_pure_iff ..).mp canonical)).elim

/-- Every sending atom at a fixed non-RAW timing coin carries the SAME
original typed result. WAIT and the independent slot tier cannot change it. -/
theorem bindingServiceCoinResponse_sending_result
    (owner : Player) (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (coin : Bool × Bool) (ordinary : coin.1 = false)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (result : PublicationResult (L.Val payload)) (selected : values past view = PMF.pure result)
    (action : (phaseApplication runtime leaks).Action)
    (supported : action ∈ (bindingServiceCoinResponse runtime leaks bounds owner coordinate payload
      values choose slotWeight slotNonnegative slotBounded coin past view).support)
    (sending : action ≠ ⟨none⟩) :
    ∃ serial, action = phaseBindingResponse runtime leaks owner coordinate.event payload result
      serial := by
  have encoded (present : action ∈ (bindingResultEncoder runtime leaks bounds owner
      coordinate.event payload values slotWeight slotNonnegative slotBounded past view).support) :=
    encoder_sending_result runtime leaks bounds owner coordinate.event payload values
      slotWeight slotNonnegative slotBounded past view result selected action present sending
  have silent (present : action ∈ (PMF.pure ⟨none⟩ :
      PMF (phaseApplication runtime leaks).Action).support) : False :=
    sending ((PMF.mem_support_pure_iff ..).mp present)
  unfold bindingServiceCoinResponse at supported
  simp only [ordinary, Bool.false_eq_true, ↓reduceIte] at supported
  split at supported
  · split at supported
    · exact (silent supported).elim
    · exact encoded supported
  · split at supported
    · split at supported
      · exact (silent supported).elim
      · exact encoded supported
    · split at supported
      · exact encoded supported
      · exact (silent supported).elim

end Vegas.EventGraphRuntime.PhaseCount

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

open Classical in
/-- Resolving the SAME original table makes the actual native domain callback
deterministic. Its selected coordinate is the physical getter, without a
new independent table or a supplied desired-source observation. -/
theorem phaseObservableDomainValues_table
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (draw : ∀ owner, setup.CommitRecoveryDomainDraw finite owner)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (info : setup.commitRecoveryModel.InfoState who)
    (selected : phaseVirtualSourceQuery? setup mode runtime leaks plan who event view = some info) :
    phaseObservableDomainValues setup mode runtime leaks plan
      (fun owner info => PMF.pure (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback
        owner) (setup.commitRecoveryDomainSites finite owner) (draw owner) info))
      who event payload binding past view =
        PMF.pure (phaseRecoveryDomainValue setup mode event who payload binding
          (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
            (setup.commitRecoveryDomainSites finite who) (draw who) info).val.1) := by
  unfold phaseObservableDomainValues
  simp only [selected, PMF.pure_map]

open Classical in
/-- At an actual initialized ready binding, every non-RAW sending atom reads
the exact coordinate of the original domain table. Its encoded typed value
is unaffected by the independent physical slot and timing encoders. -/
theorem phaseObservableDomainValues_table_sending
    (bounds : MessageBounds (serviceGraph setup mode))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (draw : ∀ owner, setup.CommitRecoveryDomainDraw finite owner)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun inputs => PhaseRuntimeState.initial plan (encodeInputs inputs))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (choose : List Nat → Bool)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (coin : Bool × Bool) (ordinary : coin.1 = false)
    (action : (phaseApplication runtime leaks).Action)
    (supported : action ∈ (PhaseCount.bindingServiceCoinResponse runtime leaks bounds who
      ⟨control.execution.application.attempt, event⟩ payload
      (fun past view => (phaseObservableDomainValues setup mode runtime leaks plan
        (fun owner info => PMF.pure (FiniteAssignment.resolve
          (setup.commitRecoveryDomainFallback owner) (setup.commitRecoveryDomainSites finite owner)
          (draw owner) info)) who event payload binding past view).map PublicationResult.success)
      choose slotWeight slotNonnegative slotBounded coin (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).support)
    (sending : action ≠ ⟨none⟩) :
    ∃ info : setup.commitRecoveryModel.InfoState who,
      phaseVirtualSourceQuery? setup mode runtime leaks plan who event
          (control.execution.observe (phaseApplication runtime leaks) who) = some info ∧
      ∃ serial, action = phaseBindingResponse runtime leaks who event payload
        (.success (phaseRecoveryDomainValue setup mode event who payload binding
          (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
            (setup.commitRecoveryDomainSites finite who) (draw who) info).val.1)) serial := by
  obtain ⟨current, sourceTrace, _actor, _position, _decision, selected⟩ :=
    phaseVirtualSourceQuery?_genuine_of_ready_binding setup mode runtime leaks plan maximal
      horizon scheduler trace who event payload binding request
  let info := setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
    (setup.commitRecoveryModel.infoOf who sourceTrace))
  refine ⟨info, selected, ?_⟩
  apply PhaseCount.bindingServiceCoinResponse_sending_result runtime leaks bounds who
    ⟨control.execution.application.attempt, event⟩ payload _ choose slotWeight slotNonnegative
      slotBounded coin ordinary _ _ _ _ action supported sending
  rw [phaseObservableDomainValues_table setup mode runtime leaks plan finite draw who event
    payload binding _ _ info selected, PMF.pure_map]

section OriginalTable

variable (bounds : MessageBounds (serviceGraph setup mode))
  (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
  (draw : ∀ owner, setup.CommitRecoveryDomainDraw finite owner)
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)
  (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "V" => phaseObservableDomainValues setup mode runtime leaks plan
  (fun owner info => PMF.pure (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback owner)
    (setup.commitRecoveryDomainSites finite owner) (draw owner) info))
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds V choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes

open Classical in
/-- The actual complete tape policy reads its original domain table at every
non-RAW sending callback. Initialization, the native invariant, and the finite
ordinal bound are discharged from the original counted trace. -/
theorem phaseCountServiceTapePolicy_domain_sending
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (binding : (graph).outputLayout coordinate.1.event = .binding who payload)
    (request : control.execution.application.SeedRequest who coordinate.1)
    (ordinary : (tapes coordinate
      ⟨_, PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon scheduler
        control ((menu).toRawTrace initial horizon scheduler trace) who active coordinate.1⟩).1 =
      false)
    (action : (app).Action)
    (chosen : action ∈ (Q who (control.execution.recall who)
      (control.execution.observe app who)).support)
    (sending : action ≠ ⟨none⟩) :
    ∃ info : setup.commitRecoveryModel.InfoState who,
      phaseVirtualSourceQuery? setup mode runtime leaks plan who coordinate.1.event
          (control.execution.observe app who) = some info ∧
      ∃ serial, action = phaseBindingResponse runtime leaks who coordinate.1.event payload
        (.success (phaseRecoveryDomainValue setup mode coordinate.1.event who payload binding
          (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
            (setup.commitRecoveryDomainSites finite who) (draw who) info).val.1)) serial := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  have requested := (control.execution.application.requests_publicView valid who coordinate.1).mpr
    request
  change PhaseRuntimeState.requests (control.execution.observe app who).application.2 who
    coordinate.1 at requested
  have inside := PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon scheduler
    control raw who active coordinate.1
  rw [phaseCountServiceTapePolicy_local_member_at setup mode runtime leaks bounds V choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    scheduler control trace who coordinate payload binding] at chosen
  unfold PhaseCount.bindingServiceTapeMember at chosen
  simp only [requested, inside, ↓reduceIte] at chosen
  have tag : control.execution.application.attempt = coordinate.1.attempt := request.1.symm
  have currentRequest : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, coordinate.1.event⟩ := by
    simpa only [tag] using request
  have originalTrace : ((app).protocol
      (setup.initialLaw.map fun input => PhaseRuntimeState.initial plan (encodeInputs input))
      horizon scheduler).Trace (some control) := by
    have initialEq : initial = setup.initialLaw.map
        (fun input => PhaseRuntimeState.initial plan (encodeInputs input)) :=
      PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
    rw [initialEq] at raw
    exact raw
  have readout := phaseObservableDomainValues_table_sending setup mode runtime leaks
    plan bounds finite draw maximal horizon scheduler originalTrace who coordinate.1.event payload
    binding currentRequest (choose who coordinate.1) slotWeight slotNonnegative slotBounded
    (tapes coordinate ⟨_, inside⟩) ordinary action
  simp only [tag] at readout
  exact readout chosen sending


open Classical in
/-- A remembered current-attempt SEND on the foreign RAW-free event has a
genuine original callback and the exact original domain-table value. This
includes declarations sent before the selected continuation entry. -/
theorem phaseCountServiceTapePolicy_recorded_domain
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (scheduler : (app).Scheduler) (start final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (phase : RuntimePhase graph) (focal who : Player) (foreign : who ≠ focal)
    (initiallyActive : who ∉ start.execution.application.current.excluded)
    (proper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      scheduler start phase focal final trace)
    (consistent : (Q who).Consistent (final.execution.recall who))
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (entry : (app).PlayerEntry) (recorded : entry ∈ final.execution.recall who)
    (material : WitnessedSubmission graph) (transmitted : entry.action.transmission = some material)
    (candidate : Handle graph) (named : material.call.packet = .commitment event candidate)
    (sameAttempt : entry.beforeView.application.2.attempt =
      start.execution.application.attempt) :
    ∃ (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = some who ∧
      before.execution.application.SeedRequest who
        ⟨start.execution.application.attempt, event⟩ ∧
      entry.beforeView = before.execution.observe app who ∧
      (Q who).Consistent (before.execution.recall who) ∧
      ∃ info : setup.commitRecoveryModel.InfoState who,
        phaseVirtualSourceQuery? setup mode runtime leaks plan who event
          (before.execution.observe app who) = some info ∧
        ∃ serial, entry.action = phaseBindingResponse runtime leaks who event payload
          (.success (phaseRecoveryDomainValue setup mode event who payload binding
            (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
              (setup.commitRecoveryDomainSites finite who) (draw who) info).val.1)) serial := by
  obtain ⟨before, prior, retained, active, viewed, chosen, _after, _recalled⟩ :=
    (menu).recorded_response_supported initial horizon scheduler final trace who (Q who)
      consistent entry recorded
  have offered := phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds V choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes who
    (before.execution.recall who) (before.execution.observe app who) entry.action chosen
  have actionEq : entry.action = (⟨some material⟩ : (app).Action) := by
    cases actionAt : entry.action with
    | mk transmission =>
        simpa only [actionAt] using congrArg ReactiveApplication.Action.mk transmitted
  have offeredSend := actionEq ▸ offered
  have beforeActive : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨before.remaining, some who, before.execution⟩) := by
    simpa only [← active] using prior
  obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    plan inputs horizon scheduler before.remaining who before.execution beforeActive material
    offeredSend
  have addressed := PhaseCount.onePacket_event_of_request runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining who
    before.execution beforeActive coordinate request material offeredSend
  rw [named] at addressed
  have sameEvent : coordinate.event = event := (Option.some.inj addressed).symm
  have tag : before.execution.application.attempt = start.execution.application.attempt := by
    rw [viewed] at sameAttempt
    exact sameAttempt
  have coordinateEq : coordinate = ⟨start.execution.application.attempt, event⟩ := by
    exact congrArg₂ CommitAttemptEvent.mk (request.1.trans tag) sameEvent
  rw [coordinateEq] at request
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining who
    before.execution beforeActive _ request material offeredSend
  have raw := (menu).toRawTrace initial horizon scheduler prior
  have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon scheduler
    (fun state member => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_seedBudget plan input) raw
  let address : PhaseSeedAddress graph := ⟨_, request.bounded budget⟩
  have ordinary := proper who foreign initiallyActive event inside address.property before prior
    retained active request unsent
  have sends : entry.action ≠ (⟨none⟩ : (app).Action) := by
    intro silent
    rw [silent] at transmitted
    cases transmitted
  obtain ⟨info, selected, serial, declared⟩ := phaseCountServiceTapePolicy_domain_sending setup
    mode runtime leaks plan bounds finite draw choose failure timing firstNonnegative firstBounded
    timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative
    rawBounded horizon tapes maximal scheduler before prior who active address payload binding
    request ordinary entry.action chosen sends
  have beforeConsistent : (Q who).Consistent (before.execution.recall who) := by
    rw [_recalled] at consistent
    exact ReactiveApplication.Policy.Consistent.of_append consistent
  exact ⟨before, prior, retained, active, request, viewed, beforeConsistent, info, selected,
    serial, declared⟩


omit [setup.FiniteInitialLaw] in
private theorem original_prefix_metadata
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    before.execution.application.phases = after.execution.application.phases ∧
      before.execution.application.entry = after.execution.application.entry ∧
      before.execution.application.retired = after.execution.application.retired := by
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state present
    obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ present
    exact PhaseRuntimeState.initial_ordered plan input
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler prior)
  have metadata := phase_attempt_metadata_of_prefix runtime leaks menu initial initialized horizon
    scheduler before after prior trace retained ordered same
  have progress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler before after prior trace retained ordered
  exact ⟨congrArg Prod.fst metadata, progress.2.2 same, congrArg Prod.snd metadata⟩

omit [setup.FiniteInitialLaw] in
private theorem original_rawFree_prefix
    (scheduler : (app).Scheduler) (start before after : (app).Control)
    (phase : RuntimePhase graph) (focal : Player)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace)
    (proper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      scheduler start phase focal after trace) :
    phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      scheduler start phase focal before prior := by
  intro owner foreign active event inside bounded current earlier prefixProof acting request
    unsent
  exact proper owner foreign active event inside bounded current earlier
    (prefixProof.trans retained)
    acting request unsent

open Classical in
/-- Foreign RAW-free callbacks in the same original commitment attempt read
identical original domain coordinates. The proof follows actual earlier own
receipts in static rank order, including callbacks before the chosen entry. -/
theorem phaseCountServiceTapePolicy_foreign_query_eq
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (start : (app).Control) (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (focal who : Player) (foreign : who ≠ focal)
    (initiallyActive : who ∉ start.execution.application.current.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (firstScheduler secondScheduler : (app).Scheduler) (first second : (app).Control)
    (firstTrace : ((menu).protocol initial horizon firstScheduler).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon secondScheduler).Trace (some second))
    (firstInstalled : phase ∈ first.execution.application.phases.head?)
    (secondInstalled : phase ∈ second.execution.application.phases.head?)
    (firstRequest : first.execution.application.SeedRequest who
      ⟨start.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest who
      ⟨start.execution.application.attempt, event⟩)
    (entry : first.execution.application.entry = second.execution.application.entry)
    (archives : first.execution.application.retired = second.execution.application.retired)
    (firstConsistent : (Q who).Consistent (first.execution.recall who))
    (secondConsistent : (Q who).Consistent (second.execution.recall who))
    (firstProper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan
      inputs firstScheduler start phase focal first firstTrace)
    (secondProper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan
      inputs secondScheduler start phase focal second secondTrace) :
    phaseVirtualSourceQuery? setup mode runtime leaks plan who event
        (first.execution.observe app who) =
      phaseVirtualSourceQuery? setup mode runtime leaks plan who event
        (second.execution.observe app who) := by
  induction rank : event.val using Nat.strong_induction_on generalizing event payload
      firstScheduler secondScheduler first second with
  | h rank ih =>
    have firstRaw := (menu).toRawTrace initial horizon firstScheduler firstTrace
    have secondRaw := (menu).toRawTrace initial horizon secondScheduler secondTrace
    have firstExclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon
      firstScheduler firstRaw
    have secondExclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon
      secondScheduler secondRaw
    have firstStored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon
      firstScheduler firstRaw
    have secondStored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon
      secondScheduler secondRaw
    have firstFailures := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
      firstScheduler firstRaw
    have secondFailures := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
      secondScheduler secondRaw
    have firstTag : first.execution.application.attempt = start.execution.application.attempt :=
      firstRequest.1.symm
    have secondTag : second.execution.application.attempt = start.execution.application.attempt :=
      secondRequest.1.symm
    have firstRequested : first.execution.application.SeedRequest who
        ⟨first.execution.application.attempt, event⟩ := by
      simpa only [firstTag] using firstRequest
    have secondRequested : second.execution.application.SeedRequest who
        ⟨second.execution.application.attempt, event⟩ := by
      simpa only [secondTag] using secondRequest
    apply phaseVirtualSourceQuery?_eq_of_ready_saved setup mode runtime leaks plan
      first.execution second.execution phase commitment firstInstalled secondInstalled
      firstExclusion.frontier secondExclusion.frontier firstStored secondStored firstFailures
      secondFailures entry (firstTag.trans secondTag.symm) archives who event inside firstRequested
      secondRequested
    intro previous previousInside earlier actor
    obtain ⟨other, previousPayload, previousBinding⟩ := commitment ▸ phase.fields previous
      ((phase.mem_events previous).mp previousInside).1
      ((phase.mem_events previous).mp previousInside).2
    have owner : other = who := Option.some.inj
      ((actor?_of_outputLayout_binding graph previousBinding).symm.trans actor)
    subst other
    obtain ⟨firstCandidate, _firstMessage, firstEntry, firstMaterial, oldFirst, oldFirstTrace,
      _firstOwned, firstAccepted, _firstRead, _firstSender, _firstAttempt, _firstCall,
      firstRecorded, _firstEmitted, firstSent, firstNamed, _oldFirstPrefix, oldFirstSame,
      _oldFirstActive, oldFirstView, _oldFirstChosen, _oldFirstSuffix⟩ :=
      phase_ready_earlier_binding_declaration runtime leaks bounds plan inputs horizon
        firstScheduler firstTrace (serviceGraph_revealRelaxedOrdered setup mode) phase
        (Option.mem_def.mp firstInstalled) who event payload binding firstRequest.2.2.1
        firstRequest.2.2.2.2 previous previousPayload previousBinding previousInside earlier
        (Q who) firstConsistent
    obtain ⟨secondCandidate, _secondMessage, secondEntry, secondMaterial, oldSecond, oldSecondTrace,
      _secondOwned, secondAccepted, _secondRead, _secondSender, _secondAttempt, _secondCall,
      secondRecorded, _secondEmitted, secondSent, secondNamed, _oldSecondPrefix, oldSecondSame,
      _oldSecondActive, oldSecondView, _oldSecondChosen, _oldSecondSuffix⟩ :=
      phase_ready_earlier_binding_declaration runtime leaks bounds plan inputs horizon
        secondScheduler secondTrace (serviceGraph_revealRelaxedOrdered setup mode) phase
        (Option.mem_def.mp secondInstalled) who event payload binding secondRequest.2.2.1
        secondRequest.2.2.2.2 previous previousPayload previousBinding previousInside earlier
        (Q who) secondConsistent
    have firstStamp : firstEntry.beforeView.application.2.attempt =
        first.execution.application.attempt := by
      rw [oldFirstView]
      exact oldFirstSame
    have secondStamp : secondEntry.beforeView.application.2.attempt =
        second.execution.application.attempt := by
      rw [oldSecondView]
      exact oldSecondSame
    obtain ⟨firstBefore, firstPrior, firstPrefix, _firstActive, firstBeforeRequest, _firstView,
      firstBeforeConsistent, firstInfo, firstSelected, firstSerial, firstDeclared⟩ :=
      phaseCountServiceTapePolicy_recorded_domain setup mode runtime leaks plan bounds finite draw
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes
        maximal firstScheduler start first firstTrace phase focal who foreign initiallyActive
        firstProper firstConsistent previous previousInside previousPayload previousBinding
        firstEntry firstRecorded firstMaterial firstSent firstCandidate firstNamed
        (firstStamp.trans firstTag)
    obtain ⟨secondBefore, secondPrior, secondPrefix, _secondActive, secondBeforeRequest,
      _secondView,
      secondBeforeConsistent, secondInfo, secondSelected, secondSerial, secondDeclared⟩ :=
      phaseCountServiceTapePolicy_recorded_domain setup mode runtime leaks plan bounds finite draw
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes
        maximal secondScheduler start second secondTrace phase focal who foreign initiallyActive
        secondProper secondConsistent previous previousInside previousPayload previousBinding
        secondEntry secondRecorded secondMaterial secondSent secondCandidate secondNamed
        (secondStamp.trans secondTag)
    have firstData := original_prefix_metadata setup mode runtime leaks plan bounds horizon
      firstScheduler firstBefore first firstPrior firstTrace firstPrefix
      (firstBeforeRequest.1.symm.trans firstRequest.1)
    have secondData := original_prefix_metadata setup mode runtime leaks plan bounds horizon
      secondScheduler secondBefore second secondPrior secondTrace secondPrefix
      (secondBeforeRequest.1.symm.trans secondRequest.1)
    have firstBeforeInstalled : phase ∈ firstBefore.execution.application.phases.head? := by
      simpa only [firstData.1] using firstInstalled
    have secondBeforeInstalled : phase ∈ secondBefore.execution.application.phases.head? := by
      simpa only [secondData.1] using secondInstalled
    have firstBeforeProper := original_rawFree_prefix setup mode runtime leaks plan bounds horizon
      tapes firstScheduler start firstBefore first phase focal firstPrior firstTrace firstPrefix
      firstProper
    have secondBeforeProper := original_rawFree_prefix setup mode runtime leaks plan bounds horizon
      tapes secondScheduler start secondBefore second phase focal secondPrior secondTrace
      secondPrefix secondProper
    have sameQuery := ih previous.val (by omega) previous previousInside previousPayload
      previousBinding firstScheduler secondScheduler firstBefore secondBefore firstPrior secondPrior
      firstBeforeInstalled secondBeforeInstalled firstBeforeRequest secondBeforeRequest
      (firstData.2.1.trans (entry.trans secondData.2.1.symm))
      (firstData.2.2.trans (archives.trans secondData.2.2.symm)) firstBeforeConsistent
      secondBeforeConsistent firstBeforeProper secondBeforeProper rfl
    have infos : firstInfo = secondInfo := Option.some.inj
      (firstSelected.symm.trans (sameQuery.trans secondSelected))
    have firstLower : first.execution.application.attempt.phase ≤ previous.val := by
      simpa only [PhaseRuntimeState.attempt, Option.mem_def.mp firstInstalled, Option.map_some,
        Option.getD_some] using ((phase.mem_events previous).mp previousInside).1
    have secondLower : second.execution.application.attempt.phase ≤ previous.val := by
      simpa only [PhaseRuntimeState.attempt, Option.mem_def.mp secondInstalled, Option.map_some,
        Option.getD_some] using ((phase.mem_events previous).mp previousInside).1
    have firstRead := phase_completed_recorded_binding_read runtime leaks bounds plan inputs
      horizon firstScheduler firstTrace who previous previousPayload previousBinding firstLower
      (firstExclusion.active previous firstCandidate firstAccepted) firstRequest.2.2.2.2
      _ firstSerial firstEntry firstRecorded firstDeclared firstStamp
    have secondRead := phase_completed_recorded_binding_read runtime leaks bounds plan inputs
      horizon secondScheduler secondTrace who previous previousPayload previousBinding secondLower
      (secondExclusion.active previous secondCandidate secondAccepted) secondRequest.2.2.2.2
      _ secondSerial secondEntry secondRecorded secondDeclared secondStamp
    rw [infos] at firstRead
    have sameRead := firstRead.trans secondRead.symm
    change cast (congrArg (fun field => Option field.Value) previousBinding)
      (first.execution.application.current.native.config.store (.inr previous)) =
      cast (congrArg (fun field => Option field.Value) previousBinding)
        (second.execution.application.current.native.config.store (.inr previous)) at sameRead
    exact (cast_inj _).mp sameRead


omit [setup.FiniteInitialLaw] in
private theorem original_common_metadata
    (scheduler : (app).Scheduler) (start before final : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (fromStart : TracePrefix startTrace trace) (fromBefore : TracePrefix prior trace)
    (same : before.execution.application.attempt = start.execution.application.attempt) :
    before.execution.application.phases = start.execution.application.phases ∧
      before.execution.application.entry = start.execution.application.entry ∧
      before.execution.application.retired = start.execution.application.retired := by
  by_cases lengths : prior.length ≤ startTrace.length
  · have path := fromBefore.reachesWithin.ancestor_comparable fromStart.reachesWithin lengths
    exact original_prefix_metadata setup mode runtime leaks plan bounds horizon scheduler before
      start prior startTrace path.tracePrefix same
  · have path := fromStart.reachesWithin.ancestor_comparable fromBefore.reachesWithin (by
      change startTrace.length ≤ prior.length
      omega)
    obtain ⟨phases, saved, archived⟩ := original_prefix_metadata setup mode runtime leaks plan
      bounds horizon scheduler start before startTrace prior path.tracePrefix same.symm
    exact ⟨phases.symm, saved.symm, archived.symm⟩

open Classical in
/-- Two actual remembered declarations in a RAW-free foreign occurrence
have the same immutable typed preparation, even when their original attempt
has since been archived or restored. Either SEND may precede the entry. -/
theorem phaseCountServiceTapePolicy_recorded_openings_eq
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (start : (app).Control) (phase : RuntimePhase graph)
    (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal who : Player) (foreign : who ≠ focal)
    (initiallyActive : who ∉ start.execution.application.current.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (firstScheduler secondScheduler : (app).Scheduler) (first second : (app).Control)
    (firstStart : ((menu).protocol initial horizon firstScheduler).Trace (some start))
    (secondStart : ((menu).protocol initial horizon secondScheduler).Trace (some start))
    (firstTrace : ((menu).protocol initial horizon firstScheduler).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon secondScheduler).Trace (some second))
    (firstFromStart : TracePrefix firstStart firstTrace)
    (secondFromStart : TracePrefix secondStart secondTrace)
    (firstConsistent : (Q who).Consistent (first.execution.recall who))
    (secondConsistent : (Q who).Consistent (second.execution.recall who))
    (firstProper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan
      inputs firstScheduler start phase focal first firstTrace)
    (secondProper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan
      inputs secondScheduler start phase focal second secondTrace)
    (firstEntry secondEntry : (app).PlayerEntry)
    (firstRecorded : firstEntry ∈ first.execution.recall who)
    (secondRecorded : secondEntry ∈ second.execution.recall who)
    (firstMaterial secondMaterial : WitnessedSubmission graph)
    (firstSent : firstEntry.action.transmission = some firstMaterial)
    (secondSent : secondEntry.action.transmission = some secondMaterial)
    (firstCandidate secondCandidate : Handle graph)
    (firstNamed : firstMaterial.call.packet = .commitment event firstCandidate)
    (secondNamed : secondMaterial.call.packet = .commitment event secondCandidate)
    (firstAttempt : firstEntry.beforeView.application.2.attempt =
      start.execution.application.attempt)
    (secondAttempt : secondEntry.beforeView.application.2.attempt =
      start.execution.application.attempt) :
    firstMaterial.call.opening = secondMaterial.call.opening := by
  obtain ⟨firstBefore, firstPrior, firstPrefix, _firstActive, firstRequest, _firstView,
    firstBeforeConsistent, firstInfo, firstSelected, firstSerial, firstDeclared⟩ :=
    phaseCountServiceTapePolicy_recorded_domain setup mode runtime leaks plan bounds finite draw
      choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
      slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes
      maximal firstScheduler start first firstTrace phase focal who foreign initiallyActive
      firstProper firstConsistent event inside payload binding firstEntry firstRecorded
      firstMaterial firstSent firstCandidate firstNamed firstAttempt
  obtain ⟨secondBefore, secondPrior, secondPrefix, _secondActive, secondRequest, _secondView,
    secondBeforeConsistent, secondInfo, secondSelected, secondSerial, secondDeclared⟩ :=
    phaseCountServiceTapePolicy_recorded_domain setup mode runtime leaks plan bounds finite draw
      choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
      slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes
      maximal secondScheduler start second secondTrace phase focal who foreign initiallyActive
      secondProper secondConsistent event inside payload binding secondEntry secondRecorded
      secondMaterial secondSent secondCandidate secondNamed secondAttempt
  have firstData := original_common_metadata setup mode runtime leaks plan bounds horizon
    firstScheduler start firstBefore first firstStart firstPrior firstTrace firstFromStart
    firstPrefix firstRequest.1.symm
  have secondData := original_common_metadata setup mode runtime leaks plan bounds horizon
    secondScheduler start secondBefore second secondStart secondPrior secondTrace secondFromStart
    secondPrefix secondRequest.1.symm
  have firstInstalled : phase ∈ firstBefore.execution.application.phases.head? := by
    simpa only [firstData.1] using installed
  have secondInstalled : phase ∈ secondBefore.execution.application.phases.head? := by
    simpa only [secondData.1] using installed
  have firstBeforeProper := original_rawFree_prefix setup mode runtime leaks plan bounds horizon
    tapes firstScheduler start firstBefore first phase focal firstPrior firstTrace firstPrefix
    firstProper
  have secondBeforeProper := original_rawFree_prefix setup mode runtime leaks plan bounds horizon
    tapes secondScheduler start secondBefore second phase focal secondPrior secondTrace secondPrefix
    secondProper
  have queries := phaseCountServiceTapePolicy_foreign_query_eq setup mode runtime leaks plan bounds
    finite draw choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes maximal
    start phase commitment focal who foreign initiallyActive event inside payload binding
    firstScheduler secondScheduler firstBefore secondBefore firstPrior secondPrior firstInstalled
    secondInstalled
    firstRequest secondRequest (firstData.2.1.trans secondData.2.1.symm)
    (firstData.2.2.trans secondData.2.2.symm) firstBeforeConsistent secondBeforeConsistent
    firstBeforeProper secondBeforeProper
  have infos : firstInfo = secondInfo := Option.some.inj
    (firstSelected.symm.trans (queries.trans secondSelected))
  have firstOpening : firstMaterial.call.opening = some ⟨payload,
      phaseRecoveryDomainValue setup mode event who payload binding
        (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
          (setup.commitRecoveryDomainSites finite who) (draw who) firstInfo).val.1⟩ :=
    congrArg (fun material : WitnessedSubmission graph => material.call.opening)
      (Option.some.inj (firstSent.symm.trans
        (congrArg ReactiveApplication.Action.transmission firstDeclared)))
  have secondOpening : secondMaterial.call.opening = some ⟨payload,
      phaseRecoveryDomainValue setup mode event who payload binding
        (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
          (setup.commitRecoveryDomainSites finite who) (draw who) secondInfo).val.1⟩ :=
    congrArg (fun material : WitnessedSubmission graph => material.call.opening)
      (Option.some.inj (secondSent.symm.trans
        (congrArg ReactiveApplication.Action.transmission secondDeclared)))
  rw [infos] at firstOpening
  exact firstOpening.trans secondOpening.symm

open Classical in
/-- True original receipts supply every static foreign word coordinate. The
typed preparations agree under the same original domain table even if a SEND
predated the common entry or the endpoint restored the native configuration. -/
theorem phaseCountServiceTapePolicy_receipted_word_eq
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (start : (app).Control) (phase : RuntimePhase graph)
    (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (firstScheduler secondScheduler : (app).Scheduler) (first second : (app).Control)
    (firstStart : ((menu).protocol initial horizon firstScheduler).Trace (some start))
    (secondStart : ((menu).protocol initial horizon secondScheduler).Trace (some start))
    (firstTrace : ((menu).protocol initial horizon firstScheduler).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon secondScheduler).Trace (some second))
    (firstFromStart : TracePrefix firstStart firstTrace)
    (secondFromStart : TracePrefix secondStart secondTrace)
    (firstConsistent : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (first.execution.recall owner))
    (secondConsistent : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (second.execution.recall owner))
    (firstProper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan
      inputs firstScheduler start phase focal first firstTrace)
    (secondProper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan
      inputs secondScheduler start phase focal second secondTrace)
    (firstReceipts : ∀ owner, owner ≠ focal →
      owner ∉ start.execution.application.current.excluded → ∀ event ∈ phase.events,
      (graph).actor? event = some owner → PhaseService.BindingAccepted runtime leaks
        ⟨start.execution.application.attempt, event⟩ owner first.execution)
    (secondReceipts : ∀ owner, owner ≠ focal →
      owner ∉ start.execution.application.current.excluded → ∀ event ∈ phase.events,
      (graph).actor? event = some owner → PhaseService.BindingAccepted runtime leaks
        ⟨start.execution.application.attempt, event⟩ owner second.execution) :
    phaseForeignStaticBindingWord runtime leaks start phase focal first =
      phaseForeignStaticBindingWord runtime leaks start phase focal second := by
  funext owner event
  unfold phaseForeignStaticBindingWord
  by_cases selected : owner ≠ focal ∧ owner ∉ start.execution.application.current.excluded ∧
      event ∈ phase.events ∧ (graph).actor? event = some owner
  · simp only [ite_eq_left selected]
    obtain ⟨foreign, active, inside, actor⟩ := selected
    have ranks := (phase.mem_events event).mp inside
    obtain ⟨other, payload, binding⟩ := commitment ▸ phase.fields event ranks.1 ranks.2
    have same : other = owner := Option.some.inj
      ((actor?_of_outputLayout_binding graph binding).symm.trans actor)
    subst other
    obtain ⟨firstEntry, firstRecorded, firstMaterial, firstCandidate, firstTag, firstSent,
      firstNamed⟩ := phase_bindingAccepted_declaration runtime leaks bounds plan inputs horizon
        firstScheduler first firstTrace start.execution.application.attempt owner event payload
        binding (firstReceipts owner foreign active event inside actor)
    obtain ⟨secondEntry, secondRecorded, secondMaterial, secondCandidate, secondTag, secondSent,
      secondNamed⟩ := phase_bindingAccepted_declaration runtime leaks bounds plan inputs horizon
        secondScheduler second secondTrace start.execution.application.attempt owner event payload
        binding (secondReceipts owner foreign active event inside actor)
    obtain ⟨firstOpening, firstSelected⟩ := phaseStaticBindingWord_present runtime leaks
      start.execution.application.attempt _ event firstEntry firstRecorded firstMaterial
      firstCandidate firstTag firstSent firstNamed
    obtain ⟨secondOpening, secondSelected⟩ := phaseStaticBindingWord_present runtime leaks
      start.execution.application.attempt _ event secondEntry secondRecorded secondMaterial
      secondCandidate secondTag secondSent secondNamed
    obtain ⟨firstHead, firstRetained, firstHeadMaterial, firstHeadCandidate, firstHeadTag,
      firstHeadSent, firstHeadNamed, firstHeadOpening⟩ := phaseStaticBindingWord_origin runtime
        leaks start.execution.application.attempt _ event firstOpening firstSelected
    obtain ⟨secondHead, secondRetained, secondHeadMaterial, secondHeadCandidate, secondHeadTag,
      secondHeadSent, secondHeadNamed, secondHeadOpening⟩ := phaseStaticBindingWord_origin runtime
        leaks start.execution.application.attempt _ event secondOpening secondSelected
    have openings := phaseCountServiceTapePolicy_recorded_openings_eq setup mode runtime leaks plan
      bounds finite draw choose failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon tapes maximal start phase installed commitment focal owner foreign active event inside
      payload binding firstScheduler secondScheduler first second firstStart secondStart firstTrace
      secondTrace firstFromStart secondFromStart (firstConsistent owner foreign)
      (secondConsistent owner foreign) firstProper secondProper firstHead secondHead firstRetained
      secondRetained firstHeadMaterial secondHeadMaterial firstHeadSent secondHeadSent
      firstHeadCandidate secondHeadCandidate firstHeadNamed secondHeadNamed firstHeadTag
      secondHeadTag
    rw [firstSelected, secondSelected]
    exact congrArg some (firstHeadOpening.symm.trans (openings.trans secondHeadOpening))
  · simp only [ite_eq_right selected]


variable (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
  {LocalSeed RestSeed : Type}
  (seedLaw : PMF (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)))
  (family : (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)) →
    (phaseApplication runtime leaks).Scheduler)
  (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan
    (setup.initialLaw.map encodeInputs) horizon seedLaw family)
  (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan
    (setup.initialLaw.map encodeInputs) horizon seedLaw family)
  (capacity : horizon ≤ bounds.candidateCount)
  (catalogue : ∀ owner event payload (_binding : (serviceGraph setup mode).outputLayout event =
      .binding owner payload),
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

open Classical in
include ordered calendar privateSuccess capacity catalogue in
/-- Under the same original domain table, timing tapes and foreign seeds,
the joint static foreign typed declaration word and good event is invariant
under arbitrary focal continuation. Off the good event the readout is a
cemetery. Permanent recall retains pre-entry SENDs and restored attempts. -/
theorem phaseCountServiceTapePolicy_good_word_law
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (firstContract : PhaseService.AsyncContract runtime leaks initial horizon (family firstSeeds)
      delay bound)
    (secondContract : PhaseService.AsyncContract runtime leaks initial horizon (family secondSeeds)
      delay bound)
    (firstProfile : ∀ who, ((menu).information initial horizon
      (family firstSeeds)).BehavioralPolicy who)
    (secondProfile : ∀ who, ((menu).information initial horizon
      (family secondSeeds)).BehavioralPolicy who)
    (start : (app).Control)
    (firstStart : ((menu).protocol initial horizon (family firstSeeds)).Trace (some start))
    (secondStart : ((menu).protocol initial horizon (family secondSeeds)).Trace (some start))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (atEntry : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (start.execution.recall owner))
    (firstFollows : ∀ owner, owner ≠ focal → firstProfile owner =
      (menu).restrictPolicy initial horizon (family firstSeeds) owner (Q owner))
    (secondFollows : ∀ owner, owner ≠ focal → secondProfile owner =
      (menu).restrictPolicy initial horizon (family secondSeeds) owner (Q owner))
    (sameSeeds : ∀ owner, owner ≠ focal → ∀ event ∈ phase.events, (serviceGraph setup mode).actor?
      event = some owner →
      ∀ bounded, firstSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩) =
        secondSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩))
    :
    let firstStopped := fun history : ((menu).protocol initial horizon
        (family firstSeeds)).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let secondStopped := fun history : ((menu).protocol initial horizon
        (family secondSeeds)).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let firstLaw := ((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
      ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
      firstStopped ⟨some start, firstStart⟩
    let secondLaw := ((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
      ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
      secondStopped ⟨some start, secondStart⟩
    let firstReadout : ((menu).protocol initial horizon (family firstSeeds)).History →
        Option (Player → (graph).EventId → Option (Option (Raw L))) :=
      fun history => match history with
        | ⟨none, _⟩ => none
        | ⟨some control, trace⟩ => if
          ((∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
            owner ∉ control.execution.application.current.excluded) ∧
          phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
            (family firstSeeds) start phase focal control trace) then
          some (phaseForeignStaticBindingWord runtime leaks start phase focal control) else none
    let secondReadout : ((menu).protocol initial horizon (family secondSeeds)).History →
        Option (Player → (graph).EventId → Option (Option (Raw L))) :=
      fun history => match history with
        | ⟨none, _⟩ => none
        | ⟨some control, trace⟩ => if
          ((∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
            owner ∉ control.execution.application.current.excluded) ∧
          phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
            (family secondSeeds) start phase focal control trace) then
          some (phaseForeignStaticBindingWord runtime leaks start phase focal control) else none
    firstLaw.map firstReadout = secondLaw.map secondReadout := by
  classical
  intro firstStopped secondStopped firstLaw secondLaw firstReadout secondReadout
  have same : ∀ first ∈ firstLaw.support, ∀ second ∈ secondLaw.support,
      firstReadout first = secondReadout second := by
    rintro ⟨firstState, firstTrace⟩ firstRun ⟨secondState, secondTrace⟩ secondRun
    obtain ⟨first, firstEq, _changed, _idle, _snapshot⟩ :=
      phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon
        (family firstSeeds) delay bound firstContract firstProfile start firstStart phase installed
        ⟨firstState, firstTrace⟩ (by
          convert firstRun using 1; congr 3; funext history
          dsimp only [firstStopped]
          cases history.state <;> rfl)
    cases firstEq
    obtain ⟨second, secondEq, _changed, _idle, _snapshot⟩ :=
      phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon
        (family secondSeeds) delay bound secondContract secondProfile start secondStart phase
        installed ⟨secondState, secondTrace⟩ (by
          convert secondRun using 1; congr 3; funext history
          dsimp only [secondStopped]
          cases history.state <;> rfl)
    cases secondEq
    dsimp only [firstLaw, firstStopped] at firstRun
    dsimp only [secondLaw, secondStopped] at secondRun
    let firstGood : Prop :=
      (∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
        owner ∉ first.execution.application.current.excluded) ∧
      phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
        (family firstSeeds) start phase focal first firstTrace
    let secondGood : Prop :=
      (∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
        owner ∉ second.execution.application.current.excluded) ∧
      phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
        (family secondSeeds) start phase focal second secondTrace
    have equivalent : firstGood ↔ secondGood := by
      constructor
      · rintro ⟨survives, proper⟩
        exact phaseCountServiceTapePolicy_good_survival setup mode runtime leaks bounds V choose
          failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
          slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan ordered
          inputs seedLaw family calendar privateSuccess capacity catalogue firstSeeds secondSeeds
          firstSupport secondSupport delay bound firstContract secondContract firstProfile
          secondProfile start first second firstStart secondStart firstTrace secondTrace phase
          installed commitment focal (by
            convert firstRun using 1; congr 3; funext history
            cases history.state <;> rfl) (by
            convert secondRun using 1; congr 3; funext history
            cases history.state <;> rfl) atEntry firstFollows secondFollows sameSeeds survives
          proper
      · rintro ⟨survives, proper⟩
        exact phaseCountServiceTapePolicy_good_survival setup mode runtime leaks bounds V choose
          failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
          slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan ordered
          inputs seedLaw family calendar privateSuccess capacity catalogue secondSeeds firstSeeds
          secondSupport firstSupport delay bound secondContract firstContract secondProfile
          firstProfile start second first secondStart firstStart secondTrace firstTrace phase
          installed commitment focal (by
            convert secondRun using 1; congr 3; funext history
            cases history.state <;> rfl) (by
            convert firstRun using 1; congr 3; funext history
            cases history.state <;> rfl) atEntry secondFollows firstFollows
          (fun owner foreign event inside actor bounded =>
            (sameSeeds owner foreign event inside actor bounded).symm) survives proper
    change (if firstGood then some (phaseForeignStaticBindingWord runtime leaks start phase focal
      first) else none) = if secondGood then some (phaseForeignStaticBindingWord runtime leaks start
        phase focal second) else none
    by_cases good : firstGood
    · have otherGood := equivalent.mp good
      rw [ite_eq_left good, ite_eq_left otherGood]
      apply congrArg some
      have firstPrefix :=
        ((menu).information initial horizon (family firstSeeds)).runBehavioralUntil_support_prefix
          ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile _
          ⟨some start, firstStart⟩ ⟨some first, firstTrace⟩ firstRun
      have secondPrefix :=
        ((menu).information initial horizon (family secondSeeds)).runBehavioralUntil_support_prefix
          ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile _
          ⟨some start, secondStart⟩ ⟨some second, secondTrace⟩ secondRun
      obtain ⟨_first, firstEq, firstReceipt⟩ := phase_attempt_stopped_survivor_iff_receipts runtime
        leaks menu plan inputs horizon (family firstSeeds) delay bound firstContract firstProfile
        start firstStart phase installed commitment ⟨some first, firstTrace⟩ (by
          convert firstRun using 1; congr 3; funext history
          cases history.state <;> rfl)
      cases Option.some.inj firstEq
      obtain ⟨_second, secondEq, secondReceipt⟩ := phase_attempt_stopped_survivor_iff_receipts
        runtime leaks menu plan inputs horizon (family secondSeeds) delay bound secondContract
        secondProfile
        start secondStart phase installed commitment ⟨some second, secondTrace⟩ (by
          convert secondRun using 1; congr 3; funext history
          cases history.state <;> rfl)
      cases Option.some.inj secondEq
      apply phaseCountServiceTapePolicy_receipted_word_eq setup mode runtime leaks plan bounds
        finite draw choose failure timing firstNonnegative firstBounded timingNonnegative
        timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
        horizon tapes maximal start phase installed commitment focal (family firstSeeds)
        (family secondSeeds) first second firstStart secondStart firstTrace secondTrace firstPrefix
        secondPrefix
      · intro owner foreign
        exact phaseCountServiceTapePolicy_consistent_of_continuation setup mode runtime leaks
          bounds V choose failure timing firstNonnegative firstBounded timingNonnegative
          timingBounded slotWeight slotNonnegative slotBounded horizon tapes plan inputs rawWeight
          rawNonnegative rawBounded (family firstSeeds) firstProfile start first firstStart
          firstTrace _ firstRun owner (firstFollows owner foreign) (atEntry owner foreign)
      · intro owner foreign
        exact phaseCountServiceTapePolicy_consistent_of_continuation setup mode runtime leaks
          bounds V choose failure timing firstNonnegative firstBounded timingNonnegative
          timingBounded slotWeight slotNonnegative slotBounded horizon tapes plan inputs rawWeight
          rawNonnegative rawBounded (family secondSeeds) secondProfile start second secondStart
          secondTrace _ secondRun owner (secondFollows owner foreign) (atEntry owner foreign)
      · exact good.2
      · exact otherGood.2
      · intro owner foreign active event inside actor
        exact (firstReceipt owner active).mp (good.1 owner foreign active) event inside actor
      · intro owner foreign active event inside actor
        exact (secondReceipt owner active).mp (otherGood.1 owner foreign active) event inside actor
    · rw [ite_eq_right good, ite_eq_right (fun other => good (equivalent.mpr other))]
  obtain ⟨reference, supported⟩ := secondLaw.support_nonempty
  calc
    _ = firstLaw.map (fun _ => secondReadout reference) :=
      map_congr_on_support firstLaw (fun first member => same first member reference supported)
    _ = PMF.pure (secondReadout reference) := PMF.map_const _ _
    _ = secondLaw.map (fun _ => secondReadout reference) := (PMF.map_const _ _).symm
    _ = secondLaw.map secondReadout :=
      map_congr_on_support secondLaw (fun second member => by
        obtain ⟨first, present⟩ := firstLaw.support_nonempty
        exact (same first present reference supported).symm.trans
          (same first present second member))


section OriginalPosterior

variable (seed : RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed))

local notation "QT" => phaseCountServiceTapePolicy setup mode runtime leaks bounds V choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
local notation "PT" => phaseCountServicePolicy setup mode runtime leaks bounds V choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
    rawBounded (Fin.val index)))
local notation "EO" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
  horizon (family seed)
local notation "NO" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
  horizon (family seed)

open Classical in
include ordered calendar privateSuccess capacity catalogue in
/-- The joint static foreign declaration word and good event, together with
every original timing table, is invariant under arbitrary focal future play.
The table law is the actual initialized entry posterior; it is not refreshed
at the callback. The original source-domain draw remains a parameter. -/
theorem phaseCountServiceTapePolicy_original_good_word_joint
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (seedSupported : seed ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : PhaseService.AsyncContract runtime leaks initial horizon (family seed) delay bound)
    (start : (app).Control) (trace : (EO).Trace (some start))
    (entryStop : (EO).History → Prop)
    (entrySupported : ⟨some start, trace⟩ ∈ ((NO).runBehavioralUntil
      ((menu).bounded initial horizon (family seed)).wellFoundedHistories
        (fun who => (menu).restrictPolicy initial horizon (family seed) who (PT who))
          entryStop (EO).initHistory).support)
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (firstFocal secondFocal : (NO).BehavioralPolicy focal) :
    let posterior := independentProduct (fun who =>
      ((app).policyMixture original (fun table => QT table who)).posterior
        (start.execution.recall who))
    let owned := fun (tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool)
        (address : PhaseSeedAddress graph) =>
      match (serviceGraph setup mode).actor? address.val.event with
      | none => fun _ : Fin horizon => (false, false)
      | some owner => tables owner address
    let stopped := fun history : (EO).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let readout := fun tables (history : (EO).History) => match history with
      | ⟨none, _⟩ => none
      | ⟨some control, finalTrace⟩ => if
        ((∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
          owner ∉ control.execution.application.current.excluded) ∧
          phaseCountServiceRawFree setup mode runtime leaks bounds horizon (owned tables) plan
            inputs (family seed) start phase focal control finalTrace) then
          some (phaseForeignStaticBindingWord runtime leaks start phase focal control) else none
    (posterior.bind fun tables =>
      (((NO).runBehavioralUntil
        ((menu).bounded initial horizon (family seed)).wellFoundedHistories
        (Function.update (fun who => (menu).restrictPolicy initial horizon (family seed) who
          (QT (tables who) who)) focal firstFocal) stopped ⟨some start, trace⟩).map
            fun final => (readout tables final, tables))) =
      (posterior.bind fun tables =>
        (((NO).runBehavioralUntil
          ((menu).bounded initial horizon (family seed)).wellFoundedHistories
          (Function.update (fun who => (menu).restrictPolicy initial horizon (family seed) who
            (QT (tables who) who)) focal secondFocal) stopped ⟨some start, trace⟩).map
              fun final => (readout tables final, tables))) := by
  classical
  intro posterior owned stopped readout
  apply bind_congr_on_support
  intro tables supported
  have consistent := phaseCountServiceTapePolicy_table_entry_consistent setup mode runtime leaks
    bounds V choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    plan inputs (family seed) entryStop ⟨some start, trace⟩ entrySupported tables supported
  let firstProfile := Function.update (fun who =>
    (menu).restrictPolicy initial horizon (family seed) who (QT (tables who) who)) focal firstFocal
  let secondProfile := Function.update (fun who =>
    (menu).restrictPolicy initial horizon (family seed) who (QT (tables who) who)) focal secondFocal
  have ownEq (owner : Player) : QT (tables owner) owner = QT (owned tables) owner :=
    phaseCountServiceTapePolicy_owned_table setup mode runtime leaks bounds V choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
      slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tables owner
  have firstFollows (owner : Player) (foreign : owner ≠ focal) : firstProfile owner =
      (menu).restrictPolicy initial horizon (family seed) owner (QT (owned tables) owner) := by
    dsimp only [firstProfile]
    rw [Function.update_of_ne foreign]
    exact congrArg ((menu).restrictPolicy initial horizon (family seed) owner) (ownEq owner)
  have secondFollows (owner : Player) (foreign : owner ≠ focal) : secondProfile owner =
      (menu).restrictPolicy initial horizon (family seed) owner (QT (owned tables) owner) := by
    dsimp only [secondProfile]
    rw [Function.update_of_ne foreign]
    exact congrArg ((menu).restrictPolicy initial horizon (family seed) owner) (ownEq owner)
  have atEntry (owner : Player) (_foreign : owner ≠ focal) :
      (QT (owned tables) owner).Consistent (start.execution.recall owner) := by
    have known := consistent owner
    change (QT (tables owner) owner).Consistent (start.execution.recall owner) at known
    rw [ownEq owner] at known
    exact known
  have same := phaseCountServiceTapePolicy_good_word_law setup mode runtime leaks plan bounds
    finite draw choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    (owned tables) ordered seedLaw family calendar privateSuccess capacity catalogue maximal seed
    seed seedSupported seedSupported delay bound contract contract firstProfile secondProfile start
    trace trace phase
    installed commitment focal atEntry firstFollows secondFollows
    (fun _owner _foreign _event _inside _actor _bounded => rfl)
  have tagged := congrArg (PMF.map fun result :
      Option (Player → (graph).EventId → Option (Option (Raw L))) => (result, tables)) same
  simp only [PMF.map_comp, Function.comp_def, firstProfile, secondProfile] at tagged
  convert tagged using 1

end OriginalPosterior

end OriginalTable

end Vegas

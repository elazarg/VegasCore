/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseObservableDomainWord
import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseCountServiceReference
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseBindingMemoryCallback
import Interaction.ReactiveResponseKernel
import Interaction.ReactiveAnchoredStopped
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Interaction.ReactiveMenuLikelihood
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import Vegas.Source.CommitRecoveryValueTremble
import Vegas.Source.CommitRecoveryErasedModel
import Vegas.Game.CommitRecoveryReference
import Vegas.Pending.PhaseReadyBindingDeclaration
import Vegas.Pending.PhaseProposalEmissionOrder
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheory.Math.Probability.Product
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.TremblingPlans

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

section OriginalTable

variable (bounds : MessageBounds (serviceGraph setup mode)) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)

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

end OriginalTable

end Vegas

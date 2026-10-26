/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Game.OnePacketIntendedProjection

/-! # The player's own disclosure resolves at its debt-free forced states

For a well-formed setup, along every history of the one-packet game at a state
forced for a player at which the player owes no failure at the decoded point,
the player's canonical disclosure at its pending reveal transmits: the decoded
point is intended for the player and shows no failed reveal of it, and its
disclosure there publishes a value (`Vegas.disclosureResolves_of_debtFree`).

A transmitting response of the one-packet menu that opens an event opens a
reveal of the responder, since the count verdict checks the call
(`Vegas.onePacket_opening_node`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **The own disclosure resolves at debt-free forced states.** For a
well-formed setup, along every history of the one-packet game at a state forced
for a player at which the player owes no failure at the decoded point, the
player's canonical disclosure at its pending reveal transmits. -/
theorem disclosureResolves_of_debtFree (wellFormed : setup.WellFormed)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (forced : ForcedState setup runtime leaks who (some control))
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    DisclosureResolves setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) := by
  intro event pending owner payload binding checks outputEq codeEq node
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec (runtime := runtime) (setup := setup) pending
  have ownerEq : owner = who :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
  subst ownerEq
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have ready : control.execution.application.config.cut.Ready event :=
    (control.execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ owner event turn).1
  have available : (EventGraph.EventCode.resolveOutput? binding checks true
      control.execution.application.config.store).isSome = true := by
    apply EventGraph.EventCode.resolveOutput?_isSome
    intro field member
    apply control.execution.application.config.read_available ready
    rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
    exact member
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
  have discloses : (cast (congrArg EventGraph.EventField.Action outputEq)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) : Bool) = true := by
    simp
  cases result with
  | success value =>
      obtain ⟨_, _, _, _, packet⟩ := EventGraphRuntime.reactiveResolutionPacket_provenance
        runtime leaks control.execution.application facts.binding owner event payload
        binding checks outputEq _ discloses value resolved
      simp only [EventGraphRuntime.canonicalServiceDecision,
        EventGraphRuntime.canonicalReactiveDecision, node]
      change ((EventGraphRuntime.reactiveNormalization runtime leaks).action owner
        (control.execution.recall owner) (control.execution.observe (application setup runtime
          leaks)
          owner)
        ⟨(EventGraphRuntime.reactiveResolutionPacket owner event payload binding checks
          outputEq _ (runtime.reactiveApplication leaks |>.observePlayer
            control.execution.application owner)).map fun packet =>
          (disclosureSubmission packet).normalizeReactive owner
            (runtime.reactiveApplication leaks |>.observePlayer
              control.execution.application owner) []⟩).transmission ≠ none
      rw [packet]
      simp only [Option.map_some, ReactiveApplication.SubmissionNormalization.action, ne_eq,
        reduceCtorEq, not_false_eq_true]
  | failure =>
      exfalso
      -- The decoded point is intended for the player and shows no failed reveal of it.
      obtain ⟨rank, ⟨residual⟩, holds⟩ := decodedState_intendedFor_or_owes (runtime := runtime)
        wellFormed owner
        (failureProfile setup.program) _ horizon scheduler trace
        control rfl
      obtain ⟨forcedRank, point, ordered, decoded, forcedPoint⟩ := forced
      have sameRank := isPrefix_unique ordered residual.checkpoint.ordered
      subst sameRank
      have pointEq : residual.lift (ProtocolState.entry residual.program residual.source) =
          point := Option.some.inj (residual.decode.symm.trans decoded)
      have decodedAt : decodedPoint setup control.execution.application.config = some point := by
        have exists_ordered : ∃ rank, control.execution.application.config.cut.IsPrefix rank :=
          ⟨_, ordered⟩
        unfold decodedPoint
        rw [dite_eq_left_of_eq_true (eq_true exists_ordered), show exists_ordered.choose = _ from
          isPrefix_unique exists_ordered.choose_spec ordered]
        exact decoded
      have intended : ProtocolState.IntendedFor owner setup.program point := by
        rcases holds _ decoded with intended | owed
        · exact intended
        · exact (notOwed point decodedAt owed).elim
      have clean : ¬ ProtocolState.RevealFailed owner setup.program point := forcedPoint.1
      -- Complete the reveal by disclosing: its output is a failure.
      have stepEq := control.execution.application.config.step_eq_map_of_code event ready
        outputEq _ codeEq true (PMF.pure .failure)
        (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl)
      rw [PMF.pure_map] at stepEq
      have member : control.execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload))) ∈
          (control.execution.application.config.step event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).support := by
        rw [stepEq]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      obtain ⟨next, reached⟩ := residual.step event ready _ _ member
      rw [pointEq] at reached
      have atRank := (ready_iff_rank setup _ forcedRank ordered event).mp ready
      subst atRank
      have nextDecoded := next.decode
      unfold sourceServicePrefix? serviceSourcePrefix? at nextDecoded
      have failedNext := ProtocolState.revealFailed_of_decode_failure setup.program event.val
        (ContextRefs.initial setup.context (outputLayout setup.program)) []
        (Revelations.initial setup.context) (outputRef setup.program) _ _ _ event.isLt owner
        payload outputEq nextDecoded ((eventOwner?_eq_actor setup.program event).trans owned)
        (by
          change (control.execution.application.config.complete event ready _ _).outputs
            event = _
          rw [EventGraph.Config.complete_output_same])
      exact ProtocolState.not_revealFailed_step owner setup.program _ _ _ intended clean
        (decodeEventAction_disclosure_true setup.program event.val event.isLt outputEq)
        reached failedNext

/-- **One-packet openings open reveals.** A transmitting response of the
one-packet menu that opens an event opens a reveal of the responder: the count
verdict checks the call. -/
theorem onePacket_opening_node {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} {response : (application setup runtime
      leaks).Action}
    (member : response ∈ bounds.onePacketActions runtime leaks who past view)
    {material : (application setup runtime leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {handle : Handle (graph setup)} {raw : Raw L}
    (packet : material.call.packet = .opening event handle raw) :
    ∃ (payload : L.Ty) (binding : EventGraph.FieldRef (graph setup).layout (.binding who payload))
      (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve who payload binding checks),
      nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq := by
  obtain ⟨_, either⟩ := (bounds.mem_onePacketActions runtime leaks who past view
    response).mp member
  rcases either with silent | ⟨material', transmits, permitted⟩
  · rw [silent] at sends
    cases sends
  have same : material' = material := Option.some.inj (transmits.symm.trans sends)
  subst same
  obtain ⟨_, correct, _⟩ := (countPermits_eq_true_iff _ _).mp permitted
  unfold CountCallCorrect at correct
  have callEq : (runtime.localEnvelope leaks who past view material').payload.call =
      .opening event handle raw := packet
  rw [callEq] at correct
  obtain ⟨_, opens⟩ := correct
  cases node : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      rw [node] at opens
      exact opens.elim
  | resolve owner payload binding checks outputEq codeEq =>
      rw [node] at opens
      obtain ⟨ownerEq, _, _⟩ := opens
      change who = owner at ownerEq
      subst ownerEq
      exact ⟨payload, binding, checks, outputEq, codeEq, rfl⟩
  | sample payload law outputEq codeEq =>
      rw [node] at opens
      exact opens.elim

end Vegas

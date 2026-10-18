/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSentMenu
import Vegas.Pending.PhaseBindingOpeningRead
import Interaction.ReactiveRawRoundTrace

/-! # Actual counted responses at an owned opening request -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every locally count-admitted response at a genuine owned request names that
request, regardless of the earlier history's response menu. Completed alternatives
already have a signed first packet. -/
theorem onePacket_event_of_request (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    {menu : (app).ResponseMenu}
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (request : execution.application.SeedRequest owner
      coordinate) (material : WitnessedSubmission graph)
    (member : (⟨some material⟩ : (app).Action) ∈ onePacketActions runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner)) :
    material.call.packet.event? graph = some coordinate.event := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  have recalled := countRecall_history runtime leaks raw
  have serials := (app).serialsBeforeNext_history scheduler initial horizon raw
  have permitted : permits ((app).outputs (execution.recall owner))
      (localEnvelope runtime leaks owner (execution.recall owner) (execution.observe app owner)
        material) = true := by
    rcases ((mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2 with
      impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  let message := localEnvelope runtime leaks owner (execution.recall owner)
    (execution.observe app owner) material
  let after := execution.respond app owner ⟨some material⟩
  obtain ⟨appended, fresh, _permanent⟩ := permits_respond runtime leaks execution recalled owner
    material
  have permittedAfter : Permits after.network.inputs message :=
    (permits_eq_true_iff _ _).mp (fresh.trans permitted)
  have authentic : message ∈ after.network.inputs := by
    rw [appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨event, named, _token⟩ := (WitnessedPacket.tokenValid_iff _).mp permittedAfter.1
  have acting : graph.actor? event = some owner :=
    countCallCorrect_owned_event _ (nativeMessage message) permittedAfter.2.1 named
  obtain ⟨phase, installed, inside⟩ := localEnvelope_phase runtime leaks execution owner material
    event permittedAfter.1 named
  have currentTag : message.payload.attempt = execution.application.attempt := rfl
  have configEq : after.application.current.native.config =
      execution.application.current.native.config := by
    change (submitStep _ owner _).config = _
    rw [submitStep_config, (material.call.register_facts owner _).1]
  have same : event = coordinate.event := by
    by_cases completed : event ∈ execution.application.current.native.config.cut.completed
    · obtain ⟨old, oldInput, oldOwner, oldTag, oldNamed⟩ := phase_completed_owned_message runtime
        leaks plan inputs horizon scheduler raw phase (Option.mem_def.mp installed) event inside
          owner acting completed request.2.2.2.2
      have oldBefore : Earlier after.network.inputs message old := by
        refine ⟨?_, oldOwner, ?_⟩
        · rw [appended]
          exact List.mem_append_left _ oldInput
        · have lower : old.id.2 < execution.network.nextSerial old.sender :=
            serials.inputs old oldInput
          have serialEq : message.id.2 = execution.network.nextSerial owner :=
            (recalled.2.1 owner).symm
          rw [oldOwner] at lower
          exact lower.trans_le serialEq.symm.le
      exact False.elim (permittedAfter.2.2.1 old oldBefore (by
        simp only [event?, oldNamed, named, Option.map_some, oldTag, currentTag]))
    · obtain ⟨afterTrace⟩ := (app).raw_trace_respond initial horizon scheduler remaining execution
        owner ⟨some material⟩ raw
      have ready := ready_of_current_authentic_token runtime leaks plan inputs horizon scheduler
        afterTrace message authentic currentTag
          permittedAfter.1 event named (by rwa [configEq])
      rw [configEq] at ready
      exact ordered.ready_actor_unique execution.application.current.native.config.cut
        request.2.2.1 ready request.2.2.2.1 acting
  subst event
  have call : message.payload.packet.call = material.call.packet := maskPacket_call _ _
  exact (congrArg (fun packet => packet.event? graph) call).symm.trans named

/-- At an actual ready publication, every nonsilent counted raw response is
an opening of the surviving accepted typed value. Preparation/evidence syntax
is retained; this is an actual menu normal form rather than source admission. -/
theorem onePacket_opening_shape (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (member : (⟨some material⟩ : (app).Action) ∈ onePacketActions runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner)) :
    ∃ (candidate : Handle graph) (value : L.Val payload),
      material.call.packet = .opening event candidate ⟨payload, value⟩ ∧
      binding.get? execution.application.current.native.config.store = some (.success value) ∧
      execution.application.current.native.accepted binding.field = some candidate ∧
      execution.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ := by
  have named := onePacket_event_of_request runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner execution trace ⟨execution.application.attempt, event⟩ request
      material member
  have permitted : permits ((app).outputs (execution.recall owner))
      (localEnvelope runtime leaks owner (execution.recall owner) (execution.observe app owner)
        material) = true := by
    rcases ((mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2 with
      impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((permits_eq_true_iff _ _).mp permitted).2.1
  have callEq : (localEnvelope runtime leaks owner (execution.recall owner)
      (execution.observe app owner) material).payload.packet.call = material.call.packet :=
    maskPacket_call _ _
  cases call : material.call.packet with
  | malformed raw => rw [call] at named; cases named
  | commitment other candidate =>
      rw [call] at named
      have same : other = event := Option.some.inj named
      subst other
      simp only [CountCallCorrect, nativeMessage, callEq, call, bindingOwnedBy, outputEq,
        Bool.false_eq_true, false_and] at correct
  | opening other candidate raw =>
      rw [call] at named
      have same : other = event := Option.some.inj named
      subst other
      obtain ⟨value, typed, successful, accepted, fixed⟩ :=
        PhaseBindingRepair.opening_response_binding_success runtime leaks bounds plan inputs
          horizon scheduler remaining execution owner trace material event candidate raw call
            member request payload binding checks outputEq codeEq node
      exact ⟨candidate, value, congrArg (Payload.opening event candidate) typed,
        successful, accepted, fixed⟩

end Vegas.EventGraphRuntime.PhaseCount

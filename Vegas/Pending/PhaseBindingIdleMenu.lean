/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSentMenu
import Vegas.Pending.PhaseBindingCountTransport
import Interaction.ReactiveRawRoundTrace

/-! # Actual callbacks without a current owned request admit only silence -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- On any actual initialized menu history, a locally count-admitted response
names a real current ready owner request. Completed alternatives already have an authentic
same-attempt packet, which contradicts the new response's firstness. -/
theorem onePacket_request_of_nonsilent (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    {menu : (app).ResponseMenu}
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (app).Action) ∈ onePacketActions runtime leaks bounds owner
      (execution.recall owner) (execution.observe (app) owner)) :
    ∃ coordinate, execution.application.SeedRequest owner coordinate := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  have recalled := countRecall_history runtime leaks raw
  have serials := (app).serialsBeforeNext_history scheduler initial horizon raw
  obtain ⟨_, allowed⟩ := (mem_onePacketActions runtime leaks bounds owner
    (execution.recall owner) (execution.observe (app) owner) ⟨some material⟩).mp offered
  rcases allowed with silent | ⟨actualMaterial, transmitted, permitted⟩
  · cases silent
  have same : actualMaterial = material := Option.some.inj transmitted.symm
  subst actualMaterial
  let message := localEnvelope runtime leaks owner (execution.recall owner)
    (execution.observe (app) owner) material
  let after := execution.respond (app) owner ⟨some material⟩
  obtain ⟨appended, fresh, _⟩ := permits_respond runtime leaks execution recalled owner material
  have permittedAfter : Permits after.network.inputs message :=
    (permits_eq_true_iff _ _).mp (fresh.trans permitted)
  have authentic : message ∈ after.network.inputs := by
    rw [appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨event, named, _⟩ :=
    (WitnessedPacket.tokenValid_iff message.payload.packet).mp permittedAfter.1
  have acting : graph.actor? event = some owner :=
    countCallCorrect_owned_event _ (nativeMessage message) permittedAfter.2.1 named
  have admitted := PhaseBindingRepair.localEnvelope_admitted runtime leaks execution owner material
    permittedAfter.1
  have allowed := admitted.1
  obtain ⟨phase, installed, actual, actualNamed, inside⟩ :=
    execution.application.allows_event material.call.packet allowed
  have callEq : message.payload.packet.call = material.call.packet := maskPacket_call _ _
  have sameEvent : actual = event := by
    rw [← callEq] at actualNamed
    exact Option.some.inj (actualNamed.symm.trans named)
  subst actual
  have currentTag : message.payload.attempt = execution.application.attempt := rfl
  have configEq : after.application.current.native.config =
      execution.application.current.native.config := by
    change (submitStep _ owner _).config = _
    rw [submitStep_config, (material.call.register_facts owner _).1]
  have unexcluded : owner ∉ execution.application.current.excluded := by
    have absent := admitted.2
    have namedCall : material.call.packet.event? graph = some event := by
      rwa [callEq] at named
    simpa only [RecoveryState.excludedCall, RecoveryState.excludedEvent, namedCall, acting,
      Option.any_some,
      decide_eq_false_iff_not] using absent
  by_cases completed : event ∈ execution.application.current.native.config.cut.completed
  · obtain ⟨old, oldInput, oldOwner, oldTag, oldNamed⟩ :=
      phase_completed_owned_message runtime leaks plan inputs horizon scheduler raw phase
        (Option.mem_def.mp installed) event inside owner acting completed unexcluded
    have before : Earlier after.network.inputs message old := by
      refine ⟨?_, oldOwner, ?_⟩
      · rw [appended]
        exact List.mem_append_left _ oldInput
      · have lower : old.id.2 < execution.network.nextSerial old.sender :=
          serials.inputs old oldInput
        have serialEq : message.id.2 = execution.network.nextSerial owner :=
          (recalled.2.1 owner).symm
        rw [oldOwner] at lower
        exact lower.trans_le serialEq.symm.le
    apply False.elim
    apply permittedAfter.2.2.1 old before
    simp only [event?, oldNamed, named, Option.map_some, oldTag, currentTag]
  · obtain ⟨afterTrace⟩ := (app).raw_trace_respond initial horizon scheduler remaining execution
      owner ⟨some material⟩ raw
    have ready := ready_of_current_authentic_token runtime leaks plan inputs horizon scheduler
      afterTrace message authentic currentTag
        permittedAfter.1 event named (by rwa [configEq])
    rw [configEq] at ready
    exact ⟨⟨execution.application.attempt, event⟩,
      rfl, ⟨phase, installed, inside⟩, ready, acting, unexcluded⟩

/-- Without a genuine current owned request, an actual initialized callback has the
singleton silent menu. No owner ordering or completion contract is assumed. -/
theorem onePacketActions_eq_singleton_of_no_request (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (absent : ∀ coordinate, ¬execution.application.SeedRequest owner coordinate) :
    onePacketActions runtime leaks bounds owner (execution.recall owner)
      (execution.observe (app) owner) = {⟨none⟩} := by
  apply Finset.ext
  intro response
  constructor
  · intro offered
    apply Finset.mem_singleton.mpr
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        obtain ⟨coordinate, request⟩ := onePacket_request_of_nonsilent runtime leaks bounds plan
          inputs horizon scheduler remaining owner execution trace material offered
        exact (absent coordinate request).elim
  · intro silent
    rw [Finset.mem_singleton.mp silent]
    exact silence_onePacket runtime leaks bounds owner _ _

end Vegas.EventGraphRuntime.PhaseCount

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Directed repairs preserve the complete public request predicate, including
its physical attempt address, rather than only the static ready event. -/
theorem seedRequest_iff (frame : Frame runtime leaks memory owner original repaired)
    (who : Player) (coordinate : CommitAttemptEvent graph) :
    original.application.SeedRequest who coordinate ↔
      repaired.application.SeedRequest who coordinate := by
  have visible : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  simp only [PhaseRuntimeState.SeedRequest, PhaseRuntimeState.attempt, frame.phases,
    frame.generation, frame.clearOriginal, frame.clearRepaired, ← State.publicView_eventReady,
    visible]

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

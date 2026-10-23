/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCompletionStampHistory
import Vegas.Pending.PhaseCurrentTokens
import Vegas.Pending.ReactiveCountedSurvivor
import Vegas.Pending.PhaseOpeningAcceptance
import Vegas.Pending.PhaseSeedScheduler
import Interaction.ReactiveRoundTrace

/-! # Actual sent callbacks admit only silence -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem localEnvelope_phase (execution : (app).Execution) (owner : Player)
    (material : (app).Submission) (event : graph.EventId)
    (authorized : (localEnvelope runtime leaks owner (execution.recall owner)
      (execution.observe app owner) material).payload.packet.tokenValid = true)
    (named : (localEnvelope runtime leaks owner (execution.recall owner)
      (execution.observe app owner) material).payload.packet.call.event? graph = some event) :
    ∃ phase ∈ execution.application.phases.head?, event ∈ phase.events := by
  classical
  let packet : WitnessedPacket graph :=
    ⟨material.call.packet, material.evidence.resolve owner
      (material.call.candidateAfter owner (execution.application.current.native.playerView
        owner).candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets (execution.recall owner)
        (execution.observe app owner)).map nativeMessage),
      execution.application.current.native.publicView.tokenFor material.call.packet⟩
  change (maskPacket execution.application.publicView packet).tokenValid = true at authorized
  change (maskPacket execution.application.publicView packet).call.event? graph =
    some event at named
  have callEq : (maskPacket execution.application.publicView packet).call = packet.call := by
    unfold maskPacket
    split_ifs <;> rfl
  rw [callEq] at named
  have allowed : allows execution.application.publicView packet.call = true := by
    cases permitted : allows execution.application.publicView packet.call with
    | false =>
        simp only [maskPacket, permitted, Bool.false_eq_true, ↓reduceIte,
          WitnessedPacket.tokenValid_none] at authorized
    | true => rfl
  rw [allows_publicView] at allowed
  obtain ⟨phase, installed, actual, actualNamed, member⟩ :=
    execution.application.allows_event packet.call allowed
  have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
  subst actual
  exact ⟨phase, installed, member⟩

/-- On an actual counted history with a ready nonexcluded owner coordinate,
a previous own packet for that coordinate leaves exactly the silent action.
Previously completed events are ruled out by actual same-attempt provenance. -/
theorem onePacketActions_eq_singleton_of_sent (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph)
    (request : execution.application.SeedRequest owner coordinate)
    (sent : ∃ message ∈ (app).outputs (execution.recall owner),
      PhaseSeedScheduler.ownPacket coordinate owner message = true) :
    onePacketActions runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner) = {⟨none⟩} := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have inputRecall := (app).history_inputRecall initial horizon scheduler raw
  have sentInput : ∃ message ∈ execution.network.inputs,
      PhaseSeedScheduler.ownPacket coordinate owner message = true := by
    obtain ⟨message, output, addressed⟩ := sent
    rw [← inputRecall owner] at output
    exact ⟨message, (List.mem_filter.mp output).1, addressed⟩
  have recalled := countRecall_history runtime leaks raw
  have serials := (app).serialsBeforeNext_history scheduler initial horizon raw
  apply Finset.ext
  intro action
  constructor
  · intro offered
    apply Finset.mem_singleton.mpr
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        exfalso
        obtain ⟨_, allowed⟩ := (mem_onePacketActions runtime leaks bounds owner
          (execution.recall owner) (execution.observe app owner) ⟨some material⟩).mp offered
        rcases allowed with silent | ⟨actualMaterial, transmitted, permitted⟩
        · cases silent
        have same : actualMaterial = material := Option.some.inj transmitted.symm
        subst actualMaterial
        let message := localEnvelope runtime leaks owner (execution.recall owner)
          (execution.observe app owner) material
        let after := execution.respond app owner ⟨some material⟩
        obtain ⟨appended, fresh, _⟩ :=
          permits_respond runtime leaks execution recalled owner material
        have permittedAfter : Permits after.network.inputs message :=
          (permits_eq_true_iff _ _).mp (fresh.trans permitted)
        have authentic : message ∈ after.network.inputs := by
          rw [appended]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        obtain ⟨event, named, _⟩ :=
          (WitnessedPacket.tokenValid_iff message.payload.packet).mp permittedAfter.1
        have acting : graph.actor? event = some owner :=
          countCallCorrect_owned_event _ (nativeMessage message) permittedAfter.2.1 named
        obtain ⟨phase, installed, member⟩ := localEnvelope_phase runtime leaks execution owner
          material event permittedAfter.1 named
        have currentTag : message.payload.attempt = execution.application.attempt := rfl
        have configEq : after.application.current.native.config =
            execution.application.current.native.config := by
          change (submitStep _ owner _).config = _
          rw [submitStep_config, (material.call.register_facts owner _).1]
        obtain ⟨old, oldInput, oldOwner, oldTag, oldNamed⟩ :
            ∃ old ∈ execution.network.inputs, old.sender = owner ∧
              old.payload.attempt = execution.application.attempt ∧
              old.payload.packet.call.event? graph = some event := by
          by_cases completed : event ∈ execution.application.current.native.config.cut.completed
          · exact phase_completed_owned_message runtime leaks plan inputs horizon scheduler raw
              phase (Option.mem_def.mp installed) event member owner acting completed
              request.2.2.2.2
          · obtain ⟨afterTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution
              owner ⟨some material⟩ trace offered
            have ready := ready_of_current_authentic_token runtime leaks plan inputs horizon
              scheduler (menu.toRawTrace initial horizon scheduler afterTrace) message authentic
              currentTag permittedAfter.1 event named (by rwa [configEq])
            rw [configEq] at ready
            have same : event = coordinate.event := ordered.ready_actor_unique
              execution.application.current.native.config.cut request.2.2.1 ready
                request.2.2.2.1 acting
            subst event
            obtain ⟨old, oldInput, oldPacket⟩ := sentInput
            have fields := of_decide_eq_true oldPacket
            exact ⟨old, oldInput, fields.1, fields.2.1.trans request.1,
              fields.2.2⟩
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
        apply permittedAfter.2.2.1 old oldBefore
        simp only [event?, oldNamed, named, Option.map_some, oldTag, currentTag]
  · intro silent
    rw [Finset.mem_singleton.mp silent]
    exact silence_onePacket runtime leaks bounds owner _ _

end Vegas.EventGraphRuntime.PhaseCount

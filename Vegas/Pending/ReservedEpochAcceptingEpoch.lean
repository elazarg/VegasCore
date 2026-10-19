/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochDelivery
import Vegas.Pending.ReservedEpochAdmission
import Vegas.Pending.PhaseCountedRequestResolution
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveMonitoring

/-! # Accepting delivery of a certified current packet in a reserved epoch -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Foreign policies are arbitrary raw policies. Only the designated author's
permanent input audit is used to identify its sole current envelope. -/
theorem processing_segment_receipt {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (physicalHorizon remaining cycle slot : Nat)
    (packets : List (Message Player (app).Payload)) (before after : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) physicalHorizon
      (family runtime leaks packetBudget tape)).Trace
        (some ⟨remaining + packets.length, none, before⟩))
    (orderedBefore : before.application.Ordered)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + slot)
    (room : slot + packets.length ≤ packetBudget)
    (epoch : tape.processes cycle = true) (pending : before.network.pending = packets)
    (message : Message Player (CommitAttemptPacket graph)) (member : message ∈ packets)
    (event : graph.EventId)
    (certificate : ReadyCall before.application message.payload.packet.call event)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (timely : before.application.current.native.WithinDeadline runtime event)
    (clean : ∀ packet ∈ before.network.inputs, packet.sender = message.sender →
      PhaseCount.permits before.network.inputs packet = true)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      packets.length before).support) :
    (message.id, true) ∈ after.receipts := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks packetBudget tape
  induction packets generalizing slot before after with
  | nil => cases member
  | cons head rest ih =>
      have reserved : slot < packetBudget := by simp only [List.length_cons] at room; omega
      have roundEq : (app).round scheduler players before =
          (app).dispatch players (process runtime leaks (before.observeEnvironment app))
            before := by
        simp only [scheduler, ReactiveApplication.round, family, PMF.pure_bind]
        rw [cursor, processing_at runtime leaks packetBudget tape cycle slot _ reserved epoch]
      simp only [List.length_cons, ReactiveApplication.runRounds] at reached
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have rounded : middle ∈ ((app).round scheduler players before).support := moved
      change middle ∈ ((app).round scheduler players before).support at moved
      rw [roundEq] at moved
      have middleEq : middle = { before.includePending app head.id with
          environmentRecall := before.environmentRecall ++
            [⟨before.observeEnvironment app, .include head.id⟩] } := by
        rw [process_dispatch runtime leaks players before head rest pending] at moved
        exact (PMF.mem_support_pure_iff _ _).mp moved
      have included : middle ∈ (before.environmentStep app (.include head.id)).support := by
        rw [middleEq]
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff _ _]
      have source : ((app).protocol initial physicalHorizon scheduler).Trace
          (some ⟨(remaining + rest.length) + 1, none, before⟩) := by
        simpa only [List.length_cons, Nat.add_assoc] using trace
      obtain ⟨middleTrace⟩ := (app).raw_trace_round initial physicalHorizon scheduler players
        (remaining + rest.length) before middle source rounded
      have step := process_step runtime leaks players before middle head rest pending moved
      have input : message ∈ before.network.inputs := by
        have envelopes := (app).retained_envelopes_mem_inputs before
          ((app).history_provenance initial physicalHorizon scheduler trace)
          ((app).history_inputRecall initial physicalHorizon scheduler trace)
        exact envelopes.pending message (by rw [pending]; exact member)
      rcases List.mem_cons.mp member with same | later
      · subst head
        obtain ⟨target, handled⟩ := readyCall_accepts runtime leaks plan inputs physicalHorizon
          scheduler _ trace message input event certificate request timely clean
        have receipted : (message.id, true) ∈ middle.receipts := by
          rw [middleEq]
          change (message.id, true) ∈ (before.includePending app message.id).receipts
          rw [(include_head runtime leaks before message rest pending).2.2, handled]
          simp
        exact ((app).receipt_policyInvariant players (message.id, true)).runRounds scheduler
          rest.length middle after receipted continued
      · by_cases receipted : (message.id, true) ∈ middle.receipts
        · exact ((app).receipt_policyInvariant players (message.id, true)).runRounds scheduler
            rest.length middle after receipted continued
        · have nextRequest : middle.application.SeedRequest message.sender
              ⟨message.payload.attempt, event⟩ := by
            by_contra lost
            have accepted := PhaseCount.timely_request_loss_accepts runtime leaks plan ordered
              inputs physicalHorizon scheduler _ trace message.sender
                ⟨message.payload.attempt, event⟩
                (fun packet present authored =>
                  (PhaseCount.permits_eq_true_iff _ _).mp (clean packet present authored))
                request timely message input rfl rfl (by
                  cases certificate with
                  | binding candidate call => rw [call]; rfl
                  | opening owner payload binding checks outputEq codeEq node
                      candidate raw call _ =>
                      rw [call]; rfl) middle
                (.include head.id) included lost
            exact receipted accepted.2.2.2.1
          obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs
            physicalHorizon scheduler trace
          have sameAttempt : before.application.attempt = middle.application.attempt :=
            request.1.symm.trans nextRequest.1
          obtain ⟨ticks, progress⟩ :=
            (phaseApplication_serviceProgress runtime leaks).environmentStep
            before middle (.include head.id) included draw valid orderedBefore sameAttempt
          have clock := PhaseSeedCalendar.environmentStep_clock runtime leaks before middle
            (.include head.id) valid included
          change middle.application.current.native.clock =
            before.application.current.native.clock + 0 at clock
          rw [Nat.add_zero] at clock
          have nextCertificate := ReadyCall.environment runtime leaks (.include head.id) included
            orderedBefore sameAttempt message.payload.packet.call event certificate
          have nextTimely : middle.application.current.native.WithinDeadline runtime event := by
            cases stamp : before.application.current.native.activatedAt event with
            | none => simp only [State.WithinDeadline, stamp] at timely
            | some entered =>
                have nextStamp := progress.activated event entered stamp nextRequest.2.2.1.1
                simpa only [State.WithinDeadline, stamp, nextStamp, clock] using timely
          have nextClean : ∀ packet ∈ middle.network.inputs, packet.sender = message.sender →
              PhaseCount.permits middle.network.inputs packet = true := by
            rw [(app).environmentStep_inputs before middle (.include head.id) included]
            exact clean
          have nextOrdered := (phaseApplication_seedOrder runtime leaks).environmentStep
            before middle (.include head.id) orderedBefore included
          have nextCursor : middle.environmentRecall.length =
              cycle * cycleWidth (graph := graph) packetBudget + (slot + 1) := by
            rw [step.2.2.2.2, cursor]
            omega
          exact ih (slot + 1) middle after middleTrace nextOrdered nextCursor
            (by simp only [List.length_cons] at room; omega) step.1 later nextCertificate
              nextRequest nextTimely nextClean continued

end Vegas.EventGraphRuntime.ReservedEpoch

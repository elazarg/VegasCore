/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochCommandShape
import Vegas.Pending.ReservedEpochClockAccounting
import Vegas.Pending.PhaseSeedRecordedWait
import Vegas.Pending.PhaseTimelyResolution
import Interaction.ReactiveRoundBoundary
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveStopping

/-! # A protected readiness episode survives until the next processing epoch -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem request_until_processing_boundary {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (physicalHorizon remaining count : Nat)
    (before after : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) physicalHorizon
      (family runtime leaks packetBudget tape)).Trace
        (some ⟨remaining + count, none, before⟩))
    (orderedBefore : before.application.Ordered)
    (sentCycle slot cycle : Nat)
    (cursor : before.environmentRecall.length =
      sentCycle * cycleWidth (graph := graph) packetBudget + slot)
    (afterProcessing : packetBudget ≤ slot)
    (quiet : ∀ later, sentCycle < later → later < cycle → tape.processes later = false)
    (room : before.environmentRecall.length + count ≤
      cycle * cycleWidth (graph := graph) packetBudget)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (entered : Nat)
    (request : before.application.SeedRequest owner coordinate)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (timely : before.application.current.native.WithinDeadline runtime coordinate.event)
    (inTime : cycle - entered < runtime.deadline coordinate.event)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players count
      before).support) :
    after.application.SeedRequest owner coordinate ∧
      after.application.current.native.activatedAt coordinate.event = some entered := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks packetBudget tape
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs physicalHorizon
    scheduler trace
  have age : before.application.current.native.clock - entered <
      runtime.deadline coordinate.event := by
    simpa only [State.WithinDeadline, stamp] using timely
  have retained : ClosedCoordinateBound runtime before.application.current.native.clock entered
      coordinate before.application :=
    ⟨le_rfl, valid.active.activated_le coordinate.event entered stamp,
      by rw [request.1], by rw [request.1], fun _ => Or.inr ⟨request.2.2.1, stamp, age⟩⟩
  have afterRequest : after.application.SeedRequest owner coordinate := by
    by_contra lostAfter
    obtain ⟨used, tail, prior, middle, resumed, selected, lengthEq, prefixReached, priorRequest,
        chosen, moved, lost, _response, _future⟩ :=
      (app).runRounds_environment_boundary scheduler players
        (fun execution => execution.application.SeedRequest owner coordinate)
        (fun execution actor action request =>
          respond_request runtime leaks execution actor action owner coordinate request)
        count before after request reached lostAfter
    have prefixCount : used ≤ remaining + count := by omega
    have prefixSource : ((app).protocol initial physicalHorizon scheduler).Trace
        (some ⟨(remaining + count - used) + used, none, before⟩) := by
      simpa only [Nat.sub_add_cancel prefixCount] using trace
    obtain ⟨priorTrace⟩ := (app).raw_trace_runRounds initial physicalHorizon scheduler players
      (remaining + count - used) used before prior prefixSource prefixReached
    have priorCursor := (app).runRounds_environmentRecall_length scheduler players used before
      prior prefixReached
    have later : sentCycle * cycleWidth (graph := graph) packetBudget + slot ≤
        prior.environmentRecall.length := by omega
    have earlier : prior.environmentRecall.length <
        cycle * cycleWidth (graph := graph) packetBudget := by omega
    have clock := clock_history runtime leaks packetBudget tape plan inputs physicalHorizon
      ⟨remaining + count - used, none, prior⟩ priorTrace
    have clockBefore : prior.application.current.native.clock < cycle := by
      rw [clock]
      exact (Nat.div_lt_iff_lt_mul (cycleWidth_pos packetBudget)).mpr earlier
    have priorBound := PhaseSeedCalendar.retained_bound_runRounds runtime leaks scheduler players
      used before prior valid orderedBefore before.application.current.native.clock entered
        coordinate retained prefixReached
    have priorStamp : prior.application.current.native.activatedAt coordinate.event =
        some entered := by
      rcases priorBound.event priorRequest.1 with complete | active
      · exact (priorRequest.2.2.1.1 complete).elim
      · exact active.2.1
    have priorTimely : prior.application.current.native.WithinDeadline runtime coordinate.event :=
        by
      simp only [State.WithinDeadline, priorStamp]
      omega
    obtain ⟨_priorDraw, priorValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs
      physicalHorizon scheduler priorTrace
    obtain ⟨identifier, packet, native, ready, action, included, _found, _sender, _named,
        _accepted, _stepped, _normalized⟩ := timely_first_request_loss_includes runtime leaks
      ordered prior middle priorValid owner coordinate priorRequest priorTimely selected moved lost
    have selectedEq := (family_support runtime leaks packetBudget tape prior.environmentRecall
      (prior.observeEnvironment app) selected).mp chosen
    have noInclude := no_include_between_epochs runtime leaks packetBudget tape sentCycle slot
      cycle afterProcessing quiet prior.environmentRecall.length (prior.observeEnvironment app)
        later earlier identifier
    exact noInclude (selectedEq.symm.trans included)
  have afterBound := PhaseSeedCalendar.retained_bound_runRounds runtime leaks scheduler players
    count before after valid orderedBefore before.application.current.native.clock entered
      coordinate retained reached
  refine ⟨afterRequest, ?_⟩
  rcases afterBound.event afterRequest.1 with complete | active
  · exact (afterRequest.2.2.1.1 complete).elim
  · exact active.2.1

end Vegas.EventGraphRuntime.ReservedEpoch

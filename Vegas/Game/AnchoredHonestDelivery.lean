/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredHonestLaw
import Vegas.Game.OnePacketPrescribedSupport
import Interaction.ReactiveAnchoredSupport
import Interaction.ReactiveResponseAccounting

/-! # As-if-honest play from a reached boundary never delivers late

From a one-packet history ending between rounds at a reached boundary decoding
to a point of the intended game, the rounds of as-if-honest play are those of
the anchored first-turn clients of the intended effective opening, which have
submitted for every event they had a turn at. So no information state
as-if-honest play reaches from that history is a late delivery
(`Vegas.not_lateDelivery_of_honestReachedFrom`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **As-if-honest play from a reached boundary never delivers late.** Under
the asynchronous contract with timely delays and retention of first covered
canonical packets, from a one-packet history ending between rounds at a reached
boundary decoding to a point of the intended game, no information state
as-if-honest play of an intended assessment reaches is a late delivery. -/
theorem not_lateDelivery_of_honestReachedFrom [Fintype Player]
    (bounds : MessageBounds (graph setup)) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    {who : Player} {info : (application setup leaks).Info}
    (reachedInfo : HonestReachedFrom setup leaks bounds horizon scheduler assessment start who
      info) :
    ¬ LateDelivery setup leaks who info := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨fuel, history, mem, infoEq⟩ := reachedInfo
  have supported := menu.runRoundsSupported_of_mem_run (initialLaw setup) horizon scheduler
    (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
    start history state mem
  have observed : app.observe who history.state = info :=
    (menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler history.trace
  have anchorTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨horizon - (anchor.environmentRecall.length + 0), none, anchor⟩) := by
    rw [Nat.add_zero, ← state]
    exact start.trace
  rintro ⟨past, view, event, same, pending, entry, member, activated⟩
  subst same
  obtain ⟨_, eventReady, owned, unrecorded⟩ := pendingEvent_spec pending
  generalize history.state = current at supported observed rawTrace
  rcases current with _ | ⟨remaining, actor, execution⟩
  · cases observed
  rcases actor with _ | player
  · simp [ReactiveApplication.observe] at observed
  by_cases same : player = who
  · subst same
    simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      at observed
    obtain ⟨pastEq, viewEq⟩ := observed
    obtain ⟨count, prior, command, priorMem, _, active, stepped⟩ := supported
    have commandEq : command = .activate player := by
      cases command with
      | activate actor =>
          exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
      | wait | «include» _ | application _ => cases active
    subst commandEq
    have priorLength := app.runRounds_environmentRecall_length scheduler
      (menu.decodeProfile (initialLaw setup) horizon scheduler
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment))
      count anchor prior priorMem
    have stepLength := app.environmentStep_environmentRecall prior execution _ stepped
    have accounted := app.raw_trace_horizon (initialLaw setup) horizon scheduler rawTrace
    have stepLengthEq := congrArg List.length stepLength
    simp only [List.length_append, List.length_singleton] at stepLengthEq
    change execution.environmentRecall.length + remaining = horizon at accounted
    have within : anchor.environmentRecall.length + count ≤ horizon := by omega
    have honestRounds := runRounds_honest_eq_anchoredClients bounds contract timely 0 assessment
      retains reached point decoded intendedPoint count 0 (by omega) anchor
      ((PMF.mem_support_pure_iff _ _).mpr rfl) ⟨anchorTrace⟩
    rw [honestRounds] at priorMem
    have appEq := activation_application setup leaks prior execution player stepped
    have recallEq := app.environmentStep_recall prior execution _ stepped
    have ready : prior.application.config.cut.Ready event := by
      rw [← appEq]
      have viewReady : (execution.observe app player).application.publicView.EventReady event := by
        rw [viewEq]
        exact eventReady
      exact (execution.application.publicView_eventReady event).mp viewReady
    have recorded := reachedBoundary_recorded_of_seen contract timely 0 assessment.strategy
      reached point decoded intendedPoint within priorMem player event owned ready
      ⟨entry, by rw [← recallEq, pastEq]; exact member, activated⟩
    rw [← recallEq, pastEq, unrecorded] at recorded
    cases recorded
  · simp [ReactiveApplication.observe, same] at observed

end Vegas

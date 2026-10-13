/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketSlotLaw
import Interaction.ReactiveSupportedRounds

/-! # Discharging inputs of the one-packet certificate

As-if-honest play never reaches a late delivery: every information state it
reaches is a round-supported state of as-if-honest play read as native
policies, whose rounds are those of the first-turn clients of the intended
effective opening, and those clients have submitted for every event they had a
turn at (`Vegas.not_lateDelivery_of_honestReached`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Honest

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- Within the horizon, as-if-honest play read as native policies reaches the
executions the first-turn clients of the intended effective opening reach. -/
theorem roundsFrom_honest_eq_openingClients (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound) {count : Nat}
    (within : count ≤ horizon) :
    (application setup leaks).roundsFrom (initialLaw setup) scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
          scheduler (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler
            assessment)) count =
      (application setup leaks).roundsFrom (initialLaw setup) scheduler
        (openingClients setup leaks bound 0 assessment.strategy) count := by
  unfold ReactiveApplication.roundsFrom
  apply bind_congr_on_support _
  intro state stateMem
  exact runRounds_honest_eq_openingClients bounds wellFormed contract timely 0 assessment retains
    count 0 (by omega) _
    ((PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateMem, (PMF.mem_support_pure_iff _ _).mpr rfl⟩)
    ((bounds.onePacketMenu (runtime setup) leaks).trace_initial (initialLaw setup) horizon
      scheduler state stateMem)

/-- **As-if-honest play never reaches a late delivery.** For a well-formed
setup, under the asynchronous contract with timely delays and retention of
first covered canonical packets, no information state as-if-honest play
reaches is a late delivery. -/
theorem not_lateDelivery_of_honestReached (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    {who : Player} {info : (application setup leaks).Info}
    (reached : HonestReached setup leaks bounds horizon scheduler assessment who info) :
    ¬ LateDelivery setup leaks who info := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨fuel, history, mem, infoEq⟩ := reached
  have supported := menu.roundSupported_of_mem_run (initialLaw setup) horizon scheduler
    (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
    history mem
  have observed : app.observe who history.state = info :=
    (menu.info (initialLaw setup) horizon scheduler who history.trace).symm.trans infoEq
  rintro ⟨past, view, event, same, pending, entry, member, activated⟩
  subst same
  obtain ⟨_, _, owned, unrecorded⟩ := pendingEvent_spec pending
  generalize history.state = state at supported observed
  rcases state with _ | ⟨remaining, actor, execution⟩
  · cases observed
  rcases actor with _ | player
  · simp [ReactiveApplication.observe] at observed
  by_cases same : player = who
  · subst same
    simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      at observed
    obtain ⟨pastEq, _⟩ := observed
    obtain ⟨accounted, count, prior, command, position, priorMem, _, _, stepped⟩ := supported
    have within : count ≤ horizon := by dsimp at accounted position; omega
    rw [roundsFrom_honest_eq_openingClients bounds wellFormed contract timely assessment retains
      within] at priorMem
    have recalled : execution.recall player = prior.recall player :=
      congrFun (app.environmentStep_recall prior execution command stepped) player
    have recorded := openingClients_recorded_of_seen wellFormed contract timely 0
      assessment.strategy within priorMem player event owned
      ⟨entry, by rw [← recalled, pastEq]; exact member, activated⟩
    rw [← recalled, pastEq, unrecorded] at recorded
    cases recorded
  · simp [ReactiveApplication.observe, same] at observed

end Honest

end Vegas

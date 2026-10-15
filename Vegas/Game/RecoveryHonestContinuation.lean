/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryBoundaryWaiting
import Vegas.Game.RecoverySuccessorBoundary
import Vegas.Game.RecoveryTerminalSourceLaw
import Vegas.Game.RecoveryChanceStoppedLaw

/-! # Honest source continuation on the actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

include initialized nativeLaw opportunity inclusion timely completes in
/-- Honest finite-menu play from an intended source boundary has the source
continuation law under actual recovery service and completion. -/
theorem recovery_honest_boundary_readout_law
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) :
    ∀ rank (start : (E).History) (execution : (application setup leaks).Execution),
      start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩ →
      ReachedBoundary setup leaks horizon scheduler rank execution →
      ∀ point, sourceServicePrefix? setup rank execution.application.config = some point →
        ProtocolState.Intended setup.program point →
      ((N).runBehavioralTerminalFrom certificate
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source) start).map
          (fun final => sourceReadout setup leaks final.state) =
        sourceContinuation setup (setup.intendedOpeningProfile source.strategy) rank
          execution.application.config := by
  classical
  let players := honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source
  let profile := setup.intendedOpeningProfile source.strategy
  let continuation := fun state : Option (ProtocolState setup.program) =>
    (setup.continuationLaw profile state).map some
  suffices remaining : ∀ gap rank (start : (E).History)
      (execution : (application setup leaks).Execution),
      (graph setup).order.eventCount - rank = gap →
      start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩ →
      ReachedBoundary setup leaks horizon scheduler rank execution →
      ∀ point, sourceServicePrefix? setup rank execution.application.config = some point →
        ProtocolState.Intended setup.program point →
      ((N).runBehavioralTerminalFrom certificate players start).map
          (fun final => sourceReadout setup leaks final.state) =
        sourceContinuation setup profile rank execution.application.config by
    intro rank start execution state boundary point decoded intended
    exact remaining _ rank start execution rfl state boundary point decoded intended
  intro gap
  induction gap with
  | zero =>
      intro rank start execution gapEq state boundary point decoded intended
      have rankEq : rank = (graph setup).order.eventCount := by
        have within := boundary.ordered.1
        change rank ≤ (graph setup).order.eventCount at within
        omega
      subst rank
      exact terminalPrefix_readout_law bounds certificate players start _ state boundary.ordered
        profile
  | succ gap ih =>
      intro rank start execution gapEq state boundary point decoded intended
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      have ready := (ready_iff_rank setup _ rank boundary.ordered event).mpr rfl
      have trace : (E).Trace
          (some ⟨horizon - execution.environmentRecall.length, none, execution⟩) :=
        state ▸ start.trace
      have clear := publicExclusionRecord_of_decodedIntended
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace)
        ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded) intended
      cases owned : (graph setup).actor? event with
      | none =>
          obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual profile (menu) horizon scheduler
            start.trace _ state
          have rankEq := isPrefix_unique residual.checkpoint.ordered boundary.ordered
          subst found
          let action := ((graph setup).nodes event).actionOfActorNone owned
          let stopping := fun history : (E).History =>
            LateStopped setup leaks bounds horizon scheduler rank history ∨
              ¬ Clear history.state
          have configLaw := recovery_chance_stopped_configLaw initialized nativeLaw completes
            certificate players start state boundary.ordered event ready owned action decoded
            intended
          rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players stopping,
            PMF.map_bind]
          calc
            _ = ((N).runBehavioralUntil certificate players stopping start).bind
                (fun final => continuation (nativeDecodedState setup leaks final.state)) := by
              refine bind_congr_on_support _ fun final supported => ?_
              have mapped : final.state.map (fun next => next.execution.application.config) ∈
                  ((execution.application.config.step event ready action).map some).support := by
                rw [← configLaw, PMF.mem_support_map_iff]
                exact ⟨final, supported, rfl⟩
              obtain ⟨nextConfig, compiled, sameConfig⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp mapped
              cases finalState : final.state with
              | none =>
                  rw [finalState] at sameConfig
                  cases sameConfig
              | some control =>
                  rw [finalState] at sameConfig
                  have configEq : nextConfig = control.execution.application.config :=
                    Option.some.inj sameConfig
                  have compiledAt : control.execution.application.config ∈
                      (execution.application.config.step event ready action).support :=
                    by rw [← configEq]; exact compiled
                  obtain ⟨before, target, beforeDecoded, afterDecoded, stepped⟩ :=
                    decodedPoint_step residual event ready action _ compiledAt
                  have decodedHere : decodedPoint setup execution.application.config = some point :=
                    (decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded
                  rw [decodedHere] at beforeDecoded
                  cases Option.some.inj beforeDecoded
                  have actors : ∀ player, ProtocolView.actor player setup.program
                      (ProtocolState.observe player setup.program point) = none :=
                    fun player => (decodedPoint_actor player ready decodedHere).trans owned
                  have targetIntended : ProtocolState.Intended setup.program target := by
                    refine ProtocolState.intended_step_of_actors setup.program point _ target
                      intended (fun player active => ?_) stepped
                    rw [actors player] at active
                    cases active
                  have decodedFinal : nativeDecodedState setup leaks final.state = some target := by
                    rw [finalState]
                    exact afterDecoded
                  obtain ⟨successor, successorState, _clear, _completed, nextDecoded,
                      nextBoundary⟩ :=
                    recovery_stopped_boundary_of_intended initialized nativeLaw completes
                      certificate
                      players start state boundary.ordered event ready final supported decodedFinal
                      targetIntended
                  have continued := ih (rank + 1) final successor (by omega) successorState
                    nextBoundary target nextDecoded targetIntended
                  refine continued.trans ?_
                  change continuation (sourceServicePrefix? setup (rank + 1)
                    successor.application.config) = continuation
                      (nativeDecodedState setup leaks (some control))
                  exact (congrArg continuation nextDecoded).trans
                    (congrArg continuation afterDecoded).symm
            _ = sourceContinuation setup profile rank execution.application.config :=
              recovery_chance_stopped_sourceContinuation initialized nativeLaw completes certificate
                players start state event owned profile residual rfl decoded intended
      | some owner =>
          let waiting := fun history : (E).History =>
            (application setup leaks).actor history.state = some owner
          rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players waiting,
            PMF.map_bind]
          calc
            _ = ((N).runBehavioralUntil certificate players waiting start).bind
                (fun _ => sourceContinuation setup profile rank execution.application.config) := by
              refine bind_congr_on_support _ fun callback supported => ?_
              obtain ⟨remaining, anchor, current, same, callbackClear, recalledEq, pending,
                  never⟩ :=
                recovery_boundary_firstActivation initialized nativeLaw opportunity timely completes
                  certificate players start state boundary clear decoded intended owner event rfl
                  owned callback supported
              let stopping := fun history : (E).History =>
                LateStopped setup leaks bounds horizon scheduler rank history ∨
                  ¬ Clear history.state
              have installed : Profile.update (sig := (N).behavioralSignature) players owner
                  ((players owner).withLaw ((N).infoOf owner callback.trace)
                    (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source
                      owner ((N).infoOf owner callback.trace))) = players := by
                change Profile.update (sig := (N).behavioralSignature) players owner
                  ((players owner).withLaw ((N).infoOf owner callback.trace)
                    (players owner ((N).infoOf owner callback.trace))) = players
                rw [BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self]
              have sourceLaw := recovery_firstActivation_honest_sourceLaw initialized nativeLaw
                opportunity inclusion timely completes wellFormed covers capacity source
                certificate
                players callback current callbackClear event pending never (same ▸ boundary.ordered)
                (same ▸ decoded) intended _ rfl
              rw [installed] at sourceLaw
              rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players
                stopping, PMF.map_bind]
              calc
                _ = ((N).runBehavioralUntil certificate players stopping callback).bind
                    (fun final => continuation (nativeDecodedState setup leaks final.state)) := by
                  refine bind_congr_on_support _ fun final reached => ?_
                  have supportedInstalled : final ∈ ((N).runBehavioralUntil certificate
                      (Profile.update (sig := (N).behavioralSignature) players owner
                        ((players owner).withLaw ((N).infoOf owner callback.trace)
                          (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
                            source owner ((N).infoOf owner callback.trace))))
                      stopping callback).support := by
                    rw [installed]
                    exact reached
                  obtain ⟨target, successor, _step, targetIntended, finalState, _clear, _completed,
                      nextDecoded, nextBoundary⟩ :=
                    recovery_firstActivation_honest_successorBoundary initialized nativeLaw
                      completes
                      opportunity inclusion timely wellFormed covers capacity source certificate
                      players callback current callbackClear event pending never
                      (same ▸ boundary.ordered) (same ▸ decoded) intended _ rfl final
                      supportedInstalled
                  have continued := ih (rank + 1) final successor (by omega) finalState nextBoundary
                    target nextDecoded targetIntended
                  refine continued.trans ?_
                  have decodedFinal : nativeDecodedState setup leaks final.state = some target := by
                    rw [finalState]
                    exact (decodedPoint_eq_of_isPrefix nextBoundary.ordered).trans nextDecoded
                  change continuation (sourceServicePrefix? setup (rank + 1)
                    successor.application.config) = continuation
                      (nativeDecodedState setup leaks final.state)
                  exact (congrArg continuation nextDecoded).trans
                    (congrArg continuation decodedFinal).symm
                _ = ((ProtocolState.behavioralStateStep setup.program profile point).map
                    some).bind continuation := by
                  rw [← sourceLaw, PMF.bind_map]
                  rfl
                _ = sourceContinuation setup profile rank execution.application.config := by
                  rw [PMF.bind_map]
                  change (ProtocolState.behavioralStateStep setup.program profile point).bind
                    (fun next => (ProtocolState.continuationLaw setup.program profile next).map
                      some) = sourceContinuation setup profile rank execution.application.config
                  rw [← PMF.map_bind, sourceStep_continuation]
                  change continuation (some point) = continuation
                    (sourceServicePrefix? setup rank execution.application.config)
                  exact (congrArg continuation decoded).symm
            _ = _ := PMF.bind_const _ _

end Vegas

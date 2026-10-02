/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSiteBridge

/-! # Completion after an actually supported response

An active control supported by the actual players contains the preceding
scheduler command and environment move. A supported current response finishes
that round, so its execution is supported from initialization with the horizon
accounted by actual environment recall.

At a ready site, complete play then places every completion-stopped execution
at the next completion boundary. Approximate boundary continuation laws transfer
to the response readout through the stopping Markov law. The scheduler and
foreign policies are arbitrary; no calendar, response menu or equilibrium
assessment is involved.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A supported response at an actual active control finishes its supported
scheduler round and preserves the remaining horizon budget. -/
theorem sourceResponse_roundSupported {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {execution : (application setup leaks).Execution} {who : Player}
    (active : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (chosen : response ∈ (players who (execution.recall who)
      (execution.observe (application setup leaks) who)).support) :
    (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler players
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) := by
  let app := application setup leaks
  obtain ⟨accounted, count, prior, command, position, priorMem, selected, acting, moved⟩ := active
  change (execution.respond app who response).environmentRecall.length + remaining = horizon ∧
    execution.respond app who response ∈ (app.roundsFrom (initialLaw setup) scheduler players
      (execution.respond app who response).environmentRecall.length).support
  rw [app.respond_environmentRecall]
  refine ⟨accounted, ?_⟩
  rw [position, app.roundsFrom_succ, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨prior, priorMem, ?_⟩
  rw [ReactiveApplication.round, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨command, selected, ?_⟩
  rw [ReactiveApplication.dispatch, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨execution, moved, ?_⟩
  rw [acting]
  change execution.respond app who response ∈ (app.invoke players who execution).support
  rw [ReactiveApplication.invoke, PMF.support_map]
  exact ⟨response, chosen, rfl⟩

namespace ReadySite

variable {execution : (application setup leaks).Execution}
  (site : ReadySite setup leaks execution)

/-- Every stopped continuation of a supported current response reaches the
next completion boundary within the actual raw horizon. -/
theorem completion_boundary_roundSupported {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {who : Player}
    (active : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (chosen : response ∈ (players who (execution.recall who)
      (execution.observe (application setup leaks) who)).support)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ (site.completionLaw scheduler horizon players who response).support) :
    stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players (site.event.val + 1) stopped := by
  have supported := sourceResponse_roundSupported active response chosen
  have lengthEq := congrArg List.length
    ((application setup leaks).respond_environmentRecall execution who response)
  have accounted := supported.1
  rw [lengthEq] at accounted
  have responded := supported.2
  rw [lengthEq] at responded
  exact site.completion_boundary_of_supported completes who response responded (by omega)
    stopped reached

/-- Approximate boundary continuation laws give the same error after an actual
supported response, averaged over its completion configuration law. -/
theorem response_completion_within_roundSupported {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (continuation : BoundaryContinuationWithin setup leaks scheduler horizon players profile error)
    {who : Player}
    (active : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (chosen : response ∈ (players who (execution.recall who)
      (execution.observe (application setup leaks) who)).support) :
    PMF.WithinTV (error (site.event.val + 1))
      (sourceResponseReadout scheduler horizon players execution who response)
      ((site.completionConfigLaw scheduler horizon players who response).bind
        (sourceContinuation setup profile (site.event.val + 1))) := by
  have supported := sourceResponse_roundSupported active response chosen
  have lengthEq := congrArg List.length
    ((application setup leaks).respond_environmentRecall execution who response)
  have accounted := supported.1
  rw [lengthEq] at accounted
  have responded := supported.2
  rw [lengthEq] at responded
  exact site.response_completion_within completes continuation who response responded (by omega)

end ReadySite

/-- Under the asynchronous contract and effective source disclosures, an
actually supported turn-policy response has the remaining deferral-weight
error of the source continuation after its event completes. -/
theorem sourceServiceTurnPolicy_response_completion_within [Finite Player]
    {horizon remaining turns : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    {execution : (application setup leaks).Execution} {who : Player}
    (site : ReadySite setup leaks execution)
    (active : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile)
      (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (chosen : response ∈ (sourceServiceTurnPolicy setup leaks bound turns timing profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
    PMF.WithinTV
      (∑ event ∈ Finset.univ.filter
        (fun event : (graph setup).EventId => site.event.val + 1 ≤ event.val),
        timing.deferral event)
      (sourceResponseReadout scheduler horizon
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) execution who response)
      ((site.completionConfigLaw scheduler horizon
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) who response).bind
          (sourceContinuation setup profile (site.event.val + 1))) := by
  exact site.response_completion_within_roundSupported contract.completes
    (sourceServiceTurnPolicy_boundaryContinuationWithin
      (sourceServiceTurnPolicy_firstTurnCompletes contract timely timing profile effective))
    active response chosen

end Vegas

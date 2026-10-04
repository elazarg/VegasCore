/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLateDecisionCompletion
import Vegas.Game.SourceServiceRecordedResolutionTraffic

/-! # Late canonical completion with the actual future turn policy

After a timely canonical call, real own recall suppresses further calls until
this event completes. The turn policy's complete stopped execution law is
therefore the silent completion law, while its behavior at later events is
retained. Actual completion is the chosen effective step or a public miss.
This is an operational bridge, without an acceptance-probability or payoff claim.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- After a real timely canonical attempt, the actual turn-counted continuation
records either its chosen effective step or a public miss. The owner's real
recorded call suppresses later attempts until completion; its policies at
future events are not replaced with permanent silence. -/
theorem sourceServiceCanonicalDecision_turnPolicy_include_or_miss
    {horizon remaining turns : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (bounds : MessageBounds (graph setup))
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player) (execution : (application setup leaks).Execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (action : (graph setup).Action event)
    (effective : EffectiveAction execution.application.config event action)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile)
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution.respond (application setup leaks) owner
        ((runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) event action))).support) :
    event ∈ stopped.application.config.cut.completed ∧
      (event ∈ stopped.application.missedEvents ∨ stopped.application.config ∈
        (execution.application.config.step event ready action).support) := by
  let app := application setup leaks
  let response := (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
    (execution.observe app owner) event action
  let start := execution.respond app owner response
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace _ _ _ trace
  obtain ⟨material, responseEq, _authored, _named, _seen, _realized⟩ :=
    sourceServiceCanonicalDecision_timely_realizes rawTrace event owned ready timely action
      effective
  have named : (runtime setup).submittedEvent? leaks response = some event := by
    rcases (runtime setup).canonicalServiceDecision_cases leaks owner (execution.recall owner)
      (execution.observe app owner) event action with silent | addressed
    · change response = ⟨none⟩ at silent
      change response = ⟨some material⟩ at responseEq
      have impossible := congrArg ReactiveApplication.Action.transmission
        (responseEq.symm.trans silent)
      cases impossible
    · exact addressed
  have recorded : (runtime setup).eventRecorded leaks (start.recall owner) event = true :=
    (runtime setup).eventRecorded_respond leaks execution owner response event named
  have readyStart : start.application.config.cut.Ready event := by
    rw [show start.application.config = execution.application.config from
      ((runtime setup).reactive_respond_application leaks execution owner response).1]
    exact ready
  change stopped ∈ (app.runUntilHorizon scheduler
    (sourceServiceTurnPolicy setup leaks bound turns timing profile)
    (fun final => event ∈ final.application.config.cut.completed) horizon start).support at reached
  rw [sourceServiceTurnPolicy_runUntilHorizon_of_recorded setup leaks scheduler bound turns
    timing profile horizon start owner event readyStart owned recorded] at reached
  exact sourceServiceCanonicalDecision_include_or_miss contract owner execution rawTrace
    event owned ready timely unrecorded action effective (fun _ => app.silentPolicy) rfl
      stopped reached

end Vegas

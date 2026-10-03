/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceProtectedDecisionCompletion
import Vegas.Game.SourceServiceRecordedResolutionAlignment

/-! # Actual protected source disclosures through completion

The aligned effective source disclosure kernel supplies FALSE or a successful
TRUE opening. Actual typed store agreement derives the action's operational
meaning. The same physical canonical packet completes its chosen typed result;
its traffic law remains conditional on that disclosure.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A supported effective source disclosure at an actual protected input is
accepted with the original identifier and its exact typed publication result. -/
theorem RevealSource.protected_completion
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : RevealSource setup profile event execution.application.config)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some site.owner, execution⟩))
    (ready : execution.application.config.cut.Ready event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (disclose : Bool)
    (selected : disclose ∈ (revealKernel site.residual (site.source.view site.owner)).support)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (Function.update players site.owner (application setup leaks).silentPolicy)
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution.respond (application setup leaks) site.owner
        ((runtime setup).canonicalServiceDecision leaks site.owner (execution.recall site.owner)
          (execution.observe (application setup leaks) site.owner) event
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)))).support) :
    event ∈ stopped.application.config.cut.completed ∧
      ((site.owner, execution.network.nextSerial site.owner), true) ∈ stopped.receipts ∧
      event ∉ stopped.application.missedEvents ∧
      stopped.application.config = execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
          (disclosureResult site.published site.binding site.source disclose)) := by
  have operational : EffectiveAction execution.application.config event
      (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) := by
    unfold EffectiveAction
    rw [nodeView_eq_resolve site.outputEq site.code]
    simp only [cast_cast, cast_eq]
    intro requested
    rcases effective_reveal_supported site.fresh site.binding site.unresolved site.next
        site.residual site.source (site.inherits effective site.owner) disclose selected with
      rfl | ⟨value, rfl, success⟩
    · cases requested
    · have result := compiled_disclosure_result (graph := graph setup) site.published site.binding
        site.source site.refs execution.application.config.store site.agree true
      rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at result
      exact ⟨value, result⟩
  have actual := sourceServiceCanonicalDecision_protected_completion contract site.owner execution
    trace event site.owned ready unrecorded fits
      (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) operational
      (Function.update players site.owner (application setup leaks).silentPolicy)
      (Function.update_self ..) stopped reached
  refine ⟨actual.1, actual.2.1, actual.2.2.1, ?_⟩
  have step := actual.2.2.2
  rw [execution.application.config.step_eq_map_of_code event ready site.outputEq _ site.code
    disclose (PMF.pure (disclosureResult site.published site.binding site.source disclose))
    (compileResolve_eval? site.refs site.source.registry site.source.revelations site.source.state
      execution.application.config.store site.agree site.binding disclose),
    PMF.pure_map, PMF.mem_support_pure_iff] at step
  exact step

end Vegas

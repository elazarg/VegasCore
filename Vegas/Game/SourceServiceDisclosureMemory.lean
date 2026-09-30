/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDisclosurePosterior
import Vegas.Source.DisclosurePosterior
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Actual native response and original disclosure-memory coupling

This couples the existing runtime response with the complete original source
successor. The conditional private-memory law is exactly the behavioral
disclosure normalizer's law. It retains earlier erased intentions as well as
the current one, and contains no assumed information-fiber equality.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- One guarded reveal preserves the joint actual native response and original
source successor under conditional-memory normalization. Native recall and
network contents are retained as parts of the actual execution, while the
original source history is restored only inside the proof coupling. -/
theorem guarded_disclosure_response_memory
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (choose : DecisionView owner Γ → PMF Bool) :
    let response := fun disclose => (runtime setup).serviceDecision leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    let memory := disclosureMemoryLaw published binding source.registry source.revelations
      remember choose (source.view owner)
    ((source.restoreMemory owner remember).bind fun original =>
      (choose (original.view owner)).map fun intended =>
        (execution.respond (application setup leaks) owner (response intended),
          revealSuccessor published binding original intended)) =
      (memory.map Prod.fst).bind fun effective =>
        ((fiberPosterior memory Prod.fst effective).map Prod.snd).map fun past =>
          (execution.respond (application setup leaks) owner (response effective),
            (revealSuccessor published binding source effective).withOwnHistory owner past) := by
  intro response memory
  have law := disclosureMemoryLaw_disintegrate published binding source.registry
    source.revelations remember choose (source.view owner) (fun effective past =>
      PMF.pure
        (execution.respond (application setup leaks) owner (response effective),
          (revealSuccessor published binding source effective).withOwnHistory owner past))
  have emitted (intended : Bool) : response
      (effectiveDisclosure published binding source intended) = response intended :=
    (serviceDecision_effectiveDisclosure (runtime setup) leaks published binding source refs
      execution agree event outputEq codeEq node intended).symm
  simp only [Config.view, effectiveDisclosureView_observe, emitted,
    revealSuccessor_effective_withOwnHistory] at law
  simpa only [Config.restoreMemory, PMF.bind_map, Config.withOwnHistory_view,
    Config.view, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
    Config.withOwnHistory, Function.update_self, revealSuccessor, Function.update_idem,
    memory] using law

end Vegas

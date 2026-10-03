/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionDecisionFactorization

/-! # Original intentions in the actual resolution response law

The original source draw and the effective transmitted choice are carried
together. A failed TRUE intention produces a FALSE packet, while the original
source history retains TRUE. The complete traffic channel depends on the
effective successor view; it need not identify the original intention.

This is an actual canonical response kernel. Timing, inclusion, source-relative
beliefs and continuation incentives require their separate proofs.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
private theorem effectiveDisclosure_emittable
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (intended : Bool) :
    effectiveDisclosure published binding source intended = false ∨
      ∃ value : L.Val payload,
        effectiveDisclosure published binding source intended = true ∧
          disclosureResult published binding source true = .success value := by
  cases intended with
  | false => exact Or.inl (effectiveDisclosure_false published binding source)
  | true =>
      cases result : disclosureResult published binding source true with
      | failure => exact Or.inl (by simp only [effectiveDisclosure, result])
      | success value =>
          exact Or.inr ⟨value, by simp only [effectiveDisclosure, result], rfl⟩

/-- An original source draw updates both source histories and emits its
effective canonical packet. The prior source-pair channel is an induction
hypothesis; the response channel follows from the actual packet law. -/
theorem source_async_resolution_intention_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (focal : Player)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (valid : ∀ seed ∈ prior.support, (execution seed).application.BindingInvariant)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (codeEq : ∀ seed, cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding))
    (node : ∀ seed, nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs (source seed).registry
        (source seed).revelations binding) outputEq (codeEq seed))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra))
    (choice : Config Player L Γ → PMF Bool) :
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (original seed)).map fun intended =>
        ((revealSuccessor published binding (source seed)
            (effectiveDisclosure published binding (source seed) intended),
          revealSuccessor published binding (original seed) intended),
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
                ((execution seed).observe (application setup leaks) owner) event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                  (effectiveDisclosure published binding (source seed) intended)))))) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (choice pair.2).map fun intended =>
          (revealSuccessor published binding pair.1
            (effectiveDisclosure published binding pair.1 intended),
            revealSuccessor published binding pair.2 intended)).bind fun pair =>
          (nextNoise (pair.1.view focal)).map fun extra => (pair, extra) := by
  have updated := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor (fun pair => choice pair.2)
    (fun pair intended =>
      (revealSuccessor published binding pair.1
        (effectiveDisclosure published binding pair.1 intended),
        revealSuccessor published binding pair.2 intended)) (fun pair => pair.1.view focal)
    (fun seed intended => PMF.pure ((runtime setup).bindingTraffic leaks focal
      ((execution seed).respond (application setup leaks) owner
        ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (effectiveDisclosure published binding (source seed) intended))))))
    (by
      intro left _ first _ right _ second _ same
      exact reveal_view_reflects focal published binding left.1 right.1
        (effectiveDisclosure published binding left.1 first)
        (effectiveDisclosure published binding right.1 second) same)
    (by
      intro left leftSupport first _ right rightSupport second _ same traffic
      apply congrArg PMF.pure
      exact source_resolution_decision_traffic_congr setup leaks published binding refs
        (source left) (source right) (execution left) (execution right)
        (agree left leftSupport) (agree right rightSupport) (valid left leftSupport)
        (valid right rightSupport) (recalled left leftSupport) (recalled right rightSupport)
        event focal outputEq (codeEq left) (codeEq right) (node left) (node right)
        (effectiveDisclosure published binding (source left) first)
        (effectiveDisclosure published binding (source right) second)
        (effectiveDisclosure_emittable published binding (source left) first)
        (effectiveDisclosure_emittable published binding (source right) second) same traffic)
  obtain ⟨nextNoise, law⟩ := updated
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_map, ← PMF.bind_pure_comp, Function.comp_def, PMF.pure_bind] using law

end Vegas

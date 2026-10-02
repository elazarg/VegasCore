/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncFactorization
import Vegas.Pending.ReactiveCanonicalDecision

/-! # Source memory and traffic after an actual binding decision

The actual opaque commitment response preserves the joint source-memory and
traffic factorization through the chosen source successor. The scheduler is
not invoked by this response step; no calendar, independent traffic, or grant
likelihood is supplied. The auxiliary readout retains the actual network,
receipts, scheduler recall and focal private input.

This is a decision kernel. Acceptance, source/runtime alignment, later event
completion and source beliefs remain separate operational obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem binding_response_traffic_congr
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (left right : (application setup leaks).Execution)
    (leftRecall : left.InputRecall (application setup leaks))
    (rightRecall : right.InputRecall (application setup leaks))
    (owner focal : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial : Nat)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    (runtime setup).bindingTraffic leaks focal
        (left.respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload first serial)) =
      (runtime setup).bindingTraffic leaks focal
        (right.respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload second serial)) := by
  have law := (runtime setup).binding_silent_window_coupling leaks
    (fun _ _ => PMF.pure .wait) [] left right leftRecall rightRecall owner focal event payload
      first second visible serial same
  simp only [List.map_nil, runInteractionPlan, PMF.pure_map] at law
  apply (PMF.mem_support_pure_iff _ _).mp
  rw [← law]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- An actual counted-slot binding response preserves the full joint original
and effective source-memory law, with its traffic conditional only on the
focal source successor view. The preceding factorization is the induction
hypothesis; equality of the new channel is derived from opaque responses. -/
theorem source_async_binding_decision_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (recalled : ∀ seed ∈ prior.support,
      (execution seed).InputRecall (application setup leaks))
    (fresh : ∀ seed ∈ prior.support,
      ((execution seed).observe (application setup leaks) owner).application.candidates
        (.prepared ((execution seed).application.publicView.bindingCount owner)) = .fresh)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra))
    (choice : Config Player L Γ → PMF (PublicationResult (L.Val payload))) :
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (original seed)).map fun result =>
        ((commitSuccessor name guard (source seed) result,
          commitSuccessor name guard (original seed) result),
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
                ((execution seed).observe (application setup leaks) owner) event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) result))))) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (choice pair.2).map fun result =>
          (commitSuccessor name guard pair.1 result,
            commitSuccessor name guard pair.2 result)).bind fun pair =>
        (nextNoise (pair.1.view focal)).map fun extra => (pair, extra) := by
  have updated := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor (fun pair => choice pair.2)
    (fun pair result => (commitSuccessor name guard pair.1 result,
      commitSuccessor name guard pair.2 result)) (fun pair => pair.1.view focal)
    (fun seed result => PMF.pure ((runtime setup).bindingTraffic leaks focal
      ((execution seed).respond (application setup leaks) owner
        ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) result)))))
    (by
      intro left _ first _ right _ second _ same
      have earlier := congrArg (DecisionView.back (decide (owner = focal))) same
      simpa only [back_commit_view] using earlier)
    (by
      intro left leftSupport first _ right rightSupport second _ same traffic
      have visible : focal = owner → first = second := by
        intro equal
        subst focal
        have cell := congrArg
          (fun view : DecisionView owner ((name, .commitment owner payload) :: Γ) =>
            view.1.cells.get .here) same
        simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons,
          ite_true] at cell
        exact Option.some.inj cell
      have publics := congrArg (fun value => value.2.2.2.2.2) traffic
      have serials : (execution left).application.publicView.bindingCount owner =
          (execution right).application.publicView.bindingCount owner :=
        congrArg (fun view => view.bindingCount owner) publics
      have firstDecision := (runtime setup).canonicalServiceDecision_binding leaks owner
        ((execution left).recall owner) ((execution left).observe (application setup leaks) owner)
        event payload outputEq codeEq node ((execution left).application.publicView.bindingCount
          owner) (canonicalFreshSlot_canonical owner _ (fresh left leftSupport)) first
      have secondDecision := (runtime setup).canonicalServiceDecision_binding leaks owner
        ((execution right).recall owner) ((execution right).observe (application setup leaks) owner)
        event payload outputEq codeEq node ((execution right).application.publicView.bindingCount
          owner) (canonicalFreshSlot_canonical owner _ (fresh right rightSupport)) second
      rw [firstDecision, secondDecision]
      apply congrArg PMF.pure
      simpa only [serials] using binding_response_traffic_congr setup leaks
        (execution left) (execution right) (recalled left leftSupport)
        (recalled right rightSupport) owner focal event payload first second visible
          ((execution left).application.publicView.bindingCount owner) traffic)
  obtain ⟨nextNoise, law⟩ := updated
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_map, ← PMF.bind_pure_comp, Function.comp_def, PMF.pure_bind] using law

end Vegas

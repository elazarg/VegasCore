/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnCompletes
import Vegas.Game.SourceServiceFirstTurnPrefix
import Vegas.Game.SourceServiceResidualSites
import Vegas.Pending.ReactiveBindingLikelihood

/-! # The first resolution draw and its actual stopped traffic

The effective source draw is carried through the same actual waiting,
transmitting and stopped-execution draws. The whole-program typed decoder is
proved at each endpoint before taking the joint law. This is a phase kernel;
it does not assert a source posterior or a sequential equilibrium.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The actual first-turn resolution law retains its effective source draw,
whole typed next prefix and full traffic jointly. Alignment, source support
and endpoint decoding are derived from the initialized completion boundary.
Effective disclosures ensure every supported TRUE draw can really open. -/
theorem sourceServiceFirstResolution_prefix_probability
    {horizon turns : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (event : (graph setup).EventId) (payload : L.Ty)
    (publication : (graph setup).outputLayout event = .publication payload)
    (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val start)
    (within : start.environmentRecall.length ≤ horizon) (focal : Player) :
    ∃ (before : ProtocolState setup.program)
      (site : RevealSource setup profile event start.application.config)
      (embed : Config Player L ((site.published, .publication site.payload) :: site.Γ) →
        ProtocolState setup.program),
      sourceServicePrefix? setup event.val start.application.config = some before ∧
      ProtocolState.behavioralStateStep setup.program profile before =
        (revealKernel site.residual (site.source.view site.owner)).map
          (fun disclose => embed (revealSuccessor site.published site.binding site.source
            disclose)) ∧
      ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          (fun final => event ∈ final.application.config.cut.completed) horizon start).map
            (fun final => (sourceServicePrefix? setup (event.val + 1) final.application.config,
              (runtime setup).bindingTraffic leaks focal final)) =
        (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
          ((application setup leaks).runUntilHorizon scheduler
            (decidedProfile (leaks := leaks) bound site.owner event
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose))
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              (fun final =>
                (some (embed (revealSuccessor site.published site.binding site.source disclose)),
                  (runtime setup).bindingTraffic leaks focal final)) := by
  let app := application setup leaks
  have ready : start.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
  obtain ⟨residual⟩ := boundary.sourceResidual (profile := profile)
  have beforeRead := residual.decode
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    _admitted, effectiveResidual, supports, lift, _recoverView, _viewRecovered, commutes,
    _steps, _injective, transport, checkpoint⟩ := residual
  cases program with
  | ret payoffs =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      change event.val < eventCount setup.program at inside
      omega
  | @sample Γ names name samplePayload fresh distribution next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph setup).outputLayout event = .publicData samplePayload := by
        rw [← head]
        change outputLayout setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans publication
  | @commit Γ names name owner payload fresh guard next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph setup).outputLayout event = .binding owner payload := by
        rw [← head]
        change outputLayout setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans publication
  | @reveal Γ names published owner name payload fresh selected unresolved next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      subst head
      let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event index
      let site : RevealSource setup profile event start.application.config :=
        ⟨Γ, names, published, owner, name, payload, fresh, selected, unresolved, next,
          residualProfile, refs, source, embedding, refsBefore, aligned, checkpoint.agrees,
          checkpoint.history, rfl, effectiveResidual, supports⟩
      let embed := fun state : Config Player L ((published, .publication payload) :: Γ) =>
        lift (Sum.inr (ProtocolState.entry next state))
      have step := commutes
        (ProtocolState.entry (.reveal published owner name fresh selected unresolved next) source)
      simp only [ProtocolState.entry] at step
      rw [ProtocolState.behavioralStateStep_reveal_entry, PMF.map_comp] at step
      have policy (current : app.Execution)
          (same : current.application.config = start.application.config) :
          sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
              (current.observe app owner) =
            ((revealKernel residualProfile (source.view owner)).map
              (fun disclose => cast (congrArg EventGraph.EventField.Action site.outputEq.symm)
                disclose)).map (fun action => (runtime setup).canonicalServiceDecision leaks owner
                  (current.recall owner) (current.observe app owner) event action) := by
        have law := sourceServiceCanonicalPolicy_reveal setup leaks fresh selected unresolved next
          profile residualProfile refs source embedding refsBefore _ aligned current
          (by rw [same]; exact checkpoint.agrees)
          (by rw [same]; exact checkpoint.history) (by rw [same]; exact ready)
        rw [PMF.map_comp]
        exact law
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) site.outputEq)
          ((graph setup).nodes event) = .resolve owner payload (refs.get selected)
            (compileChecks (published := published) refs source.registry source.revelations
              selected) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) site.outputEq)
          ((toEventGraph setup.program).nodes _) = _
        simpa [event, index, outputLayout, compileRankedNodes] using
          aligned.graphSuffix.nodeEq index
      have decodedAction (disclose : Bool) : decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) =
            some (.reveal owner name disclose) := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
        change decodeEventAction setup.program _ _ =
          some (.reveal owner name
            (cast (congrArg EventGraph.EventField.Action site.outputEq)
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose))) at lookup
        simpa only [cast_cast, cast_eq] using lookup
      have endpoint (disclose : Bool)
          (chosen : disclose ∈ (revealKernel residualProfile (source.view owner)).support)
          (stopped : app.Execution)
          (supported : stopped ∈ (app.runUntilHorizon scheduler
            (decidedProfile (leaks := leaks) bound owner event
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose))
            (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
          sourceServicePrefix? setup (event.val + 1) stopped.application.config =
            some (embed (revealSuccessor published selected source disclose)) := by
        have realized : EffectiveAction start.application.config event
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) := by
          unfold EffectiveAction
          rw [nodeView_eq_resolve site.outputEq codeEq]
          simp only [cast_cast, cast_eq]
          intro requested
          subst disclose
          have kept := (effectiveResidual effective owner).1 rfl (source.view owner) true chosen
          change effectiveDisclosureView published selected source.registry source.revelations
            (sourceObserve owner source.state) true = true at kept
          rw [effectiveDisclosureView_observe] at kept
          have resolved := compiled_disclosure_result published selected source refs
            start.application.config.store checkpoint.agrees true
          rw [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
          cases result : disclosureResult published selected source true with
          | failure => simp only [effectiveDisclosure, result] at kept; cases kept
          | success value => exact ⟨value, by rw [resolved, result]⟩
        have native := decided_completion contract timely event start boundary within ready
          site.owned (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
          realized stopped supported
        rw [start.application.config.step_eq_map_of_code event ready site.outputEq _ codeEq disclose
          (PMF.pure (disclosureResult published selected source disclose))
          (compileResolve_eval? refs source.registry source.revelations source.state
            start.application.config.store checkpoint.agrees selected disclose),
          PMF.pure_map, PMF.mem_support_pure_iff] at native
        rw [native]
        unfold sourceServicePrefix?
        rw [transport 1]
        have decoded := (checkpoint.reveal (native := configState start.application.config)
          published selected event rfl ready site.outputEq (fun ref => refsBefore ref index)
          disclose (decodedAction disclose)).decode next (fun tail => embedding.ref tail.succ)
        have localDecode := (decodeSourcePrefix?_reveal fresh selected unresolved next refs
          source.registry source.revelations embedding.ref 0 _ _).trans
            (congrArg (Option.map Sum.inr) decoded)
        change (decodeSourcePrefix? (.reveal published owner name fresh selected unresolved next)
          refs source.registry source.revelations embedding.ref 1 _ _).map lift = _
        exact congrArg (Option.map lift) localDecode
      refine ⟨lift (ProtocolState.entry
        (.reveal published owner name fresh selected unresolved next) source), site, embed,
        beforeRead, step, ?_⟩
      rw [sourceServiceTurnPolicy_firstTurn_phase event start boundary]
      unfold ReactiveApplication.runUntilHorizon
      rw [firstTurn_runUntil_mixture event start boundary owner site.owned bound turns profile
        _ policy _, PMF.map_bind, PMF.bind_map]
      apply bind_congr_on_support _
      intro disclose chosen
      apply map_congr_on_support _
      intro stopped supported
      exact Prod.ext (endpoint disclose chosen stopped supported) rfl

end Vegas

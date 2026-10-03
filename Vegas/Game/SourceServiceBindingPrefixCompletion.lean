/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingResponseCompletion
import Vegas.Game.SourceServiceResidualSites

/-! # Whole source-prefix readouts of protected binding completions

An actual initialized pending activation supplies its semantic residual before
any response is chosen. The residual's real decoder transport identifies the
whole-program source successor of each protected transmitting binding draw.
Both its typed store and own history come from the actual stopped execution.

The profile here is the profile used by the compiler. When that profile has
been normalized, this readout represents its effective source history; erased
original disclosure intentions remain separate proof data.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player]

/-- Protected binding completion realizes the whole source step, with its
residual source choice and successor embedding derived from initialized play.
The actual receipt, typed store and own history determine the decoder result.
-/
theorem sourceServiceDecision_clear_binding_prefix_completion {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (bounds : MessageBounds (graph setup))
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (who : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (bindingOwner : Player) (bindingPayload : L.Ty)
    (binding : (graph setup).outputLayout event = .binding bindingOwner bindingPayload)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (initialized : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players (some ⟨remaining, some who, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall who) event = false)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile who) :
    ∃ (before : ProtocolState setup.program)
      (site : BindingSource setup profile event execution.application.config)
      (embed : Config Player L ((site.name, .commitment site.owner site.payload) :: site.Γ) →
        ProtocolState setup.program),
      sourceServicePrefix? setup event.val execution.application.config = some before ∧
      site.owner = who ∧
      ProtocolState.behavioralStateStep setup.program profile before =
        (commitKernel site.residual (site.source.view site.owner)).map
          (fun value => embed (commitSuccessor site.name site.guard site.source value)) ∧
      ∀ value ∈ (commitKernel site.residual (site.source.view site.owner)).support,
        ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
            (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution.respond (application setup leaks) site.owner
              ((runtime setup).reactiveBinding leaks site.owner event site.payload value
                (execution.application.publicView.bindingCount site.owner)))).support,
          sourceServicePrefix? setup (event.val + 1) stopped.application.config =
            some (embed (commitSuccessor site.name site.guard site.source value)) := by
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  obtain ⟨residual⟩ := menu_ready_sourceResidual setup leaks profile
    (bounds.riskMenu (runtime setup) leaks bound) horizon scheduler trace
    ⟨remaining, some who, execution⟩ rfl event ready
  have beforeRead := residual.decode
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    admitted, effective, supports, lift, commutes, steps, injective, transport,
    checkpoint⟩ := residual
  cases program with
  | ret payoffs =>
      have count := aligned.graphSuffix.countEq
      change event.val + eventCount (.ret payoffs) = (graph setup).order.eventCount at count
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      omega
  | sample name fresh law next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have actor := aligned.actorEq ⟨0, by simp [eventCount]⟩
      rw [head] at actor
      change (graph setup).actor? event = none at actor
      rw [binding_actor setup event bindingOwner bindingPayload binding] at actor
      cases actor
  | @reveal Γ names published owner name payload fresh selected unresolved next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph setup).outputLayout event = .publication payload := by
        rw [← head]
        change outputLayout setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans binding
  | @commit Γ names name owner payload fresh guard next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      let site : BindingSource setup profile event execution.application.config :=
        ⟨Γ, names, name, owner, payload, fresh, guard, next, residualProfile, refs, source,
          embedding, refsBefore, aligned, checkpoint.agrees, checkpoint.history, head⟩
      have ownerEq : owner = who := Option.some.inj (site.owned.symm.trans
        (PublicView.ownTurn?_spec _ who event turn).2)
      subst owner
      let embed := fun state : Config Player L ((name, .commitment who payload) :: Γ) =>
        lift (Sum.inr (ProtocolState.entry next state))
      have step := commutes (ProtocolState.entry (.commit name who fresh guard next) source)
      simp only [ProtocolState.entry] at step
      rw [ProtocolState.behavioralStateStep_commit_entry, PMF.map_comp] at step
      refine ⟨lift (ProtocolState.entry (.commit name who fresh guard next) source), site,
        embed, beforeRead, rfl, step, ?_⟩
      intro value sampled stopped stoppedSupported
      obtain ⟨entry, _, message, _, _, completion⟩ := sourceServiceDecision_clear_binding_completion
        contract bounds profile players execution event site trace initialized clear unrecorded
          turn fits weight positive below follows value sampled
      obtain ⟨_, _, _, _, agrees, history⟩ := completion stopped stoppedSupported
      unfold sourceServicePrefix?
      rw [transport 1, decodeSourcePrefix?_commit]
      have read := decodeSourcePrefix?_zero_of_agrees next
        (refs.cons (name := name) ⟨.inr event, site.outputEq⟩)
        (fun tail => embedding.ref tail.succ) (commitSuccessor name guard source value)
        stopped.application.config.store agrees
      let headOutput : EventGraph.FieldRef (graphLayout setup.program) (.binding who payload) := by
        simpa [outputLayout, eventCount] using
          embedding.ref ⟨0, by simp [eventCount]⟩
      have headRef : headOutput = ⟨.inr event, site.outputEq⟩ := by
        simpa [headOutput, OutputEmbedding.ref, outputLayout, eventCount] using head
      change ((decodeSourcePrefix? next (refs.cons (name := name) headOutput)
        (commitSuccessor name guard source value).registry
        (commitSuccessor name guard source value).revelations
        (fun tail => embedding.ref tail.succ) 0
        stopped.application.config.store
        (decodeHistory setup.program (stopped.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)))).map Sum.inr).map lift = _
      rw [headRef, history]
      change ((decodeSourcePrefix? next
        (refs.cons (name := name) ⟨.inr event, site.outputEq⟩)
        (commitSuccessor name guard source value).registry
        (commitSuccessor name guard source value).revelations
        (fun tail => embedding.ref tail.succ) 0 stopped.application.config.store
        (commitSuccessor name guard source value).history).map Sum.inr).map lift = _
      rw [read]
      rfl

end Vegas

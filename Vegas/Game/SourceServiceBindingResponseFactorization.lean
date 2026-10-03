/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRecordedBindingCompletion
import Vegas.Game.SourceServiceProtectedDecisionLaw
import Vegas.Pending.ReactiveOwnerWindow
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual typed binding responses and their complete traffic law

At a protected unrecorded opportunity, actual earlier protected waits determine
the geometric timing posterior. The current response independently waits or
makes the aligned residual source commitment. Its readout retains the chosen
typed private value and the whole network, receipts, scheduler recall and focal
private input. The response does not yet complete the native configuration.

A tagged source successor distinguishes waiting from committing. It retains
both the decoded source and its original private history. The conditional
traffic channel follows from actual opaque binding responses; no independent
noise or source posterior is supplied as a new assumption.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Read the actual submitted candidate's typed result, retaining a separate
waiting branch. This is a proof readout of private runtime state. -/
def bindingResponseResult? (owner : Player) (payload : L.Ty)
    (execution : (application setup leaks).Execution)
    (response : (application setup leaks).Action) : Option (PublicationResult (L.Val payload)) :=
  if response.transmission.isSome then
    some ((execution.respond (application setup leaks) owner response).application.bindingResult
      (owner, .prepared (execution.application.publicView.bindingCount owner)) payload)
  else none

/-- Render a typed wait or commitment at the actual public counted handle. -/
def bindingChoiceResponse (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (execution : (application setup leaks).Execution) :
    Option (PublicationResult (L.Val payload)) → (application setup leaks).Action
  | none => ⟨none⟩
  | some value => (runtime setup).reactiveBinding leaks owner event payload value
      (execution.application.publicView.bindingCount owner)

private theorem bindingResponseResult_choice (owner : Player) (event : (graph setup).EventId)
    (payload : L.Ty) (execution : (application setup leaks).Execution)
    (fresh : execution.application.candidates.lookup
      (owner, .prepared (execution.application.publicView.bindingCount owner)) = .fresh)
    (choice : Option (PublicationResult (L.Val payload))) :
    bindingResponseResult? owner payload execution
      (bindingChoiceResponse owner event payload execution choice) = choice := by
  cases choice with
  | none => rfl
  | some value =>
      change some ((execution.respond (application setup leaks) owner
        ((runtime setup).reactiveBinding leaks owner event payload value
          (execution.application.publicView.bindingCount owner))).application.bindingResult
            (owner, .prepared (execution.application.publicView.bindingCount owner)) payload) = _
      exact congrArg some ((runtime setup).reactiveBinding_result leaks owner event payload value
        (execution.application.publicView.bindingCount owner) execution fresh)

/-- Waiting retains the old typed source pair; a chosen commitment extends
both source states by the same actual typed choice. -/
def commitResponseSource {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (pair : Config Player L Γ × Config Player L Γ)
    (choice : Option (PublicationResult (L.Val payload))) :
    (Config Player L Γ × Config Player L Γ) ⊕
      (Config Player L ((name, .commitment owner payload) :: Γ) ×
        Config Player L ((name, .commitment owner payload) :: Γ)) :=
  match choice with
  | none => .inl pair
  | some value => .inr (commitSuccessor name guard pair.1 value,
      commitSuccessor name guard pair.2 value)

/-- The tagged source view records whether this response made the commitment. -/
def commitResponseView {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (focal : Player) :
    ((Config Player L Γ × Config Player L Γ) ⊕
      (Config Player L ((name, .commitment owner payload) :: Γ) ×
        Config Player L ((name, .commitment owner payload) :: Γ))) →
      DecisionView focal Γ ⊕ DecisionView focal ((name, .commitment owner payload) :: Γ)
  | .inl pair => .inl (pair.1.view focal)
  | .inr pair => .inr (pair.1.view focal)

variable [Fintype Player]

/-- An actual clear unrecorded turn has never used its public counted slot.
Earlier waits are allowed and need not have occurred at the first owner turn. -/
theorem sourceService_clear_counted_candidate_fresh {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (owner : Player) (execution : (application setup leaks).Execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (event : (graph setup).EventId)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (turn : execution.application.publicView.ownTurn? owner = some event) :
    execution.application.candidates.lookup
      (owner, .prepared (execution.application.publicView.bindingCount owner)) = .fresh := by
  obtain ⟨canonical, _same⟩ := bounds.riskTrace_canonical_of_persistentClear (runtime setup) leaks
    bound (initialLaw setup) horizon scheduler trace (by
      intro control same player
      cases Option.some.inj same
      exact clear player)
  obtain ⟨atTurn, slots⟩ := retainedCanonicalSlots_history bounds
    ⟨remaining, some owner, execution⟩ canonical owner
  exact canonicalSlot_fresh_of_used
    ((bounds.canonicalMenu (runtime setup) leaks).toRawTrace _ _ _ canonical)
    owner atTurn slots event turn unrecorded

/-- The complete actual response distribution retains the residual source's
original typed commitment kernel and the geometric wait probability. -/
theorem sourceServiceDecision_clear_binding_response {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1) :
    sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon weight positive.le below.le) profile site.owner
        (execution.recall site.owner) (execution.observe (application setup leaks) site.owner) =
      mix weight positive.le below.le (PMF.pure ⟨none⟩)
        ((commitKernel site.residual (site.source.view site.owner)).map fun value =>
          (runtime setup).reactiveBinding leaks site.owner event site.payload value
            (execution.application.publicView.bindingCount site.owner)) := by
  have law := sourceServiceDecision_clear_protected_compiled_response bounds bound profile
    site.owner execution trace clear event unrecorded turn fits weight positive below
  rw [BindingSource.compiled_choice execution site, PMF.map_comp] at law
  rw [law]
  congr 1
  apply map_congr_on_support _
  intro value _supported
  have fresh := sourceService_clear_counted_candidate_fresh bounds bound site.owner execution
    trace clear event unrecorded turn
  exact (runtime setup).canonicalServiceDecision_binding leaks site.owner
    (execution.recall site.owner) (execution.observe (application setup leaks) site.owner)
    event site.payload site.outputEq site.code (nodeView_eq_bind site.outputEq site.code)
    (execution.application.publicView.bindingCount site.owner)
    (canonicalFreshSlot_canonical site.owner
      (execution.observe (application setup leaks) site.owner).application fresh) value

/-- The typed choice and complete realized traffic use the same actual
response draw. Earlier protected deferrals are retained by the physical law. -/
theorem sourceServiceDecision_clear_binding_joint_response {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (site : BindingSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1) (focal : Player) :
    (sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon weight positive.le below.le) profile site.owner
        (execution.recall site.owner) (execution.observe (application setup leaks) site.owner)).map
      (fun response => (bindingResponseResult? site.owner site.payload execution response,
        (runtime setup).bindingTraffic leaks focal
          (execution.respond (application setup leaks) site.owner response))) =
      mix weight positive.le below.le
        (PMF.pure (none, (runtime setup).bindingTraffic leaks focal
          (execution.respond (application setup leaks) site.owner ⟨none⟩)))
        ((commitKernel site.residual (site.source.view site.owner)).map fun value =>
          (some value, (runtime setup).bindingTraffic leaks focal
            (execution.respond (application setup leaks) site.owner
              ((runtime setup).reactiveBinding leaks site.owner event site.payload value
                (execution.application.publicView.bindingCount site.owner))))) := by
  rw [sourceServiceDecision_clear_binding_response bounds bound profile execution event site
    trace clear unrecorded turn fits weight positive below, mix_map, PMF.pure_map, PMF.map_comp]
  congr 1
  apply map_congr_on_support _
  intro value _supported
  apply Prod.ext
  · unfold bindingResponseResult?
    simp only [reactiveBinding]
    exact congrArg some ((runtime setup).reactiveBinding_result leaks site.owner event site.payload
      value (execution.application.publicView.bindingCount site.owner) execution
      (sourceService_clear_counted_candidate_fresh bounds bound site.owner execution trace clear
        event unrecorded turn))
  · rfl

omit [Fintype Player] in
/-- An actual wait-or-binding response preserves the typed source-pair and
traffic factorization. The choice can depend on the original private source
history. Every new channel equality follows from physical response operations;
freshness guarantees the chosen result is read from the actual submitted slot. -/
theorem source_binding_response_factorization
    {Seed : Type*} {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (focal : Player) (event : (graph setup).EventId)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (fresh : ∀ seed ∈ prior.support, (execution seed).application.candidates.lookup
      (owner, .prepared ((execution seed).application.publicView.bindingCount owner)) = .fresh)
    (choice : (Config Player L Γ × Config Player L Γ) →
      PMF (Option (PublicationResult (L.Val payload))))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise :
        (DecisionView focal Γ ⊕ DecisionView focal ((name, .commitment owner payload) :: Γ)) →
          PMF _,
      (prior.bind fun seed => (choice (source seed, original seed)).map fun selected =>
        (commitResponseSource name guard (source seed, original seed)
          (bindingResponseResult? owner payload (execution seed)
            (bindingChoiceResponse owner event payload (execution seed) selected)),
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              (bindingChoiceResponse owner event payload (execution seed) selected)))) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (choice pair).map (commitResponseSource name guard pair)).bind fun next =>
          (nextNoise (commitResponseView name focal next)).map fun extra => (next, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor choice
    (commitResponseSource name guard) (commitResponseView name focal)
    (fun seed selected => PMF.pure ((runtime setup).bindingTraffic leaks focal
      ((execution seed).respond (application setup leaks) owner
        (bindingChoiceResponse owner event payload (execution seed) selected))))
    (by
      intro left _ first _ right _ second _ same
      cases first with
      | none =>
          cases second with
          | none => exact Sum.inl.inj same
          | some value => cases same
      | some first =>
          cases second with
          | none => cases same
          | some second =>
              have earlier := congrArg (DecisionView.back (decide (owner = focal)))
                (Sum.inr.inj same)
              simpa only [back_commit_view] using earlier)
    (by
      intro left _ first _ right _ second _ same traffic
      cases first with
      | none =>
          cases second with
          | none =>
              exact congrArg PMF.pure ((runtime setup).bindingTraffic_silent leaks
                (execution left) (execution right) focal owner traffic ⟨none⟩ rfl)
          | some value => cases same
      | some first =>
          cases second with
          | none => cases same
          | some second =>
              have views := Sum.inr.inj same
              have visible : focal = owner → first = second := by
                intro equal
                subst focal
                have cell := congrArg
                  (fun view : DecisionView owner ((name, .commitment owner payload) :: Γ) =>
                    view.1.cells.get .here) views
                simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons,
                  ite_true] at cell
                exact Option.some.inj cell
              have publics := congrArg (fun read => read.2.2.2.2.2) traffic
              dsimp only [bindingTraffic] at publics
              have serialEq := congrArg (fun view => view.bindingCount owner) publics
              exact congrArg PMF.pure (by
                simpa only [bindingChoiceResponse, serialEq] using
                  (runtime setup).bindingTraffic_binding_response leaks (execution left)
                    (execution right) owner focal event payload first second visible
                    ((execution left).application.publicView.bindingCount owner) traffic))
  refine ⟨nextNoise, ?_⟩
  calc
    _ = prior.bind (fun seed => (choice (source seed, original seed)).map fun selected =>
        (commitResponseSource name guard (source seed, original seed) selected,
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              (bindingChoiceResponse owner event payload (execution seed) selected)))) := by
      apply bind_congr_on_support _
      intro seed supported
      apply map_congr_on_support _
      intro selected _chosen
      rw [bindingResponseResult_choice owner event payload (execution seed) (fresh seed supported)]
    _ = _ := by
      simpa only [PMF.pure_map, ← PMF.bind_pure_comp, PMF.pure_bind, Function.comp_def] using law

/-- The actual geometric source policy preserves the source-pair and full
traffic factorization at any supplied collection of clear protected binding
inputs. The source kernel is derived from each actual aligned configuration;
the original source state is carried jointly with its private history. -/
theorem source_async_binding_response_factorization
    {Seed : Type*} {Γ : SourceCtx Player L} {names : Finset VarId}
    {owner : Player} {payload : L.Ty} (name : VarId) (freshName : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile setup.program)
    (residual : BehavioralProfile (.commit name owner freshName guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner freshName guard next))
    (refsBefore : ContextRefsBefore refs embedding)
    (event : (graph setup).EventId) (head : embedding.event ⟨0, by simp [eventCount]⟩ = event)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (focal : Player) (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution) (remaining : Seed → Nat)
    (aligned : ∀ seed ∈ prior.support,
      CompiledPolicySuffix setup.program profile (.commit name owner freshName guard next)
        residual refs (source seed).revelations (source seed).registry embedding refsBefore
          event.val)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (history : ∀ seed ∈ prior.support, decodeHistory setup.program
      ((execution seed).application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = (source seed).history)
    (trace : ∀ seed ∈ prior.support,
      ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
        scheduler).Trace (some ⟨remaining seed, some owner, execution seed⟩))
    (clear : ∀ seed ∈ prior.support, ∀ player,
      (runtime setup).persistentServiceRisk leaks bound player ((execution seed).recall player)
        ((execution seed).observe (application setup leaks) player) = false)
    (unrecorded : ∀ seed ∈ prior.support,
      (runtime setup).eventRecorded leaks ((execution seed).recall owner) event = false)
    (turn : ∀ seed ∈ prior.support,
      (execution seed).application.publicView.ownTurn? owner = some event)
    (fits : ∀ seed ∈ prior.support,
      (execution seed).application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise :
        (DecisionView focal Γ ⊕ DecisionView focal ((name, .commitment owner payload) :: Γ)) →
          PMF _,
      (prior.bind fun seed => (sourceServiceTurnPolicy setup leaks bound horizon
          (geometricTiming setup horizon weight positive.le below.le) profile owner
          ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner)).map fun response =>
        (commitResponseSource name guard (source seed, original seed)
          (bindingResponseResult? owner payload (execution seed) response),
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner response))) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (mix weight positive.le below.le (PMF.pure none)
          ((commitKernel residual (pair.1.view owner)).map some)).map
            (commitResponseSource name guard pair)).bind fun next =>
          (nextNoise (commitResponseView name focal next)).map fun extra => (next, extra) := by
  let choice := fun pair : Config Player L Γ × Config Player L Γ =>
    mix weight positive.le below.le (PMF.pure none)
      ((commitKernel residual (pair.1.view owner)).map some)
  obtain ⟨nextNoise, law⟩ := source_binding_response_factorization name guard focal event prior
    source original execution (fun seed supported => sourceService_clear_counted_candidate_fresh
      bounds bound owner (execution seed) (trace seed supported) (clear seed supported)
        event (unrecorded seed supported) (turn seed supported)) choice noise factor
  refine ⟨nextNoise, ?_⟩
  rw [← law]
  apply bind_congr_on_support _
  intro seed supported
  let site : BindingSource setup profile event (execution seed).application.config :=
    ⟨Γ, names, name, owner, payload, freshName, guard, next, residual, refs, source seed,
      embedding, refsBefore, aligned seed supported, agree seed supported,
      history seed supported, head⟩
  have responseLaw := sourceServiceDecision_clear_binding_response bounds bound profile
    (execution seed) event site (trace seed supported) (clear seed supported)
      (unrecorded seed supported) (turn seed supported) (fits seed supported)
        weight positive below
  rw [responseLaw]
  have physical : (choice (source seed, original seed)).map
      (bindingChoiceResponse owner event payload (execution seed)) =
      mix weight positive.le below.le (PMF.pure ⟨none⟩)
        ((commitKernel residual ((source seed).view owner)).map fun value =>
          (runtime setup).reactiveBinding leaks owner event payload value
            ((execution seed).application.publicView.bindingCount owner)) := by
    simp only [choice, mix_map, PMF.pure_map, PMF.map_comp, bindingChoiceResponse,
      Function.comp_def]
  rw [← physical, PMF.map_comp]
  rfl

end Vegas

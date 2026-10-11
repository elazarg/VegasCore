/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReactiveSourceDecision
import Vegas.Pending.ReactiveFirstOpportunity

/-! # Source decisions at actual first prescribed callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The behavioral prescribed policy takes the source commit kernel averaged
through its genuine private posterior. Opponents and scheduling are arbitrary;
original source recall remains correlated with the sampled source action. -/
theorem prescribedReactivePolicy_source_commit_first_opportunity
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile whole)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout whole) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (.commit name owner
      fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (turn : execution.application.publicView.ownTurn? owner =
      some (embedding.event ⟨0, by simp [eventCount]⟩))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players owner = runtime.prescribedReactivePolicy leaks owner
      ((compileEventProfile whole wholeProfile) owner))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (initial : EventGraphRuntime.State (toEventGraph whole))
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) initial)).support)
    (earlierTurns : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠
        some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (toEventGraph whole).outputLayout (embedding.event headIndex) = .binding
      owner payload := by
      change outputLayout whole (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    runtime.prescribedReactivePolicy leaks owner ((compileEventProfile whole wholeProfile) owner)
      (execution.recall owner) (execution.observe (runtime.reactiveApplication leaks) owner) =
      ((runtime.prescribedReactiveImplementation leaks owner
        ((compileEventProfile whole wholeProfile) owner)).posterior (execution.recall owner)).bind
        fun intentions =>
          (commitKernel profile (sourceObserve owner source.state,
            originalReactiveSourceRecall whole runtime leaks owner execution intentions)).map
              fun binding =>
                let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) binding
                runtime.reactiveDecision leaks owner (embedding.event headIndex) action
                  (execution.observe (runtime.reactiveApplication leaks) owner).application := by
  dsimp only
  rw [prescribedReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [prescribedReactiveImplementation, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro intentions supported
  have flags := runtime.prescribedReactivePosterior_fresh_before_turn_of_initialized_support
    leaks owner ((compileEventProfile whole wholeProfile) owner) players focal scheduler count
      initial execution reached (embedding.event ⟨0, by simp [eventCount]⟩) earlierTurns
        intentions supported
  have law := prescribedReactiveResponse_source_commit whole runtime leaks fresh guard next
    wholeProfile profile refs source embedding refsBefore offset aligned execution intentions agree
      turn flags.1 flags.2
  rw [law]
  simp only [PMF.map_comp, Function.comp_def]

/-- At a first reveal callback, the actual behavioral compiler averages the
source reveal kernel over authentic private memory, retaining original recall. -/
theorem prescribedReactivePolicy_source_reveal_first_opportunity
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile whole)
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout whole) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (.reveal published
      owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile (.reveal published owner name fresh
      selected unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (turn : execution.application.publicView.ownTurn? owner =
      some (embedding.event ⟨0, by simp [eventCount]⟩))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players owner = runtime.prescribedReactivePolicy leaks owner
      ((compileEventProfile whole wholeProfile) owner))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (initial : EventGraphRuntime.State (toEventGraph whole))
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) initial)).support)
    (earlierTurns : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠
        some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.reveal published owner name fresh selected unresolved
      next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (toEventGraph whole).outputLayout (embedding.event headIndex) = .publication
      payload := by
      change outputLayout whole (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    runtime.prescribedReactivePolicy leaks owner ((compileEventProfile whole wholeProfile) owner)
      (execution.recall owner) (execution.observe (runtime.reactiveApplication leaks) owner) =
      ((runtime.prescribedReactiveImplementation leaks owner
        ((compileEventProfile whole wholeProfile) owner)).posterior (execution.recall owner)).bind
        fun intentions =>
          (revealKernel profile (sourceObserve owner source.state,
            originalReactiveSourceRecall whole runtime leaks owner execution intentions)).map
              fun disclose =>
                let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
                runtime.reactiveDecision leaks owner (embedding.event headIndex) action
                  (execution.observe (runtime.reactiveApplication leaks) owner).application := by
  dsimp only
  rw [prescribedReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [prescribedReactiveImplementation, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro intentions supported
  have flags := runtime.prescribedReactivePosterior_fresh_before_turn_of_initialized_support
    leaks owner ((compileEventProfile whole wholeProfile) owner) players focal scheduler count
      initial execution reached (embedding.event ⟨0, by simp [eventCount]⟩) earlierTurns
        intentions supported
  have law := prescribedReactiveResponse_source_reveal whole runtime leaks fresh selected unresolved
    next wholeProfile profile refs source embedding refsBefore offset aligned execution intentions
      agree turn flags.1 flags.2
  rw [law]
  simp only [PMF.map_comp, Function.comp_def]

end Vegas

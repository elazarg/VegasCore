/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLocalComparison

/-! # The residual source constructor at an actual decision

At every retained decision during an event's phase, whoever acts, the residual
source program at that event is aligned with the compiled profile, and the
native configuration agrees with its typed source configuration. For a binding
event the residual is a commitment (`BindingSource`); for a publication event it
is a disclosure (`RevealSource`). Recording that data once spares every local
comparison the case analysis of the residual program.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The residual source commitment of a binding event, aligned with a whole
source profile at the event's rank, whose typed configuration agrees with a
native configuration. -/
structure BindingSource (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId)
    (config : (graph setup).Config) where
  Γ : SourceCtx Player L
  names : Finset VarId
  name : VarId
  owner : Player
  payload : L.Ty
  fresh : name ∉ Γ.map Prod.fst
  guard : SourceGuard L Γ owner name payload
  next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names)
  residual : BehavioralProfile (.commit name owner fresh guard next)
  refs : ContextRefs (graphLayout setup.program) Γ
  source : Config Player L Γ
  embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
    (.commit name owner fresh guard next)
  refsBefore : ContextRefsBefore refs embedding
  aligned : CompiledPolicySuffix setup.program profile (.commit name owner fresh guard next)
    residual refs source.revelations source.registry embedding refsBefore event.val
  agree : refs.Agrees source.state config.store
  history : decodeHistory setup.program
    (config.history.map (setup.eventGraph.fromModeCompletion .sequential)) = source.history
  head : embedding.event ⟨0, by simp [eventCount]⟩ = event

namespace BindingSource

variable {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
  {event : (graph setup).EventId} {config : (graph setup).Config}
  (site : BindingSource setup profile event config)

/-- The commitment's owner acts at the event. -/
theorem owned : (graph setup).actor? event = some site.owner := by
  have actor := site.aligned.actorEq ⟨0, by simp [eventCount]⟩
  rw [site.head] at actor
  exact actor

/-- The event's output is the commitment's binding. -/
theorem outputEq : (graph setup).outputLayout event = .binding site.owner site.payload := by
  have head : (graph setup).outputLayout (site.embedding.event ⟨0, by simp [eventCount]⟩) =
      .binding site.owner site.payload := by
    change outputLayout setup.program (site.embedding.event _) = _
    simpa [outputLayout, eventCount] using site.embedding.layout_eq ⟨0, by simp [eventCount]⟩
  exact (congrArg (graph setup).outputLayout site.head).symm.trans head

end BindingSource

/-- The residual source disclosure of a publication event, aligned with a whole
source profile at the event's rank, whose typed configuration agrees with a
native configuration. -/
structure RevealSource (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId)
    (config : (graph setup).Config) where
  Γ : SourceCtx Player L
  names : Finset VarId
  published : VarId
  owner : Player
  name : VarId
  payload : L.Ty
  fresh : published ∉ Γ.map Prod.fst
  binding : HasVar Γ name (.commitment owner payload)
  unresolved : name ∈ names
  next : SourceProgram Player L ((published, .publication payload) :: Γ) (names.erase name)
  residual : BehavioralProfile (.reveal published owner name fresh binding unresolved next)
  refs : ContextRefs (graphLayout setup.program) Γ
  source : Config Player L Γ
  embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
    (.reveal published owner name fresh binding unresolved next)
  refsBefore : ContextRefsBefore refs embedding
  aligned : CompiledPolicySuffix setup.program profile
    (.reveal published owner name fresh binding unresolved next) residual refs
      source.revelations source.registry embedding refsBefore event.val
  agree : refs.Agrees source.state config.store
  history : decodeHistory setup.program
    (config.history.map (setup.eventGraph.fromModeCompletion .sequential)) = source.history
  head : embedding.event ⟨0, by simp [eventCount]⟩ = event
  inherits : (∀ who, (profile who).EffectiveDisclosures setup.program []
    (Revelations.initial setup.context)) →
      ∀ who, (residual who).EffectiveDisclosures
        (.reveal published owner name fresh binding unresolved next)
          source.registry source.revelations
  supported : (∀ who, (profile who).SupportsEffectiveChoices setup.program
    (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context)) →
      ∀ who, (residual who).SupportsEffectiveChoices
        (.reveal published owner name fresh binding unresolved next)
        (CommitmentInterface.values (.reveal published owner name fresh binding unresolved next))
          source.registry source.revelations

namespace RevealSource

variable {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
  {event : (graph setup).EventId} {config : (graph setup).Config}
  (site : RevealSource setup profile event config)

/-- The disclosure's owner acts at the event. -/
theorem owned : (graph setup).actor? event = some site.owner := by
  have actor := site.aligned.actorEq ⟨0, by simp [eventCount]⟩
  rw [site.head] at actor
  exact actor

/-- The event's output is the disclosure's publication. -/
theorem outputEq : (graph setup).outputLayout event = .publication site.payload := by
  have head : (graph setup).outputLayout (site.embedding.event ⟨0, by simp [eventCount]⟩) =
      .publication site.payload := by
    change outputLayout setup.program (site.embedding.event _) = _
    simpa [outputLayout, eventCount] using site.embedding.layout_eq ⟨0, by simp [eventCount]⟩
  exact (congrArg (graph setup).outputLayout site.head).symm.trans head

end RevealSource

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- At every retained decision during a binding event's phase, the residual
source program at that event is a commitment aligned with the given profile. -/
theorem exists_bindingSource (profile : BehavioralProfile service.setup.program)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {owner : Player} {payload : L.Ty}
    (isBinding : (graph service.setup).outputLayout phase.event = .binding owner payload) :
    Nonempty (BindingSource service.setup profile phase.event execution.application.config) := by
  obtain ⟨event, _, _, _, _, Γ, names, remaining, remainingProfile, source, refs, embedding,
      refsBefore, aligned, _, _, _, _, _, _, grant, _, _, _, _, publicEq, checkpoint, _⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network profile
      who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phase.event := phase.sole.2 event grant.1
  subst same
  cases remaining with
  | ret result =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := phase.event.isLt
      change phase.event.val < eventCount service.setup.program at inside
      omega
  | sample name fresh law next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = phase.event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have actor := aligned.actorEq ⟨0, by simp [eventCount]⟩
      rw [headEq] at actor
      change (graph service.setup).actor? phase.event = none at actor
      rw [binding_actor service.setup phase.event owner payload isBinding] at actor
      cases actor
  | @commit Γ names name owner payload fresh guard next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = phase.event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      exact ⟨⟨Γ, names, name, owner, payload, fresh, guard, next, remainingProfile, refs, source,
        embedding, refsBefore, aligned, checkpoint.agrees, checkpoint.history, headEq⟩⟩
  | @reveal Γ names published owner name payload fresh binding unresolved next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = phase.event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph service.setup).outputLayout phase.event = .publication payload := by
        rw [← headEq]
        change outputLayout service.setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans isBinding

/-- At every retained decision during a disclosure event's phase, the residual
source program at that event is a disclosure aligned with the given profile. -/
theorem exists_revealSource (profile : BehavioralProfile service.setup.program)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {payload : L.Ty}
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload) :
    Nonempty (RevealSource service.setup profile phase.event execution.application.config) := by
  obtain ⟨event, _, _, _, _, Γ, names, remaining, remainingProfile, source, refs, embedding,
      refsBefore, aligned, _, ⟨supported, inherits, _⟩, _, _, _, _, grant, _, _, _, _, publicEq,
      checkpoint, _⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network profile
      who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phase.event := phase.sole.2 event grant.1
  subst same
  cases remaining with
  | ret result =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := phase.event.isLt
      change phase.event.val < eventCount service.setup.program at inside
      omega
  | sample name fresh law next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = phase.event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have layout := embedding.layout_eq ⟨0, by simp [eventCount]⟩
      simp only [outputLayout, eventCount] at layout
      rw [head] at layout
      cases layout.symm.trans isPublication
  | @commit Γ names name owner payload fresh guard next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = phase.event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph service.setup).outputLayout phase.event = .binding owner payload := by
        rw [← head]
        change outputLayout service.setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans isPublication
  | @reveal Γ names published owner name payload fresh binding unresolved next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = phase.event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      exact ⟨⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next,
        remainingProfile, refs, source, embedding, refsBefore, aligned, checkpoint.agrees,
        checkpoint.history, head, inherits, supported⟩⟩

end SourceServiceSpec

end Vegas

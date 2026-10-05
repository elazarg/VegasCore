/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Source.DisclosureSupport

/-! # Residual source constructors aligned with native configurations

These data identify a residual binding or resolution and its typed store and
history agreement. They contain no roster position, scheduler contract or
information-set claim. Actual site reachability is established separately.
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

end Vegas

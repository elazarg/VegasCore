/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceStep
import Vegas.Game.ServiceRosterPolicy
import Vegas.Source.DisclosureBehavioral

/-! # Effective guarded source disclosures in the native service

The actual deferred-check result decides whether an authentic opening exists.
Normalized source policies prescribe true only in the successful branch. No
assumption that every initialized or newly committed value passes its future
guard is needed for these local correspondences.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
private theorem disclosureResult_success_binding
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (value : L.Val payload)
    (success : disclosureResult published binding source true = .success value) :
    source.state.get binding = .success value := by
  simp only [disclosureResult, revealSuccessor, ite_true, Env.cons_get_here] at success
  split at success
  · exact success
  · cases success

/-- A successful deferred publication has an authentic current candidate.
The candidate may have been allocated by an earlier source commitment. -/
theorem guarded_rosterOpening_success
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (valid : execution.application.BindingInvariant)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (value : L.Val payload)
    (success : disclosureResult published binding source true = .success value) :
    ∃ candidate,
      execution.application.accepted (refs.get binding).field = some candidate ∧
      candidate.1 = owner ∧
      execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      rosterOpening? setup leaks owner event
        (execution.observe (application setup leaks) owner) =
          some (candidate, ⟨payload, value⟩) := by
  have stored : (refs.get binding).get? execution.application.config.store =
      some (.success value) := by
    simpa only [disclosureResult_success_binding published binding source value success,
      cellValue] using agree binding
  obtain ⟨candidate, associated, owned, verified⟩ :=
    valid.success_provenance (refs.get binding) value stored
  have resolved := compiled_disclosure_result published binding source refs
    execution.application.config.store agree true
  rw [success] at resolved
  refine ⟨candidate, associated, owned, verified, ?_⟩
  let view := execution.observe (application setup leaks) owner
  have observedResult : EventGraph.EventCode.resolveOutput? (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true view.application.observation.store = some (.success value) := resolved
  have observedHandle : view.application.publicView.accepted (refs.get binding).field =
      some candidate := associated
  change rosterOpening? setup leaks owner event view = _
  generalize viewEq : view = actualView at observedResult observedHandle ⊢
  simp only [rosterOpening?, node, observedResult, observedHandle, bind, Option.bind_some,
    owned, ne_eq, not_true_eq_false, ↓reduceIte]

/-- Guard failure suppresses the opening even though the binding itself may
be valid and permanently fixed. An effective false decision explicitly withholds. -/
theorem guarded_rosterOpening_failure
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
    (failure : disclosureResult published binding source true = .failure) :
    rosterOpening? setup leaks owner event
      (execution.observe (application setup leaks) owner) = none := by
  have resolved := compiled_disclosure_result published binding source refs
    execution.application.config.store agree true
  rw [failure] at resolved
  let view := execution.observe (application setup leaks) owner
  have observedResult : EventGraph.EventCode.resolveOutput? (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true view.application.observation.store = some .failure := resolved
  change rosterOpening? setup leaks owner event view = none
  generalize viewEq : view = actualView at observedResult ⊢
  simp only [rosterOpening?, node, observedResult]

/-- Every supported effective source choice either withholds or has a
successful deferred-check result. This applies to the actual behavioral
normalization, including its posterior at unreachable source observations. -/
theorem effective_reveal_supported
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (source : Config Player L Γ)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations)
    (disclose : Bool) (supported : disclose ∈ (revealKernel profile (source.view owner)).support) :
    disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ disclosureResult published binding source true = .success value := by
  cases disclose with
  | false => exact Or.inl rfl
  | true =>
      have fixed := effective.1 rfl (source.view owner) true supported
      change effectiveDisclosureView published binding source.registry source.revelations
        (sourceObserve owner source.state) true = true at fixed
      rw [effectiveDisclosureView_observe] at fixed
      cases result : disclosureResult published binding source true with
      | failure => simp only [effectiveDisclosure, result, Bool.false_eq_true] at fixed
      | success value => exact Or.inr ⟨value, rfl, rfl⟩

end Vegas

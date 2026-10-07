/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Game.SourceServiceStep
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Pending.ReactiveCanonicalResolution
import Vegas.Source.DisclosureOpening

/-! # The opening client opens from its own stored commitment

A source profile that opens effectively at a reveal
(`Vegas.SourceProgram.BehavioralPolicy.OpensEffectively`) is compiled, at the
owner's turn at that reveal, to the canonical decision to disclose, whatever
else is pending (`Vegas.serviceCanonicalPolicy_reveal_opening`). When every
field the source view reads is present, the source decision discloses exactly
when the opening is effective, and an ineffective opening is silent in either
case; when an earlier publication is still pending, the view cannot be decoded
and the compiled decision attempts the opening, which the runtime sends only
when the owner's stored commitment opens.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- **The opening client discloses.** At a ready reveal whose owner's source
policy opens effectively, from any execution at which every referenced field
other than a publication is present, the owner's canonical policy is the
canonical decision to disclose. -/
theorem serviceCanonicalPolicy_reveal_opening {Γ : SourceCtx Player L}
    {openNames : Finset VarId} {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh selected unresolved next) profile
      refs revelations registry embedding refsBefore offset)
    (opens : ∀ own view, (profile owner).1 own view = PMF.pure
      (effectiveDisclosureView published selected registry revelations (own.symm ▸ view.1) true))
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩))
    (available : ∀ {readName : VarId} {cell : CellTy Player L} (ref : HasVar Γ readName cell),
      (∀ other, cell ≠ .publication other) →
        ((refs.get ref).get? execution.application.config.store).isSome) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .publication payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode deadline leaks wholeProfile owner (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
        (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner)
        (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) := by
  intro headIndex outputEq
  let app := serviceApplication setup mode deadline leaks
  let event := embedding.event headIndex
  let store := execution.application.config.store
  have actor : (serviceGraph setup mode).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  by_cases complete : ∀ {readName : VarId} {cell : CellTy Player L}
      (ref : HasVar Γ readName cell), ((refs.get ref).get? store).isSome
  · -- Every referenced field is present: the source decision is the effective one.
    obtain ⟨state, decoded⟩ := Option.isSome_iff_exists.mp
      (decodeState?_isSome_of_refs refs store complete)
    have agree : refs.Agrees state store := fun ref => decodeState?_agrees refs store state
      decoded ref
    let source : Config Player L Γ := ⟨state, registry, revelations,
      decodeHistory setup.program (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode))⟩
    have law := sourceServiceCanonicalPolicy_reveal setup leaks fresh selected unresolved next
      wholeProfile profile refs source embedding refsBefore offset aligned execution agree rfl
      ready
    simp only at law
    rw [law]
    have kernel : revealKernel profile (source.view owner) = PMF.pure
        (effectiveDisclosure published selected source true) := by
      rw [revealKernel, opens rfl (source.view owner)]
      exact congrArg PMF.pure (effectiveDisclosureView_observe published selected source true)
    rw [kernel, PMF.pure_map]
    cases effective : effectiveDisclosure published selected source true with
    | true => rfl
    | false =>
        have codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout)
            outputEq) ((serviceGraph setup mode).nodes event) = .resolve owner payload
              (refs.get selected) (compileChecks (published := published) refs registry
                revelations selected) := by
          change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
            ((toEventGraph setup.program).nodes event) = _
          simpa [event, headIndex, compileRankedNodes] using aligned.graphSuffix.nodeEq headIndex
        have node := EventGraphRuntime.nodeView_eq_resolve (graph := serviceGraph setup mode)
          outputEq codeEq
        rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_resolution_false leaks
          owner _ _ event owner payload _ _ outputEq codeEq node]
        refine congrArg PMF.pure ((serviceRuntime setup mode
          deadline).canonicalServiceDecision_resolution_unvalidated
          leaks owner _ _ event owner payload _ _ outputEq codeEq node ?_).symm
        intro value candidate resolved _
        have result := compiled_disclosure_result (graph := serviceGraph setup mode) published
          selected source refs store agree true
        change EventGraph.EventCode.resolveOutput? (refs.get selected)
          (compileChecks (published := published) refs registry revelations selected) true
          ((serviceGraph setup mode).playerStore owner store) = _ at resolved
        rw [result] at resolved
        have failed : disclosureResult published selected source true = .failure := by
          unfold effectiveDisclosure at effective
          split at effective
          · assumption
          · cases effective
        rw [failed] at resolved
        cases resolved
  · -- An earlier publication is pending: the view cannot be decoded and the
    -- compiled decision attempts the opening.
    simp only [not_forall, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at complete
    obtain ⟨readName, cell, ref, missing⟩ := complete
    obtain ⟨other, rfl⟩ : ∃ other, cell = .publication other := by
      by_contra plain
      have present := available ref fun other same => plain ⟨other, same⟩
      rw [missing] at present
      cases present
    have undecodable : decodeObservation? owner refs
        ((serviceGraph setup mode).playerStore owner store) = none := by
      exact (decodeObservation?_playerStore (graph := serviceGraph setup mode) owner refs
        store).trans (decodeObservation?_eq_none_of_publication refs owner store ref missing)
    rw [sourceServiceCanonicalPolicy_at_event setup leaks wholeProfile owner execution event
      (serviceOwnTurn?_of_ready setup execution.application ready actor) actor]
    let observation := setup.eventGraph.fromModeObservation mode owner
      ((serviceGraph setup mode).playerObserve owner execution.application.config)
    have policyLaw := aligned.policyEq owner headIndex actor observation
    change _ = compilePolicyTable (.reveal published owner name fresh selected unresolved next)
      refs embedding.ref owner (profile owner) ⟨0, by simp [eventCount]⟩
        ((serviceGraph setup mode).playerStore owner store)
        (decodeCompletions setup.program observation.ownActions) at policyLaw
    rw [compilePolicyTable_reveal_of_decode_none refs embedding.ref (profile owner) rfl _ _
      undecodable] at policyLaw
    have actionLaw := eq_map_cast_of_cast_eq
      (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ policyLaw
    rw [actionLaw, PMF.map_comp, PMF.pure_map]
    rfl

end Vegas

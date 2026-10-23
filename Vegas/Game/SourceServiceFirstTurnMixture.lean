/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceReachedDecoding

/-! # First-turn decisions of a fixed source action

The owner's policy deciding one fixed source action at its first turn at an
event, and silent at every other input (`Vegas.decidedTurnPolicy`), makes the
canonical compiled decision of that action while a fresh call still fits the
deadline (`Vegas.decidedOpportunity`). An action is effective when the compiled
decision realizes it (`Vegas.EffectiveAction`), and silent when it is a
disclosure of `false` (`Vegas.SilentAction`). On the source side, the
continuation from a decoded configuration draws the head event's source action
and continues from the configuration completed with it
(`Vegas.SourceResidual.head_law`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The owner's response with its source action fixed: the canonical compiled
decision when it transmits and a fresh call still fits the deadline within the
inclusion bound, and silence when the decision is silent, too late, or the event is
already recorded in the owner's own recall. -/
def decidedOpportunity (bound : (serviceGraph setup mode).EventId → Nat) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event) :
    (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  if (serviceRuntime setup mode deadline).eventRecorded leaks past event then
    (serviceApplication setup mode deadline leaks).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
      bound event then if
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past view event
          action).transmission = none then
      (serviceApplication setup mode deadline leaks).silentPolicy past view else PMF.pure
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past view
          event action)
  else (serviceApplication setup mode deadline leaks).silentPolicy past view

/-- Decide `action` at the first turn at `event`, and stay silent at every other
input. -/
def decidedTurnPolicy (bound : (serviceGraph setup mode).EventId → Nat) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event) :
    (serviceApplication setup mode deadline leaks).Policy :=
  (serviceApplication setup mode deadline leaks).turnScheduledPolicy
  (serviceTurn setup mode deadline leaks owner event) (some (0 : Fin 1))
  (decidedOpportunity setup leaks bound owner event action)
  (serviceApplication setup mode deadline leaks).silentPolicy

variable {setup}

/-- An action that the compiled decision realizes: a disclosure of `true` only
when the publication succeeds on the configuration. -/
def EffectiveAction (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) : Prop :=
  match nodeView (serviceGraph setup mode) event with
  | .resolve _ _ binding checks outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true →
        ∃ value, EventGraph.EventCode.resolveOutput? binding checks true config.store =
          some (.success value)
  | _ => True

/-- An action realized by silence: a disclosure of `false`. -/
def SilentAction (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) : Prop :=
  match nodeView (serviceGraph setup mode) event with
  | .resolve _ _ _ _ outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = false
  | _ => False

variable {leaks}

section Sequential

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Head

variable [Finite Player] (leaks) {profile : BehavioralProfile setup.program}

/-- **The source step at the head of a residual.** The source continuation of
a decoded configuration draws the head event's source action and continues
from the configuration completed with it. At an owned event that action law
is the source decision, compiled to native responses by the source policy,
and under effective disclosures every supported action is realized by the
compiled decision, and under disclosing profiles no supported action is a
disclosure of `false`. -/
theorem SourceResidual.head_law {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config) (event : (graph setup).EventId)
    (atRank : event.val = rank) (ready : config.cut.Ready event) :
    ∃ law : PMF ((graph setup).Action event),
      sourceContinuation setup profile rank config =
        law.bind (fun action => (config.step event ready action).bind
          fun next => sourceContinuation setup profile (rank + 1) next) ∧
      (∀ owner, (graph setup).actor? event = some owner →
        ∀ current : (application setup leaks).Execution, current.application.config = config →
          sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
              (current.observe (application setup leaks) owner) =
            law.map fun action => (runtime setup).canonicalServiceDecision leaks owner
              (current.recall owner) (current.observe (application setup leaks) owner) event
              action) ∧
      ((∀ who, (profile who).EffectiveDisclosures setup.program []
          (Revelations.initial setup.context)) →
        ∀ action ∈ law.support, EffectiveAction config event action) ∧
      ((∀ who, Disclosing setup.program (profile who)) →
        ∀ action ∈ law.support, ¬ SilentAction event action) := by
  let := Fintype.ofFinite Player
  have decoded := residual.decode
  rcases residual with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, effective, supports, disclosing, lift, commutes, steps, injective,
    transport,
    checkpoint⟩
  dsimp only at decoded
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = (graph setup).order.eventCount at counted
  have sourceEq : sourceContinuation setup profile rank config =
      (ProtocolState.behavioralStateStep program residualProfile
        (ProtocolState.entry program source)).bind
          fun state => (ProtocolState.continuationLaw setup.program profile (lift state)).map
            some := by
    unfold sourceContinuation
    simp only [sourceServicePrefix?] at decoded
    rw [decoded]
    change (ProtocolState.continuationLaw setup.program profile (lift _)).map some = _
    rw [← sourceStep_continuation setup.program profile, commutes, PMF.bind_map, PMF.map_bind]
    rfl
  have nextDecode (state : ProtocolState program) (next : (graph setup).Config)
      (read : decodeSourcePrefix? program refs source.registry source.revelations embedding.ref
        1 next.store (decodeHistory setup.program
          (next.history.map (setup.eventGraph.fromModeCompletion .sequential))) =
        some state) :
      sourceContinuation setup profile (rank + 1) next =
        (ProtocolState.continuationLaw setup.program profile (lift state)).map some := by
    unfold sourceContinuation serviceSourcePrefix?
    rw [transport 1, read]
    rfl
  cases program with
  | ret payoffs =>
      have := event.isLt
      simp only [eventCount] at counted
      omega
  | @sample Γ openNames name payload fresh distribution next =>
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atRank.trans headRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .sample payload (compilePublicDist refs distribution) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      have chance : (graph setup).actor? (embedding.event index) = none := by
        change (toEventGraph setup.program).actor? (embedding.event index) = none
        simpa [index, eventOwner?, eventCount] using aligned.actorEq index
      have decodedAction : decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        simpa [index, outputEq, decodeEventAction] using lookup
      refine ⟨PMF.pure (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit),
        ?_, ?_, ?_, ?_⟩
      · have entryStep : ProtocolState.behavioralStateStep (.sample name fresh distribution next)
            residualProfile (ProtocolState.entry _ source) =
              (L.evalDist distribution (sourcePublicEnv source.state)).map (fun value =>
                Sum.inr (ProtocolState.entry next (sampleSuccessor name source value))) :=
          ProtocolState.behavioralStateStep_sample_entry residualProfile source
        rw [sourceEq, entryStep, PMF.pure_bind, sample_step config _ ready outputEq refs
          distribution codeEq source.state checkpoint.agrees, PMF.bind_map, PMF.bind_map]
        apply bind_congr_on_support _
        intro value _
        symm
        apply nextDecode
        exact (decodeSourcePrefix?_sample fresh distribution next refs source.registry
          source.revelations embedding.ref 0 _ _).trans (congrArg (Option.map Sum.inr)
            ((checkpoint.sample (native := configState config) name (embedding.event index)
              headRank ready outputEq (fun ref => refsBefore ref index) decodedAction
              value).decode next (fun tail => embedding.ref tail.succ)))
      · intro owner owned
        rw [chance] at owned
        cases owned
      · intro _ action _
        unfold EffectiveAction
        rw [EventGraphRuntime.nodeView_eq_sample outputEq codeEq]
        trivial
      · intro _ action _
        unfold SilentAction
        rw [EventGraphRuntime.nodeView_eq_sample outputEq codeEq]
        exact id
  | @commit Γ openNames name owner payload fresh guard next =>
      let index : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atRank.trans headRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) = .bind owner payload := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      have actor : (graph setup).actor? (embedding.event index) = some owner := by
        change (toEventGraph setup.program).actor? (embedding.event index) = some owner
        simpa [index, eventOwner?, eventCount] using aligned.actorEq index
      have decodedAction (choice : PublicationResult (L.Val payload)) :
          decodeEventAction setup.program (embedding.event index)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
              some (.commit owner name payload choice) := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
        simpa [index, outputEq, decodeEventAction] using lookup
      refine ⟨(commitKernel residualProfile (source.view owner)).map
        (fun choice => cast (congrArg EventGraph.EventField.Action outputEq.symm) choice),
        ?_, ?_, ?_, ?_⟩
      · have entryStep : ProtocolState.behavioralStateStep (.commit name owner fresh guard next)
            residualProfile (ProtocolState.entry _ source) =
              (commitKernel residualProfile (source.view owner)).map (fun choice =>
                Sum.inr (ProtocolState.entry next (commitSuccessor name guard source choice))) :=
          ProtocolState.behavioralStateStep_commit_entry residualProfile source
        rw [sourceEq, entryStep, PMF.bind_map, PMF.bind_map]
        apply bind_congr_on_support _
        intro choice _
        simp only [Function.comp_apply]
        rw [commit_step config _ ready outputEq codeEq choice, PMF.pure_bind]
        symm
        apply nextDecode
        exact (decodeSourcePrefix?_commit fresh guard next refs source.registry
          source.revelations embedding.ref 0 _ _).trans (congrArg (Option.map Sum.inr)
            ((checkpoint.commit (native := configState config) name guard
              (embedding.event index) headRank ready outputEq (fun ref => refsBefore ref index)
              choice (decodedAction choice)).decode next (fun tail => embedding.ref tail.succ)))
      · intro who owned current sameConfig
        have whoEq : who = owner := Option.some.inj (owned.symm.trans actor)
        subst whoEq
        have law := sourceServiceCanonicalPolicy_commit setup leaks fresh guard next profile
          residualProfile refs source embedding refsBefore rank aligned current
          (by rw [sameConfig]; exact checkpoint.agrees)
          (by rw [sameConfig]; exact checkpoint.history) (by rw [sameConfig]; exact ready)
        rw [show sourceServiceCanonicalPolicy setup leaks = serviceCanonicalPolicy setup .sequential
          (rankDeadline setup .sequential) leaks from rfl, law, PMF.map_comp]
        rfl
      · intro _ action _
        unfold EffectiveAction
        rw [EventGraphRuntime.nodeView_eq_bind outputEq codeEq]
        trivial
      · intro _ action _
        unfold SilentAction
        rw [EventGraphRuntime.nodeView_eq_bind outputEq codeEq]
        exact id
  | @reveal Γ openNames published owner name payload fresh selected unresolved next =>
      let index : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atRank.trans headRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publication payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      let checks := compileChecks (published := published) refs
        source.registry source.revelations selected
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .resolve owner payload (refs.get selected) checks := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes, checks] using aligned.graphSuffix.nodeEq index
      have actor : (graph setup).actor? (embedding.event index) = some owner := by
        change (toEventGraph setup.program).actor? (embedding.event index) = some owner
        simpa [index, eventOwner?, eventCount] using aligned.actorEq index
      have decodedAction (disclose : Bool) : decodeEventAction setup.program
          (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
            some (.reveal owner name disclose) := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        simpa [index, outputEq, decodeEventAction] using lookup
      have stepEq (disclose : Bool) : config.step (embedding.event index) ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
            PMF.pure (config.complete (embedding.event index) ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (disclosureResult published selected source disclose))) := by
        rw [config.step_eq_map_of_code _ ready outputEq _ codeEq disclose
          (PMF.pure (disclosureResult published selected source disclose))
          (compileResolve_eval? refs source.registry source.revelations source.state
            config.store checkpoint.agrees selected disclose), PMF.pure_map]
      refine ⟨(revealKernel residualProfile (source.view owner)).map
        (fun disclose => cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose),
        ?_, ?_, ?_, ?_⟩
      · have entryStep : ProtocolState.behavioralStateStep
            (.reveal published owner name fresh selected unresolved next)
            residualProfile (ProtocolState.entry _ source) =
              (revealKernel residualProfile (source.view owner)).map (fun disclose =>
                Sum.inr (ProtocolState.entry next
                  (revealSuccessor published selected source disclose))) :=
          ProtocolState.behavioralStateStep_reveal_entry residualProfile source
        rw [sourceEq, entryStep, PMF.bind_map, PMF.bind_map]
        apply bind_congr_on_support _
        intro disclose _
        simp only [Function.comp_apply]
        rw [stepEq disclose, PMF.pure_bind]
        symm
        apply nextDecode
        exact (decodeSourcePrefix?_reveal fresh selected unresolved next refs source.registry
          source.revelations embedding.ref 0 _ _).trans (congrArg (Option.map Sum.inr)
            ((checkpoint.reveal (native := configState config) published selected
              (embedding.event index) headRank ready outputEq (fun ref => refsBefore ref index)
              disclose (decodedAction disclose)).decode next
                (fun tail => embedding.ref tail.succ)))
      · intro who owned current sameConfig
        have whoEq : who = owner := Option.some.inj (owned.symm.trans actor)
        subst whoEq
        have law := sourceServiceCanonicalPolicy_reveal setup leaks fresh selected unresolved next
          profile residualProfile refs source embedding refsBefore rank aligned current
          (by rw [sameConfig]; exact checkpoint.agrees)
          (by rw [sameConfig]; exact checkpoint.history) (by rw [sameConfig]; exact ready)
        rw [show sourceServiceCanonicalPolicy setup leaks = serviceCanonicalPolicy setup .sequential
          (rankDeadline setup .sequential) leaks from rfl, law, PMF.map_comp]
        rfl
      · intro effectiveWhole action member
        unfold EffectiveAction
        rw [EventGraphRuntime.nodeView_eq_resolve outputEq codeEq]
        obtain ⟨disclose, chosen, rfl⟩ := PMF.support_map .. ▸ member
        intro requested
        simp only [cast_cast, cast_eq] at requested
        subst requested
        have kept := (effective effectiveWhole owner).1 rfl (source.view owner) true chosen
        change effectiveDisclosureView published selected source.registry source.revelations
          (sourceObserve owner source.state) true = true at kept
        rw [effectiveDisclosureView_observe] at kept
        have resolved := compiled_disclosure_result published selected source refs config.store
          checkpoint.agrees true
        rw [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
        cases result : disclosureResult published selected source true with
        | failure => simp only [effectiveDisclosure, result] at kept; cases kept
        | success value => exact ⟨value, by rw [resolved, result]⟩
      · intro disclosingWhole action member
        unfold SilentAction
        rw [EventGraphRuntime.nodeView_eq_resolve outputEq codeEq]
        obtain ⟨disclose, chosen, rfl⟩ := PMF.support_map .. ▸ member
        intro withheld
        simp only [cast_cast, cast_eq] at withheld
        subst withheld
        exact (disclosing disclosingWhole owner).1 rfl (source.view owner) chosen

end Head

end Sequential

end Vegas

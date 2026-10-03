/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceReachedDecoding

/-! # The first-turn decision as a mixture over source actions

At a completion boundary the owner of the current event decides at its first
turn there. Its response at that turn is the source decision kernel of the
decoded source position, compiled to a native response; at every other input
it replays. Since the configuration does not change before the event
completes, the kernel is the same at whichever input the first turn falls, so
the owner's policy is a behavioral mixture over source actions of the policies
that decide one fixed action at the first turn
(`Vegas.firstTurn_runUntil_mixture`). The compiled head-action kernel and its
actual next-prefix decoder have the same law as the whole source behavioral
step (`Vegas.SourceResidual.head_step`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The owner's response with its source action fixed: the canonical compiled
decision when it transmits and a fresh call still fits the deadline within the
inclusion bound, and a replay when it is silent, too late, or the event is
already recorded in the owner's own recall. -/
def decidedOpportunity (bound : (graph setup).EventId → Nat) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event) :
    (application setup leaks).Policy := fun past view =>
  if (runtime setup).eventRecorded leaks past event then
    (application setup leaks).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline (runtime setup) bound event then
    if ((runtime setup).canonicalServiceDecision leaks owner past view event
        action).transmission = none then (application setup leaks).silentPolicy past view
    else PMF.pure ((runtime setup).canonicalServiceDecision leaks owner past view event action)
  else (application setup leaks).silentPolicy past view

/-- Decide `action` at the first turn at `event`, and replay at every other
input. -/
def decidedTurnPolicy (bound : (graph setup).EventId → Nat) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event) :
    (application setup leaks).Policy :=
  (application setup leaks).turnScheduledPolicy (sourceServiceTurn setup leaks owner event)
    (some (0 : Fin 1)) (decidedOpportunity setup leaks bound owner event action)
    (application setup leaks).silentPolicy

variable {setup}

/-- An action that the compiled decision realizes: a disclosure of `true` only
when the publication succeeds on the configuration. -/
def EffectiveAction (config : (graph setup).Config) (event : (graph setup).EventId)
    (action : (graph setup).Action event) : Prop :=
  match nodeView (graph setup) event with
  | .resolve _ _ binding checks outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true →
        ∃ value, EventGraph.EventCode.resolveOutput? binding checks true config.store =
          some (.success value)
  | _ => True

variable {leaks}

/-- Before its first turn at `event`, an owner's recorded entries were not
turns at `event`, so a first-turn family replays at all of them. -/
private theorem turn_none_of_first (owner : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (first : sourceServiceTurn setup leaks owner event past view = some 0)
    (before : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) (member : before ++ [entry] <+: past) :
    sourceServiceTurn setup leaks owner event before entry.beforeView = none := by
  apply sourceServiceTurn_of_not_turn
  intro turn
  unfold sourceServiceTurn at first
  split at first
  · have counted := Option.some.inj first
    rw [List.countP_eq_zero] at counted
    have inPast : entry ∈ past :=
      member.subset (List.mem_append_right _ (List.mem_singleton_self _))
    exact counted entry inPast (decide_eq_true turn)
  · cases first

/-- **First-turn mixture.** From a completion boundary of any players, if the
source decision at the boundary configuration is `law` compiled to native
responses, the owner's first-turn family runs as the `law`-mixture of the
policies deciding one fixed action. -/
theorem firstTurn_runUntil_mixture {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (law : PMF ((graph setup).Action event))
    (policy : ∀ current : (application setup leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
          (current.observe (application setup leaks) owner) =
        law.map fun action => (runtime setup).canonicalServiceDecision leaks owner
          (current.recall owner) (current.observe (application setup leaks) owner) event action)
    (count : Nat) :
    (application setup leaks).runUntil scheduler
        (firstTurnProfile setup leaks bound turns profile event)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      law.bind fun action => (application setup leaks).runUntil scheduler
        (Function.update (fun _ => (application setup leaks).silentPolicy) owner
          (decidedTurnPolicy setup leaks bound owner event action))
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := application setup leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let mixture := app.policyMixture law (decidedTurnPolicy setup leaks bound owner event)
  let family := sourceServiceTurnFamily setup leaks bound profile owner event turns 0
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler players _ execution
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  have firstEq : firstTurnProfile setup leaks bound turns profile event =
      Function.update (fun _ => app.silentPolicy) owner family := by
    unfold firstTurnProfile
    simp only [owned]
    rfl
  rw [firstEq]
  -- The first-turn family agrees with the mixture wherever the configuration is unchanged.
  have agree (current : app.Execution)
      (same : current.application.config = execution.application.config) :
      family (current.recall owner) (current.observe app owner) =
        mixture.policy (current.recall owner) (current.observe app owner) := by
    rw [app.policyMixture_policy]
    cases turn : sourceServiceTurn setup leaks owner event (current.recall owner)
        (current.observe app owner) with
    | none =>
        rw [show family (current.recall owner) (current.observe app owner) = _ from
          app.turnScheduledPolicy_of_none _ _ _ _ _ _ turn]
        have members : ∀ action, decidedTurnPolicy setup leaks bound owner event action
            (current.recall owner) (current.observe app owner) =
              app.silentPolicy (current.recall owner) (current.observe app owner) :=
          fun action => app.turnScheduledPolicy_of_none _ _ _ _ _ _ turn
        simp only [members, PMF.bind_const]
        rfl
    | some index =>
        by_cases zero : index = 0
        · subst zero
          have prior : mixture.posterior (current.recall owner) = law := by
            apply app.policyMixture_posterior_of_agree _ _ app.silentPolicy
            intro before entry member action
            exact app.turnScheduledPolicy_of_none _ _ _ _ _ _
              (turn_none_of_first owner event _ _ turn before entry member)
          rw [prior]
          have selected : family (current.recall owner) (current.observe app owner) =
              sourceServiceCanonicalOpportunity setup leaks bound profile owner event
                (current.recall owner) (current.observe app owner) :=
            app.turnScheduledPolicy_selected _ (0 : Fin (turns + 1)) _ _ _ _ turn
          have members : ∀ action, decidedTurnPolicy setup leaks bound owner event action
              (current.recall owner) (current.observe app owner) =
                decidedOpportunity setup leaks bound owner event action (current.recall owner)
                  (current.observe app owner) :=
            fun action => app.turnScheduledPolicy_selected _ (0 : Fin 1) _ _ _ _ turn
          rw [selected]
          simp only [members]
          unfold sourceServiceCanonicalOpportunity decidedOpportunity
          by_cases recorded : (runtime setup).eventRecorded leaks (current.recall owner) event
          · simp only [recorded, ↓reduceIte, PMF.bind_const]
          · by_cases fits : PublicView.InclusionFitsDeadline (runtime setup) bound
                (current.observe app owner).application.publicView event
            · simp only [recorded, fits, Bool.false_eq_true, ↓reduceIte]
              rw [policy current same, PMF.bind_map]
              rfl
            · simp only [recorded, fits, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
        · have other : ∀ slot : Fin 1, some index ≠ some slot.val := by
            intro slot equal
            exact zero ((Option.some.inj equal).trans (Fin.val_eq_zero slot))
          have otherFamily : ∀ slot : Fin (turns + 1), some (0 : Fin (turns + 1)) = some slot →
              some index ≠ some slot.val := by
            intro slot chosen equal
            rw [← Option.some.inj chosen] at equal
            exact zero (Option.some.inj equal)
          rw [show family (current.recall owner) (current.observe app owner) = _ from
            app.turnScheduledPolicy_unselected _ _ _ _ _ _ (fun slot chosen => by
              rw [turn]; exact otherFamily slot chosen)]
          have members : ∀ action, decidedTurnPolicy setup leaks bound owner event action
              (current.recall owner) (current.observe app owner) =
                app.silentPolicy (current.recall owner) (current.observe app owner) :=
            fun action => app.turnScheduledPolicy_unselected _ _ _ _ _ _ (fun slot chosen => by
              rw [turn]; exact other slot)
          simp only [members, PMF.bind_const]
          rfl
  let invariant := fun current : app.Execution =>
    ReadySeen setup leaks event.val current ∧
      (current.application.config = execution.application.config ∨
        current.application.config.cut.IsPrefix (event.val + 1))
  have sameOf (current : app.Execution) (holds : invariant current) (running : ¬ stop current) :
      current.application.config = execution.application.config := by
    rcases holds.2 with same | advanced
    · exact same
    · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim
  have congruent : app.runUntil scheduler
      (Function.update (fun _ => app.silentPolicy) owner family) stop count execution =
      app.runUntil scheduler (Function.update (fun _ => app.silentPolicy) owner mixture.policy)
        stop count execution := by
    apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
    · intro current holds running command _ middle moved who active
      cases command with
      | activate actor =>
          have sameApp := activation_application setup leaks current middle actor moved
          by_cases isOwner : who = owner
          · subst isOwner
            simp only [Function.update_self]
            exact agree middle (by rw [sameApp]; exact sameOf current holds running)
          · simp only [Function.update_of_ne isOwner]
      | «include» _ => cases active
      | application _ => cases active
      | wait => cases active
    · intro current holds running next reached
      obtain ⟨nextSeen, nextConfig⟩ := round_prefix setup leaks scheduler _ event.val current
        next (by rw [sameOf current holds running]; exact boundary.ordered) holds.1 reached
      refine ⟨nextSeen, ?_⟩
      rcases nextConfig with same | advanced
      · exact Or.inl (same.trans (sameOf current holds running))
      · exact Or.inr advanced
    · exact ⟨seen, Or.inl rfl⟩
  change app.runUntil scheduler (Function.update (fun _ => app.silentPolicy) owner family) stop
    count execution = _
  rw [congruent, ← app.runUntil_policyMixture scheduler law
    (decidedTurnPolicy setup leaks bound owner event) owner _ stop count execution]
  have prior : mixture.posterior (execution.recall owner) = law := by
    apply app.policyMixture_posterior_of_agree _ _ app.silentPolicy
    intro before entry member action
    apply app.turnScheduledPolicy_of_none
    apply sourceServiceTurn_of_not_turn
    intro turn
    have entryMember : entry ∈ execution.recall owner :=
      member.subset (List.mem_append_right _ (List.mem_singleton_self _))
    exact boundary.untouched event rfl owner entry entryMember
      (PublicView.ownTurn?_spec _ owner event turn).1
  change (mixture.posterior (execution.recall owner)).bind _ = _
  rw [prior]

section Head

variable [Fintype Player] (leaks) {profile : BehavioralProfile setup.program}

/-- The compiled head-action kernel reads the same whole source successor as
the behavioral source step. At an owned event its action law is compiled by
the canonical policy. Effective disclosures ensure every supported action is
realized by that decision. The readout retains the intermediate source state,
before applying any continuation or utility. -/
theorem SourceResidual.head_step {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config) (event : (graph setup).EventId)
    (atRank : event.val = rank) (ready : config.cut.Ready event) :
    ∃ law : PMF ((graph setup).Action event),
      (ProtocolState.behavioralStateStep setup.program profile
        (residual.lift (ProtocolState.entry residual.program residual.source))).map some =
        (law.bind fun action => config.step event ready action).map
          (sourceServicePrefix? setup (rank + 1)) ∧
      (∀ owner, (graph setup).actor? event = some owner →
        ∀ current : (application setup leaks).Execution, current.application.config = config →
          sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
              (current.observe (application setup leaks) owner) =
            law.map fun action => (runtime setup).canonicalServiceDecision leaks owner
              (current.recall owner) (current.observe (application setup leaks) owner) event
              action) ∧
      ((∀ who, (profile who).EffectiveDisclosures setup.program []
          (Revelations.initial setup.context)) →
        ∀ action ∈ law.support, EffectiveAction config event action) := by
  rcases residual with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, effective, supports, lift, _recoverView, _viewRecovered, commutes,
    steps, injective, transport,
    checkpoint⟩
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = (graph setup).order.eventCount at counted
  have sourceStep :
      (ProtocolState.behavioralStateStep setup.program profile
        (lift (ProtocolState.entry program source))).map some =
      (ProtocolState.behavioralStateStep program residualProfile
        (ProtocolState.entry program source)).map (fun state => some (lift state)) := by
    rw [commutes, PMF.map_comp]
    rfl
  have nextDecode (state : ProtocolState program) (next : (graph setup).Config)
      (read : decodeSourcePrefix? program refs source.registry source.revelations embedding.ref
        1 next.store (decodeHistory setup.program
          (next.history.map (setup.eventGraph.fromModeCompletion .sequential))) =
        some state) :
      sourceServicePrefix? setup (rank + 1) next = some (lift state) := by
    unfold sourceServicePrefix?
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
        ?_, ?_, ?_⟩
      · have entryStep : ProtocolState.behavioralStateStep (.sample name fresh distribution next)
            residualProfile (ProtocolState.entry _ source) =
              (L.evalDist distribution (sourcePublicEnv source.state)).map (fun value =>
                Sum.inr (ProtocolState.entry next (sampleSuccessor name source value))) :=
          ProtocolState.behavioralStateStep_sample_entry residualProfile source
        rw [sourceStep, entryStep, PMF.pure_bind, sample_step config _ ready outputEq refs
          distribution codeEq source.state checkpoint.agrees, PMF.map_comp, PMF.map_comp]
        apply map_congr_on_support _
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
        ?_, ?_, ?_⟩
      · have entryStep : ProtocolState.behavioralStateStep (.commit name owner fresh guard next)
            residualProfile (ProtocolState.entry _ source) =
              (commitKernel residualProfile (source.view owner)).map (fun choice =>
                Sum.inr (ProtocolState.entry next (commitSuccessor name guard source choice))) :=
          ProtocolState.behavioralStateStep_commit_entry residualProfile source
        rw [sourceStep, entryStep, PMF.map_comp, PMF.bind_map, PMF.map_bind]
        apply bind_congr_on_support _
        intro choice _
        simp only [Function.comp_apply]
        rw [commit_step config _ ready outputEq codeEq choice, PMF.pure_map]
        apply congrArg PMF.pure
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
        rw [law, PMF.map_comp]
        rfl
      · intro _ action _
        unfold EffectiveAction
        rw [EventGraphRuntime.nodeView_eq_bind outputEq codeEq]
        trivial
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
        ?_, ?_, ?_⟩
      · have entryStep : ProtocolState.behavioralStateStep
            (.reveal published owner name fresh selected unresolved next)
            residualProfile (ProtocolState.entry _ source) =
              (revealKernel residualProfile (source.view owner)).map (fun disclose =>
                Sum.inr (ProtocolState.entry next
                  (revealSuccessor published selected source disclose))) :=
          ProtocolState.behavioralStateStep_reveal_entry residualProfile source
        rw [sourceStep, entryStep, PMF.map_comp, PMF.bind_map, PMF.map_bind]
        apply bind_congr_on_support _
        intro disclose _
        simp only [Function.comp_apply]
        rw [stepEq disclose, PMF.pure_map]
        apply congrArg PMF.pure
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
        rw [law, PMF.map_comp]
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

end Head

end Vegas

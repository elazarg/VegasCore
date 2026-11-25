module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.NativeBindingRecord
public import Vegas.Game.BindingSourceObservation
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Predrawing a later private binding from its source prefix

Earlier fixed records of the same owner determine the callback at a later binding.
Its action can be sampled before the complete stopped native execution, while
all other clients remain active and the stopping predicate stays unchanged.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- A later binding can be predrawn from the matching ghost prefix. -/
theorem serviceReference_binding_prefix_mixture
    {horizon count remaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (notPublication : ¬ ((serviceGraph setup deps).outputLayout event).IsPublication)
    (background : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : background owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) ((serviceGraph setup deps).prefixProfile profile) owner)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (execution : (serviceApplication setup deps duration leaks).Execution)
    {inputs : (serviceGraph setup deps).Inputs}
    (initialReach : execution.application.config.Reachable inputs)
    (start : Nat) (ordered : execution.application.config.cut.IsPrefix start)
    (ghost : (serviceGraph setup deps).Config)
    (ghostPath : Relation.ReflTransGen Config.Step execution.application.config ghost)
    (ghostReady : ghost.cut.Ready event) (ghostActive : owner ∉ ghost.defaulted)
    (bindings : ∀ prior : (serviceGraph setup deps).EventId,
      start ≤ prior.val → prior.val < event.val →
      ∃ actor payload, (serviceGraph setup deps).outputLayout prior = .binding actor payload)
    (frozen : ∀ prior : (serviceGraph setup deps).EventId,
      start ≤ prior.val → prior.val < event.val →
      ∀ actor : (serviceGraph setup deps).actor? prior = some owner,
      ∃ (payload : L.Ty)
        (binding : (serviceGraph setup deps).outputLayout prior = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        (∀ view active,
          (serviceGraph setup deps).prefixProfile profile owner prior actor view active =
          PMF.pure (cast (congrArg EventField.Action binding.symm) (some result))) ∧
        completionOf ghost prior = some
          (EventGraph.completion (serviceGraph setup deps) prior
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)))
    (truthful : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks execution owner)
    (untouched : ∀ prior : (serviceGraph setup deps).EventId,
      start ≤ prior.val → prior.val ≤ event.val →
      (serviceGraph setup deps).actor? prior = some owner → Untouched setup leaks prior execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩)) :
    let app := serviceApplication setup deps duration leaks
    let reference := (serviceGraph setup deps).prefixProfile profile
    let players := turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference
    app.runUntil scheduler background stop count execution =
      (actionDistribution reference ghost event).bind (fun action =>
        app.runUntil scheduler
          (Function.update background owner (fun past view =>
            if turnIndex (serviceTimeouts setup deps duration)
              leaks owner event past view = some 0 then
              fixedOpportunity (serviceTimeouts setup deps duration) leaks
                bound owner event action past view
            else players owner past view)) stop count execution) := by
  classical
  intro app reference players
  let law := actionDistribution reference ghost event
  let first := fun past view => turnIndex (serviceTimeouts setup deps duration)
    leaks owner event past view = some 0
  let member := fun (action : (serviceGraph setup deps).Action event) past view =>
    if first past view then fixedOpportunity (serviceTimeouts setup deps duration) leaks
      bound owner event action past view
    else players owner past view
  let invariant := fun current : app.Execution =>
    (∃ used, current ∈ (app.runRounds scheduler background used execution).support) ∧
      Relation.ReflTransGen Config.Step execution.application.config current.application.config
  have restored : Function.update background owner (players owner) = background := by
    funext actor
    by_cases same : actor = owner
    · subst actor
      exact (Function.update_self ..).trans follows.symm
    · exact Function.update_of_ne same _ _
  have once : ∀ past view, first past view → ∀ before entry, before ++ [entry] <+: past →
      ¬ first before entry.beforeView := by
    intro past view selected before entry prefixed earlier
    have memberEntry : entry ∈ past := prefixed.subset (by simp)
    exact (sourceServiceTurn_first selected).2 entry memberEntry
      (sourceServiceTurn_first earlier).1
  have atFirst : ∀ left current,
      (app.protocol (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨left + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ command ∈ (scheduler current.environmentRecall (current.observeEnvironment app)).support,
      ∀ middle ∈ (current.environmentStep app command).support,
        command.actor? app = some owner → first (middle.logs owner) (middle.observe app owner) →
        players owner (middle.logs owner) (middle.observe app owner) =
          law.bind (fun action => member action (middle.logs owner)
            (middle.observe app owner)) := by
    intro left current currentTrace valid _ command selected middle moved active firstNow
    have commandEq : command = .activate owner := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have sameApplication := activation_application (setup := setup) leaks current middle owner moved
    have middleReady : middle.application.config.cut.Ready event :=
      (middle.application.publicView_eventReady event).mp
        (middle.application.publicView.ownTurn?_spec owner event
          (sourceServiceTurn_first firstNow).1).1
    have currentReady : current.application.config.cut.Ready event := by
      rwa [sameApplication] at middleReady
    have currentActive : owner ∉ current.application.config.defaulted :=
      current.application.active_of_ready_owned
        (legalFacts setup leaks horizon scheduler _ currentTrace).quiescent currentReady owned
    have middlePath : Relation.ReflTransGen Config.Step execution.application.config
        middle.application.config := by
      rw [sameApplication]
      exact valid.2
    have ownRecords : ∀ prior : (serviceGraph setup deps).EventId, prior.val < event.val →
        (serviceGraph setup deps).actor? prior = some owner →
        completionOf middle.application.config prior = completionOf ghost prior := by
      intro prior earlier actor
      by_cases old : prior.val < start
      · have completed : prior ∈ execution.application.config.cut.completed :=
          (ordered.2 prior).mpr old
        obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
          ((completionOf_isSome_iff execution.application.config prior).mpr completed)
        rw [Config.Step.path_completionOf_of_some middlePath prior record found,
          Config.Step.path_completionOf_of_some ghostPath prior record found]
      · have lower : start ≤ prior.val := Nat.le_of_not_gt old
        obtain ⟨payload, binding, result, fixed, recorded⟩ := frozen prior lower earlier actor
        have priorCompleted : prior ∈ current.application.config.cut.completed :=
          (relaxed.ready_visible_iff current.application.config.cut currentReady owned
            (EventCode.output_visible_of_actor ((serviceGraph setup deps).nodes prior) owner actor)
            (IndependentReveals.not_of_not_publication_right notPublication)
            (IndependentReveals.not_of_not_publication_left notPublication)).mpr earlier
        have pending : prior ∉ execution.application.config.cut.completed := by
          intro completed
          exact old ((ordered.2 prior).mp completed)
        obtain ⟨used, reached⟩ := valid.1
        have records := fixed_reference_binding_record_runRounds leaks scheduler bound turns
          reference
          owner prior actor payload binding result fixed background follows execution trace truthful
          (untouched prior lower earlier.le actor) pending used current reached priorCompleted
        have actualRecord := (records.resolve_left currentActive).1
        rw [sameApplication]
        exact actualRecord.trans recorded.symm
    obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialDistribution setup deps)
      horizon
      scheduler left current middle (.activate owner) currentTrace selected moved
    have callback := serviceReference_callback_of_binding_paths relaxed profile
      execution.application.config ghost start initialReach ordered middle middlePath ghostPath
      owner event owned notPublication middleReady ghostReady ghostActive bindings ownRecords
      middleTrace
    change turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner (middle.logs owner)
        (middle.observe app owner) = _
    rw [sourceServiceTurnPolicy_firstTurn_reference owned firstNow]
    simp only [member, first, firstNow, ite_true]
    unfold EventGraphRuntime.referenceOpportunity fixedOpportunity
    by_cases recorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
        (middle.logs owner) event = true
    · simp only [recorded, ite_true, PMF.bind_const]
    · have notRecorded := Bool.eq_false_of_not_eq_true recorded
      simp only [notRecorded, Bool.false_eq_true, ite_false]
      by_cases fits : (middle.observe app owner).application.publicView.InclusionFitsDeadline
          (serviceTimeouts setup deps duration) bound event
      · simp only [fits, ite_true]
        have compiled := congrArg (fun responseLaw : PMF app.Action => responseLaw.bind
          (fun response => if response.transmission = none then
            app.silentPolicy (middle.logs owner) (middle.observe app owner)
          else PMF.pure response)) callback
        exact compiled.trans (by rw [PMF.bind_map]; rfl)
      · simp only [fits, ite_false, PMF.bind_const]
  have preserved : ∀ left current,
      (app.protocol (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨left + 1, none, current⟩) →
      invariant current → ¬ stop current →
      ∀ next ∈ (app.round scheduler (Function.update background owner (players owner))
        current).support, invariant next := by
    intro left current _ valid _ next reached
    rw [restored] at reached
    refine ⟨?_, valid.2.trans
      (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks
      scheduler background current next reached)⟩
    obtain ⟨used, before⟩ := valid.1
    refine ⟨used + 1, ?_⟩
    rw [app.runRounds_add scheduler background used 1, PMF.mem_support_bind_iff]
    exact ⟨current, before, by
      simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using reached⟩
  have startBefore : start ≤ event.val := by
    by_contra earlier
    have completed : event ∈ execution.application.config.cut.completed :=
      (ordered.2 event).mpr (by omega)
    exact ghostReady.1 (Config.Step.path_completed_mono ghostPath completed)
  have clean : ∀ before entry, before ++ [entry] <+: execution.logs owner →
      ¬ first before entry.beforeView := by
    intro before entry prefixed earlier
    have memberEntry : entry ∈ execution.logs owner := prefixed.subset (by simp)
    exact untouched event startBefore le_rfl owned owner entry memberEntry
      (PublicView.ownTurn?_spec _ owner event (sourceServiceTurn_first earlier).1).1
  have initial : invariant execution := by
    refine ⟨⟨0, ?_⟩, .refl⟩
    simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff]
  have mixed := app.runUntil_mixture_at_first
    (serviceInitialDistribution setup deps) horizon scheduler background owner
      (players owner) law member
    first once (by intro action past view away; simp only [member, away, ite_false])
    stop invariant atFirst preserved count remaining execution trace initial clean
  simpa only [restored] using mixed

end Vegas

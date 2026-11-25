module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphSourceResidual
public import Vegas.Compile.EventGraphSourceStep
public import Vegas.Compile.EventGraphDistribution

@[expose] public section

/-! # Successful openings of effective source disclosure policies -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}

private theorem SourceResidual.supported_opening_succeeds {rank : Nat}
    {config : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank config)
    (event : setup.informationGraph.EventId) (atRank : event.val = rank)
    {owner : Player} (effective : residual.EffectiveDisclosures owner) {payload : L.Ty}
    {binding : FieldRef setup.informationGraph.layout (.binding owner payload)}
    {checks : List (GuardCheck setup.informationGraph.layout payload)}
    {outputEq : setup.informationGraph.outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) = .resolve owner payload binding checks)
    (action : setup.informationGraph.Action event)
    (chosen : action ∈ (actionDistribution (compileEventProfile setup.program profile)
      config event).support)
    (disclose : (cast (congrArg EventField.Action outputEq) action : Bool) = true) :
    ∃ value, EventCode.resolveOutput? binding checks true config.store =
      some (.success value) := by
  rcases residual with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, _, _, _, _, _, _, _, _, _, checkpoint⟩
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = setup.informationGraph.order.eventCount at counted
  cases program with
  | ret payoffs =>
      have := event.isLt
      simp only [eventCount] at counted
      omega
  | @sample Γ openNames name sampleType fresh distribution next =>
      let head : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event head).val = rank := by
        simpa only [head, Nat.add_zero] using aligned.graphSuffix.rankEq head
      have same : event = embedding.event head := Fin.ext (atRank.trans headRank.symm)
      subst event
      have typed : setup.informationGraph.outputLayout (embedding.event head) =
          .publicData sampleType := by
        change outputLayout setup.program (embedding.event head) = _
        simpa [head, outputLayout, eventCount] using embedding.layout_eq head
      have impossible := outputEq.symm.trans typed
      cases impossible
  | @commit Γ openNames name bindingOwner bindingType fresh guard next =>
      let head : Fin (eventCount (.commit name bindingOwner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event head).val = rank := by
        simpa only [head, Nat.add_zero] using aligned.graphSuffix.rankEq head
      have same : event = embedding.event head := Fin.ext (atRank.trans headRank.symm)
      subst event
      have typed : setup.informationGraph.outputLayout (embedding.event head) =
          .binding bindingOwner bindingType := by
        change outputLayout setup.program (embedding.event head) = _
        simpa [head, outputLayout, eventCount] using embedding.layout_eq head
      have impossible := outputEq.symm.trans typed
      cases impossible
  | @reveal Γ openNames published author name openedType fresh selected unresolved next =>
      let head : Fin (eventCount
          (.reveal published author name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event head).val = rank := by
        simpa only [head, Nat.add_zero] using aligned.graphSuffix.rankEq head
      have same : event = embedding.event head := Fin.ext (atRank.trans headRank.symm)
      subst event
      have typed : setup.informationGraph.outputLayout (embedding.event head) =
          .publication openedType := by
        change outputLayout setup.program (embedding.event head) = _
        simpa [head, outputLayout, eventCount] using embedding.layout_eq head
      have payloadEq : payload = openedType :=
        EventField.publication.inj (outputEq.symm.trans typed)
      subst payload
      let guards := compileChecks (published := published) refs
        source.registry source.revelations selected
      have actualCode : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
          (setup.informationGraph.nodes (embedding.event head)) =
            .resolve author openedType (refs.get selected) guards := by
        change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
          ((toInformationGraph setup.program).nodes (embedding.event head)) = _
        simpa [head, compileRankedNodes, guards] using aligned.graphSuffix.nodeEq head
      obtain ⟨ownerEq, bindingEq, checksEq⟩ := EventCode.resolve.inj
        (codeEq.symm.trans actualCode)
      subst owner
      have refEq := eq_of_heq bindingEq
      subst binding
      subst checks
      have actor : setup.informationGraph.actor? (embedding.event head) = some author := by
        change (toInformationGraph setup.program).actor? (embedding.event head) = _
        simpa [head, eventOwner?, eventCount] using aligned.actorEq head
      have status : config.defaulted = source.defaulted :=
        congrArg DefaultHistory.defaulted checkpoint.defaults
      by_cases inactive : author ∈ source.defaulted
      · have stopped : author ∈ config.defaulted := status.symm ▸ inactive
        rw [actionDistribution_of_actor _ _ actor, dite_eq_left stopped, PMF.mem_support_pure_iff]
          at chosen
        have mechanical := EventCode.failureAction_eq_cast outputEq _ _ actualCode
          author actor rfl
        rw [chosen, mechanical, cast_cast, cast_eq] at disclose
        cases disclose
      · have active : author ∉ config.defaulted := status.symm ▸ inactive
        have law : actionDistribution (compileEventProfile setup.program profile) config
            (embedding.event head) =
            (revealKernel residualProfile (source.view author) inactive).map
              (fun flag => cast (congrArg EventField.Action outputEq.symm) flag) := by
          rw [actionDistribution_of_actor _ _ actor, dite_eq_right active]
          exact eq_map_cast_of_cast_eq (congrArg EventField.Action outputEq) _ _
            (reveal_head_policy_eq setup.program profile selected unresolved next residualProfile
              refs source.revelations source.registry embedding refsBefore rank aligned config
              source.state checkpoint.agrees source.history checkpoint.history source.defaults
              checkpoint.defaults inactive actor)
        rw [law] at chosen
        obtain ⟨flag, supported, rfl⟩ := PMF.support_map .. ▸ chosen
        simp only [cast_cast, cast_eq] at disclose
        subst flag
        have safe := effective.1 rfl (source.view author) inactive true supported
        rw [effectiveDisclosureView_observe] at safe
        have compiled := compiled_disclosure_result (graph := setup.informationGraph)
          published selected source refs config.store checkpoint.agrees true
        rw [ite_eq_right inactive, EventCode.resolveOutput?_playerStore] at compiled
        cases result : disclosureResult published selected source true with
        | failure =>
            simp [effectiveDisclosure, result] at safe
        | success value =>
            exact ⟨value, by simpa only [result, guards] using compiled⟩

/-- Every supported true resolution action of a player whose source policy has
effective disclosures publishes successfully. This holds at every reachable ready graph
configuration, including configurations reached by arbitrary other actions. -/
theorem compileEventProfile_supported_opening_succeeds
    (inputs : setup.informationGraph.Inputs)
    (present : inputs ∈ (setup.initialDistribution.map setup.eventInputs).support)
    (config : setup.informationGraph.Config) (reachable : config.Reachable inputs)
    (event : setup.informationGraph.EventId) (ready : config.cut.Ready event)
    {owner : Player}
    (effective : (profile owner).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    {payload : L.Ty}
    {binding : FieldRef setup.informationGraph.layout (.binding owner payload)}
    {checks : List (GuardCheck setup.informationGraph.layout payload)}
    {outputEq : setup.informationGraph.outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) = .resolve owner payload binding checks)
    (action : setup.informationGraph.Action event)
    (chosen : action ∈ (actionDistribution (compileEventProfile setup.program profile)
      config event).support)
    (disclose : (cast (congrArg EventField.Action outputEq) action : Bool) = true) :
    ∃ value, EventCode.resolveOutput? binding checks true config.store =
      some (.success value) := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ present
  have existsResidual : ∃ rank, ∃ residual : SourceResidual setup profile rank config,
      residual.EffectiveDisclosures owner := by
    clear ready chosen
    induction reachable with
    | initial => exact ⟨0, SourceResidual.initial setup profile initial, effective⟩
    | step _ previousEvent previousReady previousAction after moved ih =>
        obtain ⟨rank, before, beforeEffective⟩ := ih
        obtain ⟨next, nextEffective⟩ :=
          before.step_effective beforeEffective previousEvent previousReady previousAction
            after moved
        exact ⟨rank + 1, next, nextEffective⟩
  obtain ⟨rank, residual, residualEffective⟩ := existsResidual
  have ordered : config.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun _ => config.cut.mem_completed_iff_lt_of_ready ready⟩
  exact residual.supported_opening_succeeds event
    (ordered.unique residual.checkpoint.ordered) residualEffective (outputEq := outputEq)
    codeEq action chosen disclose

end Vegas

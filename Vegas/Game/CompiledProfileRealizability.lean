module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphLaw
public import Vegas.Game.SourceServiceReachedDecoding
public import Vegas.Pending.EffectiveAction
public import Vegas.Source.DisclosureBehavioral

@[expose] public section

/-! # Realizability of compiled graph profiles

On every reachable graph configuration, a compiled authentic disclosure can open its binding.
This certificate uses graph reachability and the residual source program at that configuration.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}

/-- Authentic source disclosures compile to effective graph actions at a reached prefix. -/
private theorem SourceResidual.actionLaw_effective {rank : Nat}
    {config : setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank config) (event : setup.informationGraph.EventId)
    (atRank : event.val = rank)
    (authenticWhole : ∀ who, (profile who).AuthenticDisclosures setup.program)
    (action : setup.informationGraph.Action event)
    (member : action ∈ (EventGraph.actionLaw (compileEventProfile setup.program profile)
      config event).support) : EffectiveAction config event action := by
  rcases residual with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, _, authentic, _, _, _, _, _, _, _, checkpoint⟩
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = setup.informationGraph.order.eventCount at counted
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
      have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode setup.informationGraph.layout) outputEq)
          (setup.informationGraph.nodes (embedding.event index)) =
            .sample payload (compilePublicDist refs distribution) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toInformationGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
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
      have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode setup.informationGraph.layout) outputEq)
          (setup.informationGraph.nodes (embedding.event index)) = .bind owner payload := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toInformationGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
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
      have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
          .publication payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      let checks := compileChecks (published := published) refs
        source.registry source.revelations selected
      have codeEq : cast (congrArg (EventGraph.EventCode setup.informationGraph.layout) outputEq)
          (setup.informationGraph.nodes (embedding.event index)) =
            .resolve owner payload (refs.get selected) checks := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toInformationGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes, checks] using aligned.graphSuffix.nodeEq index
      have actor : setup.informationGraph.actor? (embedding.event index) = some owner := by
        change (toInformationGraph setup.program).actor? (embedding.event index) = some owner
        simpa [index, eventOwner?, eventCount] using aligned.actorEq index
      let choiceLaw : PMF Bool := if inactive : owner ∈ source.defaulted then PMF.pure false
        else revealKernel residualProfile (source.view owner) inactive
      have status : config.defaulted = source.defaulted :=
        congrArg DefaultHistory.defaulted checkpoint.defaults
      have lawEq : EventGraph.actionLaw (compileEventProfile setup.program profile) config
          (embedding.event index) = choiceLaw.map (fun disclose =>
            cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) := by
        rw [EventGraph.actionLaw_of_actor _ config actor]
        by_cases inactive : owner ∈ source.defaulted
        · have stopped : owner ∈ config.defaulted := status.symm ▸ inactive
          simp only [choiceLaw, dite_eq_left inactive, dite_eq_left stopped, PMF.pure_map]
          exact congrArg PMF.pure (EventGraph.EventCode.failureAction_eq_cast outputEq
            _ _ codeEq owner actor rfl)
        · have active : owner ∉ config.defaulted := status.symm ▸ inactive
          simp only [choiceLaw, dite_eq_right inactive, dite_eq_right active]
          exact eq_map_cast_of_cast_eq (congrArg EventGraph.EventField.Action outputEq) _ _
            (reveal_head_policy_eq setup.program profile selected unresolved next residualProfile
              refs source.revelations source.registry embedding refsBefore rank aligned config
              source.state checkpoint.agrees source.history checkpoint.history source.defaults
              checkpoint.defaults inactive actor)
      rw [lawEq] at member
      unfold EffectiveAction
      rw [EventGraphRuntime.nodeView_eq_resolve outputEq codeEq]
      obtain ⟨disclose, chosen, rfl⟩ := PMF.support_map .. ▸ member
      intro requested
      simp only [cast_cast, cast_eq] at requested
      subst requested
      by_cases inactive : owner ∈ source.defaulted
      · simp only [choiceLaw, dite_eq_left inactive, PMF.mem_support_pure_iff] at chosen
        cases chosen
      · have selectedChoice : true ∈
            (revealKernel residualProfile (source.view owner) inactive).support := by
          simpa only [choiceLaw, dite_eq_right inactive] using chosen
        have kept := (authentic authenticWhole owner).1 rfl (source.view owner) inactive true
          selectedChoice
        have opens : (source.state.get selected).isSuccess = true := by
          simpa [Config.view, sourceObserve, Env.get] using kept
        cases result : source.state.get selected with
        | failure => simp only [result, PublicationResult.isSuccess] at opens; cases opens
        | success value =>
            exact ⟨value, by simpa only [result, cellValue] using checkpoint.agrees selected⟩

/-- Compiling a profile with authentic disclosures supplies the graph-level realizability
certificate on every configuration reachable from the compiled input law. -/
theorem compileEventProfile_realizable
    (authentic : ∀ who, (profile who).AuthenticDisclosures setup.program) :
    RealizableProfile (graph := setup.informationGraph) (setup.initialLaw.map setup.eventInputs)
      (compileEventProfile setup.program profile) := by
  intro inputs supported config reachable
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  have hasResidual : ∃ rank, Nonempty (SourceResidual setup profile rank config) := by
    induction reachable with
    | initial => exact ⟨0, ⟨SourceResidual.initial setup profile initial⟩⟩
    | step _ previousEvent previousReady previousAction after moved ih =>
        obtain ⟨rank, ⟨before⟩⟩ := ih
        obtain ⟨after, _⟩ := before.step previousEvent previousReady previousAction after moved
        exact ⟨rank + 1, ⟨after⟩⟩
  obtain ⟨rank, ⟨residual⟩⟩ := hasResidual
  intro event ready action chosen
  have ordered : config.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun _ => setup.informationGraph.sequentialize_mem_completed_iff_lt_of_ready
      _ ready⟩
  exact residual.actionLaw_effective event (ordered.unique residual.checkpoint.ordered)
    authentic action chosen

end Vegas

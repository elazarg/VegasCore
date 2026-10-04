/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompatibleBindingResponse
import Vegas.Game.AsyncServiceCounterfactualBeliefs
import Vegas.Game.SourceServiceFirstInputAncestor
import Vegas.Game.SourceServiceInitialReadout
import Vegas.Game.SourceServiceResidualSites

/-! # Binding response draws under actual native conditional histories

At a compatible binding input, every actual hidden history supplies its own
aligned residual compiler and the same recalled owner input. The native pin's
uniform, waiting and canonical branches retain the actual initial parameter,
decoded effective prefix and full post-response traffic jointly. Their hidden
history weights are the actual counterfactual reaches. In particular, foreign
waiting and free excursions remain in those weights; no source posterior is
substituted for them.

This is a current-response law. It does not identify a subsequent free native
continuation with the recorded-owner silent stopping kernel. Original failed
disclosure memories are not identified with physical recall.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.menu (runtime) service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (Vegas.runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler

private theorem binding_response_of_trace
    (profile : BehavioralProfile service.setup.program) (who : Player) (payload : L.Ty)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (event : (graph service.setup).EventId)
    (binding : (graph service.setup).outputLayout event = .binding who payload)
    (execution : (app).Execution) (remaining : Nat)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks (execution.recall who) event = false)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ player info, 0 ≤ weight player info)
    (small : ∀ player info, weight player info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ player, (model).BehavioralPolicy player) :
    let info := some (execution.recall who, execution.observe (app) who)
    let read := fun choice : (model).Choice who info =>
      let response := choice.1.getD (⟨none⟩ : (app).Action)
      (bindingResponseResult? who payload execution response, execution.respond (app) who response)
    ((service.completedInformationWaitProfile profile weight nonnegative small delta
      deltaNonnegative deltaSmall continuation who info).map read) =
      mix delta deltaNonnegative deltaSmall
        (((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
          who info).map read)
        (mix (weight who info) (nonnegative who info) (small who info)
          (PMF.pure (none, execution.respond (app) who ⟨none⟩))
          (((compileEventProfile service.setup.program profile) who event
            (PublicView.ownTurn?_spec _ who event turn).2
            (service.setup.eventGraph.fromModeObservation .sequential who
              ((graph service.setup).playerObserve who execution.application.config))).map
                fun action =>
                  let value := cast (congrArg EventGraph.EventField.Action binding) action
                  (some value, execution.respond (app) who
                    ((runtime).reactiveBinding service.leaks who event payload value
                      (execution.application.publicView.bindingCount who))))) := by
  intro info read
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  obtain ⟨residual⟩ := menu_ready_sourceResidual service.setup service.leaks profile (menu)
    service.horizon service.scheduler trace ⟨remaining, some who, execution⟩ rfl event ready
  obtain ⟨site⟩ := residual.bindingSource binding
  change BindingSource service.setup profile event execution.application.config at site
  obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (site.outputEq.symm.trans binding)
  have localLaw := service.completedInformationWaitProfile_binding_joint_response profile event
    execution site permitted remaining trace compatible turn unrecorded weight nonnegative small
    delta deltaNonnegative deltaSmall continuation
  dsimp only at localLaw
  rw [localLaw]
  congr 2
  rw [BindingSource.compiled_choice execution site, PMF.map_comp]
  apply map_congr_on_support
  intro value _supported
  simp only [Function.comp_def, cast_cast, cast_eq]

/-- The actual conditional current-response carrier, including the same
initial parameter, decoded effective prefix and complete traffic. Counterfactual
weights retain every foreign wait and full-menu excursion in the incoming law. -/
def BindingConditionalResponseLaw
    {Parameter : Type} (parameter : State L service.setup.context → Parameter)
    (profile : BehavioralProfile service.setup.program) (who : Player) (payload : L.Ty)
    (event : (graph service.setup).EventId)
    (binding : (graph service.setup).outputLayout event = .binding who payload)
    (site : (model).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ player info, 0 ≤ weight player info)
    (small : ∀ player info, weight player info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (assessment : (model).BehavioralAssessment) : Prop :=
    ∃ execution : (model).InformationHistory who site.1 → (app).Execution,
      (∀ history, ∃ remaining initial source,
        history.1.state = some ⟨remaining, some who, execution history⟩ ∧
        (execution history).recall who = past ∧ (execution history).observe (app) who = view ∧
        initial ∈ service.setup.initialLaw.support ∧
        sourceInitialReadout service.setup (execution history).application.config = some initial ∧
        sourceServicePrefix? service.setup event.val (execution history).application.config =
          some source) ∧
      let belief := assessment.belief who site
      let carry := fun history : (model).InformationHistory who site.1 =>
        ((sourceInitialReadout service.setup (execution history).application.config).map parameter,
          sourceServicePrefix? service.setup event.val (execution history).application.config)
      let read := fun history (choice : (model).Choice who site.1) =>
        let response := choice.1.getD (⟨none⟩ : (app).Action)
        (carry history, (bindingResponseResult? who payload (execution history) response,
          (runtime).bindingTraffic service.leaks who
            ((execution history).respond (app) who response)))
      let uniform := fun history =>
        ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
          who site.1).map (read history)
      let wait := fun history => (carry history, (none,
        (runtime).bindingTraffic service.leaks who
          ((execution history).respond (app) who ⟨none⟩)))
      let draw := fun history =>
        ((compileEventProfile service.setup.program profile) who event
          (binding_actor service.setup event who payload binding)
          (service.setup.eventGraph.fromModeObservation .sequential who
            ((graph service.setup).playerObserve who (execution history).application.config))).map
              fun action =>
                let value := cast (congrArg EventGraph.EventField.Action binding) action
                (carry history, (some value, (runtime).bindingTraffic service.leaks who
                  ((execution history).respond (app) who
                    ((runtime).reactiveBinding service.leaks who event payload value
                      ((execution history).application.publicView.bindingCount who)))))
      let actual := belief.bind fun history => (assessment.strategy who site.1).map (read history)
      actual = mix delta deltaNonnegative deltaSmall (belief.bind uniform)
        (mix (weight who site.1) (nonnegative who site.1) (small who site.1)
          (belief.map wait) (belief.bind draw)) ∧
      ∀ result, (actual result).toReal =
        ∑ history : (model).InformationHistory who site.1,
          ((model).counterfactualReachProbability assessment.strategy who history.1.trace /
            service.counterfactualInformationMass (menu) assessment.strategy who site Set.univ) *
          (delta * (uniform history result).toReal + (1 - delta) *
            (weight who site.1 * ((PMF.pure (wait history)) result).toReal +
              (1 - weight who site.1) * (draw history result).toReal))

open Classical in
/-- The actual current binding law conditioned on a native information fiber.
The supplied pin equality is the exact prescribed-site field returned by native
completion, not a source-belief or continuation hypothesis. All source-reading
resources below are derived from the actual full-menu histories. -/
theorem information_wait_binding_bayes_joint_response
    {Parameter : Type} (parameter : State L service.setup.context → Parameter)
    (profile : BehavioralProfile service.setup.program) (who : Player) (payload : L.Ty)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (event : (graph service.setup).EventId)
    (binding : (graph service.setup).outputLayout event = .binding who payload)
    (site : (model).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (compatible : service.sourceCompatibleInfo who site.1)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks past event = false)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ player info, 0 ≤ weight player info)
    (small : ∀ player info, weight player info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (assessment : (model).BehavioralAssessment)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (model) assessment
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler))
    (pinned : assessment.strategy who site.1 = service.completedInformationWaitProfile profile
      weight nonnegative small delta deltaNonnegative deltaSmall assessment.strategy who site.1)
    (positive : 0 < (model).informationMass assessment.strategy who site) :
    service.BindingConditionalResponseLaw parameter profile who payload event binding site past view
      weight nonnegative small delta deltaNonnegative deltaSmall assessment := by
  rcases site with ⟨info, decision⟩
  dsimp only at observed
  subst info
  let site : (model).InformationSite who := ⟨some (past, view), decision⟩
  have observed : site.1 = some (past, view) := rfl
  unfold BindingConditionalResponseLaw
  let origin := fun history : (model).InformationHistory who site.1 =>
    sourceServiceInformation_owned_prefix service.setup service.leaks (menu)
      (initialLaw service.setup) service.horizon service.scheduler who event past view turn
      ⟨history.1, history.2.trans observed⟩
  let remaining := fun history => Classical.choose (origin history)
  let execution := fun history => Classical.choose (Classical.choose_spec (origin history))
  have actual history := Classical.choose_spec (Classical.choose_spec (origin history))
  have recalled history : (execution history).recall who = past := (actual history).2.1
  have viewed history : (execution history).observe (app) who = view := (actual history).2.2.1
  have trace history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace (some ⟨remaining history, some who, execution history⟩) :=
    (actual history).1 ▸ history.1.trace
  have turnAt history : (execution history).application.publicView.ownTurn? who = some event := by
    change ((execution history).observe (app) who).application.publicView.ownTurn? who = _
    rw [(actual history).2.2.1]
    exact turn
  have inputAt history : some ((execution history).recall who,
      (execution history).observe (app) who) = site.1 := by
    rw [(actual history).2.1, (actual history).2.2.1, observed]
  refine ⟨execution, ?_, ?_⟩
  · intro history
    have rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon
      service.scheduler (trace history)
    obtain ⟨initial, supported, initialized⟩ := sourceInitialReadout_history service.setup
      service.leaks service.horizon service.scheduler
        ⟨remaining history, some who, execution history⟩ rawTrace
    have ready := ((execution history).application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event (turnAt history)).1
    obtain ⟨residual⟩ := menu_ready_sourceResidual service.setup service.leaks profile (menu)
      service.horizon service.scheduler (trace history)
        ⟨remaining history, some who, execution history⟩ rfl event ready
    exact ⟨remaining history, initial,
      residual.lift (ProtocolState.entry residual.program residual.source),
      (actual history).1, (actual history).2.1, (actual history).2.2.1,
      supported, initialized, residual.decode⟩
  · intro belief carry read uniform wait draw actualLaw
    have conditional history :
        (assessment.strategy who site.1).map (read history) =
          mix delta deltaNonnegative deltaSmall (uniform history)
            (mix (weight who site.1) (nonnegative who site.1) (small who site.1)
              (PMF.pure (wait history)) (draw history)) := by
      have rawLaw := service.binding_response_of_trace profile who payload permitted event
        binding (execution history) (remaining history) (trace history)
        ((inputAt history).symm ▸ compatible) (turnAt history)
        (by rw [(actual history).2.1]; exact unrecorded) weight nonnegative small delta
        deltaNonnegative deltaSmall assessment.strategy
      dsimp only at rawLaw
      have mapped := congrArg (PMF.map (fun pair =>
        (carry history, (pair.1, (runtime).bindingTraffic service.leaks who pair.2)))) rawLaw
      simp only [mix_map, PMF.map_comp, PMF.pure_map, Function.comp_def] at mapped
      let physicalRead := fun response : (app).Action =>
        (carry history, (bindingResponseResult? who payload (execution history) response,
          (runtime).bindingTraffic service.leaks who
            ((execution history).respond (app) who response)))
      have pinInput := congrArg (fun info =>
        (service.completedInformationWaitProfile profile weight nonnegative small delta
          deltaNonnegative deltaSmall assessment.strategy who info).map
            (fun choice => physicalRead (choice.1.getD (⟨none⟩ : (app).Action))))
              (inputAt history)
      have uniformInput := congrArg (fun info =>
        ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
          who info).map
            (fun choice => physicalRead (choice.1.getD (⟨none⟩ : (app).Action))))
              (inputAt history)
      rw [pinInput, uniformInput, inputAt history] at mapped
      rw [pinned]
      exact mapped
    have localAtom result : (actualLaw result).toReal =
        ∑ history : (model).InformationHistory who site.1,
          (belief history).toReal *
            (delta * (uniform history result).toReal + (1 - delta) *
              (weight who site.1 * ((PMF.pure (wait history)) result).toReal +
                (1 - weight who site.1) * (draw history result).toReal)) := by
      rw [toReal_bind_apply, expect_eq_sum]
      apply Finset.sum_congr rfl
      intro history _
      rw [conditional history, mix_apply_toReal, mix_apply_toReal]
    constructor
    · apply pmf_ext_toReal
      intro result
      have actualExpectation : (actualLaw result).toReal = expect belief fun history =>
          delta * (uniform history result).toReal + (1 - delta) *
            (weight who site.1 * ((PMF.pure (wait history)) result).toReal +
              (1 - weight who site.1) * (draw history result).toReal) := by
        rw [expect_eq_sum]
        exact localAtom result
      rw [actualExpectation, mix_apply_toReal, mix_apply_toReal,
        toReal_bind_apply, toReal_bind_apply]
      have waitAtom : ((belief.map wait) result).toReal =
          expect belief fun history => ((PMF.pure (wait history)) result).toReal := by
        rw [← PMF.bind_pure_comp, toReal_bind_apply]
        rfl
      rw [waitAtom]
      rw [expect_add (payoffIntegrable_of_finite belief _)
        (payoffIntegrable_of_finite belief _), expect_const_mul, expect_const_mul,
        expect_add (payoffIntegrable_of_finite belief _)
          (payoffIntegrable_of_finite belief _), expect_const_mul, expect_const_mul]
    · intro result
      rw [localAtom]
      apply Finset.sum_congr rfl
      intro history _
      have equal := (InformationModel.BehavioralAssessment.isBayesConsistentAt_iff (model)
        assessment who site ((menu).decisionInformationAntichain (initialLaw service.setup)
          service.horizon service.scheduler who site) positive).mp (bayes who site positive)
      change (assessment.belief who site history).toReal * _ = _
      rw [equal, service.bayesBelief_apply_counterfactual (menu) assessment.strategy who site
        positive history]

end Vegas.AsyncServiceSpec

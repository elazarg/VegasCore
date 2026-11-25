module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PublicationDecision

@[expose] public section

/-! # Replacing binding omissions under fixed exit utility

An omitted binding immediately defaults its owner. Replacing the omission by
an accepted unopenable binding therefore weakly raises a payoff bounded below
by its absorbing exit value, independently of later play. The transformation
fixes every submitted binding action and every nonbinding action.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

namespace EventField

omit [DecidableEq Player] in
/-- Submit an accepted unopenable binding in place of an omission. -/
def submitAction : (field : EventField Player L) → field.Action → field.Action
  | .binding _ _, action => some (action.getD .failure)
  | .publicData _, action | .publication _, action | .privateInput _ _, action => action

omit [DecidableEq Player] in
/-- Binding actions submit a value; other field kinds impose no condition. -/
def Submitted : (field : EventField Player L) → field.Action → Prop
  | .binding _ _, action => action.isSome
  | .publicData _, _ | .publication _, _ | .privateInput _ _, _ => True

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem submitted_submitAction (field : EventField Player L) (action : field.Action) :
    field.Submitted (field.submitAction action) := by
  cases field <;> simp [Submitted, submitAction]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem submitAction_eq_self (field : EventField Player L) (action : field.Action)
    (submitted : field.Submitted action) : field.submitAction action = action := by
  cases field with
  | binding owner payload =>
    cases action <;> simp_all [Submitted, submitAction]
  | publicData | privateInput | publication => rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem submitAction_idem (field : EventField Player L) (action : field.Action) :
    field.submitAction (field.submitAction action) = field.submitAction action :=
  submitAction_eq_self field _ (submitted_submitAction field action)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem submitted_of_publication (field : EventField Player L) (publication : field.IsPublication)
    (action : field.Action) : field.Submitted action := by
  cases field <;> simp_all [IsPublication, Submitted]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem submitted_cast {left right : EventField Player L} (same : left = right)
    (action : left.Action) (submitted : left.Submitted action) :
    right.Submitted (cast (congrArg Action same) action) := by
  cases same
  exact submitted

end EventField

namespace EventCode

variable {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}

omit [DecidableEq Player] in
theorem causesDefault_of_submitAction_ne {output : EventField Player L}
    (code : EventCode layout output) (action : output.Action) (value : output.Value)
    (changed : output.submitAction action ≠ action) : code.causesDefault action value := by
  cases code with
  | bind owner payload =>
    cases action with
    | none => rfl
    | some value => exact (changed rfl).elim
  | resolve | sample => exact (changed rfl).elim

end EventCode

variable (graph : Vegas.EventGraph Player L)

/-- Submit at each binding, leaving all other local choices unchanged. -/
def submitPolicy (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.BehavioralPolicy who :=
  fun event actor observation active =>
    (policy event actor observation active).map (EventField.submitAction (graph.outputLayout event))

/-- Apply binding submission independently to every player. -/
def submitProfile (profile : graph.BehavioralProfile) : graph.BehavioralProfile :=
  fun who => graph.submitPolicy who (profile who)

/-- Every supported choice of a policy submits at bindings. -/
def PolicySubmitsBindings (who : Player) (policy : graph.BehavioralPolicy who) : Prop :=
  ∀ event actor observation active action,
    action ∈ (policy event actor observation active).support →
      (graph.outputLayout event).Submitted action

/-- Every player submits at every active binding. -/
def SubmitsBindings (profile : graph.BehavioralProfile) : Prop :=
  ∀ who, graph.PolicySubmitsBindings who (profile who)

theorem policySubmitsBindings_submitPolicy (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.PolicySubmitsBindings who (graph.submitPolicy who policy) := by
  intro event actor observation active action supported
  obtain ⟨original, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact EventField.submitted_submitAction _ original

theorem submitsBindings_submitProfile (profile : graph.BehavioralProfile) :
    graph.SubmitsBindings (graph.submitProfile profile) :=
  fun who => graph.policySubmitsBindings_submitPolicy who (profile who)

theorem SubmitsBindings.update {profile : graph.BehavioralProfile}
    (submits : graph.SubmitsBindings profile) (who : Player) (policy : graph.BehavioralPolicy who)
    (policySubmits : graph.PolicySubmitsBindings who policy) :
    graph.SubmitsBindings (Profile.update (sig := graph.gameSignature) profile who policy) := by
  intro owner
  by_cases same : owner = who
  · subst owner
    simpa only [Profile.update_same] using policySubmits
  · simpa only [Profile.update_of_ne _ _ same] using submits owner

theorem submitProfile_update (profile : graph.BehavioralProfile) (who : Player)
    (policy : graph.BehavioralPolicy who) :
    graph.submitProfile (Profile.update (sig := graph.gameSignature) profile who policy) =
      Profile.update (sig := graph.gameSignature) (graph.submitProfile profile) who
        (graph.submitPolicy who policy) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [submitProfile, Profile.update_same]
  · simp only [submitProfile, Profile.update_of_ne _ _ same]

theorem submitPolicy_eq_self (who : Player) (policy : graph.BehavioralPolicy who)
    (submits : graph.PolicySubmitsBindings who policy) :
    graph.submitPolicy who policy = policy := by
  funext event actor observation active
  change (policy event actor observation active).map _ = _
  calc
    _ = (policy event actor observation active).map id := by
      apply map_congr_on_support
      intro action supported
      exact EventField.submitAction_eq_self _ _
        (submits event actor observation active action supported)
    _ = _ := PMF.map_id _

theorem submitPolicy_idem (who : Player) (policy : graph.BehavioralPolicy who) :
    graph.submitPolicy who (graph.submitPolicy who policy) = graph.submitPolicy who policy :=
  graph.submitPolicy_eq_self who _ (graph.policySubmitsBindings_submitPolicy who policy)

theorem PolicySubmitsBindings.honestAtPublications {who : Player}
    {policy : graph.BehavioralPolicy who} (submits : graph.PolicySubmitsBindings who policy)
    (honest : graph.BehavioralPolicy who) :
    graph.PolicySubmitsBindings who (graph.honestAtPublications who policy honest) := by
  intro event actor observation active action supported
  by_cases publication : (graph.outputLayout event).IsPublication
  · exact EventField.submitted_of_publication _ publication action
  · exact submits event actor observation active action (by
      simpa only [Vegas.EventGraph.honestAtPublications, ite_eq_right publication] using supported)

variable {graph}

/-- Any action changed by binding submission immediately defaults its active
owner under the original action. -/
theorem Config.submitAction_ne_defaulted (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (who : Player) (actor : graph.actor? event = some who)
    (active : who ∉ config.defaulted) (action : graph.Action event)
    (changed : (graph.outputLayout event).submitAction action ≠ action)
    (next : graph.Config) (supported : next ∈ (config.step event ready action).support) :
    who ∈ next.defaulted := by
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨value, _, rfl⟩ := supported
  have causes := (graph.nodes event).causesDefault_of_submitAction_ne action value changed
  have decision := config.actualDecision_of_active event who actor active action
  have owned : (graph.nodes event).actor = some who := actor
  change who ∈ (config.complete event ready action value).defaults.defaulted
  rw [Config.complete_defaults, decision]
  change who ∈ (config.defaults.record ((graph.nodes event).defaultEvent action value)).defaulted
  rw [EventCode.defaultEvent, ite_eq_left causes, owned, DefaultHistory.defaulted_record_some]
  exact Finset.mem_insert_self _ _

/-- Replacing binding omissions weakly raises any payoff whose absorbing exit
value is a global lower bound, under every scheduler and every other policy. -/
private theorem submitPolicy_runValue_le_of_remaining (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (who : Player) (scheduler : graph.PublicScheduler)
    {payoff : graph.Config → ℝ} {excluded : ℝ} (low : ∀ config, excluded ≤ payoff config)
    (atDefault : ∀ config, who ∈ config.defaulted → payoff config = excluded) :
    ∀ fuel (config : graph.Config), config.remaining = fuel →
      runValue profile scheduler payoff config ≤
        runValue (Profile.update (sig := graph.gameSignature) profile who
          (graph.submitPolicy who (profile who))) scheduler payoff config := by
  let improved := Profile.update (sig := graph.gameSignature) profile who
    (graph.submitPolicy who (profile who))
  intro fuel
  induction fuel with
  | zero =>
    intro config remaining
    unfold runValue
    rw [remaining]
    simp only [EventGraph.runPlan, expect_pure, le_refl]
  | succ fuel ih =>
    intro config remaining
    by_cases defaulted : who ∈ config.defaulted
    · rw [runValue_of_defaulted profile scheduler atDefault config defaulted]
      exact le_runValue finite _ scheduler low config
    have notTerminal : ¬ config.cut.Terminal := fun terminal => by
      have := (config.terminal_iff_remaining_zero).mp terminal
      omega
    rw [runValue_step finite profile scheduler payoff config notTerminal,
      runValue_step finite improved scheduler payoff config notTerminal]
    apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    intro selected _
    let event := selected.1
    have ready : config.cut.Ready event := (EventOrder.Cut.mem_enabled _ _).mp selected.2
    have next (action : graph.Action event) (stepped : graph.Config)
        (member : stepped ∈ (config.step event ready action).support) :
        stepped.remaining = fuel := by
      have := config.remaining_step event ready action stepped member
      omega
    have stepIntegrable (action : graph.Action event) (value : graph.Config → ℝ) :
        PayoffIntegrable (config.step event ready action) value :=
      payoffIntegrable_of_finite_support _ _ (config.step_support_finite event ready action)
    have eventIntegrable (chosen : graph.BehavioralProfile) (value : graph.Config → ℝ) :
        PayoffIntegrable (eventStep chosen config event ready) value :=
      payoffIntegrable_of_finite_support _ _
        (eventStep_support_finite chosen (finite.profileFiniteSupport chosen) config event ready)
    by_cases owned : graph.actor? event = some who
    · have improvedLaw : actionDistribution improved config event =
          (actionDistribution profile config event).map
            (EventField.submitAction (graph.outputLayout event)) := by
        rw [actionDistribution_of_actor improved config owned, actionDistribution_of_actor profile
          config owned,
          dite_eq_right defaulted, dite_eq_right defaulted]
        simp only [improved, Profile.update_same, submitPolicy]
      have improvedStep : eventStep improved config event ready =
          (actionDistribution profile config event).bind fun action =>
            config.step event ready ((graph.outputLayout event).submitAction action) := by
        unfold eventStep
        rw [improvedLaw, PMF.bind_map]
        rfl
      have improvedIntegrable := eventIntegrable improved (runValue improved scheduler payoff)
      rw [improvedStep] at improvedIntegrable
      change expect ((actionDistribution profile config event).bind (config.step event ready)) _ ≤
        expect (eventStep improved config event ready) _
      rw [improvedStep, expect_bind_tower _ _ _ (eventIntegrable profile _),
        expect_bind_tower _ _ _ improvedIntegrable]
      apply expect_mono _ (payoffIntegrable_of_finite_support _ _
          (actionDistribution_support_finite finite profile config event))
        (payoffIntegrable_of_finite_support _ _
          (actionDistribution_support_finite finite profile config event))
      intro action _
      by_cases same : (graph.outputLayout event).submitAction action = action
      · rw [same]
        exact expect_mono (fun stepped member => ih stepped (next action stepped member))
          (stepIntegrable _ _) (stepIntegrable _ _)
      · rw [expect_congr_on_support (g := fun _ => excluded) fun stepped member =>
          runValue_of_defaulted profile scheduler atDefault stepped
            (config.submitAction_ne_defaulted event ready who owned defaulted action same
              stepped member), expect_constant]
        have bound := expect_mono
          (μ := config.step event ready ((graph.outputLayout event).submitAction action))
          (f := fun _ => excluded) (g := runValue improved scheduler payoff)
          (fun stepped _ => le_runValue finite improved scheduler low stepped)
          (payoffIntegrable_constant _ _) (stepIntegrable _ _)
        rwa [expect_constant] at bound
    · have sameLaw : actionDistribution improved config event =
        actionDistribution profile config event := by
        cases ownerEq : (graph.nodes event).actor with
        | none => rw [actionDistribution_of_ownerless _ _ ownerEq, actionDistribution_of_ownerless
          _ _ ownerEq]
        | some owner =>
          rw [actionDistribution_of_actor _ _ ownerEq, actionDistribution_of_actor _ _ ownerEq]
          by_cases inactive : owner ∈ config.defaulted
          · rw [dite_eq_left inactive, dite_eq_left inactive]
          rw [dite_eq_right inactive, dite_eq_right inactive]
          have different : owner ≠ who := fun same => owned (same ▸ ownerEq)
          simp only [improved, Profile.update_of_ne _ _ different]
      change expect ((actionDistribution profile config event).bind (config.step event ready)) _ ≤
        expect ((actionDistribution improved config event).bind (config.step event ready)) _
      rw [sameLaw]
      change expect (eventStep profile config event ready) _ ≤
        expect (eventStep profile config event ready) _
      apply expect_mono _ (eventIntegrable profile _) (eventIntegrable profile _)
      intro stepped member
      obtain ⟨action, _, steppedMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact ih stepped (next action stepped steppedMember)

/-- Replacing omissions by accepted unopenable bindings weakly raises the
deciding player's absorbing-exit value from every configuration. -/
theorem submitPolicy_runValue_le (finite : graph.FiniteActions)
    (profile : graph.BehavioralProfile) (who : Player) (scheduler : graph.PublicScheduler)
    {payoff : graph.Config → ℝ} {excluded : ℝ} (low : ∀ config, excluded ≤ payoff config)
    (atDefault : ∀ config, who ∈ config.defaulted → payoff config = excluded)
    (config : graph.Config) :
    runValue profile scheduler payoff config ≤
      runValue (Profile.update (sig := graph.gameSignature) profile who
        (graph.submitPolicy who (profile who))) scheduler payoff config :=
  submitPolicy_runValue_le_of_remaining finite profile who scheduler low atDefault
    config.remaining config rfl

/-- A configuration's completed bindings have no public default markers. -/
def Config.NoBindingDefaults (config : graph.Config) : Prop :=
  ∀ completion ∈ config.history, ∀ owner payload,
    graph.outputLayout completion.event = .binding owner payload → completion.defaultEvent = none

/-- An empty public default set excludes binding defaults. -/
theorem Config.NoBindingDefaults.of_clear {config : graph.Config}
    (clear : config.defaulted = ∅) : config.NoBindingDefaults := by
  intro record member _owner _payload _binding
  cases recorded : record.defaultEvent with
  | none => rfl
  | some owner =>
      have inactive : owner ∈ config.defaulted :=
        (mem_defaulted_iff_completionOf config owner).mpr
          ⟨record.event, by
            rw [(completionOf_eq_some_iff config record.event record).mpr ⟨member, rfl⟩]
            exact recorded⟩
      rw [clear] at inactive
      simp at inactive

namespace EventCode

variable {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}

theorem submitted_binding_defaultEvent {owner : Player} {payload : L.Ty}
    (code : EventCode layout (.binding owner payload)) (defaults : Finset Player)
    (action : Option (PublicationResult (L.Val payload)))
    (value : PublicationResult (L.Val payload))
    (submitted : (EventField.binding owner payload).Submitted action) :
    (code.actualDecision defaults action).bind (fun chosen => code.defaultEvent chosen value) =
      none := by
  cases code with
  | bind =>
    cases action with
    | none => cases submitted
    | some choice =>
      by_cases inactive : owner ∈ defaults <;>
        simp [EventCode.actualDecision, EventCode.actor, EventCode.defaultEvent,
          EventCode.causesDefault, inactive]

end EventCode

/-- A supported binding step under submitting policies records no public
default, including when the owner was already inactive. -/
theorem completion_bind_default_none_of_submits (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile) (config : graph.Config) (event : graph.EventId)
    (owner : Player) (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) (supported : action ∈ (actionDistribution profile config
      event).support)
    (value : (graph.outputLayout event).Value) :
    (EventGraph.completion graph event (config.actualDecision event action) value).defaultEvent =
      none := by
  have codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) = code
    cases code
    rfl
  have actor : graph.actor? event = some owner := by
    have identified := (EventCode.actor_cast outputEq (graph.nodes event)).symm
    rw [codeEq] at identified
    exact identified
  by_cases inactive : owner ∈ config.defaulted
  · rw [config.actualDecision_of_defaulted event owner actor inactive]
    rfl
  · rw [actionDistribution_of_actor profile config actor, dite_eq_right inactive] at supported
    have submitted := submits owner event actor (graph.playerObserve owner config) inactive action
      supported
    have castSubmitted : (EventField.binding owner payload).Submitted
        (cast (congrArg EventField.Action outputEq) action) :=
      EventField.submitted_cast outputEq action submitted
    have recorded := config.completion_defaultEvent_of_code event outputEq (.bind owner payload)
      codeEq (cast (congrArg EventField.Action outputEq) action)
        (cast (congrArg EventField.Value outputEq) value)
    have absent := EventCode.submitted_binding_defaultEvent
      (EventCode.bind (layout := graph.layout) owner payload) config.defaulted
        (cast (congrArg EventField.Action outputEq) action)
        (cast (congrArg EventField.Value outputEq) value) castSubmitted
    simpa only [cast_cast, cast_eq] using recorded.trans absent

theorem Config.NoBindingDefaults.eventStep {profile : graph.BehavioralProfile}
    (submits : graph.SubmitsBindings profile) {config : graph.Config}
    (clean : config.NoBindingDefaults) (event : graph.EventId) (ready : config.cut.Ready event)
    (next : graph.Config) (supported : next ∈ (eventStep profile config event ready).support) :
    next.NoBindingDefaults := by
  obtain ⟨action, selected, stepped⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  rw [Config.step, PMF.support_map] at stepped
  obtain ⟨value, _, rfl⟩ := stepped
  intro completion member owner payload outputEq
  rw [Config.complete_history, List.mem_append, List.mem_singleton] at member
  rcases member with previous | rfl
  · exact clean completion previous owner payload outputEq
  · exact completion_bind_default_none_of_submits profile submits config event owner payload
      outputEq action selected value

theorem Config.NoBindingDefaults.planReachable {profile : graph.BehavioralProfile}
    {scheduler : graph.PublicScheduler} (submits : graph.SubmitsBindings profile)
    {start final : graph.Config} (clean : start.NoBindingDefaults)
    (reach : PlanReachable profile scheduler start final) : final.NoBindingDefaults := by
  induction reach with
  | refl => exact clean
  | tail _ step ih =>
    obtain ⟨_running, selected, _chosen, supported⟩ := step
    exact ih.eventStep submits selected.1 ((EventOrder.Cut.mem_enabled _ _).mp selected.2) _
      supported

/-- Every policy-plan history of a submitting profile has no binding-default
marker. No finiteness or equilibrium assumption is needed. -/
theorem noBindingDefaults_of_planReachable (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile) (scheduler : graph.PublicScheduler)
    (inputs : graph.Inputs) (final : graph.Config)
    (reach : PlanReachable profile scheduler (Config.initial inputs) final) :
    final.NoBindingDefaults := by
  have initial : (Config.initial inputs : graph.Config).NoBindingDefaults := by
    intro completion member
    cases member
  exact initial.planReachable submits reach

omit [DecidableEq Player] in
theorem Config.NoBindingDefaults.defaultOf_binding {config : graph.Config}
    (clean : config.NoBindingDefaults) (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    (completionOf config event).bind EventCompletion.defaultEvent = none := by
  cases found : completionOf config event with
  | none => rfl
  | some completion =>
    obtain ⟨member, same⟩ := (completionOf_eq_some_iff config event completion).mp found
    exact clean completion member owner payload (same ▸ binding)

omit [DecidableEq Player] in
/-- A completed private event of a submitting run carries no public-default
marker, whether or not its owner had already defaulted elsewhere. -/
theorem Config.NoBindingDefaults.defaultOf_private {config : graph.Config}
    (clean : config.NoBindingDefaults) (event : graph.EventId)
    (privateOutput : ¬ (graph.outputLayout event).IsPublic) :
    (completionOf config event).bind EventCompletion.defaultEvent = none := by
  cases actor : graph.actor? event with
  | none =>
    exact (privateOutput (EventCode.output_public_of_actor_none (graph.nodes event) actor)).elim
  | some owner =>
    rcases EventCode.output_public_or_binding_of_actor (graph.nodes event) owner actor with
      isPublic | ⟨payload, binding⟩
    · exact (privateOutput isPublic).elim
    · exact clean.defaultOf_binding event owner payload binding

end Vegas.EventGraph

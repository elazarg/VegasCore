module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.BindingSubmission
public import Vegas.EventGraph.CanonicalStep
public import Vegas.EventGraph.PrefixRestriction
public import Vegas.EventGraph.CommutationRecall
public import Vegas.EventGraph.ObservationStep
public import Vegas.EventGraph.DependencyRelaxation
public import Vegas.EventGraph.DefaultFailure

@[expose] public section

/-! # Canonical private-binding chains

Submitting profiles preserve the complete joint honest observations when the
focal binding choices change. From a clean rank prefix, their canonical runs
also retain exact sampled action and output records without public defaults.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Retain public observations jointly with every nonfocal player's full observation. -/
def bindingObservers (focal : Player) (config : graph.Config) :=
  (graph.publicObserve config,
    fun owner : {owner : Player // owner ≠ focal} => graph.playerObserve owner.1 config)

private theorem publicStore_complete_private (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (hidden : ¬ (graph.outputLayout event).IsPublic) :
    graph.publicStore (config.complete event ready action value).store =
      graph.publicStore config.store := by
  apply graph.publicStore_congr
  intro field isPublic
  cases field with
  | inl => rfl
  | inr other =>
      have different : other ≠ event := by
        intro same
        subst other
        exact hidden isPublic
      exact config.complete_output_of_ne event other ready action value different

private theorem bindingObservers_complete_congr (focal : Player)
    (left right : graph.Config)
    (same : bindingObservers focal left = bindingObservers focal right)
    (event : graph.EventId) (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (hidden : ¬ (graph.outputLayout event).IsPublic)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value)
    (values : ∀ owner, owner ≠ focal → graph.fieldVisibleTo owner (.inr event) →
      leftValue = rightValue)
    (actions : ∀ owner, owner ≠ focal → graph.actor? event = some owner →
      leftAction = rightAction)
    (publicEffect :
      (completion graph event (left.actualDecision event leftAction) leftValue).defaultEvent =
        (completion graph event (right.actualDecision event rightAction) rightValue).defaultEvent) :
    bindingObservers focal (left.complete event leftReady leftAction leftValue) =
      bindingObservers focal (right.complete event rightReady rightAction rightValue) := by
  dsimp only [bindingObservers] at same ⊢
  have publics := congrArg Prod.fst same
  have orders := congrArg EventPublicObservation.completionOrder publics
  have stores := congrArg EventPublicObservation.store publics
  have defaults := congrArg EventPublicObservation.defaults publics
  apply Prod.ext
  · apply EventPublicObservation.ext
    · simpa only [publicObserve, Config.complete_history, List.map_append, List.map_cons,
        List.map_nil, completion] using congrArg (fun prior => prior ++ [event]) orders
    · exact (publicStore_complete_private left event leftReady leftAction leftValue hidden).trans
        (stores.trans
          (publicStore_complete_private right event rightReady rightAction rightValue hidden).symm)
    · change (left.complete event leftReady leftAction leftValue).defaults =
        (right.complete event rightReady rightAction rightValue).defaults
      rw [Config.complete_defaults, Config.complete_defaults]
      exact congrArg₂ DefaultHistory.record defaults publicEffect
  · funext owner
    have observed := congrFun (congrArg Prod.snd same) owner
    exact playerObserve_complete_congr owner.1 left right observed event leftReady rightReady
      leftAction rightAction leftValue rightValue (values owner.1 owner.2)
      (actions owner.1 owner.2) publicEffect

private theorem step_eq_outputLaw_map (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    config.step event ready action =
      (outputLaw config event ready action).map (config.complete event ready action) := rfl

private theorem option_get_eq {α : Type} {left right : Option α}
    (same : left = right) (leftSome : left.isSome) (rightSome : right.isSome) :
    left.get leftSome = right.get rightSome := by
  cases same
  rfl

private theorem binding_outputLaw_congr (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (left right : graph.Config) (defaults : left.defaulted = right.defaulted)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (action : graph.Action event) :
    outputLaw left event leftReady action = outputLaw right event rightReady action := by
  unfold outputLaw
  apply option_get_eq
  have effective : left.effectiveAction event action = right.effectiveAction event action := by
    unfold Config.effectiveAction
    rw [defaults]
  rw [effective]
  apply (graph.nodes event).eval?_congr
  intro field read
  rw [(graph.nodes event).readFields_eq_empty_of_binding binding] at read
  exact (Finset.notMem_empty _ read).elim

/-- Within a binding block the joint honest observation law is unaffected by any
submitting focal policy. All honest behavioral kernels and their dependence on
their own earlier bindings remain unchanged. -/
theorem eventStep_bindingObservers_congr
    (focal : Player) (leftProfile rightProfile : graph.BehavioralProfile)
    (leftSubmits : graph.SubmitsBindings leftProfile)
    (rightSubmits : graph.SubmitsBindings rightProfile)
    (others : ∀ owner, owner ≠ focal → leftProfile owner = rightProfile owner)
    (left right : graph.Config)
    (same : bindingObservers focal left = bindingObservers focal right)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event) :
    (eventStep leftProfile left event leftReady).map (bindingObservers focal) =
      (eventStep rightProfile right event rightReady).map (bindingObservers focal) := by
  have actor : graph.actor? event = some owner := (graph.nodes event).actor_eq_of_binding binding
  have hidden : ¬ (graph.outputLayout event).IsPublic := by
    rw [binding]
    exact fun impossible => impossible
  have defaults : left.defaulted = right.defaulted :=
    congrArg DefaultHistory.defaulted (congrArg EventPublicObservation.defaults
      (congrArg Prod.fst same))
  have effects (leftAction : graph.Action event)
      (leftSupported : leftAction ∈ (actionLaw leftProfile left event).support)
      (rightAction : graph.Action event)
      (rightSupported : rightAction ∈ (actionLaw rightProfile right event).support)
      (leftValue rightValue : (graph.outputLayout event).Value) :
      (completion graph event (left.actualDecision event leftAction) leftValue).defaultEvent =
        (completion graph event (right.actualDecision event rightAction) rightValue).defaultEvent :=
    (completion_bind_default_none_of_submits leftProfile leftSubmits left event owner payload
      binding leftAction leftSupported leftValue).trans
        (completion_bind_default_none_of_submits rightProfile rightSubmits right event owner payload
          binding rightAction rightSupported rightValue).symm
  unfold eventStep
  rw [PMF.map_bind, PMF.map_bind]
  by_cases foreign : owner = focal
  · subst owner
    apply bind_eq_of_map_eq _ _ (fun _ => ()) (fun _ => ())
      ((PMF.map_const _ ()).trans (PMF.map_const _ ()).symm)
    intro leftAction leftSupported rightAction rightSupported _
    rw [step_eq_outputLaw_map, step_eq_outputLaw_map, PMF.map_comp, PMF.map_comp,
      ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    apply bind_eq_of_map_eq _ _ (fun _ => ()) (fun _ => ())
      ((PMF.map_const _ ()).trans (PMF.map_const _ ()).symm)
    intro leftValue _ rightValue _ _
    apply congrArg PMF.pure
    apply bindingObservers_complete_congr focal left right same event leftReady rightReady hidden
      leftAction rightAction leftValue rightValue
    · intro observer different visible
      change (graph.outputLayout event).VisibleTo observer at visible
      rw [binding] at visible
      exact (different visible.symm).elim
    · intro observer different owned
      exact (different (Option.some.inj (actor.symm.trans owned)).symm).elim
    · exact effects leftAction leftSupported rightAction rightSupported leftValue rightValue
  · have actionEq : actionLaw leftProfile left event = actionLaw rightProfile right event := by
      rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
      by_cases inactive : owner ∈ left.defaulted
      · have rightInactive : owner ∈ right.defaulted := defaults ▸ inactive
        rw [dite_eq_left inactive, dite_eq_left rightInactive]
      · have rightActive : owner ∉ right.defaulted := defaults ▸ inactive
        rw [dite_eq_right inactive, dite_eq_right rightActive, others owner foreign]
        have observed := congrFun (congrArg Prod.snd same) ⟨owner, foreign⟩
        have applyCongr (first second : graph.PlayerObservation owner) (equal : first = second)
            (firstActive : owner ∉ first.defaulted) (secondActive : owner ∉ second.defaulted) :
            rightProfile owner event actor first firstActive =
              rightProfile owner event actor second secondActive := by
          cases equal
          rfl
        exact applyCongr _ _ observed _ _
    rw [actionEq]
    apply bind_congr_on_support _
    intro action rightSupported
    have leftSupported : action ∈ (actionLaw leftProfile left event).support := by
      rwa [actionEq]
    rw [step_eq_outputLaw_map, step_eq_outputLaw_map, PMF.map_comp, PMF.map_comp,
      binding_outputLaw_congr event owner payload binding left right defaults leftReady rightReady]
    apply map_congr_on_support _
    intro value _
    exact bindingObservers_complete_congr focal left right same event leftReady rightReady hidden
      action action value value (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (effects action leftSupported action rightSupported value value)

private theorem eventStep_prefix {start : Nat} (profile : graph.BehavioralProfile)
    (config : graph.Config) (ordered : config.cut.IsPrefix start)
    (event : graph.EventId) (atRank : event.val = start) (ready : config.cut.Ready event)
    (next : graph.Config) (supported : next ∈ (eventStep profile config event ready).support) :
    next.cut.IsPrefix (start + 1) := by
  obtain ⟨action, _selected, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  rw [config.step_cut event ready action next moved]
  exact ordered.complete_at event ready atRank

/-- The complete joint observations of honest owners over a canonical private-binding
block do not depend on the focal player's submitting policy. No product assumption
on an initial distribution, or independence between an owner's successive choices,
is part of this identity. -/
theorem runPlan_bindingObservers_congr
    (focal : Player) (leftProfile rightProfile : graph.BehavioralProfile)
    (leftSubmits : graph.SubmitsBindings leftProfile)
    (rightSubmits : graph.SubmitsBindings rightProfile)
    (others : ∀ owner, owner ≠ focal → leftProfile owner = rightProfile owner) :
    ∀ count start (left right : graph.Config),
      left.cut.IsPrefix start → right.cut.IsPrefix start →
      start + count ≤ graph.order.eventCount →
      (∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
        ∃ owner payload, graph.outputLayout event = .binding owner payload) →
      bindingObservers focal left = bindingObservers focal right →
      (graph.runPlan (graph.policyPlan leftProfile graph.canonicalScheduler) count left).map
          (bindingObservers focal) =
        (graph.runPlan (graph.policyPlan rightProfile graph.canonicalScheduler) count right).map
          (bindingObservers focal) := by
  intro count
  induction count with
  | zero =>
      intro start left right _leftPrefix _rightPrefix _bounded _bindings same
      simpa only [runPlan, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      intro start left right leftPrefix rightPrefix bounded bindings same
      have inside : start < graph.order.eventCount := by omega
      let event : graph.EventId := ⟨start, inside⟩
      have leftReady : left.cut.Ready event := leftPrefix.ready inside
      have rightReady : right.cut.Ready event := rightPrefix.ready inside
      have least (config : graph.Config) (ordered : config.cut.IsPrefix start)
          (other : graph.EventId) (ready : config.cut.Ready other) : event ≤ other := by
        apply Fin.le_iff_val_le_val.mpr
        change start ≤ other.val
        by_contra earlier
        exact ready.1 ((ordered.2 other).mpr (by omega))
      obtain ⟨owner, payload, binding⟩ := bindings event (by rfl) (by dsimp only [event]; omega)
      rw [runPlan_canonical_succ _ _ _ leftReady.not_terminal event leftReady
        (least left leftPrefix), runPlan_canonical_succ _ _ _ rightReady.not_terminal event
          rightReady (least right rightPrefix), PMF.map_bind, PMF.map_bind]
      apply bind_eq_of_map_eq _ _ (bindingObservers focal) (bindingObservers focal)
        (eventStep_bindingObservers_congr focal leftProfile rightProfile leftSubmits rightSubmits
          others left right same event owner payload binding leftReady rightReady)
      intro nextLeft leftSupported nextRight rightSupported nextSame
      have nextLeftPrefix := eventStep_prefix leftProfile left leftPrefix event rfl leftReady
        nextLeft leftSupported
      have nextRightPrefix := eventStep_prefix rightProfile right rightPrefix event rfl rightReady
        nextRight rightSupported
      apply ih (start + 1) nextLeft nextRight nextLeftPrefix nextRightPrefix (by omega)
      · intro other lower upper
        exact bindings other (by omega) (by omega)
      · exact nextSame

/-- Submitting an unusable placeholder at a binding fixes no public default. -/
def submittedFailurePolicy (focal : Player) : graph.BehavioralPolicy focal :=
  graph.submitPolicy focal fun event actor _ _ =>
    PMF.pure ((graph.nodes event).failureAction focal actor)

/-- The canonical honest-chain sampler may fill all focal binding positions with
unusable submitted placeholders, while retaining the full joint honest readout. -/
theorem runPlan_bindingObservers_placeholders
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (focal : Player) (policy : graph.BehavioralPolicy focal)
    (policySubmits : graph.PolicySubmitsBindings focal policy)
    (count start : Nat) (config : graph.Config) (ordered : config.cut.IsPrefix start)
    (bounded : start + count ≤ graph.order.eventCount)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
      ∃ owner payload, graph.outputLayout event = .binding owner payload) :
    (graph.runPlan (graph.policyPlan
        (Profile.update (sig := graph.gameSignature) profile focal policy)
          graph.canonicalScheduler) count config).map (bindingObservers focal) =
      (graph.runPlan (graph.policyPlan
        (Profile.update (sig := graph.gameSignature) profile focal (submittedFailurePolicy focal))
          graph.canonicalScheduler) count config).map (bindingObservers focal) := by
  apply runPlan_bindingObservers_congr focal _ _
    (SubmitsBindings.update graph submits focal policy policySubmits)
    (SubmitsBindings.update graph submits focal (submittedFailurePolicy focal)
      (graph.policySubmitsBindings_submitPolicy focal _)) _ count start config config ordered
    ordered bounded bindings rfl
  intro owner foreign
  rw [Profile.update_of_ne _ _ foreign, Profile.update_of_ne _ _ foreign]

/-- Mixing arbitrary correlated source boundaries keeps each complete boundary jointly
with the sampled honest-chain readout. No initial factorization is assumed. -/
theorem runPlan_bindingObservers_joint_placeholders
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (focal : Player) (policy : graph.BehavioralPolicy focal)
    (policySubmits : graph.PolicySubmitsBindings focal policy)
    (count start : Nat) (prior : PMF graph.Config)
    (ordered : ∀ config ∈ prior.support, config.cut.IsPrefix start)
    (bounded : start + count ≤ graph.order.eventCount)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
      ∃ owner payload, graph.outputLayout event = .binding owner payload) :
    (prior.bind fun config =>
      (graph.runPlan (graph.policyPlan
        (Profile.update (sig := graph.gameSignature) profile focal policy)
          graph.canonicalScheduler) count config).map fun final =>
            (config, bindingObservers focal final)) =
      (prior.bind fun config =>
        (graph.runPlan (graph.policyPlan
          (Profile.update (sig := graph.gameSignature) profile focal (submittedFailurePolicy focal))
            graph.canonicalScheduler) count config).map fun final =>
              (config, bindingObservers focal final)) := by
  apply bind_congr_on_support _
  intro config supported
  have law := congrArg (PMF.map fun observed => (config, observed))
    (runPlan_bindingObservers_placeholders profile submits focal policy policySubmits count start
      config (ordered config supported) bounded bindings)
  simp only [PMF.map_comp, Function.comp_def] at law
  exact law

private theorem noBindingDefaults_of_clear {config : graph.Config}
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

/-- A supported submitted binding action is retained by its exact semantic step. -/
theorem step_submitted_binding_frame (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile)
    (config : graph.Config) (clear : config.defaulted = ∅)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event)
    (selected : action ∈ (actionLaw profile config event).support)
    (next : graph.Config) (moved : next ∈ (config.step event ready action).support) :
    ∃ result : PublicationResult (L.Val payload),
      action = cast (congrArg EventField.Action binding.symm) (some result) ∧
      next.defaulted = ∅ ∧ Relation.ReflTransGen Config.Step config next ∧
        completionOf next event = some (EventGraph.completion graph event
          (some (cast (congrArg EventField.Action binding.symm) (some result)))
          (cast (congrArg EventField.Value binding.symm) result)) ∧
        next.outputs event = some (cast (congrArg EventField.Value binding.symm) result) := by
  have path : Relation.ReflTransGen Config.Step config next :=
    .single ⟨event, ready, action, moved⟩
  have codeEq : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = code
    cases code
    rfl
  have actor : graph.actor? event = some owner :=
    EventCode.actor_eq_of_binding (graph.nodes event) binding
  have active : owner ∉ config.defaulted := by rw [clear]; simp
  rw [actionLaw_of_actor profile config actor, dite_eq_right active] at selected
  have submitted := submits owner event actor (graph.playerObserve owner config) active action
    selected
  have typedSubmitted := EventField.submitted_cast binding action submitted
  change (cast (congrArg EventField.Action binding) action).isSome at typedSubmitted
  obtain ⟨result, chosen⟩ := Option.isSome_iff_exists.mp typedSubmitted
  have actionEq : action = cast (congrArg EventField.Action binding.symm) (some result) := by
    have inverse := congrArg (cast (congrArg EventField.Action binding.symm)) chosen
    simpa only [cast_cast, cast_eq] using inverse
  have law := config.step_eq_map_of_code event ready binding (.bind owner payload) codeEq
    (some result) (PMF.pure result) (by
      simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right active,
        EventCode.eval?, Option.getD_some])
  rw [actionEq, law, PMF.pure_map, PMF.mem_support_pure_iff] at moved
  subst next
  refine ⟨result, actionEq, ?_, path, ?_, Config.complete_output_same ..⟩
  · change (config.complete event ready
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result)).defaults.defaulted = ∅
    rw [Config.complete_defaults,
      config.completion_bind_some_defaultEvent event owner payload binding codeEq result result,
      DefaultHistory.defaulted_record_none]
    exact clear
  · rw [completionOf_complete, Function.update_self,
      config.actualDecision_of_active event owner actor active]

/-- One active submitted binding records its exact typed action and result. -/
theorem eventStep_submitted_binding_frame (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile)
    (config : graph.Config) (clear : config.defaulted = ∅)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (next : graph.Config) (supported : next ∈ (eventStep profile config event ready).support) :
    next.defaulted = ∅ ∧ Relation.ReflTransGen Config.Step config next ∧
      ∃ result : PublicationResult (L.Val payload),
        completionOf next event = some (EventGraph.completion graph event
          (some (cast (congrArg EventField.Action binding.symm) (some result)))
          (cast (congrArg EventField.Value binding.symm) result)) ∧
        next.outputs event = some (cast (congrArg EventField.Value binding.symm) result) := by
  obtain ⟨action, selected, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨result, _, clean, path, record, stored⟩ := step_submitted_binding_frame profile submits
    config clear event ready owner payload binding action selected next moved
  exact ⟨clean, path, result, record, stored⟩

/-- Every supported canonical binding prefix retains the exact sampled table,
its graph path and its absence of public defaults. -/
theorem runPlan_submitted_binding_frame (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile) :
    ∀ count start (config : graph.Config),
      config.cut.IsPrefix start → config.defaulted = ∅ →
      start + count ≤ graph.order.eventCount →
      (∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
        ∃ owner payload, graph.outputLayout event = .binding owner payload) →
      ∀ final ∈ (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
        count config).support,
      final.cut.IsPrefix (start + count) ∧
        Relation.ReflTransGen Config.Step config final ∧ final.defaulted = ∅ ∧
        final.NoBindingDefaults ∧
        ∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
          ∃ owner payload, ∃ binding : graph.outputLayout event = .binding owner payload,
            ∃ result : PublicationResult (L.Val payload),
              completionOf final event = some (EventGraph.completion graph event
                (some (cast (congrArg EventField.Action binding.symm) (some result)))
                (cast (congrArg EventField.Value binding.symm) result)) ∧
              final.outputs event = some (cast (congrArg EventField.Value binding.symm)
                result) := by
  intro count
  induction count with
  | zero =>
      intro start config ordered clear _bounded _bindings final supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      refine ⟨by simpa only [Nat.add_zero] using ordered, .refl, clear,
        noBindingDefaults_of_clear clear, ?_⟩
      intro event lower upper
      omega
  | succ count ih =>
      intro start config ordered clear bounded bindings final supported
      have inside : start < graph.order.eventCount := by omega
      let event : graph.EventId := ⟨start, inside⟩
      have ready : config.cut.Ready event := ordered.ready inside
      have least (other : graph.EventId) (otherReady : config.cut.Ready other) : event ≤ other := by
        apply Fin.le_iff_val_le_val.mpr
        change start ≤ other.val
        by_contra earlier
        exact otherReady.1 ((ordered.2 other).mpr (by omega))
      obtain ⟨owner, payload, binding⟩ := bindings event (by rfl) (by dsimp only [event]; omega)
      rw [runPlan_canonical_succ profile count config ready.not_terminal event ready least]
        at supported
      obtain ⟨next, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨nextClear, firstPath, result, firstRecord, firstValue⟩ :=
        eventStep_submitted_binding_frame profile submits config clear event ready owner payload
          binding next moved
      have nextPrefix : next.cut.IsPrefix (start + 1) := by
        obtain ⟨action, _, step⟩ := (PMF.mem_support_bind_iff _ _ _).mp moved
        rw [config.step_cut event ready action next step]
        exact ordered.complete inside
      have remainingBindings (other : graph.EventId) (lower : start + 1 ≤ other.val)
          (upper : other.val < start + 1 + count) :
          ∃ actor ty, graph.outputLayout other = .binding actor ty :=
        bindings other (by omega) (by omega)
      obtain ⟨finalPrefix, tailPath, finalClear, finalClean, frame⟩ :=
        ih (start + 1) next nextPrefix nextClear (by omega) remainingBindings final rest
      refine ⟨by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using finalPrefix,
        firstPath.trans tailPath, finalClear, finalClean, ?_⟩
      intro prior lower upper
      by_cases same : prior = event
      · subst prior
        exact ⟨owner, payload, binding, result,
          Config.Step.path_completionOf_of_some tailPath event _ firstRecord,
          Config.Step.path_store_of_some tailPath (.inr event) _ firstValue⟩
      · exact frame prior (by
          have different : prior.val ≠ start := fun rank => same (Fin.ext rank)
          omega) (by omega)

end Vegas.EventGraph

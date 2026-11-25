module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.NativeForfeitContinuation
public import Vegas.Game.RevealPhaseBoundary
public import Vegas.Game.GraphForfeit
public import Vegas.EventGraph.PrefixRestriction
public import Vegas.Game.NativeBindingRecord
public import Vegas.EventGraph.LastErasedLaw
public import Vegas.EventGraph.PrefixDeviation
public import Vegas.EventGraph.DefaultFailure
public import GameTheoryExtensions.Math.Probability.Support
public import Vegas.Pending.EffectiveOpening
public import Vegas.Game.BindingBlockCompletion
public import Vegas.Game.IntendedPrefixContinuation
public import Vegas.EventGraph.PolicyPatch
public import Vegas.EventGraph.CanonicalStep
public import GameTheory.Math.Probability.Expectation
public import GameTheory.Math.Probability.ExpectationConditioning
public import Vegas.Game.SourceServiceCheckpoint
public import Vegas.Compile.EventGraphPolicyLaw
public import Vegas.EventGraph.BindingChain
public import Vegas.Source.ObservationRecall
public import GameTheory.Math.Probability.ConditionalObservation
public import Vegas.Compile.EventGraphStep
public import Vegas.Source.Semantics
public import Vegas.Compile.PrescribedProfile
public import Vegas.Compile.EventGraphLaw
public import Vegas.EventGraph.CanonicalPrefix
public import Vegas.Game.BindingSourceObservation
public import Vegas.Game.SourceBindingFiber
public import Vegas.Game.BindingBlockOpacity
public import Vegas.Source.IntendedGame
public import Vegas.Game.ServiceObservation
public import Vegas.Source.DisclosureOpening
public import Vegas.Game.PublicationSurvival
public import Vegas.Game.SourceServiceReachedDecoding
public import GameTheoryExtensions.Math.Probability.ObservedChoice
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Game.SourceServiceCanonicalSlots
public import Vegas.Pending.ReactiveBindingLikelihood
public import Vegas.Compile.EventGraphObservationEncoding
public import Vegas.Game.NativeBindingTableSampling
public import Vegas.Game.AsyncDeviationChoice
public import Vegas.EventGraph.PrefixPolicy
public import Vegas.Game.SourceServiceContinuation
public import Vegas.Game.ServiceDeviationTraffic
public import Vegas.Pending.ChanceContinuation
public import Vegas.Pending.CanonicalOutcomeHead
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.EventGraph.CommutationRecall
public import Vegas.EventGraph.SequentialLaw
public import Vegas.Compile.EventGraphReadoutComplete
public import Vegas.Game.SourceServiceFactorization

@[expose] public section

/-! # Native deviations of prescribed source-prefix clients

Private binding intervals use the existing correlated source-table sampler and physical
record certificates. Publication intervals retain the complete source post-view jointly
with survival and native traffic. Irrevocable failure branches are bounded by the fixed
source exit utility. The resulting comparison covers every raw native unilateral policy.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

end Vegas

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem canonical_owned_expected_continuation
    (reference : graph.BehavioralProfile) (focal : Player) (event : graph.EventId)
    (head : graph.BehavioralPolicy focal) (count : Nat)
    {Seed NextSeed : Type} (prior : PMF Seed)
    (source : Seed → {config : graph.Config // config.cut.IsPrefix event.val})
    (nextPrior : PMF NextSeed) (nextSource : NextSeed → graph.Config)
    (marginal : nextPrior.map nextSource = (prior.map source).bind fun config =>
      eventStep (Function.update reference focal head) config.1 event
        (config.2.ready event.isLt))
    (utility : graph.Config → ℝ) (nativeValue : NextSeed → ℝ)
    (good : NextSeed → Bool) (floor bound : ℝ)
    (utilityBound : ∀ final, |utility final| ≤ bound)
    (utilityFloor : ∀ final, floor ≤ utility final)
    (nativeIntegrable : PayoffIntegrable nextPrior nativeValue)
    (bad : ∀ seed ∈ nextPrior.support, good seed = false → nativeValue seed ≤ floor)
    (tail : ∀ _present : true ∈ (nextPrior.map good).support,
      ∃ policy : graph.BehavioralPolicy focal,
        expect (fiberPosterior nextPrior good true) nativeValue ≤
          expect ((fiberPosterior nextPrior good true).bind fun seed =>
            graph.runPlan (graph.policyPlan (Function.update reference focal policy)
              graph.canonicalScheduler) count (nextSource seed)) utility) :
    ∃ policy : graph.BehavioralPolicy focal,
      expect nextPrior nativeValue ≤ expect (prior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) (source seed).1) utility := by
  classical
  obtain ⟨tailPolicy, goodBound⟩ : ∃ policy : graph.BehavioralPolicy focal,
      true ∈ (nextPrior.map good).support →
        expect (fiberPosterior nextPrior good true) nativeValue ≤
          expect ((fiberPosterior nextPrior good true).bind fun seed =>
            graph.runPlan (graph.policyPlan (Function.update reference focal policy)
              graph.canonicalScheduler) count (nextSource seed)) utility := by
    by_cases present : true ∈ (nextPrior.map good).support
    · obtain ⟨policy, comparison⟩ := tail present
      exact ⟨policy, fun _ => comparison⟩
    · exact ⟨reference focal, fun impossible => (present impossible).elim⟩
  let continuation := fun seed => graph.runPlan
    (graph.policyPlan (Function.update reference focal tailPolicy) graph.canonicalScheduler)
      count (nextSource seed)
  let value := fun seed => expect (continuation seed) utility
  have integrable (law : PMF NextSeed) : PayoffIntegrable (law.bind continuation) utility :=
    payoffIntegrable_of_bounded _ _ utilityBound
  have valueIntegrable : PayoffIntegrable nextPrior value :=
    payoffIntegrable_bind_conditionalExpectation nextPrior continuation utility
      (integrable nextPrior)
  have tailBound : expect nextPrior nativeValue ≤
      expect (nextPrior.bind continuation) utility := by
    rw [expect_bind_tower nextPrior continuation utility (integrable nextPrior)]
    apply expect_fiberwise_le nextPrior good nativeValue value nativeIntegrable valueIntegrable
    intro selected present
    cases selected with
    | false =>
        apply expect_mono _ (payoffIntegrable_fiberPosterior nextPrior good nativeValue
          nativeIntegrable false) (payoffIntegrable_fiberPosterior nextPrior good value
            valueIntegrable false)
        intro seed member
        obtain ⟨selected, supported⟩ := mem_support_fiberPosterior present member
        have lower : floor ≤ value seed := by
          have expected := expect_mono (fun final _ => utilityFloor final)
            (payoffIntegrable_constant (continuation seed) floor)
            (payoffIntegrable_of_bounded (continuation seed) utility utilityBound)
          simpa only [expect_constant] using expected
        exact (bad seed supported selected).trans lower
    | true =>
        have comparison := goodBound present
        rw [expect_bind_tower _ continuation utility
          (integrable (fiberPosterior nextPrior good true))] at comparison
        exact comparison
  let policy := patchPolicy event head tailPolicy
  have tails (config : graph.Config) (completed : event ∈ config.cut.completed) :
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) count config =
        graph.runPlan (graph.policyPlan (Function.update reference focal tailPolicy)
          graph.canonicalScheduler) count config := by
    apply runPlan_congr_of_actionLaw graph.canonicalScheduler (fun other => other = event)
      (fun current other different => actionLaw_update_patch_of_ne reference focal event
        head tailPolicy current different) count config
    intro other same
    exact same.symm ▸ completed
  have first (config : {config : graph.Config // config.cut.IsPrefix event.val}) :
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) config.1 =
        (eventStep (Function.update reference focal head) config.1 event
          (config.2.ready event.isLt)).bind fun next =>
            graph.runPlan (graph.policyPlan (Function.update reference focal tailPolicy)
              graph.canonicalScheduler) count next := by
    have ready : config.1.cut.Ready event := config.2.ready event.isLt
    have least (other : graph.EventId)
        (otherReady : config.1.cut.Ready other) : event ≤ other := by
      apply Fin.le_iff_val_le_val.mpr
      by_contra smaller
      exact otherReady.1 ((config.2.2 other).mpr (by omega))
    rw [runPlan_canonical_succ _ count config.1 ready.not_terminal event ready least]
    simp only [eventStep, policy, actionLaw_update_patch_self, PMF.bind_bind]
    apply bind_congr_on_support _
    intro action _
    apply bind_congr_on_support _
    intro next moved
    apply tails next
    rw [config.1.step_cut event ready action next moved, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have law : (prior.bind fun seed => graph.runPlan
      (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
        (count + 1) (source seed).1) =
      nextPrior.bind (fun seed => graph.runPlan
        (graph.policyPlan (Function.update reference focal tailPolicy) graph.canonicalScheduler)
          count (nextSource seed)) := by
    calc
      _ = (prior.map source).bind (fun config => graph.runPlan
          (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
            (count + 1) config.1) := by rw [PMF.bind_map]; rfl
      _ = ((prior.map source).bind fun config =>
          eventStep (Function.update reference focal head) config.1 event
            (config.2.ready event.isLt)).bind (fun next => graph.runPlan
              (graph.policyPlan (Function.update reference focal tailPolicy)
                graph.canonicalScheduler) count next) := by
        rw [PMF.bind_bind]
        apply bind_congr_on_support _
        intro config _
        exact first config
      _ = _ := by rw [← marginal, PMF.bind_map]; rfl
  exact ⟨policy, by rw [law]; exact tailBound⟩

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem exists_graph_binding_head
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    {Γ : SourceCtx Player L} {names : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (kernel : DecisionView owner Γ → PMF (Option (PublicationResult (L.Val payload))))
    (reference : (serviceGraph setup deps).BehavioralProfile) :
    ∃ head : (serviceGraph setup deps).BehavioralPolicy owner,
      ∀ (source : Config Player L Γ) (config : (serviceGraph setup deps).Config),
        SourceCheckpoint setup source refs event.val config → owner ∉ source.defaulted →
        actionLaw (Function.update reference owner head) config event =
          (kernel (source.view owner)).map
            (fun choice => cast (congrArg EventField.Action binding.symm) choice) := by
  let chosen : BehavioralPolicy owner (.commit name owner fresh guard next) :=
    ((fun _ view _ => kernel view), (profile owner).2)
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let atEvent := fun (_actor : (serviceGraph setup deps).actor? event = some owner)
      (observation : (serviceGraph setup deps).PlayerObservation owner)
      (_active : owner ∉ observation.defaulted) =>
    (compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref owner chosen
      index observation.store observation.defaults
      (decodeCompletions setup.program observation.ownActions)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice)
  let head := Function.update (reference owner) event atEvent
  refine ⟨head, ?_⟩
  intro source config checkpoint active
  have graphActive : owner ∉ config.defaulted := by
    have status := congrArg DefaultHistory.defaulted checkpoint.defaults
    change config.defaulted = source.defaulted at status
    rwa [status]
  have decoded := decodeObservation?_playerStore_eq_some
    (graph := serviceGraph setup deps) refs owner source.state config.store checkpoint.agrees
  have history : decodeCompletions setup.program
      ((serviceGraph setup deps).playerObserve owner config).ownActions = source.history owner := by
    change decodeHistory setup.program config.history owner = source.history owner
    exact congrFun checkpoint.history owner
  rw [actionLaw_of_actor _ _ owned, dite_eq_right graphActive, Function.update_self]
  simp only [head, Function.update_self]
  change atEvent owned ((serviceGraph setup deps).playerObserve owner config) graphActive = _
  change (compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref owner chosen
    index ((serviceGraph setup deps).playerStore owner config.store) config.defaults
    (decodeCompletions setup.program
      ((serviceGraph setup deps).playerObserve owner config).ownActions)).map _ = _
  rw [history, checkpoint.defaults]
  rw [compilePolicyTable_commit_of_decode refs embedding.ref chosen rfl _ source.defaults active
    (source.history owner) (sourceObserve owner source.state) decoded]
  rfl

end Vegas

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem source_binding_honest_suffix_reset
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (config : graph.Config) (clear : config.defaulted = ∅)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (ordered : config.cut.IsPrefix event.val) (focal : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding focal payload)
    (head : actionLaw profile config event =
      PMF.pure (cast (congrArg EventField.Action binding.symm)
        (some (.failure : PublicationResult (L.Val payload)))))
    (count : Nat) (bounded : event.val + 1 + count ≤ graph.order.eventCount)
    (bindings : ∀ prior : graph.EventId, event.val + 1 ≤ prior.val →
      prior.val < event.val + 1 + count → ∃ owner kind,
        graph.outputLayout prior = .binding owner kind)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ focal name payload) (source : Config Player L Γ)
    (kernel : DecisionView focal Γ → PMF (Option (PublicationResult (L.Val payload))))
    {Traffic : Type}
    (noise : DecisionView focal ((name, .commitment focal payload) :: Γ) → PMF Traffic) :
    let after := fun result => config.complete event ready
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result)
    let suffix := fun result => (graph.runPlan
      (graph.policyPlan profile graph.canonicalScheduler) count (after result)).map
        (bindingObservers focal)
    ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1)
      config).map (bindingObservers focal)).bind (fun honest =>
        (kernel (source.view focal)).bind fun action =>
          match action with
          | none => PMF.pure none
          | some result => (noise ((commitSuccessor name guard source action).view focal)).map
              fun traffic => some (((commitSuccessor name guard source action,
                after result), honest), traffic)) =
      (kernel (source.view focal)).bind fun action =>
        match action with
        | none => PMF.pure none
        | some result => (suffix result).bind fun honest =>
            (noise ((commitSuccessor name guard source action).view focal)).map fun traffic =>
              some (((commitSuccessor name guard source action, after result), honest), traffic)
    := by
  intro after suffix
  have code : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind focal payload := by
    generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = typed
    cases typed
    rfl
  have active : focal ∉ config.defaulted := by rw [clear]; simp
  have headStep := config.step_eq_map_of_code event ready binding (.bind focal payload) code
    (some (.failure : PublicationResult (L.Val payload))) (PMF.pure .failure) (by
      simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right active,
        EventCode.eval?, Option.getD_some])
  have least (other : graph.EventId) (otherReady : config.cut.Ready other) : event ≤ other := by
    apply Fin.le_iff_val_le_val.mpr
    by_contra smaller
    exact otherReady.1 ((ordered.2 other).mpr (by omega))
  have canonicalHead : (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
      (count + 1) config).map (bindingObservers focal) = suffix .failure := by
    rw [runPlan_canonical_succ profile count config ready.not_terminal event ready least,
      eventStep, head, PMF.pure_bind, headStep, PMF.pure_map, PMF.pure_bind]
  rw [canonicalHead, PMF.bind_comm]
  apply bind_congr_on_support _
  intro action _
  cases action with
  | none => exact PMF.bind_const _ _
  | some result =>
      have nextPrefix (value) : (after value).cut.IsPrefix (event.val + 1) :=
        ordered.complete_at event ready rfl
      have same : suffix .failure = suffix result :=
        runPlan_bindingObservers_congr focal profile profile submits submits (fun _ _ => rfl)
          count (event.val + 1) (after .failure) (after result) (nextPrefix .failure)
          (nextPrefix result) bounded bindings
          (bindingObservers_complete_submitted_focal config event ready focal payload binding
            .failure result)
      rw [same]

private theorem focal_source_successor_noise_reset
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (event : graph.EventId) (focal : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding focal payload)
    (count : Nat) (bounded : event.val + 1 + count ≤ graph.order.eventCount)
    (bindings : ∀ prior : graph.EventId, event.val + 1 ≤ prior.val →
      prior.val < event.val + 1 + count → ∃ owner kind,
        graph.outputLayout prior = .binding owner kind)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ focal name payload)
    (prior : PMF ({source : Config Player L Γ // focal ∉ source.defaulted} ×
      {ghost : graph.Config // ghost.cut.Ready event ∧
        ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅}))
    (head : ∀ hidden ∈ prior.support, actionLaw profile hidden.2.1 event =
      PMF.pure (cast (congrArg EventField.Action binding.symm)
        (some (.failure : PublicationResult (L.Val payload)))))
    (kernel : DecisionView focal Γ → PMF (Option (PublicationResult (L.Val payload))))
    {Traffic Seed : Type}
    (noise : DecisionView focal ((name, .commitment focal payload) :: Γ) → PMF Traffic)
    (nextPrior : PMF Seed)
    (nextSource : Seed → Config Player L ((name, .commitment focal payload) :: Γ))
    (ghost : Seed → {ghost : graph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → graph.Config) (traffic : Seed → Traffic)
    (joint : nextPrior.map (fun seed =>
        ((nextSource seed, (ghost seed, bindingObservers focal (table seed))), traffic seed)) =
      ((prior.bind fun hidden => ((graph.runPlan
        (graph.policyPlan profile graph.canonicalScheduler) (count + 1) hidden.2.1).map
          fun selected => (hidden.1, (hidden.2, bindingObservers focal selected)))).bind
        (fun hidden => (kernel (hidden.1.1.view focal)).map fun action =>
          (commitSuccessor name guard hidden.1.1 action, hidden.2))).bind fun hidden =>
            (noise (hidden.1.view focal)).map fun observed => (hidden, observed)) :
    let chosen := fun source : Config Player L ((name, .commitment focal payload) :: Γ) =>
      OwnAction.binding focal name payload (source.view focal).history.getLast?
    let advance := fun (ghost : {ghost : graph.Config // ghost.cut.Ready event ∧
        ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅}) result =>
      ghost.1.complete event ghost.2.1
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result)
    nextPrior.map (fun seed => match chosen (nextSource seed) with
      | none => none
      | some result => some (((nextSource seed, advance (ghost seed) result),
          bindingObservers focal (table seed)), traffic seed)) =
      prior.bind fun hidden => (kernel (hidden.1.1.view focal)).bind fun action =>
        match action with
        | none => PMF.pure none
        | some result => ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
            count (advance hidden.2 result)).map (bindingObservers focal)).bind fun honest =>
              (noise ((commitSuccessor name guard hidden.1.1 action).view focal)).map
                fun observed => some (((commitSuccessor name guard hidden.1.1 action,
                  advance hidden.2 result), honest), observed) := by
  intro chosen advance
  let project := fun pair :
      (Config Player L ((name, .commitment focal payload) :: Γ) ×
        ({ghost : graph.Config // ghost.cut.Ready event ∧
          ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅} ×
            (graph.PublicObservation ×
              ((owner : {owner : Player // owner ≠ focal}) → graph.PlayerObservation owner.1))))
          × Traffic =>
    match chosen pair.1.1 with
    | none => none
    | some result => some (((pair.1.1, advance pair.1.2.1 result), pair.1.2.2), pair.2)
  have remembered (source : {source : Config Player L Γ // focal ∉ source.defaulted})
      (action : Option (PublicationResult (L.Val payload))) :
      chosen (commitSuccessor name guard source.1 action) = action := by
    simp only [chosen, Config.view, commitSuccessor, source.2, ite_false,
      Function.update_self, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      OwnAction.binding_commit]
  have projected := congrArg (PMF.map project) joint
  rw [PMF.map_comp] at projected
  change nextPrior.map _ = _ at projected
  calc
    _ = _ := projected
    _ = _ := by
      simp only [PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind, Function.comp_def]
      apply bind_congr_on_support _
      intro hidden supported
      simp only [project, remembered]
      have reset := source_binding_honest_suffix_reset profile submits hidden.2.1
        hidden.2.2.2.2 event hidden.2.2.1 hidden.2.2.2.1 focal payload binding
        (head hidden supported) count bounded bindings guard hidden.1.1 kernel noise
      dsimp only at reset
      calc
        _ = ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
            (count + 1) hidden.2.1).map (bindingObservers focal)).bind (fun honest =>
              (kernel (hidden.1.1.view focal)).bind fun action =>
                match action with
                | none => PMF.pure none
                | some result =>
                    (noise ((commitSuccessor name guard hidden.1.1 action).view focal)).map
                      fun observed => some (((commitSuccessor name guard hidden.1.1 action,
                        advance hidden.2 result), honest), observed)) := by
          rw [PMF.bind_map]
          apply bind_congr_on_support _
          intro final _
          apply bind_congr_on_support _
          intro action _
          cases action with
          | none => exact pmf_map_fun_const _ _
          | some result => rfl
        _ = _ := by
          simpa only [PMF.bind_map, Function.comp_def, advance] using reset

private theorem binding_good_successor_law
    (profile : graph.BehavioralProfile) (count : Nat) (focal : Player)
    {Γ : SourceCtx Player L} {Traffic Seed : Type}
    (choices : PMF ((Config Player L Γ × graph.Config) × Bool))
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (ghost table : Seed → graph.Config) (traffic : Seed → Traffic) (submitted : Seed → Bool)
    (noise : DecisionView focal Γ → PMF Traffic) (good : Config Player L Γ → Bool)
    (law : prior.map (fun seed => if submitted seed then
        some (((source seed, ghost seed), bindingObservers focal (table seed)), traffic seed)
      else none) = choices.bind fun chosen =>
        if chosen.2 then
          ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count chosen.1.2).map
            (bindingObservers focal)).bind fun honest =>
              (noise (chosen.1.1.view focal)).map fun observed =>
                some ((chosen.1, honest), observed)
        else PMF.pure none)
    (present : true ∈ (prior.map (fun seed => submitted seed && good (source seed))).support) :
    let selected := fiberPosterior prior (fun seed => submitted seed && good (source seed)) true
    selected.map (fun seed =>
      (((source seed, ghost seed), bindingObservers focal (table seed)), traffic seed)) =
      (selected.map (fun seed => (source seed, ghost seed))).bind fun current =>
        ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count current.2).map
          (bindingObservers focal)).bind fun honest =>
            (noise (current.1.view focal)).map fun observed => ((current, honest), observed) := by
  intro selected
  let sourcePrior := (fiberPosterior choices
    (fun chosen => chosen.2 && good chosen.1.1) true).map Prod.fst
  let read := fun seed =>
    (((source seed, ghost seed), bindingObservers focal (table seed)), traffic seed)
  let optional := fun seed => if submitted seed then some (read seed) else none
  let flag := fun chosen : (Config Player L Γ × graph.Config) × Bool =>
    chosen.2 && good chosen.1.1
  let outFlag := fun observed : Option
      (((Config Player L Γ × graph.Config) ×
        (graph.PublicObservation ×
          ((owner : {owner : Player // owner ≠ focal}) → graph.PlayerObservation owner.1))) ×
            Traffic) => observed.elim false (fun current => good current.1.1.1)
  let channel := fun chosen : (Config Player L Γ × graph.Config) × Bool =>
    if chosen.2 then
      ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count chosen.1.2).map
        (bindingObservers focal)).bind fun honest =>
          (noise (chosen.1.1.view focal)).map fun observed => some ((chosen.1, honest), observed)
    else PMF.pure none
  have actualFlag : outFlag ∘ optional = fun seed => submitted seed && good (source seed) := by
    funext seed
    cases value : submitted seed <;> simp only [Function.comp_def, optional, value,
      Bool.false_eq_true, ↓reduceIte, outFlag, Option.elim_none, Bool.false_and,
      Option.elim_some, read, Bool.true_and]
  have observed (chosen) (_supported : chosen ∈ choices.support) (outcome)
      (member : outcome ∈ (channel chosen).support) : outFlag outcome = flag chosen := by
    by_cases accepted : chosen.2 = true
    · simp only [channel, accepted, ↓reduceIte] at member
      obtain ⟨honest, _, reached⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      obtain ⟨extra, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      simp only [outFlag, Option.elim_some, flag, accepted, Bool.true_and]
    · have rejected : chosen.2 = false := Bool.eq_false_iff.mpr accepted
      simp only [channel, rejected, Bool.false_eq_true, ↓reduceIte,
        PMF.mem_support_pure_iff] at member
      subst outcome
      simp only [outFlag, Option.elim_none, flag, rejected, Bool.false_and]
  have optionalLaw : prior.map optional = choices.bind channel := law
  have outPresent : true ∈ ((choices.bind channel).map outFlag).support := by
    rw [← optionalLaw, PMF.map_comp, actualFlag]
    exact present
  obtain ⟨outcome, outcomeSupport, outcomeFlag⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp outPresent
  obtain ⟨chosen, chosenSupport, chosenOutcome⟩ :=
    (PMF.mem_support_bind_iff _ _ _).mp outcomeSupport
  have choicePresent : true ∈ (choices.map flag).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨chosen, chosenSupport, (observed chosen chosenSupport outcome chosenOutcome).symm.trans
        outcomeFlag⟩
  have mapped := map_fiberPosterior_readout prior optional outFlag true (by
    rw [actualFlag]
    exact present)
  rw [actualFlag, optionalLaw] at mapped
  rw [fiberPosterior_bind_of_observation choices channel flag outFlag observed true
    choicePresent] at mapped
  have pureSome : selected.map optional = (selected.map read).map some := by
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro seed member
    have chosen := (mem_support_fiberPosterior present member).1
    have accepted : submitted seed = true := (Bool.and_eq_true_iff.mp chosen).1
    simp only [optional, accepted, ↓reduceIte, Function.comp_def]
  change selected.map optional = _ at mapped
  rw [pureSome] at mapped
  have rebuilt : ((fiberPosterior choices flag true).bind channel) =
      (sourcePrior.bind fun current =>
        ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count current.2).map
          (bindingObservers focal)).bind fun honest =>
            (noise (current.1.view focal)).map fun observed => ((current, honest), observed)).map
              some := by
    simp only [sourcePrior, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support _
    intro chosen member
    have chosenFlag := (mem_support_fiberPosterior choicePresent member).1
    have accepted : chosen.2 = true := (Bool.and_eq_true_iff.mp chosenFlag).1
    simp only [channel, accepted, ↓reduceIte, PMF.bind_map, Function.comp_def]
  rw [rebuilt] at mapped
  have unwrapped := congrArg (PMF.map fun outcome =>
    outcome.getD (read prior.support_nonempty.choose)) mapped
  simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at unwrapped
  have fullLaw := unwrapped.trans (PMF.map_id _)
  have base : selected.map (fun seed => (source seed, ghost seed)) = sourcePrior := by
    have projected := congrArg (PMF.map fun paired => paired.1.1) fullLaw
    simpa only [PMF.map_comp, Function.comp_def, read, PMF.map_bind, pmf_map_fun_const,
      PMF.bind_const, PMF.bind_pure] using projected
  rw [base]
  exact fullLaw

private theorem source_binding_graph_marginal
    (profile : graph.BehavioralProfile) (event : graph.EventId)
    (focal : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding focal payload)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ focal name payload)
    (prior : PMF ({source : Config Player L Γ // focal ∉ source.defaulted} ×
      {ghost : graph.Config // ghost.cut.Ready event ∧ ghost.defaulted = ∅}))
    (kernel : DecisionView focal Γ → PMF (Option (PublicationResult (L.Val payload))))
    (head : ∀ hidden ∈ prior.support, actionLaw profile hidden.2.1 event =
      (kernel (hidden.1.1.view focal)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice))
    (next : PMF (Config Player L ((name, .commitment focal payload) :: Γ) ×
      {ghost : graph.Config // ghost.cut.Ready event ∧ ghost.defaulted = ∅}))
    (marginal : next = prior.bind fun hidden => (kernel (hidden.1.1.view focal)).map
      fun choice => (commitSuccessor name guard hidden.1.1 choice, hidden.2)) :
    let chosen := fun source : Config Player L ((name, .commitment focal payload) :: Γ) =>
      OwnAction.binding focal name payload (source.view focal).history.getLast?
    let advance := fun (ghost : {ghost : graph.Config //
        ghost.cut.Ready event ∧ ghost.defaulted = ∅}) action =>
      ghost.1.complete event ghost.2.1
        (cast (congrArg EventField.Action binding.symm) action)
        (cast (congrArg EventField.Value binding.symm) (action.getD .failure))
    next.map (fun hidden => advance hidden.2 (chosen hidden.1)) =
      (prior.map Prod.snd).bind fun ghost => eventStep profile ghost.1 event ghost.2.1 := by
  intro chosen advance
  have remembered (source : {source : Config Player L Γ // focal ∉ source.defaulted})
      (action : Option (PublicationResult (L.Val payload))) :
      chosen (commitSuccessor name guard source.1 action) = action := by
    simp only [chosen, Config.view, commitSuccessor, source.2, ite_false,
      Function.update_self, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      OwnAction.binding_commit]
  rw [marginal, PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro hidden supported
  simp only [PMF.map_comp, Function.comp_def, remembered]
  rw [eventStep, head hidden supported, PMF.bind_map]
  have code : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind focal payload := by
    generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = typed
    cases typed
    rfl
  have active : focal ∉ hidden.2.1.defaulted := by rw [hidden.2.2.2]; simp
  change (kernel (hidden.1.1.view focal)).map _ = (kernel (hidden.1.1.view focal)).bind _
  simp only [PMF.map]
  apply bind_congr_on_support _
  intro choice _
  have law := commit_step hidden.2.1 event hidden.2.2.1 binding code choice
  simpa only [active, ite_false, advance, Function.comp_def] using law.symm

end Vegas

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem canonical_honest_binding_head_joint
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (clear : config.defaulted = ∅) (event : graph.EventId)
    (ordered : config.cut.IsPrefix event.val) (ready : config.cut.Ready event)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (submits : ∀ action ∈ (actionLaw profile config event).support,
      (graph.outputLayout event).Submitted action) (count : Nat) :
    let after := fun result => config.complete event ready
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result)
    let chosen := fun observed : graph.PublicObservation ×
        ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1) =>
      (cast (congrArg (fun field => Option field.Value) binding)
        ((observed.2 ⟨owner, different⟩).store (.inr event))).getD .failure
    (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1) config).map
        (fun final =>
          ((chosen (bindingObservers focal final), after (chosen (bindingObservers focal final))),
            bindingObservers focal final)) =
      (actionLaw profile config event).bind fun action => (config.step event ready action).bind
        fun next =>
          (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count next).map
            (fun final => (((cast (congrArg EventField.Action binding) action).getD .failure,
              next), bindingObservers focal final)) := by
  intro after chosen
  have least (other : graph.EventId) (otherReady : config.cut.Ready other) : event ≤ other := by
    apply Fin.le_iff_val_le_val.mpr
    by_contra smaller
    exact otherReady.1 ((ordered.2 other).mpr (by omega))
  rw [runPlan_canonical_succ profile count config ready.not_terminal event ready least,
    PMF.map_bind, eventStep, PMF.bind_bind]
  apply bind_congr_on_support _
  intro action selected
  apply bind_congr_on_support _
  intro next moved
  obtain ⟨result, actionEq, _clear, _path, _record, stored⟩ :=
    step_submitted_binding_frame config clear event ready owner payload binding action
      (submits action selected) next moved
  obtain ⟨value, _evaluated, rfl⟩ := PMF.support_map .. ▸ moved
  have valueEq : value = cast (congrArg EventField.Value binding.symm) result :=
    Option.some.inj ((config.complete_output_same event ready action value).symm.trans stored)
  have nextEq : config.complete event ready action value = after result := by
    rw [actionEq, valueEq]
  apply map_congr_on_support _
  intro final reached
  have path := runPlan_graph_steps (graph.policyPlan profile graph.canonicalScheduler) count
    (config.complete event ready action value) final reached
  have persisted := Config.Step.path_store_of_some path (.inr event)
    (cast (congrArg EventField.Value binding.symm) result) stored
  have actor : graph.actor? event = some owner :=
    EventCode.actor_eq_of_binding (graph.nodes event) binding
  have visible : graph.fieldVisibleTo owner (.inr event) :=
    EventCode.output_visible_of_actor (graph.nodes event) owner actor
  have viewed : (graph.playerObserve owner final).store (.inr event) =
      some (cast (congrArg EventField.Value binding.symm) result) := by
    change graph.playerStore owner final.store (.inr event) = _
    rw [graph.playerStore_of_visible owner final.store _ visible]
    exact persisted
  have castSome {left right : EventField Player L} (same : left = right) (value : right.Value) :
      cast (congrArg (fun field => Option field.Value) same)
        (some (cast (congrArg EventField.Value same.symm) value)) = some value := by
    cases same
    rfl
  have selectedResult : chosen (bindingObservers focal final) = result := by
    change (cast (congrArg (fun field => Option field.Value) binding)
      ((graph.playerObserve owner final).store (.inr event))).getD .failure = result
    rw [viewed, castSome binding result]
    rfl
  have castAction : (cast (congrArg EventField.Action binding) action).getD .failure = result := by
    rw [actionEq]
    simp only [cast_cast, cast_eq, Option.getD_some]
  exact Prod.ext (by rw [selectedResult, castAction]; exact Prod.ext rfl nextEq.symm) rfl

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem canonical_foreign_source_head_joint
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (clear : config.defaulted = ∅) (event : graph.EventId)
    (ordered : config.cut.IsPrefix event.val) (ready : config.cut.Ready event)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (submits : ∀ action ∈ (actionLaw profile config event).support,
      (graph.outputLayout event).Submitted action)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ owner name payload) (source : Config Player L Γ)
    (sourceHead : PMF (Option (PublicationResult (L.Val payload))))
    (head : actionLaw profile config event =
      sourceHead.map (fun action => cast (congrArg EventField.Action binding.symm) action))
    (count : Nat) :
    let after := fun result => config.complete event ready
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result)
    let chosen := fun observed : graph.PublicObservation ×
        ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1) =>
      (cast (congrArg (fun field => Option field.Value) binding)
        ((observed.2 ⟨owner, different⟩).store (.inr event))).getD .failure
    (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1) config).map
      (fun final =>
        ((commitSuccessor name guard source (some (chosen (bindingObservers focal final))),
          after (chosen (bindingObservers focal final))), bindingObservers focal final)) =
      sourceHead.bind fun action =>
        (config.step event ready (cast (congrArg EventField.Action binding.symm) action)).bind
          fun next =>
            (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count next).map
              fun final => ((commitSuccessor name guard source action, next),
                bindingObservers focal final) := by
  intro after chosen
  have graphJoint := canonical_honest_binding_head_joint profile config clear event ordered ready
    owner focal different payload binding submits count
  have mapped := congrArg (PMF.map fun pair =>
    ((commitSuccessor name guard source (some pair.1.1), pair.1.2), pair.2)) graphJoint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at mapped
  calc
    _ = _ := mapped
    _ = _ := by
      rw [head, PMF.bind_map]
      apply bind_congr_on_support _
      intro action supported
      have selected : cast (congrArg EventField.Action binding.symm) action ∈
          (actionLaw profile config event).support := by
        rw [head, PMF.mem_support_map_iff]
        exact ⟨action, supported, rfl⟩
      have submitted := EventField.submitted_cast binding _ (submits _ selected)
      simp only [cast_cast, cast_eq] at submitted ⊢
      cases action with
      | none => exact (Bool.false_ne_true submitted).elim
      | some result => simp only [Function.comp_def, cast_cast, cast_eq, Option.getD_some]

end Vegas

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem foreign_binding_source_head
    (setup : Setup (Player := Player) (L := L))
    (wholeProfile : BehavioralProfile setup.program)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (wholeProfile who))
    (focal owner : Player) (different : owner ≠ focal)
    {Γ : SourceCtx Player L} {names : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name names))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (source : Config Player L Γ)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile (.commit name owner fresh guard next)
      profile refs source.revelations source.registry embedding refsBefore rank)
    (config : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reach : config.Reachable inputs)
    (clean : config.NoBindingDefaults) (clear : config.defaulted = ∅)
    (checkpoint : SourceCheckpoint setup source refs rank config) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : setup.informationGraph.EventId := embedding.event index
    let binding : setup.informationGraph.outputLayout event = .binding owner payload :=
      by
        change outputLayout setup.program (embedding.event index) = _
        exact (embedding.layout_eq index).trans (by rfl)
    let reference :=
      setup.informationGraph.submitProfile (compileEventProfile setup.program wholeProfile)
    actionLaw (setup.informationGraph.prefixProfile (Function.update reference focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal))) config event =
      (commitKernel profile (source.view owner) (by
        change owner ∉ source.defaulted
        have status := congrArg DefaultHistory.defaulted checkpoint.defaults
        change config.defaulted = source.defaulted at status
        rw [← status, clear]
        simp)).map (fun choice => cast (congrArg EventField.Action binding.symm) choice) := by
  intro index event binding reference
  have eventRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have actor : setup.informationGraph.actor? event = some owner := by
    simpa [event, index, eventOwner?] using aligned.actorEq index
  have active : owner ∉ config.defaulted := by rw [clear]; simp
  have sourceActive : owner ∉ source.defaulted := by
    have status := congrArg DefaultHistory.defaulted checkpoint.defaults
    change config.defaulted = source.defaulted at status
    rwa [← status]
  have observation (who : Player) :
      setup.informationGraph.prefixObservation who event
        (setup.informationGraph.playerObserve who config) =
      setup.informationGraph.playerObserve who config :=
    (prefixObservation_playerObserve_of_prefix who event config
      (eventRank ▸ checkpoint.ordered) clean).trans
      (setup.informationGraph.normalizeObservation_playerObserve_of_rankOrdered who config
        (rankSort_history_of_reachable setup.informationGraph_total reach))
  have atObservation (policy : setup.informationGraph.BehavioralPolicy owner)
      (left right : setup.informationGraph.PlayerObservation owner) (same : left = right)
      (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted) :
      policy event actor left leftActive = policy event actor right rightActive := by
    cases same
    rfl
  have repaired : reference owner event actor
      (setup.informationGraph.playerObserve owner config) active =
      (compileEventProfile setup.program wholeProfile) owner event actor
        (setup.informationGraph.playerObserve owner config) active := by
    change setup.informationGraph.submitPolicy owner
      (compileEventProfile setup.program wholeProfile owner) event actor _ _ = _
    exact compileEventPolicy_submit_eq_of_prefix setup.program owner (wholeProfile owner)
      (submits owner) event config (eventRank ▸ checkpoint.ordered) actor active
  rw [actionLaw_of_actor _ _ actor, dite_eq_right active]
  change (Function.update reference focal (submittedFailurePolicy focal) owner) event actor
    (setup.informationGraph.prefixObservation owner event
      (setup.informationGraph.playerObserve owner config)) _ = _
  simp only [Function.update_of_ne different]
  apply (atObservation _ _ _ (observation owner) _ active).trans
  rw [repaired]
  exact eq_map_cast_of_cast_eq (congrArg EventField.Action binding) _ _
    (commit_head_policy_eq setup.program wholeProfile next profile refs source.revelations
      source.registry embedding refsBefore rank aligned config source.state checkpoint.agrees
      source.history checkpoint.history source.defaults checkpoint.defaults sourceActive actor)

end Vegas

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem completed_binding_historical_frame
    (relaxed : graph.RevealRelaxedOrdered)
    {inputs : graph.Inputs} (origin ghost final : graph.Config) (start : Nat)
    (originReach : origin.Reachable inputs) (originOrdered : origin.cut.IsPrefix start)
    (ghostPath : Relation.ReflTransGen Config.Step origin ghost)
    (actualPath : Relation.ReflTransGen Config.Step origin final)
    (focal : Player) (event : graph.EventId)
    (lower : start ≤ event.val) (owned : graph.actor? event = some focal)
    (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (ghostReady : ghost.cut.Ready event) (completed : event ∈ final.cut.completed)
    (bindings : ∀ prior : graph.EventId, start ≤ prior.val → prior.val < event.val →
      ∃ owner payload, graph.outputLayout prior = .binding owner payload)
    (priorOwn : ∀ prior : graph.EventId, prior.val < event.val →
      graph.actor? prior = some focal → completionOf final prior = completionOf ghost prior) :
    ∃ before : graph.Config, before.cut.Ready event ∧
      Relation.ReflTransGen Config.Step before final ∧
      graph.prefixObservation focal event (graph.playerObserve focal before) =
        graph.prefixObservation focal event (graph.playerObserve focal ghost) := by
  have pending : event ∉ origin.cut.completed := fun done => by
    have earlier := (originOrdered.2 event).mp done
    omega
  obtain ⟨before, next, ready, action, value, beforePath, moved, afterPath, _record, _output⟩ :=
    Config.Step.path_at_completion actualPath event pending completed
  have suffix : Relation.ReflTransGen Config.Step before final :=
    (Relation.ReflTransGen.single ⟨event, ready, action, moved⟩).trans afterPath
  refine ⟨before, ready, suffix, ?_⟩
  apply prefixObservation_playerObserve_of_binding_paths relaxed origin before ghost start
    originReach originOrdered beforePath ghostPath focal event owned notPublication ready ghostReady
    bindings
  intro prior earlier actor
  have previous : prior ∈ before.cut.completed := ready.2
    (relaxed.same_owner_predecessor prior event focal earlier actor owned)
  obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff before prior).mpr previous)
  exact found.trans ((Config.Step.path_completionOf_of_some suffix prior record found).symm.trans
    (priorOwn prior earlier actor))

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem native_focal_binding_graph_runUntil
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (focal : Player) {Γ : SourceCtx Player L} {names : Finset VarId}
    {name : VarId} {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ focal name payload)
    (next : SourceProgram Player L ((name, .commitment focal payload) :: Γ) (insert name names))
    (profile : BehavioralProfile (.commit name focal fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name focal fresh guard next))
    (event : (serviceGraph setup deps).EventId)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (owned : (serviceGraph setup deps).actor? event = some focal)
    (binding : (serviceGraph setup deps).outputLayout event = .binding focal payload)
    (reference : setup.informationGraph.BehavioralProfile) (count : Nat)
    {Seed Latent : Type} (prior : PMF Seed)
    (source : Seed → {source : Config Player L Γ // focal ∉ source.defaulted})
    (ghost : Seed → {ghost : setup.informationGraph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (latent : Seed → Latent)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (boundAt : (serviceGraph setup deps).EventId → Nat) (start finish : Nat)
    (bindings : ∀ node : (serviceGraph setup deps).EventId, start ≤ node.val →
      node.val < finish → ∃ owner kind,
        (serviceGraph setup deps).outputLayout node = .binding owner kind)
    (barrier : ∀ node : (serviceGraph setup deps).EventId, node.val = finish →
      ((serviceGraph setup deps).outputLayout node).IsPublic)
    (targetLate : event.val < finish)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (memberReference : Seed → (serviceGraph setup deps).BehavioralProfile)
    (memberSubmits : ∀ seed ∈ prior.support,
      (serviceGraph setup deps).SubmitsBindings (memberReference seed))
    (trace : ∀ seed ∈ prior.support, ∃ remaining,
      Nonempty (((serviceApplication setup deps duration leaks).protocol
        (serviceInitialLaw setup deps) horizon scheduler).Trace
          (some ⟨remaining, none, execution seed⟩)))
    (inside : ∀ seed ∈ prior.support, InBlock start finish (execution seed).application.config)
    (canonical : ∀ seed ∈ prior.support, ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (execution seed) actor ∧
        CanonicalSlotsUsed setup leaks (execution seed) actor)
    (lower : start ≤ event.val)
    (completes : CompletesPlay (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler)
    (origin nativeGhost : Seed → (serviceGraph setup deps).Config)
    (originReach : ∀ seed ∈ prior.support, ∃ inputs, (origin seed).Reachable inputs)
    (originOrdered : ∀ seed ∈ prior.support, (origin seed).cut.IsPrefix start)
    (currentPath : ∀ seed ∈ prior.support,
      Relation.ReflTransGen EventGraph.Config.Step (origin seed)
        (execution seed).application.config)
    (ghostPath : ∀ seed ∈ prior.support,
      Relation.ReflTransGen EventGraph.Config.Step (origin seed) (nativeGhost seed))
    (ghostKey : ∀ seed ∈ prior.support, runKey (nativeGhost seed) =
      runKey ((serviceGraph setup deps).fromSequentialConfig (ghost seed).1))
    (priorOwn : ∀ seed ∈ prior.support, ∀ node : (serviceGraph setup deps).EventId,
      node.val < event.val → (serviceGraph setup deps).actor? node = some focal →
      completionOf (execution seed).application.config node =
        completionOf ((serviceGraph setup deps).fromSequentialConfig (ghost seed).1) node)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, (ghost seed, latent seed)),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, (ghost seed, latent seed)))).bind fun hidden =>
        (noise (hidden.1.1.view focal)).map (fun observed => (hidden, observed)))
    (checkpoint : ∀ seed ∈ prior.support,
      SourceCheckpoint setup (source seed).1 refs event.val (ghost seed).1)
    (ghostReach : ∀ seed ∈ prior.support, ∃ inputs, (ghost seed).1.Reachable inputs)
    (ghostClean : ∀ seed ∈ prior.support, (ghost seed).1.NoBindingDefaults)
    (utility : setup.informationGraph.Config → ℝ)
    (phaseValue : Seed × (serviceApplication setup deps duration leaks).Execution → ℝ)
    (good : Config Player L ((name, .commitment focal payload) :: Γ) → Bool)
    (floor bound : ℝ) (utilityBound : ∀ final, |utility final| ≤ bound)
    (utilityFloor : ∀ final, floor ≤ utility final) :
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks boundAt turns
        (firstTurnTiming setup turns deps) (memberReference seed)) focal deviation
    let stop := fun final : (serviceApplication setup deps duration leaks).Execution =>
      event ∈ final.application.config.cut.completed
    let phase := fun seed => (serviceApplication setup deps duration leaks).runUntilHorizon
      scheduler (players seed) stop horizon (execution seed)
    let readChoice := fun final : (serviceApplication setup deps duration leaks).Execution =>
      OwnAction.binding focal name payload
        (decodeActionAt setup.program event final.application.config.history)
    let staged := prior.bind fun seed => (phase seed).map (fun final => (seed, final))
    let nextSource := fun
        (point : Seed × (serviceApplication setup deps duration leaks).Execution) =>
      commitSuccessor name guard (source point.1).1 (readChoice point.2)
    let nextGraph := fun point : Seed × (serviceApplication setup deps duration leaks).Execution =>
      (ghost point.1).1.complete event (ghost point.1).2.1
        (cast (congrArg EventField.Action binding.symm) (readChoice point.2))
        (cast (congrArg EventField.Value binding.symm) ((readChoice point.2).getD .failure))
    PayoffIntegrable staged phaseValue →
    (∀ point ∈ staged.support,
      good (nextSource point) = false → phaseValue point ≤ floor) →
    (∀ (kernel : DecisionView focal Γ → PMF (Option (PublicationResult (L.Val payload))))
      (nextNoise : DecisionView focal ((name, .commitment focal payload) :: Γ) → PMF _),
      (staged.map fun point => ((nextSource point, (ghost point.1, latent point.1)),
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal point.2)) =
      ((prior.map (fun seed => (source seed, (ghost seed, latent seed)))).bind fun hidden =>
        (kernel (hidden.1.1.view focal)).map fun action =>
          (commitSuccessor name guard hidden.1.1 action, hidden.2)).bind (fun hidden =>
            (nextNoise (hidden.1.view focal)).map fun observed => (hidden, observed)) →
      ∀ _present : true ∈ (staged.map (fun point => good (nextSource point))).support,
        ∃ policy : setup.informationGraph.BehavioralPolicy focal,
          expect (fiberPosterior staged (fun point => good (nextSource point)) true) phaseValue ≤
            expect ((fiberPosterior staged (fun point => good (nextSource point)) true).bind
              fun point => setup.informationGraph.runPlan
                (setup.informationGraph.policyPlan (Function.update reference focal policy)
                  setup.informationGraph.canonicalScheduler) count (nextGraph point)) utility) →
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect staged phaseValue ≤ expect (prior.bind fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update reference focal policy)
          setup.informationGraph.canonicalScheduler) (count + 1) (ghost seed).1) utility := by
  classical
  intro players stop phase readChoice staged nextSource nextGraph nativeIntegrable bad tail
  have notPublication : ¬ ((serviceGraph setup deps).outputLayout event).IsPublication := by
    rw [binding]
    exact fun impossible => impossible
  have coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution left) =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution right) →
      (phase left).map ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
        (phase right).map ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
    intro left leftSupported right rightSupported same
    obtain ⟨leftRemaining, ⟨leftTrace⟩⟩ := trace left leftSupported
    obtain ⟨rightRemaining, ⟨rightTrace⟩⟩ := trace right rightSupported
    have sameRecall := congrArg (fun traffic => traffic.2.2.1) same
    change (execution left).environmentRecall = (execution right).environmentRecall at sameRecall
    have sameLength := congrArg List.length sameRecall
    have leftBudget := (serviceApplication setup deps duration leaks).raw_trace_horizon
      (serviceInitialLaw setup deps) horizon scheduler leftTrace
    have rightBudget := (serviceApplication setup deps duration leaks).raw_trace_horizon
      (serviceInitialLaw setup deps) horizon scheduler rightTrace
    have rounds : leftRemaining = rightRemaining := by dsimp only at leftBudget rightBudget; omega
    have leftCount : horizon - (execution left).environmentRecall.length = leftRemaining := by
      dsimp only at leftBudget
      omega
    have rightCount : horizon - (execution right).environmentRecall.length = leftRemaining := by
      dsimp only at rightBudget
      omega
    change ((serviceApplication setup deps duration leaks).runUntil scheduler (players left)
      stop (horizon - (execution left).environmentRecall.length) (execution left)).map _ = _
    dsimp only [phase, ReactiveApplication.runUntilHorizon]
    rw [leftCount, rightCount]
    apply bindingBlock_stopped_traffic_congr relaxed scheduler boundAt start finish bindings barrier
      focal deviation stop (fun _ complete => complete event targetLate) _
      (memberReference left) (memberReference right) (memberSubmits left leftSupported)
      (memberSubmits right rightSupported) (execution left) (execution right) same
      (show ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some ⟨0 + leftRemaining, none, execution left⟩) by
          simpa only [Nat.zero_add] using leftTrace)
      (show ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some ⟨0 + leftRemaining, none, execution right⟩) from
          by simpa only [Nat.zero_add, rounds] using rightTrace)
      (inside left leftSupported) (inside right rightSupported)
      (canonical left leftSupported) (canonical right rightSupported)
    intro a b sameTraffic
    have samePublic := congrArg (fun value => value.2.2.2.2.2) sameTraffic
    change event ∈ a.application.config.cut.completed ↔ event ∈ b.application.config.cut.completed
    rw [cut_eq_of_publicView_eq samePublic]
  have frame : ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
      ∃ before : (serviceGraph setup deps).Config,
        before.cut.Ready event ∧
        Relation.ReflTransGen EventGraph.Config.Step before final.application.config ∧
        (serviceGraph setup deps).prefixObservation focal event
            ((serviceGraph setup deps).playerObserve focal before) =
          setup.informationGraph.prefixObservation focal event
            (setup.informationGraph.playerObserve focal (ghost seed).1) := by
    intro seed supported final reached
    let app := serviceApplication setup deps duration leaks
    let rounds := horizon - (execution seed).environmentRecall.length
    have reached' : final ∈ (app.runUntil scheduler (players seed) stop rounds
        (execution seed)).support := reached
    obtain ⟨remaining, ⟨currentTrace⟩⟩ := trace seed supported
    have budget := app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler
      currentTrace
    have remainingEq : remaining = rounds := by dsimp only [rounds] at *; omega
    have phasePath := reactive_runUntil_graph_steps (serviceTimeouts setup deps duration) leaks
      scheduler (players seed) stop rounds (execution seed) final reached'
    have completed : event ∈ final.application.config.cut.completed := by
      rcases app.runUntil_stopped scheduler (players seed) stop rounds (execution seed) final
        reached' with done | spent
      · exact done
      obtain ⟨used, within, history, counted⟩ := app.runUntil_runRounds scheduler (players seed)
        stop rounds (execution seed) final reached'
      have usedEq : used = rounds := by omega
      have traced : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
          (some ⟨0 + used, none, execution seed⟩) := by
        simpa only [remainingEq, usedEq, Nat.zero_add] using currentTrace
      obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup deps) horizon
        scheduler (players seed) 0 used (execution seed) final traced history
      have terminal := completes _ finalTrace (by exact ⟨rfl, rfl⟩)
      rw [terminal]
      exact Finset.mem_univ event
    have sameKey := ghostKey seed supported
    have orderedLift : ((serviceGraph setup deps).fromSequentialConfig
        (ghost seed).1).cut.IsPrefix event.val := (ghost seed).2.2.1
    have nativeOrdered : (nativeGhost seed).cut.IsPrefix event.val := by
      have cuts : (nativeGhost seed).cut =
          ((serviceGraph setup deps).fromSequentialConfig (ghost seed).1).cut :=
        congrArg Prod.fst sameKey
      rw [cuts]
      exact orderedLift
    have nativeReady : (nativeGhost seed).cut.Ready event := nativeOrdered.ready event.isLt
    have ownFinal : ∀ node : (serviceGraph setup deps).EventId,
        node.val < event.val → (serviceGraph setup deps).actor? node = some focal →
        completionOf final.application.config node = completionOf (nativeGhost seed) node := by
      intro node earlier actor
      have completedBefore := (nativeOrdered.2 node).mpr earlier
      obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff (nativeGhost seed) node).mpr completedBefore)
      have records := congrFun (congrArg (fun key => key.2.2) sameKey) node
      have currentRecord : completionOf (execution seed).application.config node = some record :=
        (priorOwn seed supported node earlier actor).trans (records.symm.trans found)
      exact (Config.Step.path_completionOf_of_some phasePath node record currentRecord).trans
        found.symm
    obtain ⟨inputs, originReached⟩ := originReach seed supported
    obtain ⟨before, ready, suffix, matching⟩ := completed_binding_historical_frame relaxed
      (origin seed) (nativeGhost seed) final.application.config start originReached
      (originOrdered seed supported) (ghostPath seed supported)
      ((currentPath seed supported).trans phasePath) focal event lower owned notPublication
      nativeReady completed
      (fun node lowerNode earlierNode => bindings node lowerNode (lt_trans earlierNode targetLate))
      ownFinal
    refine ⟨before, ready, suffix, matching.trans ?_⟩
    exact ((serviceGraph setup deps).prefixObservation_playerObserve_congr focal event
      (congrArg Prod.snd sameKey)).trans
      (fromSequentialConfig_prefixObservation focal event (ghost seed).1)
  obtain ⟨kernel, nextNoise, joint⟩ :=
    binding_source_fiber setup deps duration leaks focal guard
    refs event relaxed owned notPublication prior (fun seed => (source seed, (ghost seed,
      latent seed))) execution noise factor phase coupled (fun seed => (ghost seed).1)
      checkpoint ghostReach ghostClean frame
  have joint' : (staged.map fun point =>
      ((nextSource point, (ghost point.1, latent point.1)),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal point.2)) =
      ((prior.map (fun seed => (source seed, (ghost seed, latent seed)))).bind fun hidden =>
        (kernel (hidden.1.1.view focal)).map fun action =>
          (commitSuccessor name guard hidden.1.1 action, hidden.2)).bind (fun hidden =>
            (nextNoise (hidden.1.view focal)).map fun observed => (hidden, observed)) := by
    simpa only [staged, nextSource, readChoice, PMF.map_bind, PMF.map_comp,
      Function.comp_def] using joint
  obtain ⟨head, headLaw⟩ := exists_graph_binding_head setup setup.informationDependencies fresh
    guard next profile refs embedding event owned binding kernel reference
  let thin := fun current : {ghost : setup.informationGraph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅} =>
    (⟨current.1, current.2.1, current.2.2.2⟩ :
      {ghost : setup.informationGraph.Config // ghost.cut.Ready event ∧ ghost.defaulted = ∅})
  let before := prior.map (fun seed => (source seed, thin (ghost seed)))
  let after := staged.map (fun point => (nextSource point, thin (ghost point.1)))
  have retained : after = before.bind fun hidden => (kernel (hidden.1.1.view focal)).map
      fun choice => (commitSuccessor name guard hidden.1.1 choice, hidden.2) := by
    have projected := congrArg (PMF.map fun paired =>
      (paired.1.1, thin paired.1.2.1)) joint'
    simpa only [after, before, PMF.map_comp, PMF.map_bind, PMF.bind_map, PMF.bind_bind,
      Function.comp_def, pmf_map_fun_const, PMF.bind_pure, PMF.pure_bind, PMF.map,
      PMF.bind_const] using projected
  have currentHead : ∀ hidden ∈ before.support,
      actionLaw (Function.update reference focal head) hidden.2.1 event =
        (kernel (hidden.1.1.view focal)).map
          (fun action => cast (congrArg EventField.Action binding.symm) action) := by
    intro hidden member
    obtain ⟨seed, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact headLaw (source seed).1 (ghost seed).1 (checkpoint seed supported) (source seed).2
  have graphLaw := source_binding_graph_marginal (Function.update reference focal head) event
    focal payload binding guard before kernel currentHead after retained
  have remembered (seed) (action : Option (PublicationResult (L.Val payload))) :
      OwnAction.binding focal name payload
        ((commitSuccessor name guard (source seed).1 action).view focal).history.getLast? =
      action := by
    simp only [Config.view, commitSuccessor, (source seed).2, ite_false, Function.update_self,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, OwnAction.binding_commit]
  let current := fun seed =>
    (⟨(ghost seed).1, (ghost seed).2.2.1⟩ :
      {config : setup.informationGraph.Config // config.cut.IsPrefix event.val})
  have marginal : staged.map nextGraph = (prior.map current).bind fun config =>
      eventStep (Function.update reference focal head) config.1 event
        (config.2.ready event.isLt) := by
    simpa only [after, before, current, thin, PMF.map_comp, PMF.bind_map, Function.comp_def,
      nextSource, nextGraph, remembered] using graphLaw
  exact canonical_owned_expected_continuation reference focal event head count prior current staged
    nextGraph marginal utility phaseValue (fun point => good (nextSource point)) floor bound
    utilityBound utilityFloor nativeIntegrable bad (tail kernel nextNoise joint')

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def nativeSourceContinuation
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank point) :=
  frame.refs.CoversPrefix setup.program rank →
  ∀ {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L frame.Γ)
    (ghost : Seed → setup.informationGraph.Config),
    (∀ seed ∈ prior.support, @(source seed).revelations = @frame.source.revelations) →
    (∀ seed ∈ prior.support, (source seed).registry = frame.source.registry) →
    (∀ seed ∈ prior.support, SourceCheckpoint setup (source seed) frame.refs rank (ghost seed)) →
    (∀ seed ∈ prior.support, ∃ inputs, (ghost seed).Reachable inputs) →
    (∀ seed ∈ prior.support, ∃ history : setup.intendedProtocol.History,
      history.state = some (frame.lift (ProtocolState.entry frame.program (source seed)))) →
    ∀ (members : Seed → (serviceGraph setup deps).BehavioralProfile),
    (∀ seed ∈ prior.support, (serviceGraph setup deps).SubmitsBindings (members seed)) →
    (∀ seed ∈ prior.support, ∀ owner node actor observation active, rank ≤ node.val →
      members seed owner node actor observation active =
        reference owner node actor observation active) →
    ∀ (execution : Seed → (serviceApplication setup deps duration leaks).Execution),
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening
          ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation
    (∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler (players seed) rank (execution seed)) →
    (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
    (∀ seed ∈ prior.support, runKey (execution seed).application.config =
      runKey ((serviceGraph setup deps).fromSequentialConfig (ghost seed))) →
    ∀ (noise : DecisionView focal frame.Γ → PMF _),
    (prior.map (fun seed => ((source seed, ghost seed),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        (noise (hidden.1.view focal)).map (fun observed => (hidden, observed))) →
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (prior.bind fun seed =>
        (serviceApplication setup deps duration leaks).runToHorizon scheduler (players seed)
          horizon (execution seed)) nativePayoff ≤
        expect (prior.bind fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed))
          sourcePayoff

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def residualAt
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry)
    (ghost : setup.informationGraph.Config)
    (checkpoint : SourceCheckpoint setup source frame.refs rank ghost) :
    SourceResidual setup profile rank ghost where
  Γ := frame.Γ
  names := frame.names
  program := frame.program
  residualProfile := frame.residualProfile
  source := source
  refs := frame.refs
  embedding := frame.embedding
  refsBefore := frame.refsBefore
  aligned := by rw [revelations, registry]; exact frame.aligned
  admitted := frame.admitted
  authentic := frame.authentic
  supports := frame.supports
  disclosing := frame.disclosing
  lift := frame.lift
  commutes := frame.commutes
  steps := frame.steps
  injective := frame.injective
  transport := by
    intro more store history defaults
    rw [registry, revelations]
    exact frame.transport more store history defaults
  checkpoint := checkpoint

private def residualCommitTail
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name owner fresh guard next)
    (choice : Option (PublicationResult (L.Val payload)))
    (after : setup.informationGraph.Config) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.commit name owner fresh guard next) := programEq ▸ frame.embedding
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : setup.informationGraph.outputLayout (embedding.event index) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let refs := frame.refs.cons (name := name) ⟨.inr (embedding.event index), outputEq⟩
    SourceCheckpoint setup (commitSuccessor name guard frame.source choice) refs (rank + 1) after →
      SourceResidual setup profile (rank + 1) after := by
  rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at fresh guard next programEq choice ⊢
  cases programEq
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
      .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
  let tailRefs : ContextRefs (graphLayout setup.program)
      ((name, .commitment owner payload) :: Γ) :=
    refs.cons ⟨.inr (embedding.event index), outputEq⟩
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
    refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
  have tailAligned : CompiledPolicySuffix setup.program profile next
      (afterCommit residualProfile) tailRefs
      (commitSuccessor name guard source choice).revelations
      (commitSuccessor name guard source choice).registry
      tailEmbedding tailBefore (rank + 1) := by
    simpa only [commitSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
      aligned.commitTail setup.program profile fresh guard next residualProfile refs
        source.revelations source.registry embedding refsBefore rank
  intro tailCheckpoint
  refine {
    Γ := _, names := _, program := next, residualProfile := afterCommit residualProfile,
    source := commitSuccessor name guard source choice, refs := tailRefs,
    embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
    admitted := fun whole who => (admitted whole who).2,
    authentic := fun whole who => authentic whole who,
    supports := fun whole who => (supports whole who).2,
    disclosing := fun whole who => disclosing whole who,
    lift := lift ∘ Sum.inr,
    commutes := fun state => ?_, steps := fun state joint => ?_,
    injective := injective.comp Sum.inr_injective,
    transport := fun more store history defaults => ?_,
    checkpoint := tailCheckpoint }
  · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_commit_tail,
      PMF.map_comp]
  · rw [Function.comp_apply, steps]
    change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
    rw [PMF.map_comp]
  · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
      decodeSourcePrefix?_commit, Option.map_map]
    rfl

private def representativeCommitTail
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name owner fresh guard next) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.commit name owner fresh guard next) := programEq ▸ frame.embedding
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : setup.informationGraph.outputLayout (embedding.event index) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let atRank : (embedding.event index).val = rank := by
      rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
        aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
        transport, checkpoint⟩
      dsimp only at fresh guard next programEq ⊢
      cases programEq
      simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
    let ready : origin.cut.Ready (embedding.event index) := by
      have ordered := frame.checkpoint.ordered
      rw [← atRank] at ordered
      exact ordered.ready (embedding.event index).isLt
    SourceResidual setup profile (rank + 1)
      (origin.complete (embedding.event index) ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (some (.failure : PublicationResult (L.Val payload))))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) .failure)) := by
  rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at fresh guard next programEq ⊢
  cases programEq
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
      .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have atRank : (embedding.event index).val = rank := by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : origin.cut.Ready (embedding.event index) := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready (embedding.event index).isLt
  let choice : Option (PublicationResult (L.Val payload)) := some .failure
  have decoded : decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice) := by
    have lookup := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
    simpa [index, outputEq, decodeEventAction] using lookup
  have tailCheckpoint := checkpoint.commit (native := configState origin) name guard
    (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index) choice decoded
  have stored : (commitSuccessor name guard source choice).state.get .here = .failure := by
    by_cases inactive : owner ∈ source.defaulted <;>
      simp [commitSuccessor, choice, inactive]
  rw [stored] at tailCheckpoint
  let original : SourceResidual setup profile rank origin := {
    Γ := Γ, names := names, program := .commit name owner fresh guard next,
    residualProfile := residualProfile, source := source, refs := refs, embedding := embedding,
    refsBefore := refsBefore, aligned := aligned, admitted := admitted, authentic := authentic,
    supports := supports, disclosing := disclosing, lift := lift, commutes := commutes,
    steps := steps, injective := injective, transport := transport, checkpoint := checkpoint }
  exact residualCommitTail original fresh guard next rfl choice _ tailCheckpoint

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def nativeBindingContinuation
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (start finish : Nat) {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank point) : Prop :=
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let placeholder := setup.informationGraph.prefixProfile
    (Function.update reference focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal))
  start ≤ rank → rank ≤ finish → finish ≤ G.order.eventCount →
  frame.refs.CoversPrefix setup.program rank →
  (∀ event : G.EventId, start ≤ event.val → event.val < finish →
    ∃ owner payload, G.outputLayout event = .binding owner payload) →
  (∀ event : G.EventId, event.val = finish → (G.outputLayout event).IsPublic) →
  ∀ {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L frame.Γ)
    (ghost table : Seed → setup.informationGraph.Config)
    (members : Seed → G.BehavioralProfile)
    (anchor execution : Seed → app.Execution) (budget used : Seed → Nat)
    (nativeGhost : Seed → G.Config),
  let players := fun seed => Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed))))
      focal deviation
  (∀ seed ∈ prior.support, @(source seed).revelations = @frame.source.revelations) →
  (∀ seed ∈ prior.support, (source seed).registry = frame.source.registry) →
  (∀ seed ∈ prior.support,
    SourceCheckpoint setup (source seed) frame.refs rank (ghost seed)) →
  (∀ seed ∈ prior.support, ∃ inputs, (ghost seed).Reachable inputs) →
  (∀ seed ∈ prior.support, ∃ history : setup.intendedProtocol.History,
    history.state = some (frame.lift (ProtocolState.entry frame.program (source seed)))) →
  (∀ seed ∈ prior.support, G.SubmitsBindings (members seed)) →
  (∀ seed ∈ prior.support, ∀ owner event actor observation active, finish ≤ event.val →
    members seed owner event actor observation active =
      reference owner event actor observation active) →
  (∀ seed ∈ prior.support, ∀ event : G.EventId, start ≤ event.val → event.val < finish →
    ∀ owner payload (binding : G.outputLayout event = .binding owner payload), owner ≠ focal →
    ∃ result : PublicationResult (L.Val payload),
      completionOf (table seed) event = some (EventGraph.completion setup.informationGraph event
        (some (cast (congrArg EventField.Action binding.symm) (some result)))
        (cast (congrArg EventField.Value binding.symm) result)) ∧
      (table seed).outputs event =
        some (cast (congrArg EventField.Value binding.symm) result) ∧
      ∀ observation active,
        members seed owner event
          (EventCode.actor_eq_of_binding (G.nodes event) binding) observation active =
            PMF.pure (cast (congrArg EventField.Action binding.symm) (some result))) →
  (∀ seed ∈ prior.support, anchor seed ∈
    (app.roundsFrom (serviceInitialLaw setup deps) scheduler (players seed)
      (anchor seed).environmentRecall.length).support) →
  (∀ seed ∈ prior.support, Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon
    scheduler).Trace (some ⟨budget seed, none, anchor seed⟩))) →
  (∀ seed ∈ prior.support, (anchor seed).application.config.cut.IsPrefix start) →
  (∀ seed ∈ prior.support, (anchor seed).application.config.defaulted = ∅) →
  (∀ seed ∈ prior.support, ∀ owner, owner ≠ focal →
    OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
      CanonicalSlotsUsed setup leaks (anchor seed) owner ∧
      OwnFreshCalls setup leaks bound (anchor seed) owner ∧
      OneCallPerEvent setup leaks (anchor seed) owner) →
  (∀ seed ∈ prior.support, ActivationsAnswered setup leaks (anchor seed)) →
  (∀ seed ∈ prior.support, ∀ event : G.EventId, start ≤ event.val →
    Untouched setup leaks event (anchor seed)) →
  (∀ seed ∈ prior.support, used seed ≤ budget seed) →
  (∀ seed ∈ prior.support, execution seed ∈
    (app.runRounds scheduler (players seed) (used seed) (anchor seed)).support) →
  (∀ seed ∈ prior.support, (execution seed).application.config.defaulted = ∅) →
  (∀ seed ∈ prior.support, InBlock start finish (execution seed).application.config) →
  (∀ seed ∈ prior.support, ∀ event : G.EventId, finish ≤ event.val →
    Untouched setup leaks event (execution seed)) →
  (∀ seed ∈ prior.support,
    Relation.ReflTransGen EventGraph.Config.Step (anchor seed).application.config
      (nativeGhost seed)) →
  (∀ seed ∈ prior.support, runKey (nativeGhost seed) =
    runKey (G.fromSequentialConfig (ghost seed))) →
  (∀ seed ∈ prior.support, ∀ event : G.EventId, event.val < rank →
    G.actor? event = some focal →
      completionOf (execution seed).application.config event =
        completionOf (G.fromSequentialConfig (ghost seed)) event) →
  (∀ seed ∈ prior.support, ∀ event : G.EventId, rank ≤ event.val → event.val < finish →
    G.actor? event = some focal → event ∉ (execution seed).application.config.cut.completed) →
  ∀ (noise : DecisionView focal frame.Γ → PMF _),
  (prior.map (fun seed =>
    (((source seed, ghost seed), bindingObservers focal (table seed)),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed)))) =
    (prior.map (fun seed => (source seed, ghost seed))).bind (fun current =>
      (setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan placeholder setup.informationGraph.canonicalScheduler)
        (finish - rank) current.2).bind fun selected =>
          (noise (current.1.view focal)).map fun observed =>
            ((current, bindingObservers focal selected), observed)) →
  ∃ policy : setup.informationGraph.BehavioralPolicy focal,
    expect (prior.bind fun seed =>
      app.runToHorizon scheduler (players seed) horizon (execution seed)) nativePayoff ≤
      expect (prior.bind fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed))
        sourcePayoff

end Vegas

namespace Vegas.EventGraph

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem canonical_foreign_expected_continuation
    (reference : graph.BehavioralProfile) (focal owner : Player) (different : owner ≠ focal)
    (event : graph.EventId) (owned : graph.actor? event = some owner) (count : Nat)
    {Seed NextSeed : Type} (prior : PMF Seed)
    (source : Seed → {config : graph.Config // config.cut.IsPrefix event.val})
    (nextPrior : PMF NextSeed) (nextSource : NextSeed → graph.Config)
    (marginal : nextPrior.map nextSource = (prior.map source).bind fun config =>
      eventStep reference config.1 event (config.2.ready event.isLt))
    (utility : graph.Config → ℝ) (nativeValue : NextSeed → ℝ)
    (tail : ∃ policy : graph.BehavioralPolicy focal,
      expect nextPrior nativeValue ≤ expect (nextPrior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) count (nextSource seed)) utility) :
    ∃ policy : graph.BehavioralPolicy focal,
      expect nextPrior nativeValue ≤ expect (prior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) (source seed).1) utility := by
  obtain ⟨policy, comparison⟩ := tail
  have first (config : {config : graph.Config // config.cut.IsPrefix event.val}) :
      graph.runPlan (graph.policyPlan (Function.update reference focal policy)
          graph.canonicalScheduler) (count + 1) config.1 =
        (eventStep reference config.1 event (config.2.ready event.isLt)).bind fun next =>
          graph.runPlan (graph.policyPlan (Function.update reference focal policy)
            graph.canonicalScheduler) count next := by
    have ready : config.1.cut.Ready event := config.2.ready event.isLt
    have least (other : graph.EventId) (otherReady : config.1.cut.Ready other) : event ≤ other := by
      apply Fin.le_iff_val_le_val.mpr
      by_contra smaller
      exact otherReady.1 ((config.2.2 other).mpr (by omega))
    rw [runPlan_canonical_succ _ count config.1 ready.not_terminal event ready least]
    have same : actionLaw (Function.update reference focal policy) config.1 event =
        actionLaw reference config.1 event := by
      rw [actionLaw_of_actor _ _ owned, actionLaw_of_actor _ _ owned]
      simp only [Function.update_of_ne different]
    simp only [eventStep, same]
  have law : (prior.bind fun seed => graph.runPlan
      (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
        (count + 1) (source seed).1) =
      nextPrior.bind (fun seed => graph.runPlan
        (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
          count (nextSource seed)) := by
    calc
      _ = (prior.map source).bind (fun config => graph.runPlan
          (graph.policyPlan (Function.update reference focal policy) graph.canonicalScheduler)
            (count + 1) config.1) := by rw [PMF.bind_map]; rfl
      _ = ((prior.map source).bind fun config =>
          eventStep reference config.1 event (config.2.ready event.isLt)).bind (fun next =>
            graph.runPlan (graph.policyPlan (Function.update reference focal policy)
              graph.canonicalScheduler) count next) := by
        rw [PMF.bind_bind]
        apply bind_congr_on_support _
        intro config _
        exact first config
      _ = _ := by rw [← marginal, PMF.bind_map]; rfl
  exact ⟨policy, by rw [law]; exact comparison⟩

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem foreign_binding_shadow_law
    (profile : graph.BehavioralProfile) (event : graph.EventId)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) (count : Nat)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ owner name payload)
    {Seed Traffic : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (ghost : Seed → {ghost : graph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → graph.Config) (traffic : Seed → Traffic)
    (noise : DecisionView focal Γ → PMF Traffic)
    (sourceHead : Config Player L Γ → PMF (Option (PublicationResult (L.Val payload))))
    (head : ∀ seed ∈ prior.support, actionLaw profile (ghost seed).1 event =
      (sourceHead (source seed)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice))
    (submits : ∀ seed ∈ prior.support, ∀ action ∈
      (actionLaw profile (ghost seed).1 event).support,
        (graph.outputLayout event).Submitted action)
    (law : prior.map (fun seed =>
        ((source seed, (ghost seed, bindingObservers focal (table seed))), traffic seed)) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1)
          hidden.2.1).map (bindingObservers focal)).bind fun honest =>
            (noise (hidden.1.view focal)).map fun observed =>
              ((hidden.1, (hidden.2, honest)), observed)) :
    let chosen := fun observed : graph.PublicObservation ×
        ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1) =>
      (cast (congrArg (fun field => Option field.Value) binding)
        ((observed.2 ⟨owner, different⟩).store (.inr event))).getD .failure
    let advance := fun (current : {ghost : graph.Config // ghost.cut.Ready event ∧
        ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅}) result =>
      current.1.complete event current.2.1
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result)
    let nextSource := fun seed => commitSuccessor name guard (source seed)
      (some (chosen (bindingObservers focal (table seed))))
    let nextGhost := fun seed => advance (ghost seed) (chosen (bindingObservers focal (table seed)))
    let nextBase := (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
      (sourceHead hidden.1).bind fun choice =>
        (hidden.2.1.step event hidden.2.2.1
          (cast (congrArg EventField.Action binding.symm) choice)).map fun next =>
            (commitSuccessor name guard hidden.1 choice, next)
    prior.map (fun seed =>
      (((nextSource seed, nextGhost seed), bindingObservers focal (table seed)), traffic seed)) =
      nextBase.bind fun hidden =>
        ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count hidden.2).map
          (bindingObservers focal)).bind fun honest =>
            (noise ((hidden.1.view focal).back false)).map fun observed =>
              ((hidden, honest), observed) := by
  intro chosen advance nextSource nextGhost nextBase
  let project := fun pair :
      (Config Player L Γ ×
        ({ghost : graph.Config // ghost.cut.Ready event ∧ ghost.cut.IsPrefix event.val ∧
          ghost.defaulted = ∅} × (graph.PublicObservation ×
            ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1))))
          × Traffic =>
    (((commitSuccessor name guard pair.1.1 (some (chosen pair.1.2.2)),
      advance pair.1.2.1 (chosen pair.1.2.2)), pair.1.2.2), pair.2)
  have projected := congrArg (PMF.map project) law
  simp only [PMF.map_comp, Function.comp_def] at projected
  calc
    _ = _ := projected
    _ = _ := by
      simp only [PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
        Function.comp_def, nextBase]
      apply bind_congr_on_support _
      intro seed supported
      have sourceJoint := canonical_foreign_source_head_joint profile (ghost seed).1
        (ghost seed).2.2.2 event (ghost seed).2.2.1 (ghost seed).2.1 owner focal different
        payload binding (submits seed supported) guard (source seed) (sourceHead (source seed))
        (head seed supported) count
      let retain := fun observed :
          (Config Player L ((name, .commitment owner payload) :: Γ) × graph.Config) ×
            (graph.PublicObservation ×
              ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1)) =>
        (noise ((source seed).view focal)).map fun current => (observed, current)
      have withNoise := congrArg (fun distribution => distribution.bind retain) sourceJoint
      simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def, retain] at withNoise
      have rolled (choice : Option (PublicationResult (L.Val payload))) :
          ((commitSuccessor name guard (source seed) choice).view focal).back false =
            (source seed).view focal := by
        simpa only [different, decide_false] using
          back_commit_view focal name guard (source seed) choice
      simp only [rolled]
      calc
        _ = ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1)
            (ghost seed).1).map (bindingObservers focal)).bind (fun honest =>
              (noise ((source seed).view focal)).map fun current =>
                (((commitSuccessor name guard (source seed) (some (chosen honest)),
                  advance (ghost seed) (chosen honest)), honest), current)) := by
          simp only [PMF.bind_map, Function.comp_def, project]
        _ = _ := by
          simpa only [PMF.bind_map, Function.comp_def, chosen, advance] using withNoise

end Vegas

namespace Vegas.EventGraph

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem binding_head_support_of_observers
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (clear : config.defaulted = ∅) (event : graph.EventId)
    (ordered : config.cut.IsPrefix event.val) (ready : config.cut.Ready event)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (submits : ∀ action ∈ (actionLaw profile config event).support,
      (graph.outputLayout event).Submitted action) (count : Nat)
    (honest : graph.PublicObservation ×
      ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1))
    (selected : honest ∈ ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
      (count + 1) config).map (bindingObservers focal)).support) :
    let chosen := (cast (congrArg (fun field => Option field.Value) binding)
      ((honest.2 ⟨owner, different⟩).store (.inr event))).getD .failure
    some chosen ∈ ((actionLaw profile config event).map
      (fun action => cast (congrArg EventField.Action binding) action)).support := by
  intro chosen
  obtain ⟨final, finalSupport, finalRead⟩ := (PMF.mem_support_map_iff _ _ _).mp selected
  let chosenOf := fun observed : graph.PublicObservation ×
      ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1) =>
    (cast (congrArg (fun field => Option field.Value) binding)
      ((observed.2 ⟨owner, different⟩).store (.inr event))).getD .failure
  let after := fun result => config.complete event ready
    (cast (congrArg EventField.Action binding.symm) (some result))
    (cast (congrArg EventField.Value binding.symm) result)
  have joint := canonical_honest_binding_head_joint profile config clear event ordered ready
    owner focal different payload binding submits count
  dsimp only at joint
  have supported : ((chosenOf (bindingObservers focal final),
      after (chosenOf (bindingObservers focal final))), bindingObservers focal final) ∈
      ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1)
        config).map (fun outcome =>
          ((chosenOf (bindingObservers focal outcome),
            after (chosenOf (bindingObservers focal outcome))),
              bindingObservers focal outcome))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, finalSupport, rfl⟩
  rw [joint] at supported
  obtain ⟨action, actionSupport, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨next, _, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp rest
  obtain ⟨last, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
  have chosenEq := congrArg (fun paired => paired.1.1) same
  change (cast (congrArg EventField.Action binding) action).getD .failure =
    chosenOf (bindingObservers focal final) at chosenEq
  have submitted := EventField.submitted_cast binding _ (submits action actionSupport)
  cases typed : cast (congrArg EventField.Action binding) action with
  | none =>
    change (cast (congrArg EventField.Action binding) action).isSome = true at submitted
    rw [typed] at submitted
    exact (Bool.false_ne_true submitted).elim
  | some result =>
    have resultEq : result = chosen := by
      simpa only [typed, Option.getD_some, chosenOf, finalRead] using chosenEq
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨action, actionSupport, typed.trans (congrArg some resultEq)⟩

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem foreign_binding_choice_supported
    (profile : graph.BehavioralProfile) (event : graph.EventId)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) (count : Nat)
    {Γ : SourceCtx Player L} {Traffic Seed : Type} (prior : PMF Seed)
    (source : Seed → Config Player L Γ)
    (ghost : Seed → {ghost : graph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → graph.Config) (traffic : Seed → Traffic)
    (noise : DecisionView focal Γ → PMF Traffic)
    (sourceHead : Config Player L Γ → PMF (Option (PublicationResult (L.Val payload))))
    (head : ∀ seed ∈ prior.support, actionLaw profile (ghost seed).1 event =
      (sourceHead (source seed)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice))
    (submits : ∀ seed ∈ prior.support, ∀ action ∈
      (actionLaw profile (ghost seed).1 event).support,
        (graph.outputLayout event).Submitted action)
    (law : prior.map (fun seed =>
        ((source seed, (ghost seed, bindingObservers focal (table seed))), traffic seed)) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (count + 1)
          hidden.2.1).map (bindingObservers focal)).bind fun honest =>
            (noise (hidden.1.view focal)).map fun observed =>
              ((hidden.1, (hidden.2, honest)), observed))
    (seed : Seed) (supported : seed ∈ prior.support) :
    some ((cast (congrArg (fun field => Option field.Value) binding)
      (((bindingObservers focal (table seed)).2 ⟨owner, different⟩).store
        (.inr event))).getD .failure) ∈ (sourceHead (source seed)).support := by
  have observed : ((source seed, (ghost seed, bindingObservers focal (table seed))),
      traffic seed) ∈ (prior.map (fun seed =>
        ((source seed, (ghost seed, bindingObservers focal (table seed))),
          traffic seed))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, supported, rfl⟩
  rw [law] at observed
  obtain ⟨hidden, _, observed⟩ := (PMF.mem_support_bind_iff _ _ _).mp observed
  obtain ⟨honest, honestSupport, observed⟩ := (PMF.mem_support_bind_iff _ _ _).mp observed
  obtain ⟨extra, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  have sameBase : hidden = (source seed, ghost seed) :=
    Prod.ext (congrArg (fun pair => pair.1.1) same)
      (congrArg (fun pair => pair.1.2.1) same)
  subst hidden
  have sameHonest : honest = bindingObservers focal (table seed) :=
    congrArg (fun pair => pair.1.2.2) same
  subst honest
  have picked := binding_head_support_of_observers profile (ghost seed).1 (ghost seed).2.2.2
    event (ghost seed).2.2.1 (ghost seed).2.1 owner focal different payload binding
      (submits seed supported) count (bindingObservers focal (table seed)) honestSupport
  rw [head seed supported, PMF.map_comp] at picked
  simp only [Function.comp_def, cast_cast, cast_eq] at picked
  change _ ∈ ((sourceHead (source seed)).map id).support at picked
  rwa [PMF.map_id] at picked

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem foreign_binding_shadow_continuation
    (reference : graph.BehavioralProfile) (event : graph.EventId)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (tableCount continuationCount : Nat)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ owner name payload)
    {Seed Traffic : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (ghost : Seed → {ghost : graph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → graph.Config) (traffic : Seed → Traffic)
    (noise : DecisionView focal Γ → PMF Traffic)
    (sourceHead : Config Player L Γ → PMF (Option (PublicationResult (L.Val payload))))
    (utility : graph.Config → ℝ) (nativeValue : Seed → ℝ) :
    let prescribed := graph.prefixProfile reference
    let placeholder := graph.prefixProfile (Function.update reference focal
      (submittedFailurePolicy (graph := graph) focal))
    (∀ seed ∈ prior.support, actionLaw placeholder (ghost seed).1 event =
      (sourceHead (source seed)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice)) →
    (∀ seed ∈ prior.support, ∀ action ∈
      (actionLaw placeholder (ghost seed).1 event).support,
        (graph.outputLayout event).Submitted action) →
    (prior.map (fun seed =>
        ((source seed, (ghost seed, bindingObservers focal (table seed))), traffic seed)) =
      (prior.map (fun seed => (source seed, ghost seed))).bind (fun hidden =>
        ((graph.runPlan (graph.policyPlan placeholder graph.canonicalScheduler)
          (tableCount + 1) hidden.2.1).map (bindingObservers focal)).bind fun honest =>
            (noise (hidden.1.view focal)).map fun observed =>
              ((hidden.1, (hidden.2, honest)), observed))) →
    let chosen : Seed → PublicationResult (L.Val payload) := fun seed =>
      (cast (congrArg (fun field : EventField Player L => Option field.Value) binding)
        (show Option (graph.outputLayout event).Value from
          ((bindingObservers focal (table seed)).2 ⟨owner, different⟩).store
            (.inr event))).getD .failure
    let nextSource := fun seed => commitSuccessor name guard (source seed) (some (chosen seed))
    let nextGhost := fun seed => (ghost seed).1.complete event (ghost seed).2.1
      (cast (congrArg EventField.Action binding.symm) (some (chosen seed)))
      (cast (congrArg EventField.Value binding.symm) (chosen seed))
    (∀ _selected : ∀ seed ∈ prior.support,
        some (chosen seed) ∈ (sourceHead (source seed)).support,
      (prior.map (fun seed =>
        (((nextSource seed, nextGhost seed), bindingObservers focal (table seed)), traffic seed)) =
        (prior.map (fun seed => (nextSource seed, nextGhost seed))).bind (fun hidden =>
          ((graph.runPlan (graph.policyPlan placeholder graph.canonicalScheduler)
            tableCount hidden.2).map (bindingObservers focal)).bind fun honest =>
              (noise ((hidden.1.view focal).back false)).map fun observed =>
                ((hidden, honest), observed))) →
      ∃ policy : graph.BehavioralPolicy focal,
        expect prior nativeValue ≤ expect (prior.bind fun seed =>
          graph.runPlan (graph.policyPlan (Function.update prescribed focal policy)
            graph.canonicalScheduler) continuationCount (nextGhost seed)) utility) →
    ∃ policy : graph.BehavioralPolicy focal,
      expect prior nativeValue ≤ expect (prior.bind fun seed =>
        graph.runPlan (graph.policyPlan (Function.update prescribed focal policy)
          graph.canonicalScheduler) (continuationCount + 1) (ghost seed).1) utility := by
  intro prescribed placeholder head submits factor chosen nextSource nextGhost tail
  have selected : ∀ seed ∈ prior.support,
      some (chosen seed) ∈ (sourceHead (source seed)).support := by
    intro seed supported
    exact foreign_binding_choice_supported placeholder event owner focal different payload
      binding tableCount prior source ghost table traffic noise sourceHead head submits factor
        seed supported
  have joint := foreign_binding_shadow_law placeholder event owner focal different payload binding
    tableCount guard prior source ghost table traffic noise sourceHead head submits factor
  dsimp only at joint
  let nextBase := (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
    (sourceHead hidden.1).bind fun choice =>
      (hidden.2.1.step event hidden.2.2.1
        (cast (congrArg EventField.Action binding.symm) choice)).map fun next =>
          (commitSuccessor name guard hidden.1 choice, next)
  have base : prior.map (fun seed => (nextSource seed, nextGhost seed)) = nextBase := by
    have projected := congrArg (PMF.map fun pair => pair.1.1) joint
    simpa only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const,
      PMF.bind_const, PMF.bind_pure, nextSource, nextGhost, chosen, nextBase] using projected
  have fullLaw : (prior.map (fun seed =>
      (((nextSource seed, nextGhost seed), bindingObservers focal (table seed)), traffic seed))) =
      (prior.map (fun seed => (nextSource seed, nextGhost seed))).bind (fun hidden =>
        ((graph.runPlan (graph.policyPlan placeholder graph.canonicalScheduler)
          tableCount hidden.2).map (bindingObservers focal)).bind fun honest =>
            (noise ((hidden.1.view focal).back false)).map fun observed =>
              ((hidden, honest), observed)) := by
    rw [base]
    exact joint
  obtain ⟨policy, comparison⟩ := tail selected fullLaw
  have actor : graph.actor? event = some owner :=
    EventCode.actor_eq_of_binding (graph.nodes event) binding
  have sameHead (config : graph.Config) :
      actionLaw placeholder config event = actionLaw prescribed config event := by
    rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
    split
    · rfl
    · change (Function.update reference focal (submittedFailurePolicy focal) owner) event actor
        (graph.prefixObservation owner event (graph.playerObserve owner config)) _ = _
      simp only [Function.update_of_ne different]
      rfl
  let current := fun seed => (⟨(ghost seed).1, (ghost seed).2.2.1⟩ :
    {config : graph.Config // config.cut.IsPrefix event.val})
  have marginal : prior.map nextGhost = (prior.map current).bind fun config =>
      eventStep prescribed config.1 event (config.2.ready event.isLt) := by
    have projected := congrArg (PMF.map Prod.snd) base
    calc
      _ = nextBase.map Prod.snd := by
        simpa only [PMF.map_comp, Function.comp_def] using projected
      _ = _ := by
        simp only [nextBase, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
        apply bind_congr_on_support _
        intro seed supported
        rw [eventStep, ← sameHead, head seed supported, PMF.bind_map]
        apply bind_congr_on_support _
        intro choice _
        exact PMF.map_id _
  exact canonical_foreign_expected_continuation prescribed focal owner different event actor
    continuationCount prior current prior nextGhost marginal utility nativeValue
      ⟨policy, comparison⟩

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem foreign_binding_source_successor
    {setup : Setup (Player := Player) (L := L)} [Finite Player]
    (wellFormed : setup.WellFormed)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank origin)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name owner fresh guard next)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry)
    (ghost : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs)
    (checkpoint : SourceCheckpoint setup source frame.refs rank ghost)
    (history : setup.intendedProtocol.History)
    (historyAt : history.state =
      some (frame.lift (ProtocolState.entry frame.program source)))
    (active : owner ∉ source.defaulted) (result : PublicationResult (L.Val payload)) :
    let profile : BehavioralProfile (.commit name owner fresh guard next) :=
      programEq ▸ frame.residualProfile
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.commit name owner fresh guard next) := programEq ▸ frame.embedding
    let lift : ProtocolState (.commit name owner fresh guard next) →
        ProtocolState setup.program := programEq ▸ frame.lift
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : setup.informationGraph.EventId := embedding.event index
    let binding : setup.informationGraph.outputLayout event = .binding owner payload :=
      (embedding.layout_eq index).trans rfl
    some result ∈ (commitKernel profile (source.view owner) active).support →
      ∃ ready : ghost.cut.Ready event,
      let after := ghost.complete event ready
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result)
      SourceCheckpoint setup (commitSuccessor name guard source (some result))
          (frame.refs.cons ⟨.inr event, binding⟩) (rank + 1) after ∧
        after.Reachable inputs ∧ after.defaulted = ∅ ∧
        ∃ nextHistory : setup.intendedProtocol.History,
          nextHistory.state = some (lift (.inr (ProtocolState.entry next
            (commitSuccessor name guard source (some result))))) := by
  rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh guard next programEq source revelations registry checkpoint historyAt ⊢
  cases programEq
  let _ := Fintype.ofFinite Player
  intro selected
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : setup.informationGraph.EventId := embedding.event index
  have binding : setup.informationGraph.outputLayout event = .binding owner payload :=
    (embedding.layout_eq index).trans rfl
  have atRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : ghost.cut.Ready event := by
    have current : ghost.cut.Ready ⟨rank, atRank ▸ event.isLt⟩ :=
      checkpoint.ordered.ready (atRank ▸ event.isLt)
    exact (show event = ⟨rank, atRank ▸ event.isLt⟩ from Fin.ext atRank).symm ▸ current
  let after := ghost.complete event ready
    (cast (congrArg EventField.Action binding.symm) (some result))
    (cast (congrArg EventField.Value binding.symm) result)
  let residual : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank ghost :=
    residualAt ⟨Γ, names, .commit name owner fresh guard next, residualProfile, original, refs,
      embedding, refsBefore, aligned, admitted, authentic, supports, disclosing, lift, commutes,
      steps, injective, transport, originalCheckpoint⟩ source revelations registry ghost checkpoint
  have atGhost : history.state = sourceServicePrefix? setup rank ghost :=
    historyAt.trans residual.decode.symm
  have clear : ghost.defaulted = ∅ :=
    residual.clear_of_intended_history wellFormed history atGhost
  have sourceStep : Sum.inr (ProtocolState.entry next
      (commitSuccessor name guard source (some result))) ∈
      (ProtocolState.behavioralStateStep (.commit name owner fresh guard next) residualProfile
        (ProtocolState.entry (.commit name owner fresh guard next) source)).support := by
    change Sum.inr (ProtocolState.entry next
      (commitSuccessor name guard source (some result))) ∈
        (ProtocolState.behavioralStateStep (.commit name owner fresh guard next)
          residualProfile (.inl source)).support
    have activeView : owner ∉ (source.view owner).defaulted := active
    rw [ProtocolState.behavioralStateStep_commit_entry, dite_eq_right activeView]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, selected, rfl⟩
  obtain ⟨nextHistory, nextHistoryAt⟩ := residual.intendedHistory_of_step intended target agrees
    history atGhost _ sourceStep
  have eventRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventField.Action binding.symm) (some result)) =
        some (.commit owner name payload (some result)) := by
    simpa [index, event, binding, decodeEventAction] using aligned.actionEq index
      (cast (congrArg EventField.Action binding.symm) (some result))
  have nextCheckpoint := checkpoint.commit (native := configState ghost) name guard event eventRank
    ready binding (fun ref => refsBefore ref index) (some result) decoded
  have stored : (commitSuccessor name guard source (some result)).state.get .here = result := by
    simp only [commitSuccessor, active, ite_false, Env.get, Env.cons, Option.getD_some]
  rw [stored] at nextCheckpoint
  have code : cast (congrArg (EventCode setup.informationGraph.layout) binding)
      (setup.informationGraph.nodes event) = .bind owner payload := by
    generalize cast (congrArg (EventCode setup.informationGraph.layout) binding)
      (setup.informationGraph.nodes event) = typed
    cases typed
    rfl
  have graphStep : after ∈ (ghost.step event ready
      (cast (congrArg EventField.Action binding.symm) (some result))).support := by
    have status : ghost.defaulted = source.defaulted :=
      congrArg DefaultHistory.defaulted checkpoint.defaults
    have law := commit_step ghost event ready binding code (some result)
    simp only [status, active, ite_false, Option.getD_some] at law
    rw [law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have nextClear : after.defaulted = ∅ := by
    have status := congrArg DefaultHistory.defaulted nextCheckpoint.defaults
    change after.defaulted = (commitSuccessor name guard source (some result)).defaulted at status
    have oldStatus : ghost.defaulted = source.defaulted :=
      congrArg DefaultHistory.defaulted checkpoint.defaults
    rw [status, commitSuccessor_defaulted_of_accepted, ← oldStatus, clear]
  exact ⟨ready, nextCheckpoint, Config.Step.path_reachable
    (Relation.ReflTransGen.single ⟨event, ready, _, graphStep⟩) reachable,
      nextClear, nextHistory, nextHistoryAt⟩

end Vegas

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem fromSequential_complete
    (config : graph.sequentialize.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (liftedReady : (graph.fromSequentialConfig config).cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    graph.fromSequentialConfig (config.complete event ready action value) =
      (graph.fromSequentialConfig config).complete event liftedReady action value := by
  rfl

private theorem binding_ghost_path_successor
    (origin native : graph.Config) (source : graph.sequentialize.Config)
    (path : Relation.ReflTransGen Config.Step origin native)
    (same : runKey native = runKey (graph.fromSequentialConfig source))
    (clear : source.defaulted = ∅) (event : graph.EventId) (ready : source.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    ∃ next : graph.Config, Relation.ReflTransGen Config.Step origin next ∧
      runKey next = runKey (graph.fromSequentialConfig (source.complete event ready
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result))) := by
  have liftedReady : (graph.fromSequentialConfig source).cut.Ready event := by
    refine ⟨ready.1, ?_⟩
    intro prior predecessor
    exact ready.2 ((EventOrder.sequential.mem_predecessors prior event).mpr
      (graph.order.predecessor_lt predecessor))
  have cuts : native.cut = (graph.fromSequentialConfig source).cut := congrArg Prod.fst same
  have nativeReady : native.cut.Ready event := cuts.symm ▸ liftedReady
  have nativeClear : native.defaulted = ∅ :=
    (defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) same)).trans
      ((graph.fromSequentialConfig_defaulted source).trans clear)
  have active : owner ∉ native.defaulted := by rw [nativeClear]; simp
  have code : cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode graph.layout) binding) (graph.nodes event) = typed
    cases typed
    rfl
  let action := cast (congrArg EventField.Action binding.symm) (some result)
  let value := cast (congrArg EventField.Value binding.symm) result
  let next := native.complete event nativeReady action value
  have step : native.step event nativeReady action = PMF.pure next := by
    rw [native.step_eq_map_of_code event nativeReady binding (.bind owner payload) code
      (some result) (PMF.pure result) (by
        simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right active,
          EventCode.eval?, Option.getD_some]), PMF.pure_map]
  refine ⟨next, path.tail ⟨event, nativeReady, action, ?_⟩, ?_⟩
  · rw [step]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [fromSequential_complete source event ready liftedReady]
    exact runKey_complete_congr same event nativeReady liftedReady action value

end Vegas.EventGraph

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem foreign_binding_native_frame_successor
    (origin native current : graph.Config) (source : graph.sequentialize.Config)
    (path : Relation.ReflTransGen Config.Step origin native)
    (same : runKey native = runKey (graph.fromSequentialConfig source))
    (clear : source.defaulted = ∅) (event : graph.EventId) (ready : source.cut.Ready event)
    (owner focal : Player) (different : owner ≠ focal) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload)) (finish : Nat)
    (priorOwn : ∀ node : graph.EventId, node.val < event.val → graph.actor? node = some focal →
      completionOf current node = completionOf (graph.fromSequentialConfig source) node)
    (futureOwn : ∀ node : graph.EventId, event.val ≤ node.val → node.val < finish →
      graph.actor? node = some focal → node ∉ current.cut.completed) :
    let after := source.complete event ready
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result)
    ∃ next : graph.Config, Relation.ReflTransGen Config.Step origin next ∧
      runKey next = runKey (graph.fromSequentialConfig after) ∧
      (∀ node : graph.EventId, node.val < event.val + 1 → graph.actor? node = some focal →
        completionOf current node = completionOf (graph.fromSequentialConfig after) node) ∧
      ∀ node : graph.EventId, event.val + 1 ≤ node.val → node.val < finish →
        graph.actor? node = some focal → node ∉ current.cut.completed := by
  intro after
  obtain ⟨next, nextPath, nextKey⟩ := binding_ghost_path_successor origin native source path same
    clear event ready owner payload binding result
  refine ⟨next, nextPath, nextKey, ?_, ?_⟩
  · intro node earlier owned
    have other : node ≠ event := by
      intro equal
      have actor : graph.actor? event = some owner :=
        EventCode.actor_eq_of_binding (graph.nodes event) binding
      rw [equal, actor] at owned
      exact different (Option.some.inj owned)
    have lower : node.val < event.val := by
      have unequal : node.val ≠ event.val := fun equal => other (Fin.ext equal)
      omega
    calc
      completionOf current node = completionOf (graph.fromSequentialConfig source) node :=
        priorOwn node lower owned
      _ = completionOf (graph.fromSequentialConfig after) node := by
        have liftedReady : (graph.fromSequentialConfig source).cut.Ready event := by
          refine ⟨ready.1, ?_⟩
          intro before predecessor
          exact ready.2 ((EventOrder.sequential.mem_predecessors before event).mpr
            (graph.order.predecessor_lt predecessor))
        rw [show graph.fromSequentialConfig after = _ from
          fromSequential_complete source event ready liftedReady _ _, completionOf_complete,
          Function.update_of_ne other]
  · intro node lower upper owned
    exact futureOwn node (by omega) upper owned

end Vegas.EventGraph

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeBindingContinuation_foreign
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    [Finite Player] (wellFormed : setup.WellFormed)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (sourceSubmits : ∀ who, SourceProgram.SubmitsBindings setup.program
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target who))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : setup.informationGraph.BehavioralProfile)
    (referenceEq : reference = setup.informationGraph.submitProfile (compileEventProfile
      setup.program (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target)))
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (nativeBound : ℝ) (boundedNative : ∀ final, |nativePayoff final| ≤ nativeBound)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (start finish : Nat) {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank point)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name owner fresh guard next)
    (different : owner ≠ focal) (below : rank < finish)
    (tail : nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff start finish
        (representativeCommitTail frame fresh guard next programEq)) :
    nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff start finish frame := by
  classical
  rcases frame with ⟨Γ, names, program, profile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh guard next programEq tail ⊢
  cases programEq
  let frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank point := {
    Γ := Γ, names := names, program := .commit name owner fresh guard next,
    residualProfile := profile, source := original, refs := refs, embedding := embedding,
    refsBefore := refsBefore, aligned := aligned, admitted := admitted, authentic := authentic,
    supports := supports, disclosing := disclosing, lift := lift, commutes := commutes,
    steps := steps, injective := injective, transport := transport,
    checkpoint := originalCheckpoint }
  let tailFrame := representativeCommitTail frame fresh guard next rfl
  change nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
    (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff start finish tailFrame at tail
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : setup.informationGraph.EventId := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have binding : setup.informationGraph.outputLayout event = .binding owner payload :=
    (embedding.layout_eq index).trans rfl
  let placeholder := setup.informationGraph.prefixProfile (Function.update reference focal
    (submittedFailurePolicy (graph := setup.informationGraph) focal))
  intro lower upper bounded covered bindings barrier Seed prior source ghost table members anchor
    execution budget used nativeGhost players revelations registry checkpoint ghostReach history
    submits future fixed anchorSupported trace anchorOrdered anchorClear discipline answered
    untouched counted supported clear inside currentUntouched ghostPath ghostKey priorOwn futureOwn
    noise factor
  let supportedPrior := pmfToSubtype prior (fun seed member => member)
  have supportedAll (seed : {seed : Seed // seed ∈ prior.support}) :
      seed ∈ supportedPrior.support := by
    have found : seed.1 ∈ (supportedPrior.map Subtype.val).support := by
      rw [map_val_pmfToSubtype]
      exact seed.2
    obtain ⟨other, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp found
    exact (Subtype.ext equal : other = seed) ▸ member
  let readSource := fun seed : {seed : Seed // seed ∈ prior.support} => source seed.1
  have cleanGhost (seed : {seed : Seed // seed ∈ prior.support}) :
      (ghost seed.1).defaulted = ∅ := by
    let current := residualAt frame (source seed.1) (revelations seed.1 seed.2)
      (registry seed.1 seed.2) (ghost seed.1) (checkpoint seed.1 seed.2)
    obtain ⟨h, atHistory⟩ := history seed.1 seed.2
    exact current.clear_of_intended_history wellFormed h (atHistory.trans current.decode.symm)
  have cleanSource (seed : {seed : Seed // seed ∈ prior.support}) :
      (source seed.1).defaulted = ∅ := by
    have status : (ghost seed.1).defaulted = (source seed.1).defaulted :=
      congrArg DefaultHistory.defaulted (checkpoint seed.1 seed.2).defaults
    exact status.symm.trans (cleanGhost seed)
  let currentGhost := fun seed : {seed : Seed // seed ∈ prior.support} =>
    (⟨ghost seed.1, by
      have ordered := (checkpoint seed.1 seed.2).ordered
      rw [← eventRank] at ordered
      exact ordered.ready event.isLt, by
      simpa only [eventRank] using (checkpoint seed.1 seed.2).ordered, cleanGhost seed⟩ :
      {config : setup.informationGraph.Config // config.cut.Ready event ∧
        config.cut.IsPrefix event.val ∧ config.defaulted = ∅})
  let sourceHead := fun config : Config Player L Γ =>
    if inactive : owner ∈ config.defaulted then PMF.pure none
    else commitKernel profile (config.view owner) inactive
  have head : ∀ seed ∈ supportedPrior.support,
      actionLaw placeholder (currentGhost seed).1 event =
        (sourceHead (readSource seed)).map
          (fun choice => cast (congrArg EventField.Action binding.symm) choice) := by
    intro seed _
    obtain ⟨input, reach⟩ := ghostReach seed.1 seed.2
    have sourceActive : owner ∉ (source seed.1).defaulted := by rw [cleanSource seed]; simp
    have alignment : CompiledPolicySuffix setup.program
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
        (.commit name owner fresh guard next) profile refs (source seed.1).revelations
        (source seed.1).registry embedding refsBefore rank := by
      rw [revelations seed.1 seed.2, registry seed.1 seed.2]
      exact aligned
    have exactHead := foreign_binding_source_head setup _ sourceSubmits focal owner different
      fresh guard next profile (source seed.1) refs embedding refsBefore rank alignment
        (ghost seed.1) reach (Config.NoBindingDefaults.of_clear (cleanGhost seed))
        (cleanGhost seed) (checkpoint seed.1 seed.2)
    simpa only [placeholder, referenceEq, sourceHead, readSource,
      dite_eq_right sourceActive, currentGhost] using exactHead
  have submitting : ∀ seed ∈ supportedPrior.support, ∀ action ∈
      (actionLaw placeholder (currentGhost seed).1 event).support,
        (setup.informationGraph.outputLayout event).Submitted action := by
    intro seed _ action selected
    have global : setup.informationGraph.SubmitsBindings placeholder := by
      apply EventGraph.SubmitsBindings.prefix
      exact EventGraph.SubmitsBindings.update setup.informationGraph
        (by rw [referenceEq]; exact submitsBindings_submitProfile setup.informationGraph _)
        focal _ (setup.informationGraph.policySubmitsBindings_submitPolicy focal _)
    have actor : setup.informationGraph.actor? event = some owner :=
      EventCode.actor_eq_of_binding _ binding
    have active : owner ∉ (currentGhost seed).1.defaulted := by
      rw [(currentGhost seed).2.2.2]
      simp
    rw [actionLaw_of_actor _ _ actor, dite_eq_right active] at selected
    exact global owner event actor (setup.informationGraph.playerObserve owner
      (currentGhost seed).1) active action selected
  have countEq : finish - (rank + 1) + 1 = finish - rank := by omega
  let forget := fun {Traffic : Type} (pair :
      (Config Player L Γ ×
        ({config : setup.informationGraph.Config // config.cut.Ready event ∧
          config.cut.IsPrefix event.val ∧ config.defaulted = ∅} ×
            (setup.informationGraph.PublicObservation ×
              ((who : {who : Player // who ≠ focal}) →
                setup.informationGraph.PlayerObservation who.1)))) ×
        Traffic) =>
      (((pair.1.1, pair.1.2.1.1), pair.1.2.2), pair.2)
  have factorTyped : supportedPrior.map (fun seed =>
      ((readSource seed, (currentGhost seed, bindingObservers focal (table seed.1))),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed.1))) =
      (supportedPrior.map (fun seed => (readSource seed, currentGhost seed))).bind (fun hidden =>
        ((setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
          setup.informationGraph.canonicalScheduler) (finish - (rank + 1) + 1) hidden.2.1).map
            (bindingObservers focal)).bind fun honest =>
              (noise (hidden.1.view focal)).map fun observed =>
                ((hidden.1, (hidden.2, honest)), observed)) := by
    have priorEq : supportedPrior.map Subtype.val = prior := map_val_pmfToSubtype _ _
    have restricted := factor
    rw [← priorEq] at restricted
    simp only [PMF.map_comp, PMF.bind_map, Function.comp_def] at restricted
    apply pmf_map_injective (f := forget) (by
      intro left right same
      apply Prod.ext
      · apply Prod.ext
        · exact congrArg (fun pair => pair.1.1.1) same
        · apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun pair => pair.1.1.2) same
          · exact congrArg (fun pair => pair.1.2) same
      · exact congrArg (fun pair => pair.2) same)
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, PMF.bind_bind,
      Function.comp_def, forget, currentGhost, readSource, countEq, placeholder] using restricted
  let nativeValue := fun seed : {seed : Seed // seed ∈ prior.support} =>
    expect (app.runToHorizon scheduler (players seed.1) horizon (execution seed.1)) nativePayoff
  obtain ⟨policy, comparison⟩ := foreign_binding_shadow_continuation reference event owner focal
    different payload binding (finish - (rank + 1)) (eventCount next) guard supportedPrior
    readSource currentGhost (fun seed => table seed.1)
    (fun seed => (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
      (execution seed.1)) noise sourceHead sourcePayoff nativeValue head submitting factorTyped
      (by
        intro selected nextFactor
        let chosen := fun seed : {seed : Seed // seed ∈ prior.support} =>
          (cast (congrArg (fun field : EventField Player L => Option field.Value) binding)
            (((bindingObservers focal (table seed.1)).2 ⟨owner, different⟩).store
              (.inr event))).getD .failure
        let nextSource := fun seed =>
          commitSuccessor name guard (source seed.1) (some (chosen seed))
        let nextGhost := fun seed => (currentGhost seed).1.complete event (currentGhost seed).2.1
          (cast (congrArg EventField.Action binding.symm) (some (chosen seed)))
          (cast (congrArg EventField.Value binding.symm) (chosen seed))
        have sourceFacts (seed : {seed : Seed // seed ∈ prior.support}) :
            SourceCheckpoint setup (nextSource seed) tailFrame.refs (rank + 1) (nextGhost seed) ∧
              (∃ inputs, (nextGhost seed).Reachable inputs) ∧
              ∃ h : setup.intendedProtocol.History,
                h.state = some (tailFrame.lift (ProtocolState.entry next (nextSource seed))) := by
          obtain ⟨input, reach⟩ := ghostReach seed.1 seed.2
          obtain ⟨h, hAt⟩ := history seed.1 seed.2
          have sourceActive : owner ∉ (source seed.1).defaulted := by rw [cleanSource seed]; simp
          have chosenSupport : some (chosen seed) ∈
              (commitKernel profile ((source seed.1).view owner) sourceActive).support := by
            have fromTable := selected seed (supportedAll seed)
            simpa only [sourceHead, readSource, dite_eq_right sourceActive] using fromTable
          obtain ⟨ready, cp, reached, _empty, nextHistory, nextHistoryAt⟩ :=
            foreign_binding_source_successor wellFormed intended target agrees frame fresh guard
              next rfl (source seed.1) (revelations seed.1 seed.2) (registry seed.1 seed.2)
                (ghost seed.1) reach (checkpoint seed.1 seed.2) h hAt sourceActive (chosen seed)
                  chosenSupport
          exact ⟨cp, ⟨input, reached⟩, nextHistory, nextHistoryAt⟩
        choose nextNative nextPath nextKey nextOwn nextPending using fun seed :
            {seed : Seed // seed ∈ prior.support} =>
          foreign_binding_native_frame_successor (anchor seed.1).application.config
            (nativeGhost seed.1) (execution seed.1).application.config (ghost seed.1)
            (ghostPath seed.1 seed.2) (ghostKey seed.1 seed.2) (cleanGhost seed) event
            (currentGhost seed).2.1 owner focal different payload binding (chosen seed) finish
              (fun node earlier actor => priorOwn seed.1 seed.2 node
                (by simpa only [eventRank] using earlier) actor)
              (fun node lower upper actor => futureOwn seed.1 seed.2 node
                (by simpa only [eventRank] using lower) upper actor)
        have tailComparison : ∃ policy : setup.informationGraph.BehavioralPolicy focal,
            expect (supportedPrior.bind fun seed => app.runToHorizon scheduler
              (players seed.1) horizon (execution seed.1)) nativePayoff ≤
            expect (supportedPrior.bind fun seed => setup.informationGraph.runPlan
              (setup.informationGraph.policyPlan (Function.update
                (setup.informationGraph.prefixProfile reference) focal policy)
                  setup.informationGraph.canonicalScheduler) (eventCount next) (nextGhost seed))
              sourcePayoff := by
          apply tail (noise := fun
            (view : DecisionView focal ((name, .commitment owner payload) :: Γ)) =>
              noise (view.back false)) (by omega) (by omega) bounded
            (ContextRefs.CoversPrefix.cons setup.program (name := name)
              (cell := .commitment owner payload) covered ⟨.inr event, binding⟩ event rfl
              eventRank) bindings barrier supportedPrior nextSource nextGhost
            (fun seed => table seed.1) (fun seed => members seed.1) (fun seed => anchor seed.1)
            (fun seed => execution seed.1) (fun seed => budget seed.1) (fun seed => used seed.1)
            nextNative
          · intro seed _
            change @(commitSuccessor name guard (source seed.1) (some (chosen seed))).revelations =
              @(commitSuccessor name guard original (some .failure)).revelations
            simp only [commitSuccessor, revelations seed.1 seed.2]
          · intro seed _
            change (commitSuccessor name guard (source seed.1) (some (chosen seed))).registry =
              (commitSuccessor name guard original (some .failure)).registry
            simp only [commitSuccessor, registry seed.1 seed.2]
          · intro seed _; exact (sourceFacts seed).1
          · intro seed _; exact (sourceFacts seed).2.1
          · intro seed _; exact (sourceFacts seed).2.2
          · intro seed _; exact submits seed.1 seed.2
          · intro seed _; exact future seed.1 seed.2
          · intro seed _; exact fixed seed.1 seed.2
          · intro seed _; exact anchorSupported seed.1 seed.2
          · intro seed _; exact trace seed.1 seed.2
          · intro seed _; exact anchorOrdered seed.1 seed.2
          · intro seed _; exact anchorClear seed.1 seed.2
          · intro seed _; exact discipline seed.1 seed.2
          · intro seed _; exact answered seed.1 seed.2
          · intro seed _; exact untouched seed.1 seed.2
          · intro seed _; exact counted seed.1 seed.2
          · intro seed _; exact supported seed.1 seed.2
          · intro seed _; exact clear seed.1 seed.2
          · intro seed _; exact inside seed.1 seed.2
          · intro seed _; exact currentUntouched seed.1 seed.2
          · intro seed _; exact nextPath seed
          · intro seed _; exact nextKey seed
          · intro seed _ node earlier actor
            exact nextOwn seed node (by simpa only [eventRank] using earlier) actor
          · intro seed _ node lower upper actor
            exact nextPending seed node (by simpa only [eventRank] using lower) upper actor
          · simpa only [nextSource, nextGhost, readSource, chosen, PMF.bind_map,
              Function.comp_def] using nextFactor
        obtain ⟨tailPolicy, tailComparison⟩ := tailComparison
        rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ boundedNative)]
          at tailComparison
        exact ⟨tailPolicy, tailComparison⟩)
  refine ⟨policy, ?_⟩
  have nativeEquality : expect supportedPrior nativeValue =
      expect (prior.bind fun seed => app.runToHorizon scheduler (players seed)
        horizon (execution seed)) nativePayoff := by
    rw [← expect_bind_tower supportedPrior _ nativePayoff
      (payoffIntegrable_of_bounded _ _ boundedNative)]
    congr 1
    calc
      _ = (supportedPrior.map Subtype.val).bind (fun seed =>
          app.runToHorizon scheduler (players seed) horizon (execution seed)) := by
        rw [PMF.bind_map]
        rfl
      _ = _ := by rw [map_val_pmfToSubtype]
  rw [nativeEquality] at comparison
  have sourceEquality : (supportedPrior.bind fun seed => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount next + 1)
            (currentGhost seed).1) =
      prior.bind (fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount next + 1) (ghost seed)) := by
    calc
      _ = (supportedPrior.map Subtype.val).bind (fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
              setup.informationGraph.canonicalScheduler) (eventCount next + 1) (ghost seed)) := by
        rw [PMF.bind_map]
        rfl
      _ = _ := by rw [map_val_pmfToSubtype]
  simpa only [eventCount, sourceEquality] using comparison

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem SourceResidual.intendedHistory_of_debtFree_actor_step
    {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} (wellFormed : setup.WellFormed)
    (event : setup.informationGraph.EventId) {ghost : setup.informationGraph.Config}
    (residual : SourceResidual setup profile event.val ghost)
    (history : setup.intendedProtocol.History)
    (historyAt : history.state = sourceServicePrefix? setup event.val ghost)
    (focal : Player) (owned : setup.informationGraph.actor? event = some focal)
    (active : focal ∉ ghost.defaulted)
    (action : setup.informationGraph.Action event) (choice : OwnAction Player L)
    (decodedAction : decodeEventAction setup.program event action = some choice)
    (after : ProtocolState residual.program)
    (selected : after ∈ (ProtocolState.step residual.program
      (ProtocolState.entry residual.program residual.source)
      (fun who => if who = focal then some choice else none)).support)
    (debtFree : ¬ setup.OwesFailureState focal (some (residual.lift after))) :
    ∃ next : setup.intendedProtocol.History, next.state = some (residual.lift after) := by
  classical
  let point := residual.lift (ProtocolState.entry residual.program residual.source)
  let joint := fun who => if who = focal then some choice else none
  have decoded : sourceServicePrefix? setup event.val ghost = some point := residual.decode
  have atHistory : history.state = some point := historyAt.trans decoded
  have ownerLaw : eventOwner? setup.program event = some focal := by
    rw [eventOwner?_eq_actor]
    exact owned
  have actors (who : Player) :
      ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
        some focal := by
    have actor := decodeSourcePrefix?_actor who event.val setup.program _ _ _ _ ghost.store
      (decodeHistory setup.program ghost.history) ghost.defaults point decoded event.isLt
    have ghostActive : focal ∉ ghost.defaults.defaulted := active
    exact actor.trans (Option.filter_eq_some_iff.mpr
      ⟨ownerLaw, by simpa only [decide_eq_true_eq] using ghostActive⟩)
  have running : ¬ setup.intendedProtocol.terminal history.state := by
    rw [atHistory]
    exact ProtocolState.not_terminal_of_actor focal focal setup.program point (actors focal)
  let admission := CommitmentInterface.forfeiture setup.program
  have available (who : Player) : choice ∈ ProtocolView.available who setup.program admission
      (ProtocolState.observe who setup.program point) :=
    decodeSourcePrefix?_available who event.val setup.program _ _ _ _ ghost.store
      (decodeHistory setup.program ghost.history) ghost.defaults point decoded event.isLt
      action choice decodedAction
  have legal : (setup.executionProtocol admission).Legal history.state joint := by
    apply ExecutionProtocol.legal_of_legalOption (E := setup.executionProtocol admission) running
    intro who
    by_cases same : who = focal
    · subst who
      rw [show joint focal = some choice by simp only [joint, ↓reduceIte]]
      change _ ∧ _
      rw [atHistory]
      exact ⟨actors focal, available focal⟩
    · rw [show joint who = none by simp only [joint, same, ↓reduceIte]]
      change ¬ (setup.executionProtocol admission).active history.state who
      rw [atHistory]
      change ProtocolView.actor who setup.program
        (ProtocolState.observe who setup.program point) ≠ some who
      rw [actors who]
      exact fun equal => same (Option.some.inj equal).symm
  have wholeSelected : some (residual.lift after) ∈
      (setup.protocolStep history.state joint).support := by
    rw [atHistory]
    change some (residual.lift after) ∈ ((ProtocolState.step setup.program point joint).map
      some).support
    rw [residual.steps, PMF.map_comp]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨after, selected, rfl⟩
  have focalIntended := setup.intended_option_of_not_owesFailure admission wellFormed history
    joint legal focal (some (residual.lift after)) wholeSelected debtFree
  have intendedLegal : setup.intendedProtocol.Legal history.state joint := by
    apply ExecutionProtocol.legal_of_legalOption running
    intro who
    by_cases same : who = focal
    · subst who
      apply (setup.intendedModel.menu_adequate focal history.trace (joint focal)).mp
      rw [setup.intended_info]
      exact focalIntended
    · rw [show joint who = none by simp only [joint, same, ↓reduceIte]]
      change ¬ setup.intendedProtocol.active history.state who
      rw [atHistory]
      change ProtocolView.actor who setup.program
        (ProtocolState.observe who setup.program point) ≠ some who
      rw [actors who]
      exact fun equal => same (Option.some.inj equal).symm
  exact residual.intendedHistory_of_legal_step history historyAt joint intendedLegal after selected

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem owned_binding_source_successor
    {setup : Setup (Player := Player) (L := L)}
    (wholeProfile : BehavioralProfile setup.program) (wellFormed : setup.WellFormed)
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank origin)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name owner fresh guard next)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry)
    (ghost : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs)
    (checkpoint : SourceCheckpoint setup source frame.refs rank ghost)
    (history : setup.intendedProtocol.History)
    (historyAt : history.state =
      some (frame.lift (ProtocolState.entry frame.program source)))
    (active : owner ∉ source.defaulted) (result : PublicationResult (L.Val payload)) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.commit name owner fresh guard next) := programEq ▸ frame.embedding
    let lift : ProtocolState (.commit name owner fresh guard next) →
        ProtocolState setup.program := programEq ▸ frame.lift
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : setup.informationGraph.EventId := embedding.event index
    let binding : setup.informationGraph.outputLayout event = .binding owner payload :=
      (embedding.layout_eq index).trans rfl
    (¬ setup.OwesFailureState owner (some (lift (.inr (ProtocolState.entry next
      (commitSuccessor name guard source (some result))))))) →
      ∃ ready : ghost.cut.Ready event,
      let after := ghost.complete event ready
        (cast (congrArg EventField.Action binding.symm) (some result))
        (cast (congrArg EventField.Value binding.symm) result)
      SourceCheckpoint setup (commitSuccessor name guard source (some result))
          (frame.refs.cons ⟨.inr event, binding⟩) (rank + 1) after ∧
        after.Reachable inputs ∧ after.defaulted = ∅ ∧
        ∃ nextHistory : setup.intendedProtocol.History,
          nextHistory.state = some (lift (.inr (ProtocolState.entry next
            (commitSuccessor name guard source (some result))))) := by
  rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh guard next programEq source revelations registry checkpoint historyAt ⊢
  cases programEq
  intro debtFree
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : setup.informationGraph.EventId := embedding.event index
  have binding : setup.informationGraph.outputLayout event = .binding owner payload :=
    (embedding.layout_eq index).trans rfl
  have atRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : ghost.cut.Ready event := by
    have current : ghost.cut.Ready ⟨rank, atRank ▸ event.isLt⟩ :=
      checkpoint.ordered.ready (atRank ▸ event.isLt)
    exact (show event = ⟨rank, atRank ▸ event.isLt⟩ from Fin.ext atRank).symm ▸ current
  let after := ghost.complete event ready
    (cast (congrArg EventField.Action binding.symm) (some result))
    (cast (congrArg EventField.Value binding.symm) result)
  let residual : SourceResidual setup wholeProfile rank ghost :=
    residualAt ⟨Γ, names, .commit name owner fresh guard next, residualProfile, original, refs,
      embedding, refsBefore, aligned, admitted, authentic, supports, disclosing, lift, commutes,
      steps, injective, transport, originalCheckpoint⟩ source revelations registry ghost checkpoint
  have atGhost : history.state = sourceServicePrefix? setup rank ghost :=
    historyAt.trans residual.decode.symm
  have clear : ghost.defaulted = ∅ :=
    residual.clear_of_intended_history wellFormed history atGhost
  let joint : Player → Option (OwnAction Player L) := fun who => if who = owner then
    some (.commit owner name payload (some result)) else none
  have sourceStep : Sum.inr (ProtocolState.entry next
      (commitSuccessor name guard source (some result))) ∈
      (ProtocolState.step (.commit name owner fresh guard next)
        (ProtocolState.entry (.commit name owner fresh guard next) source) joint).support := by
    simp only [ProtocolState.entry, ProtocolState.step, Sum.elim_inl, joint, ↓reduceIte,
      OwnAction.binding_commit, PMF.mem_support_pure_iff]
  have eventRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventField.Action binding.symm) (some result)) =
        some (.commit owner name payload (some result)) := by
    simpa [index, event, binding, decodeEventAction] using aligned.actionEq index
      (cast (congrArg EventField.Action binding.symm) (some result))
  have nextHistory : ∃ h : setup.intendedProtocol.History,
      h.state = some (lift (.inr (ProtocolState.entry next
        (commitSuccessor name guard source (some result))))) := by
    have ghostActive : owner ∉ ghost.defaulted := by rw [clear]; simp
    have actor : setup.informationGraph.actor? event = some owner :=
      EventCode.actor_eq_of_binding _ binding
    cases eventRank
    exact residual.intendedHistory_of_debtFree_actor_step wellFormed event history atGhost owner
      actor ghostActive _ _ decoded _ sourceStep debtFree
  obtain ⟨nextHistory, nextHistoryAt⟩ := nextHistory
  have nextCheckpoint := checkpoint.commit (native := configState ghost) name guard event eventRank
    ready binding (fun ref => refsBefore ref index) (some result) decoded
  have stored : (commitSuccessor name guard source (some result)).state.get .here = result := by
    simp only [commitSuccessor, active, ite_false, Env.get, Env.cons, Option.getD_some]
  rw [stored] at nextCheckpoint
  have code : cast (congrArg (EventCode setup.informationGraph.layout) binding)
      (setup.informationGraph.nodes event) = .bind owner payload := by
    generalize cast (congrArg (EventCode setup.informationGraph.layout) binding)
      (setup.informationGraph.nodes event) = typed
    cases typed
    rfl
  have graphStep : after ∈ (ghost.step event ready
      (cast (congrArg EventField.Action binding.symm) (some result))).support := by
    have status : ghost.defaulted = source.defaulted :=
      congrArg DefaultHistory.defaulted checkpoint.defaults
    have law := commit_step ghost event ready binding code (some result)
    simp only [status, active, ite_false, Option.getD_some] at law
    rw [law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have nextClear : after.defaulted = ∅ := by
    have status := congrArg DefaultHistory.defaulted nextCheckpoint.defaults
    change after.defaulted = (commitSuccessor name guard source (some result)).defaulted at status
    have oldStatus : ghost.defaulted = source.defaulted :=
      congrArg DefaultHistory.defaulted checkpoint.defaults
    rw [status, commitSuccessor_defaulted_of_accepted, ← oldStatus, clear]
  exact ⟨ready, nextCheckpoint, Config.Step.path_reachable
    (Relation.ReflTransGen.single ⟨event, ready, _, graphStep⟩) reachable,
      nextClear, nextHistory, nextHistoryAt⟩

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem focal_binding_good_successor_law
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (event : graph.EventId) (focal : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding focal payload)
    (count : Nat) (bounded : event.val + 1 + count ≤ graph.order.eventCount)
    (bindings : ∀ prior : graph.EventId, event.val + 1 ≤ prior.val →
      prior.val < event.val + 1 + count → ∃ owner kind,
        graph.outputLayout prior = .binding owner kind)
    {Γ : SourceCtx Player L} {name : VarId}
    (guard : SourceGuard L Γ focal name payload)
    (prior : PMF ({source : Config Player L Γ // focal ∉ source.defaulted} ×
      {ghost : graph.Config // ghost.cut.Ready event ∧
        ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅}))
    (head : ∀ hidden ∈ prior.support, actionLaw profile hidden.2.1 event =
      PMF.pure (cast (congrArg EventField.Action binding.symm)
        (some (.failure : PublicationResult (L.Val payload)))))
    (kernel : DecisionView focal Γ → PMF (Option (PublicationResult (L.Val payload))))
    {Traffic Seed : Type}
    (noise : DecisionView focal ((name, .commitment focal payload) :: Γ) → PMF Traffic)
    (nextPrior : PMF Seed)
    (nextSource : Seed → Config Player L ((name, .commitment focal payload) :: Γ))
    (ghost : Seed → {ghost : graph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → graph.Config) (traffic : Seed → Traffic)
    (joint : nextPrior.map (fun seed =>
        ((nextSource seed, (ghost seed, bindingObservers focal (table seed))), traffic seed)) =
      ((prior.bind fun hidden => ((graph.runPlan
        (graph.policyPlan profile graph.canonicalScheduler) (count + 1) hidden.2.1).map
          fun selected => (hidden.1, (hidden.2, bindingObservers focal selected)))).bind
        (fun hidden => (kernel (hidden.1.1.view focal)).map fun action =>
          (commitSuccessor name guard hidden.1.1 action, hidden.2))).bind fun hidden =>
            (noise (hidden.1.view focal)).map fun observed => (hidden, observed))
    (good : Config Player L ((name, .commitment focal payload) :: Γ) → Bool) :
    let chosen := fun source : Config Player L ((name, .commitment focal payload) :: Γ) =>
      OwnAction.binding focal name payload (source.view focal).history.getLast?
    let advance := fun (config : {ghost : graph.Config // ghost.cut.Ready event ∧
        ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅}) action =>
      config.1.complete event config.2.1
        (cast (congrArg EventField.Action binding.symm) action)
        (cast (congrArg EventField.Value binding.symm) (action.getD .failure))
    let submitted := fun seed => (chosen (nextSource seed)).isSome
    let flag := fun seed => submitted seed && good (nextSource seed)
    ∀ _present : true ∈ (nextPrior.map flag).support,
    let selected := fiberPosterior nextPrior flag true
    selected.map (fun seed =>
      (((nextSource seed, advance (ghost seed) (chosen (nextSource seed))),
        bindingObservers focal (table seed)), traffic seed)) =
      (selected.map (fun seed =>
        (nextSource seed, advance (ghost seed) (chosen (nextSource seed))))).bind (fun current =>
          (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count current.2).bind
            fun final => (noise (current.1.view focal)).map fun observed =>
              ((current, bindingObservers focal final), observed)) := by
  intro chosen advance submitted flag present selected
  let choices := prior.bind fun hidden => (kernel (hidden.1.1.view focal)).map fun action =>
    ((commitSuccessor name guard hidden.1.1 action, advance hidden.2 action), action.isSome)
  have reset := focal_source_successor_noise_reset profile submits event focal payload binding
    count bounded bindings guard prior head kernel noise nextPrior nextSource ghost table traffic
      joint
  dsimp only at reset
  have optional : nextPrior.map (fun seed => if submitted seed then
      some (((nextSource seed, advance (ghost seed) (chosen (nextSource seed))),
        bindingObservers focal (table seed)), traffic seed) else none) =
      choices.bind (fun selected => if selected.2 then
        ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count selected.1.2).map
          (bindingObservers focal)).bind fun honest =>
            (noise (selected.1.1.view focal)).map fun observed =>
              some ((selected.1, honest), observed)
        else PMF.pure none) := by
    calc
      _ = nextPrior.map (fun seed => match chosen (nextSource seed) with
          | none => none
          | some result => some (((nextSource seed, advance (ghost seed) (some result)),
              bindingObservers focal (table seed)), traffic seed)) := by
        apply map_congr_on_support _
        intro seed _
        dsimp only [submitted]
        have split (action : Option (PublicationResult (L.Val payload))) :
            (if action.isSome then some (((nextSource seed, advance (ghost seed) action),
              bindingObservers focal (table seed)), traffic seed) else none) =
            match action with
            | none => none
            | some result => some (((nextSource seed, advance (ghost seed) (some result)),
                bindingObservers focal (table seed)), traffic seed) := by
          cases action <;> rfl
        exact split (chosen (nextSource seed))
      _ = prior.bind (fun hidden => (kernel (hidden.1.1.view focal)).bind fun action =>
          match action with
          | none => PMF.pure none
          | some result =>
              ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count
                (advance hidden.2 (some result))).map (bindingObservers focal)).bind fun honest =>
                  (noise ((commitSuccessor name guard hidden.1.1 action).view focal)).map
                    fun observed => some (((commitSuccessor name guard hidden.1.1 action,
                      advance hidden.2 (some result)), honest), observed)) := by
        simpa only [chosen, advance, Option.getD_some] using reset
      _ = _ := by
        simp only [choices, PMF.bind_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro hidden _
        apply bind_congr_on_support _
        intro action _
        cases action <;> rfl
  have posterior := binding_good_successor_law profile count focal choices nextPrior nextSource
    (fun seed => advance (ghost seed) (chosen (nextSource seed))) table traffic submitted noise
      good optional present
  simpa only [PMF.bind_map, Function.comp_def] using posterior

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem fixedBinding_submitted_stop
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    {horizon budget used turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile) (focal : Player)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : ∀ owner, owner ≠ focal → players owner =
      turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference owner)
    (anchor : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some ⟨budget, none, anchor⟩))
    (truthful : ∀ owner, owner ≠ focal → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks anchor owner)
    (answered : ActivationsAnswered setup leaks anchor)
    (calls : ∀ owner, owner ≠ focal → OwnFreshCalls setup leaks bound anchor owner)
    (once : ∀ owner, owner ≠ focal → OneCallPerEvent setup leaks anchor owner)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (fixed : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (owned : (serviceGraph setup deps).actor? event = some owner) → owner ≠ focal →
      ∃ (payload : L.Ty)
        (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        ∀ view active, reference owner event owned view active =
          PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (untouched : ∀ owner, owner ≠ focal → ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event anchor)
    (current : (serviceApplication setup deps duration leaks).Execution)
    (counted : used ≤ budget)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler
      players used anchor).support)
    (clear : current.application.config.defaulted = ∅)
    (inside : InBlock start finish current.application.config)
    (laterUntouched : ∀ event : (serviceGraph setup deps).EventId, finish ≤ event.val →
      Untouched setup leaks event current)
    (event : (serviceGraph setup deps).EventId) (late : event.val < finish)
    (name : VarId) (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding focal payload)
    (decode : ∀ choice : Option (PublicationResult (L.Val payload)),
      decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) choice) =
          some (.commit focal name payload choice))
    (pending : event ∉ current.application.config.cut.completed)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      (fun next => event ∈ next.application.config.cut.completed) (budget - used) current).support)
    (result : PublicationResult (L.Val payload))
    (played : OwnAction.binding focal name payload
      (decodeActionAt setup.program event final.application.config.history) = some result) :
    final.application.config.defaulted = ∅ ∧
      final.application.config.cut.Within start finish ∧
      event ∈ final.application.config.cut.completed ∧
      (∃ extra, used + extra ≤ budget ∧
        final ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
          (used + extra) anchor).support) ∧
      completionOf final.application.config event = some (EventGraph.completion
        (serviceGraph setup deps) event
        (some (cast (congrArg EventField.Action binding.symm) (some result)))
        (cast (congrArg EventField.Value binding.symm) result)) ∧
      final.application.config.outputs event =
        some (cast (congrArg EventField.Value binding.symm) result) ∧
      (∀ later : (serviceGraph setup deps).EventId, event.val < later.val →
        (serviceGraph setup deps).actor? later = some focal →
          later ∉ final.application.config.cut.completed) ∧
      ∀ later : (serviceGraph setup deps).EventId, finish ≤ later.val →
        Untouched setup leaks later final := by
  classical
  have active : focal ∉ current.application.config.defaulted := by rw [clear]; simp
  have finalActive := runUntil_submitted_binding_active (serviceTimeouts setup deps duration)
    leaks scheduler players event focal name payload binding decode (budget - used) current final
      active reached result played
  obtain ⟨finalClear, within, done, extra, enough, originalSupport⟩ :=
    fixedBinding_runUntil_clear_of_active scheduler bound relaxed.actorSerial contract timely
      reference focal players follows anchor trace truthful answered calls once start finish shaped
      bindings fixed untouched current counted supported clear inside _ (fun next completed =>
        completed event late) final reached finalActive
  have path := reactive_runUntil_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
    players (fun next => event ∈ next.application.config.cut.completed) (budget - used)
      current final reached
  obtain ⟨actual, sourceRead, record, stored⟩ := completed_binding_source_record setup.program path
    event pending done focal name payload binding finalActive decode
  have actualEq : actual = result := Option.some.inj (sourceRead.symm.trans played)
  subst actual
  refine ⟨finalClear, within, done, ⟨extra, enough, originalSupport⟩, record, stored, ?_, ?_⟩
  · intro later earlier actor
    exact reactive_runUntil_dependent_pending_of_clear (serviceTimeouts setup deps duration) leaks
      scheduler players event later
      (relaxed.same_owner_predecessor event later focal earlier
        (EventCode.actor_eq_of_binding _ binding) actor) (budget - used) current final pending
          reached finalClear
  · exact blockRun_untouched shaped scheduler players _
      (fun next completed => completed event late)
      (budget - used) current final inside laterUntouched reached

end Vegas

namespace Vegas.EventGraph

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem owned_binding_native_frame_successor
    (origin native before current : graph.Config) (source : graph.sequentialize.Config)
    (path : Relation.ReflTransGen Config.Step origin native)
    (same : runKey native = runKey (graph.fromSequentialConfig source))
    (clear : source.defaulted = ∅) (event : graph.EventId) (ready : source.cut.Ready event)
    (ordered : source.cut.IsPrefix event.val)
    (focal : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding focal payload)
    (result : PublicationResult (L.Val payload))
    (actualPath : Relation.ReflTransGen Config.Step before current)
    (priorOwn : ∀ node : graph.EventId, node.val < event.val → graph.actor? node = some focal →
      completionOf before node = completionOf (graph.fromSequentialConfig source) node)
    (recorded : completionOf current event = some (completion graph event
      (some (cast (congrArg EventField.Action binding.symm) (some result)))
      (cast (congrArg EventField.Value binding.symm) result))) :
    let after := source.complete event ready
      (cast (congrArg EventField.Action binding.symm) (some result))
      (cast (congrArg EventField.Value binding.symm) result)
    ∃ next : graph.Config, Relation.ReflTransGen Config.Step origin next ∧
      runKey next = runKey (graph.fromSequentialConfig after) ∧
      ∀ node : graph.EventId, node.val < event.val + 1 → graph.actor? node = some focal →
        completionOf current node = completionOf (graph.fromSequentialConfig after) node := by
  intro after
  obtain ⟨next, nextPath, nextKey⟩ := binding_ghost_path_successor origin native source path same
    clear event ready focal payload binding result
  have liftedReady : (graph.fromSequentialConfig source).cut.Ready event := by
    refine ⟨ready.1, ?_⟩
    intro prior predecessor
    exact ready.2 ((EventOrder.sequential.mem_predecessors prior event).mpr
      (graph.order.predecessor_lt predecessor))
  refine ⟨next, nextPath, nextKey, ?_⟩
  intro node earlier owned
  by_cases equal : node = event
  · subst node
    rw [show graph.fromSequentialConfig after = _ from
      fromSequential_complete source event ready liftedReady _ _, completionOf_complete,
      Function.update_self]
    rw [(graph.fromSequentialConfig source).actualDecision_of_active event focal
      (EventCode.actor_eq_of_binding _ binding) (by
        rw [graph.fromSequentialConfig_defaulted source, clear]; simp)]
    exact recorded
  · have lower : node.val < event.val := by
      have unequal : node.val ≠ event.val := fun sameVal => equal (Fin.ext sameVal)
      omega
    have done : node ∈ (graph.fromSequentialConfig source).cut.completed :=
      (ordered.2 node).mpr lower
    obtain ⟨saved, found⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff (graph.fromSequentialConfig source) node).mpr done)
    calc
      completionOf current node = some saved :=
        Config.Step.path_completionOf_of_some actualPath node saved
          ((priorOwn node lower owned).trans found)
      _ = completionOf (graph.fromSequentialConfig source) node := found.symm
      _ = completionOf (graph.fromSequentialConfig after) node := by
        rw [show graph.fromSequentialConfig after = _ from
          fromSequential_complete source event ready liftedReady _ _, completionOf_complete,
          Function.update_of_ne equal]

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime
open SourceProgram EventGraph Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeBindingContinuation_owned_good
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (wellFormed : setup.WellFormed)
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (referenceSubmits : setup.informationGraph.SubmitsBindings reference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (nativeBound : ℝ) (boundedNative : ∀ final, |nativePayoff final| ≤ nativeBound)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (start finish : Nat) (event : (serviceGraph setup deps).EventId)
    {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile event.val point)
    {name : VarId} {payload : L.Ty} (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ focal name payload)
    (next : SourceProgram Player L ((name, .commitment focal payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name focal fresh guard next)
    (binding : (serviceGraph setup deps).outputLayout event = .binding focal payload)
    (tail : nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff start finish
        (representativeCommitTail frame fresh guard next programEq))
    (lower : start ≤ event.val) (below : event.val < finish)
    (bounded : finish ≤ (serviceGraph setup deps).order.eventCount)
    (covered : frame.refs.CoversPrefix setup.program event.val)
    (bindings : ∀ node : (serviceGraph setup deps).EventId, start ≤ node.val →
      node.val < finish → ∃ owner kind,
        (serviceGraph setup deps).outputLayout node = .binding owner kind)
    (barrier : ∀ node : (serviceGraph setup deps).EventId, node.val = finish →
      ((serviceGraph setup deps).outputLayout node).IsPublic)
    {Seed : Type} (prior : PMF Seed)
    (source : Seed → {source : Config Player L frame.Γ // focal ∉ source.defaulted})
    (ghost : Seed → {ghost : setup.informationGraph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → setup.informationGraph.Config)
    (members : Seed → (serviceGraph setup deps).BehavioralProfile)
    (anchor execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (budget used : Seed → Nat) (nativeGhost : Seed → (serviceGraph setup deps).Config) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed))))
          focal deviation
    let placeholder := setup.informationGraph.prefixProfile (Function.update reference focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal))
    (∀ seed ∈ prior.support, @(source seed).1.revelations = @frame.source.revelations) →
    (∀ seed ∈ prior.support, (source seed).1.registry = frame.source.registry) →
    (∀ seed ∈ prior.support,
      SourceCheckpoint setup (source seed).1 frame.refs event.val (ghost seed).1) →
    (∀ seed ∈ prior.support, ∃ inputs, (ghost seed).1.Reachable inputs) →
    (∀ seed ∈ prior.support, ∃ h : setup.intendedProtocol.History,
      h.state = some (frame.lift (ProtocolState.entry frame.program (source seed).1))) →
    (∀ seed ∈ prior.support, G.SubmitsBindings (members seed)) →
    (∀ seed ∈ prior.support, ∀ owner node actor observation active, finish ≤ node.val →
      members seed owner node actor observation active =
        reference owner node actor observation active) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, start ≤ node.val → node.val < finish →
      ∀ owner kind (output : G.outputLayout node = .binding owner kind), owner ≠ focal →
      ∃ result : PublicationResult (L.Val kind),
        completionOf (table seed) node = some (EventGraph.completion setup.informationGraph node
          (some (cast (congrArg EventField.Action output.symm) (some result)))
          (cast (congrArg EventField.Value output.symm) result)) ∧
        (table seed).outputs node = some (cast (congrArg EventField.Value output.symm) result) ∧
        ∀ observation active, members seed owner node
          (EventCode.actor_eq_of_binding (G.nodes node) output) observation active =
            PMF.pure (cast (congrArg EventField.Action output.symm) (some result))) →
    (∀ seed ∈ prior.support, anchor seed ∈ (app.roundsFrom (serviceInitialLaw setup deps)
      scheduler (players seed) (anchor seed).environmentRecall.length).support) →
    (∀ seed ∈ prior.support, Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon
      scheduler).Trace (some ⟨budget seed, none, anchor seed⟩))) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.cut.IsPrefix start) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.defaulted = ∅) →
    (∀ seed ∈ prior.support, ∀ owner, owner ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
        CanonicalSlotsUsed setup leaks (anchor seed) owner ∧
        OwnFreshCalls setup leaks bound (anchor seed) owner ∧
        OneCallPerEvent setup leaks (anchor seed) owner) →
    (∀ seed ∈ prior.support, ActivationsAnswered setup leaks (anchor seed)) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, start ≤ node.val →
      Untouched setup leaks node (anchor seed)) →
    (∀ seed ∈ prior.support, used seed ≤ budget seed) →
    (∀ seed ∈ prior.support, execution seed ∈ (app.runRounds scheduler (players seed)
      (used seed) (anchor seed)).support) →
    (∀ seed ∈ prior.support, (execution seed).application.config.defaulted = ∅) →
    (∀ seed ∈ prior.support, InBlock start finish (execution seed).application.config) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, finish ≤ node.val →
      Untouched setup leaks node (execution seed)) →
    (∀ seed ∈ prior.support,
      Relation.ReflTransGen EventGraph.Config.Step (anchor seed).application.config
        (nativeGhost seed)) →
    (∀ seed ∈ prior.support, runKey (nativeGhost seed) =
      runKey (G.fromSequentialConfig (ghost seed).1)) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, node.val < event.val →
      G.actor? node = some focal → completionOf (execution seed).application.config node =
        completionOf (G.fromSequentialConfig (ghost seed).1) node) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, event.val ≤ node.val → node.val < finish →
      G.actor? node = some focal → node ∉ (execution seed).application.config.cut.completed) →
    let phase := fun seed => app.runUntilHorizon scheduler (players seed)
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
    let readChoice := fun final : app.Execution => OwnAction.binding focal name payload
      (decodeActionAt setup.program event final.application.config.history)
    let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
    let nextSource := fun point : Seed × app.Execution =>
      commitSuccessor name guard (source point.1).1 (readChoice point.2)
    let nextGraph := fun point : Seed × app.Execution =>
      (ghost point.1).1.complete event (ghost point.1).2.1
        (cast (congrArg EventField.Action binding.symm) (readChoice point.2))
        (cast (congrArg EventField.Value binding.symm) ((readChoice point.2).getD .failure))
    let lifted : ProtocolState (.commit name focal fresh guard next) →
      ProtocolState setup.program := fun state => frame.lift
        (cast (congrArg ProtocolState programEq.symm) state)
    let debtFree := fun config : Config Player L ((name, .commitment focal payload) :: frame.Γ) =>
      @decide (¬ setup.OwesFailureState focal
        (some (lifted (.inr (ProtocolState.entry next config))))) (Classical.propDecidable _)
    let flag := fun point : Seed × app.Execution =>
      (readChoice point.2).isSome && debtFree (nextSource point)
    ∀ (kernel : DecisionView focal frame.Γ → PMF (Option (PublicationResult (L.Val payload))))
      (nextNoise : DecisionView focal ((name, .commitment focal payload) :: frame.Γ) → PMF _),
      staged.map (fun point => ((nextSource point, (ghost point.1,
        bindingObservers focal (table point.1))),
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal point.2)) =
      ((((prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        (setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
          setup.informationGraph.canonicalScheduler) (finish - (event.val + 1) + 1)
            hidden.2.1).map fun selected =>
              (hidden.1, (hidden.2, bindingObservers focal selected))).bind fun hidden =>
        (kernel (hidden.1.1.view focal)).map fun action =>
          (commitSuccessor name guard hidden.1.1 action, hidden.2))).bind (fun hidden =>
            (nextNoise (hidden.1.view focal)).map fun traffic => (hidden, traffic)) →
      ∀ _present : true ∈ (staged.map flag).support,
      let selected := fiberPosterior staged flag true
      ∃ policy : setup.informationGraph.BehavioralPolicy focal,
        expect selected (fun point => expect
          (app.runToHorizon scheduler (players point.1) horizon point.2) nativePayoff) ≤
        expect (selected.bind fun point => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
              setup.informationGraph.canonicalScheduler) (eventCount next) (nextGraph point))
          sourcePayoff := by
  classical
  rcases frame with ⟨Γ, names, program, profile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh guard next programEq tail covered source ⊢
  cases programEq
  simp only [cast_eq]
  let frame : SourceResidual setup wholeProfile event.val point := {
    Γ := Γ, names := names, program := .commit name focal fresh guard next,
    residualProfile := profile, source := original, refs := refs, embedding := embedding,
    refsBefore := refsBefore, aligned := aligned, admitted := admitted, authentic := authentic,
    supports := supports, disclosing := disclosing, lift := lift, commutes := commutes,
    steps := steps, injective := injective, transport := transport,
    checkpoint := originalCheckpoint }
  let tailFrame := representativeCommitTail frame fresh guard next rfl
  change nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
    wholeProfile reference focal deviation nativePayoff sourcePayoff start finish tailFrame at tail
  let index : Fin (eventCount (.commit name focal fresh guard next)) := ⟨0, by simp [eventCount]⟩
  have headEq : embedding.event index = event := Fin.ext (by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index)
  have infoBinding : setup.informationGraph.outputLayout event = .binding focal payload := by
    change outputLayout setup.program event = .binding focal payload
    change outputLayout setup.program event = .binding focal payload at binding
    exact binding
  have frameHead : frame.embedding.event ⟨0, by simp [frame, eventCount]⟩ = event := headEq
  have tailRefs : tailFrame.refs = frame.refs.cons ⟨.inr event, binding⟩ := by
    change refs.cons ⟨.inr (embedding.event index), _⟩ = refs.cons ⟨.inr event, binding⟩
    simp only [headEq]
  have decoded : ∀ choice : Option (PublicationResult (L.Val payload)),
      decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) choice) =
          some (.commit focal name payload choice) := by
    intro choice
    cases headEq
    have headBinding : setup.informationGraph.outputLayout (embedding.event index) =
        .binding focal payload := infoBinding
    have law := aligned.actionEq index
      (cast (congrArg EventField.Action headBinding.symm) choice)
    simpa [index, decodeEventAction] using law
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let players := fun seed => Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed))))
        focal deviation
  let placeholder := setup.informationGraph.prefixProfile (Function.update reference focal
    (submittedFailurePolicy (graph := setup.informationGraph) focal))
  let phase := fun seed => app.runUntilHorizon scheduler (players seed)
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
  let readChoice := fun final : app.Execution => OwnAction.binding focal name payload
    (decodeActionAt setup.program event final.application.config.history)
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  let nextSource := fun point : Seed × app.Execution =>
    commitSuccessor name guard (source point.1).1 (readChoice point.2)
  let nextGraph := fun point : Seed × app.Execution =>
    (ghost point.1).1.complete event (ghost point.1).2.1
      (cast (congrArg EventField.Action binding.symm) (readChoice point.2))
      (cast (congrArg EventField.Value binding.symm) ((readChoice point.2).getD .failure))
  let lifted := lift
  let debtFree := fun config : Config Player L ((name, .commitment focal payload) :: Γ) =>
    @decide (¬ setup.OwesFailureState focal
      (some (lifted (.inr (ProtocolState.entry next config))))) (Classical.propDecidable _)
  let flag := fun point : Seed × app.Execution =>
    (readChoice point.2).isSome && debtFree (nextSource point)
  intro revelations registry checkpoint ghostReach history submits future fixed anchorSupported
    trace anchorOrdered anchorClear discipline answered untouched counted supported clear inside
    currentUntouched ghostPath ghostKey priorOwn futureOwn kernel nextNoise joint present
  change true ∈ (staged.map flag).support at present
  let selected := fiberPosterior staged flag true
  change ∃ policy : setup.informationGraph.BehavioralPolicy focal,
    expect selected (fun point => expect
      (app.runToHorizon scheduler (players point.1) horizon point.2) nativePayoff) ≤
      expect (selected.bind fun point => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount next) (nextGraph point))
        sourcePayoff
  let chosen := fun config : Config Player L ((name, .commitment focal payload) :: Γ) =>
    OwnAction.binding focal name payload (config.view focal).history.getLast?
  have remembered (seed : Seed) (action : Option (PublicationResult (L.Val payload))) :
      chosen (commitSuccessor name guard (source seed).1 action) = action := by
    simp only [chosen, Config.view, commitSuccessor, (source seed).2, ite_false,
      Function.update_self, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      OwnAction.binding_commit]
  have rememberedRaw (seed : Seed) (action : Option (PublicationResult (L.Val payload))) :
      OwnAction.binding focal name payload
        ((commitSuccessor name guard (source seed).1 action).view focal).history.getLast? =
          action := remembered seed action
  have globalSubmits : setup.informationGraph.SubmitsBindings placeholder :=
    (EventGraph.SubmitsBindings.update setup.informationGraph referenceSubmits focal _
      (setup.informationGraph.policySubmitsBindings_submitPolicy focal _)).prefix
  have pureHead : ∀ hidden ∈ (prior.map fun seed => (source seed, ghost seed)).support,
      actionLaw placeholder hidden.2.1 event = PMF.pure
        (cast (congrArg EventField.Action binding.symm) (some (.failure :
          PublicationResult (L.Val payload)))) := by
    intro hidden member
    obtain ⟨seed, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have actor : setup.informationGraph.actor? event = some focal :=
      EventCode.actor_eq_of_binding _ binding
    have active : focal ∉ (ghost seed).1.defaulted := by rw [(ghost seed).2.2.2]; simp
    rw [actionLaw_of_actor _ _ actor, dite_eq_right active]
    dsimp only [placeholder, EventGraph.prefixProfile, EventGraph.prefixPolicy]
    rw [Function.update_self]
    exact submittedFailurePolicy_binding (graph := setup.informationGraph) focal event actor
      payload infoBinding _ _
  have canonicalJoint := joint
  have boundedInfo : finish ≤ setup.informationGraph.order.eventCount := bounded
  have posteriorFactor := focal_binding_good_successor_law placeholder globalSubmits event focal
    payload binding (finish - (event.val + 1)) (by omega) (by
      intro node first last
      exact bindings node (by omega) (by omega)) guard
        (prior.map fun seed => (source seed, ghost seed)) pureHead kernel nextNoise staged
          nextSource
          (fun point => ghost point.1) (fun point => table point.1)
          (fun point => (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal point.2)
          canonicalJoint debtFree
  have sameFlag : (fun point : Seed × app.Execution =>
      (chosen (nextSource point)).isSome && debtFree (nextSource point)) = flag := by
    funext point
    simp only [nextSource, remembered, flag]
  dsimp only at posteriorFactor
  rw [sameFlag] at posteriorFactor
  have nextFactor := posteriorFactor present
  have normalizedFactor : selected.map (fun point =>
      (((nextSource point, nextGraph point), bindingObservers focal (table point.1)),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal point.2)) =
      (selected.map fun point => (nextSource point, nextGraph point)).bind fun current =>
        (setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
          setup.informationGraph.canonicalScheduler) (finish - (event.val + 1))
            current.2).bind fun final => (nextNoise (current.1.view focal)).map fun observed =>
              ((current, bindingObservers focal final), observed) := by
    simpa only [nextGraph, nextSource, rememberedRaw] using nextFactor
  let selectedPrior := pmfToSubtype selected (fun point member => member)
  let old := fun point : {point : Seed × app.Execution // point ∈ selected.support} => point.1.1
  let final := fun point : {point : Seed × app.Execution // point ∈ selected.support} => point.1.2
  have selectedFacts (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      old point ∈ prior.support ∧ final point ∈ (phase (old point)).support ∧
        (readChoice (final point)).isSome = true ∧ debtFree (nextSource point.1) = true := by
    obtain ⟨picked, stageSupport⟩ := mem_support_fiberPosterior present point.2
    obtain ⟨seed, seedSupport, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp stageSupport
    obtain ⟨ending, endingSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
    have sameSeed : seed = old point := congrArg Prod.fst same
    have sameFinal : ending = final point := congrArg Prod.snd same
    refine ⟨sameSeed ▸ seedSupport, ?_, (Bool.and_eq_true_iff.mp picked).1,
      (Bool.and_eq_true_iff.mp picked).2⟩
    simpa only [sameSeed, sameFinal] using endingSupport
  let result := fun point : {point : Seed × app.Execution // point ∈ selected.support} =>
    (readChoice (final point)).getD .failure
  have resultEq (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      readChoice (final point) = some (result point) := by
    have some := (selectedFacts point).2.2.1
    cases equation : readChoice (final point) with
    | none => simp only [equation, Option.isSome_none, Bool.false_eq_true] at some
    | some value => simp only [result, equation, Option.getD_some]
  have currentRemaining (seed : Seed) (member : seed ∈ prior.support) :
      horizon - (execution seed).environmentRecall.length = budget seed - used seed := by
    obtain ⟨raw⟩ := trace seed member
    have countedTrace := app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler raw
    have length := app.runRounds_environmentRecall_length scheduler (players seed) (used seed)
      (anchor seed) (execution seed) (supported seed member)
    have enough := counted seed member
    dsimp only at countedTrace
    omega
  have physical (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      (final point).application.config.defaulted = ∅ ∧
      (final point).application.config.cut.Within start finish ∧
      event ∈ (final point).application.config.cut.completed ∧
      (∃ extra, used (old point) + extra ≤ budget (old point) ∧ final point ∈
        (app.runRounds scheduler (players (old point)) (used (old point) + extra)
          (anchor (old point))).support) ∧
      completionOf (final point).application.config event = some (EventGraph.completion G event
        (some (cast (congrArg EventField.Action binding.symm) (some (result point))))
        (cast (congrArg EventField.Value binding.symm) (result point))) ∧
      (final point).application.config.outputs event =
        some (cast (congrArg EventField.Value binding.symm) (result point)) ∧
      (∀ later : G.EventId, event.val < later.val → G.actor? later = some focal →
        later ∉ (final point).application.config.cut.completed) ∧
      ∀ later : G.EventId, finish ≤ later.val → Untouched setup leaks later (final point) := by
    have member := (selectedFacts point).1
    let R := effectiveOpening (G.prefixProfile (members (old point)))
    have follows (owner : Player) (different : owner ≠ focal) :
        players (old point) owner = turnPolicy (serviceTimeouts setup deps duration) leaks
          bound turns
          (firstTurnTiming setup turns deps) R owner := Function.update_of_ne different _ _
    have constants : ∀ node : G.EventId, start ≤ node.val → node.val < finish → ∀ owner,
        (actor : G.actor? node = some owner) → owner ≠ focal → ∃ (kind : L.Ty)
          (output : G.outputLayout node = .binding owner kind)
          (value : PublicationResult (L.Val kind)),
          ∀ view active, R owner node actor view active =
            PMF.pure (cast (congrArg EventField.Action output.symm) (some value)) := by
      intro node first last owner actor different
      obtain ⟨other, kind, output⟩ := bindings node first last
      have ownerEq : other = owner := Option.some.inj
        ((EventCode.actor_eq_of_binding _ output).symm.trans actor)
      subst other
      obtain ⟨value, _record, _stored, constant⟩ :=
        fixed (old point) member node first last owner kind output different
      refine ⟨kind, output, value, ?_⟩
      intro view active
      dsimp only [R]
      rw [effectiveOpening_of_not_publication _ (by rw [output]; exact fun bad => bad) actor]
      exact constant _ _
    obtain ⟨raw⟩ := trace (old point) member
    have phaseSupport := (selectedFacts point).2.1
    change final point ∈ (app.runUntil scheduler (players (old point)) _
      (horizon - (execution (old point)).environmentRecall.length) (execution (old point))).support
      at phaseSupport
    rw [currentRemaining (old point) member] at phaseSupport
    exact fixedBinding_submitted_stop scheduler bound relaxed contract timely R focal
      (players (old point)) follows (anchor (old point)) raw
      (fun owner different => (discipline (old point) member owner different).1)
      (answered (old point) member)
      (fun owner different => (discipline (old point) member owner different).2.2.1)
      (fun owner different => (discipline (old point) member owner different).2.2.2)
      start finish (bindingInterval_shaped relaxed start finish bindings barrier) bindings constants
      (fun _owner _different node first _last _actor => untouched (old point) member node first)
      (execution (old point)) (counted (old point) member) (supported (old point) member)
      (clear (old point) member) (inside (old point) member) (currentUntouched (old point) member)
      event below name payload binding decoded (futureOwn (old point) member event le_rfl below
        (EventCode.actor_eq_of_binding _ binding)) (final point) phaseSupport (result point)
          (resultEq point)
  let nextS := fun point : {point : Seed × app.Execution // point ∈ selected.support} =>
    commitSuccessor name guard (source (old point)).1 (some (result point))
  let nextG := fun point : {point : Seed × app.Execution // point ∈ selected.support} =>
    (ghost (old point)).1.complete event (ghost (old point)).2.1
      (cast (congrArg EventField.Action binding.symm) (some (result point)))
      (cast (congrArg EventField.Value binding.symm) (result point))
  have nextSourceEq (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      nextSource point.1 = nextS point := by
    change commitSuccessor name guard (source (old point)).1 (readChoice (final point)) = _
    rw [resultEq point]
  have nextGraphEq (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      nextGraph point.1 = nextG point := by
    change (ghost (old point)).1.complete event _
      (cast (congrArg EventField.Action binding.symm) (readChoice (final point)))
      (cast (congrArg EventField.Value binding.symm)
        ((readChoice (final point)).getD .failure)) = _
    rw [resultEq point]
    rfl
  have sourceFacts (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      SourceCheckpoint setup (nextS point) tailFrame.refs (event.val + 1) (nextG point) ∧
      (∃ inputs, (nextG point).Reachable inputs) ∧
      ∃ h : setup.intendedProtocol.History,
        h.state = some (tailFrame.lift (ProtocolState.entry next (nextS point))) := by
    have member := (selectedFacts point).1
    obtain ⟨input, reach⟩ := ghostReach (old point) member
    obtain ⟨h, hAt⟩ := history (old point) member
    have safe : ¬ setup.OwesFailureState focal (some (lift (.inr (ProtocolState.entry next
        (nextS point))))) := by
      have known := @of_decide_eq_true
        (¬ setup.OwesFailureState focal (some (lifted (.inr (ProtocolState.entry next
          (nextSource point.1)))))) (Classical.propDecidable _) ((selectedFacts point).2.2.2)
      change ¬ setup.OwesFailureState focal (some (lift (.inr (ProtocolState.entry next
        (commitSuccessor name guard (source (old point)).1
          (readChoice (final point))))))) at known
      rw [resultEq point] at known
      exact known
    obtain ⟨ready, cp, reached, _empty, nextHistory, nextHistoryAt⟩ :=
      owned_binding_source_successor
      wholeProfile wellFormed frame fresh guard next rfl (source (old point)).1
      (revelations (old point) member) (registry (old point) member) (ghost (old point)).1
      reach (checkpoint (old point) member) h hAt (source (old point)).2 (result point) safe
    refine ⟨?_, ⟨input, ?_⟩, nextHistory, nextHistoryAt⟩
    · rw [tailRefs]
      cases headEq
      exact cp
    · cases headEq
      exact reached
  have phasePath (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      Relation.ReflTransGen EventGraph.Config.Step (execution (old point)).application.config
        (final point).application.config :=
    reactive_runUntil_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
      (players (old point)) _ _ (execution (old point)) (final point) (selectedFacts point).2.1
  choose nextNative nextPath nextKey nextOwn using fun point :
      {point : Seed × app.Execution // point ∈ selected.support} =>
    owned_binding_native_frame_successor (anchor (old point)).application.config
      (nativeGhost (old point)) (execution (old point)).application.config
      (final point).application.config (ghost (old point)).1 (ghostPath (old point)
        (selectedFacts point).1) (ghostKey (old point) (selectedFacts point).1)
      (ghost (old point)).2.2.2 event (ghost (old point)).2.1 (ghost (old point)).2.2.1 focal
      payload binding (result point) (phasePath point)
      (priorOwn (old point) (selectedFacts point).1) (physical point).2.2.2.2.1
  let extra := fun point : {point : Seed × app.Execution // point ∈ selected.support} =>
    (physical point).2.2.2.1.choose
  have extraFacts (point : {point : Seed × app.Execution // point ∈ selected.support}) :
      used (old point) + extra point ≤ budget (old point) ∧ final point ∈
        (app.runRounds scheduler (players (old point)) (used (old point) + extra point)
          (anchor (old point))).support := (physical point).2.2.2.1.choose_spec
  have comparison : ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (selectedPrior.bind fun point => app.runToHorizon scheduler
        (players (old point)) horizon (final point)) nativePayoff ≤
      expect (selectedPrior.bind fun point => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount next) (nextG point))
          sourcePayoff := by
    have nextCovered : tailFrame.refs.CoversPrefix setup.program (event.val + 1) := by
      rw [tailRefs]
      exact ContextRefs.CoversPrefix.cons setup.program (name := name)
        (cell := .commitment focal payload) covered ⟨.inr event, binding⟩ event rfl rfl
    apply tail (noise := nextNoise) (by omega) (by omega) bounded nextCovered
      bindings barrier selectedPrior nextS nextG (fun point => table (old point))
      (fun point => members (old point)) (fun point => anchor (old point)) final
      (fun point => budget (old point)) (fun point => used (old point) + extra point) nextNative
    · intro point _
      change @(commitSuccessor name guard (source (old point)).1
        (some (result point))).revelations =
        @(commitSuccessor name guard original (some .failure)).revelations
      simp only [commitSuccessor, revelations (old point) (selectedFacts point).1]
    · intro point _
      change (commitSuccessor name guard (source (old point)).1 (some (result point))).registry =
        (commitSuccessor name guard original (some .failure)).registry
      simp only [commitSuccessor, registry (old point) (selectedFacts point).1]
    · intro point _; exact (sourceFacts point).1
    · intro point _; exact (sourceFacts point).2.1
    · intro point _; exact (sourceFacts point).2.2
    · intro point _; exact submits (old point) (selectedFacts point).1
    · intro point _; exact future (old point) (selectedFacts point).1
    · intro point _; exact fixed (old point) (selectedFacts point).1
    · intro point _; exact anchorSupported (old point) (selectedFacts point).1
    · intro point _; exact trace (old point) (selectedFacts point).1
    · intro point _; exact anchorOrdered (old point) (selectedFacts point).1
    · intro point _; exact anchorClear (old point) (selectedFacts point).1
    · intro point _; exact discipline (old point) (selectedFacts point).1
    · intro point _; exact answered (old point) (selectedFacts point).1
    · intro point _; exact untouched (old point) (selectedFacts point).1
    · intro point _; exact (extraFacts point).1
    · intro point _; exact (extraFacts point).2
    · intro point _; exact (physical point).1
    · intro point _
      refine ⟨(physical point).2.1.1, ?_⟩
      intro node late done
      exact Nat.not_lt.mpr late ((physical point).2.1.2 node done)
    · intro point _; exact (physical point).2.2.2.2.2.2.2
    · intro point _; exact nextPath point
    · intro point _; exact nextKey point
    · intro point _; exact nextOwn point
    · intro point _ node later before actor
      exact (physical point).2.2.2.2.2.2.1 node (by omega) actor
    · have priorEq : selectedPrior.map Subtype.val = selected := map_val_pmfToSubtype _ _
      have restricted := normalizedFactor
      change selected.map _ = (selected.map _).bind _ at restricted
      rw [← priorEq] at restricted
      simpa only [PMF.map_comp, PMF.bind_map, Function.comp_def, nextSourceEq, nextGraphEq]
        using restricted
  obtain ⟨policy, comparison⟩ := comparison
  refine ⟨policy, ?_⟩
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ boundedNative)] at comparison
  have priorEq : selectedPrior.map Subtype.val = selected := map_val_pmfToSubtype _ _
  rw [← priorEq, PMF.bind_map]
  simpa only [PMF.map_comp, PMF.bind_map, expect_map, Function.comp_def, nextGraphEq]
    using comparison

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

open SourceProgram.Setup

private theorem native_owned_binding_bad_forfeit
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (serial : (serviceGraph setup deps).ActorSerial)
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (wholeProfile : BehavioralProfile setup.program)
    (focal : Player) (event : (serviceGraph setup deps).EventId)
    {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile event.val point)
    {name : VarId} {payload : L.Ty} (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ focal name payload)
    (next : SourceProgram Player L ((name, .commitment focal payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name focal fresh guard next)
    (binding : (serviceGraph setup deps).outputLayout event = .binding focal payload)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry) (active : focal ∉ source.defaulted)
    (ghost : setup.informationGraph.Config)
    (checkpoint : SourceCheckpoint setup source frame.refs event.val ghost)
    (ready : ghost.cut.Ready event) (clear : ghost.defaulted = ∅)
    (initial : State L setup.context) (origin native : (serviceGraph setup deps).Config)
    (start finish : Nat) (below : event.val < finish)
    (originReach : EventGraph.Config.Reachable (graph := serviceGraph setup deps)
      (setup.eventInputs initial) origin) (ordered : origin.cut.IsPrefix start)
    (ghostPath : Relation.ReflTransGen EventGraph.Config.Step origin native)
    (ghostKey : runKey native = runKey ((serviceGraph setup deps).fromSequentialConfig ghost))
    (bindings : ∀ node : (serviceGraph setup deps).EventId, start ≤ node.val →
      node.val < finish → ∃ owner kind,
        (serviceGraph setup deps).outputLayout node = .binding owner kind)
    (before final : (serviceApplication setup deps duration leaks).Execution)
    (beforePath : Relation.ReflTransGen EventGraph.Config.Step origin before.application.config)
    (phasePath : Relation.ReflTransGen EventGraph.Config.Step before.application.config
      final.application.config)
    (priorOwn : ∀ node : (serviceGraph setup deps).EventId, node.val < event.val →
      (serviceGraph setup deps).actor? node = some focal →
      completionOf before.application.config node =
        completionOf ((serviceGraph setup deps).fromSequentialConfig ghost) node)
    (pending : event ∉ before.application.config.cut.completed)
    (completed : event ∈ final.application.config.cut.completed)
    (supported : final ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players final.environmentRecall.length).support)
    (bounded : final.environmentRecall.length ≤ horizon) :
    let choice := OwnAction.binding focal name payload
      (decodeActionAt setup.program event final.application.config.history)
    let lifted : ProtocolState (.commit name focal fresh guard next) →
      ProtocolState setup.program := fun state => frame.lift
        (cast (congrArg SourceProgram.ProtocolState programEq.symm) state)
    (choice.isSome = false ∨ setup.OwesFailureState focal
      (some (lifted (.inr (ProtocolState.entry next
        (commitSuccessor name guard source choice)))))) →
    expect ((serviceApplication setup deps duration leaks).runToHorizon scheduler players horizon
      final) (fun ending => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        ending.application.config focal) ≤ leastUtility utility focal := by
  classical
  rcases frame with ⟨Γ, names, program, profile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh guard next programEq source revelations registry checkpoint ⊢
  cases programEq
  let G := serviceGraph setup deps
  let frame : SourceResidual setup wholeProfile event.val point :=
    ⟨Γ, names, .commit name focal fresh guard next, profile, original, refs, embedding, refsBefore,
      aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
      transport, originalCheckpoint⟩
  let choice := OwnAction.binding focal name payload
    (decodeActionAt setup.program event final.application.config.history)
  intro bad
  change choice.isSome = false ∨ setup.OwesFailureState focal
    (some (lift (.inr (ProtocolState.entry next
      (commitSuccessor name guard source choice))))) at bad
  by_cases defaulted : focal ∈ final.application.config.defaulted
  · exact expect_runToHorizon_forfeit_le_of_defaulted scheduler contract players parameter utility
      spread focal final supported bounded defaulted
  let index : Fin (eventCount (.commit name focal fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  have headEq : embedding.event index = event := Fin.ext (by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index)
  change outputLayout setup.program event = .binding focal payload at binding
  have decoded (action : Option (PublicationResult (L.Val payload))) :
      decodeEventAction setup.program event
        (cast (congrArg EventField.Action binding.symm) action) =
          some (.commit focal name payload action) := by
    subst event
    have law := aligned.actionEq index
      (cast (congrArg EventField.Action binding.symm) action)
    simpa [index, decodeEventAction] using law
  obtain ⟨result, sourceRead, record, _stored⟩ :=
    completed_binding_source_record setup.program
    phasePath event pending completed focal name payload binding defaulted decoded
  have chosen : choice = some result := sourceRead
  have owed : ProtocolState.OwesFailure focal setup.program
      (lift (.inr (ProtocolState.entry next
        (commitSuccessor name guard source (some result))))) := by
    rcases bad with missing | debt
    · simp only [chosen, Option.isSome_some, Bool.true_eq_false] at missing
    · rw [chosen] at debt
      exact debt
  let actual := residualAt frame source revelations registry ghost checkpoint
  have beforeRefs : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field := by
    intro readName cell ref
    have earlier := refsBefore ref index
    rwa [headEq] at earlier
  have infoBinding : setup.informationGraph.outputLayout event = .binding focal payload := by
    exact binding
  have afterCheckpoint := checkpoint.commit (deps := setup.informationDependencies)
    (native := configState ghost) name guard event rfl ready infoBinding beforeRefs (some result)
      (decoded (some result))
  have valueEq : (commitSuccessor name guard source (some result)).state.get .here = result := by
    simp only [commitSuccessor, active, ite_false, Option.getD_some]
    rfl
  rw [valueEq] at afterCheckpoint
  let after := ghost.complete event ready
    (cast (congrArg EventField.Action infoBinding.symm) (some result))
    (cast (congrArg EventField.Value infoBinding.symm) result)
  have headBinding : setup.informationGraph.outputLayout (embedding.event index) =
      .binding focal payload := by
    change outputLayout setup.program (embedding.event index) = .binding focal payload
    rw [headEq]
    exact binding
  change SourceCheckpoint (deps := setup.informationDependencies) setup
    (commitSuccessor name guard source (some result))
    (refs.cons (name := name) ⟨.inr event, infoBinding⟩) (event.val + 1) after at afterCheckpoint
  have tailCheckpoint : SourceCheckpoint (deps := setup.informationDependencies) setup
      (commitSuccessor name guard source (some result))
      (refs.cons (name := name) ⟨.inr (embedding.event index), headBinding⟩)
      (event.val + 1) after := by
    simpa only [headEq] using afterCheckpoint
  let tail := residualCommitTail actual fresh guard next rfl (some result) after
    (by exact tailCheckpoint)
  have debt : ProtocolState.OwesFailure focal setup.program
      (tail.lift (ProtocolState.entry tail.program tail.source)) := owed
  obtain ⟨nextNative, nextPath, nextKey, nextOwn⟩ := owned_binding_native_frame_successor origin
    native before.application.config final.application.config ghost ghostPath ghostKey clear event
    ready checkpoint.ordered focal payload binding result phasePath priorOwn record
  apply tail.expect_runToHorizon_forfeit_le_of_matching_binding_records serial initial focal origin
    nextNative start originReach ordered nextPath nextKey
    (fun node lower earlier => bindings node lower (by omega)) debt scheduler contract players
    parameter utility spread final supported bounded (beforePath.trans phasePath)
  intro node lower earlier actor
  have records := congrFun (congrArg (fun key => key.2.2) nextKey) node
  exact records.trans (nextOwn node earlier actor).symm

private theorem nativeBindingContinuation_owned_expected
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (wellFormed : setup.WellFormed)
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (referenceSubmits : setup.informationGraph.SubmitsBindings reference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit) :
    let nativePayoff := fun ending : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit ending.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (leastUtility utility) focal
    ∀ (start finish : Nat) (event : (serviceGraph setup deps).EventId)
    {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile event.val point)
    {name : VarId} {payload : L.Ty} (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ focal name payload)
    (next : SourceProgram Player L ((name, .commitment focal payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name focal fresh guard next)
    (binding : (serviceGraph setup deps).outputLayout event = .binding focal payload)
    (_tail : nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff start finish
        (representativeCommitTail frame fresh guard next programEq))
    (_lower : start ≤ event.val) (_below : event.val < finish)
    (_bounded : finish ≤ (serviceGraph setup deps).order.eventCount)
    (_covered : frame.refs.CoversPrefix setup.program event.val)
    (_bindings : ∀ node : (serviceGraph setup deps).EventId, start ≤ node.val →
      node.val < finish → ∃ owner kind,
        (serviceGraph setup deps).outputLayout node = .binding owner kind)
    (_barrier : ∀ node : (serviceGraph setup deps).EventId, node.val = finish →
      ((serviceGraph setup deps).outputLayout node).IsPublic)
    {Seed : Type} (prior : PMF Seed)
    (source : Seed → {source : Config Player L frame.Γ // focal ∉ source.defaulted})
    (ghost : Seed → {ghost : setup.informationGraph.Config // ghost.cut.Ready event ∧
      ghost.cut.IsPrefix event.val ∧ ghost.defaulted = ∅})
    (table : Seed → setup.informationGraph.Config)
    (members : Seed → (serviceGraph setup deps).BehavioralProfile)
    (anchor execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (budget used : Seed → Nat) (nativeGhost : Seed → (serviceGraph setup deps).Config),
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed))))
          focal deviation
    let placeholder := setup.informationGraph.prefixProfile (Function.update reference focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal))
    (∀ seed ∈ prior.support, @(source seed).1.revelations = @frame.source.revelations) →
    (∀ seed ∈ prior.support, (source seed).1.registry = frame.source.registry) →
    (∀ seed ∈ prior.support,
      SourceCheckpoint setup (source seed).1 frame.refs event.val (ghost seed).1) →
    (∀ seed ∈ prior.support, ∃ inputs, (ghost seed).1.Reachable inputs) →
    (∀ seed ∈ prior.support, ∃ h : setup.intendedProtocol.History,
      h.state = some (frame.lift (ProtocolState.entry frame.program (source seed).1))) →
    (∀ seed ∈ prior.support, G.SubmitsBindings (members seed)) →
    (∀ seed ∈ prior.support, ∀ owner node actor observation active, finish ≤ node.val →
      members seed owner node actor observation active =
        reference owner node actor observation active) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, start ≤ node.val → node.val < finish →
      ∀ owner kind (output : G.outputLayout node = .binding owner kind), owner ≠ focal →
      ∃ result : PublicationResult (L.Val kind),
        completionOf (table seed) node = some (EventGraph.completion setup.informationGraph node
          (some (cast (congrArg EventField.Action output.symm) (some result)))
          (cast (congrArg EventField.Value output.symm) result)) ∧
        (table seed).outputs node = some (cast (congrArg EventField.Value output.symm) result) ∧
        ∀ observation active, members seed owner node
          (EventCode.actor_eq_of_binding (G.nodes node) output) observation active =
            PMF.pure (cast (congrArg EventField.Action output.symm) (some result))) →
    (∀ seed ∈ prior.support, anchor seed ∈ (app.roundsFrom (serviceInitialLaw setup deps)
      scheduler (players seed) (anchor seed).environmentRecall.length).support) →
    (∀ seed ∈ prior.support, Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon
      scheduler).Trace (some ⟨budget seed, none, anchor seed⟩))) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.cut.IsPrefix start) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.defaulted = ∅) →
    (∀ seed ∈ prior.support, ∀ owner, owner ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
        CanonicalSlotsUsed setup leaks (anchor seed) owner ∧
        OwnFreshCalls setup leaks bound (anchor seed) owner ∧
        OneCallPerEvent setup leaks (anchor seed) owner) →
    (∀ seed ∈ prior.support, ActivationsAnswered setup leaks (anchor seed)) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, start ≤ node.val →
      Untouched setup leaks node (anchor seed)) →
    (∀ seed ∈ prior.support, used seed ≤ budget seed) →
    (∀ seed ∈ prior.support, execution seed ∈ (app.runRounds scheduler (players seed)
      (used seed) (anchor seed)).support) →
    (∀ seed ∈ prior.support, (execution seed).application.config.defaulted = ∅) →
    (∀ seed ∈ prior.support, InBlock start finish (execution seed).application.config) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, finish ≤ node.val →
      Untouched setup leaks node (execution seed)) →
    (∀ seed ∈ prior.support,
      Relation.ReflTransGen EventGraph.Config.Step (anchor seed).application.config
        (nativeGhost seed)) →
    (∀ seed ∈ prior.support, runKey (nativeGhost seed) =
      runKey (G.fromSequentialConfig (ghost seed).1)) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, node.val < event.val →
      G.actor? node = some focal → completionOf (execution seed).application.config node =
        completionOf (G.fromSequentialConfig (ghost seed).1) node) →
    (∀ seed ∈ prior.support, ∀ node : G.EventId, event.val ≤ node.val → node.val < finish →
      G.actor? node = some focal → node ∉ (execution seed).application.config.cut.completed) →
    let phase := fun seed => app.runUntilHorizon scheduler (players seed)
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
    let readChoice := fun final : app.Execution => OwnAction.binding focal name payload
      (decodeActionAt setup.program event final.application.config.history)
    let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
    let nextSource := fun point : Seed × app.Execution =>
      commitSuccessor name guard (source point.1).1 (readChoice point.2)
    let _nextGraph := fun point : Seed × app.Execution =>
      (ghost point.1).1.complete event (ghost point.1).2.1
        (cast (congrArg EventField.Action binding.symm) (readChoice point.2))
        (cast (congrArg EventField.Value binding.symm) ((readChoice point.2).getD .failure))
    let lifted : ProtocolState (.commit name focal fresh guard next) →
      ProtocolState setup.program := fun state => frame.lift
        (cast (congrArg SourceProgram.ProtocolState programEq.symm) state)
    let debtFree := fun config : Config Player L ((name, .commitment focal payload) :: frame.Γ) =>
      @decide (¬ setup.OwesFailureState focal
        (some (lifted (.inr (ProtocolState.entry next config))))) (Classical.propDecidable _)
    let _flag := fun point : Seed × app.Execution =>
      (readChoice point.2).isSome && debtFree (nextSource point)
    ∀ (noise : DecisionView focal frame.Γ → PMF _),
      prior.map (fun seed =>
        ((source seed, (ghost seed, bindingObservers focal (table seed))),
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        (setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
          setup.informationGraph.canonicalScheduler) (finish - (event.val + 1) + 1)
            hidden.2.1).map fun selected =>
              (hidden.1, (hidden.2, bindingObservers focal selected))).bind (fun hidden =>
                (noise (hidden.1.1.view focal)).map fun observed => (hidden, observed)) →
      ∃ policy : setup.informationGraph.BehavioralPolicy focal,
        expect staged (fun point => expect
          (app.runToHorizon scheduler (players point.1) horizon point.2) nativePayoff) ≤
        expect (prior.bind fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
              setup.informationGraph.canonicalScheduler) (eventCount next + 1) (ghost seed).1)
          sourcePayoff := by
  classical
  intro nativePayoff sourcePayoff start finish event point frame name payload fresh guard next
    programEq binding tail lower below bounded covered bindings barrier Seed prior source ghost
    table members anchor execution budget used nativeGhost G app players placeholder
    revelations registry checkpoint ghostReach history submits future fixed anchorSupported trace
    anchorOrdered anchorClear discipline answered untouched counted supported clear inside
    currentUntouched ghostPath ghostKey priorOwn futureOwn phase readChoice staged nextSource
    nextGraph lifted debtFree flag noise factor
  let phaseValue := fun point : Seed × app.Execution =>
    expect (app.runToHorizon scheduler (players point.1) horizon point.2) nativePayoff
  let chosen := fun config : Config Player L ((name, .commitment focal payload) :: frame.Γ) =>
    OwnAction.binding focal name payload (config.view focal).history.getLast?
  let good := fun config => (chosen config).isSome && debtFree config
  have remembered (seed : Seed) (action : Option (PublicationResult (L.Val payload))) :
      chosen (commitSuccessor name guard (source seed).1 action) = action := by
    simp only [chosen, Config.view, commitSuccessor, (source seed).2, ite_false,
      Function.update_self, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      OwnAction.binding_commit]
  have goodFlag : (fun point : Seed × app.Execution => good (nextSource point)) = flag := by
    funext point
    dsimp only [good, nextSource]
    rw [remembered]
  let hidden := fun seed => (source seed, (ghost seed, bindingObservers focal (table seed)))
  let hiddenPrior := (prior.map fun seed => (source seed, ghost seed)).bind fun current =>
    (setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
      setup.informationGraph.canonicalScheduler) (finish - (event.val + 1) + 1)
        current.2.1).map fun selected =>
          (current.1, (current.2, bindingObservers focal selected))
  have hiddenMarginal : prior.map hidden = hiddenPrior := by
    have projected := congrArg (PMF.map Prod.fst) factor
    simpa only [hidden, hiddenPrior, PMF.map_comp, PMF.map_bind, Function.comp_def,
      pmf_map_fun_const, PMF.bind_pure] using projected
  have factorGeneric : prior.map (fun seed => (hidden seed,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map hidden).bind fun current =>
        (noise (current.1.1.view focal)).map fun observed => (current, observed) := by
    rw [hiddenMarginal]
    exact factor
  obtain ⟨nativeBound, nativeNonnegative, nativeBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility spread focal
  have nativeAbs (ending : app.Execution) : |nativePayoff ending| ≤ nativeBound :=
    nativeBounded ending.application.config
  obtain ⟨sourceBound, _sourceNonnegative, sourceBounded⟩ :=
    setup.graphPayoff_abs_bound setup.informationDependencies parameter utility spread focal
  have currentSupported (seed : Seed) (member : seed ∈ prior.support) :
      execution seed ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler (players seed)
        (execution seed).environmentRecall.length).support := by
    have length := app.runRounds_environmentRecall_length scheduler (players seed) (used seed)
      (anchor seed) (execution seed) (supported seed member)
    rw [length]
    exact app.roundsFrom_runRounds scheduler (players seed) (serviceInitialLaw setup deps)
      (anchor seed).environmentRecall.length (used seed) (anchor seed) (execution seed)
      (anchorSupported seed member) (supported seed member)
  have currentTrace (seed : Seed) (member : seed ∈ prior.support) :
      ∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨remaining, none, execution seed⟩)) := by
    obtain ⟨raw⟩ := trace seed member
    obtain ⟨current⟩ := app.raw_trace_runRounds (serviceInitialLaw setup deps) horizon scheduler
      (players seed) (budget seed - used seed) (used seed) (anchor seed) (execution seed)
      (by simpa only [Nat.sub_add_cancel (counted seed member)] using raw)
      (supported seed member)
    exact ⟨_, ⟨current⟩⟩
  have currentBound (seed : Seed) (member : seed ∈ prior.support) :
      (execution seed).environmentRecall.length ≤ horizon := by
    obtain ⟨remaining, ⟨raw⟩⟩ := currentTrace seed member
    have available := app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler raw
    dsimp only at available
    omega
  have anchorInitial (seed : Seed) (member : seed ∈ prior.support) :
      ∃ initial : State L setup.context, EventGraph.Config.Reachable (graph := G)
        (setup.eventInputs initial) (anchor seed).application.config := by
    obtain ⟨raw⟩ := trace seed member
    rw [serviceInitialLaw_eq_inputs setup] at raw
    obtain ⟨inputs, selected, facts⟩ := reactive_history_invariant
      (serviceTimeouts setup deps duration) leaks (setup.initialLaw.map setup.eventInputs)
      horizon scheduler raw
    obtain ⟨initial, _selected, same⟩ := (PMF.mem_support_map_iff _ _ _).mp selected
    exact ⟨initial, same ▸ facts.reachable⟩
  have currentPath (seed : Seed) (member : seed ∈ prior.support) :
      Relation.ReflTransGen EventGraph.Config.Step (anchor seed).application.config
        (execution seed).application.config :=
    reactive_runRounds_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
      (players seed) (used seed) (anchor seed) (execution seed) (supported seed member)
  have canonical (seed : Seed) (member : seed ∈ prior.support) (owner : Player)
      (foreign : owner ≠ focal) : OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks (execution seed) owner ∧
        CanonicalSlotsUsed setup leaks (execution seed) owner := by
    have follows : players seed owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound
        turns (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed)))
        owner := Function.update_of_ne foreign _ _
    exact canonicalSlots_roundsFrom_reference relaxed.actorSerial scheduler (players seed) owner
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed))) follows
      (execution seed).environmentRecall.length (execution seed) (currentSupported seed member)
  refine native_focal_binding_graph_runUntil setup deps duration leaks
    focal fresh guard next (programEq ▸ frame.residualProfile) frame.refs
    (programEq ▸ frame.embedding) event relaxed (EventCode.actor_eq_of_binding _ binding) binding
    (setup.informationGraph.prefixProfile reference) (eventCount next) prior source ghost
    (fun seed => bindingObservers focal (table seed)) execution scheduler bound start finish
    bindings
    barrier below deviation (fun seed => effectiveOpening (G.prefixProfile (members seed)))
    (fun seed member => (submits seed member).prefix.effectiveOpening) currentTrace inside canonical
    lower contract.completes (fun seed => (anchor seed).application.config) nativeGhost
    (fun seed member => by obtain ⟨initial, reach⟩ := anchorInitial seed member; exact ⟨_, reach⟩)
    anchorOrdered currentPath ghostPath ghostKey priorOwn noise factorGeneric checkpoint ghostReach
    (fun seed _ => Config.NoBindingDefaults.of_clear (ghost seed).2.2.2)
    sourcePayoff phaseValue good (leastUtility utility focal) sourceBound sourceBounded
    (fun config => setup.leastUtility_le_graphPayoff setup.informationDependencies parameter utility
      spread focal config) ?_ ?_ ?_
  · exact payoffIntegrable_of_bounded staged phaseValue fun point =>
      expect_abs_le_of_bounded nativeNonnegative nativeAbs
  · intro point present failed
    obtain ⟨seed, member, selected⟩ := (PMF.mem_support_bind_iff _ _ _).mp present
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp selected
    cases same
    have completed := runUntilHorizon_stop contract (players seed)
      (fun current => event ∈ current.application.config.cut.completed)
      (fun _ terminal => by rw [terminal]; exact Finset.mem_univ _)
      (execution seed) (currentSupported seed member) (currentBound seed member) final reached
    obtain ⟨finalSupport, finalBound⟩ := runUntilHorizon_bounded
      (currentSupported seed member) (currentBound seed member) reached
    obtain ⟨initial, originReach⟩ := anchorInitial seed member
    have path := reactive_runUntil_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
      (players seed) (fun current => event ∈ current.application.config.cut.completed)
      (horizon - (execution seed).environmentRecall.length) (execution seed) final reached
    apply native_owned_binding_bad_forfeit setup deps duration leaks relaxed.actorSerial scheduler
      contract (players seed) parameter utility spread wholeProfile focal event frame fresh guard
      next programEq binding (source seed).1 (revelations seed member) (registry seed member)
      (source seed).2 (ghost seed).1 (checkpoint seed member) (ghost seed).2.1
      (ghost seed).2.2.2 initial (anchor seed).application.config (nativeGhost seed) start finish
      below
      originReach (anchorOrdered seed member) (ghostPath seed member) (ghostKey seed member)
      bindings (execution seed) final (currentPath seed member) path (priorOwn seed member)
      (futureOwn seed member event le_rfl below (EventCode.actor_eq_of_binding _ binding)) completed
      finalSupport finalBound
    have sameFlag : good (nextSource (seed, final)) = flag (seed, final) := congrFun goodFlag _
    change good (nextSource (seed, final)) = false at failed
    rw [sameFlag] at failed
    rcases Bool.and_eq_false_iff.mp failed with omitted | debt
    · exact Or.inl omitted
    · apply Or.inr
      have owed : setup.OwesFailureState focal
          (some (lifted (.inr (ProtocolState.entry next (nextSource (seed, final)))))) :=
        Classical.not_not.mp (@of_decide_eq_false _ (Classical.propDecidable _) debt)
      exact owed
  · intro kernel nextNoise joint present
    have normalized := joint
    change (staged.map fun point => ((nextSource point,
      (ghost point.1, bindingObservers focal (table point.1))),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal point.2)) =
      ((prior.map hidden).bind fun current =>
        (kernel (current.1.1.view focal)).map fun action =>
          (commitSuccessor name guard current.1.1 action, current.2)).bind (fun current =>
            (nextNoise (current.1.view focal)).map fun observed => (current, observed))
              at normalized
    rw [hiddenMarginal] at normalized
    change true ∈ (staged.map (fun point => good (nextSource point))).support at present
    rw [goodFlag] at present
    change ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (fiberPosterior staged (fun point => good (nextSource point)) true) phaseValue ≤
        expect ((fiberPosterior staged (fun point => good (nextSource point)) true).bind
          fun point => setup.informationGraph.runPlan
            (setup.informationGraph.policyPlan (Function.update
              (setup.informationGraph.prefixProfile reference) focal policy)
                setup.informationGraph.canonicalScheduler) (eventCount next) (nextGraph point))
          sourcePayoff
    rw [goodFlag]
    have answer := nativeBindingContinuation_owned_good setup deps duration leaks wellFormed horizon
      scheduler
      bound turns relaxed contract timely wholeProfile reference referenceSubmits focal deviation
      nativePayoff nativeBound nativeAbs sourcePayoff start finish event frame fresh guard next
      programEq binding tail lower below bounded covered bindings barrier prior source ghost table
      members anchor execution budget used nativeGhost
      revelations registry checkpoint ghostReach history submits future fixed anchorSupported trace
      anchorOrdered anchorClear discipline answered untouched counted supported clear inside
      currentUntouched ghostPath ghostKey priorOwn futureOwn kernel nextNoise normalized
      present
    exact answer

private theorem nativeBindingContinuation_owned
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (wellFormed : setup.WellFormed)
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (referenceSubmits : setup.informationGraph.SubmitsBindings reference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (start finish : Nat) {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank point)
    {name : VarId} {payload : L.Ty} (fresh : name ∉ frame.Γ.map Prod.fst)
    (guard : SourceGuard L frame.Γ focal name payload)
    (next : SourceProgram Player L ((name, .commitment focal payload) :: frame.Γ)
      (insert name frame.names))
    (programEq : frame.program = .commit name focal fresh guard next)
    (below : rank < finish) :
    let nativePayoff := fun final : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (Setup.leastUtility utility) focal
    nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff start finish
        (representativeCommitTail frame fresh guard next programEq) →
    nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff start finish frame := by
  classical
  intro nativePayoff sourcePayoff tail
  rcases frame with ⟨Γ, names, program, profile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh guard next programEq tail ⊢
  cases programEq
  let frame : SourceResidual setup wholeProfile rank point := {
    Γ := Γ, names := names, program := .commit name focal fresh guard next,
    residualProfile := profile, source := original, refs := refs, embedding := embedding,
    refsBefore := refsBefore, aligned := aligned, admitted := admitted, authentic := authentic,
    supports := supports, disclosing := disclosing, lift := lift, commutes := commutes,
    steps := steps, injective := injective, transport := transport,
    checkpoint := originalCheckpoint }
  let tailFrame := representativeCommitTail frame fresh guard next rfl
  change nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
    wholeProfile reference focal deviation nativePayoff sourcePayoff start finish tailFrame at tail
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let index : Fin (eventCount (.commit name focal fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : setup.informationGraph.EventId := embedding.event index
  have eventRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have binding : G.outputLayout event = .binding focal payload :=
    (embedding.layout_eq index).trans rfl
  cases eventRank
  have eventRank : event.val = event.val := rfl
  let placeholder := setup.informationGraph.prefixProfile (Function.update reference focal
    (submittedFailurePolicy (graph := setup.informationGraph) focal))
  intro lower upper bounded covered bindings barrier Seed prior source ghost table members anchor
    execution budget used nativeGhost players revelations registry checkpoint ghostReach history
    submits future fixed anchorSupported trace anchorOrdered anchorClear discipline answered
    untouched counted supported clear inside currentUntouched ghostPath ghostKey priorOwn futureOwn
    noise factor
  let supportedPrior := pmfToSubtype prior (fun seed member => member)
  have cleanGhost (seed : {seed : Seed // seed ∈ prior.support}) :
      (ghost seed.1).defaulted = ∅ := by
    let current := residualAt frame (source seed.1) (revelations seed.1 seed.2)
      (registry seed.1 seed.2) (ghost seed.1) (checkpoint seed.1 seed.2)
    obtain ⟨h, atHistory⟩ := history seed.1 seed.2
    exact current.clear_of_intended_history wellFormed h (atHistory.trans current.decode.symm)
  have cleanSource (seed : {seed : Seed // seed ∈ prior.support}) :
      (source seed.1).defaulted = ∅ := by
    have status : (ghost seed.1).defaulted = (source seed.1).defaulted :=
      congrArg DefaultHistory.defaulted (checkpoint seed.1 seed.2).defaults
    exact status.symm.trans (cleanGhost seed)
  let currentSource := fun seed : {seed : Seed // seed ∈ prior.support} =>
    (⟨source seed.1, by rw [cleanSource seed]; simp⟩ :
      {source : Config Player L Γ // focal ∉ source.defaulted})
  let currentGhost := fun seed : {seed : Seed // seed ∈ prior.support} =>
    (⟨ghost seed.1, by
      have ordered := (checkpoint seed.1 seed.2).ordered
      rw [← eventRank] at ordered
      exact ordered.ready event.isLt, by
      simpa only [eventRank] using (checkpoint seed.1 seed.2).ordered, cleanGhost seed⟩ :
      {config : setup.informationGraph.Config // config.cut.Ready event ∧
        config.cut.IsPrefix event.val ∧ config.defaulted = ∅})
  let forget := fun {Traffic : Type} (pair :
      (({source : Config Player L Γ // focal ∉ source.defaulted} ×
        ({config : setup.informationGraph.Config // config.cut.Ready event ∧
          config.cut.IsPrefix event.val ∧ config.defaulted = ∅})) ×
          (setup.informationGraph.PublicObservation ×
            ((who : {who : Player // who ≠ focal}) →
              setup.informationGraph.PlayerObservation who.1))) × Traffic) =>
      (((pair.1.1.1.1, pair.1.1.2.1), pair.1.2), pair.2)
  have factorTyped : supportedPrior.map (fun seed =>
      (((currentSource seed, currentGhost seed), bindingObservers focal (table seed.1)),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed.1))) =
      (supportedPrior.map fun seed => (currentSource seed, currentGhost seed)).bind fun current =>
        (setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
          setup.informationGraph.canonicalScheduler) (finish - event.val) current.2.1).bind
            fun selected => (noise (current.1.1.view focal)).map fun observed =>
              ((current, bindingObservers focal selected), observed) := by
    have priorEq : supportedPrior.map Subtype.val = prior := map_val_pmfToSubtype _ _
    have restricted := factor
    rw [← priorEq] at restricted
    simp only [PMF.map_comp, PMF.bind_map, Function.comp_def] at restricted
    apply pmf_map_injective (f := forget) (by
      intro left right same
      apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun pair => pair.1.1.1) same
          · apply Subtype.ext
            exact congrArg (fun pair => pair.1.1.2) same
        · exact congrArg (fun pair => pair.1.2) same
      · exact congrArg (fun pair => pair.2) same)
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, PMF.bind_bind, Function.comp_def,
      forget, currentSource, currentGhost, eventRank, placeholder] using restricted
  have factorRebracketed : supportedPrior.map (fun seed =>
      ((currentSource seed, (currentGhost seed, bindingObservers focal (table seed.1))),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed.1))) =
      ((supportedPrior.map fun seed => (currentSource seed, currentGhost seed)).bind fun current =>
        (setup.informationGraph.runPlan (setup.informationGraph.policyPlan placeholder
          setup.informationGraph.canonicalScheduler) (finish - (event.val + 1) + 1)
            current.2.1).map fun selected =>
              (current.1, (current.2, bindingObservers focal selected))).bind fun current =>
        (noise (current.1.1.view focal)).map fun observed => (current, observed) := by
    have countEq : finish - event.val = finish - (event.val + 1) + 1 := by omega
    have projected := congrArg (PMF.map fun pair =>
      ((pair.1.1.1, (pair.1.1.2, pair.1.2)), pair.2)) factorTyped
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, PMF.bind_bind, Function.comp_def,
      countEq] using projected
  obtain ⟨policy, comparison⟩ := nativeBindingContinuation_owned_expected setup deps duration leaks
    wellFormed horizon scheduler bound turns relaxed contract timely wholeProfile reference
    referenceSubmits focal deviation parameter utility spread start finish event frame fresh
    guard next rfl binding tail (by omega) (by omega) bounded covered bindings barrier
    supportedPrior
    currentSource currentGhost (fun seed => table seed.1) (fun seed => members seed.1)
    (fun seed => anchor seed.1) (fun seed => execution seed.1) (fun seed => budget seed.1)
    (fun seed => used seed.1) (fun seed => nativeGhost seed.1)
    (fun seed _ => revelations seed.1 seed.2) (fun seed _ => registry seed.1 seed.2)
    (fun seed _ => checkpoint seed.1 seed.2) (fun seed _ => ghostReach seed.1 seed.2)
    (fun seed _ => history seed.1 seed.2) (fun seed _ => submits seed.1 seed.2)
    (fun seed _ => future seed.1 seed.2) (fun seed _ => fixed seed.1 seed.2)
    (fun seed _ => anchorSupported seed.1 seed.2) (fun seed _ => trace seed.1 seed.2)
    (fun seed _ => anchorOrdered seed.1 seed.2) (fun seed _ => anchorClear seed.1 seed.2)
    (fun seed _ => discipline seed.1 seed.2) (fun seed _ => answered seed.1 seed.2)
    (fun seed _ => untouched seed.1 seed.2) (fun seed _ => counted seed.1 seed.2)
    (fun seed _ => supported seed.1 seed.2) (fun seed _ => clear seed.1 seed.2)
    (fun seed _ => inside seed.1 seed.2) (fun seed _ => currentUntouched seed.1 seed.2)
    (fun seed _ => ghostPath seed.1 seed.2) (fun seed _ => ghostKey seed.1 seed.2)
    (fun seed _ node earlier actor => priorOwn seed.1 seed.2 node (by omega) actor)
    (fun seed _ node later before actor => futureOwn seed.1 seed.2 node (by omega) before actor)
    noise factorRebracketed
  refine ⟨policy, ?_⟩
  have nativeEquality : expect
      (supportedPrior.bind fun seed => app.runToHorizon scheduler (players seed.1) horizon
        (execution seed.1)) nativePayoff =
      expect (prior.bind fun seed => app.runToHorizon scheduler (players seed) horizon
        (execution seed)) nativePayoff := by
    congr 1
    calc
      _ = (supportedPrior.map Subtype.val).bind (fun seed => app.runToHorizon scheduler
          (players seed) horizon (execution seed)) := by rw [PMF.bind_map]; rfl
      _ = _ := by rw [map_val_pmfToSubtype]
  have sourceEquality : (supportedPrior.bind fun seed => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount next + 1) (currentGhost seed).1) =
      prior.bind (fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount next + 1) (ghost seed)) := by
    calc
      _ = (supportedPrior.map Subtype.val).bind (fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
              setup.informationGraph.canonicalScheduler) (eventCount next + 1) (ghost seed)) := by
        rw [PMF.bind_map]
        rfl
      _ = _ := by rw [map_val_pmfToSubtype]
  have comparisonCurrent : expect
      (supportedPrior.bind fun seed => app.runToHorizon scheduler (players seed.1) horizon
        (execution seed.1)) nativePayoff ≤
      expect (supportedPrior.bind fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount next + 1)
              (currentGhost seed).1) sourcePayoff := by
    convert comparison using 1
    let phase := fun seed : {seed : Seed // seed ∈ prior.support} =>
      app.runUntilHorizon scheduler (players seed.1)
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed.1)
    let staged := supportedPrior.bind fun seed => (phase seed).map fun final => (seed, final)
    let suffixRun := fun point : {seed : Seed // seed ∈ prior.support} × app.Execution =>
      app.runToHorizon scheduler (players point.1.1) horizon point.2
    change expect (supportedPrior.bind fun seed => app.runToHorizon scheduler (players seed.1)
      horizon (execution seed.1)) nativePayoff =
        expect staged (fun point => expect (suffixRun point) nativePayoff)
    have boundNative :=
      setup.graphForfeitConfigPayoff_abs_bound deps parameter utility spread focal
    obtain ⟨payoffBound, _nonnegative, payoffBounded⟩ := boundNative
    rw [← expect_bind_tower staged suffixRun nativePayoff (payoffIntegrable_of_bounded _ _
      (fun final => payoffBounded final.application.config))]
    congr 1
    simp only [staged, suffixRun, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed _
    exact app.runToHorizon_eq_runUntilHorizon_bind scheduler (players seed.1)
      (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed.1)
  simpa only [eventCount, nativeEquality, sourceEquality] using comparisonCurrent

end Vegas

namespace Vegas
open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem completionOf_of_bindingObservers_eq
    {graph : EventGraph Player L} (focal owner : Player) (different : owner ≠ focal)
    (left right : graph.Config) (same : bindingObservers focal left = bindingObservers focal right)
    (event : graph.EventId) (owned : graph.actor? event = some owner)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (found : completionOf left event = some (EventGraph.completion graph event (some action)
      value)) :
    completionOf right event = some (EventGraph.completion graph event (some action) value) := by
  have member := ((completionOf_eq_some_iff left event _).mp found).1
  have own := (mem_ownCompletions owner left.history _).mpr ⟨member, owned, rfl⟩
  have observed := congrFun (congrArg Prod.snd same) ⟨owner, different⟩
  have history := congrArg EventPlayerObservation.ownActions observed
  change graph.ownCompletions owner left.history = graph.ownCompletions owner right.history
    at history
  rw [history] at own
  exact (completionOf_eq_some_iff right event _).mpr
    ⟨((mem_ownCompletions owner right.history _).mp own).1, rfl⟩

private theorem nativeBindingContinuation_finish
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (start finish : Nat) {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile finish point)
    (outer : nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff frame) :
    nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff start finish frame := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let placeholder := setup.informationGraph.prefixProfile
    (Function.update reference focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal))
  intro lower _upper bounded covered bindings barrier Seed prior source ghost
    table members anchor execution budget used nativeGhost players revelations registry checkpoint
    ghostReach intended submits future fixed anchorSupported trace anchorOrdered _anchorClear
    discipline answered untouched counted supported clear inside currentUntouched ghostPath ghostKey
    priorOwn _futureOwn noise factor
  have effectiveSubmits : ∀ seed ∈ prior.support,
      G.SubmitsBindings (effectiveOpening (G.prefixProfile (members seed))) := by
    intro seed member
    apply EventGraph.SubmitsBindings.effectiveOpening
    intro owner event actor view active action selected
    exact submits seed member owner event actor _ _ action selected
  let stop := fun next : app.Execution => BlockDone finish next.application.config
  let phase := fun seed =>
    app.runUntilHorizon scheduler (players seed) stop horizon (execution seed)
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  have factorZero := factor
  simp only [Nat.sub_self, EventGraph.runPlan, PMF.pure_bind] at factorZero
  have observers : ∀ seed ∈ prior.support,
      bindingObservers focal (table seed) = bindingObservers focal (ghost seed) := by
    intro seed member
    have present : (((source seed, ghost seed), bindingObservers focal (table seed)),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed)) ∈
        (prior.map (fun selected => (((source selected, ghost selected),
          bindingObservers focal (table selected)),
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
            (execution selected)))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, member, rfl⟩
    rw [factorZero, PMF.mem_support_bind_iff] at present
    obtain ⟨current, _currentMember, observed⟩ := present
    obtain ⟨extra, _extraMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
    have hidden := congrArg (fun value => value.1.1) same
    have honest := congrArg (fun value => value.1.2) same
    exact honest.symm.trans (congrArg (fun current => bindingObservers focal current.2) hidden)
  have currentSupport : ∀ seed ∈ prior.support, execution seed ∈
      (app.roundsFrom (serviceInitialLaw setup deps) scheduler (players seed)
        (execution seed).environmentRecall.length).support := by
    intro seed member
    have reached := app.roundsFrom_runRounds scheduler (players seed)
      (serviceInitialLaw setup deps) (anchor seed).environmentRecall.length (used seed)
      (anchor seed) (execution seed) (anchorSupported seed member) (supported seed member)
    rw [app.runRounds_environmentRecall_length scheduler (players seed) (used seed)
      (anchor seed) (execution seed) (supported seed member)]
    exact reached
  have remainingEq : ∀ seed ∈ prior.support,
      horizon - (execution seed).environmentRecall.length = budget seed - used seed := by
    intro seed member
    obtain ⟨raw⟩ := trace seed member
    have initialBudget := app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler raw
    have length := app.runRounds_environmentRecall_length scheduler (players seed) (used seed)
      (anchor seed) (execution seed) (supported seed member)
    dsimp only at initialBudget
    omega
  have endpoint : ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
      final.application.config.defaulted = ∅ ∧ final.application.config.cut.IsPrefix finish ∧
      runKey final.application.config = runKey (G.fromSequentialConfig (ghost seed)) ∧
      ∃ extra, used seed + extra ≤ budget seed ∧
        final ∈ (app.runRounds scheduler (players seed) (used seed + extra)
          (anchor seed)).support := by
    intro seed member final reached
    let R := effectiveOpening (G.prefixProfile (members seed))
    have follows (owner : Player) (different : owner ≠ focal) :
        players seed owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) R owner := by
      exact Function.update_of_ne different _ _
    obtain ⟨raw⟩ := trace seed member
    have nativeTrace := raw
    rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
    obtain ⟨input, _inputMember, valid⟩ := reactive_history_invariant
      (serviceTimeouts setup deps duration) leaks (setup.initialLaw.map setup.eventInputs)
      horizon scheduler nativeTrace
    have nativeOrdered : (nativeGhost seed).cut.IsPrefix finish := by
      have cuts : (nativeGhost seed).cut =
          (G.fromSequentialConfig (ghost seed)).cut :=
        congrArg Prod.fst (ghostKey seed member)
      rw [cuts]
      exact (checkpoint seed member).ordered
    have fixedGhost : ∀ event : G.EventId, start ≤ event.val → event.val < finish → ∀ owner,
        (owned : G.actor? event = some owner) → owner ≠ focal →
        ∃ (payload : L.Ty) (binding : G.outputLayout event = .binding owner payload)
          (result : PublicationResult (L.Val payload)),
          (∀ view active, R owner event owned view active =
            PMF.pure (cast (congrArg EventField.Action binding.symm) (some result))) ∧
          completionOf (nativeGhost seed) event = some (EventGraph.completion G event
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)) := by
      intro event first last owner owned different
      obtain ⟨other, payload, binding⟩ := bindings event first last
      have sameOwner : other = owner := Option.some.inj
        ((EventCode.actor_eq_of_binding (G.nodes event) binding).symm.trans owned)
      subst other
      obtain ⟨result, record, _stored, constant⟩ :=
        fixed seed member event first last owner payload binding different
      refine ⟨payload, binding, result, ?_, ?_⟩
      · intro view active
        change effectiveOpening (G.prefixProfile (members seed)) owner event owned view active = _
        rw [effectiveOpening_of_not_publication _ (by rw [binding]; exact fun bad => bad) owned]
        exact constant _ _
      · have actualRecord := completionOf_of_bindingObservers_eq focal owner different
          (table seed) (ghost seed) (observers seed member) event owned _ _ record
        exact (congrFun (congrArg (fun key => key.2.2) (ghostKey seed member)) event).trans
          actualRecord
    have focalComplete : ∀ event : G.EventId, start ≤ event.val → event.val < finish → ∀ owner,
        G.actor? event = some owner → ¬ owner ≠ focal →
          event ∈ (execution seed).application.config.cut.completed := by
      intro event _first last owner owned focalOwner
      have ownerEq : owner = focal := Classical.not_not.mp focalOwner
      subst owner
      apply (completionOf_isSome_iff _ event).mp
      rw [priorOwn seed member event last owned]
      exact (completionOf_isSome_iff _ event).mpr
        (((checkpoint seed member).ordered.2 event).mpr last)
    have focalMatched : ∀ event : G.EventId, start ≤ event.val → event.val < finish → ∀ owner,
        G.actor? event = some owner → ¬ owner ≠ focal →
          completionOf (execution seed).application.config event =
            completionOf (nativeGhost seed) event := by
      intro event _first last owner owned focalOwner
      have ownerEq : owner = focal := Classical.not_not.mp focalOwner
      subst owner
      exact (priorOwn seed member event last owned).trans
        (congrFun (congrArg (fun key => key.2.2) (ghostKey seed member)) event).symm
    have reached' : final ∈ (app.runUntil scheduler (players seed) stop
        (budget seed - used seed) (execution seed)).support := by
      simpa only [phase, ReactiveApplication.runUntilHorizon, remainingEq seed member] using reached
    obtain ⟨finalClear, ordered, key, extra, enough, countedFinal⟩ := fixedBinding_block_key
      scheduler bound relaxed.actorSerial contract timely R (fun owner => owner ≠ focal)
      (players seed) follows (anchor seed) raw
      (fun owner different => (discipline seed member owner different).1)
      (answered seed member)
      (fun owner different => (discipline seed member owner different).2.2.1)
      (fun owner different => (discipline seed member owner different).2.2.2)
      start finish (bindingInterval_shaped relaxed start finish bindings barrier)
      (anchorOrdered seed member) bindings (nativeGhost seed) valid.reachable
      (ghostPath seed member) nativeOrdered fixedGhost
      (fun _owner _different event first _last _owned => untouched seed member event first)
      (execution seed) (counted seed member) (supported seed member) (clear seed member)
      (inside seed member) focalComplete focalMatched final reached'
    exact ⟨finalClear, ordered, key.trans (ghostKey seed member), extra, enough, countedFinal⟩
  have currentBound : ∀ seed ∈ prior.support,
      (execution seed).environmentRecall.length ≤ horizon := by
    intro seed member
    obtain ⟨raw⟩ := trace seed member
    have budgetEq := app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler raw
    have length := app.runRounds_environmentRecall_length scheduler (players seed) (used seed)
      (anchor seed) (execution seed) (supported seed member)
    have enough := counted seed member
    dsimp only at budgetEq
    omega
  have canonical : ∀ seed ∈ prior.support, ∀ owner, owner ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (execution seed) owner ∧
        CanonicalSlotsUsed setup leaks (execution seed) owner := by
    intro seed member owner different
    exact canonicalSlots_roundsFrom_reference relaxed.actorSerial scheduler (players seed) owner
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (members seed)))
      (Function.update_of_ne different _ _) _ _ (currentSupport seed member)
  have currentTrace : ∀ seed ∈ prior.support, Nonempty
      ((app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) := by
    intro seed member
    exact app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler (players seed)
      (execution seed).environmentRecall.length (currentBound seed member) (execution seed)
      (currentSupport seed member)
  have coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution left) =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution right) →
      (phase left).map ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
        (phase right).map ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
    intro left leftSupported right rightSupported same
    have sameRecall := congrArg (fun traffic => traffic.2.2.1) same
    change (execution left).environmentRecall = (execution right).environmentRecall at sameRecall
    have sameLength := congrArg List.length sameRecall
    obtain ⟨leftTrace⟩ := currentTrace left leftSupported
    obtain ⟨rightTrace⟩ := currentTrace right rightSupported
    change (app.runUntil scheduler (players left) stop
      (horizon - (execution left).environmentRecall.length) (execution left)).map _ = _
    dsimp only [phase, ReactiveApplication.runUntilHorizon]
    rw [← sameLength]
    apply bindingBlock_stopped_traffic_congr (horizon := horizon)
      (leftRemaining := 0) (rightRemaining := 0)
      relaxed scheduler bound start finish bindings barrier
      focal deviation stop (fun _ done => done) _
      (effectiveOpening (G.prefixProfile (members left)))
      (effectiveOpening (G.prefixProfile (members right)))
      (effectiveSubmits left leftSupported) (effectiveSubmits right rightSupported)
      (execution left) (execution right) same
      (by simpa only [Nat.zero_add] using leftTrace)
      (by simpa only [Nat.zero_add, sameLength] using rightTrace)
      (inside left leftSupported) (inside right rightSupported)
      (canonical left leftSupported) (canonical right rightSupported)
    intro first second equal
    have samePublic := congrArg (fun value => value.2.2.2.2.2) equal
    change BlockDone finish first.application.config ↔ BlockDone finish second.application.config
    unfold BlockDone
    rw [cut_eq_of_publicView_eq samePublic]
  have marginalFactor : (prior.map (fun seed => ((source seed, ghost seed),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed)))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        (noise (hidden.1.view focal)).map fun observed => (hidden, observed) := by
    have marginal := congrArg (PMF.map (fun value => (value.1.1, value.2))) factorZero
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def] using marginal
  obtain ⟨nextNoise, joint⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, ghost seed))
    (fun seed => (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
      (execution seed))
    (fun hidden => hidden.1.view focal) noise marginalFactor (fun _ => PMF.pure ())
    (fun hidden _ => hidden) (fun hidden => hidden.1.view focal)
    (fun seed _ => (phase seed).map
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupported _ _ right rightSupported _ _ _ same =>
      coupled left leftSupported right rightSupported same)
  have stagedMarginal : (staged.map (fun entry => (source entry.1, ghost entry.1))) =
      prior.map (fun seed => (source seed, ghost seed)) := by
    simp only [staged, PMF.map_bind, PMF.map_comp, Function.comp_def]
    calc
      _ = prior.bind (fun seed => PMF.pure (source seed, ghost seed)) := by
        apply bind_congr_on_support _
        intro seed _
        exact PMF.map_const _ (source seed, ghost seed)
      _ = _ := by
        simpa only [Function.comp_def] using
          (PMF.bind_pure_comp (fun seed => (source seed, ghost seed)) prior)
  have nextFactor : (staged.map (fun entry => ((source entry.1, ghost entry.1),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal entry.2))) =
      (staged.map (fun entry => (source entry.1, ghost entry.1))).bind fun hidden =>
        (nextNoise (hidden.1.view focal)).map fun observed => (hidden, observed) := by
    rw [stagedMarginal]
    simpa only [staged, PMF.map_bind, PMF.map_comp, PMF.pure_bind, PMF.pure_map,
      PMF.bind_pure, Function.comp_def] using joint
  have stagedSupport (entry : Seed × app.Execution) (member : entry ∈ staged.support) :
      entry.1 ∈ prior.support ∧ entry.2 ∈ (phase entry.1).support := by
    obtain ⟨seed, selected, present⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    cases same
    exact ⟨selected, reached⟩
  have boundary : ∀ entry ∈ staged.support,
      CompletionBoundary setup leaks scheduler (players entry.1) finish entry.2 := by
    intro entry member
    obtain ⟨selected, reached⟩ := stagedSupport entry member
    obtain ⟨_clearFinal, ordered, _key, _extra, _enough, _countedFinal⟩ :=
      endpoint entry.1 selected entry.2 reached
    refine ⟨?_, ordered, ?_⟩
    · exact app.roundsFrom_runUntil scheduler (players entry.1) (serviceInitialLaw setup deps)
        stop (horizon - (execution entry.1).environmentRecall.length) (execution entry.1) entry.2
        (currentSupport entry.1 selected) reached
    · exact blockRun_untouched
        (bindingInterval_shaped relaxed start finish bindings barrier) scheduler (players entry.1)
        stop (fun _ done => done)
        (horizon - (execution entry.1).environmentRecall.length) (execution entry.1) entry.2
        (inside entry.1 selected) (currentUntouched entry.1 selected) reached
  have finalBound : ∀ entry ∈ staged.support, entry.2.environmentRecall.length ≤ horizon := by
    intro entry member
    obtain ⟨selected, reached⟩ := stagedSupport entry member
    obtain ⟨_finalClear, _ordered, _key, extra, enough, countedFinal⟩ :=
      endpoint entry.1 selected entry.2 reached
    obtain ⟨raw⟩ := trace entry.1 selected
    have budgetEq := app.raw_trace_horizon (serviceInitialLaw setup deps) horizon scheduler raw
    have length := app.runRounds_environmentRecall_length scheduler (players entry.1)
      (used entry.1 + extra) (anchor entry.1) entry.2 countedFinal
    dsimp only at budgetEq
    omega
  obtain ⟨policy, compare⟩ := outer covered staged (fun entry => source entry.1)
    (fun entry => ghost entry.1)
    (fun entry member => revelations entry.1 (stagedSupport entry member).1)
    (fun entry member => registry entry.1 (stagedSupport entry member).1)
    (fun entry member => checkpoint entry.1 (stagedSupport entry member).1)
    (fun entry member => ghostReach entry.1 (stagedSupport entry member).1)
    (fun entry member => intended entry.1 (stagedSupport entry member).1)
    (fun entry => members entry.1)
    (fun entry member => submits entry.1 (stagedSupport entry member).1)
    (fun entry member => future entry.1 (stagedSupport entry member).1)
    (fun entry => entry.2) boundary finalBound
    (fun entry member => (endpoint entry.1 (stagedSupport entry member).1 entry.2
      (stagedSupport entry member).2).2.2.1) nextNoise nextFactor
  refine ⟨policy, ?_⟩
  have nativeLaw : (staged.bind fun entry => app.runToHorizon scheduler (players entry.1)
      horizon entry.2) = prior.bind fun seed =>
        app.runToHorizon scheduler (players seed) horizon (execution seed) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed _
    exact (app.runToHorizon_eq_runUntilHorizon_bind scheduler (players seed) stop horizon
      (execution seed)).symm
  have sourceLaw : (staged.bind fun entry => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost entry.1)) =
      prior.bind fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
  rw [nativeLaw, sourceLaw] at compare
  exact compare

private theorem sourceResidual_binding_interval_induction
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    (start finish : Nat) (bounded : finish ≤ eventCount setup.program)
    (bindings : ∀ event : Fin (eventCount setup.program),
      start ≤ event.val → event.val < finish →
      ∃ owner payload, outputLayout setup.program event = .binding owner payload)
    (property : ∀ (rank : Nat) (origin : setup.informationGraph.Config),
      SourceResidual setup profile rank origin → Prop)
    (atFinish : ∀ origin (frame : SourceResidual setup profile finish origin),
      property finish origin frame)
    (atCommit : ∀ (rank : Nat) (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup profile rank origin), rank < finish →
      ∀ {name : VarId} {owner : Player} {payload : L.Ty}
        (fresh : name ∉ frame.Γ.map Prod.fst) (guard : SourceGuard L frame.Γ owner name payload)
        (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
          (insert name frame.names))
        (programEq : frame.program = .commit name owner fresh guard next),
        property (rank + 1) _ (representativeCommitTail frame fresh guard next programEq) →
          property rank origin frame) :
    ∀ (rank : Nat) (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup profile rank origin),
      start ≤ rank → rank ≤ finish → property rank origin frame := by
  intro rank origin frame lower upper
  generalize distanceEq : finish - rank = distance
  induction distance using Nat.strong_induction_on generalizing rank origin with
  | ind distance ih =>
      by_cases last : rank = finish
      · subst rank
        exact atFinish origin frame
      · have earlier : rank < finish := lt_of_le_of_ne upper last
        rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
          aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
          transport, checkpoint⟩
        have counted := aligned.graphSuffix.countEq
        change rank + eventCount program = eventCount setup.program at counted
        cases program with
        | ret payoffs =>
            simp only [eventCount] at counted
            omega
        | @sample Γ names name payload fresh distribution next =>
            let index : Fin (eventCount (.sample name fresh distribution next)) :=
              ⟨0, by simp [eventCount]⟩
            have atRank : (embedding.event index).val = rank := by
              simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
            obtain ⟨owner, cellPayload, binding⟩ := bindings (embedding.event index)
              (by omega) (by omega)
            have layout : outputLayout setup.program (embedding.event index) =
                .publicData payload := (embedding.layout_eq index).trans rfl
            cases layout.symm.trans binding
        | @reveal Γ names published owner name payload fresh selected unresolved next =>
            let index : Fin (eventCount
                (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
            have atRank : (embedding.event index).val = rank := by
              simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
            obtain ⟨other, cellPayload, binding⟩ := bindings (embedding.event index)
              (by omega) (by omega)
            have layout : outputLayout setup.program (embedding.event index) =
                .publication payload := (embedding.layout_eq index).trans rfl
            cases layout.symm.trans binding
        | @commit Γ names name owner payload fresh guard next =>
            let frame : SourceResidual setup profile rank origin :=
              ⟨Γ, names, .commit name owner fresh guard next, residualProfile, source, refs,
                embedding, refsBefore, aligned, admitted, authentic, supports, disclosing, lift,
                commutes, steps, injective, transport, checkpoint⟩
            apply atCommit rank origin frame earlier fresh guard next rfl
            exact ih (finish - (rank + 1)) (by omega) (rank + 1) _
              (representativeCommitTail frame fresh guard next rfl) (by omega) (by omega) rfl

end Vegas

namespace Vegas
open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeBindingContinuation_binding_interval [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (start finish : Nat) :
    let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := setup.informationGraph.submitProfile (compileEventProfile setup.program whole)
    let nativePayoff := fun final : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (Setup.leastUtility utility) focal
    start < finish → finish ≤ (serviceGraph setup deps).order.eventCount →
    (∀ event : (serviceGraph setup deps).EventId, start ≤ event.val → event.val < finish →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload) →
    (∀ event : (serviceGraph setup deps).EventId, event.val = finish →
      ((serviceGraph setup deps).outputLayout event).IsPublic) →
    (∀ {tailPoint : setup.informationGraph.Config}
      (tail : SourceResidual setup whole finish tailPoint),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff tail) →
    ∀ {point : setup.informationGraph.Config} (frame : SourceResidual setup whole start point),
      nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff start finish frame := by
  intro whole reference nativePayoff sourcePayoff later bounded bindings barrier outer
  classical
  obtain ⟨nativeBound, _nonnegative, nativeBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility spread focal
  let property := fun (rank : Nat) (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup whole rank origin) =>
    nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns whole
      reference focal deviation nativePayoff sourcePayoff start finish frame
  have atFinish (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup whole finish origin) : property finish origin frame :=
    nativeBindingContinuation_finish setup deps duration leaks horizon scheduler bound turns
      relaxed
      contract timely whole reference focal deviation nativePayoff sourcePayoff start finish frame
        (outer frame)
  have atCommit (rank : Nat) (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup whole rank origin) (below : rank < finish)
      {name : VarId} {owner : Player} {payload : L.Ty}
      (fresh : name ∉ frame.Γ.map Prod.fst) (guard : SourceGuard L frame.Γ owner name payload)
      (next : SourceProgram Player L ((name, .commitment owner payload) :: frame.Γ)
        (insert name frame.names))
      (programEq : frame.program = .commit name owner fresh guard next)
      (tail : property (rank + 1) _
        (representativeCommitTail frame fresh guard next programEq)) :
        property rank origin frame := by
    by_cases same : owner = focal
    · subst owner
      exact nativeBindingContinuation_owned setup deps duration leaks wellFormed horizon scheduler
        bound turns relaxed contract timely whole reference
        (submitsBindings_submitProfile setup.informationGraph _) focal deviation parameter utility
        forfeit spread start finish frame fresh guard next programEq below tail
    · exact nativeBindingContinuation_foreign setup deps duration leaks wellFormed intended target
        agrees submits horizon scheduler bound turns reference rfl focal deviation nativePayoff
        nativeBound (fun final => nativeBounded final.application.config) sourcePayoff start finish
        frame fresh guard next programEq same below tail
  intro point frame
  exact sourceResidual_binding_interval_induction start finish bounded bindings property atFinish
    atCommit start point frame le_rfl later.le

end Vegas

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def representativeRevealTail
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ frame.Γ.map Prod.fst)
    (selected : HasVar frame.Γ name (.commitment owner payload)) (unresolved : name ∈ frame.names)
    (next : SourceProgram Player L ((published, .publication payload) :: frame.Γ)
      (frame.names.erase name))
    (programEq : frame.program = .reveal published owner name fresh selected unresolved next) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.reveal published owner name fresh selected unresolved next) := programEq ▸ frame.embedding
    let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : setup.informationGraph.outputLayout (embedding.event index) =
        .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let atRank : (embedding.event index).val = rank := by
      rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
        aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
        transport, checkpoint⟩
      dsimp only at fresh selected unresolved next programEq ⊢
      cases programEq
      simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
    let ready : origin.cut.Ready (embedding.event index) := by
      have ordered := frame.checkpoint.ordered
      rw [← atRank] at ordered
      exact ordered.ready (embedding.event index).isLt
    SourceResidual setup profile (rank + 1)
      (origin.complete (embedding.event index) ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published selected frame.source true))) := by
  rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at fresh selected unresolved next programEq ⊢
  cases programEq
  let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
      .publication payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have atRank : (embedding.event index).val = rank := by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : origin.cut.Ready (embedding.event index) := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready (embedding.event index).isLt
  have decoded : decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) =
        some (.reveal owner name true) := by
    have lookup := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
    simpa [index, outputEq, decodeEventAction] using lookup
  let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
  let tailRefs : ContextRefs (graphLayout setup.program)
      ((published, .publication payload) :: Γ) :=
    refs.cons ⟨.inr (embedding.event index), outputEq⟩
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
    refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
  have tailAligned : CompiledPolicySuffix setup.program profile next
      (afterReveal residualProfile) tailRefs
      (revealSuccessor published selected source true).revelations
      (revealSuccessor published selected source true).registry
      tailEmbedding tailBefore (rank + 1) := by
    simpa only [revealSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
      aligned.revealTail setup.program profile fresh selected unresolved next
        residualProfile refs source.revelations source.registry embedding refsBefore rank
  refine {
    Γ := _, names := _, program := next, residualProfile := afterReveal residualProfile,
    source := revealSuccessor published selected source true, refs := tailRefs,
    embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
    admitted := fun whole who => admitted whole who,
    authentic := fun whole who => (authentic whole who).2,
    supports := fun whole who => (supports whole who).2,
    disclosing := fun whole who => (disclosing whole who).2,
    lift := lift ∘ Sum.inr,
    commutes := fun state => ?_, steps := fun state joint => ?_,
    injective := injective.comp Sum.inr_injective,
    transport := fun more store history defaults => ?_,
    checkpoint := checkpoint.reveal (native := configState origin) published selected
      (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index) true decoded }
  · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_reveal_tail,
      PMF.map_comp]
  · rw [Function.comp_apply, steps]
    change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
    rw [PMF.map_comp]
  · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
      decodeSourcePrefix?_reveal, Option.map_map]
    rfl

end Vegas

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem exists_reveal_prefix_source_frame
    {setup : Setup (Player := Player) (L := L)} [Finite Player]
    (wellFormed : setup.WellFormed)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who)) :
    ∀ (count rank : Nat) (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target) rank origin),
      frame.refs.CoversPrefix setup.program rank →
      rank + count ≤ setup.informationGraph.order.eventCount →
      (∀ event : setup.informationGraph.EventId, rank ≤ event.val →
        event.val < rank + count → (setup.informationGraph.outputLayout event).IsPublication) →
    ∃ (endOrigin : setup.informationGraph.Config)
      (tail : SourceResidual setup (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target) (rank + count) endOrigin),
      tail.refs.CoversPrefix setup.program (rank + count) ∧
      eventCount frame.program = count + eventCount tail.program ∧
      ∀ (source : Config Player L frame.Γ),
        @source.revelations = @frame.source.revelations →
        source.registry = frame.source.registry →
      ∀ (ghost : setup.informationGraph.Config),
        SourceCheckpoint setup source frame.refs rank ghost →
      ∀ (inputs : setup.informationGraph.Inputs), ghost.Reachable inputs →
      ∀ (history : setup.intendedProtocol.History),
        history.state = some (frame.lift (ProtocolState.entry frame.program source)) →
      ∃ (nextSource : Config Player L tail.Γ) (nextGhost : setup.informationGraph.Config),
        @nextSource.revelations = @tail.source.revelations ∧
        nextSource.registry = tail.source.registry ∧
        SourceCheckpoint setup nextSource tail.refs (rank + count) nextGhost ∧
        nextGhost.Reachable inputs ∧
        (∃ nextHistory : setup.intendedProtocol.History,
          nextHistory.state = some (tail.lift (ProtocolState.entry tail.program nextSource))) ∧
        setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan
            (compilePrescribedProfile setup.program setup.informationDependencies
              (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target))
            setup.informationGraph.canonicalScheduler) count ghost = PMF.pure nextGhost := by
  classical
  let _ := Fintype.ofFinite Player
  intro count
  induction count with
  | zero =>
      intro rank origin frame covered bounded publications
      refine ⟨origin, by simpa using frame, ?_⟩
      simp only [Nat.add_zero, Nat.zero_add]
      refine ⟨covered, rfl, ?_⟩
      intro source revelations registry ghost checkpoint inputs reachable history historyAt
      exact ⟨source, ghost, revelations, registry, checkpoint, reachable,
        ⟨history, historyAt⟩, rfl⟩
  | succ count ih =>
      intro rank origin frame covered bounded publications
      rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding,
        refsBefore, aligned, admitted, authentic, supports, opens, lift, commutes, steps,
        injective, transport, originalCheckpoint⟩
      have counted := aligned.graphSuffix.countEq
      change rank + eventCount program = setup.informationGraph.order.eventCount at counted
      cases program with
      | ret payoffs =>
          simp only [eventCount] at counted
          omega
      | @sample Γ names name payload fresh law next =>
          let index : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
          have atRank : (embedding.event index).val = rank := by
            simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have publication := publications (embedding.event index) atRank.symm.le (by omega)
          have layout : setup.informationGraph.outputLayout (embedding.event index) =
              .publicData payload := (embedding.layout_eq index).trans rfl
          rw [layout] at publication
          exact publication.elim
      | @commit Γ names name owner payload fresh guard next =>
          let index : Fin (eventCount (.commit name owner fresh guard next)) :=
            ⟨0, by simp [eventCount]⟩
          have atRank : (embedding.event index).val = rank := by
            simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have publication := publications (embedding.event index) atRank.symm.le (by omega)
          have layout : setup.informationGraph.outputLayout (embedding.event index) =
              .binding owner payload := (embedding.layout_eq index).trans rfl
          rw [layout] at publication
          exact publication.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          let frame : SourceResidual setup (setup.decodeBehavioralProfile
              (CommitmentInterface.forfeiture setup.program) target) rank origin :=
            ⟨Γ, names, .reveal published owner name fresh selected unresolved next, residualProfile,
              original, refs, embedding, refsBefore, aligned, admitted, authentic, supports,
              opens,
              lift, commutes, steps, injective, transport, originalCheckpoint⟩
          let index : Fin (eventCount
              (.reveal published owner name fresh selected unresolved next)) :=
            ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have atRank : event.val = rank := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : setup.informationGraph.outputLayout event = .publication payload :=
            (embedding.layout_eq index).trans rfl
          have decoded : decodeEventAction setup.program event
              (cast (congrArg EventField.Action outputEq.symm) true) =
                some (.reveal owner name true) := by
            simpa [index, event, outputEq, decodeEventAction] using aligned.actionEq index
              (cast (congrArg EventField.Action outputEq.symm) true)
          let head := representativeRevealTail frame fresh selected unresolved next rfl
          have headCovered : head.refs.CoversPrefix setup.program (rank + 1) :=
            covered.cons setup.program (name := published) (cell := .publication payload)
              ⟨.inr event, outputEq⟩ event rfl atRank
          obtain ⟨endOrigin, tail, tailCovered, tailCount, advance⟩ := ih (rank + 1) _ head
            headCovered (by omega) (fun node lower upper => publications node (by omega) (by omega))
          have rankEq : rank + 1 + count = rank + (count + 1) := by omega
          rw [← rankEq]
          refine ⟨endOrigin, tail, tailCovered, ?_, ?_⟩
          · change eventCount (.reveal published owner name fresh selected unresolved next) = _
            change eventCount next = count + eventCount tail.program at tailCount
            simp only [eventCount]
            omega
          · intro source revelations registry ghost checkpoint inputs reachable history historyAt
            have ready : ghost.cut.Ready event := by
              have ordered := checkpoint.ordered
              rw [← atRank] at ordered
              exact ordered.ready event.isLt
            let actual := residualAt frame source revelations registry ghost checkpoint
            have atGhost : history.state = sourceServicePrefix? setup rank ghost :=
              historyAt.trans actual.decode.symm
            have clear := actual.clear_of_intended_history wellFormed history atGhost
            have active : owner ∉ ghost.defaulted := by rw [clear]; simp
            have sourceActive : owner ∉ source.defaulted := by
              have status := congrArg DefaultHistory.defaulted checkpoint.defaults
              change ghost.defaulted = source.defaulted at status
              rw [← status]
              exact active
            let sourceAfter := revealSuccessor published selected source true
            let ghostAfter := ghost.complete event ready
              (cast (congrArg EventField.Action outputEq.symm) true)
              (cast (congrArg EventField.Value outputEq.symm)
                (disclosureResult published selected source true))
            have nextCheckpoint : SourceCheckpoint setup sourceAfter head.refs (rank + 1)
                ghostAfter := checkpoint.reveal (native := configState ghost) published selected
              event atRank ready outputEq (fun ref => refsBefore ref index) true decoded
            have codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
                (setup.informationGraph.nodes event) = .resolve owner payload (refs.get selected)
                  (compileChecks (published := published) refs source.registry source.revelations
                    selected) := by
              rw [revelations, registry]
              simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
            have status : ghost.defaulted = source.defaulted :=
              congrArg DefaultHistory.defaulted checkpoint.defaults
            have stepLaw : ghost.step event ready
                (cast (congrArg EventField.Action outputEq.symm) true) = PMF.pure ghostAfter := by
              simpa only [ghostAfter, status, disclosureResult, revealSuccessor, Env.get,
                Env.cons] using
                reveal_step ghost event ready outputEq refs source.revelations source.registry
                  selected codeEq source.state checkpoint.agrees true
            have graphStep : ghostAfter ∈ (ghost.step event ready
                (cast (congrArg EventField.Action outputEq.symm) true)).support := by
              rw [stepLaw]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
            have afterReach : ghostAfter.Reachable inputs :=
              Config.Step.path_reachable (.single ⟨event, ready, _, graphStep⟩) reachable
            have residualOpens := actual.disclosing disclosing owner
            have kernel : revealKernel residualProfile (source.view owner) sourceActive =
                PMF.pure true := eq_pure_true_of_false_not_mem
                  (residualOpens.1 rfl (source.view owner) sourceActive)
            have sourceStep : Sum.inr (ProtocolState.entry next sourceAfter) ∈
                (ProtocolState.behavioralStateStep
                  (.reveal published owner name fresh selected unresolved next) residualProfile
                  (.inl source)).support := by
              have activeView : owner ∉ (source.view owner).defaulted := sourceActive
              rw [ProtocolState.behavioralStateStep_reveal_entry, dite_eq_right activeView,
                kernel, PMF.pure_map]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
            obtain ⟨nextHistory, nextHistoryAt⟩ := actual.intendedHistory_of_step intended target
              agrees history atGhost _ sourceStep
            have afterRevelations : @sourceAfter.revelations = @head.source.revelations := by
              change @(revealSuccessor published selected source true).revelations =
                @(revealSuccessor published selected original true).revelations
              simp only [revealSuccessor_revelations, revelations]
            have afterRegistry : sourceAfter.registry = head.source.registry := by
              change source.registry.weaken = original.registry.weaken
              rw [registry]
            obtain ⟨finalSource, finalGhost, finalRevelations, finalRegistry, finalCheckpoint,
              finalReach, finalHistory, finalLaw⟩ := advance sourceAfter afterRevelations
                afterRegistry ghostAfter nextCheckpoint inputs afterReach nextHistory nextHistoryAt
            refine ⟨finalSource, finalGhost, finalRevelations, finalRegistry,
              finalCheckpoint, finalReach, finalHistory, ?_⟩
            have actor : setup.informationGraph.actor? event = some owner := by
              have law := (decodeEventAction_owner setup.program event
                (cast (congrArg EventField.Action outputEq.symm) true)).symm
              rw [eventOwner?_eq_actor] at law
              simpa [decoded, sourceActionOwner] using law
            have least : ∀ other, other ∉ ghost.cut.completed → event.val ≤ other.val := by
              intro other missing
              rw [atRank]
              exact Nat.le_of_not_gt fun lower =>
                missing ((checkpoint.ordered.2 other).mpr lower)
            rw [runPlan_canonical_actor _ count ghost event ready least owner actor active,
              compilePrescribedProfile_publication setup.program setup.informationDependencies _
                disclosing owner event actor (by rw [outputEq]; trivial),
              EventGraphRuntime.openAction_eq_cast_true outputEq, PMF.pure_bind, stepLaw,
              PMF.pure_bind]
            exact finalLaw

end Vegas

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private theorem publication_surviving_endpoint_boundary
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    (boundary : PhaseBoundary scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start origin)
    (donor : (serviceGraph setup deps).Config) (ordered : donor.cut.IsPrefix finish)
    (law : outcomeLaw profile Config.defaulted donor = PMF.pure ∅)
    (potential : canonicalLaw profile origin.application.config = canonicalLaw profile donor)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config) horizon origin).support)
    (survived : focal ∉ final.application.config.defaulted) :
    CompletionBoundary setup leaks scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      finish final ∧ final.environmentRecall.length ≤ horizon ∧
      runKey final.application.config = runKey donor := by
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  obtain ⟨_finalClear, key⟩ := publication_surviving_endpoint_key scheduler bound relaxed contract
    timely profile reference independent opens focal deviation run origin boundary donor ordered
    law potential final reached survived
  have finalOrdered : final.application.config.cut.IsPrefix finish := by
    have cuts : final.application.config.cut = donor.cut := congrArg Prod.fst key
    rw [cuts]
    exact ordered
  obtain ⟨finalSupport, finalBound⟩ := runUntilHorizon_bounded boundary.supported boundary.bounded
    reached
  have originLaw : outcomeLaw profile Config.defaulted origin.application.config = PMF.pure ∅ :=
    (outcomeLaw_eq_of_canonicalLaw_eq Config.defaulted
      (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal))
      potential).trans law
  have originClear := defaulted_eq_empty_of_outcomeLaw profile _ originLaw
  have originInside : InBlock start finish origin.application.config := by
    refine ⟨boundary.earlier, ?_⟩
    intro event later completed
    obtain ⟨_record, _value, owner, _owned, inactive⟩ :=
      boundary.later event (by have := run.nonempty; omega) completed
    rw [originClear] at inactive
    simp at inactive
  have untouched := blockRun_untouched (run.shaped relaxed) scheduler players
    (fun current => BlockDone finish current.application.config) (fun _ done => done)
    (horizon - origin.environmentRecall.length) origin final originInside
    (fun event later => boundary.seen.untouched
      (show ¬ event.val < start by have := run.nonempty; omega)) reached
  exact ⟨⟨finalSupport, finalOrdered, untouched⟩, finalBound, key⟩

private theorem publication_surviving_phase_posterior
    {Seed Source View Next NextView : Type} {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (reference : Seed → (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (advance : Source → Next) (nextView : Next → NextView)
    (donor : Next → (serviceGraph setup deps).Config)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (noise : View → PMF (MessageNetwork Player
        (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)))
    (factor : prior.map (fun seed => (source seed,
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map source).bind fun current =>
        (noise (observe current)).map fun extra => (current, extra))
    (boundary : ∀ seed ∈ prior.support, PhaseBoundary scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (reference seed))) focal deviation)
      horizon start (execution seed))
    (reachable : ∀ seed ∈ prior.support,
      ∃ inputs, (donor (advance (source seed))).Reachable inputs)
    (ordered : ∀ seed ∈ prior.support, (donor (advance (source seed))).cut.IsPrefix finish)
    (defaultLaw : ∀ seed ∈ prior.support,
      outcomeLaw profile Config.defaulted (donor (advance (source seed))) = PMF.pure ∅)
    (potential : ∀ seed ∈ prior.support,
      canonicalLaw profile (execution seed).application.config =
        canonicalLaw profile (donor (advance (source seed))))
    (reflects : ∀ left ∈ (prior.map source).support, ∀ right ∈ (prior.map source).support,
      nextView (advance left) = nextView (advance right) → observe left = observe right)
    (visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      nextView (advance (source left)) = nextView (advance (source right)) →
      keyView focal (runKey (donor (advance (source left)))) =
        keyView focal (runKey (donor (advance (source right))))) :
    let app := serviceApplication setup deps duration leaks
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (reference seed))) focal deviation
    let phase := fun seed => app.runUntilHorizon scheduler (players seed)
      (fun current => BlockDone finish current.application.config) horizon (execution seed)
    let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
    let good := fun entry : Seed × app.Execution => decide (focal ∉
      entry.2.application.config.defaulted)
    ∀ _present : true ∈ (staged.map good).support,
    let accepted := fiberPosterior staged good true
    ∃ nextNoise : NextView → PMF (MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)),
      (accepted.map (fun entry => (advance (source entry.1),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal entry.2))) =
        ((accepted.map (fun entry => advance (source entry.1))).bind fun current =>
          (nextNoise (nextView current)).map fun observed => (current, observed)) ∧
      ∀ entry ∈ accepted.support,
        CompletionBoundary setup leaks scheduler (players entry.1) finish entry.2 ∧
          entry.2.environmentRecall.length ≤ horizon ∧
          runKey entry.2.application.config = runKey (donor (advance (source entry.1))) := by
  classical
  intro app players phase staged good present accepted
  let traffic := (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
  obtain ⟨optionalNoise, optionalLaw⟩ := publication_surviving_joint
    (setup := setup) (deps := deps) (duration := duration) (leaks := leaks)
    (Seed := Seed) (Source := Source) (View := View) (Next := Next) (NextView := NextView)
    scheduler bound relaxed
    contract timely profile reference independent opens focal deviation run prior source observe
    advance nextView donor execution noise factor boundary reachable ordered defaultLaw potential
    reflects visible
  have joint : (staged.map (fun entry => (advance (source entry.1),
      if good entry then some (traffic entry.2) else none))) =
      ((prior.map source).map advance).bind fun current =>
        (optionalNoise (nextView current)).map fun extra => (current, extra) := by
    rw [PMF.map_bind]
    have same : ∀ seed ∈ prior.support,
        (phase seed).map (fun final => (advance (source seed),
          if good (seed, final) then some (traffic final) else none)) =
        (phase seed).map (fun final => (advance (source seed),
          if focal ∈ final.application.config.defaulted then none else some (traffic final))) := by
      intro seed _
      apply map_congr_on_support _
      intro final _
      by_cases failed : focal ∈ final.application.config.defaulted <;>
        simp only [good, failed, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          not_false_eq_true, decide_true]
    have converted := bind_congr_on_support prior same
    simpa only [staged, phase, players, traffic, PMF.map_bind, PMF.map_comp,
      Function.comp_def] using converted.trans optionalLaw
  have conditional := surviving_channel_posterior staged ((prior.map source).map advance)
    (fun entry => advance (source entry.1)) (fun entry => traffic entry.2) good nextView
      optionalNoise
    (traffic (execution prior.support_nonempty.choose)) joint present
  let goodNoise := fun view : NextView =>
    (fiberPosterior (optionalNoise view) Option.isSome true).map
      (fun extra => extra.getD (traffic (execution prior.support_nonempty.choose)))
  refine ⟨goodNoise, ?_, ?_⟩
  · exact conditional
  intro entry supported
  obtain ⟨selectedGood, stagedSupported⟩ := mem_support_fiberPosterior present supported
  obtain ⟨seed, seedSupported, finalSupported⟩ := (PMF.mem_support_bind_iff _ _ _).mp
    stagedSupported
  obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp finalSupported
  cases same
  have survived : focal ∉ final.application.config.defaulted := of_decide_eq_true selectedGood
  exact publication_surviving_endpoint_boundary
    (setup := setup) (deps := deps) (duration := duration) (leaks := leaks)
    scheduler bound relaxed contract timely
    profile (reference seed) independent opens focal deviation run (execution seed)
    (boundary seed seedSupported) (donor (advance (source seed))) (ordered seed seedSupported)
    (defaultLaw seed seedSupported) (potential seed seedSupported) final reached survived

private theorem native_block_expected_comparison
    {Seed Parameter : Type} {horizon turns start finish tailCount : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (reference : setup.informationGraph.BehavioralProfile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (prior : PMF Seed) (members : Seed → (serviceGraph setup deps).BehavioralProfile)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (before after : Seed → setup.informationGraph.Config)
    (lower : start ≤ finish) (bounded : finish ≤ setup.informationGraph.order.eventCount)
    (prefixAt : ∀ seed ∈ prior.support, (before seed).cut.IsPrefix start)
    (headLaw : ∀ seed ∈ prior.support,
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
          setup.informationGraph.canonicalScheduler) (finish - start) (before seed) =
        PMF.pure (after seed)) :
    let app := serviceApplication setup deps duration leaks
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps)
          (effectiveOpening ((serviceGraph setup deps).prefixProfile (members seed))))
            focal deviation
    let nativePayoff := fun final : app.Execution => setup.graphForfeitConfigPayoff deps parameter
      utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (leastUtility utility) focal
    let phase := fun seed => app.runUntilHorizon scheduler (players seed)
      (fun current => BlockDone finish current.application.config) horizon (execution seed)
    let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
    let good := fun entry : Seed × app.Execution =>
      decide (focal ∉ entry.2.application.config.defaulted)
    (∀ seed ∈ prior.support, PhaseBoundary scheduler (players seed) horizon start
      (execution seed)) →
    (∀ _present : true ∈ (staged.map good).support,
      ∃ policy : setup.informationGraph.BehavioralPolicy focal,
        let accepted := fiberPosterior staged good true
        expect (accepted.bind fun entry => app.runToHorizon scheduler (players entry.1) horizon
          entry.2) nativePayoff ≤
          expect (accepted.bind fun entry => setup.informationGraph.runPlan
            (setup.informationGraph.policyPlan (Function.update
              (setup.informationGraph.prefixProfile reference) focal policy)
              setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) sourcePayoff) →
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (prior.bind fun seed => app.runToHorizon scheduler (players seed) horizon
        (execution seed)) nativePayoff ≤
        expect (prior.bind fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (finish - start + tailCount)
              (before seed)) sourcePayoff := by
  classical
  intro app players nativePayoff sourcePayoff phase staged good boundary continues
  let nativeValue := fun entry : Seed × app.Execution =>
    expect (app.runToHorizon scheduler (players entry.1) horizon entry.2) nativePayoff
  let sourceValue := fun (policy : setup.informationGraph.BehavioralPolicy focal)
      (entry : Seed × app.Execution) => expect (setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) sourcePayoff
  obtain ⟨nativeBound, nativeNonnegative, nativeBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility range focal
  obtain ⟨sourceBound, sourceNonnegative, sourceBounded⟩ :=
    setup.graphPayoff_abs_bound setup.informationDependencies parameter utility range focal
  have nativePayoffBound : ∀ final : app.Execution, |nativePayoff final| ≤ nativeBound :=
    fun final => nativeBounded final.application.config
  have nativeValueBound : ∀ entry, |nativeValue entry| ≤ nativeBound := by
    intro entry
    exact expect_abs_le_of_bounded nativeNonnegative nativePayoffBound
  have sourceValueBound : ∀ policy entry, |sourceValue policy entry| ≤ sourceBound := by
    intro policy entry
    exact expect_abs_le_of_bounded sourceNonnegative sourceBounded
  have nativeIntegral (law : PMF app.Execution) : PayoffIntegrable law nativePayoff :=
    payoffIntegrable_of_bounded law nativePayoff nativePayoffBound
  have sourceIntegral (law : PMF setup.informationGraph.Config) :
      PayoffIntegrable law sourcePayoff :=
    payoffIntegrable_of_bounded law sourcePayoff sourceBounded
  have nativeTower (law : PMF (Seed × app.Execution)) :
      expect (law.bind fun entry => app.runToHorizon scheduler (players entry.1) horizon entry.2)
        nativePayoff = expect law nativeValue :=
    expect_bind_tower law _ nativePayoff (nativeIntegral _)
  have sourceTower (law : PMF (Seed × app.Execution)) (policy) :
      expect (law.bind fun entry => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) sourcePayoff =
        expect law (sourceValue policy) := expect_bind_tower law _ sourcePayoff (sourceIntegral _)
  obtain ⟨tailPolicy, tailCompare⟩ : ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      ∀ _present : true ∈ (staged.map good).support,
        expect (fiberPosterior staged good true) nativeValue ≤
          expect (fiberPosterior staged good true) (sourceValue policy) := by
    by_cases present : true ∈ (staged.map good).support
    · obtain ⟨policy, compare⟩ := continues present
      refine ⟨policy, fun _ => ?_⟩
      dsimp only at compare
      rw [nativeTower, sourceTower] at compare
      exact compare
    · exact ⟨(setup.informationGraph.prefixProfile reference) focal,
        fun impossible => (present impossible).elim⟩
  have sourceFloor (entry : Seed × app.Execution) :
      leastUtility utility focal ≤ sourceValue tailPolicy entry := by
    have compare := expect_mono
      (μ := setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal tailPolicy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1))
      (f := fun _ => leastUtility utility focal) (g := sourcePayoff)
      (fun config _ => setup.leastUtility_le_graphPayoff setup.informationDependencies parameter
        utility range focal config) (payoffIntegrable_constant _ _) (sourceIntegral _)
    simpa only [expect_constant] using compare
  have stagedSupport (entry : Seed × app.Execution) (member : entry ∈ staged.support) :
      entry.1 ∈ prior.support ∧ entry.2 ∈ (phase entry.1).support := by
    obtain ⟨seed, selected, present⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    cases same
    exact ⟨selected, reached⟩
  have compare : expect staged nativeValue ≤ expect staged (sourceValue tailPolicy) := by
    apply expect_fiberwise_le staged good nativeValue (sourceValue tailPolicy)
      (payoffIntegrable_of_bounded staged _ nativeValueBound)
      (payoffIntegrable_of_bounded staged _ (sourceValueBound tailPolicy))
    intro selected possible
    cases selected with
    | true => exact tailCompare possible
    | false =>
        refine expect_mono (fun entry supported => ?_)
          (payoffIntegrable_of_bounded _ _ nativeValueBound)
          (payoffIntegrable_of_bounded _ _ (sourceValueBound tailPolicy))
        obtain ⟨failed, stagedMember⟩ := mem_support_fiberPosterior possible supported
        have defaulted : focal ∈ entry.2.application.config.defaulted := by
          by_contra active
          simp only [good, active] at failed
          cases failed
        obtain ⟨seedSupported, reached⟩ := stagedSupport entry stagedMember
        obtain ⟨currentSupported, currentBound⟩ := runUntilHorizon_bounded
          (boundary entry.1 seedSupported).supported (boundary entry.1 seedSupported).bounded
          reached
        exact (expect_runToHorizon_forfeit_le_of_defaulted scheduler contract (players entry.1)
          parameter utility range focal entry.2 currentSupported currentBound defaulted).trans
          (sourceFloor entry)
  obtain ⟨policy, splice⟩ := exists_canonical_policy_splice
    (setup.informationGraph.prefixProfile reference) focal
    ((setup.informationGraph.prefixProfile reference) focal) tailPolicy start (finish - start)
    tailCount (by omega)
  refine ⟨policy, ?_⟩
  have nativeLaw : (staged.bind fun entry => app.runToHorizon scheduler (players entry.1) horizon
      entry.2) = prior.bind fun seed => app.runToHorizon scheduler (players seed) horizon
        (execution seed) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed _
    exact (app.runToHorizon_eq_runUntilHorizon_bind scheduler (players seed)
      (fun current => BlockDone finish current.application.config) horizon (execution seed)).symm
  have sourceLaw : (prior.bind fun seed => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (finish - start + tailCount) (before seed)) =
      staged.bind (fun entry => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal tailPolicy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
    apply bind_congr_on_support _
    intro seed supported
    rw [splice (before seed) (prefixAt seed supported), Function.update_eq_self,
      headLaw seed supported, PMF.pure_bind]
  rw [← nativeTower, nativeLaw, ← sourceTower, ← sourceLaw] at compare
  exact compare

private theorem native_publication_expected_continuation
    {Seed Source View Parameter : Type} {horizon turns start finish : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {tailPoint : setup.informationGraph.Config}
    (tailFrame : SourceResidual setup wholeProfile finish tailPoint)
    (tailCovered : tailFrame.refs.CoversPrefix setup.program finish)
    (outer : nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation
      (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        final.application.config focal)
      (setup.graphPayoff setup.informationDependencies parameter utility
        (leastUtility utility) focal) tailFrame)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (run : RevealRun (serviceGraph setup deps) start finish)
    (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (advance : Source → Config Player L tailFrame.Γ × setup.informationGraph.Config)
    (members : Seed → (serviceGraph setup deps).BehavioralProfile)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (before : Seed → setup.informationGraph.Config)
    (noise : View → PMF (MessageNetwork Player
        (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)))
    (factor : prior.map (fun seed => (source seed,
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map source).bind fun current =>
        (noise (observe current)).map fun extra => (current, extra))
    (submitted : ∀ seed ∈ prior.support,
      (serviceGraph setup deps).SubmitsBindings (members seed))
    (future : ∀ seed ∈ prior.support, ∀ owner node actor observation active,
      finish ≤ node.val → members seed owner node actor observation active =
        reference owner node actor observation active)
    (boundary : ∀ seed ∈ prior.support, PhaseBoundary scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening
          ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation)
      horizon start (execution seed))
    (metadata : ∀ seed ∈ prior.support,
      @(advance (source seed)).1.revelations = @tailFrame.source.revelations)
    (registry : ∀ seed ∈ prior.support,
      (advance (source seed)).1.registry = tailFrame.source.registry)
    (checkpoint : ∀ seed ∈ prior.support, SourceCheckpoint setup (advance (source seed)).1
      tailFrame.refs finish (advance (source seed)).2)
    (reachable : ∀ seed ∈ prior.support,
      ∃ inputs, (advance (source seed)).2.Reachable inputs)
    (history : ∀ seed ∈ prior.support, ∃ intended : setup.intendedProtocol.History,
      intended.state = some (tailFrame.lift
        (ProtocolState.entry tailFrame.program (advance (source seed)).1)))
    (defaultLaw : ∀ seed ∈ prior.support, outcomeLaw profile Config.defaulted
      ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2) = PMF.pure ∅)
    (potential : ∀ seed ∈ prior.support,
      canonicalLaw profile (execution seed).application.config = canonicalLaw profile
        ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2))
    (reflects : ∀ left ∈ (prior.map source).support, ∀ right ∈ (prior.map source).support,
      (advance left).1.view focal = (advance right).1.view focal → observe left = observe right)
    (visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (advance (source left)).1.view focal = (advance (source right)).1.view focal →
      keyView focal (runKey
        ((serviceGraph setup deps).fromSequentialConfig (advance (source left)).2)) =
      keyView focal (runKey
        ((serviceGraph setup deps).fromSequentialConfig (advance (source right)).2)))
    (prefixAt : ∀ seed ∈ prior.support, (before seed).cut.IsPrefix start)
    (headLaw : ∀ seed ∈ prior.support, setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
        setup.informationGraph.canonicalScheduler) (finish - start) (before seed) =
      PMF.pure (advance (source seed)).2) :
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (prior.bind fun seed =>
        (serviceApplication setup deps duration leaks).runToHorizon scheduler
          (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
            (firstTurnTiming setup turns deps) (effectiveOpening
              ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation)
          horizon (execution seed))
        (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
          final.application.config focal) ≤
      expect (prior.bind fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler)
        (finish - start + eventCount tailFrame.program) (before seed))
        (setup.graphPayoff setup.informationDependencies parameter utility
          (leastUtility utility) focal) := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := fun seed => Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening
        ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation
  let phase := fun seed => app.runUntilHorizon scheduler (players seed)
    (fun current => BlockDone finish current.application.config) horizon (execution seed)
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  let good := fun entry : Seed × app.Execution => decide
    (focal ∉ entry.2.application.config.defaulted)
  have donorReach : ∀ seed ∈ prior.support, ∃ inputs,
      ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2).Reachable
        inputs := by
    intro seed supported
    obtain ⟨inputs, reached⟩ := reachable seed supported
    exact ⟨inputs, Config.Reachable.fromSequentialConfig (serviceGraph setup deps) reached⟩
  have donorOrdered : ∀ seed ∈ prior.support,
      ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2).cut.IsPrefix
        finish := by
    intro seed supported
    exact (checkpoint seed supported).ordered
  have survivors := publication_surviving_phase_posterior
    (setup := setup) (deps := deps) (duration := duration) (leaks := leaks)
    scheduler bound relaxed contract timely profile
    (fun seed => (serviceGraph setup deps).prefixProfile (members seed)) independent opens
    focal deviation run prior source observe advance (fun next => next.1.view focal)
    (fun next => (serviceGraph setup deps).fromSequentialConfig next.2) execution noise factor
    boundary donorReach donorOrdered defaultLaw potential reflects visible
  apply native_block_expected_comparison (tailCount := eventCount tailFrame.program)
    scheduler bound contract parameter utility range
    reference focal deviation prior members execution before (fun seed => (advance (source seed)).2)
    (Nat.le_of_lt run.nonempty) run.bounded prefixAt headLaw boundary
  intro present
  obtain ⟨nextNoise, nextFactor, nextBoundary⟩ := survivors present
  let accepted := fiberPosterior staged good true
  have acceptedSeed (entry : Seed × app.Execution) (supported : entry ∈ accepted.support) :
      entry.1 ∈ prior.support := by
    obtain ⟨_survived, stagedSupport⟩ := mem_support_fiberPosterior present supported
    obtain ⟨seed, seedSupport, finalSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp stagedSupport
    obtain ⟨final, _reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp finalSupport
    cases same
    exact seedSupport
  exact outer tailCovered accepted
    (fun entry => (advance (source entry.1)).1) (fun entry => (advance (source entry.1)).2)
    (fun entry supported => metadata entry.1 (acceptedSeed entry supported))
    (fun entry supported => registry entry.1 (acceptedSeed entry supported))
    (fun entry supported => checkpoint entry.1 (acceptedSeed entry supported))
    (fun entry supported => reachable entry.1 (acceptedSeed entry supported))
    (fun entry supported => history entry.1 (acceptedSeed entry supported))
    (fun entry => members entry.1)
    (fun entry supported => submitted entry.1 (acceptedSeed entry supported))
    (fun entry supported => future entry.1 (acceptedSeed entry supported)) Prod.snd
    (fun entry supported => (nextBoundary entry supported).1)
    (fun entry supported => (nextBoundary entry supported).2.1)
    (fun entry supported => (nextBoundary entry supported).2.2) nextNoise nextFactor

private theorem phaseBoundary_of_completionBoundary
    {horizon rank : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (clear : execution.application.config.defaulted = ∅) :
    PhaseBoundary scheduler players horizon rank execution := by
  refine ⟨boundary.supported, bounded,
    (fun event lower => (boundary.ordered.2 event).mpr lower), ?_, ?_, ?_⟩
  · intro event later completed
    exact ((Nat.not_lt.mpr later) ((boundary.ordered.2 event).mp completed)).elim
  · intro owner entry member event ready
    by_contra later
    exact boundary.untouched event (Nat.le_of_not_gt later) owner entry member ready
  · intro completion member owner recorded
    have defaulted : owner ∈ execution.application.config.defaulted :=
      (mem_defaulted_iff_completionOf _ _).mpr ⟨completion.event, by
        rw [(completionOf_eq_some_iff _ _ _).mpr ⟨member, rfl⟩]
        exact recorded⟩
    rw [clear] at defaulted
    simp at defaulted

private theorem canonicalLaw_eq_of_pure_prefix {graph : EventGraph Player L}
    (profile : graph.BehavioralProfile) (before after : graph.Config) (start finish : Nat)
    (lower : start ≤ finish) (beforeOrdered : before.cut.IsPrefix start)
    (afterOrdered : after.cut.IsPrefix finish)
    (head : graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
      (finish - start) before = PMF.pure after) :
    canonicalLaw profile before = canonicalLaw profile after := by
  have remaining : before.remaining = finish - start + after.remaining := by
    have finishBound := afterOrdered.1
    simp only [Config.remaining, beforeOrdered.card, afterOrdered.card]
    omega
  unfold canonicalLaw
  rw [remaining, graph.runPlan_add, head, PMF.pure_bind]

private theorem nativeSourceContinuation_public [Finite Player]
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (wellFormed : setup.WellFormed)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) start origin)
    (run : RevealRun (serviceGraph setup deps) start finish)
    (outer : ∀ {tailPoint : setup.informationGraph.Config}
      (tail : SourceResidual setup (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target) finish tailPoint),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
        (setup.informationGraph.submitProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)))
        focal deviation
        (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
          final.application.config focal)
        (setup.graphPayoff setup.informationDependencies parameter utility
          (leastUtility utility) focal) tail) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      (setup.informationGraph.submitProfile (compileEventProfile setup.program
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)))
      focal deviation
      (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        final.application.config focal)
      (setup.graphPayoff setup.informationDependencies parameter utility
        (leastUtility utility) focal) frame := by
  classical
  let G := serviceGraph setup deps
  let wholeProfile := setup.decodeBehavioralProfile
    (CommitmentInterface.forfeiture setup.program) target
  let reference := setup.informationGraph.submitProfile
    (compileEventProfile setup.program wholeProfile)
  let profile : G.BehavioralProfile := compilePrescribedProfile setup.program deps wholeProfile
  have rawOpens (owner : Player) (event : G.EventId) (actor : G.actor? event = some owner)
      (publication : (G.outputLayout event).IsPublication) (observation : G.PlayerObservation owner)
      (active : owner ∉ observation.defaulted) :
      G.submitProfile (compileEventProfile setup.program wholeProfile) owner event actor
        observation active = PMF.pure (EventField.openAction _ publication) := by
    change (compileEventPolicy setup.program owner (wholeProfile owner) event actor observation
      active).map (EventField.submitAction _) = _
    rw [compileEventPolicy_publication setup.program owner (wholeProfile owner)
      (disclosing owner) event actor publication, PMF.pure_map]
    congr 1
    exact EventField.submitAction_eq_self _ _
      (EventField.submitted_of_publication _ publication _)
  have independent : ReadyIndependent profile :=
    relaxed.readyIndependent_prefixProfile
      (G.submitProfile (compileEventProfile setup.program wholeProfile))
      (fun owner event actor publication left right leftActive rightActive =>
        (rawOpens owner event actor publication left leftActive).trans
          (rawOpens owner event actor publication right rightActive).symm)
  have opens : OpensPublications profile := by
    intro config event owner actor publication active
    exact compilePrescribedProfile_publication setup.program deps wholeProfile disclosing
      owner event actor publication _ _
  intro covered Seed prior source ghost metadata registry checkpoint reachable history members
    submitted future execution players boundary budget keys noise factor
  have typed := exists_reveal_prefix_source_frame wellFormed intended target agrees disclosing
    (finish - start) start origin frame covered (by
      rw [Nat.add_sub_of_le (Nat.le_of_lt run.nonempty)]
      exact run.bounded)
      (fun event lower upper => run.publications event lower (by have := run.nonempty; omega))
  rw [show start + (finish - start) = finish by have := run.nonempty; omega] at typed
  obtain ⟨endOrigin, tail, tailCovered, countEq, advanceExists⟩ := typed
  let valid := fun hidden : Config Player L frame.Γ × setup.informationGraph.Config =>
    @hidden.1.revelations = @frame.source.revelations ∧
      hidden.1.registry = frame.source.registry ∧
      SourceCheckpoint setup hidden.1 frame.refs start hidden.2 ∧
      (∃ inputs, hidden.2.Reachable inputs) ∧
      ∃ intendedHistory : setup.intendedProtocol.History,
        intendedHistory.state = some (frame.lift (ProtocolState.entry frame.program hidden.1))
  let nextValid := fun (hidden : Config Player L frame.Γ × setup.informationGraph.Config)
      (next : Config Player L tail.Γ × setup.informationGraph.Config) =>
    @next.1.revelations = @tail.source.revelations ∧
      next.1.registry = tail.source.registry ∧
      SourceCheckpoint setup next.1 tail.refs finish next.2 ∧
      (∃ inputs, next.2.Reachable inputs) ∧
      (∃ intendedHistory : setup.intendedProtocol.History,
        intendedHistory.state = some (tail.lift (ProtocolState.entry tail.program next.1))) ∧
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
          setup.informationGraph.canonicalScheduler) (finish - start) hidden.2 = PMF.pure next.2
  have nextExists (hidden : Config Player L frame.Γ × setup.informationGraph.Config)
      (supported : valid hidden) : ∃ next, nextValid hidden next := by
    obtain ⟨reveals, names, check, ⟨inputs, reach⟩, intendedHistory, atHistory⟩ := supported
    obtain ⟨nextSource, nextGhost, nextMetadata, nextRegistry, nextCheckpoint, nextReach,
      nextHistory, law⟩ := advanceExists hidden.1 reveals names hidden.2 check inputs reach
        intendedHistory atHistory
    exact ⟨(nextSource, nextGhost), nextMetadata, nextRegistry, nextCheckpoint,
      ⟨inputs, nextReach⟩, nextHistory, law⟩
  let advance := fun hidden => if supported : valid hidden then
    (nextExists hidden supported).choose else (tail.source, endOrigin)
  have nextFacts (hidden : Config Player L frame.Γ × setup.informationGraph.Config)
      (supported : valid hidden) : nextValid hidden (advance hidden) := by
    dsimp only [advance]
    rw [dite_eq_left supported]
    exact (nextExists hidden supported).choose_spec
  have currentValid (seed : Seed) (supported : seed ∈ prior.support) :
      valid (source seed, ghost seed) :=
    ⟨metadata seed supported, registry seed supported, checkpoint seed supported,
      reachable seed supported, history seed supported⟩
  have endFacts (seed : Seed) (supported : seed ∈ prior.support) :
      nextValid (source seed, ghost seed) (advance (source seed, ghost seed)) :=
    nextFacts _ (currentValid seed supported)
  have endPath (seed : Seed) (supported : seed ∈ prior.support) :
      Relation.ReflTransGen Config.Step (ghost seed) (advance (source seed, ghost seed)).2 := by
    apply runPlan_graph_steps
      (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
        setup.informationGraph.canonicalScheduler) (finish - start)
    rw [(endFacts seed supported).2.2.2.2.2]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have endClear (seed : Seed) (supported : seed ∈ prior.support) :
      (advance (source seed, ghost seed)).2.defaulted = ∅ := by
    obtain ⟨reveals, names, check, _reach, ⟨intendedHistory, atHistory⟩, _law⟩ :=
      endFacts seed supported
    let actual := residualAt tail (advance (source seed, ghost seed)).1 reveals names
      (advance (source seed, ghost seed)).2 check
    exact actual.clear_of_intended_history wellFormed intendedHistory
      (atHistory.trans actual.decode.symm)
  have endLaw (seed : Seed) (supported : seed ∈ prior.support) :
      outcomeLaw profile Config.defaulted
        (G.fromSequentialConfig (advance (source seed, ghost seed)).2) = PMF.pure ∅ := by
    obtain ⟨reveals, names, check, ⟨inputs, reach⟩, ⟨intendedHistory, atHistory⟩, _law⟩ :=
      endFacts seed supported
    let actual := residualAt tail (advance (source seed, ghost seed)).1 reveals names
      (advance (source seed, ghost seed)).2 check
    exact actual.prescribed_defaultLaw_fromSequential deps wellFormed
      (CommitmentInterface.forfeiture setup.program) intended target agrees submits reach
      intendedHistory (atHistory.trans actual.decode.symm)
  have phaseBoundary (seed : Seed) (supported : seed ∈ prior.support) :
      PhaseBoundary scheduler (players seed) horizon start (execution seed) := by
    obtain ⟨intendedHistory, atHistory⟩ := history seed supported
    let actual := residualAt frame (source seed) (metadata seed supported) (registry seed supported)
      (ghost seed) (checkpoint seed supported)
    have ghostClear := actual.clear_of_intended_history wellFormed intendedHistory
      (atHistory.trans actual.decode.symm)
    have clear := defaulted_eq_of_completionOf_eq
      (congrArg (fun key => key.2.2) (keys seed supported))
    rw [G.fromSequentialConfig_defaulted, ghostClear] at clear
    exact phaseBoundary_of_completionBoundary scheduler (players seed) (execution seed)
      (boundary seed supported) (budget seed supported) clear
  have potential (seed : Seed) (supported : seed ∈ prior.support) :
      canonicalLaw profile (execution seed).application.config =
        canonicalLaw profile (G.fromSequentialConfig (advance (source seed, ghost seed)).2) := by
    have headLaw := G.runPlan_canonical_fromSequential
      (setup.informationGraph.prefixProfile reference) (finish - start) (ghost seed)
    change (setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
        setup.informationGraph.canonicalScheduler) (finish - start) (ghost seed)).map
          G.fromSequentialConfig =
        G.runPlan (G.policyPlan profile G.canonicalScheduler) (finish - start)
          (G.fromSequentialConfig (ghost seed)) at headLaw
    rw [(endFacts seed supported).2.2.2.2.2, PMF.pure_map] at headLaw
    exact (independent.canonicalLaw_congr _ _ _ rfl (keys seed supported)).trans
      (canonicalLaw_eq_of_pure_prefix profile _ _ start finish (Nat.le_of_lt run.nonempty)
        (checkpoint seed supported).ordered (endFacts seed supported).2.2.1.ordered
        headLaw.symm)
  have reflects : ∀ left ∈ (prior.map (fun seed => (source seed, ghost seed))).support,
    ∀ right ∈ (prior.map (fun seed => (source seed, ghost seed))).support,
    (advance left).1.view focal = (advance right).1.view focal →
      left.1.view focal = right.1.view focal := by
    intro left leftSupported right rightSupported same
    obtain ⟨leftSeed, leftMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp leftSupported
    obtain ⟨rightSeed, rightMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rightSupported
    obtain ⟨_leftInputs, leftReach⟩ := reachable leftSeed leftMember
    obtain ⟨_rightInputs, rightReach⟩ := reachable rightSeed rightMember
    exact SourceCheckpoint.sourceView_reflects_at_path_end frame.refs tail.refs start finish
      tailCovered focal (source leftSeed) (source rightSeed)
      (advance (source leftSeed, ghost leftSeed)).1
      (advance (source rightSeed, ghost rightSeed)).1 (ghost leftSeed) (ghost rightSeed)
      (advance (source leftSeed, ghost leftSeed)).2
      (advance (source rightSeed, ghost rightSeed)).2 leftReach rightReach
      (endPath leftSeed leftMember) (endPath rightSeed rightMember)
      (by rw [endClear leftSeed leftMember]; simp)
      (by rw [endClear rightSeed rightMember]; simp)
      (checkpoint leftSeed leftMember) (checkpoint rightSeed rightMember)
      (endFacts leftSeed leftMember).2.2.1 (endFacts rightSeed rightMember).2.2.1 same
  have visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
    (advance (source left, ghost left)).1.view focal =
      (advance (source right, ghost right)).1.view focal →
    keyView focal (runKey (G.fromSequentialConfig (advance (source left, ghost left)).2)) =
      keyView focal (runKey (G.fromSequentialConfig (advance (source right, ghost right)).2)) := by
    intro left leftSupported right rightSupported same
    obtain ⟨_leftInputs, leftReach⟩ := (endFacts left leftSupported).2.2.2.1
    obtain ⟨_rightInputs, rightReach⟩ := (endFacts right rightSupported).2.2.2.1
    exact SourceCheckpoint.keyView_eq_of_sourceView tail.refs finish tailCovered focal
      (advance (source left, ghost left)).1 (advance (source right, ghost right)).1
      (advance (source left, ghost left)).2 (advance (source right, ghost right)).2
      leftReach rightReach (by rw [endClear left leftSupported]; simp)
      (by rw [endClear right rightSupported]; simp)
      (endFacts left leftSupported).2.2.1 (endFacts right rightSupported).2.2.1 same
  obtain ⟨policy, compare⟩ := native_publication_expected_continuation scheduler bound relaxed
    contract timely parameter utility range wholeProfile reference focal deviation tail tailCovered
    (outer tail) profile independent opens run prior (fun seed => (source seed, ghost seed))
    (fun hidden => hidden.1.view focal) advance members execution ghost noise factor submitted
    (fun seed supported owner node actor observation active lower => future seed supported owner
      node actor observation active (by have := run.nonempty; omega)) phaseBoundary
    (fun seed supported => (endFacts seed supported).1)
    (fun seed supported => (endFacts seed supported).2.1)
    (fun seed supported => (endFacts seed supported).2.2.1)
    (fun seed supported => (endFacts seed supported).2.2.2.1)
    (fun seed supported => (endFacts seed supported).2.2.2.2.1)
    endLaw potential reflects visible (fun seed supported => (checkpoint seed supported).ordered)
    (fun seed supported => (endFacts seed supported).2.2.2.2.2)
  refine ⟨policy, ?_⟩
  rw [countEq]
  exact compare

end Vegas

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem roundsFrom_effective_reference_support_of_untouched
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (left right : (serviceGraph setup deps).BehavioralProfile)
    (changed : (serviceGraph setup deps).EventId → Prop)
    (same : ∀ who event actor observation active, ¬ changed event →
      left who event actor observation active = right who event actor observation active)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (count : Nat) (after : (serviceApplication setup deps duration leaks).Execution)
    (unseen : ∀ event, changed event → Untouched setup leaks event after)
    (reached : after ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps)
          (effectiveOpening ((serviceGraph setup deps).prefixProfile left)))
          focal deviation) count).support) :
    after ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps)
          (effectiveOpening ((serviceGraph setup deps).prefixProfile right)))
          focal deviation) count).support := by
  have kernels : ∀ who event actor observation active, ¬ changed event →
      effectiveOpening left who event actor observation active =
        effectiveOpening right who event actor observation active := by
    intro who event actor observation active outside
    cases node : nodeView (serviceGraph setup deps) event with
    | bind owner payload outputEq codeEq =>
        simpa only [effectiveOpening, node] using same who event actor observation active outside
    | sample payload law outputEq codeEq =>
        simpa only [effectiveOpening, node] using same who event actor observation active outside
    | resolve owner payload binding checks outputEq codeEq =>
        simp only [effectiveOpening, node]
  have support := roundsFrom_reference_support_of_untouched scheduler bound turns
    (effectiveOpening left) (effectiveOpening right) changed kernels focal deviation count after
      unseen (by simpa only [prefixProfile_effectiveOpening] using reached)
  simpa only [prefixProfile_effectiveOpening] using support

private theorem runUntil_false_eq_runRounds
    (app : ReactiveApplication Player) (scheduler : app.Scheduler) (players : Player → app.Policy)
    (count : Nat) (execution : app.Execution) :
    app.runUntil scheduler players (fun _ => False) count execution =
      app.runRounds scheduler players count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      simp only [ReactiveApplication.runUntil, ite_false, ReactiveApplication.runRounds]
      apply bind_congr_on_support _
      intro next _
      exact ih next

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem optional_binding_value_cast {field : EventField Player L}
    {owner : Player} {payload : L.Ty} (binding : field = .binding owner payload)
    (stored : Option field.Value) (value : PublicationResult (L.Val payload))
    (filled : stored = some (cast (congrArg EventField.Value binding.symm) value)) :
    cast (congrArg (fun kind => Option kind.Value) binding) stored = some value := by
  cases binding
  exact filled

private theorem nativeSourceContinuation_of_binding_interval
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (start finish : Nat) {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile start point)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered) (wellFormed : setup.WellFormed)
    (lower : start ≤ finish) (bounded : finish ≤ (serviceGraph setup deps).order.eventCount)
    (bindings : ∀ event : (serviceGraph setup deps).EventId, start ≤ event.val →
      event.val < finish → ∃ owner payload,
        (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (barrier : ∀ event : (serviceGraph setup deps).EventId, event.val = finish →
      ((serviceGraph setup deps).outputLayout event).IsPublic)
    (continuation : nativeBindingContinuation setup deps duration leaks horizon scheduler bound
      turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff start finish frame) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation nativePayoff sourcePayoff frame := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  intro covered Seed prior source ghost revelations registry checkpoints reachable histories members
    submitting future execution players boundary budget keys noise factor
  have informationBounded : finish ≤ setup.informationGraph.order.eventCount := bounded
  let count := finish - start
  have split : start + count = finish := Nat.add_sub_of_le lower
  let placeholder := setup.informationGraph.prefixProfile
    (Function.update reference focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal))
  let draw := fun config : setup.informationGraph.Config =>
    setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan placeholder setup.informationGraph.canonicalScheduler)
        count config
  let staged := prior.bind fun seed => (draw (ghost seed)).map fun table => (seed, table)
  let frozen := fun sample : Seed × setup.informationGraph.Config =>
    setup.informationGraph.freezeBindingsBefore (members sample.1) start finish sample.2
  let frozenPlayers := fun sample : Seed × setup.informationGraph.Config => Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile (frozen sample))))
        focal deviation
  have support (sample : Seed × setup.informationGraph.Config)
      (present : sample ∈ staged.support) :
      sample.1 ∈ prior.support ∧ sample.2 ∈ (draw (ghost sample.1)).support := by
    obtain ⟨seed, seedSupported, selected⟩ := (PMF.mem_support_bind_iff _ _ _).mp present
    obtain ⟨table, tableSupported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp selected
    cases same
    exact ⟨seedSupported, tableSupported⟩
  let currentResidual (seed : Seed) (present : seed ∈ prior.support) :=
    residualAt frame (source seed) (revelations seed present) (registry seed present)
      (ghost seed) (checkpoints seed present)
  have sourceClear (seed : Seed) (present : seed ∈ prior.support) :
      (ghost seed).defaulted = ∅ := by
    obtain ⟨history, state⟩ := histories seed present
    have decoded := (currentResidual seed present).decode
    change sourceServicePrefix? setup start (ghost seed) =
      some (frame.lift (ProtocolState.entry frame.program (source seed))) at decoded
    exact (currentResidual seed present).clear_of_intended_history wellFormed history
      (state.trans decoded.symm)
  have nativeClear (seed : Seed) (present : seed ∈ prior.support) :
      (execution seed).application.config.defaulted = ∅ := by
    have status := defaulted_eq_of_completionOf_eq
      (congrArg (fun key => key.2.2) (keys seed present))
    exact status.trans (sourceClear seed present)
  have rawTrace (seed : Seed) (present : seed ∈ prior.support) :
      Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) :=
    app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler (players seed)
      (execution seed).environmentRecall.length (budget seed present) (execution seed)
        (boundary seed present).supported
  have actualReach (seed : Seed) (present : seed ∈ prior.support) :
      ∃ inputs, (execution seed).application.config.Reachable inputs := by
    obtain ⟨trace⟩ := rawTrace seed present
    rw [serviceInitialLaw_eq_inputs setup] at trace
    obtain ⟨inputs, _, invariant⟩ := reactive_history_invariant
      (serviceTimeouts setup deps duration)
      leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler trace
    exact ⟨inputs, invariant.reachable⟩
  have discipline (raw : G.BehavioralProfile) (current : app.Execution)
      (present : current ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler
        (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile raw)))
            focal deviation) current.environmentRecall.length).support) :
      ∀ owner, owner ≠ focal → OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks current owner ∧
        CanonicalSlotsUsed setup leaks current owner ∧
          OwnFreshCalls setup leaks bound current owner ∧
          OneCallPerEvent setup leaks current owner := by
    intro owner foreign
    let clients := Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile raw))) focal deviation
    have follows : clients owner = turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile raw)) owner := by
      simp only [clients, Function.update_of_ne foreign]
    have slots := canonicalSlots_roundsFrom_reference relaxed.actorSerial scheduler clients owner
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile raw)) follows
        current.environmentRecall.length current present
    have calls := sourceServiceTurnPolicy_freshCalls_reference scheduler clients owner
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile raw)) follows
        current.environmentRecall.length current present
    exact ⟨slots.1, slots.2, calls.1, calls.2⟩
  have sourceLaws (seed : Seed) (present : seed ∈ prior.support) :
      setup.informationGraph.runPlan (setup.informationGraph.policyPlan
        (setup.informationGraph.prefixProfile (Function.update (members seed) focal
          (submittedFailurePolicy (graph := setup.informationGraph) focal)))
        setup.informationGraph.canonicalScheduler) count (ghost seed) = draw (ghost seed) := by
    apply runPlan_canonical_prefix_congr _ _ count start (ghost seed)
      (checkpoints seed present).ordered (by omega)
    intro event before after owner actor observation active
    simp only [placeholder, prefixProfile, prefixPolicy]
    by_cases own : owner = focal
    · subst owner
      simp only [Function.update_self]
    · simp only [Function.update_of_ne own]
      exact future seed present owner event actor _ _ before
  have anchorSupport (sample : Seed × setup.informationGraph.Config)
      (present : sample ∈ staged.support) :
      execution sample.1 ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler
        (frozenPlayers sample) (execution sample.1).environmentRecall.length).support := by
    apply roundsFrom_effective_reference_support_of_untouched scheduler bound turns
      (members sample.1) (frozen sample)
      (fun event => start ≤ event.val ∧ event.val < finish) _ focal deviation
      (execution sample.1).environmentRecall.length (execution sample.1) _
        (boundary sample.1 (support sample present).1).supported
    · intro owner event actor observation active outside
      simp only [frozen, freezeBindingsBefore, ite_eq_right outside]
    · intro event inside
      exact (boundary sample.1 (support sample present).1).untouched event inside.1
  have localSubmits (seed : Seed) (present : seed ∈ prior.support)
      (event : setup.informationGraph.EventId) (before : start ≤ event.val)
      (_after : event.val < start + count) (owner : Player) (actor)
      (observation : setup.informationGraph.PlayerObservation owner) (active)
      (action : setup.informationGraph.Action event)
      (selected : action ∈ (placeholder owner event actor observation active).support) :
      (setup.informationGraph.outputLayout event).Submitted action := by
    simp only [placeholder, prefixProfile, prefixPolicy] at selected
    by_cases own : owner = focal
    · subst owner
      simp only [Function.update_self] at selected
      exact (setup.informationGraph.policySubmitsBindings_submitPolicy focal _) event actor _ _
        action selected
    · simp only [Function.update_of_ne own] at selected
      rw [← future seed present owner event actor _ _ before] at selected
      exact submitting seed present owner event actor _ _ action selected
  have tableFrame (sample : Seed × setup.informationGraph.Config)
      (present : sample ∈ staged.support) :=
    runPlan_submitted_binding_frame placeholder count start (ghost sample.1)
      (checkpoints sample.1 (support sample present).1).ordered
      (sourceClear sample.1 (support sample present).1) (by omega)
      (localSubmits sample.1 (support sample present).1)
      (fun event before after => bindings event before (by omega)) sample.2
      (support sample present).2
  have tableFixed (sample : Seed × setup.informationGraph.Config)
      (present : sample ∈ staged.support) (event : G.EventId) (before : start ≤ event.val)
      (after : event.val < finish) (owner : Player) (payload : L.Ty)
      (binding : G.outputLayout event = .binding owner payload) (_foreign : owner ≠ focal) :
      ∃ result : PublicationResult (L.Val payload),
        completionOf sample.2 event = some (EventGraph.completion setup.informationGraph event
          (some (cast (congrArg EventField.Action binding.symm) (some result)))
          (cast (congrArg EventField.Value binding.symm) result)) ∧
        sample.2.outputs event = some (cast (congrArg EventField.Value binding.symm) result) ∧
        ∀ observation active, frozen sample owner event
          (EventCode.actor_eq_of_binding (G.nodes event) binding) observation active =
            PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)) := by
    obtain ⟨other, kind, outputEq, result, recorded, stored⟩ :=
      (tableFrame sample present).2.2.2.2 event before (by omega)
    rcases EventField.binding.inj (outputEq.symm.trans binding) with ⟨rfl, rfl⟩
    refine ⟨result, recorded, stored, ?_⟩
    intro observation active
    exact freezeBindingsBefore_binding (graph := setup.informationGraph)
      (members sample.1) start finish sample.2 _ event _
      observation active ⟨before, after⟩ binding result
        (optional_binding_value_cast binding _ result stored)
  have factorExtended := factor_extend_hidden_kernel prior (fun seed => (source seed, ghost seed))
    (fun seed => (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
      (execution seed))
    (fun state => state.1.view focal) noise factor (fun state => draw state.2)
  have baseMarginal : staged.map (fun sample => (source sample.1, ghost sample.1)) =
      prior.map (fun seed => (source seed, ghost seed)) := by
    simp only [staged, PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const]
    rfl
  have factorStaged : staged.map (fun sample =>
      (((source sample.1, ghost sample.1), bindingObservers focal sample.2),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution sample.1))) =
      (staged.map (fun sample => (source sample.1, ghost sample.1))).bind (fun state =>
        (draw state.2).bind fun table => (noise (state.1.view focal)).map fun observed =>
          ((state, bindingObservers focal table), observed)) := by
    rw [baseMarginal]
    have projected := congrArg (PMF.map fun pair =>
      ((pair.1.1, bindingObservers focal pair.1.2), pair.2)) factorExtended
    simpa only [staged, PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
      Function.comp_def] using projected
  have nativeLaw : prior.bind (fun seed => app.runToHorizon scheduler (players seed) horizon
      (execution seed)) = staged.bind (fun sample =>
        app.runToHorizon scheduler (frozenPlayers sample) horizon (execution sample.1)) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro seed present
    obtain ⟨inputs, actualReach⟩ := actualReach seed present
    obtain ⟨trace⟩ := rawTrace seed present
    have law := native_binding_unilateral_effective_source_mixture (turns := turns)
      (remaining := 0) scheduler bound relaxed (members seed) (submitting seed present) focal
      deviation (fun _ => False) (execution seed) actualReach (ghost seed) (keys seed present)
      start count (checkpoints seed present).ordered (sourceClear seed present) (by omega)
      (fun event before after => bindings event before (by omega))
      (fun owner foreign => (discipline (members seed) (execution seed)
        (boundary seed present).supported owner foreign).1)
      (fun owner _foreign event before _after _actor =>
        (boundary seed present).untouched event before)
      (by simpa only [Nat.zero_add] using trace)
    dsimp only at law
    rw [sourceLaws seed present, split] at law
    simpa only [players, frozenPlayers, frozen, ReactiveApplication.runToHorizon,
      runUntil_false_eq_runRounds, Function.comp_def] using law
  have comparison : ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (staged.bind fun sample => app.runToHorizon scheduler (frozenPlayers sample) horizon
        (execution sample.1)) nativePayoff ≤
      expect (staged.bind fun sample => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost sample.1))
        sourcePayoff := by
    refine continuation le_rfl lower bounded covered bindings barrier staged
      (fun sample => source sample.1) (fun sample => ghost sample.1) Prod.snd frozen
      (fun sample => execution sample.1) (fun sample => execution sample.1)
      (fun sample => horizon - (execution sample.1).environmentRecall.length) (fun _ => 0)
      (fun sample => (execution sample.1).application.config)
      (fun sample present => revelations sample.1 (support sample present).1)
      (fun sample present => registry sample.1 (support sample present).1)
      (fun sample present => checkpoints sample.1 (support sample present).1)
      (fun sample present => reachable sample.1 (support sample present).1)
      (fun sample present => histories sample.1 (support sample present).1)
      ?_ ?_ tableFixed anchorSupport
      (fun sample present => rawTrace sample.1 (support sample present).1)
      (fun sample present => (boundary sample.1 (support sample present).1).ordered)
      (fun sample present => nativeClear sample.1 (support sample present).1)
      (fun sample present => discipline (frozen sample) (execution sample.1)
        (anchorSupport sample present))
      (fun sample present => roundsFrom_activationsAnswered _ _ (anchorSupport sample present))
      (fun sample present => (boundary sample.1 (support sample present).1).untouched)
      (fun _ _ => Nat.zero_le _) (fun _ _ => (PMF.mem_support_pure_iff _ _).mpr rfl)
      (fun sample present => nativeClear sample.1 (support sample present).1)
      ?_ ?_ (fun _ _ => .refl)
      (fun sample present => keys sample.1 (support sample present).1)
      ?_ ?_ noise factorStaged
    · intro sample present
      exact SubmitsBindings.freezeBindingsBefore (graph := setup.informationGraph)
        (show setup.informationGraph.SubmitsBindings (members sample.1) from
          submitting sample.1 (support sample present).1) start finish sample.2
    · intro sample present owner event actor observation active late
      have outside : ¬ (start ≤ event.val ∧ event.val < finish) := by omega
      simp only [frozen, freezeBindingsBefore, ite_eq_right outside]
      exact future sample.1 (support sample present).1 owner event actor observation active
        (by omega)
    · intro sample present
      have ordered := (boundary sample.1 (support sample present).1).ordered
      exact ⟨fun event before => (ordered.2 event).mpr before,
        fun event late done => Nat.not_lt.mpr (by omega) ((ordered.2 event).mp done)⟩
    · intro sample present event late
      exact (boundary sample.1 (support sample present).1).untouched event (by omega)
    · intro sample present event _before _actor
      exact congrFun
        (congrArg (fun key => key.2.2) (keys sample.1 (support sample present).1)) event
    · intro sample present event late _before _actor done
      exact Nat.not_lt.mpr late
        (((boundary sample.1 (support sample present).1).ordered.2 event).mp done)
  obtain ⟨policy, comparison⟩ := comparison
  refine ⟨policy, ?_⟩
  rw [nativeLaw]
  have sourceLaw : (staged.bind fun sample => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost sample.1)) =
      prior.bind (fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed)) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
  rwa [sourceLaw] at comparison

end Vegas

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def representativeSampleTail
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L frame.Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: frame.Γ) frame.names)
    (programEq : frame.program = .sample name fresh distribution next)
    (value : L.Val payload) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.sample name fresh distribution next) := programEq ▸ frame.embedding
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : setup.informationGraph.outputLayout (embedding.event index) =
        .publicData payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let atRank : (embedding.event index).val = rank := by
      rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
        aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
        transport, checkpoint⟩
      dsimp only at fresh distribution next programEq value ⊢
      cases programEq
      simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
    let ready : origin.cut.Ready (embedding.event index) := by
      have ordered := frame.checkpoint.ordered
      rw [← atRank] at ordered
      exact ordered.ready (embedding.event index).isLt
    SourceResidual setup profile (rank + 1)
      (origin.complete (embedding.event index) ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          value)) := by
  rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at fresh distribution next programEq value ⊢
  cases programEq
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
      .publicData payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have atRank : (embedding.event index).val = rank := by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : origin.cut.Ready (embedding.event index) := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready (embedding.event index).isLt
  have decoded : decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) =
        none := by
    have lookup := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
    simpa [index, outputEq, decodeEventAction] using lookup
  let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
  let tailRefs : ContextRefs (graphLayout setup.program)
      ((name, .publicData payload) :: Γ) :=
    refs.cons ⟨.inr (embedding.event index), outputEq⟩
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
    refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
  have tailAligned : CompiledPolicySuffix setup.program profile next
      (afterSample residualProfile) tailRefs
      (sampleSuccessor name source value).revelations
      (sampleSuccessor name source value).registry
      tailEmbedding tailBefore (rank + 1) := by
    simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
      aligned.sampleTail setup.program profile (_openNames := names) fresh distribution next
        residualProfile refs source.revelations source.registry embedding refsBefore rank
  refine {
    Γ := _, names := _, program := next, residualProfile := afterSample residualProfile,
    source := sampleSuccessor name source value, refs := tailRefs,
    embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
    admitted := fun whole who => admitted whole who,
    authentic := fun whole who => authentic whole who,
    supports := fun whole who => supports whole who,
    disclosing := fun whole who => disclosing whole who,
    lift := lift ∘ Sum.inr,
    commutes := fun state => ?_, steps := fun state joint => ?_,
    injective := injective.comp Sum.inr_injective,
    transport := fun more store history defaults => ?_,
    checkpoint := checkpoint.sample (native := configState origin) name
      (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index)
        decoded value }
  · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_sample_tail,
      PMF.map_comp]
  · rw [Function.comp_apply, steps]
    change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
    rw [PMF.map_comp]
  · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
      decodeSourcePrefix?_sample, Option.map_map]
    rfl

private theorem sample_source_successor
    {setup : Setup (Player := Player) (L := L)} [Finite Player]
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank origin)
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L frame.Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: frame.Γ) frame.names)
    (programEq : frame.program = .sample name fresh distribution next)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry)
    (ghost : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs)
    (checkpoint : SourceCheckpoint setup source frame.refs rank ghost)
    (history : setup.intendedProtocol.History)
    (historyAt : history.state = some (frame.lift (ProtocolState.entry frame.program source)))
    (reference : setup.informationGraph.BehavioralProfile) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.sample name fresh distribution next) := programEq ▸ frame.embedding
    let lifted : ProtocolState (.sample name fresh distribution next) →
        ProtocolState setup.program := programEq ▸ frame.lift
    let index : Fin (eventCount (.sample name fresh distribution next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : setup.informationGraph.EventId := embedding.event index
    let outputEq : setup.informationGraph.outputLayout event = .publicData payload :=
      (embedding.layout_eq index).trans rfl
    ∃ ready : ghost.cut.Ready event,
      let after := fun value : L.Val payload => ghost.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value)
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan reference setup.informationGraph.canonicalScheduler)
          1 ghost = (L.evalDist distribution (sourcePublicEnv source.state)).map after ∧
      ∀ value ∈ (L.evalDist distribution (sourcePublicEnv source.state)).support,
        SourceCheckpoint setup (sampleSuccessor name source value)
          (frame.refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) (after value) ∧
        (after value).Reachable inputs ∧
        ∃ nextHistory : setup.intendedProtocol.History,
          nextHistory.state = some (lifted (.inr (ProtocolState.entry next
            (sampleSuccessor name source value)))) := by
  rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh distribution next programEq source revelations registry checkpoint historyAt ⊢
  cases programEq
  let _ := Fintype.ofFinite Player
  let frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank origin :=
    ⟨Γ, names, .sample name fresh distribution next, residualProfile, original, refs, embedding,
      refsBefore, aligned, admitted, authentic, supports, disclosing, lift, commutes, steps,
      injective, transport, originalCheckpoint⟩
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have outputEq : setup.informationGraph.outputLayout event = .publicData payload :=
    (embedding.layout_eq index).trans rfl
  have atRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : ghost.cut.Ready event := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready event.isLt
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) = none := by
    simpa [index, event, outputEq, decodeEventAction] using aligned.actionEq index
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
  have codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) =
        .sample payload (compilePublicDist refs distribution) := by
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have graphLaw := sample_step ghost event ready outputEq refs distribution codeEq source.state
    checkpoint.agrees
  have ownerless : setup.informationGraph.actor? event = none := by
    exact (EventCode.actor_cast outputEq _).symm.trans (by rw [codeEq]; rfl)
  have least : ∀ other, other ∉ ghost.cut.completed → event.val ≤ other.val := by
    intro other missing
    rw [atRank]
    exact Nat.le_of_not_gt fun lower => missing ((checkpoint.ordered.2 other).mpr lower)
  refine ⟨ready, ?_, ?_⟩
  · rw [runPlan_canonical_ownerless reference 0 ghost event ready least ownerless]
    let : Subsingleton (setup.informationGraph.Action event) := by
      change Subsingleton ((setup.informationGraph.outputLayout event).Action)
      rw [outputEq]
      infer_instance
    rw [Subsingleton.elim ((setup.informationGraph.nodes event).actionOfActorNone ownerless)
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)]
    simpa only [EventGraph.runPlan, PMF.bind_pure] using graphLaw
  · intro value drawn
    have nextCheckpoint := checkpoint.sample (native := configState ghost) name event atRank
      ready outputEq (fun ref => refsBefore ref index) decoded value
    have graphStep : ghost.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value) ∈
          (ghost.step event ready
            (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).support := by
      rw [graphLaw]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, drawn, rfl⟩
    let actual := residualAt frame source revelations registry ghost checkpoint
    have atGhost : history.state = sourceServicePrefix? setup rank ghost :=
      historyAt.trans actual.decode.symm
    have sourceStep : Sum.inr (ProtocolState.entry next (sampleSuccessor name source value)) ∈
        (ProtocolState.behavioralStateStep (.sample name fresh distribution next) residualProfile
          (.inl source)).support := by
      rw [ProtocolState.behavioralStateStep_sample_entry]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, drawn, rfl⟩
    obtain ⟨nextHistory, nextHistoryAt⟩ := actual.intendedHistory_of_step intended target agrees
      history atGhost _ sourceStep
    exact ⟨nextCheckpoint, Config.Step.path_reachable
      (.single ⟨event, ready, _, graphStep⟩) reachable, nextHistory, nextHistoryAt⟩

private theorem chance_source_ghost_joint
    {Seed : Type} {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (event : (serviceGraph setup deps).EventId)
    (ownerless : (serviceGraph setup deps).actor? event = none)
    (alone : ∀ (cut : (serviceGraph setup deps).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (horizon : Nat) (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (ghost : Seed → setup.informationGraph.Config)
    (stepGhost : setup.informationGraph.Config → L.Val payload → setup.informationGraph.Config)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (pick : MessageNetwork Player (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps) → L.Val payload)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, ghost seed),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (noise (config.1.view focal)).map fun traffic => (config, traffic))
    (ready : ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
      (execution seed).application.config.cut.Ready event)
    (sampled : ∀ seed ∈ prior.support,
      (((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
        (focalPlayers setup leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution seed)).map fun final =>
          pick ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)) =
      L.evalDist distribution (sourcePublicEnv (source seed).state)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
          (focalPlayers setup leaks focal deviation)
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            ((sampleSuccessor name (source seed)
              (pick ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)),
              stepGhost (ghost seed)
                (pick ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final))),
              (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.1.state)).map
          (fun value => (sampleSuccessor name config.1 value, stepGhost config.2 value))).bind
            fun config => (nextNoise (config.1.view focal)).map
              fun traffic => (config, traffic) := by
  let app := serviceApplication setup deps duration leaks
  let read := fun seed => (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
    (execution seed)
  let phase := fun seed => (app.runUntilHorizon scheduler (focalPlayers setup leaks focal deviation)
    (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)).map
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal)
  obtain ⟨channel, channelLaw⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, ghost seed)) read (fun config => config.1.view focal) noise factor
    (fun _ => PMF.pure ()) (fun config _ => config) (fun config => config.1.view focal)
    (fun seed _ => phase seed)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same => by
      have recalled := congrArg (fun traffic => traffic.2.2.1) same
      change (execution left).environmentRecall = (execution right).environmentRecall at recalled
      simp only [phase, ReactiveApplication.runUntilHorizon, recalled]
      exact focalPhase_traffic_congr scheduler focal deviation (Or.inl ownerless) alone
        (horizon - (execution right).environmentRecall.length)
        (execution left) (execution right) (ready left leftSupport) (ready right rightSupport) same)
  have joint : (prior.bind fun seed => (phase seed).map fun traffic =>
      ((source seed, ghost seed), traffic)) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (channel (config.1.view focal)).map fun traffic => (config, traffic) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure] using channelLaw
  let choice := fun view => (channel view).map pick
  let nextNoise := fun view : DecisionView focal ((name, .publicData payload) :: Γ) =>
    fiberPosterior (channel (view.back false)) pick (view.observation.cells.get .here)
  let advance := fun (config : Config Player L Γ × setup.informationGraph.Config) value =>
    (sampleSuccessor name config.1 value, stepGhost config.2 value)
  have factored : (prior.bind fun seed => (phase seed).map fun traffic =>
      (advance (source seed, ghost seed) (pick traffic), traffic)) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (choice (config.1.view focal)).map (advance config)).bind fun config =>
          (nextNoise (config.1.view focal)).map fun traffic => (config, traffic) := by
    calc
      _ = (prior.bind fun seed => (phase seed).map fun traffic =>
          ((source seed, ghost seed), traffic)).map
            (fun pair => (advance pair.1 (pick pair.2), pair.2)) := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      _ = ((prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
          (channel (config.1.view focal)).map fun traffic => (config, traffic)).map
            (fun pair => (advance pair.1 (pick pair.2), pair.2)) := by rw [joint]
      _ = _ := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro seed _supported
        rw [map_readout_choice (channel ((source seed).view focal)) pick
          (fun value traffic => (advance (source seed, ghost seed) value, traffic))]
        apply bind_congr_on_support _
        intro value _chosen
        have backed := back_sample_view focal name (source seed) value
        dsimp only [nextNoise, advance]
        rw [backed]
        rfl
  have projected := congrArg (PMF.map Prod.fst) factored
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
    PMF.bind_pure] at projected
  have marginal : (prior.bind fun seed => (phase seed).map
      (fun traffic => advance (source seed, ghost seed) (pick traffic))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun config =>
        (L.evalDist distribution (sourcePublicEnv config.1.state)).map (advance config) := by
    rw [PMF.bind_map]
    apply bind_congr_on_support _
    intro seed supported
    have actual := congrArg (PMF.map (advance (source seed, ghost seed))) (sampled seed supported)
    simpa only [phase, PMF.map_comp, Function.comp_def] using actual
  refine ⟨nextNoise, ?_⟩
  rw [← projected, marginal] at factored
  simpa only [phase, advance, PMF.map_bind, PMF.map_comp, Function.comp_def] using factored

private theorem native_chance_clear_endpoint
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (event : (serviceGraph setup deps).EventId)
    (ownerless : (serviceGraph setup deps).actor? event = none)
    (solitary : (serviceGraph setup deps).Solitary event)
    (count rank : Nat) (before after : (serviceApplication setup deps duration leaks).Execution)
    (ordered : before.application.config.cut.IsPrefix rank) (atRank : event.val = rank)
    (clear : before.application.config.defaulted = ∅)
    (reached : after ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      (fun current => event ∈ current.application.config.cut.completed) count before).support)
    (completed : event ∈ after.application.config.cut.completed) :
    after.application.config.defaulted = ∅ ∧
      after.application.config.cut.IsPrefix (rank + 1) ∧
      ∃ ready : before.application.config.cut.Ready event, ∃ action,
        after.application.config ∈ (before.application.config.step event ready action).support := by
  have ready : before.application.config.cut.Ready event := by
    have orderedBefore := ordered
    rw [← atRank] at orderedBefore
    exact orderedBefore.ready event.isLt
  have quiescent (query : (serviceGraph setup deps).EventId) :
      ¬ before.application.AutomaticReady query := by
    intro automatic
    obtain ⟨owner, _, defaulted⟩ := automatic.owned
    simp only [clear, Finset.notMem_empty] at defaulted
  obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain
    (serviceTimeouts setup deps duration) leaks scheduler players event count before after ready
    (fun query queryReady => solitary _ queryReady ready) quiescent reached completed
  have primaryClear : native.config.defaulted = ∅ := by
    unfold EventGraph.Config.step at primary
    obtain ⟨value, _sampled, recorded⟩ := (PMF.mem_support_map_iff _ _ _).mp primary
    rw [← recorded]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who defaulted
    have original := (mem_defaulted_complete_of_actor_ne before.application.config event ready
      action value who (by rw [ownerless]; intro impossible; cases impossible)).mp defaulted
    simp only [clear, Finset.notMem_empty] at original
  have configEq : after.application.config = native.config := by
    rw [drained, native.drain_eq_of_empty primaryClear]
  refine ⟨configEq ▸ primaryClear, ?_, ready, action, configEq ▸ primary⟩
  have orderedAfter := ordered.complete_at event ready atRank
  unfold EventGraph.Config.step at primary
  obtain ⟨value, _sampled, recorded⟩ := (PMF.mem_support_map_iff _ _ _).mp primary
  rw [configEq, ← recorded]
  exact orderedAfter

private theorem native_chance_completionBoundary
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (event : (serviceGraph setup deps).EventId)
    (ownerless : (serviceGraph setup deps).actor? event = none)
    (solitary : (serviceGraph setup deps).Solitary event)
    (before after : (serviceApplication setup deps duration leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val before)
    (budget : before.environmentRecall.length ≤ horizon)
    (clear : before.application.config.defaulted = ∅)
    (reached : after ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      players (fun current => event ∈ current.application.config.cut.completed) horizon
      before).support)
    (completed : event ∈ after.application.config.cut.completed) :
    CompletionBoundary setup leaks scheduler players (event.val + 1) after ∧
      after.environmentRecall.length ≤ horizon ∧ after.application.config.defaulted = ∅ := by
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  obtain ⟨supported, bounded⟩ := runUntilHorizon_bounded boundary.supported budget reached
  obtain ⟨afterClear, afterOrdered, _⟩ := native_chance_clear_endpoint scheduler players event
    ownerless solitary (horizon - before.environmentRecall.length) event.val before after
    boundary.ordered rfl clear reached completed
  have shaped : BlockShaped (graph := G) event.val (event.val + 1) := by
    intro config inside unfinished query queryReady
    have pending : event ∉ config.cut.completed := by
      intro done
      apply unfinished
      intro other early
      by_cases prior : other.val < event.val
      · exact inside.1 other prior
      · have same : other = event := Fin.ext (by omega)
        exact same ▸ done
    have ready : config.cut.Ready event :=
      ⟨pending, fun prior predecessor => inside.1 prior (G.order.predecessor_lt predecessor)⟩
    have same := solitary _ queryReady ready
    subst query
    exact ⟨le_rfl, Nat.lt_succ_self _⟩
  have inside : InBlock event.val (event.val + 1) before.application.config :=
    ⟨fun query prior => (boundary.ordered.2 query).mpr prior,
      fun query late done => Nat.not_lt.mpr (by omega) ((boundary.ordered.2 query).mp done)⟩
  have untouched := blockRun_untouched shaped scheduler players
    (fun current => event ∈ current.application.config.cut.completed)
    (fun _ done => done event (Nat.lt_succ_self _))
    (horizon - before.environmentRecall.length) before after inside
    (fun query late => boundary.untouched query (by omega)) reached
  exact ⟨⟨supported, afterOrdered, untouched⟩, bounded, afterClear⟩

private theorem nativeSourceContinuation_sample [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) rank point)
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ frame.Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L frame.Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: frame.Γ) frame.names)
    (programEq : frame.program = .sample name fresh distribution next)
    (continuation : nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff
      (representativeSampleTail frame fresh distribution next programEq (L.someValue payload))) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      reference focal deviation nativePayoff sourcePayoff frame := by
  classical
  rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, originalCheckpoint⟩
  dsimp only at fresh distribution next programEq continuation ⊢
  cases programEq
  let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target
  let frame : SourceResidual setup whole rank point :=
    ⟨Γ, names, .sample name fresh distribution next, residualProfile, original, refs, embedding,
      refsBefore, aligned, admitted, authentic, supports, disclosing, lift, commutes, steps,
      injective, transport, originalCheckpoint⟩
  let tail := representativeSampleTail frame fresh distribution next rfl (L.someValue payload)
  change nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
    reference focal deviation nativePayoff sourcePayoff tail at continuation
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have atRank : event.val = rank := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have outputEq : G.outputLayout event = .publicData payload :=
    (embedding.layout_eq index).trans rfl
  have codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
      .sample payload (compilePublicDist refs distribution) := by
    change cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toInformationGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have ownerless : G.actor? event = none :=
    (EventCode.actor_cast outputEq _).symm.trans (by rw [codeEq]; rfl)
  have solitary : G.Solitary event := by
    intro cut other otherReady eventReady
    apply relaxed.ready_alone_of_not_publication cut _ _ eventReady otherReady
    · rw [outputEq]; trivial
    · rw [outputEq]; exact False.elim
  have alone : ∀ (cut : G.order.Cut) (other : G.EventId),
      cut.Ready event → cut.Ready other → other = event :=
    fun cut _ ready otherReady => solitary cut otherReady ready
  intro covered Seed prior source ghost revelations registry checkpoints reachable histories members
    submitting future execution players boundary budget keys noise factor
  let pick := fun final : app.Execution => sampledValue event outputEq final.application.config
  let phase := fun seed => app.runUntilHorizon scheduler (players seed)
    (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed)
  let afterGhost := fun (config : setup.informationGraph.Config) (value : L.Val payload) =>
    if ready : config.cut.Ready event then config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
      (cast (congrArg EventField.Value outputEq.symm) value) else config
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  let nextSource := fun sample : Seed × app.Execution =>
    sampleSuccessor name (source sample.1) (pick sample.2)
  let nextGhost := fun sample : Seed × app.Execution => afterGhost (ghost sample.1) (pick sample.2)
  have support (sample : Seed × app.Execution) (present : sample ∈ staged.support) :
      sample.1 ∈ prior.support ∧ sample.2 ∈ (phase sample.1).support := by
    obtain ⟨seed, supported, selected⟩ := (PMF.mem_support_bind_iff _ _ _).mp present
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp selected
    cases same
    exact ⟨supported, reached⟩
  have ready (seed : Seed) (present : seed ∈ prior.support) :
      (execution seed).application.config.cut.Ready event := by
    have ordered := (boundary seed present).ordered
    rw [← atRank] at ordered
    exact ordered.ready event.isLt
  have ghostReady (seed : Seed) (present : seed ∈ prior.support) :
      (ghost seed).cut.Ready event := by
    have ordered := (checkpoints seed present).ordered
    rw [← atRank] at ordered
    exact ordered.ready event.isLt
  have clear (seed : Seed) (present : seed ∈ prior.support) :
      (execution seed).application.config.defaulted = ∅ := by
    let residual := residualAt frame (source seed) (revelations seed present)
      (registry seed present) (ghost seed) (checkpoints seed present)
    obtain ⟨history, historyAt⟩ := histories seed present
    have decoded := residual.decode
    change sourceServicePrefix? setup rank (ghost seed) =
      some (lift (ProtocolState.entry (.sample name fresh distribution next) (source seed)))
        at decoded
    have sourceClear := residual.clear_of_intended_history wellFormed history
      (historyAt.trans decoded.symm)
    exact (defaulted_eq_of_completionOf_eq
      (congrArg (fun key => key.2.2) (keys seed present))).trans sourceClear
  have agree (seed : Seed) (present : seed ∈ prior.support) :
      refs.Agrees (source seed).state (execution seed).application.config.store := by
    have stores := congrArg (fun key => key.2.1) (keys seed present)
    change (execution seed).application.config.store =
      (G.fromSequentialConfig (ghost seed)).store at stores
    have converted : (G.fromSequentialConfig (ghost seed)).store = (ghost seed).store := by
      funext field
      cases field <;> rfl
    rw [stores, converted]
    intro readName cell ref
    exact (checkpoints seed present).agrees ref
  have complete (seed : Seed) (present : seed ∈ prior.support) :
      ∀ final ∈ (phase seed).support, event ∈ final.application.config.cut.completed :=
    runUntilHorizon_stop contract (players seed)
      (fun current => event ∈ current.application.config.cut.completed)
      (fun _ terminal => by rw [terminal]; exact Finset.mem_univ _)
      (execution seed) (boundary seed present).supported (budget seed present)
  have focalLaw (seed : Seed) (present : seed ∈ prior.support) : phase seed =
      app.runUntilHorizon scheduler (focalPlayers setup leaks focal deviation)
        (fun current => event ∈ current.application.config.cut.completed)
        horizon (execution seed) :=
    runUntil_reference_focal scheduler bound turns (firstTurnTiming setup turns deps)
      (effectiveOpening (G.prefixProfile (members seed))) focal deviation event (Or.inl ownerless)
      alone _ (execution seed) (fun _ => ready seed present)
  have sampled (seed : Seed) (present : seed ∈ prior.support) :
      (phase seed).map pick = L.evalDist distribution (sourcePublicEnv (source seed).state) := by
    have raw := chance_completed_output_law (serviceTimeouts setup deps duration) leaks
      relaxed.actorSerial scheduler (players seed) event ownerless solitary
      (horizon - (execution seed).environmentRecall.length) (execution seed) (ready seed present)
      (complete seed present)
    rw [(G.nodes event).action_eq_of_actor_none ownerless
      (EventCode.actionOfActorNone (G.nodes event) ownerless)
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit),
      sample_step (execution seed).application.config event (ready seed present) outputEq refs
        distribution codeEq (source seed).state (agree seed present), PMF.map_comp] at raw
    have projected := congrArg (PMF.map fun value : Option (G.outputLayout event).Value =>
      (value.map (cast (congrArg EventField.Value outputEq))).getD (L.someValue payload)) raw
    simpa only [phase, pick, sampledValue, PMF.map_comp, Function.comp_def,
      Config.complete, Function.update_self, Option.map_some, cast_cast, cast_eq,
      Option.getD_some, ReactiveApplication.runUntilHorizon, show (fun x : L.Val payload => x) =
        id from rfl, PMF.map_id] using projected
  have trafficPick (final : app.Execution) : sampledTrafficValue setup leaks event outputEq
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final) = pick final := by
    have publicField : (G.layout (.inr event)).IsPublic := by
      change (G.outputLayout event).IsPublic
      rw [outputEq]; trivial
    dsimp only [sampledTrafficValue, bindingTraffic, State.publicView, EventGraph.publicObserve]
    rw [EventGraph.publicStore_of_public _ _ _ publicField]
    rfl
  obtain ⟨nextNoise, jointFocal⟩ := chance_source_ghost_joint name distribution setup leaks
    scheduler
    focal deviation event ownerless alone horizon prior source ghost afterGhost execution
    (sampledTrafficValue setup leaks event outputEq) noise factor
    (fun seed present _ => ready seed present)
    (fun seed present => by
      rw [← focalLaw seed present]
      simpa only [trafficPick] using sampled seed present)
  have joint : staged.map (fun sample => ((nextSource sample, nextGhost sample),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal sample.2)) =
      ((prior.map (fun seed => (source seed, ghost seed))).bind fun current =>
        (L.evalDist distribution (sourcePublicEnv current.1.state)).map fun value =>
          (sampleSuccessor name current.1 value, afterGhost current.2 value)).bind fun current =>
            (nextNoise (current.1.view focal)).map fun observed => (current, observed) := by
    rw [← jointFocal]
    simp only [staged, PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply bind_congr_on_support _
    intro seed present
    rw [← focalLaw seed present]
    apply map_congr_on_support _
    intro final _
    simp only [nextSource, nextGhost, trafficPick]
  have marginal := congrArg (PMF.map Prod.fst) joint
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind, pmf_map_fun_const, PMF.bind_pure]
    at marginal
  have factorNext : staged.map (fun sample => ((nextSource sample, nextGhost sample),
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal sample.2)) =
      (staged.map fun sample => (nextSource sample, nextGhost sample)).bind fun current =>
        (nextNoise (current.1.view focal)).map fun observed => (current, observed) := by
    rw [marginal]
    exact joint
  have nextFacts (sample : Seed × app.Execution) (present : sample ∈ staged.support) :
      SourceCheckpoint setup (nextSource sample) tail.refs (rank + 1) (nextGhost sample) ∧
      (∃ inputs, (nextGhost sample).Reachable inputs) ∧
      (∃ history : setup.intendedProtocol.History, history.state =
        some (tail.lift (ProtocolState.entry tail.program (nextSource sample)))) ∧
      runKey sample.2.application.config = runKey (G.fromSequentialConfig (nextGhost sample)) := by
    have supported := (support sample present).1
    have reached := (support sample present).2
    obtain ⟨history, historyAt⟩ := histories sample.1 supported
    obtain ⟨inputs, sourceReach⟩ := reachable sample.1 supported
    obtain ⟨sourceReady, headLaw, sourceGood⟩ := sample_source_successor intended target agrees
      frame fresh distribution next rfl (source sample.1) (revelations sample.1 supported)
      (registry sample.1 supported) (ghost sample.1) sourceReach (checkpoints sample.1 supported)
      history historyAt (setup.informationGraph.prefixProfile reference)
    have chosen : pick sample.2 ∈
        (L.evalDist distribution (sourcePublicEnv (source sample.1).state)).support := by
      rw [← sampled sample.1 supported]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sample.2, reached, rfl⟩
    have decoded := sourceGood (pick sample.2) chosen
    change (ghost sample.1).cut.Ready event at sourceReady
    have ghostEq : nextGhost sample = (ghost sample.1).complete event sourceReady
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) (pick sample.2)) := by
      simp only [nextGhost, afterGhost, dite_eq_left sourceReady]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ghostEq]
      exact decoded.1
    · rw [ghostEq]
      exact ⟨inputs, decoded.2.1⟩
    · exact decoded.2.2
    · obtain ⟨_, _, actualReady, action, primary⟩ := native_chance_clear_endpoint scheduler
        (players sample.1) event ownerless solitary
        (horizon - (execution sample.1).environmentRecall.length) rank
        (execution sample.1) sample.2 (boundary sample.1 supported).ordered atRank
        (clear sample.1 supported) reached (complete sample.1 supported _ reached)
      have actionEq := (G.nodes event).action_eq_of_actor_none ownerless action
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
      rw [actionEq, sample_step (execution sample.1).application.config event actualReady outputEq
        refs distribution codeEq (source sample.1).state (agree sample.1 supported),
        PMF.support_map] at primary
      obtain ⟨value, _drawn, configEq⟩ := primary
      have readValue : pick sample.2 = value := by
        change sampledValue event outputEq sample.2.application.config = value
        rw [← configEq]
        simp only [sampledValue, Config.complete, Function.update_self, Option.map_some,
          cast_cast, cast_eq, Option.getD_some]
      rw [ghostEq, readValue, ← configEq]
      have readyNative : (G.fromSequentialConfig (ghost sample.1)).cut.Ready event :=
        ⟨sourceReady.1, fun prior predecessor => sourceReady.2
          ((EventOrder.sequential.mem_predecessors prior event).mpr
            (G.order.predecessor_lt predecessor))⟩
      exact runKey_complete_congr (keys sample.1 supported) event actualReady readyNative _ _
  have nextCovered : tail.refs.CoversPrefix setup.program (rank + 1) := by
    change ContextRefs.CoversPrefix setup.program
      (refs.cons (name := name) (cell := .publicData payload) ⟨Sum.inr event, outputEq⟩) (rank + 1)
    exact covered.cons setup.program _ event rfl atRank
  have tailComparison := continuation nextCovered staged nextSource nextGhost
    (fun sample present => by
      change @(sampleSuccessor name (source sample.1) (pick sample.2)).revelations =
        @(sampleSuccessor name original (L.someValue payload)).revelations
      simp only [sampleSuccessor]
      rw [revelations sample.1 (support sample present).1])
    (fun sample present => by
      change (sampleSuccessor name (source sample.1) (pick sample.2)).registry =
        (sampleSuccessor name original (L.someValue payload)).registry
      simp only [sampleSuccessor]
      rw [registry sample.1 (support sample present).1])
    (fun sample present => (nextFacts sample present).1)
    (fun sample present => (nextFacts sample present).2.1)
    (fun sample present => (nextFacts sample present).2.2.1)
    (fun sample => members sample.1)
    (fun sample present => submitting sample.1 (support sample present).1)
    (fun sample present owner node actor observation active later =>
      future sample.1 (support sample present).1 owner node actor observation active (by omega))
    Prod.snd
    (fun sample present => by
      have supported := (support sample present).1
      have reached := (support sample present).2
      have nextBoundary := native_chance_completionBoundary scheduler (players sample.1) event
        ownerless solitary (execution sample.1) sample.2
        (by simpa only [atRank] using boundary sample.1 supported) (budget sample.1 supported)
        (clear sample.1 supported) reached (complete sample.1 supported _ reached)
      simpa only [atRank] using nextBoundary.1)
    (fun sample present => (native_chance_completionBoundary scheduler (players sample.1) event
      ownerless solitary (execution sample.1) sample.2
      (by simpa only [atRank] using boundary sample.1 (support sample present).1)
      (budget sample.1 (support sample present).1) (clear sample.1 (support sample present).1)
      (support sample present).2 (complete sample.1 (support sample present).1 _
        (support sample present).2)).2.1)
    (fun sample present => (nextFacts sample present).2.2.2) nextNoise factorNext
  obtain ⟨policy, comparison⟩ := tailComparison
  refine ⟨policy, ?_⟩
  have nativeLaw : (staged.bind fun sample => app.runToHorizon scheduler (players sample.1)
      horizon sample.2) = prior.bind (fun seed => app.runToHorizon scheduler (players seed)
        horizon (execution seed)) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed _
    exact (app.runToHorizon_eq_runUntilHorizon_bind scheduler (players seed)
      (fun current => event ∈ current.application.config.cut.completed) horizon
      (execution seed)).symm
  rw [nativeLaw] at comparison
  have sourceLaw : (staged.bind fun sample => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (eventCount next) (nextGhost sample)) =
      prior.bind (fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler)
        (eventCount (.sample name fresh distribution next)) (ghost seed)) := by
    let onward := fun current : Config Player L ((name, .publicData payload) :: Γ) ×
        setup.informationGraph.Config => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (eventCount next) current.2
    have initial : (staged.bind fun sample => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) (eventCount next) (nextGhost sample)) =
        (staged.map (fun sample => (nextSource sample, nextGhost sample))).bind onward := by
      rw [PMF.bind_map]
      rfl
    rw [initial, marginal, PMF.bind_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro seed supported
    obtain ⟨history, historyAt⟩ := histories seed supported
    obtain ⟨inputs, sourceReach⟩ := reachable seed supported
    obtain ⟨sourceReady, headLaw, _⟩ := sample_source_successor intended target agrees frame fresh
      distribution next rfl (source seed) (revelations seed supported) (registry seed supported)
      (ghost seed) sourceReach (checkpoints seed supported) history historyAt
      (Function.update (setup.informationGraph.prefixProfile reference) focal policy)
    change (ghost seed).cut.Ready event at sourceReady
    rw [eventCount, show Nat.succ (eventCount next) = 1 + eventCount next by omega,
      runPlan_add]
    rw [headLaw, PMF.bind_map]
    simp only [Function.comp_def, PMF.bind_map]
    apply bind_congr_on_support _
    intro value _
    simp only [afterGhost, dite_eq_left sourceReady, onward]
    rfl
  change expect _ nativePayoff ≤ expect _ sourcePayoff at comparison
  change expect _ nativePayoff ≤ expect _ sourcePayoff
  rw [← sourceLaw]
  exact comparison

private theorem graphPayoff_fromSequentialConfig
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excluded : Player → ℝ) (focal : Player) (ghost : setup.informationGraph.Config)
    {inputs : setup.informationGraph.Inputs} (reachable : ghost.Reachable inputs) :
    setup.graphPayoff deps parameter utility excluded focal
      ((serviceGraph setup deps).fromSequentialConfig ghost) =
        setup.graphPayoff setup.informationDependencies parameter utility excluded focal ghost := by
  unfold Setup.graphPayoff
  by_cases terminal : ghost.cut.Terminal
  · have nativeTerminal : ((serviceGraph setup deps).fromSequentialConfig ghost).cut.Terminal :=
      terminal
    rw [dite_eq_left nativeTerminal, dite_eq_left terminal]
    have nativeRanked := rankedConfig_fromSequentialConfig
      (graph := serviceGraph setup deps) reachable nativeTerminal
    have ranked : rankedConfig (graph := setup.informationGraph) ghost terminal = ghost := by
      exact rankedConfig_fromSequentialConfig (graph := setup.informationGraph) reachable terminal
    have same : (⟨rankedConfig (graph := serviceGraph setup deps)
        ((serviceGraph setup deps).fromSequentialConfig ghost) nativeTerminal,
        rankedConfig_terminal _ _⟩ : setup.informationGraph.gameSignature.Outcome) =
        ⟨rankedConfig (graph := setup.informationGraph) ghost terminal,
          rankedConfig_terminal _ _⟩ := Subtype.ext (nativeRanked.trans ranked.symm)
    exact congrArg (fun outcome => exclusionUtility setup.program excluded utility
      (setup.eventParameterOutcome parameter outcome) focal) same
  · have nativeNonterminal :
        ¬ ((serviceGraph setup deps).fromSequentialConfig ghost).cut.Terminal := terminal
    rw [dite_eq_right nativeNonterminal, dite_eq_right terminal]

private theorem nativeSourceContinuation_terminal
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank point) (ended : eventCount frame.program = 0) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns wholeProfile
      reference focal deviation
      (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        final.application.config focal)
      (setup.graphPayoff setup.informationDependencies parameter utility
        (Setup.leastUtility utility) focal) frame := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let nativeValue := fun config : G.Config =>
    setup.graphForfeitConfigPayoff deps parameter utility forfeit config focal
  let sourceValue := setup.graphPayoff setup.informationDependencies parameter utility
    (Setup.leastUtility utility) focal
  intro _covered Seed prior _source ghost _revelations _registry _checkpoints reachable _histories
    members _submitting _future execution players boundary budget keys _noise _factor
  have atEnd : rank = G.order.eventCount := by
    have counts := frame.aligned.graphSuffix.countEq
    change rank + eventCount frame.program = G.order.eventCount at counts
    omega
  have terminal (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.config.cut.Terminal := by
    change (execution seed).application.config.cut.completed = Finset.univ
    ext event
    simp only [Finset.mem_univ, iff_true]
    exact ((boundary seed supported).ordered.2 event).mpr (by rw [atEnd]; exact event.isLt)
  have nativeLaw : (prior.bind fun seed => app.runToHorizon scheduler (players seed) horizon
      (execution seed)).map (fun final => final.application.config) =
        prior.map (fun seed => (execution seed).application.config) := by
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro seed supported
    calc
      _ = (app.runToHorizon scheduler (players seed) horizon (execution seed)).map
          (fun _ => (execution seed).application.config) := by
        apply map_congr_on_support _
        intro final reached
        exact runRounds_config_eq_of_terminal scheduler (players seed) _ (execution seed) final
          (terminal seed supported) reached
      _ = PMF.pure _ := pmf_map_fun_const _ _
  have comparison (seed : Seed) (supported : seed ∈ prior.support) :
      nativeValue (execution seed).application.config ≤ sourceValue (ghost seed) := by
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
      (players seed) (execution seed).environmentRecall.length (budget seed supported)
        (execution seed) (boundary seed supported).supported
    rw [serviceInitialLaw_eq_inputs setup] at trace
    obtain ⟨inputs, _, facts⟩ := reactive_history_invariant (serviceTimeouts setup deps duration)
      leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler trace
    change setup.graphForfeitConfigPayoff deps parameter utility forfeit
      (execution seed).application.config focal ≤ sourceValue (ghost seed)
    rw [Setup.graphForfeitConfigPayoff_terminal _ _ _ _ _ _ (terminal seed supported)]
    have less := setup.graphForfeitPayoff_le deps parameter utility spread
      ⟨(execution seed).application.config, terminal seed supported⟩ facts.reachable focal
    refine less.trans_eq ?_
    rw [setup.graphPayoff_factors deps parameter utility (Setup.leastUtility utility) focal _ _
      (keys seed supported)]
    obtain ⟨_, ghostReach⟩ := reachable seed supported
    exact graphPayoff_fromSequentialConfig setup deps parameter utility (Setup.leastUtility utility)
      focal (ghost seed) ghostReach
  refine ⟨reference focal, ?_⟩
  have sourceLaw : (prior.bind fun seed => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal (reference focal))
        setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed)) =
        prior.map ghost := by
    simp only [ended, runPlan]
    rfl
  rw [sourceLaw]
  change expect _ (nativeValue ∘ fun final : app.Execution => final.application.config) ≤ _
  rw [← expect_map, nativeLaw, expect_map, expect_map]
  obtain ⟨nativeBound, _, nativeBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility spread focal
  obtain ⟨sourceBound, _, sourceBounded⟩ :=
    setup.graphPayoff_abs_bound setup.informationDependencies parameter utility spread focal
  exact expect_mono comparison
    (payoffIntegrable_of_bounded prior _ fun seed => nativeBounded _)
    (payoffIntegrable_of_bounded prior _ fun seed => sourceBounded _)

end Vegas

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem exists_binding_interval {graph : Vegas.EventGraph Player L}
    (start : graph.EventId) (privateOutput : ¬ (graph.outputLayout start).IsPublic) :
    ∃ finish, start.val < finish ∧ finish ≤ graph.order.eventCount ∧
      (∀ event : graph.EventId, start.val ≤ event.val → event.val < finish →
        ∃ owner payload, graph.outputLayout event = .binding owner payload) ∧
      ∀ event : graph.EventId, event.val = finish → (graph.outputLayout event).IsPublic := by
  classical
  let Ending := fun finish : Nat => start.val < finish ∧ (graph.order.eventCount ≤ finish ∨
      ∃ event : graph.EventId, event.val = finish ∧ (graph.outputLayout event).IsPublic)
  have existsEnd : ∃ finish, Ending finish := ⟨graph.order.eventCount, start.isLt, Or.inl le_rfl⟩
  obtain ⟨finish, ⟨after, ending⟩, minimal⟩ : ∃ finish, Ending finish ∧
      ∀ smaller < finish, ¬ Ending smaller :=
    ⟨Nat.find existsEnd, Nat.find_spec existsEnd, fun _ below => Nat.find_min existsEnd below⟩
  have inside (smaller : Nat) (below : smaller < finish) (beyond : start.val < smaller) :
      smaller < graph.order.eventCount ∧ ∀ event : graph.EventId, event.val = smaller →
        ¬ (graph.outputLayout event).IsPublic := by
    have notEnd := minimal smaller below
    simp only [Ending, not_and, not_or, not_exists, not_le] at notEnd
    obtain ⟨small, everyPrivate⟩ := notEnd beyond
    exact ⟨small, fun event same => by simpa using everyPrivate event same⟩
  have bounded : finish ≤ graph.order.eventCount := by
    rcases ending with large | ⟨event, same, _⟩
    · by_contra above
      push Not at above
      obtain ⟨small, _⟩ := inside graph.order.eventCount above start.isLt
      omega
    · have := event.isLt
      omega
  refine ⟨finish, after, bounded, ?_, ?_⟩
  · intro event lower upper
    have hidden : ¬ (graph.outputLayout event).IsPublic := by
      rcases Nat.lt_or_ge start.val event.val with beyond | atStart
      · exact (inside event.val upper beyond).2 event rfl
      · have same : event = start := Fin.ext (le_antisymm atStart lower)
        rwa [same]
    cases actor : graph.actor? event with
    | none => exact (hidden (EventCode.output_public_of_actor_none (graph.nodes event) actor)).elim
    | some owner =>
        obtain ⟨payload, binding⟩ :=
          (EventCode.output_public_or_binding_of_actor (graph.nodes event) owner actor).resolve_left
            hidden
        exact ⟨owner, payload, binding⟩
  · intro event same
    rcases ending with large | ⟨other, otherSame, publicOutput⟩
    · exact (Nat.not_lt.mpr large (same ▸ event.isLt)).elim
    · have equal : event = other := Fin.ext (same.trans otherSame.symm)
      rwa [equal]

end Vegas

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeSourceContinuation_of_private_blocks [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy) :
    let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := setup.informationGraph.submitProfile (compileEventProfile setup.program whole)
    let nativePayoff := fun final : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (Setup.leastUtility utility) focal
    (∀ start finish {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole start point),
      start < finish → finish ≤ (serviceGraph setup deps).order.eventCount →
      (∀ event : (serviceGraph setup deps).EventId, start ≤ event.val → event.val < finish →
        ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload) →
      (∀ event : (serviceGraph setup deps).EventId, event.val = finish →
        ((serviceGraph setup deps).outputLayout event).IsPublic) →
      (∀ {tailPoint : setup.informationGraph.Config}
        (tail : SourceResidual setup whole finish tailPoint),
        nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
          reference focal deviation nativePayoff sourcePayoff tail) →
      nativeBindingContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff start finish frame) →
    ∀ {rank : Nat} {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole rank point),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff frame := by
  classical
  intro whole reference nativePayoff sourcePayoff privateBlocks
  let G := serviceGraph setup deps
  let Compare := fun {rank : Nat} {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole rank point) =>
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
      reference focal deviation nativePayoff sourcePayoff frame
  suffices proof : ∀ gap rank (point : setup.informationGraph.Config)
      (frame : SourceResidual setup whole rank point), G.order.eventCount - rank = gap →
      Compare frame by
    intro rank point frame
    exact proof _ rank point frame rfl
  intro gap
  induction gap using Nat.strong_induction_on with
  | ind gap ih =>
    intro rank point frame gapEq
    have bounded : rank ≤ G.order.eventCount := frame.checkpoint.ordered.1
    have tailOf (finish : Nat) (later : rank < finish) (within : finish ≤ G.order.eventCount)
        {tailPoint : setup.informationGraph.Config} (tail : SourceResidual setup whole finish
          tailPoint) : Compare tail :=
      ih (G.order.eventCount - finish) (by omega) finish tailPoint tail rfl
    by_cases ended : eventCount frame.program = 0
    · exact nativeSourceContinuation_terminal setup deps duration leaks horizon scheduler bound
        turns
        whole reference focal deviation parameter utility forfeit spread frame ended
    have active : rank < G.order.eventCount := by
      have countEq := frame.aligned.graphSuffix.countEq
      change rank + eventCount frame.program = G.order.eventCount at countEq
      omega
    rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
      aligned, admitted, authentic, supports, disclosure, lift, commutes, steps, injective,
      transport, checkpoint⟩
    cases program with
    | ret payoffs =>
        exact (ended rfl).elim
    | @sample Γ names name payload fresh distribution next =>
        let frame : SourceResidual setup whole rank point :=
          ⟨Γ, names, .sample name fresh distribution next, residualProfile, source, refs, embedding,
            refsBefore, aligned, admitted, authentic, supports, disclosure, lift, commutes,
            steps, injective, transport, checkpoint⟩
        exact nativeSourceContinuation_sample setup deps duration leaks horizon scheduler bound
          turns wellFormed relaxed contract intended target agrees reference focal deviation
          nativePayoff sourcePayoff frame fresh distribution next rfl
          (tailOf (rank + 1) (by omega) (by omega) _)
    | @commit Γ names name owner payload fresh guard next =>
        let frame : SourceResidual setup whole rank point :=
          ⟨Γ, names, .commit name owner fresh guard next, residualProfile, source, refs, embedding,
            refsBefore, aligned, admitted, authentic, supports, disclosure, lift, commutes,
            steps, injective, transport, checkpoint⟩
        let index : Fin (eventCount (.commit name owner fresh guard next)) :=
          ⟨0, by simp [eventCount]⟩
        let event := embedding.event index
        have atRank : event.val = rank := by
          simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
        have binding : G.outputLayout event = .binding owner payload :=
          (embedding.layout_eq index).trans rfl
        have privateOutput : ¬ (G.outputLayout event).IsPublic := by
          rw [binding]
          exact False.elim
        obtain ⟨finish, later, within, bindings, barrier⟩ :=
          exists_binding_interval (graph := G) event privateOutput
        rw [atRank] at later bindings
        apply nativeSourceContinuation_of_binding_interval setup deps duration leaks horizon
          scheduler bound turns whole reference focal deviation nativePayoff sourcePayoff rank
          finish frame relaxed wellFormed later.le within bindings barrier
        exact privateBlocks rank finish frame later within bindings barrier
          (tailOf finish later within)
    | @reveal Γ names published owner name payload fresh selected unresolved next =>
        let frame : SourceResidual setup whole rank point :=
          ⟨Γ, names, .reveal published owner name fresh selected unresolved next, residualProfile,
            source, refs, embedding, refsBefore, aligned, admitted, authentic, supports, disclosure,
            lift, commutes, steps, injective, transport, checkpoint⟩
        let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next))
            :=
          ⟨0, by simp [eventCount]⟩
        let event := embedding.event index
        have atRank : event.val = rank := by
          simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
        have publication : (G.outputLayout event).IsPublication := by
          have output : G.outputLayout event = .publication payload :=
            (embedding.layout_eq index).trans rfl
          rw [output]
          trivial
        obtain ⟨finish, run⟩ := exists_revealRun publication
        rw [atRank] at run
        exact nativeSourceContinuation_public scheduler bound relaxed contract timely wellFormed
          intended target agrees submits disclosing parameter utility spread focal deviation frame
          run
          (tailOf finish run.nonempty run.bounded)

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nativeSourceContinuation_initialized
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (submitted : (serviceGraph setup deps).SubmitsBindings reference) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    (continuation : ∀ initial : State L setup.context,
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
        wholeProfile reference focal deviation nativePayoff sourcePayoff
          (SourceResidual.initial setup wholeProfile initial)) :
    let players := Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening
          ((serviceGraph setup deps).prefixProfile reference))) focal deviation
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect ((serviceApplication setup deps duration leaks).roundsFrom
        (serviceInitialLaw setup deps) scheduler players horizon) nativePayoff ≤
      expect (setup.initialLaw.bind fun initial => setup.informationGraph.runPolicies
        setup.informationGraph.canonicalScheduler
        (Function.update (setup.informationGraph.prefixProfile reference) focal policy)
          (setup.eventInputs initial)) sourcePayoff := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening
        ((serviceGraph setup deps).prefixProfile reference))) focal deviation
  let ghost := fun initial : State L setup.context =>
    EventGraph.Config.initial (graph := setup.informationGraph) (setup.eventInputs initial)
  let execution := fun initial : State L setup.context => ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (graph := serviceGraph setup deps) (setup.eventInputs initial))
  let representative := setup.initialLaw.support_nonempty.choose
  let frame := SourceResidual.initial setup wholeProfile representative
  obtain ⟨noise, initialFactor⟩ := source_initial_traffic_factorization setup
    (deps := deps) (duration := duration) leaks focal
  let augment := fun point : Config Player L setup.context ×
      MessageNetwork Player app.Payload × List (MessageId Player × Bool) ×
      List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps) =>
    ((point.1, ghost point.1.state), point.2)
  have factor : setup.initialLaw.map (fun initial =>
      ((Config.initial initial, ghost initial),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution initial))) =
      (setup.initialLaw.map (fun initial => (Config.initial initial, ghost initial))).bind
        fun hidden => (noise (hidden.1.view focal)).map fun observed => (hidden, observed) := by
    have tagged := congrArg (PMF.map augment) initialFactor
    simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def, augment,
      SourceProgram.Config.initial, ghost, execution] using tagged
  have boundary (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
      CompletionBoundary setup leaks scheduler players 0 (execution initial) := by
    refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
    · change execution initial ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler
        players 0).support
      unfold ReactiveApplication.roundsFrom
      simp only [ReactiveApplication.runRounds, serviceInitialLaw]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨_,
        (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, supported, rfl⟩,
        (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    · intro event _ owner entry member
      cases member
  have intendedHistory (initial : State L setup.context)
      (supported : initial ∈ setup.initialLaw.support) :
      ∃ history : setup.intendedProtocol.History,
        history.state = some (ProtocolState.entry setup.program (Config.initial initial)) := by
    have legal : setup.intendedProtocol.Legal setup.intendedProtocol.initHistory.state
        (fun _ => none) := setup.intendedProtocol.legal_of_legalOption
          (fun impossible => impossible) (fun _ impossible => impossible)
    have reached : some (ProtocolState.entry setup.program (Config.initial initial)) ∈
        (setup.intendedProtocol.step setup.intendedProtocol.initHistory.state ⟨_, legal⟩).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨initial, supported, rfl⟩
    exact ⟨setup.intendedProtocol.initHistory.extend legal reached, rfl⟩
  have initialContinuation := continuation representative
  obtain ⟨policy, comparison⟩ := initialContinuation
    (ContextRefs.initial_coversPrefix setup.program) setup.initialLaw Config.initial ghost
    (fun _ _ => rfl) (fun _ _ => rfl) (fun initial _ => SourceCheckpoint.initial setup initial)
    (fun initial _ => ⟨setup.eventInputs initial, .initial⟩) intendedHistory
    (fun _ => reference) (fun _ _ => submitted) (fun _ _ _ _ _ _ _ _ => rfl)
    execution boundary (fun _ _ => Nat.zero_le _) (fun _ _ => rfl) noise factor
  refine ⟨policy, ?_⟩
  have countEq : setup.informationGraph.order.eventCount = eventCount setup.program := rfl
  simpa only [countEq, Function.comp_def, ReactiveApplication.roundsFrom, serviceInitialLaw,
    PMF.bind_map,
    ReactiveApplication.runToHorizon, ReactiveApplication.Execution.initial, List.length_nil,
    Nat.sub_zero, EventGraph.runPolicies, EventGraph.run, execution, ghost, app, frame,
    SourceResidual.initial] using comparison

end Vegas

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every raw native unilateral deviation is bounded by one policy in the canonical
information graph. Initial source correlation and the complete physical observation history
are retained by the comparison; no independent-prior or scheduler-erasure premise is needed. -/
theorem native_prefix_deviation_bound [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wellFormed : setup.WellFormed)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (forfeit : ℝ)
    (spread : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy) :
    let whole := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := setup.informationGraph.submitProfile (compileEventProfile setup.program whole)
    let nativePayoff := fun final : (serviceApplication setup deps duration leaks).Execution =>
      setup.graphForfeitConfigPayoff deps parameter utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (Setup.leastUtility utility) focal
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect ((serviceApplication setup deps duration leaks).roundsFrom
        (serviceInitialLaw setup deps) scheduler
        (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) (effectiveOpening
            ((serviceGraph setup deps).prefixProfile reference))) focal deviation) horizon)
        nativePayoff ≤
      expect ((setup.graphInputs setup.informationDependencies).bind
        (setup.informationGraph.runPolicies setup.informationGraph.canonicalScheduler
          (Function.update (setup.informationGraph.prefixProfile reference) focal policy)))
        sourcePayoff := by
  intro whole reference nativePayoff sourcePayoff
  have continuation : ∀ {rank : Nat} {point : setup.informationGraph.Config}
      (frame : SourceResidual setup whole rank point),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns whole
        reference focal deviation nativePayoff sourcePayoff frame :=
    nativeSourceContinuation_of_private_blocks setup deps duration leaks horizon scheduler bound
      turns wellFormed relaxed contract timely intended target agrees submits disclosing parameter
      utility forfeit spread focal deviation (by
        intro start finish point frame later bounded bindings barrier outer
        exact nativeBindingContinuation_binding_interval setup deps duration leaks horizon scheduler
          bound turns wellFormed relaxed contract timely intended target agrees submits parameter
          utility forfeit spread focal deviation start finish later bounded bindings barrier outer
          frame)
  obtain ⟨policy, comparison⟩ := nativeSourceContinuation_initialized setup deps duration leaks
    horizon scheduler bound turns whole reference
    (submitsBindings_submitProfile (serviceGraph setup deps) _) focal deviation nativePayoff
    sourcePayoff (fun initial => continuation (SourceResidual.initial setup whole initial))
  refine ⟨policy, ?_⟩
  simpa only [Setup.graphInputs, PMF.bind_map, Function.comp_def] using comparison

end Vegas

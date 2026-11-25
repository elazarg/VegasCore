module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Math.Probability.ConditionalObservation
public import Vegas.Compile.PrescribedProfile
public import Vegas.EventGraph.BindingChain
public import Vegas.EventGraph.DeviationContinuation
public import Vegas.Game.BindingBlockOpacity
public import Vegas.Pending.FocalTraffic
public import Vegas.Game.SourceBindingFiber
public import Vegas.Game.SourceStateKernel

@[expose] public section

/-! # Source and ledger frames for a private binding interval -/

noncomputable section

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

theorem focal_source_successor_noise_reset
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
          simp only [PMF.bind_map, Function.comp_def, advance] at reset ⊢
          convert reset using 1
          apply bind_congr_on_support _
          intro action _
          cases action <;> rfl

theorem binding_good_successor_law
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

theorem canonical_honest_binding_head_joint
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

theorem canonical_foreign_source_head_joint
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

theorem foreign_binding_source_head
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

theorem native_focal_binding_graph_runUntil
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

def residualCommitTail
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

def representativeCommitTail
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
  have tailCheckpoint := checkpoint.commit (native := origin) name guard
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

def nativeBindingContinuation
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

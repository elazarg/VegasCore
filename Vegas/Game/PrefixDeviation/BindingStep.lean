module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixDeviation
public import Vegas.Game.BindingBlockCompletion
public import Vegas.Game.IntendedPrefixContinuation
public import Vegas.Game.NativeForfeitContinuation
public import Vegas.Game.PrefixDeviation.BindingFrame
public import Vegas.Game.PrefixDeviation.Boundary
public import Vegas.Game.RevealPhaseBoundary

@[expose] public section

/-! # Owned and foreign binding deviations within a private interval -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem foreign_binding_shadow_distribution
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
    (head : ∀ seed ∈ prior.support, actionDistribution profile (ghost seed).1 event =
      (sourceHead (source seed)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice))
    (submits : ∀ seed ∈ prior.support, ∀ action ∈
      (actionDistribution profile (ghost seed).1 event).support,
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
    (submits : ∀ action ∈ (actionDistribution profile config event).support,
      (graph.outputLayout event).Submitted action) (count : Nat)
    (honest : graph.PublicObservation ×
      ((other : {other : Player // other ≠ focal}) → graph.PlayerObservation other.1))
    (selected : honest ∈ ((graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
      (count + 1) config).map (bindingObservers focal)).support) :
    let chosen := (cast (congrArg (fun field => Option field.Value) binding)
      ((honest.2 ⟨owner, different⟩).store (.inr event))).getD .failure
    some chosen ∈ ((actionDistribution profile config event).map
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
    (head : ∀ seed ∈ prior.support, actionDistribution profile (ghost seed).1 event =
      (sourceHead (source seed)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice))
    (submits : ∀ seed ∈ prior.support, ∀ action ∈
      (actionDistribution profile (ghost seed).1 event).support,
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
    (∀ seed ∈ prior.support, actionDistribution placeholder (ghost seed).1 event =
      (sourceHead (source seed)).map
        (fun choice => cast (congrArg EventField.Action binding.symm) choice)) →
    (∀ seed ∈ prior.support, ∀ action ∈
      (actionDistribution placeholder (ghost seed).1 event).support,
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
  have joint := foreign_binding_shadow_distribution placeholder event owner focal different payload
    binding
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
      actionDistribution placeholder config event = actionDistribution prescribed config event := by
    rw [actionDistribution_of_actor _ _ actor, actionDistribution_of_actor _ _ actor]
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
  have nextCheckpoint := checkpoint.commit (native := ghost) name guard event eventRank
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

theorem nativeBindingContinuation_foreign
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
      actionDistribution placeholder (currentGhost seed).1 event =
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
      (actionDistribution placeholder (currentGhost seed).1 event).support,
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
    rw [actionDistribution_of_actor _ _ actor, dite_eq_right active] at selected
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
  have nextCheckpoint := checkpoint.commit (native := ghost) name guard event eventRank
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

private theorem focal_binding_good_successor_distribution
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
    (head : ∀ hidden ∈ prior.support, actionDistribution profile hidden.2.1 event =
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
        simp only [chosen, advance, Option.getD_some] at reset ⊢
        convert reset using 1
        · apply map_congr_on_support _
          intro seed _
          cases OwnAction.binding focal name payload
            (Config.view focal (nextSource seed)).history.getLast? <;> rfl
        · apply bind_congr_on_support _
          intro hidden _
          apply bind_congr_on_support _
          intro action _
          cases action <;> rfl
      _ = _ := by
        simp only [choices, PMF.bind_bind, PMF.bind_map]
        apply bind_congr_on_support _
        intro hidden _
        apply bind_congr_on_support _
        intro action _
        cases action <;> rfl
  have posterior := binding_good_successor_distribution profile count focal choices nextPrior
    nextSource
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
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile) (focal : Player)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : ∀ owner, owner ≠ focal → players owner =
      turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference owner)
    (anchor : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨budget, none, anchor⟩))
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
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
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
    (∀ seed ∈ prior.support, anchor seed ∈ (app.roundsFrom (serviceInitialDistribution setup deps)
      scheduler (players seed) (anchor seed).environmentRecall.length).support) →
    (∀ seed ∈ prior.support, Nonempty ((app.protocol (serviceInitialDistribution setup deps) horizon
      scheduler).Trace (some ⟨budget seed, none, anchor seed⟩))) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.cut.IsPrefix start) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.defaulted = ∅) →
    (∀ seed ∈ prior.support, ∀ owner, owner ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
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
      actionDistribution placeholder hidden.2.1 event = PMF.pure
        (cast (congrArg EventField.Action binding.symm) (some (.failure :
          PublicationResult (L.Val payload)))) := by
    intro hidden member
    obtain ⟨seed, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have actor : setup.informationGraph.actor? event = some focal :=
      EventCode.actor_eq_of_binding _ binding
    have active : focal ∉ (ghost seed).1.defaulted := by rw [(ghost seed).2.2.2]; simp
    rw [actionDistribution_of_actor _ _ actor, dite_eq_right active]
    dsimp only [placeholder, EventGraph.prefixProfile, EventGraph.prefixPolicy]
    rw [Function.update_self]
    exact submittedFailurePolicy_binding (graph := setup.informationGraph) focal event actor
      payload infoBinding _ _
  have canonicalJoint := joint
  have boundedInfo : finish ≤ setup.informationGraph.order.eventCount := bounded
  have posteriorFactor := focal_binding_good_successor_distribution placeholder globalSubmits event
    focal
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
    have countedTrace := app.raw_trace_horizon (serviceInitialDistribution setup deps) horizon
      scheduler raw
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
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
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
      (serviceInitialDistribution setup deps) scheduler players
        final.environmentRecall.length).support)
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
    (native := ghost) name guard event rfl ready infoBinding beforeRefs (some result)
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
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
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
    (∀ seed ∈ prior.support, anchor seed ∈ (app.roundsFrom (serviceInitialDistribution setup deps)
      scheduler (players seed) (anchor seed).environmentRecall.length).support) →
    (∀ seed ∈ prior.support, Nonempty ((app.protocol (serviceInitialDistribution setup deps) horizon
      scheduler).Trace (some ⟨budget seed, none, anchor seed⟩))) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.cut.IsPrefix start) →
    (∀ seed ∈ prior.support, (anchor seed).application.config.defaulted = ∅) →
    (∀ seed ∈ prior.support, ∀ owner, owner ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks (anchor seed) owner ∧
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
      execution seed ∈ (app.roundsFrom (serviceInitialDistribution setup deps) scheduler
        (players seed)
        (execution seed).environmentRecall.length).support := by
    have length := app.runRounds_environmentRecall_length scheduler (players seed) (used seed)
      (anchor seed) (execution seed) (supported seed member)
    rw [length]
    exact app.roundsFrom_runRounds scheduler (players seed) (serviceInitialDistribution setup deps)
      (anchor seed).environmentRecall.length (used seed) (anchor seed) (execution seed)
      (anchorSupported seed member) (supported seed member)
  have currentTrace (seed : Seed) (member : seed ∈ prior.support) :
      ∃ remaining, Nonempty ((app.protocol (serviceInitialDistribution setup deps) horizon
        scheduler).Trace
        (some ⟨remaining, none, execution seed⟩)) := by
    obtain ⟨raw⟩ := trace seed member
    obtain ⟨current⟩ := app.raw_trace_runRounds (serviceInitialDistribution setup deps) horizon
      scheduler
      (players seed) (budget seed - used seed) (used seed) (anchor seed) (execution seed)
      (by simpa only [Nat.sub_add_cancel (counted seed member)] using raw)
      (supported seed member)
    exact ⟨_, ⟨current⟩⟩
  have currentBound (seed : Seed) (member : seed ∈ prior.support) :
      (execution seed).environmentRecall.length ≤ horizon := by
    obtain ⟨remaining, ⟨raw⟩⟩ := currentTrace seed member
    have available := app.raw_trace_horizon (serviceInitialDistribution setup deps) horizon
      scheduler raw
    dsimp only at available
    omega
  have anchorInitial (seed : Seed) (member : seed ∈ prior.support) :
      ∃ initial : State L setup.context, EventGraph.Config.Reachable (graph := G)
        (setup.eventInputs initial) (anchor seed).application.config := by
    obtain ⟨raw⟩ := trace seed member
    rw [serviceInitialDistribution_eq_inputs setup] at raw
    obtain ⟨inputs, selected, facts⟩ := reactive_history_invariant
      (serviceTimeouts setup deps duration) leaks (setup.initialDistribution.map setup.eventInputs)
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
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks (execution seed) owner := by
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

theorem nativeBindingContinuation_owned
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (wellFormed : setup.WellFormed)
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
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

module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Math.Probability.ConditionalObservation
public import Vegas.Game.PrefixDeviation.BindingStep
public import Vegas.Pending.FocalTraffic

@[expose] public section

/-! # Continuation bounds across a private binding interval -/

noncomputable section

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
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks (execution seed) owner := by
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

theorem nativeBindingContinuation_binding_interval [Finite Player]
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

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem optional_binding_value_cast {field : EventField Player L}
    {owner : Player} {payload : L.Ty} (binding : field = .binding owner payload)
    (stored : Option field.Value) (value : PublicationResult (L.Val payload))
    (filled : stored = some (cast (congrArg EventField.Value binding.symm) value)) :
    cast (congrArg (fun kind => Option kind.Value) binding) stored = some value := by
  cases binding
  exact filled

theorem nativeSourceContinuation_of_binding_interval
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
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks current owner ∧
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
      ReactiveApplication.runUntil_false_eq_runRounds, Function.comp_def] using law
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

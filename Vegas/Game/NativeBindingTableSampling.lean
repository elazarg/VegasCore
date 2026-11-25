module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.StoredBindingProfile
public import Vegas.Pending.EffectiveOpening
public import Vegas.EventGraph.BindingChain
public import Vegas.Game.NativeSlotPolicies
public import Vegas.Game.BindingPrefixSampling
public import Interaction.ReactiveMixtureRounds

@[expose] public section

/-! # Jointly predrawing private bindings for compiled clients

A chosen set of compiled owners can draw their binding decisions before the
complete stopped native execution. The joint draw uses the existing canonical
graph run, while other clients and the stopping predicate stay unchanged.
-/

noncomputable section



namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem prefixProfile_patch_native_table (profile : graph.BehavioralProfile)
    (owner : Player) (event : graph.EventId) (head : graph.BehavioralPolicy owner) :
    graph.prefixProfile (Function.update profile owner (patchPolicy event head (profile owner))) =
      Function.update (graph.prefixProfile profile) owner
        (patchPolicy event (graph.prefixPolicy owner head)
          ((graph.prefixProfile profile) owner)) := by
  funext who current actor observation active
  by_cases sameOwner : who = owner
  · subst who
    by_cases sameEvent : current = event
    · simp only [prefixProfile, prefixPolicy, Function.update_self, patchPolicy,
        ite_eq_left sameEvent]
    · simp only [prefixProfile, prefixPolicy, Function.update_self, patchPolicy,
        ite_eq_right sameEvent]
  · simp only [prefixProfile, prefixPolicy, Function.update_of_ne sameOwner]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem optional_value_cast_native_table {field : EventField Player L}
    {owner : Player} {payload : L.Ty} (binding : field = .binding owner payload)
    (stored : Option field.Value) (value : PublicationResult (L.Val payload))
    (filled : stored = some (cast (congrArg EventField.Value binding.symm) value)) :
    cast (congrArg (fun kind => Option kind.Value) binding) stored = some value := by
  cases binding
  exact filled

end Vegas.EventGraph

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Joint predrawing preserves the full stopped native execution law. -/
theorem native_binding_subfamily_mixture
    {horizon nativeCount remaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (compiled : Player → Prop) [DecidablePred compiled]
    (background : Player → (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (execution : (serviceApplication setup deps duration leaks).Execution)
    {inputs : (serviceGraph setup deps).Inputs}
    (initialReach : execution.application.config.Reachable inputs)
    (start bindingCount : Nat) (ordered : execution.application.config.cut.IsPrefix start)
    (clear : execution.application.config.defaulted = ∅)
    (bounded : start + bindingCount ≤ (serviceGraph setup deps).order.eventCount)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + bindingCount →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (truthful : ∀ owner, compiled owner → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks execution owner)
    (untouched : ∀ owner, compiled owner →
      ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + bindingCount →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining + nativeCount, none, execution⟩)) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let reference := G.prefixProfile profile
    let clients := fun reference => turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns
      (firstTurnTiming setup turns deps) reference
    let prescribed := fun reference actor =>
      if compiled actor then clients reference actor else background actor
    app.runUntil scheduler (prescribed reference) stop nativeCount execution =
      (G.runPlan (G.policyPlan reference G.canonicalScheduler) bindingCount
        execution.application.config).bind fun ghost =>
          app.runUntil scheduler
            (prescribed (G.prefixProfile (G.freezeBindingsBefore profile start
              (start + bindingCount) ghost))) stop nativeCount execution := by
  classical
  intro G app reference clients prescribed
  change start + bindingCount ≤ G.order.eventCount at bounded
  let sourceRun := G.runPlan (G.policyPlan reference G.canonicalScheduler)
  let frozen := fun rank ghost => G.freezeBindingsBefore profile start rank ghost
  let players := fun rank ghost => prescribed (G.prefixProfile (frozen rank ghost))
  let native := fun rank ghost => app.runUntil scheduler (players rank ghost) stop nativeCount
    execution
  have sourceSubmits : G.SubmitsBindings reference := by
    intro owner event actor observation active action selected
    exact submits owner event actor _ _ action selected
  have advance : ∀ rest past (ghost : G.Config), past + rest ≤ bindingCount →
      ghost ∈ (sourceRun past execution.application.config).support →
      native (start + past) ghost = (sourceRun rest ghost).bind
        (native (start + past + rest)) := by
    intro rest
    induction rest with
    | zero =>
        intro past ghost _ _
        simp only [Nat.add_zero, sourceRun, runPlan, PMF.pure_bind]
    | succ rest ih =>
        intro past ghost below supported
        have frame := runPlan_submitted_binding_frame reference past start
          execution.application.config ordered clear (by omega)
          (fun event _ _ owner actor observation active action member =>
            sourceSubmits owner event actor observation active action member)
          (fun event lower upper => bindings event lower (by omega)) ghost supported
        obtain ⟨ghostOrdered, ghostPath, ghostClear, _ghostClean, ghostRecords⟩ := frame
        let rank := start + past
        have activeRank : rank < G.order.eventCount := by dsimp only [rank]; omega
        let event : G.EventId := ⟨rank, activeRank⟩
        have ready : ghost.cut.Ready event := ghostOrdered.ready activeRank
        have least (other : G.EventId) (pending : other ∉ ghost.cut.completed) :
            event.val ≤ other.val := by
          by_contra earlier
          exact pending ((ghostOrdered.2 other).mpr (by dsimp only [event, rank] at *; omega))
        obtain ⟨owner, payload, binding⟩ := bindings event
          (by dsimp only [event, rank]; omega) (by dsimp only [event, rank]; omega)
        have owned : G.actor? event = some owner :=
          EventCode.actor_eq_of_binding (G.nodes event) binding
        have active : owner ∉ ghost.defaulted := by rw [ghostClear]; simp
        let kernel := actionDistribution reference ghost event
        have firstLaw (fuel : Nat) : sourceRun (fuel + 1) ghost = kernel.bind fun action =>
            (ghost.step event ready action).bind (sourceRun fuel) := by
          dsimp only [sourceRun, kernel]
          rw [runPlan_canonical_actor reference fuel ghost event ready least owner owned active,
            actionDistribution_of_actor reference ghost owned, dite_eq_right active]
        have nextSupported (action : G.Action event) (selected : action ∈ kernel.support)
            (next : G.Config) (moved : next ∈ (ghost.step event ready action).support) :
            next ∈ (sourceRun (past + 1) execution.application.config).support := by
          have combined := runPlan_add G
            (G.policyPlan reference G.canonicalScheduler) past 1 execution.application.config
          change sourceRun (past + 1) execution.application.config =
            (sourceRun past execution.application.config).bind (sourceRun 1) at combined
          rw [combined, PMF.mem_support_bind_iff]
          refine ⟨ghost, supported, ?_⟩
          rw [firstLaw 0]
          simpa only [sourceRun, runPlan, PMF.bind_pure] using
            (PMF.mem_support_bind_iff _ _ _).mpr ⟨action, selected, moved⟩
        have nextLaw (action : G.Action event) (selected : action ∈ kernel.support)
            (next : G.Config) (moved : next ∈ (ghost.step event ready action).support) :
            native (rank + 1) next = (sourceRun rest next).bind
              (native (rank + (rest + 1))) := by
          have atRank : start + (past + 1) = rank + 1 := by dsimp only [rank]; omega
          have finalRank : (rank + 1) + rest = rank + (rest + 1) := by omega
          simpa only [atRank, finalRank] using
            ih (past + 1) next (by omega) (nextSupported action selected next moved)
        have referencePatch (action : G.Action event) (next : G.Config)
            (moved : next ∈ (ghost.step event ready action).support) :
            Function.update (G.prefixProfile (frozen rank ghost)) owner
              (patchPolicy event (G.prefixPolicy owner (frozen (rank + 1) next owner))
                ((G.prefixProfile (frozen rank ghost)) owner)) =
              G.prefixProfile (frozen (rank + 1) next) := by
          have patched := freezeBindingsBefore_step_patch profile start ghost next event ready
            action moved owner owned
          have observed := congrArg G.prefixProfile patched
          rw [prefixProfile_patch_native_table] at observed
          exact observed
        have clientsPatch (action : G.Action event) (next : G.Config)
            (moved : next ∈ (ghost.step event ready action).support) :
            clients (G.prefixProfile (frozen (rank + 1) next)) =
              Function.update (clients (G.prefixProfile (frozen rank ghost))) owner
                (clients (G.prefixProfile (frozen (rank + 1) next)) owner) := by
          funext actor
          by_cases same : actor = owner
          · subst actor
            rw [Function.update_self]
          · rw [Function.update_of_ne same]
            have samePolicy := congrFun (referencePatch action next moved) actor
            rw [Function.update_of_ne same] at samePolicy
            exact serviceReferenceTurnPolicy_eq_of_owner bound turns
              (firstTurnTiming setup turns deps) _ _ actor samePolicy.symm
        by_cases notSelected : ¬ compiled owner
        · have sameNative (action : G.Action event) (next : G.Config)
              (moved : next ∈ (ghost.step event ready action).support) :
              native (rank + 1) next = native rank ghost := by
            have samePlayers : players (rank + 1) next = players rank ghost := by
              funext actor
              dsimp only [players, prescribed]
              by_cases same : actor = owner
              · subst actor
                simp only [ite_eq_right notSelected]
              · by_cases selectedActor : compiled actor
                · simp only [ite_eq_left selectedActor]
                  have sameClient := congrFun (clientsPatch action next moved) actor
                  rw [Function.update_of_ne same] at sameClient
                  exact sameClient
                · simp only [ite_eq_right selectedActor]
            exact congrArg (fun policies => app.runUntil scheduler policies stop nativeCount
              execution) samePlayers
          symm
          rw [firstLaw rest]
          simp only [PMF.bind_bind]
          calc
            _ = kernel.bind (fun action => (ghost.step event ready action).bind
                (fun next => native (rank + 1) next)) := by
              apply bind_congr_on_support _
              intro action selected
              apply bind_congr_on_support _
              intro next moved
              exact (nextLaw action selected next moved).symm
            _ = kernel.bind (fun _ => native rank ghost) := by
              apply bind_congr_on_support _
              intro action _
              calc
                _ = (ghost.step event ready action).bind (fun _ => native rank ghost) :=
                  bind_congr_on_support _ fun next moved => sameNative action next moved
                _ = _ := PMF.bind_const _ _
            _ = _ := PMF.bind_const _ _
        · have isSelected : compiled owner := Classical.not_not.mp notSelected
          have notPublication : ¬ (G.outputLayout event).IsPublication := by
            rw [binding]
            exact fun impossible => impossible
          have follows : players rank ghost owner = turnPolicy (serviceTimeouts setup deps duration)
              leaks bound turns (firstTurnTiming setup turns deps)
              (G.prefixProfile (frozen rank ghost)) owner :=
            by simp only [players, prescribed, clients, ite_eq_left isSelected]
          have frozenRecords : ∀ prior : G.EventId, start ≤ prior.val → prior.val < event.val →
              ∀ actor : G.actor? prior = some owner,
              ∃ (payload : L.Ty) (kind : G.outputLayout prior = .binding owner payload)
                (value : PublicationResult (L.Val payload)),
                (∀ observation active, G.prefixProfile (frozen rank ghost) owner prior actor
                  observation active = PMF.pure
                    (cast (congrArg EventField.Action kind.symm) (some value))) ∧
                completionOf ghost prior = some (EventGraph.completion G prior
                  (some (cast (congrArg EventField.Action kind.symm) (some value)))
                  (cast (congrArg EventField.Value kind.symm) value)) := by
            intro prior lower earlier actor
            obtain ⟨actualOwner, ty, kind, value, recorded, output⟩ :=
              ghostRecords prior lower earlier
            have sameOwner : actualOwner = owner := Option.some.inj
              ((EventCode.actor_eq_of_binding (G.nodes prior) kind).symm.trans actor)
            subst actualOwner
            refine ⟨ty, kind, value, ?_, recorded⟩
            intro observation active
            change frozen rank ghost owner prior actor _ _ = _
            exact freezeBindingsBefore_binding profile start rank ghost owner prior actor _ _
              ⟨lower, earlier⟩ kind value (optional_value_cast_native_table kind _ value output)
          have sourceKernel : actionDistribution (G.prefixProfile (frozen rank ghost)) ghost event =
              kernel := by
            change actionDistribution (G.prefixProfile (frozen rank ghost)) ghost event =
              actionDistribution reference ghost event
            rw [actionDistribution_of_actor _ _ owned, actionDistribution_of_actor _ _ owned,
              dite_eq_right active, dite_eq_right active]
            change frozen rank ghost owner event owned _ _ = profile owner event owned _ _
            exact freezeBindingsBefore_at_rank profile start rank ghost owner event owned _ _ rfl
          let memberRun := fun action => app.runUntil scheduler
            (Function.update (players rank ghost) owner
              (fixedTurnPolicy bound owner event action
                (clients (G.prefixProfile (frozen rank ghost)) owner))) stop nativeCount execution
          have mixed : native rank ghost = kernel.bind memberRun := by
            have mixed := serviceReference_binding_prefix_mixture scheduler bound relaxed
              (frozen rank ghost) owner event owned notPublication (players rank ghost) follows
              stop execution initialReach start ordered ghost ghostPath ready active
              (fun prior lower upper =>
                bindings prior lower (by dsimp only [event, rank] at *; omega))
              frozenRecords (truthful owner isSelected)
              (fun prior lower upper actor => untouched owner isSelected prior lower
                (by dsimp only [event, rank] at *; omega) actor) trace
            change native rank ghost =
              (actionDistribution (G.prefixProfile (frozen rank ghost)) ghost event).bind memberRun
                at mixed
            rwa [sourceKernel] at mixed
          have memberLaw (action : G.Action event) (selected : action ∈ kernel.support)
              (next : G.Config) (moved : next ∈ (ghost.step event ready action).support) :
              memberRun action = native (rank + 1) next := by
            obtain ⟨value, actionEq, _nextClear, _nextPath, _nextRecord, output⟩ :=
              step_submitted_binding_frame ghost ghostClear event ready
                owner payload binding action (by
                  have played := selected
                  change action ∈ (actionDistribution reference ghost event).support at played
                  rw [actionDistribution_of_actor reference ghost owned, dite_eq_right active]
                    at played
                  exact sourceSubmits owner event owned (G.playerObserve owner ghost) active
                    action played) next moved
            let head := G.prefixPolicy owner (frozen (rank + 1) next owner)
            have fixed : ∀ observation active, head event owned observation active =
                PMF.pure action := by
              intro observation active
              rw [actionEq]
              change frozen (rank + 1) next owner event owned _ _ = _
              exact freezeBindingsBefore_binding profile start (rank + 1) next owner event owned _ _
                ⟨by dsimp only [event, rank]; omega, by dsimp only [event]; omega⟩ binding value
                (optional_value_cast_native_table binding _ value output)
            have updated : Function.update (players rank ghost) owner
                (clients (G.prefixProfile (frozen (rank + 1) next)) owner) =
                players (rank + 1) next := by
              funext actor
              by_cases sameOwner : actor = owner
              · subst actor
                simp only [Function.update_self, players, prescribed, ite_eq_left isSelected]
              · rw [Function.update_of_ne sameOwner]
                dsimp only [players, prescribed]
                by_cases selectedActor : compiled actor
                · simp only [ite_eq_left selectedActor]
                  have sameClient := congrFun (clientsPatch action next moved) actor
                  rw [Function.update_of_ne sameOwner] at sameClient
                  exact sameClient.symm
                · simp only [ite_eq_right selectedActor]
            have law := serviceReferenceTurnPolicy_patch_runUntil
              (count := nativeCount) (turns := turns) scheduler bound
              (G.prefixProfile (frozen rank ghost)) owner event owned action head fixed
              (players rank ghost) stop execution
            change app.runUntil scheduler (Function.update (players rank ghost) owner
              (clients (Function.update (G.prefixProfile (frozen rank ghost)) owner
                (patchPolicy event head ((G.prefixProfile (frozen rank ghost)) owner))) owner))
              stop nativeCount execution = memberRun action at law
            rw [referencePatch action next moved, updated] at law
            exact law.symm
          calc
            native rank ghost = kernel.bind memberRun := mixed
            _ = kernel.bind (fun action => (ghost.step event ready action).bind
                (fun next => native (rank + 1) next)) := by
              apply bind_congr_on_support _
              intro action selected
              calc
                _ = (ghost.step event ready action).bind (fun _ => memberRun action) :=
                  (PMF.bind_const _ _).symm
                _ = _ := bind_congr_on_support _ fun next moved =>
                  memberLaw action selected next moved
            _ = (sourceRun (rest + 1) ghost).bind (native (rank + (rest + 1))) := by
              rw [firstLaw rest]
              simp only [PMF.bind_bind]
              apply bind_congr_on_support _
              intro action selected
              apply bind_congr_on_support _
              intro next moved
              exact nextLaw action selected next moved
  have initial : execution.application.config ∈
      (sourceRun 0 execution.application.config).support := by
    simp only [sourceRun, runPlan, PMF.mem_support_pure_iff]
  have result := advance bindingCount 0 execution.application.config (by omega) initial
  simpa only [Nat.zero_add, Nat.add_zero, native, players, frozen, freezeBindingsBefore_at_start,
    sourceRun] using result


/-- Sample the honest table from the source origin while preserving the full native law. -/
theorem native_binding_unilateral_source_mixture
    {horizon nativeCount remaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (execution : (serviceApplication setup deps duration leaks).Execution)
    {inputs : (serviceGraph setup deps).Inputs}
    (initialReach : execution.application.config.Reachable inputs)
    (sourceOrigin : setup.informationGraph.Config)
    (same : runKey execution.application.config =
      runKey ((serviceGraph setup deps).fromSequentialConfig sourceOrigin))
    (start bindingCount : Nat) (ordered : sourceOrigin.cut.IsPrefix start)
    (clear : sourceOrigin.defaulted = ∅)
    (bounded : start + bindingCount ≤ (serviceGraph setup deps).order.eventCount)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + bindingCount →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (truthful : ∀ owner, owner ≠ focal → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks execution owner)
    (untouched : ∀ owner, owner ≠ focal →
      ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + bindingCount →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining + nativeCount, none, execution⟩)) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let clients := fun reference => turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns
      (firstTurnTiming setup turns deps) reference
    let players := fun reference => Function.update (clients reference) focal deviation
    let placeholder := Function.update profile focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal)
    app.runUntil scheduler (players (G.prefixProfile profile)) stop nativeCount execution =
      (setup.informationGraph.runPlan (setup.informationGraph.policyPlan
        (setup.informationGraph.prefixProfile placeholder)
          setup.informationGraph.canonicalScheduler) bindingCount sourceOrigin).bind fun ghost =>
            app.runUntil scheduler (players (setup.informationGraph.prefixProfile
              (setup.informationGraph.freezeBindingsBefore profile start
                (start + bindingCount) ghost))) stop nativeCount execution := by
  classical
  intro G app clients players placeholder
  have actualOrdered : execution.application.config.cut.IsPrefix start := by
    have cut : execution.application.config.cut = (G.fromSequentialConfig sourceOrigin).cut :=
      congrArg Prod.fst same
    rw [cut]
    exact ordered
  have actualClear : execution.application.config.defaulted = ∅ := by
    have records := congrArg (fun key => key.2.2) same
    rw [defaulted_eq_of_completionOf_eq records, G.fromSequentialConfig_defaulted, clear]
  let prescribed := fun reference actor =>
    if actor ≠ focal then clients reference actor else deviation
  have prescribedEq (reference : G.BehavioralProfile) :
      prescribed reference = players reference := by
    funext owner
    by_cases own : owner = focal
    · subst owner
      simp only [prescribed, players, Function.update_self, ne_eq, not_true_eq_false, ite_false]
    · simp only [prescribed, players, ite_eq_left own, Function.update_of_ne own]
  have drawn := native_binding_subfamily_mixture (setup := setup) (deps := deps)
    (duration := duration) (leaks := leaks) (turns := turns) scheduler bound relaxed profile submits
    (fun owner => owner ≠ focal) (fun _ => deviation) stop execution initialReach start bindingCount
    actualOrdered actualClear bounded bindings truthful untouched trace
  change app.runUntil scheduler (prescribed (G.prefixProfile profile)) stop nativeCount execution =
    (G.runPlan (G.policyPlan (G.prefixProfile profile) G.canonicalScheduler) bindingCount
      execution.application.config).bind (fun ghost => app.runUntil scheduler
        (prescribed (G.prefixProfile (G.freezeBindingsBefore profile start
          (start + bindingCount) ghost))) stop nativeCount execution) at drawn
  simp_rw [prescribedEq] at drawn
  have normalized := drawn.trans (runPlan_canonical_prefixProfile_bind_frozen_fromSequential
    (graph := G) profile bindingCount start (start + bindingCount) execution.application.config
      sourceOrigin same
      (fun reference => app.runUntil scheduler (players reference) stop nativeCount execution))
  change app.runUntil scheduler (players (G.prefixProfile profile)) stop nativeCount execution =
    (setup.informationGraph.runPlan (setup.informationGraph.policyPlan
      (setup.informationGraph.prefixProfile profile) setup.informationGraph.canonicalScheduler)
      bindingCount sourceOrigin).bind (fun ghost => app.runUntil scheduler
        (players (setup.informationGraph.prefixProfile (setup.informationGraph.freezeBindingsBefore
          profile start (start + bindingCount) ghost))) stop nativeCount execution) at normalized
  have prefixSubmits (base : setup.informationGraph.BehavioralProfile)
      (baseSubmits : setup.informationGraph.SubmitsBindings base) :
      setup.informationGraph.SubmitsBindings (setup.informationGraph.prefixProfile base) := by
    intro owner event actor observation active action supported
    exact baseSubmits owner event actor _ _ action supported
  have placeholderSubmits : setup.informationGraph.SubmitsBindings placeholder := by
    intro owner event actor observation active action supported
    dsimp only [placeholder] at supported
    by_cases own : owner = focal
    · subst owner
      rw [Function.update_self] at supported
      exact setup.informationGraph.policySubmitsBindings_submitPolicy focal _ event actor
        observation active action supported
    · rw [Function.update_of_ne own] at supported
      exact submits owner event actor observation active action supported
  have playersEq (left right : G.BehavioralProfile)
      (policies : ∀ owner, owner ≠ focal → left owner = right owner) :
      players left = players right :=
    by
    funext owner
    by_cases own : owner = focal
    · subst owner
      simp only [players, Function.update_self]
    · simp only [players, Function.update_of_ne own]
      exact serviceReferenceTurnPolicy_eq_of_owner (setup := setup) (deps := deps)
        (duration := duration) (leaks := leaks) bound turns (firstTurnTiming setup turns deps)
        left right owner (policies owner own)
  apply normalized.trans
  refine runPlan_bind_frozen_of_bindingObservers (graph := setup.informationGraph) focal profile
    (setup.informationGraph.prefixProfile profile)
    (setup.informationGraph.prefixProfile placeholder) (prefixSubmits profile submits)
    (prefixSubmits placeholder placeholderSubmits) ?_ bindingCount start (start + bindingCount)
    sourceOrigin sourceOrigin ordered ordered bounded bindings rfl
    (fun reference => app.runUntil scheduler (players reference) stop nativeCount execution) ?_
  · intro owner foreign
    change setup.informationGraph.prefixPolicy owner (profile owner) =
      setup.informationGraph.prefixPolicy owner (Function.update profile focal
        (submittedFailurePolicy (graph := setup.informationGraph) focal) owner)
    rw [Function.update_of_ne foreign]
  · intro left right policies
    exact congrArg (fun reference => app.runUntil scheduler reference stop nativeCount execution)
      (playersEq left right policies)

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Effective-opening clients predraw the same ordinary source binding table. -/
theorem native_binding_unilateral_effective_source_mixture
    {horizon nativeCount remaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (execution : (serviceApplication setup deps duration leaks).Execution)
    {inputs : (serviceGraph setup deps).Inputs}
    (initialReach : execution.application.config.Reachable inputs)
    (sourceOrigin : setup.informationGraph.Config)
    (same : runKey execution.application.config =
      runKey ((serviceGraph setup deps).fromSequentialConfig sourceOrigin))
    (start bindingCount : Nat) (ordered : sourceOrigin.cut.IsPrefix start)
    (clear : sourceOrigin.defaulted = ∅)
    (bounded : start + bindingCount ≤ (serviceGraph setup deps).order.eventCount)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + bindingCount →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (truthful : ∀ owner, owner ≠ focal → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks execution owner)
    (untouched : ∀ owner, owner ≠ focal →
      ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + bindingCount →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining + nativeCount, none, execution⟩)) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let clients := fun raw => turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening (G.prefixProfile raw))
    let players := fun raw => Function.update (clients raw) focal deviation
    let placeholder := Function.update profile focal
      (submittedFailurePolicy (graph := setup.informationGraph) focal)
    app.runUntil scheduler (players profile) stop nativeCount execution =
      (setup.informationGraph.runPlan (setup.informationGraph.policyPlan
        (setup.informationGraph.prefixProfile placeholder)
          setup.informationGraph.canonicalScheduler) bindingCount sourceOrigin).bind fun ghost =>
            app.runUntil scheduler (players (setup.informationGraph.freezeBindingsBefore profile
              start (start + bindingCount) ghost)) stop nativeCount execution := by
  let G := serviceGraph setup deps
  have law := native_binding_unilateral_source_mixture (turns := turns) scheduler bound relaxed
    (effectiveOpening (graph := G) profile) submits.effectiveOpening focal deviation stop execution
      initialReach sourceOrigin same start bindingCount ordered clear bounded bindings truthful
        untouched trace
  dsimp only at law
  have sourceDistribution : setup.informationGraph.runPlan (setup.informationGraph.policyPlan
      (setup.informationGraph.prefixProfile
        (Function.update (effectiveOpening (graph := G) profile) focal
          (submittedFailurePolicy (graph := setup.informationGraph) focal)))
      setup.informationGraph.canonicalScheduler) bindingCount sourceOrigin =
      setup.informationGraph.runPlan (setup.informationGraph.policyPlan
        (setup.informationGraph.prefixProfile (Function.update profile focal
          (submittedFailurePolicy (graph := setup.informationGraph) focal)))
        setup.informationGraph.canonicalScheduler) bindingCount sourceOrigin := by
    apply runPlan_canonical_prefix_congr (graph := setup.informationGraph) _ _ bindingCount
      start sourceOrigin ordered bounded
    intro event lower upper who actor observation active
    simp only [prefixProfile, prefixPolicy]
    by_cases own : who = focal
    · subst who
      simp only [Function.update_self]
    · simp only [Function.update_of_ne own]
      obtain ⟨owner, payload, outputEq⟩ := bindings event lower upper
      exact effectiveOpening_of_not_publication profile (by rw [outputEq]; exact id) actor _ _
  rw [sourceDistribution] at law
  have frozen (ghost : setup.informationGraph.Config) :
      setup.informationGraph.freezeBindingsBefore (effectiveOpening (graph := G) profile)
          start (start + bindingCount) ghost =
        effectiveOpening (graph := G)
          (setup.informationGraph.freezeBindingsBefore profile
          start (start + bindingCount) ghost) := by
    change (serviceGraph setup deps).freezeBindingsBefore (effectiveOpening (graph := G) profile)
        start (start + bindingCount) ((serviceGraph setup deps).fromSequentialConfig ghost) =
      effectiveOpening (graph := G)
        ((serviceGraph setup deps).freezeBindingsBefore profile
        start (start + bindingCount) ((serviceGraph setup deps).fromSequentialConfig ghost))
    exact (effectiveOpening_freezeBindingsBefore profile start (start + bindingCount) _).symm
  have prefixed (raw : (serviceGraph setup deps).BehavioralProfile) :
      setup.informationGraph.prefixProfile (effectiveOpening (graph := G) raw) =
        effectiveOpening (graph := G)
          ((serviceGraph setup deps).prefixProfile raw) := by
    change (serviceGraph setup deps).prefixProfile (effectiveOpening (graph := G) raw) = _
    exact prefixProfile_effectiveOpening (graph := G) raw
  simpa only [frozen, prefixed, prefixProfile_effectiveOpening] using law

end Vegas

module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.PublicationPolicy
public import Vegas.EventGraph.BarrierBlocks
public import Vegas.Game.BindingBlockCompletion
public import Vegas.Game.RevealPhasing
public import Vegas.Game.RevealServiceEffectiveTimely
public import Vegas.Game.RevealServiceRankedReadout
public import Vegas.Game.RevealServiceSoleSegment
public import Vegas.Game.SourcePrefixNash
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Pending.CanonicalOutcomeAccepted
public import Vegas.Pending.CanonicalOutcomePublication
public import Vegas.Pending.EffectiveOpening

@[expose] public section

/-! # Exact outcomes of intended source-prefix clients

Effective-opening prefix clients retain a default-free canonical continuation across
private binding intervals, publication intervals with repeated owners, and chance steps.
Forcing source disclosure leaves these physical clients exactly unchanged. Every intended
extension therefore has its intended full source configuration and payoff law under the
existing service contract, independently of equilibrium or utility-range assumptions.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Native effective-opening clients are exactly unchanged when source disclosure is forced. -/
theorem effectiveOpening_compilePrescribedProfile_forceDisclose
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (deps : (toEventGraph program).Dependencies)
    (source : BehavioralProfile program) :
    effectiveOpening (compilePrescribedProfile program deps
      (fun who => (source who).forceDisclose program)) =
        effectiveOpening (compilePrescribedProfile program deps source) := by
  let graph := (toEventGraph program).withDependencies deps
  funext who event actor observation active
  by_cases publication : (graph.outputLayout event).IsPublication
  · cases node : nodeView graph event with
    | bind owner payload outputEq codeEq =>
        rw [outputEq] at publication
        exact publication.elim
    | sample payload law outputEq codeEq =>
        rw [outputEq] at publication
        exact publication.elim
    | resolve owner payload binding checks outputEq codeEq =>
        rw [effectiveOpening_of_resolve _ node actor, effectiveOpening_of_resolve _ node actor]
  · rw [effectiveOpening_of_not_publication _ publication actor,
      effectiveOpening_of_not_publication _ publication actor]
    unfold compilePrescribedProfile submitProfile submitPolicy prefixProfile prefixPolicy
      compileEventProfile
    rw [compileEventPolicy_forceDisclose_of_not_publication program who (source who) event actor
      publication]

section

variable {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Effective-opening clients retain the canonical terminal continuation law throughout a
publication interval. Repeated owners are allowed. -/
theorem effective_publication_block_outcomeLaw
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (start finish : Nat)
    (publications : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      ((serviceGraph setup deps).outputLayout event).IsPublication)
    (barrier : ∀ event : (serviceGraph setup deps).EventId, event.val = finish →
      ¬ ((serviceGraph setup deps).outputLayout event).IsPublication)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    (inside : InBlock start finish origin.application.config)
    (supported : origin ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening profile))
      origin.environmentRecall.length).support)
    (bounded : origin.environmentRecall.length ≤ horizon)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening profile))
      (fun current => BlockDone finish current.application.config) horizon origin).support) :
    BlockDone finish final.application.config ∧
      outcomeLaw profile read final.application.config =
        outcomeLaw profile read origin.application.config := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening profile)
  let stop := fun current : app.Execution => BlockDone finish current.application.config
  have shaped : BlockShaped (graph := G) start finish := by
    intro config current running event ready
    have within : config.cut.Within start finish :=
      ⟨current.1, fun other completed => Nat.lt_of_not_ge fun later =>
        current.2 other later completed⟩
    refine ⟨Nat.le_of_not_gt fun earlier => ready.1 (current.1 event earlier), ?_⟩
    exact (relaxed.ready_lt_of_within_publications within barrier publications ready).resolve_right
      running
  have decides : ∀ (config : G.Config) (event : G.EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef G.layout (.binding owner payload))
      (checks : List (GuardCheck G.layout payload))
      (outputEq : G.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
        .resolve owner payload binding checks),
      nodeView G event = .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : G.actor? event = some owner)
        (active : owner ∉ (G.playerObserve owner config).defaulted),
      effectiveOpening profile owner event actor (G.playerObserve owner config) active =
        PMF.pure (cast (congrArg EventField.Action outputEq.symm)
          (openingAccepted event config.store)) := by
    intro config event owner payload binding checks outputEq codeEq node actor active
    rw [effectiveOpening_of_resolve profile node actor]
    change PMF.pure (cast _ (openingAccepted event (G.playerStore owner config.store))) = _
    rw [openingAccepted_playerStore event actor]
  let holds := fun (remaining : Nat) (current : app.Execution) =>
    current ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients
      current.environmentRecall.length).support ∧
    current.environmentRecall.length + remaining ≤ horizon ∧
    (¬ stop current → InBlock start finish current.application.config) ∧
    outcomeLaw profile read current.application.config =
      outcomeLaw profile read origin.application.config
  have preserved : ∀ remaining current, holds (remaining + 1) current → ¬ stop current →
      ∀ next ∈ (app.round scheduler clients current).support, holds remaining next := by
    intro remaining current valid running next moved
    obtain ⟨currentSupport, currentBound, currentInside, currentLaw⟩ := valid
    have readyPublication (event : G.EventId) (ready : current.application.config.cut.Ready event) :
        (G.outputLayout event).IsPublication := by
      have interval := shaped _ (currentInside running) running event ready
      exact publications event interval.1 interval.2
    have deadlines : ∀ event owner, current.application.config.cut.Ready event →
        G.actor? event = some owner → owner ∉ current.application.config.defaulted →
        openingAccepted event current.application.config.store = true →
        current.application.WithinDeadline (serviceTimeouts setup deps duration) event := by
      intro event owner ready actor _active accepted
      exact effectivePublication_withinDeadline contract timely clients owner
        (effectiveOpening profile) decides rfl current.environmentRecall.length (by omega) current
        currentSupport event (relaxed.actorSerial event) actor ready (readyPublication event ready)
        accepted
    have stepLaw := reactive_round_outcomeLaw_of_accepted independent opens read keyed invariant
      (serviceTimeouts setup deps duration) leaks scheduler clients current next readyPublication
      deadlines moved
    have length := app.round_environmentRecall_length scheduler clients current next moved
    refine ⟨?_, by omega, ?_, stepLaw.trans currentLaw⟩
    · rw [length, app.roundsFrom_succ]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨current, currentSupport, moved⟩
    · intro unfinished
      exact (currentInside running).path shaped
        (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler clients
          current next moved) unfinished
  have initial : holds (horizon - origin.environmentRecall.length) origin :=
    ⟨supported, by omega, fun _ => inside, rfl⟩
  obtain ⟨_, _, _, _, law⟩ := app.runUntil_support_holds scheduler clients stop holds preserved
    (horizon - origin.environmentRecall.length) origin initial final reached
  have done := runUntilHorizon_stop contract clients stop
    (fun current terminal event _ => by rw [terminal]; exact Finset.mem_univ event)
    origin supported bounded final reached
  exact ⟨done, law⟩

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

private theorem continuation_pure_of_bind {α β : Type*} (law : PMF α) (next : α → PMF β)
    (point : β) (same : law.bind next = PMF.pure point) (value : α)
    (selected : value ∈ law.support) : next value = PMF.pure point := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro result member
  have supported : result ∈ (law.bind next).support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨value, selected, member⟩
  rw [same, PMF.mem_support_pure_iff] at supported
  exact supported

private theorem honest_phase_outcomeLaw
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (opens : ∀ owner event (actor : (serviceGraph setup deps).actor? event = some owner)
      (publication : ((serviceGraph setup deps).outputLayout event).IsPublication)
      (view : (serviceGraph setup deps).PlayerObservation owner) (active : owner ∉ view.defaulted),
      profile owner event actor view active = PMF.pure (EventField.openAction _ publication))
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    {rank : Nat} (origin : (serviceApplication setup deps duration leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps)
        (effectiveOpening ((serviceGraph setup deps).prefixProfile profile))) rank origin)
    (budget : origin.environmentRecall.length ≤ horizon)
    (pending : rank < (serviceGraph setup deps).order.eventCount)
    (clear : origin.application.config.defaulted = ∅) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let reference := effectiveOpening (G.prefixProfile profile)
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference
    ∃ finish, rank < finish ∧ finish ≤ G.order.eventCount ∧
      BlockShaped (graph := G) rank finish ∧
      (app.runUntilHorizon scheduler clients
        (fun current => BlockDone finish current.application.config) horizon origin).bind
          (fun final => outcomeLaw reference read final.application.config) =
        outcomeLaw reference read origin.application.config := by
  classical
  intro G app reference clients
  have graphCount : G.order.eventCount = (serviceGraph setup deps).order.eventCount := rfl
  let ordinary := G.prefixProfile profile
  have opensOrdinary : ∀ owner event (actor : G.actor? event = some owner)
      (publication : (G.outputLayout event).IsPublication)
      (view : G.PlayerObservation owner) (active : owner ∉ view.defaulted),
      ordinary owner event actor view active = PMF.pure (EventField.openAction _ publication) := by
    intro owner event actor publication view active
    exact opens owner event actor publication _ _
  have ordinaryIndependent : ReadyIndependent ordinary :=
    relaxed.readyIndependent_prefixProfile profile (fun owner event actor publication left right
      leftActive rightActive => (opens owner event actor publication left leftActive).trans
        (opens owner event actor publication right rightActive).symm)
  have independent : ReadyIndependent reference := ordinaryIndependent.effectiveOpening
  have ordinaryOpens : OpensPublications ordinary :=
    fun config event owner actor publication active =>
      opensOrdinary owner event actor publication (G.playerObserve owner config) active
  have twins := erasureTwins_effectiveOpening_honest ordinary opensOrdinary
  have same (config : G.Config) : outcomeLaw reference read config =
      outcomeLaw ordinary read config :=
    twins.runPlan_map_of_erase_invariant G.canonicalScheduler read invariant _ config
  let event : G.EventId := ⟨rank, pending⟩
  have ready : origin.application.config.cut.Ready event :=
    boundary.ordered.ready pending
  have inside (finish : Nat) (later : rank ≤ finish) :
      InBlock rank finish origin.application.config :=
    ⟨fun query early => (boundary.ordered.2 query).mpr early,
      fun query late completed => Nat.not_lt.mpr (Nat.le_trans later late)
        ((boundary.ordered.2 query).mp completed)⟩
  by_cases publication : (G.outputLayout event).IsPublication
  · obtain ⟨finish, run⟩ := exists_revealRun publication
    refine ⟨finish, run.nonempty, run.bounded, run.shaped relaxed, ?_⟩
    have each (final : app.Execution) (reached : final ∈ (app.runUntilHorizon scheduler clients
        (fun current => BlockDone finish current.application.config) horizon origin).support) :
        outcomeLaw reference read final.application.config =
          outcomeLaw reference read origin.application.config := by
      have result := effective_publication_block_outcomeLaw (turns := turns) scheduler bound relaxed
        contract timely ordinary ordinaryIndependent ordinaryOpens read keyed invariant rank finish
        run.publications run.closed origin (inside finish run.nonempty.le) boundary.supported
          budget final reached
      exact (same _).trans (result.2.trans (same _).symm)
    calc
      _ = (app.runUntilHorizon scheduler clients
          (fun current => BlockDone finish current.application.config) horizon origin).bind
            (fun _ => outcomeLaw reference read origin.application.config) :=
        bind_congr_on_support _ each
      _ = _ := PMF.bind_const _ _
  · by_cases publicOutput : (G.outputLayout event).IsPublic
    · have ownerless : G.actor? event = none := by
        cases node : nodeView G event with
        | bind owner payload outputEq codeEq =>
            rw [outputEq] at publicOutput
            exact publicOutput.elim
        | resolve owner payload binding checks outputEq codeEq =>
            exact (publication (by rw [outputEq]; trivial)).elim
        | sample payload law outputEq codeEq =>
            change (G.nodes event).actor = none
            rw [← EventCode.actor_cast outputEq (G.nodes event), codeEq]
            rfl
      have solitary : G.Solitary event := fun cut _ otherReady eventReady =>
        relaxed.ready_alone_of_not_publication cut publicOutput publication eventReady otherReady
      have leading : G.Leading event := by
        intro cut other eventReady unfinished
        exact Nat.le_of_not_gt fun earlier => unfinished (eventReady.2
          (relaxed.keeps (barrierOrder_public_event G.outputLayout earlier publicOutput)
            (Or.inr publication)))
      have shaped : BlockShaped (graph := G) rank (rank + 1) := by
        intro config within running query queryReady
        have eventPending : event ∉ config.cut.completed := by
          intro completed
          apply running
          intro other below
          rcases Nat.lt_or_ge other.val rank with earlier | later
          · exact within.1 other earlier
          · have sameEvent : other = event := Fin.ext (by dsimp only [event]; omega)
            rwa [sameEvent]
        have eventReady : config.cut.Ready event :=
          ⟨eventPending, fun prior member => within.1 prior (G.order.predecessor_lt member)⟩
        have sameEvent := solitary config.cut queryReady eventReady
        subst query
        exact ⟨le_rfl, Nat.lt_succ_self _⟩
      refine ⟨rank + 1, by omega, by omega, shaped, ?_⟩
      let first := fun current : app.Execution => BlockDone (rank + 1) current.application.config
      let second := fun current : app.Execution => event ∈ current.application.config.cut.completed
      have stopping : app.runUntilHorizon scheduler clients first horizon origin =
          app.runUntilHorizon scheduler clients second horizon origin := by
        apply app.runUntil_stop_congr scheduler clients first second
          (fun current => BlockDone rank current.application.config)
        · intro current earlier
          constructor
          · exact fun done => done event (by dsimp only [event]; omega)
          · intro done query below
            rcases Nat.lt_or_ge query.val rank with small | large
            · exact earlier query small
            · have sameEvent : query = event := Fin.ext (by dsimp only [event]; omega)
              rwa [sameEvent]
        · intro current earlier _ next reached
          exact earlier.path (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks
            scheduler clients current next reached)
        · intro query earlier
          exact (boundary.ordered.2 query).mpr earlier
      rw [stopping]
      exact soleSegment_outcomeLaw (turns := turns) (serviceTimeouts setup deps duration) leaks
        scheduler delay bound contract timely reference independent read keyed clients event
        (fun _ _ => rfl) solitary leading publication origin ready boundary.supported
          (boundary.untouched event le_rfl) budget
    · obtain ⟨finish, later, bounded, bindings, barrier⟩ :=
        exists_binding_interval event publicOutput
      change rank < finish at later
      change (∀ query : G.EventId, rank ≤ query.val → query.val < finish →
        ∃ owner payload, G.outputLayout query = .binding owner payload) at bindings
      have splitCount : rank + (finish - rank) = finish := Nat.add_sub_of_le later.le
      refine ⟨finish, later, bounded,
        bindingInterval_shaped relaxed rank finish bindings barrier, ?_⟩
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
        clients origin.environmentRecall.length budget origin boundary.supported
      have inputTrace := trace
      rw [serviceInitialLaw_eq_inputs setup] at inputTrace
      obtain ⟨inputs, _, valid⟩ := reactive_history_invariant
        (serviceTimeouts setup deps duration) leaks (setup.initialLaw.map setup.eventInputs)
          horizon scheduler inputTrace
      have truthful : ∀ owner, OwnSubmissionsAtTurn setup leaks origin owner := by
        intro owner
        exact SubmitsAtTurn.roundsFrom setup leaks
          (sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
            (firstTurnTiming setup turns deps) reference owner)
          (serviceInitialLaw setup deps) origin.environmentRecall.length origin boundary.supported
      have fresh (owner : Player) := sourceServiceTurnPolicy_freshCalls_reference scheduler clients
        owner (firstTurnTiming setup turns deps) reference rfl origin.environmentRecall.length
          origin
          boundary.supported
      have commute : (serviceGraph setup deps).prefixProfile (effectiveOpening profile) =
          reference := prefixProfile_effectiveOpening profile
      have sourceIndependent : ReadyIndependent
          ((serviceGraph setup deps).prefixProfile (effectiveOpening profile)) := by
        rw [commute]
        exact independent
      have law := native_binding_block_outcomeLaw (turns := turns)
        (budget := horizon - origin.environmentRecall.length)
        scheduler bound relaxed contract timely (effectiveOpening profile) submits.effectiveOpening
        sourceIndependent read keyed origin valid.reachable trace truthful
        (roundsFrom_activationsAnswered origin.environmentRecall.length origin boundary.supported)
        (fun owner => (fresh owner).1) (fun owner => (fresh owner).2) rank (finish - rank)
        (by omega) boundary.ordered clear
        (by simpa only [splitCount] using bindings)
        (by simpa only [splitCount] using barrier)
        (fun query lower _ => boundary.untouched query lower)
      dsimp only at law
      rw [commute, splitCount] at law
      exact law


/-- Honest source-prefix clients retain the full canonical terminal continuation law under
arbitrary reveal-relaxed dependencies, whenever that continuation has no defaults. -/
theorem honest_prefix_runToHorizon_outcomeLaw
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (opens : ∀ owner event (actor : (serviceGraph setup deps).actor? event = some owner)
      (publication : ((serviceGraph setup deps).outputLayout event).IsPublication)
      (view : (serviceGraph setup deps).PlayerObservation owner) (active : owner ∉ view.defaulted),
      profile owner event actor view active = PMF.pure (EventField.openAction _ publication))
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let reference := effectiveOpening (G.prefixProfile profile)
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference
    ∀ rank (origin : app.Execution),
      CompletionBoundary setup leaks scheduler clients rank origin →
      origin.environmentRecall.length ≤ horizon →
      outcomeLaw reference Config.defaulted origin.application.config = PMF.pure ∅ →
      (app.runToHorizon scheduler clients horizon origin).map
        (fun final => read final.application.config) =
          outcomeLaw reference read origin.application.config := by
  classical
  intro G app reference clients rank origin
  have graphCount : G.order.eventCount = (serviceGraph setup deps).order.eventCount := rfl
  generalize leftEq : horizon - origin.environmentRecall.length = left
  induction left using Nat.strong_induction_on generalizing rank origin with
  | h left ih =>
    intro boundary budget safe
    by_cases terminal : origin.application.config.cut.Terminal
    · have exactRead (final : app.Execution) (member : final ∈
          (app.runToHorizon scheduler clients horizon origin).support) :
          read final.application.config = read origin.application.config :=
        congrArg read (runRounds_config_eq_of_terminal scheduler clients _ origin final terminal
          member)
      have pure : (app.runToHorizon scheduler clients horizon origin).map
          (fun final => read final.application.config) =
            PMF.pure (read origin.application.config) :=
        (map_congr_on_support _ exactRead).trans (pmf_map_fun_const _ _)
      have remaining := origin.application.config.terminal_iff_remaining_zero.mp terminal
      exact pure.trans (by simp only [outcomeLaw, remaining, EventGraph.runPlan, PMF.pure_map])
    · have pending : rank < G.order.eventCount := by
        by_contra after
        have exactRank : rank = G.order.eventCount := by have := boundary.ordered.1; omega
        apply terminal
        apply origin.application.config.terminal_iff_remaining_zero.mpr
        simp only [Config.remaining, boundary.ordered.card, exactRank]
        omega
      have currentClear := defaulted_eq_empty_of_outcomeLaw reference origin.application.config safe
      let paired := fun config : G.Config => (read config, config.defaulted)
      have pairedKey (a b : G.Config) (same : runKey a = runKey b) : paired a = paired b := by
        exact Prod.ext (keyed a b same)
          (defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) same))
      have pairedInvariant (config : G.Config) : paired config.erase = paired config :=
        Prod.ext (invariant config) config.erase_defaulted
      obtain ⟨finish, later, endBound, shaped, phaseLaw⟩ := honest_phase_outcomeLaw (turns := turns)
        scheduler bound relaxed contract timely profile submits opens paired pairedKey
          pairedInvariant
        origin boundary budget pending currentClear
      let stop := fun current : app.Execution => BlockDone finish current.application.config
      let phase := app.runUntilHorizon scheduler clients stop horizon origin
      change phase.bind (fun final => outcomeLaw reference paired final.application.config) =
        outcomeLaw reference paired origin.application.config at phaseLaw
      have mapDefault (config : G.Config) :
          (outcomeLaw reference paired config).map Prod.snd =
            outcomeLaw reference Config.defaulted config := by
        exact PMF.map_comp _ _ _
      have mapRead (config : G.Config) :
          (outcomeLaw reference paired config).map Prod.fst =
            outcomeLaw reference read config := by
        exact PMF.map_comp _ _ _
      have phaseDefaults : phase.bind (fun final =>
          outcomeLaw reference Config.defaulted final.application.config) = PMF.pure ∅ := by
        calc
          _ = (phase.bind (fun final =>
              outcomeLaw reference paired final.application.config)).map Prod.snd := by
            simp only [PMF.map_bind, mapDefault]
          _ = (outcomeLaw reference paired origin.application.config).map Prod.snd :=
            congrArg (PMF.map Prod.snd) phaseLaw
          _ = _ := (mapDefault _).trans safe
      have phaseRead : phase.bind (fun final =>
          outcomeLaw reference read final.application.config) =
            outcomeLaw reference read origin.application.config := by
        calc
          _ = (phase.bind (fun final =>
              outcomeLaw reference paired final.application.config)).map Prod.fst := by
            simp only [PMF.map_bind, mapRead]
          _ = (outcomeLaw reference paired origin.application.config).map Prod.fst :=
            congrArg (PMF.map Prod.fst) phaseLaw
          _ = _ := mapRead _
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler clients stop, PMF.map_bind]
      calc
        _ = phase.bind (fun final => outcomeLaw reference read final.application.config) := by
          apply bind_congr_on_support _
          intro final reached
          have safeFinal := continuation_pure_of_bind phase
            (fun next => outcomeLaw reference Config.defaulted next.application.config) ∅
            phaseDefaults final reached
          have clearFinal := defaulted_eq_empty_of_outcomeLaw reference final.application.config
            safeFinal
          have done : stop final := runUntilHorizon_stop contract clients stop
            (fun current completed query _ => by
              change current.application.config.cut.completed = Finset.univ at completed
              rw [completed]
              exact Finset.mem_univ query) origin
            boundary.supported budget final reached
          have inside : InBlock rank finish origin.application.config :=
            ⟨fun query earlier => (boundary.ordered.2 query).mpr earlier,
              fun query beyond completed => Nat.not_lt.mpr (Nat.le_trans later.le beyond)
                ((boundary.ordered.2 query).mp completed)⟩
          have within := blockRun_within_of_clear (serviceTimeouts setup deps duration) leaks
            scheduler clients shaped (horizon - origin.environmentRecall.length) origin final
            (boundary.ordered.within later.le) reached clearFinal
          have finalPrefix := within.isPrefix endBound done
          have future := blockRun_untouched later.le shaped scheduler clients
            (horizon - origin.environmentRecall.length) origin final inside boundary.untouched
              reached
          obtain ⟨used, withinBudget, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler clients
            stop (horizon - origin.environmentRecall.length) origin final reached
          have finalSupport := app.roundsFrom_runUntil scheduler clients
            (serviceInitialLaw setup deps)
            stop (horizon - origin.environmentRecall.length) origin final boundary.supported reached
          have finalBudget : final.environmentRecall.length ≤ horizon := by omega
          have usedPositive : 0 < used := by
            by_contra zero
            have usedZero : used = 0 := by omega
            subst used
            cases (PMF.mem_support_pure_iff _ _).mp rounds
            let event : G.EventId := ⟨rank, pending⟩
            exact (Nat.lt_irrefl rank) ((boundary.ordered.2 event).mp
              (done event (by dsimp only [event]; omega)))
          exact ih (horizon - final.environmentRecall.length) (by omega) finish final rfl
            ⟨finalSupport, finalPrefix, future⟩ finalBudget safeFinal
        _ = _ := phaseRead


/-- At initialization, an empty-default canonical law transfers the complete honest native law. -/
theorem honest_prefix_roundsFrom_outcomeLaw
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (opens : ∀ owner event (actor : (serviceGraph setup deps).actor? event = some owner)
      (publication : ((serviceGraph setup deps).outputLayout event).IsPublication)
      (view : (serviceGraph setup deps).PlayerObservation owner) (active : owner ∉ view.defaulted),
      profile owner event actor view active = PMF.pure (EventField.openAction _ publication))
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right, runKey left = runKey right → read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (safe : (serviceInitialLaw setup deps).bind (fun state => outcomeLaw
      (effectiveOpening ((serviceGraph setup deps).prefixProfile profile)) Config.defaulted
        state.config) = PMF.pure ∅) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let reference := effectiveOpening (G.prefixProfile profile)
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference
    (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon).map
      (fun final => read final.application.config) =
        (serviceInitialLaw setup deps).bind
          (fun state => outcomeLaw reference read state.config) := by
  classical
  intro G app reference clients
  unfold ReactiveApplication.roundsFrom
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro state selected
  let execution := ReactiveApplication.Execution.initial app state
  have supported : execution ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients
      execution.environmentRecall.length).support := by
    change execution ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler clients 0).support
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, selected, by
      simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff]
      rfl⟩
  have ordered : state.config.cut.IsPrefix 0 := by
    have encoded := selected
    rw [serviceInitialLaw_eq_inputs setup, PMF.mem_support_map_iff] at encoded
    obtain ⟨inputs, _, rfl⟩ := encoded
    exact EventOrder.Cut.empty_isPrefix _
  have boundary : CompletionBoundary setup leaks scheduler clients 0 execution := by
    refine ⟨supported, ordered, ?_⟩
    intro event _ owner entry member
    cases member
  have safeState := continuation_pure_of_bind (serviceInitialLaw setup deps)
    (fun state => outcomeLaw reference Config.defaulted state.config) ∅ safe state selected
  exact honest_prefix_runToHorizon_outcomeLaw (turns := turns) scheduler bound relaxed contract
    timely profile
    submits
    opens read keyed invariant 0 execution boundary (Nat.zero_le _) safeState

end

private theorem native_intended_law_of_disclosing (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (excluded : Player → ℝ)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound) :
    let app := serviceApplication setup deps duration leaks
    let source := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := effectiveOpening (compilePrescribedProfile setup.program deps source)
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference
    let native := app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon
    (∀ final ∈ native.support, final.application.config.defaulted = ∅) ∧
      native.map (fun final => setup.graphObservation deps parameter utility excluded
        final.application.config) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) := by
  classical
  intro app source reference clients native
  let G := serviceGraph setup deps
  let raw : G.BehavioralProfile := compileEventProfile setup.program source
  let base := G.submitProfile raw
  let ordinary := compilePrescribedProfile setup.program deps source
  let graphPlay := (G.gameForm (setup.graphInputs deps) G.canonicalScheduler).play ordinary
  have ordinaryEq : G.prefixProfile base = ordinary :=
    (G.submitProfile_prefixProfile raw).symm
  have baseSubmits : G.SubmitsBindings base := submitsBindings_submitProfile G raw
  have opensBase : ∀ owner event (actor : G.actor? event = some owner)
      (publication : (G.outputLayout event).IsPublication) (view : G.PlayerObservation owner)
      (active : owner ∉ view.defaulted),
      base owner event actor view active = PMF.pure (EventField.openAction _ publication) := by
    intro owner event actor publication view active
    change (compileEventPolicy setup.program owner (source owner) event actor view active).map
      (EventField.submitAction (G.outputLayout event)) = _
    rw [compileEventPolicy_publication setup.program owner (source owner) (disclosing owner) event
      actor publication view active, PMF.pure_map]
    congr 1
    exact EventField.submitAction_eq_self _ _
      (EventField.submitted_of_publication _ publication _)
  have opensOrdinary : ∀ owner event (actor : G.actor? event = some owner)
      (publication : (G.outputLayout event).IsPublication) (view : G.PlayerObservation owner)
      (active : owner ∉ view.defaulted),
      ordinary owner event actor view active = PMF.pure (EventField.openAction _ publication) := by
    intro owner event actor publication view active
    exact compilePrescribedProfile_publication setup.program deps source disclosing owner event
      actor publication view active
  have twins : ErasureTwins reference ordinary :=
    erasureTwins_effectiveOpening_honest ordinary opensOrdinary
  have graphClean (outcome : G.gameSignature.Outcome) (member : outcome ∈ graphPlay.support) :
      outcome.1.defaulted = ∅ := by
    have clean := (setup.compileIntendedExtension_clean deps relaxed wellFormed intended target
      agrees disclosing G.canonicalScheduler outcome member).1
    change (rankedConfig (graph := G) outcome.1 outcome.2).defaulted = ∅ at clean
    rwa [defaulted_rankedConfig] at clean
  have defaultsKey (left right : G.Config) (same : runKey left = runKey right) :
      left.defaulted = right.defaulted :=
    defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) same)
  have initialClean : (serviceInitialLaw setup deps).bind (fun state =>
      outcomeLaw ordinary Config.defaulted state.config) = PMF.pure ∅ := by
    rw [← service_play_outcomeLaw setup deps ordinary Config.defaulted]
    exact (map_congr_on_support _ graphClean).trans (pmf_map_fun_const _ _)
  have initialEffectiveClean : (serviceInitialLaw setup deps).bind (fun state =>
      outcomeLaw reference Config.defaulted state.config) = PMF.pure ∅ := by
    calc
      _ = (serviceInitialLaw setup deps).bind (fun state =>
          outcomeLaw ordinary Config.defaulted state.config) :=
        bind_congr_on_support _ (fun state _ => twins.runPlan_map_of_erase_invariant
          G.canonicalScheduler Config.defaulted Config.erase_defaulted _ state.config)
      _ = _ := initialClean
  have baseSafe : (serviceInitialLaw setup deps).bind (fun state => outcomeLaw
      (effectiveOpening (G.prefixProfile base)) Config.defaulted state.config) = PMF.pure ∅ := by
    rw [ordinaryEq]
    exact initialEffectiveClean
  have nativeDefaultLaw := honest_prefix_roundsFrom_outcomeLaw (turns := turns) scheduler bound
    relaxed contract timely base baseSubmits opensBase Config.defaulted defaultsKey
    Config.erase_defaulted baseSafe
  dsimp only at nativeDefaultLaw
  rw [ordinaryEq] at nativeDefaultLaw
  have nativeClean (final : app.Execution) (selected : final ∈ native.support) :
      final.application.config.defaulted = ∅ := by
    have observed : final.application.config.defaulted ∈
        (native.map (fun final => final.application.config.defaulted)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, selected, rfl⟩
    change (native.map (fun final => final.application.config.defaulted)) = _ at nativeDefaultLaw
    rw [nativeDefaultLaw, initialEffectiveClean, PMF.mem_support_pure_iff] at observed
    exact observed
  refine ⟨nativeClean, ?_⟩
  let read := fun config : G.Config =>
    setup.graphObservation deps parameter utility excluded config.erase
  have keyed (left right : G.Config) (same : runKey left = runKey right) : read left = read right :=
    setup.graphObservation_factors deps parameter utility excluded _ _ (erasedKey_congr same)
  have invariant (config : G.Config) : read config.erase = read config := by
    simp only [read, Config.erase_erase]
  have physical := honest_prefix_roundsFrom_outcomeLaw (turns := turns) scheduler bound relaxed
    contract timely base baseSubmits opensBase read keyed invariant baseSafe
  dsimp only at physical
  rw [ordinaryEq] at physical
  have physicalOrdinary : native.map (fun final => read final.application.config) =
      (serviceInitialLaw setup deps).bind (fun state => outcomeLaw ordinary read state.config) := by
    refine physical.trans ?_
    exact bind_congr_on_support _ (fun state _ => twins.runPlan_map_of_erase_invariant
      G.canonicalScheduler read invariant _ state.config)
  have sourceLaw := setup.compileIntendedExtension_law deps relaxed wellFormed parameter utility
    excluded intended target agrees disclosing G.canonicalScheduler
  calc
    _ = native.map (fun final => read final.application.config) := by
      apply map_congr_on_support
      intro final selected
      dsimp only [read]
      rw [final.application.config.erase_eq_of_defaulted_empty (nativeClean final selected)]
    _ = (serviceInitialLaw setup deps).bind
        (fun state => outcomeLaw ordinary read state.config) := physicalOrdinary
    _ = graphPlay.map (fun outcome => read outcome.1) :=
      (service_play_outcomeLaw setup deps ordinary read).symm
    _ = graphPlay.map (fun outcome => (some (setup.graphReadout deps outcome), fun who =>
        setup.graphPayoff deps parameter utility excluded who outcome.1)) := by
      apply map_congr_on_support
      intro outcome selected
      dsimp only [read]
      rw [outcome.1.erase_eq_of_defaulted_empty (graphClean outcome selected)]
      unfold Setup.graphObservation
      rw [dite_eq_left outcome.2]
      rfl
    _ = _ := sourceLaw

/-- Exact intended native observation laws certify completion and successful ranked readout. -/
private theorem native_clean_of_intended_law (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies) (wellFormed : setup.WellFormed)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (excluded : Player → ℝ)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon : Nat} (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (clients : Player → (serviceApplication setup deps duration leaks).Policy)
    (law : ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler clients horizon).map (fun final =>
        setup.graphObservation deps parameter utility excluded final.application.config) =
          (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
            (fun final => (setup.protocolReadout final.state, fun who =>
              (setup.protocolReadout final.state).elim 0
                (fun terminal => utility (setup.parameterOutcome parameter terminal) who))))
    (final : (serviceApplication setup deps duration leaks).Execution)
    (selected : final ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler clients horizon).support) :
    final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
      ∃ terminal, serviceRankedReadout setup deps duration leaks
        ((serviceApplication setup deps duration leaks).finished final) = some terminal ∧
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0 := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
    clients
    horizon le_rfl final selected
  have complete : final.application.config.cut.Terminal := contract.completes _ trace
    (by exact ⟨Nat.sub_self _, rfl⟩)
  let terminal := setup.graphReadout deps ⟨final.application.config, complete⟩
  have observed : setup.graphObservation deps parameter utility excluded final.application.config ∈
      ((setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state, fun who =>
          (setup.protocolReadout final.state).elim 0
            (fun terminal => utility (setup.parameterOutcome parameter terminal) who)))).support
              := by
    rw [← law, PMF.mem_support_map_iff]
    exact ⟨final, selected, rfl⟩
  obtain ⟨history, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  have sourceRead : setup.protocolReadout history.state = some terminal := by
    have read := congrArg Prod.fst same
    change setup.protocolReadout history.state =
      (if stopped : final.application.config.cut.Terminal then
        some (setup.graphReadout deps ⟨final.application.config, stopped⟩) else none) at read
    simpa only [dite_eq_left complete] using read
  have intendedState := setup.intendedState_trace wellFormed history.trace
  have sourceClear : terminal.defaulted = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
    (fun who => setup.not_defaulted_of_intendedState intendedState who sourceRead)
  have nativeClear : final.application.config.defaulted = ∅ := by
    change (rankedConfig (graph := G)
      final.application.config complete).defaulted = ∅ at sourceClear
    rwa [defaulted_rankedConfig] at sourceClear
  refine ⟨complete, nativeClear, terminal, ?_, fun who =>
    setup.failedReveals_eq_zero_of_intendedState intendedState who sourceRead⟩
  unfold serviceRankedReadout ReactiveApplication.finished
  simp only [Option.bind_some]
  rw [ite_eq_left complete]
  have storeEq : (rankedConfig (graph := G) final.application.config complete).store =
      final.application.config.store := by
    funext field
    cases field <;> rfl
  have decoded := decodeConfig?_terminal setup.program
    ⟨rankedConfig (graph := G) final.application.config complete,
      rankedConfig_terminal (graph := G) final.application.config complete⟩
  change decodeConfig? _ _ _ _ _ _ (rankedConfig (graph := G) final.application.config
    complete).store (rankedConfig (graph := G) final.application.config complete).history = _
      at decoded
  rw [storeEq] at decoded
  exact decoded

/-- Every intended extension has its full native configuration and payoff law, with no defaults.
The clients open effectively; no source disclosure or equilibrium premise is required. -/
theorem native_compileIntendedExtension_law (setup : Setup (Player := Player) (L := L))
    [Finite Player] (deps : setup.dataflowGraph.Dependencies)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (excluded : Player → ℝ)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound) :
    let app := serviceApplication setup deps duration leaks
    let source := setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
      target
    let reference := effectiveOpening (compilePrescribedProfile setup.program deps source)
    let clients := serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) reference
    let native := app.roundsFrom (serviceInitialLaw setup deps) scheduler clients horizon
    (∀ final ∈ native.support,
      final.application.config.cut.Terminal ∧ final.application.config.defaulted = ∅ ∧
        ∃ terminal, serviceRankedReadout setup deps duration leaks (app.finished final) =
          some terminal ∧ ∀ who,
            failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      native.map (fun final => setup.graphObservation deps parameter utility excluded
        final.application.config) =
        (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
          (fun final => (setup.protocolReadout final.state, fun who =>
            (setup.protocolReadout final.state).elim 0
              (fun terminal => utility (setup.parameterOutcome parameter terminal) who))) := by
  classical
  intro app source reference clients native
  have result := native_intended_law_of_disclosing (turns := turns) setup deps relaxed wellFormed
    parameter utility excluded intended (setup.disclosingSourceProfile target)
    (setup.disclosingSourceProfile_extends intended target agrees)
    (setup.disclosingSourceProfile_disclosing target) duration leaks scheduler bound contract timely
  dsimp only at result
  rw [setup.decodeBehavioralProfile_disclosingSourceProfile,
    effectiveOpening_compilePrescribedProfile_forceDisclose] at result
  refine ⟨?_, result.2⟩
  intro final selected
  exact native_clean_of_intended_law setup deps wellFormed parameter utility excluded intended
    duration leaks scheduler bound contract clients result.2 final selected

end Vegas

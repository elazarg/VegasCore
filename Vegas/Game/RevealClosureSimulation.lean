/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealClosureSolitary
import Vegas.Game.RevealDeviationLaw

/-! # Simulating a deviation through the closure

Every deviation of one player from honest effective-opening clients is
simulated phase by phase, from every phase boundary, by the last-served
erased-key laws of normalized graph deviations of the base, read at the
closure key: a solitary commitment or chance event is one phase, and a run of
concurrent reveals is a sequence of steps, one to each reveal of the deviator
in the run and a last one to the run's end. No condition on the runs of reveals
is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **A solitary phase through the closure.** At a phase boundary whose event
is not a reveal, the phase completing that event supplies its joint law and
averaged target for the closure key. -/
theorem solitary_phaseJoint {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (event : (serviceGraph setup mode).EventId)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication) :
    PhaseJoint (fun execution : (serviceApplication setup mode deadline leaks).Execution =>
        runKey (EventGraph.closure ((serviceGraph setup mode).normalizeProfile base) who
          execution.application.config))
      ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
      (fun policy => keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy)
        who)
      (PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline
        leaks bound turns (firstTurnTiming setup turns mode)
        ((serviceGraph setup mode).normalizeProfile base)) who deviation) horizon event.val)
      (fun execution => (serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
          who deviation)
        (fun current => event ∈ current.application.config.cut.completed) horizon execution) := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) R) who deviation
  have alone := alone_of_not_publication concurrent notPublication
  have endpoint := solitaryPhase_endpoint contract players concurrent event notPublication
  have stays : ∀ execution, PhaseBoundary scheduler players horizon event.val execution →
      event ∈ execution.application.config.cut.completed →
      app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon execution =
        PMF.pure execution :=
    fun execution _ done => app.runUntil_of_stop scheduler players _ _ execution done
  have completesOf {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution)
      (goods : ∀ seed ∈ prior.support,
        PhaseBoundary scheduler players horizon event.val (execution seed) ∧
          event ∉ (execution seed).application.config.cut.completed) :
      ∀ seed ∈ prior.support, ∀ final ∈ (app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support, event ∈ final.application.config.cut.completed :=
    fun seed member => runUntilHorizon_stop contract players
      (fun current => event ∈ current.application.config.cut.completed)
      (fun current terminal => by rw [terminal]; exact Finset.mem_univ _)
      (execution seed) (goods seed member).1.supported (goods seed member).1.bounded
  have pendingPrefixOf {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution)
      (goods : ∀ seed ∈ prior.support,
        PhaseBoundary scheduler players horizon event.val (execution seed) ∧
          event ∉ (execution seed).application.config.cut.completed) :
      ∀ seed ∈ prior.support, event ∉ (execution seed).application.config.cut.completed →
        (execution seed).application.config.cut.IsPrefix event.val :=
    fun seed member pending => (goods seed member).1.prefix_of_pending relaxed notPublication
      pending
  cases view : nodeView G event with
  | resolve owner payload binding checks outputEq codeEq =>
      exfalso
      apply notPublication
      rw [outputEq]
      trivial
  | bind owner payload outputEq codeEq =>
      have owned : G.actor? event = some owner := nodeView_bind_actor outputEq codeEq
      apply PhaseJoint.of_skipping
        (fun execution : app.Execution => event ∈ execution.application.config.cut.completed)
        (DefaultedBefore who event owner)
        (fun execution boundary => completed_iff_defaultedBefore R who owned boundary .refl)
        (fun execution boundary final reached => completed_iff_defaultedBefore R who owned
          boundary (runUntil_config_path scheduler players _ _ execution final reached))
        stays
      apply pending_closure_joint base who independent referenceIndependent relaxed event
        notPublication endpoint
      intro Seed prior execution goods noise factor
      by_cases isWho : owner = who
      · subst isWho
        exact lastOwned_phase_patched scheduler horizon bound turns
          (firstTurnTiming setup turns mode) R base owner deviation independent event owned alone
          prior execution (fun seed member => (goods seed member).1.quiescent)
          (pendingPrefixOf prior execution goods)
          (fun seed member done => ((goods seed member).2 done).elim)
          (completesOf prior execution goods) noise factor
      · obtain ⟨nextNoise, joint, averaged⟩ := lastForeign_phase scheduler horizon delay bound
          turns contract timely base referenceIndependent who deviation independent event owner
          owned isWho outputEq codeEq view alone prior execution
          (fun seed member => (goods seed member).1.supported)
          (fun seed member => (goods seed member).1.bounded) (pendingPrefixOf prior execution goods)
          (fun seed member _ => (goods seed member).1.seen.untouched (by omega))
          (fun seed member done => ((goods seed member).2 done).elim)
          noise factor
        exact ⟨id, nextNoise, joint, averaged, fun _ _ _ _ => rfl⟩
  | sample payload law outputEq codeEq =>
      have ownerless : G.actor? event = none := nodeView_sample_actor outputEq codeEq
      have visible : G.fieldVisibleTo who (.inr event) := by
        unfold EventGraph.fieldVisibleTo
        change (G.outputLayout event).VisibleTo who
        rw [outputEq]
        trivial
      have neverDone : ∀ execution, PhaseBoundary scheduler players horizon event.val execution →
          event ∉ execution.application.config.cut.completed := by
        intro execution boundary done
        obtain ⟨_, _, owner, ownedOwner, _⟩ := boundary.later event le_rfl done
        rw [ownerless] at ownedOwner
        cases ownedOwner
      apply PhaseJoint.of_skipping
        (fun execution : app.Execution => event ∈ execution.application.config.cut.completed)
        (fun _ => False)
        (fun execution boundary => iff_false_intro (neverDone execution boundary))
        (fun execution boundary _ _ => iff_false_intro (neverDone execution boundary))
        stays
      apply pending_closure_joint base who independent referenceIndependent relaxed event
        notPublication endpoint
      intro Seed prior execution goods noise factor
      obtain ⟨nextNoise, joint, averaged⟩ := lastChance_phase scheduler horizon bound turns
        (firstTurnTiming setup turns mode) R base who deviation independent event ownerless
        visible alone prior execution (fun seed member => (goods seed member).1.quiescent)
        (fun seed member => pendingPrefixOf prior execution goods seed member
          (goods seed member).2)
        (completesOf prior execution goods) noise factor
      exact ⟨id, nextNoise, joint, averaged, fun _ _ _ _ => rfl⟩

/-- At a terminal configuration nothing settles, so the closure is the
configuration itself. -/
theorem closure_eq_of_terminal (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player) {config : (serviceGraph setup mode).Config}
    (terminal : config.cut.Terminal) : closure reference who config = config := by
  apply closure_of_none
  intro event settles
  apply settles.1.1
  rw [terminal]
  exact Finset.mem_univ _

/-- **The deviation simulation through the closure.** From every phase
boundary of a ledger run in which honest clients open a reveal exactly when its
opening is accepted, the deviation of one player is simulated by the
last-served erased-key laws of normalized graph deviations of the base, read at
the closure key. -/
theorem closureDeviationSimulation {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent) :
    ∀ rank, rank ≤ (serviceGraph setup mode).order.eventCount →
      DeviationSimulation scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
          who deviation) horizon readErased
        (fun execution => runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
          execution.application.config))
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy)
          who)
        (PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline
          leaks bound turns (firstTurnTiming setup turns mode)
          ((serviceGraph setup mode).normalizeProfile base)) who deviation) horizon rank) := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) R) who deviation
  let point := fun execution : app.Execution => runKey (closure R who execution.application.config)
  suffices step : ∀ gap rank, G.order.eventCount - rank = gap → rank ≤ G.order.eventCount →
      DeviationSimulation scheduler players horizon readErased point
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (PhaseBoundary scheduler players horizon rank) from
    fun rank within => step _ rank rfl within
  intro gap
  induction gap using Nat.strong_induction_on with
  | _ gap ih =>
  intro rank hgap within
  by_cases last : rank = G.order.eventCount
  · subst last
    have terminalOf (execution : app.Execution)
        (boundary : PhaseBoundary scheduler players horizon G.order.eventCount execution) :
        execution.application.config.cut.Terminal := by
      unfold EventOrder.Cut.Terminal
      ext event
      simp only [Finset.mem_univ, iff_true]
      exact boundary.earlier event event.isLt
    have frozen : ∀ execution, PhaseBoundary scheduler players horizon G.order.eventCount
        execution →
        (app.runToHorizon scheduler players horizon execution).map
          (fun final => readErased (point final)) =
        PMF.pure (readErased (point execution)) := by
      intro execution boundary
      have terminal := terminalOf execution boundary
      unfold ReactiveApplication.runToHorizon
      rw [show ((app.runRounds scheduler players
          (horizon - execution.environmentRecall.length) execution).map fun final =>
            readErased (point final)) =
          (app.runRounds scheduler players (horizon - execution.environmentRecall.length)
            execution).map fun _ => readErased (point execution) from
        map_congr_on_support _ fun final reached => by
          simp only [point]
          rw [runRounds_config_eq_of_terminal scheduler players _ execution final terminal
            reached]]
      exact pmf_map_fun_const _ _
    have settled : ∀ execution, PhaseBoundary scheduler players horizon G.order.eventCount
        execution →
        keyTarget (G.lastDeviationProfile base who (base who)) who (point execution) =
        PMF.pure (readErased (point execution)) := by
      intro execution boundary
      have terminal := terminalOf execution boundary
      simp only [point]
      rw [closure_eq_of_terminal R who terminal, keyTarget_runKey (independent _),
        lastErasedLaw_terminal _ _ _ terminal, readErased_runKey]
    exact DeviationSimulation.of_frozen frozen (base who) settled
  have smaller : rank < G.order.eventCount := lt_of_le_of_ne within last
  let event : G.EventId := ⟨rank, smaller⟩
  by_cases publication : (G.outputLayout event).IsPublication
  · obtain ⟨finish, run⟩ := exists_revealRun publication
    have runStart : rank < finish := run.nonempty
    have tail : DeviationSimulation scheduler players horizon readErased point
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (PhaseBoundary scheduler players horizon finish) :=
      ih (G.order.eventCount - finish) (by omega) finish rfl run.bounded
    have points : DeviationSimulation scheduler players horizon readErased point
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (RunPoint scheduler players horizon who rank finish rank) :=
      runPoint_simulation bound turns contract timely base decides referenceIndependent who
        deviation independent relaxed concurrent run (@tail) rank runStart.le
    exact DeviationSimulation.mono (@points) fun execution boundary =>
      boundary.runPoint bound turns R who deviation relaxed run
  · have tail : DeviationSimulation scheduler players horizon readErased point
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (PhaseBoundary scheduler players horizon (rank + 1)) :=
      ih (G.order.eventCount - (rank + 1)) (by omega) (rank + 1) rfl smaller
    exact DeviationSimulation.of_averaged_phase (@tail)
      (fun execution => app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon execution)
      (fun execution _ => app.runToHorizon_eq_runUntilHorizon_bind scheduler players _ horizon
        execution)
      (fun execution boundary final reached => solitaryPhase_endpoint contract players concurrent
        event publication execution boundary final reached)
      (solitary_phaseJoint bound turns contract timely base referenceIndependent who deviation
        independent relaxed concurrent event publication)

/-- **The ledger law of a deviation.** Against honest effective-opening clients,
the ledger law of the erased key a deviation of one player reaches by the horizon
is the last-served erased-key law of a normalized graph deviation of the base
from the initial configuration, with no condition on the runs of reveals. -/
theorem closure_deviation_erased_law {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent) :
    ∃ policy : (serviceGraph setup mode).BehavioralPolicy who,
      (serviceInitialLaw setup mode).bind (fun state =>
        ((serviceApplication setup mode deadline leaks).runToHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation) horizon
          (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
            state)).map fun final => readErased (runKey final.application.config)) =
      (serviceInitialLaw setup mode).bind fun state =>
        lastErasedLaw ((serviceGraph setup mode).lastDeviationProfile base who policy) who
          state.config := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) R) who deviation
  let traffic := (serviceRuntime setup mode deadline).bindingTraffic leaks who
  let start := fun state : EventGraphRuntime.State G =>
    ReactiveApplication.Execution.initial app state
  let point := fun execution : app.Execution => runKey (closure R who execution.application.config)
  let noise := fun view : Option (G.PlayerObservation who) =>
    if present : ∃ state ∈ (serviceInitialLaw setup mode).support,
        keyView who (point (start state)) = view then
      PMF.pure (traffic (start present.choose))
    else PMF.pure (traffic (start (serviceInitialLaw setup mode).support_nonempty.choose))
  have trafficOf : ∀ first ∈ (serviceInitialLaw setup mode).support,
      ∀ second ∈ (serviceInitialLaw setup mode).support,
      keyView who (point (start first)) = keyView who (point (start second)) →
      traffic (start first) = traffic (start second) := by
    intro first firstMember second secondMember same
    have raw := phaseBoundary_reflect R who
      (initial_phaseBoundary (horizon := horizon) scheduler players first firstMember)
      (initial_phaseBoundary (horizon := horizon) scheduler players second secondMember) same
    obtain ⟨firstInitial, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstMember
    obtain ⟨secondInitial, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondMember
    exact initial_bindingTraffic_eq_of_keyView (deadline := deadline) (leaks := leaks) who _ _
      raw
  have factor : (serviceInitialLaw setup mode).map (fun state =>
      (point (start state), traffic (start state))) =
      ((serviceInitialLaw setup mode).map fun state => point (start state)).bind
        fun current => (noise (keyView who current)).map fun extra => (current, extra) := by
    rw [PMF.bind_map]
    change (serviceInitialLaw setup mode).bind (fun state => PMF.pure
      (point (start state), traffic (start state))) = _
    apply bind_congr_on_support _
    intro state supported
    have present : ∃ other ∈ (serviceInitialLaw setup mode).support,
        keyView who (point (start other)) = keyView who (point (start state)) :=
      ⟨state, supported, rfl⟩
    simp only [noise, Function.comp_apply, dite_eq_left present, PMF.pure_map]
    obtain ⟨member, same⟩ := present.choose_spec
    rw [trafficOf state supported present.choose member same.symm]
  obtain ⟨policy, law⟩ := closureDeviationSimulation bound turns contract timely base decides
    referenceIndependent who deviation independent relaxed concurrent 0 (Nat.zero_le _)
    (serviceInitialLaw setup mode) start
    (fun state supported => initial_phaseBoundary scheduler players state supported) noise
    factor
  refine ⟨policy, Eq.trans ?_ (law.trans (bind_congr_on_support _ fun state _ => ?_))⟩
  · apply bind_congr_on_support _
    intro state supported
    apply map_congr_on_support _
    intro final reached
    -- the final execution at the horizon is terminal, so its closure is itself
    have terminal : final.application.config.cut.Terminal := by
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players
        (fun current => current.application.config.cut.Terminal) horizon (start state)] at reached
      obtain ⟨middle, middleReached, finalReached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have middleTerminal := runUntilHorizon_stop contract players
        (fun current => current.application.config.cut.Terminal) (fun _ terminal => terminal)
        (start state)
        (initial_phaseBoundary (horizon := horizon) scheduler players state supported).supported
        (initial_phaseBoundary (horizon := horizon) scheduler players state supported).bounded
        middle middleReached
      unfold ReactiveApplication.runToHorizon at finalReached
      rw [runRounds_config_eq_of_terminal scheduler players _ middle final middleTerminal
        finalReached]
      exact middleTerminal
    change readErased (runKey final.application.config) =
      readErased (runKey (closure R who final.application.config))
    rw [closure_eq_of_terminal R who terminal]
  · change keyTarget (G.lastDeviationProfile base who policy) who
        (runKey (closure R who (start state).application.config)) = _
    rw [keyTarget_closure base who policy (independent policy),
      keyTarget_runKey (independent policy)]
    rfl

end Vegas

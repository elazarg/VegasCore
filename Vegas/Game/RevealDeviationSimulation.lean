/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealPhaseBoundary
import Vegas.Game.DeviationSimulation

/-! # Simulating a deviation on the ledger with concurrent reveals

On a graph whose dependencies relax the rank order exactly between independent
reveals and whose runs of reveals are pairwise independent, every deviation of
one player from honest effective-opening clients is simulated phase by phase,
from every phase boundary, by the last-served erased-key law of a normalized
graph deviation of the base: a solitary commitment of the deviator or of an
honest owner, a chance event, or a run of concurrent reveals is one phase, and
at the last boundary every event has completed.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Read

variable {graph : Vegas.EventGraph Player L}

/-- The erased key of any configuration with a given key. -/
def readErased (key : RunKey graph) : RunKey graph :=
  open scoped Classical in
  if found : ∃ config : graph.Config, runKey config = key then erasedKey found.choose else key

/-- The erased key is read from the key. -/
theorem readErased_runKey (config : graph.Config) :
    readErased (runKey config) = erasedKey config := by
  have found : ∃ other : graph.Config, runKey other = runKey config := ⟨config, rfl⟩
  unfold readErased
  rw [dite_eq_left found]
  exact erasedKey_congr found.choose_spec

end Read

/-- A round from a terminal configuration keeps it. -/
theorem round_config_eq_of_terminal
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy}
    {execution next : (serviceApplication setup mode duration leaks).Execution}
    (terminal : execution.application.config.cut.Terminal)
    (reached : next ∈
      ((serviceApplication setup mode duration leaks).round scheduler players execution).support) :
    next.application.config = execution.application.config := by
  rcases Relation.ReflTransGen.cases_head (round_config_path reached) with same | ⟨_, moved, _⟩
  · exact same.symm
  · obtain ⟨event, ready, _, _⟩ := moved
    exact (ready.1 (terminal ▸ Finset.mem_univ event)).elim

/-- Rounds from a terminal configuration keep it. -/
theorem runRounds_config_eq_of_terminal
    (scheduler : (serviceApplication setup mode duration leaks).Scheduler)
    (players : Player → (serviceApplication setup mode duration leaks).Policy) :
    ∀ (count : Nat) (execution final : (serviceApplication setup mode duration leaks).Execution),
      execution.application.config.cut.Terminal →
      final ∈ ((serviceApplication setup mode duration leaks).runRounds scheduler players count
        execution).support →
      final.application.config = execution.application.config := by
  intro count
  induction count with
  | zero =>
      intro execution final _ reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      intro execution final terminal reached
      simp only [ReactiveApplication.runRounds] at reached
      obtain ⟨next, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      have same := round_config_eq_of_terminal terminal moved
      rw [ih next final (same ▸ terminal) rest, same]

/-- **The deviation simulation with concurrent reveals.** From every phase
boundary of a ledger run in which honest clients open a reveal exactly when its
opening is accepted, the deviation of one player is simulated by the
last-served erased-key laws of normalized graph deviations of the base. -/
theorem concurrentDeviationSimulation {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
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
    (who : Player) (deviation : (serviceApplication setup mode duration leaks).Policy)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    (runs : FlatRevealRuns (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent) :
    ∀ rank, rank ≤ (serviceGraph setup mode).order.eventCount →
      DeviationSimulation scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound turns
          (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
          who deviation) horizon readErased
        (fun execution => runKey execution.application.config)
        ((bindingTraffic (serviceTimeouts setup mode duration)) leaks who) (keyView who)
        (fun policy => keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy)
          who)
        (PhaseBoundary scheduler (Function.update (serviceReferenceTurnPolicy setup mode duration
          leaks bound turns (firstTurnTiming setup turns mode)
          ((serviceGraph setup mode).normalizeProfile base)) who deviation) horizon rank) := by
  classical
  let G := serviceGraph setup mode
  let app := serviceApplication setup mode duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode duration leaks bound
    turns (firstTurnTiming setup turns mode) (G.normalizeProfile base)) who deviation
  suffices step : ∀ gap rank, G.order.eventCount - rank = gap → rank ≤ G.order.eventCount →
      DeviationSimulation scheduler players horizon readErased
        (fun execution => runKey execution.application.config)
        ((bindingTraffic (serviceTimeouts setup mode duration)) leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (PhaseBoundary scheduler players horizon rank) from
    fun rank within => step _ rank rfl within
  intro gap
  induction gap using Nat.strong_induction_on with
  | _ gap ih =>
  intro rank hgap within
  by_cases last : rank = G.order.eventCount
  · subst last
    have frozen : ∀ execution, PhaseBoundary scheduler players horizon G.order.eventCount
        execution →
        (app.runToHorizon scheduler players horizon execution).map
          (fun final => readErased (runKey final.application.config)) =
        PMF.pure (readErased (runKey execution.application.config)) := by
      intro execution boundary
      have terminal : execution.application.config.cut.Terminal := by
        unfold EventOrder.Cut.Terminal
        ext event
        simp only [Finset.mem_univ, iff_true]
        exact boundary.earlier event event.isLt
      unfold ReactiveApplication.runToHorizon
      rw [show ((app.runRounds scheduler players
          (horizon - execution.environmentRecall.length) execution).map fun final =>
            readErased (runKey final.application.config)) =
          (app.runRounds scheduler players (horizon - execution.environmentRecall.length)
            execution).map fun _ => readErased (runKey execution.application.config) from
        map_congr_on_support _ fun final reached => by
          rw [runRounds_config_eq_of_terminal scheduler players _ execution final terminal
            reached]]
      exact pmf_map_fun_const _ _
    have settled : ∀ execution, PhaseBoundary scheduler players horizon G.order.eventCount
        execution →
        keyTarget (G.lastDeviationProfile base who (base who)) who
          (runKey execution.application.config) =
        PMF.pure (readErased (runKey execution.application.config)) := by
      intro execution boundary
      have terminal : execution.application.config.cut.Terminal := by
        unfold EventOrder.Cut.Terminal
        ext event
        simp only [Finset.mem_univ, iff_true]
        exact boundary.earlier event event.isLt
      rw [keyTarget_runKey (independent _), lastErasedLaw_terminal _ _ _ terminal,
        readErased_runKey]
    exact DeviationSimulation.of_frozen frozen (base who) settled
  have smaller : rank < G.order.eventCount := lt_of_le_of_ne within last
  have tailOf : ∀ next, next ≤ G.order.eventCount → rank < next →
      DeviationSimulation scheduler players horizon readErased
        (fun execution => runKey execution.application.config)
        ((bindingTraffic (serviceTimeouts setup mode duration)) leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (PhaseBoundary scheduler players horizon next) :=
    fun next bounded later => ih (G.order.eventCount - next) (by omega) next rfl bounded
  let event : G.EventId := ⟨rank, smaller⟩
  have rankEq : event.val = rank := rfl
  by_cases publication : (G.outputLayout event).IsPublication
  · obtain ⟨finish, run⟩ := exists_revealRun publication
    refine DeviationSimulation.of_averaged_phase (@tailOf finish run.bounded run.nonempty)
      (fun execution => app.runUntilHorizon scheduler players
        (fun current => BlockDone finish current.application.config) horizon execution)
      ?_ ?_ ?_
    · intro execution _
      exact app.runToHorizon_eq_runUntilHorizon_bind scheduler players _ horizon execution
    · intro execution boundary final reached
      exact blockPhase_endpoint bound turns contract timely (G.normalizeProfile base) decides who
        deviation relaxed runs run execution boundary final reached
    · intro Seed prior execution goods noise factor
      obtain ⟨build, nextNoise, joint, averaged⟩ := lastBlock_phase bound turns contract timely
        base decides who deviation independent rank finish (run.shaped relaxed)
        run.publications concurrent (run.flat relaxed runs) prior execution
        (fun seed member => (goods seed member).supported)
        (fun seed member => (goods seed member).bounded)
        (fun seed member => (goods seed member).blockStart relaxed runs run)
        (fun seed member => (goods seed member).owners)
        (fun seed member query early _ => (goods seed member).seen.untouched (by omega))
        (fun seed member => runUntilHorizon_stop contract players
          (fun current => BlockDone finish current.application.config)
          (fun current terminal query _ => by rw [terminal]; exact Finset.mem_univ _)
          (execution seed) (goods seed member).supported (goods seed member).bounded)
        noise factor
      exact ⟨build, nextNoise, joint, averaged⟩
  have alone := alone_of_not_publication concurrent publication
  have completes {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution)
      (goods : ∀ seed ∈ prior.support, PhaseBoundary scheduler players horizon rank
        (execution seed)) :
      ∀ seed ∈ prior.support, ∀ final ∈ (app.runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed)).support, event ∈ final.application.config.cut.completed :=
    fun seed member => runUntilHorizon_stop contract players
      (fun current => event ∈ current.application.config.cut.completed)
      (fun current terminal => by rw [terminal]; exact Finset.mem_univ _)
      (execution seed) (goods seed member).supported (goods seed member).bounded
  refine DeviationSimulation.of_averaged_phase (@tailOf (rank + 1) smaller (Nat.lt_succ_self _))
    (fun execution => app.runUntilHorizon scheduler players
      (fun current => event ∈ current.application.config.cut.completed) horizon execution)
    ?_ ?_ ?_
  · intro execution _
    exact app.runToHorizon_eq_runUntilHorizon_bind scheduler players _ horizon execution
  · intro execution boundary final reached
    exact solitaryPhase_endpoint contract players concurrent event publication execution
      boundary final reached
  intro Seed prior execution goods noise factor
  have pendingPrefix : ∀ seed ∈ prior.support,
      event ∉ (execution seed).application.config.cut.completed →
        (execution seed).application.config.cut.IsPrefix event.val :=
    fun seed member pending => (goods seed member).prefix_of_pending relaxed publication pending
  cases view : nodeView G event with
  | resolve owner payload binding checks outputEq codeEq =>
      exfalso
      apply publication
      rw [outputEq]
      trivial
  | bind owner payload outputEq codeEq =>
      have owned : G.actor? event = some owner := nodeView_bind_actor outputEq codeEq
      by_cases isWho : owner = who
      · subst isWho
        obtain ⟨build, nextNoise, joint, averaged⟩ := lastOwned_phase scheduler horizon bound
          turns (firstTurnTiming setup turns mode) (G.normalizeProfile base) base owner deviation
          independent event owned alone prior execution
          (fun seed member => (goods seed member).quiescent) pendingPrefix
          (fun seed member done => observedAction_of_silent owner
            ((goods seed member).later event le_rfl done).1)
          (completes prior execution goods) noise factor
        exact ⟨build, nextNoise, joint, averaged⟩
      · obtain ⟨nextNoise, joint, averaged⟩ := lastForeign_phase scheduler horizon delay bound
          turns contract timely base referenceIndependent who deviation independent event owner
          owned isWho outputEq codeEq view alone prior execution
          (fun seed member => (goods seed member).supported)
          (fun seed member => (goods seed member).bounded) pendingPrefix
          (fun seed member _ => (goods seed member).seen.untouched (by omega))
          (fun seed member done => by
            obtain ⟨recorded, _, other, otherOwned, inactive⟩ :=
              (goods seed member).later event le_rfl done
            rw [owned] at otherOwned
            cases otherOwned
            exact ⟨inactive, by rw [recorded]; rfl⟩)
          noise factor
        exact ⟨id, nextNoise, joint, averaged⟩
  | sample payload law outputEq codeEq =>
      have ownerless : G.actor? event = none := nodeView_sample_actor outputEq codeEq
      have visible : G.fieldVisibleTo who (.inr event) := by
        unfold EventGraph.fieldVisibleTo
        change (G.outputLayout event).VisibleTo who
        rw [outputEq]
        trivial
      have ordered : ∀ seed ∈ prior.support,
          (execution seed).application.config.cut.IsPrefix event.val := by
        intro seed member
        apply pendingPrefix seed member
        intro done
        obtain ⟨_, _, owner, owned, _⟩ := (goods seed member).later event le_rfl done
        rw [ownerless] at owned
        cases owned
      obtain ⟨nextNoise, joint, averaged⟩ := lastChance_phase scheduler horizon bound turns
        (firstTurnTiming setup turns mode) (G.normalizeProfile base) base who deviation
        independent event ownerless visible alone prior execution
        (fun seed member => (goods seed member).quiescent) ordered
        (completes prior execution goods) noise factor
      exact ⟨id, nextNoise, joint, averaged⟩

end Vegas

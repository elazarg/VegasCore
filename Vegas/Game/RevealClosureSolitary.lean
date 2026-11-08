/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunPoint
import Vegas.Game.DeviationSplit
import Vegas.Game.RevealDeviationSimulation

/-! # Solitary phases through the closure

At a phase boundary whose event is not a reveal, the event may already have
completed automatically, for an owner defaulted by an earlier event. Those
executions skip the phase. The deviator tells them apart from the others, both
before and after the phase, by whether the event's owner was defaulted by an
event before it.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A simulation for a larger set of executions is one for a smaller set. -/
theorem DeviationSimulation.mono {Principal : Type} [DecidableEq Principal]
    {app : ReactiveApplication Principal} {scheduler : app.Scheduler}
    {players : Principal → app.Policy} {horizon : Nat} {Point Outcome Traffic View Policy : Type}
    {read : Point → Outcome} {point : app.Execution → Point} {traffic : app.Execution → Traffic}
    {view : Point → View} {target : Policy → Point → PMF Outcome}
    {small large : app.Execution → Prop}
    (simulation :
      DeviationSimulation scheduler players horizon read point traffic view target large)
    (within : ∀ execution, small execution → large execution) :
    DeviationSimulation scheduler players horizon read point traffic view target small :=
  fun prior execution goods noise factor => simulation prior execution
    (fun seed member => within _ (goods seed member)) noise factor

/-- The deviator sees that an owner was defaulted by an event before `event`. -/
def DefaultedBefore (who : Player) (event : (serviceGraph setup mode).EventId) (owner : Player)
    (view : Option ((serviceGraph setup mode).PlayerObservation who)) : Prop :=
  ∃ config : (serviceGraph setup mode).Config, keyView who (runKey config) = view ∧
    ∃ defaulting : (serviceGraph setup mode).EventId, defaulting.val < event.val ∧
      (completionOf config defaulting).bind EventCompletion.defaultEvent = some owner

/-- **An owned solitary event skipped at a boundary.** At a phase boundary
whose event is owned, the event has completed exactly when the deviator sees,
in the closure of any later configuration, that its owner was defaulted by an
earlier event. -/
theorem completed_iff_defaultedBefore (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {horizon : Nat}
    {event : (serviceGraph setup mode).EventId} {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (boundary : PhaseBoundary scheduler players horizon event.val execution)
    {later : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step execution.application.config later) :
    event ∈ execution.application.config.cut.completed ↔
      DefaultedBefore who event owner
        (keyView who (runKey (closure reference who later))) := by
  let G := serviceGraph setup mode
  have toClosure := path.trans (closure_path reference who later)
  constructor
  · intro done
    obtain ⟨_, _, other, otherOwned, inactive⟩ := boundary.later event le_rfl done
    rw [owned] at otherOwned
    cases otherOwned
    rw [mem_defaulted_iff_completionOf] at inactive
    obtain ⟨defaulting, found⟩ := inactive
    obtain ⟨record, recorded⟩ : ∃ record,
        completionOf execution.application.config defaulting = some record := by
      cases recordedEq : completionOf execution.application.config defaulting with
      | none => rw [recordedEq] at found; cases found
      | some record => exact ⟨record, rfl⟩
    have doneDefaulting : defaulting ∈ execution.application.config.cut.completed :=
      (completionOf_isSome_iff _ defaulting).mp (by rw [recorded]; rfl)
    have early : defaulting.val < event.val := by
      by_contra late
      push Not at late
      rw [(boundary.later defaulting late doneDefaulting).1] at found
      cases found
    refine ⟨closure reference who later, rfl, defaulting, early, ?_⟩
    rw [Config.Step.path_completionOf_of_some toClosure defaulting record recorded, ← recorded]
    exact found
  · rintro ⟨config, views, defaulting, early, found⟩
    rw [keyView_runKey, keyView_runKey] at views
    have present : (completionOf config defaulting).isSome := by
      cases recordedEq : completionOf config defaulting with
      | none => rw [recordedEq] at found; cases found
      | some _ => rfl
    have defaults := normalize_defaultEvent_congr who (Option.some.inj views) defaulting present
    have doneDefaulting := boundary.earlier defaulting early
    obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff _ defaulting).mpr doneDefaulting)
    rw [Config.Step.path_completionOf_of_some toClosure defaulting record recorded] at defaults
    have inactive : owner ∈ execution.application.config.defaulted := by
      rw [mem_defaulted_iff_completionOf]
      exact ⟨defaulting, by rw [recorded, ← defaults]; exact found⟩
    by_contra pending
    have ready : execution.application.config.cut.Ready event := ⟨pending, fun prior member =>
      boundary.earlier prior (G.order.predecessor_lt member)⟩
    apply boundary.quiescent event
    unfold EventGraphRuntime.State.AutomaticReady
    rw [owned]
    exact ⟨ready, inactive⟩

/-- **A run of reveals in the deviation simulation.** From every point of a run
of concurrent reveals, the deviation is simulated by the last-served erased-key
laws of normalized graph deviations read at the closure key, once it is from
the phase boundary at the run's end. -/
theorem runPoint_simulation {horizon : Nat}
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
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent) {start finish : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
    (tail : DeviationSimulation scheduler
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
        ((serviceGraph setup mode).normalizeProfile base)) who deviation) horizon finish)) :
    ∀ bar, bar ≤ finish →
      DeviationSimulation scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
          who deviation) horizon readErased
        (fun execution => runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
          execution.application.config))
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy)
          who)
        (RunPoint scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks
          bound turns (firstTurnTiming setup turns mode)
          ((serviceGraph setup mode).normalizeProfile base)) who deviation) horizon who start
          finish bar) := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) R) who deviation
  suffices step : ∀ gap bar, finish - bar = gap → bar ≤ finish →
      DeviationSimulation scheduler players horizon readErased
        (fun execution => runKey (closure R who execution.application.config))
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (RunPoint scheduler players horizon who start finish bar) from
    fun bar within => step _ bar rfl within
  intro gap
  induction gap using Nat.strong_induction_on with
  | _ gap ih =>
  intro bar hgap within
  by_cases hasOwned : ∃ owned : G.EventId, bar ≤ owned.val ∧ owned.val < finish ∧
      G.actor? owned = some who
  · let Ranked := fun rank : Nat => ∃ owned : G.EventId, owned.val = rank ∧ bar ≤ rank ∧
      rank < finish ∧ G.actor? owned = some who
    have exists_ranked : ∃ rank, Ranked rank := by
      obtain ⟨owned, early, late, mine⟩ := hasOwned
      exact ⟨owned.val, owned, rfl, early, late, mine⟩
    obtain ⟨target, targetRank, targetEarlyFound, targetLateFound, targetOwned⟩ :=
      Nat.find_spec exists_ranked
    have targetEarly : bar ≤ target.val := by rw [targetRank]; exact targetEarlyFound
    have targetLate : target.val < finish := by rw [targetRank]; exact targetLateFound
    have least : ∀ event : G.EventId, bar ≤ event.val → event.val < target.val →
        G.actor? event ≠ some who := by
      intro event early smaller mine
      have := Nat.find_min exists_ranked (targetRank ▸ smaller)
      exact this ⟨event, rfl, early, by omega, mine⟩
    have tailTarget : DeviationSimulation scheduler players horizon readErased
        (fun execution => runKey (closure R who execution.application.config))
        ((serviceRuntime setup mode deadline).bindingTraffic leaks who) (keyView who)
        (fun policy => keyTarget (G.lastDeviationProfile base who policy) who)
        (RunPoint scheduler players horizon who start finish (target.val + 1)) :=
      ih (finish - (target.val + 1)) (by omega) (target.val + 1) rfl (by omega)
    refine DeviationSimulation.of_averaged_phase (@tailTarget)
      (fun execution => app.runUntilHorizon scheduler players
        (fun current => target ∈ current.application.config.cut.completed) horizon execution)
      (fun execution _ => app.runToHorizon_eq_runUntilHorizon_bind scheduler players _ horizon
        execution)
      (fun execution point final reached => RunPoint.target_endpoint bound turns contract timely R
        decides who deviation relaxed run target targetOwned targetEarly targetLate least point
        final reached) ?_
    intro Seed prior execution goods noise factor
    exact targetStep_phase bound turns contract timely base decides referenceIndependent who
      deviation independent relaxed concurrent run target targetOwned targetLate prior execution
      (fun seed member => (goods seed member).supported)
      (fun seed member => (goods seed member).bounded)
      (fun seed member =>
        ⟨(goods seed member).earlier, (goods seed member).inside,
          fun event early smaller owned => by
            by_cases low : event.val < bar
            · exact (goods seed member).owned event early low owned
            · exact (least event (by omega) smaller owned).elim,
          fun active => (goods seed member).pending target targetEarly targetLate targetOwned
            active,
          (goods seed member).silent target targetEarly targetLate targetOwned⟩)
      (fun seed member => (goods seed member).submissions) noise factor
  · push Not at hasOwned
    refine DeviationSimulation.of_averaged_phase (@tail)
      (fun execution => app.runUntilHorizon scheduler players
        (fun current => BlockDone finish current.application.config) horizon execution)
      (fun execution _ => app.runToHorizon_eq_runUntilHorizon_bind scheduler players _ horizon
        execution)
      (fun execution point final reached => RunPoint.final_endpoint bound turns contract timely R
        decides who deviation relaxed run point final reached) ?_
    intro Seed prior execution goods noise factor
    exact finalStep_phase bound turns contract timely base decides referenceIndependent who
      deviation relaxed run prior execution
      (fun seed member => (goods seed member).supported)
      (fun seed member => (goods seed member).bounded)
      (fun seed member =>
        ⟨(goods seed member).earlier, (goods seed member).inside,
          fun event early late owned => by
            by_cases low : event.val < bar
            · exact (goods seed member).owned event early low owned
            · exact (hasOwned event (by omega) late owned).elim⟩)
      (fun seed member => (goods seed member).submissions) noise factor

end Vegas

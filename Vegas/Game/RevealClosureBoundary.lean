module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealRunTargetPhase
public import Vegas.Game.FactorTransfer

@[expose] public section

/-! # Phase boundaries seen through the closure

At a phase boundary every event from the boundary's rank on that has completed
did so automatically for an owner defaulted earlier, and no event is
automatically ready. So the configuration is read from the deviator's view of
its closure: two boundaries whose closures look alike to the deviator look
alike themselves.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **Reflection at a phase boundary.** Two phase boundaries at one rank whose
closures look alike to the deviator look alike to the deviator. -/
theorem phaseBoundary_reflect (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player)
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy} {horizon rank : Nat}
    {left right : (serviceApplication setup mode duration leaks).Execution}
    (leftBoundary : PhaseBoundary scheduler players horizon rank left)
    (rightBoundary : PhaseBoundary scheduler players horizon rank right)
    (views : keyView who (runKey (closure reference who left.application.config)) =
      keyView who (runKey (closure reference who right.application.config))) :
    keyView who (runKey left.application.config) =
      keyView who (runKey right.application.config) := by
  classical
  let G := serviceGraph setup mode
  rw [keyView_runKey, keyView_runKey] at views
  have same := Option.some.inj views
  have leftPath := closure_path reference who left.application.config
  have rightPath := closure_path reference who right.application.config
  -- defaults transfer through the deviator's view of the closures
  have defaultsTransfer {first second : (serviceApplication setup mode duration leaks).Execution}
      (firstBoundary : PhaseBoundary scheduler players horizon rank first)
      (secondBoundary : PhaseBoundary scheduler players horizon rank second)
      (sameViews : G.normalizeObservation who (G.playerObserve who
          (closure reference who first.application.config)) =
        G.normalizeObservation who (G.playerObserve who
          (closure reference who second.application.config)))
      {owner : Player} (inactive : owner ∈ first.application.config.defaulted) :
      owner ∈ second.application.config.defaulted := by
    rw [mem_defaulted_iff_completionOf] at inactive ⊢
    obtain ⟨defaulting, found⟩ := inactive
    obtain ⟨record, recorded⟩ : ∃ record,
        completionOf first.application.config defaulting = some record := by
      cases recordedEq : completionOf first.application.config defaulting with
      | none => rw [recordedEq] at found; cases found
      | some record => exact ⟨record, rfl⟩
    have done : defaulting ∈ first.application.config.cut.completed :=
      (completionOf_isSome_iff _ defaulting).mp (by rw [recorded]; rfl)
    have early : defaulting.val < rank := by
      by_contra late
      push Not at late
      rw [(firstBoundary.later defaulting late done).1] at found
      cases found
    have secondDone := secondBoundary.earlier defaulting early
    obtain ⟨secondRecord, secondRecorded⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff _ defaulting).mpr secondDone)
    have firstClosure := Config.Step.path_completionOf_of_some
      (closure_path reference who first.application.config) defaulting record recorded
    have secondClosure := Config.Step.path_completionOf_of_some
      (closure_path reference who second.application.config) defaulting secondRecord
      secondRecorded
    have defaults := normalize_defaultEvent_congr who sameViews defaulting
      (by rw [firstClosure]; rfl)
    rw [firstClosure, secondClosure] at defaults
    refine ⟨defaulting, ?_⟩
    rw [secondRecorded, ← defaults, ← recorded]
    exact found
  have sets : left.application.config.cut.completed = right.application.config.cut.completed := by
    have oneWay {first second : (serviceApplication setup mode duration leaks).Execution}
        (firstBoundary : PhaseBoundary scheduler players horizon rank first)
        (secondBoundary : PhaseBoundary scheduler players horizon rank second)
        (sameViews : G.normalizeObservation who (G.playerObserve who
            (closure reference who first.application.config)) =
          G.normalizeObservation who (G.playerObserve who
            (closure reference who second.application.config))) :
        ∀ event : G.EventId, event ∈ first.application.config.cut.completed →
          event ∈ second.application.config.cut.completed := by
      intro event
      induction hval : event.val using Nat.strong_induction_on generalizing event with
      | _ value ih =>
      intro done
      by_cases early : event.val < rank
      · exact secondBoundary.earlier event early
      push Not at early
      obtain ⟨_, _, owner, owned, inactive⟩ := firstBoundary.later event early done
      by_contra pending
      have ready : second.application.config.cut.Ready event := ⟨pending, fun prior member =>
        ih prior.val (hval ▸ G.order.predecessor_lt member) prior rfl
          (first.application.config.cut.predecessor_closed done member)⟩
      apply secondBoundary.quiescent event
      unfold EventGraphRuntime.State.AutomaticReady
      rw [owned]
      exact ⟨ready, defaultsTransfer firstBoundary secondBoundary sameViews inactive⟩
    ext event
    exact ⟨oneWay leftBoundary rightBoundary same event,
      oneWay rightBoundary leftBoundary same.symm event⟩
  rw [keyView_runKey, keyView_runKey, normalizeObservation_playerObserve_restrict who _
    (Config.restrictionOf_of_completed rfl leftPath)
    (Config.restrictionOf_of_completed sets.symm rightPath) same]

/-- **The closure at a pending solitary event.** At a phase boundary whose
event is not a reveal and is pending, nothing settles, so the closure is the
configuration itself. -/
theorem closure_eq_of_pending (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode))
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy} {horizon : Nat}
    {event : (serviceGraph setup mode).EventId}
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (boundary : PhaseBoundary scheduler players horizon event.val execution)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication)
    (pending : event ∉ execution.application.config.cut.completed) :
    closure reference who execution.application.config = execution.application.config := by
  apply closure_of_none
  intro other settles
  obtain ⟨ready, kind, _⟩ := settles
  rcases kind with publication | ⟨owner, owned, inactive⟩
  · rcases Nat.lt_trichotomy other.val event.val with smaller | same | larger
    · exact ready.1 (boundary.earlier other smaller)
    · have equal : other = event := Fin.ext same
      subst equal
      exact notPublication publication
    · exact pending (ready.2 (relaxed.predecessor_of_not_publication notPublication larger))
  · apply boundary.quiescent other
    unfold EventGraphRuntime.State.AutomaticReady
    have ownedGraph : (serviceGraph setup mode).actor? other = some owner := owned
    rw [ownedGraph]
    exact ⟨ready, inactive⟩

/-- The closure key read from an order-free key. -/
def closureKeyOf (reference : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (key : RunKey (serviceGraph setup mode)) : RunKey (serviceGraph setup mode) :=
  open scoped Classical in
  if found : ∃ config : (serviceGraph setup mode).Config, runKey config = key then
    runKey (closure reference who found.choose)
  else key

/-- The closure key of a configuration is read from its key. -/
theorem closureKeyOf_runKey {reference : (serviceGraph setup mode).BehavioralProfile}
    (independent : ReadyIndependent reference) (who : Player)
    (config : (serviceGraph setup mode).Config) :
    closureKeyOf reference who (runKey config) = runKey (closure reference who config) := by
  have found : ∃ other : (serviceGraph setup mode).Config, runKey other = runKey config :=
    ⟨config, rfl⟩
  unfold closureKeyOf
  rw [dite_eq_left found]
  exact closure_runKey_congr independent.congr _ _ _ rfl found.choose_spec

/-- The target of a normalized deviation is read from the closure key. -/
theorem keyTarget_closure (base : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (policy : (serviceGraph setup mode).BehavioralPolicy who)
    (independent : LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (config : (serviceGraph setup mode).Config) :
    keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
        (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who config)) =
      keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
        (runKey config) := by
  rw [keyTarget_runKey independent, keyTarget_runKey independent,
    lastErasedLaw_closure_deviation base who policy independent]

/-- **A solitary phase through the closure, for pending events.** A solitary
phase whose joint law, averaged target and patched policy are known for the raw
key, from priors of phase boundaries with its event pending, has them for the
closure key too; and its built policy keeps the target where the event has
completed. -/
theorem pending_closure_joint (base : (serviceGraph setup mode).BehavioralProfile)
    (who : Player)
    (independent : ∀ policy, LastIndependent
      ((serviceGraph setup mode).lastDeviationProfile base who policy) who)
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (relaxed : RelaxedOrder (serviceGraph setup mode))
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {players : Player → (serviceApplication setup mode duration leaks).Policy} {horizon : Nat}
    (event : (serviceGraph setup mode).EventId)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication)
    (endpoint : ∀ execution, PhaseBoundary scheduler players horizon event.val execution →
      ∀ final ∈ ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
        (fun current => event ∈ current.application.config.cut.completed) horizon
        execution).support,
        PhaseBoundary scheduler players horizon (event.val + 1) final)
    (rawJoint : ∀ {Seed : Type} (prior : PMF Seed)
      (execution : Seed → (serviceApplication setup mode duration leaks).Execution),
      (∀ seed ∈ prior.support, PhaseBoundary scheduler players horizon event.val (execution seed) ∧
        event ∉ (execution seed).application.config.cut.completed) →
      ∀ noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _,
      (prior.map (fun seed => (runKey (execution seed).application.config,
          (bindingTraffic (serviceTimeouts setup mode duration)) leaks who (execution seed))) =
        (prior.map fun seed => runKey (execution seed).application.config).bind fun current =>
          (noise (keyView who current)).map fun extra => (current, extra)) →
      ∃ (build : (serviceGraph setup mode).BehavioralPolicy who →
          (serviceGraph setup mode).BehavioralPolicy who)
        (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _),
        (prior.bind fun seed =>
          ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).map fun final => (runKey final.application.config,
              (bindingTraffic (serviceTimeouts setup mode duration)) leaks who final)) =
          (prior.bind fun seed =>
            ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
              (fun current => event ∈ current.application.config.cut.completed) horizon
              (execution seed)).map fun final => runKey final.application.config).bind
            (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
        (∀ policy, (prior.bind fun seed =>
          ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).bind fun final =>
              keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
                (runKey final.application.config)) =
          prior.bind fun seed =>
            keyTarget ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) who
              (runKey (execution seed).application.config)) ∧
        ∀ policy (config : (serviceGraph setup mode).Config) other, other ≠ event →
          actionLaw ((serviceGraph setup mode).lastDeviationProfile base who (build policy))
              config other =
            actionLaw ((serviceGraph setup mode).lastDeviationProfile base who policy) config
              other) :
    ∀ {Seed : Type} (prior : PMF Seed)
      (execution : Seed → (serviceApplication setup mode duration leaks).Execution),
      (∀ seed ∈ prior.support, PhaseBoundary scheduler players horizon event.val (execution seed) ∧
        ¬ event ∈ (execution seed).application.config.cut.completed) →
      ∀ noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _,
      (prior.map (fun seed => (runKey (closure ((serviceGraph setup mode).normalizeProfile base)
          who (execution seed).application.config),
          (bindingTraffic (serviceTimeouts setup mode duration)) leaks who (execution seed))) =
        (prior.map fun seed => runKey (closure ((serviceGraph setup mode).normalizeProfile base)
          who (execution seed).application.config)).bind fun current =>
          (noise (keyView who current)).map fun extra => (current, extra)) →
      ∃ (build : (serviceGraph setup mode).BehavioralPolicy who →
          (serviceGraph setup mode).BehavioralPolicy who)
        (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _),
        (prior.bind fun seed =>
          ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).map fun final => (runKey (closure
              ((serviceGraph setup mode).normalizeProfile base) who final.application.config),
              (bindingTraffic (serviceTimeouts setup mode duration)) leaks who final)) =
          (prior.bind fun seed =>
            ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
              (fun current => event ∈ current.application.config.cut.completed) horizon
              (execution seed)).map fun final => runKey (closure
                ((serviceGraph setup mode).normalizeProfile base) who
                final.application.config)).bind
            (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
        (∀ policy, (prior.bind fun seed =>
          ((serviceApplication setup mode duration leaks).runUntilHorizon scheduler players
            (fun current => event ∈ current.application.config.cut.completed) horizon
            (execution seed)).bind fun final =>
              keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
                (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
                  final.application.config))) =
          prior.bind fun seed =>
            keyTarget ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) who
              (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
                (execution seed).application.config))) ∧
        ∀ policy (execution : (serviceApplication setup mode duration leaks).Execution),
          PhaseBoundary scheduler players horizon event.val execution →
          event ∈ execution.application.config.cut.completed →
          keyTarget ((serviceGraph setup mode).lastDeviationProfile base who (build policy)) who
              (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
                execution.application.config)) =
            keyTarget ((serviceGraph setup mode).lastDeviationProfile base who policy) who
              (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
                execution.application.config)) := by
  classical
  intro Seed prior execution goods noise factor
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode duration leaks
  let phase := fun seed => app.runUntilHorizon scheduler players
    (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed)
  let traffic := (bindingTraffic (serviceTimeouts setup mode duration)) leaks who
  have startEq (seed : Seed) (member : seed ∈ prior.support) :
      runKey (closure R who (execution seed).application.config) =
        runKey (execution seed).application.config := by
    rw [closure_eq_of_pending R who relaxed (goods seed member).1 notPublication
      (goods seed member).2]
  have rawFactor : prior.map (fun seed => (runKey (execution seed).application.config,
      traffic (execution seed))) =
      (prior.map fun seed => runKey (execution seed).application.config).bind fun current =>
        (noise (keyView who current)).map fun extra => (current, extra) := by
    have mapsEq : prior.map (fun seed => runKey (execution seed).application.config) =
        prior.map (fun seed => runKey (closure R who (execution seed).application.config)) :=
      map_congr_on_support _ fun seed member => (startEq seed member).symm
    rw [mapsEq, ← factor]
    apply map_congr_on_support _
    intro seed member
    exact Prod.ext (startEq seed member).symm rfl
  obtain ⟨build, rawNoise, rawEnd, rawAveraged, agree⟩ := rawJoint prior execution
    goods noise rawFactor
  -- the end factor moves to the closure key
  have endLaw := factored_of_finer (prior.bind phase)
    (fun final => runKey final.application.config)
    (fun final => runKey (closure R who final.application.config)) traffic (keyView who) rawNoise
    (by simpa only [PMF.map_bind] using rawEnd) (closureKeyOf R who)
    (fun final _ => (closureKeyOf_runKey referenceIndependent who _).symm)
    (fun left leftMember right rightMember views => by
      obtain ⟨leftSeed, leftSeedMember, leftReached⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ leftMember)
      obtain ⟨rightSeed, rightSeedMember, rightReached⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ rightMember)
      exact phaseBoundary_reflect R who
        (endpoint _ (goods leftSeed leftSeedMember).1 left leftReached)
        (endpoint _ (goods rightSeed rightSeedMember).1 right rightReached) views)
  obtain ⟨fineNoise, fineLaw⟩ := endLaw
  refine ⟨build, fineNoise, ?_, fun policy => ?_, fun policy config boundary done => ?_⟩
  · simpa only [PMF.map_bind] using fineLaw
  · refine Eq.trans ?_ ((rawAveraged policy).trans ?_)
    · apply bind_congr_on_support _
      intro seed _
      apply bind_congr_on_support _
      intro final _
      exact keyTarget_closure base who policy (independent policy) _
    · apply bind_congr_on_support _
      intro seed member
      rw [startEq seed member]
  · rw [keyTarget_runKey (independent _), keyTarget_runKey (independent _)]
    exact lastErasedLaw_patch_completed event (fun current other different =>
      agree policy current other different) _
      (Config.Step.path_completed_mono (closure_path R who _) done)

end Vegas

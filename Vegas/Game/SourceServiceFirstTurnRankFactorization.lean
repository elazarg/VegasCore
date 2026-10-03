/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceInitialTraffic
import Vegas.Game.SourceServiceFirstTurnSharedCheckpoint
import Vegas.Game.SourceServiceFirstTurnSampleFactorization
import Vegas.Game.SourceServiceFirstTurnBindingFactorization
import Vegas.Game.SourceServiceFirstTurnResolutionFactorization

/-! # Actual first-turn source prefixes and full traffic at every rank

The actual initialized scheduler execution advances through ordered completion
stops at the same horizon. Each source constructor propagates the source-view
traffic channel using one compiler slice shared by all supported seeds. The
parameter remains attached to the same initial draw throughout the execution.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- At every actual initialized completion rank the full focal traffic
depends on the carried source position only through its whole observation.
Both the prefix marginal and the channel are derived from the real runtime. -/
private theorem initialized_rank_factorization [Finite Player] {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (parameter : State L setup.context → Parameter) (focal : Player) :
    ∀ rank, rank ≤ (graph setup).order.eventCount →
      ∃ noise : Option (ProtocolView focal setup.program) → PMF _,
        (setup.initialLaw.bind fun initial =>
          ((application setup leaks).runUntilHorizon scheduler
            (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
            (sourceServiceRankCompleted rank) horizon
            (.initial (application setup leaks)
              (EventGraphRuntime.State.initial (setup.eventInputs initial)))).map fun execution =>
                ((parameter initial, sourceServicePrefix? setup rank execution.application.config),
                  (runtime setup).bindingTraffic leaks focal execution)) =
          (setup.initialLaw.bind fun initial =>
            ((application setup leaks).runUntilHorizon scheduler
              (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
                profile)
              (sourceServiceRankCompleted rank) horizon
              (.initial (application setup leaks)
                (EventGraphRuntime.State.initial (setup.eventInputs initial)))).map fun execution =>
                  (parameter initial, sourceServicePrefix? setup rank
                    execution.application.config)).bind fun carried =>
            (noise (carried.2.map (ProtocolState.observe focal setup.program))).map
              fun extra => (carried, extra) := by
  classical
  let _ := Fintype.ofFinite Player
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let start := fun initial : State L setup.context => ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  let native := fun rank initial => app.runUntilHorizon scheduler players
    (sourceServiceRankCompleted rank) horizon (start initial)
  let prior := fun rank => setup.initialLaw.bind fun initial =>
    (native rank initial).map fun execution => (initial, execution)
  let carried := fun rank (seed : State L setup.context × app.Execution) =>
    (parameter seed.1, sourceServicePrefix? setup rank seed.2.application.config)
  let traffic := fun seed : State L setup.context × app.Execution =>
    (runtime setup).bindingTraffic leaks focal seed.2
  have supported rank seed (reached : seed ∈ (prior rank).support) :
      seed.1 ∈ setup.initialLaw.support ∧ seed.2 ∈ (native rank seed.1).support := by
    rw [PMF.mem_support_bind_iff] at reached
    obtain ⟨initial, initialSupport, reached⟩ := reached
    rw [PMF.support_map] at reached
    obtain ⟨execution, reached, equal⟩ := reached
    cases equal
    exact ⟨initialSupport, reached⟩
  have desired : ∀ rank, rank ≤ (graph setup).order.eventCount →
      ∃ noise : Option (ProtocolView focal setup.program) → PMF _,
        (prior rank).map (fun seed => (carried rank seed, traffic seed)) =
          ((prior rank).map (carried rank)).bind fun pair =>
            (noise (pair.2.map (ProtocolState.observe focal setup.program))).map
              fun extra => (pair, extra) := by
    intro rank
    induction rank with
    | zero =>
        intro within
        have stopped initial : native 0 initial = PMF.pure (start initial) := by
          exact app.runUntil_of_stop scheduler players _ _ (start initial)
            (fun event below => by omega)
        have initialPrior : prior 0 = setup.initialLaw.map (fun initial =>
            (initial, start initial)) := by
          dsimp only [prior]
          simp only [stopped, PMF.pure_map]
          rfl
        obtain ⟨initialNoise, decoded, base⟩ :=
          sourceService_initial_parameter_traffic_factorization setup leaks focal parameter
        let noise := fun view : Option (ProtocolView focal setup.program) =>
          view.elim (PMF.pure (traffic (setup.initialLaw.support_nonempty.choose,
            start setup.initialLaw.support_nonempty.choose))) initialNoise
        refine ⟨noise, ?_⟩
        rw [initialPrior]
        have lifted := congrArg (PMF.map fun pair =>
          ((pair.1.1, some pair.1.2), pair.2)) base
        simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def, carried,
          traffic, start, app, decoded, Option.map_some, noise, Option.elim_some] using lifted
    | succ rank ih =>
        intro within
        have sourceWithin : rank + 1 ≤ eventCount setup.program := within
        obtain ⟨noise, factor⟩ := ih (by omega)
        obtain ⟨Γ, names, tail, tailProfile, refs, registry, revelations, embedding, refsBefore,
          lift, liftView, recover, counted, aligned, tailEffective, injective, viewed, recovered,
          commutes, transport, endpoints⟩ :=
          sourceServiceFirstTurn_shared_checkpoint (turns := turns) contract timely profile
            effective rank (by omega)
        have resources seed (reached : seed ∈ (prior rank).support) :=
          endpoints seed.1 (supported rank seed reached).1 seed.2 (supported rank seed reached).2
        let source := fun seed : State L setup.context × app.Execution =>
          if reached : seed ∈ (prior rank).support then (resources seed reached).2.2.choose
          else (resources (prior rank).support_nonempty.choose
            (prior rank).support_nonempty.choose_spec).2.2.choose
        have sourceFacts seed (reached : seed ∈ (prior rank).support) :
            (source seed).registry = registry ∧
            ((source seed).revelations : Revelations Γ) = @revelations ∧
            decodeState? refs seed.2.application.config.store = some (source seed).state ∧
            SourceCheckpoint setup (source seed) refs rank seed.2.application.config ∧
            sourceServicePrefix? setup rank seed.2.application.config =
              some (lift (ProtocolState.entry tail (source seed))) := by
          simpa only [source, dite_eq_left reached] using
            (resources seed reached).2.2.choose_spec
        let before := fun seed : State L setup.context × app.Execution =>
          (parameter seed.1, lift (ProtocolState.entry tail (source seed)))
        let typedNoise := fun view : ProtocolView focal setup.program => noise (some view)
        have typedFactor : (prior rank).map (fun seed => (before seed, traffic seed)) =
            ((prior rank).map before).bind fun pair =>
              (typedNoise (ProtocolState.observe focal setup.program pair.2)).map
                fun extra => (pair, extra) := by
          let embed := fun pair : (Parameter × ProtocolState setup.program) ×
              (MessageNetwork Player app.Payload × List (MessageId Player × Bool) ×
                List app.EnvironmentEntry × List app.PlayerEntry × PlayerView (graph setup) ×
                  PublicView (graph setup)) => ((pair.1.1, some pair.1.2), pair.2)
          apply pmf_map_injective (f := embed) (by
            intro left right equal
            obtain ⟨carriedEq, trafficEq⟩ := Prod.mk.inj equal
            obtain ⟨parameterEq, sourceEq⟩ := Prod.mk.inj carriedEq
            exact Prod.ext (Prod.ext parameterEq (Option.some.inj sourceEq)) trafficEq)
          have prefixed : (prior rank).map (fun seed =>
              ((parameter seed.1, some (before seed).2), traffic seed)) =
                (prior rank).map (fun seed => (carried rank seed, traffic seed)) := by
            apply map_congr_on_support _
            intro seed reached
            dsimp only [carried, before]
            rw [(sourceFacts seed reached).2.2.2.2]
          simp only [embed, PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def]
          rw [prefixed, factor, PMF.bind_map]
          apply bind_congr_on_support _
          intro seed reached
          dsimp only [Function.comp_def, carried, before, typedNoise]
          rw [(sourceFacts seed reached).2.2.2.2, Option.map_some]
        let event : (graph setup).EventId := ⟨rank, by omega⟩
        have composed : prior (rank + 1) = (prior rank).bind fun seed =>
            (app.runUntilHorizon scheduler players (sourceServiceRankCompleted (rank + 1))
              horizon seed.2).map fun final => (seed.1, final) := by
          dsimp only [prior]
          rw [PMF.bind_bind]
          apply bind_congr_on_support _
          intro initial initialSupport
          have kernel := app.runUntilHorizon_eq_runUntilHorizon_bind scheduler players
            (sourceServiceRankCompleted rank) (sourceServiceRankCompleted (rank + 1))
            (fun execution completed other below => completed other (by omega)) horizon
            (start initial)
          simpa only [native, PMF.map_bind, PMF.bind_map, Function.comp_def] using
            congrArg (PMF.map fun final => (initial, final)) kernel
        have actualPhase : (prior (rank + 1)).map (fun seed =>
            (carried (rank + 1) seed, traffic seed)) =
              (prior rank).bind fun seed =>
                (app.runUntilHorizon scheduler players
                  (fun final => event ∈ final.application.config.cut.completed) horizon seed.2).map
                    fun final => ((parameter seed.1,
                      sourceServicePrefix? setup (rank + 1) final.application.config),
                      (runtime setup).bindingTraffic leaks focal final) := by
          rw [composed, PMF.map_bind]
          apply bind_congr_on_support _
          intro seed reached
          rw [PMF.map_comp]
          have boundary : CompletionBoundary setup leaks scheduler players event.val seed.2 :=
            (resources seed reached).2.1
          rw [sourceServiceRank_runUntil_eq_event event seed.2 boundary]
          rfl
        have phase : ∃ nextNoise : Option (ProtocolView focal setup.program) → PMF _,
            (prior (rank + 1)).map (fun seed => (carried (rank + 1) seed, traffic seed)) =
              (((prior rank).map before).bind fun pair =>
                (ProtocolState.behavioralStateStep setup.program profile pair.2).map
                  fun after => (pair.1, some after)).bind fun pair =>
                    (nextNoise (pair.2.map (ProtocolState.observe focal setup.program))).map
                      fun extra => (pair, extra) := by
          cases tail with
          | ret payoffs =>
              simp only [eventCount] at counted
              omega
          | sample name fresh distribution next =>
              obtain ⟨nextNoise, decoded, law⟩ :=
                sourceServiceFirstTurn_sample_prefix_factorization setup leaks contract profile
                  name fresh distribution next tailProfile refs registry revelations embedding
                  refsBefore rank aligned lift injective liftView viewed recover recovered
                  commutes transport (prior rank) (fun seed => parameter seed.1) source Prod.snd
                  (fun seed reached => (sourceFacts seed reached).1)
                  (fun seed reached => (sourceFacts seed reached).2.1)
                  (fun seed reached => (resources seed reached).2.1)
                  (fun seed reached => (resources seed reached).1)
                  (fun seed reached => (sourceFacts seed reached).2.2.2.1)
                  focal typedNoise typedFactor
              have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
                apply Fin.ext
                simpa only [event, Nat.add_zero] using
                  aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
              rw [headEq] at law
              exact ⟨nextNoise, actualPhase.trans law⟩
          | commit name owner fresh guard next =>
              obtain ⟨nextNoise, decoded, law⟩ :=
                sourceServiceFirstTurn_binding_prefix_factorization setup leaks contract timely
                  profile name owner fresh guard next tailProfile refs registry revelations
                  embedding refsBefore rank aligned lift injective liftView viewed recover
                  recovered commutes transport (prior rank) (fun seed => parameter seed.1) source
                  Prod.snd (fun seed reached => (sourceFacts seed reached).1)
                  (fun seed reached => (sourceFacts seed reached).2.1)
                  (fun seed reached => (resources seed reached).2.1)
                  (fun seed reached => (resources seed reached).1)
                  (fun seed reached => (sourceFacts seed reached).2.2.2.1)
                  focal typedNoise typedFactor
              have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
                apply Fin.ext
                simpa only [event, Nat.add_zero] using
                  aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
              rw [headEq] at law
              exact ⟨nextNoise, actualPhase.trans law⟩
          | reveal published owner name fresh binding unresolved next =>
              obtain ⟨nextNoise, decoded, law⟩ :=
                sourceServiceFirstTurn_resolution_prefix_factorization setup leaks contract timely
                  profile published name owner fresh binding unresolved next tailProfile refs
                  registry revelations embedding refsBefore rank aligned tailEffective lift
                  injective liftView viewed recover recovered commutes transport (prior rank)
                  (fun seed => parameter seed.1) source Prod.snd
                  (fun seed reached => (sourceFacts seed reached).1)
                  (fun seed reached => (sourceFacts seed reached).2.1)
                  (fun seed reached => (resources seed reached).2.1)
                  (fun seed reached => (resources seed reached).1)
                  (fun seed reached => (sourceFacts seed reached).2.2.2.1)
                  focal typedNoise typedFactor
              have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
                apply Fin.ext
                simpa only [event, Nat.add_zero] using
                  aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
              rw [headEq] at law
              exact ⟨nextNoise, actualPhase.trans law⟩
        obtain ⟨nextNoise, law⟩ := phase
        refine ⟨nextNoise, ?_⟩
        have projected := congrArg (PMF.map Prod.fst) law
        have collapse (pair : Parameter × setup.ProtocolState) :
            (nextNoise (pair.2.map (ProtocolState.observe focal setup.program))).map
                (fun _ => pair) = PMF.pure pair := PMF.map_const _ _
        simp only [PMF.map_comp, PMF.map_bind, Function.comp_def, collapse,
          PMF.bind_pure] at projected
        rw [projected]
        exact law
  intro rank within
  obtain ⟨noise, law⟩ := desired rank within
  refine ⟨noise, ?_⟩
  simpa only [prior, native, app, players, start, carried, traffic, PMF.map_bind,
    PMF.map_comp, Function.comp_def] using law

/-- The initialized pure-first-turn rank likelihood is the true source
behavioral iteration with the same initial parameter and full focal traffic.
The channel reads only the optional whole effective source observation. -/
theorem sourceServiceFirstTurn_rank_traffic_law [Fintype Player] {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (parameter : State L setup.context → Parameter) (focal : Player)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) :
    ∃ noise : Option (ProtocolView focal setup.program) → PMF _,
      (setup.initialLaw.bind fun initial =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          (sourceServiceRankCompleted rank) horizon
          (.initial (application setup leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).map fun execution =>
              ((parameter initial, sourceServicePrefix? setup rank execution.application.config),
                (runtime setup).bindingTraffic leaks focal execution)) =
        (setup.initialLaw.bind fun initial =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
            (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
              fun before => (parameter initial, some before)).bind fun carried =>
          (noise (carried.2.map (ProtocolState.observe focal setup.program))).map
            fun extra => (carried, extra) := by
  obtain ⟨noise, factor⟩ := initialized_rank_factorization (turns := turns) contract timely profile
    effective parameter focal rank within
  refine ⟨noise, ?_⟩
  rw [sourceServiceFirstTurn_rank_joint_law (turns := turns) contract timely profile effective
    parameter rank
    within] at factor
  exact factor

end Vegas

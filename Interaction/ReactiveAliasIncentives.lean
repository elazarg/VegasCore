/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAliasStrategy
import Interaction.ReactiveAliasLaw
import Interaction.ReactiveAliasImplementation
import Interaction.ReactiveAliasAdmissibility
import Interaction.ReactiveResponseEvaluation

/-! # Continuation incentives under private response normalization

Canonical policies read normalized own recall. An arbitrary raw deviation is
realized behaviorally by retaining only its private response names internally.
The continuation comparison uses the assessment's projected beliefs and the
same remaining protocol horizon.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization) (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)
  (closed : ∀ who past view response, response ∈ raw.actions who past view →
    normal.action who past view response ∈ raw.actions who past view)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem decode_canonicalPolicy (who : Principal)
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    app.decodePolicy (raw.embedPolicy initial horizon scheduler who
        (normal.canonicalPolicy raw stable closed initial horizon scheduler who source)) past view =
      app.decodePolicy ((normal.menu raw).embedPolicy initial horizon scheduler who source)
        (normal.recall who past) view := by
  simp only [decodePolicy, ResponseMenu.embedPolicy, canonicalPolicy, FinDist.map_comp]
  rfl

theorem decode_canonicalProfile
    (source : ∀ who,
      ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who) :
    raw.decodeProfile initial horizon scheduler (fun who =>
        normal.canonicalPolicy raw stable closed initial horizon scheduler who (source who)) =
      (fun who past view => (normal.menu raw).decodeProfile initial horizon scheduler source who
        (normal.recall who past) view) := by
  funext who past view
  exact normal.decode_canonicalPolicy raw stable closed initial horizon scheduler who
    (source who) past view

theorem decodeProfile_normal
    (source : ∀ who,
      ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (response : app.Action)
    (supported : response ∈
      ((normal.menu raw).decodeProfile initial horizon scheduler source who past view).support) :
    normal.action who past view response = response :=
  normal.menu_normal raw who past view response
    ((normal.menu raw).decode_embedPolicy_covered initial horizon scheduler who (source who)
      past view response supported)

theorem aliasDeviation_finish
    (source : ∀ who,
      ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal)
    (alternative : (raw.information initial horizon scheduler).BehavioralPolicy who)
    (execution : app.Execution) (valid : execution.InputRecall app)
    (remaining : Nat) (actor : Option Principal) :
    (app.finish initial horizon scheduler
      (raw.decodeProfile initial horizon scheduler (GameTheory.Profile.update
        (sig := (raw.information initial horizon scheduler).behavioralSignature)
        (fun player => normal.canonicalPolicy raw stable closed initial horizon scheduler
          player (source player)) who alternative)) (some ⟨remaining, actor, execution⟩)).map
            normal.state =
      app.finish initial horizon scheduler
        ((normal.menu raw).decodeProfile initial horizon scheduler (GameTheory.Profile.update
          (sig := ((normal.menu raw).information initial horizon scheduler).behavioralSignature)
            source who (normal.aliasDeviation raw stable initial horizon scheduler who
              (execution.recall who) alternative)))
          (normal.state (some ⟨remaining, actor, execution⟩)) := by
  rw [raw.decodeProfile_update, (normal.menu raw).decodeProfile_update,
    normal.decode_canonicalProfile, normal.decode_aliasDeviation]
  have law := normal.aliasImplementation_behavioral_continuation who
    (app.decodePolicy (raw.embedPolicy initial horizon scheduler who alternative))
    ((normal.menu raw).decodeProfile initial horizon scheduler source)
    (normal.decodeProfile_normal raw initial horizon scheduler source)
    scheduler remaining actor execution valid
  change _ = ((app.resume _ actor (normal.execution execution)).bind _).map app.finished
  rw [law, FinDist.map_comp]
  simp only [finish, FinDist.map_comp]
  rfl

variable [Fintype Principal]

theorem aliasDeviation_historyLaw
    (source : ∀ who,
      ((normal.menu raw).information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal)
    (alternative : (raw.information initial horizon scheduler).BehavioralPolicy who)
    (current : (raw.protocol initial horizon scheduler).History)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : (raw.information initial horizon scheduler).infoOf who current.trace =
      some (past, view)) :
    (((raw.information initial horizon scheduler).runBehavioralFrom
      (GameTheory.Profile.update
        (sig := (raw.information initial horizon scheduler).behavioralSignature)
        (fun player => normal.canonicalPolicy raw stable closed initial horizon scheduler
          player (source player)) who alternative) (2 * horizon + 1) current).map History.state).map
            normal.state =
      (((normal.menu raw).information initial horizon scheduler).runBehavioralFrom
        (GameTheory.Profile.update
          (sig := ((normal.menu raw).information initial horizon scheduler).behavioralSignature)
            source who (normal.aliasDeviation raw stable initial horizon scheduler who
              past alternative)) (2 * horizon + 1)
          (normal.history raw stable initial horizon scheduler current)).map History.state := by
  have sourceBound := app.trace_bound initial horizon scheduler
    ((normal.menu raw).toRawTrace initial horizon scheduler
      (normal.trace raw stable initial horizon scheduler current.trace))
  have targetBound := app.trace_bound initial horizon scheduler
    (raw.toRawTrace initial horizon scheduler current.trace)
  rw [raw.run_eq_finish initial horizon scheduler _ _ current (by omega),
    (normal.menu raw).run_eq_finish initial horizon scheduler _ _ _ (by
      change app.rank horizon (normal.state current.state) ≤ _
      omega)]
  change (raw.signals initial horizon scheduler).infoOf who current.trace =
    some (past, view) at observed
  rw [raw.info] at observed
  have valid := app.history_inputRecall initial horizon scheduler
    (raw.toRawTrace initial horizon scheduler current.trace)
  cases stateEq : current.state with
  | none => simp only [stateEq, observe] at observed; cases observed
  | some control =>
      rw [stateEq] at observed
      dsimp only [observe] at observed
      split at observed
      · have remembered := congrArg Prod.fst (Option.some.inj observed)
        dsimp only at remembered
        change (app.finish initial horizon scheduler _ (some control)).map normal.state =
          app.finish initial horizon scheduler _ (normal.state current.state)
        rw [stateEq, ← remembered]
        exact normal.aliasDeviation_finish raw stable closed initial horizon scheduler source who
          alternative control.execution (by simpa only [stateEq, inputRecall] using valid)
            control.remaining control.actor
      · cases observed

theorem canonical_context_value
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (target : (raw.information initial horizon scheduler).BehavioralAssessment)
    (strategy : target.strategy = (fun player => normal.canonicalPolicy raw stable closed
      initial horizon scheduler player (source.strategy player)))
    (who : Principal) (original : (raw.information initial horizon scheduler).InformationSite who)
    (beliefs : (target.belief who original).map
        (normal.informationHistory raw stable initial horizon scheduler who original.1) =
      source.belief who (normal.site raw stable initial horizon scheduler who original))
    (payoff : app.ProtocolState → ℝ) :
    (target.continuationContext original (fun history => payoff (normal.state history.state))
      (2 * horizon + 1)).value (target.strategy who) =
      (source.continuationContext (normal.site raw stable initial horizon scheduler who original)
        (fun history => payoff history.state) (2 * horizon + 1)).value (source.strategy who) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  simp only [GameTheory.Profile.update_eq_self, FinDist.expect_bind]
  rw [strategy]
  calc
    _ = (target.belief who original).expect (fun history =>
        (((normal.menu raw).information initial horizon scheduler).runBehavioralFrom
          source.strategy (2 * horizon + 1)
            (normal.history raw stable initial horizon scheduler history.1)).expect
          (fun final => payoff final.state)) := by
      apply FinDist.expect_congr
      intro history _
      have law := normal.runBehavioral_projection raw stable initial horizon scheduler
        (fun player => normal.canonicalPolicy raw stable closed initial horizon scheduler
          player (source.strategy player)) source.strategy
        (fun player observed => normal.canonicalPolicy_project raw stable closed initial horizon
          scheduler player (source.strategy player) observed) (2 * horizon + 1) history.1
      rw [← law, FinDist.expect_map]
      rfl
    _ = _ := by
      rw [← beliefs, FinDist.expect_map]
      rfl

theorem aliasDeviation_context_value
    (source : ((normal.menu raw).information initial horizon scheduler).BehavioralAssessment)
    (target : (raw.information initial horizon scheduler).BehavioralAssessment)
    (strategy : target.strategy = (fun player => normal.canonicalPolicy raw stable closed
      initial horizon scheduler player (source.strategy player)))
    (who : Principal) (original : (raw.information initial horizon scheduler).InformationSite who)
    (beliefs : (target.belief who original).map
        (normal.informationHistory raw stable initial horizon scheduler who original.1) =
      source.belief who (normal.site raw stable initial horizon scheduler who original))
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : original.1 = some (past, view))
    (payoff : app.ProtocolState → ℝ)
    (alternative : (raw.information initial horizon scheduler).BehavioralPolicy who) :
    (target.continuationContext original (fun history => payoff (normal.state history.state))
      (2 * horizon + 1)).value alternative =
      (source.continuationContext (normal.site raw stable initial horizon scheduler who original)
        (fun history => payoff history.state) (2 * horizon + 1)).value
          (normal.aliasDeviation raw stable initial horizon scheduler who past alternative) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    InformationModel.BehavioralAssessment.continuationContext_value]
  simp only [FinDist.expect_bind]
  rw [strategy]
  calc
    _ = (target.belief who original).expect (fun history =>
        (((normal.menu raw).information initial horizon scheduler).runBehavioralFrom
          (GameTheory.Profile.update
            (sig := ((normal.menu raw).information initial horizon scheduler).behavioralSignature)
              source.strategy who
                (normal.aliasDeviation raw stable initial horizon scheduler who past alternative))
          (2 * horizon + 1) (normal.history raw stable initial horizon scheduler history.1)).expect
            (fun final => payoff final.state)) := by
      apply FinDist.expect_congr
      intro history _
      have law := normal.aliasDeviation_historyLaw raw stable closed initial horizon scheduler
        source.strategy who alternative history.1 past view (history.2.trans observed)
      have value := congrArg (fun law => law.expect payoff) law
      simpa only [FinDist.expect_map] using value
    _ = _ := by
      rw [← beliefs, FinDist.expect_map]
      rfl

end Interaction.ReactiveApplication.SubmissionNormalization

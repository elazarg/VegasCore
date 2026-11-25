module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CanonicalStep

@[expose] public section

/-! # Behavioral policies from observation-conditional traffic

At each canonical prefix, native traffic may convey information already present
in the focal player's graph observation and may supply additional randomness.
If its conditional law depends only on that observation, a traffic-dependent
choice can be mixed into a behavioral action at the corresponding event.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A single canonical graph step from a numeric prefix runs its next event. -/
theorem runPlan_one_at_prefix {g : Vegas.EventGraph Player L} (reference : g.BehavioralProfile)
    (config : g.Config) (event : g.EventId) (ordered : config.cut.IsPrefix event.val) :
    g.runPlan (g.policyPlan reference g.canonicalScheduler) 1 config =
      eventStep reference config event (ordered.ready event.isLt) := by
  have ready := ordered.ready event.isLt
  rw [runPlan_canonical_succ reference 0 config ready.not_terminal event ready
    (fun other enabled => Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt fun earlier =>
      enabled.1 ((ordered.2 other).mpr earlier)))]
  simp only [runPlan, PMF.bind_pure]

/-- Mix the focal player's action against the traffic distribution at the
observed event. -/
def trafficPolicy {Traffic : Type*} (focal : Player)
    (traffic : graph.EventId → graph.PlayerObservation focal → PMF Traffic)
    (respond : Traffic → graph.BehavioralPolicy focal) : graph.BehavioralPolicy focal :=
  fun event actor observation active =>
    (traffic event observation).bind fun extra => respond extra event actor observation active

/-- Mixing traffic into a graph step changes only the active focal player's
action. Ownerless, defaulted and foreign events keep their usual kernels. -/
theorem bind_eventStep_eq_trafficPolicy {Traffic : Type*} (reference : graph.BehavioralProfile)
    (focal : Player) (traffic : graph.EventId → graph.PlayerObservation focal → PMF Traffic)
    (respond : Traffic → graph.BehavioralPolicy focal)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event) :
    (traffic event (graph.playerObserve focal config)).bind (fun extra =>
      eventStep (Function.update reference focal (respond extra)) config event ready) =
    eventStep (Function.update reference focal (trafficPolicy focal traffic respond))
      config event ready := by
  unfold eventStep
  cases actor : (graph.nodes event).actor with
  | none => simp [actionLaw_of_ownerless _ _ actor, PMF.bind_const]
  | some owner =>
      simp only [actionLaw_of_actor _ _ actor]
      by_cases active : owner ∈ config.defaulted
      · simp only [dite_eq_left active, PMF.bind_const]
      · simp only [dite_eq_right active]
        by_cases same : owner = focal
        · subst owner
          simp only [Function.update_self, trafficPolicy, PMF.bind_bind]
        · simp only [Function.update_of_ne same, PMF.bind_const]

/-- Compile a sequence of native prefix laws into a unilateral graph policy.
The phase premise gives only the one-event configuration marginal at each
prefix, and the traffic factorization uses the focal player's actual graph
observation. The same policy realizes every prefix marginal. -/
theorem trafficPolicy_prefixLaw {Traffic : Type*} (reference : graph.BehavioralProfile)
    (focal : Player) (inputs : PMF graph.Inputs)
    (traffic : graph.EventId → graph.PlayerObservation focal → PMF Traffic)
    (respond : Traffic → graph.BehavioralPolicy focal)
    (boundary : (rank : Nat) → rank ≤ graph.order.eventCount →
      PMF ({config : graph.Config // config.cut.IsPrefix rank} × Traffic))
    (initial : (boundary 0 (Nat.zero_le _)).map (fun pair => pair.1.val) =
      inputs.map Config.initial)
    (factor : ∀ (event : graph.EventId),
      boundary event.val event.isLt.le =
        ((boundary event.val event.isLt.le).map Prod.fst).bind fun config =>
          (traffic event (graph.playerObserve focal config.val)).map fun extra => (config, extra))
    (phase : ∀ (event : graph.EventId),
      (boundary (event.val + 1) event.isLt).map (fun pair => pair.1.val) =
        (boundary event.val event.isLt.le).bind fun pair =>
          eventStep (Function.update reference focal (respond pair.2)) pair.1.val event
            (pair.1.property.ready event.isLt)) :
    ∀ rank (bounded : rank ≤ graph.order.eventCount),
      (boundary rank bounded).map (fun pair => pair.1.val) =
        inputs.bind fun seed =>
          graph.runPlan (graph.policyPlan
            (Function.update reference focal (trafficPolicy focal traffic respond))
            graph.canonicalScheduler) rank (Config.initial seed) := by
  let profile := Function.update reference focal (trafficPolicy focal traffic respond)
  intro rank
  induction rank with
  | zero =>
      intro _
      exact initial
  | succ rank ih =>
      intro bounded
      have rankBounded : rank ≤ graph.order.eventCount := by omega
      let event : graph.EventId := ⟨rank, by omega⟩
      have step (config : {config : graph.Config // config.cut.IsPrefix rank}) :
          graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) 1 config.val =
            eventStep profile config.val event (config.property.ready event.isLt) :=
        runPlan_one_at_prefix profile config.val event config.property
      calc
        _ = (boundary rank rankBounded).bind (fun pair =>
              eventStep (Function.update reference focal (respond pair.2)) pair.1.val event
                (pair.1.property.ready event.isLt)) := phase event
        _ = ((boundary rank rankBounded).map Prod.fst).bind (fun config =>
              graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) 1 config.val) := by
          conv_lhs => rw [show boundary rank rankBounded = _ from factor event]
          rw [PMF.bind_bind]
          apply bind_congr_on_support _
          intro config _
          rw [PMF.bind_map, step]
          exact bind_eventStep_eq_trafficPolicy reference focal traffic respond config.val event
            (config.property.ready event.isLt)
        _ = ((boundary rank rankBounded).map (fun pair => pair.1.val)).bind
              (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) 1) := by
          rw [show (boundary rank rankBounded).map (fun pair => pair.1.val) =
            ((boundary rank rankBounded).map Prod.fst).map Subtype.val by rw [PMF.map_comp]; rfl]
          simp only [PMF.bind_map, Function.comp_def]
        _ = _ := by
          rw [ih (by omega), PMF.bind_bind]
          apply bind_congr_on_support _
          intro seed _
          exact (graph.runPlan_add (graph.policyPlan profile graph.canonicalScheduler)
            rank 1 (Config.initial seed)).symm

end Vegas.EventGraph

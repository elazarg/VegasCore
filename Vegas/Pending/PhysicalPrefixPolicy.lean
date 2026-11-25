module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PhysicalPrefix
public import Vegas.Pending.OwnedCompletionConfig

@[expose] public section

/-! # Assembling a unilateral policy from physical completion boundaries -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {timeouts : EventTimeouts graph.sequentialize}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)}

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

/-- At an actual physical prefix, the current conditional traffic law yields
one graph decision and a conditional traffic law at the next primary graph
configuration. Other players keep the reference profile. -/
def PhysicalPrefixPolicyStep (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF (G).Inputs) (horizon : Nat) (reference : (G).BehavioralProfile) (focal : Player)
    (event : (G).EventId) : Prop :=
  let boundary := physicalPrefix timeouts leaks scheduler players inputs horizon
  let config := fun rank (execution : (app).Execution) =>
    Config.rankPrefix rank execution.application.config
  let traffic := bindingTraffic timeouts leaks focal
  let observe := (G).playerObserve focal
  ∀ noise : (G).PlayerObservation focal → PMF (BindingTraffic timeouts leaks),
    (boundary event.val).map (fun before => (config event.val before, traffic before)) =
      ((boundary event.val).map (config event.val)).bind (fun before =>
        (noise (observe before)).map fun extra => (before, extra)) →
    ∃ policy : (G).BehavioralPolicy focal,
    ∃ nextNoise : (G).PlayerObservation focal → PMF (BindingTraffic timeouts leaks),
      (boundary (event.val + 1)).map (fun after => (config (event.val + 1) after, traffic after)) =
        (((boundary event.val).map (config event.val)).bind ((G).runPlan
          ((G).policyPlan (Function.update reference focal policy) (G).canonicalScheduler) 1)).bind
            fun primary => (nextNoise (observe primary)).map fun extra => (primary, extra)

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

private theorem actionLaw_diagonal {g : Vegas.EventGraph Player L}
    (reference : g.BehavioralProfile) (focal : Player)
    (sites : g.EventId → g.BehavioralPolicy focal) (event : g.EventId) (config : g.Config) :
    actionLaw (Function.update reference focal (sites event)) config event =
      actionLaw (Function.update reference focal (fun e => sites e e)) config event := by
  cases actor : g.actor? event with
  | none => rw [actionLaw_of_ownerless _ _ actor, actionLaw_of_ownerless _ _ actor]
  | some owner =>
    rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
    by_cases inactive : owner ∈ config.defaulted
    · simp only [dite_eq_left inactive]
    · simp only [dite_eq_right inactive]
      by_cases same : owner = focal
      · subst owner
        simp only [Function.update_self]
      · simp only [Function.update_of_ne same]

/-- Local physical traffic laws give one unilateral policy that realizes every
actual rank-prefix distribution and the complete terminal configuration law. -/
theorem physicalPrefix_policy_of_steps
    (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF (G).Inputs) (horizon : Nat) (reference : (G).BehavioralProfile) (focal : Player)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (steps : ∀ event, PhysicalPrefixPolicyStep scheduler players inputs horizon reference focal
      event) :
    let boundary := physicalPrefix timeouts leaks scheduler players inputs horizon
    ∃ policy : (G).BehavioralPolicy focal,
      (∀ rank, rank ≤ (G).order.eventCount →
        (boundary rank).map (fun execution => Config.rankPrefix rank execution.application.config) =
          inputs.bind fun seed => (G).runPlan
            ((G).policyPlan (Function.update reference focal policy) (G).canonicalScheduler)
            rank (Config.initial seed)) ∧
      ((app).roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
        inputs.bind ((G).runPolicies (G).canonicalScheduler
          (Function.update reference focal policy))
    := by
  classical
  intro boundary
  let config := fun rank (execution : (app).Execution) =>
    Config.rankPrefix rank execution.application.config
  let traffic := bindingTraffic timeouts leaks focal
  let observe := (G).playerObserve focal
  let marginal := fun rank => (boundary rank).map (config rank)
  let joint := fun rank => (boundary rank).map fun exec => (config rank exec, traffic exec)
  let WithNoise := fun rank
      (noise : (G).PlayerObservation focal → PMF (BindingTraffic timeouts leaks)) =>
      joint rank = (marginal rank).bind fun before =>
      (noise (observe before)).map fun extra => (before, extra)
  have atZero (seed : (G).Inputs) :
      Config.rankPrefix 0 (Config.initial (graph := G) seed) = Config.initial seed :=
    Config.rankPrefix_of_path (EventOrder.Cut.empty_isPrefix _) .refl
  have init : marginal 0 = inputs.map Config.initial := by
    simp only [marginal, boundary, physicalPrefix, PMF.map_comp, Function.comp_def, config]
    apply congrArg (fun f => inputs.map f)
    funext seed
    exact atZero seed
  have initialNoise : ∃ noise, WithNoise 0 noise := by
    obtain ⟨noise, factor⟩ := initial_bindingTraffic_factorization timeouts leaks focal inputs
    refine ⟨noise, ?_⟩
    change joint 0 = (marginal 0).bind _
    rw [init]
    change ((inputs.map _).map _) = _
    rw [PMF.map_comp]
    convert factor using 1
    apply congrArg (fun f => inputs.map f)
    funext seed
    exact Prod.ext (atZero seed) rfl
  have fst (rank : Nat) : (joint rank).map Prod.fst = marginal rank := by
    simp only [joint, marginal, PMF.map_comp, Function.comp_def]
  have project {rank : Nat} {ideal : PMF (G).Config}
      {noise : (G).PlayerObservation focal → PMF (BindingTraffic timeouts leaks)}
      (factor : joint rank = ideal.bind fun next =>
        (noise (observe next)).map fun extra => (next, extra)) :
      marginal rank = ideal := by
    rw [← fst, factor, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, pmf_map_fun_const, PMF.bind_pure]
  have factorAt : ∀ rank, rank ≤ (G).order.eventCount → ∃ noise, WithNoise rank noise := by
    intro rank
    induction rank with
    | zero => exact fun _ => initialNoise
    | succ rank ih =>
      intro bounded
      let event : (G).EventId := ⟨rank, bounded⟩
      obtain ⟨noise, previous⟩ := ih (by omega)
      obtain ⟨site, next, moved⟩ := steps event noise previous
      refine ⟨next, ?_⟩
      change joint (rank + 1) = (marginal (rank + 1)).bind _
      rw [project moved]
      exact moved
  have phase (event : (G).EventId) : ∃ site : (G).BehavioralPolicy focal,
      marginal (event.val + 1) = (marginal event.val).bind ((G).runPlan
        ((G).policyPlan (Function.update reference focal site) (G).canonicalScheduler) 1) := by
    obtain ⟨noise, factor⟩ := factorAt event.val event.isLt.le
    obtain ⟨site, _, moved⟩ := steps event noise factor
    exact ⟨site, project moved⟩
  choose sites laws using phase
  let policy : (G).BehavioralPolicy focal := fun event => sites event event
  let updated := Function.update reference focal policy
  let plan := (G).policyPlan updated (G).canonicalScheduler
  have allRanks : ∀ rank, rank ≤ (G).order.eventCount →
      marginal rank = inputs.bind fun seed => (G).runPlan plan rank (Config.initial seed) := by
    intro rank
    induction rank with
    | zero =>
      intro _
      rw [init, ← PMF.bind_pure_comp]
      rfl
    | succ rank ih =>
      intro bounded
      let event : (G).EventId := ⟨rank, bounded⟩
      have same : marginal (rank + 1) = (marginal rank).bind ((G).runPlan plan 1) := by
        refine (laws event).trans (bind_congr_on_support _ ?_)
        intro primary member
        obtain ⟨execution, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        obtain ⟨_, _, _, _, ordered, _⟩ := physicalPrefix_supported timeouts leaks scheduler
          players inputs horizon completes rank (Nat.le_of_lt event.isLt) execution supported
        change (G).runPlan _ 1 (config rank execution) = (G).runPlan _ 1 (config rank execution)
        rw [runPlan_one_at_prefix _ _ event ordered, runPlan_one_at_prefix _ _ event ordered]
        unfold eventStep
        exact congrArg (fun law => PMF.bind law _) (actionLaw_diagonal reference focal sites
          event (config rank execution))
      rw [same, ih (by omega), PMF.bind_bind]
      apply bind_congr_on_support _
      intro seed _
      exact ((G).runPlan_add plan rank 1 _).symm
  refine ⟨policy, allRanks, ?_⟩
  rw [roundsFrom_config_eq_physicalPrefix timeouts leaks scheduler players inputs horizon completes]
  refine Eq.trans ?_ (allRanks (G).order.eventCount le_rfl)
  apply map_congr_on_support _
  intro final member
  obtain ⟨actual, lower, atBoundary, _⟩ := physicalPrefix_supported timeouts leaks scheduler
    players inputs horizon completes (G).order.eventCount le_rfl final member
  have full := le_antisymm atBoundary.ordered.1 lower
  exact (Config.rankPrefix_of_path (full ▸ atBoundary.ordered) .refl).symm

end Vegas.EventGraphRuntime

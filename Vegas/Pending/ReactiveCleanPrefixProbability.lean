/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRiskPersistence
import Interaction.ReactiveMenuPolicy
import GameTheory.Protocol.HistoryPathMass

/-! # Exact probabilities of clean prefixes

The canonical and risk menus give the same probability to each clean realized
raw history when representing the same physical policy family. Their local
menus coincide before every response on such a history. A late opportunity at
the endpoint does not matter because that endpoint's response has not been
taken. The result concerns the two actual finite-menu runners; it does not
claim either representation executes an uncovered physical response law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bound : graph.EventId → Nat)

/-- Every owner's persistent flag is clear in the current actual state.
This omits current opportunities, which need not have entered private recall. -/
def AllPersistentServiceRiskClear
    (state : (runtime.reactiveApplication leaks).ProtocolState) : Prop :=
  ∀ control, state = some control → ∀ who,
    runtime.persistentServiceRisk leaks bound who (control.execution.recall who)
      (control.execution.observe (runtime.reactiveApplication leaks) who) = false

variable (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)

omit [Fintype Player] in
/-- A clear realized successor makes every predecessor persistent flag clear.
Any actor whose response was traversed also had its full input risk clear. -/
theorem allPersistentServiceRiskClear_before_transition
    (before after : (runtime.reactiveApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (realized : after ∈ ((runtime.reactiveApplication leaks).transition initial horizon scheduler
      before joint).support)
    (clear : runtime.AllPersistentServiceRiskClear leaks bound after) :
    runtime.AllPersistentServiceRiskClear leaks bound before ∧
      ∀ control, before = some control → ∀ who, control.actor = some who →
        runtime.serviceRisk leaks bound who (control.execution.recall who)
          (control.execution.observe (runtime.reactiveApplication leaks) who) = false := by
  cases before with
  | none =>
      constructor
      · intro _ impossible
        cases impossible
      · intro _ impossible
        cases impossible
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some owner =>
          cases (PMF.mem_support_pure_iff _ _).mp realized
          have afterClear := clear _ rfl
          refine ⟨?_, ?_⟩
          · intro current same who
            cases Option.some.inj same
            exact runtime.persistentServiceRisk_clear_before_respond leaks bound execution owner
              who ((joint owner).getD ⟨none⟩) (afterClear who)
          · intro current same who acting
            cases Option.some.inj same
            cases Option.some.inj acting
            exact runtime.serviceRisk_clear_before_respond leaks bound execution owner
              ((joint owner).getD ⟨none⟩) (afterClear owner)
      | none =>
          have prior : runtime.AllPersistentServiceRiskClear leaks bound
              (some ⟨remaining, none, execution⟩) := by
            cases remaining with
            | zero => cases (PMF.mem_support_pure_iff _ _).mp realized; exact clear
            | succ remaining =>
                obtain ⟨command, _, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
                cases same
                intro current same who
                cases Option.some.inj same
                exact runtime.persistentServiceRisk_clear_before_environment leaks bound who
                  (clear _ rfl who) supported
          refine ⟨prior, ?_⟩
          intro current same who acting
          cases Option.some.inj same
          cases acting

namespace MessageBounds

variable (bounds : MessageBounds graph)

private theorem embed_restrict_clear (who : Player)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (clear : runtime.serviceRisk leaks bound who past view = false) :
    (bounds.canonicalMenu runtime leaks).embedPolicy initial horizon scheduler who
        ((bounds.canonicalMenu runtime leaks).restrictPolicy initial horizon scheduler who policy)
        (some (past, view)) =
      (bounds.riskMenu runtime leaks bound).embedPolicy initial horizon scheduler who
        ((bounds.riskMenu runtime leaks bound).restrictPolicy initial horizon scheduler who policy)
        (some (past, view)) := by
  classical
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  simp only [ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp]
  change (((bounds.canonicalMenu runtime leaks).restrictPolicy initial horizon scheduler who
    policy) (some (past, view))).map Subtype.val =
      (((bounds.riskMenu runtime leaks bound).restrictPolicy initial horizon scheduler who
        policy) (some (past, view))).map Subtype.val
  simp only [ReactiveApplication.ResponseMenu.restrictPolicy, canonicalMenu, riskMenu,
    riskActions, clear, Bool.false_eq_true, ↓reduceIte]
  by_cases covered : ∀ response ∈ (policy past view).support,
      response ∈ bounds.canonicalActions runtime leaks who past view
  · simp only [dite_eq_left covered, map_bindOnSupport, PMF.pure_map]
  · simp only [dite_eq_right covered, PMF.pure_map]

/-- At its exact trace depth, each clean full raw history has identical mass
under the two menu representations of any common physical policy family. -/
theorem cleanPrefix_probability_exact
    (players : Player → (runtime.reactiveApplication leaks).Policy) :
    ∀ {state : (runtime.reactiveApplication leaks).ProtocolState}
      (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
        state),
      runtime.AllPersistentServiceRiskClear leaks bound state →
      let canonical := bounds.canonicalMenu runtime leaks
      let risk := bounds.riskMenu runtime leaks bound
      let model := (runtime.reactiveApplication leaks).information initial horizon scheduler
      model.runBehavioral (fun who => canonical.embedPolicy initial horizon scheduler who
        (canonical.restrictPolicy initial horizon scheduler who (players who))) trace.length
          ⟨state, trace⟩ =
      model.runBehavioral (fun who => risk.embedPolicy initial horizon scheduler who
        (risk.restrictPolicy initial horizon scheduler who (players who))) trace.length
          ⟨state, trace⟩
  | _, .start, _ => rfl
  | _, .extend prior joint legal realized, clear => by
      intro canonical risk model
      obtain ⟨priorClear, actingClear⟩ :=
        runtime.allPersistentServiceRiskClear_before_transition leaks bound initial horizon
          scheduler _ _ joint realized clear
      have earlier := cleanPrefix_probability_exact players prior priorClear
      have one : model.runBehavioralFrom (fun who => canonical.embedPolicy initial horizon
            scheduler who (canonical.restrictPolicy initial horizon scheduler who (players who)))
            1 ⟨_, prior⟩ =
          model.runBehavioralFrom (fun who => risk.embedPolicy initial horizon scheduler who
            (risk.restrictPolicy initial horizon scheduler who (players who))) 1 ⟨_, prior⟩ := by
        apply ExecutionProtocol.runRandomizedFor_one_congr_at_start
        intro running
        apply InformationModel.behavioralJoint_congr
        intro who
        have observed : model.infoOf who prior =
            (runtime.reactiveApplication leaks).observe who (History.mk _ prior).state
            := (runtime.reactiveApplication leaks).info initial horizon scheduler who prior
        rw [observed]
        cases before : (⟨_, prior⟩ :
            ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History).state
            with
        | none => rfl
        | some control =>
            by_cases active : control.actor = some who
            · simp only [ReactiveApplication.observe]
              rw [ite_eq_left active]
              exact bounds.embed_restrict_clear runtime leaks bound initial horizon scheduler who
                (players who) _ _ (actingClear control before who active)
            · simp only [ReactiveApplication.observe]
              rw [ite_eq_right active]
              rfl
      rw [InformationModel.runBehavioral, InformationModel.runBehavioral,
        InformationModel.runBehavioralFrom, InformationModel.runBehavioralFrom]
      simp only [Trace.length]
      conv_lhs =>
        rw [ExecutionProtocol.runRandomizedFor_apply_of_trace_succ _ _ _ _
          (by simp [ExecutionProtocol.initHistory, Trace.length])]
      conv_rhs =>
        rw [ExecutionProtocol.runRandomizedFor_apply_of_trace_succ _ _ _ _
          (by simp [ExecutionProtocol.initHistory, Trace.length])]
      exact congrArg₂ (fun first second : ENNReal => first * second) earlier
        (congrArg (fun law => law ⟨_, .extend prior joint legal realized⟩) one)

/-- The same exact clean-history mass holds at every initialized fuel. A
nonterminal history has mass only at its trace depth; a terminal one absorbs
additional fuel. Neither case queries the endpoint's response law. -/
theorem cleanPrefix_probability
    (players : Player → (runtime.reactiveApplication leaks).Policy) (fuel : Nat)
    (history : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History)
    (clear : runtime.AllPersistentServiceRiskClear leaks bound history.state) :
    let canonical := bounds.canonicalMenu runtime leaks
    let risk := bounds.riskMenu runtime leaks bound
    let model := (runtime.reactiveApplication leaks).information initial horizon scheduler
    model.runBehavioral (fun who => canonical.embedPolicy initial horizon scheduler who
      (canonical.restrictPolicy initial horizon scheduler who (players who))) fuel history =
    model.runBehavioral (fun who => risk.embedPolicy initial horizon scheduler who
      (risk.restrictPolicy initial horizon scheduler who (players who))) fuel history := by
  intro canonical risk model
  let first := model.randomizedChooser fun who => canonical.embedPolicy initial horizon scheduler
    who (canonical.restrictPolicy initial horizon scheduler who (players who))
  let second := model.randomizedChooser fun who => risk.embedPolicy initial horizon scheduler who
    (risk.restrictPolicy initial horizon scheduler who (players who))
  let protocol := (runtime.reactiveApplication leaks).protocol initial horizon scheduler
  have exactMass : protocol.runRandomizedFor first history.trace.length protocol.initHistory
        history =
      protocol.runRandomizedFor second history.trace.length protocol.initHistory history :=
    bounds.cleanPrefix_probability_exact runtime leaks bound initial horizon scheduler players
      history.trace clear
  change protocol.runRandomizedFor first fuel protocol.initHistory history =
    protocol.runRandomizedFor second fuel protocol.initHistory history
  rcases lt_trichotomy fuel history.trace.length with short | exactDepth | long
  · rw [ExecutionProtocol.runRandomizedFor_apply_eq_zero_of_length_gt first fuel _ history
      (by simpa [ExecutionProtocol.initHistory, Trace.length] using short),
      ExecutionProtocol.runRandomizedFor_apply_eq_zero_of_length_gt second fuel _ history
        (by simpa [ExecutionProtocol.initHistory, Trace.length] using short)]
  · rw [exactDepth]
    exact exactMass
  · by_cases stopped : (runtime.reactiveApplication leaks).terminal history.state
    · obtain ⟨extra, sameFuel⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt long)
      rw [sameFuel,
        ExecutionProtocol.runRandomizedFor_apply_terminal_add first history.trace.length extra
          _ history (by simp [ExecutionProtocol.initHistory, Trace.length]) stopped,
        ExecutionProtocol.runRandomizedFor_apply_terminal_add second history.trace.length extra
          _ history (by simp [ExecutionProtocol.initHistory, Trace.length]) stopped]
      exact exactMass
    · rw [ExecutionProtocol.runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal first fuel
        _ history (by simpa [ExecutionProtocol.initHistory, Trace.length] using long) stopped,
        ExecutionProtocol.runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal second fuel
          _ history (by simpa [ExecutionProtocol.initHistory, Trace.length] using long) stopped]

/-- Equality is a point mass of the actual finite-menu runners after retaining
the complete realized raw history. It is not a separate path-mass model. -/
theorem cleanPrefix_menu_probability
    (players : Player → (runtime.reactiveApplication leaks).Policy) (fuel : Nat)
    (history : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History)
    (clear : runtime.AllPersistentServiceRiskClear leaks bound history.state) :
    let canonical := bounds.canonicalMenu runtime leaks
    let risk := bounds.riskMenu runtime leaks bound
    ((canonical.information initial horizon scheduler).runBehavioral
      (fun who => canonical.restrictPolicy initial horizon scheduler who (players who)) fuel).map
        (canonical.toRawHistory initial horizon scheduler) history =
    ((risk.information initial horizon scheduler).runBehavioral
      (fun who => risk.restrictPolicy initial horizon scheduler who (players who)) fuel).map
        (risk.toRawHistory initial horizon scheduler) history := by
  intro canonical risk
  rw [InformationModel.runBehavioral, canonical.run_embed,
    InformationModel.runBehavioral, risk.run_embed]
  exact bounds.cleanPrefix_probability runtime leaks bound initial horizon scheduler players fuel
    history clear

/-- Every event consisting of clean prefixes has the same unnormalized
probability in the two finite-menu games. The event may select public data,
private recall, exact traffic or an information fiber within those prefixes. -/
theorem cleanPrefix_event_probability
    (players : Player → (runtime.reactiveApplication leaks).Policy) (fuel : Nat)
    (event : Set
      ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).History)
    (clear : ∀ history ∈ event,
      runtime.AllPersistentServiceRiskClear leaks bound history.state) :
    let canonical := bounds.canonicalMenu runtime leaks
    let risk := bounds.riskMenu runtime leaks bound
    (((canonical.information initial horizon scheduler).runBehavioral
      (fun who => canonical.restrictPolicy initial horizon scheduler who (players who)) fuel).map
        (canonical.toRawHistory initial horizon scheduler)).toOuterMeasure event =
    (((risk.information initial horizon scheduler).runBehavioral
      (fun who => risk.restrictPolicy initial horizon scheduler who (players who)) fuel).map
        (risk.toRawHistory initial horizon scheduler)).toOuterMeasure event := by
  classical
  intro canonical risk
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro history
  by_cases present : history ∈ event
  · rw [Set.indicator_of_mem present, Set.indicator_of_mem present]
    exact bounds.cleanPrefix_menu_probability runtime leaks bound initial horizon scheduler
      players fuel history (clear history present)
  · simp only [Set.indicator, ite_eq_right present]

end MessageBounds
end Vegas.EventGraphRuntime

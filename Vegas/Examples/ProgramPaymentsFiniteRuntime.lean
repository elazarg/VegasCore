/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ProgramPayments
import Vegas.EventGraph.SequentialLaw
import Vegas.EventGraph.SchedulerProtocol
import GameTheoryExtensions.Analysis.PrivateObservableTransport

/-! # Exact finite configurations of the compiled payment program

The carrier retains failed binding attempts and the original disclosure action.
It represents the compiled event graph, rather than the signed-message runtime.
-/

noncomputable section

namespace Vegas.Examples.ProgramPaymentsFiniteRuntime

open EventGraph SourceProgram GameTheory GameTheory.Math.Probability
open ProgramPayments

abbrev graph := (toEventGraph (program 2)).withMode .sequential

private instance : NeZero graph.order.eventCount := ⟨by decide⟩

inductive ConfigCode where
  | initial
  | bound (binding : PublicationResult Bool)
  | revealed (binding : PublicationResult Bool) (publish : Bool)
  deriving DecidableEq, Fintype

def initial : graph.Config := .initial fun input => Fin.elim0 input

theorem initial_ready : initial.cut.Ready 0 := by decide

def bound (binding : PublicationResult Bool) : graph.Config :=
  initial.complete 0 initial_ready binding binding

theorem bound_ready (binding : PublicationResult Bool) : (bound binding).cut.Ready 1 := by
  change (initial.cut.complete 0 initial_ready).Ready 1
  decide

def publication (binding : PublicationResult Bool) (publish : Bool) : PublicationResult Bool :=
  if publish then binding else .failure

def revealed (binding : PublicationResult Bool) (publish : Bool) : graph.Config :=
  (bound binding).complete 1 (bound_ready binding) publish (publication binding publish)

def encode : ConfigCode → graph.Config
  | .initial => initial
  | .bound binding => bound binding
  | .revealed binding publish => revealed binding publish

theorem state_card : Fintype.card ConfigCode = 10 := by decide

theorem binding_step (binding : PublicationResult Bool) :
    initial.step 0 initial_ready binding = PMF.pure (bound binding) := by
  rw [initial.step_eq_map_of_eval 0 initial_ready binding (PMF.pure binding) rfl,
    PMF.pure_map]
  rfl

theorem reveal_step (binding : PublicationResult Bool) (publish : Bool) :
    (bound binding).step 1 (bound_ready binding) publish =
      PMF.pure (revealed binding publish) := by
  have evaluates : (graph.nodes 1).eval? publish (bound binding).store =
      some (PMF.pure (publication binding publish)) := by
    cases binding with
    | failure => cases publish <;> rfl
    | success bit => cases bit <;> cases publish <;> rfl
  rw [(bound binding).step_eq_map_of_eval 1 (bound_ready binding) publish
    (PMF.pure (publication binding publish)) evaluates, PMF.pure_map]
  rfl

def actionHistory : ConfigCode → List graph.Completion
  | .initial => []
  | .bound binding => [⟨0, binding⟩]
  | .revealed binding publish => [⟨0, binding⟩, ⟨1, publish⟩]

theorem observation_actions (state : ConfigCode) :
    (graph.playerObserve .alice (encode state)).ownActions = actionHistory state := by
  cases state <;> rfl

theorem actionHistory_injective : Function.Injective actionHistory := by
  intro left right equal
  cases left <;> cases right
  · rfl
  · cases equal
  · cases equal
  · cases equal
  · rename_i left right
    have head := congrArg List.head? equal
    have actions := Option.some.inj head
    have same : left = right := by cases actions; rfl
    exact congrArg ConfigCode.bound same
  · cases equal
  · cases equal
  · cases equal
  · rename_i leftBinding leftPublish rightBinding rightPublish
    have first := congrArg List.head? equal
    have first := Option.some.inj first
    have binding : leftBinding = rightBinding := by cases first; rfl
    have last := congrArg (fun xs => xs[1]?) equal
    have last := Option.some.inj last
    have publish : leftPublish = rightPublish := by cases last; rfl
    cases binding
    cases publish
    rfl

/-- The actual owner observation distinguishes all ten reachable encodings. -/
theorem observation_injective :
    Function.Injective (fun state => graph.playerObserve .alice (encode state)) := by
  intro left right equal
  apply actionHistory_injective
  simpa only [observation_actions] using congrArg PlayerObservation.ownActions equal

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  exact observation_injective (congrArg (graph.playerObserve .alice) equal)

theorem revealed_terminal (binding : PublicationResult Bool) (publish : Bool) :
    (revealed binding publish).cut.Terminal := by
  change ({1, 0} : Finset (Fin 2)) = Finset.univ
  decide

/-- The finite representation evaluates the original compiled payment expression. -/
theorem revealed_payments (binding : PublicationResult Bool) (publish : Bool) :
    (revealed binding publish).terminalPayoffs (revealed_terminal binding publish) =
      [(.alice, if publication binding publish = .success true then 2 else 0)] := by
  cases binding with
  | failure => cases publish <;> rfl
  | success bit => cases bit <;> cases publish <;> rfl

abbrev Action := PublicationResult Bool × Bool

def next : ConfigCode → Action → ConfigCode
  | .initial, action => .bound action.1
  | .bound binding, action => .revealed binding action.2
  | .revealed binding publish, _ => .revealed binding publish

def advance (state : ConfigCode) (action : Action) : PMF ConfigCode := PMF.pure (next state action)

/-- Padding is explicit only after both real instructions have completed. -/
def actualAdvance (state : ConfigCode) (action : Action) : PMF graph.Config :=
  match state with
  | .initial => initial.step 0 initial_ready action.1
  | .bound binding => (bound binding).step 1 (bound_ready binding) action.2
  | .revealed binding publish => PMF.pure (revealed binding publish)

theorem advance_encoded (state : ConfigCode) (action : Action) :
    (advance state action).map encode = actualAdvance state action := by
  cases state
  · exact (PMF.pure_map _ _).trans (binding_step action.1).symm
  · exact (PMF.pure_map _ _).trans (reveal_step _ action.2).symm
  · exact PMF.pure_map _ _

theorem step_closed (state : ConfigCode) (event : graph.EventId)
    (ready : (encode state).cut.Ready event) (action : graph.Action event) :
    ∃ successor, (encode state).step event ready action = PMF.pure (encode successor) := by
  cases state with
  | initial =>
      have same := EventOrder.Cut.ready_unique initial.cut ready initial_ready
      subst event
      exact ⟨.bound action, binding_step action⟩
  | bound binding =>
      have same := EventOrder.Cut.ready_unique (bound binding).cut ready (bound_ready binding)
      subst event
      exact ⟨.revealed binding action, reveal_step binding action⟩
  | revealed binding publish =>
      have terminal := revealed_terminal binding publish
      exact False.elim (ready.1 (terminal ▸ Finset.mem_univ event))

theorem encoded_reachable (state : ConfigCode) :
    Config.Reachable initial.inputs (encode state) := by
  have start : Config.Reachable initial.inputs initial := .initial
  have first (binding : PublicationResult Bool) :
      Config.Reachable initial.inputs (bound binding) :=
    .step start 0 initial_ready binding (bound binding) (by rw [binding_step]; simp)
  cases state with
  | initial => exact start
  | bound binding => exact first binding
  | revealed binding publish =>
      exact .step (first binding) 1 (bound_ready binding) publish (revealed binding publish)
        (by rw [reveal_step]; simp)

/-- The finite carrier is exactly the reachable Config carrier,
including intermediate states. -/
theorem reachable_iff (config : graph.Config) :
    Config.Reachable initial.inputs config ↔ ∃ state, encode state = config := by
  constructor
  · intro reachable
    induction reachable with
    | initial => exact ⟨.initial, rfl⟩
    | step prior event ready action successor supported ih =>
        obtain ⟨state, rfl⟩ := ih
        obtain ⟨nextState, law⟩ := step_closed state event ready action
        rw [law] at supported
        exact ⟨nextState, ((PMF.mem_support_pure_iff _ _).mp supported).symm⟩
  · rintro ⟨state, rfl⟩
    exact encoded_reachable state

instance : Inhabited ConfigCode := ⟨.initial⟩

def observation (state : ConfigCode) := graph.playerObserve .alice (encode state)

def decodeObservation : graph.PlayerObservation .alice → ConfigCode :=
  Function.invFun observation

theorem decode_observation (state : ConfigCode) : decodeObservation (observation state) = state :=
  Function.leftInverse_invFun observation_injective state

/-- A total legal graph profile: the unused coordinate of each action pair is ignored. -/
def toProfile (policy : ConfigCode → PMF Action) : graph.BehavioralProfile :=
  fun who event _ observed => by
    cases who
    change Fin 2 at event
    refine Fin.cases ?_ (fun tail => ?_) event
    · exact (policy (decodeObservation observed)).map Prod.fst
    · exact Fin.cases ((policy (decodeObservation observed)).map Prod.snd)
        (fun impossible => Fin.elim0 impossible) tail

/-- Every genuine graph action law has a finite paired representative. -/
def fromProfile (profile : graph.BehavioralProfile) (state : ConfigCode) : PMF Action :=
  match state with
  | .initial => (profile .alice 0 rfl (observation state)).map fun binding => (binding, false)
  | .bound _ => (profile .alice 1 rfl (observation state)).map fun publish => (.failure, publish)
  | .revealed _ _ => PMF.pure (.failure, false)

theorem toProfile_binding (policy : ConfigCode → PMF Action) :
    toProfile policy .alice 0 rfl (observation .initial) =
      (policy .initial).map Prod.fst := by
  change (policy (decodeObservation (observation .initial))).map Prod.fst = _
  rw [decode_observation]

theorem toProfile_reveal (policy : ConfigCode → PMF Action) (binding : PublicationResult Bool) :
    toProfile policy .alice 1 rfl (observation (.bound binding)) =
      (policy (.bound binding)).map Prod.snd := by
  change (policy (decodeObservation (observation (.bound binding)))).map Prod.snd = _
  rw [decode_observation]

theorem fromProfile_binding (profile : graph.BehavioralProfile) :
    (fromProfile profile .initial).map Prod.fst =
      profile .alice 0 rfl (observation .initial) := by
  rw [fromProfile, PMF.map_comp]
  exact PMF.map_id _

theorem fromProfile_reveal (profile : graph.BehavioralProfile)
    (binding : PublicationResult Bool) :
    (fromProfile profile (.bound binding)).map Prod.snd =
      profile .alice 1 rfl (observation (.bound binding)) := by
  rw [fromProfile, PMF.map_comp]
  exact PMF.map_id _

theorem scheduler_draw (scheduler : graph.PublicScheduler) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) (event : graph.EventId)
    (ready : config.cut.Ready event) :
    scheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal) =
      PMF.pure ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩ := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro selected _
  apply Set.mem_singleton_iff.mpr
  apply Subtype.ext
  exact EventOrder.Cut.ready_unique config.cut
    ((EventOrder.Cut.mem_enabled _ _).mp selected.2) ready

theorem runPolicies_law (scheduler : graph.PublicScheduler)
    (profile : graph.BehavioralProfile) :
    graph.runPolicies scheduler profile initial.inputs =
      (profile .alice 0 rfl (observation .initial)).bind fun binding =>
        (profile .alice 1 rfl (observation (.bound binding))).map
          (revealed binding) := by
  have initialNotTerminal : ¬ initial.cut.Terminal := by decide
  have boundNotTerminal (binding : PublicationResult Bool) :
      ¬ (bound binding).cut.Terminal := by
    change ¬ ({0} : Finset (Fin 2)) = Finset.univ
    decide
  change graph.runPlan (graph.policyPlan profile scheduler) 2 initial = _
  rw [runPlan, dite_eq_right initialNotTerminal, policyPlan_step_bind,
    scheduler_draw scheduler initial initialNotTerminal 0 initial_ready, PMF.pure_bind]
  unfold selectedPolicyStep
  change (((profile .alice 0 rfl (observation .initial)).bind
    (initial.step 0 initial_ready)).bind
      (graph.runPlan (graph.policyPlan profile scheduler) 1)) = _
  rw [PMF.bind_bind]
  simp only [binding_step, PMF.pure_bind]
  apply bind_congr_on_support
  intro binding _
  rw [runPlan, dite_eq_right (boundNotTerminal binding), policyPlan_step_bind,
    scheduler_draw scheduler (bound binding) (boundNotTerminal binding) 1
      (bound_ready binding), PMF.pure_bind]
  unfold selectedPolicyStep
  change (((profile .alice 1 rfl (observation (.bound binding))).bind
    ((bound binding).step 1 (bound_ready binding))).bind
      (graph.runPlan (graph.policyPlan profile scheduler) 0)) = _
  rw [PMF.bind_bind]
  simp only [reveal_step, runPlan, PMF.bind_pure]
  exact PMF.bind_pure_comp _ _

/-- The finite runner uses both genuine choices, with arbitrary observation-local laws. -/
theorem finite_run_actual (scheduler : graph.PublicScheduler) (policy : ConfigCode → PMF Action) :
    (GameTheory.Protocol.PrivateStrategy.runBehavioral (fun _ => policy) id advance 2 []
        .initial).map (fun result => encode result.1) =
      graph.runPolicies scheduler (toProfile policy) initial.inputs := by
  rw [runPolicies_law, toProfile_binding]
  simp only [GameTheory.Protocol.PrivateStrategy.runBehavioral, id_eq, advance, next,
    PMF.pure_bind, PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def]
  apply bind_congr_on_support
  intro action _
  rw [toProfile_reveal, PMF.map_comp]
  rfl

open GameTheory.Protocol.PrivateStrategy GameTheory.Math.InvariantObservables

inductive Readout where
  | unfinished
  | failed
  | falsePublication
  | truePublication
  deriving DecidableEq, Fintype

def readout : ConfigCode → Readout
  | .initial | .bound _ => .unfinished
  | .revealed binding publish =>
      match publication binding publish with
      | .failure => .failed
      | .success false => .falsePublication
      | .success true => .truePublication

def jointReadout : Readout → Option (PublicationResult Bool) × Int × ℝ
  | .unfinished => (none, 0, 0)
  | .failed => (some .failure, 0, 0)
  | .falsePublication => (some (.success false), 0, 0)
  | .truePublication => (some (.success true), 2, 1)

theorem jointReadout_injective : Function.Injective jointReadout := by
  intro first second equal
  cases first <;> cases second <;> simp_all [jointReadout]

/-- Joint publication, compiled payment and original utility, evaluated together. -/
theorem jointReadout_actual (binding : PublicationResult Bool) (publish : Bool) :
    jointReadout (readout (.revealed binding publish)) =
      ((revealed binding publish).outputs 1,
        transferAmount ((revealed binding publish).terminalPayoffs
          (revealed_terminal binding publish)) .alice,
        (game 2).utility
          (Env.cons (publication binding publish) (Env.empty simpleExpr.Val)) .alice) := by
  rw [revealed_payments, utility_eq]
  cases binding with
  | failure => cases publish <;> rfl
  | success bit => cases bit <;> cases publish <;> norm_num [jointReadout, readout,
      publication, revealed, EventGraph.Config.complete, transferAmount, Env.get, Env.cons]

end Vegas.Examples.ProgramPaymentsFiniteRuntime

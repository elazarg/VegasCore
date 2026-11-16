module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensFairLaw
public import Vegas.Game.IntendedSourceProfile
public import Vegas.Game.SourcePrefixForfeit
public import Vegas.Game.RevealService

@[expose] public section

noncomputable section

namespace Vegas.Examples.OddsEvensConcurrent

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability
open OddsEvens

abbrev dependencies := setup.dataflowGraph.bindingDependencies setup.revealDependencies
abbrev graph := serviceGraph setup dependencies

instance : NeZero graph.order.eventCount := ⟨by decide⟩
instance : NeZero setup.dataflowGraph.order.eventCount := ⟨by decide⟩

theorem event_count : graph.order.eventCount = 4 := rfl

theorem all_owned (event : graph.EventId) : ∃ who, graph.actor? event = some who := by
  fin_cases event <;> exact ⟨_, rfl⟩

theorem relaxed : graph.RevealRelaxedOrdered :=
  setup.informationGraph.relaxReveals.relaxBindings_revealRelaxedOrdered
    (setup.informationGraph.relaxReveals_revealRelaxedOrdered
      (toInformationGraph_barrierOrdered setup.program).revealRelaxedOrdered)

abbrev initial : graph.Config := Config.initial (setup.eventInputs (Env.empty _))

theorem bindings_independent : setup.dataflowGraph.IndependentBindings 0 1 :=
  ⟨even, odd, .bool, .bool, rfl, rfl, by decide⟩

theorem reveals_independent : setup.dataflowGraph.IndependentReveals 2 3 := by
  constructor
  · trivial
  constructor
  · trivial
  constructor <;> decide

theorem bindings_ready_initial : initial.cut.Ready 0 ∧ initial.cut.Ready 1 := by
  classical
  constructor
  · refine ⟨by decide, ?_⟩
    intro prior member
    have earlier := graph.order.predecessor_lt member
    change prior.val < 0 at earlier
    exact (Nat.not_lt_zero prior.val earlier).elim
  · refine ⟨by decide, ?_⟩
    intro prior member
    have earlier := graph.order.predecessor_lt member
    have same : prior = 0 := by
      simpa [show setup.dataflowGraph.order.eventCount = 4 from rfl] using earlier
    subst prior
    have kept : ¬ setup.dataflowGraph.IndependentBindings 0 1 :=
      (Finset.mem_filter.mp member).2
    exact (kept bindings_independent).elim

def evenBound (bit : Bool) : graph.Config :=
  initial.complete 0 bindings_ready_initial.1 (some (.success bit)) (.success bit)

theorem odd_binding_ready (bit : Bool) : (evenBound bit).cut.Ready 1 :=
  bindings_ready_initial.2.after_complete bindings_ready_initial.1 (by decide)

def bothBound (evenBit oddBit : Bool) : graph.Config :=
  (evenBound evenBit).complete 1 (odd_binding_ready evenBit)
    (some (.success oddBit)) (.success oddBit)

theorem even_binding_step (bit : Bool) :
    initial.step 0 bindings_ready_initial.1 (some (.success bit)) =
      PMF.pure (evenBound bit) := by
  rw [initial.step_eq_map_of_eval 0 bindings_ready_initial.1 (some (.success bit))
    (PMF.pure (.success bit)) (by rfl), PMF.pure_map]
  rfl

theorem odd_binding_step (evenBit oddBit : Bool) :
    (evenBound evenBit).step 1 (odd_binding_ready evenBit) (some (.success oddBit)) =
      PMF.pure (bothBound evenBit oddBit) := by
  rw [Config.step_eq_map_of_eval _ 1 (odd_binding_ready evenBit) (some (.success oddBit))
    (PMF.pure (.success oddBit)) (by rfl), PMF.pure_map]
  rfl

theorem bothBound_reachable (evenBit oddBit : Bool) :
    Config.Reachable initial.inputs (bothBound evenBit oddBit) := by
  have first : Config.Reachable initial.inputs (evenBound evenBit) :=
    .step .initial 0 bindings_ready_initial.1 (some (.success evenBit)) _
      (by rw [even_binding_step]; simp)
  exact .step first 1 (odd_binding_ready evenBit) (some (.success oddBit)) _
    (by rw [odd_binding_step]; simp)

theorem reveals_ready_after_bindings (evenBit oddBit : Bool) :
    (bothBound evenBit oddBit).cut.Ready 2 ∧ (bothBound evenBit oddBit).cut.Ready 3 := by
  classical
  constructor
  · refine ⟨by change (2 : graph.EventId) ∉ ({1, 0} : Finset _); decide, ?_⟩
    intro prior member
    have earlier := graph.order.predecessor_lt member
    change prior.val < 2 at earlier
    fin_cases prior
    · change (0 : graph.EventId) ∈ ({1, 0} : Finset _); decide
    · change (1 : graph.EventId) ∈ ({1, 0} : Finset _); decide
    · norm_num [event_count] at earlier
    · norm_num [event_count] at earlier
  · refine ⟨by change (3 : graph.EventId) ∉ ({1, 0} : Finset _); decide, ?_⟩
    intro prior member
    have earlier := graph.order.predecessor_lt member
    change prior.val < 3 at earlier
    fin_cases prior
    · change (0 : graph.EventId) ∈ ({1, 0} : Finset _); decide
    · change (1 : graph.EventId) ∈ ({1, 0} : Finset _); decide
    · have revealEdge : (2 : graph.EventId) ∈ setup.revealDependencies.predecessors 3 :=
        (Finset.mem_filter.mp member).1
      exact ((Finset.mem_filter.mp revealEdge).2 reveals_independent).elim
    · norm_num [event_count] at earlier

theorem bindings_enabled_initial : {0, 1} ⊆ initial.cut.enabled := by
  intro event member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact (EventOrder.Cut.mem_enabled _ _).2 bindings_ready_initial.1
  · exact (EventOrder.Cut.mem_enabled _ _).2 bindings_ready_initial.2

theorem reveals_enabled_after_bindings (evenBit oddBit : Bool) :
    {2, 3} ⊆ (bothBound evenBit oddBit).cut.enabled := by
  intro event member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact (EventOrder.Cut.mem_enabled _ _).2 (reveals_ready_after_bindings _ _).1
  · exact (EventOrder.Cut.mem_enabled _ _).2 (reveals_ready_after_bindings _ _).2

theorem utility_spread (high low : Unit × PublicOutcome program) (who : Player) :
    sourceUtility high who - sourceUtility low who ≤ 200 := by
  have highBound := (sourceUtility_bounds high who).2
  have lowBound := (sourceUtility_bounds low who).1
  linarith

private theorem sourceUtility_integrable (law : PMF setup.intendedProtocol.History)
    (who : Player) : PayoffIntegrable law (terminalUtility who) :=
  payoffIntegrable_of_finite_support _ _ (Set.toFinite _)

theorem uniform_isNash : IsεNash
    (setup.intendedModel.toBehavioralGameForm (instructionCount setup.program + 1))
    (fun final who => (setup.protocolReadout final.state).elim 0
      (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who))
    0 uniformAssessment.strategy := by
  rw [IsεNash, isNash_iff]
  intro who replacement
  apply (euPreferenceWithin_iff _ _ _ _ _
    (sourceUtility_integrable _ who) (sourceUtility_integrable _ who)).2
  change expect (setup.intendedModel.runBehavioral
    (Profile.update (sig := setup.intendedModel.behavioralSignature)
      uniformProfile who replacement) (instructionCount setup.program + 1))
      (terminalUtility who) ≤
    expect (setup.intendedModel.runBehavioral uniformProfile
      (instructionCount setup.program + 1)) (terminalUtility who) + 0
  rw [uniform_root_value, uniform_expected_payoff]
  norm_num

abbrev admission := CommitmentInterface.forfeiture program
def target := setup.intendedSourceProfile admission uniformAssessment.strategy
def source := setup.decodeBehavioralProfile admission target
def graphClients : graph.BehavioralProfile := compilePrescribedProfile program dependencies source

theorem target_extends : (setup.intendedRestriction admission).ExtendsProfile
    uniformAssessment.strategy target := setup.intendedSourceProfile_extends _ _

theorem source_disclosing (who : Player) : Disclosing program (source who) :=
  setup.intendedSourceProfile_disclosing admission uniformAssessment.strategy who

theorem uniform_joint_law :
    (setup.intendedModel.runBehavioral uniformAssessment.strategy
      (instructionCount setup.program + 1)).map (fun final =>
        (setup.protocolReadout final.state, fun who => (setup.protocolReadout final.state).elim 0
          (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who))) =
        uniformJointLaw := by
  rw [← uniform_source_joint_law]
  apply map_congr_on_support _
  intro final _supported
  refine Prod.ext rfl (funext fun who => ?_)
  exact (setup.intended_exclusionReadoutUtility wellFormed (fun _ => ()) sourceUtility
    (fun _ => 0) final who).symm

theorem graph_equilibrium (scheduler : graph.PublicScheduler) :
    IsεNash (graph.gameForm (setup.graphInputs dependencies) scheduler)
      (setup.graphForfeitPayoff dependencies (fun _ => ()) sourceUtility 200) 0 graphClients ∧
    (∀ outcome ∈ ((graph.gameForm (setup.graphInputs dependencies) scheduler).play
        graphClients).support,
      (setup.graphReadout dependencies outcome).defaulted = ∅ ∧
        ∀ who, failedReveals program who
          (publicOutcome program (setup.graphReadout dependencies outcome)) = 0) ∧
    (((graph.gameForm (setup.graphInputs dependencies) scheduler).play graphClients).map
      (fun outcome => (some (setup.graphReadout dependencies outcome),
        setup.graphForfeitPayoff dependencies (fun _ => ()) sourceUtility 200 outcome))) =
      uniformJointLaw ∧
    ∀ who, expect ((graph.gameForm (setup.graphInputs dependencies) scheduler).play graphClients)
      (fun outcome => setup.graphForfeitPayoff dependencies (fun _ => ()) sourceUtility 200
        outcome who) = 100 := by
  obtain ⟨nash, clean, law⟩ := setup.compileIntendedExtension_forfeit dependencies relaxed
    finiteBindingTypes wellFormed (fun _ => ()) sourceUtility 200 utility_spread
    uniformAssessment.strategy target target_extends source_disclosing 0 uniform_isNash scheduler
  have exactLaw := law.trans uniform_joint_law
  refine ⟨nash, clean, exactLaw, ?_⟩
  intro who
  have expected := congrArg (fun law => expect law (fun observed => observed.2 who)) exactLaw
  rw [expect_map] at expected
  exact expected.trans (uniformJointLaw_expected who)

end Vegas.Examples.OddsEvensConcurrent

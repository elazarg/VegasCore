/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ObservationRequirement
import GameTheoryExtensionsTests.ContinuationDecision

/-! # Fixed-payoff observation requirements at actual protocol sites

Both bit values have positive probability in the existing terminal decision
protocol. Its player knows the bit and is paid for reporting it correctly.
Every further observation abstraction merging the two actual information sites
fails rationality if the executed report law factors through the abstraction.
The protocol nevertheless has a standard sequential equilibrium. A constant
macro label interpreted using the concrete state executes that equilibrium,
showing why the response-law factorization premise is essential.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ObservationRequirement

open GameTheory GameTheory.Protocol GameTheory.DecisionExperiment
open GameTheory.DecisionExperiment.Protocol GameTheory.Math.Probability
open GameTheoryExtensionsTests.ContinuationDecision

abbrev bitModel := model (Action := Bool) biasedBit id

def bitDecision (bit : Bool) : bitModel.ContinuationDecision
    (fun _ history => payoff (reportUtility id) history.state) 2 Bool Bool :=
  decision biasedBit id (site biasedBit id bit (biasedBit_full bit)) (reportUtility id)

theorem bit_known (bit : Bool) :
    bitModel.Knows () (bitDecision bit).site.1
      (fun history => latent biasedBit history.state = bit) := by
  intro history
  obtain ⟨state, _, current, observed⟩ :=
    history_at_site biasedBit id (bitDecision bit).site history
  have same : state = bit := Option.some.inj observed
  rw [current]
  exact same

theorem bit_reward (original : bitModel.BehavioralAssessment) (bit action : Bool) :
    (bitDecision bit).expectedReward original action = if bit = action then 1 else 0 := by
  exact (bitDecision bit).expectedReward_of_known
    (fun history => latent biasedBit history.state) (fun _ => rfl) bit (bit_known bit)
      original action

theorem incompatible_maximizers (original : bitModel.BehavioralAssessment) :
    ¬ ∃ action,
      (∀ alternative, (bitDecision false).expectedReward original alternative ≤
        (bitDecision false).expectedReward original action) ∧
      (∀ alternative, (bitDecision true).expectedReward original alternative ≤
        (bitDecision true).expectedReward original action) := by
  rintro ⟨action, first, second⟩
  cases action with
  | false =>
      have impossible := second true
      norm_num [bit_reward] at impossible
  | true =>
      have impossible := first false
      norm_num [bit_reward] at impossible

/-- No alphabet or additional coarsening can hide this distinction while
retaining a state-independent report interpretation. Beliefs cannot help. -/
theorem merged_bits_not_sequentially_rational {Observation Coarse : Type*}
    (observe : Bool → Observation) (coarsen : Observation → Coarse)
    (respond : Coarse → FinDist Bool) (original : bitModel.BehavioralAssessment)
    (factors : ∀ bit, (bitDecision bit).response original.strategy =
      respond (coarsen (observe bit)))
    (merged : coarsen (observe false) = coarsen (observe true)) :
    ¬ original.IsSequentiallyRationalWithin
      (fun _ history => payoff (reportUtility id) history.state) 2 :=
  InformationModel.ContinuationDecision.not_rational_of_coarsening_collision bitDecision
    observe coarsen respond original factors false true merged (incompatible_maximizers original)

def reporting : bitModel.BehavioralAssessment :=
  assessment biasedBit id (fun bit => FinDist.pure bit)

theorem reporting_sequential_equilibrium :
    reporting.IsSequentialEquilibriumFor (antichain biasedBit id)
      (fun _ site => reporting.continuationContext site
        (fun history => payoff (reportUtility id) history.state) 2) := by
  apply (isSequentialEquilibrium_iff biasedBit id _ _).mpr
  intro signal alternative
  unfold localValue
  apply FinDist.expect_mono
  intro state _
  by_cases same : state = signal
  · subst state
    simp only [Set.mem_preimage, Set.mem_singleton_iff, id_eq, Set.indicator_of_mem,
      FinDist.expect_pure, reportUtility, ite_true]
    apply FinDist.expect_le_of_forall
    intro action _
    unfold reportUtility
    split <;> norm_num
  · simp [same]

theorem reporting_response (bit : Bool) :
    (bitDecision bit).response reporting.strategy = FinDist.pure bit := by
  change response biasedBit id (policy biasedBit id (fun bit => FinDist.pure bit))
    (siteSignal biasedBit id (bitDecision bit).site) = _
  rw [response_policy]
  have observed := site_signal biasedBit id (bitDecision bit).site
  have same : bit = siteSignal biasedBit id (bitDecision bit).site := Option.some.inj observed
  rw [← same]

/-- A single macro label can retain the distinction operationally: its
interpretation reads the state and emits the corresponding report. Such a
macro does not factor the executed report law through the constant label. -/
theorem state_aware_macro_executes_equilibrium :
    (∀ bit, (bitDecision bit).response reporting.strategy =
      (FinDist.pure ()).bind (fun _ => FinDist.pure bit)) ∧
      ¬ ∃ respond : Unit → FinDist Bool, ∀ bit,
        (bitDecision bit).response reporting.strategy = respond () := by
  refine ⟨fun bit => by simpa using reporting_response bit, ?_⟩
  rintro ⟨respond, factors⟩
  exact merged_bits_not_sequentially_rational (fun _ => ()) id respond reporting factors rfl
    reporting_sequential_equilibrium.1

end GameTheoryExtensionsTests.ObservationRequirement

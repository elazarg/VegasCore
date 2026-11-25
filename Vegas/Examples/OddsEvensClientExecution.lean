module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensClientOutput
public import Interaction.ReactiveRecovery

@[expose] public section

/-! # Execution of the coin-driven packet client against arbitrary opponents -/

noncomputable section

namespace Vegas.Examples.OddsEvensExecutableClient

open OddsEvens OddsEvensLedgerClient EventGraphRuntime Interaction GameTheory.Math.Probability

/-- At every finite prefix the coin-driven clients and the model clients
give the same full execution distribution. Install the client for either
player, both players or neither. All other callback policies are arbitrary. -/
theorem respondWithCoin_roundsFrom (installed : Player → Bool)
    (other : Player → app.Policy) (inputs : PMF compiled.Inputs) (scheduler : app.Scheduler)
    (rounds : Nat) :
    app.roundsFrom (inputs.map State.initial) scheduler (fun who =>
      if installed who then fun past view => (uniformLaw Bool).map (respondWithCoin who past view)
      else other who) rounds =
    app.roundsFrom (inputs.map State.initial) scheduler
      (fun who => if installed who then policy who else other who) rounds := by
  let valid (execution : app.Execution) :=
    CandidateRecall OddsEvensService.timeouts OddsEvensService.leaks execution ∧
      execution.Provenance app
  have invariant (players : Player → app.Policy) : app.PolicyInvariant players valid := {
    respond := fun execution who action before _ => ⟨candidateRecall_respond
      OddsEvensService.timeouts OddsEvensService.leaks execution who action before.1,
      app.respond_provenance execution who action before.2⟩
    environment := fun execution next command before reached => ⟨candidateRecall_environment
      OddsEvensService.timeouts OddsEvensService.leaks execution next command before.1 before.2
      reached, app.environment_provenance execution next command before.2 reached⟩ }
  unfold ReactiveApplication.roundsFrom
  rw [PMF.bind_map, PMF.bind_map]
  apply bind_congr_on_support
  intro input _
  apply (invariant _).runRounds_congr
  · intro execution ok who
    cases used : installed who
    · rfl
    · simp only [↓reduceIte]
      apply respondWithCoin_distribution_of_slot
      rw [countCompletedBindings_eq, bindingSlotFresh_eq]
      exact boundedCanonicalSlot_eq who _ _ (reactiveFreshSlot_le_recall
        OddsEvensService.timeouts OddsEvensService.leaks execution who ok.1)
  · exact ⟨fun who serial _ => State.initial_candidate input who (.prepared serial),
      MessageNetwork.Satisfies.empty⟩

end Vegas.Examples.OddsEvensExecutableClient

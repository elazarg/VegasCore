module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedPrivateValueAuction
public import Vegas.Game.ClientSpecification

@[expose] public section

noncomputable section

namespace Vegas.Examples.BoundedPrivateValueAuction

open SourceProgram EventGraphRuntime GameTheory GameTheory.Math.Probability
open CommitRevealAuction (Player)

abbrev graph := (setup uniformPrior).informationGraph

def bounds : MessageBounds graph where
  candidateCount := 2
  values := Finset.univ.image fun value : Bid => (⟨.range 0 6, value⟩ : Raw simpleExpr)

theorem outputValues : bounds.CoversOutputValues := by
  intro event
  fin_cases event <;> intro value <;> exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩

theorem inputValues : bounds.CoversInputValues := by
  intro input
  fin_cases input <;> intro owner payload impossible <;> cases impossible

theorem candidateCapacity : ∀ who, bindingEventCount graph who < bounds.candidateCount := by
  intro who
  cases who <;> decide

private theorem bounded_economic_utility (values : Player → ℝ)
    (bounds : ∀ who, 0 ≤ values who ∧ values who ≤ 6)
    (alice bob : PublicationResult Bid) (who : Player) :
    -6 ≤ CommitRevealAuction.utility values 6
        (CommitRevealAuction.result (BoundedPaymentAuction.integerPublication alice)
          (BoundedPaymentAuction.integerPublication bob)) who ∧
      CommitRevealAuction.utility values 6
        (CommitRevealAuction.result (BoundedPaymentAuction.integerPublication alice)
          (BoundedPaymentAuction.integerPublication bob)) who ≤ 6 := by
  cases who with
  | alice =>
      cases alice with
      | failure =>
          change (-6 : ℝ) ≤ -6 ∧ (-6 : ℝ) ≤ 6
          norm_num
      | success alice =>
          cases bob with
          | failure =>
              change -6 ≤ values .alice ∧ values .alice ≤ 6
              exact ⟨(by linarith [(bounds .alice).1]), (bounds .alice).2⟩
          | success bob =>
              change -6 ≤ (if bob.val ≤ alice.val then values .alice - (bob.val : ℝ) else 0) ∧
                (if bob.val ≤ alice.val then values .alice - (bob.val : ℝ) else 0) ≤ 6
              have bid : (0 : ℝ) ≤ (bob.val : ℝ) ∧ (bob.val : ℝ) ≤ 6 := by
                exact_mod_cast bob.property
              split_ifs <;> constructor <;> linarith [(bounds .alice).1, (bounds .alice).2]
  | bob =>
      cases bob with
      | failure =>
          change (-6 : ℝ) ≤ -6 ∧ (-6 : ℝ) ≤ 6
          norm_num
      | success bob =>
          cases alice with
          | failure =>
              change -6 ≤ values .bob ∧ values .bob ≤ 6
              exact ⟨(by linarith [(bounds .bob).1]), (bounds .bob).2⟩
          | success alice =>
              change -6 ≤ (if alice.val < bob.val then values .bob - (alice.val : ℝ) else 0) ∧
                (if alice.val < bob.val then values .bob - (alice.val : ℝ) else 0) ≤ 6
              have bid : (0 : ℝ) ≤ (alice.val : ℝ) ∧ (alice.val : ℝ) ≤ 6 := by
                exact_mod_cast alice.property
              split_ifs <;> constructor <;> linarith [(bounds .bob).1, (bounds .bob).2]

theorem utility_bounds (outcome : (Player → Bid) × PublicOutcome program) (who : Player) :
    -6 ≤ utility outcome who ∧ utility outcome who ≤ 6 := by
  rw [utility_eq_economic]
  apply bounded_economic_utility
  intro actor
  exact_mod_cast (outcome.1 actor).property

end Vegas.Examples.BoundedPrivateValueAuction

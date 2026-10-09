/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLatePrefixKernel
import Vegas.Examples.LateOpeningRuntimeAliceFirstWitness
import Interaction.ReactiveSubmissionSerial

/-! # Canonical envelope identity after a nongenuine first submission

Once Alice has authored identifier zero, all her later responses receive a
larger identifier. If its full envelope was nongenuine, the initialized
canonical identifier-zero opening cannot enter any subsequent receiver sample
or ledger. The physical exclusion holds under every later raw policy.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeOpeningIdentity

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeFirstObservation LateOpeningRuntimeLatePrefixKernel

private def ExcludesOpening (bit : Bool) (execution : app.Execution) : Prop :=
  1 ≤ execution.network.nextSerial alice ∧
    execution.network.Satisfies (fun message => message ≠ openingMessage bit)

private theorem excludes_invariant (bit : Bool) (players : Player → app.Policy) :
    app.PolicyInvariant players (ExcludesOpening bit) where
  respond execution who response valid _ := by
    have lower := valid.1
    refine ⟨?_, ?_⟩
    · rw [app.respond_nextSerial]
      omega
    · rcases response with ⟨transmission⟩
      cases transmission with
      | none => exact valid.2
      | some submission =>
          apply valid.2.submit who
          intro same
          have identifier := congrArg Message.id same
          have owner := congrArg Prod.fst identifier
          change who = alice at owner
          subst who
          have serial := congrArg Prod.snd identifier
          change execution.network.nextSerial alice = 0 at serial
          omega
  environment execution next command valid reached := by
    refine ⟨?_, ?_⟩
    · rw [app.environmentStep_nextSerial execution next command reached]
      exact valid.1
    · cases command with
      | wait =>
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact valid.2
      | activate who =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
          obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact valid.2.learn who selected
      | «include» id =>
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          have retained := valid.2.includePending id
          cases found : execution.network.lookup id <;>
            simpa only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found] using retained
      | application command =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact valid.2

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem nongenuine_excludes (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (nongenuine : ¬ LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) :
    ExcludesOpening bit (sent weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨some submission⟩) := by
  refine ⟨by change 1 ≤ 1; decide, ?_⟩
  change (MessageNetwork.empty.submit alice
    (app.packet (app.submit (firstLateDecision bit label).application alice submission) alice
      ((firstLateDecision bit label).network.known alice) submission)).2.Satisfies _
  apply MessageNetwork.Satisfies.empty.submit alice
  intro same
  apply nongenuine
  exact congrArg Message.payload same

def ObservedCanonicalOpening (bit : Bool) (execution : app.Execution) : Prop :=
  openingMessage bit ∈ (execution.observe app bob).messages.leaked ++
    (execution.observe app bob).messages.ledger

private theorem excludes_not_observed {bit : Bool} {execution : app.Execution}
    (valid : ExcludesOpening bit execution) : ¬ ObservedCanonicalOpening bit execution := by
  intro observed
  rcases List.mem_append.mp observed with leaked | ledger
  · exact (valid.2.leaked bob (openingMessage bit) leaked) rfl
  · exact (valid.2.ledger (openingMessage bit) ledger) rfl

/-- Every actual first-late nongenuine packet contributes zero to any full
binding readout event containing the initialized canonical Alice/0 envelope. -/
theorem nongenuine_first_observed_event_zero (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (nongenuine : ¬ LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission)
    (players : Player → app.Policy) (event : Set app.Execution)
    (observed : ∀ final ∈ event, ObservedCanonicalOpening bit final) :
    (firstBindingLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨some submission⟩ players).toOuterMeasure event = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro final reached member
  obtain ⟨before, continued, activated⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have invariant := excludes_invariant bit players
  have retained := invariant.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    7 _ before (nongenuine_excludes weight nonnegative bit label submission nongenuine) continued
  exact excludes_not_observed
    (invariant.environment before final (.activate bob) retained activated) (observed final member)

end Vegas.Examples.LateOpeningRuntimeOpeningIdentity

import Vegas.Examples.Refinement

/-!
# Batch-canonicalizing refinement examples

This module exercises the fact that `projectEventBatch` is independent
refinement data. A backend can retain meaningful pointwise event projections
while canonicalizing whole administrative batches away.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

noncomputable def stutterMachine : Machine PUnit where
  State := PUnit
  Action := fun _ => PUnit
  Internal := PUnit
  Public := PUnit
  Obs := fun _ => PUnit
  Outcome := PUnit
  init := PUnit.unit
  available := fun _ _ => Set.univ
  availableInternal := fun _ => Set.univ
  stepPlay := fun _ _ _ => PMF.pure PUnit.unit
  stepInternal := fun _ _ => PMF.pure PUnit.unit
  terminal := fun _ => False
  publicView := fun _ => PUnit.unit
  observe := fun _ _ => PUnit.unit
  outcome := fun _ => some PUnit.unit
  utility := fun _ _ => 0

theorem stutterMachine_runEventsFrom
    (events : List stutterMachine.Event) (state : stutterMachine.State) :
    stutterMachine.runEventsFrom events state = PMF.pure state := by
  cases state
  induction events with
  | nil => rfl
  | cons event events ih =>
      rw [Machine.runEventsFrom_cons_bind]
      cases event <;> simpa [Machine.step, stutterMachine] using ih

def stutterProjectEvent? :
    stutterMachine.Event → Option stutterMachine.Event := some

/-- This deliberately differs from `filterMap stutterProjectEvent?`: individual
events project pointwise, but whole batches canonicalize stuttering work away. -/
def stutterProjectEventBatch (_batch : List stutterMachine.Event) :
    List stutterMachine.Event := []

noncomputable def stutterBatchRefinement :
    Machine.StochasticRefinement stutterMachine stutterMachine where
  projectState := id
  projectEvent? := stutterProjectEvent?
  projectEventBatch := stutterProjectEventBatch
  projectPublic := id
  projectObs := fun _ => id
  projectOutcome := id
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    cases hproject
    exact havailable
  step_project := by
    intro event source
    cases source
    cases event <;> rw [PMF.map_id] <;> rfl
  eventBatch_project := by
    intro events source
    cases source
    simp [stutterProjectEventBatch, stutterMachine_runEventsFrom,
      PMF.map_id]
  publicView_project := by
    intro state
    cases state
    rfl
  observe_project := by
    intro player state
    cases state
    rfl
  terminal_project := by
    intro state hterminal
    exact hterminal
  terminal_reflect := by
    intro state hterminal
    exact hterminal
  outcome_project := by
    intro state
    cases state
    rfl
  utility_project := by
    intro outcome player
    cases outcome
    cases player
    rfl

example :
    stutterBatchRefinement.projectEventBatch
        [.play PUnit.unit PUnit.unit] = [] := rfl

example :
    (List.filterMap stutterBatchRefinement.projectEvent?
        [.play PUnit.unit PUnit.unit]) =
      [.play PUnit.unit PUnit.unit] := rfl

example :
    stutterBatchRefinement.projectEventBatch
        [.play PUnit.unit PUnit.unit] ≠
      List.filterMap stutterBatchRefinement.projectEvent?
        [.play PUnit.unit PUnit.unit] := by
  simp [stutterBatchRefinement, stutterProjectEventBatch,
    stutterProjectEvent?]

noncomputable def stutterSpecLawFamily :
    stutterMachine.EventBatchLawFamily (fun _ : PUnit => PUnit) where
  law := fun _ _ => PMF.pure []
  legal := by
    intro profile trace hnonterminal batch hbatch
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
    subst batch
    exact ⟨trace.2, Machine.AvailableRunFrom.nil _⟩

noncomputable def stutterImplLawFamily :
    stutterMachine.EventBatchLawFamily (fun _ : PUnit => PUnit) where
  law := fun _ _ => PMF.pure [.play PUnit.unit PUnit.unit]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
    subst batch
    cases trace.2
    refine ⟨PUnit.unit, ?_⟩
    refine
      Machine.AvailableRunFrom.cons ?_ ?_
        (Machine.AvailableRunFrom.nil _)
    · trivial
    · change PUnit.unit ∈ (PMF.pure PUnit.unit).support
      rw [PMF.support_pure]
      exact Set.mem_singleton _

noncomputable def stutterBatchLawLift :
    stutterBatchRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => PUnit) stutterSpecLawFamily where
  impl := stutterImplLawFamily
  compatible := by
    intro profile trace
    change
      PMF.map stutterProjectEventBatch
          (PMF.pure [.play PUnit.unit PUnit.unit]) =
        PMF.pure []
    rw [PMF.pure_map]
    rfl

noncomputable def auditedStutterBatchRefinement :
    Machine.StochasticRefinement (Machine.audited stutterMachine)
      stutterMachine :=
  stutterBatchRefinement.compose
    (Machine.audited.refinement stutterMachine)

noncomputable def auditedStutterBatchLawLift :
    auditedStutterBatchRefinement.EventBatchLawFamilyLift
      (fun _ : PUnit => PUnit) stutterSpecLawFamily :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    stutterBatchLawLift
    (Machine.audited.liftEventBatchLawFamily stutterMachine
      stutterBatchLawLift.impl)

example (profile : ∀ _player : PUnit, PUnit) :
    PMF.map auditedStutterBatchRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            (Machine.audited stutterMachine) (fun _ : PUnit => PUnit)
            auditedStutterBatchLawLift.impl (fun _ => 0) 2).outcomeKernel
          profile) =
      ((Machine.eventBatchTraceKernelGame
          stutterMachine (fun _ : PUnit => PUnit)
          stutterSpecLawFamily (fun _ => 0) 2).outcomeKernel profile) :=
  auditedStutterBatchRefinement.eventBatchTraceKernelGame_projectTrace_eq
    auditedStutterBatchLawLift (fun _ => 0) 2 profile

theorem auditedStutterTraceUtility_bound
    (player : PUnit)
    (trace : (Machine.audited stutterMachine).EventBatchTrace) :
    |Machine.eventBatchTraceUtility (Machine.audited stutterMachine)
        (fun _ => 0) trace player| ≤ 0 := by
  cases player
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨state, audit⟩
  cases state
  simp [Machine.eventBatchTraceUtility, Machine.audited,
    Machine.RoundView.optionOutcomeUtility, stutterMachine]

theorem stutterTraceUtility_bound
    (player : PUnit) (trace : stutterMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility stutterMachine (fun _ => 0)
        trace player| ≤ 0 := by
  cases player
  rcases trace with ⟨batches, state⟩
  cases state
  simp [Machine.eventBatchTraceUtility, stutterMachine,
    Machine.RoundView.optionOutcomeUtility]

theorem stutterSpecGame_nash
    (profile : ∀ _player : PUnit, PUnit) :
    (Machine.eventBatchTraceKernelGame
        stutterMachine (fun _ : PUnit => PUnit)
        stutterSpecLawFamily (fun _ => 0) 2).IsNash profile := by
  intro player alternative
  cases player
  cases alternative
  simp [Machine.eventBatchTraceKernelGame, stutterMachine]

example (profile : ∀ _player : PUnit, PUnit) :
    (Machine.eventBatchTraceKernelGame
        (Machine.audited stutterMachine) (fun _ : PUnit => PUnit)
        auditedStutterBatchLawLift.impl (fun _ => 0) 2).IsNash profile := by
  exact
    auditedStutterBatchRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        auditedStutterBatchLawLift (fun _ => 0) 2
        (CImpl := fun _ => 0) (CSpec := fun _ => 0)
        auditedStutterTraceUtility_bound stutterTraceUtility_bound
        (stutterSpecGame_nash profile)

end Refinement
end Examples
end Vegas

import Vegas.Core.Theorems.Refinement
import Vegas.Examples.MatchingPennies

/-!
# Refinement smoke examples

The identity refinement is the baseline runtime relation for any compiled
machine; concrete backends later prove into the same interface.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

noncomputable def matchingPenniesMachine :
    Machine Vegas.Examples.Player :=
  ToEventGraph.PrimitiveMachine Vegas.Examples.matchingPenniesCompiled

noncomputable def matchingPenniesIdentity :
    Machine.StochasticRefinement matchingPenniesMachine
      matchingPenniesMachine :=
  Machine.StochasticRefinement.refl matchingPenniesMachine

example :
    matchingPenniesIdentity.projectState matchingPenniesMachine.init =
      matchingPenniesMachine.init := by
  rfl

example (state : matchingPenniesMachine.State) :
    Option.map matchingPenniesIdentity.projectOutcome
        (matchingPenniesMachine.outcome state) =
      matchingPenniesMachine.outcome
        (matchingPenniesIdentity.projectState state) :=
  matchingPenniesIdentity.outcome_project state

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    Option.map matchingPenniesIdentity.projectOutcome
        (matchingPenniesMachine.outcome state) =
      some
        (ToEventGraph.sourceOutcomeAtTerminal
          Vegas.Examples.matchingPenniesChecked.core
          (matchingPenniesIdentity.projectState state)
          (by
            have hspec :
                (ToEventGraph.PrimitiveMachine
                  (ToEventGraph.compile
                    Vegas.Examples.matchingPenniesChecked.core)).terminal
                  (matchingPenniesIdentity.projectState state) := by
              simpa [matchingPenniesMachine, matchingPenniesCompiled]
                using matchingPenniesIdentity.terminal_project hterminal
            simpa [ToEventGraph.PrimitiveMachine,
              ToEventGraph.primitiveMachineSpec] using hspec)) := by
  simpa [matchingPenniesMachine, matchingPenniesCompiled] using
    Vegas.Examples.matchingPenniesChecked
      |>.runtimeRefinement_terminalOutcome_project_eq_source
        matchingPenniesIdentity hterminal

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)) :
    WFProgram.RuntimeTraceAdequacy matchingPenniesChecked
      (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)
      matchingPenniesIdentity :=
  Vegas.WFProgram.RuntimeTraceAdequacy.identity law

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)) :
    WFProgram.RuntimeTraceAdequacy matchingPenniesChecked
      (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked)
      (Machine.audited.refinement matchingPenniesMachine) :=
  Vegas.WFProgram.RuntimeTraceAdequacy.audited law

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.pureFrontierTraceSurface matchingPenniesChecked)) :
    WFProgram.RuntimeTraceAdequacy matchingPenniesChecked
      (WFProgram.pureFrontierTraceSurface matchingPenniesChecked)
      (Machine.audited.refinement matchingPenniesMachine) :=
  Vegas.WFProgram.RuntimeTraceAdequacy.audited law

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.mixedPureFrontierTraceSurface matchingPenniesChecked)) :
    WFProgram.RuntimeTraceAdequacy matchingPenniesChecked
      (WFProgram.mixedPureFrontierTraceSurface matchingPenniesChecked)
      (Machine.audited.refinement matchingPenniesMachine) :=
  Vegas.WFProgram.RuntimeTraceAdequacy.audited law

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    (Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame
      (Vegas.WFProgram.RuntimeTraceAdequacy.identity law)).udist
        profile =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  by
    simpa [Vegas.WFProgram.behavioralFrontierTraceSurface] using
      Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame_udist_surface
        (Vegas.WFProgram.RuntimeTraceAdequacy.identity law) profile

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.behavioralFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.BehavioralFrontierProfile) :
    (Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame
      (Vegas.WFProgram.RuntimeTraceAdequacy.audited law)).udist
        profile =
      matchingPenniesChecked.behavioralFrontierGame.udist profile :=
  by
    simpa [Vegas.WFProgram.behavioralFrontierTraceSurface] using
      Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame_udist_surface
        (Vegas.WFProgram.RuntimeTraceAdequacy.audited law) profile

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.pureFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.PureFrontierProfile) :
    (Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame
      (Vegas.WFProgram.RuntimeTraceAdequacy.audited law)).udist
        profile =
      matchingPenniesChecked.pureFrontierGame.udist profile :=
  by
    simpa [Vegas.WFProgram.pureFrontierTraceSurface] using
      Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame_udist_surface
        (Vegas.WFProgram.RuntimeTraceAdequacy.audited law) profile

noncomputable example
    (law :
      WFProgram.TraceSpecEventBatchLaw matchingPenniesChecked
        (WFProgram.mixedPureFrontierTraceSurface matchingPenniesChecked))
    (profile : matchingPenniesChecked.MixedPureFrontierProfile) :
    (Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame
      (Vegas.WFProgram.RuntimeTraceAdequacy.audited law)).udist
        profile =
      matchingPenniesChecked.mixedPureFrontierGame.udist profile :=
  by
    simpa [Vegas.WFProgram.mixedPureFrontierTraceSurface] using
      Vegas.WFProgram.RuntimeTraceAdequacy.implTraceGame_udist_surface
        (Vegas.WFProgram.RuntimeTraceAdequacy.audited law) profile

/-! ## Trace-kernel refinement smoke test -/

noncomputable def unitMachine : Machine PUnit where
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
  terminal := fun _ => True
  publicView := fun _ => PUnit.unit
  observe := fun _ _ => PUnit.unit
  outcome := fun _ => some PUnit.unit
  utility := fun _ _ => 0

noncomputable def unitLawFamily :
    unitMachine.EventBatchLawFamily (fun _ : PUnit => PUnit) where
  law := fun _ _ => PMF.pure []
  legal := by
    intro _profile trace hnonterminal
    exact False.elim (hnonterminal trivial)

noncomputable def unitIdentity :
    Machine.StochasticRefinement unitMachine unitMachine :=
  Machine.StochasticRefinement.refl unitMachine

noncomputable def unitLawLift :
    unitIdentity.EventBatchLawFamilyLift (fun _ : PUnit => PUnit)
      unitLawFamily :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.refl
    unitMachine unitLawFamily

example (profile : ∀ _player : PUnit, PUnit) :
    PMF.map unitIdentity.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            unitMachine (fun _ : PUnit => PUnit)
            unitLawLift.impl (fun _ => 0) 2).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          unitMachine (fun _ : PUnit => PUnit)
          unitLawFamily (fun _ => 0) 2).outcomeKernel profile) :=
  unitIdentity.eventBatchTraceKernelGame_projectTrace_eq
    unitLawLift (fun _ => 0) 2 profile

example (profile : ∀ _player : PUnit, PUnit)
    (hNash :
      (Machine.eventBatchTraceKernelGame
          unitMachine (fun _ : PUnit => PUnit)
          unitLawFamily (fun _ => 0) 2).IsNash profile) :
    (Machine.eventBatchTraceKernelGame
        unitMachine (fun _ : PUnit => PUnit)
        unitLawLift.impl (fun _ => 0) 2).IsNash profile := by
  refine
    unitIdentity.eventBatchTraceKernelGame_nash_pullback_of_bounded
      unitLawLift (fun _ => 0) 2
      (CImpl := fun _ => 0) (CSpec := fun _ => 0) ?_ ?_ hNash
  · intro player trace
    cases player
    rcases trace with ⟨batches, state⟩
    cases state
    simp [Machine.eventBatchTraceUtility, unitMachine,
      Machine.RoundView.optionOutcomeUtility]
  · intro player trace
    cases player
    rcases trace with ⟨batches, state⟩
    cases state
    simp [Machine.eventBatchTraceUtility, unitMachine,
      Machine.RoundView.optionOutcomeUtility]

/-! ## Non-identity encoded-runtime refinement -/

noncomputable def boolSpecMachine : Machine PUnit where
  State := Option Bool
  Action := fun _ => Bool
  Internal := PEmpty
  Public := Option Bool
  Obs := fun _ => Option Bool
  Outcome := Bool
  init := none
  available := fun state _ =>
    match state with
    | none => Set.univ
    | some _ => ∅
  availableInternal := fun _ => ∅
  stepPlay := fun _ action _ => PMF.pure (some action)
  stepInternal := fun event _ => nomatch event
  terminal := fun state => state.isSome = true
  publicView := id
  observe := fun _ => id
  outcome := id
  utility := fun outcome _ => if outcome then 1 else 0

structure EncodedState where
  payload : Option Nat
  audit : Nat
deriving DecidableEq, Repr

def EncodedState.init : EncodedState where
  payload := none
  audit := 0

def EncodedState.project (state : EncodedState) : Option Bool :=
  state.payload.map fun value => value != 0

def EncodedState.publicProject (view : Option Nat × Nat) : Option Bool :=
  view.1.map fun value => value != 0

def encodeBool (value : Bool) : Nat :=
  if value then 1 else 0

def decodeNat (value : Nat) : Bool :=
  value != 0

noncomputable def encodedImplMachine : Machine PUnit where
  State := EncodedState
  Action := fun _ => Bool
  Internal := PUnit
  Public := Option Nat × Nat
  Obs := fun _ => Option Nat × Nat
  Outcome := Nat
  init := EncodedState.init
  available := fun state _ =>
    match state.payload with
    | none => Set.univ
    | some _ => ∅
  availableInternal := fun state =>
    match state.payload with
    | none => Set.univ
    | some _ => ∅
  stepPlay := fun _ action state =>
    PMF.pure { state with payload := some (encodeBool action) }
  stepInternal := fun _ state =>
    PMF.pure { state with audit := state.audit + 1 }
  terminal := fun state => state.payload.isSome = true
  publicView := fun state => (state.payload, state.audit)
  observe := fun _ state => (state.payload, state.audit)
  outcome := fun state => state.payload
  utility := fun outcome _ => if decodeNat outcome then 1 else 0

def encodedProjectEvent? :
    encodedImplMachine.Event → Option boolSpecMachine.Event
  | .play player action => some (.play player action)
  | .internal _ => none

def encodedProjectEventBatch
    (batch : List encodedImplMachine.Event) :
    List boolSpecMachine.Event :=
  batch.filterMap encodedProjectEvent?

noncomputable def encodedRefinement :
    Machine.StochasticRefinement encodedImplMachine boolSpecMachine where
  projectState := EncodedState.project
  projectEvent? := encodedProjectEvent?
  projectEventBatch := encodedProjectEventBatch
  projectPublic := EncodedState.publicProject
  projectObs := fun _ => EncodedState.publicProject
  projectOutcome := decodeNat
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    cases event with
    | play player action =>
        cases hproject
        cases state with
        | mk payload audit =>
            cases payload
            · cases action <;>
                simp [encodedImplMachine, boolSpecMachine,
                  EncodedState.project] at havailable ⊢
            · simp [encodedImplMachine] at havailable
    | internal event =>
        simp [encodedProjectEvent?] at hproject
  step_project := by
    intro event source
    cases event with
    | play player action =>
        cases source with
        | mk payload audit =>
            cases action
            · change
                PMF.map EncodedState.project
                    (PMF.pure
                      ({ payload := some 0, audit := audit } :
                        EncodedState)) =
                  PMF.pure (some false)
              rw [PMF.pure_map]
              rfl
            · change
                PMF.map EncodedState.project
                    (PMF.pure
                      ({ payload := some 1, audit := audit } :
                        EncodedState)) =
                  PMF.pure (some true)
              rw [PMF.pure_map]
              rfl
    | internal event =>
        cases source with
        | mk payload audit =>
            change
              PMF.map EncodedState.project
                  (PMF.pure
                    ({ payload := payload, audit := audit + 1 } :
                      EncodedState)) =
                PMF.pure (EncodedState.project
                  { payload := payload, audit := audit })
            rw [PMF.pure_map]
            rfl
  eventBatch_project := by
    intro events source
    induction events generalizing source with
    | nil =>
        change
          PMF.map EncodedState.project (PMF.pure source) =
            PMF.pure (EncodedState.project source)
        rw [PMF.pure_map]
    | cons event events ih =>
        cases event with
        | play player action =>
            cases source with
            | mk payload audit =>
                cases action
                · simpa [Machine.runEventsFrom_cons_bind, Machine.step,
                    encodedProjectEventBatch, encodedProjectEvent?,
                    encodedImplMachine, boolSpecMachine,
                    EncodedState.project, encodeBool, PMF.map_bind] using
                    ih { payload := some 0, audit := audit }
                · simpa [Machine.runEventsFrom_cons_bind, Machine.step,
                    encodedProjectEventBatch, encodedProjectEvent?,
                    encodedImplMachine, boolSpecMachine,
                    EncodedState.project, encodeBool, PMF.map_bind] using
                    ih { payload := some 1, audit := audit }
        | internal event =>
            cases source with
            | mk payload audit =>
                simpa [Machine.runEventsFrom_cons_bind, Machine.step,
                  encodedProjectEventBatch, encodedProjectEvent?,
                  encodedImplMachine, boolSpecMachine, EncodedState.project,
                  PMF.map_bind] using
                    ih { payload := payload, audit := audit + 1 }
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
    rcases state with ⟨payload, audit⟩
    cases payload <;> simp [encodedImplMachine, boolSpecMachine,
      EncodedState.project] at hterminal ⊢
  terminal_reflect := by
    intro state hterminal
    rcases state with ⟨payload, audit⟩
    cases payload <;> simp [encodedImplMachine, boolSpecMachine,
      EncodedState.project] at hterminal ⊢
  outcome_project := by
    intro state
    cases state
    rfl
  utility_project := by
    intro outcome player
    rfl

example :
    encodedRefinement.projectState
        { payload := some 1, audit := 7 } =
      some true := by
  rfl

example :
    encodedRefinement.projectEventBatch
        [.internal PUnit.unit, .play PUnit.unit true] =
      [.play PUnit.unit true] := by
  rfl

noncomputable def boolSpecLawFamily :
    boolSpecMachine.EventBatchLawFamily (fun _ : PUnit => Bool) where
  law := fun profile _trace =>
    PMF.pure [.play PUnit.unit (profile PUnit.unit)]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
    subst batch
    rcases trace with ⟨batches, state⟩
    cases state with
    | none =>
        exact Machine.AvailableBatchFrom.singleton
          (by simp [boolSpecMachine])
    | some value =>
        exact False.elim (hnonterminal (by simp [boolSpecMachine]))

noncomputable def encodedImplLawFamily :
    encodedImplMachine.EventBatchLawFamily (fun _ : PUnit => Bool) where
  law := fun profile _trace =>
    PMF.pure
      [.internal PUnit.unit, .play PUnit.unit (profile PUnit.unit)]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
    subst batch
    rcases trace with ⟨batches, state⟩
    cases state with
    | mk payload audit =>
        cases payload with
        | none =>
            let src : encodedImplMachine.State :=
              { payload := none, audit := audit }
            let mid : encodedImplMachine.State :=
              { payload := none, audit := audit + 1 }
            change
              encodedImplMachine.AvailableBatchFrom src
                [.internal PUnit.unit,
                  .play PUnit.unit (profile PUnit.unit)]
            refine Machine.AvailableBatchFrom.cons ?_ ?_
            · simp [encodedImplMachine, src]
            · intro mid' hmid'
              change mid' ∈ (PMF.pure mid).support at hmid'
              rw [PMF.support_pure] at hmid'
              subst mid'
              exact Machine.AvailableBatchFrom.singleton
                (by
                  cases profile PUnit.unit <;>
                    simp [encodedImplMachine, mid])
        | some value =>
            exact False.elim (hnonterminal (by simp [encodedImplMachine]))

noncomputable def encodedLawLift :
    encodedRefinement.EventBatchLawFamilyLift (fun _ : PUnit => Bool)
      boolSpecLawFamily where
  impl := encodedImplLawFamily
  compatible := by
    intro profile trace
    change
      PMF.map encodedProjectEventBatch
          (PMF.pure
            [.internal PUnit.unit,
              .play PUnit.unit (profile PUnit.unit)]) =
        PMF.pure [.play PUnit.unit (profile PUnit.unit)]
    rw [PMF.pure_map]
    rfl

example (profile : ∀ _player : PUnit, Bool) :
    PMF.map encodedRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
            encodedImplMachine (fun _ : PUnit => Bool)
            encodedLawLift.impl (fun _ => 0) 2).outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool)
          boolSpecLawFamily (fun _ => 0) 2).outcomeKernel profile) :=
  encodedRefinement.eventBatchTraceKernelGame_projectTrace_eq
    encodedLawLift (fun _ => 0) 2 profile

theorem encodedImplTraceUtility_bound
    (player : PUnit) (trace : encodedImplMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility encodedImplMachine (fun _ => 0)
        trace player| ≤ 1 := by
  cases player
  rcases trace with ⟨batches, state⟩
  rcases state with ⟨payload, audit⟩
  cases payload with
  | none =>
      simp [Machine.eventBatchTraceUtility, encodedImplMachine,
        Machine.RoundView.optionOutcomeUtility]
  | some value =>
      by_cases hdecode : decodeNat value
      · simp [Machine.eventBatchTraceUtility, encodedImplMachine,
          Machine.RoundView.optionOutcomeUtility, hdecode]
      · simp [Machine.eventBatchTraceUtility, encodedImplMachine,
          Machine.RoundView.optionOutcomeUtility, hdecode]

theorem boolSpecTraceUtility_bound
    (player : PUnit) (trace : boolSpecMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility boolSpecMachine (fun _ => 0)
        trace player| ≤ 1 := by
  cases player
  rcases trace with ⟨batches, state⟩
  cases state with
  | none =>
      simp [Machine.eventBatchTraceUtility, boolSpecMachine,
        Machine.RoundView.optionOutcomeUtility]
  | some value =>
      cases value <;>
        simp [Machine.eventBatchTraceUtility, boolSpecMachine,
          Machine.RoundView.optionOutcomeUtility]

example (profile : ∀ _player : PUnit, Bool)
    (hNash :
      (Machine.eventBatchTraceKernelGame
          boolSpecMachine (fun _ : PUnit => Bool)
          boolSpecLawFamily (fun _ => 0) 2).IsNash profile) :
    (Machine.eventBatchTraceKernelGame
        encodedImplMachine (fun _ : PUnit => Bool)
        encodedLawLift.impl (fun _ => 0) 2).IsNash profile := by
  exact
    encodedRefinement.eventBatchTraceKernelGame_nash_pullback_of_bounded
      encodedLawLift (fun _ => 0) 2
      (CImpl := fun _ => 1) (CSpec := fun _ => 1)
      encodedImplTraceUtility_bound boolSpecTraceUtility_bound hNash

end Refinement
end Examples
end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceInformationWait

/-! # Actual waiting likelihood at protected source inputs

The source-compatible witness supplies the actual recalled silent turns and
finite-menu resources. Their timing posterior is the retained timing tail,
so an unrecorded current decision waits with probability exactly `weight`.
The source profile may vary independently of the compatibility witness.

Information-dependent full effective pins add their actual uniform WAIT atom. These
are local response laws, not a source posterior or prescribed-site incentive
claim. A foreign player's waiting likelihood remains in another player's
counterfactual reach weight.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.menu (runtime service.setup) service.leaks
local notation "riskMenu" => service.bounds.riskMenu (runtime service.setup) service.leaks
  service.bound

private theorem sourceCompatibleInfo_opportunity_not_silent
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false) :
    (⟨none⟩ : (app).Action) ∉
      (sourceServiceCanonicalOpportunity service.setup service.leaks service.bound profile who
        event past view).support := by
  obtain ⟨remaining, execution, trace, observed⟩ :=
    service.sourceCompatibleInfo_canonicalHistory who (some (past, view)) compatible
  let canonical := service.bounds.canonicalMenu (runtime service.setup) service.leaks
  have stateInfo : (canonical.information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who trace =
        (app).observe who (some ⟨remaining, some who, execution⟩) :=
    canonical.info (initialLaw service.setup) service.horizon service.scheduler who trace
  have input := stateInfo.symm.trans observed
  have same : (execution.recall who, execution.observe (app) who) = (past, view) := by
    apply Option.some.inj
    simpa only [ReactiveApplication.observe, ↓reduceIte] using input
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  dsimp only at pastEq viewEq
  have actualTurn : execution.application.publicView.ownTurn? who = some event := by
    change (execution.observe (app) who).application.publicView.ownTurn? who = some event
    rw [viewEq]
    exact turn
  have actualUnrecorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall who) event = false := by rw [pastEq]; exact unrecorded
  have fits := service.sourceCompatibleInfo_protected_opportunity who past view compatible event
    turn unrecorded
  rw [← viewEq] at fits
  obtain ⟨atTurn, slots⟩ := retainedCanonicalSlots_history service.bounds
    ⟨remaining, some who, execution⟩ trace who
  have notSilent := sourceServiceDecisionOpportunity_not_silent
    (canonical.toRawTrace (initialLaw service.setup) service.horizon service.scheduler trace)
      atTurn slots event actualTurn actualUnrecorded fits (profile := profile)
  simpa only [pastEq, viewEq] using notSilent

/-- Earlier benign waits do not restore the untouched timing prior: the
actual recalled-tail posterior gives this exact current geometric WAIT mass. -/
theorem sourceCompatibleInfo_geometric_wait_probability
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false)
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1) :
    ((sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
      (geometricTiming service.setup service.horizon weight positive.le small.le) profile who
        past view) ⟨none⟩).toReal = weight := by
  classical
  have witnessed := compatible
  obtain ⟨_witnessProfile, _turns, _timing, _permitted, _effective, history, remaining, execution,
    current, observed, _actual, allClear, _clear⟩ := witnessed
  have trace : ((riskMenu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have stateInfo : ((riskMenu).information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who history.trace = (app).observe who history.state :=
    (riskMenu).info (initialLaw service.setup) service.horizon service.scheduler who
      history.trace
  rw [stateInfo, current] at observed
  have same : (execution.recall who, execution.observe (app) who) = (past, view) := by
    apply Option.some.inj
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  dsimp only at pastEq viewEq
  have actualTurn : execution.application.publicView.ownTurn? who = some event := by
    change (execution.observe (app) who).application.publicView.ownTurn? who = some event
    rw [viewEq]
    exact turn
  have actualUnrecorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall who) event = false := by
    rw [pastEq]
    exact unrecorded
  have notSilent := service.sourceCompatibleInfo_opportunity_not_silent profile who past view
    compatible event turn unrecorded
  rw [← pastEq, ← viewEq] at notSilent ⊢
  rw [sourceServiceDecision_clear_geometric_response service.bounds service.bound profile who
    execution trace allClear event actualUnrecorded actualTurn weight positive small,
    mix_apply_toReal,
    pmf_toReal_eq_zero_iff.mpr notSilent]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, mul_one, mul_zero, add_zero]

/-- Forgetting the finite-menu witness retains the same actual WAIT
likelihood. Local coverage is derived at the compatible input. -/
theorem sourceCompatibleInfo_restricted_geometric_wait_probability
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false)
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1) :
    ((((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
      (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
        (geometricTiming service.setup service.horizon weight positive.le small.le) profile who))
          (some (past, view))).map Subtype.val (some ⟨none⟩)).toReal = weight := by
  have witnessed := compatible
  obtain ⟨_witnessProfile, _turns, _timing, _admitted, _effective, history, remaining, execution,
    current, observed, _actual, _allClear, clear⟩ := witnessed
  have trace : ((riskMenu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have stateInfo : ((riskMenu).information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who history.trace = (app).observe who history.state :=
    (riskMenu).info (initialLaw service.setup) service.horizon service.scheduler who
      history.trace
  rw [stateInfo, current] at observed
  have same : (execution.recall who, execution.observe (app) who) = (past, view) := by
    apply Option.some.inj
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  dsimp only at pastEq viewEq
  have covered : ∀ response ∈ (sourceServiceTurnPolicy service.setup service.leaks service.bound
      service.horizon (geometricTiming service.setup service.horizon weight positive.le small.le)
        profile who past view).support, response ∈ (menu).actions who past view := by
    rw [← pastEq, ← viewEq]
    intro response chosen
    exact service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
      service.bound who _ _
        (sourceServiceTurnPolicy_risk_retained service.bounds service.values service.initialValues
          service.capacity service.bound service.horizon _ profile who permitted
            ⟨remaining, some who, execution⟩ trace clear response chosen)
  have atoms := pmf_map_apply_of_injective
    (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
      (geometricTiming service.setup service.horizon weight positive.le small.le) profile who
        past view) (Option.some_injective (app).Action) ⟨none⟩
  have represented := congrArg (fun law => (law (some (⟨none⟩ : (app).Action))).toReal)
    ((menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon service.scheduler
      who _ past view covered)
  exact represented.trans ((congrArg ENNReal.toReal atoms).trans
    (service.sourceCompatibleInfo_geometric_wait_probability profile who past view compatible
      event turn unrecorded weight positive small))

/-- At an actual protected unrecorded source input, the represented
immediate policy has no WAIT mass, even after earlier benign waits. -/
theorem sourceCompatibleInfo_immediate_wait_probability_zero
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false) :
    (((service.effectiveImmediateComparator profile who (some (past, view))).map Subtype.val)
      (some ⟨none⟩)).toReal = 0 := by
  obtain ⟨remaining, execution, canonicalTrace, observed⟩ :=
    service.sourceCompatibleInfo_canonicalHistory who (some (past, view)) compatible
  let canonical := service.bounds.canonicalMenu (runtime service.setup) service.leaks
  let trace := (service.bounds.canonicalMenu_in_risk (runtime service.setup) service.leaks
    service.bound).trace (initialLaw service.setup) service.horizon service.scheduler canonicalTrace
  have stateInfo : (canonical.information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who canonicalTrace =
        (app).observe who (some ⟨remaining, some who, execution⟩) :=
    canonical.info (initialLaw service.setup) service.horizon service.scheduler who canonicalTrace
  have input := stateInfo.symm.trans observed
  have same : (execution.recall who, execution.observe (app) who) = (past, view) := by
    apply Option.some.inj
    simpa only [ReactiveApplication.observe, ↓reduceIte] using input
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  dsimp only at pastEq viewEq
  have covered : ∀ response ∈ (sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who past view).support, response ∈ (menu).actions who past view := by
    rw [← pastEq, ← viewEq]
    intro response chosen
    exact service.bounds.riskMenu_in_effective (runtime service.setup) service.leaks
      service.bound who _ _
        (sourceServiceImmediatePolicy_risk_retained service.bounds service.values
          service.initialValues service.capacity service.bound profile who permitted
            ⟨remaining, some who, execution⟩ trace response chosen)
  obtain ⟨seenPast, seenView, seen, _identity, clear⟩ :=
    service.sourceCompatibleInfo_clear who (some (past, view)) compatible
  have pairEq := Option.some.inj seen
  have recalledEq := congrArg Prod.fst pairEq
  have observedEq := congrArg Prod.snd pairEq
  dsimp only at recalledEq observedEq
  subst seenPast seenView
  have physical : ((sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who past view) ⟨none⟩).toReal = 0 := by
    rw [sourceServiceImmediatePolicy_at_event clear turn]
    exact pmf_toReal_eq_zero_iff.mpr (service.sourceCompatibleInfo_opportunity_not_silent profile
      who past view compatible event turn unrecorded)
  have atoms := pmf_map_apply_of_injective
    (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who past view)
      (Option.some_injective (app).Action) ⟨none⟩
  have represented := congrArg (fun law => (law (some (⟨none⟩ : (app).Action))).toReal)
    ((menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon service.scheduler
      who _ past view covered)
  exact represented.trans ((congrArg ENNReal.toReal atoms).trans physical)

/-- The genuine information-dependent native pin has its exact WAIT atom.
The native uniform tremble remains in this likelihood, and free continuation
laws have no effect at the prescribed input. -/
theorem sourceCompatibleInfo_information_wait_probability
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ player info, 0 ≤ weight player info)
    (small : ∀ player info, weight player info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player) :
    (((service.completedInformationWaitProfile profile weight nonnegative small delta
      deltaNonnegative deltaSmall continuation who (some (past, view))).map Subtype.val)
        (some ⟨none⟩)).toReal =
      delta * ((((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
        who (some (past, view))).map Subtype.val) (some ⟨none⟩)).toReal +
          (1 - delta) * weight who (some (past, view)) := by
  classical
  have covered : ∀ response ∈ ((app).silentPolicy past view).support,
      response ∈ (menu).actions who past view := by
    intro response chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact service.bounds.canonicalActions_effective (runtime service.setup) service.leaks
      who past view (service.bounds.silence_canonical (runtime service.setup)
        service.leaks who past view)
  have silent := (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
    service.scheduler who (app).silentPolicy past view covered
  have wait : (((((menu).restrictPolicy (initialLaw service.setup) service.horizon
      service.scheduler who (app).silentPolicy) (some (past, view))).map Subtype.val)
        (some ⟨none⟩)).toReal = 1 := by
    have atoms := congrArg (fun law => (law (some (⟨none⟩ : (app).Action))).toReal) silent
    simpa only [ReactiveApplication.silentPolicy, PMF.pure_map, PMF.pure_apply,
      ↓reduceIte, ENNReal.toReal_one] using atoms
  rw [completedInformationWaitProfile, ite_eq_left compatible, mix_map, mix_apply_toReal,
    mix_map, mix_apply_toReal, wait,
    service.sourceCompatibleInfo_immediate_wait_probability_zero profile who permitted past view
      compatible event turn unrecorded]
  simp only [mul_one, mul_zero, add_zero]

end Vegas.AsyncServiceSpec

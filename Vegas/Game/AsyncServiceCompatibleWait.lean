/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServicePrescribedCompletion

/-! # Actual waiting likelihood at protected source inputs

The source-compatible witness supplies the actual recalled silent turns and
finite-menu resources. Their timing posterior is the retained timing tail,
so an unrecorded current decision waits with probability exactly `weight`.
The source profile may vary independently of the compatibility witness.

Native uniform trembles add their actual WAIT atom to this likelihood. These
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
local notation "menu" => service.bounds.riskMenu (runtime service.setup) service.leaks
  service.bound

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
  have trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have stateInfo : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who history.trace = (app).observe who history.state :=
    (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
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
  have fits := service.sourceCompatibleInfo_protected_opportunity who _ _ compatible event
    turn unrecorded
  rw [← viewEq] at fits
  obtain ⟨canonical, _sameTrace⟩ := service.bounds.riskTrace_canonical_of_persistentClear
    (runtime service.setup) service.leaks service.bound (initialLaw service.setup) service.horizon
      service.scheduler trace (by
        intro control equal player
        cases Option.some.inj equal
        exact allClear player)
  obtain ⟨atTurn, slots⟩ := retainedCanonicalSlots_history service.bounds
    ⟨remaining, some who, execution⟩ canonical who
  have notSilent := sourceServiceDecisionOpportunity_not_silent
    ((menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler trace)
      atTurn slots event actualTurn actualUnrecorded fits (profile := profile)
  rw [← pastEq, ← viewEq]
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
  have trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have stateInfo : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).infoOf who history.trace = (app).observe who history.state :=
    (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
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
    exact sourceServiceTurnPolicy_risk_retained service.bounds service.values service.initialValues
      service.capacity service.bound service.horizon _ profile who permitted
        ⟨remaining, some who, execution⟩ trace clear
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

/-- The actual fully supported native pin retains its uniform WAIT atom as
well as the geometric WAIT likelihood; neither term is dropped from Bayes. -/
theorem sourceCompatibleInfo_uniform_geometric_wait_probability
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false)
    (weight : ℝ) (positive : 0 < weight) (small : weight < 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1) :
    ((mix delta deltaNonnegative deltaSmall
      ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler who
        (some (past, view)))
      (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound service.horizon
          (geometricTiming service.setup service.horizon weight positive.le small.le) profile who))
            (some (past, view)))).map Subtype.val (some ⟨none⟩)).toReal =
      delta * ((((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
        who (some (past, view))).map Subtype.val) (some ⟨none⟩)).toReal +
          (1 - delta) * weight := by
  rw [mix_map, mix_apply_toReal,
    service.sourceCompatibleInfo_restricted_geometric_wait_probability profile who permitted
      past view compatible event turn unrecorded weight positive small]

end Vegas.AsyncServiceSpec

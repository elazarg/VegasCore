/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceCounterfactualBeliefs
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveRecallEntries
import Vegas.Pending.ReactiveServiceRecall

/-! # Source compatibility of actual earlier own decision inputs

A compatible current input has an initialized physical source-policy witness.
Every recalled earlier input is compatible too: persistent clarity propagates
backward through the actual rounds, and recording a response makes its full
preceding opportunity clear. The proof retains the same source policy and
timing, including benign waits. It does not condition away foreign waiting.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.riskMenu (runtime service.setup) service.leaks
  service.bound
local notation "canonical" => service.bounds.canonicalMenu (runtime service.setup) service.leaks

private def CompatibleRecall (who : Player) (past : List (app).PlayerEntry) : Prop :=
  ∀ index entry, past[index]? = some entry →
    service.sourceCompatibleInfo who (some (past.take index, entry.beforeView))

private theorem compatibleRecall_snoc (who : Player) (past : List (app).PlayerEntry)
    (entry : (app).PlayerEntry) (prior : service.CompatibleRecall who past)
    (current : service.sourceCompatibleInfo who (some (past, entry.beforeView))) :
    service.CompatibleRecall who (past ++ [entry]) := by
  intro index found recorded
  by_cases earlier : index < past.length
  · rw [List.getElem?_append_left earlier] at recorded
    rw [List.take_append_of_le_length earlier.le]
    exact prior index found recorded
  · have after : past.length ≤ index := Nat.le_of_not_gt earlier
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at recorded
    cases extra with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at recorded
        subst found
        simpa only [Nat.add_zero, List.take_append_of_le_length (le_refl past.length),
          List.take_length] using current
    | succ extra => simp at recorded

private theorem sourcePolicy_canonical_admissible
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (turns : Nat) (timing : TurnTiming service.setup turns) (who : Player) :
    (canonical).Admissible (initialLaw service.setup) service.horizon service.scheduler who
      (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile who)
      := by
  intro control trace _ response chosen
  exact sourceServiceTurnPolicy_retained service.bounds service.values service.initialValues
    service.capacity service.bound turns timing profile who (permitted who) control trace response
    chosen

private theorem roundsFrom_compatibleRecall
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (count : Nat) (within : count ≤ service.horizon)
    (execution : (app).Execution)
    (reached : execution ∈ ((app).roundsFrom (initialLaw service.setup) service.scheduler
      (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile)
        count).support)
    (clear : ∀ who, (runtime service.setup).persistentServiceRisk service.leaks service.bound who
      (execution.recall who) (execution.observe (app) who) = false) :
    ∀ who, service.CompatibleRecall who (execution.recall who) := by
  let players := sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
    profile
  have admitted := service.sourcePolicy_canonical_admissible profile permitted turns timing
  induction count generalizing execution with
  | zero =>
      obtain ⟨initial, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro who index entry recorded
      change ([] : List (app).PlayerEntry)[index]? = some entry at recorded
      simp only [List.getElem?_nil] at recorded
      cases recorded
  | succ count ih =>
      rw [(app).roundsFrom_succ] at reached
      obtain ⟨prior, priorReached, stepped⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ stepped)
      obtain ⟨middle, moved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have recallEq := (app).environmentStep_recall prior middle command moved
      cases active : command.actor? (app) with
      | none =>
          change execution ∈ ((app).resume players (command.actor? (app)) middle).support
            at resumed
          rw [active] at resumed
          cases (PMF.mem_support_pure_iff _ _).mp resumed
          have priorClear (who : Player) :=
            (runtime service.setup).persistentServiceRisk_clear_before_environment service.leaks
              service.bound who (clear who) moved
          have old := ih (by omega) prior priorReached priorClear
          intro who
          rw [recallEq]
          exact old who
      | some actor =>
          change execution ∈ ((app).resume players (command.actor? (app)) middle).support
            at resumed
          rw [active] at resumed
          obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ resumed
          have middleClear (who : Player) :=
            (runtime service.setup).persistentServiceRisk_clear_before_respond service.leaks
              service.bound middle actor who response (clear who)
          have actorClear := (runtime service.setup).serviceRisk_clear_before_respond
            service.leaks service.bound middle actor response (clear actor)
          have priorClear (who : Player) :=
            (runtime service.setup).persistentServiceRisk_clear_before_environment service.leaks
              service.bound who (middleClear who) moved
          have old := ih (by omega) prior priorReached priorClear
          obtain ⟨priorTrace⟩ := (canonical).trace_roundsFrom_of_admissible
            (initialLaw service.setup) service.horizon service.scheduler players admitted count
              (by omega) prior priorReached
          have remaining : service.horizon - count =
              (service.horizon - (count + 1)) + 1 := by omega
          rw [remaining] at priorTrace
          obtain ⟨pending⟩ := (canonical).trace_environment (initialLaw service.setup)
            service.horizon service.scheduler (service.horizon - (count + 1)) prior middle
              command priorTrace selected moved
          rw [active] at pending
          let riskTrace := (service.bounds.canonicalMenu_in_risk (runtime service.setup)
            service.leaks service.bound).trace (initialLaw service.setup) service.horizon
              service.scheduler pending
          let history : ((menu).protocol (initialLaw service.setup) service.horizon
            service.scheduler).History := ⟨_, riskTrace⟩
          have atInput :
              ((menu).information (initialLaw service.setup) service.horizon
                service.scheduler).infoOf actor history.trace =
                some (middle.recall actor, middle.observe (app) actor) := by
            have observed :
                ((menu).information (initialLaw service.setup) service.horizon
                  service.scheduler).infoOf actor history.trace =
                    (app).observe actor history.state :=
              (menu).info (initialLaw service.setup) service.horizon service.scheduler actor
                history.trace
            exact observed.trans (by
              simp only [history, ReactiveApplication.observe, ↓reduceIte])
          have actual : (app).RoundSupported (initialLaw service.setup) service.horizon
              service.scheduler players history.state := by
            have length := (app).roundsFrom_recall (initialLaw service.setup) service.scheduler
              players count prior priorReached
            have advanced : middle.environmentRecall.length = count + 1 := by
              obtain ⟨updated, _, same⟩ := PMF.support_map .. ▸ moved
              cases same
              change (prior.environmentRecall ++ [_]).length = _
              simp only [List.length_append, List.length_singleton, length]
            refine ⟨?_, count, prior, command, advanced, priorReached, selected, active, moved⟩
            change middle.environmentRecall.length + (service.horizon - (count + 1)) = _
            rw [advanced]
            omega
          have compatible : service.sourceCompatibleInfo actor
              (some (middle.recall actor, middle.observe (app) actor)) :=
            ⟨profile, turns, timing, permitted, effective, history,
              service.horizon - (count + 1), middle, rfl, atInput, actual, middleClear, actorClear⟩
          intro who
          by_cases same : who = actor
          · subst who
            obtain ⟨entry, appended, seen, _⟩ := (runtime service.setup).response_recall_entry
              service.leaks middle actor response
            rw [appended]
            apply service.compatibleRecall_snoc actor (middle.recall actor) entry
            · rw [recallEq]
              exact old actor
            · rw [seen]
              exact compatible
          · rw [(app).respond_recall_other middle actor who same response, recallEq]
            exact old who

/-- Every earlier own decision recorded at compatible information is itself
compatible, with its exact preceding recall and view. Arbitrarily many benign
waits and intervening foreign decisions are retained. -/
theorem sourceCompatibleInfo_recalled_input (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (index : Nat) (entry : (app).PlayerEntry) (recorded : past[index]? = some entry) :
    service.sourceCompatibleInfo who (some (past.take index, entry.beforeView)) := by
  obtain ⟨profile, turns, timing, permitted, effective, history, remaining, execution,
    current, observed, actual, allClear, _clear⟩ := compatible
  have atState :
      ((menu).information (initialLaw service.setup) service.horizon
        service.scheduler).infoOf who history.trace = (app).observe who history.state :=
    (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
  have sameInput : some (execution.recall who, execution.observe (app) who) =
      some (past, view) := by
    have input := atState.symm.trans observed
    rw [current] at input
    simpa only [ReactiveApplication.observe, ↓reduceIte] using input
  have pastEq : execution.recall who = past := congrArg Prod.fst (Option.some.inj sameInput)
  rw [current] at actual
  obtain ⟨accounted, count, prior, command, position, priorReached, _selected, _active, moved⟩ :=
    actual
  have priorClear (player : Player) :=
    (runtime service.setup).persistentServiceRisk_clear_before_environment service.leaks
      service.bound player (allClear player) moved
  have priorFacts := service.roundsFrom_compatibleRecall profile permitted effective turns timing
    count (by omega) prior priorReached priorClear who
  have recalls := (app).environmentStep_recall prior execution command moved
  rw [← pastEq, recalls] at recorded ⊢
  exact priorFacts index entry recorded

/-- Every information value in the focal own-action record lies in the
prescribed classifier. This includes preceding WAIT inputs at their original
views, rather than restarting a timing prior at the current input. -/
theorem sourceCompatibleInfo_ownPlay (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (input : (app).Info) (action : (app).Action)
    (member : (input, action) ∈ (app).recallOwnPlay past) :
    service.sourceCompatibleInfo who input := by
  obtain ⟨index, entry, recorded, seen⟩ := (app).ownPlayFrom_recorded_input [] past input action
    member
  simp only [List.nil_append] at seen
  rw [seen]
  exact service.sourceCompatibleInfo_recalled_input who past view compatible index entry recorded

/-- Completing behavior away from compatible inputs leaves the focal's
entire recorded likelihood unchanged at a compatible site. Foreign response
likelihoods are not identified or removed by this statement. -/
theorem sourceCompatibleInfo_recalledOwnReach_eq
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (first second : ∀ who,
      ((responseMenu).information (initialLaw service.setup) service.horizon
        service.scheduler).BehavioralPolicy who)
    (who : Player)
    (site : ((responseMenu).information (initialLaw service.setup) service.horizon
      service.scheduler).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (agrees : ∀ input, service.sourceCompatibleInfo who input →
      first who input = second who input) :
    service.recalledOwnReach responseMenu first who site =
      service.recalledOwnReach responseMenu second who site := by
  obtain ⟨past, view, seen, _identity, _clear⟩ := service.sourceCompatibleInfo_clear who site.1
    compatible
  unfold recalledOwnReach
  rw [seen]
  apply InformationModel.ownPlayReachProbability_congr
  intro entry member
  exact agrees entry.1 (service.sourceCompatibleInfo_ownPlay who past view (seen ▸ compatible)
    entry.1 entry.2 member)

end Vegas.AsyncServiceSpec

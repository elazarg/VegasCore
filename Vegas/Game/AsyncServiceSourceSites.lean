/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceFirstTurnProfile
import Vegas.Pending.ReactiveCleanPrefix

/-! # Native information compatible with protected source execution

The classifier uses an initialized turn-counted source execution with any
timing, retaining earlier silent responses in actual own recall. Its witness
has a legal risk-menu history, clear persistent risk for every owner and a
clear current owner opportunity. The property depends on the information
value, rather than on which hidden history currently realizes it.

Every decision visited by exact first-turn initialized play is classified.
The classifier does not fix off-path strategy laws: those must be limits of
the timing approximants. Posterior comparison with escaped branches and
source-information transport remain separate obligations. This is a proof classifier,
not a runtime gate or a sequential-equilibrium assertion.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- A native information value has an actual protected source-execution
witness. Any timing is allowed, so the definition retains benign deferrals. -/
def sourceCompatibleInfo (who : Player) (info : (application service.setup service.leaks).Info) :
    Prop :=
  ∃ (profile : BehavioralProfile service.setup.program) (turns : Nat)
    (timing : TurnTiming service.setup turns),
    (∀ player, (profile player).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) ∧
    (∀ player, (profile player).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context)) ∧
    ∃ (history : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
      (remaining : Nat) (execution : (application service.setup service.leaks).Execution),
      history.state = some ⟨remaining, some who, execution⟩ ∧
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who history.trace =
          info ∧
      (application service.setup service.leaks).RoundSupported (initialLaw service.setup)
        service.horizon service.scheduler
        (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile)
          history.state ∧
      (∀ player, (runtime service.setup).persistentServiceRisk service.leaks service.bound player
        (execution.recall player)
        (execution.observe (application service.setup service.leaks) player) = false) ∧
      (runtime service.setup).serviceRisk service.leaks service.bound who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who) = false

/-- Compatibility is stronger than local clarity. Its witness supplies the
same recalled input and clear current opportunity throughout the information
fiber, without revealing the witness to the player. -/
theorem sourceCompatibleInfo_clear (who : Player)
    (info : (application service.setup service.leaks).Info)
    (compatible : service.sourceCompatibleInfo who info) :
    ∃ past view, info = some (past, view) ∧
      view.application.who = who ∧
      (runtime service.setup).serviceRisk service.leaks service.bound who past view = false := by
  obtain ⟨_profile, _turns, _timing, _permitted, _effective, history, remaining, execution,
    current, observed, _actual, _allClear, clear⟩ := compatible
  refine ⟨execution.recall who, execution.observe (application service.setup service.leaks) who,
    observed.symm.trans ?_, rfl, clear⟩
  have atState :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who history.trace =
      (application service.setup service.leaks).observe who history.state :=
    (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).info
      (initialLaw service.setup) service.horizon service.scheduler who history.trace
  refine atState.trans ?_
  rw [current]
  simp only [ReactiveApplication.observe, ↓reduceIte]

/-- Public misses cannot be hidden by the source-compatible classifier.
Every owner has an unmarked public record at this information value, even
though another owner's recalled opportunity or submission risk may be hidden. -/
theorem sourceCompatibleInfo_no_public_miss (who : Player)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view))) (player : Player) :
    view.application.publicView.missedDecisionBy player = false := by
  obtain ⟨_profile, _turns, _timing, _permitted, _effective, history, remaining, execution,
    current, observed, _actual, allClear, _clear⟩ := compatible
  have atState :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who history.trace =
      (application service.setup service.leaks).observe who history.state :=
    (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).info
      (initialLaw service.setup) service.horizon service.scheduler who history.trace
  have input :
      some (execution.recall who, execution.observe (application service.setup service.leaks) who) =
        some (past, view) := by
    rw [atState, current] at observed
    simpa only [ReactiveApplication.observe, ↓reduceIte] using observed
  have sameView := congrArg Prod.snd (Option.some.inj input)
  dsimp only at sameView
  rw [← sameView]
  exact ((runtime service.setup).persistentServiceRisk_clear_iff service.leaks service.bound
    player (execution.recall player)
      (execution.observe (application service.setup service.leaks) player)).mp (allClear player)
    |>.1.1

/-- At a source-compatible unrecorded owned turn, the actual inclusion
window is protected, for either kind of strategic decision. -/
theorem sourceCompatibleInfo_protected_opportunity (who : Player)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false) :
    view.application.publicView.InclusionFitsDeadline (runtime service.setup) service.bound
      event := by
  obtain ⟨seenPast, seenView, same, identity, clear⟩ :=
    service.sourceCompatibleInfo_clear who _ compatible
  have pairEq := Option.some.inj same
  have pastEq := congrArg Prod.fst pairEq
  have viewEq := congrArg Prod.snd pairEq
  dsimp only at pastEq viewEq
  subst seenPast seenView
  exact (runtime service.setup).serviceRisk_clear_protected_opportunity service.leaks
    service.bound who past view event identity turn unrecorded clear

/-- A compatible information value has a legal canonical decision history.
The conversion keeps its actual state and complete recalled input. -/
theorem sourceCompatibleInfo_canonicalHistory (who : Player)
    (info : (application service.setup service.leaks).Info)
    (compatible : service.sourceCompatibleInfo who info) :
    ∃ (remaining : Nat) (execution : (application service.setup service.leaks).Execution)
      (trace : ((service.bounds.canonicalMenu (runtime service.setup) service.leaks).protocol
        (initialLaw service.setup) service.horizon service.scheduler).Trace
          (some ⟨remaining, some who, execution⟩)),
      ((service.bounds.canonicalMenu (runtime service.setup) service.leaks).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who trace = info := by
  obtain ⟨_profile, _turns, _timing, _permitted, _effective, history, remaining, execution,
    current, observed, _actual, allClear, _clear⟩ := compatible
  have riskTrace :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).protocol
        (initialLaw service.setup) service.horizon service.scheduler).Trace
          (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  obtain ⟨canonical, _sameTrace⟩ := service.bounds.riskTrace_canonical_of_persistentClear
    (runtime service.setup) service.leaks service.bound (initialLaw service.setup) service.horizon
    service.scheduler riskTrace (by
      intro control same player
      cases Option.some.inj same
      exact allClear player)
  refine ⟨remaining, execution, canonical, ?_⟩
  have atState :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who history.trace =
      (application service.setup service.leaks).observe who history.state :=
    (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).info
      (initialLaw service.setup) service.horizon service.scheduler who history.trace
  have canonicalInfo :
      ((service.bounds.canonicalMenu (runtime service.setup) service.leaks).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who canonical =
      (application service.setup service.leaks).observe who
        (some ⟨remaining, some who, execution⟩) :=
    (service.bounds.canonicalMenu (runtime service.setup) service.leaks).info
      (initialLaw service.setup) service.horizon service.scheduler who canonical
  exact canonicalInfo.trans ((congrArg ((application service.setup service.leaks).observe who)
    current).symm.trans (atState.symm.trans observed))

/-- Exact initialized first-turn play visits only source-compatible native
decision inputs. The witness is independent of any later completion policy. -/
theorem firstTurnProfile_sourceCompatibleInfo (turns : Nat)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ player, (profile player).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ player, (profile player).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (fuel : Nat)
    (history :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).protocol
        (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
          (service.firstTurnProfile turns profile) fuel).support)
    (who : Player)
    (active :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).protocol
        (initialLaw service.setup) service.horizon service.scheduler).active history.state who) :
    service.sourceCompatibleInfo who
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who
          history.trace) := by
  have actual := service.firstTurnProfile_initialized_roundSupported turns profile permitted
    fuel history reached
  have atState :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who history.trace =
      (application service.setup service.leaks).observe who history.state :=
    (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).info
      (initialLaw service.setup) service.horizon service.scheduler who history.trace
  suffices service.sourceCompatibleInfo who
      ((application service.setup service.leaks).observe who history.state) from
    atState.symm ▸ this
  cases current : history.state with
  | none =>
      rw [current] at active
      cases active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [current] at active
      change actor = some who at active
      subst actor
      have clear (player : Player) :
          (runtime service.setup).serviceRisk service.leaks service.bound player
            (execution.recall player)
            (execution.observe (application service.setup service.leaks) player) = false :=
        sourceServiceFirstTurn_serviceRisk_clear_roundSupported service.contract service.timely
          _ player turns profile rfl _ (current ▸ actual)
      refine ⟨profile, turns, firstTurnTiming service.setup turns, permitted, effective,
        history, remaining, execution, current, ?_, actual, ?_, clear who⟩
      · exact atState.trans (congrArg ((application service.setup service.leaks).observe who)
          current)
      · intro player
        exact ((runtime service.setup).serviceRisk_clear_iff service.leaks service.bound player
          _ _).mp (clear player) |>.1

end Vegas.AsyncServiceSpec

import Vegas.Examples.TwoPlayerMessageProtocol

/-!
# Pending-message conditioning

Property boundary: this file proves a concrete pending-message-conditioned
Nash equilibrium, showing that front-running-style conditioning is modeled
rather than erased.

This fixture models the first strategic feature needed for frontrunning:
a player may condition on messages that are in flight before the runtime
delivers them.  The machine is still the concrete `messageInFlight` wrapper;
the difference from `TwoPlayerMessageProtocol` is the strategy space and law
family at the trace-game frontier.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

/-- A pending-message strategy has a public message coordinate and an action
rule that may inspect the current in-flight buffer.  In the frontrunning
fixture below row's rule is unused; column's rule is applied before delivery. -/
abbrev PendingFrontrunStrategy (_player : TalkPlayer) :=
  Bool × (List (Sigma (fun _ : TalkPlayer => Bool)) → Bool)

def pendingTalkMessage? (player : TalkPlayer) :
    List (Sigma (fun _ : TalkPlayer => Bool)) → Option Bool :=
  deliveredTalkMessage? player

def pendingTalkMessage
    (pending : List (Sigma (fun _ : TalkPlayer => Bool)))
    (player : TalkPlayer) : Bool :=
  (pendingTalkMessage? player pending).getD false

def pendingRowSignal
    (pending : List (Sigma (fun _ : TalkPlayer => Bool))) : Bool :=
  pendingTalkMessage pending TalkPlayer.row

def pendingFrontrunRowMessage
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player) :
    Bool :=
  (profile TalkPlayer.row).1

def pendingFrontrunColAction
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player)
    (pending : List (Sigma (fun _ : TalkPlayer => Bool))) : Bool :=
  (profile TalkPlayer.col).2 pending

/-- Row sends a message.  Before that message is delivered, column chooses its
underlying coordination action from the pending buffer.  The runtime then
delivers the row message, and row commits to the same bit it sent. -/
noncomputable def pendingFrontrunLaw
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player) :
    coordinationMessageMachine.EventBatchLaw :=
  fun trace =>
    match trace.2.source.rowAction, trace.2.source.colAction,
        trace.2.pending with
    | none, none, [] =>
        PMF.pure
          [.play TalkPlayer.row
            (.send (pendingFrontrunRowMessage profile))]
    | none, none, _ :: _ =>
        PMF.pure
          [.play TalkPlayer.col
            (.spec (pendingFrontrunColAction profile trace.2.pending))]
    | none, some _, _ :: _ =>
        PMF.pure [.internal .deliver]
    | none, some _, [] =>
        PMF.pure
          [.play TalkPlayer.row
            (.spec (pendingFrontrunRowMessage profile))]
    | some _, _, _ =>
        PMF.pure []

noncomputable def pendingFrontrunLawFamily :
    coordinationMessageMachine.EventBatchLawFamily PendingFrontrunStrategy where
  law := pendingFrontrunLaw
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨source, pending, delivered⟩
    rcases source with ⟨rowAction, colAction⟩
    cases rowAction with
    | some rowAction =>
        have hbatch_eq : batch = [] := by
          cases colAction <;> cases pending <;>
            simpa [pendingFrontrunLaw] using hbatch
        subst batch
        exact
          ⟨{ source := { rowAction := some rowAction,
                         colAction := colAction },
              pending := pending,
              delivered := delivered },
            Machine.AvailableRunFrom.nil _⟩
    | none =>
        cases colAction with
        | none =>
            cases pending with
            | nil =>
                have hbatch_eq :
                    batch =
                      [.play TalkPlayer.row
                        (.send (pendingFrontrunRowMessage profile))] := by
                  simpa [pendingFrontrunLaw] using hbatch
                subst batch
                let sent : Sigma (fun _ : TalkPlayer => Bool) :=
                  ⟨TalkPlayer.row, pendingFrontrunRowMessage profile⟩
                let src : coordinationMessageMachine.State :=
                  { source := { rowAction := none, colAction := none },
                    pending := [],
                    delivered := delivered }
                let dst : coordinationMessageMachine.State :=
                  { source := { rowAction := none, colAction := none },
                    pending := [sent],
                    delivered := delivered }
                refine ⟨dst, ?_⟩
                change
                  coordinationMessageMachine.AvailableRunFrom src
                    [.play TalkPlayer.row
                      (.send (pendingFrontrunRowMessage profile))] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.send
                    (pendingFrontrunRowMessage profile) ∈
                    coordinationMessageMachine.available src TalkPlayer.row
                  exact hnonterminal
                · change dst ∈ (PMF.pure dst).support
                  rw [PMF.support_pure]
                  exact Set.mem_singleton _
            | cons message rest =>
                let action := pendingFrontrunColAction profile (message :: rest)
                have hbatch_eq :
                    batch =
                      [.play TalkPlayer.col (.spec action)] := by
                  simpa [pendingFrontrunLaw, action,
                    pendingFrontrunColAction] using hbatch
                subst batch
                let src : coordinationMessageMachine.State :=
                  { source := { rowAction := none, colAction := none },
                    pending := message :: rest,
                    delivered := delivered }
                let dst : coordinationMessageMachine.State :=
                  { source := { rowAction := none,
                                colAction := some action },
                    pending := message :: rest,
                    delivered := delivered }
                let finalSource : CoordinationState :=
                  { rowAction := none, colAction := some action }
                let restore
                    (sourceValue : CoordinationState) :
                    coordinationMessageMachine.State :=
                  { source := sourceValue,
                    pending := message :: rest,
                    delivered := delivered }
                refine ⟨dst, ?_⟩
                change
                  coordinationMessageMachine.AvailableRunFrom src
                    [.play TalkPlayer.col (.spec action)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.spec action ∈
                    coordinationMessageMachine.available src TalkPlayer.col
                  change action ∈
                    coordinationMachine.available src.source TalkPlayer.col
                  change action ∈ Set.univ
                  exact Set.mem_univ action
                · change dst ∈
                    (PMF.map restore (PMF.pure finalSource)).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
        | some colAction =>
            cases pending with
            | nil =>
                let action := pendingFrontrunRowMessage profile
                have hbatch_eq :
                    batch =
                      [.play TalkPlayer.row (.spec action)] := by
                  simpa [pendingFrontrunLaw, action] using hbatch
                subst batch
                let src : coordinationMessageMachine.State :=
                  { source := { rowAction := none,
                                colAction := some colAction },
                    pending := [],
                    delivered := delivered }
                let dst : coordinationMessageMachine.State :=
                  { source := { rowAction := some action,
                                colAction := some colAction },
                    pending := [],
                    delivered := delivered }
                let finalSource : CoordinationState :=
                  { rowAction := some action,
                    colAction := some colAction }
                let restore
                    (sourceValue : CoordinationState) :
                    coordinationMessageMachine.State :=
                  { source := sourceValue,
                    pending := [],
                    delivered := delivered }
                refine ⟨dst, ?_⟩
                change
                  coordinationMessageMachine.AvailableRunFrom src
                    [.play TalkPlayer.row (.spec action)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.spec action ∈
                    coordinationMessageMachine.available src TalkPlayer.row
                  change action ∈
                    coordinationMachine.available src.source TalkPlayer.row
                  change action ∈ Set.univ
                  exact Set.mem_univ action
                · change dst ∈
                    (PMF.map restore (PMF.pure finalSource)).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
            | cons message rest =>
                have hbatch_eq :
                    batch = [.internal .deliver] := by
                  simpa [pendingFrontrunLaw] using hbatch
                subst batch
                let src : coordinationMessageMachine.State :=
                  { source := { rowAction := none,
                                colAction := some colAction },
                    pending := message :: rest,
                    delivered := delivered }
                let dst : coordinationMessageMachine.State :=
                  { source := { rowAction := none,
                                colAction := some colAction },
                    pending := rest,
                    delivered := delivered ++ [message] }
                refine ⟨dst, ?_⟩
                change
                  coordinationMessageMachine.AvailableRunFrom src
                    [.internal .deliver] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightInternal.deliver ∈
                    coordinationMessageMachine.availableInternal src
                  change src.pending ≠ [] ∧
                    ¬ coordinationMachine.terminal src.source
                  constructor
                  · change message :: rest ≠ []
                    intro hnil
                    cases hnil
                  · exact hnonterminal
                · change dst ∈ (PMF.pure dst).support
                  rw [PMF.support_pure]
                  exact Set.mem_singleton _

noncomputable abbrev pendingFrontrunTraceGame : KernelGame TalkPlayer :=
  Machine.eventBatchTraceKernelGame
    coordinationMessageMachine PendingFrontrunStrategy
    pendingFrontrunLawFamily (fun _ => 0) 4

theorem pendingFrontrunTrace_after_two
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player) :
    PMF.map
        (fun trace =>
          (trace.2.pending, trace.2.delivered, trace.2.source.rowAction,
            trace.2.source.colAction))
        (coordinationMessageMachine.eventBatchTraceDist
          (pendingFrontrunLaw profile) 2) =
      PMF.pure
        ([⟨TalkPlayer.row, pendingFrontrunRowMessage profile⟩], [],
          none,
          some
            (pendingFrontrunColAction profile
              [⟨TalkPlayer.row, pendingFrontrunRowMessage profile⟩])) := by
  simp [Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
    pendingFrontrunLaw, coordinationMessageMachine, Machine.messageInFlight,
    coordinationMachine, Machine.runEventBatchesFrom,
    Machine.runEventsFrom, Machine.step, CoordinationState.init,
    CoordinationState.setAction, CoordinationState.action?,
    pendingFrontrunRowMessage, pendingFrontrunColAction, PMF.pure_map]

theorem pendingFrontrunTraceGame_eu_four
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player)
    (player : TalkPlayer) :
    pendingFrontrunTraceGame.eu profile player =
      if pendingFrontrunRowMessage profile =
          pendingFrontrunColAction profile
            [⟨TalkPlayer.row, pendingFrontrunRowMessage profile⟩]
      then 1 else 0 := by
  cases player <;>
    simp [Machine.eventBatchTraceKernelGame,
      Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
      pendingFrontrunLawFamily, pendingFrontrunLaw,
      coordinationMessageMachine, Machine.messageInFlight,
      coordinationMachine, Machine.runEventBatchesFrom,
      Machine.runEventsFrom, Machine.step, KernelGame.eu,
      Machine.eventBatchTraceUtility, Machine.RoundView.optionOutcomeUtility,
      CoordinationState.init, CoordinationState.outcome?,
      CoordinationState.setAction, CoordinationState.action?,
      pendingFrontrunRowMessage, pendingFrontrunColAction]

theorem pendingFrontrunTraceGame_projectedOutcome_four
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player) :
    PMF.map (fun trace => coordinationMessageMachine.outcome trace.2)
        (pendingFrontrunTraceGame.outcomeKernel profile) =
      PMF.pure
        (some
          (pendingFrontrunRowMessage profile,
            pendingFrontrunColAction profile
              [⟨TalkPlayer.row, pendingFrontrunRowMessage profile⟩])) := by
  simp [Machine.eventBatchTraceKernelGame,
    Machine.eventBatchTraceDist, Machine.eventBatchTraceDistFrom,
    pendingFrontrunLawFamily, pendingFrontrunLaw,
    coordinationMessageMachine, Machine.messageInFlight, coordinationMachine,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step,
    CoordinationState.init, CoordinationState.outcome?,
    CoordinationState.setAction, CoordinationState.action?,
    pendingFrontrunRowMessage, pendingFrontrunColAction, PMF.pure_map]

def copyPendingRowStrategy :
    ∀ player : TalkPlayer, PendingFrontrunStrategy player
  | TalkPlayer.row => (true, fun _ => true)
  | TalkPlayer.col => (false, pendingRowSignal)

example :
    pendingFrontrunColAction copyPendingRowStrategy
        [⟨TalkPlayer.row, true⟩] = true := by
  rfl

example :
    pendingFrontrunColAction copyPendingRowStrategy
        [⟨TalkPlayer.row, false⟩] = false := by
  rfl

theorem copyPendingRowStrategy_eu
    (player : TalkPlayer) :
    pendingFrontrunTraceGame.eu copyPendingRowStrategy player = 1 := by
  rw [pendingFrontrunTraceGame_eu_four]
  rfl

/-- If column copies row's pending message, row cannot profitably alter its
message bit and column cannot improve above payoff `1`.  This is a real
strategic result at the pending-message runtime layer, not an erasure theorem
back to the original simultaneous coordination game. Row's deviations are
payoff-neutral at this profile; the result is Nash, not strict Nash. -/
theorem copyPendingRowStrategy_nash :
    pendingFrontrunTraceGame.IsNash copyPendingRowStrategy := by
  intro player alternative
  cases player
  · have hdev :
        pendingFrontrunRowMessage
            (Function.update copyPendingRowStrategy TalkPlayer.row alternative) =
          pendingFrontrunColAction
            (Function.update copyPendingRowStrategy TalkPlayer.row alternative)
            [⟨TalkPlayer.row,
              pendingFrontrunRowMessage
                (Function.update copyPendingRowStrategy TalkPlayer.row
                  alternative)⟩] := by
      cases alternative with
      | mk message rule =>
          cases message <;> rfl
    have hright :
        pendingFrontrunTraceGame.eu
            (Function.update copyPendingRowStrategy TalkPlayer.row alternative)
            TalkPlayer.row = 1 := by
      rw [pendingFrontrunTraceGame_eu_four]
      exact if_pos hdev
    rw [copyPendingRowStrategy_eu TalkPlayer.row, hright]
  · rw [copyPendingRowStrategy_eu TalkPlayer.col,
      pendingFrontrunTraceGame_eu_four]
    split <;> norm_num

/-! ## Audited backend preserves pending-message conditioning -/

noncomputable def auditedPendingFrontrunLawLift :
    (Machine.audited.refinement coordinationMessageMachine)
      |>.EventBatchLawFamilyLift PendingFrontrunStrategy
        pendingFrontrunLawFamily :=
  Machine.audited.liftEventBatchLawFamily coordinationMessageMachine
    pendingFrontrunLawFamily

theorem auditedPendingFrontrun_projectTrace_eq
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player) :
    PMF.map
        ((Machine.audited.refinement coordinationMessageMachine)
          |>.projectEventBatchTrace)
        ((Machine.eventBatchTraceKernelGame
          auditedCoordinationMessageMachine PendingFrontrunStrategy
          auditedPendingFrontrunLawLift.impl (fun _ => 0) 4)
          |>.outcomeKernel profile) =
      pendingFrontrunTraceGame.outcomeKernel profile := by
  exact
    (Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceKernelGame_projectTrace_eq
        auditedPendingFrontrunLawLift (fun _ => 0) 4 profile

theorem auditedPendingFrontrun_eu_four
    (profile : ∀ player : TalkPlayer, PendingFrontrunStrategy player)
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        auditedCoordinationMessageMachine PendingFrontrunStrategy
        auditedPendingFrontrunLawLift.impl (fun _ => 0) 4).eu profile player =
      if pendingFrontrunRowMessage profile =
          pendingFrontrunColAction profile
            [⟨TalkPlayer.row, pendingFrontrunRowMessage profile⟩]
      then 1 else 0 := by
  have h :=
    ((Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceEUMorphismOfBounded
        auditedPendingFrontrunLawLift (fun _ => 0) 4
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound).eu_preserved profile player
  simpa [auditedCoordinationMessageMachine, pendingFrontrunTraceGame] using
    h.symm.trans (pendingFrontrunTraceGame_eu_four profile player)

theorem auditedCopyPendingRowStrategy_eu
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        auditedCoordinationMessageMachine PendingFrontrunStrategy
        auditedPendingFrontrunLawLift.impl (fun _ => 0) 4).eu
      copyPendingRowStrategy player = 1 := by
  rw [auditedPendingFrontrun_eu_four]
  rfl

theorem auditedCopyPendingRowStrategy_nash :
    (Machine.eventBatchTraceKernelGame
        auditedCoordinationMessageMachine PendingFrontrunStrategy
        auditedPendingFrontrunLawLift.impl (fun _ => 0) 4).IsNash
      copyPendingRowStrategy := by
  exact
    (Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        auditedPendingFrontrunLawLift (fun _ => 0) 4
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound
        copyPendingRowStrategy_nash

def ignorePendingFalseStrategy :
    ∀ player : TalkPlayer, PendingFrontrunStrategy player
  | TalkPlayer.row => (true, fun _ => true)
  | TalkPlayer.col => (false, fun _ => false)

theorem ignorePendingFalseStrategy_eu_zero
    (player : TalkPlayer) :
    pendingFrontrunTraceGame.eu ignorePendingFalseStrategy player = 0 := by
  rw [pendingFrontrunTraceGame_eu_four]
  rfl

end Refinement
end Examples
end Vegas

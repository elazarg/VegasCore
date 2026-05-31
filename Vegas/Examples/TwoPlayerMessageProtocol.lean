import Vegas.Machine.MessageInFlight
import Vegas.Machine.RefinementKernelGame
import Vegas.Machine.Audited
import Vegas.Examples.CheapTalk

/-!
# Two-player explicit message protocol

This fixture uses the real `Machine.messageInFlight` wrapper with two players.
It models an explicit protocol where row and column players send Bool messages,
the runtime delivers them through the pending queue, and then each player chooses
the real coordination-game action from the delivered message profile.

The result is intentionally at the explicit message-protocol layer. It shows
where messages affect analysis without claiming that message-conditioned
strategies can be erased back to the original game for free.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

structure CoordinationState where
  rowAction : Option Bool
  colAction : Option Bool
deriving DecidableEq, Repr

def CoordinationState.init : CoordinationState where
  rowAction := none
  colAction := none

def CoordinationState.setAction
    (player : TalkPlayer) (action : Bool)
    (state : CoordinationState) : CoordinationState :=
  match player with
  | TalkPlayer.row => { state with rowAction := some action }
  | TalkPlayer.col => { state with colAction := some action }

def CoordinationState.action? :
    CoordinationState → TalkPlayer → Option Bool
  | state, TalkPlayer.row => state.rowAction
  | state, TalkPlayer.col => state.colAction

def CoordinationState.outcome? (state : CoordinationState) :
    Option (Bool × Bool) :=
  match state.rowAction, state.colAction with
  | some rowAction, some colAction => some (rowAction, colAction)
  | _, _ => none

noncomputable def coordinationMachine : Machine TalkPlayer where
  State := CoordinationState
  Action := fun _ => Bool
  Internal := PEmpty
  Public := CoordinationState
  Obs := fun _ => CoordinationState
  Outcome := Bool × Bool
  init := CoordinationState.init
  available := fun state player =>
    match state.action? player with
    | none => Set.univ
    | some _ => ∅
  availableInternal := fun _ => ∅
  stepPlay := fun player action state =>
    PMF.pure (state.setAction player action)
  stepInternal := fun event _ => nomatch event
  terminal := fun state =>
    state.rowAction.isSome = true ∧ state.colAction.isSome = true
  publicView := id
  observe := fun _ => id
  outcome := CoordinationState.outcome?
  utility := fun outcome _ => if outcome.1 == outcome.2 then 1 else 0

noncomputable def coordinationMessageMachine : Machine TalkPlayer :=
  Machine.messageInFlight coordinationMachine (fun _ : TalkPlayer => Bool)

theorem coordinationMessage_sendAvailableRunFrom
    (source : CoordinationState)
    (pending delivered : List (Sigma (fun _ : TalkPlayer => Bool)))
    (player : TalkPlayer) (message : Bool)
    (hnonterminal : ¬ coordinationMachine.terminal source) :
    coordinationMessageMachine.AvailableRunFrom
      { source := source,
        pending := pending,
        delivered := delivered }
      [.play player (.send message)]
      { source := source,
        pending := pending ++ [⟨player, message⟩],
        delivered := delivered } := by
  simpa [coordinationMessageMachine] using
    Machine.messageInFlight.sendAvailableRunFrom coordinationMachine
      (fun _ : TalkPlayer => Bool)
      { source := source, pending := pending, delivered := delivered }
      player message hnonterminal

theorem coordinationMessage_deliverAvailableRunFrom
    (source : CoordinationState)
    (message : Sigma (fun _ : TalkPlayer => Bool))
    (rest delivered : List (Sigma (fun _ : TalkPlayer => Bool)))
    (hnonterminal : ¬ coordinationMachine.terminal source) :
    coordinationMessageMachine.AvailableRunFrom
      { source := source,
        pending := message :: rest,
        delivered := delivered }
      [.internal .deliver]
      { source := source,
        pending := rest,
        delivered := delivered ++ [message] } := by
  simpa [coordinationMessageMachine] using
    Machine.messageInFlight.deliverAvailableRunFrom coordinationMachine
      (fun _ : TalkPlayer => Bool) source message rest delivered hnonterminal

theorem coordinationMessage_specPlayAvailableRunFrom
    (source : CoordinationState)
    (pending delivered : List (Sigma (fun _ : TalkPlayer => Bool)))
    (player : TalkPlayer) (action : Bool)
    (havailable : action ∈ coordinationMachine.available source player) :
    coordinationMessageMachine.AvailableRunFrom
      { source := source,
        pending := pending,
        delivered := delivered }
      [.play player (.spec action)]
      { source := source.setAction player action,
        pending := pending,
        delivered := delivered } := by
  have hrun :
      coordinationMachine.AvailableRunFrom source
        [.play player action] (source.setAction player action) := by
    refine Machine.AvailableRunFrom.cons ?_ ?_
      (Machine.AvailableRunFrom.nil _)
    · exact havailable
    · change source.setAction player action ∈
        (PMF.pure (source.setAction player action)).support
      rw [PMF.support_pure]
      exact Set.mem_singleton _
  simpa [coordinationMessageMachine, Machine.messageInFlight.liftEvent] using
    Machine.messageInFlight.liftAvailableRunFrom coordinationMachine
      (fun _ : TalkPlayer => Bool) pending delivered hrun

def deliveredTalkMessage? (player : TalkPlayer) :
    List (Sigma (fun _ : TalkPlayer => Bool)) → Option Bool
  | [] => none
  | ⟨sender, message⟩ :: rest =>
      if sender = player then some message else deliveredTalkMessage? player rest

def deliveredTalkMessage
    (delivered : List (Sigma (fun _ : TalkPlayer => Bool)))
    (player : TalkPlayer) : Bool :=
  (deliveredTalkMessage? player delivered).getD false

def deliveredTalkProfile
    (delivered : List (Sigma (fun _ : TalkPlayer => Bool))) :
    TalkPlayer → Bool :=
  fun player => deliveredTalkMessage delivered player

abbrev TalkProtocolStrategy (_player : TalkPlayer) :=
  Bool × ((TalkPlayer → Bool) → Bool)

def talkProtocolMessageProfile
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    TalkPlayer → Bool :=
  fun player => (profile player).1

def talkProtocolAction
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) : Bool :=
  (profile player).2 (talkProtocolMessageProfile profile)

def talkProtocolDeliveredAction
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (delivered : List (Sigma (fun _ : TalkPlayer => Bool)))
    (player : TalkPlayer) : Bool :=
  (profile player).2 (deliveredTalkProfile delivered)

theorem deliveredTalkProfile_row_col
    (rowMessage colMessage : Bool) :
    deliveredTalkProfile
        [⟨TalkPlayer.row, rowMessage⟩, ⟨TalkPlayer.col, colMessage⟩] =
      fun player =>
        match player with
        | TalkPlayer.row => rowMessage
        | TalkPlayer.col => colMessage := by
  funext player
  cases player <;> simp [deliveredTalkProfile, deliveredTalkMessage,
    deliveredTalkMessage?]

theorem deliveredTalkProfile_sent
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    deliveredTalkProfile
        [⟨TalkPlayer.row, (profile TalkPlayer.row).1⟩,
          ⟨TalkPlayer.col, (profile TalkPlayer.col).1⟩] =
      talkProtocolMessageProfile profile := by
  funext player
  cases player <;> simp [deliveredTalkProfile, deliveredTalkMessage,
    deliveredTalkMessage?, talkProtocolMessageProfile]

noncomputable def talkProtocolLaw
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    coordinationMessageMachine.EventBatchLaw :=
  fun trace =>
    match trace.2.pending with
    | _ :: _ => PMF.pure [.internal .deliver]
    | [] =>
        match deliveredTalkMessage? TalkPlayer.row trace.2.delivered with
        | none =>
            PMF.pure
              [.play TalkPlayer.row
                (.send (profile TalkPlayer.row).1)]
        | some _ =>
            match deliveredTalkMessage? TalkPlayer.col trace.2.delivered with
            | none =>
                PMF.pure
                  [.play TalkPlayer.col
                    (.send (profile TalkPlayer.col).1)]
            | some _ =>
                match trace.2.source.rowAction with
                | none =>
                    PMF.pure
                      [.play TalkPlayer.row
                        (.spec
                          (talkProtocolDeliveredAction profile
                            trace.2.delivered TalkPlayer.row))]
                | some _ =>
                    match trace.2.source.colAction with
                    | none =>
                        PMF.pure
                          [.play TalkPlayer.col
                            (.spec
                              (talkProtocolDeliveredAction profile
                                trace.2.delivered TalkPlayer.col))]
                    | some _ => PMF.pure []

noncomputable def talkProtocolLawFamily :
    coordinationMessageMachine.EventBatchLawFamily TalkProtocolStrategy where
  law := talkProtocolLaw
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨source, pending, delivered⟩
    cases pending with
    | cons message rest =>
        have hbatch_eq : batch = [.internal .deliver] := by
          simpa [talkProtocolLaw] using hbatch
        subst batch
        let src : coordinationMessageMachine.State :=
          { source := source,
            pending := message :: rest,
            delivered := delivered }
        let dst : coordinationMessageMachine.State :=
          { source := source,
            pending := rest,
            delivered := delivered ++ [message] }
        refine ⟨dst, ?_⟩
        simpa [src, dst] using
          coordinationMessage_deliverAvailableRunFrom source message rest
            delivered
            (by
              simpa [coordinationMessageMachine, Machine.messageInFlight, src]
                using hnonterminal)
    | nil =>
        cases hrow :
            deliveredTalkMessage? TalkPlayer.row delivered with
        | none =>
            have hbatch_eq :
                batch =
                  [.play TalkPlayer.row
                    (.send (profile TalkPlayer.row).1)] := by
              simpa [talkProtocolLaw, hrow] using hbatch
            subst batch
            let sent : Sigma (fun _ : TalkPlayer => Bool) :=
              ⟨TalkPlayer.row, (profile TalkPlayer.row).1⟩
            let src : coordinationMessageMachine.State :=
              { source := source,
                pending := [],
                delivered := delivered }
            let dst : coordinationMessageMachine.State :=
              { source := source,
                pending := [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            simpa [src, dst, sent] using
              coordinationMessage_sendAvailableRunFrom source [] delivered
                TalkPlayer.row (profile TalkPlayer.row).1
                (by
                  simpa [coordinationMessageMachine,
                    Machine.messageInFlight, src] using hnonterminal)
        | some rowMessage =>
            cases hcol :
                deliveredTalkMessage? TalkPlayer.col delivered with
            | none =>
                have hbatch_eq :
                    batch =
                      [.play TalkPlayer.col
                        (.send (profile TalkPlayer.col).1)] := by
                  simpa [talkProtocolLaw, hrow, hcol] using hbatch
                subst batch
                let sent : Sigma (fun _ : TalkPlayer => Bool) :=
                  ⟨TalkPlayer.col, (profile TalkPlayer.col).1⟩
                let src : coordinationMessageMachine.State :=
                  { source := source,
                    pending := [],
                    delivered := delivered }
                let dst : coordinationMessageMachine.State :=
                  { source := source,
                    pending := [sent],
                    delivered := delivered }
                refine ⟨dst, ?_⟩
                simpa [src, dst, sent] using
                  coordinationMessage_sendAvailableRunFrom source [] delivered
                    TalkPlayer.col (profile TalkPlayer.col).1
                    (by
                      simpa [coordinationMessageMachine,
                        Machine.messageInFlight, src] using hnonterminal)
            | some colMessage =>
                cases source with
                | mk rowAction colAction =>
                    cases rowAction with
                    | none =>
                        let action :=
                          talkProtocolDeliveredAction profile delivered
                            TalkPlayer.row
                        have hbatch_eq :
                            batch =
                              [.play TalkPlayer.row (.spec action)] := by
                          simpa [talkProtocolLaw, hrow, hcol, action]
                            using hbatch
                        subst batch
                        let src : coordinationMessageMachine.State :=
                          { source := { rowAction := none,
                                        colAction := colAction },
                            pending := [],
                            delivered := delivered }
                        let dst : coordinationMessageMachine.State :=
                          { source :=
                              { rowAction := some action,
                                colAction := colAction },
                            pending := [],
                            delivered := delivered }
                        let finalSource : CoordinationState :=
                          { rowAction := some action,
                            colAction := colAction }
                        let restore
                            (sourceValue : CoordinationState) :
                            coordinationMessageMachine.State :=
                          { source := sourceValue,
                            pending := [],
                            delivered := delivered }
                        refine ⟨dst, ?_⟩
                        simpa [src, dst, finalSource, restore,
                          CoordinationState.setAction] using
                          coordinationMessage_specPlayAvailableRunFrom
                            { rowAction := none, colAction := colAction }
                            [] delivered TalkPlayer.row action
                            (by
                              change action ∈ Set.univ
                              exact Set.mem_univ action)
                    | some rowAction =>
                        cases colAction with
                        | none =>
                            let action :=
                              talkProtocolDeliveredAction profile delivered
                                TalkPlayer.col
                            have hbatch_eq :
                                batch =
                                  [.play TalkPlayer.col (.spec action)] := by
                              simpa [talkProtocolLaw, hrow, hcol, action]
                                using hbatch
                            subst batch
                            let src : coordinationMessageMachine.State :=
                              { source := { rowAction := some rowAction,
                                            colAction := none },
                                pending := [],
                                delivered := delivered }
                            let dst : coordinationMessageMachine.State :=
                              { source :=
                                  { rowAction := some rowAction,
                                    colAction := some action },
                                pending := [],
                                delivered := delivered }
                            let finalSource : CoordinationState :=
                              { rowAction := some rowAction,
                                colAction := some action }
                            let restore
                                (sourceValue : CoordinationState) :
                                coordinationMessageMachine.State :=
                              { source := sourceValue,
                                pending := [],
                                delivered := delivered }
                            refine ⟨dst, ?_⟩
                            simpa [src, dst, finalSource, restore,
                              CoordinationState.setAction] using
                              coordinationMessage_specPlayAvailableRunFrom
                                { rowAction := some rowAction,
                                  colAction := none }
                                [] delivered TalkPlayer.col action
                                (by
                                  change action ∈ Set.univ
                                  exact Set.mem_univ action)
                        | some colAction =>
                            exact False.elim
                              (hnonterminal (by
                                simp [coordinationMessageMachine,
                                  Machine.messageInFlight,
                                  coordinationMachine]))

def rowSignalTalkProtocolProfile :
    ∀ player : TalkPlayer, TalkProtocolStrategy player
  | TalkPlayer.row => (true, fun _ => true)
  | TalkPlayer.col => (false, fun messages => messages TalkPlayer.row)

theorem talkProtocolAction_eq_cheapTalkAction
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) :
    talkProtocolAction profile player =
      coordinationCheapTalkAction profile player := by
  cases player <;> rfl

theorem talkProtocolTraceGame_eu_six
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        coordinationMessageMachine TalkProtocolStrategy
        talkProtocolLawFamily (fun _ => 0) 6).eu profile player =
      if talkProtocolAction profile TalkPlayer.row =
          talkProtocolAction profile TalkPlayer.col then 1 else 0 := by
  cases player <;>
    simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
      Machine.eventBatchTraceDistFrom, talkProtocolLawFamily,
      talkProtocolLaw,
      coordinationMessageMachine, Machine.messageInFlight,
      coordinationMachine, Machine.runEventBatchesFrom,
      Machine.runEventsFrom, Machine.step, KernelGame.eu,
      Machine.eventBatchTraceUtility, Machine.RoundView.optionOutcomeUtility,
      CoordinationState.init,
      CoordinationState.outcome?, CoordinationState.setAction,
      CoordinationState.action?, talkProtocolAction,
      talkProtocolDeliveredAction, deliveredTalkMessage?,
      deliveredTalkProfile_sent]

theorem talkProtocolTraceGame_eu_eq_cheapTalk
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        coordinationMessageMachine TalkProtocolStrategy
        talkProtocolLawFamily (fun _ => 0) 6).eu profile player =
      coordinationCheapTalkGame.eu profile player := by
  rw [talkProtocolTraceGame_eu_six, coordinationCheapTalk_eu]
  rw [talkProtocolAction_eq_cheapTalkAction profile TalkPlayer.row]
  rw [talkProtocolAction_eq_cheapTalkAction profile TalkPlayer.col]

theorem talkProtocolTraceGame_projectedOutcome_raw_six
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    PMF.map (fun trace => coordinationMessageMachine.outcome trace.2)
        ((Machine.eventBatchTraceKernelGame
          coordinationMessageMachine TalkProtocolStrategy
          talkProtocolLawFamily (fun _ => 0) 6).outcomeKernel profile) =
      PMF.pure
        (some
          (talkProtocolAction profile TalkPlayer.row,
            talkProtocolAction profile TalkPlayer.col)) := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom, talkProtocolLawFamily, talkProtocolLaw,
    coordinationMessageMachine, Machine.messageInFlight, coordinationMachine,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step,
    CoordinationState.init, CoordinationState.outcome?,
    CoordinationState.setAction, CoordinationState.action?,
    talkProtocolAction, talkProtocolDeliveredAction,
    deliveredTalkMessage?, deliveredTalkProfile_sent, PMF.pure_map]

theorem talkProtocolTraceGame_projectedOutcome_six
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    PMF.map (fun trace => coordinationMessageMachine.outcome trace.2)
        ((Machine.eventBatchTraceKernelGame
          coordinationMessageMachine TalkProtocolStrategy
          talkProtocolLawFamily (fun _ => 0) 6).outcomeKernel profile) =
      PMF.pure
        (some
          (coordinationCheapTalkAction profile TalkPlayer.row,
            coordinationCheapTalkAction profile TalkPlayer.col)) := by
  rw [talkProtocolTraceGame_projectedOutcome_raw_six]
  rw [← talkProtocolAction_eq_cheapTalkAction profile TalkPlayer.row]
  rw [← talkProtocolAction_eq_cheapTalkAction profile TalkPlayer.col]

theorem talkProtocolTraceGame_nash_iff_cheapTalk
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    (Machine.eventBatchTraceKernelGame
        coordinationMessageMachine TalkProtocolStrategy
        talkProtocolLawFamily (fun _ => 0) 6).IsNash profile ↔
      coordinationCheapTalkGame.IsNash profile := by
  constructor
  · intro h player alternative
    change TalkProtocolStrategy player at alternative
    calc
      coordinationCheapTalkGame.eu profile player =
          (Machine.eventBatchTraceKernelGame
            coordinationMessageMachine TalkProtocolStrategy
            talkProtocolLawFamily (fun _ => 0) 6).eu profile player :=
        (talkProtocolTraceGame_eu_eq_cheapTalk profile player).symm
      _ ≥
          (Machine.eventBatchTraceKernelGame
            coordinationMessageMachine TalkProtocolStrategy
            talkProtocolLawFamily (fun _ => 0) 6).eu
            (Function.update profile player alternative) player :=
        h player alternative
      _ =
          coordinationCheapTalkGame.eu
            (Function.update profile player alternative) player :=
        talkProtocolTraceGame_eu_eq_cheapTalk
          (Function.update profile player alternative) player
  · intro h player alternative
    change coordinationCheapTalkGame.Strategy player at alternative
    calc
      (Machine.eventBatchTraceKernelGame
          coordinationMessageMachine TalkProtocolStrategy
          talkProtocolLawFamily (fun _ => 0) 6).eu profile player =
          coordinationCheapTalkGame.eu profile player :=
        talkProtocolTraceGame_eu_eq_cheapTalk profile player
      _ ≥
          coordinationCheapTalkGame.eu
            (Function.update profile player alternative) player :=
        h player alternative
      _ =
          (Machine.eventBatchTraceKernelGame
            coordinationMessageMachine TalkProtocolStrategy
            talkProtocolLawFamily (fun _ => 0) 6).eu
            (Function.update profile player alternative) player :=
        (talkProtocolTraceGame_eu_eq_cheapTalk
          (Function.update profile player alternative) player).symm

def faithfulRowSignalTalkProtocolProfile :
    ∀ player : TalkPlayer, TalkProtocolStrategy player
  | TalkPlayer.row => (true, fun messages => messages TalkPlayer.row)
  | TalkPlayer.col => (false, fun messages => messages TalkPlayer.row)

theorem faithfulRowSignalTalkProtocolProfile_eq_rowSignalsTrueProfile :
    faithfulRowSignalTalkProtocolProfile = rowSignalsTrueProfile := by
  funext player
  cases player <;> rfl

example :
    talkProtocolAction faithfulRowSignalTalkProtocolProfile
      TalkPlayer.row = true := by
  rfl

example :
    talkProtocolAction faithfulRowSignalTalkProtocolProfile
      TalkPlayer.col = true := by
  rfl

example :
    (faithfulRowSignalTalkProtocolProfile TalkPlayer.row).2
      (fun _ => false) = false := by
  rfl

example :
    (rowSignalTalkProtocolProfile TalkPlayer.row).2
      (fun _ => false) = true := by
  rfl

theorem faithfulRowSignalTalkProtocol_nash :
    (Machine.eventBatchTraceKernelGame
        coordinationMessageMachine TalkProtocolStrategy
        talkProtocolLawFamily (fun _ => 0) 6).IsNash
      faithfulRowSignalTalkProtocolProfile := by
  rw [talkProtocolTraceGame_nash_iff_cheapTalk]
  rw [faithfulRowSignalTalkProtocolProfile_eq_rowSignalsTrueProfile]
  exact coordinationCheapTalk_rowSignal_true_nash

theorem coordinationMessageTraceUtility_bound
    (player : TalkPlayer)
    (trace : coordinationMessageMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility
        coordinationMessageMachine (fun _ => 0) trace player| ≤ 1 := by
  rcases trace with ⟨_batches, state⟩
  rcases state with ⟨source, _pending, _delivered⟩
  rcases source with ⟨rowAction, colAction⟩
  cases rowAction <;> cases colAction <;> cases player <;>
    simp [Machine.eventBatchTraceUtility, coordinationMessageMachine,
      Machine.messageInFlight, coordinationMachine,
      Machine.RoundView.optionOutcomeUtility, CoordinationState.outcome?]
  all_goals split <;> norm_num

/-! ## Audited compiled protocol layer -/

noncomputable def auditedCoordinationMessageMachine : Machine TalkPlayer :=
  Machine.audited coordinationMessageMachine

noncomputable def auditedTalkProtocolLawLift :
    (Machine.audited.refinement coordinationMessageMachine)
      |>.EventBatchLawFamilyLift TalkProtocolStrategy
        talkProtocolLawFamily :=
  Machine.audited.liftEventBatchLawFamily coordinationMessageMachine
    talkProtocolLawFamily

theorem auditedCoordinationMessageTraceUtility_bound
    (player : TalkPlayer)
    (trace : auditedCoordinationMessageMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility
        auditedCoordinationMessageMachine (fun _ => 0) trace player| ≤ 1 := by
  simpa [auditedCoordinationMessageMachine] using
    (Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceUtility_bound_project (fun _ => 0)
        coordinationMessageTraceUtility_bound player trace

theorem auditedTalkProtocol_projectTrace_eq
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    PMF.map
        ((Machine.audited.refinement coordinationMessageMachine)
          |>.projectEventBatchTrace)
        ((Machine.eventBatchTraceKernelGame
          auditedCoordinationMessageMachine TalkProtocolStrategy
          auditedTalkProtocolLawLift.impl (fun _ => 0) 6)
          |>.outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          coordinationMessageMachine TalkProtocolStrategy
          talkProtocolLawFamily (fun _ => 0) 6)
          |>.outcomeKernel profile) := by
  exact
    (Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceKernelGame_projectTrace_eq
        auditedTalkProtocolLawLift (fun _ => 0) 6 profile

theorem auditedTalkProtocol_eu_eq_cheapTalk
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        auditedCoordinationMessageMachine TalkProtocolStrategy
        auditedTalkProtocolLawLift.impl (fun _ => 0) 6).eu
      profile player =
      coordinationCheapTalkGame.eu profile player := by
  have h :=
    ((Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceEUMorphismOfBounded
        auditedTalkProtocolLawLift (fun _ => 0) 6
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound).eu_preserved profile player
  simpa [auditedCoordinationMessageMachine] using
    h.symm.trans (talkProtocolTraceGame_eu_eq_cheapTalk profile player)

theorem auditedFaithfulRowSignalTalkProtocol_nash :
    (Machine.eventBatchTraceKernelGame
        auditedCoordinationMessageMachine TalkProtocolStrategy
        auditedTalkProtocolLawLift.impl (fun _ => 0) 6).IsNash
      faithfulRowSignalTalkProtocolProfile := by
  exact
    (Machine.audited.refinement coordinationMessageMachine)
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        auditedTalkProtocolLawLift (fun _ => 0) 6
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound
        faithfulRowSignalTalkProtocol_nash

/-! ## Encoded-storage compiled protocol layer -/

structure EncodedCoordinationState where
  rowAction : Option Nat
  colAction : Option Nat
  audit : Nat
deriving DecidableEq, Repr

def encodeTalkBool (value : Bool) : Nat :=
  if value then 1 else 0

def decodeTalkNat (value : Nat) : Bool :=
  value != 0

@[simp] theorem decodeTalkNat_zero :
    decodeTalkNat 0 = false := by
  simp [decodeTalkNat]

@[simp] theorem decodeTalkNat_one :
    decodeTalkNat 1 = true := by
  simp [decodeTalkNat]

def EncodedCoordinationState.init : EncodedCoordinationState where
  rowAction := none
  colAction := none
  audit := 0

def EncodedCoordinationState.project
    (state : EncodedCoordinationState) : CoordinationState where
  rowAction := state.rowAction.map decodeTalkNat
  colAction := state.colAction.map decodeTalkNat

def EncodedCoordinationState.projectPublic
    (view : Option Nat × Option Nat × Nat) : CoordinationState :=
  { rowAction := view.1.map decodeTalkNat,
    colAction := view.2.1.map decodeTalkNat }

def EncodedCoordinationState.action? :
    EncodedCoordinationState → TalkPlayer → Option Nat
  | state, TalkPlayer.row => state.rowAction
  | state, TalkPlayer.col => state.colAction

def EncodedCoordinationState.setAction
    (player : TalkPlayer) (action : Bool)
    (state : EncodedCoordinationState) : EncodedCoordinationState :=
  match player with
  | TalkPlayer.row =>
      { state with rowAction := some (encodeTalkBool action) }
  | TalkPlayer.col =>
      { state with colAction := some (encodeTalkBool action) }

def EncodedCoordinationState.outcome?
    (state : EncodedCoordinationState) :
    Option (Nat × Nat) :=
  match state.rowAction, state.colAction with
  | some rowAction, some colAction => some (rowAction, colAction)
  | _, _ => none

noncomputable def encodedCoordinationMachine : Machine TalkPlayer where
  State := EncodedCoordinationState
  Action := fun _ => Bool
  Internal := PUnit
  Public := Option Nat × Option Nat × Nat
  Obs := fun _ => Option Nat × Option Nat × Nat
  Outcome := Nat × Nat
  init := EncodedCoordinationState.init
  available := fun state player =>
    match state.action? player with
    | none => Set.univ
    | some _ => ∅
  availableInternal := fun state _ =>
    ¬ (state.rowAction.isSome = true ∧ state.colAction.isSome = true)
  stepPlay := fun player action state =>
    PMF.pure (state.setAction player action)
  stepInternal := fun _ state =>
    PMF.pure { state with audit := state.audit + 1 }
  terminal := fun state =>
    state.rowAction.isSome = true ∧ state.colAction.isSome = true
  publicView := fun state =>
    (state.rowAction, state.colAction, state.audit)
  observe := fun _ state =>
    (state.rowAction, state.colAction, state.audit)
  outcome := EncodedCoordinationState.outcome?
  utility := fun outcome _ =>
    if decodeTalkNat outcome.1 == decodeTalkNat outcome.2 then 1 else 0

noncomputable def encodedCoordinationMessageMachine : Machine TalkPlayer :=
  Machine.messageInFlight encodedCoordinationMachine
    (fun _ : TalkPlayer => Bool)

def encodedCoordinationMessageProjectState
    (state : encodedCoordinationMessageMachine.State) :
    coordinationMessageMachine.State :=
  { source := state.source.project,
    pending := state.pending,
    delivered := state.delivered }

def encodedCoordinationMessageProjectEvent? :
    encodedCoordinationMessageMachine.Event →
      Option coordinationMessageMachine.Event
  | .play player (.send message) =>
      some (.play player (.send message))
  | .play player (.spec action) =>
      some (.play player (.spec action))
  | .internal .deliver =>
      some (.internal .deliver)
  | .internal (.spec _event) =>
      none

def encodedCoordinationMessageProjectEventBatch
    (batch : List encodedCoordinationMessageMachine.Event) :
    List coordinationMessageMachine.Event :=
  batch.filterMap encodedCoordinationMessageProjectEvent?

def encodedCoordinationMessageProjectPublic
    (view : encodedCoordinationMessageMachine.Public) :
    coordinationMessageMachine.Public :=
  (EncodedCoordinationState.projectPublic view.1, view.2.1, view.2.2)

def encodedCoordinationMessageProjectObs
    (player : TalkPlayer)
    (view : encodedCoordinationMessageMachine.Obs player) :
    coordinationMessageMachine.Obs player :=
  (EncodedCoordinationState.projectPublic view.1, view.2.1, view.2.2)

set_option linter.flexible false in
theorem encodedCoordinationMessage_step_project
    (event : encodedCoordinationMessageMachine.Event)
    (state : encodedCoordinationMessageMachine.State) :
    PMF.map encodedCoordinationMessageProjectState
        (encodedCoordinationMessageMachine.step event state) =
      match encodedCoordinationMessageProjectEvent? event with
      | some specEvent =>
          coordinationMessageMachine.step specEvent
            (encodedCoordinationMessageProjectState state)
      | none =>
          PMF.pure (encodedCoordinationMessageProjectState state) := by
  rcases state with ⟨encodedState, pending, delivered⟩
  rcases encodedState with ⟨rowAction, colAction, audit⟩
  cases event with
  | play player action =>
      cases action with
      | send message =>
          simp [encodedCoordinationMessageProjectState,
            encodedCoordinationMessageProjectEvent?,
            encodedCoordinationMessageMachine, coordinationMessageMachine,
            Machine.messageInFlight, Machine.step]
          rw [PMF.pure_map]
          rfl
      | spec action =>
          cases player <;> cases action <;>
            simp [encodedCoordinationMessageProjectState,
              encodedCoordinationMessageProjectEvent?,
              encodedCoordinationMessageMachine, coordinationMessageMachine,
              encodedCoordinationMachine, coordinationMachine,
              Machine.messageInFlight, Machine.step,
              EncodedCoordinationState.project,
              EncodedCoordinationState.setAction,
              CoordinationState.setAction, encodeTalkBool, PMF.pure_map]
  | internal event =>
      cases event with
      | deliver =>
          cases pending with
          | nil =>
              simp [encodedCoordinationMessageProjectState,
                encodedCoordinationMessageProjectEvent?,
                encodedCoordinationMessageMachine, coordinationMessageMachine,
                Machine.messageInFlight, Machine.step]
              rw [PMF.pure_map]
              rfl
          | cons message rest =>
              simp [encodedCoordinationMessageProjectState,
                encodedCoordinationMessageProjectEvent?,
                encodedCoordinationMessageMachine, coordinationMessageMachine,
                Machine.messageInFlight, Machine.step]
              rw [PMF.pure_map]
              rfl
      | spec event =>
          simp [encodedCoordinationMessageProjectState,
            encodedCoordinationMessageProjectEvent?,
            encodedCoordinationMessageMachine, coordinationMessageMachine,
            encodedCoordinationMachine, Machine.messageInFlight,
            Machine.step, EncodedCoordinationState.project, PMF.pure_map]

theorem encodedCoordinationMessage_runEventsFrom_project_eq
    (events : List encodedCoordinationMessageMachine.Event)
    (state : encodedCoordinationMessageMachine.State) :
    PMF.map encodedCoordinationMessageProjectState
        (encodedCoordinationMessageMachine.runEventsFrom events state) =
      coordinationMessageMachine.runEventsFrom
        (encodedCoordinationMessageProjectEventBatch events)
        (encodedCoordinationMessageProjectState state) := by
  induction events generalizing state with
  | nil =>
      change
        PMF.map encodedCoordinationMessageProjectState (PMF.pure state) =
          PMF.pure (encodedCoordinationMessageProjectState state)
      rw [PMF.pure_map]
  | cons event events ih =>
      rw [Machine.runEventsFrom_cons_bind]
      rw [PMF.map_bind]
      simp_rw [ih]
      change
        (encodedCoordinationMessageMachine.step event state).bind
            ((fun specState =>
                coordinationMessageMachine.runEventsFrom
                  (encodedCoordinationMessageProjectEventBatch events)
                  specState) ∘
              encodedCoordinationMessageProjectState) =
          coordinationMessageMachine.runEventsFrom
            (encodedCoordinationMessageProjectEventBatch (event :: events))
            (encodedCoordinationMessageProjectState state)
      rw [← PMF.bind_map
        (p := encodedCoordinationMessageMachine.step event state)
        (f := encodedCoordinationMessageProjectState)
        (q := fun specState =>
          coordinationMessageMachine.runEventsFrom
            (encodedCoordinationMessageProjectEventBatch events) specState)]
      rw [encodedCoordinationMessage_step_project event state]
      cases hproject : encodedCoordinationMessageProjectEvent? event with
      | none =>
          simp [encodedCoordinationMessageProjectEventBatch, hproject,
            PMF.pure_bind]
      | some specEvent =>
          simp [encodedCoordinationMessageProjectEventBatch, hproject,
            Machine.runEventsFrom_cons_bind]

noncomputable def encodedCoordinationMessageRefinement :
    Machine.StochasticRefinement encodedCoordinationMessageMachine
      coordinationMessageMachine where
  projectState := encodedCoordinationMessageProjectState
  projectEvent? := encodedCoordinationMessageProjectEvent?
  projectEventBatch := encodedCoordinationMessageProjectEventBatch
  projectPublic := encodedCoordinationMessageProjectPublic
  projectObs := encodedCoordinationMessageProjectObs
  projectOutcome := fun outcome =>
    (decodeTalkNat outcome.1, decodeTalkNat outcome.2)
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨rowAction, colAction, audit⟩
    cases event with
    | play player action =>
        cases action with
        | send message =>
            cases hproject
            change ¬ coordinationMachine.terminal
              (EncodedCoordinationState.project
                { rowAction := rowAction, colAction := colAction,
                  audit := audit })
            intro hterminal
            change ¬ encodedCoordinationMachine.terminal
              { rowAction := rowAction, colAction := colAction,
                audit := audit } at havailable
            cases rowAction <;> cases colAction <;>
              simp [encodedCoordinationMachine, coordinationMachine,
                EncodedCoordinationState.project] at hterminal havailable
        | spec action =>
            cases hproject
            cases player <;> cases rowAction <;> cases colAction <;>
              simpa [encodedCoordinationMessageMachine,
                coordinationMessageMachine, Machine.messageInFlight,
                encodedCoordinationMachine, coordinationMachine,
                encodedCoordinationMessageProjectState,
                EncodedCoordinationState.project,
                EncodedCoordinationState.action?,
                CoordinationState.action?] using havailable
    | internal event =>
        cases event with
        | deliver =>
            cases hproject
            rcases havailable with ⟨hpending, hnonterminal⟩
            constructor
            · exact hpending
            · change ¬ coordinationMachine.terminal
                (EncodedCoordinationState.project
                  { rowAction := rowAction, colAction := colAction,
                    audit := audit })
              intro hterminal
              change ¬ encodedCoordinationMachine.terminal
                { rowAction := rowAction, colAction := colAction,
                  audit := audit } at hnonterminal
              cases rowAction <;> cases colAction <;>
                simp [encodedCoordinationMachine, coordinationMachine,
                  EncodedCoordinationState.project] at hterminal hnonterminal
        | spec event =>
            simp [encodedCoordinationMessageProjectEvent?] at hproject
  step_project := by
    intro event source
    cases hproject : encodedCoordinationMessageProjectEvent? event with
    | none =>
        rw [encodedCoordinationMessage_step_project event source]
        simp [hproject]
    | some specEvent =>
        rw [encodedCoordinationMessage_step_project event source]
        simp [hproject]
  eventBatch_project := by
    intro events source
    exact encodedCoordinationMessage_runEventsFrom_project_eq events source
  publicView_project := by
    intro state
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨rowAction, colAction, audit⟩
    rfl
  observe_project := by
    intro player state
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨rowAction, colAction, audit⟩
    rfl
  terminal_project := by
    intro state hterminal
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨rowAction, colAction, audit⟩
    cases rowAction <;> cases colAction <;>
      simp [encodedCoordinationMessageMachine, coordinationMessageMachine,
        Machine.messageInFlight, encodedCoordinationMachine,
        coordinationMachine, encodedCoordinationMessageProjectState,
        EncodedCoordinationState.project] at hterminal ⊢
  terminal_reflect := by
    intro state hterminal
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨rowAction, colAction, audit⟩
    cases rowAction <;> cases colAction <;>
      simp [encodedCoordinationMessageMachine, coordinationMessageMachine,
        Machine.messageInFlight, encodedCoordinationMachine,
        coordinationMachine, encodedCoordinationMessageProjectState,
        EncodedCoordinationState.project] at hterminal ⊢
  outcome_project := by
    intro state
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨rowAction, colAction, audit⟩
    cases rowAction <;> cases colAction <;> rfl
  utility_project := by
    intro outcome player
    cases outcome with
    | mk rowAction colAction =>
        cases player
        · simp [encodedCoordinationMessageMachine,
            coordinationMessageMachine, Machine.messageInFlight,
            encodedCoordinationMachine, coordinationMachine]
        · simp [encodedCoordinationMessageMachine,
            coordinationMessageMachine, Machine.messageInFlight,
            encodedCoordinationMachine, coordinationMachine]

noncomputable def encodedTalkProtocolLaw
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    encodedCoordinationMessageMachine.EventBatchLaw :=
  fun trace =>
    match trace.2.pending with
    | _ :: _ => PMF.pure [.internal .deliver]
    | [] =>
        match deliveredTalkMessage? TalkPlayer.row trace.2.delivered with
        | none =>
            PMF.pure
              [.play TalkPlayer.row
                (.send (profile TalkPlayer.row).1)]
        | some _ =>
            match deliveredTalkMessage? TalkPlayer.col trace.2.delivered with
            | none =>
                PMF.pure
                  [.play TalkPlayer.col
                    (.send (profile TalkPlayer.col).1)]
            | some _ =>
                match trace.2.source.rowAction with
                | none =>
                    PMF.pure
                      [.internal (.spec PUnit.unit),
                        .play TalkPlayer.row
                          (.spec
                            (talkProtocolDeliveredAction profile
                              trace.2.delivered TalkPlayer.row))]
                | some _ =>
                    match trace.2.source.colAction with
                    | none =>
                        PMF.pure
                          [.internal (.spec PUnit.unit),
                            .play TalkPlayer.col
                              (.spec
                                (talkProtocolDeliveredAction profile
                                  trace.2.delivered TalkPlayer.col))]
                    | some _ => PMF.pure []

set_option linter.flexible false in
noncomputable def encodedTalkProtocolLawFamily :
    encodedCoordinationMessageMachine.EventBatchLawFamily
      TalkProtocolStrategy where
  law := encodedTalkProtocolLaw
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨source, pending, delivered⟩
    rcases source with ⟨rowAction, colAction, audit⟩
    cases pending with
    | cons message rest =>
        have hbatch_eq : batch = [.internal .deliver] := by
          simpa [encodedTalkProtocolLaw] using hbatch
        subst batch
        let src : encodedCoordinationMessageMachine.State :=
          { source := { rowAction := rowAction,
                        colAction := colAction,
                        audit := audit },
            pending := message :: rest,
            delivered := delivered }
        let dst : encodedCoordinationMessageMachine.State :=
          { source := { rowAction := rowAction,
                        colAction := colAction,
                        audit := audit },
            pending := rest,
            delivered := delivered ++ [message] }
        refine ⟨dst, ?_⟩
        change
          encodedCoordinationMessageMachine.AvailableRunFrom src
            [.internal .deliver] dst
        refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
          (Machine.AvailableRunFrom.nil _)
        · change Machine.MessageInFlightInternal.deliver ∈
            encodedCoordinationMessageMachine.availableInternal src
          constructor
          · intro hnil
            cases hnil
          · exact hnonterminal
        · change dst ∈ (PMF.pure dst).support
          rw [PMF.support_pure]
          exact Set.mem_singleton _
    | nil =>
        cases hrow :
            deliveredTalkMessage? TalkPlayer.row delivered with
        | none =>
            have hbatch_eq :
                batch =
                  [.play TalkPlayer.row
                    (.send (profile TalkPlayer.row).1)] := by
              simpa [encodedTalkProtocolLaw, hrow] using hbatch
            subst batch
            let sent : Sigma (fun _ : TalkPlayer => Bool) :=
              ⟨TalkPlayer.row, (profile TalkPlayer.row).1⟩
            let src : encodedCoordinationMessageMachine.State :=
              { source := { rowAction := rowAction,
                            colAction := colAction,
                            audit := audit },
                pending := [],
                delivered := delivered }
            let dst : encodedCoordinationMessageMachine.State :=
              { source := { rowAction := rowAction,
                            colAction := colAction,
                            audit := audit },
                pending := [sent],
                delivered := delivered }
            refine ⟨dst, ?_⟩
            change
              encodedCoordinationMessageMachine.AvailableRunFrom src
                [.play TalkPlayer.row
                  (.send (profile TalkPlayer.row).1)] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change Machine.MessageInFlightAction.send
                (profile TalkPlayer.row).1 ∈
                encodedCoordinationMessageMachine.available src TalkPlayer.row
              exact hnonterminal
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
        | some rowMessage =>
            cases hcol :
                deliveredTalkMessage? TalkPlayer.col delivered with
            | none =>
                have hbatch_eq :
                    batch =
                      [.play TalkPlayer.col
                        (.send (profile TalkPlayer.col).1)] := by
                  simpa [encodedTalkProtocolLaw, hrow, hcol] using hbatch
                subst batch
                let sent : Sigma (fun _ : TalkPlayer => Bool) :=
                  ⟨TalkPlayer.col, (profile TalkPlayer.col).1⟩
                let src : encodedCoordinationMessageMachine.State :=
                  { source := { rowAction := rowAction,
                                colAction := colAction,
                                audit := audit },
                    pending := [],
                    delivered := delivered }
                let dst : encodedCoordinationMessageMachine.State :=
                  { source := { rowAction := rowAction,
                                colAction := colAction,
                                audit := audit },
                    pending := [sent],
                    delivered := delivered }
                refine ⟨dst, ?_⟩
                change
                  encodedCoordinationMessageMachine.AvailableRunFrom src
                    [.play TalkPlayer.col
                      (.send (profile TalkPlayer.col).1)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.send
                    (profile TalkPlayer.col).1 ∈
                    encodedCoordinationMessageMachine.available src
                      TalkPlayer.col
                  exact hnonterminal
                · change dst ∈ (PMF.pure dst).support
                  rw [PMF.support_pure]
                  exact Set.mem_singleton _
            | some colMessage =>
                cases rowAction with
                | none =>
                    let action :=
                      talkProtocolDeliveredAction profile delivered
                        TalkPlayer.row
                    have hbatch_eq :
                        batch =
                          [.internal (.spec PUnit.unit),
                            .play TalkPlayer.row (.spec action)] := by
                      simpa [encodedTalkProtocolLaw, hrow, hcol, action]
                        using hbatch
                    subst batch
                    let src : encodedCoordinationMessageMachine.State :=
                      { source := { rowAction := none,
                                    colAction := colAction,
                                    audit := audit },
                        pending := [],
                        delivered := delivered }
                    let midSource : EncodedCoordinationState :=
                      { rowAction := none,
                        colAction := colAction,
                        audit := audit + 1 }
                    let mid : encodedCoordinationMessageMachine.State :=
                      { source := midSource,
                        pending := [],
                        delivered := delivered }
                    let finalSource : EncodedCoordinationState :=
                      { rowAction := some (encodeTalkBool action),
                        colAction := colAction,
                        audit := audit + 1 }
                    let dst : encodedCoordinationMessageMachine.State :=
                      { source := finalSource,
                        pending := [],
                        delivered := delivered }
                    refine ⟨dst, ?_⟩
                    change
                      encodedCoordinationMessageMachine.AvailableRunFrom src
                        [.internal (.spec PUnit.unit),
                          .play TalkPlayer.row (.spec action)] dst
                    refine Machine.AvailableRunFrom.cons (mid := mid)
                      ?_ ?_ ?_
                    · change Machine.MessageInFlightInternal.spec
                        PUnit.unit ∈
                        encodedCoordinationMessageMachine.availableInternal
                          src
                      change PUnit.unit ∈
                        encodedCoordinationMachine.availableInternal
                          src.source
                      trivial
                    · simp [encodedCoordinationMessageMachine,
                        Machine.messageInFlight, encodedCoordinationMachine,
                        Machine.step, src, mid, midSource]
                      exact Set.mem_singleton _
                    · refine Machine.AvailableRunFrom.cons (mid := dst)
                        ?_ ?_ (Machine.AvailableRunFrom.nil _)
                      · change Machine.MessageInFlightAction.spec action ∈
                          encodedCoordinationMessageMachine.available mid
                            TalkPlayer.row
                        change action ∈
                          encodedCoordinationMachine.available mid.source
                            TalkPlayer.row
                        change action ∈ Set.univ
                        exact Set.mem_univ action
                      · simp [encodedCoordinationMessageMachine,
                          Machine.messageInFlight, encodedCoordinationMachine,
                          Machine.step, mid, dst, finalSource,
                          EncodedCoordinationState.setAction]
                        exact Set.mem_singleton _
                | some rowValue =>
                    cases colAction with
                    | none =>
                        let action :=
                          talkProtocolDeliveredAction profile delivered
                            TalkPlayer.col
                        have hbatch_eq :
                            batch =
                              [.internal (.spec PUnit.unit),
                                .play TalkPlayer.col (.spec action)] := by
                          simpa [encodedTalkProtocolLaw, hrow, hcol, action]
                            using hbatch
                        subst batch
                        let src : encodedCoordinationMessageMachine.State :=
                          { source := { rowAction := some rowValue,
                                        colAction := none,
                                        audit := audit },
                            pending := [],
                            delivered := delivered }
                        let midSource : EncodedCoordinationState :=
                          { rowAction := some rowValue,
                            colAction := none,
                            audit := audit + 1 }
                        let mid : encodedCoordinationMessageMachine.State :=
                          { source := midSource,
                            pending := [],
                            delivered := delivered }
                        let finalSource : EncodedCoordinationState :=
                          { rowAction := some rowValue,
                            colAction := some (encodeTalkBool action),
                            audit := audit + 1 }
                        let dst : encodedCoordinationMessageMachine.State :=
                          { source := finalSource,
                            pending := [],
                            delivered := delivered }
                        refine ⟨dst, ?_⟩
                        change
                          encodedCoordinationMessageMachine.AvailableRunFrom src
                            [.internal (.spec PUnit.unit),
                              .play TalkPlayer.col (.spec action)] dst
                        refine Machine.AvailableRunFrom.cons (mid := mid)
                          ?_ ?_ ?_
                        · change Machine.MessageInFlightInternal.spec
                            PUnit.unit ∈
                            encodedCoordinationMessageMachine.availableInternal
                              src
                          change PUnit.unit ∈
                            encodedCoordinationMachine.availableInternal
                              src.source
                          trivial
                        · simp [encodedCoordinationMessageMachine,
                            Machine.messageInFlight, encodedCoordinationMachine,
                            Machine.step, src, mid, midSource]
                          exact Set.mem_singleton _
                        · refine Machine.AvailableRunFrom.cons (mid := dst)
                            ?_ ?_ (Machine.AvailableRunFrom.nil _)
                          · change
                              Machine.MessageInFlightAction.spec action ∈
                                encodedCoordinationMessageMachine.available mid
                                  TalkPlayer.col
                            change action ∈
                              encodedCoordinationMachine.available mid.source
                                TalkPlayer.col
                            change action ∈ Set.univ
                            exact Set.mem_univ action
                          · simp [encodedCoordinationMessageMachine,
                              Machine.messageInFlight,
                              encodedCoordinationMachine, Machine.step, mid,
                              dst, finalSource,
                              EncodedCoordinationState.setAction]
                            exact Set.mem_singleton _
                    | some colValue =>
                        exact False.elim
                          (hnonterminal (by
                            simp [encodedCoordinationMessageMachine,
                              Machine.messageInFlight,
                              encodedCoordinationMachine]))

noncomputable def encodedTalkProtocolLawLift :
    encodedCoordinationMessageRefinement.EventBatchLawFamilyLift
      TalkProtocolStrategy talkProtocolLawFamily where
  impl := encodedTalkProtocolLawFamily
  compatible := by
    intro profile trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨source, pending, delivered⟩
    rcases source with ⟨rowAction, colAction, audit⟩
    cases pending with
    | cons message rest =>
        simp [encodedCoordinationMessageRefinement,
          encodedTalkProtocolLawFamily, talkProtocolLawFamily,
          encodedTalkProtocolLaw, talkProtocolLaw,
          encodedCoordinationMessageProjectState,
          encodedCoordinationMessageProjectEventBatch,
          encodedCoordinationMessageProjectEvent?,
          EncodedCoordinationState.project, PMF.pure_map]
    | nil =>
        cases hrow :
            deliveredTalkMessage? TalkPlayer.row delivered with
        | none =>
            simp [encodedCoordinationMessageRefinement,
              encodedTalkProtocolLawFamily, talkProtocolLawFamily,
              encodedTalkProtocolLaw, talkProtocolLaw, hrow,
              encodedCoordinationMessageProjectState,
              encodedCoordinationMessageProjectEventBatch,
              encodedCoordinationMessageProjectEvent?,
              EncodedCoordinationState.project, PMF.pure_map]
        | some rowMessage =>
            cases hcol :
                deliveredTalkMessage? TalkPlayer.col delivered with
            | none =>
                simp [encodedCoordinationMessageRefinement,
                  encodedTalkProtocolLawFamily, talkProtocolLawFamily,
                  encodedTalkProtocolLaw, talkProtocolLaw, hrow, hcol,
                  encodedCoordinationMessageProjectState,
                  encodedCoordinationMessageProjectEventBatch,
                  encodedCoordinationMessageProjectEvent?,
                  EncodedCoordinationState.project, PMF.pure_map]
            | some colMessage =>
                cases rowAction with
                | none =>
                    let action :=
                      talkProtocolDeliveredAction profile delivered
                        TalkPlayer.row
                    simp [encodedCoordinationMessageRefinement,
                      encodedTalkProtocolLawFamily, talkProtocolLawFamily,
                      encodedTalkProtocolLaw, talkProtocolLaw, hrow, hcol,
                      encodedCoordinationMessageProjectState,
                      encodedCoordinationMessageProjectEventBatch,
                      encodedCoordinationMessageProjectEvent?,
                      EncodedCoordinationState.project, PMF.pure_map]
                | some rowValue =>
                    cases colAction with
                    | none =>
                        let action :=
                          talkProtocolDeliveredAction profile delivered
                            TalkPlayer.col
                        simp [encodedCoordinationMessageRefinement,
                          encodedTalkProtocolLawFamily, talkProtocolLawFamily,
                          encodedTalkProtocolLaw, talkProtocolLaw, hrow, hcol,
                          encodedCoordinationMessageProjectState,
                          encodedCoordinationMessageProjectEventBatch,
                          encodedCoordinationMessageProjectEvent?,
                          EncodedCoordinationState.project, PMF.pure_map]
                    | some colValue =>
                        simp [encodedCoordinationMessageRefinement,
                          encodedTalkProtocolLawFamily, talkProtocolLawFamily,
                          encodedTalkProtocolLaw, talkProtocolLaw, hrow, hcol,
                          encodedCoordinationMessageProjectState,
                          encodedCoordinationMessageProjectEventBatch,
                          encodedCoordinationMessageProjectEvent?,
                          EncodedCoordinationState.project, PMF.pure_map]

theorem encodedCoordinationMessageTraceUtility_bound
    (player : TalkPlayer)
    (trace : encodedCoordinationMessageMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility
        encodedCoordinationMessageMachine (fun _ => 0) trace player| ≤ 1 := by
  rcases trace with ⟨_batches, state⟩
  rcases state with ⟨source, _pending, _delivered⟩
  rcases source with ⟨rowAction, colAction, audit⟩
  cases rowAction <;> cases colAction <;> cases player <;>
    simp [Machine.eventBatchTraceUtility,
      encodedCoordinationMessageMachine, Machine.messageInFlight,
      encodedCoordinationMachine, Machine.RoundView.optionOutcomeUtility,
      EncodedCoordinationState.outcome?]
  all_goals split <;> norm_num

theorem encodedTalkProtocol_projectTrace_eq
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    PMF.map encodedCoordinationMessageRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
          encodedCoordinationMessageMachine TalkProtocolStrategy
          encodedTalkProtocolLawLift.impl (fun _ => 0) 6)
          |>.outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          coordinationMessageMachine TalkProtocolStrategy
          talkProtocolLawFamily (fun _ => 0) 6)
          |>.outcomeKernel profile) := by
  exact
    encodedCoordinationMessageRefinement
      |>.eventBatchTraceKernelGame_projectTrace_eq
        encodedTalkProtocolLawLift (fun _ => 0) 6 profile

theorem encodedTalkProtocol_finalState_six
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    PMF.map (fun trace => trace.2)
        ((Machine.eventBatchTraceKernelGame
          encodedCoordinationMessageMachine TalkProtocolStrategy
          encodedTalkProtocolLawLift.impl (fun _ => 0) 6)
          |>.outcomeKernel profile) =
      PMF.pure
        { source :=
            { rowAction :=
                some (encodeTalkBool
                  (talkProtocolAction profile TalkPlayer.row)),
              colAction :=
                some (encodeTalkBool
                  (talkProtocolAction profile TalkPlayer.col)),
              audit := 2 },
          pending := [],
          delivered :=
            [⟨TalkPlayer.row, (profile TalkPlayer.row).1⟩,
              ⟨TalkPlayer.col, (profile TalkPlayer.col).1⟩] } := by
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom, encodedTalkProtocolLawLift,
    encodedTalkProtocolLawFamily, encodedTalkProtocolLaw,
    encodedCoordinationMessageMachine,
    encodedCoordinationMachine, Machine.messageInFlight,
    Machine.runEventBatchesFrom, Machine.runEventsFrom, Machine.step,
    EncodedCoordinationState.init, EncodedCoordinationState.setAction,
    talkProtocolAction, talkProtocolDeliveredAction,
    deliveredTalkMessage?, deliveredTalkProfile_sent, PMF.pure_map]

theorem encodedTalkProtocol_eu_eq_cheapTalk
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        encodedCoordinationMessageMachine TalkProtocolStrategy
        encodedTalkProtocolLawLift.impl (fun _ => 0) 6).eu
      profile player =
      coordinationCheapTalkGame.eu profile player := by
  have h :=
    (encodedCoordinationMessageRefinement
      |>.eventBatchTraceEUMorphismOfBounded
        encodedTalkProtocolLawLift (fun _ => 0) 6
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        encodedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound).eu_preserved profile player
  rw [← h]
  exact talkProtocolTraceGame_eu_eq_cheapTalk profile player

theorem encodedFaithfulRowSignalTalkProtocol_nash :
    (Machine.eventBatchTraceKernelGame
        encodedCoordinationMessageMachine TalkProtocolStrategy
        encodedTalkProtocolLawLift.impl (fun _ => 0) 6).IsNash
      faithfulRowSignalTalkProtocolProfile := by
  exact
    encodedCoordinationMessageRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        encodedTalkProtocolLawLift (fun _ => 0) 6
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        encodedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound
        faithfulRowSignalTalkProtocol_nash

/-! ## Audited encoded-storage backend -/

noncomputable def auditedEncodedCoordinationMessageMachine :
    Machine TalkPlayer :=
  Machine.audited encodedCoordinationMessageMachine

noncomputable def auditedEncodedCoordinationMessageRefinement :
    Machine.StochasticRefinement auditedEncodedCoordinationMessageMachine
      coordinationMessageMachine :=
  encodedCoordinationMessageRefinement.compose
    (Machine.audited.refinement encodedCoordinationMessageMachine)

noncomputable def auditedEncodedTalkProtocolLawLift :
    auditedEncodedCoordinationMessageRefinement.EventBatchLawFamilyLift
      TalkProtocolStrategy talkProtocolLawFamily :=
  Machine.StochasticRefinement.EventBatchLawFamilyLift.compose
    encodedTalkProtocolLawLift
    (Machine.audited.liftEventBatchLawFamily
      encodedCoordinationMessageMachine encodedTalkProtocolLawLift.impl)

theorem auditedEncodedCoordinationMessageTraceUtility_bound
    (player : TalkPlayer)
    (trace : auditedEncodedCoordinationMessageMachine.EventBatchTrace) :
    |Machine.eventBatchTraceUtility
        auditedEncodedCoordinationMessageMachine (fun _ => 0) trace player| ≤
      1 := by
  rcases trace with ⟨_batches, state⟩
  rcases state with ⟨messageState, _auditWrapper⟩
  rcases messageState with ⟨source, _pending, _delivered⟩
  rcases source with ⟨rowAction, colAction, audit⟩
  cases rowAction <;> cases colAction <;> cases player <;>
    simp [Machine.eventBatchTraceUtility,
      auditedEncodedCoordinationMessageMachine, Machine.audited,
      encodedCoordinationMessageMachine, Machine.messageInFlight,
      encodedCoordinationMachine, Machine.RoundView.optionOutcomeUtility,
      EncodedCoordinationState.outcome?]
  all_goals split <;> norm_num

theorem auditedEncodedTalkProtocol_projectTrace_eq
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player) :
    PMF.map auditedEncodedCoordinationMessageRefinement.projectEventBatchTrace
        ((Machine.eventBatchTraceKernelGame
          auditedEncodedCoordinationMessageMachine TalkProtocolStrategy
          auditedEncodedTalkProtocolLawLift.impl (fun _ => 0) 6)
          |>.outcomeKernel profile) =
      ((Machine.eventBatchTraceKernelGame
          coordinationMessageMachine TalkProtocolStrategy
          talkProtocolLawFamily (fun _ => 0) 6)
          |>.outcomeKernel profile) := by
  exact
    auditedEncodedCoordinationMessageRefinement
      |>.eventBatchTraceKernelGame_projectTrace_eq
        auditedEncodedTalkProtocolLawLift (fun _ => 0) 6 profile

theorem auditedEncodedTalkProtocol_eu_eq_cheapTalk
    (profile : ∀ player : TalkPlayer, TalkProtocolStrategy player)
    (player : TalkPlayer) :
    (Machine.eventBatchTraceKernelGame
        auditedEncodedCoordinationMessageMachine TalkProtocolStrategy
        auditedEncodedTalkProtocolLawLift.impl (fun _ => 0) 6).eu
      profile player =
      coordinationCheapTalkGame.eu profile player := by
  have h :=
    (auditedEncodedCoordinationMessageRefinement
      |>.eventBatchTraceEUMorphismOfBounded
        auditedEncodedTalkProtocolLawLift (fun _ => 0) 6
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedEncodedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound).eu_preserved profile player
  rw [← h]
  exact talkProtocolTraceGame_eu_eq_cheapTalk profile player

theorem auditedEncodedFaithfulRowSignalTalkProtocol_nash :
    (Machine.eventBatchTraceKernelGame
        auditedEncodedCoordinationMessageMachine TalkProtocolStrategy
        auditedEncodedTalkProtocolLawLift.impl (fun _ => 0) 6).IsNash
      faithfulRowSignalTalkProtocolProfile := by
  exact
    auditedEncodedCoordinationMessageRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        auditedEncodedTalkProtocolLawLift (fun _ => 0) 6
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        auditedEncodedCoordinationMessageTraceUtility_bound
        coordinationMessageTraceUtility_bound
        faithfulRowSignalTalkProtocol_nash

theorem rowSignalTalkProtocol_nash :
    (Machine.eventBatchTraceKernelGame
        coordinationMessageMachine TalkProtocolStrategy
        talkProtocolLawFamily (fun _ => 0) 6).IsNash
      rowSignalTalkProtocolProfile := by
  intro player alternative
  cases player
  · rw [talkProtocolTraceGame_eu_six, talkProtocolTraceGame_eu_six]
    have hbase :
        talkProtocolAction rowSignalTalkProtocolProfile TalkPlayer.row =
          talkProtocolAction rowSignalTalkProtocolProfile TalkPlayer.col := by
      rfl
    rw [if_pos hbase]
    split <;> norm_num
  · rw [talkProtocolTraceGame_eu_six, talkProtocolTraceGame_eu_six]
    have hbase :
        talkProtocolAction rowSignalTalkProtocolProfile TalkPlayer.row =
          talkProtocolAction rowSignalTalkProtocolProfile TalkPlayer.col := by
      rfl
    rw [if_pos hbase]
    split <;> norm_num

example :
    talkProtocolAction rowSignalTalkProtocolProfile TalkPlayer.row = true := by
  rfl

example :
    talkProtocolAction rowSignalTalkProtocolProfile TalkPlayer.col = true := by
  rfl

end Refinement
end Examples
end Vegas

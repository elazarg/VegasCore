/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.Sequential
import GameTheory.Protocol.FiniteHorizon

/-! # A late-turn game with leaked openings

A sender has a private type `(v, s)`: a committed bit `v`, which is one with
probability `9/20`, and an independent label `s` drawn uniformly from three
values. The sender can open `v` at a protected turn, where the opening is
always included, or wait. Having waited, it can send the opening at a first or
a second late turn, or never. A late opening is included with probability
`q`, strictly between zero and one, by a coin independent of everything else.

A listener is activated between the two late turns and sees every opening
pending at that moment. An opening sent at the first late turn is still
pending then, so the listener learns `v` from it even when it is later dropped.
After the opening resolves the listener answers. After a successful opening it
plays a safe answer, worth `2/5` to it, or guesses the label, worth one when
correct. After a failure it guesses the bit and is paid when correct.

With reward scale `R`, forfeit `D` and drop charge `c`, the sender
gets `R/2` under the safe answer; under any label guess, labels `A` and `B` get
`R` and label `C` gets nothing. After a failure the sender gets `R` under the
bit guess `1` if its label is `A`, and `R` under the bit guess `0` if its label
is `B`. The sender pays `D` when the opening fails and, in addition, `c` when a
late opening it sent was dropped.

The intended game is the same game in which the sender can only open at the
protected turn. Both games share states, information and payoffs; they differ
only in the sender's menu at the protected turn. The prior and the listener's
payoffs are fixed; the parameters `R`, `D`, `c` and `q` are arbitrary.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-- The parameters of the late-turn game: the sender's reward scale `R`, the
forfeit `D` on a failed opening, the charge `c` on a dropped late opening, and
the inclusion probability `q` of a late opening. -/
structure LateLeakParameters where
  /-- The reward scale `R`. -/
  reward : ℝ
  /-- The forfeit `D` charged when the opening fails. -/
  forfeit : ℝ
  /-- The charge `c` on a late opening that was sent and dropped. -/
  dropCharge : ℝ
  /-- The inclusion probability `q` of a late opening. -/
  inclusion : Set.Ioo (0 : ℝ) 1

variable {G : LateLeakParameters}

/-- The sender owns the committed value; the listener answers. -/
inductive LateLeakRole
  | sender
  | listener
  deriving DecidableEq, Fintype

/-- The sender's hidden label, which the listener may try to guess. -/
inductive LateLeakLabel
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- A sender type: the committed bit and the hidden label. -/
abbrev LateLeakType := Bool × LateLeakLabel

/-- How the sender's opening resolved. -/
inductive LateLeakResolution
  /-- Opened at the protected turn. -/
  | protectedOpen
  /-- Sent at the first late turn and included. -/
  | firstIncluded
  /-- Sent at the first late turn and dropped after the listener saw it. -/
  | firstDropped
  /-- Sent at the second late turn and included. -/
  | secondIncluded
  /-- Sent at the second late turn and dropped. -/
  | secondDropped
  /-- Never sent. -/
  | withheld
  deriving DecidableEq, Fintype

/-- The listener's answers. -/
inductive LateLeakAnswer
  /-- The safe answer after a successful opening. -/
  | safe
  /-- A guess of the sender's label after a successful opening. -/
  | guess (label : LateLeakLabel)
  /-- A guess of the committed bit after a failed opening. -/
  | failure (bit : Bool)
  deriving DecidableEq, Fintype

/-- A move of either player. -/
inductive LateLeakMove
  /-- The sender opens now (`true`) or waits (`false`). -/
  | opening (now : Bool)
  /-- The listener's answer. -/
  | reply (answer : LateLeakAnswer)
  deriving DecidableEq, Fintype

/-- Execution states. Every state records the path that reached it. -/
inductive LateLeakState
  | initial
  | protectedTurn (secret : LateLeakType)
  | firstLate (secret : LateLeakType)
  | secondLate (secret : LateLeakType)
  | answering (secret : LateLeakType) (resolution : LateLeakResolution)
  | finished (secret : LateLeakType) (resolution : LateLeakResolution)
      (answer : LateLeakAnswer)
  deriving DecidableEq, Fintype

/-- What the listener knows when it answers. -/
inductive LateLeakSignal
  | protectedSuccess (bit : Bool)
  | firstSuccess (bit : Bool)
  | secondSuccess (bit : Bool)
  /-- The opening failed after the listener saw it pending. -/
  | leakedFailure (bit : Bool)
  /-- The opening failed and the listener never saw it. -/
  | silentFailure
  deriving DecidableEq, Fintype

/-- A player's information state. The sender sees the whole state; the
listener sees only its signal and its own answer. -/
inductive LateLeakView
  | full (state : LateLeakState)
  | idle
  | asked (signal : LateLeakSignal)
  | answered (signal : LateLeakSignal) (answer : LateLeakAnswer)
  deriving DecidableEq

/-- Whether an opening resolved successfully. -/
def LateLeakResolution.succeeded : LateLeakResolution → Bool
  | .protectedOpen | .firstIncluded | .secondIncluded => true
  | _ => false

/-- Whether a late opening was sent and dropped. -/
def LateLeakResolution.droppedLate : LateLeakResolution → Bool
  | .firstDropped | .secondDropped => true
  | _ => false

/-- What the listener learns from a resolution: a pending first-turn opening
reveals the committed bit even when it is dropped. -/
def lateLeakSignal (secret : LateLeakType) : LateLeakResolution → LateLeakSignal
  | .protectedOpen => .protectedSuccess secret.1
  | .firstIncluded => .firstSuccess secret.1
  | .secondIncluded => .secondSuccess secret.1
  | .firstDropped => .leakedFailure secret.1
  | .secondDropped => .silentFailure
  | .withheld => .silentFailure

/-- Whether a signal reports a successful opening. -/
def LateLeakSignal.success : LateLeakSignal → Bool
  | .leakedFailure _ | .silentFailure => false
  | _ => true

/-- The answers available after a signal. -/
def LateLeakAnswer.fits : LateLeakAnswer → LateLeakSignal → Bool
  | .failure _, signal => !signal.success
  | _, signal => signal.success

/-- The player who moves at a state; nobody moves initially or at the end. -/
def LateLeakState.actor : LateLeakState → Option LateLeakRole
  | .protectedTurn _ | .firstLate _ | .secondLate _ => some .sender
  | .answering _ _ => some .listener
  | _ => none

/-- The coordinate a transition reads. -/
def LateLeakState.mover (state : LateLeakState) : LateLeakRole :=
  state.actor.getD .sender

/-- Play has stopped. -/
def LateLeakState.IsFinished : LateLeakState → Prop
  | .finished _ _ _ => True
  | _ => False

instance : DecidablePred LateLeakState.IsFinished := fun state => by
  cases state <;> unfold LateLeakState.IsFinished <;> infer_instance

/-- The listener's answer read from a move; other moves read as the safe
answer, which no legal play uses. -/
def lateLeakReplyOf : Option LateLeakMove → LateLeakAnswer
  | some (.reply answer) => answer
  | _ => .safe

/-- The prior over sender types: `P(v = 1) = 9/20`, label uniform. -/
def lateLeakPrior : PMF LateLeakType :=
  PMF.ofFintype (fun secret => ((if secret.1 then 3 / 20 else 11 / 60 : NNReal) : ENNReal)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : Fintype.card LateLeakLabel = 3 := rfl
    rw [this]
    norm_num)

/-- The inclusion probability `q` of a late opening. -/
def lateLeakInclusionProb (G : LateLeakParameters) : ℝ := G.inclusion

theorem lateLeakInclusionProb_pos (G : LateLeakParameters) : 0 < lateLeakInclusionProb G :=
  G.inclusion.2.1

theorem lateLeakInclusionProb_lt_one (G : LateLeakParameters) : lateLeakInclusionProb G < 1 :=
  G.inclusion.2.2

/-- The margins under which deferring the opening pays. The reward scale is
positive; sending at the second late turn strictly beats never sending,
`q (D - R) > (1 - q) c`; and the full reward `R` that a guessing listener pays
after a late inclusion beats the safe answer's `R/2` at the protected turn,
`q R - (1 - q) (D + c) > R/2`. -/
structure LateLeakParameters.DeferralPays (G : LateLeakParameters) : Prop where
  reward_pos : 0 < G.reward
  send_beats_withhold :
    (1 - lateLeakInclusionProb G) * G.dropCharge < lateLeakInclusionProb G * (G.forfeit - G.reward)
  guess_beats_safe :
    G.reward / 2 < lateLeakInclusionProb G * G.reward -
      (1 - lateLeakInclusionProb G) * (G.forfeit + G.dropCharge)

/-- The content-blind inclusion coin of a late opening: included with
probability `q`. -/
def lateLeakInclusion (G : LateLeakParameters) : PMF Bool :=
  PMF.ofFintype (fun included =>
      ENNReal.ofReal (if included then lateLeakInclusionProb G else 1 - lateLeakInclusionProb G))
    (by
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add (lateLeakInclusionProb_pos G).le
          (sub_nonneg.mpr (lateLeakInclusionProb_lt_one G).le),
        add_sub_cancel, ENNReal.ofReal_one])

/-- The successor law of a state given the mover's contribution. -/
def lateLeakAdvance (G : LateLeakParameters) :
    LateLeakState → Option LateLeakMove → PMF LateLeakState
  | .initial, _ => lateLeakPrior.map .protectedTurn
  | .protectedTurn secret, choice =>
      PMF.pure (if choice = some (.opening true) then .answering secret .protectedOpen
        else .firstLate secret)
  | .firstLate secret, choice =>
      if choice = some (.opening true) then
        (lateLeakInclusion G).map fun included =>
          .answering secret (if included then .firstIncluded else .firstDropped)
      else PMF.pure (.secondLate secret)
  | .secondLate secret, choice =>
      if choice = some (.opening true) then
        (lateLeakInclusion G).map fun included =>
          .answering secret (if included then .secondIncluded else .secondDropped)
      else PMF.pure (.answering secret .withheld)
  | .answering secret resolution, choice =>
      PMF.pure (.finished secret resolution (lateLeakReplyOf choice))
  | .finished secret resolution answer, _ => PMF.pure (.finished secret resolution answer)

/-- What each player sees of a state. -/
def lateLeakView : LateLeakRole → LateLeakState → LateLeakView
  | .sender, state => .full state
  | .listener, .answering secret resolution => .asked (lateLeakSignal secret resolution)
  | .listener, .finished secret resolution answer =>
      .answered (lateLeakSignal secret resolution) answer
  | .listener, _ => .idle

/-- The options at an information state. With `late = false` the sender can
only open at the protected turn. -/
def lateLeakMenu (late : Bool) : LateLeakView → Set (Option LateLeakMove)
  | .full (.protectedTurn _) => {choice | ∃ now, choice = some (.opening now) ∧ (late || now)}
  | .full (.firstLate _) => {choice | ∃ now, choice = some (.opening now)}
  | .full (.secondLate _) => {choice | ∃ now, choice = some (.opening now)}
  | .asked signal => {choice | ∃ answer, choice = some (.reply answer) ∧ answer.fits signal}
  | _ => {none}

/-- A legal move at each decision state. -/
def lateLeakDefaultMove : LateLeakState → LateLeakMove
  | .answering secret resolution =>
      .reply (if (lateLeakSignal secret resolution).success then .safe else .failure true)
  | _ => .opening true

/-- The execution protocol. -/
@[reducible]
def lateLeakExecution (G : LateLeakParameters) (late : Bool) : ExecutionProtocol LateLeakRole where
  State := LateLeakState
  Action _ := LateLeakMove
  init := .initial
  active state who := state.actor = some who
  available state who := {move | some move ∈ lateLeakMenu late (lateLeakView who state)}
  terminal state := state.IsFinished
  step state joint := lateLeakAdvance G state (joint.1 state.mover)
  progress state running := by
    refine ⟨fun who => if state.actor = some who then some (lateLeakDefaultMove state) else none,
      fun who => ?_⟩
    cases state with
    | initial => simp [LateLeakState.actor]
    | protectedTurn secret =>
        cases who <;> simp [LateLeakState.actor, lateLeakView, lateLeakMenu, lateLeakDefaultMove]
    | firstLate secret =>
        cases who <;> simp [LateLeakState.actor, lateLeakView, lateLeakMenu, lateLeakDefaultMove]
    | secondLate secret =>
        cases who <;> simp [LateLeakState.actor, lateLeakView, lateLeakMenu, lateLeakDefaultMove]
    | answering secret resolution =>
        cases who <;> cases resolution <;>
          simp [LateLeakState.actor, lateLeakView, lateLeakMenu, lateLeakDefaultMove,
            lateLeakSignal, LateLeakSignal.success, LateLeakAnswer.fits]
    | finished secret resolution answer => exact (running trivial).elim

/-- Each player's view is emitted as its private signal and replaces its
information state. -/
@[reducible]
def lateLeakSignals (G : LateLeakParameters) (late : Bool) :
    InfoSignals (lateLeakExecution G late) where
  PublicSignal := Unit
  PrivateSignal _ := LateLeakView
  initialPublic := ()
  initialPrivate who := lateLeakView who .initial
  publicSignal _ := ()
  privateSignal who event := lateLeakView who event.target
  InfoState _ := LateLeakView
  initInfo _ signal _ := signal
  pushInfo _ _ _ signal _ := signal

theorem lateLeak_infoOf (G : LateLeakParameters) (late : Bool) (who : LateLeakRole) :
    ∀ {state : LateLeakState} (trace : (lateLeakExecution G late).Trace state),
      (lateLeakSignals G late).infoOf who trace = lateLeakView who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- The information model. -/
@[reducible]
def lateLeakModel (G : LateLeakParameters) (late : Bool) :
    InformationModel (lateLeakExecution G late) where
  toInfoSignals := lateLeakSignals G late
  menu _ view := lateLeakMenu late view
  menu_adequate who state trace choice := by
    rw [lateLeak_infoOf]
    cases who <;> cases state <;> cases choice <;>
      simp [lateLeakView, lateLeakMenu, LegalOption, LateLeakState.actor]

instance (late : Bool) (who : LateLeakRole) :
    DecidableEq ((lateLeakModel G late).InfoState who) :=
  inferInstanceAs (DecidableEq LateLeakView)

/-- The sender's payoff at a final state, before charges. -/
def lateLeakSenderBase (G : LateLeakParameters) (label : LateLeakLabel)
    (resolution : LateLeakResolution)
    (answer : LateLeakAnswer) : ℝ :=
  if resolution.succeeded then
    match answer with
    | .safe => G.reward / 2
    | .guess _ => if label = .c then 0 else G.reward
    | .failure _ => 0
  else
    match answer with
    | .failure true => if label = .a then G.reward else 0
    | .failure false => if label = .b then G.reward else 0
    | _ => 0

/-- The sender's payoff: base utility, minus the forfeit `D` on a failed
opening, minus the drop charge `c` on a dropped late opening. -/
def lateLeakSenderPayoff (G : LateLeakParameters) (secret : LateLeakType)
    (resolution : LateLeakResolution)
    (answer : LateLeakAnswer) : ℝ :=
  lateLeakSenderBase G secret.2 resolution answer -
    (if resolution.succeeded then 0 else G.forfeit) -
      (if resolution.droppedLate then G.dropCharge else 0)

/-- The listener's payoff: `2/5` for the safe answer, one for a correct guess. -/
def lateLeakListenerPayoff (secret : LateLeakType) (resolution : LateLeakResolution)
    (answer : LateLeakAnswer) : ℝ :=
  if resolution.succeeded then
    match answer with
    | .safe => 2 / 5
    | .guess label => if label = secret.2 then 1 else 0
    | .failure _ => 0
  else
    match answer with
    | .failure bit => if bit = secret.1 then 1 else 0
    | _ => 0

/-- Payoffs at a state; only final states pay. -/
def lateLeakStatePayoff (G : LateLeakParameters) : LateLeakRole → LateLeakState → ℝ
  | .sender, .finished secret resolution answer => lateLeakSenderPayoff G secret resolution answer
  | .listener, .finished secret resolution answer =>
      lateLeakListenerPayoff secret resolution answer
  | _, _ => 0

/-- Payoffs on histories. -/
def lateLeakPayoff (G : LateLeakParameters) (late : Bool) (who : LateLeakRole)
    (history : (lateLeakExecution G late).History) : ℝ :=
  lateLeakStatePayoff G who history.state

/-! ## Tree structure -/

/-- The state a transition into a state comes from. -/
def lateLeakParent : LateLeakState → LateLeakState
  | .initial => .initial
  | .protectedTurn _ => .initial
  | .firstLate secret => .protectedTurn secret
  | .secondLate secret => .firstLate secret
  | .answering secret .protectedOpen => .protectedTurn secret
  | .answering secret .firstIncluded => .firstLate secret
  | .answering secret .firstDropped => .firstLate secret
  | .answering secret _ => .secondLate secret
  | .finished secret resolution _ => .answering secret resolution

/-- The move that led into a state. -/
def lateLeakLastMove : LateLeakState → Option LateLeakMove
  | .initial | .protectedTurn _ => none
  | .firstLate _ | .secondLate _ => some (.opening false)
  | .answering _ .withheld => some (.opening false)
  | .answering _ _ => some (.opening true)
  | .finished _ _ answer => some (.reply answer)

/-- The joint action that led into a state. -/
def lateLeakLastJoint (state : LateLeakState) : LateLeakRole → Option LateLeakMove :=
  fun who => if (lateLeakParent state).actor = some who then lateLeakLastMove state else none

private theorem joint_eq_of_legal {late : Bool} {source : LateLeakState}
    {joint : LateLeakRole → Option LateLeakMove}
    (legal : (lateLeakExecution G late).Legal source joint) :
    joint = fun who => if source.actor = some who then joint who else none := by
  funext who
  by_cases acting : source.actor = some who
  · simp [acting]
  · simp only [acting, ite_false]
    exact LegalOption.eq_none_of_inactive (E := lateLeakExecution G late) (joint who)
      ((lateLeakExecution G late).legalOption_of_legal legal who) acting

theorem lateLeak_mover_choice_of_legal {late : Bool} {source : LateLeakState}
    {joint : LateLeakRole → Option LateLeakMove}
    (legal : (lateLeakExecution G late).Legal source joint) {who : LateLeakRole}
    (acting : source.actor = some who) :
    ∃ move, joint who = some move ∧ some move ∈ lateLeakMenu late (lateLeakView who source) := by
  obtain ⟨move, chosen⟩ := LegalOption.exists_eq_some_of_active (E := lateLeakExecution G late)
    (joint who) ((lateLeakExecution G late).legalOption_of_legal legal who) acting
  have option := (lateLeakExecution G late).legalOption_of_legal legal who
  rw [chosen] at option
  exact ⟨move, chosen, option.2⟩

/-- A realized transition comes from the parent state by the last joint. -/
theorem lateLeak_step_parent {late : Bool} {source target : LateLeakState}
    {joint : LateLeakRole → Option LateLeakMove}
    (legal : (lateLeakExecution G late).Legal source joint)
    (realized : target ∈ ((lateLeakExecution G late).step source ⟨joint, legal⟩).support) :
    source = lateLeakParent target ∧ joint = lateLeakLastJoint target := by
  have shape := joint_eq_of_legal legal
  change target ∈ (lateLeakAdvance G source (joint source.mover)).support at realized
  cases source with
  | initial =>
      rw [lateLeakAdvance, PMF.support_map] at realized
      obtain ⟨secret, _, rfl⟩ := realized
      refine ⟨rfl, ?_⟩
      rw [shape]
      funext who
      simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent]
  | protectedTurn secret =>
      obtain ⟨move, chosen, menu⟩ := lateLeak_mover_choice_of_legal legal (who := .sender) rfl
      simp only [lateLeakView, lateLeakMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨now, hmove, -⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, chosen,
        lateLeakAdvance, PMF.mem_support_pure_iff] at realized
      subst realized
      rw [shape]
      cases now <;> exact ⟨by simp [lateLeakParent], by
        funext who
        cases who <;>
          simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent, lateLeakLastMove, chosen]⟩
  | firstLate secret =>
      obtain ⟨move, chosen, menu⟩ := lateLeak_mover_choice_of_legal legal (who := .sender) rfl
      simp only [lateLeakView, lateLeakMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨now, hmove⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, chosen,
        lateLeakAdvance] at realized
      rw [shape]
      cases now
      · simp only [ite_false, Option.some.injEq, LateLeakMove.opening.injEq,
          Bool.false_eq_true, PMF.mem_support_pure_iff] at realized
        subst realized
        refine ⟨rfl, ?_⟩
        funext who
        cases who <;> simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent,
          lateLeakLastMove, chosen]
      · simp only [ite_true, PMF.support_map] at realized
        obtain ⟨included, _, rfl⟩ := realized
        cases included <;> refine ⟨rfl, ?_⟩ <;> funext who <;> cases who <;>
          simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent, lateLeakLastMove, chosen]
  | secondLate secret =>
      obtain ⟨move, chosen, menu⟩ := lateLeak_mover_choice_of_legal legal (who := .sender) rfl
      simp only [lateLeakView, lateLeakMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨now, hmove⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, chosen,
        lateLeakAdvance] at realized
      rw [shape]
      cases now
      · simp only [ite_false, Option.some.injEq, LateLeakMove.opening.injEq,
          Bool.false_eq_true, PMF.mem_support_pure_iff] at realized
        subst realized
        refine ⟨rfl, ?_⟩
        funext who
        cases who <;> simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent,
          lateLeakLastMove, chosen]
      · simp only [ite_true, PMF.support_map] at realized
        obtain ⟨included, _, rfl⟩ := realized
        cases included <;> refine ⟨rfl, ?_⟩ <;> funext who <;> cases who <;>
          simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent, lateLeakLastMove, chosen]
  | answering secret resolution =>
      obtain ⟨move, chosen, menu⟩ := lateLeak_mover_choice_of_legal legal (who := .listener) rfl
      simp only [lateLeakView, lateLeakMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨answer, hmove, -⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [LateLeakState.mover, LateLeakState.actor, Option.getD_some, chosen,
        lateLeakAdvance, PMF.mem_support_pure_iff, lateLeakReplyOf] at realized
      subst realized
      refine ⟨rfl, ?_⟩
      rw [shape]
      funext who
      cases who <;> simp [LateLeakState.actor, lateLeakLastJoint, lateLeakParent,
        lateLeakLastMove, chosen]
  | finished secret resolution answer => exact (legal.1 trivial).elim

theorem lateLeak_initial_not_reached {late : Bool} (source : LateLeakState)
    (joint : LateLeakRole → Option LateLeakMove)
    (legal : (lateLeakExecution G late).Legal source joint) :
    LateLeakState.initial ∉ ((lateLeakExecution G late).step source ⟨joint, legal⟩).support := by
  intro reached
  have parent := (lateLeak_step_parent legal reached).1
  cases source with
  | initial =>
      change LateLeakState.initial ∈
        (lateLeakAdvance G .initial (joint LateLeakState.initial.mover)).support at reached
      rw [lateLeakAdvance, PMF.support_map] at reached
      obtain ⟨_, _, impossible⟩ := reached
      cases impossible
  | finished => exact legal.1 trivial
  | _ => cases parent

/-- Every reachable state has exactly one history. -/
theorem lateLeak_treeShaped (G : LateLeakParameters) (late : Bool) :
    (lateLeakExecution G late).IsTreeShaped :=
  ExecutionProtocol.isTreeShaped_of_predecessor_unique
    (fun source joint legal => lateLeak_initial_not_reached source joint legal)
    (fun firstLegal secondLegal firstRealized secondRealized => by
      obtain ⟨firstSource, firstJoint⟩ := lateLeak_step_parent firstLegal firstRealized
      obtain ⟨secondSource, secondJoint⟩ := lateLeak_step_parent secondLegal secondRealized
      exact ⟨firstSource.trans secondSource.symm, firstJoint.trans secondJoint.symm⟩)

/-- Histories are determined by the state they reach. -/
theorem lateLeak_history_eq_of_state_eq {late : Bool}
    {first second : (lateLeakExecution G late).History} (same : first.state = second.state) :
    first = second := by
  rcases first with ⟨state, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  change state = secondState at same
  subst same
  have := (lateLeak_treeShaped G late state).allEq firstTrace secondTrace
  subst this
  rfl

theorem lateLeak_state_injective (G : LateLeakParameters) (late : Bool) :
    Function.Injective (fun history : (lateLeakExecution G late).History => history.state) :=
  fun _ _ same => lateLeak_history_eq_of_state_eq same

instance (late : Bool) : Finite (lateLeakExecution G late).History :=
  Finite.of_injective _ (lateLeak_state_injective G late)

/-- The number of transitions from the initial state. -/
def lateLeakDepth : LateLeakState → ℕ
  | .initial => 0
  | .protectedTurn _ => 1
  | .firstLate _ => 2
  | .secondLate _ => 3
  | .answering _ .protectedOpen => 2
  | .answering _ .firstIncluded => 3
  | .answering _ .firstDropped => 3
  | .answering _ _ => 4
  | .finished _ .protectedOpen _ => 3
  | .finished _ .firstIncluded _ => 4
  | .finished _ .firstDropped _ => 4
  | .finished _ _ _ => 5

theorem lateLeak_trace_length (G : LateLeakParameters) (late : Bool) :
    ∀ {state : LateLeakState} (trace : (lateLeakExecution G late).Trace state),
      trace.length = lateLeakDepth state
  | _, .start => rfl
  | _, .extend (target := target) prior joint legal realized => by
      have earlier := lateLeak_trace_length G late prior
      obtain ⟨rfl, -⟩ := lateLeak_step_parent legal realized
      rw [ExecutionProtocol.Trace.length, earlier]
      have reached := lateLeak_initial_not_reached _ joint legal
      cases target with
      | initial => exact (reached realized).elim
      | answering secret resolution => cases resolution <;> rfl
      | finished secret resolution answer => cases resolution <;> rfl
      | _ => rfl

theorem lateLeak_bounded (G : LateLeakParameters) (late : Bool) :
    (lateLeakExecution G late).BoundedHorizon 5 := by
  intro state trace enough
  rw [lateLeak_trace_length G late trace] at enough
  cases state with
  | finished => trivial
  | answering secret resolution => cases resolution <;> simp [lateLeakDepth] at enough
  | _ => simp [lateLeakDepth] at enough

/-- Every play stops within five transitions. -/
theorem lateLeak_terminates (G : LateLeakParameters) (late : Bool) :
    (lateLeakExecution G late).WellFoundedHistories :=
  (lateLeak_bounded G late).wellFoundedHistories

/-- The depth of the decision states with a given view. -/
def lateLeakViewDepth : LateLeakView → ℕ
  | .full state => lateLeakDepth state
  | .asked (.protectedSuccess _) => 2
  | .asked (.firstSuccess _) => 3
  | .asked (.leakedFailure _) => 3
  | .asked _ => 4
  | _ => 0

private theorem depth_eq_viewDepth (late : Bool) (who : LateLeakRole) (state : LateLeakState)
    (move : LateLeakMove) (menu : some move ∈ lateLeakMenu late (lateLeakView who state)) :
    lateLeakDepth state = lateLeakViewDepth (lateLeakView who state) := by
  cases who with
  | sender => rfl
  | listener =>
      cases state with
      | answering secret resolution => cases resolution <;> rfl
      | _ => simp [lateLeakView, lateLeakMenu] at menu

/-- Histories in one decision information set have a common depth, so none
continues to another. -/
theorem lateLeak_antichain (G : LateLeakParameters) (late : Bool) :
    (lateLeakModel G late).DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel path
  obtain ⟨_, _, move, menu⟩ := site.2
  have depthOf (history : (lateLeakModel G late).InformationHistory who site.1) :
      history.1.trace.length = lateLeakViewDepth site.1 := by
    have view : lateLeakView who history.1.state = site.1 := by
      rw [← lateLeak_infoOf G late who history.1.trace]
      exact history.2
    rw [lateLeak_trace_length, depth_eq_viewDepth late who _ move (by rw [view]; exact menu),
      view]
  have increases := path.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increases
  rw [depthOf first, depthOf second] at increases
  omega

end Vegas

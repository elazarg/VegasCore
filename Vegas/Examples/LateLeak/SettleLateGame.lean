/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Game

/-! # The late-turn game under a settle-late builder

This game places the sender and listener of the late-turn game in an
asynchronous runtime with a builder that settles every late packet at once,
after the sender's last late activation, and with a stateless leak rule.

A sender of type `(v, s)` has a protected turn, a first late turn and a second
late turn. At each activation it emits at most one packet: nothing, a raw
signal carrying one bit, or an opening of its committed bit `v`.

* At the protected turn an opening is included surely. The sender is then
  activated once more and may add a raw signal; the listener answers after
  seeing the signal, if any.
* Otherwise the sender may signal at the protected turn and emits again at the
  first late turn. The listener then has one observe-only activation: its
  answer is not yet ready, it may send a raw packet of its own, which costs it
  c_L and is never included, and it sees every pending packet of the sender
  with one exception: each pending opening is seen independently with
  probability `λ`. The sender sees the listener's packet when it emits at the
  second late turn, where it may also open a second time.
* One inclusion step then settles every late packet. A sole late opening is
  included with probability `q`. Two late openings compete under the Luce law
  forced by a builder blind to late packets: each is included with
  probability `q / (1 + q)`, so one of them with probability `2q / (1 + q)`.
* An opening that was not included stays pending, so the listener sees it with
  probability `λ` when it answers, unless it already saw it. The ledger shows
  the serial of the included opening, which is the number of packets the
  sender emitted before it.

The capped escrow charges the sender `c` once if any packet of it was not
included: a raw signal, a dropped opening, or a second opening. A failed
reveal forfeits `D`. Payoffs, the prior and the listener's answers are those of
the late-turn game: after a success the listener answers safely or guesses the
label; after a failure it guesses the bit.

Every observation is a function of the observer and the pending pool: the
rule never depends on the content of an opening beyond showing it, and an
opening pending at two activations is drawn afresh at each.

The intended game is the same game in which the sender opens at the protected
turn and adds no raw signal.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-- The parameters of the settle-late game: those of the late-turn game, the
probability `λ` that the leak rule shows a pending opening at one activation,
and the cost c_L of the listener's raw packet. -/
structure SettleLateParameters extends LateLeakParameters where
  /-- The probability `λ` that a pending opening is seen at one activation. -/
  leak : Set.Ioo (0 : ℝ) 1
  /-- The listener's cost c_L of emitting its raw packet. -/
  packetCost : ℝ

variable {G : SettleLateParameters}

/-- A packet the sender emits at one activation. -/
inductive SettleLatePacket
  /-- No packet. -/
  | silent
  /-- A raw signal carrying one bit. -/
  | signal (word : Bool)
  /-- An opening of the committed bit. -/
  | opening
  deriving DecidableEq, Fintype

/-- What the sender emitted at the first late turn, and whether the
observe-only activation saw a pending opening. -/
inductive SettleLateFirst
  | silent
  | signal (word : Bool)
  | opening (seen : Bool)
  deriving DecidableEq, Fintype

/-- The two late turns. -/
inductive SettleLateSlot
  | first
  | second
  deriving DecidableEq, Fintype

/-- How the late inclusion step settled: the included opening, if any, and
which dropped openings the listener sees when it answers. -/
structure SettleLateFate where
  /-- The late turn whose opening was included. -/
  included : Option SettleLateSlot
  /-- The listener sees the dropped first-turn opening when it answers. -/
  firstExposed : Bool
  /-- The listener sees the dropped second-turn opening when it answers. -/
  secondExposed : Bool
  deriving DecidableEq, Fintype

/-- A play that deferred the protected opening, up to the listener's answer. -/
structure SettleLateRecord where
  /-- The sender's type. -/
  secret : LateLeakType
  /-- The raw signal sent at the protected turn, if any. -/
  early : Option Bool
  /-- The first late turn. -/
  first : SettleLateFirst
  /-- Whether the listener emitted its raw packet. -/
  ping : Bool
  /-- The packet of the second late turn. -/
  second : SettleLatePacket
  /-- How the inclusion step settled. -/
  fate : SettleLateFate
  deriving DecidableEq, Fintype

/-- Execution states. Every state records the path that reached it. -/
inductive SettleLateState
  | initial
  | protectedTurn (secret : LateLeakType)
  /-- The sender's next activation after a protected opening. -/
  | afterProtected (secret : LateLeakType)
  /-- The listener answers after a protected opening and the raw signal, if any. -/
  | protectedAnswer (secret : LateLeakType) (talk : Option Bool)
  | protectedDone (secret : LateLeakType) (talk : Option Bool) (answer : LateLeakAnswer)
  | firstLate (secret : LateLeakType) (early : Option Bool)
  /-- The listener's observe-only activation. -/
  | watching (secret : LateLeakType) (early : Option Bool) (first : SettleLateFirst)
  | secondLate (secret : LateLeakType) (early : Option Bool) (first : SettleLateFirst)
      (ping : Bool)
  | answering (record : SettleLateRecord)
  | finished (record : SettleLateRecord) (answer : LateLeakAnswer)
  deriving DecidableEq, Fintype

/-- A move: the sender's packet, the listener's raw packet at its observe-only
activation, or the listener's answer. -/
inductive SettleLateMove
  | emit (packet : SettleLatePacket)
  | ping (sent : Bool)
  | reply (answer : LateLeakAnswer)
  deriving DecidableEq, Fintype

/-- What the observe-only activation shows of the first late turn. -/
inductive SettleLateGlimpse
  | nothing
  | signal (word : Bool)
  | opening (bit : Bool)
  deriving DecidableEq

/-- What the listener sees when it answers after the late turns. -/
structure SettleLateReport where
  /-- The raw signal sent at the protected turn, if any. -/
  early : Option Bool
  /-- What its observe-only activation showed. -/
  glimpse : SettleLateGlimpse
  /-- Whether it emitted its raw packet. -/
  ping : Bool
  /-- The serial of the included opening, if any. -/
  included : Option ℕ
  /-- The serials of dropped openings seen now. -/
  exposed : List ℕ
  /-- The raw signal sent at the second late turn, if any. -/
  talk : Option Bool
  /-- The committed bit, once an opening was seen or included. -/
  bit : Option Bool
  deriving DecidableEq

/-- A player's information state. -/
inductive SettleLateView
  | idle
  | protectedTurn (secret : LateLeakType)
  | afterProtected (secret : LateLeakType)
  | firstTurn (secret : LateLeakType) (early : Option Bool)
  /-- The sender at the second late turn sees its own packets and the
  listener's raw packet, but not what the listener saw. -/
  | secondTurn (secret : LateLeakType) (early : Option Bool) (first : SettleLatePacket)
      (ping : Bool)
  | watching (early : Option Bool) (glimpse : SettleLateGlimpse)
  | protectedAsked (bit : Bool) (talk : Option Bool)
  | asked (report : SettleLateReport)
  deriving DecidableEq

/-! ## Reading states -/

/-- The packet emitted at the first late turn. -/
def SettleLateFirst.packet : SettleLateFirst → SettleLatePacket
  | .silent => .silent
  | .signal word => .signal word
  | .opening _ => .opening

/-- Whether an opening was emitted at the first late turn. -/
def SettleLateFirst.opened : SettleLateFirst → Bool
  | .opening _ => true
  | _ => false

/-- Whether the observe-only activation saw the first-turn opening. -/
def SettleLateFirst.seen : SettleLateFirst → Bool
  | .opening seen => seen
  | _ => false

/-- Whether a raw signal was emitted at the first late turn. -/
def SettleLateFirst.signaled : SettleLateFirst → Bool
  | .signal _ => true
  | _ => false

/-- What the observe-only activation shows of the first late turn. -/
def SettleLateFirst.glimpse (bit : Bool) : SettleLateFirst → SettleLateGlimpse
  | .silent => .nothing
  | .signal word => .signal word
  | .opening seen => if seen then .opening bit else .nothing

/-- The bit carried by a raw signal. -/
def SettleLatePacket.word : SettleLatePacket → Option Bool
  | .signal word => some word
  | _ => none

/-- Whether a packet is an opening. -/
def SettleLatePacket.isOpening : SettleLatePacket → Bool
  | .opening => true
  | _ => false

/-- Whether a packet is a raw signal. -/
def SettleLatePacket.isSignal : SettleLatePacket → Bool
  | .signal _ => true
  | _ => false

/-- The packet that sends a raw signal when one is given. -/
def settleLateTalkPacket : Option Bool → SettleLatePacket
  | none => .silent
  | some word => .signal word

/-- The serial of a late opening: the number of packets emitted before it. -/
def SettleLateRecord.serial (record : SettleLateRecord) : SettleLateSlot → ℕ
  | .first => if record.early.isSome then 1 else 0
  | .second => (if record.early.isSome then 1 else 0) + (if record.first = .silent then 0 else 1)

/-- Whether a late opening was included. -/
def SettleLateRecord.succeeded (record : SettleLateRecord) : Bool :=
  record.fate.included.isSome

/-- Whether a late opening was dropped. -/
def SettleLateRecord.dropped (record : SettleLateRecord) : Bool :=
  (record.first.opened && record.fate.included != some .first) ||
    (record.second.isOpening && record.fate.included != some .second)

/-- Whether the capped escrow charges the sender: some packet of it was not
included. -/
def SettleLateRecord.charged (record : SettleLateRecord) : Bool :=
  record.early.isSome || record.first.signaled || record.second.isSignal || record.dropped

/-- What the listener sees when it answers. -/
def SettleLateRecord.report (record : SettleLateRecord) : SettleLateReport where
  early := record.early
  glimpse := record.first.glimpse record.secret.1
  ping := record.ping
  included := record.fate.included.map record.serial
  exposed := (if record.fate.firstExposed then [record.serial .first] else []) ++
    (if record.fate.secondExposed then [record.serial .second] else [])
  talk := record.second.word
  bit := if record.succeeded || record.first.seen || record.fate.firstExposed ||
      record.fate.secondExposed then some record.secret.1 else none

/-- Whether an answer fits a resolved reveal: answers after a success, bit
guesses after a failure. -/
def LateLeakAnswer.fitsOutcome (answer : LateLeakAnswer) (success : Bool) : Bool :=
  match answer with
  | .failure _ => !success
  | _ => success

/-- The player who moves at a state; nobody moves initially or at the end. -/
def SettleLateState.actor : SettleLateState → Option LateLeakRole
  | .protectedTurn _ | .afterProtected _ | .firstLate _ _ | .secondLate _ _ _ _ => some .sender
  | .protectedAnswer _ _ | .watching _ _ _ | .answering _ => some .listener
  | _ => none

/-- The coordinate a transition reads. -/
def SettleLateState.mover (state : SettleLateState) : LateLeakRole :=
  state.actor.getD .sender

/-- Play has stopped. -/
def SettleLateState.IsFinished : SettleLateState → Prop
  | .protectedDone _ _ _ | .finished _ _ => True
  | _ => False

instance : DecidablePred SettleLateState.IsFinished := fun state => by
  cases state <;> unfold SettleLateState.IsFinished <;> infer_instance

/-- The packet read from a move; other moves read as no packet. -/
def settleLatePacketOf : Option SettleLateMove → SettleLatePacket
  | some (.emit packet) => packet
  | _ => .silent

/-- The listener's raw packet read from a move. -/
def settleLatePingOf : Option SettleLateMove → Bool
  | some (.ping sent) => sent
  | _ => false

/-- The listener's answer read from a move; other moves read as the safe
answer, which no legal play uses there. -/
def settleLateReplyOf : Option SettleLateMove → LateLeakAnswer
  | some (.reply answer) => answer
  | _ => .safe

/-! ## Chance -/

/-- The probability `λ` that a pending opening is seen at one activation. -/
def settleLateLeakProb (G : SettleLateParameters) : ℝ := G.leak

theorem settleLateLeakProb_pos (G : SettleLateParameters) : 0 < settleLateLeakProb G :=
  G.leak.2.1

theorem settleLateLeakProb_lt_one (G : SettleLateParameters) : settleLateLeakProb G < 1 :=
  G.leak.2.2

/-- The leak rule at one activation: a pending opening is seen with
probability `λ`. -/
def settleLateLeakCoin (G : SettleLateParameters) : PMF Bool :=
  PMF.ofFintype (fun seen =>
      ENNReal.ofReal (if seen then settleLateLeakProb G else 1 - settleLateLeakProb G))
    (by
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rw [← ENNReal.ofReal_add (settleLateLeakProb_pos G).le
          (sub_nonneg.mpr (settleLateLeakProb_lt_one G).le),
        add_sub_cancel, ENNReal.ofReal_one])

/-- The leak rule at the answer for a dropped opening: seen with probability
`λ` if still unseen, and not drawn again otherwise. -/
def settleLateExposure (G : SettleLateParameters) (pending : Bool) : PMF Bool :=
  if pending then settleLateLeakCoin G else PMF.pure false

/-- The Luce law of two competing late openings: each is included with
probability `q / (1 + q)`. -/
def settleLateRetryLaw (G : SettleLateParameters) : PMF (Option SettleLateSlot) :=
  PMF.ofFintype (fun included => ENNReal.ofReal (match included with
      | some _ => lateLeakInclusionProb G.toLateLeakParameters /
          (1 + lateLeakInclusionProb G.toLateLeakParameters)
      | none => (1 - lateLeakInclusionProb G.toLateLeakParameters) /
          (1 + lateLeakInclusionProb G.toLateLeakParameters)))
    (by
      have q0 := lateLeakInclusionProb_pos G.toLateLeakParameters
      have q1 := lateLeakInclusionProb_lt_one G.toLateLeakParameters
      have total : Fintype.card SettleLateSlot = 2 := rfl
      rw [Fintype.sum_option, Fintype.sum_congr _ (fun _ => ENNReal.ofReal
          (lateLeakInclusionProb G.toLateLeakParameters /
            (1 + lateLeakInclusionProb G.toLateLeakParameters))) (fun _ => rfl),
        Finset.sum_const, Finset.card_univ, total, nsmul_eq_mul]
      rw [show ((2 : ℕ) : ENNReal) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (div_nonneg (by linarith) (by linarith))
          (mul_nonneg (by norm_num) (div_nonneg q0.le (by linarith)))]
      rw [← ENNReal.ofReal_one]
      congr 1
      field_simp
      ring)

/-- What the observe-only activation records of the first late turn. -/
def settleLateFirstLaw (G : SettleLateParameters) : SettleLatePacket → PMF SettleLateFirst
  | .silent => PMF.pure .silent
  | .signal word => PMF.pure (.signal word)
  | .opening => (settleLateLeakCoin G).map SettleLateFirst.opening

/-- The inclusion step and the leak at the answer. -/
def settleLateFateLaw (G : SettleLateParameters) (first : SettleLateFirst)
    (second : SettleLatePacket) : PMF SettleLateFate :=
  match first.opened, second.isOpening with
  | true, true =>
      (settleLateRetryLaw G).bind fun included =>
        (settleLateExposure G (included != some .first && !first.seen)).bind fun firstExposed =>
          (settleLateExposure G (included != some .second)).map fun secondExposed =>
            ⟨included, firstExposed, secondExposed⟩
  | true, false =>
      (lateLeakInclusion G.toLateLeakParameters).bind fun included =>
        if included then PMF.pure ⟨some .first, false, false⟩
        else (settleLateExposure G !first.seen).map fun exposed => ⟨none, exposed, false⟩
  | false, true =>
      (lateLeakInclusion G.toLateLeakParameters).bind fun included =>
        if included then PMF.pure ⟨some .second, false, false⟩
        else (settleLateLeakCoin G).map fun exposed => ⟨none, false, exposed⟩
  | false, false => PMF.pure ⟨none, false, false⟩

/-! ## The protocol -/

/-- The successor law of a state given the mover's contribution. -/
def settleLateAdvance (G : SettleLateParameters) :
    SettleLateState → Option SettleLateMove → PMF SettleLateState
  | .initial, _ => lateLeakPrior.map .protectedTurn
  | .protectedTurn secret, choice =>
      PMF.pure (if settleLatePacketOf choice = .opening then .afterProtected secret
        else .firstLate secret (settleLatePacketOf choice).word)
  | .afterProtected secret, choice =>
      PMF.pure (.protectedAnswer secret (settleLatePacketOf choice).word)
  | .protectedAnswer secret talk, choice =>
      PMF.pure (.protectedDone secret talk (settleLateReplyOf choice))
  | .protectedDone secret talk answer, _ => PMF.pure (.protectedDone secret talk answer)
  | .firstLate secret early, choice =>
      (settleLateFirstLaw G (settleLatePacketOf choice)).map (.watching secret early)
  | .watching secret early first, choice =>
      PMF.pure (.secondLate secret early first (settleLatePingOf choice))
  | .secondLate secret early first ping, choice =>
      (settleLateFateLaw G first (settleLatePacketOf choice)).map fun fate =>
        .answering ⟨secret, early, first, ping, settleLatePacketOf choice, fate⟩
  | .answering record, choice => PMF.pure (.finished record (settleLateReplyOf choice))
  | .finished record answer, _ => PMF.pure (.finished record answer)

/-- What each player sees of a state. -/
def settleLateView : LateLeakRole → SettleLateState → SettleLateView
  | .sender, .protectedTurn secret => .protectedTurn secret
  | .sender, .afterProtected secret => .afterProtected secret
  | .sender, .firstLate secret early => .firstTurn secret early
  | .sender, .secondLate secret early first ping => .secondTurn secret early first.packet ping
  | .listener, .watching secret early first => .watching early (first.glimpse secret.1)
  | .listener, .protectedAnswer secret talk => .protectedAsked secret.1 talk
  | .listener, .answering record => .asked record.report
  | _, _ => .idle

/-- The options at an information state. With `late = false` the sender opens
at the protected turn and emits nothing more. -/
def settleLateMenu (late : Bool) : SettleLateView → Set (Option SettleLateMove)
  | .protectedTurn _ =>
      {choice | ∃ packet, choice = some (.emit packet) ∧ (late = true ∨ packet = .opening)}
  | .afterProtected _ =>
      {choice | ∃ word, choice = some (.emit (settleLateTalkPacket word)) ∧
        (late = true ∨ word = none)}
  | .firstTurn _ _ => {choice | ∃ packet, choice = some (.emit packet)}
  | .secondTurn _ _ _ _ => {choice | ∃ packet, choice = some (.emit packet)}
  | .watching _ _ => {choice | ∃ sent, choice = some (.ping sent)}
  | .protectedAsked _ _ =>
      {choice | ∃ answer, choice = some (.reply answer) ∧ answer.fitsOutcome true}
  | .asked report =>
      {choice | ∃ answer, choice = some (.reply answer) ∧
        answer.fitsOutcome report.included.isSome}
  | .idle => {none}

/-- A legal move at each decision state. -/
def settleLateDefaultMove : SettleLateState → SettleLateMove
  | .protectedTurn _ => .emit .opening
  | .watching _ _ _ => .ping false
  | .protectedAnswer _ _ => .reply .safe
  | .answering record => .reply (if record.succeeded then .safe else .failure true)
  | _ => .emit .silent

/-- The execution protocol. -/
@[reducible]
def settleLateExecution (G : SettleLateParameters) (late : Bool) :
    ExecutionProtocol LateLeakRole where
  State := SettleLateState
  Action _ := SettleLateMove
  init := .initial
  active state who := state.actor = some who
  available state who := {move | some move ∈ settleLateMenu late (settleLateView who state)}
  terminal state := state.IsFinished
  step state joint := settleLateAdvance G state (joint.1 state.mover)
  progress state running := by
    refine ⟨fun who => if state.actor = some who then some (settleLateDefaultMove state) else none,
      fun who => ?_⟩
    cases state with
    | initial => simp [SettleLateState.actor]
    | protectedTurn secret =>
        cases who <;> simp [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove]
    | afterProtected secret =>
        cases who <;> simp only [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove, reduceCtorEq, Option.some.injEq, ite_true, ite_false,
          Set.mem_ofPred_eq, true_and, not_false_eq_true]
        exact ⟨none, rfl, Or.inr rfl⟩
    | firstLate secret early =>
        cases who <;> simp [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove]
    | watching secret early first =>
        cases who <;> simp [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove]
    | secondLate secret early first ping =>
        cases who <;> simp [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove]
    | protectedAnswer secret talk =>
        cases who <;> simp [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove, LateLeakAnswer.fitsOutcome]
    | answering record =>
        cases who <;> simp only [SettleLateState.actor, settleLateView, settleLateMenu,
          settleLateDefaultMove, reduceCtorEq, ite_true, ite_false,
          Set.mem_ofPred_eq, Option.some.injEq, SettleLateMove.reply.injEq, exists_eq_left',
          not_false_eq_true, true_and]
        cases included : record.fate.included <;>
          simp [SettleLateRecord.report, LateLeakAnswer.fitsOutcome, SettleLateRecord.succeeded,
            included]
    | protectedDone => exact (running trivial).elim
    | finished => exact (running trivial).elim

/-- Each player's view is emitted as its private signal and replaces its
information state. -/
@[reducible]
def settleLateSignals (G : SettleLateParameters) (late : Bool) :
    InfoSignals (settleLateExecution G late) where
  PublicSignal := Unit
  PrivateSignal _ := SettleLateView
  initialPublic := ()
  initialPrivate who := settleLateView who .initial
  publicSignal _ := ()
  privateSignal who event := settleLateView who event.target
  InfoState _ := SettleLateView
  initInfo _ signal _ := signal
  pushInfo _ _ _ signal _ := signal

theorem settleLate_infoOf (G : SettleLateParameters) (late : Bool) (who : LateLeakRole) :
    ∀ {state : SettleLateState} (trace : (settleLateExecution G late).Trace state),
      (settleLateSignals G late).infoOf who trace = settleLateView who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- The menu at a state's view is exactly the legal options there. -/
theorem settleLate_menu_iff_legal (G : SettleLateParameters) (late : Bool) (who : LateLeakRole)
    (state : SettleLateState) (choice : Option SettleLateMove) :
    choice ∈ settleLateMenu late (settleLateView who state) ↔
      LegalOption (settleLateExecution G late) state who choice := by
  cases who <;> cases state <;> cases choice <;>
    simp [settleLateView, settleLateMenu, LegalOption, SettleLateState.actor]

/-- The information model. -/
@[reducible]
def settleLateModel (G : SettleLateParameters) (late : Bool) :
    InformationModel (settleLateExecution G late) where
  toInfoSignals := settleLateSignals G late
  menu _ view := settleLateMenu late view
  menu_adequate who state trace choice := by
    rw [settleLate_infoOf]
    exact settleLate_menu_iff_legal G late who state choice

instance (late : Bool) (who : LateLeakRole) :
    DecidableEq ((settleLateModel G late).InfoState who) :=
  inferInstanceAs (DecidableEq SettleLateView)

/-! ## Payoffs -/

/-- The sender's payoff from an answer before forfeits and charges: `R/2`
under the safe answer, `R` for labels `A` and `B` under a label guess, and `R`
under the bit guess `1` for label `A` or the bit guess `0` for label `B` after a
failure. -/
def settleLateSenderBase (G : SettleLateParameters) (label : LateLeakLabel) (succeeded : Bool)
    (answer : LateLeakAnswer) : ℝ :=
  if succeeded then
    match answer with
    | .safe => G.reward / 2
    | .guess _ => if label = .c then 0 else G.reward
    | .failure _ => 0
  else
    match answer with
    | .failure true => if label = .a then G.reward else 0
    | .failure false => if label = .b then G.reward else 0
    | _ => 0

/-- The listener's payoff from an answer: `2/5` for the safe answer, one for a
correct guess. -/
def settleLateListenerBase (secret : LateLeakType) (succeeded : Bool) (answer : LateLeakAnswer) :
    ℝ :=
  if succeeded then
    match answer with
    | .safe => 2 / 5
    | .guess label => if label = secret.2 then 1 else 0
    | .failure _ => 0
  else
    match answer with
    | .failure bit => if bit = secret.1 then 1 else 0
    | _ => 0

/-- Payoffs at a state; only final states pay. The sender forfeits `D` after a
failed reveal and pays the charge `c` once if the escrow charges it; the
listener pays c_L for its raw packet. -/
def settleLateStatePayoff (G : SettleLateParameters) : LateLeakRole → SettleLateState → ℝ
  | .sender, .protectedDone secret talk answer =>
      settleLateSenderBase G secret.2 true answer - (if talk.isSome then G.dropCharge else 0)
  | .sender, .finished record answer =>
      settleLateSenderBase G record.secret.2 record.succeeded answer -
        (if record.succeeded then 0 else G.forfeit) -
          (if record.charged then G.dropCharge else 0)
  | .listener, .protectedDone secret _ answer => settleLateListenerBase secret true answer
  | .listener, .finished record answer =>
      settleLateListenerBase record.secret record.succeeded answer -
        (if record.ping then G.packetCost else 0)
  | _, _ => 0

/-- Payoffs on histories. -/
def settleLatePayoff (G : SettleLateParameters) (late : Bool) (who : LateLeakRole)
    (history : (settleLateExecution G late).History) : ℝ :=
  settleLateStatePayoff G who history.state

/-! ## Tree structure -/

/-- The state a transition into a state comes from. -/
def settleLateParent : SettleLateState → SettleLateState
  | .initial => .initial
  | .protectedTurn _ => .initial
  | .afterProtected secret => .protectedTurn secret
  | .protectedAnswer secret _ => .afterProtected secret
  | .protectedDone secret talk _ => .protectedAnswer secret talk
  | .firstLate secret _ => .protectedTurn secret
  | .watching secret early _ => .firstLate secret early
  | .secondLate secret early first _ => .watching secret early first
  | .answering record => .secondLate record.secret record.early record.first record.ping
  | .finished record _ => .answering record

/-- The move that led into a state. -/
def settleLateLastMove : SettleLateState → Option SettleLateMove
  | .initial | .protectedTurn _ => none
  | .afterProtected _ => some (.emit .opening)
  | .protectedAnswer _ talk => some (.emit (settleLateTalkPacket talk))
  | .protectedDone _ _ answer => some (.reply answer)
  | .firstLate _ early => some (.emit (settleLateTalkPacket early))
  | .watching _ _ first => some (.emit first.packet)
  | .secondLate _ _ _ ping => some (.ping ping)
  | .answering record => some (.emit record.second)
  | .finished _ answer => some (.reply answer)

/-- The joint action that led into a state. -/
def settleLateLastJoint (state : SettleLateState) : LateLeakRole → Option SettleLateMove :=
  fun who => if (settleLateParent state).actor = some who then settleLateLastMove state else none

theorem settleLateTalkPacket_word (word : Option Bool) :
    (settleLateTalkPacket word).word = word := by
  cases word <;> rfl

theorem settleLateTalkPacket_of_ne_opening {packet : SettleLatePacket}
    (closed : packet ≠ .opening) : settleLateTalkPacket packet.word = packet := by
  cases packet
  · rfl
  · rfl
  · exact (closed rfl).elim

theorem settleLateFirstLaw_support {packet : SettleLatePacket} {first : SettleLateFirst}
    (supported : first ∈ (settleLateFirstLaw G packet).support) : first.packet = packet := by
  cases packet with
  | silent =>
      rw [settleLateFirstLaw, PMF.mem_support_pure_iff] at supported
      subst supported
      rfl
  | signal word =>
      rw [settleLateFirstLaw, PMF.mem_support_pure_iff] at supported
      subst supported
      rfl
  | opening =>
      rw [settleLateFirstLaw, PMF.support_map] at supported
      obtain ⟨seen, _, rfl⟩ := supported
      rfl

private theorem joint_eq_of_legal {late : Bool} {source : SettleLateState}
    {joint : LateLeakRole → Option SettleLateMove}
    (legal : (settleLateExecution G late).Legal source joint) :
    joint = fun who => if source.actor = some who then joint who else none := by
  funext who
  by_cases acting : source.actor = some who
  · simp [acting]
  · simp only [acting, ite_false]
    exact LegalOption.eq_none_of_inactive (E := settleLateExecution G late) (joint who)
      ((settleLateExecution G late).legalOption_of_legal legal who) acting

theorem settleLate_mover_choice_of_legal {late : Bool} {source : SettleLateState}
    {joint : LateLeakRole → Option SettleLateMove}
    (legal : (settleLateExecution G late).Legal source joint) {who : LateLeakRole}
    (acting : source.actor = some who) :
    ∃ move, joint who = some move ∧
      some move ∈ settleLateMenu late (settleLateView who source) := by
  obtain ⟨move, chosen⟩ := LegalOption.exists_eq_some_of_active (E := settleLateExecution G late)
    (joint who) ((settleLateExecution G late).legalOption_of_legal legal who) acting
  have option := (settleLateExecution G late).legalOption_of_legal legal who
  rw [chosen] at option
  exact ⟨move, chosen, option.2⟩

/-- A realized transition comes from the parent state by the last joint. -/
theorem settleLate_step_parent {late : Bool} {source target : SettleLateState}
    {joint : LateLeakRole → Option SettleLateMove}
    (legal : (settleLateExecution G late).Legal source joint)
    (realized : target ∈ ((settleLateExecution G late).step source ⟨joint, legal⟩).support) :
    source = settleLateParent target ∧ joint = settleLateLastJoint target := by
  have shape := joint_eq_of_legal legal
  change target ∈ (settleLateAdvance G source (joint source.mover)).support at realized
  cases source with
  | initial =>
      rw [settleLateAdvance, PMF.support_map] at realized
      obtain ⟨secret, _, rfl⟩ := realized
      refine ⟨rfl, ?_⟩
      rw [shape]
      funext who
      simp [SettleLateState.actor, settleLateLastJoint, settleLateParent]
  | protectedTurn secret =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .sender) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨packet, hmove, -⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLatePacketOf, PMF.mem_support_pure_iff] at realized
      subst realized
      rw [shape]
      by_cases opened : packet = .opening
      · subst opened
        exact ⟨rfl, by
          funext who
          cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
            settleLateLastMove, chosen]⟩
      · simp only [opened, ite_false]
        exact ⟨rfl, by
          funext who
          cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
            settleLateLastMove, chosen, settleLateTalkPacket_of_ne_opening opened]⟩
  | afterProtected secret =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .sender) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨word, hmove, -⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLatePacketOf, settleLateTalkPacket_word,
        PMF.mem_support_pure_iff] at realized
      subst realized
      rw [shape]
      exact ⟨rfl, by
        funext who
        cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
          settleLateLastMove, chosen]⟩
  | protectedAnswer secret talk =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .listener) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨answer, hmove, -⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLateReplyOf, PMF.mem_support_pure_iff] at realized
      subst realized
      rw [shape]
      exact ⟨rfl, by
        funext who
        cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
          settleLateLastMove, chosen]⟩
  | firstLate secret early =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .sender) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨packet, hmove⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLatePacketOf, PMF.support_map] at realized
      obtain ⟨first, supported, rfl⟩ := realized
      have packet_eq := settleLateFirstLaw_support supported
      rw [shape]
      exact ⟨rfl, by
        funext who
        cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
          settleLateLastMove, chosen, packet_eq]⟩
  | watching secret early first =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .listener) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨sent, hmove⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLatePingOf, PMF.mem_support_pure_iff] at realized
      subst realized
      rw [shape]
      exact ⟨rfl, by
        funext who
        cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
          settleLateLastMove, chosen]⟩
  | secondLate secret early first ping =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .sender) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨packet, hmove⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLatePacketOf, PMF.support_map] at realized
      obtain ⟨fate, _, rfl⟩ := realized
      rw [shape]
      exact ⟨rfl, by
        funext who
        cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
          settleLateLastMove, chosen]⟩
  | answering record =>
      obtain ⟨move, chosen, menu⟩ := settleLate_mover_choice_of_legal legal (who := .listener) rfl
      simp only [settleLateView, settleLateMenu, Set.mem_ofPred_eq] at menu
      obtain ⟨answer, hmove, -⟩ := menu
      obtain rfl := Option.some.inj hmove
      simp only [SettleLateState.mover, SettleLateState.actor, Option.getD_some, chosen,
        settleLateAdvance, settleLateReplyOf, PMF.mem_support_pure_iff] at realized
      subst realized
      rw [shape]
      exact ⟨rfl, by
        funext who
        cases who <;> simp [SettleLateState.actor, settleLateLastJoint, settleLateParent,
          settleLateLastMove, chosen]⟩
  | protectedDone => exact (legal.1 trivial).elim
  | finished => exact (legal.1 trivial).elim

theorem settleLate_initial_not_reached {late : Bool} (source : SettleLateState)
    (joint : LateLeakRole → Option SettleLateMove)
    (legal : (settleLateExecution G late).Legal source joint) :
    SettleLateState.initial ∉
      ((settleLateExecution G late).step source ⟨joint, legal⟩).support := by
  intro reached
  have parent := (settleLate_step_parent legal reached).1
  cases source with
  | initial =>
      change SettleLateState.initial ∈
        (settleLateAdvance G .initial (joint SettleLateState.initial.mover)).support at reached
      rw [settleLateAdvance, PMF.support_map] at reached
      obtain ⟨_, _, impossible⟩ := reached
      cases impossible
  | protectedDone => exact legal.1 trivial
  | finished => exact legal.1 trivial
  | _ => cases parent

/-- Every reachable state has exactly one history. -/
theorem settleLate_treeShaped (G : SettleLateParameters) (late : Bool) :
    (settleLateExecution G late).IsTreeShaped :=
  ExecutionProtocol.isTreeShaped_of_predecessor_unique
    (fun source joint legal => settleLate_initial_not_reached source joint legal)
    (fun firstLegal secondLegal firstRealized secondRealized => by
      obtain ⟨firstSource, firstJoint⟩ := settleLate_step_parent firstLegal firstRealized
      obtain ⟨secondSource, secondJoint⟩ := settleLate_step_parent secondLegal secondRealized
      exact ⟨firstSource.trans secondSource.symm, firstJoint.trans secondJoint.symm⟩)

/-- Histories are determined by the state they reach. -/
theorem settleLate_history_eq_of_state_eq {late : Bool}
    {first second : (settleLateExecution G late).History} (same : first.state = second.state) :
    first = second := by
  rcases first with ⟨state, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  change state = secondState at same
  subst same
  have := (settleLate_treeShaped G late state).allEq firstTrace secondTrace
  subst this
  rfl

theorem settleLate_state_injective (G : SettleLateParameters) (late : Bool) :
    Function.Injective (fun history : (settleLateExecution G late).History => history.state) :=
  fun _ _ same => settleLate_history_eq_of_state_eq same

instance (late : Bool) : Finite (settleLateExecution G late).History :=
  Finite.of_injective _ (settleLate_state_injective G late)

/-- The number of transitions from the initial state. -/
def settleLateDepth : SettleLateState → ℕ
  | .initial => 0
  | .protectedTurn _ => 1
  | .afterProtected _ => 2
  | .protectedAnswer _ _ => 3
  | .protectedDone _ _ _ => 4
  | .firstLate _ _ => 2
  | .watching _ _ _ => 3
  | .secondLate _ _ _ _ => 4
  | .answering _ => 5
  | .finished _ _ => 6

theorem settleLate_trace_length (G : SettleLateParameters) (late : Bool) :
    ∀ {state : SettleLateState} (trace : (settleLateExecution G late).Trace state),
      trace.length = settleLateDepth state
  | _, .start => rfl
  | _, .extend (target := target) prior joint legal realized => by
      have earlier := settleLate_trace_length G late prior
      obtain ⟨rfl, -⟩ := settleLate_step_parent legal realized
      rw [ExecutionProtocol.Trace.length, earlier]
      have reached := settleLate_initial_not_reached _ joint legal
      cases target with
      | initial => exact (reached realized).elim
      | _ => rfl

theorem settleLate_bounded (G : SettleLateParameters) (late : Bool) :
    (settleLateExecution G late).BoundedHorizon 6 := by
  intro state trace enough
  rw [settleLate_trace_length G late trace] at enough
  cases state with
  | finished => trivial
  | _ => simp [settleLateDepth] at enough

/-- Every play stops within six transitions. -/
theorem settleLate_terminates (G : SettleLateParameters) (late : Bool) :
    (settleLateExecution G late).WellFoundedHistories :=
  (settleLate_bounded G late).wellFoundedHistories

/-- The depth of the decision states with a given view. -/
def settleLateViewDepth : SettleLateView → ℕ
  | .protectedTurn _ => 1
  | .afterProtected _ => 2
  | .firstTurn _ _ => 2
  | .secondTurn _ _ _ _ => 4
  | .watching _ _ => 3
  | .protectedAsked _ _ => 3
  | .asked _ => 5
  | .idle => 0

private theorem depth_eq_viewDepth (late : Bool) (who : LateLeakRole) (state : SettleLateState)
    (move : SettleLateMove)
    (menu : some move ∈ settleLateMenu late (settleLateView who state)) :
    settleLateDepth state = settleLateViewDepth (settleLateView who state) := by
  cases who <;> cases state <;> first
    | rfl
    | simp [settleLateView, settleLateMenu] at menu

/-- Histories in one decision information set have a common depth, so none
continues to another. -/
theorem settleLate_antichain (G : SettleLateParameters) (late : Bool) :
    (settleLateModel G late).DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel path
  obtain ⟨_, _, move, menu⟩ := site.2
  have depthOf (history : (settleLateModel G late).InformationHistory who site.1) :
      history.1.trace.length = settleLateViewDepth site.1 := by
    have view : settleLateView who history.1.state = site.1 := by
      rw [← settleLate_infoOf G late who history.1.trace]
      exact history.2
    rw [settleLate_trace_length, depth_eq_viewDepth late who _ move (by rw [view]; exact menu),
      view]
  have increases := path.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increases
  rw [depthOf first, depthOf second] at increases
  omega

end Vegas

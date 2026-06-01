import Vegas.Examples.ProtocolMessageBridge

/-!
# Message-aware protocol strategies

Property boundary: this file preserves the explicit message-aware protocol
game under an encoded backend; it does not erase message observations or prove
front-running deviations unprofitable.

This module keeps the next strategic step at the explicit protocol boundary.
Strategies may choose an outgoing protocol message and then choose the real
Bool action as a function of the delivered message profile. This is not an
erased-message theorem: the preservation result is from the encoded backend to
the explicit Bool message protocol, where send/deliver events and delivered
message observations are still present.

The fixture is intentionally one-player (`PUnit`). It tests the boundary and
proof shape for message-conditioned continuations without claiming a general
multi-player history/view semantics.
-/

namespace Vegas

open GameTheory

namespace Examples
namespace Refinement

abbrev BoolMessageAwareStrategy : PUnit.{1} → Type :=
  fun _ : PUnit.{1} =>
    Bool × ((∀ _player : PUnit.{1}, Bool) → Bool)

def sentBoolMessageProfile
    (profile : ∀ player : PUnit.{1}, BoolMessageAwareStrategy player) :
    ∀ _player : PUnit.{1}, Bool :=
  fun player => (profile player).1

def deliveredBoolMessageProfile
    (delivered : List (Sigma (fun _ : PUnit.{1} => Bool))) :
    ∀ _player : PUnit.{1}, Bool :=
  fun _ =>
    match delivered with
    | [] => false
    | message :: _ => message.2

@[simp] theorem deliveredBoolMessageProfile_singleton (message : Bool) :
    deliveredBoolMessageProfile [⟨PUnit.unit, message⟩] =
      fun _ : PUnit.{1} => message := by
  funext player
  cases player
  rfl

@[simp] theorem sentBoolMessageProfile_eq_unit
    (profile : ∀ player : PUnit.{1}, BoolMessageAwareStrategy player) :
    sentBoolMessageProfile profile =
      fun _ : PUnit.{1} => (profile PUnit.unit).1 := by
  funext player
  cases player
  rfl

def boolMessageAwareAction
    (profile : ∀ player : PUnit.{1}, BoolMessageAwareStrategy player)
    (player : PUnit.{1}) : Bool :=
  (profile player).2 (sentBoolMessageProfile profile)

def boolMessageAwareDeliveredAction
    (profile : ∀ player : PUnit.{1}, BoolMessageAwareStrategy player)
    (delivered : List (Sigma (fun _ : PUnit.{1} => Bool)))
    (player : PUnit.{1}) : Bool :=
  (profile player).2 (deliveredBoolMessageProfile delivered)

def boolMessageAwareFollowDelivered :
    BoolMessageAwareStrategy PUnit.unit :=
  (true, fun messages => messages PUnit.unit)

example :
    boolMessageAwareDeliveredAction
        (fun _ : PUnit.{1} => boolMessageAwareFollowDelivered)
        [⟨PUnit.unit, false⟩] PUnit.unit = false := by
  rfl

example :
    boolMessageAwareDeliveredAction
        (fun _ : PUnit.{1} => boolMessageAwareFollowDelivered)
        [⟨PUnit.unit, true⟩] PUnit.unit = true := by
  rfl

noncomputable def boolMessageAwareProtocolLawFamily :
    boolMessageInFlightMachine.EventBatchLawFamily
      BoolMessageAwareStrategy where
  law := fun profile trace =>
    match trace.2.source with
    | some _ => PMF.pure []
    | none =>
        match trace.2.pending with
        | old :: rest => PMF.pure [.internal .deliver]
        | [] =>
            match trace.2.delivered with
            | [] =>
                PMF.pure
                  [.play PUnit.unit (.send (profile PUnit.unit).1)]
            | _ :: _ =>
                PMF.pure
                  [.play PUnit.unit
                    (.spec
                      (boolMessageAwareDeliveredAction profile
                        trace.2.delivered PUnit.unit))]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨sourceState, pending, delivered⟩
    cases sourceState with
    | some value =>
        exact False.elim
          (hnonterminal (by
            cases value <;>
              simp [boolMessageInFlightMachine, Machine.messageInFlight,
                boolSpecMachine]))
    | none =>
        cases pending with
        | cons old rest =>
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            let src : boolMessageInFlightMachine.State :=
              { source := none,
                pending := old :: rest,
                delivered := delivered }
            exact Machine.AvailableBatchFrom.singleton
              (by
                change Machine.MessageInFlightInternal.deliver ∈
                boolMessageInFlightMachine.availableInternal src
                change src.pending ≠ [] ∧
                  ¬ boolSpecMachine.terminal src.source
                constructor
                · change old :: rest ≠ []
                  intro hnil
                  cases hnil
                · change ¬ boolSpecMachine.terminal none
                  simp [boolSpecMachine])
        | nil =>
            cases delivered with
            | nil =>
                rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
                subst batch
                let src : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := [],
                    delivered := [] }
                exact Machine.AvailableBatchFrom.singleton
                  (by
                    change Machine.MessageInFlightAction.send
                      (profile PUnit.unit).1 ∈
                      boolMessageInFlightMachine.available src PUnit.unit
                    change ¬ boolSpecMachine.terminal none
                    simp [boolSpecMachine])
            | cons deliveredHead deliveredTail =>
                rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
                subst batch
                let deliveredMessages :=
                  deliveredHead :: deliveredTail
                let action :=
                  boolMessageAwareDeliveredAction profile deliveredMessages
                    PUnit.unit
                let src : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := [],
                    delivered := deliveredMessages }
                exact Machine.AvailableBatchFrom.singleton
                  (by
                    change Machine.MessageInFlightAction.spec action ∈
                    boolMessageInFlightMachine.available src PUnit.unit
                    change action ∈
                      boolSpecMachine.available src.source PUnit.unit ∧
                    (src.pending = [] ∨
                      ∀ target,
                        target ∈
                          (boolSpecMachine.stepPlay PUnit.unit action
                            src.source).support →
                          ¬ boolSpecMachine.terminal target)
                    constructor
                    · change action ∈ Set.univ
                      exact Set.mem_univ action
                    · exact Or.inl rfl)

noncomputable def encodedMessageAwareProtocolLawFamily :
    encodedMessageInFlightMachine.EventBatchLawFamily
      BoolMessageAwareStrategy where
  law := fun profile trace =>
    match trace.2.source.payload with
    | some _ => PMF.pure []
    | none =>
        match trace.2.pending with
        | old :: rest => PMF.pure [.internal .deliver]
        | [] =>
            match trace.2.delivered with
            | [] =>
                PMF.pure
                  [.play PUnit.unit (.send (profile PUnit.unit).1)]
            | _ :: _ =>
                PMF.pure
                  [.internal (.spec PUnit.unit),
                    .play PUnit.unit
                      (.spec
                        (boolMessageAwareDeliveredAction profile
                          trace.2.delivered PUnit.unit))]
  legal := by
    intro profile trace hnonterminal batch hbatch
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    cases payload with
    | some value =>
        exact False.elim
          (hnonterminal (by
            simp [encodedMessageInFlightMachine, Machine.messageInFlight,
              encodedImplMachine]))
    | none =>
        cases pending with
        | cons old rest =>
            rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
            subst batch
            let src : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := old :: rest,
                delivered := delivered }
            exact Machine.AvailableBatchFrom.singleton
              (by
                change Machine.MessageInFlightInternal.deliver ∈
                encodedMessageInFlightMachine.availableInternal src
                change src.pending ≠ [] ∧
                  ¬ encodedImplMachine.terminal src.source
                constructor
                · change old :: rest ≠ []
                  intro hnil
                  cases hnil
                · change ¬ encodedImplMachine.terminal
                    { payload := none, audit := audit }
                  simp [encodedImplMachine])
        | nil =>
            cases delivered with
            | nil =>
                rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
                subst batch
                let src : encodedMessageInFlightMachine.State :=
                  { source := { payload := none, audit := audit },
                    pending := [],
                    delivered := [] }
                exact Machine.AvailableBatchFrom.singleton
                  (by
                    change Machine.MessageInFlightAction.send
                      (profile PUnit.unit).1 ∈
                      encodedMessageInFlightMachine.available src PUnit.unit
                    change ¬ encodedImplMachine.terminal
                      { payload := none, audit := audit }
                    simp [encodedImplMachine])
            | cons deliveredHead deliveredTail =>
                rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
                subst batch
                let deliveredMessages :=
                  deliveredHead :: deliveredTail
                let action :=
                  boolMessageAwareDeliveredAction profile deliveredMessages
                    PUnit.unit
                let src : encodedMessageInFlightMachine.State :=
                  { source := { payload := none, audit := audit },
                    pending := [],
                    delivered := deliveredMessages }
                let mid : encodedMessageInFlightMachine.State :=
                  { source := { payload := none, audit := audit + 1 },
                    pending := [],
                    delivered := deliveredMessages }
                change
                  encodedMessageInFlightMachine.AvailableBatchFrom src
                    [.internal (.spec PUnit.unit),
                      .play PUnit.unit (.spec action)]
                refine Machine.AvailableBatchFrom.cons ?_ ?_
                · change Machine.MessageInFlightInternal.spec PUnit.unit ∈
                    encodedMessageInFlightMachine.availableInternal src
                  change PUnit.unit ∈
                      encodedImplMachine.availableInternal src.source ∧
                    (src.pending = [] ∨
                      ∀ target,
                        target ∈
                          (encodedImplMachine.stepInternal PUnit.unit
                            src.source).support →
                          ¬ encodedImplMachine.terminal target)
                  constructor
                  · change PUnit.unit ∈ Set.univ
                    trivial
                  · exact Or.inl rfl
                · intro mid' hmid'
                  change mid' ∈
                    (PMF.map
                      (fun dst =>
                        ({ source := dst,
                           pending := [],
                           delivered := deliveredMessages } :
                          encodedMessageInFlightMachine.State))
                      (PMF.pure
                        ({ payload := none, audit := audit + 1 } :
                          EncodedState))).support at hmid'
                  rw [PMF.pure_map, PMF.support_pure] at hmid'
                  subst mid'
                  exact Machine.AvailableBatchFrom.singleton
                    (by
                      change Machine.MessageInFlightAction.spec action ∈
                      encodedMessageInFlightMachine.available mid PUnit.unit
                      change action ∈
                        encodedImplMachine.available mid.source PUnit.unit ∧
                      (mid.pending = [] ∨
                        ∀ target,
                          target ∈
                            (encodedImplMachine.stepPlay PUnit.unit action
                              mid.source).support →
                            ¬ encodedImplMachine.terminal target)
                      constructor
                      · change action ∈ Set.univ
                        exact Set.mem_univ action
                      · exact Or.inl rfl)

noncomputable def encodedMessageAwareProtocolLawLift :
    encodedMessageProtocolRefinement.EventBatchLawFamilyLift
      BoolMessageAwareStrategy
      boolMessageAwareProtocolLawFamily where
  impl := encodedMessageAwareProtocolLawFamily
  compatible := by
    intro profile trace
    rcases trace with ⟨batches, state⟩
    rcases state with ⟨encodedState, pending, delivered⟩
    rcases encodedState with ⟨payload, audit⟩
    cases payload with
    | some value =>
        change
          PMF.map encodedMessageProtocolProjectEventBatch (PMF.pure []) =
            PMF.pure []
        rw [PMF.pure_map]
        rfl
    | none =>
        cases pending with
        | cons old rest =>
            change
              PMF.map encodedMessageProtocolProjectEventBatch
                  (PMF.pure [.internal .deliver]) =
                PMF.pure [.internal .deliver]
            rw [PMF.pure_map]
            rfl
        | nil =>
            cases delivered with
            | nil =>
                change
                  PMF.map encodedMessageProtocolProjectEventBatch
                      (PMF.pure
                        [.play PUnit.unit
                          (.send (profile PUnit.unit).1)]) =
                    PMF.pure
                      [.play PUnit.unit
                        (.send (profile PUnit.unit).1)]
                rw [PMF.pure_map]
                rfl
            | cons deliveredHead deliveredTail =>
                change
                  PMF.map encodedMessageProtocolProjectEventBatch
                      (PMF.pure
                        [.internal (.spec PUnit.unit),
                          .play PUnit.unit
                            (.spec
                              (boolMessageAwareDeliveredAction profile
                                (deliveredHead :: deliveredTail)
                                PUnit.unit))]) =
                    PMF.pure
                      [.play PUnit.unit
                        (.spec
                          (boolMessageAwareDeliveredAction profile
                            (deliveredHead :: deliveredTail)
                            PUnit.unit))]
                rw [PMF.pure_map]
                rfl

theorem boolMessageAwareTraceGame_eu_three
    (profile : ∀ player : PUnit.{1}, BoolMessageAwareStrategy player) :
    (Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine BoolMessageAwareStrategy
        boolMessageAwareProtocolLawFamily (fun _ => 0) 3).eu
      profile PUnit.unit =
      if boolMessageAwareAction profile PUnit.unit then 1 else 0 := by
  unfold KernelGame.eu
  simp [Machine.eventBatchTraceKernelGame, Machine.eventBatchTraceDist,
    Machine.eventBatchTraceDistFrom, boolMessageAwareProtocolLawFamily,
    boolMessageInFlightMachine, Machine.messageInFlight,
    boolSpecMachine, Machine.runEventBatchesFrom, Machine.runEventsFrom,
    Machine.step, Machine.eventBatchTraceUtility,
    Machine.RoundView.optionOutcomeUtility, boolMessageAwareAction,
    boolMessageAwareDeliveredAction]

def boolMessageAwareTrueProfile (message : Bool) :
    ∀ player : PUnit.{1}, BoolMessageAwareStrategy player :=
  fun _ =>
    (message, fun _ : (∀ _player : PUnit.{1}, Bool) => true)

theorem boolMessageAware_true_nash (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        boolMessageInFlightMachine BoolMessageAwareStrategy
        boolMessageAwareProtocolLawFamily (fun _ => 0) 3).IsNash
      (boolMessageAwareTrueProfile message) := by
  intro player alternative
  cases player
  rw [boolMessageAwareTraceGame_eu_three,
    boolMessageAwareTraceGame_eu_three]
  simp [boolMessageAwareTrueProfile, boolMessageAwareAction,
    Function.update]
  cases h :
      alternative.2 (fun _ : PUnit.{1} => alternative.1) <;>
    simp

theorem encodedMessageAware_true_nash (message : Bool) :
    (Machine.eventBatchTraceKernelGame
        encodedMessageInFlightMachine BoolMessageAwareStrategy
        encodedMessageAwareProtocolLawLift.impl (fun _ => 0) 3).IsNash
      (boolMessageAwareTrueProfile message) := by
  exact
    encodedMessageProtocolRefinement
      |>.eventBatchTraceKernelGame_nash_pullback_of_bounded
        encodedMessageAwareProtocolLawLift
        (fun _ => 0) 3
        (CImpl := fun _ => 1) (CSpec := fun _ => 1)
        encodedMessageInFlightTraceUtility_bound
        boolMessageInFlightTraceUtility_bound
        (boolMessageAware_true_nash message)

end Refinement
end Examples
end Vegas

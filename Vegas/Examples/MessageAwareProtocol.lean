import Vegas.Examples.ProtocolMessageBridge

/-!
# Message-aware protocol strategies

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
            let dst : boolMessageInFlightMachine.State :=
              { source := none,
                pending := rest,
                delivered := delivered ++ [old] }
            refine ⟨dst, ?_⟩
            change
              boolMessageInFlightMachine.AvailableRunFrom src
                [.internal .deliver] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change Machine.MessageInFlightInternal.deliver ∈
                boolMessageInFlightMachine.availableInternal src
              change src.pending ≠ [] ∧ ¬ boolSpecMachine.terminal src.source
              constructor
              · change old :: rest ≠ []
                intro hnil
                cases hnil
              · change ¬ boolSpecMachine.terminal none
                simp [boolSpecMachine]
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
        | nil =>
            cases delivered with
            | nil =>
                rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
                subst batch
                let sent : Sigma (fun _ : PUnit.{1} => Bool) :=
                  ⟨PUnit.unit, (profile PUnit.unit).1⟩
                let src : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := [],
                    delivered := [] }
                let dst : boolMessageInFlightMachine.State :=
                  { source := none,
                    pending := [sent],
                    delivered := [] }
                refine ⟨dst, ?_⟩
                change
                  boolMessageInFlightMachine.AvailableRunFrom src
                    [.play PUnit.unit (.send (profile PUnit.unit).1)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.send
                    (profile PUnit.unit).1 ∈
                    boolMessageInFlightMachine.available src PUnit.unit
                  change ¬ boolSpecMachine.terminal none
                  simp [boolSpecMachine]
                · change dst ∈ (PMF.pure dst).support
                  rw [PMF.support_pure]
                  exact Set.mem_singleton _
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
                let dst : boolMessageInFlightMachine.State :=
                  { source := some action,
                    pending := [],
                    delivered := deliveredMessages }
                let restore
                    (sourceValue : Option Bool) :
                    boolMessageInFlightMachine.State :=
                  { source := sourceValue,
                    pending := [],
                    delivered := deliveredMessages }
                refine ⟨dst, ?_⟩
                change
                  boolMessageInFlightMachine.AvailableRunFrom src
                    [.play PUnit.unit (.spec action)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.spec action ∈
                    boolMessageInFlightMachine.available src PUnit.unit
                  change action ∈
                    boolSpecMachine.available src.source PUnit.unit
                  change action ∈ Set.univ
                  exact Set.mem_univ action
                · change dst ∈
                    (PMF.map restore (PMF.pure (some action))).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _

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
            let dst : encodedMessageInFlightMachine.State :=
              { source := { payload := none, audit := audit },
                pending := rest,
                delivered := delivered ++ [old] }
            refine ⟨dst, ?_⟩
            change
              encodedMessageInFlightMachine.AvailableRunFrom src
                [.internal .deliver] dst
            refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
              (Machine.AvailableRunFrom.nil _)
            · change Machine.MessageInFlightInternal.deliver ∈
                encodedMessageInFlightMachine.availableInternal src
              change src.pending ≠ [] ∧
                ¬ encodedImplMachine.terminal src.source
              constructor
              · change old :: rest ≠ []
                intro hnil
                cases hnil
              · change ¬ encodedImplMachine.terminal
                  { payload := none, audit := audit }
                simp [encodedImplMachine]
            · change dst ∈ (PMF.pure dst).support
              rw [PMF.support_pure]
              exact Set.mem_singleton _
        | nil =>
            cases delivered with
            | nil =>
                rw [PMF.support_pure, Set.mem_singleton_iff] at hbatch
                subst batch
                let sent : Sigma (fun _ : PUnit.{1} => Bool) :=
                  ⟨PUnit.unit, (profile PUnit.unit).1⟩
                let src : encodedMessageInFlightMachine.State :=
                  { source := { payload := none, audit := audit },
                    pending := [],
                    delivered := [] }
                let dst : encodedMessageInFlightMachine.State :=
                  { source := { payload := none, audit := audit },
                    pending := [sent],
                    delivered := [] }
                refine ⟨dst, ?_⟩
                change
                  encodedMessageInFlightMachine.AvailableRunFrom src
                    [.play PUnit.unit (.send (profile PUnit.unit).1)] dst
                refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                  (Machine.AvailableRunFrom.nil _)
                · change Machine.MessageInFlightAction.send
                    (profile PUnit.unit).1 ∈
                    encodedMessageInFlightMachine.available src PUnit.unit
                  change ¬ encodedImplMachine.terminal
                    { payload := none, audit := audit }
                  simp [encodedImplMachine]
                · change dst ∈ (PMF.pure dst).support
                  rw [PMF.support_pure]
                  exact Set.mem_singleton _
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
                let finalSource : EncodedState :=
                  { payload := some (encodeBool action),
                    audit := audit + 1 }
                let dst : encodedMessageInFlightMachine.State :=
                  { source := finalSource,
                    pending := [],
                    delivered := deliveredMessages }
                let restore
                    (sourceValue : EncodedState) :
                    encodedMessageInFlightMachine.State :=
                  { source := sourceValue,
                    pending := [],
                    delivered := deliveredMessages }
                refine ⟨dst, ?_⟩
                change
                  encodedMessageInFlightMachine.AvailableRunFrom src
                    [.internal (.spec PUnit.unit),
                      .play PUnit.unit (.spec action)] dst
                refine Machine.AvailableRunFrom.cons (mid := mid) ?_ ?_ ?_
                · change Machine.MessageInFlightInternal.spec PUnit.unit ∈
                    encodedMessageInFlightMachine.availableInternal src
                  change PUnit.unit ∈
                    encodedImplMachine.availableInternal src.source
                  change PUnit.unit ∈ Set.univ
                  trivial
                · change mid ∈
                    (PMF.map restore
                      (PMF.pure
                        ({ payload := none, audit := audit + 1 } :
                          EncodedState))).support
                  rw [PMF.pure_map, PMF.support_pure]
                  exact Set.mem_singleton _
                · refine Machine.AvailableRunFrom.cons (mid := dst) ?_ ?_
                    (Machine.AvailableRunFrom.nil _)
                  · change Machine.MessageInFlightAction.spec action ∈
                      encodedMessageInFlightMachine.available mid PUnit.unit
                    change action ∈
                      encodedImplMachine.available mid.source PUnit.unit
                    change action ∈ Set.univ
                    exact Set.mem_univ action
                  · change dst ∈
                      (PMF.map restore
                        (PMF.pure finalSource)).support
                    rw [PMF.pure_map, PMF.support_pure]
                    exact Set.mem_singleton _

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

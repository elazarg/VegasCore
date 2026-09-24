/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Information

/-! # Remembering observations and own actions at public rounds

This construction remembers the information seen at each transition and the
player's own action. It adds no strategic memory-writing operation. Since the
record also counts transitions, it is appropriate for a model with observable
round boundaries; it must not silently be used to reveal hidden timing.
-/

namespace GameTheory.Protocol

inductive ObservationRecall (View Action : Type*) where
  | initial (view : View)
  | next (prior : ObservationRecall View Action) (action : Option Action) (view : View)

namespace ObservationRecall

variable {View Action : Type*}

def current : ObservationRecall View Action → View
  | .initial view => view
  | .next _ _ view => view

def ownPlay : ObservationRecall View Action → List (ObservationRecall View Action × Action)
  | .initial _ => []
  | .next prior none _ => prior.ownPlay
  | .next prior (some action) _ => (prior, action) :: prior.ownPlay

end ObservationRecall

namespace InfoSignals

variable {Player : Type*} {E : ExecutionProtocol Player} (signals : InfoSignals E)

def withObservationRecall : InfoSignals E where
  PublicSignal := signals.PublicSignal
  PrivateSignal := signals.PrivateSignal
  initialPublic := signals.initialPublic
  initialPrivate := signals.initialPrivate
  publicSignal := signals.publicSignal
  privateSignal := signals.privateSignal
  InfoState who := ObservationRecall (signals.InfoState who) (E.Action who)
  initInfo who view publicView := .initial (signals.initInfo who view publicView)
  pushInfo who prior action view publicView := .next prior action
    (signals.pushInfo who prior.current action view publicView)

theorem withObservationRecall_current (who : Player) : ∀ {state} (trace : E.Trace state),
    (signals.withObservationRecall.infoOf who trace).current = signals.infoOf who trace
  | _, .start => rfl
  | _, .extend prior joint legal realized => by
      change signals.pushInfo who
        (signals.withObservationRecall.infoOf who prior).current _ _ _ = _
      rw [withObservationRecall_current who prior]
      rfl

theorem withObservationRecall_ownPlay (who : Player) : ∀ {state} (trace : E.Trace state),
    (signals.withObservationRecall.infoOf who trace).ownPlay =
      signals.withObservationRecall.ownPlay who trace
  | _, .start => rfl
  | _, .extend prior joint legal realized => by
      rw [infoOf_extend]
      change (ObservationRecall.next (signals.withObservationRecall.infoOf who prior)
        (joint who) _).ownPlay = _
      rw [ownPlay]
      cases chosen : joint who <;> simp only [ObservationRecall.ownPlay]
      · exact withObservationRecall_ownPlay who prior
      · exact congrArg (List.cons _) (withObservationRecall_ownPlay who prior)

theorem withObservationRecall_perfectRecall : signals.withObservationRecall.PerfectRecall := by
  intro who first second earlier later same
  rw [← signals.withObservationRecall_ownPlay who earlier,
    ← signals.withObservationRecall_ownPlay who later, same]

end InfoSignals
end GameTheory.Protocol

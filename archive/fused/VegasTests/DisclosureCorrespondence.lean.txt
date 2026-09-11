/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory
import VegasTests.DisclosurePolicy
import VegasTests.DisclosureTrace

/-! # Explicit finite disclosure game

This source-level fixture is independent of a graph-policy adapter. The sender
binds a Boolean before public chance and later decides whether to publish it;
the responder observes the signal and optional publication.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open GameTheory GameTheory.Math.Probability

def Strategy : TestPlayer → Type
  | 0 => SenderStrategy
  | 1 => ResponderStrategy

def finiteLaw (profile : ∀ who, Strategy who) : FinDist RunData :=
  ((profile 0).binding).bind fun secret =>
    fairCoin.denote.bind fun signal =>
      ((profile 0).complete secret signal).bind fun complete =>
        let opening := if complete then some secret else none
        (profile 1 signal opening).map fun response =>
          ⟨secret, signal, opening, response⟩

def finiteForm : GameForm TestPlayer where
  sig := { Strategy := Strategy, Outcome := RunData }
  play := finiteLaw

end VegasTests.OptionalDisclosure

/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Wire scheduling without application-trigger authority

A wire policy sees the complete environment observation and remembers its
environment commands. Its choices are delivery, inclusion, and waiting.
Application triggers such as clock boundaries can consequently be supplied by
a separate driver without giving that policy extra trigger opportunities.
-/

namespace Interaction

universe uPrincipal

inductive WireCommand (Principal : Type uPrincipal) where
  | deliver (observer : Principal) (id : MessageId Principal)
  | include (id : MessageId Principal)
  | wait

namespace WireCommand

variable {Principal : Type uPrincipal}

def toEnvironmentCommand (app : MessageApplication Principal) :
    WireCommand Principal → app.EnvironmentPolicyCommand
  | .deliver observer id => .deliver observer id
  | .include id => .include id
  | .wait => .wait

end WireCommand

namespace MessageApplication

open GameTheory.Math.Probability

variable {Principal : Type uPrincipal}

abbrev WirePolicy (app : MessageApplication Principal) :=
  List (MessageInterface.EnvironmentEntry app.toMessageInterface) →
    app.EnvironmentObservation → FinDist (WireCommand Principal)

noncomputable def wireEnvironment (app : MessageApplication Principal)
    (policy : app.WirePolicy) : app.EnvironmentPolicy :=
  fun history view => (policy history view).map (WireCommand.toEnvironmentCommand app)

end MessageApplication
end Interaction

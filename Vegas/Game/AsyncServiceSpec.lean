/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Game.SourceContinuation
import Vegas.Source.DisclosureBehavioral
import Interaction.ReactiveMenuPolicy
import Vegas.Pending.ReactiveBoundedValues
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveAsyncContract
import Vegas.Pending.ExclusionFiniteNature

/-! # Full-source services under an asynchronous scheduler

`Vegas.AsyncServiceSpec` is the full-source native service with an arbitrary
public scheduler in place of the roster calendar: the program setup, the
dependency mode of its event graph and a configured deadline duration per
event, passive observation rule and message bounds with the compiler's side
conditions on them, a horizon, and a scheduler satisfying the asynchronous
contract with per-event reaction bounds `delay` and inclusion bounds `bound`
that leave room before every configured deadline. It has no rosters and no
activation opportunities: the contract's opportunity clause replaces them.

Concrete scheduler realizations and their all-history contract proofs belong
to their instance modules. The generic specification does not supply a
realization of its opportunity, inclusion or completion fields.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

/-- The full-source native service under an asynchronous scheduler: the
program setup, the dependency mode and configured deadlines of its runtime,
passive observation rule and message bounds, with the compiler's side
conditions on them, and a scheduler satisfying the asynchronous contract up to
a fixed horizon, with bounds that fit every configured deadline. -/
structure AsyncServiceSpec (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] where
  setup : Setup (Player := Player) (L := L)
  /-- The dependency mode of the compiled event graph. -/
  mode : EventGraph.ExecutionMode
  /-- The configured deadline duration of each event, counted by the runtime
  from the clock at which the event became ready. -/
  deadline : (serviceGraph setup mode).EventId → Nat
  leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))
  bounds : MessageBounds (serviceGraph setup mode)
  /-- Every binding value the source can choose has a native message form. -/
  values : bounds.CoversBindingValues
  /-- Every supported initial binding table fits the candidate catalogue. -/
  initialValues : ∀ state ∈ (serviceInitialLaw setup mode).support, bounds.CandidateValues state
  /-- The candidate catalogue has a slot for every event. -/
  capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount
  /-- The number of scheduler rounds. -/
  horizon : Nat
  /-- The public scheduler: activations, inclusions, clock, sampling and expiry. -/
  scheduler : (serviceApplication setup mode deadline leaks).Scheduler
  /-- Per-event reaction bound: slots before the owner's first activation. -/
  delay : (serviceGraph setup mode).EventId → Nat
  /-- Per-event inclusion bound for an owner's sole packet. -/
  bound : (serviceGraph setup mode).EventId → Nat
  contract : AsyncContract (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup mode)
    horizon scheduler delay bound
  /-- Every owned event's reaction and inclusion fit before its configured
  deadline. -/
  timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound
  /-- The prior over initial states is finitely supported. -/
  initialFinite : setup.FiniteInitialLaw
  /-- The leak rule branches finitely. -/
  leaksFinite : leaks.FiniteSupport
  /-- The scheduler branches finitely. -/
  schedulerFinite : ∀ past view, (scheduler past view).support.Finite

attribute [instance] AsyncServiceSpec.initialFinite AsyncServiceSpec.leaksFinite

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- All of the service's nature branches finitely: the prior, the leak rule and
the scheduler. -/
instance finiteNature :
    (serviceApplication service.setup service.mode service.deadline service.leaks).FiniteNature
      (serviceInitialLaw service.setup service.mode) service.scheduler where
  initial_finite := serviceInitialLaw_support_finite service.setup service.mode
  scheduler_finite := service.schedulerFinite

/-- The scheduler completes every event by the horizon. -/
theorem completes : CompletesPlay (serviceRuntime service.setup service.mode service.deadline)
    service.leaks (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler :=
  service.contract.completes


/-- The bounded raw response menu: every native response within the service's
message bounds. -/
abbrev rawMenu [Fintype Player] : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ResponseMenu :=
  service.bounds.rawMenu (serviceRuntime service.setup service.mode service.deadline) service.leaks


variable (admission : CommitmentInterface service.setup.program)

/-- The source information model of the service's program, at its supplied commitment
admission interface. -/
abbrev sourceModel := service.setup.informationModel admission

/-- **The turn-counted clients** of a source profile in a response menu: each
player follows the turn-counted policy of its disclosure-normalized source
policy, completed by silence after its own off-policy responses
(`Vegas.serviceClientPolicy`). -/
def clientProfile (menu : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature) :
    Profile (menu.information (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).behavioralSignature := fun who =>
  menu.restrictPolicy (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler who
    (serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
      turns timing
      (normalizeDisclosureProfile service.setup.program
        (service.setup.decodeBehavioralProfile admission
          source)) who)

private theorem clientPolicy_congr {turns : Nat} (timing : TurnTiming service.setup turns
    service.mode)
    (profile other : BehavioralProfile service.setup.program) (who : Player)
    (same : profile who = other who) :
    serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
      turns timing profile who =
      serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
        turns timing other
        who := by
  unfold serviceClientPolicy serviceTurnPolicy serviceTurnFamily serviceCanonicalOpportunity
    serviceCanonicalPolicy compileEventProfile
  rw [same]

/-- Each player's client depends only on its own source policy. -/
theorem clientProfile_congr (menu : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source other : Profile (service.sourceModel admission).behavioralSignature) (who : Player)
    (same : source who = other who) :
    service.clientProfile admission menu timing source who = service.clientProfile admission menu
      timing other who := by
  have decoded : normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile admission
        source) who =
    normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile admission
        other) who := by
    simp only [normalizeDisclosureProfile, normalizeDisclosureProfileFrom,
      Setup.decodeBehavioralProfile, same]
  exact congrArg (menu.restrictPolicy (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler who) (clientPolicy_congr service timing _ _ who decoded)

/-- The clients of a unilateral source deviation are a unilateral deviation of
the clients. -/
theorem clientProfile_update (menu : (serviceApplication service.setup service.mode
    service.deadline service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature) (who : Player)
    (alternative : (service.sourceModel admission).BehavioralPolicy who) :
    Profile.update (service.clientProfile admission menu timing source) who
        (service.clientProfile admission menu timing (Profile.update source who alternative) who) =
      service.clientProfile admission menu timing (Profile.update source who alternative) := by
  funext other
  by_cases same : other = who
  · subst other
    simp only [Profile.update, Function.update_self]
  · simp only [Profile.update, Function.update_of_ne same]
    exact service.clientProfile_congr admission menu timing _ _ other (by
      simp only [Function.update_of_ne same])


end AsyncServiceSpec



end Vegas

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCommitFailure
import Vegas.Game.OnePacketLateCertificate
import GameTheoryExtensions.Math.Probability.ProductDecorrelation

/-! # Uniform errors over late-commitment sites

The newest entry of an operational record is the operational state of the
history's state (`Vegas.operationalRecord_headD`), and every history of a
decision site with a pending event is a prefix of the site's rank
(`Vegas.ordered_of_site`). Errors vanishing at each of the finitely many sites
give one vanishing error for all of them (`Vegas.exists_uniform_of_sites`,
`Vegas.exists_uniform_decorrelation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The newest entry of an operational record is the operational state of the
history's state. -/
theorem operationalRecord_headD {state : (application setup runtime leaks).ProtocolState}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state) :
    (operationalRecord setup runtime leaks bounds horizon scheduler trace).headD
        (operationalState setup runtime leaks none) = operationalState setup runtime leaks state :=
  match trace with
  | .start => rfl
  | .extend _ _ _ _ => rfl

omit [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Filter in
/-- **Uniform decorrelation.** If at every site satisfying a condition the
beliefs decorrelate the operational records and the decoded points up to a
vanishing error, one vanishing error serves every such site. -/
theorem exists_uniform_decorrelation
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (condition : ∀ who, (onePacketN).InformationSite who → Prop)
    (perSite : ∀ who (site : (onePacketN).InformationSite who), condition who site →
      ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧ ∀ n,
        BeliefDecorrelated ((targetSequence n).belief who site)
          (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
            history.1.trace)
          (fun history => nativeDecodedState setup runtime leaks history.1.state) (error n)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who), condition who site →
        BeliefDecorrelated ((targetSequence n).belief who site)
          (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
            history.1.trace)
          (fun history => nativeDecodedState setup runtime leaks history.1.state) (error n) :=
  exists_uniform_of_sites setup runtime leaks bounds horizon scheduler
    (fun n who site error => BeliefDecorrelated ((targetSequence n).belief who site)
      (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
      (fun history => nativeDecodedState setup runtime leaks history.1.state) error)
    (fun _ _ _ _ _ le decorrelated => decorrelated.mono le) condition perSite

end Vegas

module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketAssessmentExtension
public import Interaction.ReactiveMenuInvariant

@[expose] public section

/-! # Every retained native information site has a canonical raw representative -/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (State graph)) (horizon : Nat)
  (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)

private theorem onePacket_normalRecall_invariant :
    (bounds.onePacketMenu timeouts leaks).ServiceInvariant scheduler (fun execution =>
      ∀ who, ((reactiveNormalization timeouts) leaks).logs who (execution.logs who) =
        execution.logs who) where
  respond execution who action fixed member := by
    have normalAction := ((reactiveNormalization timeouts) leaks).menu_normal
      (bounds.rawMenu timeouts leaks) who (execution.logs who)
      (execution.observe ((reactiveApplication timeouts) leaks) who) action
      (bounds.onePacketMenu_in_effective timeouts leaks who _ _ member)
    intro observer
    by_cases same : observer = who
    · subst observer
      have recalled : ∃ emitted, (execution.respond ((reactiveApplication timeouts) leaks) who
          action).logs who = execution.logs who ++
            [⟨execution.observe ((reactiveApplication timeouts) leaks) who, action, emitted⟩] := by
        rcases action with ⟨transmission⟩
        cases transmission <;> simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          <;> exact ⟨_, rfl⟩
      obtain ⟨emitted, recalled⟩ := recalled
      rw [recalled, ReactiveApplication.SubmissionNormalization.recall_append_action, fixed who,
        normalAction]
    · rw [((reactiveApplication timeouts) leaks).respond_recall_other execution who observer same]
      exact fixed observer
  environment execution next command fixed _selected moved := by
    intro who
    rw [((reactiveApplication timeouts) leaks).environmentStep_recall execution next command moved]
    exact fixed who

/-- One-packet histories already have normalized response recall. -/
theorem onePacket_history_info_normal
    (who : Player)
    (history : ((bounds.onePacketMenu timeouts leaks).protocol initial horizon scheduler).History) :
    ((reactiveNormalization timeouts) leaks).info who
        (((bounds.onePacketMenu timeouts leaks).information initial horizon scheduler).infoOf who
          history.trace) =
      ((bounds.onePacketMenu timeouts leaks).information initial horizon scheduler).infoOf who
        history.trace := by
  have fixed := (onePacket_normalRecall_invariant bounds timeouts leaks scheduler).history initial
    horizon (fun _ _ _ => rfl) history.trace
  have observed :
      ((bounds.onePacketMenu timeouts leaks).information initial horizon scheduler).infoOf who
          history.trace = ((reactiveApplication timeouts) leaks).observe who history.state :=
    (bounds.onePacketMenu timeouts leaks).info initial horizon scheduler who history.trace
  rw [observed]
  cases current : history.state with
  | none => rfl
  | some control =>
      rw [current] at fixed
      change ∀ who, ((reactiveNormalization timeouts) leaks).logs who (control.execution.logs who) =
        control.execution.logs who at fixed
      by_cases acting : control.actor = some who
      · simp only [ReactiveApplication.observe, acting, ↓reduceIte,
          ReactiveApplication.SubmissionNormalization.info, Option.map_some]
        rw [fixed who]
      · simp only [ReactiveApplication.observe, acting, ↓reduceIte,
          ReactiveApplication.SubmissionNormalization.info, Option.map_none]

/-- Every retained native decision has a raw decision whose normalization returns exactly the
same embedded information site. No reachability under an equilibrium profile is required. -/
theorem exists_raw_site_of_onePacket_site
    (who : Player)
    (sourceSite : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).InformationSite who) :
    ∃ rawSite : ((bounds.rawMenu timeouts leaks).information initial horizon
        scheduler).InformationSite who,
      ((reactiveNormalization timeouts) leaks).site (bounds.rawMenu timeouts leaks)
        (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who rawSite =
      (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).site who
        sourceSite := by
  let rawSite := ((bounds.onePacketMenu_in_raw timeouts leaks).actionRestriction initial horizon
    scheduler).site who sourceSite
  refine ⟨rawSite, Subtype.ext ?_⟩
  change ((reactiveNormalization timeouts) leaks).info who sourceSite.1 = sourceSite.1
  obtain ⟨history, _running, _action, _member⟩ := sourceSite.2
  have fixed := onePacket_history_info_normal bounds timeouts leaks initial horizon scheduler who
    history.1
  simpa only [history.2] using fixed

end Vegas.EventGraphRuntime.MessageBounds

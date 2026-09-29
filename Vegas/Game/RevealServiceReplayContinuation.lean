/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplaySource
import Interaction.ReactiveLocalContinuation

/-! # Actual continuation comparison after watcher replay aliases

The comparison uses the unchanged scheduler and ordinary players' complete
native inputs. Watcher response recall may differ arbitrarily. Its admitted
responses reveal no new packet under this native observation interface.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

variable
  (source : Profile (information setup leaks bounds watcher).behavioralSignature)
  (target : Profile ((replayMenu setup leaks bounds watcher).information
    (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)).behavioralSignature)
  (agrees : ((menu_in_replay setup leaks bounds watcher).actionRestriction
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).ExtendsProfile
      source target)

include agrees in
theorem replay_ordinary_policy_eq
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (who : Player) (first second : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, first⟩) (ordinary : who ≠ watcher)
    (same : ReplayAgreement setup leaks watcher first second) :
    (replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) target who
        (second.recall who) (second.observe (application setup leaks) who) =
      (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) source who
        (first.recall who) (first.observe (application setup leaks) who) := by
  have active : (protocol setup leaks bounds watcher).active history.state who := by
    change (application setup leaks).actor history.state = some who
    rw [current]
    rfl
  have running : ¬ (protocol setup leaks bounds watcher).terminal history.state := by
    change ¬ (application setup leaks).terminal history.state
    rw [current]
    simp [ReactiveApplication.terminal]
  obtain ⟨site, observed⟩ := InformationModel.exists_informationSite_of_active
    (M := information setup leaks bounds watcher) who history running active
  have input : site.1 = some (first.recall who, first.observe (application setup leaks) who) := by
    rw [observed]
    change ((menu setup leaks bounds watcher).signals (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).infoOf who history.trace = _
    rw [ReactiveApplication.ResponseMenu.info, current]
    simp only [ReactiveApplication.observe, reduceIte]
  rw [← same.recall who ordinary, ← same.observe who]
  exact (menu_in_replay setup leaks bounds watcher).decoded_at_site (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher) source target agrees who site _ _ input

include reveals observer openable in
/-- One actual control-kernel step transports any continuation comparison.
This includes passive activation and reserved inclusion, not just responses. -/
theorem replay_control_bind_eq {Outcome : Type}
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (actor : Option Player)
    (first second : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, actor, first⟩)
    (same : ReplayAgreement setup leaks watcher first second)
    (ordinaryLaw : ∀ who, actor = some who → who ≠ watcher →
      (replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) target who
          (second.recall who) (second.observe (application setup leaks) who) =
        (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) source who
          (first.recall who) (first.observe (application setup leaks) who))
    (leftValue rightValue : (application setup leaks).ProtocolState → PMF Outcome)
    (continued : ∀ count nextActor left right,
      some ⟨count, nextActor, left⟩ ∈
        ((application setup leaks).controlStep (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher)
          ((menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
            (horizon setup watcher) (scheduler setup leaks watcher) source)
          (some ⟨remaining, actor, first⟩)).support →
      ReplayAgreement setup leaks watcher left right →
      leftValue (some ⟨count, nextActor, left⟩) =
        rightValue (some ⟨count, nextActor, right⟩)) :
    ((application setup leaks).controlStep (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)
        ((menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) source)
        (some ⟨remaining, actor, first⟩)).bind leftValue =
      ((application setup leaks).controlStep (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)
        ((replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) target)
        (some ⟨remaining, actor, second⟩)).bind rightValue := by
  classical
  let app := application setup leaks
  let sourceMenu := menu setup leaks bounds watcher
  let targetMenu := replayMenu setup leaks bounds watcher
  let firstPlayers := sourceMenu.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) source
  let secondPlayers := targetMenu.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) target
  change (app.controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) firstPlayers (some ⟨remaining, actor, first⟩)).bind _ =
    (app.controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) secondPlayers (some ⟨remaining, actor, second⟩)).bind _
  cases actor with
  | some who =>
      have step (players : Player → app.Policy) (execution : app.Execution) :
          app.controlStep (initialLaw setup) (horizon setup watcher)
              (scheduler setup leaks watcher) players (some ⟨remaining, some who, execution⟩) =
            (players who (execution.recall who) (execution.observe app who)).map fun response =>
              some ⟨remaining, none, execution.respond app who response⟩ := by
        simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
          ReactiveApplication.transition, reduceIte, Option.getD_some, ← PMF.bind_pure_comp,
              Function.comp_def]
      rw [step, step, PMF.bind_map, PMF.bind_map]
      by_cases watches : who = watcher
      · subst who
        have quiet := watcher_history_silent setup leaks bounds watcher reveals observer openable
          history ⟨remaining, some watcher, first⟩ current rfl
        have prescribed : firstPlayers watcher (first.recall watcher)
            (first.observe app watcher) = PMF.pure ⟨none⟩ := by
          rw [show firstPlayers watcher = app.reportFirstUnpublished from
            menu_decode_reports setup leaks bounds watcher source]
          exact quiet
        rw [prescribed, PMF.pure_bind]
        symm
        refine (bind_congr_on_support _ (g := fun _ =>
          leftValue (some ⟨remaining, none, first.respond app watcher ⟨none⟩⟩)) ?_).trans
            (PMF.bind_const _ _)
        intro response supported
        have allowed := targetMenu.decode_embedPolicy_covered (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) watcher
          (target watcher) _ _ response supported
        change response ∈ targetMenu.actions watcher (second.recall watcher)
          (second.observe app watcher) at allowed
        rw [replay_menu_watcher] at allowed
        have secondQuiet : app.reportFirstUnpublished (second.recall watcher)
            (second.observe app watcher) = PMF.pure ⟨none⟩ := by
          apply app.reportFirstUnpublished_silent
          intro message seen
          have clean := (active_history_clean setup leaks bounds watcher reveals observer openable
            history ⟨remaining, some watcher, first⟩ current watcher rfl).1
          change message ∈ second.network.leaked watcher at seen
          rw [← same.leaked, clean] at seen
          exact (List.not_mem_nil seen).elim
        have reached : some ⟨remaining, none, first.respond app watcher ⟨none⟩⟩ ∈
            (app.controlStep (initialLaw setup) (horizon setup watcher)
              (scheduler setup leaks watcher) firstPlayers
              (some ⟨remaining, some watcher, first⟩)).support := by
          rw [step, prescribed, PMF.pure_map]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl
        have related : ReplayAgreement setup leaks watcher
            (first.respond app watcher ⟨none⟩) (second.respond app watcher response) := by
          rcases Finset.mem_union.mp allowed with prescribedResponse | replayed
          · rw [Set.Finite.mem_toFinset, secondQuiet, PMF.mem_support_pure_iff _ _]
              at prescribedResponse
            subst response
            exact same.respond_watcher_silent
          · obtain ⟨packet, published, rfl⟩ :=
              (mem_publishedReplays setup leaks _ response).mp replayed
            exact same.respond_watcher_replay packet.id
              (List.mem_map.mpr ⟨packet, published, rfl⟩)
        exact (continued remaining none _ _ reached related).symm
      · have policyEq := ordinaryLaw who rfl watches
        change secondPlayers who _ _ = firstPlayers who _ _ at policyEq
        rw [policyEq]
        apply bind_congr_on_support _
        intro response supported
        apply continued remaining none
        · rw [step, PMF.support_map]
          exact ⟨response, supported, rfl⟩
        · exact same.respond_ordinary who watches response
  | none =>
      cases remaining with
      | zero =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_some, ReactiveApplication.transition, PMF.pure_bind]
          exact continued 0 none first second ((PMF.mem_support_pure_iff _ _).mpr rfl) same
      | succ remaining =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_some, ReactiveApplication.transition, PMF.bind_bind, PMF.bind_map]
          have scheduled := replay_scheduler_eq setup leaks bounds watcher reveals observer openable
            history ⟨remaining + 1, none, first⟩ current second same
          rw [← scheduled]
          apply bind_congr_on_support _
          intro command supported
          apply same.environment_bind_eq command
          · intro id chosen
            subst command
            exact scheduler_inclusion_fresh setup leaks watcher _ _ id supported
          · intro who chosen
            subst command
            exact before_activation_published setup leaks bounds watcher reveals observer openable
              history remaining first current who supported
          · intro left reached right related
            apply continued remaining (command.actor? app) left right _ related
            change _ ∈ ((scheduler setup leaks watcher first.environmentRecall
              (first.observeEnvironment app)).bind _).support
            rw [PMF.support_bind]
            apply Set.mem_iUnion₂.mpr
            refine ⟨command, supported, ?_⟩
            rw [PMF.support_map]
            exact ⟨left, reached, rfl⟩


include reveals observer openable agrees in
/-- Published watcher replays preserve the complete application-state law under
arbitrary paired continuation profiles, including later choices by repeated
owners. Raw private response records are retained on both sides. -/
theorem replay_finish_application_law
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (actor : Option Player)
    (first second : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, actor, first⟩)
    (same : ReplayAgreement setup leaks watcher first second) :
    ((application setup leaks).finish (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)
        ((menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) source)
        (some ⟨remaining, actor, first⟩)).map
        (fun state => state.map (fun control => control.execution.application)) =
      ((application setup leaks).finish (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)
        ((replayMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher) target)
        (some ⟨remaining, actor, second⟩)).map
        (fun state => state.map (fun control => control.execution.application)) := by
  let app := application setup leaks
  let sourceMenu := menu setup leaks bounds watcher
  let targetMenu := replayMenu setup leaks bounds watcher
  let firstPlayers := sourceMenu.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) source
  let secondPlayers := targetMenu.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) target
  let observe : app.ProtocolState → Option app.State :=
    fun state => state.map (fun control => control.execution.application)
  change (app.finish (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    firstPlayers (some ⟨remaining, actor, first⟩)).map observe =
    (app.finish (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
      secondPlayers (some ⟨remaining, actor, second⟩)).map observe
  generalize rankEq : app.rank (horizon setup watcher)
    (some ⟨remaining, actor, first⟩) = rank
  induction rank using Nat.strong_induction_on
      generalizing history remaining actor first second with
  | h rank ih =>
    by_cases stopped : app.terminal (some ⟨remaining, actor, first⟩)
    · have otherStopped : app.terminal (some ⟨remaining, actor, second⟩) := stopped
      rw [app.finish_terminal _ _ _ _ _ stopped,
        app.finish_terminal _ _ _ _ _ otherStopped, PMF.pure_map, PMF.pure_map]
      congr 1
      exact congrArg some same.applicationEq
    · rw [← app.finish_step (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) firstPlayers (some ⟨remaining, actor, first⟩),
        ← app.finish_step (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) secondPlayers (some ⟨remaining, actor, second⟩),
        PMF.map_bind, PMF.map_bind]
      apply replay_control_bind_eq setup leaks bounds watcher reveals observer openable
        source target history remaining actor first second current same
      · intro who active ordinary
        subst actor
        exact replay_ordinary_policy_eq setup leaks bounds watcher source target agrees
          history remaining who first second current ordinary same
      intro count nextActor left right reached related
      have prefixLaw := sourceMenu.run_map_controlSteps (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) source 1 history
      simp only [Function.iterate_one, PMF.pure_bind, current] at prefixLaw
      have reachable : some ⟨count, nextActor, left⟩ ∈
          (((information setup leaks bounds watcher).runBehavioralFrom source 1 history).map
            History.state).support := by
        rw [prefixLaw]
        exact reached
      rw [PMF.support_map] at reachable
      obtain ⟨nextHistory, _, nextState⟩ := reachable
      have decreases := app.controlStep_rank (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) firstPlayers _ _ stopped reached
      rw [rankEq] at decreases
      exact ih _ decreases nextHistory count nextActor left right nextState related rfl

end Vegas

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveNormalRecall

/-! # Normalizing legal reactive histories

Raw responses and their normal forms have different private recall. This map
projects the complete legal trace, using the same scheduler, leaks and emitted
packets. The menu premise says that changing only private aliases cannot change
which responses are available next. The native bounded menus satisfy it.
-/

noncomputable section

namespace Interaction.ReactiveApplication.SubmissionNormalization

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization)

def state : app.ProtocolState → app.ProtocolState :=
  Option.map fun control => { control with execution := normal.execution control.execution }

def info (who : Principal) : app.Info → app.Info :=
  Option.map fun data => (normal.recall who data.1, data.2)

def joint (before : app.ProtocolState) (choices : Principal → Option app.Action) :
    Principal → Option app.Action :=
  match before with
  | none => choices
  | some control => fun who => (choices who).map
      (normal.action who (control.execution.recall who) (control.execution.observe app who))

omit [DecidableEq Principal] in
@[simp] theorem state_actor (before : app.ProtocolState) :
    app.actor (normal.state before) = app.actor before := by
  cases before <;> rfl

omit [DecidableEq Principal] in
@[simp] theorem state_terminal (before : app.ProtocolState) :
    app.terminal (normal.state before) ↔ app.terminal before := by
  cases before <;> rfl

@[simp] theorem state_observe (before : app.ProtocolState) (who : Principal) :
    app.observe who (normal.state before) = normal.info who (app.observe who before) := by
  cases before with
  | none => rfl
  | some control =>
      by_cases active : control.actor = some who
      all_goals simp only [state, info, Option.map_some, observe, active, ↓reduceIte,
        Option.map_none, execution]
      rfl

theorem state_transition (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before : app.ProtocolState)
    (choices : Principal → Option app.Action) (valid : app.inputRecall before) :
    (app.transition initial horizon scheduler before choices).map normal.state =
      app.transition initial horizon scheduler (normal.state before)
        (normal.joint before choices) := by
  cases before with
  | none =>
      simp only [transition, state, Option.map_none, FinDist.map_comp]
      rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          simp only [transition, state, joint, Option.map_some, FinDist.map_pure]
          have response := normal.execution_respond execution who
            ((choices who).getD ⟨none⟩) valid
          cases chosen : choices who with
          | none =>
              simpa only [chosen, Option.getD_none, Option.map_none, action] using
                congrArg (fun next => FinDist.pure (some (Control.mk remaining none next)))
                  response
          | some response =>
              simpa only [chosen, Option.getD_some, Option.map_some] using
                congrArg (fun next => FinDist.pure (some (Control.mk remaining none next)))
                  (normal.execution_respond execution who response valid)
      | none =>
          cases remaining with
          | zero => simp only [transition, state, Option.map_some, FinDist.map_pure]
          | succ remaining =>
              simp only [transition, state, Option.map_some, FinDist.map_bind]
              change _ = (scheduler execution.environmentRecall
                (execution.observeEnvironment app)).bind _
              congr 1
              funext command
              rw [FinDist.map_comp, ← normal.execution_environmentStep]
              rw [FinDist.map_comp]
              rfl

variable (raw : app.ResponseMenu)
  (stable : ∀ who past view,
    raw.actions who (normal.recall who past) view = raw.actions who past view)

include stable in
theorem legal_joint (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before : app.ProtocolState) (choices : Principal → Option app.Action)
    (legal : (raw.protocol initial horizon scheduler).Legal before choices) :
    ((normal.menu raw).protocol initial horizon scheduler).Legal
      (normal.state before) (normal.joint before choices) := by
  refine ⟨(normal.state_terminal before).not.mpr legal.1, ?_⟩
  intro who
  have player := legal.2 who
  cases before with
  | none => exact player
  | some control =>
      cases chosen : choices who with
      | none =>
          simp only [joint, chosen, Option.map_none]
          change app.actor (normal.state (some control)) ≠ some who
          rw [normal.state_actor]
          simpa only [chosen, ResponseMenu.protocol] using player
      | some response =>
          simp only [chosen] at player
          simp only [joint, chosen, Option.map_some]
          have active : app.actor (some control) = some who := by
            exact player.1
          have member : response ∈ raw.actions who (control.execution.recall who)
              (control.execution.observe app who) := by
            exact player.2
          constructor
          · exact (normal.state_actor (some control)).trans active
          · change normal.action who (control.execution.recall who)
                (control.execution.observe app who) response ∈
              ((normal.menu raw).actions who
                (normal.recall who (control.execution.recall who))
                  (control.execution.observe app who))
            rw [normal.menu_mem]
            exact ⟨response, (stable who _ _).symm ▸ member, normal.action_recall ..⟩

def trace (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {before}, (raw.protocol initial horizon scheduler).Trace before →
      ((normal.menu raw).protocol initial horizon scheduler).Trace (normal.state before)
  | _, .start => .start
  | before, .extend prior choices legal realized =>
      .extend (trace initial horizon scheduler prior)
        (normal.joint _ choices)
        (normal.legal_joint raw stable initial horizon scheduler _ choices legal)
        (by
          rename_i source
          have valid := app.history_inputRecall initial horizon scheduler
            (raw.toRawTrace initial horizon scheduler prior)
          have mapped : normal.state before ∈
              ((app.transition initial horizon scheduler source choices).map
                normal.state).support := by
            rw [FinDist.support_map]
            exact ⟨before, realized, rfl⟩
          rw [normal.state_transition initial horizon scheduler _ choices valid] at mapped
          exact mapped)

def history (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (original : (raw.protocol initial horizon scheduler).History) :
    ((normal.menu raw).protocol initial horizon scheduler).History :=
  ⟨normal.state original.state, normal.trace raw stable initial horizon scheduler original.trace⟩

@[simp] theorem trace_length (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) {before}
    (original : (raw.protocol initial horizon scheduler).Trace before) :
    (normal.trace raw stable initial horizon scheduler original).length = original.length := by
  induction original with
  | start => rfl
  | extend prior choices legal realized ih => exact congrArg Nat.succ ih

theorem history_info (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal)
    (original : (raw.protocol initial horizon scheduler).History) :
    ((normal.menu raw).information initial horizon scheduler).infoOf who
        (normal.history raw stable initial horizon scheduler original).trace =
      normal.info who ((raw.information initial horizon scheduler).infoOf who original.trace) := by
  change ((normal.menu raw).signals initial horizon scheduler).infoOf who _ =
    normal.info who ((raw.signals initial horizon scheduler).infoOf who _)
  rw [ResponseMenu.info, ResponseMenu.info]
  exact normal.state_observe original.state who

def informationHistory (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) (observed : app.Info)
    (original : (raw.information initial horizon scheduler).InformationHistory who observed) :
    ((normal.menu raw).information initial horizon scheduler).InformationHistory who
      (normal.info who observed) :=
  ⟨normal.history raw stable initial horizon scheduler original.1,
    (normal.history_info raw stable initial horizon scheduler who original.1).trans
      (congrArg (normal.info who) original.2)⟩

/-- Normalize the chosen response and the player's recalled response names.
The unique inactive choice stays inactive. -/
def choice (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (observed : app.Info)
    (original : (raw.information initial horizon scheduler).Choice who observed) :
    ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who observed) := by
  refine ⟨match observed with
    | none => original.1
    | some data => original.1.map (normal.action who data.1 data.2), ?_⟩
  cases observed with
  | none => exact original.2
  | some data =>
      obtain ⟨response, member, chosen⟩ := original.2
      refine ⟨normal.action who data.1 data.2 response, ?_, ?_⟩
      · apply (normal.menu_mem raw who (normal.recall who data.1) data.2 _).mpr
        exact ⟨response, (stable who data.1 data.2).symm ▸ member,
          normal.action_recall who data.1 data.2 response⟩
      · simp only [chosen, Option.map_some]

def site (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (original : (raw.information initial horizon scheduler).InformationSite who) :
    ((normal.menu raw).information initial horizon scheduler).InformationSite who := by
  refine ⟨normal.info who original.1, ?_⟩
  obtain ⟨witness, running, response, member⟩ := original.2
  refine ⟨normal.informationHistory raw stable initial horizon scheduler who original.1 witness,
    (normal.state_terminal witness.1.state).not.mpr running, ?_⟩
  cases observed : original.1 with
  | none =>
      change some response ∈ (raw.information initial horizon scheduler).menu who original.1
        at member
      rw [observed] at member
      change some response = none at member
      contradiction
  | some data =>
      rw [observed] at member
      obtain ⟨other, supported, same⟩ := member
      have equal := Option.some.inj same
      subst other
      refine ⟨normal.action who data.1 data.2 response, ?_⟩
      refine ⟨normal.action who data.1 data.2 response, ?_, rfl⟩
      exact (normal.menu_mem raw who (normal.recall who data.1) data.2 _).mpr
        ⟨response, (stable who data.1 data.2).symm ▸ supported,
          normal.action_recall who data.1 data.2 response⟩

variable (closed : ∀ who past view response, response ∈ raw.actions who past view →
  normal.action who past view response ∈ raw.actions who past view)

/-- The canonical raw representative has exactly the same response syntax as
the normal choice. Its availability follows from closure of the raw menu. -/
def canonicalChoice (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) (observed : app.Info)
    (canonical : ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who observed)) :
    (raw.information initial horizon scheduler).Choice who observed := by
  refine ⟨canonical.1, ?_⟩
  cases observed with
  | none => exact canonical.2
  | some data =>
      obtain ⟨response, member, chosen⟩ := canonical.2
      have rawMember := ((normal.menu_mem_iff_of_closed raw who
        (normal.recall who data.1) data.2 (closed who _ _) response).mp member).1
      exact ⟨response, (stable who data.1 data.2) ▸ rawMember, chosen⟩

@[simp] theorem choice_canonicalChoice (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) (observed : app.Info)
    (canonical : ((normal.menu raw).information initial horizon scheduler).Choice who
      (normal.info who observed)) :
    normal.choice raw stable initial horizon scheduler who observed
        (normal.canonicalChoice raw stable closed initial horizon scheduler who observed
          canonical) =
      canonical := by
  apply Subtype.ext
  cases observed with
  | none => rfl
  | some data =>
      obtain ⟨response, member, chosen⟩ := canonical.2
      have fixed := normal.menu_normal raw who (normal.recall who data.1) data.2 response member
      rw [normal.action_recall] at fixed
      change canonical.1.map (normal.action who data.1 data.2) = canonical.1
      rw [chosen, Option.map_some, fixed]

end Interaction.ReactiveApplication.SubmissionNormalization

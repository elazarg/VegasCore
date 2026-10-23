/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Math.Probability.ExpectationComposition

/-! # Play until a stopping set

Behavioral play from a history until it reaches a stopping set or a terminal
history (`GameTheory.Protocol.InformationModel.runBehavioralUntil`) is a law on
the first such histories. Terminal play is play until the stopping set followed
by terminal play from there
(`GameTheory.Protocol.InformationModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil`).

Play until a stopping set depends only on the policies' answers at the
nonterminal histories it can reach
(`GameTheory.Protocol.InformationModel.runBehavioralUntil_congr`), stays in
every set of states closed under legal steps
(`GameTheory.Protocol.InformationModel.runBehavioralUntil_support_closed`), and,
from a decision whose information state cannot matter twice, is affine in the
law installed there
(`GameTheory.Protocol.InformationModel.runBehavioralUntil_update_withLaw_eq_bind`).
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} [Fintype ι] {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)

/-- One step of play from a nonterminal history reaches only its one-step
extensions, and whatever they reach. -/
theorem mem_support_runBehavioralFrom_one (policies : (i : ι) → M.BehavioralPolicy i)
    {history next : E.History} (running : ¬ E.terminal history.state)
    (member : next ∈ (M.runBehavioralFrom policies 1 history).support) :
    E.HistorySuccessor next history ∧
      ∀ later, E.HistoryReaches next later → E.HistoryReaches history later := by
  rw [M.runBehavioralFrom_succ_of_not_terminal policies 0 running,
    PMF.mem_support_bind_iff] at member
  obtain ⟨draw, _, stepped⟩ := member
  rw [PMF.mem_support_bindOnSupport_iff] at stepped
  obtain ⟨target, realized, reached⟩ := stepped
  change next ∈ (PMF.pure _).support at reached
  rw [PMF.mem_support_pure_iff] at reached
  subst reached
  exact ⟨⟨draw.1, draw.2, realized⟩, fun later reached =>
    ExecutionProtocol.HistoryReaches.step E draw.2 realized reached⟩

open Classical in
/-- **Play until a stopping set.** Behavioral play from a history, one step at a
time, until it reaches a history of the stopping set or a terminal history. -/
def runBehavioralUntil (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped : E.History → Prop) :
    E.History → PMF E.History :=
  E.historyBackwardRec certificate fun history recurse =>
    if stopped history then PMF.pure history
    else if running : E.terminal history.state then PMF.pure history
    else (M.runBehavioralFrom policies 1 history).bindOnSupport fun next member =>
      recurse next (M.mem_support_runBehavioralFrom_one policies running member).1

theorem runBehavioralUntil_of_stopped (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) {stopped : E.History → Prop}
    {history : E.History} (stop : stopped history) :
    M.runBehavioralUntil certificate policies stopped history = PMF.pure history := by
  classical
  rw [runBehavioralUntil, ExecutionProtocol.historyBackwardRec_eq, ite_eq_left stop ..]

theorem runBehavioralUntil_of_terminal (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) {stopped : E.History → Prop}
    {history : E.History} (ended : E.terminal history.state) :
    M.runBehavioralUntil certificate policies stopped history = PMF.pure history := by
  classical
  rw [runBehavioralUntil, ExecutionProtocol.historyBackwardRec_eq]
  split <;> rfl

/-- From an unstopped nonterminal history, play until the stopping set takes
one step and continues. -/
theorem runBehavioralUntil_of_running (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) {stopped : E.History → Prop}
    {history : E.History} (going : ¬ stopped history) (running : ¬ E.terminal history.state) :
    M.runBehavioralUntil certificate policies stopped history =
      (M.runBehavioralFrom policies 1 history).bind
        (M.runBehavioralUntil certificate policies stopped) := by
  classical
  rw [runBehavioralUntil, ExecutionProtocol.historyBackwardRec_eq, ite_eq_right going ..,
    dite_eq_right running]
  exact PMF.bindOnSupport_eq_bind _ _

/-- Play until a stopping set ends at stopped or terminal histories. -/
theorem mem_support_runBehavioralUntil (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped : E.History → Prop)
    (start : E.History) :
    ∀ stop ∈ (M.runBehavioralUntil certificate policies stopped start).support,
      stopped stop ∨ E.terminal stop.state := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  intro stop member
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies halt,
      PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inl halt
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended,
      PMF.mem_support_pure_iff] at member
    subst member
    exact Or.inr ended
  rw [M.runBehavioralUntil_of_running certificate policies halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  exact ih next (M.mem_support_runBehavioralFrom_one policies ended nextMember).1 stop reached

omit [Fintype ι] in
/-- A bind after a support-dependent bind distributes into its branches. -/
private theorem bindOnSupport_bind {α β γ : Type*} (law : PMF α)
    (first : ∀ a ∈ law.support, PMF β) (second : β → PMF γ) :
    (law.bindOnSupport first).bind second =
      law.bindOnSupport fun a member => (first a member).bind second := by
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  refine bindOnSupport_congr _ fun a member => ?_
  rw [PMF.bindOnSupport_eq_bind]

/-- Profiles that answer alike at every nonterminal history play can reach
induce the same play until a stopping set. -/
theorem runBehavioralUntil_congr (certificate : E.WellFoundedHistories)
    {first second : (i : ι) → M.BehavioralPolicy i} (stopped : E.History → Prop)
    (start : E.History)
    (agree : ∀ later, E.HistoryReaches start later → ¬ E.terminal later.state →
      ∀ i, first i (M.infoOf i later.trace) = second i (M.infoOf i later.trace)) :
    M.runBehavioralUntil certificate first stopped start =
      M.runBehavioralUntil certificate second stopped start := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate first halt,
      M.runBehavioralUntil_of_stopped certificate second halt]
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate first ended,
      M.runBehavioralUntil_of_terminal certificate second ended]
  rw [M.runBehavioralUntil_of_running certificate first halt ended,
    M.runBehavioralUntil_of_running certificate second halt ended,
    M.runBehavioralFrom_congr 1 history fun later reached running =>
      agree later ⟨1, reached⟩ running]
  apply bind_congr_on_support
  intro next member
  obtain ⟨successor, reaches⟩ := M.mem_support_runBehavioralFrom_one second ended member
  exact ih next successor fun later reached running =>
    agree later (reaches later reached) running

/-- **Play until a stopping set from a decision is affine in its law.** From an
unstopped nonterminal history at an information state where `who` acts and
which cannot matter twice, play until the stopping set with a law installed
there draws a choice from the law and plays the corresponding commitment. -/
theorem runBehavioralUntil_update_withLaw_eq_bind [DecidableEq ι]
    (certificate : E.WellFoundedHistories) (actsOnce : M.ActsOnceWhereItMatters)
    (profile : (i : ι) → M.BehavioralPolicy i) (who : ι) (policy : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)] (info : M.InfoState who) (law : PMF (M.Choice who info))
    (stopped : E.History → Prop) (history : E.History)
    (atInfo : M.infoOf who history.trace = info) (going : ¬ stopped history)
    (running : ¬ E.terminal history.state) (active : E.active history.state who) :
    M.runBehavioralUntil certificate
        (Profile.update (sig := M.behavioralSignature) profile who (policy.withLaw info law))
        stopped history =
      law.bind fun choice => M.runBehavioralUntil certificate
        (Profile.update (sig := M.behavioralSignature) profile who (policy.commit info choice))
        stopped history := by
  rw [M.runBehavioralUntil_of_running certificate _ going running,
    M.runBehavioralFrom_update_withLaw_eq_bind actsOnce profile who policy info law history
      atInfo running active 0, PMF.bind_bind]
  refine bind_congr_on_support law fun choice _ => ?_
  rw [M.runBehavioralUntil_of_running certificate _ going running,
    M.runBehavioralFrom_succ_of_not_terminal _ 0 running, PMF.bind_bind, PMF.bind_bind]
  refine bind_congr_on_support _ fun draw _ => ?_
  rw [bindOnSupport_bind, bindOnSupport_bind]
  refine bindOnSupport_congr _ fun target realized => ?_
  change (PMF.pure _).bind _ = (PMF.pure _).bind _
  rw [PMF.pure_bind, PMF.pure_bind]
  refine M.runBehavioralUntil_congr certificate stopped _ fun later reached later_running
    player => ?_
  obtain ⟨fuel, within⟩ := reached
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact M.withLaw_eq_commit_after_actsOnce actsOnce policy info law choice atInfo active
      draw.2 realized later within later_running
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

/-- Play until a stopping set stays in every set of states closed under legal
steps. -/
theorem runBehavioralUntil_support_closed (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped : E.History → Prop)
    (closed : E.State → Prop)
    (step : ∀ state joint (legal : E.Legal state joint) target, closed state →
      target ∈ (E.step state ⟨joint, legal⟩).support → closed target)
    (start : E.History) (holds : closed start.state) :
    ∀ stop ∈ (M.runBehavioralUntil certificate policies stopped start).support,
      closed stop.state := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  intro stop member
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies halt,
      PMF.mem_support_pure_iff] at member
    subst member
    exact holds
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended,
      PMF.mem_support_pure_iff] at member
    subst member
    exact holds
  rw [M.runBehavioralUntil_of_running certificate policies halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
    M.mem_support_runBehavioralFrom_one policies ended nextMember
  exact ih next ⟨joint, legal, realized⟩ (step _ joint legal _ holds realized) stop reached

/-- Play until a stopping set stays in every set of states closed under the
legal steps from unstopped nonterminal histories. -/
theorem runBehavioralUntil_support_closed_of_going (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped : E.History → Prop)
    (closed : E.State → Prop)
    (step : ∀ history : E.History, ¬ stopped history → ¬ E.terminal history.state →
      ∀ joint (legal : E.Legal history.state joint) target, closed history.state →
        target ∈ (E.step history.state ⟨joint, legal⟩).support → closed target)
    (start : E.History) (holds : closed start.state) :
    ∀ stop ∈ (M.runBehavioralUntil certificate policies stopped start).support,
      closed stop.state := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  intro stop member
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies halt,
      PMF.mem_support_pure_iff] at member
    subst member
    exact holds
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended,
      PMF.mem_support_pure_iff] at member
    subst member
    exact holds
  rw [M.runBehavioralUntil_of_running certificate policies halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
    M.mem_support_runBehavioralFrom_one policies ended nextMember
  exact ih next ⟨joint, legal, realized⟩
    (step history halt ended joint legal _ holds realized) stop reached

/-- A pure current commitment is consumed at the first step. Its continuation
uses the original profile because the information state cannot matter twice. -/
theorem runBehavioralTerminalFrom_commit_eq_bind [DecidableEq ι]
    [∀ i, DecidableEq (M.InfoState i)]
    (certificate : E.WellFoundedHistories) (actsOnce : M.ActsOnceWhereItMatters)
    (profile : ∀ i, M.BehavioralPolicy i) (who : ι) (history : E.History)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    let forced := Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).commit (M.infoOf who history.trace) choice)
    M.runBehavioralTerminalFrom certificate forced history =
      (M.runBehavioralFrom forced 1 history).bind
        (M.runBehavioralTerminalFrom certificate profile) := by
  classical
  intro forced
  rw [M.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate forced 1 history]
  apply bind_congr_on_support
  intro next supported
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralFrom_of_terminal forced 1 ended,
      PMF.mem_support_pure_iff] at supported
    subst next
    simp only [runBehavioralTerminalFrom, E.randomizedBackwardLaw_of_terminal ended]
  rw [M.runBehavioralFrom_succ_of_not_terminal forced 0 ended,
    PMF.mem_support_bind_iff] at supported
  obtain ⟨joint, _drawn, supported⟩ := supported
  rw [PMF.mem_support_bindOnSupport_iff] at supported
  obtain ⟨target, realized, exactNext⟩ := supported
  change next ∈ (PMF.pure (history.extend joint.property realized)).support at exactNext
  cases (PMF.mem_support_pure_iff _ _).mp exactNext
  let draws : ∀ owner, M.Choice owner (M.infoOf owner history.trace) := fun owner =>
    if same : owner = who then same.symm ▸ choice
    else (profile owner (M.infoOf owner history.trace)).support_nonempty.choose
  apply M.runBehavioralTerminalFrom_congr certificate
  intro later reachable running owner
  by_cases own : owner = who
  · subst owner
    obtain ⟨fuel, reachable⟩ := reachable
    have agree := M.commit_agree_of_actsOnce actsOnce profile draws joint.property realized
      later reachable running who
    simpa only [forced, Profile.update_same, draws, dite_true, eq_rec_constant] using agree
  · simp only [forced, Profile.update_of_ne _ _ own]

/-- **Terminal play splits at a stopping set.** Terminal play from a history is
play until the stopping set followed by terminal play from there. -/
theorem runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
    (certificate : E.WellFoundedHistories) (policies : (i : ι) → M.BehavioralPolicy i)
    (stopped : E.History → Prop) (start : E.History) :
    M.runBehavioralTerminalFrom certificate policies start =
      (M.runBehavioralUntil certificate policies stopped start).bind
        (M.runBehavioralTerminalFrom certificate policies) := by
  induction start using certificate.induction with
  | _ history ih =>
  by_cases stop : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies stop, PMF.pure_bind]
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended, PMF.pure_bind]
  rw [M.runBehavioralUntil_of_running certificate policies stop ended, PMF.bind_bind,
    M.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate policies 1 history]
  apply bind_congr_on_support
  intro next member
  exact ih next (M.mem_support_runBehavioralFrom_one policies ended member).1

end InformationModel

end GameTheory.Protocol

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOpeningLaw

/-! # States consistent with a late-delivery site

A profile that installs a law at one information state of the owner differs
from the assessment's strategy only there. Play from that site visits states at
which the owner either is at the site itself or has recalled past it
(`Vegas.SiteConsistent`); every control step keeps such states
(`Vegas.siteConsistent_step`), and the site's histories start in them
(`Vegas.siteConsistent_of_history`). At such a state, an owner activation with
the site's late-delivery key is the site itself (`Vegas.siteConsistent_key`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The recall of an information state; empty at a non-decision input. -/
def infoRecall : (application setup runtime leaks).Info → List (application setup runtime
  leaks).PlayerEntry
  | none => []
  | some (past, _) => past

/-- **Consistent with a site.** The owner acts at the site's information, or its
recall strictly longer the site's recall. -/
def SiteConsistent (who : Player) (info : (application setup runtime leaks).Info) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control => (info.isSome ∧ (application setup runtime leaks).observe who (some control) =
    info) ∨
      ∃ entry rest, control.execution.recall who = infoRecall (runtime := runtime) info ++ entry
        :: rest

/-- The control step appends one entry to the recall of an acting player and
keeps every other player's recall. -/
theorem controlStep_recall {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    (players : Player → (application setup runtime leaks).Policy)
    (control : (application setup runtime leaks).Control) {next : (application setup runtime
      leaks).ProtocolState}
    (member : next ∈ ((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
      players (some control)).support) (who : Player) :
    ∃ control', next = some control' ∧
      (control.actor = some who → ∃ entry, control'.execution.recall who =
        control.execution.recall who ++ [entry]) ∧
      (control.actor ≠ some who →
        control'.execution.recall who = control.execution.recall who) := by
  rcases control with ⟨remaining, actor, execution⟩
  unfold ReactiveApplication.controlStep at member
  cases actor with
  | none =>
      have idle : (none : Option Player) ≠ some who := fun same => by cases same
      cases remaining with
      | zero =>
          exact ⟨_, (PMF.mem_support_pure_iff _ _).mp member, fun acting => (idle acting).elim,
            fun _ => rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
          obtain ⟨next', supported, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, fun acting => (idle acting).elim, fun _ => congrFun
            ((application setup runtime leaks).environmentStep_recall execution next' command
              supported)
            who⟩
  | some actor =>
      simp only [ReactiveApplication.actor, Option.bind_some] at member
      rw [PMF.mem_support_bind_iff] at member
      obtain ⟨action, _, reached⟩ := member
      refine ⟨_, (PMF.mem_support_pure_iff _ _).mp reached, ?_, ?_⟩
      · intro acting
        cases Option.some.inj acting
        simp only [↓reduceIte, Option.getD_some, ReactiveApplication.Execution.respond]
        rcases action with ⟨_ | _⟩ <;> exact ⟨_, rfl⟩
      · intro idle
        have different : who ≠ actor := fun same => idle (by rw [same])
        simp only [↓reduceIte, Option.getD_some]
        exact (application setup runtime leaks).respond_recall_other execution actor who different _

/-- **Site consistency is kept by every control step.** -/
theorem siteConsistent_step {horizon : Nat} {scheduler : (application setup runtime
  leaks).Scheduler}
    (players : Player → (application setup runtime leaks).Policy) (who : Player)
    (info : (application setup runtime leaks).Info) {state : (application setup runtime
      leaks).ProtocolState}
    (consistent : SiteConsistent (runtime := runtime) who info state) {next : (application setup
      runtime leaks).ProtocolState}
    (member : next ∈ ((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
      players state).support) :
    SiteConsistent (runtime := runtime) who info next := by
  cases state with
  | none => exact consistent.elim
  | some control =>
      obtain ⟨control', rfl, acted, idle⟩ := controlStep_recall (runtime := runtime) players
        control member who
      right
      rcases consistent with ⟨isSome, atSite⟩ | ⟨entry, rest, longer⟩
      · have acting : control.actor = some who := by
          by_contra notActing
          simp only [ReactiveApplication.observe, notActing, ↓reduceIte] at atSite
          rw [← atSite] at isSome
          cases isSome
        obtain ⟨added, appended⟩ := acted acting
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at atSite
        rw [← atSite]
        exact ⟨added, [], appended⟩
      · by_cases acting : control.actor = some who
        · obtain ⟨added, appended⟩ := acted acting
          exact ⟨entry, rest ++ [added], by rw [appended, longer]; simp⟩
        · exact ⟨entry, rest, by rw [idle acting, longer]⟩

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- A history of a site is consistent with it. -/
theorem siteConsistent_of_history {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1) :
    SiteConsistent (runtime := runtime) who site.1 history.1.state := by
  have info := history.2
  rw [onePacket_infoOf] at info
  cases current : history.1.state with
  | none =>
      rw [current] at info
      rw [← info] at siteKey
      cases siteKey
  | some control =>
      rw [current] at info
      left
      refine ⟨?_, info⟩
      cases site_info : site.1 with
      | none =>
          rw [site_info] at siteKey
          cases siteKey
      | some _ => rfl

omit [Fintype Player] in
/-- **At a consistent state, the site's key is the site.** At a state consistent
with a site, an owner whose late-delivery key is the site's key observes the
site's information. -/
theorem siteConsistent_key {who : Player} {info : (application setup runtime leaks).Info}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who info = some key)
    {control : (application setup runtime leaks).Control}
    (consistent : SiteConsistent (runtime := runtime) who info (some control))
    (sameKey : LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) = key) :
    (application setup runtime leaks).observe who (some control) = info := by
  rcases consistent with ⟨_, atSite⟩ | ⟨entry, rest, longer⟩
  · exact atSite
  · exfalso
    cases info with
    | none => cases siteKey
    | some info =>
        rcases info with ⟨past, view⟩
        simp only [lateKey, Option.some.injEq] at siteKey
        have lengths := congrArg (fun key : LateKey setup runtime leaks => key.recalled.length)
          (sameKey.trans siteKey.symm)
        simp only [LateKey.ofView, List.length_map, longer, infoRecall, List.length_append,
          List.length_cons] at lengths
        omega

end Vegas

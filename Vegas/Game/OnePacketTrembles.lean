/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketForced
import Vegas.Game.IntendedAuditedOutcome
import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Compile.EventGraphBacktranslation
import Interaction.ReactiveFiniteAssessment
import GameTheory.Math.Probability.Mixture

/-! # Trembles and components of the one-packet game

**Tremble scale.** The intended step floor of an intended assessment is the
smallest positive probability of one step of intended play under its strategy:
a player's choice together with Nature's draw, including the initial draw
(`Vegas.SourceProgram.Setup.intendedStepFloor`); every step of positive
probability has at least that probability
(`Vegas.SourceProgram.Setup.intendedStepFloor_le`). The tremble scale at index
`n` and depth `T` is the floor to the power `T + 1`, divided by `n + 4`
(`Vegas.trembleScale`). Along any sequence of floors in `(0, 1]` it is at most
a quarter, and both the scale divided by the floor and its square divided by
the floor to the power `T` tend to zero
(`Vegas.tendsto_trembleScale_div`, `Vegas.tendsto_trembleScale_sq_div_pow`).

**As-if-honest play.** The intended game offers its intended menu at every
source view, including views at which the owner holds a bad binding: the values
its guard is predicted to accept given the owner's observation, or every value
when none is predicted, and always the opening at a reveal. An intended
assessment's strategy is therefore defined at the projected source view of
every native information state (`Vegas.projectView`); the as-if-honest law is
that strategy read at the projected view (`Vegas.asIfHonestProfile`). This is
the fixed choice at the owner's own bad-binding views. Its native realization
is the canonical decision of the encoded source action at the owner's turn,
silence where there is no turn or the action does not encode
(`Vegas.honestResponse`).

**Components.** At an information state of the one-packet game, a trembled
component puts the square of the scale on the uniform law over the menu, and
the rest on a mixture giving the scale to an alternative and the remainder to a
main law (`Vegas.trembledChoice`), so a main choice has probability
`(1 - scale²)(1 - scale)` times its main law at every information state. The
prescribed component sends the as-if-honest response, with silence as the
timing deviation (`Vegas.prescribedComponent`); the waiting component keeps
silence, with the as-if-honest response as the timing deviation
(`Vegas.waitComponent`); the silent component keeps silence
(`Vegas.silentComponent`). Each is fully supported for a positive scale.

**Late-delivery key.** The pool key of a late-delivery decision is its owner,
the operational part of its current view and of its recall (the contract's
public view, its network view, its receipts and its own emitted envelopes), and
at a reveal the owner's stored binding of the revealed commitment, which is
the value the opening delivers (`Vegas.lateKey`). It reads no other private
value of the owner: neither its masked store elsewhere, nor its own source
actions, nor its candidate material.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

open Classical in
/-- The positive probabilities of single steps of intended play under an
assessment's strategy, over all pairs of intended histories. -/
def intendedStepMasses [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment) : Finset ℝ :=
  let := Fintype.ofFinite setup.intendedProtocol.History
  ((Finset.univ : Finset (setup.intendedProtocol.History × setup.intendedProtocol.History)).image
    fun pair => (setup.intendedModel.runBehavioralFrom assessment.strategy 1 pair.1 pair.2).toReal
    ).filter (0 < ·)

/-- **The intended step floor.** The smallest positive probability of one step
of intended play under an assessment's strategy: a player's choice together
with Nature's draw. It is one when no step has positive probability. -/
def intendedStepFloor [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment) : ℝ :=
  if nonempty : (setup.intendedStepMasses assessment).Nonempty then
    (setup.intendedStepMasses assessment).min' nonempty
  else 1

theorem mem_intendedStepMasses [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment) {mass : ℝ} :
    mass ∈ setup.intendedStepMasses assessment →
      0 < mass ∧ mass ≤ 1 := by
  classical
  intro member
  unfold intendedStepMasses at member
  rw [Finset.mem_filter, Finset.mem_image] at member
  obtain ⟨⟨pair, _, rfl⟩, positive⟩ := member
  exact ⟨positive, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using PMF.coe_le_one _ _)⟩

theorem intendedStepFloor_pos [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment) :
    0 < setup.intendedStepFloor assessment := by
  unfold intendedStepFloor
  split
  · rename_i nonempty
    exact (setup.mem_intendedStepMasses assessment
      ((setup.intendedStepMasses assessment).min'_mem nonempty)).1
  · exact zero_lt_one

theorem intendedStepFloor_le_one [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment) :
    setup.intendedStepFloor assessment ≤ 1 := by
  unfold intendedStepFloor
  split
  · rename_i nonempty
    exact (setup.mem_intendedStepMasses assessment
      ((setup.intendedStepMasses assessment).min'_mem nonempty)).2
  · exact le_rfl

/-- Every step of intended play with positive probability has probability at
least the intended step floor. -/
theorem intendedStepFloor_le [Finite setup.intendedProtocol.History]
    (assessment : setup.intendedModel.BehavioralAssessment)
    (history next : setup.intendedProtocol.History)
    (supported : next ∈ (setup.intendedModel.runBehavioralFrom assessment.strategy 1
      history).support) :
    setup.intendedStepFloor assessment ≤
      (setup.intendedModel.runBehavioralFrom assessment.strategy 1 history next).toReal := by
  classical
  have member : (setup.intendedModel.runBehavioralFrom assessment.strategy 1 history
      next).toReal ∈ setup.intendedStepMasses assessment := by
    unfold intendedStepMasses
    rw [Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨(history, next), by simp, rfl⟩,
      ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _)⟩
  unfold intendedStepFloor
  rw [dite_eq_left ⟨_, member⟩]
  exact Finset.min'_le _ _ member

end Vegas.SourceProgram.Setup

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

section Scale

/-- **The tremble scale.** At index `n` and depth `depth`, the floor to the power
`depth + 1`, divided by `n + 4`. -/
def trembleScale (floor : ℝ) (depth n : ℕ) : ℝ :=
  floor ^ (depth + 1) / ((n : ℝ) + 4)

variable {floor : ℝ} {depth n : ℕ}

theorem trembleScale_pos (positive : 0 < floor) : 0 < trembleScale floor depth n := by
  unfold trembleScale
  positivity

theorem trembleScale_nonneg (nonnegative : 0 ≤ floor) : 0 ≤ trembleScale floor depth n := by
  unfold trembleScale
  positivity

theorem trembleScale_le_quarter (nonnegative : 0 ≤ floor) (le_one : floor ≤ 1) :
    trembleScale floor depth n ≤ 1 / 4 := by
  unfold trembleScale
  have power : floor ^ (depth + 1) ≤ 1 := pow_le_one₀ nonnegative le_one
  have positive : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  rw [div_le_div_iff₀ positive (by norm_num)]
  have : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  nlinarith

theorem trembleScale_le_one (nonnegative : 0 ≤ floor) (le_one : floor ≤ 1) :
    trembleScale floor depth n ≤ 1 :=
  (trembleScale_le_quarter nonnegative le_one).trans (by norm_num)

private theorem tendsto_of_le_inverse (ratio : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ ratio n)
    (bounded : ∀ n, ratio n ≤ 1 / ((n : ℝ) + 1)) : Tendsto ratio atTop (nhds 0) :=
  squeeze_zero nonnegative bounded tendsto_one_div_add_atTop_nhds_zero_nat

variable (floors : ℕ → ℝ) (positive : ∀ n, 0 < floors n) (le_one : ∀ n, floors n ≤ 1)
include positive le_one

/-- The tremble scale vanishes. -/
theorem tendsto_trembleScale :
    Tendsto (fun n => trembleScale (floors n) depth n) atTop (nhds 0) := by
  refine tendsto_of_le_inverse _ (fun n => trembleScale_nonneg (positive n).le) fun n => ?_
  unfold trembleScale
  have power : floors n ^ (depth + 1) ≤ 1 := pow_le_one₀ (positive n).le (le_one n)
  have cast : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg (positive n).le (depth + 1)]

/-- **The tremble scale is negligible against the floor.** -/
theorem tendsto_trembleScale_div :
    Tendsto (fun n => trembleScale (floors n) depth n / floors n) atTop (nhds 0) := by
  refine tendsto_of_le_inverse _
    (fun n => div_nonneg (trembleScale_nonneg (positive n).le) (positive n).le) fun n => ?_
  have floorPos := positive n
  have rewritten : trembleScale (floors n) depth n / floors n =
      floors n ^ depth / ((n : ℝ) + 4) := by
    unfold trembleScale
    field_simp
    ring
  rw [rewritten]
  have power : floors n ^ depth ≤ 1 := pow_le_one₀ floorPos.le (le_one n)
  have cast : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg floorPos.le depth]

/-- **The squared tremble scale is negligible against the floor to the power
of the depth.** -/
theorem tendsto_trembleScale_sq_div_pow :
    Tendsto (fun n => trembleScale (floors n) depth n ^ 2 / floors n ^ depth) atTop
      (nhds 0) := by
  refine tendsto_of_le_inverse _
    (fun n => div_nonneg (sq_nonneg _) (pow_nonneg (positive n).le _)) fun n => ?_
  have floorPos := positive n
  have rewritten : trembleScale (floors n) depth n ^ 2 / floors n ^ depth =
      floors n ^ (depth + 2) / ((n : ℝ) + 4) ^ 2 := by
    unfold trembleScale
    field_simp
    ring
  rw [rewritten]
  have power : floors n ^ (depth + 2) ≤ 1 := pow_le_one₀ floorPos.le (le_one n)
  have cast : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg floorPos.le (depth + 2)]

end Scale

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section AsIfHonest

/-- **As-if-honest play.** The law over source choices that an intended
assessment's strategy gives at the projected source view of a native
information state. At the owner's own bad-binding views it is the intended law
over the intended menu of that view. -/
def asIfHonestProfile (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (info : (application setup leaks).Info) : PMF (Option (OwnAction Player L)) :=
  (assessment.strategy who (projectView setup leaks who info)).map Subtype.val

/-- The native realization of as-if-honest play at a player view: at the
owner's turn, the canonical decision of the encoded source action, and silence
where the law chooses no action or the action does not encode at the event;
silence when it is not the player's turn. -/
def honestResponse (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : PMF (application setup leaks).Action :=
  match view.application.publicView.ownTurn? who with
  | none => PMF.pure ⟨none⟩
  | some event =>
      (asIfHonestProfile setup leaks assessment who (some (past, view))).map fun choice =>
        match choice.bind (encodeEventAction? setup.program event) with
        | none => ⟨none⟩
        | some action =>
            (runtime setup).canonicalServiceDecision leaks who past view event action

end AsIfHonest

section Components

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- The information model of the one-packet game of the default runtime. -/
abbrev onePacketModel :=
  (bounds.onePacketMenu (runtime setup) leaks).information initial horizon scheduler

open Classical in
/-- The one-packet choice transmitting a response: the response itself when the
one-packet menu offers it, silence otherwise, and the unique empty choice at a
non-decision input. -/
def responseChoice (who : Player) :
    (info : (application setup leaks).Info) → (application setup leaks).Action →
      (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info
  | none, _ => ⟨none, rfl⟩
  | some (past, view), response =>
      if member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view then
        ⟨some response, response, member, rfl⟩
      else
        ⟨some ⟨none⟩, ⟨none⟩, bounds.silence_onePacket (runtime setup) leaks who past view, rfl⟩

/-- The one-packet choice of silence. -/
def silenceChoice (who : Player) (info : (application setup leaks).Info) :
    (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info :=
  responseChoice setup leaks bounds initial horizon scheduler who info ⟨none⟩

/-- The as-if-honest response as a law over one-packet choices. -/
def honestChoice (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    (info : (application setup leaks).Info) →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
  | none => PMF.pure ⟨none, rfl⟩
  | some (past, view) => (honestResponse setup leaks assessment who past view).map
      (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view)))

/-- **A trembled component.** The square of the scale on the uniform law over
the one-packet menu, and the rest on the mixture giving the scale to the
alternative and the remainder to the main law. -/
def trembledChoice (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
    ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy initial horizon scheduler who info)
    (mix scale nonnegative le_one alternative main)

/-- **The prescribed component.** Send the as-if-honest response; the timing
deviation is silence. -/
def prescribedComponent (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (honestChoice setup leaks bounds initial horizon scheduler assessment who info)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))

/-- **The waiting component.** Keep silence; the timing deviation is the
as-if-honest response. -/
def waitComponent (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
    (honestChoice setup leaks bounds initial horizon scheduler assessment who info)

/-- **The silent component.** Keep silence, with no timing deviation. -/
def silentComponent (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))

/-- A trembled component with a positive scale is fully supported. -/
theorem trembledChoice_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)) :
    FullSupport (trembledChoice setup leaks bounds initial horizon scheduler scale positive.le
      le_one who info main alternative) := by
  intro choice
  let := Fintype.ofFinite
    ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
  exact mem_support_mix_left _ _ _ (pow_pos positive 2) (PMF.mem_support_uniformOfFintype choice)

/-- The real mass a trembled component gives a choice. -/
theorem trembledChoice_apply_toReal (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup leaks).Info)
    (main alternative :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :
    (trembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
        main alternative choice).toReal =
      scale ^ 2 * ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy initial horizon
          scheduler who info choice).toReal +
        (1 - scale ^ 2) * (scale * (alternative choice).toReal +
          (1 - scale) * (main choice).toReal) := by
  unfold trembledChoice
  rw [mix_apply_toReal, mix_apply_toReal]

end Components

section LateKey

/-- The operational part of a player view: the contract's public view, the
network view and the receipts. It leaves out the masked store, the player's own
source actions and its candidate material. -/
abbrev OperationalView :=
  EventGraphRuntime.PublicView (graph setup) ×
    MessageNetwork.PlayerView Player (application setup leaks).Payload ×
    List (MessageId Player × Bool)

/-- The operational part of a player view. -/
def operationalView (view : (application setup leaks).PlayerView) :
    OperationalView setup leaks :=
  (view.application.publicView, view.messages, view.receipts)

/-- The value an opening at the owner's turn delivers: at a reveal event, the
owner's stored binding of the revealed commitment, with its field kind; nothing
at any other event or when it is not the owner's turn. -/
def deliveredValue (who : Player) (view : (application setup leaks).PlayerView) :
    Option (Σ kind : EventGraph.EventField Player L, Option kind.Value) :=
  match view.application.publicView.ownTurn? who with
  | none => none
  | some event =>
      match nodeView (graph setup) event with
      | .resolve owner payload binding _ _ _ =>
          some ⟨.binding owner payload, binding.get? view.application.observation.store⟩
      | _ => none

/-- The pool key of a late-delivery decision. -/
structure LateKey where
  /-- The deciding player. -/
  owner : Player
  /-- The operational part of its current view. -/
  current : OperationalView setup leaks
  /-- The operational part of each recalled view, with the envelope it emitted. -/
  recalled : List (OperationalView setup leaks ×
    Option (Message Player (application setup leaks).Payload))
  /-- At a reveal, the value its opening delivers. -/
  delivered : Option (Σ kind : EventGraph.EventField Player L, Option kind.Value)

/-- **The late-delivery key.** The owner, the operational parts of its current
view and recall, and the delivered value at a reveal; `none` at a non-decision
input. -/
def lateKey (who : Player) : (application setup leaks).Info → Option (LateKey setup leaks)
  | none => none
  | some (past, view) => some
      { owner := who
        current := operationalView setup leaks view
        recalled := past.map fun entry =>
          (operationalView setup leaks entry.beforeView, entry.emitted)
        delivered := deliveredValue setup leaks who view }

end LateKey

end Vegas

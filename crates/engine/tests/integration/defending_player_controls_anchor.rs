//! `StaticCondition::DefendingPlayerControls` — the CR 508.5 anchor, bound at
//! both combat doors, in both printed polarities.
//!
//! # The defect this file pins closed
//!
//! The condition had an evaluator all along. What it did not have was an
//! ANCHOR: it resolved "which player is the defending player?" with
//! `combat.attackers.iter().find(|a| a.object_id == source_id)`, which is
//! `None` during the CR 508.1c legality check because the proposed attacker is
//! not yet in `state.combat.attackers`, and `is_some_and(..)` renders that
//! `None` as `false`.
//!
//! One root cause, TWO live bugs in OPPOSITE directions — which is why no row
//! here asserts a single arm:
//!
//! | printed gate | parsed tree | old leaf | old outcome |
//! |---|---|---|---|
//! | `can't attack **unless** defending player controls …` | `Not { DefendingPlayerControls }` | `false` → `Not` `true` | definition SURVIVES the CR 604.1 filter ⇒ **restriction always applied** (Dandân, Hammerhead Shark could never attack on any board) |
//! | `can't attack **if** defending player controls …` | bare `DefendingPlayerControls` | `false` | definition DROPPED by the CR 604.1 filter ⇒ **restriction never applied** (Veteran Brawlers attacked freely) |
//!
//! A fix that corrected only one polarity would be worse than none, because the
//! coverage flip would then advertise cards that are actively wrong. Every 2×2
//! below asserts all of its cells.
//!
//! # The shape of the fix, named so a reverter knows what to look for
//!
//! * `combat::defending_player_for_static_gate` — the anchor authority.
//!   Precedence: proposed CR 508.1b pairing → the RECIPIENT's live attacker
//!   entry (CR 508.5) → the SOURCE's own entry. A sibling of
//!   `defending_player_cr508_5`, never a caller of it (CR 603.4's trigger-scope
//!   binding rule does not govern a CR 508.1c legality check).
//! * `layers::evaluate_condition_with_attack_pairing` — the wrapper that
//!   carries a proposed pairing, with the CR 109.4 / CR 725.5 designation
//!   guard the other two wrappers carry.
//! * `combat::attacker_can_attack_target` — the per-pairing CR 508.1c door. It
//!   supplies `attack_target` to `static_abilities::check_static_ability`, whose
//!   `static_ability_match_applies` both SKIPS a defender-anchored gate when no
//!   pairing is in context and evaluates it against the pairing when one is, so
//!   the bare-`DefendingPlayerControls` polarity is not dropped before the
//!   pairing is known. There is deliberately no second, per-attacker clause in
//!   that function: the whole-game sweep already reaches the attacker's own
//!   `affected: SelfRef` definitions.
//! * `combat::carries_defender_sensitive_local_cant_attack` — the routing
//!   predicate for the target-agnostic door, iterating
//!   `functioning_abilities::functioning_static_definitions` (the
//!   condition-SKIPPING sibling) so a bare `DefendingPlayerControls` gate is not
//!   filtered out before it can be classified.
//! * `combat::creature_cant_attack_on_any_target` — the existential form, for
//!   narrowing the CR 508.1a candidate set by CR 508.1c, the must-attack
//!   override (CR 508.1c beats CR 508.1d) and the display badge. The
//!   restriction itself is CR 508.1c at BOTH doors; CR 508.1a is only the step
//!   that chooses which creatures will attack.
//!
//! # FIXTURE CONTRACT
//!
//! Inherited in substance from `issue_8183_static_gate_fail_open.rs`, whose
//! helpers are private to that file; the properties are reproduced here rather
//! than imported, and each is named where it is constructed.
//!
//! **F1 — every `is_err` arm has a paired positive control in the SAME
//! fixture.** An unrestricted Grizzly Bears that IS a legal attacker, or an
//! unrestricted attacker that CAN be blocked. This is not ritual: the first
//! probe written against this mechanism returned `Err` in every row including
//! its own control, i.e. it measured nothing.
//!
//! **F2 — every combat fixture leaves at least one legal block available.**
//! The engine auto-submits the declare-blockers step when `valid_blocker_ids`
//! is empty, so a block row whose restriction correctly applies and where
//! nothing else is blockable never enters the step under test. Every block row
//! declares TWO attackers: the card under test and an unrestricted ally.
//! Constructed and asserted by `declare_attackers_and_reach_blockers`.
//!
//! **F3 — the board reach-guard.** Where an arm turns on a permanent having a
//! particular type line (an Island, an artifact LAND, a SNOW land), the fixture
//! asserts the permanent really carries it before reading the legality outcome.
//! A probe run whose "artifact land" was `types=[Land], subtypes=[]` proved
//! nothing in either arm.
//!
//! **F4 — a row that concludes "the restriction does NOT apply" must first
//! prove the carrier HAS the restriction.** The zone / phasing rows (R13–R15)
//! assert a NEGATIVE about a gate on the carrier, so each one reads the
//! carrier's ungated definition list through
//! `assert_carries_one_cant_attack_static` before drawing any conclusion, and
//! each pairs its suppressed arm with an unsuppressed arm in the SAME fixture.
//! Without both, a fixture that simply failed to build the carrier passes
//! vacuously.
//!
//! Every card is built from VERBATIM Oracle text through
//! `GameScenario`/`GameRunner`, so the production route runs end to end: Oracle
//! text → static parser → `StaticDefinition.condition` → `evaluate_condition*`
//! → combat legality. Three `StaticDefinition`s in this file are SYNTHESIZED
//! rather than parsed, each labelled as such at its construction site: the
//! bare-polarity half of the quantity-door pin (R12), the unrelated remote
//! carrier that makes R10's `sources` assertions distinguish carriers, and
//! R15's remote defender-anchored carrier (a shape no printed card has).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use engine::game::combat::{AttackTarget, CombatRequirement};
use engine::game::game_object::{PhaseOutCause, PhaseStatus};
use engine::game::phasing::phase_out_object;
use engine::game::scenario::{GameRunner, GameScenario, P0, P1};
use engine::types::ability::{
    Comparator, PlayerScope, QuantityExpr, QuantityRef, StaticCondition, StaticDefinition,
    TargetFilter,
};
use engine::types::card_type::{CoreType, Supertype};
use engine::types::events::GameEvent;
use engine::types::game_state::WaitingFor;
use engine::types::identifiers::ObjectId;
use engine::types::mana::ManaColor;
use engine::types::phase::Phase;
use engine::types::player::PlayerId;
use engine::types::statics::StaticMode;
use engine::types::zones::Zone;

const P2: PlayerId = PlayerId(2);

// --- Verbatim Oracle text (Scryfall `cards/named?exact=`) --------------------

/// The 33-card `can't attack unless` majority, with NO second line — preferred
/// over Dandân for the attack-side rows precisely because Dandân's "When you
/// control no Islands, sacrifice this creature" adds a way for a fixture to go
/// vacuous.
const HAMMERHEAD_SHARK: &str =
    "This creature can't attack unless defending player controls an Island.";

/// The `can't attack if` mirror polarity. The SECOND line is verbatim and must
/// not surprise a fixture: it is a `CantBlock` static gated on the controller's
/// own untapped lands, and every row here keeps Veteran Brawlers on offence.
const VETERAN_BRAWLERS: &str = "This creature can't attack if defending player controls an untapped land.\nThis creature can't block if you control an untapped land.";

/// Second `can't attack if` card, with a richer filter (untapped CREATURE with
/// power 3 or greater → `Untapped` + `PtComparison`). Line 1 is a keyword and
/// line 3 is a block restriction; neither is exercised here.
const ORGG: &str = "Trample\nThis creature can't attack if defending player controls an untapped creature with power 3 or greater.\nThis creature can't block creatures with power 3 or greater.";

/// The block door, intrinsic (`affected: SelfRef`) form. Measured working
/// BEFORE this change, so it is the non-regression anchor for the anchor
/// refactor.
const SCRAPDIVER_SERPENT: &str =
    "This creature can't be blocked as long as defending player controls an artifact.";

/// The ONLY remote-`affected` card in the population, and the only one whose
/// anchor must follow the RECIPIENT rather than the source.
const TANGLEWALKER: &str = "Each creature you control can't be blocked as long as defending player controls an artifact land.";

/// `CantBeBlockedBy { filter }` — proves the fix is mode-agnostic rather than
/// special-cased to `CantBeBlocked`.
const ARCTIC_FOXES: &str = "This creature can't be blocked by creatures with power 2 or greater as long as defending player controls a snow land.";

/// Defending-player QUANTITY shape, deliberately NOT fixed here. Outside the
/// 45-card `DefendingPlayerControls` population.
const GOBLIN_GOON: &str =
    "This creature can't attack or block unless you control more creatures than defending player.";

// --- Fixture helpers --------------------------------------------------------

/// From `Phase::PreCombatMain`, reach the declare-attackers step and PROVE we
/// arrived, so a harness change surfaces as a clear failure rather than
/// silently making every legality assertion below vacuous (CR 508.1).
fn advance_to_declare_attackers(runner: &mut GameRunner) {
    runner.advance_to_combat();
    assert!(
        matches!(
            runner.state().waiting_for,
            WaitingFor::DeclareAttackers { .. }
        ),
        "fixture must reach the declare-attackers step; got {}",
        runner.state().waiting_for.variant_name()
    );
}

/// The three fields of the live `WaitingFor::DeclareAttackers` payload every row
/// here reads, owned so the fixture can keep mutating the runner afterwards.
struct AttackersPayload {
    /// CR 508.1a: the creatures the prompt actually offers.
    valid: Vec<ObjectId>,
    /// CR 508.1c / CR 508.1d: the per-creature display badges.
    constraints: HashMap<ObjectId, CombatRequirement>,
    /// CR 508.1b: the per-attacker selectable defenders.
    legal_targets: HashMap<ObjectId, Vec<AttackTarget>>,
}

/// The live `WaitingFor::DeclareAttackers` payload.
///
/// This IS the production payload: `turns.rs`'s declare-attackers arm builds it
/// with `combat::build_declare_attackers_waiting_for`. Rows never read
/// `combat::get_valid_attacker_ids`, which no production path consults for the
/// prompt and which would measure a query no player ever sees.
fn attackers_payload(runner: &GameRunner) -> AttackersPayload {
    let WaitingFor::DeclareAttackers {
        valid_attacker_ids,
        attacker_constraints,
        valid_attack_targets_by_attacker,
        ..
    } = &runner.state().waiting_for
    else {
        panic!(
            "must be at the declare-attackers step to read its payload; got {}",
            runner.state().waiting_for.variant_name()
        );
    };
    AttackersPayload {
        valid: valid_attacker_ids.clone(),
        constraints: attacker_constraints.clone(),
        legal_targets: valid_attack_targets_by_attacker.clone().unwrap_or_default(),
    }
}

/// FIXTURE PROPERTY F2. Declare `attackers`, then pass priority to the
/// declare-blockers step and PROVE we arrived with a block actually available.
///
/// CR 508.2: the active player gets priority after attackers are declared.
/// CR 117.4: the step ends when all players pass in succession, which is what
/// reaches CR 509.1's declare-blockers step. The pass budget is bounded so a
/// stuck transition fails loudly instead of spinning.
fn declare_attackers_and_reach_blockers(
    runner: &mut GameRunner,
    attackers: &[(ObjectId, AttackTarget)],
) {
    runner
        .declare_attackers(attackers)
        .expect("every attacker in this fixture must be a legal attacker");
    for _ in 0..8 {
        if !matches!(runner.state().waiting_for, WaitingFor::Priority { .. }) {
            break;
        }
        runner.pass_both_players();
    }
    let WaitingFor::DeclareBlockers {
        valid_blocker_ids,
        valid_block_targets,
        ..
    } = &runner.state().waiting_for
    else {
        panic!(
            "fixture must reach the declare-blockers step (CR 509.1); got {}. \
             Still `Priority` means the pass budget is too short; any other \
             prompt means some ability of a fixture card needs player input",
            runner.state().waiting_for.variant_name()
        );
    };
    assert!(
        !valid_blocker_ids.is_empty(),
        "FIXTURE PROPERTY F2: the declare-blockers step must be reached with at \
         least one legal block available, or the engine auto-submits empty \
         blockers and the row's block assertion is never evaluated"
    );
    assert!(
        !valid_block_targets.is_empty(),
        "FIXTURE PROPERTY F2: at least one blocker must have a legal attacker \
         to block; got an empty valid_block_targets map"
    );
}

/// The defending player's per-blocker legal-attacker list at the
/// declare-blockers step (CR 509.1a).
fn legal_attackers_for(runner: &GameRunner, blocker: ObjectId) -> Vec<ObjectId> {
    let WaitingFor::DeclareBlockers {
        valid_block_targets,
        ..
    } = &runner.state().waiting_for
    else {
        panic!(
            "must be at the declare-blockers step to read valid_block_targets; got {}",
            runner.state().waiting_for.variant_name()
        );
    };
    valid_block_targets
        .get(&blocker)
        .cloned()
        .unwrap_or_default()
}

/// FIXTURE PROPERTY F1, constructed rather than repeated.
///
/// Assert the card under test's declaration legality WITH its unrestricted
/// positive control, in the only ordering that can carry both claims:
///
///  * expected LEGAL — the control attacks in the SAME call. A successful
///    declaration ends the declare-attackers step (CR 508.1), so a follow-up
///    call could only ever fail and would prove nothing; declaring both at once
///    proves the control is live at the moment the claim is made.
///  * expected ILLEGAL — a rejected declaration leaves the step open
///    (CR 508.1c: the whole declaration is illegal and is not applied), so the
///    control is declared afterwards, alone.
fn assert_declaration_with_control(
    runner: &mut GameRunner,
    card: ObjectId,
    control: ObjectId,
    target: AttackTarget,
    expect_legal: bool,
    label: &str,
) {
    if expect_legal {
        let declared = runner.declare_attackers(&[(card, target), (control, target)]);
        assert!(
            declared.is_ok(),
            "CR 508.1c: the declaration must be LEGAL, and the unrestricted \
             control attacks in the same call ({label}); got {declared:?}"
        );
    } else {
        let declared = runner.declare_attackers(&[(card, target)]);
        assert!(
            declared.is_err(),
            "CR 508.1c: the declaration must be ILLEGAL ({label}); got {declared:?}"
        );
        let control_declared = runner.declare_attackers(&[(control, target)]);
        assert!(
            control_declared.is_ok(),
            "FIXTURE PROPERTY F1: the unrestricted control must be a legal \
             attacker on the same board, or the `Err` above is global rather \
             than specific ({label}); got {control_declared:?}"
        );
    }
}

/// Tap a permanent in place. This is fixture STATE, not a game action — no rule
/// is being modelled. Used by the rows whose filter carries
/// `FilterProp::Untapped`.
fn tap(runner: &mut GameRunner, id: ObjectId) {
    runner.state_mut().objects.get_mut(&id).unwrap().tapped = true;
}

/// Add `Artifact` to a land already on the battlefield, producing the
/// artifact-land type line Tanglewalker's gate asks about (CR 205.1: the type
/// line carries the card's card TYPES, plural). Written on BOTH `card_types`
/// and `base_card_types` so a layer pass cannot revert it.
fn make_artifact_land(runner: &mut GameRunner, id: ObjectId) {
    let obj = runner.state_mut().objects.get_mut(&id).unwrap();
    obj.card_types.core_types.push(CoreType::Artifact);
    obj.base_card_types = obj.card_types.clone();
    runner.state_mut().layers_dirty.mark_full();
}

/// Add the `Snow` supertype to a land already on the battlefield (CR 205.4a
/// lists snow among the supertypes; CR 205.4g: a permanent with that supertype
/// is a snow permanent), which is what Arctic Foxes'
/// `FilterProp::HasSupertype { Snow }` reads.
fn make_snow_land(runner: &mut GameRunner, id: ObjectId) {
    let obj = runner.state_mut().objects.get_mut(&id).unwrap();
    obj.card_types.supertypes.push(Supertype::Snow);
    obj.base_card_types = obj.card_types.clone();
    runner.state_mut().layers_dirty.mark_full();
}

/// FIXTURE PROPERTY F3: assert a permanent really carries the type line the arm
/// turns on, before any legality outcome is read from it.
fn assert_type_line(
    runner: &GameRunner,
    id: ObjectId,
    core: &[CoreType],
    supertypes: &[Supertype],
    subtypes: &[&str],
) {
    let obj = &runner.state().objects[&id];
    for t in core {
        assert!(
            obj.card_types.core_types.contains(t),
            "FIXTURE PROPERTY F3: {} must carry core type {t:?}; got {:?}",
            obj.name,
            obj.card_types.core_types
        );
    }
    for t in supertypes {
        assert!(
            obj.card_types.supertypes.contains(t),
            "FIXTURE PROPERTY F3: {} must carry supertype {t:?}; got {:?}",
            obj.name,
            obj.card_types.supertypes
        );
    }
    for t in subtypes {
        assert!(
            obj.card_types.subtypes.iter().any(|s| s == t),
            "FIXTURE PROPERTY F3: {} must carry subtype {t}; got {:?}",
            obj.name,
            obj.card_types.subtypes
        );
    }
}

/// FIXTURE PROPERTY F4 — the carrier reach-guard.
///
/// Read the carrier's static definitions UNGATED (`iter_unchecked` applies no
/// CR gate at all) and assert exactly one `CantAttack` / `CantAttackOrBlock`
/// definition is present. Every row that concludes "the restriction does NOT
/// apply" runs this FIRST, in EVERY arm, so a fixture whose carrier silently
/// failed to carry the restriction — the card's line not parsing, a synthesized
/// definition not attached — cannot pass for the wrong reason.
///
/// The count is pinned at exactly one so the off-zone retune below cannot
/// silently miss a second carrier of the same mode.
fn assert_carries_one_cant_attack_static(runner: &GameRunner, carrier: ObjectId, label: &str) {
    let obj = &runner.state().objects[&carrier];
    let modes: Vec<StaticMode> = obj
        .static_definitions
        .iter_unchecked()
        .map(|def| def.mode.clone())
        .collect();
    let count = modes
        .iter()
        .filter(|mode| matches!(mode, StaticMode::CantAttack | StaticMode::CantAttackOrBlock))
        .count();
    assert_eq!(
        count, 1,
        "FIXTURE PROPERTY F4: {} must carry exactly ONE attack restriction for \
         the row to say anything about whether it applies ({label}); got modes \
         {modes:?}",
        obj.name
    );
}

/// CR 113.6b: "An ability that states which zones it functions in functions
/// only from those zones." Retune the carrier's one attack restriction so it
/// declares the GRAVEYARD — i.e. the carrier's current zone (the battlefield)
/// is NOT a zone that definition functions in, so the restriction must not
/// apply to a battlefield carrier.
///
/// This is fixture STATE, not a game action, exactly like `tap` and
/// `make_snow_land`: it is the integration-level analogue of the unit test
/// `functioning_abilities::functioning_static_definitions_respects_active_zones`,
/// which builds the same off-zone definition directly and never reaches combat.
/// Retuning the REAL parsed definition rather than synthesizing one keeps the
/// production route (Oracle text → parser → `StaticDefinition`) intact on both
/// sides of the arm.
///
/// Written to BOTH `static_definitions` and `base_static_definitions` because
/// `layers.rs` re-seeds the live list from the base list on every full pass —
/// the same reason `make_artifact_land` writes both type-line fields.
fn make_cant_attack_graveyard_only(runner: &mut GameRunner, carrier: ObjectId, label: &str) {
    assert_carries_one_cant_attack_static(runner, carrier, label);
    {
        let obj = runner.state_mut().objects.get_mut(&carrier).unwrap();
        let mut defs: Vec<StaticDefinition> = obj.static_definitions.as_slice().to_vec();
        for def in defs.iter_mut() {
            if matches!(
                def.mode,
                StaticMode::CantAttack | StaticMode::CantAttackOrBlock
            ) {
                def.active_zones = vec![Zone::Graveyard];
            }
        }
        obj.static_definitions = defs.clone().into();
        obj.base_static_definitions = Arc::new(defs);
    }
    runner.state_mut().layers_dirty.mark_full();
}

/// CR 702.26b: phase the carrier out, through the production phasing authority
/// (`phasing::phase_out_object`) rather than by hand-writing `phase_status`, so
/// the row measures the state the game actually produces — including the
/// CR 702.26g indirect phase-out of anything attached.
fn phase_carrier_out(runner: &mut GameRunner, carrier: ObjectId, label: &str) {
    let mut events: Vec<GameEvent> = Vec::new();
    phase_out_object(
        runner.state_mut(),
        carrier,
        PhaseOutCause::Directly,
        &mut events,
    );
    assert!(
        matches!(
            runner.state().objects[&carrier].phase_status,
            PhaseStatus::PhasedOut {
                cause: PhaseOutCause::Directly
            }
        ),
        "CR 702.26b: the carrier must really be phased out before the row reads \
         any legality outcome from it ({label}); got {:?}",
        runner.state().objects[&carrier].phase_status
    );
    runner.state_mut().layers_dirty.mark_full();
}

// ---------------------------------------------------------------------------
// R1 — the `unless` polarity: the attack gate follows the DEFENDER's board
// ---------------------------------------------------------------------------

/// CR 508.1c + CR 508.5 + CR 506.2. Hammerhead Shark prints "This creature
/// can't attack unless defending player controls an Island."
///
/// The 2×2 plus a hostile third arm:
///
/// | defender's board | expected |
/// |---|---|
/// | an Island | `Ok` — **fails on revert**: before the anchor bound, this was `Err` |
/// | nothing | `Err` |
/// | a Mountain (a land, not an Island) | `Err` — the first branch reached is `matches_target_filter`'s subtype test |
///
/// FIXTURE PROPERTY F1: an unrestricted Grizzly Bears is in
/// `valid_attacker_ids` and is a legal attacker in EVERY arm, which excludes
/// summoning sickness, an illegal attack target and a harness artifact as
/// causes of the `Err`.
#[test]
fn hammerhead_shark_attacks_only_when_defender_controls_an_island() {
    // (defender's land color, gate met?)
    for (defender_land, gate_met) in [
        (Some(ManaColor::Blue), true),
        (None, false),
        (Some(ManaColor::Red), false),
    ] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let shark = scenario
            .add_creature_from_oracle(P0, "Hammerhead Shark", 5, 5, HAMMERHEAD_SHARK)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let land = defender_land.map(|color| scenario.add_basic_land(P1, color));
        let mut runner = scenario.build();

        // FIXTURE PROPERTY F3.
        if let (Some(land), Some(color)) = (land, defender_land) {
            let subtype = match color {
                ManaColor::Blue => "Island",
                ManaColor::Red => "Mountain",
                _ => unreachable!("only the two arms above are built"),
            };
            assert_type_line(&runner, land, &[CoreType::Land], &[], &[subtype]);
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload { valid, .. } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be a valid \
             attacker (defender_land = {defender_land:?}); got {valid:?}"
        );
        assert_eq!(
            valid.contains(&shark),
            gate_met,
            "CR 508.1a + CR 508.1c: the prompt must offer Hammerhead Shark iff \
             its gate can be met by some defender (defender_land = \
             {defender_land:?}); got {valid:?}"
        );

        // CR 508.5: `can't attack unless defending player controls an Island`
        // must follow the DEFENDING player's board.
        assert_declaration_with_control(
            &mut runner,
            shark,
            bear,
            AttackTarget::Player(P1),
            gate_met,
            &format!("defender_land = {defender_land:?}"),
        );
    }
}

// ---------------------------------------------------------------------------
// R3 — the `if` polarity: the restriction APPLIES when the gate is met
// ---------------------------------------------------------------------------

/// CR 508.1c + CR 508.5. Veteran Brawlers prints "This creature can't attack if
/// defending player controls an untapped land."
///
/// This is the mirror polarity, and before the fix it was a silent FAIL-OPEN:
/// the bare `DefendingPlayerControls` leaf read `false` with no anchor, the
/// CR 604.1 condition filter in `active_static_definitions` dropped the whole
/// definition, and the restriction applied on NO board.
///
/// | defender's board | expected |
/// |---|---|
/// | an untapped land | `Err` — **fails on revert**: this was `Ok` |
/// | the same land, tapped | `Ok` |
/// | a tapped land plus an untapped CREATURE | `Ok` — the filter is `Land` + `Untapped`, not "any untapped permanent"; the first branch reached is `FilterProp::Untapped` |
#[test]
fn veteran_brawlers_cant_attack_when_defender_has_an_untapped_land() {
    // (land tapped?, defender also has an untapped creature?, attack legal?)
    for (land_tapped, untapped_creature, attack_legal) in [
        (false, false, false),
        (true, false, true),
        (true, true, true),
    ] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let brawlers = scenario
            .add_creature_from_oracle(P0, "Veteran Brawlers", 3, 3, VETERAN_BRAWLERS)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let land = scenario.add_basic_land(P1, ManaColor::Green);
        let defender_creature =
            untapped_creature.then(|| scenario.add_creature(P1, "Defender Bear", 2, 2).id());
        let mut runner = scenario.build();

        assert_type_line(&runner, land, &[CoreType::Land], &[], &["Forest"]);
        if land_tapped {
            tap(&mut runner, land);
        }
        // F3: the hostile arm's untapped permanent must really be an untapped
        // NONLAND, or it proves nothing about the filter's `Land` leg.
        if let Some(creature) = defender_creature {
            assert_type_line(&runner, creature, &[CoreType::Creature], &[], &[]);
            assert!(!runner.state().objects[&creature].tapped);
            assert!(!runner.state().objects[&creature]
                .card_types
                .core_types
                .contains(&CoreType::Land));
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload { valid, .. } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be a valid attacker"
        );

        // CR 508.1c + CR 508.5: `can't attack IF defending player controls an
        // untapped land` must APPLY when the gate is met.
        assert_declaration_with_control(
            &mut runner,
            brawlers,
            bear,
            AttackTarget::Player(P1),
            attack_legal,
            &format!("land_tapped = {land_tapped}, untapped_creature = {untapped_creature}"),
        );
    }
}

// ---------------------------------------------------------------------------
// R4 — the filter half still evaluates under the new anchor
// ---------------------------------------------------------------------------

/// CR 508.1c + CR 508.5. Orgg prints "This creature can't attack if defending
/// player controls an untapped creature with power 3 or greater" — the same
/// bare polarity as R3 but with `Untapped` + `PtComparison` in the filter.
///
/// The fourth arm is the hostile one: the 3/3 is controlled by the ATTACKER's
/// own controller, so an implementation that swept "any player" rather than the
/// defending player would refuse the attack and fail here.
///
/// Orgg's third line (`can't block creatures with power 3 or greater`) is never
/// exercised — Orgg stays on offence in every arm.
#[test]
fn orgg_cant_attack_into_an_untapped_power_3_creature() {
    // (label, blocker power, tapped?, controlled by the defender?, legal?)
    for (label, power, tapped, defender_controls, attack_legal) in [
        ("untapped 3/3 on defence", 3, false, true, false),
        ("untapped 2/2 on defence", 2, false, true, true),
        ("tapped 3/3 on defence", 3, true, true, true),
        ("untapped 3/3 the ATTACKER controls", 3, false, false, true),
    ] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let orgg = scenario
            .add_creature_from_oracle(P0, "Orgg", 6, 6, ORGG)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let owner = if defender_controls { P1 } else { P0 };
        let other = scenario
            .add_creature(owner, "Power Probe", power, power)
            .id();
        let mut runner = scenario.build();
        if tapped {
            tap(&mut runner, other);
        }
        assert_eq!(
            runner.state().objects[&other].power,
            Some(power),
            "F3: the probe creature's power is what the PtComparison reads"
        );

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload { valid, .. } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be a valid attacker ({label})"
        );

        // CR 508.5: Orgg's gate reads the DEFENDING player's board only.
        assert_declaration_with_control(
            &mut runner,
            orgg,
            bear,
            AttackTarget::Player(P1),
            attack_legal,
            label,
        );
    }
}

// ---------------------------------------------------------------------------
// R5 — the binding is PER PAIRING, not board-wide
// ---------------------------------------------------------------------------

/// CR 508.1b + CR 508.5a: in a multiplayer game "a defending player" refers to
/// ONE SPECIFIC defending player — the one that creature is attacking — not to
/// all of them.
///
/// Three-player board. P1 controls an Island; P2 controls none. Hammerhead
/// Shark may attack P1 and may NOT attack P2, from the same static definition
/// on the same board. A source-keyed or first-defender implementation passes
/// every two-player row above and fails here.
///
/// The hostile arm attacks a PLANESWALKER P2 controls: the anchor must resolve
/// through `defending_player_for_target_or` to P2 (the planeswalker's
/// controller), not to the planeswalker object, so the attack is refused for
/// the same reason attacking P2 directly is.
///
/// The BATTLE/protector arm (CR 310.9d) is deliberately absent: `GameScenario`
/// has no battle builder, and a hand-built battle is not an attackable defender
/// in `attackable_defender_targets`. A second planeswalker row would prove
/// nothing the first did not, so the row is dropped rather than silently
/// substituted.
#[test]
fn hammerhead_shark_binds_per_defender_in_multiplayer() {
    let mut scenario = GameScenario::new_n_player(3, 7);
    scenario.at_phase(Phase::PreCombatMain);
    let shark = scenario
        .add_creature_from_oracle(P0, "Hammerhead Shark", 5, 5, HAMMERHEAD_SHARK)
        .id();
    let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
    let island = scenario.add_basic_land(P1, ManaColor::Blue);
    // P2 gets a land that is NOT an Island, so the arm distinguishes "no board"
    // from "the wrong board".
    let p2_land = scenario.add_basic_land(P2, ManaColor::Red);
    let p2_walker = scenario
        .add_planeswalker_from_oracle(P2, "Test Walker", "Jace", 4, "+1: Draw a card.")
        .id();
    let mut runner = scenario.build();

    assert_type_line(&runner, island, &[CoreType::Land], &[], &["Island"]);
    assert_type_line(&runner, p2_land, &[CoreType::Land], &[], &["Mountain"]);
    assert_type_line(&runner, p2_walker, &[CoreType::Planeswalker], &[], &[]);

    advance_to_declare_attackers(&mut runner);
    let AttackersPayload {
        valid,
        legal_targets: by_attacker,
        ..
    } = attackers_payload(&runner);
    assert!(
        valid.contains(&bear),
        "FIXTURE PROPERTY F1: the unrestricted bear must be a valid attacker; got {valid:?}"
    );
    assert!(
        valid.contains(&shark),
        "CR 508.1a: the shark HAS a legal declaration (against P1), so the \
         prompt must still offer it; got {valid:?}"
    );

    // CR 508.1b: the per-attacker selectable map must offer P1 and neither P2
    // nor P2's planeswalker.
    let shark_targets: HashSet<AttackTarget> = by_attacker
        .get(&shark)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .collect();
    assert!(
        shark_targets.contains(&AttackTarget::Player(P1)),
        "CR 508.5a: P1 (who controls the Island) must be a selectable target \
         for the shark; got {shark_targets:?}"
    );
    assert!(
        !shark_targets.contains(&AttackTarget::Player(P2)),
        "CR 508.5a: P2 controls no Island, so the shark's gate refuses that \
         pairing and P2 must NOT be selectable; got {shark_targets:?}"
    );
    assert!(
        !shark_targets.contains(&AttackTarget::Planeswalker(p2_walker)),
        "CR 508.5: a planeswalker answers with its CONTROLLER, so attacking \
         P2's planeswalker reads P2's board and must also be refused; got \
         {shark_targets:?}"
    );
    let bear_targets: HashSet<AttackTarget> = by_attacker
        .get(&bear)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .collect();
    assert!(
        bear_targets.contains(&AttackTarget::Player(P2))
            && bear_targets.contains(&AttackTarget::Planeswalker(p2_walker)),
        "FIXTURE PROPERTY F1: the unrestricted bear can attack P2 and P2's \
         planeswalker, so the shark's exclusions above are about its GATE and \
         not about the defenders being unattackable; got {bear_targets:?}"
    );

    // The declarations themselves, in the same fixture. The two REJECTED ones
    // run first: a rejected declaration leaves the step open (CR 508.1c), while
    // the accepted one ends it, so the accepted declaration must be last.
    assert!(
        runner
            .declare_attackers(&[(shark, AttackTarget::Player(P2))])
            .is_err(),
        "CR 508.5a: attacking P2, who controls no Island, does NOT satisfy the \
         gate — the anaphor means ONE SPECIFIC defending player"
    );
    assert!(
        runner
            .declare_attackers(&[(shark, AttackTarget::Planeswalker(p2_walker))])
            .is_err(),
        "CR 508.5: attacking P2's planeswalker resolves the anchor to P2 (the \
         controller of the planeswalker that creature is attacking)"
    );
    // FIXTURE PROPERTY F1: the unrestricted bear attacks P2 in the SAME call,
    // proving the two rejections above are about the shark's gate and not about
    // P2 being unattackable.
    let declared = runner.declare_attackers(&[
        (shark, AttackTarget::Player(P1)),
        (bear, AttackTarget::Player(P2)),
    ]);
    assert!(
        declared.is_ok(),
        "CR 508.5a: attacking P1, who controls an Island, satisfies the gate, \
         and the unrestricted bear may attack P2 in the same declaration; got \
         {declared:?}"
    );
}

// ---------------------------------------------------------------------------
// R6 — the intrinsic block door is UNREGRESSED
// ---------------------------------------------------------------------------

/// CR 509.1b + CR 508.5. Scrapdiver Serpent prints "This creature can't be
/// blocked as long as defending player controls an artifact."
///
/// This door was already correct before the anchor refactor, for a structural
/// reason: the attacker IS in `state.combat.attackers` by the time CR 509.1b
/// runs, and for `affected: SelfRef` the recipient equals the source, so the
/// old source-keyed lookup happened to hit. The row therefore asserts NON-
/// REGRESSION: if `defending_player_for_static_gate`'s precedence broke the
/// source form, this goes red.
///
/// FIXTURE PROPERTY F2: two attackers in both arms — the serpent and an
/// unrestricted ally — so the declare-blockers step is genuinely entered.
#[test]
fn scrapdiver_serpent_block_gate_unchanged() {
    for defender_artifact in [true, false] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let serpent = scenario
            .add_creature_from_oracle(P0, "Scrapdiver Serpent", 5, 5, SCRAPDIVER_SERPENT)
            .id();
        let ally = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let wall = scenario.add_creature(P1, "Stone Wall", 0, 6).id();
        let artifact = defender_artifact.then(|| {
            scenario
                .add_artifact_from_oracle(P1, "Ornithopter Husk", "")
                .id()
        });
        let mut runner = scenario.build();
        if let Some(artifact) = artifact {
            assert_type_line(&runner, artifact, &[CoreType::Artifact], &[], &[]);
        }

        advance_to_declare_attackers(&mut runner);
        declare_attackers_and_reach_blockers(
            &mut runner,
            &[
                (serpent, AttackTarget::Player(P1)),
                (ally, AttackTarget::Player(P1)),
            ],
        );

        let legal = legal_attackers_for(&runner, wall);
        assert!(
            legal.contains(&ally),
            "FIXTURE PROPERTY F1/F2: the wall must be able to block the \
             unrestricted ally in BOTH arms, so the serpent's exclusion is \
             specific rather than global (defender_artifact = \
             {defender_artifact}); got {legal:?}"
        );
        assert_eq!(
            legal.contains(&serpent),
            !defender_artifact,
            "CR 509.1b + CR 508.5: the serpent is unblockable exactly while the \
             DEFENDING player controls an artifact (defender_artifact = \
             {defender_artifact}); got {legal:?}"
        );
        assert_eq!(
            runner.declare_blockers(&[(wall, serpent)]).is_ok(),
            !defender_artifact,
            "CR 509.1b: the block declaration must agree with the legal-target \
             map (defender_artifact = {defender_artifact})"
        );
    }
}

// ---------------------------------------------------------------------------
// R7 — the remote `affected` grant binds to the RECIPIENT, not the source
// ---------------------------------------------------------------------------

/// CR 508.5 + CR 509.1b. Tanglewalker prints "Each creature you control can't
/// be blocked as long as defending player controls an artifact land."
///
/// This is the ONLY card in the population whose `affected` is remote
/// (`Typed(Creature, controller: You)`), so its `source_id` is the Tanglewalker
/// permanent — which need not be attacking at all. Before the anchor had a
/// recipient precedence step, the lookup was keyed on `source_id`, Tanglewalker
/// was not in `combat.attackers`, the anchor resolved to `None`, and the whole
/// grant was INERT.
///
/// PRIMARY form: TWO attackers attacking TWO DIFFERENT defenders, only one of
/// whom controls an artifact land. The gate must be met for one attacker and
/// unmet for the other FROM THE SAME STATIC DEFINITION — which is only possible
/// if the anchor follows the recipient. The arms swap which defender holds the
/// artifact land, so neither verdict can be a constant.
///
/// R7-GUARD, both halves:
///  * the artifact land really carries BOTH `Artifact` and `Land` (a probe run
///    whose "artifact land" was a plain land measured nothing in either arm);
///  * **Tanglewalker itself is NOT in `combat.attackers`.** If it were, its
///    `source_id` would be in the attacker list and a two-player source-keyed
///    lookup would coincidentally return the right player — i.e. the row would
///    pass on unfixed code.
///
/// Read through `combat::get_valid_block_targets_for_player`, the engine
/// predicate that BUILDS the declare-blockers payload, rather than through the
/// prompt: with the grant active, every creature attacking the artifact-land
/// defender is unblockable, so that defender's prompt is auto-submitted and the
/// step can never be observed. The positive control is the OTHER defender, who
/// can block in the same fixture.
#[test]
fn tanglewalker_two_attackers_different_defenders() {
    for artifact_land_holder in [P1, P2] {
        let other_holder = if artifact_land_holder == P1 { P2 } else { P1 };
        let mut scenario = GameScenario::new_n_player(3, 11);
        scenario.at_phase(Phase::PreCombatMain);
        let tanglewalker = scenario
            .add_creature_from_oracle(P0, "Tanglewalker", 2, 2, TANGLEWALKER)
            .id();
        let attacker_gated = scenario.add_creature(P0, "Gated Attacker", 2, 2).id();
        let attacker_plain = scenario.add_creature(P0, "Plain Attacker", 2, 2).id();
        let artifact_land = scenario.add_basic_land(artifact_land_holder, ManaColor::Blue);
        scenario.add_basic_land(other_holder, ManaColor::Blue);
        let blocker_a = scenario
            .add_creature(artifact_land_holder, "Wall A", 0, 6)
            .id();
        let blocker_b = scenario.add_creature(other_holder, "Wall B", 0, 6).id();
        let mut runner = scenario.build();
        make_artifact_land(&mut runner, artifact_land);

        // R7-GUARD half 1 (FIXTURE PROPERTY F3).
        assert_type_line(
            &runner,
            artifact_land,
            &[CoreType::Artifact, CoreType::Land],
            &[],
            &["Island"],
        );

        advance_to_declare_attackers(&mut runner);
        runner
            .declare_attackers(&[
                (attacker_gated, AttackTarget::Player(artifact_land_holder)),
                (attacker_plain, AttackTarget::Player(other_holder)),
            ])
            .expect("both attackers are unrestricted; only BLOCKING is gated here");

        // R7-GUARD half 2: the grant's SOURCE is not an attacker.
        let attackers: Vec<ObjectId> = runner
            .state()
            .combat
            .as_ref()
            .expect("combat exists after a declaration")
            .attackers
            .iter()
            .map(|a| a.object_id)
            .collect();
        assert!(
            !attackers.contains(&tanglewalker),
            "R7-GUARD: Tanglewalker must NOT be attacking, or a source-keyed \
             anchor would coincidentally answer correctly and this row would \
             pass on unfixed code; got {attackers:?}"
        );
        assert!(
            attackers.contains(&attacker_gated) && attackers.contains(&attacker_plain),
            "both creatures must actually be attacking; got {attackers:?}"
        );

        let gated_targets = engine::game::combat::get_valid_block_targets_for_player(
            runner.state(),
            artifact_land_holder,
        );
        let plain_targets =
            engine::game::combat::get_valid_block_targets_for_player(runner.state(), other_holder);

        assert!(
            plain_targets
                .get(&blocker_b)
                .is_some_and(|atk| atk.contains(&attacker_plain)),
            "FIXTURE PROPERTY F1: the defender WITHOUT an artifact land must be \
             able to block, so the exclusion below is about the gate and not \
             about blocking being broken (artifact_land_holder = \
             {artifact_land_holder:?}); got {plain_targets:?}"
        );
        assert!(
            gated_targets
                .get(&blocker_a)
                .is_none_or(|atk| !atk.contains(&attacker_gated)),
            "CR 508.5: the creature attacking the ARTIFACT-LAND defender must \
             be unblockable — the anchor follows the RECIPIENT, not \
             Tanglewalker (artifact_land_holder = {artifact_land_holder:?}); \
             got {gated_targets:?}"
        );
        assert!(
            engine::game::combat::has_cant_be_blocked_static(runner.state(), attacker_gated),
            "CR 509.1b: the recipient attacking the artifact-land defender \
             carries the restriction"
        );
        assert!(
            !engine::game::combat::has_cant_be_blocked_static(runner.state(), attacker_plain),
            "CR 508.5a: the SAME static definition must NOT restrict the \
             recipient attacking the defender who controls no artifact land — \
             this is the per-recipient half of the claim"
        );
    }
}

// ---------------------------------------------------------------------------
// R8 — `CantBeBlockedBy { filter }` honours the same gate
// ---------------------------------------------------------------------------

/// CR 509.1b + CR 508.5. Arctic Foxes prints "This creature can't be blocked by
/// creatures with power 2 or greater as long as defending player controls a
/// snow land." Proves the fix is mode-agnostic rather than special-cased to
/// `CantBeBlocked`.
///
/// | defender's land | blocker power | expected |
/// |---|---|---|
/// | snow | 2 | blocked ⇒ `Err` |
/// | snow | 1 | blocked ⇒ `Ok` (the filter's power leg still runs) |
/// | non-snow | 2 | blocked ⇒ `Ok` — the first branch reached is `FilterProp::HasSupertype { Snow }` |
#[test]
fn arctic_foxes_power_scoped_block_gate() {
    for (snow, blocker_power, block_legal) in [(true, 2, false), (true, 1, true), (false, 2, true)]
    {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let foxes = scenario
            .add_creature_from_oracle(P0, "Arctic Foxes", 2, 2, ARCTIC_FOXES)
            .id();
        let ally = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let blocker = scenario
            .add_creature(P1, "Chosen Blocker", blocker_power, 4)
            .id();
        // FIXTURE PROPERTY F2: a second, always-legal blocker so the
        // declare-blockers step is entered even when the gate applies.
        let spare = scenario.add_creature(P1, "Spare Wall", 0, 6).id();
        let land = scenario.add_basic_land(P1, ManaColor::White);
        let mut runner = scenario.build();
        if snow {
            make_snow_land(&mut runner, land);
        }
        assert_type_line(
            &runner,
            land,
            &[CoreType::Land],
            if snow { &[Supertype::Snow] } else { &[] },
            &["Plains"],
        );

        advance_to_declare_attackers(&mut runner);
        declare_attackers_and_reach_blockers(
            &mut runner,
            &[
                (foxes, AttackTarget::Player(P1)),
                (ally, AttackTarget::Player(P1)),
            ],
        );

        let spare_legal = legal_attackers_for(&runner, spare);
        assert!(
            spare_legal.contains(&ally),
            "FIXTURE PROPERTY F1: the 0-power spare wall must be able to block \
             the unrestricted ally in every arm (snow = {snow}, blocker_power \
             = {blocker_power}); got {spare_legal:?}"
        );
        let legal = legal_attackers_for(&runner, blocker);
        assert_eq!(
            legal.contains(&foxes),
            block_legal,
            "CR 509.1b + CR 508.5: Arctic Foxes refuses a power-2-or-greater \
             blocker exactly while the DEFENDING player controls a snow land \
             (snow = {snow}, blocker_power = {blocker_power}); got {legal:?}"
        );
        assert_eq!(
            runner.declare_blockers(&[(blocker, foxes)]).is_ok(),
            block_legal,
            "CR 509.1b: the block declaration must agree with the legal-target \
             map (snow = {snow}, blocker_power = {blocker_power})"
        );
    }
}

// ---------------------------------------------------------------------------
// R9 — CR 508.1c beats CR 508.1d: a gate-blocked creature is not FORCED to attack
// ---------------------------------------------------------------------------

/// CR 508.1c + CR 508.1d + CR 701.15b. A goaded creature "attacks each combat
/// if able"; a creature whose defender-anchored gate refuses EVERY attackable
/// defender is not able, so the requirement must not be enforced against it.
///
/// | defender's board | declaring ZERO attackers |
/// |---|---|
/// | no Island — the shark's gate refuses everyone | `Ok` |
/// | an Island — the shark CAN attack | `Err` (the paired positive: the requirement machinery is live) |
///
/// A second goaded, defender-gated creature under the DEFENDING player sits on
/// the board in both arms and must never appear in the active player's
/// constraint map (CR 506.2).
///
/// That off-team row does NOT observe the `active_team` parameter threaded into
/// `creature_must_attack_with_attackable_targets_gated`, and this doc does not
/// claim it does. `attacker_constraints_for_active_player` already filters
/// `!active_team.contains(&obj.controller)` before calling the function under
/// test, so the row holds for any team argument; and every production caller of
/// the `_gated` form passes `active_attacking_team(state)`, so the parameter is
/// a pure hoist that no integration fixture can discriminate. It is observed
/// directly instead, by the unit row
/// `combat::tests::must_attack_gate_reads_the_supplied_active_team`, which calls
/// the private `_gated` form twice with two different team arguments.
///
/// The goad designation is stamped on `GameObject::goaded_by` directly — that
/// field IS the CR 701.15b designation the engine reads
/// (`game::filter::FilterProp::Goaded`), and routing a real goad spell through
/// the cast pipeline would add an unrelated failure surface to a row about
/// combat requirements.
#[test]
fn a_goaded_defender_gated_creature_is_not_forced_to_attack() {
    for defender_island in [false, true] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let shark = scenario
            .add_creature_from_oracle(P0, "Hammerhead Shark", 5, 5, HAMMERHEAD_SHARK)
            .id();
        // Controlled by the DEFENDING player: outside the attacking team, so no
        // requirement of the active player's declaration may reference it.
        let off_team = scenario
            .add_creature_from_oracle(P1, "Hammerhead Shark", 5, 5, HAMMERHEAD_SHARK)
            .id();
        // FIXTURE: an unrestricted attacker on the active team. Without it the
        // no-Island arm has NO creature that can attack, the engine skips the
        // whole combat phase, and the fixture never reaches the step under test.
        // It is not goaded, so it imposes no requirement of its own.
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let island = defender_island.then(|| scenario.add_basic_land(P1, ManaColor::Blue));
        let mut runner = scenario.build();
        if let Some(island) = island {
            assert_type_line(&runner, island, &[CoreType::Land], &[], &["Island"]);
        }
        // CR 701.15b: goad both, so the two differ only in controller.
        for id in [shark, off_team] {
            runner
                .state_mut()
                .objects
                .get_mut(&id)
                .unwrap()
                .goaded_by
                .insert(if id == shark { P1 } else { P0 });
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid, constraints, ..
        } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be a valid attacker \
             in both arms (defender_island = {defender_island}); got {valid:?}"
        );
        assert!(
            !constraints.contains_key(&off_team),
            "CR 506.2: in a two-player game the nonactive player is the \
             defending player, so their creature is not on the attacking team \
             and must carry no attacker constraint; got {constraints:?}"
        );
        assert_eq!(
            valid.contains(&shark),
            defender_island,
            "CR 508.1a: eligibility must track whether some defender satisfies \
             the gate (defender_island = {defender_island}); got {valid:?}"
        );

        let declared_nothing = runner.declare_attackers(&[]);
        assert_eq!(
            declared_nothing.is_err(),
            defender_island,
            "CR 508.1c beats CR 508.1d: the goaded shark must be forced to \
             attack ONLY when its gate admits some defender \
             (defender_island = {defender_island}); got {declared_nothing:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// R10 / R10b — the display badge agrees with enforcement, in BOTH polarities
// ---------------------------------------------------------------------------

/// CR 508.1c. The `unless` polarity's payload/badge seam.
///
/// Absence from `valid_attacker_ids` and presence of the badge are JOINTLY
/// produced by two edits that are jointly, not severally, sufficient: the
/// payload narrowing in `build_declare_attackers_waiting_for`, and the swap of
/// `attacker_constraints_for_active_player`'s `else if` from
/// `creature_cant_attack_gated` to `creature_cant_attack_on_any_target`. With
/// only the narrowing, the creature is absent from `valid` but the `else if`
/// answers `false` (step 2.2 routed the definition off that door) and NO badge
/// is emitted. With only the swap, the creature is still in `valid` and the
/// `else` branch is never reached.
///
/// The `sources` half is the third edit: `cant_attack_sources_gated`'s second
/// intrinsic-carrier arm. Without it the badge appears with an EMPTY carrier
/// list. The mixed-board arm pins that two differently-caused restrictions
/// report DIFFERENT carriers.
#[test]
fn attacker_badge_matches_enforcement_for_a_defender_gated_creature() {
    for defender_island in [false, true] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let shark = scenario
            .add_creature_from_oracle(P0, "Hammerhead Shark", 5, 5, HAMMERHEAD_SHARK)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        // Mixed board: a second creature restricted for an UNRELATED reason and
        // by a DIFFERENT carrier, so the `sources` assertions below distinguish
        // carriers rather than merely counting badges.
        //
        // The carrier is a SYNTHESIZED remote `CantAttack` scoped to one object —
        // the same shape `combat.rs`'s own
        // `cant_attack_sources_collects_two_sorted_remote_carriers` uses. An
        // Aura would need real CR 303.4 enchant wiring (CR 704.5m puts an Aura
        // attached to an illegal object — or to nothing — into its owner's
        // GRAVEYARD on the next state-based-action check, destroying the carrier
        // outright rather than merely unattaching it; CR 704.5p, which
        // unattaches, explicitly excludes Auras), which is an unrelated failure
        // surface for a row about carrier attribution.
        let restricted = scenario.add_creature(P0, "Restrained Bear", 2, 2).id();
        let restrainer = scenario
            .add_enchantment_from_oracle(P0, "Restraining Bolt", "")
            .with_static_definition(
                StaticDefinition::new(StaticMode::CantAttack)
                    .affected(TargetFilter::SpecificObject { id: restricted }),
            )
            .id();
        let island = defender_island.then(|| scenario.add_basic_land(P1, ManaColor::Blue));
        let mut runner = scenario.build();
        if let Some(island) = island {
            assert_type_line(&runner, island, &[CoreType::Land], &[], &["Island"]);
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid,
            constraints,
            legal_targets: by_attacker,
        } = attackers_payload(&runner);

        assert!(
            valid.contains(&bear) && !constraints.contains_key(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be offered and \
             badge-free in both arms; got valid={valid:?} constraints={constraints:?}"
        );
        // The unrelated restriction is the mixed-board control: it is badged in
        // BOTH arms, with ITS OWN carrier.
        let restricted_badge = constraints.get(&restricted);
        assert!(
            matches!(
                restricted_badge,
                Some(CombatRequirement::CantAttack { sources }) if sources.contains(&restrainer)
            ),
            "CR 508.1c + CR 611.3a: the remotely-restricted creature must carry \
             a CantAttack badge naming the RESTRAINING PERMANENT as its \
             carrier, so the shark's self-carried badge below is a distinct \
             attribution and not a shared constant; got {restricted_badge:?}"
        );

        assert_eq!(
            valid.contains(&shark),
            defender_island,
            "CR 508.1c: the payload must offer the shark iff some defender \
             satisfies its gate (defender_island = {defender_island}); got {valid:?}"
        );
        let shark_badge = constraints.get(&shark);
        if defender_island {
            assert!(
                shark_badge.is_none(),
                "CR 508.1c: with a qualifying defender the shark carries NO \
                 badge; got {shark_badge:?}"
            );
            assert!(
                by_attacker.get(&shark).is_some_and(|t| !t.is_empty()),
                "CR 508.1b: the shark must have at least one selectable target; \
                 got {by_attacker:?}"
            );
        } else {
            assert!(
                matches!(
                    shark_badge,
                    Some(CombatRequirement::CantAttack { sources }) if sources == &vec![shark]
                ),
                "CR 508.1c: with no qualifying defender the shark must carry a \
                 CantAttack badge whose only carrier is ITSELF (CR 604.1 + \
                 CR 109.5: an unscoped source-local restriction is intrinsic); \
                 got {shark_badge:?}"
            );
        }
    }
}

/// CR 508.1c. The `if` polarity's payload/badge seam — the row that exists
/// solely to pin the ITERATOR inside
/// `combat::carries_defender_sensitive_local_cant_attack`.
///
/// That helper MUST iterate `functioning_abilities::functioning_static_definitions`.
/// Substitute `active_static_definitions` and all three assertions below invert
/// at once: a bare `DefendingPlayerControls` gate evaluates `false` with no
/// pairing, the CR 604.1 condition filter drops the definition on every board,
/// the helper answers `false` unconditionally for the whole `if` population,
/// and Veteran Brawlers keeps both the eligibility and the badge it is supposed
/// to lose.
///
/// No other row catches that substitution: R1/R3/R4 exercise
/// `declare_attackers`, which routes through `attacker_can_attack_target` and so
/// through `check_static_ability`'s whole-game `game_functioning_statics` sweep
/// — a different (and already correct) iterator that this helper's substitution
/// does not touch — and R10 and R12 both use `unless`-polarity gates, which
/// survive the condition filter.
#[test]
fn veteran_brawlers_badge_and_eligibility_follow_the_defenders_untapped_land() {
    for land_tapped in [false, true] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let brawlers = scenario
            .add_creature_from_oracle(P0, "Veteran Brawlers", 3, 3, VETERAN_BRAWLERS)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let land = scenario.add_basic_land(P1, ManaColor::Green);
        let mut runner = scenario.build();
        assert_type_line(&runner, land, &[CoreType::Land], &[], &["Forest"]);
        if land_tapped {
            tap(&mut runner, land);
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid,
            constraints,
            legal_targets: by_attacker,
        } = attackers_payload(&runner);

        assert!(
            valid.contains(&bear) && !constraints.contains_key(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be offered and \
             badge-free in both arms (land_tapped = {land_tapped}); got \
             valid={valid:?} constraints={constraints:?}"
        );
        assert_eq!(
            valid.contains(&brawlers),
            land_tapped,
            "CR 508.1a + CR 508.1c: the payload must stop offering Veteran \
             Brawlers once the defender has an UNTAPPED land \
             (land_tapped = {land_tapped}); got {valid:?}"
        );
        let badge = constraints.get(&brawlers);
        if land_tapped {
            assert!(
                badge.is_none(),
                "CR 508.1c: with the defender's only land tapped the gate is \
                 unmet and Veteran Brawlers carries no badge; got {badge:?}"
            );
            assert!(
                by_attacker.get(&brawlers).is_some_and(|t| !t.is_empty()),
                "CR 508.1b: Veteran Brawlers must have a selectable target; got {by_attacker:?}"
            );
        } else {
            assert!(
                matches!(
                    badge,
                    Some(CombatRequirement::CantAttack { sources }) if sources == &vec![brawlers]
                ),
                "CR 508.1c: with the defender holding an untapped land, Veteran \
                 Brawlers must carry a CantAttack badge whose only carrier is \
                 ITSELF. All three of (absent from valid, badged, sources = \
                 [self]) hold together or not at all — they are the pin on the \
                 `functioning_static_definitions` iterator; got {badge:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// R12 — the defending-player QUANTITY door is UNCHANGED, both polarities
// ---------------------------------------------------------------------------

/// This row asserts NO change. It is a pin, not a discriminator.
///
/// `StaticCondition::mentions_defending_player` — the routing predicate — is
/// deliberately BROADER than the anchor fix: it matches a `QuantityComparison`
/// scoped to `PlayerScope::DefendingPlayer` as well as the
/// `DefendingPlayerControls` leaf, because the honest answer to "does this tree
/// read the combat defender anchor?" is yes for both. The quantity door's own
/// anchor still resolves through `combat::defending_player_cr508_5`, which has
/// NO proposed-pairing axis and is untouched here, so routing those shapes
/// through the per-pairing door must be behaviour-preserving in both
/// polarities. This row proves it rather than leaving it to inference.
///
/// **Enumeration duty, discharged.** Every one of the 45 cards carrying
/// `ResolverFeature:static_condition:DefendingPlayerControls` was parsed and
/// dumped: all 45 produce a `DefendingPlayerControls` leaf and NONE produces a
/// `mentions_defending_player`-matching tree with any other leaf. The printed
/// quantity/predicate cards outside that population — Goblin Goon, Mogg Toady,
/// Monstrous Hound, Vantress Gargoyle, Chained Throatseeker, Crown-Hunter
/// Hireling — all lower to `Not { Unrecognized { .. } }` today, so the
/// predicate's extra breadth affects ZERO cards in the flip set. The bare and
/// negated quantity polarities are therefore pinned on a SYNTHESIZED condition
/// tree, labelled as such below, because no card in the corpus produces one.
#[test]
fn defending_player_quantity_gate_is_unchanged_by_the_pairing_route() {
    // --- Half 1: the real printed card, unchanged. -------------------------
    //
    // Goblin Goon's gate does not type: it lowers to `Not { Unrecognized }`.
    // `Unrecognized` evaluates TRUE, the `Not` negates it to FALSE, the CR 604.1
    // condition filter drops the definition, and the restriction applies on no
    // board. `mentions_defending_player` answers FALSE for that tree (the leaf
    // is `Unrecognized`, not a quantity), so the routing change cannot reach it
    // at all. Pinned so a future typing of that gate is a deliberate change
    // with its own test, not a silent side effect of this one.
    for defender_creatures in [0usize, 3] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let goon = scenario
            .add_creature_from_oracle(P0, "Goblin Goon", 6, 6, GOBLIN_GOON)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        for i in 0..defender_creatures {
            scenario.add_creature(P1, &format!("Defender Body {i}"), 1, 1);
        }
        let mut runner = scenario.build();

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid, constraints, ..
        } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be a valid attacker"
        );
        assert!(
            valid.contains(&goon) && !constraints.contains_key(&goon),
            "the defending-player QUANTITY door is unchanged by this work: \
             Goblin Goon's gate never types, so it carries no restriction and \
             no badge on either board (defender_creatures = \
             {defender_creatures}); got valid={valid:?} constraints={constraints:?}"
        );
        assert!(
            runner
                .declare_attackers(&[(goon, AttackTarget::Player(P1))])
                .is_ok(),
            "unchanged: Goblin Goon attacks freely on both boards \
             (defender_creatures = {defender_creatures})"
        );
    }

    // --- Half 2: the SYNTHESIZED quantity tree, both polarities. -----------
    //
    // `LifeTotal { player: DefendingPlayer }` is a `QuantityRef` carrying the
    // anaphor, so `mentions_defending_player` matches and the definition IS
    // routed to the per-pairing door. The quantity itself still resolves
    // through `defending_player_cr508_5`, which answers `None` on the attack
    // door, which `PlayerScope::DefendingPlayer`'s `map_or(0, ..)` renders as
    // zero — exactly as it did before the routing change.
    //
    //  * BARE `0 >= 1` is FALSE ⇒ the restriction never applies ⇒ legal attack,
    //    before and after.
    //  * NEGATED `Not { 0 >= 1 }` is TRUE ⇒ the restriction applies against
    //    every defender ⇒ illegal attack AND a `CantAttack` badge carried by
    //    the creature itself, before and after. That badge half is what pins
    //    the `else if` swap in `attacker_constraints_for_active_player`:
    //    without it, routing this definition off the blanket door would make
    //    the badge silently disappear.
    let quantity_gate = StaticCondition::QuantityComparison {
        lhs: QuantityExpr::Ref {
            qty: QuantityRef::LifeTotal {
                player: PlayerScope::DefendingPlayer,
            },
        },
        comparator: Comparator::GE,
        rhs: QuantityExpr::Fixed { value: 1 },
    };
    for negated in [false, true] {
        let condition = if negated {
            StaticCondition::Not {
                condition: Box::new(quantity_gate.clone()),
            }
        } else {
            quantity_gate.clone()
        };
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let gated = scenario
            .add_creature(P0, "Quantity Gated", 3, 3)
            .with_static_definition(
                StaticDefinition::new(StaticMode::CantAttack)
                    // CR 604.1 + CR 109.5: SelfRef, or an unscoped `affected`
                    // would restrict every creature on the battlefield and take
                    // the positive control down with it.
                    .affected(TargetFilter::SelfRef)
                    .condition(condition),
            )
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let mut runner = scenario.build();

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid, constraints, ..
        } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear) && !constraints.contains_key(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be offered and \
             badge-free (negated = {negated})"
        );
        assert_eq!(
            valid.contains(&gated),
            !negated,
            "the quantity door is unchanged: a BARE defending-player quantity \
             gate reads zero and never applies; the NEGATED form applies \
             against every defender (negated = {negated}); got {valid:?}"
        );
        let badge = constraints.get(&gated);
        assert_eq!(
            matches!(
                badge,
                Some(CombatRequirement::CantAttack { sources }) if sources == &vec![gated]
            ),
            negated,
            "CR 508.1c: the badge must survive the routing change for the \
             NEGATED form and must not appear for the bare one \
             (negated = {negated}); got {badge:?}"
        );
        assert_eq!(
            runner
                .declare_attackers(&[(gated, AttackTarget::Player(P1))])
                .is_ok(),
            !negated,
            "enforcement must agree with the badge (negated = {negated})"
        );
    }
}

// ---------------------------------------------------------------------------
// R13 / R14 — the carrier's ZONE-OF-FUNCTION and PHASING gates, through combat
// ---------------------------------------------------------------------------
//
// Why these rows exist, and why the unit tests they mirror are not enough.
//
// `combat::carries_defender_sensitive_local_cant_attack` — the routing
// predicate that feeds BOTH the prompt's `valid_attacker_ids` and its
// `attacker_constraints` badge — iterates
// `functioning_abilities::functioning_static_definitions`, which applies two
// gates and only two: the CR 702.26b phased-out early return, and the per-
// definition CR 113.6 / CR 113.6b `static_functions_in_zone` filter.
//
// `functioning_abilities`' own unit tests
// (`functioning_static_definitions_respects_active_zones`,
// `functioning_static_definitions_still_filters_phased_out`) call that private
// iterator DIRECTLY on a hand-built object. They cannot see the combat
// pipeline, so a regression that reached the same definitions by some other
// route — a caller swapped to `iter_unchecked`, a hoisted cache built without
// the gates — leaves them green while the prompt is wrong. R13 and R14 read the
// gates back out of the live `WaitingFor::DeclareAttackers` payload instead.
//
// WHAT THESE ROWS PIN, MEASURED RATHER THAN ASSUMED. They pin the payload's
// observable behaviour, NOT any single call site, and the difference was
// established by injecting the regressions:
//
//  * Bypassing `static_functions_in_zone` in the SHARED CR 113.6 authority
//    (both statics gathers) turns R13 red.
//  * Bypassing it in `functioning_static_definitions` ALONE leaves R13 green:
//    the per-pairing door (`attacker_can_attack_target` →
//    `static_abilities::check_static_ability` → `game_functioning_statics`)
//    re-applies the same gate, so a spurious `true` out of the routing
//    predicate is caught one step later and the payload is unchanged. The two
//    gates are redundant for every outcome combat can observe; the rows cannot
//    separate them and do not claim to.
//  * R14 is likewise redundantly protected — CR 702.26b is enforced at the
//    candidate sweep (`GameState::battlefield_phased_in_ids`), at both statics
//    gathers, and inside filter evaluation — so it is a behaviour pin, not a
//    one-line revert detector. It is NOT vacuous: leaving the carrier phased in
//    while the arm still expects a phased-out carrier makes the badge appear
//    and the row fail.
//
// These are NOT the false-condition row. R3/R10b already pin the case where the
// definition FUNCTIONS and its `condition` is false. Here the condition is TRUE
// in every arm (the defender's land is untapped throughout) and what varies is
// whether the CARRIER's state lets the definition function at all.

/// CR 113.6b + CR 508.1c. Veteran Brawlers' printed
/// `can't attack if defending player controls an untapped land` retuned to
/// declare `active_zones = [Graveyard]`, so the definition does not function
/// from the battlefield the carrier is standing on.
///
/// | carrier's definition | expected |
/// |---|---|
/// | graveyard-only (CR 113.6b) | offered, NO badge, declaration `Ok` |
/// | battlefield default (CR 113.6) — the positive control | not offered, `CantAttack` badge carried by itself, declaration `Err` |
///
/// The two arms are the same board, the same card and the same (satisfied)
/// gate; the ONLY difference is the definition's zone-of-function list, so a
/// combat pipeline that stops honouring CR 113.6b cannot keep both arms. Stop
/// the shared `functioning_abilities::static_functions_in_zone` authority from
/// gating and the off-zone arm goes red on its first assertion — the creature
/// stops being offered. (See the section banner: bypassing that gate in
/// `functioning_static_definitions` alone is masked by the per-pairing door,
/// which applies it again.)
///
/// FIXTURE PROPERTY F4: `make_cant_attack_graveyard_only` and the control arm
/// both assert the carrier really carries exactly one attack restriction first,
/// so "no badge" cannot mean "no definition".
#[test]
fn defender_gated_cant_attack_ignores_an_off_zone_carrier() {
    // (label, definition retuned off the battlefield?, attack legal?)
    for (label, off_zone, attack_legal) in [
        ("battlefield-default definition (control)", false, false),
        ("graveyard-only definition", true, true),
    ] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let brawlers = scenario
            .add_creature_from_oracle(P0, "Veteran Brawlers", 3, 3, VETERAN_BRAWLERS)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let land = scenario.add_basic_land(P1, ManaColor::Green);
        let mut runner = scenario.build();

        // FIXTURE PROPERTY F3 + the shared premise of both arms: the gate is
        // MET in each of them, so the arms differ only in zone-of-function.
        assert_type_line(&runner, land, &[CoreType::Land], &[], &["Forest"]);
        assert!(
            !runner.state().objects[&land].tapped,
            "both arms require the defender's land to be UNTAPPED, or the \
             condition is false and the row degenerates into R3 ({label})"
        );
        assert_carries_one_cant_attack_static(&runner, brawlers, label);
        if off_zone {
            make_cant_attack_graveyard_only(&mut runner, brawlers, label);
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid, constraints, ..
        } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear) && !constraints.contains_key(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be offered and \
             badge-free in both arms ({label}); got valid={valid:?} \
             constraints={constraints:?}"
        );
        assert_eq!(
            valid.contains(&brawlers),
            off_zone,
            "CR 113.6b + CR 508.1a: a restriction that functions only from the \
             GRAVEYARD does not restrict its battlefield carrier, so the prompt \
             must offer Veteran Brawlers exactly when the definition is off-zone \
             ({label}); got {valid:?}"
        );
        let badge = constraints.get(&brawlers);
        if off_zone {
            assert!(
                badge.is_none(),
                "CR 113.6b: an off-zone definition is not a functioning \
                 restriction, so no badge may be emitted for it ({label}); got \
                 {badge:?}"
            );
        } else {
            assert!(
                matches!(
                    badge,
                    Some(CombatRequirement::CantAttack { sources }) if sources == &vec![brawlers]
                ),
                "POSITIVE CONTROL (CR 508.1c): with the SAME card, the SAME \
                 satisfied gate and the definition left at the CR 113.6 \
                 battlefield default, the restriction DOES apply and Veteran \
                 Brawlers is badged with itself as carrier — without this the \
                 off-zone arm proves nothing ({label}); got {badge:?}"
            );
        }

        assert_declaration_with_control(
            &mut runner,
            brawlers,
            bear,
            AttackTarget::Player(P1),
            attack_legal,
            label,
        );
    }
}

/// CR 702.26b + CR 508.1c. The same card, the same satisfied gate, with the
/// CARRIER phased out.
///
/// CR 702.26b: "a phased-out permanent is treated as though it does not exist.
/// It can't affect or be affected by anything else in the game." So its
/// `CantAttack` must not be a functioning restriction, and the prompt must not
/// badge it as one.
///
/// | carrier | expected |
/// |---|---|
/// | phased out (CR 702.26b) | NO badge — the restriction does not apply |
/// | phased in — the positive control | `CantAttack` badge carried by itself, declaration `Err` |
///
/// SCOPE NOTE, so the row is not read as claiming more than it does: a
/// phased-out creature is never OFFERED either, but that is CR 702.26b acting
/// one step earlier — `combat::team_eligible_attacker_ids` draws its candidates
/// from `GameState::battlefield_phased_in_ids`, before any restriction
/// predicate runs. The unrestricted `ghost` bear is in the fixture precisely to
/// attribute that absence: it is phased out alongside Veteran Brawlers, carries
/// no restriction at all, and disappears from `valid_attacker_ids` too. The
/// BADGE is therefore the discriminating assertion here, and
/// `attacker_constraints_for_active_player` does reach a phased-out creature —
/// it iterates `state.battlefield`, which CR 702.26d keeps a phased-out
/// permanent in.
///
/// The badge assertion is what carries the row: leave the carrier phased IN
/// while the arm still expects a phased-out carrier and
/// `CantAttack { sources: [brawlers] }` appears where the row demands none. See
/// the section banner for what this does and does not detect — CR 702.26b is
/// enforced redundantly along this path, so the row pins the payload's
/// behaviour rather than any one gate's call site.
#[test]
fn defender_gated_cant_attack_ignores_a_phased_out_carrier() {
    for (label, phased_out) in [("phased in (control)", false), ("phased out", true)] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let brawlers = scenario
            .add_creature_from_oracle(P0, "Veteran Brawlers", 3, 3, VETERAN_BRAWLERS)
            .id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        // The attribution control: unrestricted, and phased out in lockstep
        // with the carrier.
        let ghost = scenario.add_creature(P0, "Ghostly Bear", 2, 2).id();
        let land = scenario.add_basic_land(P1, ManaColor::Green);
        let mut runner = scenario.build();

        assert_type_line(&runner, land, &[CoreType::Land], &[], &["Forest"]);
        assert!(
            !runner.state().objects[&land].tapped,
            "both arms require the defender's land to be UNTAPPED, so the gate \
             is satisfied and only the carrier's phase status varies ({label})"
        );
        assert_carries_one_cant_attack_static(&runner, brawlers, label);
        if phased_out {
            phase_carrier_out(&mut runner, brawlers, label);
            phase_carrier_out(&mut runner, ghost, label);
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid, constraints, ..
        } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear) && !constraints.contains_key(&bear),
            "FIXTURE PROPERTY F1: the phased-IN unrestricted bear must be \
             offered and badge-free in both arms ({label}); got valid={valid:?} \
             constraints={constraints:?}"
        );
        assert_eq!(
            valid.contains(&ghost),
            !phased_out,
            "CR 702.26b + CR 508.1a: the UNRESTRICTED ghost drops out of the \
             candidate set purely by phasing out, which is what attributes \
             Veteran Brawlers' own absence below to CR 702.26b rather than to \
             its restriction ({label}); got {valid:?}"
        );
        assert!(
            !constraints.contains_key(&ghost),
            "a creature with no attack restriction is never badged, phased out \
             or not ({label}); got {constraints:?}"
        );
        assert!(
            !valid.contains(&brawlers),
            "Veteran Brawlers is absent from the candidate set in BOTH arms — \
             restricted when phased in (CR 508.1c), nonexistent when phased out \
             (CR 702.26b) ({label}); got {valid:?}"
        );

        let badge = constraints.get(&brawlers);
        if phased_out {
            assert!(
                badge.is_none(),
                "CR 702.26b: a phased-out permanent's abilities do not \
                 function, so its `CantAttack` is not a functioning \
                 restriction and the payload must carry NO badge for it \
                 ({label}); got {badge:?}"
            );
        } else {
            assert!(
                matches!(
                    badge,
                    Some(CombatRequirement::CantAttack { sources }) if sources == &vec![brawlers]
                ),
                "POSITIVE CONTROL (CR 508.1c): phased IN, on the same board \
                 with the same satisfied gate, the restriction DOES apply and \
                 the badge IS emitted — without this the phased-out arm passes \
                 whether or not the engine honours CR 702.26b ({label}); got \
                 {badge:?}"
            );
        }

        // CR 508.1c: the declaration is refused in both arms (restricted, then
        // nonexistent), and FIXTURE PROPERTY F1's control proves the board
        // still admits an attack in each of them.
        assert_declaration_with_control(
            &mut runner,
            brawlers,
            bear,
            AttackTarget::Player(P1),
            false,
            label,
        );
    }
}

// ---------------------------------------------------------------------------
// R15 — a REMOTE carrier's zone and phasing, at the per-pairing door
// ---------------------------------------------------------------------------

/// CR 113.6 + CR 702.26b + CR 508.1c. The carrier is a DIFFERENT object from
/// the restricted creature, so the creature stays on the battlefield and
/// attacks (or fails to) while the carrier moves zone or phases out.
///
/// | carrier | expected declaration |
/// |---|---|
/// | on the battlefield, phased in — the positive control | `Err` |
/// | in the GRAVEYARD | `Ok` |
/// | on the battlefield, PHASED OUT | `Ok` |
///
/// The definition is SYNTHESIZED, and labelled as such at its construction site
/// below: `combat::carries_defender_sensitive_local_cant_attack` records that
/// every carrier in the printed `DefendingPlayerControls` population is
/// self-referential, so no Oracle text produces this shape. It is built here
/// because the per-pairing door (`attacker_can_attack_target` →
/// `static_abilities::check_static_ability` →
/// `functioning_abilities::game_functioning_statics`) is a SECOND, separately
/// implemented functioning gate, and that sweep's own CR 702.26b filter is
/// reached by no other row in this file: deleting it leaves R13 and R14 green
/// (measured) because the phased-out carrier they use is ALSO the restricted
/// creature, and CR 702.26b has already removed that creature from the
/// candidate set one step earlier.
///
/// The two suppressions are not the same gate: the graveyard arm is refused by
/// `game_functioning_statics`' battlefield+command-zone SCOPE (a graveyard
/// object is never swept, whatever its `active_zones` say), the phased-out arm
/// by that sweep's explicit CR 702.26b `is_phased_out` filter. Measured:
/// deleting that filter turns the phased-out arm red, and the graveyard arm is
/// correspondingly unaffected by a zone-gate regression — this is the only row
/// in the file that pins either of those two properties of the sweep.
///
/// DECLARED SCOPE CUT, asserted rather than assumed: a REMOTE defender-anchored
/// `CantAttack` is not recovered by the target-agnostic door, so the restricted
/// creature is OFFERED and BADGE-FREE in every arm including the control —
/// `combat::carries_defender_sensitive_local_cant_attack` documents this and
/// why it is taken. Only the declaration discriminates. If that cut is ever
/// closed, this row is the one that says so.
#[test]
fn remote_defender_gated_cant_attack_follows_its_carriers_zone_and_phasing() {
    // (label, carrier in the graveyard?, carrier phased out?, attack legal?)
    for (label, in_graveyard, phased_out, attack_legal) in [
        (
            "carrier on the battlefield, phased in (control)",
            false,
            false,
            false,
        ),
        ("carrier in the graveyard", true, false, true),
        ("carrier phased out", false, true, true),
    ] {
        let mut scenario = GameScenario::new();
        scenario.at_phase(Phase::PreCombatMain);
        let restricted = scenario.add_creature(P0, "Restrained Bear", 2, 2).id();
        let bear = scenario.add_creature(P0, "Grizzly Bears", 2, 2).id();
        let land = scenario.add_basic_land(P1, ManaColor::Green);
        // SYNTHESIZED (see the doc comment): a remote `CantAttack` scoped to one
        // creature, gated on the defending player controlling one specific
        // permanent. `SpecificObject` is used for both the affected filter and
        // the gate's filter so the row turns on the carrier's functioning state
        // alone and not on any filter-evaluation subtlety — the gate is TRUE in
        // every arm, because P1 controls that land in every arm.
        let remote_gate = StaticDefinition::new(StaticMode::CantAttack)
            .affected(TargetFilter::SpecificObject { id: restricted })
            .condition(StaticCondition::DefendingPlayerControls {
                filter: TargetFilter::SpecificObject { id: land },
            });
        let carrier = if in_graveyard {
            scenario
                .add_creature_to_graveyard(P0, "Watchful Sentry", 1, 1)
                .with_static_definition(remote_gate)
                .id()
        } else {
            scenario
                .add_creature(P0, "Watchful Sentry", 1, 1)
                .with_static_definition(remote_gate)
                .id()
        };
        let mut runner = scenario.build();

        assert_carries_one_cant_attack_static(&runner, carrier, label);
        assert_eq!(
            runner.state().objects[&carrier].zone,
            if in_graveyard {
                Zone::Graveyard
            } else {
                Zone::Battlefield
            },
            "the arm's premise is the carrier's ZONE, so assert it before \
             reading any legality outcome ({label})"
        );
        assert_eq!(
            runner.state().objects[&land].controller,
            P1,
            "the synthesized gate reads `defending player controls <land>`, so \
             the defending player must control it in every arm ({label})"
        );
        if phased_out {
            phase_carrier_out(&mut runner, carrier, label);
        }

        advance_to_declare_attackers(&mut runner);
        let AttackersPayload {
            valid, constraints, ..
        } = attackers_payload(&runner);
        assert!(
            valid.contains(&bear) && !constraints.contains_key(&bear),
            "FIXTURE PROPERTY F1: the unrestricted bear must be offered and \
             badge-free in every arm ({label}); got valid={valid:?} \
             constraints={constraints:?}"
        );
        assert!(
            valid.contains(&restricted) && !constraints.contains_key(&restricted),
            "DECLARED SCOPE CUT: a remote defender-anchored restriction is not \
             recovered by the target-agnostic door, so the creature is offered \
             and badge-free in EVERY arm and only the declaration below \
             discriminates ({label}); got valid={valid:?} \
             constraints={constraints:?}"
        );

        assert_declaration_with_control(
            &mut runner,
            restricted,
            bear,
            AttackTarget::Player(P1),
            attack_legal,
            label,
        );
    }
}

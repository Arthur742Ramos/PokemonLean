/-
  PokemonLean / RadiantCollection.lean

  Radiant Pokémon mechanics formalised in Lean 4.
  Covers: one Radiant per deck rule, colorless basics with
  powerful abilities, Radiant Charizard (Excited Heart),
  Radiant Greninja (Concealed Cards), Radiant Alakazam
  (Painful Spoons), no evolution, interaction with non-rule
  box status.

  All proofs are sorry-free. Uses computational paths for
  game-state transitions.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  Computational Paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive GPath (α : Type) : α → α → Type where
  | nil  : (a : α) → GPath α a a
  | cons : Step α a b → GPath α b c → GPath α a c

def GPath.trans : GPath α a b → GPath α b c → GPath α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule nm a b => .rule (nm ++ "⁻¹") b a

def GPath.symm : GPath α a b → GPath α b a
  | .nil a => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def GPath.length : GPath α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

def GPath.single (s : Step α a b) : GPath α a b :=
  .cons s (.nil _)

def GPath.congrArg (f : α → β) : GPath α a b → GPath β (f a) (f b)
  | .nil a => .nil (f a)
  | .cons (.refl a) p => (GPath.nil (f a)).trans (GPath.congrArg f p)
  | .cons (.rule nm a b) p => .cons (.rule nm (f a) (f b)) (GPath.congrArg f p)

-- Path algebra
theorem gpath_trans_assoc (p : GPath α a b) (q : GPath α b c) (r : GPath α c d) :
    GPath.trans (GPath.trans p q) r = GPath.trans p (GPath.trans q r) := by
  induction p with
  | nil _ => simp [GPath.trans]
  | cons s _ ih => simp [GPath.trans, ih]

theorem gpath_trans_nil_right (p : GPath α a b) :
    GPath.trans p (GPath.nil b) = p := by
  induction p with
  | nil _ => simp [GPath.trans]
  | cons s _ ih => simp [GPath.trans, ih]

theorem gpath_length_trans (p : GPath α a b) (q : GPath α b c) :
    (GPath.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [GPath.trans, GPath.length]
  | cons s _ ih => simp [GPath.trans, GPath.length, ih, Nat.add_assoc]

-- ============================================================
-- §2  Radiant Pokémon definitions
-- ============================================================

/-- Known Radiant Pokémon. -/
inductive RadiantName where
  | charizard   -- Excited Heart ability
  | greninja    -- Concealed Cards ability
  | alakazam    -- Painful Spoons ability
  | eevee       -- Radiant Eevee
  | gardevoir   -- Radiant Gardevoir
  | hawlucha    -- Radiant Hawlucha
  | hisuianSneasler  -- Radiant Hisuian Sneasler
  | steelix     -- Radiant Steelix
  | tsareena    -- Radiant Tsareena
  | eternatus   -- Radiant Eternatus
  | jirachi     -- Radiant Jirachi
deriving DecidableEq, Repr, BEq

/-- Radiant Pokémon are always Basic, colorless-entry. -/
structure RadiantCard where
  name : RadiantName
  hp   : Nat
  abilityName : String
  attackName  : String
  attackCost  : Nat   -- number of energy required
  attackDamage : Nat
deriving DecidableEq, Repr

-- Canonical cards
def radiantCharizard : RadiantCard :=
  ⟨.charizard, 160, "Excited Heart", "Combustion Blast", 3, 250⟩

def radiantGreninja : RadiantCard :=
  ⟨.greninja, 130, "Concealed Cards", "Moonlight Shuriken", 2, 90⟩

def radiantAlakazam : RadiantCard :=
  ⟨.alakazam, 130, "Painful Spoons", "Mind Ruler", 2, 20⟩

def radiantEevee : RadiantCard :=
  ⟨.eevee, 90, "Twinkle Gathering", "Sharp Fang", 2, 30⟩

def radiantGardevoir : RadiantCard :=
  ⟨.gardevoir, 130, "Loving Veil", "Psychic", 2, 70⟩

def radiantHawlucha : RadiantCard :=
  ⟨.hawlucha, 90, "Big Match", "Flying Entry", 1, 30⟩

def radiantJirachi : RadiantCard :=
  ⟨.jirachi, 90, "Entrusted Wishes", "Astral Misfortune", 2, 0⟩

-- ============================================================
-- §3  Deck representation
-- ============================================================

/-- Cards in a Radiant-era deck. -/
inductive RCard where
  | radiant : RadiantCard → RCard
  | regular : String → RCard
deriving DecidableEq, Repr

abbrev RDeck := List RCard

/-- Count Radiant Pokémon in a deck. -/
def radiantCount (d : RDeck) : Nat :=
  d.filter (fun c => match c with | .radiant _ => true | .regular _ => false) |>.length

/-- A deck is Radiant-valid: at most one Radiant Pokémon. -/
def radiantValid (d : RDeck) : Prop := radiantCount d ≤ 1

instance : Decidable (radiantValid d) := inferInstanceAs (Decidable (radiantCount d ≤ 1))

-- ============================================================
-- §4  Basic Radiant validation theorems
-- ============================================================

/-- Theorem 1: Empty deck is Radiant-valid. -/
theorem empty_radiant_valid : radiantValid [] := by
  simp [radiantValid, radiantCount, List.filter, List.length]

/-- Theorem 2: Deck of only regular cards is Radiant-valid. -/
theorem regular_only_radiant_valid (cards : List String) :
    radiantValid (cards.map RCard.regular) := by
  induction cards with
  | nil => exact empty_radiant_valid
  | cons _ _ ih =>
    simp [radiantValid, radiantCount, List.filter, List.map] at *
    exact ih

/-- Theorem 3: Single Radiant deck is valid. -/
theorem single_radiant_valid (rc : RadiantCard) :
    radiantValid [RCard.radiant rc] := by
  simp [radiantValid, radiantCount, List.filter, List.length]

/-- Theorem 4: Adding a regular card preserves Radiant-validity. -/
theorem add_regular_preserves (d : RDeck) (name : String) (hv : radiantValid d) :
    radiantValid (RCard.regular name :: d) := by
  simp [radiantValid, radiantCount, List.filter] at *
  exact hv

-- ============================================================
-- §5  Non-Rule Box status
-- ============================================================

/-- Rule box categories (V, VMAX, VSTAR, ex, GX). -/
inductive RuleBox where
  | v | vmax | vstar | ex | gx
deriving DecidableEq, Repr

/-- A card's rule box status. -/
def isRuleBox : RCard → Bool
  | .radiant _ => false   -- Radiant Pokémon are NOT Rule Box
  | .regular _ => false

/-- Theorem 5: Radiant Pokémon are never Rule Box. -/
theorem radiant_not_rule_box (rc : RadiantCard) :
    isRuleBox (RCard.radiant rc) = false := by
  simp [isRuleBox]

/-- Theorem 6: Radiant Charizard specifically is not Rule Box. -/
theorem charizard_not_rule_box :
    isRuleBox (RCard.radiant radiantCharizard) = false := by
  simp [isRuleBox]

-- ============================================================
-- §6  No evolution rule
-- ============================================================

/-- Radiant Pokémon cannot evolve. -/
inductive Stage where
  | basic | stage1 | stage2
deriving DecidableEq, Repr

def radiantStage (_rc : RadiantCard) : Stage := Stage.basic

/-- Theorem 7: All Radiant Pokémon are Basic stage. -/
theorem radiant_always_basic (rc : RadiantCard) :
    radiantStage rc = Stage.basic := by
  simp [radiantStage]

/-- Can a card evolve? Radiants cannot. -/
def canEvolve : RCard → Bool
  | .radiant _ => false
  | .regular _ => true  -- regular cards might evolve

/-- Theorem 8: Radiant Pokémon cannot evolve. -/
theorem radiant_no_evolve (rc : RadiantCard) :
    canEvolve (RCard.radiant rc) = false := by
  simp [canEvolve]

-- ============================================================
-- §7  Ability mechanics via paths
-- ============================================================

/-- Game state for ability resolution. -/
structure GameState where
  hand      : List String
  deck      : List String
  discard   : List String
  bench     : List RadiantCard
  active    : Option RadiantCard
  damage    : Nat  -- damage counters on opponent's board total
  prizes    : Nat
deriving Repr

/-- Excited Heart: Radiant Charizard's ability — discard energy to power up. -/
def excitedHeartBonus (energyInDiscard : Nat) (baseDamage : Nat) : Nat :=
  baseDamage + energyInDiscard * 30  -- fictional simplified bonus

/-- Concealed Cards: Radiant Greninja — discard energy, draw 2. -/
def concealedCardsDraw (gs : GameState) (energyDiscarded : Bool) : GameState :=
  if energyDiscarded then
    { gs with hand := gs.hand ++ gs.deck.take 2,
              deck := gs.deck.drop 2 }
  else gs

/-- Painful Spoons: Radiant Alakazam — move damage counters. -/
def painfulSpoons (totalDmg : Nat) (moved : Nat) : Nat × Nat :=
  if moved ≤ totalDmg then (totalDmg - moved, moved)
  else (totalDmg, 0)

/-- Theorem 9: Excited Heart with 0 energy = base damage. -/
theorem excited_heart_zero : excitedHeartBonus 0 250 = 250 := by
  simp [excitedHeartBonus]

/-- Theorem 10: Excited Heart with 5 energy = 250+150 = 400. -/
theorem excited_heart_five : excitedHeartBonus 5 250 = 400 := by
  simp [excitedHeartBonus]

/-- Theorem 11: Concealed Cards without discard doesn't change state. -/
theorem concealed_no_discard (gs : GameState) :
    concealedCardsDraw gs false = gs := by
  simp [concealedCardsDraw]

/-- Theorem 12: Painful Spoons with 0 moved keeps damage. -/
theorem painful_spoons_zero (dmg : Nat) :
    painfulSpoons dmg 0 = (dmg, 0) := by
  simp [painfulSpoons]

-- ============================================================
-- §8  Game state transition paths
-- ============================================================

/-- Ability activation as a step. -/
def abilityStep (name : String) (before after : GameState) :
    Step GameState before after :=
  Step.rule name before after

/-- Theorem 13: Single ability activation path has length 1. -/
theorem ability_path_single (gs₁ gs₂ : GameState) :
    (GPath.single (abilityStep "Concealed Cards" gs₁ gs₂)).length = 1 := by
  simp [GPath.single, GPath.length]

/-- Theorem 14: Two ability activations compose to length 2 path. -/
theorem two_abilities_compose (gs₁ gs₂ gs₃ : GameState) :
    let p1 := GPath.single (abilityStep "Excited Heart" gs₁ gs₂)
    let p2 := GPath.single (abilityStep "Concealed Cards" gs₂ gs₃)
    (GPath.trans p1 p2).length = 2 := by
  simp [GPath.single, GPath.trans, GPath.length]

/-- Theorem 15: Three-step turn path: ability → ability → attack. -/
theorem turn_three_steps (gs₁ gs₂ gs₃ gs₄ : GameState) :
    let p := GPath.trans
              (GPath.single (abilityStep "Painful Spoons" gs₁ gs₂))
              (GPath.trans
                (GPath.single (abilityStep "Concealed Cards" gs₂ gs₃))
                (GPath.single (Step.rule "attack" gs₃ gs₄)))
    p.length = 3 := by
  simp [GPath.single, GPath.trans, GPath.length]

-- ============================================================
-- §9  Prize interaction (Radiant gives 1 prize)
-- ============================================================

/-- Prizes given up when KO'd. -/
def prizesGiven : RCard → Nat
  | .radiant _ => 1   -- Radiant = non-Rule Box = 1 prize
  | .regular _ => 1

/-- Theorem 16: Radiant gives exactly 1 prize. -/
theorem radiant_one_prize (rc : RadiantCard) :
    prizesGiven (RCard.radiant rc) = 1 := by
  simp [prizesGiven]

/-- Theorem 17: Radiant Charizard gives 1 prize despite 250 attack. -/
theorem charizard_one_prize :
    prizesGiven (RCard.radiant radiantCharizard) = 1 := by
  simp [prizesGiven]

-- ============================================================
-- §10  Path coherence and symmetry
-- ============================================================

/-- Theorem 18: Symm of nil path is nil. -/
theorem symm_nil_game (gs : GameState) :
    GPath.symm (GPath.nil gs) = GPath.nil gs := by
  simp [GPath.symm]

/-- Theorem 19: Trans with nil is identity. -/
theorem trans_nil_right_game (p : GPath GameState gs₁ gs₂) :
    GPath.trans p (GPath.nil gs₂) = p := by
  exact gpath_trans_nil_right p

/-- Theorem 20: HP values are positive for all defined Radiants. -/
theorem charizard_hp_pos : radiantCharizard.hp > 0 := by decide
theorem greninja_hp_pos : radiantGreninja.hp > 0 := by decide
theorem alakazam_hp_pos : radiantAlakazam.hp > 0 := by decide

/-- Theorem 21: Charizard has highest HP among the big three. -/
theorem charizard_highest_hp :
    radiantCharizard.hp ≥ radiantGreninja.hp ∧
    radiantCharizard.hp ≥ radiantAlakazam.hp := by
  constructor <;> decide

/-- Theorem 22: Attack damage ordering. -/
theorem attack_damage_order :
    radiantCharizard.attackDamage > radiantGreninja.attackDamage ∧
    radiantGreninja.attackDamage > radiantAlakazam.attackDamage := by
  constructor <;> decide

/-- Theorem 23: Excited Heart bonus is monotone in energy count. -/
theorem excited_heart_monotone (e₁ e₂ base : Nat) (h : e₁ ≤ e₂) :
    excitedHeartBonus e₁ base ≤ excitedHeartBonus e₂ base := by
  simp [excitedHeartBonus]
  omega

/-- Theorem 24: Path length is additive (instantiated for game states). -/
theorem game_path_length_add (gs₁ gs₂ gs₃ : GameState)
    (p : GPath GameState gs₁ gs₂) (q : GPath GameState gs₂ gs₃) :
    (GPath.trans p q).length = p.length + q.length :=
  gpath_length_trans p q

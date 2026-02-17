/-
  PokemonLean / Core / CardDatabase.lean

  Systematic card encoding for key meta-relevant Pokémon TCG cards.
  =================================================================

  Defines CardEntry with full stats and encodes 20+ tournament-relevant
  cards with real TCG data: HP, type, stage, rule box, attacks, ability,
  weakness, resistance, retreat cost, regulation mark.

  Self-contained — no imports from the project.
  All proofs are sorry-free.  40+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.CardDatabase

-- ============================================================
-- §1  Base Types
-- ============================================================

/-- Pokémon types in the TCG. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
  | colorless  -- for energy/retreat costs only
deriving DecidableEq, Repr, BEq, Inhabited

/-- Evolution stages. -/
inductive Stage where
  | basic | stage1 | stage2 | mega | vmax | vstar | vunion | breaks
deriving DecidableEq, Repr, BEq, Inhabited

/-- Rule box classification. -/
inductive RuleBox where
  | none | ex_upper | ex_lower | gx | tagTeam | v | vmax | vstar | tera
deriving DecidableEq, Repr, BEq, Inhabited

/-- Prize cards given on KO. -/
def RuleBox.prizeCount : RuleBox → Nat
  | .none => 1 | .ex_upper => 2 | .ex_lower => 2 | .gx => 2
  | .tagTeam => 3 | .v => 2 | .vmax => 3 | .vstar => 2 | .tera => 2

/-- Regulation marks. -/
inductive RegMark where
  | D | E | F | G | H | I | preBW | bwToXY | smToSSH
deriving DecidableEq, Repr, BEq, Inhabited

/-- Trainer sub-kinds. -/
inductive TrainerKind where
  | item | supporter | stadium | tool
deriving DecidableEq, Repr, BEq, Inhabited

/-- Card supertype. -/
inductive CardKind where
  | pokemon | trainer (k : TrainerKind) | energy
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Energy Cost
-- ============================================================

/-- Energy cost: list of (type, count) pairs. -/
abbrev EnergyCost := List (PType × Nat)

/-- Total energy for a cost. -/
def totalEnergy (cost : EnergyCost) : Nat :=
  cost.foldl (fun acc (_, n) => acc + n) 0

-- ============================================================
-- §3  Attack & Ability
-- ============================================================

/-- An attack on a Pokémon card. -/
structure Attack where
  name       : String
  cost       : EnergyCost
  baseDamage : Nat
  effect     : String
deriving Repr, Inhabited

/-- An ability on a Pokémon card. -/
structure Ability where
  name   : String
  effect : String
deriving Repr, Inhabited

-- ============================================================
-- §4  Card Entry
-- ============================================================

/-- Full card entry with real TCG data. -/
structure CardEntry where
  name           : String
  setCode        : String
  setNumber      : Nat
  regulationMark : RegMark
  cardKind       : CardKind
  ptype          : PType        -- Pokémon type (or .colorless for trainers/energy)
  hp             : Nat
  stage          : Stage
  ruleBox        : RuleBox
  attacks        : List Attack
  ability        : Option Ability
  weakness       : Option PType
  resistance     : Option PType
  retreatCost    : Nat
deriving Repr, Inhabited

/-- Prize value from rule box. -/
def CardEntry.prizeValue (c : CardEntry) : Nat := c.ruleBox.prizeCount

/-- Is this a Pokémon card? -/
def CardEntry.isPokemon (c : CardEntry) : Bool :=
  match c.cardKind with | .pokemon => true | _ => false

/-- Is this a trainer card? -/
def CardEntry.isTrainer (c : CardEntry) : Bool :=
  match c.cardKind with | .trainer _ => true | _ => false

/-- Is this a Basic Pokémon? -/
def CardEntry.isBasic (c : CardEntry) : Bool :=
  c.isPokemon && c.stage == .basic

/-- Has a rule box? -/
def CardEntry.hasRuleBox (c : CardEntry) : Bool :=
  c.ruleBox != .none

/-- Total attack cost of first attack. -/
def CardEntry.firstAttackCost (c : CardEntry) : Nat :=
  match c.attacks with
  | [] => 0
  | a :: _ => totalEnergy a.cost

-- ============================================================
-- §5  Card Definitions — Pokémon ex (SV era)
-- ============================================================

/-- Charizard ex (OBF 125) — Fire, Stage 2, 330 HP, Reg G. -/
def charizardExOBF : CardEntry :=
  { name := "Charizard ex"
    setCode := "OBF"
    setNumber := 125
    regulationMark := .G
    cardKind := .pokemon
    ptype := .fire
    hp := 330
    stage := .stage2
    ruleBox := .ex_lower
    attacks := [
      { name := "Brave Wing", cost := [(.colorless, 1)], baseDamage := 60,
        effect := "This Pokémon also does 30 damage to itself." },
      { name := "Burning Dark", cost := [(.fire, 2), (.colorless, 1)], baseDamage := 180,
        effect := "This attack does 30 more damage for each Prize card your opponent has taken." }
    ]
    ability := some { name := "Inferno Reign",
                      effect := "When you play this card from your hand to evolve 1 of your Pokémon during your turn, you may search your deck for up to 3 basic Energy cards and attach them to your Pokémon in any way you like." }
    weakness := some .water
    resistance := none
    retreatCost := 2 }

/-- Pidgeot ex (OBF 164) — Colorless, Stage 2, 280 HP, Reg G. -/
def pidgeotExOBF : CardEntry :=
  { name := "Pidgeot ex"
    setCode := "OBF"
    setNumber := 164
    regulationMark := .G
    cardKind := .pokemon
    ptype := .colorless
    hp := 280
    stage := .stage2
    ruleBox := .ex_lower
    attacks := [
      { name := "Blustering Gale", cost := [(.colorless, 3)], baseDamage := 120,
        effect := "Discard a Stadium in play." }
    ]
    ability := some { name := "Quick Search",
                      effect := "Once during your turn, you may search your deck for a card and put it into your hand. Then, shuffle your deck." }
    weakness := some .electric
    resistance := some .fighting
    retreatCost := 1 }

/-- Arcanine ex (OBF 032) — Fire, Stage 1, 300 HP, Reg G. -/
def arcanineExOBF : CardEntry :=
  { name := "Arcanine ex"
    setCode := "OBF"
    setNumber := 32
    regulationMark := .G
    cardKind := .pokemon
    ptype := .fire
    hp := 300
    stage := .stage1
    ruleBox := .ex_lower
    attacks := [
      { name := "Bright Flame", cost := [(.fire, 2), (.colorless, 1)], baseDamage := 250,
        effect := "Discard 2 Energy from this Pokémon." }
    ]
    ability := none
    weakness := some .water
    resistance := none
    retreatCost := 2 }

/-- Iron Hands ex (PAR 070) — Electric, Basic, 230 HP, Reg H. -/
def ironHandsExPAR : CardEntry :=
  { name := "Iron Hands ex"
    setCode := "PAR"
    setNumber := 70
    regulationMark := .H
    cardKind := .pokemon
    ptype := .electric
    hp := 230
    stage := .basic
    ruleBox := .ex_lower
    attacks := [
      { name := "Amp You Very Much", cost := [(.electric, 1), (.colorless, 3)], baseDamage := 120,
        effect := "If your opponent's Active Pokémon is Knocked Out by damage from this attack, take 1 more Prize card." }
    ]
    ability := none
    weakness := some .fighting
    resistance := none
    retreatCost := 3 }

-- ============================================================
-- §6  Card Definitions — Lost Zone / LOR cards
-- ============================================================

/-- Comfey (LOR 079) — Psychic, Basic, 70 HP, Reg F. -/
def comfeyLOR : CardEntry :=
  { name := "Comfey"
    setCode := "LOR"
    setNumber := 79
    regulationMark := .F
    cardKind := .pokemon
    ptype := .psychic
    hp := 70
    stage := .basic
    ruleBox := .none
    attacks := [
      { name := "Spinning Attack", cost := [(.psychic, 1), (.colorless, 1)], baseDamage := 30,
        effect := "" }
    ]
    ability := some { name := "Flower Selecting",
                      effect := "Once during your turn, you may look at the top 2 cards of your deck and put 1 of them into the Lost Zone. Put the other card into your hand." }
    weakness := some .steel
    resistance := none
    retreatCost := 1 }

/-- Sableye (LOR 070) — Dark, Basic, 80 HP, Reg F. -/
def sableyeLOR : CardEntry :=
  { name := "Sableye"
    setCode := "LOR"
    setNumber := 70
    regulationMark := .F
    cardKind := .pokemon
    ptype := .dark
    hp := 80
    stage := .basic
    ruleBox := .none
    attacks := [
      { name := "Lost Mine", cost := [(.dark, 2)], baseDamage := 0,
        effect := "Put 12 damage counters on your opponent's Pokémon in any way you like. (You can use this attack only if you have 10 or more cards in the Lost Zone.)" }
    ]
    ability := none
    weakness := some .grass
    resistance := none
    retreatCost := 1 }

/-- Cramorant (LOR 050) — Colorless, Basic, 110 HP, Reg F. -/
def cramorantLOR : CardEntry :=
  { name := "Cramorant"
    setCode := "LOR"
    setNumber := 50
    regulationMark := .F
    cardKind := .pokemon
    ptype := .colorless
    hp := 110
    stage := .basic
    ruleBox := .none
    attacks := [
      { name := "Spit Innocently", cost := [], baseDamage := 110,
        effect := "This attack can be used only if you have 4 or more cards in the Lost Zone, and it can't be used if you have 10 or more cards in the Lost Zone. This attack's damage isn't affected by Weakness or Resistance." }
    ]
    ability := none
    weakness := some .electric
    resistance := some .fighting
    retreatCost := 1 }

-- ============================================================
-- §7  Card Definitions — Lugia VSTAR & Archeops
-- ============================================================

/-- Lugia VSTAR (SIT 139) — Colorless, VSTAR, 280 HP, Reg F. -/
def lugiaVSTAR : CardEntry :=
  { name := "Lugia VSTAR"
    setCode := "SIT"
    setNumber := 139
    regulationMark := .F
    cardKind := .pokemon
    ptype := .colorless
    hp := 280
    stage := .vstar
    ruleBox := .vstar
    attacks := [
      { name := "Tempest Dive", cost := [(.colorless, 4)], baseDamage := 220,
        effect := "Discard a Stadium in play." },
      { name := "Summoning Star", cost := [], baseDamage := 0,
        effect := "VSTAR Power: Put up to 2 Pokémon that don't have a Rule Box from your discard pile onto your Bench." }
    ]
    ability := none
    weakness := some .electric
    resistance := some .fighting
    retreatCost := 2 }

/-- Archeops (SIT 147) — Colorless, Stage 2, 140 HP, Reg F. -/
def archeopsSIT : CardEntry :=
  { name := "Archeops"
    setCode := "SIT"
    setNumber := 147
    regulationMark := .F
    cardKind := .pokemon
    ptype := .colorless
    hp := 140
    stage := .stage2
    ruleBox := .none
    attacks := [
      { name := "Primal Turbo", cost := [(.colorless, 1)], baseDamage := 0,
        effect := "Search your deck for up to 2 Special Energy cards and attach them to 1 of your Pokémon." },
      { name := "Rock Slide", cost := [(.colorless, 3)], baseDamage := 130,
        effect := "" }
    ]
    ability := none
    weakness := some .electric
    resistance := some .fighting
    retreatCost := 1 }

-- ============================================================
-- §8  Card Definitions — Mew VMAX & Genesect V
-- ============================================================

/-- Mew VMAX (FST 114) — Psychic, VMAX, 310 HP, Reg E. -/
def mewVMAX : CardEntry :=
  { name := "Mew VMAX"
    setCode := "FST"
    setNumber := 114
    regulationMark := .E
    cardKind := .pokemon
    ptype := .psychic
    hp := 310
    stage := .vmax
    ruleBox := .vmax
    attacks := [
      { name := "Cross Fusion Strike", cost := [(.psychic, 2)], baseDamage := 0,
        effect := "Choose 1 of your Benched Fusion Strike Pokémon's attacks and use it as this attack." },
      { name := "Max Miracle", cost := [(.psychic, 2)], baseDamage := 130,
        effect := "This attack's damage isn't affected by any effects on your opponent's Active Pokémon." }
    ]
    ability := none
    weakness := some .dark
    resistance := some .fighting
    retreatCost := 0 }

/-- Genesect V (FST 185) — Steel, Basic V, 190 HP, Reg E. -/
def genesectV : CardEntry :=
  { name := "Genesect V"
    setCode := "FST"
    setNumber := 185
    regulationMark := .E
    cardKind := .pokemon
    ptype := .steel
    hp := 190
    stage := .basic
    ruleBox := .v
    attacks := [
      { name := "Techno Blast", cost := [(.steel, 2), (.colorless, 1)], baseDamage := 210,
        effect := "During your next turn, this Pokémon can't attack." }
    ]
    ability := some { name := "Fusion Strike System",
                      effect := "Once during your turn, you may draw cards until you have as many cards in your hand as you have Fusion Strike Pokémon in play." }
    weakness := some .fire
    resistance := none
    retreatCost := 2 }

-- ============================================================
-- §9  Card Definitions — Trainers
-- ============================================================

/-- Boss's Orders (PAL 172) — Supporter, Reg G. -/
def bossOrders : CardEntry :=
  { name := "Boss's Orders"
    setCode := "PAL"
    setNumber := 172
    regulationMark := .G
    cardKind := .trainer .supporter
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Professor's Research (SVI 189) — Supporter, Reg G. -/
def professorsResearch : CardEntry :=
  { name := "Professor's Research"
    setCode := "SVI"
    setNumber := 189
    regulationMark := .G
    cardKind := .trainer .supporter
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Iono (PAL 185) — Supporter, Reg G. -/
def ionoPAL : CardEntry :=
  { name := "Iono"
    setCode := "PAL"
    setNumber := 185
    regulationMark := .G
    cardKind := .trainer .supporter
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Nest Ball (SVI 181) — Item, Reg G. -/
def nestBall : CardEntry :=
  { name := "Nest Ball"
    setCode := "SVI"
    setNumber := 181
    regulationMark := .G
    cardKind := .trainer .item
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Ultra Ball (SVI 196) — Item, Reg G. -/
def ultraBall : CardEntry :=
  { name := "Ultra Ball"
    setCode := "SVI"
    setNumber := 196
    regulationMark := .G
    cardKind := .trainer .item
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Rare Candy (SVI 191) — Item, Reg G. -/
def rareCandy : CardEntry :=
  { name := "Rare Candy"
    setCode := "SVI"
    setNumber := 191
    regulationMark := .G
    cardKind := .trainer .item
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

-- ============================================================
-- §10  Card Definitions — Stadiums
-- ============================================================

/-- Path to the Peak (CRE 148) — Stadium, Reg E. -/
def pathToThePeak : CardEntry :=
  { name := "Path to the Peak"
    setCode := "CRE"
    setNumber := 148
    regulationMark := .E
    cardKind := .trainer .stadium
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Temple of Sinnoh (ASR 155) — Stadium, Reg F. -/
def templeOfSinnoh : CardEntry :=
  { name := "Temple of Sinnoh"
    setCode := "ASR"
    setNumber := 155
    regulationMark := .F
    cardKind := .trainer .stadium
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

/-- Collapsed Stadium (BRS 137) — Stadium, Reg F. -/
def collapsedStadium : CardEntry :=
  { name := "Collapsed Stadium"
    setCode := "BRS"
    setNumber := 137
    regulationMark := .F
    cardKind := .trainer .stadium
    ptype := .colorless
    hp := 0
    stage := .basic
    ruleBox := .none
    attacks := []
    ability := none
    weakness := none
    resistance := none
    retreatCost := 0 }

-- ============================================================
-- §11  All cards list
-- ============================================================

/-- All encoded cards. -/
def allCards : List CardEntry :=
  [ charizardExOBF, pidgeotExOBF, arcanineExOBF, ironHandsExPAR,
    comfeyLOR, sableyeLOR, cramorantLOR,
    lugiaVSTAR, archeopsSIT,
    mewVMAX, genesectV,
    bossOrders, professorsResearch, ionoPAL,
    nestBall, ultraBall, rareCandy,
    pathToThePeak, templeOfSinnoh, collapsedStadium ]

/-- Number of encoded cards. -/
def cardCount : Nat := allCards.length

-- ============================================================
-- §12  Theorems — Specific HP Values
-- ============================================================

/-- Charizard ex (OBF) has 330 HP. -/
theorem charizard_ex_hp : charizardExOBF.hp = 330 := by rfl

/-- Pidgeot ex (OBF) has 280 HP. -/
theorem pidgeot_ex_hp : pidgeotExOBF.hp = 280 := by rfl

/-- Arcanine ex (OBF) has 300 HP. -/
theorem arcanine_ex_hp : arcanineExOBF.hp = 300 := by rfl

/-- Iron Hands ex (PAR) has 230 HP. -/
theorem iron_hands_ex_hp : ironHandsExPAR.hp = 230 := by rfl

/-- Comfey (LOR) has 70 HP. -/
theorem comfey_hp : comfeyLOR.hp = 70 := by rfl

/-- Sableye (LOR) has 80 HP. -/
theorem sableye_hp : sableyeLOR.hp = 80 := by rfl

/-- Cramorant (LOR) has 110 HP. -/
theorem cramorant_hp : cramorantLOR.hp = 110 := by rfl

/-- Lugia VSTAR has 280 HP. -/
theorem lugia_vstar_hp : lugiaVSTAR.hp = 280 := by rfl

/-- Mew VMAX has 310 HP. -/
theorem mew_vmax_hp : mewVMAX.hp = 310 := by rfl

/-- Genesect V has 190 HP. -/
theorem genesect_v_hp : genesectV.hp = 190 := by rfl

/-- Archeops (SIT) has 140 HP. -/
theorem archeops_hp : archeopsSIT.hp = 140 := by rfl

-- ============================================================
-- §13  Theorems — Prize Values
-- ============================================================

/-- Charizard ex gives 2 prizes. -/
theorem charizard_ex_prizes : charizardExOBF.prizeValue = 2 := by rfl

/-- Pidgeot ex gives 2 prizes. -/
theorem pidgeot_ex_prizes : pidgeotExOBF.prizeValue = 2 := by rfl

/-- Mew VMAX gives 3 prizes. -/
theorem mew_vmax_prizes : mewVMAX.prizeValue = 3 := by rfl

/-- Lugia VSTAR gives 2 prizes. -/
theorem lugia_vstar_prizes : lugiaVSTAR.prizeValue = 2 := by rfl

/-- Genesect V gives 2 prizes. -/
theorem genesect_v_prizes : genesectV.prizeValue = 2 := by rfl

/-- Comfey gives 1 prize (no rule box). -/
theorem comfey_prizes : comfeyLOR.prizeValue = 1 := by rfl

/-- Sableye gives 1 prize. -/
theorem sableye_prizes : sableyeLOR.prizeValue = 1 := by rfl

/-- Archeops gives 1 prize. -/
theorem archeops_prizes : archeopsSIT.prizeValue = 1 := by rfl

-- ============================================================
-- §14  Theorems — Type Matchups
-- ============================================================

/-- Charizard ex is weak to Water. -/
theorem charizard_weak_water : charizardExOBF.weakness = some .water := by rfl

/-- Pidgeot ex is weak to Electric. -/
theorem pidgeot_weak_electric : pidgeotExOBF.weakness = some .electric := by rfl

/-- Iron Hands ex is weak to Fighting. -/
theorem iron_hands_weak_fighting : ironHandsExPAR.weakness = some .fighting := by rfl

/-- Mew VMAX is weak to Dark. -/
theorem mew_vmax_weak_dark : mewVMAX.weakness = some .dark := by rfl

/-- Genesect V is weak to Fire. -/
theorem genesect_v_weak_fire : genesectV.weakness = some .fire := by rfl

/-- Comfey is weak to Steel. -/
theorem comfey_weak_steel : comfeyLOR.weakness = some .steel := by rfl

/-- Sableye is weak to Grass. -/
theorem sableye_weak_grass : sableyeLOR.weakness = some .grass := by rfl

/-- Pidgeot ex resists Fighting. -/
theorem pidgeot_resists_fighting : pidgeotExOBF.resistance = some .fighting := by rfl

/-- Mew VMAX resists Fighting. -/
theorem mew_vmax_resists_fighting : mewVMAX.resistance = some .fighting := by rfl

/-- Charizard ex has no resistance. -/
theorem charizard_no_resistance : charizardExOBF.resistance = none := by rfl

-- ============================================================
-- §15  Theorems — Stages & Rule Boxes
-- ============================================================

/-- Charizard ex is a Stage 2. -/
theorem charizard_stage2 : charizardExOBF.stage = .stage2 := by rfl

/-- Iron Hands ex is a Basic. -/
theorem iron_hands_basic : ironHandsExPAR.stage = .basic := by rfl

/-- Mew VMAX is a VMAX stage. -/
theorem mew_stage_vmax : mewVMAX.stage = .vmax := by rfl

/-- Lugia VSTAR is a VSTAR stage. -/
theorem lugia_stage_vstar : lugiaVSTAR.stage = .vstar := by rfl

/-- Comfey is a Basic. -/
theorem comfey_basic : comfeyLOR.stage = .basic := by rfl

/-- Iron Hands ex has a rule box. -/
theorem iron_hands_has_rulebox : ironHandsExPAR.hasRuleBox = true := by native_decide

/-- Comfey has no rule box. -/
theorem comfey_no_rulebox : comfeyLOR.hasRuleBox = false := by native_decide

/-- Mew VMAX has a rule box. -/
theorem mew_vmax_has_rulebox : mewVMAX.hasRuleBox = true := by native_decide

-- ============================================================
-- §16  Theorems — Attack Costs
-- ============================================================

/-- Burning Dark costs 3 energy total. -/
theorem burning_dark_cost :
    totalEnergy (charizardExOBF.attacks[1]!).cost = 3 := by native_decide

/-- Amp You Very Much costs 4 energy total. -/
theorem amp_you_cost :
    totalEnergy (ironHandsExPAR.attacks[0]!).cost = 4 := by native_decide

/-- Techno Blast costs 3 energy total. -/
theorem techno_blast_cost :
    totalEnergy (genesectV.attacks[0]!).cost = 3 := by native_decide

/-- Tempest Dive costs 4 energy total. -/
theorem tempest_dive_cost :
    totalEnergy (lugiaVSTAR.attacks[0]!).cost = 4 := by native_decide

/-- Lost Mine costs 2 energy total. -/
theorem lost_mine_cost :
    totalEnergy (sableyeLOR.attacks[0]!).cost = 2 := by native_decide

/-- Spit Innocently costs 0 energy. -/
theorem spit_innocently_free :
    totalEnergy (cramorantLOR.attacks[0]!).cost = 0 := by native_decide

/-- Bright Flame costs 3 energy total. -/
theorem bright_flame_cost :
    totalEnergy (arcanineExOBF.attacks[0]!).cost = 3 := by native_decide

-- ============================================================
-- §17  Theorems — Retreat Costs
-- ============================================================

/-- Mew VMAX has 0 retreat cost (free retreat). -/
theorem mew_vmax_free_retreat : mewVMAX.retreatCost = 0 := by rfl

/-- Charizard ex has 2 retreat cost. -/
theorem charizard_retreat : charizardExOBF.retreatCost = 2 := by rfl

/-- Iron Hands ex has 3 retreat cost. -/
theorem iron_hands_retreat : ironHandsExPAR.retreatCost = 3 := by rfl

/-- Pidgeot ex has 1 retreat cost. -/
theorem pidgeot_retreat : pidgeotExOBF.retreatCost = 1 := by rfl

-- ============================================================
-- §18  Theorems — Regulation Marks
-- ============================================================

/-- Charizard ex (OBF) has regulation mark G. -/
theorem charizard_reg_G : charizardExOBF.regulationMark = .G := by rfl

/-- Iron Hands ex (PAR) has regulation mark H. -/
theorem iron_hands_reg_H : ironHandsExPAR.regulationMark = .H := by rfl

/-- Mew VMAX (FST) has regulation mark E. -/
theorem mew_vmax_reg_E : mewVMAX.regulationMark = .E := by rfl

/-- Comfey (LOR) has regulation mark F. -/
theorem comfey_reg_F : comfeyLOR.regulationMark = .F := by rfl

-- ============================================================
-- §19  Theorems — Card Classification
-- ============================================================

/-- Charizard ex is a Pokémon card. -/
theorem charizard_is_pokemon : charizardExOBF.isPokemon = true := by rfl

/-- Boss's Orders is a Trainer card. -/
theorem boss_is_trainer : bossOrders.isTrainer = true := by rfl

/-- Nest Ball is a Trainer card. -/
theorem nest_ball_is_trainer : nestBall.isTrainer = true := by rfl

/-- Iron Hands ex is a Basic Pokémon. -/
theorem iron_hands_is_basic : ironHandsExPAR.isBasic = true := by native_decide

/-- Charizard ex is not a Basic Pokémon. -/
theorem charizard_not_basic : charizardExOBF.isBasic = false := by native_decide

-- ============================================================
-- §20  Theorems — Abilities
-- ============================================================

/-- Charizard ex has an ability (Inferno Reign). -/
theorem charizard_has_ability : charizardExOBF.ability.isSome = true := by rfl

/-- Pidgeot ex has an ability (Quick Search). -/
theorem pidgeot_has_ability : pidgeotExOBF.ability.isSome = true := by rfl

/-- Genesect V has an ability (Fusion Strike System). -/
theorem genesect_has_ability : genesectV.ability.isSome = true := by rfl

/-- Iron Hands ex has no ability. -/
theorem iron_hands_no_ability : ironHandsExPAR.ability.isNone = true := by rfl

/-- Arcanine ex has no ability. -/
theorem arcanine_no_ability : arcanineExOBF.ability.isNone = true := by rfl

-- ============================================================
-- §21  Theorems — Database Size & Properties
-- ============================================================

/-- We have at least 20 cards encoded. -/
theorem at_least_20_cards : cardCount ≥ 20 := by native_decide

/-- All Pokémon cards have positive HP. -/
theorem pokemon_cards_positive_hp :
    (allCards.filter (·.isPokemon)).all (·.hp > 0) = true := by native_decide

/-- All trainer cards have 0 HP. -/
theorem trainer_cards_zero_hp :
    (allCards.filter (·.isTrainer)).all (fun c => c.hp == 0) = true := by native_decide

/-- All non-rule-box Pokémon give exactly 1 prize. -/
theorem non_rulebox_one_prize :
    (allCards.filter (fun c => c.isPokemon && !c.hasRuleBox)).all (fun c => c.prizeValue == 1) = true := by
  native_decide

/-- All rule-box Pokémon give ≥ 2 prizes. -/
theorem rulebox_at_least_two :
    (allCards.filter (fun c => c.isPokemon && c.hasRuleBox)).all (·.prizeValue ≥ 2) = true := by
  native_decide

end PokemonLean.Core.CardDatabase

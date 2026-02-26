#!/usr/bin/env python3
"""
Pokémon TCG API Scraper → Lean 4 Definitions Generator

Fetches cards from the Pokémon TCG API and generates Lean 4 definitions
for use in the PokemonLean formal verification project.

Usage:
    python fetch_cards.py [--set SET_ID] [--output OUTPUT_FILE]

Example:
    python fetch_cards.py --set sv1 --output ../PokemonLean/Cards.lean
"""

import argparse
import json
import sys
from urllib.request import urlopen, Request
from urllib.error import URLError

API_BASE = "https://api.pokemontcg.io/v2"

ENERGY_TYPE_MAP = {
    "Fire": "fire",
    "Water": "water",
    "Grass": "grass",
    "Lightning": "lightning",
    "Psychic": "psychic",
    "Fighting": "fighting",
    "Darkness": "dark",
    "Metal": "metal",
    "Fairy": "fairy",
    "Dragon": "dragon",
    "Colorless": "colorless",
}

def fetch_json(url: str) -> dict:
    """Fetch JSON from URL with proper headers."""
    req = Request(url, headers={"User-Agent": "PokemonLean/1.0"})
    with urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode())

def get_standard_sets() -> list[str]:
    """Get current Standard format set IDs."""
    # Standard format typically includes the most recent sets
    # These are approximate - update based on rotation
    return ["sv1", "sv2", "sv3", "sv4", "sv5", "sv6", "sv7", "sv8"]

def fetch_cards(set_id: str | None = None, limit: int = 50) -> list[dict]:
    """Fetch cards from the API."""
    if set_id:
        url = f"{API_BASE}/cards?q=set.id:{set_id}&pageSize={limit}"
    else:
        url = f"{API_BASE}/cards?q=supertype:Pokémon&pageSize={limit}"
    
    try:
        data = fetch_json(url)
        return data.get("data", [])
    except URLError as e:
        print(f"Error fetching cards: {e}", file=sys.stderr)
        return []

def parse_energy_type(types: list[str] | None) -> str:
    """Convert API energy type to Lean enum."""
    if not types:
        return "colorless"
    return ENERGY_TYPE_MAP.get(types[0], "colorless")

def parse_weakness(weaknesses: list[dict] | None, card_types: list[str]) -> str:
    """Generate Lean weakness option."""
    if not weaknesses:
        return "none"
    w = weaknesses[0]
    energy = ENERGY_TYPE_MAP.get(w.get("type", ""), "colorless")
    return f'some {{ energyType := .{energy} }}'

def parse_resistance(resistances: list[dict] | None) -> str:
    """Generate Lean resistance option."""
    if not resistances:
        return "none"
    r = resistances[0]
    energy = ENERGY_TYPE_MAP.get(r.get("type", ""), "colorless")
    value = r.get("value", "-30").replace("-", "")
    return f'some {{ energyType := .{energy}, amount := {value} }}'

def parse_attacks(attacks: list[dict] | None) -> str:
    """Generate Lean attack list."""
    if not attacks:
        return "[]"
    
    attack_strs = []
    for atk in attacks[:2]:  # Limit to 2 attacks
        name = atk.get("name", "Unknown").replace('"', '\\"')
        damage_str = atk.get("damage", "0")
        # Parse damage (can be "30", "30+", "30×", etc.)
        damage = 0
        for char in damage_str:
            if char.isdigit():
                damage = damage * 10 + int(char)
            else:
                break
        attack_strs.append(
            f'{{ name := "{name}", baseDamage := {damage}, effects := [] }}'
        )
    
    return "[" + ", ".join(attack_strs) + "]"

def sanitize_name(name: str) -> str:
    """Convert card name to valid Lean identifier."""
    # Remove special chars, spaces → camelCase
    result = []
    capitalize_next = False
    for char in name:
        if char.isalnum():
            if capitalize_next:
                result.append(char.upper())
                capitalize_next = False
            else:
                result.append(char.lower() if not result else char)
        else:
            capitalize_next = True
    
    # Ensure starts with lowercase letter
    if result and result[0].isdigit():
        result.insert(0, 'c')
    
    return "".join(result) or "unknownCard"

def card_to_lean(card: dict) -> str:
    """Convert a card dict to a Lean definition."""
    name = card.get("name", "Unknown")
    lean_name = sanitize_name(name)
    hp = card.get("hp", "50")
    try:
        hp_int = int(hp)
    except (ValueError, TypeError):
        hp_int = 50
    
    energy = parse_energy_type(card.get("types"))
    attacks = parse_attacks(card.get("attacks"))
    weakness = parse_weakness(card.get("weaknesses"), card.get("types"))
    resistance = parse_resistance(card.get("resistances"))
    
    return f'''def {lean_name} : Card :=
  {{ name := "{name}"
  , hp := {hp_int}
  , energyType := .{energy}
  , attacks := {attacks}
  , weakness := {weakness}
  , resistance := {resistance} }}
'''

def generate_lean_file(cards: list[dict]) -> str:
    """Generate complete Lean file with card definitions."""
    header = """-- Auto-generated from Pokémon TCG API
-- Do not edit manually

import PokemonLean.Basic

namespace PokemonLean.Cards

"""
    
    # Track used names to avoid duplicates
    used_names = {}
    card_defs = []
    for card in cards:
        name = sanitize_name(card.get("name", "Unknown"))
        if name in used_names:
            used_names[name] += 1
            name = f"{name}{used_names[name]}"
        else:
            used_names[name] = 1
        
        # Generate with unique name
        original_name = card.get("name", "Unknown")
        hp = card.get("hp", "50")
        try:
            hp_int = int(hp)
        except (ValueError, TypeError):
            hp_int = 50
        
        energy = parse_energy_type(card.get("types"))
        attacks = parse_attacks(card.get("attacks"))
        weakness = parse_weakness(card.get("weaknesses"), card.get("types"))
        resistance = parse_resistance(card.get("resistances"))
        
        card_defs.append(f'''def {name} : Card :=
  {{ name := "{original_name}"
  , hp := {hp_int}
  , energyType := .{energy}
  , attacks := {attacks}
  , weakness := {weakness}
  , resistance := {resistance} }}
''')
    
    body = "\n".join(card_defs)
    
    footer = """
end PokemonLean.Cards
"""
    
    return header + body + footer

def main():
    parser = argparse.ArgumentParser(
        description="Fetch Pokémon TCG cards and generate Lean definitions"
    )
    parser.add_argument("--set", dest="set_id", help="Set ID to fetch (e.g., sv1)")
    parser.add_argument("--output", "-o", help="Output Lean file path")
    parser.add_argument("--limit", type=int, default=20, help="Max cards to fetch")
    parser.add_argument("--list-sets", action="store_true", help="List standard sets")
    
    args = parser.parse_args()
    
    if args.list_sets:
        print("Standard format sets:", ", ".join(get_standard_sets()))
        return
    
    print(f"Fetching cards{' from set ' + args.set_id if args.set_id else ''}...")
    cards = fetch_cards(args.set_id, args.limit)
    
    if not cards:
        print("No cards fetched.", file=sys.stderr)
        sys.exit(1)
    
    print(f"Fetched {len(cards)} cards")
    
    lean_code = generate_lean_file(cards)
    
    if args.output:
        with open(args.output, "w") as f:
            f.write(lean_code)
        print(f"Written to {args.output}")
    else:
        print(lean_code)

if __name__ == "__main__":
    main()

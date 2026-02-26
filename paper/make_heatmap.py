#!/usr/bin/env python3
"""Generate a matchup matrix heatmap for IEEE DataPort submission."""

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

# 14 decks in order
decks = [
    'Alakazam\nDudunsparce', 'Ceruledge', 'Charizard\nNoctowl', 'Charizard\nPidgeot',
    'Dragapult\nCharizard', 'Dragapult\nDusknoir', 'Gardevoir', 'Gardevoir\nJellicent',
    'Gholdengo\nLunatone', 'Grimmsnarl\nFroslass', 'Kangaskhan\nBouffalant', 'Mega Absol\nBox',
    "N's Zoroark", 'Raging Bolt\nOgerpon'
]

short = [
    'Alak.', 'Cerul.', 'Char.N', 'Char.P',
    'Drag.C', 'Drag.D', 'Garde.', 'Gard.J',
    'Ghol.L', 'Grim.F', 'Kang.B', 'M.Abs',
    "N.Zor", 'R.Bolt'
]

# 14x14 win rate matrix (row = attacker, col = defender)
matrix = np.array([
    [48.9, 67.5, 36.6, 46.6, 37.0, 34.1, 31.5, 41.2, 58.8, 36.8, 77.2, 44.1, 40.7, 65.3],
    [30.0, 48.1, 37.0, 33.9, 47.5, 44.0, 32.5, 41.8, 53.8, 39.8, 41.4, 54.5, 70.9, 42.6],
    [58.4, 59.3, 48.7, 58.1, 42.2, 32.4, 55.8, 54.9, 48.0, 39.7, 33.0, 47.1, 49.3, 55.7],
    [49.2, 60.4, 36.2, 48.7, 34.7, 39.6, 58.4, 59.8, 51.0, 38.6, 45.0, 50.0, 50.6, 53.5],
    [59.3, 49.0, 53.6, 58.0, 48.9, 48.0, 42.1, 46.3, 52.8, 36.1, 51.0, 43.2, 57.3, 45.4],
    [62.7, 53.1, 64.1, 56.3, 48.6, 49.4, 34.3, 41.8, 43.6, 38.6, 36.8, 38.2, 47.2, 45.4],
    [63.3, 62.7, 39.4, 37.4, 51.6, 62.7, 48.0, 36.2, 49.3, 37.4, 39.2, 40.2, 44.8, 62.5],
    [54.8, 52.6, 39.0, 34.5, 48.6, 54.4, 58.3, 48.9, 49.8, 34.6, 42.2, 36.4, 36.0, 61.9],
    [37.3, 43.9, 48.3, 45.9, 42.5, 52.1, 44.1, 43.9, 48.8, 47.6, 55.3, 44.3, 51.6, 49.6],
    [59.9, 56.1, 55.8, 57.0, 59.8, 57.2, 56.6, 59.2, 46.7, 48.5, 47.3, 34.4, 54.5, 47.3],
    [19.8, 55.0, 63.5, 51.8, 44.9, 58.2, 54.9, 52.4, 40.1, 47.3, 49.0, 49.2, 47.7, 31.1],
    [51.5, 41.4, 47.5, 45.1, 52.4, 57.6, 55.8, 58.7, 51.2, 62.1, 47.4, 49.4, 41.8, 29.8],
    [55.6, 26.2, 46.3, 43.8, 39.1, 49.0, 51.9, 60.1, 43.9, 41.7, 49.2, 54.8, 49.5, 34.0],
    [30.3, 53.7, 40.9, 42.6, 49.0, 51.0, 33.3, 33.2, 45.8, 47.7, 65.3, 67.3, 62.3, 48.7],
])

# Meta shares for annotation
shares = [3.2, 2.8, 4.3, 3.9, 3.5, 15.5, 4.6, 4.2, 9.9, 5.1, 2.5, 5.0, 3.1, 3.4]

fig, ax = plt.subplots(figsize=(14, 12))

# Diverging colormap centered at 50%
cmap = plt.cm.RdYlGn
norm = matplotlib.colors.TwoSlopeNorm(vmin=19, vcenter=50, vmax=78)

im = ax.imshow(matrix, cmap=cmap, norm=norm, aspect='equal')

# Add text annotations
for i in range(14):
    for j in range(14):
        val = matrix[i, j]
        color = 'white' if val < 32 or val > 65 else 'black'
        ax.text(j, i, f'{val:.0f}', ha='center', va='center',
                fontsize=8, fontweight='bold', color=color)

ax.set_xticks(range(14))
ax.set_yticks(range(14))
ax.set_xticklabels(short, fontsize=9, rotation=45, ha='right')
ax.set_yticklabels(short, fontsize=9)

ax.set_xlabel('Opponent Deck', fontsize=12, fontweight='bold', labelpad=10)
ax.set_ylabel('Player Deck', fontsize=12, fontweight='bold', labelpad=10)
ax.set_title('Pokémon TCG 14×14 Matchup Win Rate Matrix (%)\nTrainer Hill Tournament Data, Jan 29 – Feb 19, 2026',
             fontsize=14, fontweight='bold', pad=15)

# Colorbar
cbar = plt.colorbar(im, ax=ax, shrink=0.8, pad=0.02)
cbar.set_label('Win Rate (%)', fontsize=11)

# Add meta share bar on the right
ax2 = fig.add_axes([0.92, 0.15, 0.03, 0.55])
colors_bar = [cmap(norm(s * 3 + 35)) for s in shares]  # scale for visual
ax2.barh(range(14), shares, color='#4a90d9', height=0.7, edgecolor='#2c5f8a')
ax2.set_yticks(range(14))
ax2.set_yticklabels(['' for _ in range(14)])
ax2.set_xlabel('Meta %', fontsize=8)
ax2.set_title('Share', fontsize=9, fontweight='bold')
ax2.invert_yaxis()
ax2.tick_params(labelsize=7)
for i, v in enumerate(shares):
    ax2.text(v + 0.3, i, f'{v}%', va='center', fontsize=7)
ax2.set_xlim(0, max(shares) * 1.4)

plt.tight_layout(rect=[0, 0, 0.88, 1])
output = '/Users/arthur/clawd/PokemonLean/paper/matchup_heatmap.png'
plt.savefig(output, dpi=300, bbox_inches='tight', facecolor='white')
print(f"Saved: {output}")

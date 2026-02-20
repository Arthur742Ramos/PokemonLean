
matchup_data = [
  [494, 436, 386, 382, 343, 641, 418, 563, 486, 454, 472, 627, 368, 531],
  [521, 488, 476, 443, 441, 483, 439, 459, 425, 496, 516, 373, 553, 439],
  [572, 467, 485, 344, 566, 558, 592, 570, 598, 473, 545, 599, 473, 561],
  [576, 512, 621, 494, 558, 475, 587, 451, 524, 298, 418, 515, 474, 414],
  [627, 493, 374, 402, 480, 394, 362, 374, 516, 625, 448, 633, 392, 627],
  [324, 480, 397, 471, 558, 487, 549, 581, 422, 557, 493, 584, 330, 593],
  [544, 498, 346, 364, 583, 390, 489, 345, 486, 619, 360, 548, 422, 526],
  [396, 510, 386, 500, 584, 362, 598, 487, 347, 535, 506, 492, 450, 604],
  [480, 528, 361, 432, 421, 536, 463, 580, 489, 454, 573, 593, 510, 490],
  [510, 458, 477, 673, 333, 409, 332, 426, 490, 487, 623, 303, 653, 537],
  [490, 439, 417, 548, 519, 463, 601, 438, 391, 340, 495, 556, 492, 262],
  [341, 588, 368, 441, 315, 366, 412, 466, 370, 653, 407, 489, 772, 675],
  [582, 401, 473, 492, 549, 635, 524, 518, 449, 311, 477, 198, 490, 550],
  [440, 538, 398, 545, 325, 370, 418, 339, 475, 426, 709, 300, 414, 481]
]

meta_shares = [155, 99, 51, 50, 46, 43, 42, 35, 35, 33, 30, 28, 25, 23]

deck_names = [
    "DragapultDusknoir", "GholdengoLunatone", "GrimssnarlFroslass", "MegaAbsolBox",
    "Gardevoir", "CharizardNoctowl", "GardevoirJellicent", "CharizardPidgeot",
    "DragapultCharizard", "RagingBoltOgerpon", "NsZoroark", "AlakazamDudunsparce",
    "KangaskhanBouffalant", "Ceruledge"
]

total_share = sum(meta_shares)
normalized_shares = [s / total_share for s in meta_shares]

print(f"Total Share: {total_share}")

for i, deck_name in enumerate(deck_names):
    expected_wr = 0
    for j, share in enumerate(normalized_shares):
        expected_wr += (matchup_data[i][j] / 1000.0) * share
    print(f"{deck_name}: {expected_wr * 100:.1f}%")

print("-" * 20)
print("Checking specific values:")
dragapult_wr = 0
for j, share in enumerate(normalized_shares):
    dragapult_wr += (matchup_data[0][j] / 1000.0) * share
print(f"Dragapult Expected WR: {dragapult_wr * 100:.1f}% (Claim: 46.7%)")

grimmsnarl_wr = 0
for j, share in enumerate(normalized_shares):
    grimmsnarl_wr += (matchup_data[2][j] / 1000.0) * share
print(f"Grimmsnarl Expected WR: {grimmsnarl_wr * 100:.1f}% (Claim: 52.7%)")

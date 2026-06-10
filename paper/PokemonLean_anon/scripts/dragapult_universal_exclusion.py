#!/usr/bin/env python3
"""Universal (equilibrium-independent) exclusion of Dragapult from the symmetrization.

Proves, via a single linear program, that Dragapult Dusknoir is a best response to NO
optimal strategy of the constant-sum symmetrization S, hence appears in the support of
NO Nash equilibrium (symmetric or asymmetric). This is the global form of the
complementary-slackness argument in Section VII.

Cross-checked against Lean: PokemonLean/SymmetricNash.lean
(symmetric_nash_dragapult_strict_gap proves the same strict inequality for the symmetric mix).
"""
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

def h(x): return F(x, 2)
S = [
 [500, h(915), 407, 403, 358, h(1317), 437, h(1167), 503, 472, 491, 643, 393, h(1091)],
 [h(1085), 500, h(1009), h(931), 474, h(1003), h(941), h(949), h(897), 519, h(1077), h(785), 576, h(901)],
 [593, h(991), 500, h(723), 596, h(1161), 623, 592, h(1237), 498, 564, h(1231), 500, h(1163)],
 [597, h(1069), h(1277), 500, 578, 502, h(1223), h(951), 546, h(625), 435, 537, 491, h(869)],
 [642, 526, 404, 422, 500, 418, h(779), 395, h(1095), 646, h(929), 659, h(843), 651],
 [h(683), h(997), h(839), 498, 582, 500, h(1159), h(1219), 443, 574, 515, 609, h(695), h(1223)],
 [563, h(1059), 377, h(777), h(1221), h(841), 500, h(747), h(1023), h(1287), h(759), 568, 449, 554],
 [h(833), h(1051), 408, h(1049), 605, h(781), h(1253), 500, h(767), h(1109), 534, 513, 466, h(1265)],
 [497, h(1103), h(763), 454, h(905), 557, h(977), h(1233), 500, 482, 591, h(1223), h(1061), h(1015)],
 [528, 481, 502, h(1375), 354, 426, h(713), h(891), 518, 500, h(1283), 325, 671, h(1111)],
 [509, h(923), 436, 565, h(1071), 485, h(1241), 466, 409, h(717), 500, h(1149), h(1015), h(553)],
 [357, h(1215), h(769), 463, 341, 391, 432, 487, h(777), 675, h(851), 500, 787, h(1375)],
 [607, 424, 500, 509, h(1157), h(1305), 551, 534, h(939), 329, h(985), 213, 500, 568],
 [h(909), h(1099), h(837), h(1131), 349, h(777), 446, h(735), h(985), h(889), h(1447), h(625), 432, 500],
]
n = 14
Sf = np.array([[float(S[i][j]) for j in range(n)] for i in range(n)])

# Game value via column-min LP: minimize z s.t. S y <= z (rowwise), sum y = 1, y >= 0.
c = np.zeros(n + 1); c[-1] = 1
A_ub = np.hstack([Sf, -np.ones((n, 1))]); b_ub = np.zeros(n)
A_eq = np.zeros((1, n + 1)); A_eq[0, :n] = 1; b_eq = [1]
bounds = [(0, None)] * n + [(None, None)]
r = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
value = r.x[-1]
print(f"Game value of symmetrization: {value:.6f} permil  (expected 500)")

# Maximize Dragapult(0)'s payoff over the set of OPTIMAL opponent strategies (z <= value).
c2 = np.append(-Sf[0], 0.0)
A_ub2 = np.vstack([A_ub, np.append(np.zeros(n), 1.0)])
b_ub2 = np.append(b_ub, value + 1e-9)
r2 = linprog(c2, A_ub=A_ub2, b_ub=b_ub2, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
best = -r2.fun
print(f"Max Dragapult payoff over ALL optimal opponent strategies: {best:.6f} permil")
print(f"Strictly below value? {best < value - 1e-6}  (gap {value - best:.4f} permil)")
assert best < value - 1e-6, "Dragapult would be a best response to some optimal strategy"
print("\nCONCLUSION: Dragapult is a best response to NO optimal strategy of the")
print("symmetrization, hence is excluded from the support of EVERY Nash equilibrium")
print("(symmetric or asymmetric). This is the global, equilibrium-independent exclusion.")

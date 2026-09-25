/-
Frozen statement: a copy of a statement frozen in the development repository.
id: T8.1
paper_clause: ADVXXZ 2024 numerical.tex:57-60 (the strict certified finish); the main result: omega over ℚ is below 2371339/10^6.
sha256: 9f5ec0e45a9b074b54392cb879da97608f72b6d234da4513a118ed7714e99182
The sha256 is the SHA-256 of the statement text, every byte after the closing line of
this comment. PLATFORM/README.md explains the fields and how to recompute the hash.
-/
import OmegaBound.Omega

/-- The capstone statement of the omega-lean campaign: the matrix-multiplication exponent over ℚ is strictly below
2.371339. Frozen first, per the local platform's rule; every other statement is a milestone toward it. -/
def S_T8_1 : Prop := OmegaBound.omegaMM ℚ < (2371339 : ℝ) / 10 ^ 6

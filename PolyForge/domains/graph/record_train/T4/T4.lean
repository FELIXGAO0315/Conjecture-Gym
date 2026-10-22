import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T4 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) :
    (G.cliqueNum : ℤ) ≤ -(Fintype.card V : ℤ) + 3 * (G.indepNum : ℤ) + 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s2]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(Fintype.card V : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ -1 := by linarith [s1, s2, s3, s4, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]

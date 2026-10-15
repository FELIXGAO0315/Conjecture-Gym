import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C254 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.indepNum : ℤ) ≥ 2 * (G.cliqueNum : ℤ)) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ (G.cliqueNum : ℤ)) :
    2 * (G.cliqueNum : ℤ) ≥ 2 * (Fintype.card V : ℤ) - 5 * (G.indepNum : ℤ) + 8 := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.indepNum : ℤ) ≥ 2 := by linarith [s5, s2]
  have s7 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -2 * (Fintype.card V : ℤ) + 2 * (G.cliqueNum : ℤ) + 5 * (G.indepNum : ℤ) ≥ 8 := by linarith [s1, s2, s3, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]

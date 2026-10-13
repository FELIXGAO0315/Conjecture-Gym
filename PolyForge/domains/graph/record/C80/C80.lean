import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C80 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≤ (G.maxDegree : ℤ)) :
    2 * (G.cliqueNum : ℤ) ≤ -(Fintype.card V : ℤ) + 4 * (G.indepNum : ℤ) := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s5, s1]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s9 : -4 * (G.cliqueNum : ℤ) + 6 * (G.indepNum : ℤ) ≥ 1 := by linarith [s5, s7, s1, s8, s2, s4]
  have s10 : -2 * (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 1 := by have hr := s9; omega
  have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s12 : -6 * (G.cliqueNum : ℤ) + 9 * (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [s1, s2, s4, s6, s10, s11]
  have s13 : -2 * (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by have hr := s12; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s13, heq_gallai]

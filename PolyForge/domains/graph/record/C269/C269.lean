import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C269 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ)) (hn2 : (G.maxDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.cliqueNum : ℤ) ≤ 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - 2 := by
  have s1 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_card_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
      have s11 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [s12, s13]
      have s15 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : 9 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ 5 := by linarith [s7, s8, s9, s10, s15]
      have s17 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 2 := by have hr := s16; omega
      linarith [s17]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

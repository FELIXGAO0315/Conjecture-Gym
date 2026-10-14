import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C121 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 2) (hn2 : (G.maxDegree : ℤ) ≤ (G.cliqueNum : ℤ)) :
    (Fintype.card V : ℤ) ≥ 3 := by
  have s1 : 2 * (Fintype.card V : ℤ) + 3 * (G.indepNum : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s5 : 2 * (Fintype.card V : ℤ) + 3 * (G.indepNum : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
      have s8 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s10 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s10, s11, s12]
      have s14 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s9]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : 3 * (Fintype.card V : ℤ) ≥ 7 := by linarith [s6, s7, s8, s14]
      have s16 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s15; omega
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s18 : 2 * (Fintype.card V : ℤ) + 3 * (G.indepNum : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s16, s17]
      linarith [s18]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

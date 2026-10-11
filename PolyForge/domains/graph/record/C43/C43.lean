import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C43 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ (G.edgeFinset.card : ℤ)) :
    2 * (Fintype.card V : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 3 := by
  have s1 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_card_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s12 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s13 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s7, s13, s11, s14]
      have s16 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : 6 * (Fintype.card V : ℤ) - 9 * (G.edgeFinset.card : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) ≥ 7 := by linarith [s7, s8, s9, s10, s11, s16]
      have s18 : 2 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s17; omega
      linarith [s18]
  linarith [s1]

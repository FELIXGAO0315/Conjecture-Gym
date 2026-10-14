import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C161 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) + 6 := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := connected_min_deg_int G hp2 hp1
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s3, s4, s7]
      have s9 : -(Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s8]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by linarith [s2, s3, s4, s5, s9, s7]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp2
        try push_cast at hw
        linarith [hw]
      have s12 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
      have s13 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.indepNum : ℤ) ≥ 3 := by linarith [s12, s14, s15, s17, s18]
      have s20 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s19]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := connected_min_deg_int G hp2 hp1
        try push_cast at hw
        linarith [hw]
      have s22 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s12, s14, s15, s17, s18]
      have s23 : -(Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s22]) (by linarith [s21])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : 3 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) ≥ 17 := by linarith [s11, s12, s13, s14, s20, s23, s18]
      have s25 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by have hr := s24; omega
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

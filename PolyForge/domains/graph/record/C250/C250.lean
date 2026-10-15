import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C250 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) (hn2 : (G.maxDegree : ℤ) ≤ 3) :
    (G.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 15 := by
  have s1 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 15 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
      have s5 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
      have s7 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s8 : 3 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s10 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 15 := by linarith [s2, s3, s4, s5, s6, s8, s9]
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
      have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.indepNum : ℤ) ≥ 3 := by linarith [s11, s12, s13, s15, s16]
      have s18 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
      have s20 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s21 : 3 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s17]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s23 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 15 := by linarith [s17, s11, s18, s12, s19, s21, s22, s16]
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

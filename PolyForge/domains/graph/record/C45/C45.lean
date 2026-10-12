import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C45 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.girth : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
        have hw := girth_le_card_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 9 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s10 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s10]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s7, s8, s9, s11]
      have s13 : (G.indepNum : ℤ) ≥ 2 := by have hr := s12; omega
      have s14 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
        have hw := girth_le_card_int G hp1
        try push_cast at hw
        linarith [hw]
      have s15 : (G.edgeFinset.card : ℤ) ≥ 3 := by
        have hw := three_le_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s16 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s18 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s17, s9]
      have s20 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : 21 * (G.chromaticNumber.toNat : ℤ) + 21 * (G.indepNum : ℤ) - 7 * (G.girth : ℤ) ≥ 54 := by linarith [s13, s14, s15, s16, s8, s17, s18, s20]
      have s22 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 8 := by have hr := s21; omega
      linarith [s22]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

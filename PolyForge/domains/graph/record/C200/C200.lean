import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C200 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≤ 1) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.maxDegree : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) + 2 := by
  have s1 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s4 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn2]
      have s5 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s10 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn2]
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s15 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s9, s12]
      have s16 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s15]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s18 : 18 * (G.maxDegree : ℤ) + 12 * (G.chromaticNumber.toNat : ℤ) - 18 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s6, s7, s8, s9, s10, s13, s16, s17]
      have s19 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s18; omega
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

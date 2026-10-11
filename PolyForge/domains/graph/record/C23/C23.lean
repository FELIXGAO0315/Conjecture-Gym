import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C23 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.edgeFinset.card : ℤ) ≤ 4) :
    2 * (G.minDegree : ℤ) ≤ -2 * (Fintype.card V : ℤ) + 5 * (G.indepNum : ℤ) + 2 := by
  have s1 : -2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s2]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.edgeFinset.card : ℤ) ≥ -4 := by linarith [hn1]
      have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s9 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s9, s10]
      have s12 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s11]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : -3 * (G.minDegree : ℤ) ≥ -8 := by linarith [s6, s7, s12]
      have s14 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s13; omega
      have s15 : -2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [s2, s3, s4, s5, s14, s10]
      linarith [s15]
    · -- 1*alpha <= 2
      have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s19 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s20 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := bipartite_four_mul_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s22 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s23 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s22]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s25 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s27 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s25]) (by linarith [s26])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s28 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s18, s21, s25, s27]
      have s29 : 5 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s24]) (by linarith [s28])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s30 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s16, s17, s18, s21, s25, s23]
      have s31 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s28]) (by linarith [s30])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s32 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s33 : -6 * (G.minDegree : ℤ) + 9 * (G.indepNum : ℤ) - 6 * (G.vertexCoverNum.toNat : ℤ) ≥ -8 := by linarith [s16, s17, s18, s19, s20, s21, s23, s29, s31, s32]
      have s34 : -2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hr := s33; omega
      linarith [s34]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

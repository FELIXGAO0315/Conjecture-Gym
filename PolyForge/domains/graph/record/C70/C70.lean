import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C70 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 5) (hn2 : (G.edgeFinset.card : ℤ) ≥ 4) :
    (G.indepNum : ℤ) ≥ 2 * (G.minDegree : ℤ) + 1 := by
  have s1 : -2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 1 := by
    by_cases hc1 : (10 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 10
      have s2 : (Fintype.card V : ℤ) ≥ 10 := by have hcc := hc1; omega
      have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s4 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [hn1]
      have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s6 : -10 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 10) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s2]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s9 : -10 * (G.minDegree : ℤ) + 5 * (G.indepNum : ℤ) ≥ 7 := by linarith [s2, s3, s4, s6, s7, s8]
      have s10 : -2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 2 := by have hr := s9; omega
      linarith [s10]
    · -- 1*n <= 9
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) ≥ 4 := by linarith [hn2]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s17 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s11, s12, s13, s15, s16]
      have s18 : (G.indepNum : ℤ) ≥ 3 := by have hr := s17; omega
      have s19 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s20 : -(Fintype.card V : ℤ) ≥ -9 := by have hcc := hc1; omega
      have s21 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s22 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s12, s16]
      have s23 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s22]) (by linarith [s21])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s25 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s26 : -(G.minDegree : ℤ) ≥ -8 := by linarith [s24, s25, s20]
      have s27 : -8 * (Fintype.card V : ℤ) - 9 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -72 := by
        have hmul : (0 : ℤ) ≤ (9 - (Fintype.card V : ℤ)) * (8 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s26])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s28 : -3 * (G.minDegree : ℤ) ≥ -8 := by linarith [s19, s23, s27, s16]
      have s29 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s28; omega
      have s30 : -2 * (Fintype.card V : ℤ) - 9 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -18 := by
        have hmul : (0 : ℤ) ≤ (9 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s29])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s31 : -9 * (G.minDegree : ℤ) ≥ -16 := by linarith [s19, s30, s16]
      have s32 : -(G.minDegree : ℤ) ≥ -1 := by have hr := s31; omega
      have s33 : -2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 1 := by linarith [s18, s32]
      linarith [s33]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

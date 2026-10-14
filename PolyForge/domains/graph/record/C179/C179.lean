import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C179 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.diam : ℤ) ≥ 5) :
    (Fintype.card V : ℤ) ≥ 3 * (G.minDegree : ℤ) - (G.indepNum : ℤ) + 6 := by
  have s1 : (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (5 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 5
      have s2 : (G.indepNum : ℤ) ≥ 5 := by have hcc := hc1; omega
      have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s5 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s6 : (G.diam : ℤ) ≥ 5 := by linarith [hn1]
      have s7 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s5, s6]
      have s8 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s7]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 6 := by linarith [s2, s3, s8, s9]
      linarith [s10]
    · -- 1*alpha <= 4
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s13 : (G.diam : ℤ) ≥ 5 := by linarith [hn1]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : (G.indepNum : ℤ) ≥ 3 := by linarith [s11, s12, s13, s14, s16]
      have s18 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.indepNum : ℤ) ≥ -4 := by have hcc := hc1; omega
      have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s19]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : -(Fintype.card V : ℤ) ≥ -8 := by linarith [s11, s14, s19, s21]
      have s23 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s24 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s12, s13]
      have s25 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s24]) (by linarith [s23])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s26 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s27 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s28 : -(G.minDegree : ℤ) ≥ -7 := by linarith [s26, s27, s11, s14, s19, s21]
      have s29 : -7 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -56 := by
        have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (7 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s22]) (by linarith [s28])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s30 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s31 : -23 * (G.minDegree : ℤ) ≥ -49 := by linarith [s18, s25, s29, s30]
      have s32 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s31; omega
      have s33 : -2 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -16 := by
        have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s22]) (by linarith [s32])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s34 : -4 * (G.minDegree : ℤ) ≥ -7 := by linarith [s18, s33, s30]
      have s35 : -(G.minDegree : ℤ) ≥ -1 := by have hr := s34; omega
      have s36 : 7 * (Fintype.card V : ℤ) + 6 * (G.minDegree : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 42 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * (7 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s24]) (by linarith [s28])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s37 : (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 6 := by linarith [s17, s35, s25, s36]
      linarith [s37]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

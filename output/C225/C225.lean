import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C225 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.indepNum : ℤ) ≥ 3) :
    (G.minDegree : ℤ) ≤ 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.indepNum : ℤ) ≥ 3 := by linarith [hn1]
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s6]) (by linarith [s2])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s9 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s3]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s11 : -3 * (G.minDegree : ℤ) + 9 * (G.indepNum : ℤ) ≥ 22 := by linarith [s2, s3, s4, s5, s7, s9, s10]
      have s12 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by have hr := s11; omega
      linarith [s12]
    · -- 1*n <= 5
      have s13 : (G.indepNum : ℤ) ≥ 3 := by linarith [hn1]
      have s14 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
      have s16 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s17 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 0 := by
        have hw := alpha_le_card_int G
        try push_cast at hw
        linarith [hw]
      have s18 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s13, s17]
      have s19 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s18]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s21 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s22 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s20, s21, s15]
      have s23 : -4 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -20 := by
        have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s25 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s14, s19, s23, s24]
      have s26 : -2 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -10 := by
        have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s25])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s27 : -5 * (G.minDegree : ℤ) + 15 * (G.indepNum : ℤ) ≥ 37 := by linarith [s13, s14, s26, s24]
      have s28 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by have hr := s27; omega
      linarith [s28]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

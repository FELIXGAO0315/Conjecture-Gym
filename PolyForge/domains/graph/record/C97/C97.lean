import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C97 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.radius.toNat : ℤ) ≤ 6) :
    (G.diam : ℤ) ≤ -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - 1 := by
  have s1 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 1 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.radius.toNat : ℤ)
    · -- 1*radius >= 2
      have s2 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 1 := by
        by_cases hc2 : (5 : ℤ) ≤ (G.radius.toNat : ℤ)
        · -- 1*radius >= 5
          have s3 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := acyclic_chi_int G (isTree_acyclic G hp1)
            try push_cast at hw
            linarith [hw]
          have s5 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s6 : (G.radius.toNat : ℤ) ≥ 5 := by have hcc := hc2; omega
          have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s8 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s8]) (by linarith [s4])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : (G.indepNum : ℤ) ≥ 3 := by linarith [s3, s4, s5, s6, s7, s9]
          have s11 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s13 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s3, s5, s6]
          have s14 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s13]) (by linarith [s12])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s15 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
            have hw := tree_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s16 : -3 * (G.minDegree : ℤ) + 9 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) ≥ 7 := by linarith [s10, s4, s5, s11, s7, s9, s14, s15]
          have s17 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 3 := by have hr := s16; omega
          linarith [s17]
        · -- 1*radius <= 4
          have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := acyclic_chi_int G (isTree_acyclic G hp1)
            try push_cast at hw
            linarith [hw]
          have s19 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s20 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
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
          have s24 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := diam_le_two_radius_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.radius.toNat : ℤ) ≥ -4 := by have hcc := hc2; omega
          have s26 : -(G.diam : ℤ) ≥ -8 := by linarith [s24, s25]
          have s27 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s28 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s29 : (G.radius.toNat : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s30 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s28, s19, s29]
          have s31 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s30]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
            have hw := tree_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s33 : -6 * (G.minDegree : ℤ) + 18 * (G.indepNum : ℤ) - 6 * (G.diam : ℤ) ≥ 1 := by linarith [s18, s19, s20, s21, s23, s26, s31, s32]
          have s34 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 1 := by have hr := s33; omega
          linarith [s34]
      linarith [s2]
    · -- 1*radius <= 1
      have s35 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s36 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s37 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s38 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s39 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s40 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s41 : -(G.radius.toNat : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s42 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s43 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s42]) (by linarith [s38])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s44 : -2 * (G.minDegree : ℤ) + 6 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 1 := by linarith [s35, s36, s37, s38, s39, s40, s41, s43]
      have s45 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 1 := by have hr := s44; omega
      linarith [s45]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

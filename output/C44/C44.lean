import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C44 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ)) (hn2 : (G.maxDegree : ℤ) ≥ 2) :
    2 * (G.minDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 10 := by
  have s1 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s3 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
            by_cases hc3 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 6
              have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := acyclic_chi_int G (isTree_acyclic G hp1)
                try push_cast at hw
                linarith [hw]
              have s5 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc3; omega
              have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s9 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s8]) (by linarith [s4])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s10 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s11 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s5]) (by linarith [s10])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s12 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
                have hw := tree_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s13 : -6 * (G.minDegree : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 35 := by linarith [s4, s5, s6, s7, s9, s11, s12]
              have s14 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by have hr := s13; omega
              linarith [s14]
            · -- 1*n <= 5
              have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc2; omega
              have s16 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s17 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s18 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc3; omega
              have s19 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s20 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
              have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s22 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s16, s20, s21]
              have s23 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s22]) (by linarith [s19])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s24 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s25 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s26 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
                have hw := tree_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s27 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s24, s25, s18, s26]
              have s28 : -4 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -20 := by
                have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s18]) (by linarith [s27])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s29 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s17, s23, s28, s26]
              have s30 : -2 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -10 := by
                have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s18]) (by linarith [s29])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s31 : -5 * (G.minDegree : ℤ) ≥ -8 := by linarith [s17, s30, s26]
              have s32 : -(G.minDegree : ℤ) ≥ -1 := by have hr := s31; omega
              have s33 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s15, s16, s32]
              linarith [s33]
          linarith [s3]
        · -- 1*chi <= 1
          have s34 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s35 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s36 : (G.maxDegree : ℤ) ≥ 2 := by linarith [hn2]
          have s37 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s38 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s39 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s40 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s41 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s40]) (by linarith [s38])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s42 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s43 : -(G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [s38, s39, s41, s42]
          have s44 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s45 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
          have s46 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s40, s45, s42]
          have s47 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s46]) (by linarith [s44])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s48 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
            have hw := tree_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s49 : -6 * (G.minDegree : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 28 := by linarith [s34, s35, s36, s37, s43, s47, s42, s48]
          have s50 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by have hr := s49; omega
          linarith [s50]
      linarith [s2]
    · -- 1*alpha <= 2
      have s51 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s52 : (G.maxDegree : ℤ) ≥ 2 := by linarith [hn2]
      have s53 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s54 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s55 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s56 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s54]) (by linarith [s55])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s57 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s58 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s51, s52, s53, s54, s56, s57]
      have s59 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s58; omega
      have s60 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s61 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s51, s52, s60, s57]
      have s62 : (G.indepNum : ℤ) ≥ 2 := by have hr := s61; omega
      have s63 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s64 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s65 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s51, s52, s57]
      have s66 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s65]) (by linarith [s64])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s67 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s60, s54]
      have s68 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s69 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s70 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s68, s69, s60, s54]
      have s71 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s67]) (by linarith [s70])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s72 : -11 * (G.minDegree : ℤ) ≥ -18 := by linarith [s63, s66, s71, s57]
      have s73 : -(G.minDegree : ℤ) ≥ -1 := by have hr := s72; omega
      have s74 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s59, s62, s73]
      linarith [s74]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

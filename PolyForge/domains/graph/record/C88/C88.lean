import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C88 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.diam : ℤ) ≤ 6) :
    2 * (G.radius.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 3 * (G.diam : ℤ) := by
  have s1 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 2
      have s2 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.radius.toNat : ℤ)
        · -- 1*radius >= 3
          have s3 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
            by_cases hc3 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 7
              have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := acyclic_chi_int G (isTree_acyclic G hp1)
                try push_cast at hw
                linarith [hw]
              have s5 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc3; omega
              have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s7 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s7]) (by linarith [s4])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s9 : 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s4, s5, s6, s8]
              have s10 : (G.indepNum : ℤ) ≥ 4 := by have hr := s9; omega
              have s11 : (G.radius.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s12 : -(G.diam : ℤ) ≥ -6 := by linarith [hn1]
              have s13 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by linarith [s10, s11, s12]
              linarith [s13]
            · -- 1*n <= 6
              have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := acyclic_chi_int G (isTree_acyclic G hp1)
                try push_cast at hw
                linarith [hw]
              have s15 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
                try push_cast at hw
                linarith [hw]
              have s16 : (G.radius.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s18 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc3; omega
              have s19 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s20 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s14])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by linarith [s14, s15, s16, s17, s18, s20]
              linarith [s21]
          linarith [s3]
        · -- 1*radius <= 2
          have s22 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := diam_le_two_radius_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s23 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := acyclic_chi_int G (isTree_acyclic G hp1)
            try push_cast at hw
            linarith [hw]
          have s24 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
            try push_cast at hw
            linarith [hw]
          have s25 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s26 : -(G.radius.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s27 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s27]) (by linarith [s23])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s29 : 6 * (G.indepNum : ℤ) - 6 * (G.diam : ℤ) + 4 * (G.radius.toNat : ℤ) ≥ -1 := by linarith [s22, s23, s24, s25, s26, s28]
          have s30 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by have hr := s29; omega
          linarith [s30]
      linarith [s2]
    · -- 1*chi <= 1
      have s31 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s32 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s33 : (G.radius.toNat : ℤ) ≥ 0 := by positivity
      have s34 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s35 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s36 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s35]) (by linarith [s31])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s37 : 3 * (G.indepNum : ℤ) - 3 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s31, s32, s33, s34, s36]
      linarith [s37]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

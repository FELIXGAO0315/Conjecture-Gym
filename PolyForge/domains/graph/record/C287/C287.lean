import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C287 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (Fintype.card V : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) + 6 := by
  have s1 : (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.edgeFinset.card : ℤ) ≥ 3 := by
        have hw := three_le_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s10 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s5, s9]
      have s11 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s10])
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s13 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : -(Fintype.card V : ℤ) ≥ -8 := by linarith [s5, s7, s8, s9, s14]
      have s16 : 11 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 24 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (8 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.indepNum : ℤ) ≥ -4 := by linarith [s5, s8, s9]
      have s19 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s18]) (by linarith [s17])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 33 * (G.chromaticNumber.toNat : ℤ) ≥ 40 := by linarith [s5, s6, s7, s8, s11, s16, s19]
      have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s20; omega
      have s22 : 11 * (Fintype.card V : ℤ) ≥ 36 := by linarith [s6, s11, s16]
      have s23 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s22; omega
      have s24 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s21, s23]
      linarith [s24]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C25 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.maxDegree : ℤ) ≥ 2) (hn2 : (Fintype.card V : ℤ) ≤ 6) :
    (G.cliqueNum : ℤ) - (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≤ 4 := by
  have s1 : -(G.cliqueNum : ℤ) + (G.indepNum : ℤ) + (G.radius.toNat : ℤ) ≥ -4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp2
        linarith [hw]
      have s4 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
        have hw := girth_le_diam_int G hp2 hp1
        linarith [hw]
      have s5 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s6 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s3, s4, s5]
      have s7 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s6; omega
      have s8 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn2]
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [s8, s9]
      have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s12 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s8, s11]
      have s13 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        have hw := tau_le_card_sub_one_int G (by omega)
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        linarith [hw]
      have s15 : -(G.cliqueNum : ℤ) + (G.indepNum : ℤ) + (G.radius.toNat : ℤ) ≥ -4 := by linarith [s2, s7, s10, s13, s14]
      linarith [s15]
    · -- 1*chi <= 2
      have s16 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s17 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp2
        linarith [hw]
      have s18 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
        have hw := girth_le_diam_int G hp2 hp1
        linarith [hw]
      have s19 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s20 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s22 : -2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ -3 := by linarith [s16, s17, s18, s19, s20, s21]
      have s23 : -(G.cliqueNum : ℤ) + (G.indepNum : ℤ) + (G.radius.toNat : ℤ) ≥ -1 := by have hr := s22; omega
      linarith [s23]
  linarith [s1]

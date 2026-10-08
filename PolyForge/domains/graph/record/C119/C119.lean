import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C119 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hp2 : G.IsTree) (hn1 : (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 0) :
    -(G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.radius.toNat : ℤ) ≤ -2 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 2 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.diam : ℤ)
    · -- 1*diam >= 1
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G (isTree_connected G hp2)
        linarith [hw]
      have s4 : (G.diam : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s5 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s3, s4]
      have s6 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s5; omega
      have s7 : (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s8 : (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s2, s6, s7]
      linarith [s8]
    · -- 1*diam <= 0
      have s9 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
      have s10 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp2
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s9, s10]
      have s12 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int G (by omega)
        linarith [hw]
      have s13 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int G (by omega)
        linarith [hw]
      have s14 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G (isTree_connected G hp2)
        linarith [hw]
      have s15 : -(G.diam : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s16 : -(G.radius.toNat : ℤ) ≥ 0 := by linarith [s14, s15]
      have s17 : (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 2 := by linarith [s12, s13, s16]
      linarith [s17]
  linarith [s1]

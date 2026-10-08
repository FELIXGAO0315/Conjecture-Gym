import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsEdgeConnected 2) (hn1 : (G.cliqueNum : ℤ) ≤ 6) :
    (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≤ 5 := by
  have s1 : -(G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s6 : -(G.cliqueNum : ℤ) ≥ -6 := by linarith [hn1]
      have s7 : -2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -10 := by linarith [s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s9 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : -2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ -4 := by linarith [s8, s9, s10]
      linarith [s11]
  linarith [s1]

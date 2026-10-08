import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C62 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 4) :
    -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by
  have s1 : -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s5]
      have s7 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int G (by omega)
        linarith [hw]
      have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -4 := by linarith [hn2]
      have s9 : -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by linarith [s2, s3, s7, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s11 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        linarith [hw]
      have s12 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) + 2 * (G.girth : ℤ) ≥ 4 := by linarith [s10, s11, s12, s13]
      linarith [s14]
  linarith [s1]

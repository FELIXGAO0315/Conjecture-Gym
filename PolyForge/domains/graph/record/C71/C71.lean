import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C71 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : (G.cliqueNum : ℤ) ≤ 3) (hn2 : (Fintype.card V : ℤ) ≤ 5) :
    -(Fintype.card V : ℤ) + 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≤ 2 := by
  have s1 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by
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
      have s6 : -(G.cliqueNum : ℤ) ≥ -3 := by linarith [hn1]
      have s7 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by linarith [s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s10 : (G.indepNum : ℤ) ≥ 0 := by positivity
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : (Fintype.card V : ℤ) - 2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ -2 := by linarith [s8, s9, s10, s11]
      linarith [s12]
  linarith [s1]

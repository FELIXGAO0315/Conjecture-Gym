import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C56 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0) (hn2 : -2 * (G.minDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0) :
    2 * (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) - (G.girth : ℤ) ≤ -7 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    linarith [hw]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s4 : -2 * (G.minDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s4]
  have s6 : -(G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s5; omega
  have s7 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.girth : ℤ) ≥ 7 := by linarith [s1, s6]
  linarith [s7]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C131 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0) (hn2 : (G.edgeFinset.card : ℤ) ≥ 5) :
    2 * (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 8 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [hn2]
  have s3 : (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 4 * (G.edgeFinset.card : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 15 := by linarith [s1, s2, s3]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (G.cliqueNum : ℤ) ≥ 8 := by have hr := s4; omega
  linarith [s5]

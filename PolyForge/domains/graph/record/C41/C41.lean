import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C41 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.indepNum : ℤ) ≥ 3) (hn2 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≤ 0) :
    (G.minDegree : ℤ) ≥ -2 * (G.maxDegree : ℤ) + 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s3 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s3; omega
  have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s6 : 2 * (G.maxDegree : ℤ) + (G.minDegree : ℤ) ≥ 4 := by linarith [s4, s5]
  linarith [s6]

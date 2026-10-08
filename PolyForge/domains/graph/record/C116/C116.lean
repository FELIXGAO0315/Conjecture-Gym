import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C116 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0) :
    2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 7 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s2, s1, s3]
  have s5 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s4; omega
  have s6 : 2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 7 := by linarith [s1, s5]
  linarith [s6]

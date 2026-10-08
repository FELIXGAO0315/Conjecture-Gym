import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C100 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.IsBipartite) (hn1 : -(G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0) :
    -(G.maxDegree : ℤ) - (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≤ 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s3 : -(G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s6 : 2 * (G.minDegree : ℤ) - 4 * (G.chromaticNumber.toNat : ℤ) ≥ -7 := by linarith [s1, s4, s3, s5]
  have s7 : (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hr := s6; omega
  have s8 : 3 * (G.maxDegree : ℤ) + 3 * (G.minDegree : ℤ) - 6 * (G.chromaticNumber.toNat : ℤ) ≥ -8 := by linarith [s1, s2, s3, s7, s5]
  have s9 : (G.maxDegree : ℤ) + (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hr := s8; omega
  linarith [s9]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C133 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : G.Connected) (hn1 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.diam : ℤ) ≥ 0) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 1) :
    2 * (Fintype.card V : ℤ) - (G.radius.toNat : ℤ) ≥ 2 := by
  have s1 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := radius_le_diam_int G hp2
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [hn2]
  have s3 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s4 : (G.chromaticNumber.toNat : ℤ) - 2 * (G.diam : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    linarith [hw]
  have s6 : 4 * (Fintype.card V : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4, s5]
  have s7 : 2 * (Fintype.card V : ℤ) - (G.radius.toNat : ℤ) ≥ 2 := by have hr := s6; omega
  linarith [s7]

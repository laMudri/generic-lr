{-# OPTIONS --sized-types --without-K #-}

module Everything where

-- Small stdlib additions
import Data.Bool.Extra
import Data.Hand
import Data.Wrap.Top
import Function.Extra
import Relation.Binary.Setoid
import Relation.Unary.Checked
import Relation.Unary.Extra

-- Basic definitions of the bunched connectives
import Relation.Unary.Bunched
import Relation.Unary.Bunched.Checked
import Relation.Unary.Bunched.Properties
import Relation.Unary.Bunched.Synth

-- Partially ordered algebraic structures
import Algebra.Po
import Algebra.Po.Construct.Vector
import Algebra.Po.Construct.Nat
import Algebra.Po.Relation

-- Skew algebraic structures
import Algebra.Skew
import Algebra.Skew.Definitions
import Algebra.Skew.Definitions.Left
import Algebra.Skew.Definitions.Both
import Algebra.Skew.Definitions.Right
import Algebra.Skew.Construct.Vector
import Algebra.Skew.Relation

-- Relational algebraic structures
import Algebra.Relational
import Algebra.Relational.Construct.Vector
import Algebra.Relational.Relation
import Algebra.PoToRel

-- The nullary-binary tree data structure
import Data.LTree
import Data.LTree.Vector
import Data.LTree.Automation
import Data.LTree.Vector.Properties
import Data.LTree.Matrix
import Data.LTree.Matrix.Properties

-- Algebraic gadgets useful in the framework (mostly for working with vectors)
import Generic.Linear.Operations
import Generic.Linear.Algebra

-- Syntax, culminating in a definition of terms in a given system, as well as
-- map-s for a layer of syntax
import Generic.Linear.Syntax
import Generic.Linear.Syntax.Interpretation
import Generic.Linear.Syntax.Interpretation.Map
import Generic.Linear.Syntax.Term

-- Supplementary notions: usage-checked variables, environments, and renamings
import Generic.Linear.Variable
import Generic.Linear.Environment
import Generic.Linear.Environment.Properties
import Generic.Linear.Environment.Categorical
import Generic.Linear.Renaming
import Generic.Linear.Renaming.Properties
import Generic.Linear.Renaming.Monoidal

-- Derivation of the generic traversal `semantics`
import Generic.Linear.Semantics

-- A packaged version of the framework --- standard module for users to import
import Generic.Linear.Everything

-- Examples
import Generic.Linear.Semantics.Syntactic
import Generic.Linear.Example.Mono
import Generic.Linear.Example.ZeroOneMany.Affine
import Generic.Linear.Example.ZeroOneMany
import Generic.Linear.Example.PaperExamples
import Generic.Linear.Example.Environment
import Generic.Linear.Example.MuMuTilde.Term
import Generic.Linear.Example.WRel
import Generic.Linear.Example.UsageCheck
import Generic.Linear.Example.UsageCheck.Example
import Generic.Linear.Example.PaperExamples.HeavyI
import Generic.Linear.Example.WRel.Monotonicity
import Generic.Linear.Example.MuMuTilde

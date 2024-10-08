Require Export EnsemblesImplicit.
Require Export Utf8.
Require Export Families.
Require Export IndexedFamilies.
Require Import EnsemblesSpec.
Notation "x ∈ S" := (In S x) (at level 75).
Notation "S ∩ T" := (Intersection S T) (right associativity, at level 55).
Notation "S //\\ T" := (Intersection S T) (only parsing, right associativity, at level 55).
Notation "S ∪ T" := (Union S T) (right associativity, at level 65).
Notation "S \\// T" := (Union S T) (only parsing, right associativity, at level 65).
Notation "S ∖ T" := (Setminus S T) (no associativity, at level 65).
Notation "S \ T" := (Setminus S T) (only parsing, no associativity, at level 65).
Notation "S ⊆ T" := (Included S T) (at level 70).
Notation "S <= T" := (Included S T) (only parsing, at level 70).
Notation "S ⊊ T" := (Strict_Included S T) (at level 70).
Notation "S < T" := (Strict_Included S T) (only parsing, at level 70).
Notation "[[ x ]]" := (Singleton x) (at level 0).
Notation "[[ x , y ]]" := (Couple x y) (at level 0).
Notation "[[ x , y , z ]]" := (Triple x y z) (at level 0).
Notation "∅" := Empty_set (at level 0).
Notation "⋃ F" := (FamilyUnion F) (at level 0).
Notation "⋃ [ x : X ] S" := (IndexedUnion (fun x:X => S)) (at level 0, x ident).
Notation "\\// [ x : X ] S" := (IndexedUnion (fun x:X => S)) (only parsing, x ident, at level 0).
Notation "⋂ F" := (FamilyIntersection F) (at level 0).
Notation "⋂ [ x : X ] S" := (IndexedIntersection (fun x:X => S)) (at level 0, x ident).
Notation "//\\ [ x : X ] S" := (IndexedIntersection (fun x:X => S)) (only parsing, x ident, at level 0).
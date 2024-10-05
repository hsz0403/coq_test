Require Import Orders.
Require Export DepMapInterface.
Require Export DepMapFactsInterface.
Require Export DepMapImplementation.
Require Export DepMapFactsImplementation.
Module Make (X : OrderedType) : DepMapFacts (X).
Module Map := DepMapImpl(X).
Module Facts := DepMapFactsOn(X)(Map).
Include Facts.
End Make.
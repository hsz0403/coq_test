From Huffman Require Import Huffman.
From Huffman Require Import Code.
From Huffman Require Import ISort.
From Coq Require Extraction.
Extraction Inline list_length_induction huffman_aux_F.
Extraction NoInline code insert isort map frequency_list huffman encode decode.
Extraction "huffman.ml" code huffman encode decode.
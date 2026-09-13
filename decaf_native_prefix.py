"""Derive native Rust multiplication checkpoints; Rocq proves their decomposition."""
import re


def multiplication_prefix(extraction):
    match = re.search(r"^Definition fq_mul\b.*? :=\n(.*?)(?=^Definition |\Z)", extraction, re.M | re.S)
    if match is None:
        raise ValueError("missing native multiplication body")
    body = match[1].strip()
    first = "  let x40 : t_u32 := (0 : t_u32) in\n"
    second = "  let x87 : t_u32 := (0 : t_u32) in\n"
    if body.count(first) != 1 or body.count(second) != 1 or not body.endswith("out1."):
        raise ValueError("native multiplication checkpoint boundaries changed")
    row, remainder = body.split(first)
    reduction, tail = remainder.split(second)
    row_names = ["x23", "x25", "x27", "x29", "x31", "x33", "x35", "x37", "x39"]
    reduced_names = [f"x{i}" for i in range(71, 86, 2)]
    reads = "".join(f"let x{i} := f_index arg1 (({i if i < 8 else 0} : t_usize)) in\n"
                    for i in range(1, 9))
    generated = """(* Generated from the pinned Hax body. Do not edit.
   Checkpoint meanings and links to fq_mul are proved in separate modules. *)
From Stdlib Require Import ZArith List.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Import ListNotations.
Open Scope Z_scope.
Definition native_first_row (arg1 arg2 : list t_u32) : list t_u32 :=
"""
    generated += row + "[" + ";".join(row_names) + "].\n"
    generated += "Definition native_remainder (out1 arg1 arg2 row : list t_u32) : list t_u32 :=\n"
    generated += reads + "match row with [" + ";".join(row_names) + "] =>\n"
    generated += first + remainder.removesuffix("out1.") + "out1\n| _ => [] end.\n"
    generated += "Definition native_redc_state (row : list t_u32) : list t_u32 * t_u8 :=\n"
    generated += "match row with [" + ";".join(row_names) + "] =>\n" + first + reduction
    generated += "([" + ";".join(reduced_names) + "], x86)\n| _ => ([], (0 : t_u8)) end.\n"
    generated += """Definition redc_words (row : list t_u32) : list t_u32 :=
  let state := native_redc_state row in fst state ++ [(cast (snd state) : t_u32)].
Definition native_after_redc (out1 arg1 arg2 : list t_u32) (state : list t_u32 * t_u8) : list t_u32 :=
"""
    generated += reads + "let x86 := snd state in match fst state with [" + ";".join(reduced_names) + "] =>\n"
    generated += second + tail.removesuffix("out1.") + "out1\n| _ => [] end.\n"
    return generated

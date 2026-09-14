"""Derive native Rust multiplication checkpoints; Rocq proves their decomposition."""
import re


SUFFIX_MODULES = tuple(f"NativeSuffixDefinition{i}" for i in range(1, 9))


def multiplication_suffixes(extraction):
    """Extract exact remaining bodies; separate Rocq equations check every link."""
    match = re.search(r"^Definition fq_mul\b.*? :=\n(.*?)(?=^Definition |\Z)", extraction, re.M | re.S)
    if match is None or not match[1].strip().endswith("out1."):
        raise ValueError("missing native multiplication suffix body")
    body = match[1].strip()
    header = """(* Generated from the pinned Hax body. Do not edit.
   RustMultiplyTail proves every connection to the extracted multiplication. *)
From Stdlib Require Import ZArith List.
From Core Require Import Core.
From Slice Require Import Decaf_proof_slice_Fiat.
Import ListNotations.
Open Scope Z_scope.
"""
    reads = "".join(f"let x{i} := f_index arg1 (({i if i < 8 else 0} : t_usize)) in\n"
                    for i in range(1, 9))
    result = {}
    for index, start in enumerate(range(87, 767, 97), 1):
        marker = f"  let x{start} : t_u32 := (0 : t_u32) in\n"
        if body.count(marker) != 1:
            raise ValueError("native suffix boundary changed")
        tail = (marker + body.split(marker)[1]).removesuffix("out1.") + "out1\n"
        if index == 1:
            acc = [f"x{i}" for i in range(71, 86, 2)] + ["acc_top"]
            if tail.count("(cast (x86))") != 1:
                raise ValueError("native suffix carry interface changed")
            tail = tail.replace("(cast (x86))", "(acc_top)")
        else:
            acc = [f"x{i}" for i in range(start - 17, start - 2, 2)] + [f"x{start - 1}"]
        name = "native_final" if index == 8 else f"native_suffix{index}"
        args = "out1 acc" if index == 8 else "out1 arg1 arg2 acc"
        source = header + f"Definition {name} ({args} : list t_u32) : list t_u32 :=\n"
        source += reads if index != 8 else ""
        source += "match acc with [" + ";".join(acc) + "] =>\n" + tail + "| _ => [] end.\n"
        result[SUFFIX_MODULES[index - 1] + ".v"] = source
    return result


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


def multiplication_rounds(extraction):
    """Derive the repeated-round stages; their equations are proved in Rocq."""
    match = re.search(r"^Definition fq_mul\b.*? :=\n(.*?)(?=^Definition |\Z)", extraction, re.M | re.S)
    if match is None:
        raise ValueError("missing native multiplication body")
    body = match[1]

    def segment(first, last):
        begin = f"  let x{first} : t_u32 := (0 : t_u32) in\n"
        end = f"  let x{last} : t_u32 := (0 : t_u32) in\n"
        if body.count(begin) != 1 or body.count(end) != 1:
            raise ValueError("native round boundaries changed")
        return begin + body.split(begin)[1].split(end)[0]

    baseline = None
    for index, start in enumerate(range(87, 670, 97)):
        current = segment(start, start + 97)
        mapping = {i: i - start + 87 for i in range(start, start + 97)}
        mapping[index + 1] = 1
        if index == 0:
            if current.count("(cast (x86))") != 1:
                raise ValueError("first repeated round carry interface changed")
            current = current.replace("(cast (x86))", "(acc_top)")
        else:
            mapping.update(zip(range(start - 17, start - 2, 2), range(71, 86, 2)))
            current = re.sub(r"\bx" + str(start - 1) + r"\b", "acc_top", current)
        current = re.sub(r"\bx(\d+)\b", lambda m: "x" + str(mapping.get(int(m[1]), int(m[1]))), current)
        if baseline is None:
            baseline = current
        elif current != baseline:
            raise ValueError("native repeated rounds no longer share the reviewed shape")
    # Shape equality is a fail-closed inventory check, not whole-body refinement.
    acc = ";".join([f"x{i}" for i in range(71, 86, 2)] + ["acc_top"])
    product = ";".join(f"x{i}" for i in range(101, 118, 2))
    summed = ";".join(f"x{i}" for i in range(118, 135, 2))
    output = "[" + ";".join([f"x{i}" for i in range(167, 182, 2)] + ["x183"]) + "]\n"
    sum_tail = segment(118, 184).replace("(cast (x86))", "(acc_top)")
    add = segment(118, 136).replace("(cast (x86))", "(acc_top)")
    reduction = segment(136, 184)
    generated = "Definition native_round (digit : t_u32) (arg2 acc : list t_u32) : list t_u32 :=\n"
    generated += "let x1 := digit in match acc with [" + acc + "] =>\n" + baseline + output + "| _ => [] end.\n"
    generated += "Definition native_add9 (a b : list t_u32) : list t_u32 * t_u8 :=\n"
    generated += "match a, b with [" + acc + "], [" + product + "] =>\n" + add
    generated += "([" + summed + "], x135)\n| _, _ => ([], (0 : t_u8)) end.\n"
    generated += "Definition round_after_product (acc row : list t_u32) : list t_u32 :=\n"
    generated += "match acc, row with [" + acc + "], [" + product + "] =>\n" + sum_tail + output + "| _, _ => [] end.\n"
    generated += "Definition round_after_sum (state : list t_u32 * t_u8) : list t_u32 :=\n"
    generated += "let x135 := snd state in match fst state with [" + summed + "] =>\n" + reduction + output + "| _ => [] end.\n"
    generated += """Definition round_finish (state : list t_u32 * t_u8) (carry : t_u8) :=
  fst state ++ [f_add (cast (snd state) : t_u32) (cast carry : t_u32)].
Definition digit_input (digit : t_u32) : list t_u32 :=
  [digit; (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32); (0:t_u32)].
"""
    return generated

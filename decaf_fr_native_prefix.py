"""Derive Fr multiplication checkpoints from the pinned Hax source.

These definitions do not prove their own connection to native execution.
Separate Rocq equations connect every checkpoint to the complete extracted body.
"""
import re

HEADER = """(* Generated from the pinned Hax Fr body. Do not edit. *)
From Stdlib Require Import ZArith List.
From Core Require Import Core.
From FrSlice Require Import Decaf_fr_slice_Fiat.
Import ListNotations.
Open Scope Z_scope.
"""
READS = "".join(f"let x{i} := f_index arg1 (({i if i < 8 else 0} : t_usize)) in\n"
                for i in range(1, 9))
SUFFIX_MODULES = tuple(f"FrSuffixDefinition{i}" for i in range(1, 8))
DERIVED_MODULES = ("FrPrefix", "FrRoundDefinition", "FrAfterReductionDefinition",
                   *SUFFIX_MODULES, "FrFinalDefinition")


def multiplication_checkpoints(extraction):
    match = re.search(r"^Definition fr_mul\b.*? :=\n(.*?)(?=^Definition |\Z)",
                      extraction, re.M | re.S)
    if match is None or not match[1].strip().endswith("out1."):
        raise ValueError("missing or unsupported Fr multiplication body")
    body = match[1].strip()

    def marker(index):
        text = f"  let x{index} : t_u32 := (0 : t_u32) in\n"
        if body.count(text) != 1:
            raise ValueError("Fr checkpoint boundary changed")
        return text

    def segment(start, end):
        first, last = marker(start), marker(end)
        if body.index(first) >= body.index(last):
            raise ValueError("Fr checkpoint order changed")
        return first + body.split(first)[1].split(last)[0]

    def tail(start):
        first = marker(start)
        return (first + body.split(first)[1]).removesuffix("out1.") + "out1\n"

    boundaries = [40, *range(91, 799, 101)]
    offsets = [body.index(marker(index)) for index in boundaries]
    if offsets != sorted(offsets):
        raise ValueError("Fr checkpoint order changed")
    row, remainder = body.split(marker(40))
    reduction = remainder.split(marker(91))[0]
    row_names = ";".join(f"x{i}" for i in range(23, 40, 2))
    redc_names = ";".join(f"x{i}" for i in range(75, 90, 2))
    prefix = HEADER + "Definition fr_native_first_row (arg1 arg2 : list t_u32) : list t_u32 :=\n"
    prefix += row + "[" + row_names + "].\n"
    prefix += "Definition fr_native_remainder (out1 arg1 arg2 row : list t_u32) : list t_u32 :=\n"
    prefix += READS + "match row with [" + row_names + "] =>\n" + tail(40) + "| _ => [] end.\n"
    prefix += "Definition fr_native_redc_state (row : list t_u32) : list t_u32 * t_u8 :=\n"
    prefix += "match row with [" + row_names + "] =>\n" + marker(40) + reduction
    prefix += "([" + redc_names + "],x90)\n| _ => ([],(0:t_u8)) end.\n"
    prefix += "Definition fr_redc_words (row : list t_u32) : list t_u32 := let state := fr_native_redc_state row in fst state ++ [(cast (snd state) : t_u32)].\n"
    result = {"FrPrefix.v": prefix}
    after = HEADER + "Definition fr_native_after_redc (out1 arg1 arg2 : list t_u32) (state : list t_u32 * t_u8) : list t_u32 :=\n"
    after += READS + "let x90 := snd state in match fst state with [" + redc_names + "] =>\n"
    result["FrAfterReductionDefinition.v"] = after + tail(91) + "| _ => [] end.\n"
    for index, start in enumerate(range(91, 799, 101), 1):
        current = tail(start)
        if index == 1:
            if current.count("(cast (x90))") != 1:
                raise ValueError("Fr carry interface changed")
            current = current.replace("(cast (x90))", "(acc_top)")
            acc = redc_names + ";acc_top"
        else:
            acc = ";".join([f"x{i}" for i in range(start - 17, start - 2, 2)] + [f"x{start-1}"])
        name = "fr_native_final" if index == 8 else f"fr_native_suffix{index}"
        args = "out1 acc" if index == 8 else "out1 arg1 arg2 acc"
        module = "FrFinalDefinition" if index == 8 else f"FrSuffixDefinition{index}"
        source = HEADER + f"Definition {name} ({args} : list t_u32) : list t_u32 :=\n"
        source += READS if index != 8 else ""
        result[module + ".v"] = source + "match acc with [" + acc + "] =>\n" + current + "| _ => [] end.\n"
    baseline = None
    for index, start in enumerate(range(91, 698, 101)):
        current = segment(start, start + 101)
        prior = (set(range(75, 90, 2)) | {90} if index == 0 else
                 set(range(start - 17, start - 2, 2)) | {start - 1})
        allowed = set(range(start, start + 101)) | prior | {index + 1}
        references = {int(value) for value in re.findall(r"\bx(\d+)\b", current)}
        if not references <= allowed:
            raise ValueError("Fr round has an unexpected cross-round reference")
        mapping = {i: i - start + 91 for i in range(start, start + 101)}
        mapping[index + 1] = 1
        if index == 0:
            current = current.replace("(cast (x90))", "(acc_top)")
        else:
            mapping.update(zip(range(start - 17, start - 2, 2), range(75, 90, 2)))
            current = re.sub(r"\bx" + str(start - 1) + r"\b", "acc_top", current)
        current = re.sub(r"\bx(\d+)\b", lambda m: "x" + str(mapping.get(int(m[1]), int(m[1]))), current)
        if baseline is None:
            baseline = current
        elif current != baseline:
            raise ValueError("Fr repeated rounds no longer share the reviewed shape")
    acc = redc_names + ";acc_top"
    product = ";".join(f"x{i}" for i in range(105, 122, 2))
    summed = ";".join(f"x{i}" for i in range(122, 139, 2))
    output = "[" + ";".join([f"x{i}" for i in range(175, 190, 2)] + ["x191"]) + "]\n"
    rounds = HEADER + "Definition fr_native_round (digit : t_u32) (arg2 acc : list t_u32) : list t_u32 :=\n"
    rounds += "let x1 := digit in match acc with [" + acc + "] =>\n" + baseline + output + "| _ => [] end.\n"
    rounds += "Definition fr_native_add9 (a b : list t_u32) : list t_u32 * t_u8 :=\nmatch a,b with [" + acc + "],[" + product + "] =>\n"
    rounds += segment(122, 140).replace("(cast (x90))", "(acc_top)") + "([" + summed + "],x139)\n| _,_ => ([],(0:t_u8)) end.\n"
    rounds += "Definition fr_round_after_product (acc row : list t_u32) : list t_u32 :=\nmatch acc,row with [" + acc + "],[" + product + "] =>\n"
    rounds += segment(122, 192).replace("(cast (x90))", "(acc_top)") + output + "| _,_ => [] end.\n"
    rounds += "Definition fr_round_after_sum (state : list t_u32 * t_u8) : list t_u32 :=\nlet x139 := snd state in match fst state with [" + summed + "] =>\n"
    rounds += segment(140, 192) + output + "| _ => [] end.\n"
    result["FrRoundDefinition.v"] = rounds
    if set(result) != {module + ".v" for module in DERIVED_MODULES}:
        raise ValueError("Fr checkpoint inventory is incomplete")
    return result

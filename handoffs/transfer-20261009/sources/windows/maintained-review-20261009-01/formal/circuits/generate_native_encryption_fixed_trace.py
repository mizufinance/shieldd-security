"""Finite integer round certificates for the fixed domain28/domain29 hashes."""
import re

PARAMETERS = 'RuntimeHashBlock_authorization_rnk_permutation2_0.parameters'
ARITHMETIC = 'NativeEncryptionFixedArithmetic'


def audited(body, names):
    return body + ''.join(
        f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n'
        for name in names)


def generate(witnesses):
    modulus = int(witnesses['modulus'])
    assert modulus == 52435875175126190479447740508185965837690552500527637822603658699938581184513
    records = witnesses['records']
    assert [row['domain'] for row in records] == [28, 29]
    modules = {}
    audits = {}
    for record in records:
        domain = record['domain']
        states = record['states']
        assert record['arity'] == 0 and len(states) == 66
        assert all(len(row) == 3 and all(0 <= n < modulus for n in row) for row in states)
        assert states[0] == [domain, 0, 0] and states[65][1] == record['hash']
        prefix = f'RuntimeNativeEncryptionFixed{domain}'
        namespace = 'ShielddSecurity.' + prefix
        data_name = prefix + '_Data'
        body = (f'import ShielddSecurity.{ARITHMETIC}\n'
                'import ShielddSecurity.NativeAssetHashParameters\n'
                'set_option maxHeartbeats 250000\nset_option maxRecDepth 2048\n'
                f'namespace {namespace}\n'
                'def states (index : Nat) (column : Fin 3) : Int :=\n'
                '  match index with\n')
        for index, values in enumerate(states):
            body += f'  | {index} => match column.val with\n'
            body += ''.join(f'    | {j} => {n}\n' for j, n in enumerate(values))
            body += '    | _ => 0\n'
        body += '  | _ => 0\n'
        body += (f'theorem initial : states 0 = {ARITHMETIC}.integerInitial 3 {domain} := by\n'
                 '  funext column\n  fin_cases column <;> decide\n')
        modules[data_name] = audited(body, ['initial']) + f'end {namespace}\n'
        audits[data_name] = ['initial']
        round_names = []
        for start in range(0, 65, 5):
            name = prefix + f'_Rounds_{start:02}_{start+4:02}'
            body = (f'import ShielddSecurity.{data_name}\n'
                    'set_option maxHeartbeats 250000\nset_option maxRecDepth 2048\n'
                    f'namespace {namespace}\n')
            names = []
            for index in range(start, start + 5):
                lemma = f'step{index:02}'
                names.append(lemma)
                body += (f'theorem {lemma} : states {index+1} =\n'
                         f'    {ARITHMETIC}.integerRound {PARAMETERS} {index} (states {index}) := by\n'
                         '  funext column\n  fin_cases column <;> decide\n')
            modules[name] = audited(body, names) + f'end {namespace}\n'
            audits[name] = names
            round_names.append(name)
        join = prefix + '_Hash'
        body = ''.join(f'import ShielddSecurity.{name}\n' for name in round_names)
        body += ('set_option maxHeartbeats 250000\nset_option maxRecDepth 2048\n'
                 f'namespace {namespace}\n'
                 f'theorem steps (index : Nat) (bounded : index < 65) : states (index + 1) =\n'
                 f'    {ARITHMETIC}.integerRound {PARAMETERS} index (states index) := by\n'
                 '  interval_cases index <;> first\n')
        body += ''.join(f'    | exact step{index:02}\n' for index in range(65))
        body += ('theorem hash_value {F : Type} [Field F] [CharP F Scalar.modulus] :\n'
                 f'    Poseidon.hash3 NativeAssetHashParameters.smallParameters {domain} [] =\n'
                 f'      ({record["hash"]} : F) := by\n'
                 '  simpa only [states, Int.cast_ofNat] using\n'
                 f'    ({ARITHMETIC}.fixed_empty_hash_trace (F := F) {domain} states initial steps)\n')
        modules[join] = audited(body, ['steps', 'hash_value']) + f'end {namespace}\n'
        audits[join] = ['steps', 'hash_value']
    assert len(modules) == 30 and sum(map(len, audits.values())) == 136
    assert all(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', body) for body in modules.values())
    return modules, audits

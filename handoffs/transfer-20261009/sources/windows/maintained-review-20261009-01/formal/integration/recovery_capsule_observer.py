"""Read-only recovery source recipe for a fresh diagnostic stage.

The existing65-page packet is immutable. This companion owns no compiler or
Var operation and requires future exporter lifecycle/ordinary2/repeat wiring.
"""


def instrument_recovery(data,group_source):
    if not isinstance(data,bytes):raise ValueError('recovery source bytes required')
    if not isinstance(group_source,bytes):raise ValueError('pinned group nonidentity source required')
    group=group_source.decode().replace('\r\n','\n')
    nonidentity='    pub fn assert_non_identity(&self) {\n        // A prime-subgroup point has x=0 only at identity (the other x=0 point has order 2).\n        let _ = self.x.inv();\n    }'
    if group.count(nonidentity)!=1:raise ValueError('pinned group nonidentity operation changed')
    newline='\r\n' if b'\r\n' in data else '\n' 
    text=data.decode()
    if newline=='\r\n' and '\n' in text.replace('\r\n',''):
        raise ValueError('recovery mixed source line endings')
    text=text.replace('\r\n','\n')
    if 'capsule_inspection' in text:raise ValueError('recovery observer already activated')
    def replace(old,new):
        nonlocal text
        if text.count(old)!=1:raise ValueError('recovery exact operation/source anchor drift')
        text=text.replace(old,new)
    replace('use commonware_math::algebra::Additive;', 'use commonware_math::algebra::{Additive, Field};')
    replace('    let var = |s: &Scalar| Var::witness(ctx, |_| s.clone());\n    let out = witness.capsule.witness_fields(ctx);','    #[cfg(feature = "formal-observer")]\n    let _capsule_scope = capsule_inspection::scope();\n    let var = |s: &Scalar| Var::witness(ctx, |_| s.clone());\n    let out = witness.capsule.witness_fields(ctx);')
    replace('    let bits = scalar::canonical_bits(ctx, &var(&witness.randomizer));\n    group::generator()\n        .multiply_fixed(&bits)\n        .assert_equal(&out.epk);','    let randomizer = var(&witness.randomizer);\n    let bits = scalar::canonical_bits(ctx, &randomizer);\n    let computed_epk = group::generator().multiply_fixed(&bits);\n    computed_epk.assert_equal(&out.epk);')
    replace('    out.epk.assert_non_identity();','    let epk_inverse = out.epk.x.inv();')
    replace('    capsule.epk.assert_non_identity();','    let epk_inverse = capsule.epk.x.inv();')
    replace('    (seed.clone() + &encryption::secret(params, &shared)).assert_eq(&out.c2);\n    constrain_plaintext(params, amount, blinding, &out, &seed);','    let secret = encryption::secret(params, &shared);\n    let computed_c2 = seed.clone() + &secret;\n    computed_c2.assert_eq(&out.c2);\n    #[cfg(feature = "formal-observer")]\n    capsule_inspection::core(payload_key, amount, blinding, &randomizer, &bits,\n        &seed, &out, &computed_epk, &shared, &secret, &computed_c2, &epk_inverse);\n    constrain_plaintext(params, amount, blinding, &out, &seed);')
    replace('    params\n        .circuit(\n            CONFIRMATION,','    let computed_confirmation = params\n        .circuit(\n            CONFIRMATION,')
    replace('        )\n        .assert_eq(&capsule.confirmation);\n    (amount.clone() + &encryption::stream(params, seed, 0)).assert_eq(&capsule.encrypted_amount);\n    (blinding.clone() + &encryption::stream(params, seed, 1))\n        .assert_eq(&capsule.encrypted_blinding);','        );\n    computed_confirmation.assert_eq(&capsule.confirmation);\n    let amount_stream = encryption::stream(params, seed, 0);\n    let computed_amount = amount.clone() + &amount_stream;\n    computed_amount.assert_eq(&capsule.encrypted_amount);\n    let blinding_stream = encryption::stream(params, seed, 1);\n    let computed_blinding = blinding.clone() + &blinding_stream;\n    computed_blinding.assert_eq(&capsule.encrypted_blinding);')
    replace('        .circuit(COMMITMENT, &capsule.commitment_inputs())\n        .assert_eq(&capsule.commitment);\n}','        .circuit(COMMITMENT, &capsule.commitment_inputs())\n        .assert_eq(&capsule.commitment);\n    #[cfg(feature = "formal-observer")]\n    capsule_inspection::plaintext(amount, blinding, capsule, seed,\n        &computed_confirmation, &amount_stream, &computed_amount,\n        &blinding_stream, &computed_blinding, &epk_inverse);\n}')
    return ('#[cfg(feature = "formal-observer")]\npub mod capsule_inspection;\n'+text).replace('\n',newline).encode()


def import_existing_inverse_field(data):
    """Exact import repair on retained source04; ordinary operations unchanged."""
    if not isinstance(data,bytes):raise ValueError('recovery source bytes required')
    newline=b'\r\n' if b'\r\n' in data else b'\n'
    if newline==b'\r\n' and b'\n' in data.replace(b'\r\n',b''):raise ValueError('recovery mixed source line endings')
    text=data.replace(b'\r\n',b'\n')
    anchor=b'use commonware_math::algebra::Additive;'
    if text.count(anchor)!=1 or text.count(b'let epk_inverse = out.epk.x.inv();')!=1 or text.count(b'let epk_inverse = capsule.epk.x.inv();')!=1:
        raise ValueError('retained recovery inverse/import source drift')
    return text.replace(anchor,b'use commonware_math::algebra::{Additive, Field};').replace(b'\n',newline)

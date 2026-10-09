// Current source fragment: shieldd.lock 844389ee069e1fb2e576708842d0b389b4d9a44a
pub fn constrain_spend<'ctx>(
    ctx: Context<'ctx, Scalar>,
    params: &Parameters,
    shared: &SpendContext<'ctx>,
    w: &SpendWitness,
    optional: Option<(&OptionalWitness, Padding)>,
) -> Spend<'ctx> {
    let var = |s: &Scalar| Var::witness(ctx, |_| s.clone());
    let note = w.note.witness(ctx);
    decompose(ctx, &note.amount, 128);
    let commitment = params.circuit(NOTE, &note.fields(&shared.asset, &shared.address));
    let path = w.path.witness(ctx);
    let real_nullifier = params.circuit(
        NOTE_NULLIFIER,
        &[shared.nk.clone(), commitment.clone(), path.position.clone()],
    );
    let positions = decompose(ctx, &path.position, 48);
    let anchor =
        tree::root_with_position_bits(ctx, params, Tree::State, commitment, &path, &positions);
    let nullifier = var(&w.nullifier);
    let dummy = match optional {
        None => {
            real_nullifier.assert_eq(&nullifier);
            anchor.assert_eq(&shared.anchor);
            BoolVar::constant(false)
        }
        Some((optional, padding)) => {
            let (domain, slot) = padding.domain_slot();
            let dummy = BoolVar::witness(ctx, |_| optional.is_dummy);
            let synthetic = params.circuit(
                domain,
                &[
                    var(&optional.seed),
                    shared.randomizer.clone(),
                    Var::native(Scalar::from(slot as u64)),
                ],
            );
            dummy
                .select(&synthetic, &real_nullifier)
                .assert_eq(&nullifier);
            let real = !dummy.clone();
            (real.var().clone() * &(anchor - &shared.anchor)).assert_eq(&Var::zero());
            (dummy.var().clone() * &note.amount).assert_eq(&Var::zero());
            dummy
        }
    };
    Spend {
        is_dummy: dummy,
        amount: note.amount,
        nullifier,
    }
}

#[derive(Clone)]
pub struct OutputWitness;

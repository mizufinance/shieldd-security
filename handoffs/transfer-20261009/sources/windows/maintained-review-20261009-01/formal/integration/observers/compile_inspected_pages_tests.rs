#[cfg(test)]
mod inspected_pages_tests {
    use super::*;
    use crate::zk::circuit::{build, Var};

    fn small() -> (Circuit<Scalar>, Vec<CircuitIdx>, InputLayout) {
        let (circuit, selected) = build(|ctx| {
            let x = Var::witness(ctx, |_| Scalar::from(3u64));
            let y = Var::witness(ctx, |_| Scalar::from(7u64));
            let product = x.clone() * &y;
            product.assert_eq(&Var::witness(ctx, |_| Scalar::from(21u64)));
            vec![x, y, product]
        });
        let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
        (circuit, selected, layout)
    }
    #[test]
    fn pages_match_single_inspection_and_full_ordinary_rows() {
        let (circuit, selected, layout) = small();
        let ordinary = Relation::compile(&circuit, &layout).unwrap();
        let (single, expected, copy) =
            Relation::compile_inspected(&circuit, &layout, &selected).unwrap();
        let pages = [&selected[..2], &selected[2..]];
        let mut expressions = Vec::new();
        let mut calls = Vec::new();
        let result: Result<_, super::super::Error> = Relation::compile_inspected_pages(
            &circuit,
            &layout,
            2,
            pages,
            |ordinal, handles, page| {
                calls.push((ordinal, handles.len()));
                expressions.extend(page);
                Ok(())
            },
        );
        let (paged, paged_copy) = result.unwrap();
        assert_eq!(calls, vec![(0, 2), (1, 1)]);
        assert_eq!(expressions, expected);
        assert_eq!(paged_copy, copy);
        assert_eq!(paged.rows, ordinary.rows);
        assert_eq!(paged.rows, single.rows);
        assert_eq!(paged.digest, ordinary.digest);
        assert_eq!(paged.size, ordinary.size);
        assert_eq!(paged.public_inputs, ordinary.public_inputs);
        assert_eq!(paged.blocks, ordinary.blocks);
        assert_eq!(paged.committed_start, ordinary.committed_start);
    }
    #[derive(Debug)]
    enum SinkFailure {
        Compiler,
        Stop,
    }
    impl From<super::super::Error> for SinkFailure {
        fn from(_: super::super::Error) -> Self {
            Self::Compiler
        }
    }
    #[test]
    fn sink_failure_stops_before_the_next_page() {
        let (circuit, selected, layout) = small();
        let mut calls = 0;
        let result = Relation::compile_inspected_pages(
            &circuit,
            &layout,
            2,
            [&selected[..2], &selected[2..]],
            |_, _, _| {
                calls += 1;
                Err::<(), _>(SinkFailure::Stop)
            },
        );
        assert!(matches!(result, Err(SinkFailure::Stop)));
        assert_eq!(calls, 1);
    }
    #[test]
    fn truncated_overflow_empty_duplicate_and_oversize_pages_are_refused() {
        let (circuit, selected, layout) = small();
        let oversized = vec![selected[0]; 4097];
        let duplicate = vec![selected[0]; 2];
        for (count, pages) in [
            (2, vec![&selected[..2]]),
            (1, vec![&selected[..2], &selected[2..]]),
            (1, vec![&selected[..0]]),
            (1, vec![duplicate.as_slice()]),
            (1, vec![oversized.as_slice()]),
            (0, vec![&selected[..2]]),
            (75, vec![&selected[..2]]),
        ] {
            let result: Result<_, super::super::Error> = Relation::compile_inspected_pages(
                &circuit,
                &layout,
                count,
                pages,
                |_, _, _| Ok(()),
            );
            assert!(result.is_err());
        }
    }
    #[test]
    fn full_transfer_catalogues_keep_ordinary_rows_and_stop_at_the_boundary() {
        let (circuit, selected, layout) = small();
        let ordinary = Relation::compile(&circuit, &layout).unwrap();
        for count in [65usize, 74] {
            let mut calls = 0;
            let result: Result<_, super::super::Error> = Relation::compile_inspected_pages(
                &circuit, &layout, count, std::iter::repeat_n(&selected[..2], count),
                |ordinal, handles, expressions| {
                    assert_eq!(ordinal, calls);
                    assert_eq!(handles, &selected[..2]);
                    assert_eq!(expressions.len(), 2);
                    calls += 1;
                    Ok(())
                },
            );
            let (observed, _) = result.unwrap();
            assert_eq!(calls, count);
            assert_eq!(observed.rows, ordinary.rows);
            assert_eq!(observed.digest, ordinary.digest);
            assert_eq!(observed.size, ordinary.size);
            assert_eq!(observed.public_inputs, ordinary.public_inputs);
            assert_eq!(observed.blocks, ordinary.blocks);
        }
        let mut called = false;
        let refused: Result<_, super::super::Error> = Relation::compile_inspected_pages(
            &circuit, &layout, 75, [&selected[..2]], |_, _, _| { called = true; Ok(()) },
        );
        let error = match refused {
            Ok(_) => panic!("over-limit Transfer catalogue unexpectedly accepted"),
            Err(error) => error,
        };
        assert!(error.to_string().contains("outside 1..74"));
        assert!(!called);
    }
    #[test]
    fn deferred_square_is_refused_before_callback() {
        let (circuit, selected) = build(|ctx| {
            let x = Var::witness(ctx, |_| Scalar::from(3u64));
            let y = Var::witness(ctx, |_| Scalar::from(9u64));
            let square = x.clone() * &x;
            square.assert_eq(&y);
            vec![x, y, square]
        });
        let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
        let mut consumed = false;
        let result: Result<_, super::super::Error> =
            Relation::compile_inspected_pages(&circuit, &layout, 1, [&selected[2..]], |_, _, _| {
                consumed = true;
                Ok(())
            });
        let failure = match result {
            Ok(_) => panic!("deferred square page unexpectedly accepted"),
            Err(error) => error,
        };
        assert!(failure.to_string().contains("inspection deferred square"));
        assert!(!consumed);
    }
}

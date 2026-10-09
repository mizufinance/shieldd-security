/// Fresh-stage diagnostic adapter for the bounded Transfer catalogue (up to74 pages).
/// Compiler operations retain exactly the ordinary order. Pages expose only
/// pre-outline LCs; callers must stream/discard each callback payload, and must
/// qualify the finished relation by full ordered ordinary rows plus a repeat.
pub fn compile_inspected_pages<'page, Pages, Consume, SinkError>(
    circuit: &Circuit<Scalar>,
    layout: &InputLayout,
    expected_pages: usize,
    pages: Pages,
    mut consume: Consume,
) -> Result<(Self, u32), SinkError>
where
    Pages: IntoIterator<Item = &'page [CircuitIdx]>,
    Consume: FnMut(usize, &'page [CircuitIdx], Vec<Vec<(u32, Scalar)>>) -> Result<(), SinkError>,
    SinkError: From<super::Error>,
{
    let invalid = |context| {
        super::Error::from(Error::InvalidIndex {
            context,
            index: CircuitIdx::Node(0),
        })
    };
    if !(1..=74).contains(&expected_pages) {
        return Err(invalid("inspection expected page count outside 1..74").into());
    }
    let mut compiler = Compiler::new(circuit, layout).map_err(super::Error::from)?;
    compiler.compile_nodes().map_err(super::Error::from)?;
    compiler.compile_assertions().map_err(super::Error::from)?;
    compiler.link_inputs().map_err(super::Error::from)?;
    let mut count = 0;
    for (ordinal, selected) in pages.into_iter().enumerate() {
        if ordinal >= expected_pages {
            return Err(invalid("inspection page overflow").into());
        }
        if selected.is_empty() || selected.len() > 4096 {
            return Err(invalid("inspection page selection outside 1..4096").into());
        }
        if selected.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(invalid("inspection page handles not strictly sorted").into());
        }
        let mut expressions = Vec::with_capacity(selected.len());
        let mut terms = 0usize;
        for &index in selected {
            if let CircuitIdx::Node(node) = index {
                if compiler.square_nodes.contains_key(&(node as usize)) {
                    return Err(super::Error::from(Error::InvalidIndex {
                        context: "inspection deferred square",
                        index,
                    })
                    .into());
                }
            }
            let expression = compiler.expression(index).map_err(super::Error::from)?;
            let expression = to_sparse(&expression).map_err(super::Error::from)?;
            terms = terms
                .checked_add(expression.len())
                .ok_or_else(|| invalid("inspection page term overflow"))?;
            if expression.len() > 4096 || terms > 65536 {
                return Err(invalid("inspection page sparse term bound").into());
            }
            expressions.push(expression);
        }
        consume(ordinal, selected, expressions)?;
        count += 1;
    }
    if count != expected_pages {
        return Err(invalid("inspection truncated page stream").into());
    }
    let constant_copy =
        u32::try_from(compiler.next_column).map_err(|_| super::Error::from(Error::SizeOverflow))?;
    compiler.outline_constant().map_err(super::Error::from)?;
    let relation = compiler.finish().map_err(super::Error::from)?;
    Ok((relation, constant_copy))
}

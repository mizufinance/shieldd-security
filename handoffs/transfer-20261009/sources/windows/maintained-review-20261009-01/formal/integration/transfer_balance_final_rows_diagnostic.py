"""Root-only bounded diagnostic slice; never a constructor or qualification.

One full identity-checked stream is observed, retaining direct seed rows and
64 neighbouring rows around the two final outputs. Bounds refuse rather than truncate. The
consumer still has to prove exact source operations and original-row coverage.
"""
from collections import deque
from circuits import transfer_relation as relation

SEEDS = frozenset((22230, 22231, 22734, 22735, 21711, 195230, 195234))
COPY = 200692
ANCHORS = frozenset((195230, 195234))
DIGEST = '16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'


class Slice:
    def __init__(self):
        self.columns = set(SEEDS)
        self.rows = {}
        self.reasons = {}
        self.previous = deque(maxlen=64)
        self.follow_until = -1

    def keep(self, row, reason):
        self.rows[row['row']] = row
        self.reasons.setdefault(row['row'], set()).add(reason)
        if len(self.rows) > 2048:
            raise relation.RelationError('final balance diagnostic row bound2048')

    def observe(self, row):
        support = {column for side in ('a', 'b') for column, _ in row[side]} - {0, COPY}
        seed = bool(support & SEEDS)
        anchor = bool(support & ANCHORS)
        if seed:
            self.keep(row, 'direct-seed')
            self.columns.update(support)
            if len(self.columns) > 4096:
                raise relation.RelationError('final balance diagnostic support bound4096')
        if anchor:
            for previous in self.previous:
                self.keep(previous, 'final-output-neighbour')
            self.follow_until = max(self.follow_until, row['row'] + 64)
        if row['row'] <= self.follow_until:
            self.keep(row, 'final-output-neighbour')
        if row['row'] == 200769:
            self.keep(row, 'constant-link-position')
        self.previous.append(row)


def extract(stream):
    collector = Slice()
    identity = relation.inspect(stream, DIGEST, row_observer=collector.observe)
    if (identity['domain_size'], identity['stored_rows'], identity['source_public'], identity['source_blocks']) != (
            262144, 200770, [[1, 22734]], [[[1, 6]]]):
        raise relation.RelationError('exact production diagnostic identity required')
    return dict(identity=identity, seeds=sorted(SEEDS), support=sorted(collector.columns),
                selected_rows=[collector.rows[i] for i in sorted(collector.rows)],
                reasons={str(i): sorted(collector.reasons[i]) for i in sorted(collector.rows)},
                diagnostics_only=True, qualification=False, certification=False,
                scope='Direct seed and bounded final-output-neighbour original row slice only; no completeness or selected-row satisfaction credit.')

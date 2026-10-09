"""Independent integer/affine oracle for TEST-ONLY native threshold vectors.

No Rust/Jubjub library is invoked. This checks one deterministic fixture, not
DKG, randomness, authorization, computational security or live release.
Jubjub equation/encoding: https://github.com/zkcrypto/jubjub/blob/main/src/lib.rs
Scalar order: https://github.com/zkcrypto/jubjub/blob/main/src/fr.rs
The actual compiled generator bytes remain an explicit suite-identity input.
"""
import hashlib
import json
import re

Q = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001
R = 0x0E7DB4EA6533AFA906673B0101343B00A6682093CCC81082D0970E5ED6F72CB7
D = -10240 * pow(10241, -1, Q) % Q
IDENTITY = (0, 1)


def add(left, right):
    x, y = left
    u, v = right
    factor = D * x * u * y * v % Q
    return ((x * v + y * u) * pow(1 + factor, -1, Q) % Q,
            (y * v + x * u) * pow(1 - factor, -1, Q) % Q)


def multiply(point, scalar):
    # Do not reduce scalar here: the independent subgroup check needs [R]G.
    result = IDENTITY
    while scalar:
        if scalar & 1:
            result = add(result, point)
        point = add(point, point)
        scalar >>= 1
    return result


def square_root(value):
    """Tonelli-Shanks over the prime base field; variable-time test oracle."""
    value %= Q
    if value == 0:
        return 0
    if pow(value, (Q - 1) // 2, Q) != 1:
        raise ValueError('generator is not on curve')
    odd, power = Q - 1, 0
    while odd % 2 == 0:
        odd //= 2
        power += 1
    nonresidue = 2
    while pow(nonresidue, (Q - 1) // 2, Q) != Q - 1:
        nonresidue += 1
    c = pow(nonresidue, odd, Q)
    t = pow(value, odd, Q)
    root = pow(value, (odd + 1) // 2, Q)
    while t != 1:
        index, squared = 0, t
        while squared != 1 and index < power:
            squared = squared * squared % Q
            index += 1
        if index == power:
            raise ValueError('invalid square-root state')
        factor = pow(c, 1 << (power - index - 1), Q)
        root = root * factor % Q
        c = factor * factor % Q
        t = t * c % Q
        power = index
    return root


def encode(point):
    x, y = point
    return (y | ((x & 1) << 255)).to_bytes(32, 'little')


def decode_generator(encoded):
    if len(encoded) != 32:
        raise ValueError('wrong generator length')
    raw = int.from_bytes(encoded, 'little')
    y, sign = raw & ((1 << 255) - 1), raw >> 255
    if y >= Q:
        raise ValueError('noncanonical generator')
    x = square_root((y * y - 1) * pow(1 + D * y * y, -1, Q))
    if x & 1 != sign:
        x = -x % Q
    point = (x, y)
    if encode(point) != encoded or point == IDENTITY or multiply(point, R) != IDENTITY:
        raise ValueError('invalid generator subgroup/encoding')
    return point


def lp(value):
    return len(value).to_bytes(4, 'little') + value


def check_storm(log):
    """Check the deterministic TEST-ONLY STORM transcript with integer arithmetic.

    Reconstruct every dealer polynomial from its private test vectors, then
    independently recompute both NIKE paths, the two hashes and all output
    shares. This is finite arithmetic evidence, not a DKG security theorem.
    """
    matches = re.findall(r'^ORBIS_STORM_VECTOR:(.+)$', log, re.M)
    if len(matches) != 1:
        raise ValueError('expected one STORM vector')
    vector = json.loads(matches[0])

    def raw(value):
        if not isinstance(value, list) or len(value) != 32 or any(
                type(item) is not int or not 0 <= item <= 255 for item in value):
            raise ValueError('noncanonical vector bytes')
        return bytes(value)

    def scalar(value):
        number = int.from_bytes(raw(value), 'little')
        if number >= R:
            raise ValueError('noncanonical vector scalar')
        return number

    def equal(actual, expected, role):
        if actual != expected:
            raise ValueError(f'STORM oracle mismatch: {role}')

    context = raw(vector['context'])
    generator = decode_generator(raw(vector['generator']))

    def point(number):
        return encode(multiply(generator, number % R))

    def digest(domain, values):
        transcript = len(domain).to_bytes(4, 'big') + domain + context + b''.join(values)
        return int.from_bytes(hashlib.sha512(transcript).digest(), 'little') % R

    commitments, openings, private = (vector[key] for key in ('commitments', 'openings', 'private_shares'))
    if any(len(items) != 5 for items in (commitments, openings, private)):
        raise ValueError('STORM profile count')
    alphas, slopes, factors, coefficient_bytes = [], [], [], []
    for index, (commitment, opening, shares) in enumerate(zip(commitments, openings, private), 1):
        equal((raw(commitment['context']), commitment['dealer']), (context, index), 'commitment identity')
        equal((raw(opening['context']), opening['participant']), (context, index), 'opening identity')
        if len(shares) != 5 or len(commitment['coefficients']) != 2:
            raise ValueError('STORM polynomial dimensions')
        values = [scalar(share) for share in shares]
        slope, alpha = (values[1] - values[0]) % R, (2 * values[0] - values[1]) % R
        equal(values, [(alpha + slope * participant) % R for participant in range(1, 6)], 'private evaluations')
        expected_coefficients = [point(alpha), point(slope)]
        equal([raw(item) for item in commitment['coefficients']], expected_coefficients, 'Feldman coefficients')
        equal(raw(commitment['alpha_public']), point(alpha), 'alpha public')
        beta = scalar(opening['beta'])
        equal(raw(commitment['beta_public']), point(beta), 'beta public')
        # Independent scalar reconstruction above corresponds to recovery of
        # alpha; valid beta opening and recovered alpha must give the SAME factor.
        factor = encode(multiply(multiply(generator, alpha), beta))
        equal(factor, encode(multiply(multiply(generator, beta), alpha)), 'NIKE recovery')
        factors.append(factor)
        coefficient_bytes.extend(expected_coefficients)
        alphas.append(alpha)
        slopes.append(slope)
    aux = digest(b'orbis-storm-jubjub-fixed5-v1.h2', factors)
    tweak = digest(b'orbis-storm-jubjub-fixed5-v1.h1', coefficient_bytes + [aux.to_bytes(32, 'little')])
    equal(scalar(vector['tweak']), tweak, 'full-set H2/H1 tweak')
    constant, slope = (sum(alphas) + tweak) % R, sum(slopes) % R
    equal(raw(vector['public_key']), point(constant), 'public key')
    equal([raw(item) for item in vector['coefficients']], [point(constant), point(slope)], 'aggregate polynomial')
    expected_shares = [(constant + slope * index) % R for index in range(1, 6)]
    equal([scalar(item) for item in vector['local_shares']], expected_shares, 'private outputs')
    equal([raw(item) for item in vector['verification_shares']], [point(item) for item in expected_shares], 'public shares')
    return {'dealers': 5, 'private_evaluations': 25, 'output_shares': 5,
            'scope': 'one deterministic test transcript; no DKG/authorization/security proof'}


def check(log):
    """Consume exactly one native vector emission and compare full wire bytes."""
    observed = {}
    for role in ['REGISTRY', 'EVIDENCE', 'GENERATOR', 'OPENING']:
        found = re.findall(rf'^ORBIS_THRESHOLD_{role}_HEX=([0-9a-f]+)$', log, re.M)
        if len(found) != 1:
            raise ValueError(f'expected one native {role} vector')
        observed[role] = bytes.fromhex(found[0])
    generator = decode_generator(observed['GENERATOR'])

    def point(scalar):
        return encode(multiply(generator, scalar % R))

    registry = b'STRG' + bytes([1, 1, 5, 2, 1]) + (1).to_bytes(8, 'little') + b'\x01'
    registry += point(11) + point(7)
    for participant in range(1, 6):
        registry += participant.to_bytes(2, 'little') + point(11 + 7 * participant)
    registry_hash = hashlib.blake2b(lp(b'shieldd.orbis.registry.v1') + registry, digest_size=32).digest()
    context, attempt, epk = bytes([42]) * 32, bytes([17]) * 32, point(13)
    evidence = b'STEV' + b'\x01\x01' + context + registry_hash + attempt + epk + b'\x02'
    for participant in [1, 3]:
        secret, nonce = 11 + 7 * participant, 100 + participant
        key, opening, a, b = point(secret), point(13 * secret), point(nonce), point(13 * nonce)
        transcript = (lp(b'shieldd.orbis.capsule-share.v1') + b'\x01' + context + registry_hash +
                      attempt + participant.to_bytes(2, 'little') + observed['GENERATOR'] +
                      key + epk + opening + a + b)
        challenge = int.from_bytes(hashlib.blake2b(transcript, digest_size=64).digest(), 'little') % R
        response = (nonce + challenge * secret) % R
        evidence += participant.to_bytes(2, 'little') + opening + a + b + response.to_bytes(32, 'little')
    expected = {'REGISTRY': registry, 'EVIDENCE': evidence, 'OPENING': point(143)}
    for role, encoded in expected.items():
        if observed[role] != encoded:
            raise ValueError(f'native {role} differs from independent integer/affine fixture')
    return {'scope': 'test-only deterministic threshold vector; no service qualification',
            'oracle': 'Python integer Fr and affine Edwards arithmetic, hashlib Blake2b',
            'sha256': {role.lower(): hashlib.sha256(value).hexdigest()
                       for role, value in observed.items()}}

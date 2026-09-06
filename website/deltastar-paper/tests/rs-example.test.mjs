import test from 'node:test';
import assert from 'node:assert/strict';
import { encode, ORIGINAL, example } from '../lib/rs-example.ts';

// Independently reproduced in Python using sum(a_i*x**i) mod 17 over all 17**4 polynomials.
test('exact finite-field example and exhaustive list counts', () => {
  assert.deepEqual(ORIGINAL, [7, 8, 2, 7, 1, 1, 11, 5]);
  assert.deepEqual(encode([0, 0, 0, 0]), Array(8).fill(0));
  for (const [errors, expected] of [1, 1, 1, 4, 54].entries()) {
    const result = example(errors);
    assert.equal(result.count, expected);
    assert.equal(result.received.filter((v, i) => v !== ORIGINAL[i]).length, errors);
    for (const word of result.samples) {
      assert.ok(word.filter((v, i) => v !== result.received[i]).length <= errors);
    }
  }
  for (const invalid of [-1, 1.5, 5, NaN]) assert.throws(() => example(invalid), RangeError);
});

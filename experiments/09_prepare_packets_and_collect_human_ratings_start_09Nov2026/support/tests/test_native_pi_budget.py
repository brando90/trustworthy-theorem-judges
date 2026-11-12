"""Deterministic native Pi spending guards; no provider/API requests."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
import urllib.error

RUNNER = Path(__file__).resolve().parents[1] / 'scripts/native_packet_generation/pi_runner.py'
SPEC = importlib.util.spec_from_file_location('native_pi_runner', RUNNER)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BudgetTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.budget = MODULE.Budget(Path(self.temp.name) / 'ledger.json')

    def test_count_tokens_omits_prior_billed_thinking(self):
        first = self.budget.reserve(4200, 16384, 'first')
        self.budget.settle(first, {'promptTokenCount': 4200, 'candidatesTokenCount': 29,
                                  'thoughtsTokenCount': 80}, 'fixture', 200, 'STOP')
        second = self.budget.reserve(4518, 16384, 'second')
        self.assertEqual(second['prior_billed_thought_tokens'], 80)
        self.assertEqual(second['input_admission_bound'], 5622)
        self.assertEqual(second['reserved_input_tokens'], 65536)
        self.budget.settle(second, {'promptTokenCount': 4598, 'candidatesTokenCount': 33,
                                   'thoughtsTokenCount': 26}, 'fixture', 200, 'STOP')
        third = self.budget.reserve(4620, 16384, 'third')
        self.assertEqual(third['prior_billed_thought_tokens'], 106)
        self.assertEqual(third['input_admission_bound'], 5750)
        self.budget.settle(third, {'promptTokenCount': 4726, 'candidatesTokenCount': 27,
                                  'thoughtsTokenCount': 17}, 'fixture', 200, 'STOP')
        with self.assertRaisesRegex(ValueError, 'Input token cap'):
            self.budget.reserve(65000, 16384, 'oversize')

    def test_incomplete_response_keeps_reservation_and_stops_new_admission(self):
        row = self.budget.reserve(100, 16384, 'one')
        reservation = row['reserved_usd']
        self.budget.settle(row, {'promptTokenCount': 100, 'candidatesTokenCount': 10},
                           'fixture', 200)
        self.assertEqual(self.budget.data['accounted_usd'], reservation)
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            self.budget.reserve(100, 16384, 'two')

    def test_next_request_rejected_near_seventy_five_cent_cap(self):
        for i in range(7):
            row = self.budget.reserve(1000, 16384, str(i))
            self.budget.settle(row, {'promptTokenCount': 65536, 'candidatesTokenCount': 12200},
                               'fixture', 200, 'STOP')
        self.assertAlmostEqual(self.budget.data['accounted_usd'], .664314)
        self.assertEqual(MODULE.CELL_CAP, .75)
        with self.assertRaisesRegex(ValueError, 'dollar cap'):
            self.budget.reserve(1000, 16384, 'must not admit')
        self.assertLessEqual(self.budget.data['accounted_usd'], MODULE.CELL_CAP)

    def test_request_and_output_caps(self):
        for i in range(40):
            row = self.budget.reserve(1, 1, str(i))
            self.budget.settle(row, {'promptTokenCount': 1, 'candidatesTokenCount': 1},
                               'fixture', 200, 'STOP')
        with self.assertRaisesRegex(ValueError, 'request cap'):
            self.budget.reserve(1, 1, 'forty first')
        fresh = MODULE.Budget(Path(self.temp.name) / 'other.json')
        with self.assertRaisesRegex(ValueError, 'Output token cap'):
            fresh.reserve(1, 16385, 'too many output tokens')

    def test_fake_503_transport_retries_same_request_and_keeps_reservations(self):
        calls, delays = [], []
        response = object()
        request = object()
        def fake_open(req, timeout):
            calls.append((req, timeout))
            if len(calls) < 3:
                raise urllib.error.HTTPError('https://fixture.invalid', 503, 'fixture', {}, None)
            return response
        row, actual = MODULE.open_generation_with_503_recovery(
            self.budget, 100, 16384, b'unchanged payload', request,
            opener=fake_open, sleeper=delays.append)
        self.assertIs(actual, response)
        self.assertEqual(MODULE.PROVIDER_TIMEOUT_SECONDS, 600)
        self.assertEqual(calls, [(request, 600)] * 3)
        self.assertEqual(delays, [5, 15])
        self.assertEqual([r['http503_retry_index'] for r in self.budget.data['requests']], [0, 1, 2])
        self.assertEqual(len({r['payload_sha256'] for r in self.budget.data['requests']}), 1)
        self.budget.settle(row, {'promptTokenCount': 100, 'candidatesTokenCount': 1}, 'fixture', 200, 'STOP')
        self.assertAlmostEqual(self.budget.data['accounted_usd'], 2 * .110592 + .00007875)

    def test_503_recovery_exhausts_after_three_calls_and_honors_dollar_cap(self):
        def fail503(*args, **kwargs):
            raise urllib.error.HTTPError('https://fixture.invalid', 503, 'fixture', {}, None)
        with self.assertRaises(urllib.error.HTTPError):
            MODULE.open_generation_with_503_recovery(self.budget, 100, 16384, b'payload', object(),
                                                     opener=fail503, sleeper=lambda _: None)
        self.assertEqual(len(self.budget.data['requests']), 3)
        self.assertAlmostEqual(self.budget.data['accounted_usd'], 3 * .110592)
        # Keep all three prior failed reservations; the next group cannot
        # exceed the same dollar cap even though each 503 is retryable.
        with self.assertRaises(urllib.error.HTTPError):
            MODULE.open_generation_with_503_recovery(self.budget, 100, 16384, b'payload2', object(),
                                                     opener=fail503, sleeper=lambda _: None)
        with self.assertRaisesRegex(ValueError, 'dollar cap'):
            MODULE.open_generation_with_503_recovery(self.budget, 100, 16384, b'payload3', object(),
                                                     opener=fail503, sleeper=lambda _: None)
        self.assertEqual(len(self.budget.data['requests']), 6)
        self.assertLess(self.budget.data['accounted_usd'], .75)

    def test_transport_recovery_does_not_retry_non_503(self):
        for error in [urllib.error.HTTPError('https://fixture.invalid', 429, 'fixture', {}, None),
                      urllib.error.URLError(TimeoutError())]:
            budget = MODULE.Budget(Path(self.temp.name) / (str(type(error).__name__) + '.json'))
            calls = []
            def fail_other(*args, **kwargs):
                calls.append(1)
                raise error
            with self.assertRaises(type(error)):
                MODULE.open_generation_with_503_recovery(budget, 100, 16384, b'payload', object(),
                                                         opener=fail_other, sleeper=lambda _: None)
            self.assertEqual(calls, [1])
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                budget.reserve(100, 16384, 'another')


if __name__ == '__main__':
    unittest.main()

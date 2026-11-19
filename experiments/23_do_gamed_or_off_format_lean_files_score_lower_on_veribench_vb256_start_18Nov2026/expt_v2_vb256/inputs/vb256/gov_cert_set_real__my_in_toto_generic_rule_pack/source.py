# Source: https://github.com/in-toto/in-toto, in_toto/rulelib.py, commit 94ec6c8fe2ddac968440174781608f50b372bcac, Apache-2.0
# Original language: Python
# Category: 13_gov_cert
# Lines: ~70
"""Pack an in-toto generic artifact rule into its canonical two-token representation."""

from typing import Callable


GENERIC_RULES = {"CREATE", "MODIFY", "DELETE", "ALLOW", "DISALLOW", "REQUIRE"}


def pre_condition(rule_type: str, pattern: str) -> bool:
    """Return whether both arguments are strings and rule_type uppercases to CREATE, MODIFY,
    DELETE, ALLOW, DISALLOW, or REQUIRE. Empty patterns are accepted.
    """
    return isinstance(rule_type, str) and isinstance(pattern, str) and rule_type.upper() in GENERIC_RULES


def my_in_toto_generic_rule_pack(rule_type: str, pattern: str) -> list[str]:
    """Return [rule_type.upper(), pattern], preserving the pattern unchanged. This packs rules such
    as ALLOW *.md into two tokens. Raise AssertionError unless both arguments are strings and
    the uppercased rule type belongs to GENERIC_RULES.
    """
    assert pre_condition(rule_type, pattern), "unsupported generic rule"
    return [rule_type.upper(), pattern]


def check(candidate: Callable[..., list[str]]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    assert candidate('create', 'src/*') == ['CREATE', 'src/*']
    assert candidate('MODIFY', 'bin/app') == ['MODIFY', 'bin/app']
    assert candidate('delete', 'tmp/*') == ['DELETE', 'tmp/*']
    assert candidate('create', '') == ['CREATE', '']
    try:
        candidate('MATCH', '*.py')
    except AssertionError:
        pass
    else:
        raise AssertionError('expected AssertionError')
    return True


if __name__ == "__main__":
    assert check(my_in_toto_generic_rule_pack)
    print(f"All tests passed: {__file__}!")

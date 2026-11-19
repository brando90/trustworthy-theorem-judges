"""
Provides a class for rational numbers (Fractions).

Sourced from Python's standard `fractions` library.
"""

import math
import operator

# -- Pre-condition --

def pre_create(numerator, denominator=None):
    """Return True iff numerator is an int and denominator is either None or an int. Booleans count
    as integers. A zero denominator passes this check.
    """
    if denominator is None:
        return isinstance(numerator, int)
    return isinstance(numerator, int) and isinstance(denominator, int)

# -- Implementation --

class Fraction:
    """This class implements rational numbers. Used e.g. to do exact rational arithmetic without floating-point rounding, such as summing ratios of integers, or to store a quantity like 1/3 exactly in lowest terms."""

    __slots__ = ('_numerator', '_denominator')

    def __new__(cls, numerator=0, denominator=None):
        """Construct a fraction from an integer numerator and an optional integer denominator,
        defaulting to one. Store lowest terms with a positive denominator. Raise TypeError for
        unsupported types and ZeroDivisionError for a zero denominator.
        """
        self = super(Fraction, cls).__new__(cls)

        if denominator is None:
            if isinstance(numerator, int):
                self._numerator = numerator
                self._denominator = 1
                return self
            else:
                 raise TypeError("argument should be an int")
        elif isinstance(numerator, int) and isinstance(denominator, int):
            pass
        else:
            raise TypeError("both arguments should be ints")

        if denominator == 0:
            raise ZeroDivisionError('Fraction(%s, 0)' % numerator)
        
        g = math.gcd(numerator, denominator)
        if denominator < 0:
            g = -g
        self._numerator = numerator // g
        self._denominator = denominator // g
        return self

    @property
    def numerator(self):
        """Return the numerator of the fraction in lowest terms."""
        return self._numerator

    @property
    def denominator(self):
        """Return the positive denominator of the fraction in lowest terms."""
        return self._denominator

    def __repr__(self):
        """Return a string of the form Fraction(num, den)."""
        return 'Fraction(%s, %s)' % (self._numerator, self._denominator)

    def __add__(self, other):
        """Return self + other as a Fraction, or NotImplemented if other is not an int or Fraction."""
        if isinstance(other, int):
            other = Fraction(other)
        if isinstance(other, Fraction):
            return Fraction(self.numerator * other.denominator +
                            self.denominator * other.numerator,
                            self.denominator * other.denominator)
        return NotImplemented

    def __sub__(self, other):
        """Return self - other as a Fraction, or NotImplemented if other is not an int or Fraction."""
        if isinstance(other, int):
            other = Fraction(other)
        if isinstance(other, Fraction):
            return Fraction(self.numerator * other.denominator -
                            self.denominator * other.numerator,
                            self.denominator * other.denominator)
        return NotImplemented

    def __mul__(self, other):
        """Return self * other as a Fraction, or NotImplemented if other is not an int or Fraction."""
        if isinstance(other, int):
            other = Fraction(other)
        if isinstance(other, Fraction):
            return Fraction(self.numerator * other.numerator,
                            self.denominator * other.denominator)
        return NotImplemented

    def __truediv__(self, other):
        """Return self / other as a Fraction. Raise ZeroDivisionError when an int or Fraction
        divisor is zero. Return NotImplemented if other is neither an int nor a Fraction.
        """
        if isinstance(other, int):
            other = Fraction(other)
        if isinstance(other, Fraction):
            return Fraction(self.numerator * other.denominator,
                            self.denominator * other.numerator)
        return NotImplemented

    def __eq__(self, other):
        """Return True iff other equals self; NotImplemented if other is not an int or Fraction."""
        if isinstance(other, int):
            other = Fraction(other)
        if isinstance(other, Fraction):
            return (self.numerator == other.numerator and
                    self.denominator == other.denominator)
        return NotImplemented

    def __lt__(self, other):
        """Return True iff self is less than other; NotImplemented if other is not an int or Fraction."""
        if isinstance(other, int):
            other = Fraction(other)
        if isinstance(other, Fraction):
            return (self.numerator * other.denominator <
                    self.denominator * other.numerator)
        return NotImplemented

# Main class to be verified
benchmark_fraction = Fraction

# -- Tests --

from typing import Type

def check(candidate: Type[Fraction]) -> bool:
    """Run the fixed examples and return True after all checks pass. A mismatched observation
    raises AssertionError.
    """
    f = candidate(8, 6)
    assert (f.numerator, f.denominator) == (4, 3)
    f = candidate(10, -8)
    assert (f.numerator, f.denominator) == (-5, 4)
    f = candidate(0)
    assert (f.numerator, f.denominator) == (0, 1)
    f = candidate(-6, -9)
    assert (f.numerator, f.denominator) == (2, 3)
    f = candidate(12, 3)
    assert (f.numerator, f.denominator) == (4, 1)
    return True

if __name__ == "__main__":
    assert check(benchmark_fraction), f"Failed: {__file__}"
    print("All tests passed.")

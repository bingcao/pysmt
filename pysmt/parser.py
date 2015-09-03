import re
from fractions import Fraction

from pysmt.shortcuts import *


SCANNER = re.compile(r'''
  (\s+) |                      # whitespace
  (-?\d+/\d+) |                  # fractions
  (-?\d+\.\d+) |                  # decimals
  (-?\d+_\d+) |                  # bv
  (-?\d+) |                      # integer literals
  (&)   |                      # conjunction
  (\|)  |                      # disjunction
  (!)   |                      # negation
  (\()   |                     # open parenthesis
  (\))   |                     # closed parenthesis
  (<->)   |                    # iff
  (->)   |                     # implies
  (>=)   |                     # ge
  (<=)   |                     # le
  (>)   |                      # gt
  (<)   |                      # lt
  (=)    |                     # eq
  (\+)    |                     # plus
  (-)    |                     # minus
  (\*)    |                     # times
  (/)    |                     # div
  (\?)    |                     # question
  (:)    |                     # colon
  (False)   |                  # False
  (True)   |                   # True
  (,)   |                      # comma
  ([A-Za-z_][A-Za-z0-9_]*) |   # identifiers
  (.)                          # an error!
''', re.DOTALL | re.VERBOSE)

def UMinus(x):
    if get_type(x).is_int_type():
        return Times(Int(-1), x)
    else:
        return Times(Real(-1), x)

def tokenize_fun(data):
    for match in re.finditer(SCANNER, data):
        (space,
         fraction,
         decimal,
         bv,
         integer,
         conjunction,
         disjunction,
         negation,
         open_par,
         close_par,
         iff,
         implies,
         ge, le, gt, lt, eq,
         plus, minus, times, div,
         question, colon,
         false,
         true,
         comma,
         identifier,
         badchar) = match.groups()
        if space:
            pass # silently skip spaces
        elif fraction:
            yield Constant(Real(Fraction(fraction)))
        elif decimal:
            yield Constant(Real(Fraction(decimal)))
        elif bv:
            v, w = bv.split("_")
            yield Constant(BV(int(v), width=int(w)))
        elif integer:
            yield Constant(Int(int(integer)))
        elif conjunction:
            yield InfixOpAdapter(And, 20)
        elif disjunction:
            yield InfixOpAdapter(Or, 10)
        elif negation:
            yield UnaryOpAdapter(Not, 1)
        elif open_par:
            yield OpenPar()
        elif close_par:
            yield ClosePar()
        elif gt:
            yield InfixOpAdapter(GT, 5)
        elif lt:
            yield InfixOpAdapter(LT, 5)
        elif ge:
            yield InfixOpAdapter(GE, 5)
        elif le:
            yield InfixOpAdapter(LE, 5)
        elif eq:
            yield InfixOpAdapter(Equals, 5)
        elif plus:
            yield InfixOpAdapter(Plus, 5)
        elif minus:
            yield InfixOrUnaryOpAdapter(Minus, UMinus, 5)
        elif times:
            yield InfixOpAdapter(Times, 5)
        elif div:
            yield InfixOpAdapter(Div, 5)
        elif implies:
            yield InfixOpAdapter(Implies, 5)
        elif iff:
            yield InfixOpAdapter(Iff, 5)
        elif question:
            yield ExprIf()
        elif colon:
            yield ExprElse()
        elif false:
            yield Constant(FALSE())
        elif true:
            yield Constant(TRUE())
        elif comma:
            yield ExprComma()
        elif identifier:
            yield Identifier(identifier)
        elif badchar:
            raise SyntaxError("Unexpected input: %s" % badchar)
    yield EndOfInput()


class GrammarSymbol(object):

    def __init__(self):
        self.lbp = 0
        self.tk_type = None # token type name
        self.value = None # used by literals
        self.payload = None

    def nud(self, tokenizer, token):
        raise SyntaxError(
            "Syntax error (%r)." % self
        )

    def led(self, tokenizer, token, left):
        raise SyntaxError(
            "Unknown operator (%r)." % self
        )

class EndOfInput(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)

class Constant(GrammarSymbol):
    def __init__(self, value):
        GrammarSymbol.__init__(self)
        self.value = value

    def nud(self, tokenizer, token):
        return self.value, token

class Identifier(GrammarSymbol):
    def __init__(self, name):
        GrammarSymbol.__init__(self)
        self.value = get_env().formula_manager.get_symbol(name)

    def nud(self, tokenizer, token):
        return self.value, token

class ClosePar(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)

class ExprIf(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 5

    def led(self, tokenizer, token, left):
        cond_ = left
        then_, token = expression(tokenizer, token, self.lbp)
        if type(token) != ExprElse:
            raise SyntaxError("Expected ':'")
        token = next(tokenizer)
        else_, token = expression(tokenizer, token, self.lbp)
        return Ite(cond_, then_, else_), token

class ExprElse(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)

class ExprComma(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)

class OpenPar(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 150

    def nud(self, tokenizer, token):
        r, token = expression(tokenizer, token)
        if type(token) != ClosePar:
            raise SyntaxError("Expected ')'")
        token = next(tokenizer)
        return r, token

    def led(self, tokenizer, token, left):
        # a function call
        fun = left
        params = []
        if type(token) != ClosePar:
            while True:
                r, token = expression(tokenizer, token)
                params.append(r)
                if type(token) != ExprComma:
                    break
                token = next(tokenizer)
        if type(token) != ClosePar:
            print token, params
            raise SyntaxError("Expected ')'")
        token = next(tokenizer)
        return Function(fun, params), token

class InfixOpAdapter(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def led(self, tokenizer, token, left):
        right, token = expression(tokenizer, token, self.lbp)
        return self.operator(left, right), token

class UnaryOpAdapter(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, tokenizer, token):
        right, token = expression(tokenizer, token, self.lbp)
        return self.operator(right), token


class InfixOrUnaryOpAdapter(GrammarSymbol):
    def __init__(self, b_operator, u_operator, b_lbp):
        GrammarSymbol.__init__(self)
        self.b_operator = b_operator
        self.u_operator = u_operator
        self.lbp = b_lbp

    def nud(self, tokenizer, token):
        right, token = expression(tokenizer, token, 0)
        return self.u_operator(right), token

    def led(self, tokenizer, token, left):
        right, token = expression(tokenizer, token, self.lbp)
        return self.b_operator(left, right), token


def expression(tokenizer, token, rbp=0):
    t = token
    token = next(tokenizer)
    left, token = t.nud(tokenizer, token)
    while rbp < token.lbp:
        t = token
        token = next(tokenizer)
        left, token = t.led(tokenizer, token, left)
    return left, token


def parse(data):
    tokenizer = tokenize_fun(data)
    token = next(tokenizer)
    result, _ = expression(tokenizer, token)
    try:
        bd = next(tokenizer)
        raise SyntaxError("bogus data after expression: '%s'" % bd)
    except StopIteration:
        return result


if __name__ == "__main__":
    from pysmt.test.examples import get_example_formulae
    from six.moves import cStringIO

    res = set()
    for (f, validity, satisfiability, logic) in get_example_formulae():
        s = f.serialize()
        print "\nChecking: '%s'" % s
        print list(tokenize_fun(s))
        res = parse(s)
        print res.serialize()
        assert res == f or is_valid(Iff(res, f))

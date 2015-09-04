import re
from fractions import Fraction

from pysmt.shortcuts import *


def UMinusOrBvNeg(x):
    ty = get_type(x)
    if ty.is_int_type():
        return Times(Int(-1), x)
    elif ty.is_real_type():
        return Times(Real(-1), x)
    else:
        return BVNeg(x)

def AndOrBVAnd(l, r):
    if get_type(l).is_bool_type():
        return And(l, r)
    else:
        return BVAnd(l, r)

def OrOrBVOr(l, r):
    if get_type(l).is_bool_type():
        return Or(l, r)
    else:
        return BVOr(l, r)

def NotOrBVNot(x):
    if get_type(x).is_bool_type():
        return Not(x)
    else:
        return BVNot(x)

def PlusOrBVAdd(l, r):
    if get_type(l).is_bv_type():
        return BVAdd(l, r)
    else:
        return Plus(l, r)

def MinusOrBVSub(l, r):
    if get_type(l).is_bv_type():
        return BVSub(l, r)
    else:
        return Minus(l, r)

def TimesOrBVMul(l, r):
    if get_type(l).is_bv_type():
        return BVMul(l, r)
    else:
        return Times(l, r)

def BVHack(op):
    def res(a, b):
        if b.is_constant():
            return op(a, b.constant_value())
        else:
            raise SyntaxError("Constant expected, got '%s'" % b)
    return res


class Lexer(object):
    def __init__(self):
        self.rules = []
        self.rules.append((r"(\s+)", None, False)) # whitespace
        self.rules.append((r"(-?\d+/\d+)", self.real_constant, True)) # fractions
        self.rules.append((r"(-?\d+\.\d+)", self.real_constant, True)) # decimals
        self.rules.append((r"(-?\d+_\d+)", self.bv_constant, True)) # bv
        self.rules.append((r"(-?\d+)", self.int_constant, True)) # integer literals
        self.rules.append((r"(&)", InfixOpAdapter(AndOrBVAnd, 20), False)) # conjunction
        self.rules.append((r"(\|)", InfixOpAdapter(OrOrBVOr, 20), False)) # disjunction
        self.rules.append((r"(!)", UnaryOpAdapter(NotOrBVNot, 1), False)) # negation
        self.rules.append((r"(\()", OpenPar(), False)) # open parenthesis
        self.rules.append((r"(\))", ClosePar(), False)) # closed parenthesis
        self.rules.append((r"(\[)", OpenBrak(), False)) # open parenthesis
        self.rules.append((r"(\])", CloseBrak(), False)) # closed parenthesis
        self.rules.append((r"(<<)", InfixOpAdapter(BVLShl, 5), False)) # iff
        self.rules.append((r"(>>)", InfixOpAdapter(BVLShr, 5), False)) # iff
        self.rules.append((r"(a>>)", InfixOpAdapter(BVAShr, 5), False)) # iff
        self.rules.append((r"(<->)", InfixOpAdapter(Iff, 5), False)) # iff
        self.rules.append((r"(->)", InfixOpAdapter(Implies, 5), False)) # implies
        self.rules.append((r"(u<=)", InfixOpAdapter(BVULE, 5), False)) # bvult
        self.rules.append((r"(u>=)", InfixOpAdapter(BVUGE, 5), False)) # bvult
        self.rules.append((r"(u<)", InfixOpAdapter(BVULT, 5), False)) # bvult
        self.rules.append((r"(u>)", InfixOpAdapter(BVUGT, 5), False)) # bvult
        self.rules.append((r"(s<=)", InfixOpAdapter(BVSLE, 5), False)) # bvslt
        self.rules.append((r"(s>=)", InfixOpAdapter(BVSGE, 5), False)) # bvslt
        self.rules.append((r"(s<)", InfixOpAdapter(BVSLT, 5), False)) # bvslt
        self.rules.append((r"(s>)", InfixOpAdapter(BVSGT, 5), False)) # bvslt
        self.rules.append((r"(>=)", InfixOpAdapter(GE, 5), False)) # ge
        self.rules.append((r"(<=)", InfixOpAdapter(LE, 5), False)) # le
        self.rules.append((r"(>)", InfixOpAdapter(GT, 5), False)) # gt
        self.rules.append((r"(<)", InfixOpAdapter(LT, 5), False)) # lt
        self.rules.append((r"(=)", InfixOpAdapter(Equals, 5), False)) # eq
        self.rules.append((r"(\+)", InfixOpAdapter(PlusOrBVAdd, 5), False)) # plus
        self.rules.append((r"(-)", InfixOrUnaryOpAdapter(MinusOrBVSub, UMinusOrBvNeg, 5), False)) # minus
        self.rules.append((r"(\*)", InfixOpAdapter(TimesOrBVMul, 5), False)) # times
        self.rules.append((r"(u/)", InfixOpAdapter(BVUDiv, 5), False)) # div
        self.rules.append((r"(s/)", InfixOpAdapter(BVSDiv, 5), False)) # div
        self.rules.append((r"(/)", InfixOpAdapter(Div, 5), False)) # div
        self.rules.append((r"(s%)", InfixOpAdapter(BVSRem, 5), False)) # div
        self.rules.append((r"(u%)", InfixOpAdapter(BVURem, 5), False)) # div
        self.rules.append((r"(\?)", ExprIf(), False)) # question
        self.rules.append((r"(::)", InfixOpAdapter(BVConcat, 5), False)) # BVXor
        self.rules.append((r"(:)", ExprElse(), False)) # colon
        self.rules.append((r"(False)", Constant(FALSE()) , False)) # False
        self.rules.append((r"(True)", Constant(TRUE()), False)) # True
        self.rules.append((r"(,)", ExprComma(), False)) # comma
        self.rules.append((r"(\.)", ExprDot(), False)) # dot
        self.rules.append((r"(xor)", InfixOpAdapter(BVXor, 5), False)) # BVXor
        self.rules.append((r"(ROR)", InfixOpAdapter(BVHack(BVRor), 5), False)) # BVXor
        self.rules.append((r"(ROL)", InfixOpAdapter(BVHack(BVRol), 5), False)) # BVXor
        self.rules.append((r"(ZEXT)", InfixOpAdapter(BVHack(BVZExt), 5), False)) # BVXor
        self.rules.append((r"(SEXT)", InfixOpAdapter(BVHack(BVSExt), 5), False)) # BVXor
        self.rules.append((r"(bvcomp)", InfixOpAdapter(BVComp, 5), False)) # BVXor
        self.rules.append((r"(forall)", Quantifier(ForAll, 5), False)) # BVXor
        self.rules.append((r"(exists)", Quantifier(Exists, 5), False)) # BVXor
        self.rules.append((r"(ToReal)", UnaryOpAdapter(ToReal, 100), False)) # BVXor
        self.rules.append((r"\"(.*?)\"", self.identifier, True)) # quoted identifiers
        self.rules.append((r"([A-Za-z_][A-Za-z0-9_]*)", self.identifier, True)) # identifiers
        self.rules.append((r"(.)", self.lexing_error, True)) # input error

        self.scanner = re.compile("|".join(x for x,_,_ in self.rules),
                                  re.DOTALL | re.VERBOSE)
        self.eoi = EndOfInput()

    def real_constant(self, read):
        return Constant(Real(Fraction(read)))

    def bv_constant(self, read):
        v, w = read.split("_")
        return Constant(BV(int(v), width=int(w)))

    def int_constant(self, read):
        return Constant(Int(int(read)))

    def identifier(self, read):
        return Identifier(read)

    def lexing_error(self, read):
        raise SyntaxError("Unexpected input: %s" % read)

    def tokenize(self, data):
        for match in re.finditer(self.scanner, data):
            for idx, capture in enumerate(match.groups()):
                if capture is not None:
                    _, rule, fun = self.rules[idx]
                    if rule is not None:
                        if fun:
                            yield rule(capture)
                        else:
                            yield rule
                    break
        yield self.eoi


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
        if self.value is None:
            raise ValueError("Undefined symbol: '%s'" % name)

    def nud(self, tokenizer, token):
        return self.value, token

class ClosePar(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)

class CloseBrak(GrammarSymbol):
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

class ExprDot(GrammarSymbol):
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
            raise SyntaxError("Expected ')'")
        token = next(tokenizer)
        return Function(fun, params), token

class OpenBrak(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 150

    def led(self, tokenizer, token, left):
        # BVExtract
        bv = left
        start, token = expression(tokenizer, token, self.lbp)
        if type(token) != ExprElse:
            raise SyntaxError("Expected ':'")
        token = next(tokenizer)
        end, token = expression(tokenizer, token, self.lbp)
        if type(token) != CloseBrak:
            raise SyntaxError("Expected ']'")
        token = next(tokenizer)
        return BVExtract(bv, start.constant_value(), end.constant_value()), token


class InfixOpAdapter(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def led(self, tokenizer, token, left):
        right, token = expression(tokenizer, token, self.lbp)
        return self.operator(left, right), token

    def __repr__(self):
        return repr(self.operator)

class UnaryOpAdapter(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, tokenizer, token):
        right, token = expression(tokenizer, token, self.lbp)
        return self.operator(right), token


class Quantifier(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, tokenizer, token):
        qvars = []
        if type(token) != ExprDot:
            while True:
                r, token = expression(tokenizer, token)
                qvars.append(r)
                if type(token) != ExprComma:
                    break
                token = next(tokenizer)
        if type(token) != ExprDot:
            raise SyntaxError("Expected '.'")
        token = next(tokenizer)
        matrix, token = expression(tokenizer, token, self.lbp)
        return self.operator(qvars, matrix),  token

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
    #    tokenizer = tokenize_fun(data)
    tokenizer = Lexer().tokenize(data)
    token = next(tokenizer)
    result, _ = expression(tokenizer, token)
    try:
        bd = next(tokenizer)
        raise SyntaxError("bogus data after expression: '%s'" % bd)
    except StopIteration:
        return result


if __name__ == "__main__":
    from pysmt.test.examples import get_example_formulae

    # for x in "abcdxyz":
    #     Symbol(x)

    # s = raw_input()
    # print "-->",s
    # res = parse(s)
    # print res.serialize()
    # exit(1)

    for (f, validity, satisfiability, logic) in get_example_formulae():
        s = f.serialize()
        print "\nChecking: '%s'" % s
        print list(Lexer().tokenize(s))
        res = parse(s)
        print res.serialize()
        assert res == f or is_valid(Iff(res, f))

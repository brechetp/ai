#!/usr/bin/python2.7
# -*- coding: utf-8 -*-
""" Solutions to practical #4, Techniques in Artificial Intelligence
First-Order Logic
Pierre Bréchet
IMAT: 03672392 """
import re, collections

# 2.1 We start by the lexer (the same one as the practical #3)
# Given an string, we tokenize it according to ASCII tokens
# We use the regular expression to match the tokens 

space = "[ \t\n\r]+"
punctuation = "[\[\]{}(),]" # we want to scatter adjacent punctuation, so no '+'
symbolic = r"[~`!@#$%^&*\-+=|/\\:;<>.?]+"
numeric = "[0-9]+"
alphanumeric = "[A-Za-z0-9_']+"

# We combine all regular expressions except for the spaces 
# which we want to discard 

regexp_str = "(?P<punctuation>{0})|(?P<symbolic>{1})|(?P<numeric>{2})|(?P<alphanumeric>{3})".format(punctuation, symbolic, numeric, alphanumeric)

regexp = re.compile(regexp_str)

def lex (string):
  """ returns the list of ASCII tokens from an input string """
  scatter = regexp.findall(string) # returns a list of tuples with empty ('') entries when the class (e.g. punctuation) is not found and the token otherwise
  res = [filter(lambda x: x != '', t)[0] for t in scatter] #discard the empty entries in the tuples and combine the non-empty ones (tokens) into a list of ASCII tokens
  return res

# 2.2 We need to have a type for term and first-order formulae
# As in practical #3, I've decided tu use Python named tuple
# to mimic OCaml types, but this time I choose to call a 
# constructor for each types of operators
Var = collections.namedtuple('Var', 'string')
Fn = collections.namedtuple('Fn', ['string', 'term_list']) 
term = collections.namedtuple('term', 'val')
# for example
# cos(x+y)^2 --> term(Fn('power', [Fn('+', [Var('x'), Var('y')]), Fn('2', [])]))
# name is here either Var (and value is a string) 
# or Fn (and value is a tuple (string, term list)
# the operator type is accessed by type(x).__name__
R = collections.namedtuple('R', ['string', 'term_list'])
fol = collections.namedtuple('fol', 'R')
# Definition of a formula, with different tuple constructors
Atom = collections.namedtuple('Atom', 'val') # Atom(True|False) will be our True and False
And = collections.namedtuple('And', ['L', 'R']) 
Or = collections.namedtuple('Or', ['L', 'R'])
Imp = collections.namedtuple('Imp', ['L', 'R'])
Iff = collections.namedtuple('Iff', ['L', 'R'])
Forall = collections.namedtuple('Forall', ['string', 'formula'])
Exists = collections.namedtuple('Exists', ['string', 'formula'])
formula = collections.namedtuple('formula', 'val')

Token = collections.namedtuple('Token', ['name', 'value']) 
# maps the ASCII code to the token name
token_map = {
    '<=>': 'IFF',
    '==>': 'IMP',
    '\\/': 'OR', # in order to avoid the escaping character \,
    '/\\': 'AND',# I chose to use & and | instead of /\ and \/
    '~': 'NOT', 
    '(': 'LPAR',
    ')': 'RPAR',
    'true': 'T',
    'false': 'F',
    'exists': 'Exists',
    'forall': 'Forall'
    }

def parse_ginfix(opsym, opupdate, sof, subparser, inp):
    (e1, inp1) = subparser(inp)
    print e1, inp1, inp, opsym
    print "parse_ginfix1 :", inp1
    if inp1:
        if inp1[0] == opsym:
            print "parse_ginfix2 :", inp1
            print 'trouvé'
            return parse_ginfix(opsym, opupdate, lambda x: opupdate(lambda y:sof(y),e1, x), subparser, inp1[1:])
    print "pas trouvé"
    return sof((e1, inp1))


def parse_left_infix(opsym, opcon):
    return lambda x1, y1: parse_ginfix(opsym, lambda(f, e1, e2): opcon(f(e1), e2), lambda x: x, x1, y1)
def parse_right_infix(opsym, opcon):
    return lambda x1, y1: parse_ginfix(opsym, lambda(f, e1, e2): f(opcon(e1, e2)), lambda x: x, x1, y1)
def parse_list(opsym):
    return lambda x1, y1: parse_ginfix(opsym, lambda(f, e1, e2): f(e1) + [e2], lambda x: [x], x1, y1)

def papply(f, (ast, rest)):
    return (f(ast), rest)

def nextin(inp, tok):
    """ returns True iff the name of the first ASCII token in 
    inp is tok """
    return inp != [] and inp[0] == tok

def parse_bracketed(subparser, cbra, inp):
    print "parse_bracketed: ", inp, subparser(inp)
    (ast, rest) = subparser(inp)
    if nextin(rest, cbra):
        return (ast, rest[1:])
    else:
        raise Exception("Closing bracket expected")

def parse_atomic_formula((ifn, afn), vs, inp):
    if inp == []:
        raise Exception("formula expected")
    tok,rest = inp[0], inp[1:]
    if tok == "false":
        return Atom(False), rest
    elif tok == "true":
        return Atom(True), rest
    elif tok == "(":
        try:
            return ifn(vs, input)
        except:
            return parse_bracketed( lambda x: parse_formula((ifn, afn), vs, x), ')', rest)
    elif tok == "~":
        return papply(lambda x: Not(x), parse_atomic_formula((ifn, afn), vs, rest))
    elif tok == "forall":
        x = rest[0]
        return parse_quant((ifn, afn), [x] + vs, lambda x,p: Forall(x, p), x, rest[1:])
    elif tok == "exists":
        x = rest[0]
        return parse_quant((ifn, afn), [x] + vs, lambda x,p: Exists(x, p), x, rest[1:])
    else:
        return afn(vs, inp)
def parse_quant((ifn, afn), vs, qcon, x, inp):
    if inp == []:
        raise Exception("Body of quantified term expected")
    y = inp.pop(0)
    if y == ".":
        return papply(lambda fm: qcon(x, fm), parse_formula((ifn, afn), vs, inp))
    else:
        return papply(lambda fm: qcon(x, fm), parse_quant((ifn, afn), [y] + vs, qcon, y, inp))

def parse_formula((ifn, afn), vs, inp):
    return parse_right_infix("<=>", lambda p, q: Iff(p, q))(lambda x1: parse_right_infix("==>", lambda p, q: Imp(p, q))(lambda x2: parse_right_infix("\\/", lambda p, q: Or(p, q))(lambda x3: parse_right_infix("/\\", lambda p, q: And(p, q))(lambda x :parse_atomic_formula((ifn, afn), vs, x), x3), x2), x1), inp)

def is_const_name(s):
    try:
        float(s)
        return True
    except ValueError:
        return s == ""

def parse_atomic_term(vs, inp):
    if inp == []:
        raise Exception("term expected")
    (tok, rest) = inp[0], inp[1:]
    if tok == '(':
        return parse_bracketed (lambda x: parse_term(vs, x), ')', rest)
    if tok == '-':
        return papply(lambda t: Fn('-', [t]), parse_atomic_term(vs, rest))
    if len(rest) >= 2:
        (tok2, tok3) = rest[0], rest[1]
        if tok2 == '(':
            if tok3 == ')':
                return Fn(tok, []), rest[2:]
            else:
                return papply( lambda args: Fn(tok, args), parse_bracketed(lambda x: parse_list(',')(lambda y: parse_term(vs, y), x), ')', rest[1:]))
    if (is_const_name(tok) and (not tok in vs)):
        return Fn(tok, []), rest
    else:
        return Var(tok), rest

def parse_term(vs, inp):
    return term(parse_right_infix('::', lambda e1, e2: Fn('::', [e1, e2]))(lambda x1: parse_right_infix('+', lambda e1, e2: Fn('+', [e1, e2]))(lambda x2: parse_left_infix('-', lambda e1, e2: Fn('-', [e1, e2]))(lambda x3: parse_right_infix('*', lambda e1, e2: Fn('*', [e1, e2]))(lambda x4: parse_left_infix('/', lambda e1, e2: Fn('/', [e1, e2]))(lambda x5: parse_left_infix('^', lambda e1, e2: Fn('^', [e1, e2]))(lambda x:parse_atomic_term(vs, x), x5), x4), x3), x2), x1), inp))

def parset(inp):
    try:
        return parse_term([], inp)
    except:
        raise

def parse_infix_atom(vs, inp):
    (tm, rest) = parse_term(vs, inp)
    #print tm, rest
    if any([nextin(rest, x) for x in ["=", "<", "<=", ">", ">="]]):
        return papply(lambda tm_prime: Atom(R(rest[0], [tm, tm_prime])), parse_term(vs, rest[1:]))
    else:
        raise Exception("")

def parse_atom(vs, inp):
    try:
        return parse_infix_atom(vs, inp)
    except:
        if len(inp)>= 3:
            if inp[1] == '(' and inp[2] == ')':
                return Atom(R(inp[0], [])), inp[3:]
            if inp[1] == '(':
                return papply(lambda args : Atom(R(inp[0], args)), parse_bracketed(lambda x: parse_list(',')(lambda y: parse_term(vs, y), x), ')', inp[3:]))
        if inp:
            if inp[0] != '(':
                return Atom(R(inp[0], [])), inp[1:]
        raise Exception("parse_atom")

def parse(inp):
    try:
        return parse_formula((lambda x,y: parse_infix_atom(x, y), lambda x,y: parse_atom(x, y)), [], inp)
    except:
        raise
default_parser = parse
secondary_parser = parset




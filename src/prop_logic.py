#!/usr/bin/python2.7
# -*- coding: utf-8 -*-
""" Solutions to practical #3, Techniques in Artificial Intelligence
Propositional Logic
Pierre Bréchet
IMAT: 03672392 """
import re, collections

# 2.1 We start by the lexer
# Given an string, we tokenize it according to ASCII tokens
# We use the regular expression to match the tokens 

space = "[ \t\n\r]+"
punctuation = "[\[\]{}(),]" # we want to scatter adjacent punctuation, so no '+'
symbolic = "[~`!@#$%^&*\-+=|\\:;<>.?/]+"
numeric = "[0-9]+"
alphanumeric = "[A-Za-z0-9_']+"

# We combine all regular expressions except for the spaces 
# which we want to discard 

regexp_str = "(?P<punctuation>{0})|(?P<symbolic>{1})|(?P<numeric>{2})|(?P<alphanumeric>{3})".format(punctuation, symbolic, numeric, alphanumeric)

regexp = re.compile(regexp_str)

def lex (string):
  """ returns the list of tokens from an input string """
  scatter = regexp.findall(string) # returns a list of tuples with empty ('') entries when the class (e.g. punctuation) is not found and the token otherwise
  res = [filter(lambda x: x != '', t)[0] for t in scatter] #discard the empty entries in the tuples and combine the non-empty ones (tokens) into a list of ASCII tokens
  return res

# Tokens used in first order logic formulas (tuple type)
Token = collections.namedtuple('Token', ['name', 'value']) 
# maps the ASCII code to the token name
token_map = {
    '<=>': 'IFF',
    '==>': 'IMP',
    '|': 'OR', # in order to avoid the escaping character \,
    '&': 'AND',# I chose to use & and | instead of /\ and \/
    '~': 'NOT', 
    '(': 'LPAR',
    ')': 'RPAR',
    'true': 'T',
    'false': 'F'
    }
# defining the grammar

"""
We define a grammar respecting the precedence rules
and the right-recursive fashion

iff --> impli IFF iff | impli
impli --> or IMP impli | or
or --> and OR or | or
and --> not AND and | not
not --> NOT atom | atom
atom --> ATOM | '(' iff ')' | T | F

"""
# code for the parser
# Formula is the recursive type in which we parse the expression, the type is one of ATOM, NOT, AND, OR, IMP, IFF and the value is either the value of the ATOM of the operands (in tuple) of the operator.
Formula = collections.namedtuple('Formula', ['type', 'value'])

# we first write the function to parse the word atom
# atom --> ATOM | LPAR iff RPAR
def parse_atom(i):
  if not i: # the expression is missing an operand
    raise Exception('Expected an expression at end of input')
  tok = i.pop(0) # take the first token in the list
  if tok.name == 'ATOM' or tok.name == 'T' or tok.name == 'F':
    # if we have a terminating symbol
    # we return  the new constructed formula and the rest of the tokens to be parsed
    return Formula(tok.name, tok.value), i
  if tok.name == 'LPAR': # if the parenthesis are open
    e2,i2 = parse_iff(i) # we look for an iff word
    if i2:
      if i2.pop(0).name == 'RPAR':
        return e2,i2 # we return the parsed iff clause
    raise Exception('Expected closing bracket')

# same thing for parsing the not clauses
# not --> NOT atom | atom

def parse_not(i):
  if not i: # the expression is missing an operand
    raise Exception('Expected an expression')
  tok = i[0]
  if tok.name == 'NOT': # clause of the form NOT atom
    e2, i2 = parse_atom(i[1:]) # we parse the atom
    return Formula('NOT', e2), i2 # and return the newly constructed NOT formula
  else:
    return parse_atom(i) # clause of the form atom

# same thing for and clauses
# and --> not AND and | not
def parse_and(i):
  e1, i1 = parse_not(i) # look for a not clause
  if i1:
    if i1[0].name == 'AND': # if we have the AND conjunction
      e2, i2 = parse_and(i1[1:]) # we have to find the other and clause on the right
      return Formula('AND', (e1, e2)), i2 # we return the newly constructed 
                                          # AND conjunction
  return e1, i1 # else we return the not parsed expression

# the same thing applies to the operators with two operands OR, IMP and IFF
# or --> and OR or | and
def parse_or(i):
  e1, i1 = parse_and(i)
  if i1:
    if i1[0].name == 'OR':
      e2, i2 = parse_or(i1[1:])
      return Formula('OR', (e1, e2)), i2
  return e1, i1

# imp --> or IMP imp | or
def parse_imp(i):
  e1, i1 = parse_or(i)
  if i1:
    if i1[0].name == 'IMP':
      e2, i2 = parse_imp(i1[1:])
      return Formula('IMP', (e1, e2)), i2
  return e1, i1

# iff --> imp IFF iff | imp
def parse_iff(i):
  e1, i1 = parse_imp(i)
  if i1:
    if i1[0].name == 'IFF':
      e2, i2 = parse_iff(i1[1:])
      return Formula('IFF', (e1, e2)), i2
  return e1, i1

# finally, we wrap up the parser into the parser function
# which checks if the list is empty and no error occurs

def parser(string):
  """ Parses an fol expression given as a string """ 
#1 we tokenize the expression, thanks to the lexer and the Token constructor
# the names are mapped thanks to the token_map dictionary
  tokens = [Token(token_map.get(x, 'ATOM'), x) for x in lex(string)]
  try:
    (e, i) = parse_iff(tokens)
    if not i:
      return e
    else:
      raise Exception('Unparsed input')
  except:
    raise

def eval_formula(formula, valuation):
  """ evaluates the formula according to the valuation """
# recursively evaluates the formula according to the clause formula.name
  return eval_switch[formula[0]](formula.value, valuation)
# switch case

def eval_t(value, valuation):
  return True

def eval_f(value, valuation):
  return False

def eval_atom(value, valuation):
  # simply read the valuation of the atom (valuation is a dict)
  try:
    return valuation[value]
  except:
    print "The valuation is not total"
    raise
# the rest are the implementation of the logical operators
# we recursively dig into the formula 
def eval_not(value, valuation):
  return not eval_formula(value, valuation)

def eval_and(value, valuation):
  return eval_formula(value[0], valuation) and eval_formula(value[1], valuation)

def eval_or(value, valuation):
  return eval_formula(value[0], valuation) or eval_formula(value[1], valuation)

def eval_imp(value, valuation):
  return (not eval_formula(value[0], valuation)) or eval_formula(value[1], valuation)

def eval_iff(value, valuation):
  return (eval_formula(value[0], valuation) == eval_formula(value[1], valuation))

# defines the different auxiliaries functions
eval_switch = {
    'T': eval_t,
    'F': eval_f,
    'ATOM' : eval_atom,
    'NOT' : eval_not,
    'AND' : eval_and,
    'OR': eval_or,
    'IMP': eval_imp,
    'IFF': eval_iff
    }

def atoms(formula):
  """ returns the set of all the atoms in the formula """
  if formula[0] == 'ATOM':
    return set([formula.value])
  elif formula[0] == 'NOT':
    return atoms(formula.value)
  elif not(formula[0] == 'T' or formula[0] == 'F'): # two-operands operators
    # returns the union of the two sets of atoms
    return atoms(formula.value[0]) | atoms(formula.value[1])
  else: # for 'T' and 'F' types
    return set()

def onallvaluations(formula):
  atom_set = atoms(formula)
  for val in val_gen(atom_set): # we use the valuation generator
    if not eval_formula(formula, val): # we break if one valuation evaluates to false
      return False
  return True

def val_gen(atom_set):
  """ generates all valuations from a given atom set """
  N = len(atom_set) # the number of atoms
  for p in range(0, 2** N): 
    p_bin = list(bin(p)[2:].zfill(N)) # binary representation of p with N numbers
    val = {key: value=='1' for (key,value) in zip(atom_set, p_bin)} # we construct a dictionary with values for each key (atom) depending on the bit of p
    yield val

def tautology(formula):
  """ returns if a formula is a tautology """
  return onallvaluations(formula)

def unsatisfiable(formula):
  return tautology(Formula('NOT', formula))

def satisfiable(formula):
  return not unsatisfiable(formula)

def entails(f1, f2):
  # f1 |= f2 iff f1 => f2 is a tautology
  return tautology(Formula('IMP', (f1, f2)))


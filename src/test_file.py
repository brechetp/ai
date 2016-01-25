#!/usr/bin/python2.7
# -*- coding: utf-8 -*-
""" Test file for the assignment #3
Pierre Bréchet
IMAT: 03672392 """

import prop_logic


# 4. Exercise

print "4.1.1"
print "False |= True : " + str(prop_logic.entails(prop_logic.parser("false"), prop_logic.parser("true")))

print "4.1.2"
print "True |= False : " + str(prop_logic.entails(prop_logic.parser("true"), prop_logic.parser("false")))

print "4.1.3"
print "(A /\ B) |= (A <=> B) : " + str(prop_logic.entails(prop_logic.parser("a & b"), prop_logic.parser("a <=> b")))

print "4.1.4"
print "(A <=> B) |= (A \/ B) : " + str(prop_logic.entails(prop_logic.parser("a <=> b"), prop_logic.parser("a | b")))

print "4.1.5"
print "(A <=> B) |= (~A \/ B) : " + str(prop_logic.entails(prop_logic.parser("a <=> b"), prop_logic.parser("~a | b")))

print "\n** 4.2.2 **\n"
expressions = ['Smoke ==> Smoke', '(Smoke ==> Fire) ==> (~Smoke ==> ~Fire)', 'Smoke | Fire | ~Fire', '(Fire ==> Smoke ) & Fire & ~Smoke']
tests = {
    ' is a tautology: ': prop_logic.tautology, 
    ' is satisfiable: ': prop_logic.satisfiable,
    ' is unsatisfiable: ': prop_logic.unsatisfiable
    }
for expr in expressions:
  formula = prop_logic.parser(expr)
  for t in tests:
    print expr +t+ str(tests[t](formula))

print "\n ** 4.3 ** \n"
b_formula = prop_logic.parser("b <=> (a <=> ~a)")
print "bsays: "
print b_formula
c_formula = prop_logic.parser("c <=> ~b")
print "csays: "
print c_formula 

kb = prop_logic.Formula('AND', (b_formula, c_formula)) # the knowledge base
print "A is a knight: " + str(prop_logic.entails(kb, prop_logic.parser('a')))
print "A is a knave: " + str(prop_logic.entails(kb, prop_logic.parser('~a')))
print "B is a knight: " + str(prop_logic.entails(kb, prop_logic.parser('b')))
print "B is a knave: " + str(prop_logic.entails(kb, prop_logic.parser('~b')))
print "C is a knight: " + str(prop_logic.entails(kb, prop_logic.parser('c')))
print "C is a knave: " + str(prop_logic.entails(kb, prop_logic.parser('~c')))



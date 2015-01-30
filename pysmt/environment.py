#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
"""
The Environment is a key structure in pySMT. It contains multiple
singleton objects that are used throughout the system, such as the
FormulaManager, Simplifier, HRSerializer, SimpleTypeChecker.

A global environment is defined in shortcuts.py
"""

import pysmt.simplifier
import pysmt.printers
import pysmt.substituter
import pysmt.type_checker
import pysmt.formula
import pysmt.factory
import pysmt.shortcuts
import pysmt.decorators

class Environment(object):
    FormulaManagerClass = pysmt.formula.FormulaManager

    def __init__(self):
        self._stc = pysmt.type_checker.SimpleTypeChecker(self)
        self._formula_manager = self.FormulaManagerClass(self)
        # NOTE: Both Simplifier and Substituter keep an internal copy
        # of the Formula Manager
        self._simplifier = pysmt.simplifier.Simplifier(self)
        self._substituter = pysmt.substituter.Substituter(self)
        self._serializer = pysmt.printers.HRSerializer(self)
        self._qfo = pysmt.type_checker.QuantifierOracle(self)

        self._factory = None
        # Configurations
        self.enable_infix_notation = False


    @property
    def formula_manager(self):
        return self._formula_manager

    @property
    def simplifier(self):
        return self._simplifier

    @property
    def serializer(self):
        return self._serializer

    @property
    def substituter(self):
        return self._substituter

    @property
    def stc(self):
        """ Get the Simple Type Checker """
        return self._stc

    @property
    def qfo(self):
        """ Get the Quantifier Oracle """
        return self._qfo

    @property
    def factory(self):
        if self._factory is None:
            self._factory = pysmt.factory.Factory(self)
        return self._factory

    def __enter__(self):
        """Entering a Context """
        pysmt.shortcuts.push_env(self)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Remove environment from global stack."""
        pysmt.shortcuts.pop_env()

# EOC Environment



class TypeUnsafeEnvironment(Environment):
    FormulaManagerClass = pysmt.formula.TypeUnsafeFormulaManager

#EOC TypeUnsafeFormulaManager
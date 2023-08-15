#! /usr/bin/env python3

import sys
import math
import os.path
import re
import textwrap
import optparse
import xml.parsers.expat
import collections
import locale
import json
import fnmatch


########################################################################
# Model


MULTIPLICATION_SIGN = chr(0xd7)


def times(x):
    return "%u%s" % (x, MULTIPLICATION_SIGN)

def percentage(p):
    return "%.02f%%" % (p*100.0,)

def add(a, b):
    return a + b

def fail(a, b):
    assert False


tol = 2 ** -23

def ratio(numerator, denominator):
    try:
        ratio = float(numerator)/float(denominator)
    except ZeroDivisionError:
        # 0/0 is undefined, but 1.0 yields more useful results
        return 1.0
    if ratio < 0.0:
        if ratio < -tol:
            sys.stderr.write('warning: negative ratio (%s/%s)\n' % (numerator, denominator))
        return 0.0
    if ratio > 1.0:
        if ratio > 1.0 + tol:
            sys.stderr.write('warning: ratio greater than one (%s/%s)\n' % (numerator, denominator))
        return 1.0
    return ratio


def sorted_iteritems(d):
    # Used mostly for result reproducibility (while testing.)
    keys = list(d.keys())
    keys.sort()
    for key in keys:
        value = d[key]
        yield key, value

class UndefinedEvent(Exception):
    """Raised when attempting to get an event which is undefined."""

    def __init__(self, event):
        Exception.__init__(self)
        self.event = event

    def __str__(self):
        return 'unspecified event %s' % self.event.name


class Event(object):
    """Describe a kind of event, and its basic operations."""

    def __init__(self, name, null, aggregator, formatter = str):
        self.name = name
        self._null = null
        self._aggregator = aggregator
        self._formatter = formatter

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return self is other

    def __hash__(self):
        return id(self)

    def null(self):
        return self._null

    def aggregate(self, val1, val2):
        """Aggregate two event values."""
        assert val1 is not None
        assert val2 is not None
        return self._aggregator(val1, val2)

    def format(self, val):
        """Format an event value."""
        assert val is not None
        return self._formatter(val)


CALLS = Event("Calls", 0, add, times)
SAMPLES = Event("Samples", 0, add, times)
SAMPLES2 = Event("Samples", 0, add, times)

# Count of samples where a given function was either executing or on the stack.
# This is used to calculate the total time ratio according to the
# straightforward method described in Mike Dunlavey's answer to
# stackoverflow.com/questions/1777556/alternatives-to-gprof, item 4 (the myth
# "that recursion is a tricky confusing issue"), last edited 2012-08-30: it's
# just the ratio of TOTAL_SAMPLES over the number of samples in the profile.
#
# Used only when totalMethod == callstacks
TOTAL_SAMPLES = Event("Samples", 0, add, times)

TIME = Event("Self Time", 0.0, add, lambda x: str(x))
KIDS_TIME = Event("Descendants Time", 0.0, add, lambda x: str(x))
TIME_RATIO = Event("Time ratio", 0.0, add, lambda x: percentage(x))
TOTAL_TIME = Event("Cumulative time", 0.0, fail, lambda x: str(x))
TOTAL_TIME_RATIO = Event("Cumulative time ratio", 0.0, fail, lambda x: percentage(x))

labels = {
    'self-time': TIME,
    'kids-time': KIDS_TIME,
    'self-time-percentage': TIME_RATIO,
    'total-time': TOTAL_TIME,
    'total-time-percentage': TOTAL_TIME_RATIO,
}
defaultLabelNames = ['total-time-percentage', 'self-time-percentage', 'total-time', 'total-time-percentage', 'kida-time']

totalMethod = 'callratios'


class Object(object):
    """Base class for all objects in profile which can store events."""

    def __init__(self, events=None):
        if events is None:
            self.events = {}
        else:
            self.events = events

    def __hash__(self):
        return id(self)

    def __eq__(self, other):
        return self is other

    def __lt__(self, other):
        return id(self) < id(other)

    def __contains__(self, event):
        return event in self.events

    def __getitem__(self, event):
        try:
            return self.events[event]
        except KeyError:
            raise UndefinedEvent(event)

    def __setitem__(self, event, value):
        if value is None:
            if event in self.events:
                del self.events[event]
        else:
            self.events[event] = value


class Call(Object):
    """A call between functions.

    There should be at most one call object for every pair of functions.
    """

    def __init__(self, callee_id):
        Object.__init__(self)
        self.callee_id = callee_id
        self.ratio = None
        self.weight = None


class Function(Object):
    """A function."""

    def __init__(self, id, name):
        Object.__init__(self)
        self.id = id
        self.name = name
        self.module = None
        self.process = None
        self.calls = {}
        self.called = None
        self.weight = None
        self.cycle = None
        self.filename = None

    def add_call(self, call):
        if call.callee_id in self.calls:
            sys.stderr.write('warning: overwriting call from function %s to %s\n' % (str(self.id), str(call.callee_id)))
        self.calls[call.callee_id] = call

    def get_call(self, callee_id):
        if not callee_id in self.calls:
            call = Call(callee_id)
            call[SAMPLES] = 0
            call[SAMPLES2] = 0
            call[CALLS] = 0
            self.calls[callee_id] = call
        return self.calls[callee_id]

    _parenthesis_re = re.compile(r'\([^()]*\)')
    _angles_re = re.compile(r'<[^<>]*>')
    _const_re = re.compile(r'\s+const$')

    def stripped_name(self):
        """Remove extraneous information from C++ demangled function names."""

        name = self.name

        # Strip function parameters from name by recursively removing paired parenthesis
        while True:
            name, n = self._parenthesis_re.subn('', name)
            if not n:
                break

        # Strip const qualifier
        name = self._const_re.sub('', name)

        # Strip template parameters from name by recursively removing paired angles
        while True:
            name, n = self._angles_re.subn('', name)
            if not n:
                break

        return name

    # TODO: write utility functions

    def __repr__(self):
        return self.name

    def dump(self, sep1=",\n\t", sep2=":=", sep3="\n"):
        """ Returns as a string all information available in this Function object
            separators sep1:between entries
                       sep2:between attribute name and value,
                       sep3: inserted at end
        """
        return sep1.join(sep2.join([k,str(v)]) for (k,v) in sorted(self.__dict__.items())) + sep3


class Cycle(Object):
    """A cycle made from recursive function calls."""

    def __init__(self, id, name):
        Object.__init__(self)
        self.id = id
        self.name = name
        self.functions = set()

    def add_function(self, function):
        assert function not in self.functions
        self.functions.add(function)
        if function.cycle is not None:
            for other in function.cycle.functions:
                if function not in self.functions:
                    self.add_function(other)
        function.cycle = self


class Profile(Object):
    """The whole profile."""

    def __init__(self):
        Object.__init__(self)
        self.functions = {}
        self.cycles = []

    def add_function(self, function):
        if function.id in self.functions:
            sys.stderr.write('warning: overwriting function %s (id %s)\n' % (function.name, str(function.id)))
        self.functions[function.id] = function

    def add_cycle(self, cycle):
        self.cycles.append(cycle)

    def validate(self):
        """Validate the edges."""

        for function in self.functions.values():
            for callee_id in list(function.calls.keys()):
                assert function.calls[callee_id].callee_id == callee_id
                if callee_id not in self.functions:
                    sys.stderr.write('warning: call to undefined function %s from function %s\n' % (str(callee_id), function.name))
                    del function.calls[callee_id]

    def find_cycles(self):
        """Find cycles using Tarjan's strongly connected components algorithm."""

        # Apply the Tarjan's algorithm successively until all functions are visited
        stack = []
        data = {}
        order = 0
        for function in self.functions.values():
            order = self._tarjan(function, order, stack, data)
        cycles = []
        for function in self.functions.values():
            if function.cycle is not None and function.cycle not in cycles:
                cycles.append(function.cycle)
        self.cycles = cycles
        if 0:
            for cycle in cycles:
                sys.stderr.write("Cycle:\n")
                for member in cycle.functions:
                    sys.stderr.write("\tFunction %s\n" % member.name)

    def prune_root(self, roots, depth=-1):
        visited = set()
        frontier = set([(root_node, depth) for root_node in roots])
        while len(frontier) > 0:
            node, node_depth = frontier.pop()
            visited.add(node)
            if node_depth == 0:
                continue
            f = self.functions[node]
            newNodes = set(f.calls.keys()) - visited
            frontier = frontier.union({(new_node, node_depth - 1) for new_node in newNodes})
        subtreeFunctions = {}
        for n in visited:
            f = self.functions[n]
            newCalls = {}
            for c in f.calls.keys():
                if c in visited:
                    newCalls[c] = f.calls[c]
            f.calls = newCalls
            subtreeFunctions[n] = f
        self.functions = subtreeFunctions

    def prune_leaf(self, leafs, depth=-1):
        edgesUp = collections.defaultdict(set)
        for f in self.functions.keys():
            for n in self.functions[f].calls.keys():
                edgesUp[n].add(f)
        # build the tree up
        visited = set()
        frontier = set([(leaf_node, depth) for leaf_node in leafs])
        while len(frontier) > 0:
            node, node_depth = frontier.pop()
            visited.add(node)
            if node_depth == 0:
                continue
            newNodes = edgesUp[node] - visited
            frontier = frontier.union({(new_node, node_depth - 1) for new_node in newNodes})
        downTree = set(self.functions.keys())
        upTree = visited
        path = downTree.intersection(upTree)
        pathFunctions = {}
        for n in path:
            f = self.functions[n]
            newCalls = {}
            for c in f.calls.keys():
                if c in path:
                    newCalls[c] = f.calls[c]
            f.calls = newCalls
            pathFunctions[n] = f
        self.functions = pathFunctions

    def getFunctionIds(self, funcName):
        function_names = {v.name: k for (k, v) in self.functions.items()}
        return [function_names[name] for name in fnmatch.filter(function_names.keys(), funcName)]

    def getFunctionId(self, funcName):
        for f in self.functions:
            if self.functions[f].name == funcName:
                return f
        return False

    def printFunctionIds(self, selector=None, file=sys.stderr):
        """ Print to file function entries selected by fnmatch.fnmatch like in
            method getFunctionIds, with following extensions:
             - selector starts with "%": dump all information available
             - selector is '+' or '-': select all function entries
        """
        if selector is None or selector in ("+", "*"):
            v = ",\n".join(("%s:\t%s" % (kf,self.functions[kf].name)
                            for kf in self.functions.keys()))
        else:
            if selector[0]=="%":
                selector=selector[1:]
                function_info={k:v for (k,v)
                               in self.functions.items()
                               if fnmatch.fnmatch(v.name,selector)}
                v = ",\n".join( ("%s\t({k})\t(%s)::\n\t%s" % (v.name,type(v),v.dump())
                                 for (k,v) in function_info.items()
                                  ))

            else:
                function_names = (v.name for v in self.functions.values())
                v = ",\n".join( ( nm for nm in fnmatch.filter(function_names,selector )))

        file.write(v+"\n")
        file.flush()

    class _TarjanData:
        def __init__(self, order):
            self.order = order
            self.lowlink = order
            self.onstack = False

    def _tarjan(self, function, order, stack, data):
        """Tarjan's strongly connected components algorithm.

        See also:
        - http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm
        """

        try:
            func_data = data[function.id]
            return order
        except KeyError:
            func_data = self._TarjanData(order)
            data[function.id] = func_data
        order += 1
        pos = len(stack)
        stack.append(function)
        func_data.onstack = True
        for call in function.calls.values():
            try:
                callee_data = data[call.callee_id]
                if callee_data.onstack:
                    func_data.lowlink = min(func_data.lowlink, callee_data.order)
            except KeyError:
                callee = self.functions[call.callee_id]
                order = self._tarjan(callee, order, stack, data)
                callee_data = data[call.callee_id]
                func_data.lowlink = min(func_data.lowlink, callee_data.lowlink)
        if func_data.lowlink == func_data.order:
            # Strongly connected component found
            members = stack[pos:]
            del stack[pos:]
            if len(members) > 1:
                cycle = Cycle()
                for member in members:
                    cycle.add_function(member)
                    data[member.id].onstack = False
            else:
                for member in members:
                    data[member.id].onstack = False
        return order

    def call_ratios(self, event):
        # Aggregate for incoming calls
        cycle_totals = {}
        for cycle in self.cycles:
            cycle_totals[cycle] = 0.0
        function_totals = {}
        for function in self.functions.values():
            function_totals[function] = 0.0

        # Pass 1:  function_total gets the sum of call[event] for all
        #          incoming arrows.  Same for cycle_total for all arrows
        #          that are coming into the *cycle* but are not part of it.
        for function in self.functions.values():
            for call in function.calls.values():
                if call.callee_id != function.id:
                    callee = self.functions[call.callee_id]
                    if event in call.events:
                        function_totals[callee] += call[event]
                        if callee.cycle is not None and callee.cycle is not function.cycle:
                            cycle_totals[callee.cycle] += call[event]
                    else:
                        sys.stderr.write("call_ratios: No data for " + function.name + " call to " + callee.name + "\n")

        # Pass 2:  Compute the ratios.  Each call[event] is scaled by the
        #          function_total of the callee.  Calls into cycles use the
        #          cycle_total, but not calls within cycles.
        for function in self.functions.values():
            for call in function.calls.values():
                assert call.ratio is None
                if call.callee_id != function.id:
                    callee = self.functions[call.callee_id]
                    if event in call.events:
                        if callee.cycle is not None and callee.cycle is not function.cycle:
                            total = cycle_totals[callee.cycle]
                        else:
                            total = function_totals[callee]
                        call.ratio = ratio(call[event], total)
                    else:
                        # Warnings here would only repeat those issued above.
                        call.ratio = 0.0

    def integrate(self, outevent, inevent):
        """Propagate function time ratio along the function calls.

        Must be called after finding the cycles.

        See also:
        - http://citeseer.ist.psu.edu/graham82gprof.html
        """

        # Sanity checking
        assert outevent not in self
        for function in self.functions.values():
            assert outevent not in function
            assert inevent in function
            for call in function.calls.values():
                assert outevent not in call
                if call.callee_id != function.id:
                    assert call.ratio is not None

        # Aggregate the input for each cycle
        for cycle in self.cycles:
            total = inevent.null()
            for function in self.functions.values():
                total = inevent.aggregate(total, function[inevent])
            self[inevent] = total

        # Integrate along the edges
        total = inevent.null()
        for function in self.functions.values():
            total = inevent.aggregate(total, function[inevent])
            self._integrate_function(function, outevent, inevent)
        self[outevent] = total

    def _integrate_function(self, function, outevent, inevent):
        if function.cycle is not None:
            return self._integrate_cycle(function.cycle, outevent, inevent)
        else:
            if outevent not in function:
                total = function[inevent]
                for call in function.calls.values():
                    if call.callee_id != function.id:
                        total += self._integrate_call(call, outevent, inevent)
                function[outevent] = total
            return function[outevent]

    def _integrate_call(self, call, outevent, inevent):
        assert outevent not in call
        assert call.ratio is not None
        callee = self.functions[call.callee_id]
        subtotal = call.ratio *self._integrate_function(callee, outevent, inevent)
        call[outevent] = subtotal
        return subtotal

    def _integrate_cycle(self, cycle, outevent, inevent):
        if outevent not in cycle:

            # Compute the outevent for the whole cycle
            total = inevent.null()
            for member in cycle.functions:
                subtotal = member[inevent]
                for call in member.calls.values():
                    callee = self.functions[call.callee_id]
                    if callee.cycle is not cycle:
                        subtotal += self._integrate_call(call, outevent, inevent)
                total += subtotal
            cycle[outevent] = total

            # Compute the time propagated to callers of this cycle
            callees = {}
            for function in self.functions.values():
                if function.cycle is not cycle:
                    for call in function.calls.values():
                        callee = self.functions[call.callee_id]
                        if callee.cycle is cycle:
                            try:
                                callees[callee] += call.ratio
                            except KeyError:
                                callees[callee] = call.ratio

            for member in cycle.functions:
                member[outevent] = outevent.null()

            for callee, call_ratio in callees.items():
                ranks = {}
                call_ratios = {}
                partials = {}
                self._rank_cycle_function(cycle, callee, ranks)
                self._call_ratios_cycle(cycle, callee, ranks, call_ratios, set())
                partial = self._integrate_cycle_function(cycle, callee, call_ratio, partials, ranks, call_ratios, outevent, inevent)

                # Ensure `partial == max(partials.values())`, but with round-off tolerance
                max_partial = max(partials.values())
                assert abs(partial - max_partial) <= 1e-7*max_partial

                assert abs(call_ratio*total - partial) <= 0.001*call_ratio*total

        return cycle[outevent]

    def _rank_cycle_function(self, cycle, function, ranks):
        """Dijkstra's shortest paths algorithm.

        See also:
        - http://en.wikipedia.org/wiki/Dijkstra's_algorithm
        """

        import heapq
        Q = []
        Qd = {}
        p = {}
        visited = set([function])

        ranks[function] = 0
        for call in function.calls.values():
            if call.callee_id != function.id:
                callee = self.functions[call.callee_id]
                if callee.cycle is cycle:
                    ranks[callee] = 1
                    item = [ranks[callee], function, callee]
                    heapq.heappush(Q, item)
                    Qd[callee] = item

        while Q:
            cost, parent, member = heapq.heappop(Q)
            if member not in visited:
                p[member]= parent
                visited.add(member)
                for call in member.calls.values():
                    if call.callee_id != member.id:
                        callee = self.functions[call.callee_id]
                        if callee.cycle is cycle:
                            member_rank = ranks[member]
                            rank = ranks.get(callee)
                            if rank is not None:
                                if rank > 1 + member_rank:
                                    rank = 1 + member_rank
                                    ranks[callee] = rank
                                    Qd_callee = Qd[callee]
                                    Qd_callee[0] = rank
                                    Qd_callee[1] = member
                                    heapq._siftdown(Q, 0, Q.index(Qd_callee))
                            else:
                                rank = 1 + member_rank
                                ranks[callee] = rank
                                item = [rank, member, callee]
                                heapq.heappush(Q, item)
                                Qd[callee] = item

    def _call_ratios_cycle(self, cycle, function, ranks, call_ratios, visited):
        if function not in visited:
            visited.add(function)
            for call in function.calls.values():
                if call.callee_id != function.id:
                    callee = self.functions[call.callee_id]
                    if callee.cycle is cycle:
                        if ranks[callee] > ranks[function]:
                            call_ratios[callee] = call_ratios.get(callee, 0.0) + call.ratio
                            self._call_ratios_cycle(cycle, callee, ranks, call_ratios, visited)

    def _integrate_cycle_function(self, cycle, function, partial_ratio, partials, ranks, call_ratios, outevent, inevent):
        if function not in partials:
            partial = partial_ratio*function[inevent]
            for call in function.calls.values():
                if call.callee_id != function.id:
                    callee = self.functions[call.callee_id]
                    if callee.cycle is not cycle:
                        assert outevent in call
                        partial += partial_ratio*call[outevent]
                    else:
                        if ranks[callee] > ranks[function]:
                            callee_partial = self._integrate_cycle_function(cycle, callee, partial_ratio, partials, ranks, call_ratios, outevent, inevent)
                            call_ratio = ratio(call.ratio, call_ratios[callee])
                            call_partial = call_ratio*callee_partial
                            try:
                                call[outevent] += call_partial
                            except UndefinedEvent:
                                call[outevent] = call_partial
                            partial += call_partial
            partials[function] = partial
            try:
                function[outevent] += partial
            except UndefinedEvent:
                function[outevent] = partial
        return partials[function]

    def aggregate(self, event):
        """Aggregate an event for the whole profile."""

        total = event.null()
        for function in self.functions.values():
            try:
                total = event.aggregate(total, function[event])
            except UndefinedEvent:
                return
        self[event] = total

    def ratio(self, outevent, inevent):
        assert outevent not in self
        assert inevent in self
        for function in self.functions.values():
            assert outevent not in function
            assert inevent in function
            function[outevent] = ratio(function[inevent], self[inevent])
            for call in function.calls.values():
                assert outevent not in call
                if inevent in call:
                    call[outevent] = ratio(call[inevent], self[inevent])
        self[outevent] = 1.0

    def prune(self, node_thres, edge_thres, paths, color_nodes_by_selftime):
        """Prune the profile"""

        # compute the prune ratios
        for function in self.functions.values():
            try:
                function.weight = function[TOTAL_TIME_RATIO]
            except UndefinedEvent:
                pass

            for call in function.calls.values():
                callee = self.functions[call.callee_id]

                if TOTAL_TIME_RATIO in call:
                    # handle exact cases first
                    call.weight = call[TOTAL_TIME_RATIO]
                else:
                    try:
                        # make a safe estimate
                        call.weight = min(function[TOTAL_TIME_RATIO], callee[TOTAL_TIME_RATIO])
                    except UndefinedEvent:
                        pass

        # prune the nodes
        for function_id in list(self.functions.keys()):
            function = self.functions[function_id]
            if function.weight is not None:
                if function.weight < node_thres:
                    del self.functions[function_id]

        # prune file paths
        for function_id in list(self.functions.keys()):
            function = self.functions[function_id]
            if paths and function.filename and not any(function.filename.startswith(path) for path in paths):
                del self.functions[function_id]
            elif paths and function.module and not any((function.module.find(path)>-1) for path in paths):
                del self.functions[function_id]

        # prune the edges
        for function in self.functions.values():
            for callee_id in list(function.calls.keys()):
                call = function.calls[callee_id]
                if callee_id not in self.functions or call.weight is not None and call.weight < edge_thres:
                    del function.calls[callee_id]

        if color_nodes_by_selftime:
            weights = []
            for function in self.functions.values():
                try:
                    weights.append(function[TIME_RATIO])
                except UndefinedEvent:
                    pass
            max_ratio = max(weights or [1])

            # apply rescaled weights for coloriung
            for function in self.functions.values():
                try:
                    function.weight = function[TIME_RATIO] / max_ratio
                except (ZeroDivisionError, UndefinedEvent):
                    pass

    def dump(self):
        for function in self.functions.values():
            sys.stderr.write('Function %s:\n' % (function.name,))
            self._dump_events(function.events)
            for call in function.calls.values():
                callee = self.functions[call.callee_id]
                sys.stderr.write('  Call %s:\n' % (callee.name,))
                self._dump_events(call.events)
        for cycle in self.cycles:
            sys.stderr.write("Cycle: %s\n" % cycle.name)
            self._dump_events(cycle.events)
            for function in cycle.functions:
                sys.stderr.write('  Function %s\n' % (function.name,))
                self._dump_events(function.events)

    def _dump_events(self, events):
        for event, value in events.items():
            sys.stderr.write('    %s: %s\n' % (event.name, event.format(value)))



########################################################################
# Parsers


class Struct:
    """Masquerade a dictionary with a structure-like behavior."""

    def __init__(self, attrs = None):
        if attrs is None:
            attrs = {}
        self.__dict__['_attrs'] = attrs

    def __getattr__(self, name):
        try:
            return self._attrs[name]
        except KeyError:
            raise AttributeError(name)

    def __setattr__(self, name, value):
        self._attrs[name] = value

    def __str__(self):
        return str(self._attrs)

    def __repr__(self):
        return repr(self._attrs)


class ParseError(Exception):
    """Raised when parsing to signal mismatches."""

    def __init__(self, msg, line):
        Exception.__init__(self)
        self.msg = msg
        # TODO: store more source line information
        self.line = line

    def __str__(self):
        return '%s: %r' % (self.msg, self.line)

class Parser:
    """Parser interface."""

    stdinInput = True
    multipleInput = False

    def __init__(self):
        pass

    def parse(self):
        raise NotImplementedError



class VtuneParser(Parser):
    "Parser for VTune gprof-cc report output with semicolon delimiters."

    def __init__(self, fp):
        Parser.__init__(self)
        self.fp = fp
        self.functions = {}
        self.cycles = {}

    def readline(self):
        line = self.fp.readline()
        if not line:
            sys.stderr.write('error: unexpected end of file\n')
            sys.exit(1)
        line = line.rstrip('\r\n')
        return line

    _int_re = re.compile(r'^\d+$')
    _float_re = re.compile(r'^\d+\.\d+$')

    def translate(self, mo):
        """Extract a structure from a match object, while translating the types in the process."""
        attrs = {}
        groupdict = mo.groupdict()
        #print(groupdict)
        for name, value in sorted_iteritems(groupdict):
            if value is None:
                value = None
            elif self._int_re.match(value):
                value = int(value)
            elif self._float_re.match(value):
                value = float(value)
            attrs[name] = (value)
        return Struct(attrs)

    _cg_header_re = re.compile(
        'Index;% CPU Time:Total;CPU Time:Self;CPU Time:Children;Name;Index'
    )

    _cg_footer_re = re.compile(r'^Index;Function$')

    _cg_primary_re = re.compile(
        r'^\[(?P<index>\d+)\];' +
        r'(?P<percentage_time>\d+\.\d+);' +
        r'(?P<self_time>\d+\.\d+);' +
        r'(?P<descendants_time>(-)?\d+\.\d+);' +
        r'(?P<name>\S.*?)' +
        r'(?:\s+<cycle\s(?P<cycle>\d+)>)?;' +
        r'\[(\d+)\]$'
    )
    assert(_cg_primary_re.match('[1];108.69;0.099967;8162.684926;[Stitch point frame] <cycle 95>;[1]'))
    _cg_parent_re = re.compile(
        r'^;;(?P<self_time>\d+\.\d+)?' +
        r';(?P<descendants_time>\d+\.\d+)?' +
        r';\s\s((?P<name>\S.*?)' +
        r'(?:\s<cycle\s(?P<cycle>\d+)>)?' +
        r';(?:\[(?P<index>\d+)\])|<spontaneous>;)$'
    )
    assert(_cg_parent_re.match(';;;;  tbb::detail::r1::task_group_context_impl::bind_to <cycle 95>;[25074]'))
    assert(_cg_parent_re.match(';;;;  <spontaneous>;'))
    _cg_child_re = _cg_parent_re
    assert(_cg_child_re.match(';;0.109114;2.155263;  execute <cycle 15>;[29946]'))
    assert(_cg_child_re.match(';;0.020019;0.0;  TObjArray::operator[];[17803]'))
    assert(_cg_child_re.match(';;;;  task_ptr_or_nullptr<const edm::WaitingTaskHolder::doneWaiting(std::__exception_ptr::exception_ptr)::<lambda()>&> <cycle 95>;[54425]'))
    _cg_cycle_header_re = re.compile(
        r'^\[(?P<index>\d+)\]?;' +
        r'(?P<percentage_time>\d+\.\d+)?;' +
        r'(?P<self_time>\d+\.\d+)?;' +
        r'(?P<descendants_time>-?\d+\.\d+)?;' +
        r'<cycle\s(?P<cycle>\d+)\sas\sa\swhole>;' +
        r'\[(\d+)\]$'
    )
    assert(_cg_cycle_header_re.match('[2];99.99;192.093033;7317.508338;<cycle 15 as a whole>;[2]'))
    assert(_cg_cycle_header_re.match('[1346];0.03;0.480006;-0.000000;<cycle 25 as a whole>;[1346]'))

    _cg_cycle_member_re = re.compile(
        r'^;;(?P<self_time>\d+\.\d+)?' +
        r';(?P<descendants_time>\d+\.\d+)?' +
        r';\s\s(?P<name>\S.*?)' +
        r'(?:\s+<cycle\s(?P<cycle>\d+)>)?' +
        r';\[(?P<index>\d+)\]$'
    )
    assert(_cg_cycle_member_re.match(';;48.451673;19.315687;  PFBlockAlgo::findBlocks <cycle 15>;[307]'))
    def parse_function_entry(self, lines):
        parents = []
        children = []

        while True:
            if not lines:
                sys.stderr.write('warning: unexpected end of entry\n')
                return
            line = lines.pop(0)
            if line.startswith('['):
                break
            # read function parent line
            mo = self._cg_parent_re.match(line)
            if not mo:
                sys.stderr.write('warning: unrecognized call graph entry (1): %r\n' % line)
            else:
                parent = self.translate(mo)
                #print("function parent : %s" % parent)
                if parent.name != '<spontaneous>':
                    parents.append(parent)

        # read primary line
        mo = self._cg_primary_re.match(line)
        if not mo:
            sys.stderr.write('warning: unrecognized call graph entry (2): %r\n' % line)
            return
        else:
            function = self.translate(mo)
            #print("function : %s" % function)

        while lines:
            line = lines.pop(0)

            # read function subroutine line
            mo = self._cg_child_re.match(line)
            if not mo:
                sys.stderr.write('warning: unrecognized call graph entry (3): %r\n' % line)
            else:
                child = self.translate(mo)
                #print("function child : %s" % child)
                if child.name != '<spontaneous>':
                    children.append(child)

        if function.name != '<spontaneous>':
            function.parents = parents
            function.children = children

            self.functions[function.index] = function

    def parse_cycle_entry(self, lines):

        # Process the parents that were not there in gprof format.
        parents = []
        while True:
            if not lines:
                write('warning: unexpected end of cycle entry\n')
                return
            line = lines.pop(0)
            if line.startswith('['):
                break
            mo = self._cg_parent_re.match(line)
            if not mo:
                sys.stderr.write('warning: unrecognized call graph entry (6): %r\n' % line)
            else:
                parent = self.translate(mo)
                if parent.name != '<spontaneous>':
                    parents.append(parent)

        # read cycle header line
        mo = self._cg_cycle_header_re.match(line)
        if not mo:
            sys.stderr.write('warning: unrecognized call graph entry (4): %r\n' % line)
            return
        cycle = self.translate(mo)

        # read cycle member lines
        cycle.functions = []
        for line in lines[1:]:
            mo = self._cg_cycle_member_re.match(line)
            if not mo:
                sys.stderr.write('warning: unrecognized call graph entry (5): %r\n' % line)
                continue
            call = self.translate(mo)
            cycle.functions.append(call)

        cycle.parents = parents
        self.cycles[cycle.cycle] = cycle

    def parse_cg_entry(self, lines):
        if any("as a whole" in linelooper for linelooper in lines):
            self.parse_cycle_entry(lines)
        else:
            self.parse_function_entry(lines)

    def parse_cg(self):
        """Parse the call graph."""

        # skip call graph header
        line = self.readline()
        while self._cg_header_re.match(line):
            line = self.readline()

        # process call graph entries
        entry_lines = []
        # An EOF in readline terminates the program without returning.
        while not self._cg_footer_re.match(line):
            if line == ';;;;;':
                self.parse_cg_entry(entry_lines)
                entry_lines = []
            else:
                entry_lines.append(line)
            line = self.readline()

    def parse(self):
        #sys.stderr.write('warning: for axe format, edge weights are unreliable estimates derived from function total times.\n')
        self.parse_cg()
        self.fp.close()

        profile = Profile()
        profile[TIME] = 0.0

        cycles = {}
        for index in self.cycles:
            cycles[index] = Cycle(index, "<cycle %u as a whole>" % index)


        for entry in self.functions.values():
            # populate the function
            function = Function(entry.index, entry.name)
            st = entry.self_time or 0.0
            dt = entry.descendants_time or 0.0
            tt = st + dt 
            function[TIME] = st
            function[KIDS_TIME] = dt
            function[TOTAL_TIME] = tt
            function[TOTAL_TIME_RATIO] = entry.percentage_time / 100.0

            # populate the function calls
            for child in entry.children:
                call = Call(child.index)
                # The following bogus value affects only the weighting of
                # the calls.
                call[TOTAL_TIME_RATIO] = function[TOTAL_TIME_RATIO]
                st = child.self_time or 0.0
                dt = child.descendants_time or 0.0
                tt = st + dt
                call[TIME] = st
                call[KIDS_TIME] = dt
                call[TOTAL_TIME] = tt

                if child.index not in self.functions:
                    # NOTE: functions that were never called but were discovered by gprof's
                    # static call graph analysis dont have a call graph entry so we need
                    # to add them here
                    # FIXME: Is this applicable?
                    missing = Function(child.index, child.name)
                    function[TIME] = 0.0
                    profile.add_function(missing)

                function.add_call(call)

            profile.add_function(function)

            if entry.cycle is not None:
                try:
                    cycle = cycles[entry.cycle]
                except KeyError:
                    sys.stderr.write('warning: <cycle %u as a whole> entry missing\n' % entry.cycle)
                    cycle = Cycle(entry.cycle, "<cycle %u as a whole>" % entry.cycle)
                    cycles[entry.cycle] = cycle
                cycle.add_function(function)    

            profile[TIME] = profile[TIME] + function[TIME]

        for cycle in cycles.values():
            #st = cycle.self_time or 0.0
            #dt = cycle.descendants_time or 0.0
            #tt = st + dt
            #cycle[TIME] = st
            #cycle[KIDS_TIME] = dt
            #cycle[TOTAL_TIME] = tt
            #cycle[TOTAL_TIME_RATIO] = cycle.percentage_time / 100.0
            profile.add_cycle(cycle)

        # Compute derived events.
        profile.validate()
        profile.ratio(TIME_RATIO, TIME)
        # Lacking call counts, fake call ratios based on total times.
        profile.call_ratios(TOTAL_TIME_RATIO)
        # The TOTAL_TIME_RATIO of functions is already set.  Propagate that
        # total time to the calls.  (TOTAL_TIME is neither set nor used.)
        for function in profile.functions.values():
            for call in function.calls.values():
                if call.ratio is not None:
                    callee = profile.functions[call.callee_id]
                    call[TOTAL_TIME_RATIO] = call.ratio * callee[TOTAL_TIME_RATIO]

        return profile

formats = {"vtune": VtuneParser,}

class SQLiteWriter:
    """Writer for the SQLite language.

    """

    def __init__(self, fp):
        self.fp = fp

    show_function_events = [TOTAL_TIME, TOTAL_TIME_RATIO, TIME, TIME_RATIO, KIDS_TIME]
    show_edge_events = [TOTAL_TIME, TOTAL_TIME_RATIO, TIME, TIME_RATIO]

    def graph(self, profile):
        self.begin_graph()
        self.print_summary(profile)
        labels=[]
        for _, function in sorted_iteritems(profile.functions):
            self.node(function.id,symbol=function.name,symbol_id=function.id,self_count=int(function[TIME]/0.000001),cumulative_count=int(function[TOTAL_TIME]/0.000001),kids=int(function[KIDS_TIME]/0.000001),self_calls=0,total_calls=0,self_paths=0,total_paths=0,pct=function[TOTAL_TIME_RATIO])
            for _, call in sorted_iteritems(function.calls):
                callee = profile.functions[call.callee_id]
                self.edge(function.id, call.callee_id , count=int(call[TOTAL_TIME]/0.000001), calls=0, paths=0,pct=call[TOTAL_TIME_RATIO])
                
        for cycle in sorted(profile.cycles):
            sys.stderr.write("%s\n"%cycle.name)
        self.end_graph()

    def begin_graph(self):
        begincommands = """
PRAGMA journal_mode=OFF;
PRAGMA count_changes=OFF;
DROP TABLE IF EXISTS files;
DROP TABLE IF EXISTS symbols;
DROP TABLE IF EXISTS mainrows;
DROP TABLE IF EXISTS children;
DROP TABLE IF EXISTS parents;
DROP TABLE IF EXISTS summary;\n
CREATE TABLE summary (
counter TEXT,
total_count INTEGER,
total_freq INTEGER,
tick_period REAL
);\n
CREATE TABLE files (
id,
name TEXT
);\n
CREATE TABLE symbols (
id,
name TEXT,
filename_id INTEGER CONSTRAINT file_id_exists REFERENCES files(id)
);\n
CREATE TABLE mainrows (
id INTEGER PRIMARY KEY,
symbol_id INTEGER CONSTRAINT symbol_id_exists REFERENCES symbols(id),
self_count INTEGER,
cumulative_count INTEGER,
kids INTEGER,
self_calls INTEGER,
total_calls INTEGER,
self_paths INTEGER,
total_paths INTEGER,
pct REAL
);\n
CREATE TABLE children (
self_id INTEGER CONSTRAINT self_exists REFERENCES mainrows(id),
parent_id INTEGER CONSTRAINT parent_exists REFERENCES mainrows(id),
from_parent_count INTEGER,
from_parent_calls INTEGER,
from_parent_paths INTEGER,
pct REAL
);\n
CREATE TABLE parents (
self_id INTEGER CONSTRAINT self_exists REFERENCES mainrows(id),
child_id INTEGER CONSTRAINT child_exists REFERENCES mainrows(id),
to_child_count INTEGER,
to_child_calls INTEGER,
to_child_paths INTEGER,
pct REAL
);\n
PRAGMA synchronous=OFF;\n
BEGIN TRANSACTION;\n
"""
        self.write(begincommands)

    def print_summary(self, profile):
        summary_commands="""
INSERT INTO summary (counter, total_count, total_freq, tick_period) VALUES(\"PERF_TICKS\",%s,%s,0.000001);\n
INSERT INTO files VALUES(1, "<unknown>");\n
""" % (int(profile[TIME]/0.000001), int(profile[TIME]/0.000001))
        self.write(summary_commands)


    def end_graph(self):
        endcommands="""
END TRANSACTION;\n
CREATE UNIQUE INDEX fileIndex ON files (id);
CREATE UNIQUE INDEX symbolsIndex ON symbols (id);
CREATE INDEX selfCountIndex ON mainrows(self_count);
CREATE INDEX totalCountIndex ON mainrows(cumulative_count);
"""
        self.write(endcommands)

    def attr(self, what, **attrs):
        self.write(what)
        self.attr_list(attrs)

    def node(self, node, **attrs):
        self.write('INSERT INTO symbols VALUES(')
        self.id(node)
        self.write(', "')
        self.id(str(attrs["symbol"]))
        self.write('", 1);\n')

        self.write('INSERT INTO mainrows VALUES (')
        self.id(node)
        self.write(', ')
        self.id(attrs["symbol_id"])
        self.write(', ')
        self.id(attrs["self_count"])
        self.write(', ')
        self.id(attrs["cumulative_count"])
        self.write(', ')
        self.id(attrs["kids"])
        self.write(', ')
        self.id(attrs["self_calls"])
        self.write(', ')
        self.id(attrs["total_calls"])
        self.write(', ')
        self.id(attrs["self_paths"])
        self.write(', ')
        self.id(attrs["total_paths"])
        self.write(', ')
        self.id(attrs["pct"]*100)
        self.write(');\n')

    def edge(self, src, dst, **attrs):
        self.write('INSERT INTO children VALUES (')
        self.id(dst)
        self.write(', ')
        self.id(src)
        self.write(', ')
        self.id(attrs["count"])
        self.write(', ')
        self.id(attrs["calls"])
        self.write(', ')
        self.id(attrs["paths"])
        self.write(', ')
        self.id(attrs["pct"]*100)
        self.write(');\n')
        self.write('INSERT INTO parents VALUES (')
        self.id(src)
        self.write(', ')
        self.id(dst)
        self.write(', ')
        self.id(attrs["count"])
        self.write(', ')
        self.id(attrs["calls"])
        self.write(', ')
        self.id(attrs["paths"])
        self.write(', ')
        self.id(attrs["pct"]*100)
        self.write(');\n')

    def attr_list(self, attrs):
        if not attrs:
            return
        first = True
        for name, value in sorted_iteritems(attrs):
            if value is None:
                continue
            if first:
                first = False
            else:
                self.write(", ")
            self.id(value)

    def id(self, id):
        if isinstance(id, int):
            s = str(id)
        elif isinstance(id, float):
            s = "{:2.2f}".format(id)
        elif isinstance(id, str):
            if id.isalnum() and not id.startswith('0x'):
                s = id
            else:
                s = self.escape(id)
        else:
            raise TypeError
        self.write(s)

    def escape(self, s):
        s = s.replace('\\', r'\\')
        s = s.replace('\n', r'\n')
        s = s.replace('\t', r'\t')
        s = s.replace('"', r'\"')
        return s

    def write(self, s):
        self.fp.write(s)

# Main program


def naturalJoin(values):
    if len(values) >= 2:
        return ', '.join(values[:-1]) + ' or ' + values[-1]

    else:
        return ''.join(values)


def main(argv=sys.argv[1:]):
    """Main program."""

    optparser = optparse.OptionParser(
        usage="\n\t%prog [options] [file] ...")
    optparser.add_option(
        '-o', '--output', metavar='FILE',
        type="string", dest="output",
        help="output filename [stdout]")
    (options, args) = optparser.parse_args(argv)

    Format = formats["vtune"]
    if Format.stdinInput:
        if not args:
            fp = sys.stdin
        else:
            fp = open(args[0], 'rt', encoding='UTF-8')
        parser = Format(fp)
    else:
        if len(args) != 1:
            optparser.error('exactly one file must be specified for %s input' % options.format)
        parser = Format(args[0])

    profile = parser.parse()
    #profile.prune(0.000001, 0.000001, "", True)

    if options.output is None:
        output = open(sys.stdout.fileno(), mode='wt', encoding='UTF-8', closefd=False)
    else:
        output = open(options.output, 'wt', encoding='UTF-8')

    mysql = SQLiteWriter(output)
    mysql.graph(profile)
    profile.dump()


if __name__ == '__main__':
    main()


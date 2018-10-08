
class BoundQuiver(DiGraph):
    def __init__(self, data=None, ideal=[], **args):
        default_values = {'implementation': 'c_graph', 'data_structure': 'sparse', 'vertex_labels': True, 'sparse': True, 'immutable': False}
        default_values.update(args)

        # Create the digraph
        DiGraph.__init__(self, data=data, **default_values)

        # Save the ideal (assume that it is admissible)
        self._ideal = ideal

    # Redefines show method
    def show(self, **args):
        r'''
            Show the quiver as an oriented graph.

            Note that relations are not visible. 
        '''
        DiGraph.show(self, edge_labels=True, **args)

    def edges_in(self, v):
        r'''
            Return the labels of the incoming edges to a vertex v.
        '''
        return [l for s,t,l in self.incoming_edges(v)]

    def edges_out(self, v):
        r'''
            Return the labels of the outgoing edges to a vertex v.
        '''
        return [l for s,t,l in self.outgoing_edges(v)]

    def ideal(self):
        r'''
            Return the ideal of the bound quiver.
        '''
        return self._ideal

    def copy(self, **ignored):
        r'''
            Return a copy of the bound quiver.
        '''
        return type(self)(self, ideal=deepcopy(self._ideal), name=self.name(), pos=deepcopy(self._pos))

    def is_locally_gentle(self):
        r'''
            Check that the bound quiver is locally gentle.

            Note that we are not testing that the ideal is admissible.
        '''
        for v in self.vertices():
            ins = self.edges_in(v)
            outs = self.edges_out(v)
            # each vertex has in and out degree at most 2 
            if len(ins) > 2 or len(outs) > 2:
                print "num wrong"
                return False
            # For each vertex every arrow going in/out can have at most 1 arrow with/without a relation
            cins = copy(ins)
            for relation in self._ideal:
                if relation[0] in cins:
                    if relation[0] not in ins or relation[1] not in outs:
                        return False
                    else:
                        ins.remove(relation[0])
                        outs.remove(relation[1])
            if (len(ins) > 1 and len(outs) > 0) or (len(ins) > 0 and len(outs) > 1):
                return False
        return True

    # Manipulation of labels of edges.
    # Arrows are labeled by strings. The reverse of an arrow labeled by a is labeled by a-. The following functions are manipulating these labels.

    def positive_label(self, l):
        r'''
            Return the label with no sign.
        '''
        return l[:-1] if l[-1] == '-' else l

    def inverse_label(self, l):
        r'''
            Return the inverse of a label.
        '''
        return l[:-1] if l[-1] == '-' else l+'-'

    def inverse_string(self, w):
        r'''
            Return the inverse of a string, taking care of inversing the labels.
        '''
        res = []
        for i in range(len(w)-2, 0, -2):
            res += [w[i+1], self.inverse_label(w[i])]
        return tuple(res + [w[0]])

    def same_signs(self, l1, l2):
        r'''
            Test whether the two labels l1 and l2 have the same sign.
        '''
        return (l1[-1] == '-' and l2[-1] == '-') or (l1[-1] != '-' and l2[-1] != '-') 

    def different_signs(self, l1, l2):
        r'''
            Test whether the two labels l1 and l2 have the distinct sign.
        '''
        return (l1[-1] == '-' and l2[-1] != '-') or (l1[-1] != '-' and l2[-1] == '-') 

    # Generation of all paths and strings 

    # Paths
    # A path in Q is a sequence (v0, a1, v1, ..., ak, vk) where vi are vertices and ai are arcs, such that [vi, v{i+1}] is not in the ideal I for any i.

    def enumerate_paths(self, start, nexts, maximal=True):
        r'''
            Enumeration process given the seeds start, the generating rule nexts, and the maximality criterion.
        '''
        start = [(p, set({tuple(p[1])})) for p in start]
        def children((p,s)):
            for n in nexts[p[-2]]:
                if tuple(n[0]) in s:
                    raise ValueError, "infinitely many paths"
                yield p+n, s.union({tuple(n[0])})
        if maximal:
            def post_process((p,s)):
                return None if nexts[p[-2]] else p
        else:
            def post_process((p,s)):
                return p
        return RecursivelyEnumeratedSet(start, children, structure='forest', post_process=post_process, category=EnumeratedSets().Finite())

    def start_path(self):
        return [(s,l,t) for s,t,l in self.edges()]

    def next_possible_arrows_path(self):
        return {l1:[(l2,t2) for s2,t2,l2 in self.edges() if s2 == t1 and (l1,l2) not in self._ideal] for s1,t1,l1 in self.edges()}

    def quiver_paths(self, with_idempotents=False):
        r'''
        Return all paths on the quiver.

        Paths are represented by tuples (v0, a1, v1, ..., ak, vk) where vi are vertices and ai are arcs.

        EXAMPLES::

            sage: Q = BoundQuiver({'e1':{'e2':['a','b']}, 'e2':{'e3':['c']}}, [('a','c')])
            sage: list(Q.quiver_paths(with_idempotents=True))
            [('e1',),
             ('e2',),
             ('e3',),
             ('e1', 'a', 'e2'),
             ('e1', 'b', 'e2'),
             ('e1', 'b', 'e2', 'c', 'e3'),
             ('e2', 'c', 'e3')]
        '''
        res = self.enumerate_paths(self.start_path(), self.next_possible_arrows_path(), maximal=False)
        if with_idempotents:
            return DisjointUnionEnumeratedSets([FiniteEnumeratedSet([(v,) for v in self.vertices()]), res])
        return res

    # Strings

    def start_string(self, maximal=False):
        if not maximal:
            return [(s,l,t) for s,t,l in self.edges()] + [(t,self.inverse_label(l),s) for s,t,l in self.edges()]
        else:
            return [(s,l,t) for s,t,l in self.edges() if self.next_possible_arrows_string()[self.inverse_label(l)] == []] + [(t,self.inverse_label(l),s) for s,t,l in self.edges() if self.next_possible_arrows_string()[l] == []]

    @cached_method
    def next_possible_arrows_string(self):
        from collections import defaultdict
        next_possible_arrows = defaultdict(list)
        for s1,t1,l1 in self.edges():
            for s2,t2,l2 in self.edges():
                if s2 == t1 and (l1,l2) not in self._ideal:
                    next_possible_arrows[l1].append((l2,t2))
                    next_possible_arrows[self.inverse_label(l2)].append((self.inverse_label(l1),s1))
                if t2 == t1 and l1 != l2:
                    next_possible_arrows[l1].append((self.inverse_label(l2),s2))
                if s2 == s1 and l1 != l2:
                    next_possible_arrows[self.inverse_label(l1)].append((l2,t2))
        return next_possible_arrows

    def quiver_strings(self, maximal=False, with_idempotents=True):
        r'''
            Return all strings on the quiver, that is paths using arrows or antiarrows.

            Strings are represented by tuples (v0, a1, v1, ..., ak, vk) where vi are vertices and ai are arcs.

            EXAMPLES::

                sage: Q = BoundQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: list(Q.quiver_strings())

                [('e1',),
                 ('e2',),
                 ('e3',),
                 ('e1', 'a', 'e2'),
                 ('e2', 'b', 'e3'),
                 ('e2', 'b', 'e3', 'c', 'e1'),
                 ('e2', 'b', 'e3', 'c', 'e1', 'a', 'e2'),
                 ('e3', 'c', 'e1'),
                 ('e3', 'c', 'e1', 'a', 'e2'),
                 ('e2', 'a-', 'e1'),
                 ('e2', 'a-', 'e1', 'c-', 'e3'),
                 ('e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2'),
                 ('e3', 'b-', 'e2'),
                 ('e1', 'c-', 'e3'),
                 ('e1', 'c-', 'e3', 'b-', 'e2')]
        '''
        res = self.enumerate_paths(self.start_string(maximal=maximal), self.next_possible_arrows_string(), maximal=maximal)
        if not maximal and with_idempotents:
            return DisjointUnionEnumeratedSets([FiniteEnumeratedSet([(v,) for v in self.vertices()]), res])
        return res

    def undirected_quiver_strings(self, maximal=False, with_idempotents=True):
        r'''
            Return only one representative per undirected string of the quiver.

            EXAMPLES::

                sage: Q = BoundQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: list(Q.undirected_quiver_strings())

                [('e1',),
                 ('e2',),
                 ('e3',),
                 ('e1', 'a', 'e2'),
                 ('e2', 'b', 'e3'),
                 ('e2', 'b', 'e3', 'c', 'e1'),
                 ('e2', 'b', 'e3', 'c', 'e1', 'a', 'e2'),
                 ('e3', 'c', 'e1'),
                 ('e3', 'c', 'e1', 'a', 'e2')]
        '''
        res = []
        for s in self.quiver_strings(maximal=maximal, with_idempotents=with_idempotents):
            if self.inverse_string(s) not in res:
                res.append(s)
        return res

    # Straight strings

    def is_straight(self, w):
        r'''
            Test if a string is straight.

            Works both for directed or undirected strings.
        '''
        # be carefull that only odd indices correspond to arcs.
        return len([w[2*i+1] for i in range(len(w)/2) if w[2*i+1][-1] == '-']) in [0,len(w)/2]

class GentleQuiver(BoundQuiver):
    r'''
        A class for gentle quivers.

        A gentle algebra $A = kQ/I$ is the path algebra of a quiver $Q$ with relations $I$ such that :
            - $I$ is generated by relations of length 2,
            - each vertex is incident to at most two incomming and at most two outgoing arrows,
            - for each arrow $\beta$, there is at most one arrow $\alpha$ such that $\alpha\beta \in I$ (resp. such that $\alpha\beta \notin I$),
            - for each arrow $\beta$, there is at most one arrow $\gamma$ such that $\beta\gamma \in I$ (resp. such that $\beta\gamma \notin I$).

        EXAMPLES::

            sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
    '''

    # we need all these paramters to properly work with DiGraph
    def __init__(self, data=None, ideal=[], **args):
        # Creates the quiver
        BoundQuiver.__init__(self, data=data, ideal=ideal, **args)

        # Require that our quiver be gentle
        if not BoundQuiver.is_locally_gentle(self):
            raise TypeError('Quiver provided is not gentle')

    # Since we do a test in the beginning if it's gentle, this should always return True
    def is_locally_gentle(self):
        return True

    # Koszul duality

    def koszul_dual(self):
        r'''
            Return the Koszul dual of the quiver.

            Relations and non-relations are exchanged.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: kd = Q.koszul_dual()
                sage: kd.edges()
                [('e1', 'e3', 'c'), ('e2', 'e1', 'a'), ('e3', 'e2', 'b')]
                sage: kd.ideal()
                [('a', 'c'), ('c', 'b')]
            '''
        return GentleQuiver(self.reverse(), [(l1, l2) for s1,t1,l1 in self.edges() for s2,t2,l2 in self.edges() if s1 == t2 and (l2,l1) not in self._ideal])

    # Blossoming quiver and its walks

    @cached_method
    def blossoming_quiver(self):
        r'''
            Return the blossoming quiver of the gentle quiver.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: bQ = Q.blossoming_quiver()
                sage: bQ.vertices()
                ['e1', 'e1i0', 'e1o0', 'e2', 'e2i0', 'e2o0', 'e3', 'e3i0', 'e3o0']
                sage: bQ.edges()

                [('e1', 'e1o0', 'be1o0'),
                 ('e1', 'e2', 'a'),
                 ('e1i0', 'e1', 'be1i0'),
                 ('e2', 'e2o0', 'be2o0'),
                 ('e2', 'e3', 'b'),
                 ('e2i0', 'e2', 'be2i0'),
                 ('e3', 'e1', 'c'),
                 ('e3', 'e3o0', 'be3o0'),
                 ('e3i0', 'e3', 'be3i0')]
        '''
        I = self.ideal()
        starts = [s for s,t in I]
        terminalss = [t for s,t in I]
        bQ = self.copy()
        bI = copy(I)
        for v in self.vertices():
            # Grab what edges are going in, and which are going out
            ins = self.edges_in(v)
            outs = self.edges_out(v)
            # We first add vertices so that every already existing vertex has
            # two arrows going in and two arrows going out.
            for i in range(2 - len(ins)):
                newVertex = v+'i'+str(i)
                bQ.add_vertex(newVertex)
                bQ.add_edge(newVertex, v, 'b'+newVertex)
                ins.append('b'+newVertex)
            for i in range(2 - len(outs)):
                newVertex = v+'o'+str(i)
                bQ.add_vertex(newVertex)
                bQ.add_edge(v, newVertex, 'b'+newVertex)
                outs.append('b'+newVertex)
            # For each arrow coming in, there eixsts one and exactly one arrow going out
            # that it has a relationship with
            # Since our original ins/outs appear first, we should match them with those inserted
            # last in order to not add any new relationships with already existing arrows
            # Note that we should have exactly 2 ins and 2 outs
            #
            # First we remove the ones that already exist
            cins = copy(ins)
            for ini in cins:
                for i in I:
                    if ini == i[0]: 
                        ins.remove(i[0])
                        outs.remove(i[1])
            # Now add the new relations
            while ins:
                i = ins.pop(0) # first one
                o = outs.pop() # last one
                assert((i,o) not in bI)
                bI.append((i,o))

        bQ._ideal = bI
        return bQ

    def blossoming_quiver_walks(self):
        r'''
            Return all walks on the blossoming quiver.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: list(Q.blossoming_quiver_walks())

                [('e1i0', 'be1i0', 'e1', 'be1o0', 'e1o0'),
                 ('e1i0', 'be1i0', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e1i0', 'be1i0', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2i0-', 'e2i0'),
                 ('e1i0', 'be1i0', 'e1', 'c-', 'e3', 'be3o0', 'e3o0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'be1o0', 'e1o0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2i0-', 'e2i0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'c-', 'e3', 'be3o0', 'e3o0'),
                 ('e2i0', 'be2i0', 'e2', 'b', 'e3', 'c', 'e1', 'a', 'e2', 'be2o0', 'e2o0'),
                 ('e2i0', 'be2i0', 'e2', 'b', 'e3', 'c', 'e1', 'a', 'e2', 'be2i0-', 'e2i0'),
                 ('e2i0', 'be2i0', 'e2', 'b', 'e3', 'c', 'e1', 'be1i0-', 'e1i0'),
                 ('e2i0', 'be2i0', 'e2', 'b', 'e3', 'be3i0-', 'e3i0'),
                 ('e3i0', 'be3i0', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e3i0', 'be3i0', 'e3', 'b-', 'e2', 'be2i0-', 'e2i0'),
                 ('e3i0', 'be3i0', 'e3', 'be3o0', 'e3o0'),
                 ('e1o0', 'be1o0-', 'e1', 'a', 'e2', 'be2o0', 'e2o0'),
                 ('e1o0', 'be1o0-', 'e1', 'a', 'e2', 'be2i0-', 'e2i0'),
                 ('e1o0', 'be1o0-', 'e1', 'be1i0-', 'e1i0'),
                 ('e2o0', 'be2o0-', 'e2', 'a-', 'e1', 'be1o0', 'e1o0'),
                 ('e2o0', 'be2o0-', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e2o0', 'be2o0-', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2i0-', 'e2i0'),
                 ('e2o0', 'be2o0-', 'e2', 'a-', 'e1', 'c-', 'e3', 'be3o0', 'e3o0'),
                 ('e2o0', 'be2o0-', 'e2', 'b', 'e3', 'c', 'e1', 'a', 'e2', 'be2o0', 'e2o0'),
                 ('e2o0', 'be2o0-', 'e2', 'b', 'e3', 'c', 'e1', 'a', 'e2', 'be2i0-', 'e2i0'),
                 ('e2o0', 'be2o0-', 'e2', 'b', 'e3', 'c', 'e1', 'be1i0-', 'e1i0'),
                 ('e2o0', 'be2o0-', 'e2', 'b', 'e3', 'be3i0-', 'e3i0'),
                 ('e3o0', 'be3o0-', 'e3', 'c', 'e1', 'a', 'e2', 'be2o0', 'e2o0'),
                 ('e3o0', 'be3o0-', 'e3', 'c', 'e1', 'a', 'e2', 'be2i0-', 'e2i0'),
                 ('e3o0', 'be3o0-', 'e3', 'c', 'e1', 'be1i0-', 'e1i0'),
                 ('e3o0', 'be3o0-', 'e3', 'be3i0-', 'e3i0')]
        '''
        return self.blossoming_quiver().quiver_strings(maximal=True, with_idempotents=False)

    def undirected_blossoming_quiver_walks(self):
        r'''
            Return all undirected walks on the blossoming quiver.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.undirected_blossoming_quiver_walks()

                [('e1i0', 'be1i0', 'e1', 'be1o0', 'e1o0'),
                 ('e1i0', 'be1i0', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e1i0', 'be1i0', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2i0-', 'e2i0'),
                 ('e1i0', 'be1i0', 'e1', 'c-', 'e3', 'be3o0', 'e3o0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'be1o0', 'e1o0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2i0-', 'e2i0'),
                 ('e2i0', 'be2i0', 'e2', 'a-', 'e1', 'c-', 'e3', 'be3o0', 'e3o0'),
                 ('e2i0', 'be2i0', 'e2', 'b', 'e3', 'c', 'e1', 'a', 'e2', 'be2o0', 'e2o0'),
                 ('e2i0', 'be2i0', 'e2', 'b', 'e3', 'be3i0-', 'e3i0'),
                 ('e3i0', 'be3i0', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e3i0', 'be3i0', 'e3', 'be3o0', 'e3o0'),
                 ('e1o0', 'be1o0-', 'e1', 'a', 'e2', 'be2o0', 'e2o0'),
                 ('e2o0', 'be2o0-', 'e2', 'a-', 'e1', 'c-', 'e3', 'b-', 'e2', 'be2o0', 'e2o0'),
                 ('e2o0', 'be2o0-', 'e2', 'a-', 'e1', 'c-', 'e3', 'be3o0', 'e3o0')]
        '''
        return self.blossoming_quiver().undirected_quiver_strings(maximal=True, with_idempotents=False)

    # Extensions, hooks and cohooks

    def extending_arrow(self, v, a, dir='in'):
        r'''
            Return the arrow with vertex v that is compatible with a.
        '''
        bQ = self.blossoming_quiver()
        if dir == 'in':
            return [(b, u) for (u, w, b) in bQ.incoming_edges(v) if b != a and (b, a) not in bQ.ideal() and (b, bQ.inverse_label(a)) not in bQ.ideal()]
        if dir == 'out':
            return [(b, w) for (u, w, b) in bQ.outgoing_edges(v) if b != a and (a, b) not in bQ.ideal() and (bQ.inverse_label(a), b) not in bQ.ideal()]

    def extending_walk(self, v, a, dir='in'):
        r'''
            Return the straight subwalk starting at v and compatible with a.
        '''
        bQ = self.blossoming_quiver()
        subwalk = [v]
        while True:
            arrow = self.extending_arrow(v, a, dir=dir)
            if arrow == []:
                break
            v = arrow[0][1]
            a = arrow[0][0]
            subwalk = subwalk + [a if dir == 'out' else bQ.inverse_label(a), v]
        return subwalk

    def hook(self, v, a, dir='hook'):
        r'''
            Return the hook (or cohook) starting at v and compatible with a.
        '''
        bQ = self.blossoming_quiver()
        arrow = self.extending_arrow(v, a, 'in' if dir == 'hook' else 'out')
        if arrow == []:
            raise ValueError, "there is no hook / cohook at a blossom."
        w = arrow[0][1]
        b = arrow[0][0]
        subwalk = self.extending_walk(w, b, 'out' if dir == 'hook' else 'in')
        return [v, bQ.inverse_label(b) if dir == 'hook' else b] + subwalk

    def add_hooks(self, string, dir='hook'):
        r'''
            Return the walk obtained from the string by adding (co)hooks on both sides.
        '''
        bQ = self.blossoming_quiver()
        if (len(string) == 1):
            v = string[0]
            arrows = bQ.edges_in(v) if dir == 'hook' else bQ.edges_out(v)
            h_start = self.inverse_string(self.hook(v, arrows[0], dir=dir))
            h_end = self.hook(v, arrows[1], dir=dir)
        else:
            h_start = self.inverse_string(self.hook(string[0], Q.positive_label(string[1]), dir=dir))
            h_end = self.hook(string[-1], Q.positive_label(string[-2]), dir=dir)
        return tuple(list(h_start)[:-1] + list(string) + list(h_end)[1:])

    # Distinguishable strings

    def distinguishable(self, string):
        r'''
            Test if string is distinguishable.

            A string s is distinguishable if and only if there is no substring which is both on top and on bottom of s.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.distinguishable(('e1','a','e2'))
                True
                sage: Q.distinguishable(('e2','b','e3','c','e1','a','e2'))
                False
        '''
        bQ = self.blossoming_quiver()
        if len(string) == 1:
            return True
        inverse = bQ.inverse_string
        extension1 = tuple(reversed(bQ.extending_arrow(string[0], string[1], dir='in')[0])) + string + bQ.extending_arrow(string[-1], string[-2], dir='out')[0] 
        extension2 = inverse(tuple(reversed(bQ.extending_arrow(string[-1], string[-2], dir='in')[0])) + inverse(string) + bQ.extending_arrow(string[0], string[1], dir='out')[0]) 
        return not self.is_self_kissing_undirected_walk(extension1) and not self.is_self_kissing_undirected_walk(extension2)

    # Kissing numbers

    # Directed walks

    def kissing_walks_iterator(self, w1, w2):
        r'''
            Iterate all positions of kissings between two walks w1 and w2.
        '''
        for i in range(1, len(w1)-3, 2):
        # i = starting point of common substring on w1
            for j in range(1, len(w2)-3, 2):
                # j = starting point of common substring on w2
                if w1[i] != w2[j] and w1[i+1] == w2[j+1]:
                    k = 2 # 2 * length of common substring
                    while i+k < len(w1) and j+k < len(w2) and w1[i+k] == w2[j+k]:
                        k += 2
                    if i+k < len(w1) and j+k < len(w2) and self.different_signs(w1[i], w1[i+k]) and self.different_signs(w2[j], w2[j+k]):
                        # in case the common substring is restricted to a vertex, we need extra care
                        if k > 2 or (w1[i] != self.inverse_label(w2[j+k]) and w1[i+k] != self.inverse_label(w2[j])):
                            yield (i, j, k)

    def are_positively_kissing_walks(self, w1, w2):
        r'''
            Test if the walk w1 is kissing the walk w2.
        '''
        for i,j,k in self.kissing_walks_iterator(w1,w2):
            if w1[i][-1] == '-' and self.distinguishable(w1[i+1:i+k]):
                return True
        return False

    def are_kissing_walks(self, w1, w2):
        r'''
            Test if the two walks w1 and w2 are kissing.
        '''
        it = self.kissing_walks_iterator(w1,w2)
        try:
            it.next()
            return True
        except StopIteration:
            return False

    def all_kissing_walks(self, w1, w2):
        r'''
            Return all kissings between two walks w1 and w2.
        '''
        return [w1[i+1:i+k] for (i,j,k) in list(self.kissing_walks_iterator(w1, w2))]

    def kissing_number_walk(self, w1, w2):
        r'''
            Return the number of kisses between the two walks w1 and w2.
        '''
        return len(self.all_kissing_walks(w1, w2))

    # Undirected walks

    def all_kissing_undirected_walks(self, w1, w2):
        r'''
            Return all kissings between two undirected walks w1 and w2.

            Careful that kisses at a single point should be counted only in one direction.
        '''
        l = len(w2)
        return self.all_kissing_walks(w1, w2) + [string for string in self.all_kissing_walks(w1, self.inverse_string(w2)) if len(string) > 1]

    def are_kissing_undirected_walks(self, w1, w2):
        r'''
            Test if the two undirected walks w1 and w2 are kissing.
        '''
        return self.are_kissing_walks(w1, w2) or self.are_kissing_walks(w1, self.inverse_string(w2))

    def are_positively_kissing_undirected_walks(self, w1, w2):
        r'''
            Test if the undirected walk w1 is kissing the undirected walk w2.
        '''
        return self.are_positively_kissing_walks(w1, w2) or self.are_positively_kissing_walks(w1, self.inverse_string(w2))

    def kissing_number_undirected_walks(self, w1, w2):
        r'''
            Return the number of kisses between the two undirected walks w1 and w2.
        '''
        return len(self.all_kissing_undirected_walks(w1, w2))

    def total_kissing_number_undirected_walk(self, w):
        r'''
            Return the total kissing number of the undirected walk w, that is the total number of kisses of w with another walk.
        '''
        return add([self.kissing_number_undirected_walks(w,w2) for w2 in self.blossoming_quiver_walks()])

    def is_self_kissing_undirected_walk(self, w):
        r'''
            Test if an undirected walk w is self-kissing.
        '''
        return self.are_kissing_undirected_walks(w, w)

    def kiss_along_string(self, w1, w2, string):
        r'''
            Test if w1 and w2 kiss along the given string. 
        '''
        kissings = self.all_kissing_undirected_walks(w1, w2)
        return any([string == kiss or self.inverse_string(string) == kiss for kiss in kissings])

    def kiss_along_substring(self, w1, w2, substring):
        r'''
            Test if w1 and w2 kiss along the substring s. 
        '''
        kissings = [Word(kiss) for kiss in self.all_kissing_undirected_walks(w1, w2)]
        s = Word(substring)
        t = Word(self.inverse_string(substring))
        return any([s.is_factor(k) or t.is_factor(k) for k in kissings])

    # Orienting a flip

    def orient(self, flip):
        r'''
            Orient the flip in the increasing flip orientation.
        '''
        f1,f2,_ = flip
        s1 = f1.set()
        s2 = f2.set()
        w1 = list(s1-s2)[0]
        w2 = list(s2-s1)[0]
        if self.are_positively_kissing_undirected_walks(w1,w2):
            return [f1, f2]
        return [f2, f1]

    def orient_exchangeable(self, flip, string=[], substring=[]):
        r'''
            Orient the flip in the increasing flip orientation. Return the oriented pair of exchangeable walks.

            If string != [], we moreover require that the distinguished string is string.
            If substring != [], we moreover require that the distinguished string contains substring.
        '''
        f1,f2,_ = flip
        s1 = f1.set()
        s2 = f2.set()
        w1 = list(s1-s2)[0]
        w2 = list(s2-s1)[0]
        if string != [] and not self.kiss_along_string(w1, w2, string):
            return []
        if substring != [] and not self.kiss_along_substring(w1, w2, substring):
            return []
        if [self.distinguishable(kiss) for kiss in self.all_kissing_undirected_walks(w1, w2)] != []:
            return [w1, w2]
        return [w2, w1]

    # Conjecture exchangeable walks

    def exchangeable(self, w1, w2):
        r'''
            Test whether the walks w1 and w2 are exchangeable.

            Conjecturally, this is when they have a unique distinguishable kiss. It seems to work for gentle algebras where all strings are distinguishable. Otherwise, it seems that there is one inclusion.
        '''
        distinguishable_common_substrings1 = [(i,j,k) for (i,j,k) in self.kissing_walks_iterator(w1, w2) if self.distinguishable(w1[i+1: i+k])]
        distinguishable_common_substrings2 = [(i,j,k) for (i,j,k) in self.kissing_walks_iterator(w1, Q.inverse_string(w2)) if k > 2 and self.distinguishable(w1[i+1: i+k])]
        if len(distinguishable_common_substrings1) + len(distinguishable_common_substrings2) != 1:
            return False
        (i,j,k) = (distinguishable_common_substrings1 + distinguishable_common_substrings2)[0]
        print i,j,k
        # reverse the walk w2 in the second case
        if len(distinguishable_common_substrings2) == 1:
            print w1, w2, i, j, k
            w2 = Q.inverse_string(w2)
            print w2
        mu = w2[:j+1] + w1[i+1:]
        nu = w1[:i+1] + w2[j+1:]
        print mu, nu
        return not (self.is_self_kissing_undirected_walk(mu) or self.is_self_kissing_undirected_walk(nu))

    def test_conjecture_exchangeables(self):
        r'''
            Test the conjecture that exchangeable walks are those with a unique distinguishable kiss.

            It seems to work for gentle algebras where all strings are distinguishable. Otherwise, it seems that there is one inclusion.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.test_conjecture_exchangeables()
        '''
        exchangeable_pairs_1 = set([tuple(sorted(list(set(flip[0]).symmetric_difference(flip[1])))) for flip in self.non_kissing_flip_graph().edges()])
        exchangeable_pairs_2 = set([tuple(sorted([w1, w2])) for (w1, w2) in Subsets(self.relevant_walks(), 2) if self.exchangeable(w1, w2)])
        return (exchangeable_pairs_1.issubset(exchangeable_pairs_2), exchangeable_pairs_2.issubset(exchangeable_pairs_1), exchangeable_pairs_2.difference(exchangeable_pairs_1))

    def counter_current_order(self, walk1, pos1, walk2, pos2):
        r'''
            Compare the walks walk1 and walk2 in the counter-current order with respect to the arrow at position pos1 in walk1 and at position pos2 in walk2 (these arrows are assumed to coincide).
        '''
        assert(walk1[pos1] == walk2[pos2])
        direction = walk1[pos1][-1]
        l = len(walk1)
        i = 1
        while(True):
            # consider the arrows i positions before and 
            if pos1 + 2*i < l and walk1[pos1 + 2*i][-1] != walk2[pos2 + 2*i][-1] != direction:
                return walk1[pos1 + 2*i][-1] == direction
            if pos1 - 2*i > 0 and walk1[pos1 - 2*i][-1] != walk2[pos2 + 2*i][-1]:
                return walk1[pos1 + 2*i][-1] == direction
            i += 1
        return False

    # Combinatorics: non-kissing complex

    def relevant_walks(self):
        r'''
            Return the walks that are neither straight nor self-kissing.
            These are the vertices of the non-kissing complex
        '''
        return [w for w in self.undirected_blossoming_quiver_walks() if not self.is_straight(w) and not self.is_self_kissing_undirected_walk(w)]

    @cached_method
    def non_kissing_complex(self):
        r'''
            Return the non-kissing complex of the gentle quiver.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.non_kissing_complex()
                Simplicial complex with 11 vertices and 18 facets
        '''
        non_kissing_graph = Graph([self.relevant_walks(), lambda w1, w2: w1 != w2 and not self.are_kissing_undirected_walks(w1, w2)])
        return non_kissing_graph.clique_complex()

    # Lattice: flip graph and non-kissing lattice

    @cached_method
    def non_kissing_flip_graph(self):
        r'''
            Return the flip graph of the non-kissing complex.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.non_kissing_flip_graph()
                Graph on 18 vertices
        '''
        return self.non_kissing_complex().flip_graph()

    @cached_method
    def oriented_non_kissing_flip_graph(self):
        r'''
            Return the flip graph of the non-kissing complex, oriented by increasing flips.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.oriented_non_kissing_flip_graph()
                Digraph on 18 vertices

        '''
        fg = self.non_kissing_flip_graph()
        return DiGraph([fg.vertices(), [self.orient(flip) for flip in fg.edges()]], immutable=True)

    @cached_method
    def non_kissing_lattice(self):
        r'''
            Return the non-kissing lattice.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.non_kissing_lattice()
                Finite lattice containing 18 elements
        '''
        return LatticePoset(self.oriented_non_kissing_flip_graph())

    def increasing_exchangeable_graph(self):
        r'''
            Return the increasing exchangeable graph of the quiver.

            The vertices are the non-self-kissing walks and the vertices are pairs of exchangeable walks related by an increasing flip.
        '''
        return DiGraph([self.orient_exchangeable(flip) for flip in self.non_kissing_flip_graph().edges()], multiedges=False)

    def increasing_exchangeable_subgraph(self, string):
        edges = []
        for flip in self.non_kissing_flip_graph().edges():
            oriented_exchangeable = self.orient_exchangeable(flip, substring=string)
            if oriented_exchangeable != []:
                edges.append(oriented_exchangeable)
        return DiGraph(edges , format='list_of_edges', multiedges=False)

    # Algebra: Auslander-Reiten quiver

    @cached_method
    def elementary_move(self, w, side='start'):
        r'''
            Perform an elementary move on the walk w in direction side.
        '''
        inverse = self.blossoming_quiver().inverse_string
        if side == 'start':
            rev = self.elementary_move(inverse(w), side='end')
            if rev is None:
                return None
            return inverse(rev)
        if side == 'end':
            non_reversed_arrows = [i for i in range((len(w)-1)/2) if w[2*i+1][-1] != '-']
            if non_reversed_arrows == []:
                return None
            # raise ValueError, "this is a straight walk"
            i = non_reversed_arrows[-1]
            if i == 0:
                return None
                # raise ValueError, "this elementary move is not possible"
            return w[:2*i] + tuple(self.hook(w[2*i], w[2*i-1], dir='hook'))

    def elementary_moves(self, w, i, side='start'):
        r'''
            Perform i repetitions of elementary moves on the walk w in direction side.
        '''
        return w if i == 0 else self.elementary_move(self.elementary_moves(w, i-1, side=side), side=side)

    def elementary_move_next_nonkissing(self, w, side='start'):
        r'''
            Perform elementary moves on the walk w in direction side until it finds a non-self-kissing walk.
        '''
        if w is None:
            return (None,-1)
        res = self.elementary_move(w, side=side)
        if res is None:
            return (None,0)
        i = 1
        while self.is_self_kissing_undirected_walk(res):
            if res is None:
                return (None,0)
            res = self.elementary_move(res, side=side)
            i = i+1
        return (res, i)

    def square_mesh(self, w):
        r'''
            Return the square mesh starting at walk w, no matter whether wS, wE and wES are self-kissing.
        '''
        wS = self.elementary_move(w, side='start')
        wE = self.elementary_move(w, side='end')
        if wS is None or wE is None:
            raise ValueError, "there is no mesh here..."
        wES = self.elementary_move(wE, side='start')
        wSE = self.elementary_move(wS, side='end')
        if wSE != wES:
            raise ValueError, "the start and end elementary moves should commute..."
        return [w, wS, wE, wSE]

    # the following function tries to close the mesh
    @cached_method
    def close_mesh(self, wS, i, wE, j):
        if wS is None or wE is None:
            return []
        wSE = self.elementary_moves(wS, j, side='end')
        wES = self.elementary_moves(wE, i, side='start')
        if wSE != wES:
            raise ValueError, "the start and end elementary moves should commute..."
        if not self.is_self_kissing_undirected_walk(wSE):
            return [(wS, wE, wSE)]
        else:
            (wSS, ii) = self.elementary_move_next_nonkissing(wS, side='start')
            (wEE, jj) = self.elementary_move_next_nonkissing(wE, side='end')
            return self.close_mesh(wSS, i + ii, wE, j) + self.close_mesh(wS, i, wEE, j + jj)

    def meshes(self, w):
        r'''
            Return the real meshes starting at walk w, taking into account self-kissing walks.

            The definition is not clear...
        '''
        (wS, i) = self.elementary_move_next_nonkissing(w, side='start')
        (wE, j) = self.elementary_move_next_nonkissing(w, side='end')
        return self.close_mesh(wS, i, wE, j)

    def all_meshes(self):
        r'''
            Return all meshes from all walks.
        '''
        return flatten([self.meshes(w) for w in self.undirected_blossoming_quiver_walks()], max_level=1)

    def Auslander_Reiten_quiver_slice(self):
        r'''
            Return the Auslander-Reiten quiver.
   
           It is not working at the moment.
        '''
        walks = [w for w in self.blossoming_quiver_walks() if not self.is_straight(w) and not self.is_self_kissing_undirected_walk(w)]
        edges = []
        for w in walks:
            wS = self.elementary_move(w, side='start')
            if wS is not None:
                edges.append((w, wS))
            wE = self.elementary_move(w, side='end')
            if wE is not None:
                edges.append((w, wE))
        G = Graph(edges)
        # at the moment, we have two copies of each path, thus two connected components. We only keep one of these components. 
        return G.subgraph(G.connected_components()[0])

    # Geometry: g-vector fan and non-kissing associahedron

    def g_vector(self, w):
        r'''
            Return the g-vector of a walk w.
        '''
        res = {v:0 for v in self.vertices()}
        for i in range(2, len(w)-2, 2):
            if w[i-1][-1] == '-' and w[i+1][-1] != '-':
                res[w[i]] += 1
            if w[i-1][-1] != '-' and w[i+1][-1] == '-':
                    res[w[i]] += -1
        return vector([res[v] for v in self.vertices()])

    def non_kissing_fan(self):
        r'''
            Return the g-vector fan of the quiver.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: F = Q.non_kissing_fan()
                sage: F
                Rational polyhedral fan in 3-d lattice N
                sage: F.nrays()
                11
        '''
        nkc = self.non_kissing_complex()
        all_g_vectors = {w: self.g_vector(w) for w in nkc.vertices()}
        return Fan([Cone([all_g_vectors[w] for w in f]) for f in nkc.facets()])

    def non_kissing_associahedron(self):
        r'''
            Return the non-kissing associahedron associated to the quiver.

            EXAMPLES::

                sage: Q = GentleQuiver({'e1':{'e2':['a']}, 'e2':{'e3':['b']}, 'e3':{'e1':['c']}}, [('a','b')])
                sage: Q.non_kissing_associahedron()
                A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 18 vertices
            '''
        return Polyhedron(ieqs=[[self.blossoming_quiver().total_kissing_number_undirected_walk(w)] + list(self.g_vector(w)) for w in self.relevant_walks()])

# Examples of relevant gentle quivers

def quiver_type_A(n):
    r'''
        Construct the quiver of type A_n.

        EXAMPLES::

            sage: Q = quiver_type_A(4)
            sage: Q.edges()
            [('e1', 'e2', 'a1'), ('e2', 'e3', 'a2'), ('e3', 'e4', 'a3')]
            sage: Q.ideal()
            []
    '''
    return GentleQuiver({'e'+str(i):{'e'+str(i+1):['a'+str(i)]} for i in range(1,n)})

def grid_quiver(n=0, m=0, subset=[]):
    r'''
        Construct the grid quiver defined by a subset X of Z^2.
        If n > 0 and m > 0, then constructs the n x m grid

        EXAMPLES::

            sage: Q = grid_quiver(n=2, m=2)
            sage: Q.vertices()
            ['e.1.0', 'e.1.1', 'e.2.0', 'e.2.1']
            sage: Q.edges()
            [('e.1.0', 'e.1.1', 'a.0.0.v'),
            ('e.1.0', 'e.2.0', 'a.0.0.h'),
            ('e.1.1', 'e.2.1', 'a.0.1.h'),
            ('e.2.0', 'e.2.1', 'a.1.0.v')]
            sage: Q.ideal()
            [('a.0.0.h', 'a.1.0.v'), ('a.0.0.v', 'a.0.1.h')]
    '''
    if n > 0 and m > 0:
        X = [(i,j) for i in range(n) for j in range(m)]
    else:
        X = subset
    def vertex(i,j):
        # The vertex (i,j) is denoted e.i.j.
        return 'e.'+str(i+1)+'.'+str(j)
    def arrow(i,j,dir):
        # The arrow from (i,j) in direction dir (v for vertical, h for horizontal) is denoted a.i.j.dir.
        return 'a.'+str(i)+'.'+str(j)+'.'+dir
    arrows = {(i,j) : dict() for (i,j) in X}
    for (i,j) in X:
        if (i+1,j) in X:
            arrows[(i,j)][vertex(i+1,j)] = [arrow(i,j,'h')]
        if (i,j+1) in X:
            arrows[(i,j)][vertex(i,j+1)] = [arrow(i,j,'v')]
    quiver = {vertex(i,j) : arrows[(i,j)] for (i,j) in X}
    ideal = [(arrow(i-1,j,'h'), arrow(i,j,'v')) for (i,j) in X if (i-1,j) in X and (i,j+1) in X] + [(arrow(i,j-1,'v'), arrow(i,j,'h')) for (i,j) in X if (i,j-1) in X and (i+1,j) in X]
    return GentleQuiver(quiver, ideal=ideal)

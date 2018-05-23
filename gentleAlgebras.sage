
# ALGÈBRES AIMABLES
# 
# Une algèbre aimable $A = kQ/I$ est l'algèbre d'un carquois $Q$ avec relations $I$ tels que :
#    - $I$ est engendré par des chemins de longueur 2,
#    - tout sommet est incident à au plus 2 flèches entrantes et 2 flèches sortantes,
#    - pour toute flèche $\beta$, il y a au plus une flèche $\alpha$ telle que $\alpha\beta \in I$ (resp. telle que $\alpha\beta \notin I$),
#    - pour toute flèche $\beta$, il y a au plus une flèche $\gamma$ telle que $\beta\gamma \in I$ (resp. telle que $\beta\gamma \notin I$).

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
        DiGraph.show(self, edge_labels=True, **args)

    def edges_in(self, vertex):
        'Returns the labels of the incoming edges to a vertex'
        return [l for s,t,l in self.edges() if t == vertex]

    def edges_out(self, vertex):
        'Returns the labels of the outgoing edges to a vertex'
        return [l for s,t,l in self.edges() if s == vertex]

    def ideal(self):
        'Returns the ideal of the bound quiver'
        return self._ideal

    def copy(self, **ignored):
        'Return a copy of the bound quiver'
        return type(self)(self, ideal=deepcopy(self._ideal), name=self.name(), pos=deepcopy(self._pos))

    # See if the quiver matches the definition of a gentle quiver
    ##### NOTE THAT THIS DOESN'T CHECK IF "I" IS AN ADMISSIBLE IDEAL!
    #####     (Maybe this can be done with G.all_cycles_iterator()?)
    def is_gentle(self):
        'Checks that the bound quiver is gentle'
        # We suppose that the ideal is admissible
        
        # We need to test each vertex
        for v in self.vertices():
            ins = self.edges_in(v)
            outs = self.edges_out(v)

            # For every vertex we must have at most 2 arrows in and 2 arrows out
            if len(ins) > 2 or len(outs) > 2:
                print "num wrong"
                return False
            # For each vertex every arrow going in/out can have at most 1 arrow with/without a relation
            # To do this we grab all arrows coming in/out
            # Then if we have a relation, we remove the in/out arrow from our lists
            # If we then have a relation that uses the same in/out arrow, we'll get an error contradicting at most 1 arrow with relation
            # At the end, if there are 2 arrows left in ins/outs then we get an error contradicting at most 1 arrow without relation
            cins = copy(ins)
            couts = copy(outs)
            for i in self._ideal:
                if i[0] in cins:
                    if i[0] not in ins or i[1] not in outs:
                        return False
                    else:
                        ins.remove(i[0])
                        outs.remove(i[1])
            if (len(ins) > 1 and len(outs) > 0) or (len(ins) > 0 and len(outs) > 1):
                return False
        return True

    def inverse(self, l):
        'Returns the inverse of a label'
        if l[-1] == '-':
            return l[:-1]
        else:
            return l+'-'

    def inverse_walk(self, w):
        'Returns the inverse of a walk'
        res = []
        for i in range(len(w)-2, 0, -2):
            res += [w[i+1], self.inverse(w[i])]
        return tuple(res + [w[0]])

    def same_signs(self, l1, l2):
        return (l1[-1] == '-' and l2[-1] == '-') or (l1[-1] != '-' and l2[-1] != '-') 

    def different_signs(self, l1, l2):
        return (l1[-1] == '-' and l2[-1] != '-') or (l1[-1] != '-' and l2[-1] == '-') 

    def quiver_paths(self, with_idems=False):
        r'''
            Returns all paths on the quiver.
            Paths are represented by tuples (v0, a1, v1, ..., ak, vk) where vi are vertices and ai are arcs. 
        '''
        next_possible_arrows = {l1:[[l2,t2] for s2,t2,l2 in self.edges() if s2 == t1 and (l1,l2) not in self._ideal] for s1,t1,l1 in self.edges()}
        start = [tuple([s,l,t]) for s,t,l in self.edges()]
        res = RecursivelyEnumeratedSet(start, lambda x: [tuple(list(x)+n) for n in next_possible_arrows[x[-2]]], structure='forest')
        if with_idems:
            res += self.vertices()
        return res

    def quiver_walks(self):
        r'''
            Returns all walks on the quiver, that is maximal walks using arrows or antiarrows
            Walks are represented by tuples (v0, a1, v1, ..., ak, vk) where vi are vertices and ai are arcs. 
        '''
        from collections import defaultdict
        next_possible_arrows = defaultdict(list)
        for s1,t1,l1 in self.edges():
            for s2,t2,l2 in self.edges():
                if s2 == t1 and (l1,l2) not in self._ideal:
                    next_possible_arrows[l1].append([l2,t2])
                    next_possible_arrows[self.inverse(l2)].append([self.inverse(l1),s1])
                if t2 == t1 and l1 != l2:
                    next_possible_arrows[l1].append([self.inverse(l2),s2])
                if s2 == s1 and l1 != l2:
                    next_possible_arrows[self.inverse(l1)].append([l2,t2])
        start = [tuple([s,l,t]) for s,t,l in self.edges() if next_possible_arrows[self.inverse(l)] == []] + [tuple([t,self.inverse(l),s]) for s,t,l in self.edges() if next_possible_arrows[l] == []]
        return RecursivelyEnumeratedSet(start, lambda x: [tuple(list(x)+n) for n in next_possible_arrows[x[-2]]], structure='forest', post_process = lambda x: x if next_possible_arrows[x[-2]] == [] else None)

    def undirected_quiver_walks(self):
        'Returns only one representative per undirected walk of the quiver'
        res = []
        for w in self.quiver_walks():
            if self.inverse_walk(w) not in res:
                res.append(w)
        return res

    def is_straight(self, w):
        r'''
        Checks that a walk is straight.
        Works both for directed or undirected walks.
        '''
        # be carefull that only odd indices correspond to arcs.
        return len([w[2*i+1] for i in range(len(w)/2) if w[2*i+1][-1] == '-']) in [0,len(w)/2]

    def kissing_walks(self, w1, w2):
        'Tests if two walks are kissing'
        for i in range(1, len(w1)-2, 2):
            for j in range(1, len(w2)-2, 2):
                if w1[i] != w2[j] and w1[i+1] == w2[j+1]:
                    k = 2
                    while i+k < len(w1) and j+k < len(w2) and w1[i+k] == w2[j+k]:
                        k += 2
                    if i+k < len(w1) and j+k < len(w2) and self.different_signs(w1[i], w1[i+k]) and self.different_signs(w2[j], w2[j+k]):
                        # in case the common substring is restricted to a vertex, we need extra care
                        if k > 2 or (w1[i] != self.inverse(w2[j+k]) and w1[i+k] != self.inverse(w2[j])):
                            return True
        return False

    def kissing_undirected_walks(self, w1, w2):
        'Tests if two undirected walks are kissing'
        return self.kissing_walks(w1, w2) or self.kissing_walks(w1, self.inverse_walk(w2))

class GentleQuiver(BoundQuiver):
    # we need all these paramters to properly work with DiGraph
    def __init__(self, data=None, ideal=[], **args):
        # Creates the quiver
        BoundQuiver.__init__(self, data=data, ideal=ideal, **args)

        # Require that our quiver be gentle
        if not BoundQuiver.is_gentle(self):
            raise TypeError('Quiver provided is not gentle')

    # Since we do a test in the beginning if it's gentle, this should always return True
    def is_gentle(self):
        return True

    def blossoming_quiver(self):
        'Return the blossoming quiver of the gentle quiver'
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

    def koszul_dual(self):
        r'''
            Returns the Koszul dual of the quiver.
            Relations and non-relations are exchanged.
        '''
        res = self.copy()
        res._ideal = [(l1, l2) for s1,t1,l1 in self.edges() for s2,t2,l2 in self.edges() if t1 == s2 and (l1,l2) not in self._ideal]
        return res

    def blossoming_quiver_walks(self):
        'Returns all walks on the blossoming quiver'
        return self.blossoming_quiver().quiver_walks()

    def undirected_blossoming_quiver_walks(self):
        'Returns all undirected walks on the blossoming quiver'
        return self.blossoming_quiver().undirected_quiver_walks()

    def non_kissing_complex(self):
        'Returns the non-kissing complex of the gentle quiver'
        non_self_kissing_walks = [w for w in self.undirected_blossoming_quiver_walks() if not self.is_straight(w) and not self.kissing_undirected_walks(w, w)]
        non_kissing_graph = Graph([non_self_kissing_walks, lambda w1, w2: w1 != w2 and not self.kissing_undirected_walks(w1, w2)])
        return non_kissing_graph.clique_complex()

def quiver_type_A(n):
    return GentleQuiver({'e'+str(i):{'e'+str(i+1):['a'+str(i+1)]} for i in range(n)})


# coding: utf-8

# ALGÈBRES AIMABLES
# 
# Une algèbre aimable $A = kQ/I$ est l'algèbre d'un carquois $Q$ avec relations $I$ tels que :
#    - $I$ est engendré par des chemins de longueur 2,
#    - tout sommet est incident à au plus 2 flèches entrantes et 2 flèches sortantes,
#    - pour toute flèche $\beta$, il y a au plus une flèche $\alpha$ telle que $\alpha\beta \in I$ (resp. telle que $\alpha\beta \notin I$),
#    - pour toute flèche $\beta$, il y a au plus une flèche $\gamma$ telle que $\beta\gamma \in I$ (resp. telle que $\beta\gamma \notin I$).

from mygap import mygap

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
        'Returns the incoming edges to a vertex'
        return [e for s,t,e in self.edges() if t == vertex]

    def edges_out(self, vertex):
        'Returns the outgoing edges to a vertex'
        return [e for s,t,e in self.edges() if s == vertex]
   
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
    
    def semi_group(self):
        r'''
        Returns the semigroup of the bound quiver
        'z' is the zero.
        '''
        Q = self
        I = self._ideal
        FSG = mygap.FreeSemigroup(Q.vertices() + Q.edge_labels() + ['z'])
        edge_gens = {e:g for (e,g) in zip(Q.vertices() + Q.edge_labels() + ['z'], FSG.semigroup_generators())}
        zeros = []
        for u in Q.vertices():
            zeros.append([edge_gens[u]^2, edge_gens[u]]) # eu is an idempotent
            for v in Q.vertices():
                if u != v:
                    zeros.append([edge_gens[u] * edge_gens[v], edge_gens['z']]) # eu * ev = 0
        for a in Q.edges():
            zeros.append([edge_gens[a[2]] * edge_gens['z'], edge_gens['z']]) # a*0 = 0
            zeros.append([edge_gens['z'] * edge_gens[a[2]], edge_gens['z']]) # 0*a = 0
            for u in Q.vertices():
                zeros.append([edge_gens[u] * edge_gens[a[2]], edge_gens[a[2]] if u == a[0] else edge_gens['z']]) # if a = (u,v) then eu*a = a else eu*a = 0
                zeros.append([edge_gens[a[2]] * edge_gens[u], edge_gens[a[2]] if u == a[1] else edge_gens['z']]) # if a = (u,v) then a*ev = a else a*ev = 0
        for i in I:
            zeros.append([edge_gens[i[0]] * edge_gens[i[1]], edge_gens['z']]) # a*b is not a path
        return FSG / zeros

    def quiver_paths(self):
        'Returns all paths on the quiver'
        sg = self.semi_group()
        if not sg.is_finite():
            raise ValueError('your algebra is not finite...')
        else:
            sg._refine_category_()
            return [Word(str(path).split('*')) for path in sg.list()]
    
    def maximal_quiver_paths(self):
        'Returns all maximal paths on the quiver'
        nonTrivialPaths = [w for w in self.quiver_paths() if w[0][0] not in ['e','z']]
        return Poset((nonTrivialPaths, lambda v,w: v.is_factor(w))).maximal_elements()
    
    def _walks_quiver(self):
        'Returns the quiver which will enable to compute all walks'
        res = BoundQuiver(self, ideal=deepcopy(self._ideal), name=self.name(), pos=deepcopy(self._pos))
        for s,t,l in self.edges():
            lm = l+'-'
            res.add_edge(t,s,lm)
            res._ideal.append([l,lm])
            res._ideal.append([lm,l])
        return res
    
    def quiver_walks(self):
        'Returns all walks on the quiver'
        return self._walks_quiver().maximal_quiver_paths()

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

    def blossomingQuiver(self):
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

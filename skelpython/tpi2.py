#encoding: utf8

# YOUR NAME: Rodrigo Abreu
# YOUR NUMBER: 113626

# COLLEAGUES WITH WHOM YOU DISCUSSED THIS ASSIGNMENT (names, numbers):
# - ...
# - ...

from semantic_network import *
from constraintsearch import *
from bayes_net import *
from itertools import product

class MySN(SemanticNetwork):

    def __init__(self):
        SemanticNetwork.__init__(self)

    def query(self, entity, relname):
        decls = self.query_local(relname=relname)
  
        if relname in ["member", "subtype"]:
            return list({decl.relation.entity2 for decl in decls if decl.relation.entity1 == entity})
  
        to_check, visited, valid_decls = [entity], set(), []
        while to_check:
            current_entity = to_check.pop()
            if current_entity in visited:
                continue
            visited.add(current_entity)
            valid_decls.extend(decl for decl in decls if decl.relation.entity1 == current_entity)
            to_check.extend(decl.relation.entity2 for decl in self.query_local(e1=current_entity) if decl.relation.name in ["subtype", "member"])
  
        if any(isinstance(decl.relation, AssocSome) for decl in valid_decls):
            return list({decl.relation.entity2 for decl in valid_decls if isinstance(decl.relation, AssocSome)})
  
        total_types = { type(decl.relation).__name__.lower(): sum(1 for d in valid_decls if type(d.relation) == type(decl.relation)) for decl in valid_decls }
        
        if not total_types:
            return []
  
        most_frequent_type = max(total_types, key=total_types.get)
        valid_decls = [decl for decl in valid_decls if  most_frequent_type == type(decl.relation).__name__.lower()]
  
        direct_declarations = [decl for decl in valid_decls if decl.relation.entity1 == entity]
        if direct_declarations:
            valid_decls = direct_declarations
  
        if most_frequent_type == "assocone":
            return [max({decl.relation.entity2: sum(1 for d in valid_decls if d.relation.entity2 == decl.relation.entity2) for decl in valid_decls}, key=lambda k: k[1])]
  
        elif most_frequent_type == "assocnum":
            assocnum_values = [decl.relation.entity2 for decl in valid_decls if isinstance(decl.relation.entity2, (int, float))]
            return [sum(assocnum_values) / len(assocnum_values)] if assocnum_values else []
  
        return []

class MyBN(BayesNet):

    def __init__(self):
        BayesNet.__init__(self)

    def test_independence(self, v1, v2, given):
        def find_ancestors(var, ancestors):
            [ancestors.add(parent) or find_ancestors(parent, ancestors) 
             for (mt, mf, _) in self.dependencies.get(var, []) for parent in mt + mf if parent not in ancestors]

        relevant_vars = set([v1, v2] + given)
        all_ancestors = set(); 
        [find_ancestors(var, all_ancestors) for var in relevant_vars]
        graph = {}
        for var in relevant_vars | all_ancestors:
            if var not in graph:
                graph[var] = set()
            for (mt, mf, _) in self.dependencies.get(var, []):
                for parent in mt + mf:
                    graph.setdefault(parent, set()).add(var)
                    graph[var].add(parent)

        for var in relevant_vars | all_ancestors:
            parents = {parent for (mt, mf, _) in self.dependencies.get(var, []) for parent in mt + mf}
            for p1 in parents:
                for p2 in parents:
                    if p1 != p2:
                        graph.setdefault(p1, set()).add(p2)
                        graph.setdefault(p2, set()).add(p1)

        for given_var in given:
            if given_var in graph:
                for neighbor in list(graph[given_var]):
                    graph[neighbor].discard(given_var)
                del graph[given_var]

        def has_path(v1, v2):
            visited, queue = set(), [v1]
            while queue:
                current = queue.pop(0)
                if current == v2: 
                    return True
                visited.add(current)
                queue.extend(neighbor for neighbor in graph.get(current, []) if neighbor not in visited)
            return False

        edges = [(key, neighbor) for key in graph for neighbor in graph[key] if key < neighbor]
        return edges, not has_path(v1, v2)

class MyCS(ConstraintSearch):

    def __init__(self, domains, constraints):
        ConstraintSearch.__init__(self, domains, constraints)

    def search_all(self, domains=None):
        if not domains:
            domains = self.domains
        if any([len(lv) == 0 for lv in domains.values()]):
            return []
        if all([len(lv) == 1 for lv in domains.values()]):
            return [{v: lv[0] for v, lv in domains.items()}]

        var = min((v for v in domains if len(domains[v]) > 1), key=lambda v: len(domains[v]))
        solutions = []
        for val in domains[var]:
            new_domains = dict(domains)
            new_domains[var] = [val]
            self.propagate(new_domains, var)
            solutions.extend(self.search_all(new_domains))

        return [dict(t) for t in {tuple(sorted(sol.items())) for sol in solutions}]

def handle_ho_constraint(domains, constraints, variables, constraint):
    joinded_var = "".join(variables)
    domains[joinded_var] = [vals for vals in product(*(domains[var] for var in variables)) if constraint(vals)]
    for i, var in enumerate(variables):
        constraints[(var, joinded_var)] = lambda a,b,c,d, index=i: d[index] == b
        constraints[(joinded_var, var)] = lambda a,b,c,d, index=i: b[index] == d

    return domains, constraints

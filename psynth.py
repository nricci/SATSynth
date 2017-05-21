import alloy
from alloy.cli import als2cnfbed
from alloy.relations import Relations
from alloy.kodkod import Relation
from minisat import minisat
import sys, os, platform
from subprocess import call


import logging
#Log  = logging.getLogger(__name__)

import time

VERSION = "bottomup 1.0b1 save instances"


def vars_to_atom_indexes(s, rs):
	return map(lambda v: rs.v2rt[v][1], s)

def vars_to_named_rel(s, rs):
	return map(lambda t: tuple(rs.ind2an[e] for e in t), vars_to_atom_indexes(s, rs))

def named_rel_to_atom_indexes(rel, rs):
	return map(lambda t: tuple(rs.an2ind[e] for e in t), rel)

def atom_indexes_to_vars(rind, rel, rs):
	return map(lambda t: rs.rt2v[rind, t], rel)

def named_rel_to_vars(rind, rel, rs):
	rai = named_rel_to_atom_indexes(rel, rs)
	return atom_indexes_to_vars(rind, rai, rs)

# rel se obtiene de ejecutar vars_to_named_rel(s, rs) para algun s: set Vars, rs: Relations
def named_rel_to_alloy(name, nrel):
	if nrel == []:
		return name + ' in none->none'
	else:
		return name + ' in ' + ' + '.join(map(lambda p: p[0] + '->' + p[1], nrel))

def bound_to_alloy(bdname, s, rs):
	return named_rel_to_alloy(bdname, vars_to_named_rel(s, rs))


def write_instance(rs, rels, path_als, ith_solving):
    filename = './instances/' + path_als[path_als.rfind('/')+1:path_als.rfind('.')] + '-i' + str(ith_solving) + '.txt'
#    print 'writing current instance to file: ' + filename
    f = open(filename, 'w')

    towrite = []
    for a in rs.atoms:
		if a.domain == 'Node':
			towrite.append(a.domain + "$" + a.number)
    f.write('nodes=' + ','.join(towrite) + '\n')

    #print rs.v2rt
    for j in xrange(len(rels)):
		r = rels[j]
		towrite = []
		#if r.name == "Node.val":
		print r.name,
		for v in r.vrange:
			if z.evalmodel(v) == '1':
				#towrite.append(rs.ind2an[rs.v2rt[v][1][0]] + ':' + format_atom_name(rs.ind2an[rs.v2rt[v][1][1]]))
				print rs.atoms[rs.v2rt[v][1][0]], "->", rs.atoms[rs.v2rt[v][1][1]]
				#print " "
					#towrite.append(rs.atoms[rs.v2rt[v][1][0]])
					#f.write(r.name + '=' + ','.join(towrite) + '\n')

    f.close()

def to_dot(rs, rels, path_als, ith_solving):
	filename = './instances/' + path_als[path_als.rfind('/')+1:path_als.rfind('.')] + '-i' + str(ith_solving) + '.dot'
	filenamejson = './instances/' + path_als[path_als.rfind('/')+1:path_als.rfind('.')] + '-i' + str(ith_solving) + '.json'

	#    print 'writing current instance to file: ' + filename
	f = open(filename, 'w')
	f2 = open(filenamejson, 'w')

	nodes = set()
	succ = dict()
	actions = dict()
	val = dict()
	for a in rs.atoms:
		if a.domain == 'Node':
			n = a.domain + a.number
			nodes.add(n)
			val[n] = set()
	#print "---------"
	#print rs;
	#print "---------"
	for r in rs.rels:
		# is the relation binary
		#print r
		if len(r.shape) == 2:
			if r.name == "Node.val":
				for v in r.vrange:
					if z.evalmodel(v) != '1': continue
					node = rs.atoms[rs.v2rt[v][1][0]]
					node = node.domain + node.number
					value = rs.atoms[rs.v2rt[v][1][1]]
					value = value.domain
					value = value.replace("Prop_","")
					value = value.replace("Res_","")
					value = value.replace("OwnsRes_","")
					if not value.startswith("Aux"):
						val[node].add(value)
			else:
				#print "entro"
				rel = dict()
				for v in r.vrange:
					if z.evalmodel(v) != '1': continue
					node1 = rs.atoms[rs.v2rt[v][1][0]]
					node1 = node1.domain + node1.number
					node2 = rs.atoms[rs.v2rt[v][1][1]]
					node2 = node2.domain + node2.number
					if node1 in rel:
						rel[node1].add(node2)
					else:
						rel[node1] = set()
						rel[node1].add(node2)
				actions[r.name.replace("Node.","").replace("change_", "c_")] = rel
		else:
			for v in r.vrange:
				if z.evalmodel(v) == '1':
					root = rs.atoms[rs.v2rt[v][1][0]]
					root = root.domain + root.number

	#print "---------"
	#print root
	#print "Nodes : ", nodes
	#print "Succ : ", succ
	#print "Val : ", val
	#print "Actions, ", actions
	tricolor = "<FONT COLOR=\"black\">{0}</FONT><FONT COLOR=\"red\">{1}</FONT><FONT COLOR=\"blue\">{2}</FONT>"

	towrite = []
	f.write("digraph {\nrankdir=LR;\n")
	clusters = dict()
	for n in nodes:
		towrite = n + '[shape='+('doublecircle' if n==root else 'circle')+',label=\"' + n + "\n"
		towrite += '\n'.join(val[n])
		towrite += '\"];\n'
		f.write(towrite)
		key = ','.join(sorted(val[n] - {'leftfork','rightfork'}))
		if key in clusters:
			clusters[key].add(n)
		else:
			clusters[key] = set()
			clusters[key].add(n)

	i = 0
	f.write('\n')
	for ck in clusters.keys():
		f.write('subgraph cluster' + str(i) + ' {\n\t' + ';\n\t'.join(clusters[ck]) + '\n\tlabel=\"'+ck+'\";\n\tstyle=filled;\n\tcolor=lightgray;\n}\n' )
		i += 1

	for a in actions:
		if a.startswith("$Model"): continue
		action = actions[a]
		for n in action.keys():
			for m in action[n]:
				l0 = a
				l1 = "-"
				l2 = "-"
				if not a.startswith("c_"):
					if n in actions["$Model_" + a + "1"]:
						if m in actions["$Model_" + a + "1"][n]:
							l1 = "F1"
					if n in actions["$Model_" + a + "2"]:
						if m in actions["$Model_" + a + "2"][n]:
							l2 = "F2"
				f.write(n + " -> " + m + "[label=<"+tricolor.format(l0,l1,l2)+">];\n")

	f.write("}")
	f.close()

	## -------------- JSON ---------------

	f2.write("{")
	f2.write("\"nodes\" : [")
	f2.write(',\n'.join(map(lambda n: "{\"id\":\""+n+"\",\"name\":\""+','.join(val[n])+"\"}",nodes)))
	f2.write("],")
	f2.write("\"links\" : [")
	ll = list()
	for a in actions:
		action = actions[a]
		for n in action.keys():
			for m in action[n]:
				ll.append("{\"source\":\""+n+ "\",\"target\":\""+m+"\"}")
	f2.write(',\n'.join(ll))
	f2.write("]")
	f2.write("}")
	f2.close()




def format_atom_name(atom):
    barpos = atom.find("/")
    if barpos != -1:
        return atom[barpos+1:]
    i32pos = atom.find("i32")
    if i32pos != -1:
        return atom[3:]
    return atom

if __name__ == '__main__':

	assert len(sys.argv) == 2, "usage: {} path_to_alsfile".format(sys.args[0])
	path_als = os.path.abspath(sys.argv[1])
	nodename = platform.node()

	print("This is {} running on {}\nExperiment starting at {}".format(VERSION, nodename, time.strftime("%c")))
	print("\nTranslating {} to .cnf and .rels... ".format(path_als))

	t0 = time.time()

	t_before_xlation = time.time()
	output = als2cnfbed(path_als)
	t_after_xlation = time.time()
	xlation_seconds = t_after_xlation - t_before_xlation

	path_cnf = output.path_cnf
	path_rels = output.path_rels

	print("\nParsing {}".format(path_rels))
	rs = Relations(path_rels)

	print("\nCreating native solver instance")
	z = minisat.Zolver()

	print("Parsing {}".format(path_cnf))
	z.read(path_cnf)

	rels = [rel for rel in rs.rels if rel.name == "Node.Next" or rel.name == "Node.val" or rel.name == "$Model_s"  ]

	#print "atoms:",  rs.atoms
	#print "hello"
	#for rel in rels:
	#	print rel.name
	#	for var in rel.vrange:
	#		print rs.v2rt[var], ", ",

	print("\nGoing to compute bounds for: {}\n\n".format([r.name for r in rels]))

	pending = {}

	for rel in rels:
		pending[rel.name] = set(rel.vrange)

	t1 = time.time()
	print("Elapsed so far: {} s".format(t1 - t0))

	newsolvertime = 0
	ith_solving = 0

	bound = dict()
	boundalloy = dict()
	clbound = []

	verdict = True
	while verdict:
		verdict = z.solve()
		print "Found one"
		if verdict == True:
			ith_solving += 1
			to_dot(rs, rels, path_als, ith_solving)
			call(["sh", "dot2jpeg.sh"])
			print "Press key (time elapsed {:.2f} s)".format(time.time()-t0)
			c = sys.stdin.read(1)

			cl = []
			for j in xrange(len(rels)):
				r = rels[j]
				for v in r.vrange:
					if z.evalmodel(v) == '1':
						cl.append(-v)
					else:
						cl.append(v)
			z.addclause(cl)

	t2 = time.time()

	print("Total elapsed time: {:.2f} s".format((t2 - t0)))
	print("Number of instances: {}".format(ith_solving))
	print("\n")

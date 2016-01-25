from sys import argv

queries =list()

kb = dict()	#Implicative form statements
facts = set() #facts
factdict = dict()

visited = set()

stdIndex = 0





#--------------------------------------------------------------------------------------

class UnionFind:

	#ugroup dict is to store representation node for each node
	#numlinks is used for storing num links for each node
    def __init__(self):
        self.numlinks = {}
        self.ugroup = {}

    def __getitem__(self, object):

        if object not in self.ugroup:
            self.ugroup[object] = object
            self.numlinks[object] = 1
            return object

        path = [object]
        root = self.ugroup[object]
        while root != path[-1]:
            path.append(root)
            root = self.ugroup[root]

        for ancestor in path:
            self.ugroup[ancestor] = root
        return root
        
    def __iter__(self):
        return iter(self.ugroup)

    def union(self, *objects):
        roots = [self[x] for x in objects]
        for r in roots:
            if not isVar(r):
                primekey = r
                break
            else:
                primekey = max([(self.numlinks[r],r) for r in roots])[1]
        for r in roots:
            for i in self.ugroup.keys():
                if self.ugroup[i] == r:
                    self.ugroup[i] = primekey
            if r != primekey:
                self.numlinks[primekey] += self.numlinks[r]
                self.ugroup[r] = primekey


class Literal(object):
	"""
	Predicate over variables or constants
	"""

	def __init__(self, line):

		self.type = 'l' #l for literal

		if line[0]=='~':
			self.positive = False
			line = line[1:]
		else:
			self.positive = True

		bracket1 = line.find('(')

		self.pred = line[:bracket1]
		self.terms = line[bracket1+1:-1].split(',')


	def __repr__(self):
		return self.eng()
		return "Literal: " + str(self.positive) + "  " + self.pred + "\n\t\t" + str(self.terms) + "\n"


	def eng(self):
		l = "" if self.positive else "~"
		return l + self.pred + '(' + ','.join([i for i in self.terms]) + ')'


	def __eq__(self, other):
		return self.eng() == other.eng()


	def __hash__(self):
		"""
		For comparison in set
		"""
		return 6


	def pIndex(self):
		"""
		Predicate with sign for indexing
		"""
		l="~" if not self.positive else ""
		return l + self.pred




#--------------------------------------------------------------------------------------

class Statement(object):
	"""
	Conjunction of Literals implying another Literal
	"""

	def __init__(self, line):
		"""
		line is a split list of the original line
		"""

		#Generating LHS: List of literals

		self.type = 's'	#s for Statement
		self.str = line
		self.lhs = list()
		line = line.split()
		llen = len(line)
		for i in range(llen):
			l = line.pop(0)
			if l=="=>":
				break
			if l=="^":
				continue
			self.lhs.append(Literal(l))


		#Generating RHS: Single literal
		self.rhs = Literal(line[0])

		self.str = self.eng()

	def __repr__(self):
		return self.eng()
		return "Statement: " + " lhs: \n\t" + str(self.lhs) + " rhs: \n\t" + str(self.rhs) + "\n"


	def eng(self):
		return " ^ ".join([i.eng() for i in self.lhs]) + " => " + self.rhs.eng()


#--------------------------------------------------------------------------------------

def standardize(rule):
	global stdIndex
	stdRule = Statement(rule.str)

	for i in range(len(stdRule.lhs)):
		for j in range(len(stdRule.lhs[i].terms)):
			if isVar(stdRule.lhs[i].terms[j]):
				stdRule.lhs[i].terms[j] = stdRule.lhs[i].terms[j] + str(stdIndex)
	for i in range(len(stdRule.rhs.terms)):
		if isVar(stdRule.rhs.terms[i]):
			stdRule.rhs.terms[i] = stdRule.rhs.terms[i] + str(stdIndex)
	stdIndex += 1
	return stdRule

def unstandardize(lit):
	stdRule = Literal(lit.eng())
	for i in range(len(stdRule.terms)):
		if isVar(stdRule.terms[i]):
			stdRule.terms[i] = stdRule.terms[i][0]
	return stdRule

def isVar(str):
	return str[0].islower()

def combineSub(a,b):
	sub = dict()
	for bk in b.keys():
		#if a.get(bk)!= None and a.get(bk)!=b[bk]:
		#	return False
		sub[bk] = b[bk]
	for ak in a.keys():
		#if b.get(ak)!= None and b.get(ak)!=a[ak]:
		#	return False
		sub[ak] = a[ak]
	return sub

def arrange(rule):
	#Literals with same predicate should come at the end
	conseq = rule.rhs.pIndex()
	for i in range(len(rule.lhs)-1,-1,-1):
		if rule.lhs[i].pIndex() == conseq:
			rule.lhs = rule.lhs + [rule.lhs.pop(i)]
	return rule
#--------------------------------------------------------------------------------------

def subst(lit, sub):
	substituted = Literal(lit.eng()) #Substituted
	for i in range(len(substituted.terms)):
		val = sub.get(substituted.terms[i])
		if val:
			substituted.terms[i] = val
	return substituted

def unify(var, con, sub):
	#create new sub. return false if conflict. check if there is a condition when no sub reqd but always true. finally check if negation of the formed lit is in the facts section if all variables have been replaced. if yes, return false.
	if sub==False:
		return False
	elif var.positive!=con.positive:
		return False
	elif var==con:
		return {}#sub
	else:
		newsub = dict()

		uf = UnionFind()
		for v in sub.values():
			uf[v]
		for i in range(len(var.terms)):
			v = var.terms[i]
			c = con.terms[i]
			if not isVar(v) and not isVar(c): #done0
				if v!=c:
					return False
			if isVar(v): 
				if newsub.get(v)==None: #done1
						newsub[v]=uf[c]
						continue


				x =uf[newsub[v]]
				if not isVar(c):
					if not isVar(x) and x!=c: #done3
						return False

				uf.union(c,x) #done2, done4

		for k in newsub.keys():
			newsub[k] = uf[newsub[k]]
		uf = UnionFind()
		for v in sub.values():
			uf[v]
		for i in range(len(var.terms)):
			c = var.terms[i]
			v = con.terms[i]
			if not isVar(v) and not isVar(c): #done0
				if v!=c:
					return False
			if isVar(v): 
				if newsub.get(v)==None: #done1
						newsub[v]=uf[c]
						continue


				x =uf[newsub[v]]
				if not isVar(c):
					if not isVar(x) and x!=c: #done3
						return False

				uf.union(c,x) #done2, done4

		for k in newsub.keys():
			newsub[k] = uf[newsub[k]]
		return combineSub(newsub,sub)
	return False

def getVal(gen):
	try:
		val = gen.next()
		return val
	except:
		return None
#--------------------------------------------------------------------------------------

def bc_or(goal, sub={}):
	"""
	#goal is the query. Need an OR of the goal to be True.
	returns a substitution. orig is if it is the original query.will return true the first time a substitution is found.
	"""

	global visited
	
	#FIXME
	subvf = verifyFact(goal)#FIXMEsubst(goal, sub))
	subvf_sol = getVal(subvf)
	while subvf_sol!=None and subvf_sol!=False:
		yield combineSub(subvf_sol, sub)
		subvf_sol = getVal(subvf)


	if not hasVariable(goal):
		ugoal = goal
		#ugoal = unstandardize(subst(goal,sub))
		if ugoal.eng() in visited:
			yield None
		visited.add(ugoal.eng())

	rules = kb.get(goal.pIndex())
	if rules:
		for s in rules:
			stdS = standardize(s)
			stdS = arrange(stdS)
			and_sol = bc_and(stdS.lhs, unify(stdS.rhs, goal, sub))
			val = getVal(and_sol)
			while val!= None:
				if val!=False:
					yield val
				val = getVal(and_sol)
			
def bc_and(goals, sub={}):
	"""
	goals are the literals on the lhs that must be True together. Need an AND of the goals to be True.
	returns a substitution
	"""

	#Case where UNIFY fails
	if sub==False:
		yield None

	#Case where no more goals to be checked
	if len(goals)==0:
		yield sub

	first = goals[0]
	rest = goals[1:]
	or_sol = bc_or(subst(first, sub), sub)
	or_val = getVal(or_sol)
	while or_val!= None:
		if rest:
			and_sol = bc_and(rest, combineSub(or_val, sub))
			and_val = getVal(and_sol)
			while and_val!= None:
				yield and_val
				and_val = getVal(and_sol)
		else:
			yield or_val
		or_val = getVal(or_sol)

#--------------------------------------------------------------------------------------
#FIXME

def hasVariable(lit):
	for t in lit.terms:
		if isVar(t):
			return True
	return False

def verifyFact(query):
	global facts
	hasVar = hasVariable(query)
	match = False
	if not hasVar:
		if query in facts:
			yield {}
	else:
		subs = list()
		qfacts = factdict.get(query.pIndex())
		if qfacts:
			for qf in qfacts:
				uni = unify(query, qf, {})
				if uni!=False:
					yield uni


def parse(line):
	if line.find("=>") == -1:
		return Literal(line)
	return Statement(line)


def ask(query):
	ans = bc_or(query, {})
	ans_val = getVal(ans)
	if ans_val!=None:
		return True
	return False




#--------------------------------------------------------------------------------------
def main():
	global queries, kb, facts, factdict, visited

	f = open(argv[2], 'r')

	#Reading queries
	numq = int(f.readline())
	for i in range(numq):
		queries.append(Literal(f.readline().strip()))

	#Reading kb
	nums = int(f.readline())
	for i in range(nums):
		s = parse(f.readline().strip())
		if s.type=='l':
			facts.add(s)
			if s.pIndex() not in factdict.keys():
				factdict[s.pIndex()] = list()
			factdict[s.pIndex()].append(s)
		else:
			if s.rhs.pIndex() not in kb.keys():
				kb[s.rhs.pIndex()] = list()
			kb[s.rhs.pIndex()].append(s)

	#----------------------------------------------------

	g = open('output.txt', 'w')
	g.close()
	for q in queries:
		b = str(ask(q)).upper()
		if b=="TRUE":
			facts.add(q)
		g = open('output.txt', 'a')
		g.write( b + "\n")
		g.close()
		visited = set()

	#-----------------------------------------------------

	f.close()

if __name__=="__main__":
	main()
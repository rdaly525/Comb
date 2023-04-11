def PostFilteringAlgorithm():
  rdb = RuleDatabase()
  #Synthesize all Rules
  #Number of IR Instructions
  for nIR in range(maxIR):
    #Number of ISA Instrcutions
    for nISA in range(maxISA):
      #Each possible set of IR instructions
      for IRInsts in multi_comb(nIR, AllIRInsts):
        #Each possible set of ISA instructions
        for ISAInsts multi_comb(nISA, AllISAInsts):
          #Each possible function type
          for T in enum_Ts(IRInsts, ISAInsts):
            query = create_query(IRInsts, ISAInsts)
            #Canonicalize symmetries
            query &= sym_constraints
            while True:
              sol = CEGIS(query)
              #Break if no rule was found
              if sol is UNSAT:
                break
              #Every solution represents a rewrite rule
              rdb.add(decodeRule(sol))

  # Post Filtering
  for rule in rdb:
    if rule matches any other rule in rdb:
      rdb.remove(rule)

def IncrementalFilteringAlgorithm():
  rdb = RuleDatabase()
  #Synthesize all Rules
  #Number of IR Instructions
  for nIR in range(maxIR):
    #Number of ISA Instrcutions
    for nISA in range(maxISA):
      #Each possible set of IR instructions
      for IRInsts in multi_comb(nIR, AllIRInsts):
        #Each possible set of ISA instructions
        for ISAInsts in multi_comb(nISA, AllISAInsts):
          #Each possible function type
          for T in enum_Ts(IRInsts, ISAInsts):
            query = create_query(IRInsts, ISAInsts)
            #Canonicalize symmetries
            query &= sym_constraints
            while True:
              sol = CEGIS(query)
              #Break if no rule was found
              if sol is UNSAT:
                break
              #Every solution represents a rewrite rule
              rdb.add(decodeRule(sol))
              #Exclude current rule
              query &= ~sol

  # Post Filtering
  for rule in rdb:
    if rule matches any other rule in rdb:
      rdb.remove(rule)


def IncremantalFilteringAlgorithm():
  rdb = RuleDatabase()
  #Synthesize all Rules
  #Number of IR Instructions
  for nIR in range(maxIR):
    #Number of ISA Instrcutions
    for nISA in range(maxISA):
      #Each possible set of IR instructions
      for IRInsts in multi_comb(nIR, AllIRInsts):
        #Each possible set of ISA instructions
        for ISAInsts multi_comb(nISA, AllISAInsts):
          query = create_query(IRInsts, ISAInsts)
          #Canonicalize symmetries
          query &= sym_constraints
          while True:
            sol = CEGIS(query)
            #Break if no rule was found
            if sol is UNSAT:
              break
            #Every solution represents a rewrite rule
            rdb.add(decodeRule(sol))
            #Exclude All equivalent rules
            for other_sol in enum_equiv_rules(sol):
              query &= ~other_sol

  # Post Filtering
  for rule in rdb:
    if rule matches any other rule in rdb:
      rdb.remove(rule)
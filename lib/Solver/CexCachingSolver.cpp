//===-- CexCachingSolver.cpp ----------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Solver.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/SolverImpl.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/ExprVisitor.h"
#include "klee/util/IndependenceAnalysis.h"
#include "klee/Internal/ADT/MapOfSets.h"

#include "SolverStats.h"

#include "llvm/Support/CommandLine.h"

#include <ciso646>
#ifdef _LIBCPP_VERSION
#include <unordered_map>
#define unordered_map std::unordered_map
#else
#include <tr1/unordered_map>
#define unordered_map std::tr1::unordered_map
#endif

using namespace klee;
using namespace llvm;

namespace {
  cl::opt<bool>
  DebugCexCacheCheckBinding("debug-cex-cache-check-binding");

  cl::opt<bool>
  CexCacheTryAll("cex-cache-try-all",
                 cl::desc("try substituting all counterexamples before asking the SMT solver"),
                 cl::init(false));

  cl::opt<bool>
  CexCacheExperimental("cex-cache-exp", cl::init(false));

  cl::opt<bool>
  CexQuickCache("quick-cache",
                cl::desc("Enable the QuickCache optimization in CexCachingSolver (default=on)"),
                cl::init(true));

  cl::opt<bool>
  CexPrevSolution("prev-solution",
                  cl::desc("Enable the Previous Solution optimization in CexCachingSolver (default=on)"),
                  cl::init(true));

  cl::opt<bool>
  CexDisableSuperSet("disable-super-set",
                     cl::desc("Disable the CexCachingSolver check for super set solutions (default=on)"),
                     cl::init(true));
}

///

typedef std::set< ref<Expr> > KeyType;

struct AssignmentLessThan {
  bool operator()(const Assignment *a, const Assignment *b) {
    return a->bindings < b->bindings;
  }
};

struct QuickCacheEntry {
  KeyType constraints;

  QuickCacheEntry(const KeyType &key)
    : constraints(key) {}

  QuickCacheEntry(const QuickCacheEntry &ce)
    : constraints(ce.constraints) {}

  bool operator==(const QuickCacheEntry &b) const {
    return constraints.size() == b.constraints.size() && constraints == b.constraints;
  }
};

struct QuickCacheEntryHash {
  unsigned operator()(const QuickCacheEntry &ce) const {
    unsigned comboHash = 0;
    for (KeyType::const_iterator it = ce.constraints.begin(); it != ce.constraints.end(); it++){
      comboHash += (*it).get()->hash();
    }
    return comboHash;
  }
};


class CexCachingSolver : public SolverImpl {
  typedef std::set<Assignment*, AssignmentLessThan> assignmentsTable_ty;

  typedef unordered_map<QuickCacheEntry,
                        Assignment *,
                        QuickCacheEntryHash> cache_map;

  Solver *solver;
  
  cache_map quickCache;

  MapOfSets<ref<Expr>, Assignment*> cache;
  // memo table
  assignmentsTable_ty assignmentsTable;

  bool searchForAssignment(KeyType &key, 
                           Assignment *&result);
  
  bool lookupAssignment(const Query& query, KeyType &key, Assignment *&result);

  bool lookupAssignment(const Query& query, Assignment *&result) {
    KeyType key;
    return lookupAssignment(query, key, result);
  }

  // Caching operations
  bool getFromQuickCache(const KeyType & key, Assignment * &assignment);
  void insertInQuickCache(const KeyType & key, Assignment * &binding);
  void insertInCaches(const KeyType & key, Assignment * &binding);

  bool checkPreviousSolutionHelper(const ref<Expr>, const std::set<ref<Expr> > &key, Assignment * &result);
  bool checkPreviousSolution(const Query &query, Assignment *&result);

  bool guessIndependent(const Query& query,
                        Assignment *parentSolution,
                        Assignment *&result);

  bool getAssignment(const Query& query, Assignment *&result);
  
public:
  CexCachingSolver(Solver *_solver) : solver(_solver) {}
  ~CexCachingSolver();
  
  bool computeTruth(const Query&, bool &isValid);
  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeValue(const Query&, ref<Expr> &result);
  bool computeInitialValues(const Query&,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query& query);
  void setCoreSolverTimeout(double timeout);
};

///

struct NullAssignment {
  bool operator()(Assignment *a) const { return !a; }
};

struct NonNullAssignment {
  bool operator()(Assignment *a) const { return a!=0; }
};

struct NullOrSatisfyingAssignment {
  KeyType &key;
  
  NullOrSatisfyingAssignment(KeyType &_key) : key(_key) {}

  bool operator()(Assignment *a) const { 
    return !a || a->satisfies(key.begin(), key.end()); 
  }
};

/// searchForAssignment - Look for a cached solution for a query.
///
/// \param key - The query to look up.
/// \param result [out] - The cached result, if the lookup is succesful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return - True if a cached result was found.
bool CexCachingSolver::searchForAssignment(KeyType &key, Assignment *&result) {
  TimerStatIncrementer t(stats::cexUBTime);

  Assignment * const *lookup = cache.lookup(key);
  if (lookup) {
    ++stats::cexLookupHits;
    result = *lookup;
    return true;
  }

  if (CexCacheTryAll) {
    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = cache.findSuperset(key, NonNullAssignment());
    
    // Otherwise, look for a subset which is unsatisfiable, see below.
    if (!lookup) 
      lookup = cache.findSubset(key, NullAssignment());

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }

    // Otherwise, iterate through the set of current assignments to see if one
    // of them satisfies the query.
    for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
           ie = assignmentsTable.end(); it != ie; ++it) {
      Assignment *a = *it;
      if (a->satisfies(key.begin(), key.end())) {
        result = a;
        return true;
      }
    }
  } else {
    // FIXME: Which order? one is sure to be better.

    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = 0;
    if(!lookup && !CexDisableSuperSet) {
      TimerStatIncrementer tSuper(stats::cexUBSuperTime);
      lookup = cache.findSuperset(key, NonNullAssignment());
      if(lookup) {
        ++stats::cexUBSuperHits;
      }
    }

    // Otherwise, look for a subset which is unsatisfiable -- if the subset is
    // unsatisfiable then no additional constraints can produce a valid
    // assignment. While searching subsets, we also explicitly the solutions for
    // satisfiable subsets to see if they solve the current query and return
    // them if so. This is cheap and frequently succeeds.
    if (!lookup) {
      TimerStatIncrementer tSub(stats::cexUBSubTime);
      lookup = cache.findSubset(key, NullOrSatisfyingAssignment(key));
      if(lookup) {
        ++stats::cexUBSubHits;
      }
    }

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }
  }
  
  return false;
}


bool
CexCachingSolver::getFromQuickCache(const KeyType &key, Assignment * &result){
  QuickCacheEntry ce(key);
  cache_map::iterator it = quickCache.find(ce);

  if (it != quickCache.end()) {
    result = it ->second;
    return true;
  }
  return false;
}

void
CexCachingSolver::insertInQuickCache(const KeyType &key, Assignment * &binding){
  QuickCacheEntry ce(key);
  quickCache.insert(std::make_pair(ce, binding));
}

void
CexCachingSolver::insertInCaches(const KeyType &key, Assignment * &binding){
  insertInQuickCache(key, binding);
  cache.insert(key, binding);
}

bool
CexCachingSolver::checkPreviousSolutionHelper(const ref<Expr> queryExpr,
                                              const std::set<ref<Expr> > &key,
                                              Assignment * &result){
  Assignment * parentSolution = 0;
  if (getFromQuickCache(key, parentSolution)){
    if (!parentSolution){
      // Means that the the previous state was UNSAT and therefore the
      // new answer will also necessarily be UNSAT (Subsumes UNSAT)
      result = 0;
      return true;
    } else {
      // Means that there is in fact a parent solution.  In this case,
      // we can now check whether this parent solution satisfies the
      // child state.  There's a pretty good chance... at least 50/50
      ref<Expr> neg = Expr::createIsZero(queryExpr);
      ref<Expr> q = parentSolution->evaluate(neg);

      assert(isa<ConstantExpr>(q) && "assignment evaluation did not result in constant");
      if (cast<ConstantExpr>(q)->isTrue()){
        result = parentSolution;
        return true;
      } else {
        // If goes false, that means that the point that had gotten us to our parent
        // went along the opposing branch and it won't help us at this stage.
        return false;
      }
    }
  }
  assert(!parentSolution);
  return false;
}

bool
CexCachingSolver::checkPreviousSolution(const Query &query, Assignment * &result){
  if (query.constraints.size() == 0){
    return false;
  }

  std::set<ref<Expr> > parentKey;
  ref<Expr> queryExpr;
  if (isa<ConstantExpr>(query.expr)){
    assert(cast<ConstantExpr>(query.expr)->isFalse() && "query.expr == true should'd happen");
    for (unsigned i = 0; i < query.constraints.size() - 1; i ++){
      ref<Expr> ref = query.constraints.get(i);
      parentKey.insert(ref);
    }

    ref<Expr> toNeg = query.constraints.get(query.constraints.size() - 1);
    queryExpr = Expr::createIsZero(toNeg);
  } else {
    for (unsigned i = 0; i < query.constraints.size(); i ++){
      ref<Expr> ref = query.constraints.get(i);
      parentKey.insert(ref);
    }
    queryExpr = query.expr;
  }

  if (checkPreviousSolutionHelper(queryExpr, parentKey, result)){
    // result may contain one of two things
    //  - A 0, meaning that the previous piece of the was UNSAT and therefore new is too
    //  - An actual result which we should verify is correct.
    return true;
  } else {
    return false;
  }
}

bool CexCachingSolver::guessIndependent(const Query& query,
                                        Assignment *parentSolution,
                                        Assignment * &result){

  /*
   * At this point we know that the point going through the state
   * prior to us is NOT helpful.  That means that it must go down
   * the opposite branch.  What this means is that we were close,
   * but no cigar.
   *
   * What I would like to do, therefore, is get all of the constraints
   * DIRECTLY associated with the newest constraint.  I would then
   * look in the cache for a result for the DIRECT piece.  I would
   * then overwrite the indices of the previous state's solution with
   * the answers for the DIRECT piece.
   *
   * Final note: it seems likely I will need to fill the quickCache
   * much more carefully.  Perhaps things like using a renamer and
   * pulling apart a solution every which way to increase chances of
   * future hits.  For example (x > 1) && (x < 15) -> (x==5) would
   * result in quickCache[x>1] = (x==5) and quickCache[x<15] = (x==5)
   *
   * OVERALL IDEA:
   * 1) Get expression that is new
   *    - If it is something like arr[x], then just RETURN FALSE
   * 2) Get all expressions DIRECTLY associated with new expression
   *    - Use the same setup as in IndependentSolver
   * 3) See if this small piece exists
   *    - If it doesn't, then just RETURN FALSE
   * 4) Get the two results associated with each
   *    - For each piece of the DIRECTLY associated expressions,
   *      overwrite the big result
   * 5) See if it works
   *    - If works, then resultNoTouch = newResult, and RETURN TRUE
   *    - If doesn't, then just RETURN FALSE.
   */

  //TODO
  //if(newExpr contains arr[x]) return false;

  std::vector<ref<Expr> > unsafeFactor;
  IndependentElementSet ies = getIndependentConstraintsUnsafe(query, unsafeFactor);

  //TODO: I think this check needs to be improved
  if(unsafeFactor.size() == query.constraints.size() || ies.elements.size() == 0){
    return false;
  }

  Assignment * newestAssignment = 0;
  ConstraintManager tmp(unsafeFactor);
  Query optimisticQuery = Query(tmp,  query.expr);

  // Recursively call get assignment at the unsafe factor the of the larger
  // constraint.  This factor will only contain elements directly related to
  // the fresh part of the constraints. We insert true into the optional
  // skipStats part in order to avoid having this recursive "helper" call
  // messing up the stats of the actual process.
  if(!getAssignment(optimisticQuery, newestAssignment)){
    return false;
  }else if(!newestAssignment){
    // means the solution is impossible, and therefore the entire constraint
    // is impossible! (see lookupAssignment docs)
    result = 0;
    return true;
  }else{
    result = new Assignment(*parentSolution, *newestAssignment, ies);
    ref<Expr> neg = Expr::createIsZero(query.expr);
    ref<Expr> q = result->evaluate(neg);

    assert(isa<ConstantExpr>(q) && "assignment evaluation did not result in constant");
    if(cast<ConstantExpr>(q)->isTrue()  && result->satisfies(query.constraints.begin(), query.constraints.end())){
      return true;
    }else{
      delete result;
      return false;
    }
  return false;
  }
}

/// lookupAssignment - Lookup a cached result for the given \arg query.
///
/// \param query - The query to lookup.
/// \param key [out] - On return, the key constructed for the query.
/// \param result [out] - The cached result, if the lookup is succesful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return True if a cached result was found.
bool CexCachingSolver::lookupAssignment(const Query &query, 
                                        KeyType &key,
                                        Assignment *&result) {
  key = KeyType(query.constraints.begin(), query.constraints.end());
  ref<Expr> neg = Expr::createIsZero(query.expr);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(neg)) {
    if (CE->isFalse()) {
      result = (Assignment*) 0;
      ++stats::cexHits;
      return true;
    }
  } else {
    key.insert(neg);
  }

  bool found = false;
  if(!found && CexQuickCache) {
    found = getFromQuickCache(key, result);
    if(found){
      ++stats::cexQuickHits;
    }
  }

  if (!found && CexPrevSolution){
    found = checkPreviousSolution(query, result);
    if (found){
      ++stats::cexPrevHits;
      insertInQuickCache(key, result);
    }
  }

  if (!found){
    found = searchForAssignment(key, result);
    if (found){
      ++stats::cexUBHits;
      insertInQuickCache(key, result);
    }
  }

  if (found)
    ++stats::cexHits;
  else
    ++stats::cexMisses;
    
  return found;
}

bool CexCachingSolver::getAssignment(const Query& query, Assignment *&result) {
  KeyType key;
  if (lookupAssignment(query, key, result))
    return true;

  std::vector<const Array*> objects;
  findSymbolicObjects(key.begin(), key.end(), objects);

  std::vector< std::vector<unsigned char> > values;
  bool hasSolution;
  if (!solver->impl->computeInitialValues(query, objects, values, 
                                          hasSolution))
    return false;
    
  Assignment *binding;
  if (hasSolution) {
    binding = new Assignment(objects, values);

    // Memoize the result.
    std::pair<assignmentsTable_ty::iterator, bool>
      res = assignmentsTable.insert(binding);
    if (!res.second) {
      delete binding;
      binding = *res.first;
    }
    
    if (DebugCexCacheCheckBinding)
      assert(binding->satisfies(key.begin(), key.end()));
  } else {
    binding = (Assignment*) 0;
  }
  
  result = binding;
  insertInCaches(key, binding);

  return true;
}

///

CexCachingSolver::~CexCachingSolver() {
  cache.clear();
  quickCache.clear();
  delete solver;
  for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
         ie = assignmentsTable.end(); it != ie; ++it)
    delete *it;
}

bool CexCachingSolver::computeValidity(const Query& query,
                                       Solver::Validity &result) {
  TimerStatIncrementer t(stats::cexTime);
  Assignment *a;
  if (!getAssignment(query.withFalse(), a))
    return false;
  assert(a && "computeValidity() must have assignment");
  ref<Expr> q = a->evaluate(query.expr);
  assert(isa<ConstantExpr>(q) && 
         "assignment evaluation did not result in constant");

  if (cast<ConstantExpr>(q)->isTrue()) {
    if (!getAssignment(query, a))
      return false;
    result = !a ? Solver::True : Solver::Unknown;
  } else {
    if (!getAssignment(query.negateExpr(), a))
      return false;
    result = !a ? Solver::False : Solver::Unknown;
  }
  
  return true;
}

bool CexCachingSolver::computeTruth(const Query& query,
                                    bool &isValid) {
  TimerStatIncrementer t(stats::cexTime);

  // There is a small amount of redundancy here. We only need to know
  // truth and do not really need to compute an assignment. This means
  // that we could check the cache to see if we already know that
  // state ^ query has no assignment. In that case, by the validity of
  // state, we know that state ^ !query must have an assignment, and
  // so query cannot be true (valid). This does get hits, but doesn't
  // really seem to be worth the overhead.

  if (CexCacheExperimental) {
    Assignment *a;
    if (lookupAssignment(query.negateExpr(), a) && !a)
      return false;
  }

  Assignment *a;
  if (!getAssignment(query, a))
    return false;

  isValid = !a;

  return true;
}

bool CexCachingSolver::computeValue(const Query& query,
                                    ref<Expr> &result) {
  TimerStatIncrementer t(stats::cexTime);

  Assignment *a;
  if (!getAssignment(query.withFalse(), a))
    return false;
  assert(a && "computeValue() must have assignment");
  result = a->evaluate(query.expr);  
  assert(isa<ConstantExpr>(result) && 
         "assignment evaluation did not result in constant");
  return true;
}

bool 
CexCachingSolver::computeInitialValues(const Query& query,
                                       const std::vector<const Array*> 
                                         &objects,
                                       std::vector< std::vector<unsigned char> >
                                         &values,
                                       bool &hasSolution) {
  TimerStatIncrementer t(stats::cexTime);
  Assignment *a;
  if (!getAssignment(query, a))
    return false;
  hasSolution = !!a;
  
  if (!a)
    return true;

  // FIXME: We should use smarter assignment for result so we don't
  // need redundant copy.
  values = std::vector< std::vector<unsigned char> >(objects.size());
  for (unsigned i=0; i < objects.size(); ++i) {
    const Array *os = objects[i];
    Assignment::bindings_ty::iterator it = a->bindings.find(os);
    
    if (it == a->bindings.end()) {
      values[i] = std::vector<unsigned char>(os->size, 0);
    } else {
      values[i] = it->second;
    }
  }
  
  return true;
}

SolverImpl::SolverRunStatus CexCachingSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *CexCachingSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void CexCachingSolver::setCoreSolverTimeout(double timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

///

Solver *klee::createCexCachingSolver(Solver *_solver) {
  return new Solver(new CexCachingSolver(_solver));
}

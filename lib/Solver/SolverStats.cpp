//===-- SolverStats.cpp ---------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "SolverStats.h"

using namespace klee;


Statistic stats::queries("Queries", "Q");
Statistic stats::queriesInvalid("QueriesInvalid", "Qiv");
Statistic stats::queriesValid("QueriesValid", "Qv");

Statistic stats::independentTime("IndependentTime","ITime");

Statistic stats::cacheHits("CacheHits", "CHits") ;
Statistic stats::cacheMisses("CacheMisses", "CMisses");
Statistic stats::cacheTime("CacheTime","CTime");

Statistic stats::cexLookupHits("CexLookupHits", "CexLHits");
Statistic stats::cexQuickHits("CexQuickHits", "CexQHits");
Statistic stats::cexPrevHits("CexPrevHits", "CexPHits");
Statistic stats::cexUBHits("CexUBHits", "CexUBHits");
Statistic stats::cexUBSuperHits("CexUBSuperHits", "CexSuperH");
Statistic stats::cexUBSubHits("CexUBSubHits", "CexSubH");
Statistic stats::cexUBTime("CexUBTime", "CexUBTime");
Statistic stats::cexUBSuperTime("CexUBSuperTime", "CexSuperT");
Statistic stats::cexUBSubTime("CexUBSubTime", "CexSubT");
Statistic stats::cexHits("CexCacheHits", "CexHits");
Statistic stats::cexMisses("CexCacheMisses", "CexMisses");
Statistic stats::cexTime("CexCacheTime", "CexTime");

Statistic stats::smtTime("SMTTime", "SMTTime");

Statistic stats::queryConstructTime("QueryConstructTime", "QBTime") ;
Statistic stats::queryConstructs("QueriesConstructs", "QB");
Statistic stats::queryCounterexamples("QueriesCEX", "Qcex");

#ifdef DEBUG
Statistic stats::arrayHashTime("ArrayHashTime", "AHtime");
#endif

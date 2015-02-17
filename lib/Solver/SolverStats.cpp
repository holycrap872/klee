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

Statistic stats::cexCacheHits("CexCacheHits", "CexHits");
Statistic stats::cexCacheMisses("CexCacheMisses", "CexMisses");
Statistic stats::cexCacheTime("CexCacheTime", "CexTime");

Statistic stats::smtTime("SMTTime", "SMTTime");

Statistic stats::queryConstructTime("QueryConstructTime", "QBTime") ;
Statistic stats::queryConstructs("QueriesConstructs", "QB");
Statistic stats::queryCounterexamples("QueriesCEX", "Qcex");

#ifdef DEBUG
Statistic stats::arrayHashTime("ArrayHashTime", "AHtime");
#endif

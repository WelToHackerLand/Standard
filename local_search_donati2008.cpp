#ifndef VRP_LOCAL_SEARCH_Donati2008
#define VRP_LOCAL_SEARCH_Donati2008

#include "VrpSolution.cpp"
#include "Tour.cpp"
#include "PVH_Optimize_Tour_version2.cpp"

namespace LOCAL_SEARCH_Donati2008 {
    struct SequentialSearchProfile {
        int m, numTour;
        vector<int> tripId;
        vector<int> nextNode, prevNode;
        vector<double> costBefore, costAfter;
        vector<int> demandBefore, demandAfter;
        vector<vector<pair<double, int>>> neighborList;
        vector<int> tourStartPoint, tourEndPoint;

        SequentialSearchProfile(const VrpSolution &sol) {
            numTour = sol.tours.size();
            m = VRP_INSTANCE.nNode - 1 + sol.tours.size();
            tripId.resize(m + 1);
            nextNode.resize(m + 1);
            prevNode.resize(m + 1);
            costBefore.resize(m + 1);
            costAfter.resize(m + 1);
            demandBefore.resize(m + 1);
            demandAfter.resize(m + 1);
            neighborList.resize(m + 1);
            tourStartPoint.resize(sol.tours.size()+1);
            tourEndPoint.resize(sol.tours.size()+1);

            for (int iTour = 0; iTour < (int) sol.tours.size(); ++iTour) {
                const Tour &tour = sol.tours[iTour];
                for (int i = 1; i + 1 < (int) tour.length(); ++i) {
                    tripId[tour[i]] = iTour + 1;
                    nextNode[tour[i]] = tour[i + 1];
                    prevNode[tour[i]] = tour[i - 1];

                    for (int y = 1; y <= m; ++y) {
                        if (y != tour[i]) {
                            double dist = VRP_INSTANCE.distances[tour[i]][0];
                            if (y < VRP_INSTANCE.nNode) {
                                dist = VRP_INSTANCE.distances[tour[i]][y];
                            }

                            auto &NL = neighborList[tour[i]];
                            NL.emplace_back(dist, y);
                            push_heap(NL.begin(), NL.end());
                            if (NL.size() > PARAMS.graspNNLength) {
                                pop_heap(NL.begin(), NL.end());
                                NL.pop_back();
                            }
                        }
                    }
                    sort_heap(neighborList.begin(), neighborList.end());
                }

                // connect to virtual depots
                prevNode[tour[1]] = VRP_INSTANCE.nNode + iTour;
                nextNode[VRP_INSTANCE.nNode + iTour] = tour[1];
                tripId[VRP_INSTANCE.nNode + iTour] = iTour + 1;

                int depotId = (iTour + 1 < (int) sol.tours.size() ? VRP_INSTANCE.nNode + iTour + 1 : VRP_INSTANCE.nNode);
                nextNode[tour[tour.length() - 2]] = depotId;
                prevNode[depotId] = tour[tour.length() - 2];

                /// build StartPoint and EndPoint
                tourStartPoint[iTour+1] = VRP_INSTANCE.nNode + iTour;
                tourEndPoint[iTour+1] = depotId;

                // cumulative vectors
                for (int i = 1; i + 1 < tour.length(); ++i) {
                    costBefore[tour[i]] = costBefore[tour[i - 1]] + VRP_INSTANCE.distances[tour[i - 1]][tour[i]];
                    demandBefore[tour[i]] = demandBefore[tour[i - 1]] + VRP_INSTANCE.demands[tour[i]];
                }

                for (int i = tour.length() - 2; i > 0; --i) {
                    costAfter[tour[i]] = costAfter[tour[i + 1]] + VRP_INSTANCE.distances[tour[i + 1]][tour[i]];
                    demandAfter[tour[i]] = demandAfter[tour[i + 1]] + VRP_INSTANCE.demands[tour[i]];
                }
            }
        }

        void debug() {
            cerr << m << " " << numTour << '\n';

            cerr << "VER: ";
            int cc = VRP_INSTANCE.nNode, cnt = 0;
            while (cnt++ <= m) {
                cerr << cc;
                if ( cc >= VRP_INSTANCE.nNode ) cerr << "(" << 0 << ")";
                cerr << " ";
                cc = nextNode[cc];
            }
            cerr << "\n\n";

            cerr << "ID: ";
            cc = VRP_INSTANCE.nNode, cnt = 0;
            while (cnt++ <= m) {
                cerr << tripId[cc];
                if ( cc >= VRP_INSTANCE.nNode ) cerr << "(" << 0 << ")";
                cerr << " ";
                cc = nextNode[cc];
            }
            cerr << '\n';
        }

        void recalculateTrip(int id) {
            int startNode = VRP_INSTANCE.nNode - 1 + id;
            int lastNode = startNode;

            for (int x = nextNode[startNode]; x < VRP_INSTANCE.nNode; x = nextNode[x]) {
                demandBefore[x] = demandBefore[prevNode[x]] + getDemand(x);
                costBefore[x] = costBefore[prevNode[x]] + getDist(prevNode[x], x);
                tripId[x] = id;
                lastNode = x;
            }

            for (int x = lastNode; x != startNode; x = prevNode[x]) {
                demandAfter[x] = demandAfter[nextNode[x]] + getDemand(x);
                costAfter[x] = costAfter[nextNode[x]] + getDist(x, nextNode[x]);
            }
        }

        VrpSolution toSolution() const {
            VrpSolution sol;
            for (int depotId = VRP_INSTANCE.nNode; depotId <= m; ++depotId) {
                sol.tours.emplace_back();
                Tour &tour = sol.tours.back();

                tour.append(0);
                for (int x = nextNode[depotId]; x < VRP_INSTANCE.nNode; x = nextNode[x]) {
                    tour.append(x);
                }
                tour.append(0);
            }

            return sol.trim();
        }

        void validate() {
            int nodeCnt = 0;
            for (int depotId = VRP_INSTANCE.nNode; depotId <= m; ++depotId) {
                int cumulativeDemand = 0;
                double cumulativeCost = 0;
                int x = nextNode[depotId];
                while (x < VRP_INSTANCE.nNode) {
                    cumulativeCost += getDist(prevNode[x], x);
                    cumulativeDemand += getDemand(x);
                    assert(tripId[x] == tripId[depotId]);
                    assert(abs(cumulativeCost - costBefore[x]) < Common::EPS);
                    assert(cumulativeDemand == demandBefore[x]);

                    x = nextNode[x];
                    nodeCnt++;
                }

                x = prevNode[x];
                cumulativeCost = 0;
                cumulativeDemand = 0;
                while (x < VRP_INSTANCE.nNode) {
                    cumulativeCost += getDist(nextNode[x], x);
                    cumulativeDemand += getDemand(x);
                    assert(abs(cumulativeCost - costAfter[x]) < Common::EPS);
                    assert(cumulativeDemand == demandAfter[x]);

                    x = prevNode[x];
                }
                assert(cumulativeDemand <= VRP_INSTANCE.vehicleCapacity);
            }

            assert(nodeCnt + 1 == VRP_INSTANCE.nNode);
        }

        inline double getDist(int x, int y) const {
            if (x >= VRP_INSTANCE.nNode) x = 0;
            if (y >= VRP_INSTANCE.nNode) y = 0;
            return VRP_INSTANCE.distances[x][y];
        }

        inline int getDemand(int x) const {
            if (x >= VRP_INSTANCE.nNode) x = 0;
            return VRP_INSTANCE.demands[x];
        }

        double getCost() {
            VrpSolution vrp_tour = toSolution();
            double cost = vrp_tour.getCost();
            return cost;
        }
    };

    static bool Customer_relocation(SequentialSearchProfile &profile) {
        /// choose the best
        double bestDeltaCost = -1e-9;
        pair<int, int> bestChoice = make_pair(-1, -1);

        for (int x = 1; x < VRP_INSTANCE.nNode; ++x) {
            int px = profile.prevNode[x], nx = profile.nextNode[x];
            for (int y = 1; y <= profile.m; ++y) {
                /// insert x after position of y
                if (x == y || y == px) continue;
                int ny = profile.nextNode[y];

                bool capFlag = (profile.demandBefore[y] + profile.demandAfter[ny] + profile.getDemand(x) <= VRP_INSTANCE.vehicleCapacity)
                            || (profile.tripId[x] == profile.tripId[y]);

                double deltaCost = profile.getDist(y, x) + profile.getDist(x, ny) + profile.getDist(px, nx);
                                 - profile.getDist(px, x) - profile.getDist(x, nx) - profile.getDist(y, ny);

                if ( capFlag && deltaCost < bestDeltaCost ) {
                    bestDeltaCost = deltaCost;
                    bestChoice = make_pair(x, y);
                }
            } 
        }

        if (bestChoice == make_pair(-1, -1)) return false;
        int x = bestChoice.first, y = bestChoice.second;
        int px = profile.prevNode[x], nx = profile.nextNode[x], ny = profile.nextNode[y];

        profile.nextNode[px] = nx;
        profile.prevNode[nx] = px;

        profile.nextNode[y] = profile.prevNode[ny] = x;
        profile.nextNode[x] = ny;
        profile.prevNode[x] = y;

        int tx = profile.tripId[x], ty = profile.tripId[y];
        profile.recalculateTrip(tx);
        profile.recalculateTrip(ty);

        return true;
    }

    static bool Customer_exchange(SequentialSearchProfile &profile) {
        /// choose the best one
        double bestDeltaCost = -1e-9;
        pair<int, int> exchangePoint = make_pair(-1, -1);

        for (int x = 1; x < VRP_INSTANCE.nNode; ++x) {
            int px = profile.prevNode[x];
            int nx = profile.nextNode[x];
            for (int y = x+1; y < VRP_INSTANCE.nNode; ++y) {
                int py = profile.prevNode[y];
                int ny = profile.nextNode[y];
                bool capFlag = (profile.demandBefore[px] + profile.demandAfter[nx] + profile.getDemand(y) <= VRP_INSTANCE.vehicleCapacity)
                        && (profile.demandBefore[py] + profile.demandAfter[ny] + profile.getDemand(x) <= VRP_INSTANCE.vehicleCapacity);
                double deltaCost = profile.getDist(px, y)
                        + profile.getDist(y, nx)
                        + profile.getDist(py, x)
                        + profile.getDist(x, ny)
                        - profile.getDist(px, x)
                        - profile.getDist(x, nx)
                        - profile.getDist(py, y)
                        - profile.getDist(y, ny);
                if (y == nx) {
                    deltaCost = profile.getDist(px, y)
                            + profile.getDist(x, ny)
                            - profile.getDist(px, x)
                            - profile.getDist(y, ny);
                }
                if (x == ny) {
                    deltaCost = profile.getDist(py, x)
                            + profile.getDist(y, nx)
                            - profile.getDist(py, y)
                            - profile.getDist(x, nx);
                }

                if (capFlag && deltaCost < bestDeltaCost) {
                    bestDeltaCost = deltaCost;
                    exchangePoint = make_pair(x, y);
                }
            }
        }

        if ( exchangePoint == make_pair(-1, -1) ) return false;
        int x = exchangePoint.first, y = exchangePoint.second;
        int px = profile.prevNode[x], nx = profile.nextNode[x];
        int py = profile.prevNode[y], ny = profile.nextNode[y];

        if (y != nx && x != ny) {
            profile.nextNode[px] = profile.prevNode[nx] = y;
            profile.prevNode[y] = px;
            profile.nextNode[y] = nx;

            profile.nextNode[py] = profile.prevNode[ny] = x;
            profile.prevNode[x] = py;
            profile.nextNode[x] = ny;
        } else {
            if (x == ny) swap(x, y), swap(px, py), swap(nx, ny);
            profile.nextNode[x] = ny;
            profile.prevNode[ny] = x;
            profile.prevNode[x] = y;
            profile.nextNode[y] = x;
            profile.prevNode[y] = px;
            profile.nextNode[px] = y;
        }

        int tx = profile.tripId[x];
        int ty = profile.tripId[y];
        profile.recalculateTrip(tx);
        profile.recalculateTrip(ty);

        return true;
    }

    static bool InTour_2_k_opt(SequentialSearchProfile &profile) {
        /// PLOT : inverse subsequence from (nx -> y)
        /// FORM : 0 -> ... -> x -> (nx -> ... -> y) -> ny -> ... -> 0 
        /// ===>   0 -> ... -> x -> (y -> ... -> nx) -> ny -> ... -> 0

        for (int x = 1; x < VRP_INSTANCE.nNode; ++x) {
            int nx = profile.nextNode[x];
            if (nx >= VRP_INSTANCE.nNode) continue;

            for (int y = nx; y < VRP_INSTANCE.nNode; y = profile.nextNode[y]) {
                    // if ( profile.tripId[x] != profile.tripId[y] ) {
                    //     profile.debug();
                    //     cerr << "/?? " << x << " " << y << '\n';
                    //     exit(0);
                    // }
                assert(profile.tripId[x] == profile.tripId[y]);

                int ny = profile.nextNode[y];
                bool capFlag = (profile.demandBefore[x] + profile.demandBefore[y] <= VRP_INSTANCE.vehicleCapacity)
                                && (profile.demandAfter[nx] + profile.demandAfter[ny] <= VRP_INSTANCE.vehicleCapacity);
                double deltaCost = profile.getDist(x, y)
                        + profile.getDist(nx, ny)
                        - profile.getDist(x, nx)
                        - profile.getDist(y, ny);

                    ///***************** ORE NOTE : capFlag for wut ?? ********************* 
                    capFlag = true;

                if (capFlag && deltaCost < -Common::EPS) {
                    profile.prevNode[nx] = profile.nextNode[x] = 0;
                    profile.prevNode[ny] = profile.nextNode[y] = 0;

                    for (int k = nx; k != 0; k = profile.prevNode[k]) {
                        swap(profile.nextNode[k], profile.prevNode[k]);
                    }

                    profile.nextNode[x] = y;
                    profile.prevNode[y] = x;
                    profile.nextNode[nx] = ny;
                    profile.prevNode[ny] = nx;

                    int tx = profile.tripId[x];
                    int ty = profile.tripId[y];
                    profile.recalculateTrip(tx);
                    profile.recalculateTrip(ty);
                    return true;
                }
            }
        }

        return false;
    }

    static bool Branch_relocation(SequentialSearchProfile &profile) {
        /// PLOT : relocation subsequence ( x -> (A) -> y ) into (k -> nk) 
        /// FORM : 0 -> ... -> px -> x -> (A) -> y -> ny -> ... -> 0 -> ... -> k -> nk -> ... -> 0
        /// ===>   0 -> ... -> px -> ny -> ... -> 0 -> ... -> k -> x -> (A) -> y -> nk -> ... -> 0

        bool returnValue = false;
        for (int iTour = 1; iTour <= profile.numTour; ++iTour) {
            bool improvedSolutionFound = false;
            assert( profile.tourStartPoint[iTour] == VRP_INSTANCE.nNode+iTour-1 );

            for (int x = profile.tourStartPoint[iTour]; x != profile.tourEndPoint[iTour]; x = profile.nextNode[x]) {
                if ( improvedSolutionFound ) break;
                if ( x >= VRP_INSTANCE.nNode ) continue;

                int demandX = profile.getDemand(x), px = profile.prevNode[x];
                for (int y = profile.nextNode[x]; y != profile.tourEndPoint[iTour]; y = profile.nextNode[y]) {
                    if ( improvedSolutionFound ) break;

                    int ny = profile.nextNode[y];
                    demandX += profile.getDemand(y);

                    for (int jTour = 1; jTour <= profile.numTour; ++jTour) {
                        if ( iTour == jTour ) continue;
                        if ( improvedSolutionFound ) break;
                        assert( profile.tourStartPoint[jTour] == VRP_INSTANCE.nNode+jTour-1 );

                        int startPoint = profile.nextNode[VRP_INSTANCE.nNode+jTour-1];
                        if ( demandX + profile.demandAfter[startPoint] > VRP_INSTANCE.vehicleCapacity ) continue;
                        
                        for (int k = profile.tourStartPoint[jTour]; k != profile.tourEndPoint[jTour]; k = profile.nextNode[k]) {
                            int nk = profile.nextNode[k];
                            double deltaCost = profile.getDist(k, x) + profile.getDist(y, nk) + profile.getDist(px, ny)
                                             - profile.getDist(px, x) - profile.getDist(y, ny) - profile.getDist(k, nk);
                            if (deltaCost < -1e-9) {
                                profile.nextNode[px] = ny;
                                profile.prevNode[ny] = px;

                                profile.nextNode[k] = x;
                                profile.prevNode[x] = k;
                                profile.nextNode[y] = nk;
                                profile.prevNode[nk] = y;

                                int tx = profile.tripId[x], tk = profile.tripId[k];
                                profile.recalculateTrip(tx);
                                profile.recalculateTrip(tk);

                                improvedSolutionFound = true;
                                returnValue = true;
                                break;
                            }
                        } 
                    }
                }
            }
        }

        return returnValue;
    }

    static bool Branch_exchange(SequentialSearchProfile &profile) {
        bool returnValue = false;
        for (int iTour = 1; iTour <= profile.numTour; ++iTour) {
            bool improvedSolutionFound = false;
            assert( profile.tourStartPoint[iTour] == VRP_INSTANCE.nNode+iTour-1 );

            for (int x = profile.tourStartPoint[iTour]; x != profile.tourEndPoint[iTour]; x = profile.nextNode[x]) {
                if ( improvedSolutionFound ) break;
                if ( x >= VRP_INSTANCE.nNode ) continue;

                int demandX = 0, px = profile.prevNode[x];
                for (int y = x; y != profile.tourEndPoint[iTour]; y = profile.nextNode[y]) {
                    if ( improvedSolutionFound ) break;

                    int ny = profile.nextNode[y];
                    demandX += profile.getDemand(y);

                    for (int jTour = iTour+1; jTour <= profile.numTour; ++jTour) {
                        if ( iTour == jTour ) continue;
                        if ( improvedSolutionFound ) break;
                        assert( profile.tourStartPoint[jTour] == VRP_INSTANCE.nNode+jTour-1 );

                        for (int k = profile.tourStartPoint[jTour]; k != profile.tourEndPoint[jTour]; k = profile.nextNode[k]) {
                            if ( improvedSolutionFound ) break;
                            if ( k >= VRP_INSTANCE.nNode ) continue;
                            
                            int demandK = profile.getDemand(k), pk = profile.prevNode[k];
                            for (int p = profile.nextNode[k]; p != profile.tourEndPoint[jTour]; p = profile.nextNode[p]) {
                                if ( improvedSolutionFound ) break;

                                int np = profile.nextNode[p];
                                demandK += profile.getDemand(p);
                                if ( profile.demandBefore[px] + profile.demandAfter[ny] + demandK > VRP_INSTANCE.vehicleCapacity ) break;

                                bool capFlag = (profile.demandBefore[px] + profile.demandAfter[ny] + demandK <= VRP_INSTANCE.vehicleCapacity)
                                            && (profile.demandBefore[pk] + profile.demandAfter[np] + demandX <= VRP_INSTANCE.vehicleCapacity);
                                double deltaCost = profile.getDist(pk, x) + profile.getDist(y, np) 
                                                 + profile.getDist(px, k) + profile.getDist(p, ny)
                                                 - profile.getDist(px, x) - profile.getDist(y, ny) 
                                                 - profile.getDist(pk, k) - profile.getDist(p, np);
                                
                                if (capFlag && deltaCost < -1e-9) {
                                    profile.nextNode[px] = k; 
                                    profile.prevNode[k] = px;
                                    profile.nextNode[p] = ny;
                                    profile.prevNode[ny] = p;

                                    profile.nextNode[pk] = x;
                                    profile.prevNode[x] = pk;
                                    profile.nextNode[y] = np;
                                    profile.prevNode[np] = y;

                                    int tx = profile.tripId[x], tk = profile.tripId[k];
                                    profile.recalculateTrip(tx);
                                    profile.recalculateTrip(tk);

                                    improvedSolutionFound = true;
                                    returnValue = true;
                                    break;
                                }
                            }
                        } 
                    }
                }
            }
        }

        return returnValue;
    }

    static void Shuffle_the_tour_order(SequentialSearchProfile &profile) {
        VrpSolution vrp_tour = profile.toSolution();
        Common::randomShuffle(vrp_tour.tours);
        SequentialSearchProfile newProfile(vrp_tour);
        profile = newProfile;
    }

    void TotalLocalSearch(VrpSolution &sol) {
        SequentialSearchProfile profile(sol);
        double originalCost = sol.getCost();

        while (true) {
            bool improvedSolution = false;

            if ( Customer_relocation(profile) ) {
                improvedSolution = true;
                    cerr << "***********************\n";
            }
			
				cerr << "1 --> " << profile.getCost() << '\n';

            if ( Customer_exchange(profile) ) {
                improvedSolution = true;
            }
				
				cerr << "2 --> " << profile.getCost() << '\n';

            if ( InTour_2_k_opt(profile) ) {
                improvedSolution = true;
            }
				
				cerr << "3 --> " << profile.getCost() << '\n';

            if ( Branch_relocation(profile) ) {
                improvedSolution = true;
            }
				
				cerr << "4 --> " << profile.getCost() << '\n';

            if (Branch_exchange(profile)) {
                improvedSolution = true;
            }
			
				cerr << "5 --> " << profile.getCost() << '\n';

            Shuffle_the_tour_order(profile);

            if (!improvedSolution) break;
        }

        sol = profile.toSolution();
        sol.validate();
    }

    void HybridLocalSearch(VrpSolution &sol, vector<vector<double> > &tsp_phe) {
        SequentialSearchProfile profile(sol);
        double originalCost = sol.getCost();

        while (true) {
            bool improvedSolution = false;
            // double previousCost = profile.getCost();

            if ( Customer_relocation(profile) ) {
                improvedSolution = true;
            }

            if ( Customer_exchange(profile) ) {
                improvedSolution = true;
            }

            if ( InTour_2_k_opt(profile) ) {
                improvedSolution = true;
            }

            if ( Branch_relocation(profile) ) {
                improvedSolution = true;
            }

            if ( Branch_exchange(profile) ) {
                improvedSolution = true;
            }

            if ( 1 > 0 ) {
                VrpSolution vrp_tour = profile.toSolution();

                int cnt_optimize = 0;
                while ( cnt_optimize <= 20 ) {
                    ++cnt_optimize;
                    if ( PVH_Optimize_Tour_ver2::optimize(vrp_tour, tsp_phe) ) {
                        cnt_optimize = 0;
                        improvedSolution = true;
                    }
                }

                vrp_tour.balance();

                SequentialSearchProfile newProfile(vrp_tour);
                profile = newProfile;
            }

            Shuffle_the_tour_order(profile);

            if (!improvedSolution) break;

        }

        sol = profile.toSolution();
        sol.validate();
    }
}

#endif // VRP_LOCAL_SEARCH_Donati2008

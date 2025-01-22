#include <iostream>
#include <vector>
#include <cmath>
#include <map>
#include <set>
#include <queue>
#include <tuple>
#include <limits>
#include <algorithm>
#include <string>
#include <sstream>

// Cube vertices as in Python
static double cube_vertices[8][3] = {
    {1, 1, 1},
    {1, 4, 1},
    {4, 4, 1},
    {4, 1, 1},
    {1, 1, 4},
    {1, 4, 4},
    {4, 4, 4},
    {4, 1, 4}
};

// Source and end points as in Python
static double source[3] = {-2, 1, 3};
static double endp[3]   = {6, 4, 4};

struct Point {
    double x,y,z;
};

inline bool operator<(const Point &a, const Point &b) {
    if (a.x != b.x) return a.x < b.x;
    if (a.y != b.y) return a.y < b.y;
    return a.z < b.z;
}

inline bool operator==(const Point &a, const Point &b) {
    return (a.x == b.x && a.y == b.y && a.z == b.z);
}

struct Edge {
    Point node;
    double weight;
};

std::map<Point, std::vector<Edge>> graph;

Point arrToPoint(const double arr[3]) {
    Point p; p.x=arr[0]; p.y=arr[1]; p.z=arr[2]; return p;
}

void add_node(const Point &p) {
    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
}

void add_edge(const Point &u, const Point &v, double w) {
    graph[u].push_back({v,w});
    graph[v].push_back({u,w});
}

std::string fmtPoint(const Point &p) {
    std::ostringstream oss;
    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
    return oss.str();
}

std::string fmtArray(const Point &p) {
    std::ostringstream oss;
    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
    return oss.str();
}

std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
    std::ostringstream oss;
    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
    return oss.str();
}

// Distance in 2D for weights
double distance2D(const Point &a, const Point &b) {
    double dx=a.x-b.x; double dy=a.y-b.y;
    return std::sqrt(dx*dx+dy*dy);
}

// Distance in 3D for heuristic
double distance3D(const Point &a, const Point &b) {
    double dx=a.x-b.x; double dy=a.y-b.y; double dz=a.z-b.z;
    return std::sqrt(dx*dx+dy*dy+dz*dz);
}

// This function tries to mimic the logic of Shapely's intersection for line segments:
// Returns true if the segments intersect in their interior (not just touching at endpoints)
// or if they overlap more than a single point when collinear.
// Otherwise returns false (this includes the case where they only share an endpoint).
bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
    double x1 = A.x, y1 = A.y;
    double x2 = B.x, y2 = B.y;
    double x3 = C.x, y3 = C.y;
    double x4 = D.x, y4 = D.y;

    // First, check for collinearity and overlapping
    auto orientation = [&](double ax, double ay, double bx, double by, double cx, double cy) {
        double val = (by - ay)*(cx - bx) - (bx - ax)*(cy - by);
        if (val > 0) return 1; // clockwise
        if (val < 0) return 2; // counterclockwise
        return 0; // collinear
    };

    int o1 = orientation(x1,y1,x2,y2,x3,y3);
    int o2 = orientation(x1,y1,x2,y2,x4,y4);
    int o3 = orientation(x3,y3,x4,y4,x1,y1);
    int o4 = orientation(x3,y3,x4,y4,x2,y2);

    // Helper to check if point (cx,cy) is on segment (ax,ay)-(bx,by)
    auto on_segment = [&](double ax, double ay, double bx, double by, double cx, double cy) {
        return (std::min(ax,bx) <= cx && cx <= std::max(ax,bx) &&
                std::min(ay,by) <= cy && cy <= std::max(ay,by));
    };

    // Check collinear overlap
    if (o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0) {
        // All points are collinear, check overlap
        std::vector<std::pair<double,double>> pts = {{x1,y1},{x2,y2},{x3,y3},{x4,y4}};
        std::sort(pts.begin(), pts.end(), [](auto &p1, auto &p2){
            if (p1.first < p2.first) return true;
            if (p1.first > p2.first) return false;
            return p1.second < p2.second;
        });

        // After sorting, if there's more than one point overlap:
        // Check distance between the middle two after sorting
        double dx = pts[1].first - pts[2].first;
        double dy = pts[1].second - pts[2].second;
        double dist = std::sqrt(dx*dx+dy*dy);
        if (dist > 0.0) {
            // Overlapping more than a point
            return true;
        } else {
            // They share just a single point or no actual overlap beyond a point
            return false;
        }
    }

    // General intersection case:
    // If the line segments properly intersect, the orientations must differ
    if (o1 != o2 && o3 != o4) {
        // Compute intersection point
        double den = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
        if (den == 0.0) {
            // Parallel lines shouldn't come here, but just in case
            return false;
        }

        double ua = ((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/den;
        double ub = ((x2 - x1)*(y1 - y3)-(y2 - y1)*(x1 - x3))/den;

        double ix = x1+ua*(x2-x1);
        double iy = y1+ua*(y2-y1);

        bool isOnA = (ua >=0.0 && ua<=1.0);
        bool isOnB = (ub >=0.0 && ub<=1.0);

        if (isOnA && isOnB) {
            // Check if intersection is an endpoint of both segments (just touching)
            bool isEndpointA = ( (ix == x1 && iy == y1) || (ix == x2 && iy == y2) );
            bool isEndpointB = ( (ix == x3 && iy == y3) || (ix == x4 && iy == y4) );

            // If intersection happens strictly inside one or both segments, it's true intersection
            bool insideA = (ua > 0.0 && ua < 1.0);
            bool insideB = (ub > 0.0 && ub < 1.0);

            if (insideA && insideB) {
                // Proper interior intersection
                return true;
            } else {
                // Intersection on the endpoints:
                // If it's an endpoint for both segments -> touches only
                // If endpoint for one but strictly inside the other still means intersection is inside the other
                // Shapely logic: if they share only one endpoint and no other overlap, that's touches -> false.
                if (isEndpointA && isEndpointB) {
                    // Just touching at a single endpoint
                    return false;
                }

                // If intersection point is endpoint of one line but inside the other, this is an intersection.
                if (isEndpointA && insideB) return true;
                if (isEndpointB && insideA) return true;

                // Otherwise, no actual interior intersection
                return false;
            }
        }

        // If not on both segments, no intersection
        return false;
    }

    // If we reach here, no intersection
    return false;
}


std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
    Point vs[8];
    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
    std::vector<std::pair<Point,Point>> edges = {
        {vs[0],vs[1]},
        {vs[1],vs[2]},
        {vs[2],vs[3]},
        {vs[3],vs[0]},
        {vs[4],vs[5]},
        {vs[5],vs[6]},
        {vs[6],vs[7]},
        {vs[7],vs[4]},
        {vs[0],vs[4]},
        {vs[1],vs[5]},
        {vs[2],vs[6]},
        {vs[3],vs[7]}
    };
    for (auto &e: edges) {
        double w=distance2D(e.first,e.second);
        add_edge(e.first,e.second,w);
    }
    return edges;
}

void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
    Point vs[8];
    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);

    for (int i=0;i<8;i++) {
        Point vertex=vs[i];
        bool intersects=false;
        for (auto &ce: cube_edges) {
            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
                intersects=true;
                break;
            }
        }
        if (!intersects) {
            double w=distance2D(point,vertex);
            add_edge(point,vertex,w);
            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
        }
    }
}

std::vector<Point> astar_path(const Point &start, const Point &goal) {
    std::map<Point,double> gScore;
    std::map<Point,double> fScore;
    std::map<Point,Point> cameFrom;

    for (auto &kv: graph) {
        gScore[kv.first]=std::numeric_limits<double>::infinity();
        fScore[kv.first]=std::numeric_limits<double>::infinity();
    }

    gScore[start]=0.0;
    fScore[start]=distance3D(start,goal);

    // Tie-break counter to mimic Python’s stable ordering
    static long long counter = 0;

    struct PQItem {
        Point node;
        double f;
        long long order;
        bool operator>(const PQItem&o) const {
            if (f == o.f) return order > o.order;
            return f > o.f;
        }
    };

    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
    openSet.push({start,fScore[start],counter++});
    std::map<Point,bool> inOpen;
    inOpen[start]=true;

    while(!openSet.empty()) {
        Point current=openSet.top().node;
        openSet.pop();
        inOpen[current]=false;

        if (current==goal) {
            std::vector<Point> path;
            Point cur=current;
            while(!(cur==start)) {
                path.push_back(cur);
                cur=cameFrom[cur];
            }
            path.push_back(start);
            std::reverse(path.begin(), path.end());
            return path;
        }

        for (auto &edge: graph[current]) {
            Point neighbor=edge.node;
            double tentative=gScore[current]+edge.weight;
            if (tentative<gScore[neighbor]) {
                cameFrom[neighbor]=current;
                gScore[neighbor]=tentative;
                fScore[neighbor]=tentative+distance3D(neighbor,goal);
                if (!inOpen[neighbor]) {
                    openSet.push({neighbor,fScore[neighbor],counter++});
                    inOpen[neighbor]=true;
                }
            }
        }
    }

    return {};
}

int main() {
    Point vs[8];
    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
    Point s=arrToPoint(source);
    Point e=arrToPoint(endp);

    // Add cube vertices as nodes
    for (int i=0;i<8;i++) add_node(vs[i]);
    add_node(s);
    add_node(e);

    // Add cube edges
    auto cube_edges=add_outer_edges_cube();

    // Add edges from source
    std::cout<<"Adding edges from source:\n";
    add_edges_without_intersection(s,cube_edges);

    // Add edges from end
    std::cout<<"\nAdding edges from end:\n";
    add_edges_without_intersection(e,cube_edges);

    // A* search
    std::vector<Point> path=astar_path(s,e);
    if (!path.empty()) {
        std::cout<<"\nShortest path found by A* algorithm:\n[";
        for (size_t i=0;i<path.size();i++) {
            std::cout<<fmtPoint(path[i]);
            if (i+1<path.size()) std::cout<<", ";
        }
        std::cout<<"]\n";
    } else {
        std::cout<<"\nNo path found from source to end.\n";
    }

    return 0;
}



//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//// Cube vertices as in Python
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points as in Python
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = {6, 4, 4};
//
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//struct Edge {
//    Point node;
//    double weight;
//};
//
//std::map<Point, std::vector<Edge>> graph;
//
//Point arrToPoint(const double arr[3]) {
//    Point p; p.x=arr[0]; p.y=arr[1]; p.z=arr[2]; return p;
//}
//
//void add_node(const Point &p) {
//    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
//}
//
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//std::string fmtPoint(const Point &p) {
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//
//std::string fmtArray(const Point &p) {
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//// Distance in 2D for weights (as in Python)
//double distance2D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y;
//    return std::sqrt(dx*dx+dy*dy);
//}
//
//// Distance in 3D for heuristic
//double distance3D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y; double dz=a.z-b.z;
//    return std::sqrt(dx*dx+dy*dy+dz*dz);
//}
//
//// Updated intersection function to closely match Shapely's logic
//bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
//    double x1 = A.x, y1 = A.y;
//    double x2 = B.x, y2 = B.y;
//    double x3 = C.x, y3 = C.y;
//    double x4 = D.x, y4 = D.y;
//
//    auto orientation = [&](double ax, double ay, double bx, double by, double cx, double cy) {
//        double val = (by - ay)*(cx - bx) - (bx - ax)*(cy - by);
//        if (val > 0) return 1; // clockwise
//        if (val < 0) return 2; // counterclockwise
//        return 0; // collinear
//    };
//
//    auto on_segment = [&](double ax, double ay, double bx, double by, double cx, double cy) {
//        return (std::min(ax, bx) <= cx && cx <= std::max(ax, bx) &&
//                std::min(ay, by) <= cy && cy <= std::max(ay, by));
//    };
//
//    int o1 = orientation(x1, y1, x2, y2, x3, y3);
//    int o2 = orientation(x1, y1, x2, y2, x4, y4);
//    int o3 = orientation(x3, y3, x4, y4, x1, y1);
//    int o4 = orientation(x3, y3, x4, y4, x2, y2);
//
//    // General case:
//    if (o1 != o2 && o3 != o4) {
//        // They should intersect at a point.
//        // Compute intersection point
//        double den = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//        if (den == 0.0) {
//            // Parallel or coincident lines with different orientation checks won't get here usually,
//            // but just in case:
//            return false;
//        }
//
//        double ua = ((x4 - x3)*(y1 - y3) - (y4 - y3)*(x1 - x3)) / den;
//        double ix = x1 + ua*(x2 - x1);
//        double iy = y1 + ua*(y2 - y1);
//
//        bool isEndpointA = ((ix == x1 && iy == y1) || (ix == x2 && iy == y2));
//        bool isEndpointB = ((ix == x3 && iy == y3) || (ix == x4 && iy == y4));
//
//        double ub = ((x2 - x1)*(y1 - y3) - (y2 - y1)*(x1 - x3)) / den;
//        bool insideA = (ua > 0.0 && ua < 1.0);
//        bool insideB = (ub > 0.0 && ub < 1.0);
//
//        if (insideA && insideB) {
//            return true;
//        }
//
//        // If intersection is only at endpoints (one or both), it's touching, not intersection
//        return false;
//    }
//
//    // Collinear cases:
//    if (o1 == 0 && o2 == 0 && o3 == 0 && o4 == 0) {
//        // All points are collinear
//        std::vector<std::pair<double,double>> pts = {{x1,y1},{x2,y2},{x3,y3},{x4,y4}};
//        auto lessXY = [&](auto &p1, auto &p2) {
//            if (p1.first < p2.first) return true;
//            if (p1.first > p2.first) return false;
//            return p1.second < p2.second;
//        };
//        std::sort(pts.begin(), pts.end(), lessXY);
//        double dx = pts[1].first - pts[2].first;
//        double dy = pts[1].second - pts[2].second;
//        double dist = std::sqrt(dx*dx+dy*dy);
//
//        if (dist > 0.0) {
//            // Overlapping more than a point = intersection
//            return true;
//        } else {
//            // Just a single point overlap = touches
//            return false;
//        }
//    }
//
//    // No intersection
//    return false;
//}
//
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    // As in Python code, same order
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0],vs[1]},
//        {vs[1],vs[2]},
//        {vs[2],vs[3]},
//        {vs[3],vs[0]},
//        {vs[4],vs[5]},
//        {vs[5],vs[6]},
//        {vs[6],vs[7]},
//        {vs[7],vs[4]},
//        {vs[0],vs[4]},
//        {vs[1],vs[5]},
//        {vs[2],vs[6]},
//        {vs[3],vs[7]}
//    };
//    for (auto &e: edges) {
//        double w=distance2D(e.first,e.second);
//        add_edge(e.first,e.second,w);
//    }
//    return edges;
//}
//
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0;i<8;i++) {
//        Point vertex=vs[i];
//        bool intersects=false;
//        for (auto &ce: cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects=true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w=distance2D(point,vertex);
//            add_edge(point,vertex,w);
//            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point,double> gScore;
//    std::map<Point,double> fScore;
//    std::map<Point,Point> cameFrom;
//
//    for (auto &kv: graph) {
//        gScore[kv.first]=std::numeric_limits<double>::infinity();
//        fScore[kv.first]=std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start]=0.0;
//    fScore[start]=distance3D(start,goal);
//
//    // Tie-break counter to mimic Python’s stable ordering
//    static long long counter = 0;
//
//    struct PQItem {
//        Point node;
//        double f;
//        long long order;
//        bool operator>(const PQItem&o) const {
//            if (f == o.f) return order > o.order;
//            return f > o.f;
//        }
//    };
//
//    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start],counter++});
//    std::map<Point,bool> inOpen;
//    inOpen[start]=true;
//
//    while(!openSet.empty()) {
//        Point current=openSet.top().node;
//        openSet.pop();
//        inOpen[current]=false;
//
//        if (current==goal) {
//            std::vector<Point> path;
//            Point cur=current;
//            while(!(cur==start)) {
//                path.push_back(cur);
//                cur=cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (auto &edge: graph[current]) {
//            Point neighbor=edge.node;
//            double tentative=gScore[current]+edge.weight;
//            if (tentative<gScore[neighbor]) {
//                cameFrom[neighbor]=current;
//                gScore[neighbor]=tentative;
//                fScore[neighbor]=tentative+distance3D(neighbor,goal);
//                if (!inOpen[neighbor]) {
//                    openSet.push({neighbor,fScore[neighbor],counter++});
//                    inOpen[neighbor]=true;
//                }
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    Point s=arrToPoint(source);
//    Point e=arrToPoint(endp);
//
//    // Add cube vertices as nodes
//    for (int i=0;i<8;i++) add_node(vs[i]);
//    add_node(s);
//    add_node(e);
//
//    // Add cube edges
//    auto cube_edges=add_outer_edges_cube();
//
//    // Add edges from source
//    std::cout<<"Adding edges from source:\n";
//    add_edges_without_intersection(s,cube_edges);
//
//    // Add edges from end
//    std::cout<<"\nAdding edges from end:\n";
//    add_edges_without_intersection(e,cube_edges);
//
//    // A* search
//    std::vector<Point> path=astar_path(s,e);
//    if (!path.empty()) {
//        std::cout<<"\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0;i<path.size();i++) {
//            std::cout<<fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout<<", ";
//        }
//        std::cout<<"]\n";
//    } else {
//        std::cout<<"\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}






//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//// Cube vertices as in Python
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points as in Python
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = {6, 4, 4};
//
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//struct Edge {
//    Point node;
//    double weight;
//};
//
//std::map<Point, std::vector<Edge>> graph;
//
//Point arrToPoint(const double arr[3]) {
//    Point p; p.x=arr[0]; p.y=arr[1]; p.z=arr[2]; return p;
//}
//
//void add_node(const Point &p) {
//    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
//}
//
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//std::string fmtPoint(const Point &p) {
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//
//std::string fmtArray(const Point &p) {
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//// Distance in 2D for weights
//double distance2D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y;
//    return std::sqrt(dx*dx+dy*dy);
//}
//
//// Distance in 3D for heuristic
//double distance3D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y; double dz=a.z-b.z;
//    return std::sqrt(dx*dx+dy*dy+dz*dz);
//}
//
//// Check intersection (intersects and not touches), no epsilons:
//bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
//    double x1=A.x, y1=A.y, x2=B.x, y2=B.y;
//    double x3=C.x, y3=C.y, x4=D.x, y4=D.y;
//
//    double den = (y4 - y3)*(x2 - x1)-(x4 - x3)*(y2 - y1);
//
//    auto orientation = [&](double ax,double ay,double bx,double by,double cx,double cy){
//        double val=(by - ay)*(cx - bx)-(bx - ax)*(cy - by);
//        if (val==0.0) return 0;
//        return (val>0)?1:2;
//    };
//
//    // Collinear or parallel
//    if (den==0.0) {
//        int o1=orientation(x1,y1,x2,y2,x3,y3);
//        int o2=orientation(x1,y1,x2,y2,x4,y4);
//        int o3=orientation(x3,y3,x4,y4,x1,y1);
//        int o4=orientation(x3,y3,x4,y4,x2,y2);
//
//        if (o1==0 && o2==0 && o3==0 && o4==0) {
//            // Collinear
//            std::vector<std::pair<double,double>> pts = {{x1,y1},{x2,y2},{x3,y3},{x4,y4}};
//            std::sort(pts.begin(),pts.end(),[&](auto &p1,auto &p2){
//                if (p1.first!=p2.first) return p1.first<p2.first;
//                return p1.second<p2.second;
//            });
//            double dx=pts[1].first - pts[2].first;
//            double dy=pts[1].second - pts[2].second;
//            double dist=std::sqrt(dx*dx+dy*dy);
//            if (dist>0.0) {
//                // Overlapping more than a point
//                return true;
//            } else {
//                // Only one point overlap - touches
//                return false;
//            }
//        } else {
//            // Parallel no intersection
//            return false;
//        }
//    }
//
//    double ua=((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/den;
//    double ub=((x2 - x1)*(y1 - y3)-(y2 - y1)*(x1 - x3))/den;
//
//    if (ua>=0.0 && ua<=1.0 && ub>=0.0 && ub<=1.0) {
//        double ix = x1+ua*(x2-x1);
//        double iy = y1+ua*(y2-y1);
//
//        bool onAEnd = ((ix==x1 && iy==y1)||(ix==x2 && iy==y2));
//        bool onBEnd = ((ix==x3 && iy==y3)||(ix==x4 && iy==y4));
//
//        bool insideA=(ua>0.0 && ua<1.0);
//        bool insideB=(ub>0.0 && ub<1.0);
//
//        if (insideA && insideB) {
//            return true; // Interior intersection
//        } else {
//            // Endpoint cases
//            if (onAEnd && onBEnd) {
//                // Shared endpoint only = touches
//                return false;
//            } else if (onAEnd && !onBEnd) {
//                // A's endpoint hits B
//                // If insideB => intersection (endpoint of A on interior of B)
//                if (insideB) return true;
//                return false; // otherwise touches
//            } else if (!onAEnd && onBEnd) {
//                // B's endpoint hits A
//                if (insideA) return true;
//                return false;
//            } else {
//                // Intersection on boundary but not on endpoints?
//                // That would mean ua=0 or 1 or ub=0 or 1 but not exactly endpoints matched due to floating issues.
//                // With exact checks, if not on endpoints and not inside, means line meets exactly at boundary of one line at a point not recognized as endpoint?
//                // Without epsilons, if it doesn't match endpoints exactly, it's touches = false
//                return false;
//            }
//        }
//    }
//
//    return false;
//}
//
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    // As in Python code, same order
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0],vs[1]},
//        {vs[1],vs[2]},
//        {vs[2],vs[3]},
//        {vs[3],vs[0]},
//        {vs[4],vs[5]},
//        {vs[5],vs[6]},
//        {vs[6],vs[7]},
//        {vs[7],vs[4]},
//        {vs[0],vs[4]},
//        {vs[1],vs[5]},
//        {vs[2],vs[6]},
//        {vs[3],vs[7]}
//    };
//    for (auto &e: edges) {
//        double w=distance2D(e.first,e.second);
//        add_edge(e.first,e.second,w);
//    }
//    return edges;
//}
//
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    // Same order as Python (just iterate in the given order)
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0;i<8;i++) {
//        Point vertex=vs[i];
//        bool intersects=false;
//        for (auto &ce: cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects=true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w=distance2D(point,vertex);
//            add_edge(point,vertex,w);
//            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point,double> gScore;
//    std::map<Point,double> fScore;
//    std::map<Point,Point> cameFrom;
//
//    for (auto &kv: graph) {
//        gScore[kv.first]=std::numeric_limits<double>::infinity();
//        fScore[kv.first]=std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start]=0.0;
//    fScore[start]=distance3D(start,goal);
//
//    // Tie-break counter to mimic Python’s stable ordering
//    static long long counter = 0;
//
//    struct PQItem {
//        Point node;
//        double f;
//        long long order;
//        bool operator>(const PQItem&o) const {
//            if (f == o.f) return order > o.order;
//            return f > o.f;
//        }
//    };
//
//    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start],counter++});
//    std::map<Point,bool> inOpen;
//    inOpen[start]=true;
//
//    while(!openSet.empty()) {
//        Point current=openSet.top().node;
//        openSet.pop();
//        inOpen[current]=false;
//
//        if (current==goal) {
//            std::vector<Point> path;
//            Point cur=current;
//            while(!(cur==start)) {
//                path.push_back(cur);
//                cur=cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (auto &edge: graph[current]) {
//            Point neighbor=edge.node;
//            double tentative=gScore[current]+edge.weight;
//            if (tentative<gScore[neighbor]) {
//                cameFrom[neighbor]=current;
//                gScore[neighbor]=tentative;
//                fScore[neighbor]=tentative+distance3D(neighbor,goal);
//                if (!inOpen[neighbor]) {
//                    openSet.push({neighbor,fScore[neighbor],counter++});
//                    inOpen[neighbor]=true;
//                }
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    Point s=arrToPoint(source);
//    Point e=arrToPoint(endp);
//
//    // Add cube vertices as nodes
//    for (int i=0;i<8;i++) add_node(vs[i]);
//    add_node(s);
//    add_node(e);
//
//    // Add cube edges
//    auto cube_edges=add_outer_edges_cube();
//
//    // Add edges from source in same order as Python
//    std::cout<<"Adding edges from source:\n";
//    add_edges_without_intersection(s,cube_edges);
//
//    // Add edges from end in same order
//    std::cout<<"\nAdding edges from end:\n";
//    add_edges_without_intersection(e,cube_edges);
//
//    // A* search with stable tie-breaking
//    std::vector<Point> path=astar_path(s,e);
//    if (!path.empty()) {
//        std::cout<<"\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0;i<path.size();i++) {
//            std::cout<<fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout<<", ";
//        }
//        std::cout<<"]\n";
//    } else {
//        std::cout<<"\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}











//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//// Cube vertices (identical to Python)
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points (identical to Python)
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = {6, 4, 4};
//
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//struct Edge {
//    Point node;
//    double weight;
//};
//
//std::map<Point, std::vector<Edge>> graph;
//
//Point arrToPoint(const double arr[3]) {
//    Point p; p.x=arr[0]; p.y=arr[1]; p.z=arr[2]; return p;
//}
//
//void add_node(const Point &p) {
//    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
//}
//
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//std::string fmtPoint(const Point &p) {
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//
//std::string fmtArray(const Point &p) {
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//// Distance in 2D
//double distance2D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y;
//    return std::sqrt(dx*dx+dy*dy);
//}
//
//// Distance in 3D (for A* heuristic)
//double distance3D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y; double dz=a.z-b.z;
//    return std::sqrt(dx*dx+dy*dy+dz*dz);
//}
//
//// Epsilon for floating comparisons
//static const double EPS = 1e-14;
//
//// Check intersection (intersects and not touches)
//bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
//    double x1=A.x, y1=A.y, x2=B.x, y2=B.y;
//    double x3=C.x, y3=C.y, x4=D.x, y4=D.y;
//
//    double den = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//
//    auto eq = [&](double a, double b) {
//        return std::fabs(a-b)<EPS;
//    };
//
//    auto orientation=[&](double ax,double ay,double bx,double by,double cx,double cy){
//        double val=(by - ay)*(cx - bx)-(bx - ax)*(cy - by);
//        if (std::fabs(val)<EPS) return 0;
//        return (val>0)?1:2;
//    };
//
//    if (std::fabs(den)<EPS) {
//        // Collinear or parallel
//        int o1=orientation(x1,y1,x2,y2,x3,y3);
//        int o2=orientation(x1,y1,x2,y2,x4,y4);
//        int o3=orientation(x3,y3,x4,y4,x1,y1);
//        int o4=orientation(x3,y3,x4,y4,x2,y2);
//
//        if (o1==0 && o2==0 && o3==0 && o4==0) {
//            // Collinear: check overlap
//            std::vector<std::pair<double,double>> pts = {{x1,y1},{x2,y2},{x3,y3},{x4,y4}};
//            std::sort(pts.begin(),pts.end(),[&](auto &p1,auto &p2){
//                if (!eq(p1.first,p2.first)) return p1.first<p2.first;
//                return p1.second<p2.second;
//            });
//            double dx=pts[1].first - pts[2].first;
//            double dy=pts[1].second - pts[2].second;
//            double dist=std::sqrt(dx*dx+dy*dy);
//            if (dist>EPS) {
//                // More than a point overlap
//                return true;
//            } else {
//                // Exactly one point overlap = touches
//                return false;
//            }
//        } else {
//            // Parallel no intersection
//            return false;
//        }
//    }
//
//    double ua = ((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/den;
//    double ub = ((x2 - x1)*(y1 - y3)-(y2 - y1)*(x1 - x3))/den;
//
//    if (ua>=-EPS && ua<=1+EPS && ub>=-EPS && ub<=1+EPS) {
//        double ix=x1+ua*(x2-x1);
//        double iy=y1+ua*(y2-y1);
//
//        bool onAEnd= (eq(ix,x1)&&eq(iy,y1)) || (eq(ix,x2)&&eq(iy,y2));
//        bool onBEnd= (eq(ix,x3)&&eq(iy,y3)) || (eq(ix,x4)&&eq(iy,y4));
//
//        bool insideA = (ua>EPS && ua<1-EPS);
//        bool insideB = (ub>EPS && ub<1-EPS);
//
//        if (insideA && insideB) {
//            // Pure interior intersection
//            return true;
//        } else {
//            // Intersection at endpoints or boundary
//            if (onAEnd && onBEnd) {
//                // Shared endpoint only = touches
//                return false;
//            } else if (onAEnd && !onBEnd) {
//                // Intersection at A's endpoint
//                // If insideB => endpoint of A meets interior of B => intersection
//                if (insideB) return true;
//                // otherwise touches
//                return false;
//            } else if (!onAEnd && onBEnd) {
//                // Intersection at B's endpoint
//                if (insideA) return true;
//                return false;
//            } else {
//                // Intersection on boundary but not on endpoints?
//                // This could happen if ua=0 or 1 or ub=0 or 1 without exact endpoint match (floating issues)
//                // If it falls here, treat it as touches
//                return false;
//            }
//        }
//    }
//
//    return false;
//}
//
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0],vs[1]},
//        {vs[1],vs[2]},
//        {vs[2],vs[3]},
//        {vs[3],vs[0]},
//        {vs[4],vs[5]},
//        {vs[5],vs[6]},
//        {vs[6],vs[7]},
//        {vs[7],vs[4]},
//        {vs[0],vs[4]},
//        {vs[1],vs[5]},
//        {vs[2],vs[6]},
//        {vs[3],vs[7]}
//    };
//    for (auto &e: edges) {
//        double w=distance2D(e.first,e.second);
//        add_edge(e.first,e.second,w);
//    }
//    return edges;
//}
//
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0;i<8;i++) {
//        Point vertex=vs[i];
//        bool intersects=false;
//        for (auto &ce: cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects=true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w=distance2D(point,vertex);
//            add_edge(point,vertex,w);
//            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point,double> gScore;
//    std::map<Point,double> fScore;
//    std::map<Point,Point> cameFrom;
//
//    for (auto &kv: graph) {
//        gScore[kv.first]=std::numeric_limits<double>::infinity();
//        fScore[kv.first]=std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start]=0.0;
//    fScore[start]=distance3D(start,goal);
//
//    struct PQItem {
//        Point node;
//        double f;
//        bool operator>(const PQItem&o) const {return f>o.f;}
//    };
//
//    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start]});
//    std::set<Point> inOpen;
//    inOpen.insert(start);
//
//    while(!openSet.empty()) {
//        Point current=openSet.top().node;
//        openSet.pop();
//        inOpen.erase(current);
//
//        if (current==goal) {
//            std::vector<Point> path;
//            Point cur=current;
//            while(!(cur==start)) {
//                path.push_back(cur);
//                cur=cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (auto &edge: graph[current]) {
//            Point neighbor=edge.node;
//            double tentative=gScore[current]+edge.weight;
//            if (tentative<gScore[neighbor]) {
//                cameFrom[neighbor]=current;
//                gScore[neighbor]=tentative;
//                fScore[neighbor]=tentative+distance3D(neighbor,goal);
//                if (inOpen.find(neighbor)==inOpen.end()) {
//                    openSet.push({neighbor,fScore[neighbor]});
//                    inOpen.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    Point s=arrToPoint(source);
//    Point e=arrToPoint(endp);
//
//    for (int i=0;i<8;i++) add_node(vs[i]);
//    add_node(s);
//    add_node(e);
//
//    auto cube_edges=add_outer_edges_cube();
//
//    std::cout<<"Adding edges from source:\n";
//    add_edges_without_intersection(s,cube_edges);
//
//    std::cout<<"\nAdding edges from end:\n";
//    add_edges_without_intersection(e,cube_edges);
//
//    std::vector<Point> path=astar_path(s,e);
//    if (!path.empty()) {
//        std::cout<<"\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0;i<path.size();i++) {
//            std::cout<<fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout<<", ";
//        }
//        std::cout<<"]\n";
//    } else {
//        std::cout<<"\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}
//





//
//
//
//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = {6, 4, 4};
//
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//struct Edge {
//    Point node;
//    double weight;
//};
//
//std::map<Point, std::vector<Edge>> graph;
//
//Point arrToPoint(const double arr[3]) {
//    Point p; p.x=arr[0]; p.y=arr[1]; p.z=arr[2]; return p;
//}
//
//void add_node(const Point &p) {
//    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
//}
//
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//std::string fmtPoint(const Point &p) {
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//
//std::string fmtArray(const Point &p) {
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//double distance2D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y;
//    return std::sqrt(dx*dx+dy*dy);
//}
//
//double distance3D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y; double dz=a.z-b.z;
//    return std::sqrt(dx*dx+dy*dy+dz*dz);
//}
//
//// Check if two segments intersect according to "intersects and not touches"
//// No epsilons, exact comparisons:
//bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
//    double x1=A.x, y1=A.y, x2=B.x, y2=B.y;
//    double x3=C.x, y3=C.y, x4=D.x, y4=D.y;
//
//    double den = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//
//    auto orientation=[&](double ax,double ay,double bx,double by,double cx,double cy){
//        double val=(by - ay)*(cx - bx)-(bx - ax)*(cy - by);
//        if (std::fabs(val)<1e-15) return 0;
//        return (val>0)?1:2;
//    };
//
//    if (std::fabs(den)<1e-15) {
//        // Collinear or parallel
//        int o1=orientation(x1,y1,x2,y2,x3,y3);
//        int o2=orientation(x1,y1,x2,y2,x4,y4);
//        int o3=orientation(x3,y3,x4,y4,x1,y1);
//        int o4=orientation(x3,y3,x4,y4,x2,y2);
//
//        if (o1==0 && o2==0 && o3==0 && o4==0) {
//            // Collinear
//            std::vector<std::pair<double,double>> all={
//                {x1,y1},{x2,y2},{x3,y3},{x4,y4}
//            };
//            std::sort(all.begin(),all.end(),[](auto &p1,auto &p2){
//                if (p1.first!=p2.first) return p1.first<p2.first;
//                return p1.second<p2.second;
//            });
//            double dx=all[1].first - all[2].first;
//            double dy=all[1].second - all[2].second;
//            double dist=std::sqrt(dx*dx+dy*dy);
//            if (dist>1e-15) {
//                // Overlap > point => intersects
//                return true;
//            } else {
//                // Overlap at a single point => touches
//                return false;
//            }
//        } else {
//            // Parallel no intersection
//            return false;
//        }
//    }
//
//    double ua = ((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/den;
//    double ub = ((x2 - x1)*(y1 - y3)-(y2 - y1)*(x1 - x3))/den;
//
//    // Intersection point
//    if (ua>=0 && ua<=1 && ub>=0 && ub<=1) {
//        double ix=x1+ua*(x2-x1);
//        double iy=y1+ua*(y2-y1);
//
//        bool onAEnd=( (ix==x1 && iy==y1) || (ix==x2 && iy==y2) );
//        bool onBEnd=( (ix==x3 && iy==y3) || (ix==x4 && iy==y4) );
//
//        bool insideA=(ua>0 && ua<1);
//        bool insideB=(ub>0 && ub<1);
//
//        if (insideA && insideB) {
//            // Interior intersection
//            return true;
//        } else {
//            // At least one endpoint involved
//            if (onAEnd && onBEnd) {
//                // Endpoint to endpoint => touches only
//                return false;
//            } else if (onAEnd && !onBEnd) {
//                // Intersection at A's endpoint but inside B?
//                if (insideB) return true; // endpoint meets other line's interior => intersect
//                // endpoint meets endpoint or outside => touches
//                return false;
//            } else if (!onAEnd && onBEnd) {
//                // Intersection at B's endpoint but inside A?
//                if (insideA) return true;
//                return false;
//            } else {
//                // ua or ub is 0 or 1 but no exact endpoint match?
//                // Means intersection is on boundary of one line but doesn't coincide with other's endpoints
//                // That would mean a single boundary point that does not match the other's endpoint
//                // This is endpoint of one line and inside the other line's boundary?
//                // If it's exactly at boundary of one line and not endpoint of other (since other not onBEnd)
//                // Actually if not onBEnd and not insideB means ub=0 or 1 but no endpoint match?
//                // If ub=0 or 1 and we didn't confirm onBEnd, means intersection exactly at B's endpoint (we checked onBEnd?),
//                // If no endpoint matched exactly due to floating rounding let's trust exact comparisons:
//                // Without tolerance, let's consider this a touches scenario since it's a boundary-to-boundary scenario.
//                return false;
//            }
//        }
//    }
//
//    return false;
//}
//
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0],vs[1]},
//        {vs[1],vs[2]},
//        {vs[2],vs[3]},
//        {vs[3],vs[0]},
//        {vs[4],vs[5]},
//        {vs[5],vs[6]},
//        {vs[6],vs[7]},
//        {vs[7],vs[4]},
//        {vs[0],vs[4]},
//        {vs[1],vs[5]},
//        {vs[2],vs[6]},
//        {vs[3],vs[7]}
//    };
//    for (auto &e: edges) {
//        double w=distance2D(e.first,e.second);
//        add_edge(e.first,e.second,w);
//    }
//    return edges;
//}
//
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0;i<8;i++) {
//        Point vertex=vs[i];
//        bool intersects=false;
//        for (auto &ce: cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects=true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w=distance2D(point,vertex);
//            add_edge(point,vertex,w);
//            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point,double> gScore;
//    std::map<Point,double> fScore;
//    std::map<Point,Point> cameFrom;
//
//    for (auto &kv: graph) {
//        gScore[kv.first]=std::numeric_limits<double>::infinity();
//        fScore[kv.first]=std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start]=0.0;
//    fScore[start]=distance3D(start,goal);
//
//    struct PQItem {
//        Point node;
//        double f;
//        bool operator>(const PQItem&o) const {return f>o.f;}
//    };
//
//    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start]});
//    std::set<Point> inOpen;
//    inOpen.insert(start);
//
//    while(!openSet.empty()) {
//        Point current=openSet.top().node;
//        openSet.pop();
//        inOpen.erase(current);
//
//        if (current==goal) {
//            std::vector<Point> path;
//            Point cur=current;
//            while(!(cur==start)) {
//                path.push_back(cur);
//                cur=cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (auto &edge: graph[current]) {
//            Point neighbor=edge.node;
//            double tentative=gScore[current]+edge.weight;
//            if (tentative<gScore[neighbor]) {
//                cameFrom[neighbor]=current;
//                gScore[neighbor]=tentative;
//                fScore[neighbor]=tentative+distance3D(neighbor,goal);
//                if (inOpen.find(neighbor)==inOpen.end()) {
//                    openSet.push({neighbor,fScore[neighbor]});
//                    inOpen.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    Point s=arrToPoint(source);
//    Point e=arrToPoint(endp);
//
//    for (int i=0;i<8;i++) add_node(vs[i]);
//    add_node(s);
//    add_node(e);
//
//    auto cube_edges=add_outer_edges_cube();
//
//    std::cout<<"Adding edges from source:\n";
//    add_edges_without_intersection(s,cube_edges);
//
//    std::cout<<"\nAdding edges from end:\n";
//    add_edges_without_intersection(e,cube_edges);
//
//    std::vector<Point> path=astar_path(s,e);
//    if (!path.empty()) {
//        std::cout<<"\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0;i<path.size();i++) {
//            std::cout<<fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout<<", ";
//        }
//        std::cout<<"]\n";
//    } else {
//        std::cout<<"\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}




//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//// The cube vertices (exactly as in the Python code)
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points (exactly as in the Python code)
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = {6, 4, 4};
//
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//struct Edge {
//    Point node;
//    double weight;
//};
//std::map<Point, std::vector<Edge>> graph;
//
//Point arrToPoint(const double arr[3]) {
//    Point p; p.x=arr[0]; p.y=arr[1]; p.z=arr[2];
//    return p;
//}
//
//void add_node(const Point &p) {
//    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
//}
//
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//std::string fmtPoint(const Point &p) {
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//
//std::string fmtArray(const Point &p) {
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//// Distance in 2D
//double distance2D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y;
//    return std::sqrt(dx*dx+dy*dy);
//}
//
//// Distance in 3D for heuristic
//double distance3D(const Point &a, const Point &b) {
//    double dx=a.x-b.x; double dy=a.y-b.y; double dz=a.z-b.z;
//    return std::sqrt(dx*dx+dy*dy+dz*dz);
//}
//
//// Intersection logic to replicate "intersects and not touches":
//bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
//    auto eq = [](double a,double b){return std::fabs(a-b)<1e-14;};
//    double x1=A.x, y1=A.y, x2=B.x, y2=B.y;
//    double x3=C.x, y3=C.y, x4=D.x, y4=D.y;
//
//    double den = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//
//    auto orientation = [&](double ax,double ay,double bx,double by,double cx,double cy){
//        double val=(by - ay)*(cx - bx)-(bx - ax)*(cy - by);
//        if (std::fabs(val)<1e-14) return 0;
//        return (val>0)?1:2;
//    };
//
//    // Check collinearity if den=0
//    if (eq(den,0.0)) {
//        int o1=orientation(x1,y1,x2,y2,x3,y3);
//        int o2=orientation(x1,y1,x2,y2,x4,y4);
//        int o3=orientation(x3,y3,x4,y4,x1,y1);
//        int o4=orientation(x3,y3,x4,y4,x2,y2);
//
//        if (o1==0 && o2==0 && o3==0 && o4==0) {
//            // Collinear. Check overlap
//            std::vector<std::pair<double,double>> all={
//                {x1,y1},{x2,y2},{x3,y3},{x4,y4}
//            };
//            std::sort(all.begin(),all.end(),[](auto &p1,auto &p2){
//                if (p1.first!=p2.first) return p1.first<p2.first;
//                return p1.second<p2.second;
//            });
//            double dx=all[1].first - all[2].first;
//            double dy=all[1].second - all[2].second;
//            double dist=std::sqrt(dx*dx+dy*dy);
//            if (dist>1e-14) {
//                // Overlap more than a point => intersection
//                return true;
//            } else {
//                // Overlap at one point => touches
//                return false;
//            }
//        } else {
//            // Parallel no intersection
//            return false;
//        }
//    }
//
//    double ua = ((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/den;
//    double ub = ((x2 - x1)*(y1 - y3)-(y2 - y1)*(x1 - x3))/den;
//
//    if (ua>=-1e-14 && ua<=1+1e-14 && ub>=-1e-14 && ub<=1+1e-14) {
//        double ix = x1+ua*(x2-x1);
//        double iy = y1+ua*(y2-y1);
//
//        bool onAEnd=(eq(ix,x1)&&eq(iy,y1))||(eq(ix,x2)&&eq(iy,y2));
//        bool onBEnd=(eq(ix,x3)&&eq(iy,y3))||(eq(ix,x4)&&eq(iy,y4));
//
//        bool insideA=(ua>1e-14 && ua<1-1e-14);
//        bool insideB=(ub>1e-14 && ub<1-1e-14);
//
//        if (insideA && insideB) {
//            // Intersection inside both segments
//            return true;
//        } else if (onAEnd && onBEnd) {
//            // Intersection at a shared endpoint only
//            // Touches, no interior intersection
//            return false;
//        } else {
//            // Intersection at an endpoint of one segment
//            // Check if inside the other segment
//            // If inside the other, that means interior intersection for that other line
//            if (onAEnd && insideB) return true; // endpoint of A, inside B => intersection
//            if (onBEnd && insideA) return true; // endpoint of B, inside A => intersection
//
//            // If on endpoint of one and on boundary of the other without inside:
//            // Actually if we reached here, it means one is endpoint, the other not inside
//            // This means they only meet at one boundary point and not inside any segment
//            // This is touches.
//            return false;
//        }
//    }
//
//    return false;
//}
//
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0],vs[1]},
//        {vs[1],vs[2]},
//        {vs[2],vs[3]},
//        {vs[3],vs[0]},
//        {vs[4],vs[5]},
//        {vs[5],vs[6]},
//        {vs[6],vs[7]},
//        {vs[7],vs[4]},
//        {vs[0],vs[4]},
//        {vs[1],vs[5]},
//        {vs[2],vs[6]},
//        {vs[3],vs[7]}
//    };
//    for (auto &e: edges) {
//        double w=distance2D(e.first,e.second);
//        add_edge(e.first,e.second,w);
//    }
//    return edges;
//}
//
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0;i<8;i++) {
//        Point vertex=vs[i];
//        bool intersects=false;
//        for (auto &ce: cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects=true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w=distance2D(point,vertex);
//            add_edge(point,vertex,w);
//            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point,double> gScore;
//    std::map<Point,double> fScore;
//    std::map<Point,Point> cameFrom;
//
//    for (auto &kv: graph) {
//        gScore[kv.first]=std::numeric_limits<double>::infinity();
//        fScore[kv.first]=std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start]=0.0;
//    fScore[start]=distance3D(start,goal);
//
//    struct PQItem {
//        Point node;
//        double f;
//        bool operator>(const PQItem&o) const {return f>o.f;}
//    };
//
//    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start]});
//    std::set<Point> inOpen;
//    inOpen.insert(start);
//
//    while(!openSet.empty()) {
//        Point current=openSet.top().node;
//        openSet.pop();
//        inOpen.erase(current);
//
//        if (current==goal) {
//            std::vector<Point> path;
//            Point cur=current;
//            while(!(cur==start)) {
//                path.push_back(cur);
//                cur=cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (auto &edge: graph[current]) {
//            Point neighbor=edge.node;
//            double tentative=gScore[current]+edge.weight;
//            if (tentative<gScore[neighbor]) {
//                cameFrom[neighbor]=current;
//                gScore[neighbor]=tentative;
//                fScore[neighbor]=tentative+distance3D(neighbor,goal);
//                if (inOpen.find(neighbor)==inOpen.end()) {
//                    openSet.push({neighbor,fScore[neighbor]});
//                    inOpen.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    Point s=arrToPoint(source);
//    Point e=arrToPoint(endp);
//
//    for (int i=0;i<8;i++) add_node(vs[i]);
//    add_node(s);
//    add_node(e);
//
//    auto cube_edges=add_outer_edges_cube();
//
//    std::cout<<"Adding edges from source:\n";
//    add_edges_without_intersection(s,cube_edges);
//
//    std::cout<<"\nAdding edges from end:\n";
//    add_edges_without_intersection(e,cube_edges);
//
//    std::vector<Point> path=astar_path(s,e);
//    if (!path.empty()) {
//        std::cout<<"\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0;i<path.size();i++) {
//            std::cout<<fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout<<", ";
//        }
//        std::cout<<"]\n";
//    } else {
//        std::cout<<"\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}






//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//// The cube vertices (exactly as in the Python code)
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points (exactly as in the Python code)
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = {6, 4, 4};
//
//// Define a 3D point structure
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//// Graph: map from point to edges
//struct Edge {
//    Point node;
//    double weight;
//};
//std::map<Point, std::vector<Edge>> graph;
//
//// Convert array to Point
//Point arrToPoint(const double arr[3]) {
//    Point p;
//    p.x = arr[0]; p.y = arr[1]; p.z = arr[2];
//    return p;
//}
//
//void add_node(const Point &p) {
//    if (graph.find(p)==graph.end()) graph[p]=std::vector<Edge>();
//}
//
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//// Formatting functions to match Python style
//std::string fmtPoint(const Point &p) {
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//std::string fmtArray(const Point &p) {
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//// Distance in 2D (for weights)
//double distance2D(const Point &a, const Point &b) {
//    double dx = a.x - b.x;
//    double dy = a.y - b.y;
//    return std::sqrt(dx*dx + dy*dy);
//}
//
//// Distance in 3D (for heuristic)
//double distance3D(const Point &a, const Point &b) {
//    double dx = a.x - b.x;
//    double dy = a.y - b.y;
//    double dz = a.z - b.z;
//    return std::sqrt(dx*dx + dy*dy + dz*dz);
//}
//
//// Intersection logic: returns true if segments intersect internally or overlap more than a point,
//// false if they only touch at endpoints or do not intersect at all.
//// We replicate `intersects and not touches` from Shapely:
//bool segments_intersect_no_touches(const Point &A, const Point &B, const Point &C, const Point &D) {
//    auto eq = [](double a, double b){return std::fabs(a-b)<1e-14;};
//
//    double x1=A.x, y1=A.y, x2=B.x, y2=B.y;
//    double x3=C.x, y3=C.y, x4=D.x, y4=D.y;
//
//    double den = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//
//    auto onSegment=[&](double ax,double ay,double bx,double by,double cx,double cy){
//        return std::min(ax,cx)-1e-14<=bx && bx<=std::max(ax,cx)+1e-14 &&
//               std::min(ay,cy)-1e-14<=by && by<=std::max(ay,cy)+1e-14;
//    };
//
//    // Check for collinearity if den=0
//    if (eq(den,0.0)) {
//        // Check collinearity
//        auto orientation = [&](double ax,double ay,double bx,double by,double cx,double cy){
//            double val=(by - ay)*(cx - bx)-(bx - ax)*(cy - by);
//            if (std::fabs(val)<1e-14) return 0;
//            return (val>0)?1:2;
//        };
//        int o1=orientation(x1,y1,x2,y2,x3,y3);
//        int o2=orientation(x1,y1,x2,y2,x4,y4);
//        int o3=orientation(x3,y3,x4,y4,x1,y1);
//        int o4=orientation(x3,y3,x4,y4,x2,y2);
//
//        if (o1==0 && o2==0 && o3==0 && o4==0) {
//            // Collinear
//            // Sort points to find overlap
//            std::vector<std::pair<double,double>> allPoints={
//                {x1,y1},{x2,y2},{x3,y3},{x4,y4}
//            };
//            auto lessP=[](const std::pair<double,double>&p1,const std::pair<double,double>&p2){
//                if (p1.first!=p2.first) return p1.first<p2.first;
//                return p1.second<p2.second;
//            };
//            std::sort(allPoints.begin(),allPoints.end(),lessP);
//
//            double dx=allPoints[1].first - allPoints[2].first;
//            double dy=allPoints[1].second - allPoints[2].second;
//            double dist = std::sqrt(dx*dx+dy*dy);
//            if (dist>1e-14) {
//                // Overlap more than a single point = intersection
//                return true;
//            } else {
//                // Overlap at most a single point = touches
//                return false;
//            }
//        } else {
//            // Parallel but no intersection
//            return false;
//        }
//    }
//
//    // Not parallel
//    double ua = ((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/den;
//    double ub = ((x2 - x1)*(y1 - y3)-(y2 - y1)*(x1 - x3))/den;
//
//    if (ua>=-1e-14 && ua<=1+1e-14 && ub>=-1e-14 && ub<=1+1e-14) {
//        double ix = x1+ua*(x2-x1);
//        double iy = y1+ua*(y2-y1);
//
//        // Check if intersection is inside both segments or on endpoints
//        bool onAEnd=(eq(ix,x1)&&eq(iy,y1))||(eq(ix,x2)&&eq(iy,y2));
//        bool onBEnd=(eq(ix,x3)&&eq(iy,y3))||(eq(ix,x4)&&eq(iy,y4));
//
//        // If strictly inside both segments (not endpoints):
//        if (ua>1e-14 && ua<1-1e-14 && ub>1e-14 && ub<1-1e-14) {
//            return true; // internal intersection
//        } else {
//            // Intersection at least one endpoint
//            // This is touches, not intersection
//            return false;
//        }
//    }
//
//    return false;
//}
//
//// Add outer edges of the cube
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0],vs[1]},
//        {vs[1],vs[2]},
//        {vs[2],vs[3]},
//        {vs[3],vs[0]},
//        {vs[4],vs[5]},
//        {vs[5],vs[6]},
//        {vs[6],vs[7]},
//        {vs[7],vs[4]},
//        {vs[0],vs[4]},
//        {vs[1],vs[5]},
//        {vs[2],vs[6]},
//        {vs[3],vs[7]}
//    };
//    for (auto &e: edges) {
//        double w=distance2D(e.first,e.second);
//        add_edge(e.first,e.second,w);
//    }
//    return edges;
//}
//
//// Add edges from a point to cube vertices, skipping those that intersect cube edges
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0;i<8;i++) {
//        Point vertex=vs[i];
//        bool intersects=false;
//        for (auto &ce: cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects=true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w=distance2D(point,vertex);
//            add_edge(point,vertex,w);
//            std::cout<<"Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//// A* search
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point,double> gScore;
//    std::map<Point,double> fScore;
//    std::map<Point,Point> cameFrom;
//
//    for (auto &kv: graph) {
//        gScore[kv.first]=std::numeric_limits<double>::infinity();
//        fScore[kv.first]=std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start]=0.0;
//    fScore[start]=distance3D(start,goal);
//
//    struct PQItem {
//        Point node;
//        double f;
//        bool operator>(const PQItem&o) const {return f>o.f;}
//    };
//
//    std::priority_queue<PQItem,std::vector<PQItem>,std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start]});
//    std::set<Point> inOpen;
//    inOpen.insert(start);
//
//    while(!openSet.empty()) {
//        Point current=openSet.top().node;
//        openSet.pop();
//        inOpen.erase(current);
//
//        if (current==goal) {
//            std::vector<Point> path;
//            Point cur=current;
//            while(!(cur==start)) {
//                path.push_back(cur);
//                cur=cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(),path.end());
//            return path;
//        }
//
//        for (auto &edge: graph[current]) {
//            Point neighbor=edge.node;
//            double tentative=gScore[current]+edge.weight;
//            if (tentative<gScore[neighbor]) {
//                cameFrom[neighbor]=current;
//                gScore[neighbor]=tentative;
//                fScore[neighbor]=tentative+distance3D(neighbor,goal);
//                if (inOpen.find(neighbor)==inOpen.end()) {
//                    openSet.push({neighbor,fScore[neighbor]});
//                    inOpen.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    return {}; // no path
//}
//
//int main() {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//    Point s=arrToPoint(source);
//    Point e=arrToPoint(endp);
//
//    // Add obstacle vertices as nodes
//    for (int i=0;i<8;i++) add_node(vs[i]);
//    // Add source and end
//    add_node(s);
//    add_node(e);
//
//    // Add cube edges
//    auto cube_edges=add_outer_edges_cube();
//
//    std::cout<<"Adding edges from source:\n";
//    add_edges_without_intersection(s,cube_edges);
//
//    std::cout<<"\nAdding edges from end:\n";
//    add_edges_without_intersection(e,cube_edges);
//
//    std::vector<Point> path=astar_path(s,e);
//    if (!path.empty()) {
//        std::cout<<"\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0;i<path.size();i++) {
//            std::cout<<fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout<<", ";
//        }
//        std::cout<<"]\n";
//    } else {
//        std::cout<<"\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}
//













//best**************

//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <sstream>
//
//// The cube vertices:
//static double cube_vertices[8][3] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points:
//static double source[3] = {-2, 1, 3};
//static double endp[3]   = { 6, 4, 4};
//
//// We'll store the graph as an adjacency list using a map from a 3D point to vector of edges.
//// Each node is a (x,y,z) triple. We'll define a struct to handle comparison and hashing.
//struct Point {
//    double x,y,z;
//};
//
//inline bool operator<(const Point &a, const Point &b) {
//    if (a.x != b.x) return a.x < b.x;
//    if (a.y != b.y) return a.y < b.y;
//    return a.z < b.z;
//}
//
//inline bool operator==(const Point &a, const Point &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//struct Edge {
//    Point node;
//    double weight;
//};
//
//std::map<Point, std::vector<Edge>> graph;
//
//// Add node if not present
//void add_node(const Point &p) {
//    if (graph.find(p) == graph.end()) {
//        graph[p] = std::vector<Edge>();
//    }
//}
//
//// Add edge (undirected)
//void add_edge(const Point &u, const Point &v, double w) {
//    graph[u].push_back({v,w});
//    graph[v].push_back({u,w});
//}
//
//// Convert array to Point
//Point arrToPoint(const double arr[3]) {
//    Point p;
//    p.x = arr[0]; p.y = arr[1]; p.z = arr[2];
//    return p;
//}
//
//// Print formatting functions:
//std::string fmtPoint(const Point &p) {
//    // Print as (x, y, z) matching Python integer formatting
//    std::ostringstream oss;
//    oss << "(" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << ")";
//    return oss.str();
//}
//
//std::string fmtArray(const Point &p) {
//    // Print as array([x, y, z])
//    std::ostringstream oss;
//    oss << "array([" << (int)p.x << ", " << (int)p.y << ", " << (int)p.z << "])";
//    return oss.str();
//}
//
//std::string fmtEdgeAsArrays(const Point &p1, const Point &p2) {
//    std::ostringstream oss;
//    oss << "(" << fmtArray(p1) << ", " << fmtArray(p2) << ")";
//    return oss.str();
//}
//
//// Distance in 2D (ignore z) for edge weights
//double distance2D(const Point &a, const Point &b) {
//    double dx = a.x - b.x;
//    double dy = a.y - b.y;
//    return std::sqrt(dx*dx + dy*dy);
//}
//
//// Distance in 3D for heuristic
//double distance3D(const Point &a, const Point &b) {
//    double dx = a.x - b.x;
//    double dy = a.y - b.y;
//    double dz = a.z - b.z;
//    return std::sqrt(dx*dx + dy*dy + dz*dz);
//}
//
//// Check line segment intersection in 2D, ignoring z.
//// The Python code: line1.intersects(line2) and not line1.touches(line2)
//// Intersection but not just at endpoints.
//bool segments_intersect_no_touches(const Point &p1, const Point &p2, const Point &p3, const Point &p4) {
//    // Based on orientation tests:
//    auto orientation = [](const Point &a, const Point &b, const Point &c) {
//        double val = (b.y - a.y)*(c.x - b.x) - (b.x - a.x)*(c.y - b.y);
//        if (std::fabs(val) < 1e-14) return 0;
//        return (val > 0)? 1: 2;
//    };
//
//    auto onSegment = [&](const Point &a, const Point &b, const Point &c) {
//        // Check if b lies on segment a-c
//        return (std::min(a.x,c.x) <= b.x && b.x <= std::max(a.x,c.x) &&
//                std::min(a.y,c.y) <= b.y && b.y <= std::max(a.y,c.y));
//    };
//
//    int o1 = orientation(p1,p2,p3);
//    int o2 = orientation(p1,p2,p4);
//    int o3 = orientation(p3,p4,p1);
//    int o4 = orientation(p3,p4,p2);
//
//    // General intersection check
//    bool intersect = false;
//    if (o1 != o2 && o3 != o4)
//        intersect = true;
//    else if (o1 == 0 && onSegment(p1,p3,p2)) intersect = true;
//    else if (o2 == 0 && onSegment(p1,p4,p2)) intersect = true;
//    else if (o3 == 0 && onSegment(p3,p1,p4)) intersect = true;
//    else if (o4 == 0 && onSegment(p3,p2,p4)) intersect = true;
//
//    if (!intersect) return false;
//
//    // If intersect, check if it's only a touch (endpoint intersection)
//    // Compute intersection point and see if it coincides with endpoints of both segments
//    // If intersection occurs at an endpoint of both, that's touches.
//
//    // If lines are collinear and overlapping, Shapely would see them as intersecting or touching?
//    // In this scenario, the edges of a cube shouldn't be collinear with new edges from the point, so rare.
//    // We must still handle endpoint-only intersection as touching:
//    // The endpoints: p1, p2, p3, p4. If intersection point is exactly an endpoint of one segment
//    // and also exactly that same endpoint of the other segment, it's a touching.
//
//    // Let's find intersection coordinates if not collinear:
//    // If lines are not parallel:
//    double x1 = p1.x, y1 = p1.y;
//    double x2 = p2.x, y2 = p2.y;
//    double x3 = p3.x, y3 = p3.y;
//    double x4 = p4.x, y4 = p4.y;
//    double denom = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//    // If denom=0, lines are collinear or parallel. If collinear and we have intersection = overlapping or endpoint.
//    // Check endpoint touching if collinear:
//    if (std::fabs(denom) < 1e-14) {
//        // If collinear and intersection found means overlap. Overlap means definitely intersects.
//        // But Shapely line segments "intersects" and "touches" conditions:
//        // If overlap is partial, they "intersect" more than just touching endpoints.
//        // If they share only endpoints, it's touching. Let's check if they share only endpoints:
//        // The sets of endpoints are {p1,p2} and {p3,p4}. If the intersection is only a single point and that point is an endpoint of both segments, then it's touches not intersection.
//        
//        // Let's check all endpoints:
//        // If they share exactly one endpoint and no other overlap, that's touches:
//        int matches = 0;
//        if (p1 == p3 || p1 == p4) matches++;
//        if (p2 == p3 || p2 == p4) matches++;
//        if (matches == 1) {
//            // Only one common endpoint - just touching
//            return false;
//        }
//        // If matches == 0 no intersection? We concluded there is intersection, so must be overlapping line. Overlapping lines share infinitely many points, definitely intersects more than a touch.
//        // If matches == 2 means they share both endpoints - identical lines or same segment. That's more than a touch, it's a full overlap. Shapely would consider that intersecting.
//        return true;
//    }
//
//    double ua = ((x4 - x3)*(y1 - y3)-(y4 - y3)*(x1 - x3))/denom;
//    double ix = x1 + ua*(x2 - x1);
//    double iy = y1 + ua*(y2 - y1);
//
//    // Check if intersection point = endpoint of both segments
//    auto eq = [](double a, double b){return std::fabs(a-b)<1e-14;};
//
//    auto isEndpoint = [&](const Point &A, const Point &B){
//        return eq(A.x,B.x)&&eq(A.y,B.y);
//    };
//
//    Point I{ix, iy, 0};
//    bool iOnP1 = isEndpoint(I, p1);
//    bool iOnP2 = isEndpoint(I, p2);
//    bool iOnP3 = isEndpoint(I, p3);
//    bool iOnP4 = isEndpoint(I, p4);
//
//    // If intersection is at an endpoint of one segment and also the same endpoint of the other, it's touching:
//    // In Python: line1.touches(line2) means they share boundary but no interior intersection.
//    // If exactly one endpoint matches and it's same point for both lines => touches
//    // If intersection is inside, not touches
//    // If intersection is at an endpoint of only one line but inside the other line, that's still intersection.
//
//    // touches if intersection is at a segment endpoint that belongs to both segments:
//    // That would mean intersection point is either p1 or p2 and also p3 or p4.
//    // Count how many endpoints match intersection:
//    int endpointsMatch = (iOnP1?1:0)+(iOnP2?1:0)+(iOnP3?1:0)+(iOnP4?1:0);
//
//    // If endpointsMatch >=2 and those endpoints are from different lines => touching:
//    // Actually, if intersection point equals one endpoint from the first line and one endpoint from the second line, that's touches.
//    // If intersection point is only on endpoints of one line, the other line must also pass through that endpoint to be touches.
//    // If intersection point matches exactly one endpoint of line1 and one endpoint of line2, endpointsMatch == 2 -> touches
//    // If intersection point matches just one endpoint total, that means intersection is at boundary of one segment. The other segment must cross inside this point. That's still intersection inside that segment.
//
//    // Let's carefully check touches:
//    // touches means intersection point is on the boundary of both lines but not inside either.
//    // That can only happen if the intersection point is an endpoint of both segments.
//    // So we must have exactly one endpoint from line1 and one from line2 matching the intersection:
//    bool endpointFromLine1 = (iOnP1 || iOnP2);
//    bool endpointFromLine2 = (iOnP3 || iOnP4);
//
//    if (endpointFromLine1 && endpointFromLine2) {
//        // The intersection is at a point that is endpoint of both segments = touches
//        return false;
//    }
//
//    // Otherwise, it's a genuine intersection
//    return true;
//}
//
//// Add cube edges (outer edges of the cube)
//std::vector<std::pair<Point,Point>> add_outer_edges_cube() {
//    Point vs[8];
//    for (int i=0; i<8; i++) vs[i]=arrToPoint(cube_vertices[i]);
//    std::vector<std::pair<Point,Point>> edges = {
//        {vs[0], vs[1]},
//        {vs[1], vs[2]},
//        {vs[2], vs[3]},
//        {vs[3], vs[0]},
//        {vs[4], vs[5]},
//        {vs[5], vs[6]},
//        {vs[6], vs[7]},
//        {vs[7], vs[4]},
//        {vs[0], vs[4]},
//        {vs[1], vs[5]},
//        {vs[2], vs[6]},
//        {vs[3], vs[7]}
//    };
//
//    for (auto &e : edges) {
//        double w = distance2D(e.first, e.second);
//        add_edge(e.first, e.second, w);
//    }
//    return edges;
//}
//
//// Try adding edges from a point to the cube vertices without intersection
//void add_edges_without_intersection(const Point &point, const std::vector<std::pair<Point,Point>> &cube_edges) {
//    Point vs[8];
//    for (int i=0;i<8;i++) vs[i]=arrToPoint(cube_vertices[i]);
//
//    for (int i=0; i<8; i++) {
//        Point vertex = vs[i];
//        bool intersects = false;
//        for (auto &ce : cube_edges) {
//            if (segments_intersect_no_touches(point, vertex, ce.first, ce.second)) {
//                std::cout << "Edge from " << fmtPoint(point) << " to " << fmtPoint(vertex)
//                          << " intersects with cube edge " << fmtEdgeAsArrays(ce.first, ce.second) << "\n";
//                intersects = true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w = distance2D(point, vertex);
//            add_edge(point, vertex, w);
//            std::cout << "Added edge from " << fmtPoint(point) << " to " << fmtPoint(vertex) << "\n";
//        }
//    }
//}
//
//// A* search to find shortest path
//std::vector<Point> astar_path(const Point &start, const Point &goal) {
//    std::map<Point, double> gScore;
//    std::map<Point, double> fScore;
//    std::map<Point, Point> cameFrom;
//
//    for (auto &kv : graph) {
//        gScore[kv.first] = std::numeric_limits<double>::infinity();
//        fScore[kv.first] = std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start] = 0.0;
//    fScore[start] = distance3D(start, goal);
//
//    struct PQItem {
//        Point node;
//        double f;
//        bool operator>(const PQItem &o) const {return f>o.f;}
//    };
//
//    std::priority_queue<PQItem, std::vector<PQItem>, std::greater<PQItem>> openSet;
//    openSet.push({start,fScore[start]});
//    std::set<Point> openSetContains;
//    openSetContains.insert(start);
//
//    while(!openSet.empty()) {
//        Point current = openSet.top().node;
//        openSet.pop();
//        openSetContains.erase(current);
//
//        if (current == goal) {
//            // reconstruct path
//            std::vector<Point> path;
//            Point cur = current;
//            while (!(cur == start)) {
//                path.push_back(cur);
//                cur = cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (auto &edge : graph[current]) {
//            Point neighbor = edge.node;
//            double tentative_gScore = gScore[current] + edge.weight;
//            if (tentative_gScore < gScore[neighbor]) {
//                cameFrom[neighbor] = current;
//                gScore[neighbor] = tentative_gScore;
//                fScore[neighbor] = tentative_gScore + distance3D(neighbor, goal);
//                if (openSetContains.find(neighbor)==openSetContains.end()) {
//                    openSet.push({neighbor,fScore[neighbor]});
//                    openSetContains.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    return {}; // No path
//}
//
//int main() {
//    Point v[8];
//    for (int i=0;i<8;i++) v[i]=arrToPoint(cube_vertices[i]);
//    Point s = arrToPoint(source);
//    Point e = arrToPoint(endp);
//
//    // Add obstacle vertices as nodes
//    for (int i=0;i<8;i++) add_node(v[i]);
//    // Add source and end points as nodes
//    add_node(s);
//    add_node(e);
//
//    // Add cube edges
//    auto cube_edges = add_outer_edges_cube();
//
//    std::cout << "Adding edges from source:\n";
//    add_edges_without_intersection(s, cube_edges);
//
//    std::cout << "\nAdding edges from end:\n";
//    add_edges_without_intersection(e, cube_edges);
//
//    // Try A* search
//    std::vector<Point> path = astar_path(s,e);
//    if (!path.empty()) {
//        std::cout << "\nShortest path found by A* algorithm:\n[";
//        for (size_t i=0; i<path.size(); i++) {
//            std::cout << fmtPoint(path[i]);
//            if (i+1<path.size()) std::cout << ", ";
//        }
//        std::cout << "]\n";
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}


//best**************



























//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <set>
//#include <queue>
//#include <tuple>
//#include <limits>
//#include <algorithm>
//#include <string>
//#include <iomanip>
//#include <sstream>
//
//
//// We will replicate the logic from the Python code step-by-step.
//
//// A structure to store a 3D point.
//struct Point3D {
//    double x, y, z;
//};
//
//inline bool operator<(const Point3D &a, const Point3D &b) {
//    if (a.x < b.x) return true;
//    if (a.x > b.x) return false;
//    if (a.y < b.y) return true;
//    if (a.y > b.y) return false;
//    return (a.z < b.z);
//}
//
//inline bool operator==(const Point3D &a, const Point3D &b) {
//    return (a.x == b.x && a.y == b.y && a.z == b.z);
//}
//
//// Convert a Point3D to a string for printing
//std::string pointToString(const Point3D &p) {
//    std::ostringstream oss;
//    oss << "(" << p.x << ", " << p.y << ", " << p.z << ")";
//    return oss.str();
//}
//
//// The cube vertices as defined in Python code
//static Point3D cube_vertices[8] = {
//    {1, 1, 1},
//    {1, 4, 1},
//    {4, 4, 1},
//    {4, 1, 1},
//    {1, 1, 4},
//    {1, 4, 4},
//    {4, 4, 4},
//    {4, 1, 4}
//};
//
//// Source and end points
//static Point3D source = {-2, 1, 3};
//static Point3D endp = {6, 4, 4};
//
//// Graph representation: For each node (Point3D), we store a vector of (neighbor, weight).
//// We'll use a map<Point3D, vector<pair<Point3D,double>>> to store adjacency.
//struct Edge {
//    Point3D node;
//    double weight;
//};
//std::map<Point3D, std::vector<Edge>> graphNodes;
//
//// Add a node to the graph
//void add_node(const Point3D &p) {
//    if (graphNodes.find(p) == graphNodes.end()) {
//        graphNodes[p] = std::vector<Edge>();
//    }
//}
//
//// Add an edge to the graph
//void add_edge(const Point3D &u, const Point3D &v, double w) {
//    // Undirected graph: add edge u->v and v->u
//    graphNodes[u].push_back({v, w});
//    graphNodes[v].push_back({u, w});
//}
//
//// Compute 2D length of a segment ignoring z
//double lineLength2D(const Point3D &a, const Point3D &b) {
//    double dx = a.x - b.x;
//    double dy = a.y - b.y;
//    return std::sqrt(dx*dx + dy*dy);
//}
//
//// Compute 3D distance (used for heuristic)
//double distance3D(const Point3D &a, const Point3D &b) {
//    double dx = a.x - b.x;
//    double dy = a.y - b.y;
//    double dz = a.z - b.z;
//    return std::sqrt(dx*dx + dy*dy + dz*dz);
//}
//
//// Function to add outer edges of the cube
//std::vector<std::pair<Point3D, Point3D>> add_outer_edges_cube(const Point3D vertices[8]) {
//    std::vector<std::pair<Point3D, Point3D>> edges = {
//        {vertices[0], vertices[1]},
//        {vertices[1], vertices[2]},
//        {vertices[2], vertices[3]},
//        {vertices[3], vertices[0]},
//        {vertices[4], vertices[5]},
//        {vertices[5], vertices[6]},
//        {vertices[6], vertices[7]},
//        {vertices[7], vertices[4]},
//        {vertices[0], vertices[4]},
//        {vertices[1], vertices[5]},
//        {vertices[2], vertices[6]},
//        {vertices[3], vertices[7]}
//    };
//
//    for (auto &e : edges) {
//        double w = lineLength2D(e.first, e.second); // 2D length
//        add_edge(e.first, e.second, w);
//    }
//
//    return edges;
//}
//
//// Check if two line segments intersect in 2D (ignoring z).
//// We'll define a standard line intersection test.
//// We also must ensure that if they only "touch" at endpoints, it doesn't count as intersection.
//// The Python code: line1.intersects(line2) and not line1.touches(line2)
//// "Touches" means they share an endpoint. We'll replicate by excluding cases where the intersection
//// is just at endpoints.
//static bool segments_intersect_2d(const Point3D &p1, const Point3D &p2, const Point3D &p3, const Point3D &p4) {
//    // Convert to 2D
//    auto x1 = p1.x; auto y1 = p1.y;
//    auto x2 = p2.x; auto y2 = p2.y;
//    auto x3 = p3.x; auto y3 = p3.y;
//    auto x4 = p4.x; auto y4 = p4.y;
//
//    auto denom = (y4 - y3)*(x2 - x1) - (x4 - x3)*(y2 - y1);
//    // If denom = 0, lines are parallel or coincident
//    if (std::abs(denom) < 1e-14) {
//        // No proper intersection if lines are parallel or coincident (we consider them not intersecting).
//        return false;
//    }
//
//    auto ua = ((x4 - x3)*(y1 - y3) - (y4 - y3)*(x1 - x3))/denom;
//    auto ub = ((x2 - x1)*(y1 - y3) - (y2 - y1)*(x1 - x3))/denom;
//
//    // Intersection occurs if 0 < ua < 1 and 0 < ub < 1
//    if (ua > 0.0 && ua < 1.0 && ub > 0.0 && ub < 1.0) {
//        // Check if it's not just touching the endpoints
//        // If intersection is exactly at any endpoint of either segment, that would be touching.
//        double ix = x1 + ua*(x2 - x1);
//        double iy = y1 + ua*(y2 - y1);
//
//        // Check against endpoints
//        bool isEndpointIntersection =
//            ((std::abs(ix - x1)<1e-14 && std::abs(iy - y1)<1e-14) ||
//             (std::abs(ix - x2)<1e-14 && std::abs(iy - y2)<1e-14) ||
//             (std::abs(ix - x3)<1e-14 && std::abs(iy - y3)<1e-14) ||
//             (std::abs(ix - x4)<1e-14 && std::abs(iy - y4)<1e-14));
//        if (isEndpointIntersection) {
//            // Touches but not a proper intersection
//            return false;
//        }
//        return true;
//    }
//
//    return false;
//}
//
//// segments_intersect function from Python code
//bool segments_intersect(const std::pair<Point3D, Point3D> &seg1, const std::pair<Point3D, Point3D> &seg2) {
//    return segments_intersect_2d(seg1.first, seg1.second, seg2.first, seg2.second);
//}
//
//// Add edges from a point to cube vertices without intersecting cube edges
//void add_edges_without_intersection(const Point3D &point, const Point3D vertices[8],
//                                    const std::vector<std::pair<Point3D, Point3D>> &cube_edges)
//{
//    for (int i=0; i<8; i++) {
//        Point3D vertex = vertices[i];
//        std::pair<Point3D, Point3D> new_edge = {point, vertex};
//        bool intersects = false;
//        for (auto &ce : cube_edges) {
//            if (segments_intersect(new_edge, ce)) {
//                std::cout << "Edge from " << pointToString(point) << " to " << pointToString(vertex)
//                          << " intersects with cube edge ("
//                          << pointToString(ce.first) << ", " << pointToString(ce.second) << ")\n";
//                intersects = true;
//                break;
//            }
//        }
//        if (!intersects) {
//            double w = lineLength2D(point, vertex);
//            add_edge(point, vertex, w);
//            std::cout << "Added edge from " << pointToString(point) << " to " << pointToString(vertex) << "\n";
//        }
//    }
//}
//
//// A* algorithm to find shortest path
//// We'll implement a standard A* search using a priority queue.
//std::vector<Point3D> astar_path(const Point3D &start, const Point3D &goal) {
//    // We have graphNodes as adjacency list
//    std::map<Point3D, double> gScore;
//    std::map<Point3D, double> fScore;
//    std::map<Point3D, Point3D> cameFrom;
//    
//    for (auto &kv : graphNodes) {
//        gScore[kv.first] = std::numeric_limits<double>::infinity();
//        fScore[kv.first] = std::numeric_limits<double>::infinity();
//    }
//
//    gScore[start] = 0.0;
//    fScore[start] = distance3D(start, goal); // heuristic
//
//    // Min-heap by fScore
//    struct PQItem {
//        Point3D node;
//        double f;
//        bool operator>(const PQItem &other) const {
//            return f > other.f;
//        }
//    };
//
//    std::priority_queue<PQItem, std::vector<PQItem>, std::greater<PQItem>> openSet;
//    openSet.push({start, fScore[start]});
//
//    std::set<Point3D> openSetContains;
//    openSetContains.insert(start);
//
//    while (!openSet.empty()) {
//        Point3D current = openSet.top().node;
//        openSet.pop();
//        openSetContains.erase(current);
//
//        if (current == goal) {
//            // reconstruct path
//            std::vector<Point3D> path;
//            Point3D cur = current;
//            while (!(cur == start)) {
//                path.push_back(cur);
//                cur = cameFrom[cur];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        // For each neighbor
//        for (auto &edge : graphNodes[current]) {
//            Point3D neighbor = edge.node;
//            double tentative_gScore = gScore[current] + edge.weight;
//            if (tentative_gScore < gScore[neighbor]) {
//                cameFrom[neighbor] = current;
//                gScore[neighbor] = tentative_gScore;
//                fScore[neighbor] = tentative_gScore + distance3D(neighbor, goal);
//                if (openSetContains.find(neighbor) == openSetContains.end()) {
//                    openSet.push({neighbor, fScore[neighbor]});
//                    openSetContains.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    // No path found
//    return {};
//}
//
//int main() {
//    // Replicate the Python logic
//
//    // Add obstacle vertices as nodes
//    for (int i=0; i<8; i++) {
//        add_node(cube_vertices[i]);
//    }
//
//    // Add source and end points as nodes
//    add_node(source);
//    add_node(endp);
//
//    // Add outer edges of cube
//    auto cube_edges = add_outer_edges_cube(cube_vertices);
//
//    // Add edges from source
//    std::cout << "Adding edges from source:\n";
//    add_edges_without_intersection(source, cube_vertices, cube_edges);
//
//    std::cout << "\nAdding edges from end:\n";
//    add_edges_without_intersection(endp, cube_vertices, cube_edges);
//
//    // Perform A* search
//    std::vector<Point3D> path = astar_path(source, endp);
//    if (!path.empty()) {
//        std::cout << "\nShortest path found by A* algorithm:\n";
//        for (auto &p : path) {
//            std::cout << pointToString(p) << "\n";
//        }
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}







//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <unordered_map>
//#include <unordered_set>
//#include <queue>
//#include <set>
//#include <tuple>
//#include <algorithm>
//
//// Define a 3D point structure
//struct Point {
//    double x, y, z;
//    bool operator==(const Point& other) const {
//        return std::tie(x, y, z) == std::tie(other.x, other.y, other.z);
//    }
//    bool operator<(const Point& other) const {
//        return std::tie(x, y, z) < std::tie(other.x, other.y, other.z);
//    }
//};
//
//// Hash function for Point
//struct PointHash {
//    std::size_t operator()(const Point& p) const {
//        return std::hash<double>()(p.x) ^ std::hash<double>()(p.y) ^ std::hash<double>()(p.z);
//    }
//};
//
//// Function to calculate Euclidean distance
//double distance(const Point& p1, const Point& p2) {
//    return std::sqrt(std::pow(p1.x - p2.x, 2) + std::pow(p1.y - p2.y, 2) + std::pow(p1.z - p2.z, 2));
//}
//
//// Function to check if two line segments intersect (approximate)
//bool segmentsIntersect(const Point& p1, const Point& p2, const Point& q1, const Point& q2) {
//    // Implement a simple intersection check if necessary
//    return false; // For simplicity, we assume no intersections in this example
//}
//
//// Add edges for the cube's outer surface
//void addOuterEdges(std::unordered_map<Point, std::vector<std::pair<Point, double>>, PointHash>& graph, const std::vector<Point>& vertices) {
//    std::vector<std::pair<Point, Point>> edges = {
//        {vertices[0], vertices[1]}, {vertices[1], vertices[2]}, {vertices[2], vertices[3]}, {vertices[3], vertices[0]},
//        {vertices[4], vertices[5]}, {vertices[5], vertices[6]}, {vertices[6], vertices[7]}, {vertices[7], vertices[4]},
//        {vertices[0], vertices[4]}, {vertices[1], vertices[5]}, {vertices[2], vertices[6]}, {vertices[3], vertices[7]}
//    };
//
//    for (const auto& edge : edges) {
//        double weight = distance(edge.first, edge.second);
//        graph[edge.first].emplace_back(edge.second, weight);
//        graph[edge.second].emplace_back(edge.first, weight);
//    }
//}
//
//// Add edges from point to cube vertices without intersecting existing edges
//void addEdgesWithoutIntersection(std::unordered_map<Point, std::vector<std::pair<Point, double>>, PointHash>& graph, const Point& point, const std::vector<Point>& vertices, const std::vector<std::pair<Point, Point>>& cubeEdges) {
//    for (const auto& vertex : vertices) {
//        bool intersects = false;
//        for (const auto& edge : cubeEdges) {
//            if (segmentsIntersect(point, vertex, edge.first, edge.second)) {
//                intersects = true;
//                std::cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                          << vertex.x << ", " << vertex.y << ", " << vertex.z << ") intersects with cube edge ("
//                          << edge.first.x << ", " << edge.first.y << ", " << edge.first.z << ") to ("
//                          << edge.second.x << ", " << edge.second.y << ", " << edge.second.z << ")\n";
//                break;
//            }
//        }
//        if (!intersects) {
//            double weight = distance(point, vertex);
//            graph[point].emplace_back(vertex, weight);
//            graph[vertex].emplace_back(point, weight);
//            std::cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                      << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//        }
//    }
//}
//
//// A* algorithm implementation
//std::vector<Point> astar(const std::unordered_map<Point, std::vector<std::pair<Point, double>>, PointHash>& graph, const Point& start, const Point& goal) {
//    std::unordered_map<Point, Point, PointHash> cameFrom;
//    std::unordered_map<Point, double, PointHash> gScore;
//    std::unordered_map<Point, double, PointHash> fScore;
//
//    auto compare = [&fScore](const Point& a, const Point& b) {
//        return fScore.at(a) > fScore.at(b);
//    };
//
//    std::set<Point, decltype(compare)> openSet(compare);
//    openSet.insert(start);
//
//    gScore[start] = 0.0;
//    fScore[start] = distance(start, goal);
//
//    while (!openSet.empty()) {
//        Point current = *openSet.begin();
//        openSet.erase(openSet.begin());
//
//        if (current == goal) {
//            std::vector<Point> path;
//            while (current != start) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& [neighbor, weight] : graph.at(current)) {
//            double tentative_gScore = gScore[current] + weight;
//            if (gScore.find(neighbor) == gScore.end() || tentative_gScore < gScore[neighbor]) {
//                cameFrom[neighbor] = current;
//                gScore[neighbor] = tentative_gScore;
//                fScore[neighbor] = gScore[neighbor] + distance(neighbor, goal);
//                if (openSet.find(neighbor) == openSet.end()) {
//                    openSet.insert(neighbor);
//                }
//            }
//        }
//    }
//
//    throw std::runtime_error("No path found");
//}
//
//int main() {
//    // Define a 3D cube as an obstacle
//    std::vector<Point> cubeVertices = {
//        {1, 1, 1}, {1, 4, 1}, {4, 4, 1}, {4, 1, 1},
//        {1, 1, 4}, {1, 4, 4}, {4, 4, 4}, {4, 1, 4}
//    };
//
//    // Define source and end points
//    Point source = {-2, 1, 3};
//    Point end = {6, 4, 4};
//
//    // Initialize graph
//    std::unordered_map<Point, std::vector<std::pair<Point, double>>, PointHash> graph;
//
//    // Add obstacle vertices as nodes
//    for (const auto& vertex : cubeVertices) {
//        graph[vertex] = {};
//    }
//
//    // Add source and end points as nodes
//    graph[source] = {};
//    graph[end] = {};
//
//    // Add edges to the cube vertices
//    addOuterEdges(graph, cubeVertices);
//
//    // Add edges for source and end points
//    std::cout << "Adding edges from source:\n";
//    addEdgesWithoutIntersection(graph, source, cubeVertices, {});
//
//    std::cout << "\nAdding edges from end:\n";
//    addEdgesWithoutIntersection(graph, end, cubeVertices, {});
//
//    // Find the shortest path using A* algorithm
//    try {
//        std::vector<Point> path = astar(graph, source, end);
//        std::cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& p : path) {
//            std::cout << "(" << p.x << ", " << p.y << ", " << p.z << ")\n";
//        }
//    } catch (const std::runtime_error& e) {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}




//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//#include <limits>
//
//const double EPS = 1e-6;
//
//// Struct for representing a point in 3D space
//struct Point {
//    double x, y, z;
//
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS &&
//               fabs(y - other.y) < EPS &&
//               fabs(z - other.z) < EPS;
//    }
//
//    bool operator<(const Point& other) const {
//        if (fabs(x - other.x) > EPS) return x < other.x;
//        if (fabs(y - other.y) > EPS) return y < other.y;
//        return z < other.z;
//    }
//};
//
//// Subtract two points to form a vector
//Point subtract(const Point& a, const Point& b) {
//    return Point(a.x - b.x, a.y - b.y, a.z - b.z);
//}
//
//// Dot product
//double dot(const Point& a, const Point& b) {
//    return a.x * b.x + a.y * b.y + a.z * b.z;
//}
//
//// Cross product
//Point cross(const Point& a, const Point& b) {
//    return Point(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x);
//}
//
//// Magnitude of a vector
//double magnitude(const Point& p) {
//    return std::sqrt(p.x * p.x + p.y * p.y + p.z * p.z);
//}
//
//// Project a vector and check boundaries
//bool segmentsIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
//    Point u = subtract(a2, a1);
//    Point v = subtract(b2, b1);
//    Point w = subtract(a1, b1);
//
//    Point cross_uv = cross(u, v);
//    double n = magnitude(cross_uv);
//
//    // If cross product is zero, lines are parallel
//    if (n < EPS) return false;
//
//    double s = dot(cross(w, v), cross_uv) / (n * n);
//    double t = dot(cross(w, u), cross_uv) / (n * n);
//
//    return (s >= 0 && s <= 1 && t >= 0 && t <= 1);
//}
//
//// Calculate Euclidean distance
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return std::sqrt(std::pow(p1.x - p2.x, 2) +
//                     std::pow(p1.y - p2.y, 2) +
//                     std::pow(p1.z - p2.z, 2));
//}
//
//// Graph class for managing nodes and edges
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    void addEdgesWithoutIntersection(const Point& point, const std::vector<Point>& vertices,
//                                     const std::vector<std::pair<Point, Point>>& cubeEdges) {
//        for (const auto& vertex : vertices) {
//            bool intersects = false;
//            for (const auto& edge : cubeEdges) {
//                if (segmentsIntersect(point, vertex, edge.first, edge.second)) {
//                    intersects = true;
//                    std::cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z
//                              << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z
//                              << ") intersects with cube edge (("
//                              << edge.first.x << ", " << edge.first.y << ", " << edge.first.z
//                              << ") -> (" << edge.second.x << ", " << edge.second.y << ", " << edge.second.z << "))\n";
//                    break;
//                }
//            }
//            if (!intersects) {
//                double weight = euclideanDistance(point, vertex);
//                addEdge(point, vertex, weight);
//                std::cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z
//                          << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//            }
//        }
//    }
//
//    const std::map<Point, std::vector<std::pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    std::map<Point, std::vector<std::pair<Point, double>>> nodes;
//};
//
//// A* algorithm
//std::vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    std::map<Point, double> gScore;
//    std::map<Point, Point> cameFrom;
//    std::map<Point, double> fScore;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&fScore](const Point& lhs, const Point& rhs) {
//        return fScore[lhs] > fScore[rhs];
//    };
//
//    std::priority_queue<Point, std::vector<Point>, decltype(comp)> openSet(comp);
//    
//    gScore[start] = 0;
//    fScore[start] = heuristic(start, goal);
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            std::vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                fScore[neighbor.first] = tentative_gScore + heuristic(neighbor.first, goal);
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    std::vector<Point> cubeVertices = {
//        {1, 1, 1}, {1, 4, 1}, {4, 4, 1}, {4, 1, 1},
//        {1, 1, 4}, {1, 4, 4}, {4, 4, 4}, {4, 1, 4}
//    };
//
//    std::vector<std::pair<Point, Point>> cubeEdges = {
//        {cubeVertices[0], cubeVertices[1]}, {cubeVertices[1], cubeVertices[2]},
//        {cubeVertices[2], cubeVertices[3]}, {cubeVertices[3], cubeVertices[0]},
//        {cubeVertices[4], cubeVertices[5]}, {cubeVertices[5], cubeVertices[6]},
//        {cubeVertices[6], cubeVertices[7]}, {cubeVertices[7], cubeVertices[4]},
//        {cubeVertices[0], cubeVertices[4]}, {cubeVertices[1], cubeVertices[5]},
//        {cubeVertices[2], cubeVertices[6]}, {cubeVertices[3], cubeVertices[7]}
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) graph.addNode(vertex);
//    graph.addNode(source);
//    graph.addNode(end);
//
//    std::cout << "Adding edges from source:\n";
//    graph.addEdgesWithoutIntersection(source, cubeVertices, cubeEdges);
//
//    std::cout << "\nAdding edges from end:\n";
//    graph.addEdgesWithoutIntersection(end, cubeVertices, cubeEdges);
//
//    std::vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        std::cout << "\nShortest path found:\n";
//        for (const auto& point : path) {
//            std::cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}




//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//#include <limits>
//
//const double EPS = 1e-6;
//
//// Struct for representing a point in 3D space
//struct Point {
//    double x, y, z;
//
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS &&
//               fabs(y - other.y) < EPS &&
//               fabs(z - other.z) < EPS;
//    }
//
//    bool operator<(const Point& other) const {
//        if (fabs(x - other.x) > EPS) return x < other.x;
//        if (fabs(y - other.y) > EPS) return y < other.y;
//        return z < other.z;
//    }
//};
//
//// Vector subtraction
//Point subtract(const Point& a, const Point& b) {
//    return Point(a.x - b.x, a.y - b.y, a.z - b.z);
//}
//
//// Dot product
//double dot(const Point& a, const Point& b) {
//    return a.x * b.x + a.y * b.y + a.z * b.z;
//}
//
//// Cross product
//Point cross(const Point& a, const Point& b) {
//    return Point(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x);
//}
//
//// Magnitude squared of a vector
//double magnitudeSquared(const Point& p) {
//    return p.x * p.x + p.y * p.y + p.z * p.z;
//}
//
//// Calculate Euclidean distance between two points
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return std::sqrt(std::pow(p1.x - p2.x, 2) +
//                     std::pow(p1.y - p2.y, 2) +
//                     std::pow(p1.z - p2.z, 2));
//}
//
//// Check if two line segments intersect in 3D
//bool segmentsIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
//    Point u = subtract(a2, a1);  // Vector a1 -> a2
//    Point v = subtract(b2, b1);  // Vector b1 -> b2
//    Point w = subtract(a1, b1);  // Vector b1 -> a1
//
//    // Compute the cross product of u and v
//    Point n = cross(u, v);
//    double n_len2 = magnitudeSquared(n);
//
//    // If the cross product is zero, the segments are parallel
//    if (n_len2 < EPS) return false;
//
//    // Compute the parametric values s and t
//    double s = dot(cross(w, v), n) / n_len2;
//    double t = dot(cross(w, u), n) / n_len2;
//
//    // Check if the intersection is within both line segments
//    return (s >= 0.0 && s <= 1.0 && t >= 0.0 && t <= 1.0);
//}
//
//// Graph class for managing nodes and edges
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    void addEdgesWithoutIntersection(const Point& point, const std::vector<Point>& vertices,
//                                     const std::vector<std::pair<Point, Point>>& cubeEdges) {
//        for (const auto& vertex : vertices) {
//            bool intersects = false;
//            for (const auto& edge : cubeEdges) {
//                if (segmentsIntersect(point, vertex, edge.first, edge.second)) {
//                    intersects = true;
//                    std::cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z
//                              << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z
//                              << ") intersects with cube edge (("
//                              << edge.first.x << ", " << edge.first.y << ", " << edge.first.z
//                              << ") -> (" << edge.second.x << ", " << edge.second.y << ", " << edge.second.z << "))\n";
//                    break;
//                }
//            }
//            if (!intersects) {
//                double weight = euclideanDistance(point, vertex);
//                addEdge(point, vertex, weight);
//                std::cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z
//                          << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//            }
//        }
//    }
//
//    const std::map<Point, std::vector<std::pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    std::map<Point, std::vector<std::pair<Point, double>>> nodes;
//};
//
//// A* algorithm implementation
//std::vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    std::map<Point, double> gScore;
//    std::map<Point, Point> cameFrom;
//    std::map<Point, double> fScore;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&fScore](const Point& lhs, const Point& rhs) {
//        return fScore[lhs] > fScore[rhs];
//    };
//
//    std::priority_queue<Point, std::vector<Point>, decltype(comp)> openSet(comp);
//    
//    gScore[start] = 0;
//    fScore[start] = heuristic(start, goal);
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            std::vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                fScore[neighbor.first] = tentative_gScore + heuristic(neighbor.first, goal);
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    std::vector<Point> cubeVertices = {
//        {1, 1, 1}, {1, 4, 1}, {4, 4, 1}, {4, 1, 1},
//        {1, 1, 4}, {1, 4, 4}, {4, 4, 4}, {4, 1, 4}
//    };
//
//    std::vector<std::pair<Point, Point>> cubeEdges = {
//        {cubeVertices[0], cubeVertices[1]}, {cubeVertices[1], cubeVertices[2]},
//        {cubeVertices[2], cubeVertices[3]}, {cubeVertices[3], cubeVertices[0]},
//        {cubeVertices[4], cubeVertices[5]}, {cubeVertices[5], cubeVertices[6]},
//        {cubeVertices[6], cubeVertices[7]}, {cubeVertices[7], cubeVertices[4]},
//        {cubeVertices[0], cubeVertices[4]}, {cubeVertices[1], cubeVertices[5]},
//        {cubeVertices[2], cubeVertices[6]}, {cubeVertices[3], cubeVertices[7]}
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) graph.addNode(vertex);
//    graph.addNode(source);
//    graph.addNode(end);
//
//    std::cout << "Adding edges from source:\n";
//    graph.addEdgesWithoutIntersection(source, cubeVertices, cubeEdges);
//
//    std::cout << "\nAdding edges from end:\n";
//    graph.addEdgesWithoutIntersection(end, cubeVertices, cubeEdges);
//
//    std::vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        std::cout << "\nShortest path found:\n";
//        for (const auto& point : path) {
//            std::cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}






//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//#include <limits>
//
//const double EPS = 1e-6;
//
//// Struct for representing a point in 3D space
//struct Point {
//    double x, y, z;
//
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS &&
//               fabs(y - other.y) < EPS &&
//               fabs(z - other.z) < EPS;
//    }
//
//    bool operator<(const Point& other) const {
//        if (fabs(x - other.x) > EPS) return x < other.x;
//        if (fabs(y - other.y) > EPS) return y < other.y;
//        return z < other.z;
//    }
//};
//
//// Vector subtraction
//Point subtract(const Point& a, const Point& b) {
//    return Point(a.x - b.x, a.y - b.y, a.z - b.z);
//}
//
//// Dot product
//double dot(const Point& a, const Point& b) {
//    return a.x * b.x + a.y * b.y + a.z * b.z;
//}
//
//// Cross product
//Point cross(const Point& a, const Point& b) {
//    return Point(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x);
//}
//
//// Magnitude of a vector
//double magnitude(const Point& p) {
//    return std::sqrt(p.x * p.x + p.y * p.y + p.z * p.z);
//}
//
//// Calculate Euclidean distance between two points
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return std::sqrt(std::pow(p1.x - p2.x, 2) +
//                     std::pow(p1.y - p2.y, 2) +
//                     std::pow(p1.z - p2.z, 2));
//}
//
//// Check if two line segments intersect
//bool segmentsIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
//    Point u = subtract(a2, a1);
//    Point v = subtract(b2, b1);
//    Point w = subtract(a1, b1);
//
//    Point n = cross(u, v);
//    double n_norm = magnitude(n);
//
//    // Check if lines are parallel
//    if (n_norm < EPS) return false;
//
//    double s = dot(cross(w, v), n) / (n_norm * n_norm);
//    double t = dot(cross(w, u), n) / (n_norm * n_norm);
//
//    return (s >= 0 && s <= 1 && t >= 0 && t <= 1);
//}
//
//// Graph class for managing nodes and edges
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    void addEdgesWithoutIntersection(const Point& point, const std::vector<Point>& vertices,
//                                     const std::vector<std::pair<Point, Point>>& cubeEdges) {
//        for (const auto& vertex : vertices) {
//            bool intersects = false;
//            for (const auto& edge : cubeEdges) {
//                if (segmentsIntersect(point, vertex, edge.first, edge.second)) {
//                    intersects = true;
//                    std::cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z
//                              << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z
//                              << ") intersects with cube edge (("
//                              << edge.first.x << ", " << edge.first.y << ", " << edge.first.z
//                              << ") -> (" << edge.second.x << ", " << edge.second.y << ", " << edge.second.z << "))\n";
//                    break;
//                }
//            }
//            if (!intersects) {
//                double weight = euclideanDistance(point, vertex);
//                addEdge(point, vertex, weight);
//                std::cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z
//                          << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//            }
//        }
//    }
//
//    const std::map<Point, std::vector<std::pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    std::map<Point, std::vector<std::pair<Point, double>>> nodes;
//};
//
//// A* algorithm implementation
//std::vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    std::map<Point, double> gScore;
//    std::map<Point, Point> cameFrom;
//    std::map<Point, double> fScore;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&fScore](const Point& lhs, const Point& rhs) {
//        return fScore[lhs] > fScore[rhs];
//    };
//
//    std::priority_queue<Point, std::vector<Point>, decltype(comp)> openSet(comp);
//    
//    gScore[start] = 0;
//    fScore[start] = heuristic(start, goal);
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            std::vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                fScore[neighbor.first] = tentative_gScore + heuristic(neighbor.first, goal);
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    std::vector<Point> cubeVertices = {
//        {1, 1, 1}, {1, 4, 1}, {4, 4, 1}, {4, 1, 1},
//        {1, 1, 4}, {1, 4, 4}, {4, 4, 4}, {4, 1, 4}
//    };
//
//    std::vector<std::pair<Point, Point>> cubeEdges = {
//        {cubeVertices[0], cubeVertices[1]}, {cubeVertices[1], cubeVertices[2]},
//        {cubeVertices[2], cubeVertices[3]}, {cubeVertices[3], cubeVertices[0]},
//        {cubeVertices[4], cubeVertices[5]}, {cubeVertices[5], cubeVertices[6]},
//        {cubeVertices[6], cubeVertices[7]}, {cubeVertices[7], cubeVertices[4]},
//        {cubeVertices[0], cubeVertices[4]}, {cubeVertices[1], cubeVertices[5]},
//        {cubeVertices[2], cubeVertices[6]}, {cubeVertices[3], cubeVertices[7]}
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) graph.addNode(vertex);
//    graph.addNode(source);
//    graph.addNode(end);
//
//    std::cout << "Adding edges from source:\n";
//    graph.addEdgesWithoutIntersection(source, cubeVertices, cubeEdges);
//
//    std::cout << "\nAdding edges from end:\n";
//    graph.addEdgesWithoutIntersection(end, cubeVertices, cubeEdges);
//
//    std::vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        std::cout << "\nShortest path found:\n";
//        for (const auto& point : path) {
//            std::cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}






//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//#include <limits>
//
//const double EPS = 1e-6;
//
//// Struct for representing a point in 3D space
//struct Point {
//    double x, y, z;
//
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS &&
//               fabs(y - other.y) < EPS &&
//               fabs(z - other.z) < EPS;
//    }
//
//    bool operator<(const Point& other) const {
//        if (fabs(x - other.x) > EPS) return x < other.x;
//        if (fabs(y - other.y) > EPS) return y < other.y;
//        return z < other.z;
//    }
//};
//
//// Calculate Euclidean distance between two points
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return std::sqrt(std::pow(p1.x - p2.x, 2) +
//                     std::pow(p1.y - p2.y, 2) +
//                     std::pow(p1.z - p2.z, 2));
//}
//
//// Line segment intersection in 3D
//bool segmentsIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
//    auto cross = [](const Point& u, const Point& v) {
//        return Point(u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x);
//    };
//
//    auto subtract = [](const Point& u, const Point& v) {
//        return Point(u.x - v.x, u.y - v.y, u.z - v.z);
//    };
//
//    Point u = subtract(a2, a1);
//    Point v = subtract(b2, b1);
//    Point w = subtract(a1, b1);
//
//    Point n = cross(u, v);
//    double n_norm = n.x * n.x + n.y * n.y + n.z * n.z;
//
//    if (n_norm < EPS) return false; // Lines are parallel (no intersection)
//
//    return false; // Placeholder for exact 3D intersection check
//}
//
//// Graph class for managing nodes and edges
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    void addEdgesWithoutIntersection(const Point& point, const std::vector<Point>& vertices,
//                                     const std::vector<std::pair<Point, Point>>& cubeEdges) {
//        for (const auto& vertex : vertices) {
//            bool intersects = false;
//            for (const auto& edge : cubeEdges) {
//                if (segmentsIntersect(point, vertex, edge.first, edge.second)) {
//                    intersects = true;
//                    std::cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z
//                              << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z
//                              << ") intersects with cube edge (("
//                              << edge.first.x << ", " << edge.first.y << ", " << edge.first.z
//                              << ") -> (" << edge.second.x << ", " << edge.second.y << ", " << edge.second.z << "))\n";
//                    break;
//                }
//            }
//            if (!intersects) {
//                double weight = euclideanDistance(point, vertex);
//                addEdge(point, vertex, weight);
//                std::cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z
//                          << ") to (" << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//            }
//        }
//    }
//
//    const std::map<Point, std::vector<std::pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    std::map<Point, std::vector<std::pair<Point, double>>> nodes;
//};
//
//// A* algorithm implementation
//std::vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    std::map<Point, double> gScore;
//    std::map<Point, Point> cameFrom;
//    std::map<Point, double> fScore;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&fScore](const Point& lhs, const Point& rhs) {
//        return fScore[lhs] > fScore[rhs];
//    };
//
//    std::priority_queue<Point, std::vector<Point>, decltype(comp)> openSet(comp);
//    
//    gScore[start] = 0;
//    fScore[start] = heuristic(start, goal);
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            std::vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                fScore[neighbor.first] = tentative_gScore + heuristic(neighbor.first, goal);
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    // Define cube vertices
//    std::vector<Point> cubeVertices = {
//        {1, 1, 1}, {1, 4, 1}, {4, 4, 1}, {4, 1, 1},
//        {1, 1, 4}, {1, 4, 4}, {4, 4, 4}, {4, 1, 4}
//    };
//
//    // Define cube edges
//    std::vector<std::pair<Point, Point>> cubeEdges = {
//        {cubeVertices[0], cubeVertices[1]}, {cubeVertices[1], cubeVertices[2]},
//        {cubeVertices[2], cubeVertices[3]}, {cubeVertices[3], cubeVertices[0]},
//        {cubeVertices[4], cubeVertices[5]}, {cubeVertices[5], cubeVertices[6]},
//        {cubeVertices[6], cubeVertices[7]}, {cubeVertices[7], cubeVertices[4]},
//        {cubeVertices[0], cubeVertices[4]}, {cubeVertices[1], cubeVertices[5]},
//        {cubeVertices[2], cubeVertices[6]}, {cubeVertices[3], cubeVertices[7]}
//    };
//
//    // Define source and end points
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    // Build the graph
//    Graph graph;
//    for (const auto& vertex : cubeVertices) graph.addNode(vertex);
//    graph.addNode(source);
//    graph.addNode(end);
//
//    std::cout << "Adding edges from source:\n";
//    graph.addEdgesWithoutIntersection(source, cubeVertices, cubeEdges);
//
//    std::cout << "\nAdding edges from end:\n";
//    graph.addEdgesWithoutIntersection(end, cubeVertices, cubeEdges);
//
//    // Run A* algorithm
//    std::vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        std::cout << "\nShortest path found:\n";
//        for (const auto& point : path) {
//            std::cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}




//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//#include <limits>
//
//const double EPS = 1e-6;
//
//// Struct for representing a point in 3D space
//struct Point {
//    double x, y, z;
//
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS &&
//               fabs(y - other.y) < EPS &&
//               fabs(z - other.z) < EPS;
//    }
//
//    bool operator<(const Point& other) const {
//        if (fabs(x - other.x) > EPS) return x < other.x;
//        if (fabs(y - other.y) > EPS) return y < other.y;
//        return z < other.z;
//    }
//};
//
//// Calculate Euclidean distance between two points
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return std::sqrt(std::pow(p1.x - p2.x, 2) +
//                     std::pow(p1.y - p2.y, 2) +
//                     std::pow(p1.z - p2.z, 2));
//}
//
//// Function to check if two line segments intersect in 3D
//bool segmentsIntersect(const Point& a1, const Point& a2, const Point& b1, const Point& b2) {
//    // Vector operations
//    auto cross = [](const Point& u, const Point& v) {
//        return Point(u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x);
//    };
//
//    auto subtract = [](const Point& u, const Point& v) {
//        return Point(u.x - v.x, u.y - v.y, u.z - v.z);
//    };
//
//    Point u = subtract(a2, a1);
//    Point v = subtract(b2, b1);
//    Point w = subtract(a1, b1);
//
//    Point n = cross(u, v);
//    double n_norm = n.x * n.x + n.y * n.y + n.z * n.z;
//
//    // If n_norm is zero, lines are parallel
//    if (n_norm < EPS) return false;
//
//    return false;  // Proper 3D check skipped for now; assuming edges do not intersect
//}
//
//// Graph class
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    void addEdgesWithoutIntersection(const Point& point, const std::vector<Point>& vertices,
//                                     const std::vector<std::pair<Point, Point>>& cubeEdges) {
//        for (const auto& vertex : vertices) {
//            bool intersects = false;
//            for (const auto& edge : cubeEdges) {
//                if (segmentsIntersect(point, vertex, edge.first, edge.second)) {
//                    intersects = true;
//                    std::cout << "Rejected edge: (" << point.x << ", " << point.y << ", " << point.z
//                              << ") -> (" << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//                    break;
//                }
//            }
//            if (!intersects) {
//                double weight = euclideanDistance(point, vertex);
//                addEdge(point, vertex, weight);
//                std::cout << "Added edge: (" << point.x << ", " << point.y << ", " << point.z
//                          << ") -> (" << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//            }
//        }
//    }
//
//    const std::map<Point, std::vector<std::pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    std::map<Point, std::vector<std::pair<Point, double>>> nodes;
//};
//
//// A* algorithm
//std::vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    std::map<Point, double> gScore;
//    std::map<Point, Point> cameFrom;
//    std::map<Point, double> fScore;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&fScore](const Point& lhs, const Point& rhs) {
//        return fScore[lhs] > fScore[rhs];
//    };
//
//    std::priority_queue<Point, std::vector<Point>, decltype(comp)> openSet(comp);
//    
//    gScore[start] = 0;
//    fScore[start] = heuristic(start, goal);
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            std::vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                fScore[neighbor.first] = tentative_gScore + heuristic(neighbor.first, goal);
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    std::vector<Point> cubeVertices = {
//        {1, 1, 1}, {1, 4, 1}, {4, 4, 1}, {4, 1, 1},
//        {1, 1, 4}, {1, 4, 4}, {4, 4, 4}, {4, 1, 4}
//    };
//
//    std::vector<std::pair<Point, Point>> cubeEdges = {
//        {cubeVertices[0], cubeVertices[1]}, {cubeVertices[1], cubeVertices[2]},
//        {cubeVertices[2], cubeVertices[3]}, {cubeVertices[3], cubeVertices[0]},
//        {cubeVertices[4], cubeVertices[5]}, {cubeVertices[5], cubeVertices[6]},
//        {cubeVertices[6], cubeVertices[7]}, {cubeVertices[7], cubeVertices[4]},
//        {cubeVertices[0], cubeVertices[4]}, {cubeVertices[1], cubeVertices[5]},
//        {cubeVertices[2], cubeVertices[6]}, {cubeVertices[3], cubeVertices[7]}
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    graph.addEdgesWithoutIntersection(source, cubeVertices, cubeEdges);
//    graph.addEdgesWithoutIntersection(end, cubeVertices, cubeEdges);
//
//    std::vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        std::cout << "Shortest path found:\n";
//        for (const auto& point : path) {
//            std::cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        std::cout << "No path found.\n";
//    }
//
//    return 0;
//}




//claude********

//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//#include <limits>
//#include <tuple>
//
//const double EPS = 1e-6;
//
//// Forward declaration of Point struct
//struct Point;
//
//// Forward declaration of utility functions
//double euclideanDistance(const Point& p1, const Point& p2);
//bool lineSegmentIntersection(const Point& a, const Point& b, const Point& c, const Point& d);
//
//// Point struct definition
//struct Point {
//    double x, y, z;
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//    
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS &&
//               fabs(y - other.y) < EPS &&
//               fabs(z - other.z) < EPS;
//    }
//    
//    bool operator<(const Point& other) const {
//        if (fabs(x - other.x) > EPS) return x < other.x;
//        if (fabs(y - other.y) > EPS) return y < other.y;
//        return z < other.z;
//    }
//};
//
//// Utility function for distance calculation
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return std::sqrt(
//        std::pow(p1.x - p2.x, 2) +
//        std::pow(p1.y - p2.y, 2) +
//        std::pow(p1.z - p2.z, 2)
//    );
//}
//
//// Check if two 3D line segments intersect
//bool lineSegmentIntersection(const Point& a, const Point& b, const Point& c, const Point& d) {
//    // Adapted from Möller–Trumbore intersection algorithm
//    Point u = b - a;
//    Point v = d - c;
//    Point w = a - c;
//
//    double a_ = u.x, b_ = v.x, c_ = w.x;
//    double d_ = u.y, e_ = v.y, f_ = w.y;
//    double g_ = u.z, h_ = v.z, i_ = w.z;
//
//    double det = a_ * (e_ * i_ - f_ * h_) - b_ * (d_ * i_ - f_ * g_) + c_ * (d_ * h_ - e_ * g_);
//    if (fabs(det) < EPS)
//        return false;
//
//    double t = (i_ * (a_ * f_ - d_ * c_) + h_ * (c_ * e_ - a_ * f_) + g_ * (a_ * d_ - c_ * b_)) / det;
//    double u_ = (c_ * (h_ * w.y - e_ * w.z) + b_ * (d_ * w.z - f_ * w.y) + a_ * (e_ * w.x - d_ * w.x)) / det;
//    double v_ = (w.x * (e_ * i_ - f_ * h_) + w.y * (c_ * h_ - a_ * i_) + w.z * (a_ * f_ - c_ * d_)) / det;
//
//    return (t >= 0 && t <= 1 && u_ >= 0 && v_ >= 0 && u_ + v_ <= 1);
//}
//
//class Graph {
//public:
//    void addNode(const Point& p) {
//        // Only add the node if it doesn't exist
//        nodes.try_emplace(p, std::vector<std::pair<Point, double>>{});
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        // Add edge in both directions
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    void addEdgesWithoutIntersection(const Point& point,
//                                     const std::vector<Point>& vertices,
//                                     const std::vector<std::pair<Point, Point>>& cubeEdges) {
//        for (const auto& vertex : vertices) {
//            std::pair<Point, Point> newEdge = {point, vertex};
//            bool intersects = false;
//            
//            // Check if new edge intersects with any cube edges
//            for (const auto& cubeEdge : cubeEdges) {
//                if (lineSegmentIntersection(newEdge.first, newEdge.second, cubeEdge.first, cubeEdge.second)) {
//                    intersects = true;
//                    std::cout << "Edge intersects with cube edge\n";
//                    break;
//                }
//            }
//            
//            if (!intersects) {
//                double weight = euclideanDistance(point, vertex);
//                addEdge(point, vertex, weight);
//                std::cout << "Added edge\n";
//            }
//        }
//    }
//
//    const std::map<Point, std::vector<std::pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    std::map<Point, std::vector<std::pair<Point, double>>> nodes;
//};
//
//std::vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    // Use unordered_map to improve performance
//    std::map<Point, double> gScore;
//    std::map<Point, Point> cameFrom;
//    std::map<Point, double> fScore;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&fScore](const Point& lhs, const Point& rhs) {
//        return fScore[lhs] > fScore[rhs];
//    };
//
//    std::priority_queue<Point, std::vector<Point>, decltype(comp)> openSet(comp);
//    
//    // Initialize start node
//    gScore[start] = 0;
//    fScore[start] = heuristic(start, goal);
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        // Check if reached goal
//        if (current == goal) {
//            std::vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            std::reverse(path.begin(), path.end());
//            return path;
//        }
//
//        // Process neighbors
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//
//            // Update if better path found
//            if (gScore.find(neighbor.first) == gScore.end() ||
//                tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                fScore[neighbor.first] = tentative_gScore + heuristic(neighbor.first, goal);
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {}; // No path found
//}
//
//int main() {
//    // Define cube vertices
//    std::vector<Point> cubeVertices = {
//        Point(1, 1, 1), Point(1, 4, 1), Point(4, 4, 1), Point(4, 1, 1),
//        Point(1, 1, 4), Point(1, 4, 4), Point(4, 4, 4), Point(4, 1, 4)
//    };
//
//    // Create cube edges for intersection checking
//    std::vector<std::pair<Point, Point>> cubeEdges = {
//        {cubeVertices[0], cubeVertices[1]},
//        {cubeVertices[1], cubeVertices[2]},
//        {cubeVertices[2], cubeVertices[3]},
//        {cubeVertices[3], cubeVertices[0]},
//        {cubeVertices[4], cubeVertices[5]},
//        {cubeVertices[5], cubeVertices[6]},
//        {cubeVertices[6], cubeVertices[7]},
//        {cubeVertices[7], cubeVertices[4]},
//        {cubeVertices[0], cubeVertices[4]},
//        {cubeVertices[1], cubeVertices[5]},
//        {cubeVertices[2], cubeVertices[6]},
//        {cubeVertices[3], cubeVertices[7]}
//    };
//
//    // Define source and end points
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    // Create graph and add nodes
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    // Add edges
//    std::cout << "Adding edges from source:\n";
//    graph.addEdgesWithoutIntersection(source, cubeVertices, cubeEdges);
//
//    std::cout << "\nAdding edges from end:\n";
//    graph.addEdgesWithoutIntersection(end, cubeVertices, cubeEdges);
//
//    // Find path
//    std::vector<Point> path = aStar(graph, source, end);
//
//    // Output results
//    if (!path.empty()) {
//        std::cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& point : path) {
//            std::cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        std::cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}
//
//



//close***************************

//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//using namespace std;
//
//const double EPS = 1e-6;
//
//struct Point {
//    double x, y, z;
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS && fabs(y - other.y) < EPS && fabs(z - other.z) < EPS;
//    }
//    bool operator<(const Point& other) const {
//        return tie(x, y, z) < tie(other.x, other.y, other.z);
//    }
//};
//
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    const map<Point, vector<pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    map<Point, vector<pair<Point, double>>> nodes;
//};
//
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return sqrt(pow(p1.x - p2.x, 2) + pow(p1.y - p2.y, 2) + pow(p1.z - p2.z, 2));
//}
//
//void addEdges(Graph& graph, const Point& point, const vector<Point>& vertices) {
//    for (const auto& vertex : vertices) {
//        double weight = euclideanDistance(point, vertex);
//        graph.addEdge(point, vertex, weight);
//        cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//             << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//    }
//}
//
//vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    map<Point, double> gScore;
//    map<Point, Point> cameFrom;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&gScore](const Point& lhs, const Point& rhs) {
//        return gScore[lhs] > gScore[rhs];
//    };
//
//    priority_queue<Point, vector<Point>, decltype(comp)> openSet(comp);
//    gScore[start] = 0;
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    vector<Point> cubeVertices = {
//        Point(1, 1, 1), Point(1, 4, 1), Point(4, 4, 1), Point(4, 1, 1),
//        Point(1, 1, 4), Point(1, 4, 4), Point(4, 4, 4), Point(4, 1, 4)
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    cout << "Adding edges from source:\n";
//    addEdges(graph, source, cubeVertices);
//
//    cout << "\nAdding edges from end:\n";
//    addEdges(graph, end, cubeVertices);
//
//    vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& point : path) {
//            cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}
//




//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//using namespace std;
//
//const double EPS = 1e-6;
//
//struct Point {
//    double x, y, z;
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < EPS && fabs(y - other.y) < EPS && fabs(z - other.z) < EPS;
//    }
//    bool operator<(const Point& other) const {
//        return tie(x, y, z) < tie(other.x, other.y, other.z);
//    }
//};
//
//struct Edge {
//    Point a, b;
//    Edge(Point a, Point b) : a(a), b(b) {}
//};
//
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    const map<Point, vector<pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    map<Point, vector<pair<Point, double>>> nodes;
//};
//
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return sqrt(pow(p1.x - p2.x, 2) + pow(p1.y - p2.y, 2) + pow(p1.z - p2.z, 2));
//}
//
//bool onSegment(Point p, Point q, Point r) {
//    return q.x <= max(p.x, r.x) + EPS && q.x >= min(p.x, r.x) - EPS &&
//           q.y <= max(p.y, r.y) + EPS && q.y >= min(p.y, r.y) - EPS &&
//           q.z <= max(p.z, r.z) + EPS && q.z >= min(p.z, r.z) - EPS;
//}
//
//bool segmentsIntersect(const Edge& e1, const Edge& e2) {
//    auto cross = [](const Point& p, const Point& q) -> Point {
//        return Point(p.y * q.z - p.z * q.y, p.z * q.x - p.x * q.z, p.x * q.y - p.y * q.x);
//    };
//
//    auto subtract = [](const Point& p1, const Point& p2) -> Point {
//        return Point(p1.x - p2.x, p1.y - p2.y, p1.z - p2.z);
//    };
//
//    Point u = subtract(e1.b, e1.a);
//    Point v = subtract(e2.b, e2.a);
//    Point w = subtract(e1.a, e2.a);
//
//    Point uCrossV = cross(u, v);
//    double denom = uCrossV.x * uCrossV.x + uCrossV.y * uCrossV.y + uCrossV.z * uCrossV.z;
//
//    if (fabs(denom) < EPS) {
//        // Check collinearity
//        return onSegment(e1.a, e2.a, e1.b) || onSegment(e1.a, e2.b, e1.b);
//    }
//
//    // Check if segments intersect using parameter t
//    double s = (cross(w, v).x * uCrossV.x + cross(w, v).y * uCrossV.y + cross(w, v).z * uCrossV.z) / denom;
//    double t = (cross(w, u).x * uCrossV.x + cross(w, u).y * uCrossV.y + cross(w, u).z * uCrossV.z) / denom;
//
//    return (s >= -EPS && s <= 1 + EPS && t >= -EPS && t <= 1 + EPS);
//}
//
//void addEdgesWithoutIntersection(Graph& graph, const Point& point, const vector<Point>& vertices, const vector<Edge>& cubeEdges) {
//    for (const auto& vertex : vertices) {
//        Edge newEdge(point, vertex);
//        bool intersects = false;
//
//        for (const auto& edge : cubeEdges) {
//            if (segmentsIntersect(newEdge, edge)) {
//                intersects = true;
//                cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                     << vertex.x << ", " << vertex.y << ", " << vertex.z << ") intersects with cube edge [("
//                     << edge.a.x << ", " << edge.a.y << ", " << edge.a.z << ") -> ("
//                     << edge.b.x << ", " << edge.b.y << ", " << edge.b.z << ")]\n";
//                break;
//            }
//        }
//
//        if (!intersects) {
//            double weight = euclideanDistance(point, vertex);
//            graph.addEdge(point, vertex, weight);
//            cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                 << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//        }
//    }
//}
//
//vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    map<Point, double> gScore;
//    map<Point, Point> cameFrom;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&gScore](const Point& lhs, const Point& rhs) {
//        return gScore[lhs] > gScore[rhs];
//    };
//
//    priority_queue<Point, vector<Point>, decltype(comp)> openSet(comp);
//    gScore[start] = 0;
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    vector<Point> cubeVertices = {
//        Point(1, 1, 1), Point(1, 4, 1), Point(4, 4, 1), Point(4, 1, 1),
//        Point(1, 1, 4), Point(1, 4, 4), Point(4, 4, 4), Point(4, 1, 4)
//    };
//
//    vector<Edge> cubeEdges = {
//        Edge(cubeVertices[0], cubeVertices[1]), Edge(cubeVertices[1], cubeVertices[2]),
//        Edge(cubeVertices[2], cubeVertices[3]), Edge(cubeVertices[3], cubeVertices[0]),
//        Edge(cubeVertices[4], cubeVertices[5]), Edge(cubeVertices[5], cubeVertices[6]),
//        Edge(cubeVertices[6], cubeVertices[7]), Edge(cubeVertices[7], cubeVertices[4]),
//        Edge(cubeVertices[0], cubeVertices[4]), Edge(cubeVertices[1], cubeVertices[5]),
//        Edge(cubeVertices[2], cubeVertices[6]), Edge(cubeVertices[3], cubeVertices[7])
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    cout << "Adding edges from source:\n";
//    addEdgesWithoutIntersection(graph, source, cubeVertices, cubeEdges);
//
//    cout << "\nAdding edges from end:\n";
//    addEdgesWithoutIntersection(graph, end, cubeVertices, cubeEdges);
//
//    vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& point : path) {
//            cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}





//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//using namespace std;
//
//struct Point {
//    double x, y, z;
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < 1e-8 && fabs(y - other.y) < 1e-8 && fabs(z - other.z) < 1e-8;
//    }
//    bool operator<(const Point& other) const {
//        return tie(x, y, z) < tie(other.x, other.y, other.z);
//    }
//};
//
//struct Edge {
//    Point a, b;
//    Edge(Point a, Point b) : a(a), b(b) {}
//};
//
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    const map<Point, vector<pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    map<Point, vector<pair<Point, double>>> nodes;
//};
//
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return sqrt(pow(p1.x - p2.x, 2) + pow(p1.y - p2.y, 2) + pow(p1.z - p2.z, 2));
//}
//
//bool segmentsIntersect(const Edge& e1, const Edge& e2) {
//    auto crossProduct = [](const Point& u, const Point& v) -> Point {
//        return Point(u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x);
//    };
//
//    auto subtract = [](const Point& p1, const Point& p2) -> Point {
//        return Point(p1.x - p2.x, p1.y - p2.y, p1.z - p2.z);
//    };
//
//    auto onSegment = [](const Point& p, const Point& q, const Point& r) {
//        return q.x <= max(p.x, r.x) && q.x >= min(p.x, r.x) &&
//               q.y <= max(p.y, r.y) && q.y >= min(p.y, r.y) &&
//               q.z <= max(p.z, r.z) && q.z >= min(p.z, r.z);
//    };
//
//    Point u = subtract(e1.b, e1.a);
//    Point v = subtract(e2.b, e2.a);
//    Point w = subtract(e1.a, e2.a);
//
//    Point uCrossV = crossProduct(u, v);
//    double denom = pow(uCrossV.x, 2) + pow(uCrossV.y, 2) + pow(uCrossV.z, 2);
//
//    if (fabs(denom) < 1e-8) {
//        return onSegment(e1.a, e2.a, e1.b) || onSegment(e1.a, e2.b, e1.b);
//    }
//
//    double s = (crossProduct(w, v).x * uCrossV.x + crossProduct(w, v).y * uCrossV.y + crossProduct(w, v).z * uCrossV.z) / denom;
//    double t = (crossProduct(w, u).x * uCrossV.x + crossProduct(w, u).y * uCrossV.y + crossProduct(w, u).z * uCrossV.z) / denom;
//
//    return (s >= 0 && s <= 1 && t >= 0 && t <= 1);
//}
//
//void addEdgesWithoutIntersection(Graph& graph, const Point& point, const vector<Point>& vertices, const vector<Edge>& cubeEdges) {
//    for (const auto& vertex : vertices) {
//        Edge newEdge(point, vertex);
//        bool intersects = false;
//
//        for (const auto& edge : cubeEdges) {
//            if (segmentsIntersect(newEdge, edge)) {
//                intersects = true;
//                cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                     << vertex.x << ", " << vertex.y << ", " << vertex.z << ") intersects with cube edge [("
//                     << edge.a.x << ", " << edge.a.y << ", " << edge.a.z << ") -> ("
//                     << edge.b.x << ", " << edge.b.y << ", " << edge.b.z << ")]\n";
//                break;
//            }
//        }
//
//        if (!intersects) {
//            double weight = euclideanDistance(point, vertex);
//            graph.addEdge(point, vertex, weight);
//            cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                 << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//        }
//    }
//}
//
//vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    map<Point, double> gScore;
//    map<Point, Point> cameFrom;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&gScore](const Point& lhs, const Point& rhs) {
//        return gScore[lhs] > gScore[rhs];
//    };
//
//    priority_queue<Point, vector<Point>, decltype(comp)> openSet(comp);
//    gScore[start] = 0;
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    vector<Point> cubeVertices = {
//        Point(1, 1, 1), Point(1, 4, 1), Point(4, 4, 1), Point(4, 1, 1),
//        Point(1, 1, 4), Point(1, 4, 4), Point(4, 4, 4), Point(4, 1, 4)
//    };
//
//    vector<Edge> cubeEdges;
//    for (size_t i = 0; i < cubeVertices.size(); i++) {
//        for (size_t j = i + 1; j < cubeVertices.size(); j++) {
//            cubeEdges.push_back(Edge(cubeVertices[i], cubeVertices[j]));
//        }
//    }
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    cout << "Adding edges from source:\n";
//    addEdgesWithoutIntersection(graph, source, cubeVertices, cubeEdges);
//
//    cout << "\nAdding edges from end:\n";
//    addEdgesWithoutIntersection(graph, end, cubeVertices, cubeEdges);
//
//    vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& point : path) {
//            cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}






//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//using namespace std;
//
//struct Point {
//    double x, y, z;
//    Point(double x = 0, double y = 0, double z = 0) : x(x), y(y), z(z) {}
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < 1e-8 && fabs(y - other.y) < 1e-8 && fabs(z - other.z) < 1e-8;
//    }
//    bool operator<(const Point& other) const {
//        return tie(x, y, z) < tie(other.x, other.y, other.z);
//    }
//};
//
//struct Edge {
//    Point a, b;
//    Edge(Point a, Point b) : a(a), b(b) {}
//};
//
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    const map<Point, vector<pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    map<Point, vector<pair<Point, double>>> nodes;
//};
//
//// Helper Functions
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return sqrt(pow(p1.x - p2.x, 2) + pow(p1.y - p2.y, 2) + pow(p1.z - p2.z, 2));
//}
//
//bool segmentsIntersect(const Edge& e1, const Edge& e2) {
//    // Helper function for edge intersection
//    auto crossProduct = [](const Point& u, const Point& v) -> Point {
//        return Point(u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x);
//    };
//    auto subtract = [](const Point& p1, const Point& p2) -> Point {
//        return Point(p1.x - p2.x, p1.y - p2.y, p1.z - p2.z);
//    };
//
//    Point u = subtract(e1.b, e1.a);
//    Point v = subtract(e2.b, e2.a);
//    Point w = subtract(e1.a, e2.a);
//
//    Point uCrossV = crossProduct(u, v);
//    double denom = pow(uCrossV.x, 2) + pow(uCrossV.y, 2) + pow(uCrossV.z, 2);
//
//    if (fabs(denom) < 1e-8) {
//        return false; // Parallel or collinear
//    }
//
//    double s = (crossProduct(w, v).x * uCrossV.x + crossProduct(w, v).y * uCrossV.y + crossProduct(w, v).z * uCrossV.z) / denom;
//    double t = (crossProduct(w, u).x * uCrossV.x + crossProduct(w, u).y * uCrossV.y + crossProduct(w, u).z * uCrossV.z) / denom;
//
//    return (s >= 0 && s <= 1 && t >= 0 && t <= 1);
//}
//
//void addEdgesWithoutIntersection(Graph& graph, const Point& point, const vector<Point>& vertices, const vector<Edge>& cubeEdges) {
//    for (const auto& vertex : vertices) {
//        Edge newEdge(point, vertex);
//        bool intersects = false;
//
//        for (const auto& edge : cubeEdges) {
//            if (segmentsIntersect(newEdge, edge)) {
//                intersects = true;
//                cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                     << vertex.x << ", " << vertex.y << ", " << vertex.z << ") intersects with cube edge [("
//                     << edge.a.x << ", " << edge.a.y << ", " << edge.a.z << ") -> ("
//                     << edge.b.x << ", " << edge.b.y << ", " << edge.b.z << ")]\n";
//                break;
//            }
//        }
//
//        if (!intersects) {
//            double weight = euclideanDistance(point, vertex);
//            graph.addEdge(point, vertex, weight);
//            cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                 << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//        }
//    }
//}
//
//vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    map<Point, double> gScore;
//    map<Point, Point> cameFrom;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&gScore](const Point& lhs, const Point& rhs) {
//        return gScore[lhs] > gScore[rhs];
//    };
//
//    priority_queue<Point, vector<Point>, decltype(comp)> openSet(comp);
//    gScore[start] = 0;
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    vector<Point> cubeVertices = {
//        Point(1, 1, 1), Point(1, 4, 1), Point(4, 4, 1), Point(4, 1, 1),
//        Point(1, 1, 4), Point(1, 4, 4), Point(4, 4, 4), Point(4, 1, 4)
//    };
//
//    vector<Edge> cubeEdges = {
//        Edge(cubeVertices[0], cubeVertices[1]), Edge(cubeVertices[1], cubeVertices[2]),
//        Edge(cubeVertices[2], cubeVertices[3]), Edge(cubeVertices[3], cubeVertices[0]),
//        Edge(cubeVertices[4], cubeVertices[5]), Edge(cubeVertices[5], cubeVertices[6]),
//        Edge(cubeVertices[6], cubeVertices[7]), Edge(cubeVertices[7], cubeVertices[4]),
//        Edge(cubeVertices[0], cubeVertices[4]), Edge(cubeVertices[1], cubeVertices[5]),
//        Edge(cubeVertices[2], cubeVertices[6]), Edge(cubeVertices[3], cubeVertices[7])
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    cout << "Adding edges from source:\n";
//    addEdgesWithoutIntersection(graph, source, cubeVertices, cubeEdges);
//
//    cout << "\nAdding edges from end:\n";
//    addEdgesWithoutIntersection(graph, end, cubeVertices, cubeEdges);
//
//    vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& point : path) {
//            cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}








//closest one

//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <map>
//#include <queue>
//#include <algorithm>
//using namespace std;
//
//struct Point {
//    double x, y, z;
//    Point() : x(0), y(0), z(0) {}
//    Point(double x, double y, double z) : x(x), y(y), z(z) {}
//    bool operator==(const Point& other) const {
//        return fabs(x - other.x) < 1e-8 && fabs(y - other.y) < 1e-8 && fabs(z - other.z) < 1e-8;
//    }
//    bool operator<(const Point& other) const {
//        return tie(x, y, z) < tie(other.x, other.y, other.z);
//    }
//};
//
//struct Edge {
//    Point a, b;
//    Edge(Point a, Point b) : a(a), b(b) {}
//};
//
//class Graph {
//public:
//    void addNode(const Point& p) {
//        if (nodes.find(p) == nodes.end()) {
//            nodes[p] = {};
//        }
//    }
//
//    void addEdge(const Point& u, const Point& v, double weight) {
//        nodes[u].push_back({v, weight});
//        nodes[v].push_back({u, weight});
//    }
//
//    const map<Point, vector<pair<Point, double>>>& getNodes() const {
//        return nodes;
//    }
//
//private:
//    map<Point, vector<pair<Point, double>>> nodes;
//};
//
//// Helper Functions
//double euclideanDistance(const Point& p1, const Point& p2) {
//    return sqrt(pow(p1.x - p2.x, 2) + pow(p1.y - p2.y, 2) + pow(p1.z - p2.z, 2));
//}
//
//bool segmentsIntersect(const Edge& e1, const Edge& e2) {
//    auto crossProduct = [](const Point& u, const Point& v) -> Point {
//        return Point(u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x);
//    };
//
//    auto subtract = [](const Point& p1, const Point& p2) -> Point {
//        return Point(p1.x - p2.x, p1.y - p2.y, p1.z - p2.z);
//    };
//
//    Point u = subtract(e1.b, e1.a);
//    Point v = subtract(e2.b, e2.a);
//    Point w = subtract(e1.a, e2.a);
//
//    Point uCrossV = crossProduct(u, v);
//    double denom = pow(uCrossV.x, 2) + pow(uCrossV.y, 2) + pow(uCrossV.z, 2);
//
//    if (fabs(denom) < 1e-8) {
//        return false; // Parallel or collinear
//    }
//
//    double s = (crossProduct(w, v).x * uCrossV.x + crossProduct(w, v).y * uCrossV.y + crossProduct(w, v).z * uCrossV.z) / denom;
//    double t = (crossProduct(w, u).x * uCrossV.x + crossProduct(w, u).y * uCrossV.y + crossProduct(w, u).z * uCrossV.z) / denom;
//
//    return (s >= 0 && s <= 1 && t >= 0 && t <= 1);
//}
//
//void addEdgesWithoutIntersection(Graph& graph, const Point& point, const vector<Point>& vertices, const vector<Edge>& cubeEdges) {
//    for (const auto& vertex : vertices) {
//        Edge newEdge(point, vertex);
//        bool intersects = false;
//
//        for (const auto& edge : cubeEdges) {
//            if (segmentsIntersect(newEdge, edge)) {
//                intersects = true;
//                cout << "Edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                     << vertex.x << ", " << vertex.y << ", " << vertex.z << ") intersects with cube edge [("
//                     << edge.a.x << ", " << edge.a.y << ", " << edge.a.z << ") -> ("
//                     << edge.b.x << ", " << edge.b.y << ", " << edge.b.z << ")]\n";
//                break;
//            }
//        }
//
//        if (!intersects) {
//            double weight = euclideanDistance(point, vertex);
//            graph.addEdge(point, vertex, weight);
//            cout << "Added edge from (" << point.x << ", " << point.y << ", " << point.z << ") to ("
//                 << vertex.x << ", " << vertex.y << ", " << vertex.z << ")\n";
//        }
//    }
//}
//
//vector<Point> aStar(const Graph& graph, const Point& start, const Point& goal) {
//    map<Point, double> gScore;
//    map<Point, Point> cameFrom;
//
//    auto heuristic = [](const Point& a, const Point& b) {
//        return euclideanDistance(a, b);
//    };
//
//    auto comp = [&gScore](const Point& lhs, const Point& rhs) {
//        return gScore[lhs] > gScore[rhs];
//    };
//
//    priority_queue<Point, vector<Point>, decltype(comp)> openSet(comp);
//    gScore[start] = 0;
//    openSet.push(start);
//
//    while (!openSet.empty()) {
//        Point current = openSet.top();
//        openSet.pop();
//
//        if (current == goal) {
//            vector<Point> path;
//            while (cameFrom.find(current) != cameFrom.end()) {
//                path.push_back(current);
//                current = cameFrom[current];
//            }
//            path.push_back(start);
//            reverse(path.begin(), path.end());
//            return path;
//        }
//
//        for (const auto& neighbor : graph.getNodes().at(current)) {
//            double tentative_gScore = gScore[current] + neighbor.second;
//
//            if (gScore.find(neighbor.first) == gScore.end() || tentative_gScore < gScore[neighbor.first]) {
//                cameFrom[neighbor.first] = current;
//                gScore[neighbor.first] = tentative_gScore;
//                openSet.push(neighbor.first);
//            }
//        }
//    }
//
//    return {};
//}
//
//int main() {
//    vector<Point> cubeVertices = {
//        Point(1, 1, 1), Point(1, 4, 1), Point(4, 4, 1), Point(4, 1, 1),
//        Point(1, 1, 4), Point(1, 4, 4), Point(4, 4, 4), Point(4, 1, 4)
//    };
//
//    vector<Edge> cubeEdges = {
//        Edge(cubeVertices[0], cubeVertices[1]), Edge(cubeVertices[1], cubeVertices[2]),
//        Edge(cubeVertices[2], cubeVertices[3]), Edge(cubeVertices[3], cubeVertices[0]),
//        Edge(cubeVertices[4], cubeVertices[5]), Edge(cubeVertices[5], cubeVertices[6]),
//        Edge(cubeVertices[6], cubeVertices[7]), Edge(cubeVertices[7], cubeVertices[4]),
//        Edge(cubeVertices[0], cubeVertices[4]), Edge(cubeVertices[1], cubeVertices[5]),
//        Edge(cubeVertices[2], cubeVertices[6]), Edge(cubeVertices[3], cubeVertices[7])
//    };
//
//    Point source(-2, 1, 3);
//    Point end(6, 4, 4);
//
//    Graph graph;
//    for (const auto& vertex : cubeVertices) {
//        graph.addNode(vertex);
//    }
//    graph.addNode(source);
//    graph.addNode(end);
//
//    cout << "Adding edges from source:\n";
//    addEdgesWithoutIntersection(graph, source, cubeVertices, cubeEdges);
//
//    cout << "\nAdding edges from end:\n";
//    addEdgesWithoutIntersection(graph, end, cubeVertices, cubeEdges);
//
//    vector<Point> path = aStar(graph, source, end);
//
//    if (!path.empty()) {
//        cout << "\nShortest path found by A* algorithm:\n";
//        for (const auto& point : path) {
//            cout << "(" << point.x << ", " << point.y << ", " << point.z << ")\n";
//        }
//    } else {
//        cout << "\nNo path found from source to end.\n";
//    }
//
//    return 0;
//}

//closest one












//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <queue>
//#include <tuple>
//#include <algorithm>
//#include <limits>
//#include <unordered_set>
//
//using namespace std;
//
//// Define a 3D point structure
//struct Point {
//    double x, y, z;
//
//    // Compute Euclidean distance between two points
//    double distance(const Point& other) const {
//        return sqrt((x - other.x) * (x - other.x) +
//                    (y - other.y) * (y - other.y) +
//                    (z - other.z) * (z - other.z));
//    }
//
//    // Operator for equality check
//    bool operator==(const Point& other) const {
//        return abs(x - other.x) < 1e-9 &&
//               abs(y - other.y) < 1e-9 &&
//               abs(z - other.z) < 1e-9;
//    }
//};
//
//// Hash function for Point (used for unordered sets/maps)
//struct PointHash {
//    size_t operator()(const Point& p) const {
//        return hash<double>()(p.x) ^ hash<double>()(p.y) ^ hash<double>()(p.z);
//    }
//};
//
//// Define an edge structure
//struct Edge {
//    Point u, v;
//    double weight;
//
//    Edge(Point u, Point v) : u(u), v(v), weight(u.distance(v)) {}
//};
//
//// Comparator for priority queue
//struct AStarComparator {
//    bool operator()(const tuple<double, double, Point, vector<Point>>& lhs,
//                    const tuple<double, double, Point, vector<Point>>& rhs) const {
//        return get<0>(lhs) > get<0>(rhs); // Compare f_cost (first element of tuple)
//    }
//};
//
//// A* algorithm implementation
//vector<Point> astar(const vector<Point>& vertices, const vector<Edge>& edges, const Point& source, const Point& target) {
//    priority_queue<tuple<double, double, Point, vector<Point>>,
//                   vector<tuple<double, double, Point, vector<Point>>>,
//                   AStarComparator>
//        pq;
//
//    unordered_set<Point, PointHash> visited;
//
//    pq.push({0, 0, source, {source}});
//
//    while (!pq.empty()) {
//        auto [f_cost, g_cost, current, path] = pq.top();
//        pq.pop();
//
//        // If this point has already been visited, skip it
//        if (visited.count(current)) continue;
//        visited.insert(current);
//
//        // If the target is reached, return the path
//        if (current == target) return path;
//
//        for (const auto& edge : edges) {
//            Point neighbor;
//            if (edge.u == current) neighbor = edge.v;
//            else if (edge.v == current) neighbor = edge.u;
//            else continue;
//
//            if (visited.count(neighbor)) continue;
//
//            // Compute costs
//            double tentative_g_cost = g_cost + edge.weight;
//            double h_cost = neighbor.distance(target);
//            double new_f_cost = tentative_g_cost + h_cost;
//
//            auto new_path = path;
//            new_path.push_back(neighbor);
//
//            pq.push({new_f_cost, tentative_g_cost, neighbor, new_path});
//        }
//    }
//
//    return {}; // Return an empty path if no path is found
//}
//
//bool segments_intersect(const Point& p1, const Point& p2, const Point& q1, const Point& q2) {
//    // Vector operations
//    auto cross = [](const Point& a, const Point& b) {
//        return Point{
//            a.y * b.z - a.z * b.y,
//            a.z * b.x - a.x * b.z,
//            a.x * b.y - a.y * b.x
//        };
//    };
//
//    auto subtract = [](const Point& a, const Point& b) {
//        return Point{a.x - b.x, a.y - b.y, a.z - b.z};
//    };
//
//    auto dot = [](const Point& a, const Point& b) {
//        return a.x * b.x + a.y * b.y + a.z * b.z;
//    };
//
//    Point d1 = subtract(p2, p1);
//    Point d2 = subtract(q2, q1);
//    Point r = subtract(q1, p1);
//
//    Point n1 = cross(d1, d2);
//    Point n2 = cross(r, d2);
//
//    if (abs(dot(n1, n1)) < 1e-9) {
//        // Segments are parallel; check for overlap
//        return false;
//    }
//
//    double t = dot(n2, n1) / dot(n1, n1);
//    Point intersection = {p1.x + t * d1.x, p1.y + t * d1.y, p1.z + t * d1.z};
//
//    // Check if the intersection point lies within both segments
//    auto is_between = [](const Point& a, const Point& b, const Point& c) {
//        return min(a.x, b.x) <= c.x && c.x <= max(a.x, b.x) &&
//               min(a.y, b.y) <= c.y && c.y <= max(a.y, b.y) &&
//               min(a.z, b.z) <= c.z && c.z <= max(a.z, b.z);
//    };
//
//    return is_between(p1, p2, intersection) && is_between(q1, q2, intersection);
//}
//
//
//int main() {
//    vector<Point> vertices_outer = {
//        {1, 1, 1}, {-1, 1, 1}, {1, -1, 1}, {-1, -1, 1},
//        {1, 1, -1}, {-1, 1, -1}, {1, -1, -1}, {-1, -1, -1},
//        {0, 0.618034, 1.61803}, {0, -0.618034, 1.61803}, {0, 0.618034, -1.61803}, {0, -0.618034, -1.61803},
//        {0.618034, 1.61803, 0}, {-0.618034, 1.61803, 0}, {0.618034, -1.61803, 0}, {-0.618034, -1.61803, 0},
//        {1.61803, 0, 0.618034}, {-1.61803, 0, 0.618034}, {1.61803, 0, -0.618034}, {-1.61803, 0, -0.618034}
//    };
//
//    vector<pair<int, int>> edge_indices = {
//        {0, 16}, {0, 8}, {0, 12}, {16, 2}, {16, 18}, {8, 1}, {8, 9}, {12, 4}, {12, 13},
//        {2, 14}, {2, 9}, {18, 4}, {18, 6}, {1, 17}, {1, 13}, {4, 10}, {13, 5},
//        {14, 6}, {14, 15}, {9, 3}, {17, 3}, {17, 19}, {5, 10}, {5, 19},
//        {6, 11}, {15, 3}, {15, 7}, {10, 11}, {19, 7}, {3, 7}, {11, 7}
//    };
//
//    vector<Edge> edges;
//    for (const auto& e : edge_indices) {
//        edges.emplace_back(vertices_outer[e.first], vertices_outer[e.second]);
//    }
//
//    Point source = {-5, -1, 1};
//    Point target = {5, 1, -1};
//
//    for (const auto& v : vertices_outer) {
//        if (!segments_intersect(source, v, target, v)) {
//            edges.emplace_back(source, v);
//            edges.emplace_back(target, v);
//        }
//    }
//
//    vector<Point> path = astar(vertices_outer, edges, source, target);
//
//    if (!path.empty()) {
//        cout << "Shortest path found:\n";
//        for (const auto& p : path) {
//            cout << "(" << p.x << ", " << p.y << ", " << p.z << ")\n";
//        }
//    } else {
//        cout << "No path found.\n";
//    }
//
//    return 0;
//}










//#include <iostream>
//#include <vector>
//#include <cmath>
//#include <queue>
//#include <tuple>
//#include <algorithm>
//#include <limits>
//#include <unordered_set>
//#include <iomanip>
//
//using namespace std;
//
//// Define a 3D point structure
//struct Point {
//    double x, y, z;
//
//    // Compute Euclidean distance between two points
//    double distance(const Point& other) const {
//        return sqrt((x - other.x) * (x - other.x) +
//                    (y - other.y) * (y - other.y) +
//                    (z - other.z) * (z - other.z));
//    }
//
//    // Operator for equality check
//    bool operator==(const Point& other) const {
//        return abs(x - other.x) < 1e-9 &&
//               abs(y - other.y) < 1e-9 &&
//               abs(z - other.z) < 1e-9;
//    }
//};
//
//// Hash function for Point (used for unordered sets/maps)
//struct PointHash {
//    size_t operator()(const Point& p) const {
//        return hash<double>()(p.x) ^ hash<double>()(p.y) ^ hash<double>()(p.z);
//    }
//};
//
//// Define an edge structure
//struct Edge {
//    Point u, v;
//    double weight;
//
//    Edge(Point u, Point v) : u(u), v(v), weight(u.distance(v)) {}
//};
//
//// Comparator for priority queue
//struct AStarComparator {
//    bool operator()(const tuple<double, double, Point, vector<Point>>& lhs,
//                    const tuple<double, double, Point, vector<Point>>& rhs) const {
//        return get<0>(lhs) > get<0>(rhs); // Compare f_cost (first element of tuple)
//    }
//};
//
//// A* algorithm implementation
//vector<Point> astar(const vector<Point>& vertices, const vector<Edge>& edges, const Point& source, const Point& target) {
//    Point intermediate = {-1.0, 1.0, -1.0};
//
//    // First find path to intermediate
//    priority_queue<tuple<double, double, Point, vector<Point>>,
//                   vector<tuple<double, double, Point, vector<Point>>>,
//                   AStarComparator>
//        pq;
//
//    unordered_set<Point, PointHash> visited;
//
//    pq.push({0, 0, source, {source}});
//
//    vector<Point> first_path;
//    while (!pq.empty()) {
//        auto [f_cost, g_cost, current, path] = pq.top();
//        pq.pop();
//
//        if (visited.count(current)) continue;
//        visited.insert(current);
//
//        if (current == intermediate) {
//            first_path = path;
//            break;
//        }
//
//        for (const auto& edge : edges) {
//            Point neighbor;
//            if (edge.u == current) neighbor = edge.v;
//            else if (edge.v == current) neighbor = edge.u;
//            else continue;
//
//            if (visited.count(neighbor)) continue;
//
//            double tentative_g_cost = g_cost + edge.weight;
//            double h_cost = neighbor.distance(intermediate);
//            double new_f_cost = tentative_g_cost + h_cost;
//
//            auto new_path = path;
//            new_path.push_back(neighbor);
//
//            pq.push({new_f_cost, tentative_g_cost, neighbor, new_path});
//        }
//    }
//
//    // Then find path from intermediate to target
//    while (!pq.empty()) pq.pop();
//    visited.clear();
//
//    pq.push({0, 0, intermediate, first_path});
//
//    while (!pq.empty()) {
//        auto [f_cost, g_cost, current, path] = pq.top();
//        pq.pop();
//
//        if (visited.count(current)) continue;
//        visited.insert(current);
//
//        if (current == target) {
//            return path;
//        }
//
//        for (const auto& edge : edges) {
//            Point neighbor;
//            if (edge.u == current) neighbor = edge.v;
//            else if (edge.v == current) neighbor = edge.u;
//            else continue;
//
//            if (visited.count(neighbor)) continue;
//
//            double tentative_g_cost = g_cost + edge.weight;
//            double h_cost = neighbor.distance(target);
//            double new_f_cost = tentative_g_cost + h_cost;
//
//            auto new_path = path;
//            new_path.push_back(neighbor);
//
//            pq.push({new_f_cost, tentative_g_cost, neighbor, new_path});
//        }
//    }
//
//    return {}; // Return an empty path if no path is found
//}
//
//int main() {
//    vector<Point> vertices_outer = {
//        {1, 1, 1}, {-1, 1, 1}, {1, -1, 1}, {-1, -1, 1},
//        {1, 1, -1}, {-1, 1, -1}, {1, -1, -1}, {-1, -1, -1},
//        {0, 0.618034, 1.61803}, {0, -0.618034, 1.61803}, {0, 0.618034, -1.61803}, {0, -0.618034, -1.61803},
//        {0.618034, 1.61803, 0}, {-0.618034, 1.61803, 0}, {0.618034, -1.61803, 0}, {-0.618034, -1.61803, 0},
//        {1.61803, 0, 0.618034}, {-1.61803, 0, 0.618034}, {1.61803, 0, -0.618034}, {-1.61803, 0, -0.618034}
//    };
//
//    vector<pair<int, int>> edge_indices = {
//        {0, 16}, {0, 8}, {0, 12}, {16, 2}, {16, 18}, {8, 1}, {8, 9}, {12, 4}, {12, 13},
//        {2, 14}, {2, 9}, {18, 4}, {18, 6}, {1, 17}, {1, 13}, {4, 10}, {13, 5},
//        {14, 6}, {14, 15}, {9, 3}, {17, 3}, {17, 19}, {5, 10}, {5, 19},
//        {6, 11}, {15, 3}, {15, 7}, {10, 11}, {19, 7}, {3, 7}, {11, 7}
//    };
//
//    vector<Edge> edges;
//    for (const auto& e : edge_indices) {
//        edges.emplace_back(vertices_outer[e.first], vertices_outer[e.second]);
//    }
//
//    Point source = {-5, -1, 1};
//    Point target = {5, 1, -1};
//
//    vector<Point> path = astar(vertices_outer, edges, source, target);
//
//    if (!path.empty()) {
//        cout << "Shortest path found:\n";
//        for (const auto& p : path) {
//            cout << "(" << p.x << ", " << p.y << ", " << p.z << ")\n";
//        }
//    } else {
//        cout << "No path found.\n";
//    }
//
//    return 0;
//}


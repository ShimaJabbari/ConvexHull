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
#include <geos_c.h>
#include <chrono>  // Include chrono for time measurement

// Cube vertices
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

// Source and end points
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

// Create a global GEOS context
GEOSContextHandle_t geos_ctx = nullptr;

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

// Use GEOS to check intersection
bool segments_intersect_no_touches_geos(const Point &A, const Point &B, const Point &C, const Point &D) {
    // Create line segment for AB
    GEOSCoordSequence* seq1 = GEOSCoordSeq_create_r(geos_ctx, 2, 2);
    GEOSCoordSeq_setXY_r(geos_ctx, seq1, 0, A.x, A.y);
    GEOSCoordSeq_setXY_r(geos_ctx, seq1, 1, B.x, B.y);
    GEOSGeometry* line1 = GEOSGeom_createLineString_r(geos_ctx, seq1);

    // Create line segment for CD
    GEOSCoordSequence* seq2 = GEOSCoordSeq_create_r(geos_ctx, 2, 2);
    GEOSCoordSeq_setXY_r(geos_ctx, seq2, 0, C.x, C.y);
    GEOSCoordSeq_setXY_r(geos_ctx, seq2, 1, D.x, D.y);
    GEOSGeometry* line2 = GEOSGeom_createLineString_r(geos_ctx, seq2);

    char intersects = GEOSIntersects_r(geos_ctx, line1, line2);
    char touches = GEOSTouches_r(geos_ctx, line1, line2);

    bool result = false;
    if (intersects && !touches) {
        result = true;
    }

    GEOSGeom_destroy_r(geos_ctx, line1);
    GEOSGeom_destroy_r(geos_ctx, line2);

    return result;
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
            if (segments_intersect_no_touches_geos(point, vertex, ce.first, ce.second)) {
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
    // Initialize GEOS
    geos_ctx = GEOS_init_r();

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

    // Record the start time
    auto start_time = std::chrono::high_resolution_clock::now();

    // A* search
    std::vector<Point> path=astar_path(s,e);
    
    // Record the end time
    auto end_time = std::chrono::high_resolution_clock::now();
    
    // Calculate and print execution time
    std::chrono::duration<double> duration = end_time - start_time;
    std::cout << "\nExecution time: " << duration.count() << " seconds\n";
    
    if (!path.empty()) {
        std::cout<<"\nShortest path found by A* algorithm:\n[";
        for (auto &p: path) std::cout<<fmtPoint(p)<<" ";
        std::cout<<"]\n";
    } else {
        std::cout << "No path found.\n";
    }

    // Free GEOS resources
    GEOS_finish_r(geos_ctx);

    return 0;
}




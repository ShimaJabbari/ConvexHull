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

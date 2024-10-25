#include <iostream>
#include <vector>
#include <cmath>
#include <map>
#include <tuple>
#include <set>
#include <algorithm>
#include <chrono>
#include <queue>
#include <cstdlib>
#include <ctime>
#include <random>  // For normal distribution

// Define 3D vector type
typedef std::vector<double> Vec3D;
typedef std::tuple<double, double, double> Point3D;

// Graph structure with weights
typedef std::map<Point3D, std::vector<std::pair<Point3D, double>>> Graph;

// Function to calculate Euclidean distance between two 3D points
double euclideanDistance(const Vec3D& a, const Vec3D& b) {
    return sqrt(pow(b[0] - a[0], 2) + pow(b[1] - a[1], 2) + pow(b[2] - a[2], 2));
}

// Function to normalize a 3D vector
Vec3D normalize(const Vec3D& v) {
    double length = euclideanDistance(v, {0, 0, 0});
    return {v[0] / length, v[1] / length, v[2] / length};
}

// Function to subtract two 3D vectors
Vec3D subtract(const Vec3D& a, const Vec3D& b) {
    return {a[0] - b[0], a[1] - b[1], a[2] - b[2]};
}

// Function to scale a 3D vector
Vec3D scale(const Vec3D& v, double factor) {
    return {v[0] * factor, v[1] * factor, v[2] * factor};
}

// Add edge to graph with weight
void addEdge(Graph& graph, const Point3D& u, const Point3D& v, double weight) {
    graph[u].emplace_back(v, weight);
    graph[v].emplace_back(u, weight);
}

// Cross product of two 3D vectors
Vec3D cross(const Vec3D& a, const Vec3D& b) {
    return {
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0]
    };
}

// Check if two line segments intersect and log results
bool segmentsIntersect(const Vec3D& a1, const Vec3D& a2, const Vec3D& b1, const Vec3D& b2) {
    auto cross_product = [](const Vec3D& v1, const Vec3D& v2) {
        return cross(v1, v2);
    };

    Vec3D d1 = subtract(a2, a1);
    Vec3D d2 = subtract(b2, b1);

    double det = d1[0] * d2[1] - d1[1] * d2[0];
    if (std::abs(det) < 1e-9) {
        // Parallel lines
        return false;
    }
    
    double t = ((b1[0] - a1[0]) * d2[1] - (b1[1] - a1[1]) * d2[0]) / det;
    double u = ((b1[0] - a1[0]) * d1[1] - (b1[1] - a1[1]) * d1[0]) / det;
    
    bool intersect = t >= 0 && t <= 1 && u >= 0 && u <= 1;

    // Log result
    if (intersect) {
        std::cout << "Intersection found between edges: ("
                  << a1[0] << ", " << a1[1] << ", " << a1[2] << ") -> ("
                  << a2[0] << ", " << a2[1] << ", " << a2[2] << ") and ("
                  << b1[0] << ", " << b1[1] << ", " << b1[2] << ") -> ("
                  << b2[0] << ", " << b2[1] << ", " << b2[2] << ")\n";
    }
    
    return intersect;
}

// A* pathfinding algorithm
std::vector<Point3D> aStar(const Graph& graph, const Point3D& start, const Point3D& goal) {
    std::map<Point3D, double> gScore;
    std::map<Point3D, double> fScore;
    std::map<Point3D, Point3D> cameFrom;
    std::set<Point3D> visited;

    auto heuristic = [](const Point3D& a, const Point3D& b) {
        return sqrt(pow(std::get<0>(b) - std::get<0>(a), 2) +
                    pow(std::get<1>(b) - std::get<1>(a), 2) +
                    pow(std::get<2>(b) - std::get<2>(a), 2));
    };

    auto cmp = [&](const Point3D& a, const Point3D& b) {
        return fScore[a] > fScore[b];
    };

    std::priority_queue<Point3D, std::vector<Point3D>, decltype(cmp)> openSet(cmp);
    
    gScore[start] = 0;
    fScore[start] = heuristic(start, goal);
    openSet.push(start);

    while (!openSet.empty()) {
        Point3D current = openSet.top();
        openSet.pop();

        if (current == goal) {
            // Reconstruct the path
            std::vector<Point3D> path;
            while (current != start) {
                path.push_back(current);
                current = cameFrom[current];
            }
            path.push_back(start);
            std::reverse(path.begin(), path.end());
            return path;
        }

        visited.insert(current);

        for (const auto& neighbor : graph.at(current)) {
            const Point3D& next = neighbor.first;
            double weight = neighbor.second;

            if (visited.find(next) != visited.end()) {
                continue;
            }

            double tentative_gScore = gScore[current] + weight;

            if (gScore.find(next) == gScore.end() || tentative_gScore < gScore[next]) {
                cameFrom[next] = current;
                gScore[next] = tentative_gScore;
                fScore[next] = tentative_gScore + heuristic(next, goal);

                openSet.push(next);
            }
        }
    }

    return {}; // No path found
}

// Function to generate random points inside the inner dodecahedron with Gaussian distribution
void generateRandomPointsInsideDodecahedron(Graph& graph, const std::vector<Vec3D>& vertices_inner, int numPoints) {
    std::default_random_engine generator;
    std::normal_distribution<double> distribution(0.0, 1.0);  // Mean 0, Std deviation 1

    Vec3D center = {0, 0, 0};  // Calculate the center of the inner dodecahedron
    for (const auto& v : vertices_inner) {
        center[0] += v[0];
        center[1] += v[1];
        center[2] += v[2];
    }
    center[0] /= vertices_inner.size();
    center[1] /= vertices_inner.size();
    center[2] /= vertices_inner.size();

    // Calculate the radius of the inner dodecahedron
    double inner_radius = 0;
    for (const auto& v : vertices_inner) {
        double dist = euclideanDistance(v, center);
        if (dist > inner_radius) inner_radius = dist;
    }

    for (int i = 0; i < numPoints; ++i) {
        Vec3D randomPoint;
        do {
            randomPoint = {
                center[0] + distribution(generator) * inner_radius / 3,  // Gaussian distribution
                center[1] + distribution(generator) * inner_radius / 3,
                center[2] + distribution(generator) * inner_radius / 3
            };
        } while (euclideanDistance(randomPoint, center) > inner_radius);

        graph[std::make_tuple(randomPoint[0], randomPoint[1], randomPoint[2])] = {};
    }
}

// Function to add edges without intersection from the source/end to the dodecahedron vertices
void addEdgesWithoutIntersection(Graph& graph, const Vec3D& point, const std::vector<Vec3D>& vertices, const std::vector<std::pair<int, int>>& dodecahedronEdges) {
    for (const auto& vertex : vertices) {
        bool intersects = false;
        for (const auto& edge : dodecahedronEdges) {
            if (segmentsIntersect(point, vertex, vertices[edge.first], vertices[edge.second])) {
                intersects = true;
                break;
            }
        }
        if (!intersects) {
            double weight = euclideanDistance(point, vertex);
            addEdge(graph, std::make_tuple(point[0], point[1], point[2]), std::make_tuple(vertex[0], vertex[1], vertex[2]), weight);
        }
    }
}

// Function to add points slightly inside the inner dodecahedron vertices
void addPointsInsideInnerDodecahedron(Graph& graph, const std::vector<Vec3D>& vertices_inner, double distance_inside) {
    for (const auto& vertex : vertices_inner) {
        Vec3D direction_to_center = subtract({0, 0, 0}, vertex);  // Assuming the center is at {0, 0, 0}
        Vec3D direction_normalized = normalize(direction_to_center);
        Vec3D new_point = {
            vertex[0] + distance_inside * direction_normalized[0],
            vertex[1] + distance_inside * direction_normalized[1],
            vertex[2] + distance_inside * direction_normalized[2]
        };
        graph[std::make_tuple(new_point[0], new_point[1], new_point[2])] = {};
    }
}

int main() {
    // Start time measurement
    auto start = std::chrono::high_resolution_clock::now();

    // Define the golden ratio
    const double phi = (1 + sqrt(5)) / 2;

    // Define vertices of the outer dodecahedron
    std::vector<Vec3D> vertices_outer = {
        {1, 1, 1}, {-1, 1, 1}, {1, -1, 1}, {-1, -1, 1},
        {1, 1, -1}, {-1, 1, -1}, {1, -1, -1}, {-1, -1, -1},
        {0, 1 / phi, phi}, {0, -1 / phi, phi}, {0, 1 / phi, -phi}, {0, -1 / phi, -phi},
        {1 / phi, phi, 0}, {-1 / phi, phi, 0}, {1 / phi, -phi, 0}, {-1 / phi, -phi, 0},
        {phi, 0, 1 / phi}, {-phi, 0, 1 / phi}, {phi, 0, -1 / phi}, {-phi, 0, -1 / phi}
    };

    // Define vertices of the inner dodecahedron by scaling the outer vertices
    double scale_factor = 0.8;
    std::vector<Vec3D> vertices_inner;
    Vec3D center = {0, 0, 0};

    for (const auto& v : vertices_outer) {
        center[0] += v[0];
        center[1] += v[1];
        center[2] += v[2];
    }
    center[0] /= vertices_outer.size();
    center[1] /= vertices_outer.size();
    center[2] /= vertices_outer.size();

    for (const auto& v : vertices_outer) {
        Vec3D translated = subtract(v, center);
        Vec3D scaled = scale(translated, scale_factor);
        vertices_inner.push_back({scaled[0] + center[0], scaled[1] + center[1], scaled[2] + center[2]});
    }

    // Define source and end points
    Vec3D source = {-5, -1, 1};
    Vec3D end = {5, 1, -1};

    // Initialize graph
    Graph G;

    // Add dodecahedron vertices to the graph
    for (const auto& v : vertices_outer) {
        G[std::make_tuple(v[0], v[1], v[2])] = {};
    }
    for (const auto& v : vertices_inner) {
        G[std::make_tuple(v[0], v[1], v[2])] = {};
    }

    // Define the edges
    std::vector<std::pair<int, int>> edges = {
        {0, 16}, {0, 8}, {0, 12}, {16, 2}, {16, 18}, {8, 1}, {8, 9}, {12, 4}, {12, 13},
        {2, 14}, {2, 9}, {18, 4}, {18, 6}, {1, 17}, {1, 13}, {4, 10}, {13, 5},
        {14, 6}, {14, 15}, {9, 3}, {17, 3}, {17, 19}, {5, 10}, {5, 19},
        {6, 11}, {15, 3}, {15, 7}, {10, 11}, {19, 7}, {3, 7}, {11, 7}
    };

    // Add edges between vertices with Euclidean distance as the weight
    for (const auto& edge : edges) {
        Vec3D u = vertices_outer[edge.first];
        Vec3D v = vertices_outer[edge.second];
        double weight = euclideanDistance(u, v);
        addEdge(G, std::make_tuple(u[0], u[1], u[2]), std::make_tuple(v[0], v[1], v[2]), weight);
    }

    // Add source and end points to the graph
    G[std::make_tuple(source[0], source[1], source[2])] = {};
    G[std::make_tuple(end[0], end[1], end[2])] = {};

    // Add random points inside the inner dodecahedron
    generateRandomPointsInsideDodecahedron(G, vertices_inner, 200);

    // Add points slightly inside the inner dodecahedron
    addPointsInsideInnerDodecahedron(G, vertices_inner, 0.1);

    // Add edges from source and end points to the graph, avoiding intersections
    addEdgesWithoutIntersection(G, source, vertices_outer, edges);
    addEdgesWithoutIntersection(G, end, vertices_outer, edges);

    // Run A* to find the shortest path
    auto path = aStar(G, std::make_tuple(source[0], source[1], source[2]), std::make_tuple(end[0], end[1], end[2]));

    // Print the shortest path
    if (!path.empty()) {
        std::cout << "Shortest path found:\n";
        for (const auto& point : path) {
            std::cout << "(" << std::get<0>(point) << ", " << std::get<1>(point) << ", " << std::get<2>(point) << ")\n";
        }
    } else {
        std::cout << "No path found between source and end.\n";
    }

    // End time measurement
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end_time - start;
    std::cout << "Time taken to run the program: " << elapsed.count() << " seconds." << std::endl;

    return 0;
}


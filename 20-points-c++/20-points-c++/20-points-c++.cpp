#include <iostream>
#include <vector>
#include <cmath>
#include <map>
#include <tuple>
#include <set>
#include <algorithm>
#include <chrono>  // Include for time measurement

// Define 3D vector type
typedef std::vector<double> Vec3D;

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

// Create 3D point type
typedef std::tuple<double, double, double> Point3D;

// Graph structure
typedef std::map<Point3D, std::vector<Point3D>> Graph;

// Add edge to graph
void addEdge(Graph& graph, const Point3D& u, const Point3D& v) {
    graph[u].push_back(v);
    graph[v].push_back(u);
}

// Define the golden ratio
const double phi = (1 + sqrt(5)) / 2;

int main() {
    // Start time measurement
    auto start = std::chrono::high_resolution_clock::now();

    // Define vertices of the outer dodecahedron
    std::vector<Vec3D> vertices_outer = {
        {1, 1, 1}, {-1, 1, 1}, {1, -1, 1}, {-1, -1, 1},
        {1, 1, -1}, {-1, 1, -1}, {1, -1, -1}, {-1, -1, -1},
        {0, 1 / phi, phi}, {0, -1 / phi, phi}, {0, 1 / phi, -phi}, {0, -1 / phi, -phi},
        {1 / phi, phi, 0}, {-1 / phi, phi, 0}, {1 / phi, -phi, 0}, {-1 / phi, -phi, 0},
        {phi, 0, 1 / phi}, {-phi, 0, 1 / phi}, {phi, 0, -1 / phi}, {-phi, 0, -1 / phi}
    };

    // Calculate center of the dodecahedron
    Vec3D center = {0, 0, 0};
    for (const auto& v : vertices_outer) {
        center[0] += v[0];
        center[1] += v[1];
        center[2] += v[2];
    }
    center[0] /= vertices_outer.size();
    center[1] /= vertices_outer.size();
    center[2] /= vertices_outer.size();

    // Create inner dodecahedron by scaling the outer vertices
    double scale_factor = 0.8;
    std::vector<Vec3D> vertices_inner;
    for (const auto& v : vertices_outer) {
        Vec3D translated = subtract(v, center);
        Vec3D scaled = scale(translated, scale_factor);
        vertices_inner.push_back({scaled[0] + center[0], scaled[1] + center[1], scaled[2] + center[2]});
    }

    // Define the edges
    std::vector<std::pair<int, int>> edges = {
        {0, 16}, {0, 8}, {0, 12}, {16, 2}, {16, 18}, {8, 1}, {8, 9}, {12, 4}, {12, 13},
        {2, 14}, {2, 9}, {18, 4}, {18, 6}, {1, 17}, {1, 13}, {4, 10}, {13, 5},
        {14, 6}, {14, 15}, {9, 3}, {17, 3}, {17, 19}, {5, 10}, {5, 19},
        {6, 11}, {15, 3}, {15, 7}, {10, 11}, {19, 7}, {3, 7}, {11, 7}
    };

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

    // Add edges between vertices
    for (const auto& edge : edges) {
        Vec3D u = vertices_outer[edge.first];
        Vec3D v = vertices_outer[edge.second];
        addEdge(G, std::make_tuple(u[0], u[1], u[2]), std::make_tuple(v[0], v[1], v[2]));
    }

    // Add source and end nodes to the graph
    G[std::make_tuple(source[0], source[1], source[2])] = {};
    G[std::make_tuple(end[0], end[1], end[2])] = {};

    // Add logic to compute paths, avoid intersections, etc...
    // You can implement A* or another algorithm here without relying on external libraries.

    std::cout << "Graph construction completed!" << std::endl;

    // End time measurement
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end_time - start;
    std::cout << "Time taken to run the program: " << elapsed.count() << " seconds." << std::endl;

    return 0;
}



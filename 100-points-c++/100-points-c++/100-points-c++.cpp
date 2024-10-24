#include <iostream>
#include <vector>
#include <cmath>
#include <map>
#include <tuple>
#include <set>
#include <random>
#include <algorithm>
#include <fstream>
#include <chrono>

// Define 3D vector type
typedef std::vector<double> Vec3D;
typedef std::tuple<double, double, double> Point3D;
typedef std::map<Point3D, std::vector<Point3D>> Graph;

// Function to calculate Euclidean distance between two 3D points
double euclideanDistance(const Vec3D& a, const Vec3D& b) {
    return sqrt(pow(b[0] - a[0], 2) + pow(b[1] - a[1], 2) + pow(b[2] - a[2], 2));
}

// Function to subtract two 3D vectors
Vec3D subtract(const Vec3D& a, const Vec3D& b) {
    return {a[0] - b[0], a[1] - b[1], a[2] - b[2]};
}

// Function to scale a 3D vector
Vec3D scale(const Vec3D& v, double factor) {
    return {v[0] * factor, v[1] * factor, v[2] * factor};
}

// Add edge to graph
void addEdge(Graph& graph, const Point3D& u, const Point3D& v, double weight) {
    graph[u].push_back(v);
    graph[v].push_back(u);
}

// Function to add edges between polytope vertices within a distance threshold
void addEdgesPolytope(Graph& graph, const std::vector<Vec3D>& vertices, double max_distance) {
    int num_vertices = vertices.size();
    for (int i = 0; i < num_vertices; ++i) {
        for (int j = i + 1; j < num_vertices; ++j) {
            Vec3D u = vertices[i];
            Vec3D v = vertices[j];
            double distance = euclideanDistance(u, v);
            if (distance <= max_distance) {
                addEdge(graph, {u[0], u[1], u[2]}, {v[0], v[1], v[2]}, distance);
            }
        }
    }
}

// Function to add edges from a point to polytope vertices
void addEdgesFromPoint(Graph& graph, const Vec3D& point, const std::vector<Vec3D>& vertices, int max_connections, double max_distance) {
    std::vector<std::pair<double, Vec3D>> distances;
    for (const auto& vertex : vertices) {
        double distance = euclideanDistance(point, vertex);
        distances.push_back({distance, vertex});
    }
    
    // Sort by distance and limit the number of connections
    std::sort(distances.begin(), distances.end());
    for (int i = 0; i < std::min((int)distances.size(), max_connections); ++i) {
        if (distances[i].first <= max_distance) {
            addEdge(graph, {point[0], point[1], point[2]}, {distances[i].second[0], distances[i].second[1], distances[i].second[2]}, distances[i].first);
        }
    }
}

// Generate points on a sphere (same as Python version)
std::vector<Vec3D> generateSpherePoints(int num_points) {
    std::vector<Vec3D> vertices;
    double phi = M_PI * (3. - sqrt(5.));  // golden angle in radians
    
    for (int i = 0; i < num_points; ++i) {
        double y = 1 - (i / (double)(num_points - 1)) * 2;  // y goes from 1 to -1
        double radius = sqrt(1 - y * y);  // radius at y
        double theta = phi * i;  // golden angle increment
        
        double x = cos(theta) * radius;
        double z = sin(theta) * radius;
        vertices.push_back({x, y, z});
    }
    
    return vertices;
}

int main() {
    // Start time measurement
    auto start = std::chrono::high_resolution_clock::now();
    
    // Generate random points on a sphere for the outer polytope
    int num_points = 100;
    std::vector<Vec3D> vertices_outer = generateSpherePoints(num_points);
    
    // Scale down for the inner polytope with 0.2 distance
    double scale_factor = 0.8;
    Vec3D center_outer = {0, 0, 0};  // Simple center for this example
    std::vector<Vec3D> vertices_inner;
    for (const auto& v : vertices_outer) {
        Vec3D translated = subtract(v, center_outer);
        Vec3D scaled = scale(translated, scale_factor);
        vertices_inner.push_back({scaled[0] + center_outer[0], scaled[1] + center_outer[1], scaled[2] + center_outer[2]});
    }

    // Initialize graph
    Graph G;
    
    // Add edges for the outer and inner polytopes with a distance threshold
    addEdgesPolytope(G, vertices_outer, 0.5);
    addEdgesPolytope(G, vertices_inner, 0.5);

    // Define source and end points
    Vec3D source = {-0.8, -0.8, -0.8};
    Vec3D end = {0.8, 0.8, 0.8};
    
    // Add source and end points to the graph
    G[{source[0], source[1], source[2]}] = {};
    G[{end[0], end[1], end[2]}] = {};
    
    // Add more edges for source and end points
    addEdgesFromPoint(G, source, vertices_outer, 20, 0.5);
    addEdgesFromPoint(G, end, vertices_outer, 20, 0.5);
    
    // Generate random rock-like points within the inner polytope
    int num_rock_points = 170;
    std::vector<Vec3D> rock_points;
    std::random_device rd;
    std::mt19937 gen(rd());
    std::normal_distribution<> d(0, scale_factor / 3);
    
    while (rock_points.size() < num_rock_points) {
        Vec3D point = {d(gen), d(gen), d(gen)};
        if (point[0] >= -1 && point[0] <= 1 && point[1] >= -1 && point[1] <= 1 && point[2] >= -1 && point[2] <= 1) {
            rock_points.push_back(point);
        }
    }
    
    // Save rock points inside inner polytope to a file
    std::ofstream file("rock.txt");
    for (const auto& point : rock_points) {
        file << point[0] << ", " << point[1] << ", " << point[2] << "\n";
    }
    file.close();

    // End time measurement
    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end_time - start;
    std::cout << "Time taken to run the program: " << elapsed.count() << " seconds." << std::endl;

    return 0;
}


#include <iostream>
#include <vector>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <stdexcept>
#include <sstream>
#include <tuple>
#include <algorithm>
#include <functional>
#include <time.h>

using namespace std;
int n;
double B;
vector<tuple<int, int, double>> edgesList;

struct Node {
	int id;
	vector<pair<Node*, double>> children;
	Node* parent = nullptr;
	bool visited = false; // Mark if the node has been visited during DFS.
	Node(int _id) : id(_id) {}
};

struct PathResult {
	vector<Node*> path;
};

class Tree {
private:
	Node* root;
	double B;
	unordered_map<int, Node*> nodes;
	unordered_map<int, double> distanceFromRoot;

	// Gets the node with given id or creates a new one if it does not exist.
	Node* getOrCreate(int id) {
		if (!nodes.count(id)) {
			nodes[id] = new Node(id);
		}
		return nodes[id];
	}

	// Recursively assign the distance from the root node to each node.
	void assignDistanceFromRoot(Node* node, double currentLength, unordered_set<int>& visitedSet) {
		if (visitedSet.count(node->id))
			return;
		visitedSet.insert(node->id);
		distanceFromRoot[node->id] = currentLength;
		for (auto& childPair : node->children) {
			Node* child = childPair.first;
			double w = childPair.second;
			assignDistanceFromRoot(child, currentLength + w, visitedSet);
		}
	}

	// Return the weight of the edge connecting two nodes.
	double getEdgeWeight(Node* a, Node* b) {
		for (auto& edge : a->children) {
			if (edge.first == b)
				return edge.second;
		}
		for (auto& edge : b->children) {
			if (edge.first == a)
				return edge.second;
		}
		return 0.0;
	}

public:
	// Constructs the tree from an edge list
	Tree(const vector<tuple<int, int, double>>& edgeList, int n, double _B) : B(_B) {
		root = getOrCreate(0);
		for (const auto& edge : edgeList) {
			int from = get<0>(edge);
			int to = get<1>(edge);
			double w = get<2>(edge);
			Node* parent = getOrCreate(from);
			Node* child = getOrCreate(to);
			parent->children.emplace_back(child, w);
			child->parent = parent;
		}
		unordered_set<int> visitedSet;
		assignDistanceFromRoot(root, 0.0, visitedSet);
	}

	PathResult path_to_root(Node* target) {
		PathResult result;
		while (target) {
			result.path.push_back(target);
			target = target->parent;
		}
		return result;
	}
	void PDFS_offline() {
		vector<pair<Node*, double>> path;
		vector<int> currentRoute;
		vector<vector<int>> routes;
		vector<double> routeCosts;
		vector<double> surplusEnergy;

		double currentLength = 0.0;
		double routeEnergy = 0.0;
		double sumEnergy = 0.0;
		int routeCount = 1;
		double carriedSurplus = 0.0; // Năng lượng dồn từ tuyến trước

		vector<int> fullDFS;
		unordered_set<Node*> exploredNodes;

		path.push_back({ root, 0.0 });
		currentRoute.push_back(root->id);
		fullDFS.push_back(root->id);

		function<void(Node*, double)> exploreWithSurplus = [&](Node* currentNode, double surplus) {
			for (auto& childPair : currentNode->children) {
				Node* child = childPair.first;
				double weight = childPair.second;

				if (!child->visited && (weight * 2) <= surplus) {
					child->visited = true;
					currentRoute.push_back(child->id);
					fullDFS.push_back(child->id);
					routeEnergy += (weight * 2);
					exploreWithSurplus(child, surplus - (weight * 2));

					currentRoute.push_back(currentNode->id);
					fullDFS.push_back(currentNode->id);
				}
			}
			};

		function<void(Node*)> DFS = [&](Node* u) {
			for (auto& childPair : u->children) {
				Node* v = childPair.first;
				double w = childPair.second;

				if (!v->visited) {

					if (routeEnergy + w + (currentLength + w) > B + carriedSurplus) {

						double surplus = B + carriedSurplus - (routeEnergy + currentLength);
						if (surplus > 0) {
							exploreWithSurplus(u, surplus);
						}


						double distToRoot = currentLength;
						routeEnergy += distToRoot;

						double actualSurplus = B + carriedSurplus - routeEnergy;
						surplusEnergy.push_back(actualSurplus);
						carriedSurplus = actualSurplus;

						for (int i = (int)path.size() - 2; i >= 0; i--) {
							currentRoute.push_back(path[i].first->id);
						}
						routes.push_back(currentRoute);
						routeCosts.push_back(routeEnergy);


						routeCount++;
						currentRoute.clear();
						currentRoute.push_back(root->id);
						routeEnergy = 0.0;
						double newDist = 0.0;


						for (int i = 1; i < (int)path.size(); i++) {
							Node* parentNode = path[i - 1].first;
							Node* curNode = path[i].first;
							double wt = path[i].second;
							newDist += wt;
							routeEnergy += wt;
							sumEnergy += newDist;
							currentRoute.push_back(curNode->id);
						}
						currentLength = newDist;
					}

					v->visited = true;
					fullDFS.push_back(v->id);
					currentLength += w;
					routeEnergy += w;
					sumEnergy += currentLength;
					currentRoute.push_back(v->id);
					path.push_back({ v, w });

					DFS(v);

					fullDFS.push_back(u->id);
					path.pop_back();
					currentLength -= w;
					routeEnergy += w;
					currentRoute.push_back(u->id);
				}
			}
			};

		root->visited = true;
		DFS(root);


		if (currentRoute.size() > 1) {
			double distToRoot = currentLength;
			routeEnergy += distToRoot;

			double finalSurplus = B + carriedSurplus - routeEnergy;
			if (finalSurplus > 0) {
				exploreWithSurplus(root, finalSurplus);
			}

			surplusEnergy.push_back(finalSurplus);
			carriedSurplus = finalSurplus;

			for (int i = (int)path.size() - 2; i >= 0; i--) {
				currentRoute.push_back(path[i].first->id);
			}
			routes.push_back(currentRoute);
			routeCosts.push_back(routeEnergy);
		}
		// Print the full DFS traversal order
		for (int id : fullDFS) {
			cout << id << " ";
		}
		cout << endl;

		for (int i = 0; i < routes.size(); i++) {
			cout << "Route " << (i + 1) << " (cost = " << routeCosts[i]
				<< ", surplus = " << surplusEnergy[i] << "): ";
			for (int j = 0; j < routes[i].size(); j++) {
				cout << routes[i][j];
				if (j < routes[i].size() - 1)
					cout << " ";
			}
			cout << endl;
		}
	}

	~Tree() {
		for (auto& pair : nodes) {
			delete pair.second;
		}
		nodes.clear();
	}
};


vector<tuple<int, int, double>> readEdgeList() {
	for (int i = 0; i < n - 1; i++) {
		int from, to;
		double w;
		cin >> from >> to >> w;
		edgesList.emplace_back(from, to, w);
	}
	return edgesList;
}

int main() {
	try {
		cin >> n >> B;
		readEdgeList();

		Tree tree(edgesList, n, B);
		clock_t begin = clock();
		tree.PDFS_offline();
		clock_t end = clock(); //ghi lại thời gian lúc sau
		cout << "Time run: " << (float)(end - begin) / CLOCKS_PER_SEC << " s" << endl;
	}
	catch (const exception& e) {
		cerr << "Error: " << e.what() << endl;

	}
	return 0;
}


/*
Từ bài báo:
Input:
7 20
0 1 1
0 6 2
1 2 8
1 3 4
3 4 3
3 5 3
Output:
0 1 2 1 3 4 3 5 3 1 0 6 0
Route 1 (cost = 18): 0 1 2 1 0
Route 2 (cost = 16): 0 1 3 4 3 1 0
Route 3 (cost = 20): 0 1 3 5 3 1 0 6 0

Tự cho:
Input
11 32
0 1 2
0 8 10
1 2 3
1 3 4
2 4 3
2 5 2
3 6 8
3 7 9
8 9 1
8 10 5
Output:
0 1 2 4 2 5 2 1 3 6 3 7 3 1 0 8 9 8 10 8 0
Route 1 (cost = 28): 0 1 2 4 2 5 2 1 3 1 0
Route 2 (cost = 28): 0 1 3 6 3 1 0
Route 3 (cost = 30): 0 1 3 7 3 1 0
Route 4 (cost = 32): 0 8 9 8 10 8 0

Input:
10 26
0 1 2
0 2 3
1 3 4
1 4 1
2 5 5
2 6 1
5 7 2
5 8 2
8 9 3
Output:
0 1 3 1 4 1 0 2 5 7 5 8 9 8 5 2 6 2 0
Route 1 (cost = 20): 0 1 3 1 4 1 0 2 0
Route 2 (cost = 24): 0 2 5 7 5 8 5 2 0
Route 3 (cost = 26): 0 2 5 8 9 8 5 2 0
Route 4 (cost = 8): 0 2 6 2 0

Tự cho :
Input:
24 100
0 1 1
0 2 2
1 3 3
1 4 4
1 5 5
2 6 6
2 7 7
3 8 8
3 9 9
4 10 10
4 11 11
5 12 12
6 13 13
6 14 14
7 15 15
7 16 16
9 17 17
11 18 18
12 19 19
12 20 20
14 21 21
14 22 22
22 23 6

Output:
0 1 3 8 3 9 17 9 3 1 4 10 4 11 18 11 4 1 5 12 19 12 20 12 5 1 0 2 6 13 6 14 21 14 22 23 22 14 6 2 7 15 7 16 7 2 0
Route 1 (cost = 84): 0 1 3 8 3 9 17 9 3 1 4 1 0
Route 2 (cost = 98): 0 1 4 10 4 11 18 11 4 1 5 1 0
Route 3 (cost = 74): 0 1 5 12 19 12 5 1 0
Route 4 (cost = 92): 0 1 5 12 20 12 5 1 0 2 6 2 0
Route 5 (cost = 70): 0 2 6 13 6 14 6 2 0
Route 6 (cost = 86): 0 2 6 14 21 14 6 2 0
Route 7 (cost = 100): 0 2 6 14 22 23 22 14 6 2 0
Route 8 (cost = 80): 0 2 7 15 7 16 7 2 0

Input:
41 100
0 1 1
0 23 1
1 2 1
2 3 1
2 19 1
19 20 1
20 21 1
21 22 1
3 4 1
4 5 1
5 6 1
6 7 1
7 8 1
7 13 1
13 14 1
13 17 1
17 18 1
14 15 1
15 16 1
8 9 1
9 10 1
10 11 1
11 12 1
23 25 1
25 26 1
26 27 1
26 29 1
27 28 1
23 24 1
24 30 1
30 31 1
31 32 1
32 33 1
33 34 1
34 35 1
35 36 1
36 37 1
37 38 1
38 39 1
39 40 1

0 1 2 3 4 5 6 7 8 9 10 11 12 11 10 9 8 7 13 14 15 16 15 14 13 17 18
17 13 7 6 5 4 3 2 19 20 21 22 21 20 19 2 1 0 23 25 26 27 28 27 26 29 26 25
23 24 30 31 32 33 34 35 36 37 38 39 40 39 38 37 36 35 34 33 32 31 30 24 23 0
Route 1 (cost = 30): 0 1 2 3 4 5 6 7 8 9 10 11 12 11 10 9 8 7 13 14 15 14 13 7 6 5 4 3 2 1 0
Route 2 (cost = 30): 0 1 2 3 4 5 6 7 13 14 15 16 15 14 13 17 18 17 13 7 6 5 4 3 2 19 20 19 2 1 0
Route 3 (cost = 30): 0 1 2 19 20 21 22 21 20 19 2 1 0 23 25 26 27 28 27 26 29 26 25 23 24 30 31 30 24 23 0
Route 4 (cost = 26): 0 23 24 30 31 32 33 34 35 36 37 38 39 40 39 38 37 36 35 34 33 32 31 30 24 23 0

41 40
0 1 1
0 23 1
1 2 1
2 3 1
2 19 1
19 20 1
20 21 1
21 22 1
3 4 1
4 5 1
5 6 1
6 7 1
7 8 1
7 13 1
13 14 1
13 17 1
17 18 1
14 15 1
15 16 1
8 9 1
9 10 1
10 11 1
11 12 1
23 25 1
25 26 1
26 27 1
26 29 1
27 28 1
23 24 1
24 30 1
30 31 1
31 32 1
32 33 1
33 34 1
34 35 1
35 36 1
36 37 1
37 38 1
38 39 1
39 40 1

0 1 2 3 4 5 6 7 8 9 10 11 12 11 10 9 8 7 13 14 15 16 15 14 13 17 18 17 13
7 6 5 4 3 2 19 20 21 22 21 20 19 2 1 0 23 25 26 27 28 27 26 29 26 25 23 24 30
31 32 33 34 35 36 37 38 39 40 39 38 37 36 35 34 33 32 31 30 24 23 0
Route 1 (cost = 40): 0 1 2 3 4 5 6 7 8 9 10 11 12 11 10 9 8 7 13 14 15 16 15 14 13 17 18 17 13 7 6 5 4 3 2 19 20 19 2 1 0
Route 2 (cost = 40): 0 1 2 3 4 5 6 7 13 14 15 16 15 14 13 17 18 17 13 7 6 5 4 3 2 19 20 19 2 1 0
Route 3 (cost = 26): 0 23 24 30 31 32 33 34 35 36 37 38 39 40 39 38 37 36 35 34 33 32 31 30 24 23 0

11 24
0 1 3
0 3 1
1 2 1
1 4 5
2 7 4
2 8 7
3 5 6
3 6 1
5 9 1
5 10 5

0 1 2 7 2 8 2 1 4 1 0 3 5 9 5 10 5 3 6 3 0
Route 1 (cost = 16): 0 1 2 7 2 1 0
Route 2 (cost = 22): 0 1 2 8 2 1 0
Route 3 (cost = 18): 0 1 4 1 0 3 0
Route 4 (cost = 16): 0 3 5 9 5 3 0
Route 5 (cost = 24): 0 3 5 10 5 3 0
Route 6 (cost = 4): 0 3 6 3 0

13 86
0 1 1
1 2 9
1 6 8
2 3 10
3 4 11
4 5 12
0 7 2
7 8 7
0 9 3
9 10 6
0 11 4
11 12 5
0 1 2 3 4 5 4 3 2 1 6 1 0 7 8 7 0 9 10 9 0 11 12 11 0
Route 1 (cost = 86): 0 1 2 3 4 5 4 3 2 1 0
Route 2 (cost = 72): 0 1 6 1 0 7 8 7 0 9 10 9 0 11 12 11 0

*/
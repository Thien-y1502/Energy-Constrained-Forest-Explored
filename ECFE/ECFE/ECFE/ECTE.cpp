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

int numTrees; // Số lượng cây trong rừng
double B;
vector<tuple<int, int, double>> edgesList;

struct Node {
	int id;
	vector<pair<Node*, double>> children;
	Node* parent = nullptr;
	bool visited = false; // Đánh dấu đỉnh đã được duyệt trong DFS.
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

	Node* getOrCreate(int id) {
		if (!nodes.count(id)) {
			nodes[id] = new Node(id);
		}
		return nodes[id];
	}

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

	// Hàm tìm các gốc thực của các cây trong rừng
	vector<int> findRoots(const vector<tuple<int, int, double>>& edgeList) {
		unordered_set<int> allNodes, childNodes;
		for (const auto& edge : edgeList) {
			int from = get<0>(edge);
			int to = get<1>(edge);
			allNodes.insert(from);
			allNodes.insert(to);
			childNodes.insert(to);
		}
		vector<int> roots;
		for (int id : allNodes) {
			if (!childNodes.count(id)) {
				roots.push_back(id);
			}
		}
		return roots;
	}


public:
	// Constructor xử lý nhiều cây bằng cách tạo một gốc ảo (-1)
	Tree(const vector<tuple<int, int, double>>& edgeList, double _B) : B(_B) {
		for (const auto& edge : edgeList) {
			int from = get<0>(edge);
			int to = get<1>(edge);
			double w = get<2>(edge);
			Node* parent = getOrCreate(from);
			Node* child = getOrCreate(to);
			parent->children.emplace_back(child, w);
			child->parent = parent;
		}

		vector<int> roots = findRoots(edgeList);
		root = getOrCreate(-1); // Gốc ảo
		for (int realRoot : roots) {
			Node* ch = getOrCreate(realRoot);
			root->children.emplace_back(ch, 0.0); // Nối các gốc thật vào gốc ảo với trọng số 0
			ch->parent = root;
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
		double carriedSurplus = 0.0;
		int routeCount = 1;

		vector<int> fullDFS;

		path.push_back({ root, 0.0 });
		currentRoute.push_back(root->id);
		fullDFS.push_back(root->id);

		function<void(Node*, double)> exploreWithSurplus =
			[&](Node* currentNode, double surplus) {

			for (auto& childPair : currentNode->children) {
				Node* child = childPair.first;
				double weight = childPair.second;

				// Chỉ duyệt nếu đỉnh chưa được thăm và có đủ năng lượng dư thừa
				if (!child->visited && (weight * 2) <= surplus) {
					child->visited = true; // Đánh dấu đã thăm
					currentRoute.push_back(child->id);
					fullDFS.push_back(child->id);

					// Năng lượng để đi và về từ đỉnh con
					double usedEnergy = weight * 2;
					routeEnergy += usedEnergy;

					// Đệ quy để khám phá sâu hơn từ đỉnh con
					exploreWithSurplus(child, surplus - usedEnergy);

					currentRoute.push_back(currentNode->id);
					fullDFS.push_back(currentNode->id);
				}
			}
			};

		function<void(Node*)> DFS = [&](Node* u) {

			for (auto& childPair : u->children) {
				Node* v = childPair.first;
				double w = childPair.second;

				if (v->visited) continue; // Bỏ qua nếu đã duyệt

				// Kiểm tra nếu ngân sách không đủ để đi tới v và quay về gốc
				if (routeEnergy + w + (currentLength + w) > B + carriedSurplus) {

					// Tính toán năng lượng dư thừa có thể dùng
					double surplus = B + carriedSurplus - (routeEnergy + currentLength);
					if (surplus > 0) {
						exploreWithSurplus(u, surplus);
					}

					// Hoàn thành tuyến đường hiện tại
					double distToRoot = currentLength;
					routeEnergy += distToRoot;

					double actualSurplus = B + carriedSurplus - routeEnergy;
					surplusEnergy.push_back(actualSurplus);
					carriedSurplus = actualSurplus; // Chuyển năng lượng dư thừa cho tuyến sau

					// Thêm đường về gốc vào tuyến đường
					for (int i = (int)path.size() - 2; i >= 0; i--) {
						currentRoute.push_back(path[i].first->id);
					}
					routes.push_back(currentRoute);
					routeCosts.push_back(routeEnergy);

					// Bắt đầu một tuyến đường mới
					routeCount++;
					currentRoute.clear();
					currentRoute.push_back(root->id); // Bắt đầu từ gốc ảo
					routeEnergy = 0.0;

					// Xây dựng lại đường đi từ gốc ảo đến vị trí hiện tại cho tuyến mới
					double newDist = 0.0;
					for (int i = 1; i < (int)path.size(); i++) {
						double wt = path[i].second;
						newDist += wt;
						routeEnergy += wt;
						currentRoute.push_back(path[i].first->id);
					}
					currentLength = newDist;
				}

				// Tiếp tục di chuyển đến đỉnh v
				v->visited = true;
				fullDFS.push_back(v->id);
				currentLength += w;
				routeEnergy += w;
				currentRoute.push_back(v->id);
				path.push_back({ v, w });

				DFS(v); // Đệ quy

				// Backtrack
				fullDFS.push_back(u->id);
				path.pop_back();
				currentLength -= w;
				routeEnergy += w; // Năng lượng quay về u
				currentRoute.push_back(u->id);
			}
			};

		root->visited = true;
		DFS(root);

		// Xử lý tuyến đường cuối cùng
		if (currentRoute.size() > 1) {
			double distToRoot = currentLength;

			// Tận dụng năng lượng dư thừa lần cuối
			double surplus = B + carriedSurplus - (routeEnergy + currentLength);
			if (surplus > 0) {
				Node* lastNode = path.back().first;
				exploreWithSurplus(lastNode, surplus);
			}

			routeEnergy += distToRoot;
			double finalSurplus = B + carriedSurplus - routeEnergy;
			surplusEnergy.push_back(finalSurplus);

			for (int i = (int)path.size() - 2; i >= 0; i--) {
				currentRoute.push_back(path[i].first->id);
			}
			routes.push_back(currentRoute);
			routeCosts.push_back(routeEnergy);
		}

		// In kết quả
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
	edgesList.clear();
	int totalNodes = 0;
	for (int t = 0; t < numTrees; t++) {
		int nodesInTree;
		cin >> nodesInTree;
		if (t == 0) totalNodes = nodesInTree;
		else totalNodes += nodesInTree - 1;
		for (int i = 0; i < nodesInTree - 1; i++) {
			int from, to;
			double w;
			cin >> from >> to >> w;
			edgesList.emplace_back(from, to, w);
		}
	}
	return edgesList;
}

int main() {
	ios::sync_with_stdio(false);
	cin.tie(nullptr);
	try {
		cin >> numTrees >> B;
		readEdgeList();

		
		Tree tree(edgesList, B);
		clock_t begin = clock();
		tree.PDFS_offline();
		clock_t end = clock();
		cout << "Time run: " << (double)(end - begin) / CLOCKS_PER_SEC << " s" << endl;
	}
	catch (const exception& e) {
		cerr << "Error: " << e.what() << endl;
	}
	return 0;
}
/*
Route 1 (cost = 22, surplus = 4): -1 0 1 3 1 4 1 0 2 6 2 0 -1
Route 2 (cost = 30, surplus = 0): -1 0 2 5 7 5 8 9 8 5 2 0 -1 10 -1
Route 3 (cost = 16, surplus = 10): -1 10 11 12 17 12 11 10 -1
Route 4 (cost = 36, surplus = 0): -1 10 11 12 18 12 11 14 11 10 13 16 13 10 -1
Route 5 (cost = 26, surplus = 0): -1 10 13 15 19 15 20 15 13 10 -1
-1 0 1 3 1 4 1 0 2 6 2 5 7 5 8 9 8 5 2 0 -1 10 11 12 17 12 18 12 11 14 11 10 13 16 13 15 19 15 20 15 13 10 -1
*/


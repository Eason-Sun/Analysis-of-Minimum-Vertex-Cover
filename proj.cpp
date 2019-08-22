#include <minisat/core/Solver.h>
#include "minisat/mtl/Vec.h"
#include <iostream>
#include <vector>
#include <sstream>
#include <string>
#include <algorithm>
#include <set>
#include <pthread.h>
#include <errno.h>

using namespace std;
using edge = pair<int, int>;

pair<bool, string> printVertexCover(vector<edge>&, int, int);
void inputParser(string);
bool isRemoved(char);
int findHighestDegreeVertex(vector<edge>&);
void* APPROX_VC_1(void*);
void* APPROX_VC_2(void*);
void* CNF_SAT_VC(void*);
void* ioOperation(void*);

vector<string> outputStrVec;
vector<edge> edges;
set<int> vertices;
int maxVertexId = -1;
pthread_mutex_t cout_mutex = PTHREAD_MUTEX_INITIALIZER;

int main() {
    pthread_t io;
    pthread_create(&io, NULL, &ioOperation, NULL);
    pthread_join(io, NULL);
}

pair<bool, string> printVertexCover(vector<edge>& E_, int V, int k) {
    using Minisat::Var;
    using Minisat::Lit;
    using Minisat::mkLit;
    using Minisat::lbool;
    using Minisat::l_True;
    using Minisat::vec;
    Var arr[V][k];
    Minisat::Solver solver;
    string output = "";
    // Create variables
    for (int i = 0; i < V; i++) {
        for (int j = 0; j < k; j++) {
            arr[i][j] = solver.newVar();
        }
    }
    // Create the clauses
    for (int j = 0; j < k; j++) {
        vec<Lit> v;
        for (int i = 0; i < V; i++) {
            Lit l = mkLit(arr[i][j]);
            const Lit& l_ = l;
            v.push(l_);
        }
        const vec<Lit>& v_ = v;
        solver.addClause(v_);
    }
    for (int i = 0; i < V; i++) {
        for (int p = 0; p < k; p++) {
            for (int q = p + 1; q < k; q++) {
                solver.addClause(~mkLit(arr[i][p]), ~mkLit(arr[i][q]));
            }
        }
    }
    for (int j = 0; j < k; j++) {
        for (int p = 0; p < V; p++) {
            for (int q = p + 1; q < V; q++) {
                solver.addClause(~mkLit(arr[p][j]), ~mkLit(arr[q][j]));
            }
        }
    }
    for (auto it = E_.begin(); it != E_.end(); ++it) {
        int i = (*it).first;
        int j = (*it).second;
        vec<Lit> v;
        for (int x = 0; x < k; x++) {
            Lit l1 = mkLit(arr[i][x]);
            const Lit& l1_ = l1;
            v.push(l1_);
            Lit l2 = mkLit(arr[j][x]);
            const Lit& l2_ = l2;
            v.push(l2_);
        }
        const vec<Lit>& v_ = v;
        solver.addClause(v_);
    }

    // Check for solution and retrieve model if found
    auto sat = solver.solve();
    if (sat) {
        vector<int> vertices;
        for (int i = 0; i < V; i++) {
            for (int j = 0; j < k; j++) {
                if (solver.modelValue(arr[i][j]) == l_True) {
                    vertices.push_back(i);
                }
            }
        }
        sort(vertices.begin(), vertices.end());
        for (auto it = vertices.begin(); it != vertices.end(); ++it) {
            output += to_string(*(it));
            if ((it + 1) != vertices.end()) {
                output += " ";
            }
        }
        output += "\n";
        return make_pair(true, output);
    } else {
        return make_pair(false, output);
        ;
    }
}

void inputParser(string cmd) {
    string str = cmd;
    str = str.substr(2);
    stringstream ss(str);
    string segment;
    char delimiter = '<';
    getline(ss, segment, delimiter);
    while (getline(ss, segment, delimiter)) {
        segment.erase(remove_if(segment.end() - 3, segment.end(), isRemoved), segment.end());
        size_t index = segment.find_first_of(",");
        int first = atoi((segment.substr(0, index)).c_str());
        int second = atoi((segment.substr(index + 1, segment.size() - index - 1)).c_str());
        max(first, second) > maxVertexId ? maxVertexId = max(first, second) : maxVertexId;
        vertices.insert(first);
        vertices.insert(second);
        edges.push_back(make_pair(first, second));
    }
}

bool isRemoved(char c) {
    return (c == '>') || (c == '}') || (c == ',');
}

void* APPROX_VC_2(void*) {
    vector<edge> tmp = edges;
    vector<int> output;
    string outputStr = "APPROX_VC_2: ";
    while (tmp.size() > 0) {
        int first = tmp[0].first;
        int second = tmp[0].second;
        output.push_back(first);
        output.push_back(second);
        for (auto it = tmp.begin(); it != tmp.end(); ++it) {
            if ((*it).first == first || (*it).first == second || (*it).second == first || (*it).second == second) {
                tmp.erase(it);
                it--;
            }
        }
    }
    sort(output.begin(), output.end());
    for (auto it : output) {
        outputStr += to_string(it) + " ";
    }
    pthread_mutex_lock(&cout_mutex);
    outputStrVec.push_back(outputStr);
    pthread_mutex_unlock(&cout_mutex);
    return NULL;
}

void* APPROX_VC_1(void*) {
    vector<edge> tmp = edges;
    vector<int> output;
    string outputStr = "APPROX_VC_1: ";
    while (tmp.size() > 0) {
        vector<edge>& tmp_ = tmp;
        int targetVertexId = findHighestDegreeVertex(tmp_);
        output.push_back(targetVertexId);
        for (auto it = tmp.begin(); it != tmp.end(); ++it) {
            if ((*it).first == targetVertexId || (*it).second == targetVertexId) {
                tmp.erase(it);
                it--;
            }
        }
    }
    sort(output.begin(), output.end());
    for (auto it : output) {
        outputStr += to_string(it) + " ";
    }
    pthread_mutex_lock(&cout_mutex);
    outputStrVec.push_back(outputStr);
    pthread_mutex_unlock(&cout_mutex);
    return NULL;
}

int findHighestDegreeVertex(vector<edge>& edges_) {
    int targetVertexId = -1;
    int maxCount = 0;
    for (auto v : vertices) {
        int count = 0;
        for (auto e : edges_) {
            if (v == e.first || v == e.second) {
                count++;
            }
        }
        if (count > maxCount) {
            maxCount = count;
            targetVertexId = v;
        }
    }
    return targetVertexId;
}

void* CNF_SAT_VC(void*) {
    vector<edge>& E_ = edges;
    int low = 1, high = maxVertexId, mid;
    string outputStr;
    while (low <= high) {
        mid = (high + low) / 2;
        pair<bool, string> p = printVertexCover(E_, maxVertexId + 1, mid);
        if (p.first) {
            high = mid - 1;
            outputStr = p.second;
        } else {
            low = mid + 1;
        }
    }
    pthread_mutex_lock(&cout_mutex);
    outputStr = "CNF_SAT_VC: " + outputStr;
    outputStrVec.push_back(outputStr);
    pthread_mutex_unlock(&cout_mutex);
    return NULL;
}

void* ioOperation(void*) {
    int V;
    string input;
    getline(cin, input);
    while (input.at(0) == 'V') {
        V = atoi((input.substr(2)).c_str());
        getline(cin, input);
        while (input.at(0) == 'E') {
            inputParser(input);
            if ((maxVertexId + 1) > V) {
                cerr << "Error: At least one vertex in E whose id is greater than (V - 1)." << endl;
            } else {
                pthread_t t1, t2, t3;
                pthread_create(&t1, NULL, &CNF_SAT_VC, NULL);
                pthread_create(&t2, NULL, &APPROX_VC_1, NULL);
                pthread_create(&t3, NULL, &APPROX_VC_2, NULL);
                pthread_join(t1, NULL);
                pthread_join(t2, NULL);
                pthread_join(t3, NULL);
                string cnf, appr1, appr2;
                for(auto str : outputStrVec) {
                    if(str.find("CNF_SAT_VC")!=std::string::npos) {
                        cnf = str;
                    }
                    if(str.find("APPROX_VC_1")!=std::string::npos) {
                        appr1 = str;
                    }
                    if(str.find("APPROX_VC_2")!=std::string::npos) {
                        appr2 = str;
                    }
		}
            cout << cnf << appr1 << endl << appr2 << endl;
            }
            maxVertexId = -1;
            getline(cin, input);
            edges.clear();
            vertices.clear();
            outputStrVec.clear();
            }
    }
    return NULL;
}

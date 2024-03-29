# Analysis-of-Minimum-Vertex-Cover

## Problem Definition: 
The purpose of this project is to solve minimum vertex cover problem for an existing unidirectional graph by using three different methods and study the time efficiency and accuracy of these three methods.

## Method 1:
CNF-SAT: In this method, the vertex cover problem is transferred into an CNF format and solved by MiniSAT library.

## Method 2:
APPROX-VC-1: Pick a vertex of highest degree (most incident edges). Add it to vertex cover and throw away all edges incidents on that vertex. Repeat till no edges remain.

## Method 3:
APPROX-VC-2: Randomly pick an edge <u, v>. Add both u and v to vertex cover and throw away all edges incidents on that vertex. Repeat till no edges remain.

## Test Inputs:
Graphs with vertices size 7, 10, 13, 15 and 17 were generated by “graphGen” and used as input for the tests for CNF-SAT and approximation ratio. For Approx-VC-1 and Approx-VC-2, Therefore graphs with vertices size 7, 10, 13, 15, 17, 20, 30 and 40 were generated by “graphGen” and used as input.

## Result and Analysis:
### Time Efficiency:
To ensure an invariant testing environment, three threads are created to run the three algorithms concurrently. The time efficiency is analyzed by measuring the CPU clock time of the whole period of individual thread. Below is the log-linear plot for the comparison.
Theoretical time-efficiency analysis:   

CNF-SAT: The reduction consists of 4 components.   
1) Non-empty ith vertex in vertex cover of size k, where i ∈[1,𝑘]. (k clauses)
2) At most one occurrence of a particular vertex is allowed in vertex cover, which means ith and jth vertex in vertex cover cannot be the same vertex. (𝑛 × (𝑘 choose 2) clauses)
3) ith vertex in vertex cover cannot map to more than one vertex in the graph. (𝑘 × (𝑛 choose 2) clauses)
4) Every edge is incident to at least one vertex in vertex cover. (|E|)

For graph with fixed number of vertices, the running time is exponential to the expected size the vertex cover, k. In our implementation, we adopt binary search to find the minimum of k, rather than linear probing.

The main factor is the number of vertices in the graph. It is obvious that (𝑛 choose 2) will lead O(a^n), that is, with increased number of vertices contributes to exponential growth of the time consumption.

![Report](https://user-images.githubusercontent.com/29167705/63555461-03c60080-c50f-11e9-8f6d-1066da21c6e4.jpg)

The above is the overview comparison plot among three algorithms. We can clearly observe that the CNF-SAT running time tends to be linear to the total number of vertices in a log-linear plot, which illustrates their exponential relationship.

We also observe that the standard deviation in CNF-SAT increases exponentially with n. This is due to the fact that the running time is O(a^k). In our algorithm, the binary search was implemented to find the minimum. k on the second run. When n = 10, k becomes 7 from 5. When n = 100, k becomes 75 from 50. The greater Δ𝑘 is, the greater difference presented in time. In general, it performs worse than the other two approximation algorithm in terms of time-efficiency.

Approx-VC-1 and Approx-VC-2 behaves very similarly in terms of the time-efficiency and a lot more efficient than CNF-SAT. According to the figure, they both run in polynomial time asymptotically. This observation agrees with the following asymptotical analysis of these methods.

In Approx-VC-1, it takes O(n) of time to locate the most incident vertex(linear search) and remove all connected vertices. This operation will be iterated at most n times which result a running time of O(n^2).

Similarly, In Approx-VC-2, it takes O(n) of time to remove all connected vertices. This operation will be iterated at most n times which result a running time of O(n^2).

However, there exists some cumbersomeness in APPROX_VC_1 due to the fact that it requires an extra linear search to find the highest degree vertex. Asymptotically, though, the difference is subtle.

Due to the large relative different scale between CNF-SAT and two approximation methods, Figure 2 has been plot to contain only two approximation methods to reveal their performance.

![Report](https://user-images.githubusercontent.com/29167705/63555538-4c7db980-c50f-11e9-8e39-a97cd2c7de20.jpg)

From it, we can observe that the standard deviation in Approx-2 decreases with number of vertices increase. This is because Approx-2 randomly picks an edge <u, v> from the edge list so that it is independent of the sparsity of a particular graph. Approx-VC-1 has to linearly search through the graph to find the most incident vertex in each iteration which is highly graph dependent. Therefore Approx-VC-1’s running time is more sensitive to different inputs than Approx-VC-2 which reflects by the discrepancy in standard deviations.

### Accuracy
From the figure below, it is clear that Approx-VC-1 is better than Approx-VC-2 in terms of the size of vertex cover, for the reason that the approximation ratio for Approx-VC-1 is very close to 1 while the approximation ratio for Approx-VC-2 fluctuate around 1.5. Also, Approx-VC-1 has very small standard deviation compare to Approx-VC-2 which indicates that Approx-VC-1 more likely to delivery stable outcome than Approx-VC-1.

![Report](https://user-images.githubusercontent.com/29167705/63555589-851d9300-c50f-11e9-96ac-a58dd9fe3cb5.jpg)

The difference in Approximation ratio output for these two method is because of the algorithm difference. In Approx-VC-1, Step 1 is to pick the most incident vertex and Approx-VC-2 randomly selects an edge from the edge list and adds the both ends to vertex cover. After picking the vertex, Step 2 for both methods is to throw away all incident vertices. Step 1 and 2 will be repeated until there is no edge left. In most cases, vertex selected in Aprox-VC-1 in every step covers more edges than vertex selected in Approx-VC-2. More importantly, Approx-VC-2 add both ends to the vertex cover in Step 1 which means it has a very big chance to add a vertex which has already been covered into vertex cover. This dramatically increase the size of vertex by potentially inserting already covered vertices in each iteration.

From the reason above, Approx-VC-1 more likely to produce a vertex cover with smaller size compare to Approx-VC-2. This agrees with the observation from the figure.

Regarding the standard deviation discrepancy between Approx-VC-1 and Approx-VC-2, it is caused by similar reason. Within Approx-VC-1, each selection is defined (Always the most incident edge) however for Approx-VC-2, there is no control on each selection (random selection). Because of that, the result of Approx-VC-2 for the same graph may likely be different while Approx-VC-1 always produce the same result for same graph. As a result, over of a wide range of graph with different vertices size, Approx-VC-1 provides more stably results compare to Approx-VC-2 which means less deviation.

In terms of the spikes in Figure 3.Approximation Ratio of Approx-VC-1 and Approx-VC-2, for Approx-VC-1 the spikes at V15 is mainly caused by the geometry of input graph. For Approx-VC-2, the approximation goes up and down along with the increasing of vertices number. There are two main contributions to it, first is the geometry of input graph and the second is the randomness in edge picking.

## Conclusion:
Base on our testing results and analysis above. We can conclude that CNF-SAT provides most accurate result while Approx-VC-2 is the most time efficient. Approx-VC-1 lays between these two methods. The time consumption of CNF-SAT increase exponentially versus number of vertices and the time consumption of Approx-VC-1 and Approx-VC-2 increase polynomial versus number of vertices. Under the input of same vertex number. The performance of CNF-SAT is highly depended on input graph. In contrast, Approx-VC-2’s behaviour is mostly independent of the inputs. Meanwhile, input has moderate effect on Aprrox-VC-1’s performance.

In respect of real world vertex cover application, if it is required to produce a minimum vertex cover than CNF-SAT is the only method should be used. If a small tolerance is allowed on the size of output vertex cover, Approx-VC-1 is recommended for its well balance in both efficiency and accuracy.

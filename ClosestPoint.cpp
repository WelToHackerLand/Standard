#include <bits/stdc++.h>

#define     less    ___less
#define     INF     1000000000
using namespace std;

struct Point {
    double x, y;
};

Point result1, result2;
double bestDistance;

double euclideanDistance(Point a, Point b)  {
    double X = a.x - b.x, Y = a.y - b.y;
    return sqrt(X*X + Y*Y);
}

// comparison first done by y coordinate, then by x coordinate
bool less(Point a, Point b) {
    if(a.y < b.y) return true;
    if(a.y > b.y) return false;
    return a.x < b.x;
}

void merge(Point* a, Point* aux, int lo, int mid, int hi)   {
    int i, j, k;
    for(k = lo; k <= hi; k++)
        aux[k] = a[k];

    i = lo; j = mid + 1; k = lo;
    while(i <= mid && j <= hi)
        a[k++] = less(aux[i], aux[j]) ? aux[i++] : aux[j++];

    // Copy the rest of the left side of the array into the target array
    while(i <= mid)
        a[k++] = aux[i++];
}

double closestPair(Point* pointsByX, Point* pointsByY, Point* aux, int lo, int hi)    {
    if(hi <= lo)
        return INF;

    int mid = lo + (hi - lo)/2;
    double delta = closestPair(pointsByX, pointsByY, aux, lo, mid);
    double dist = closestPair(pointsByX, pointsByY, aux, mid+1, hi);
    if(dist < delta)
        delta = dist;

    merge(pointsByY, aux, lo, mid, hi);

    int M = 0, i, j;
    for(i = lo; i <= hi; i++)
        if(abs(pointsByY[i].x - pointsByX[mid].x) < delta)
            aux[M++] = pointsByY[i];

    double distance, t;
    for(i = 0; i < M; i++)  {
        for(j = i+1; j < M && (aux[j].y - aux[i].y < delta); j++) {
            distance = euclideanDistance(aux[i], aux[j]);
            if(distance < delta)    {
                delta = distance;
                if(delta < bestDistance) {
                    bestDistance = delta;
                    result1 = aux[i];
                    result2 = aux[j];
                }
            }
        }
    }
    return delta;
}

bool X_ORDER(Point a, Point b)  {
    return a.x < b.x;
}

int main()  {
    int N, i;
    Point *points, *pointsByY, *aux;

    //freopen("input.txt", "r", stdin);

    cin>> N;            //Enter the number of points in the plane
    points = new Point[N];
    for(i=0; i<N; i++)  // Enter N points (x, y)
        cin>>points[i].x >>points[i].y;

    if(N <= 1) return 0;

    sort(points, points + N, X_ORDER);
    pointsByY = new Point[N];
    for(i=0; i<N; i++)
        pointsByY[i] = points[i];
    aux = new Point[N];

    bestDistance = INF;
    closestPair(points, pointsByY, aux, 0, N-1);

    // print their euclidean distance
    printf("%.3f",bestDistance);

    return 0;
}

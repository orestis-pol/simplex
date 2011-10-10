/*
 * Implementation of the
 * revised Simplex method
 * for linear programming
 * orestis@cs.columbia.edu
 */

#include <stdlib.h>


enum { OPTIMAL, UNBOUNDED, UNFEASIBLE, UNDEFINED };

int simplex_core(double **A, double *c, int m, int n, double *x, char *bs,
                 double **B, double **Bi, double *y, double *d)
{
	int i, j, z, s, e;
	double ya, xd, *t;
	for (;;) {
		//assemble B
		for (j = z = 0 ; z != m ; ++j)
			if (bs[j]) {
				for (i = 0 ; i != m ; ++i)
					B[i][z] = A[i][j];
				z++;
			}
		//compute B^-1
		for (i = 0 ; i != m ; ++i)
			for (j = 0 ; j != m ; ++j)
				Bi[i][j] = (i == j ? 1.0 : 0.0);
		for (i = 0 ; i != m ; ++i) {
			for (z = i, j = i+1 ; j != m ; ++j)
				if ((B[j][i] < 0.0 ? -B[j][i] : B[j][i]) >
				    (B[z][i] < 0.0 ? -B[z][i] : B[z][i]))
					z = j;
			t = B[i];
			B[i] = B[z];
			B[z] = t;
			t = Bi[i];
			Bi[i] = Bi[z];
			Bi[z] = t;
			for (j = 0 ; j != m ; ++j)
				if (i != j) {
					xd = B[j][i] / B[i][i];
					for (z = i ; z != m ; ++z)
						B[j][z] -= B[i][z] * xd;
					for (z = 0 ; z != m ; ++z)
						Bi[j][z] -= Bi[i][z] * xd;
				}
		}
		for (i = 0 ; i != m ; ++i)
			for (j = 0 ; j != m ; ++j)
				Bi[i][j] /= B[i][i];
		//compute y
		for (i = 0 ; i != m ; ++i)
			for (y[i] = 0.0, j = z = 0 ; z != m ; ++j)
				if (bs[j])
					y[i] += c[j] * Bi[z++][i];
		//check if there is a column to enter in base
		for (s = 0 ; s != n + m ; ++s)
			if (!bs[s]) {
				for (ya = 0.0, i = 0 ; i != m ; ++i)
					ya += y[i] * A[i][s];
				if (c[s] - ya > 0.00000001) break;
			}
		//check if solution is optimal
		if (s == n + m)
			return OPTIMAL;
		//compute d
		for (i = 0 ; i != m ; ++i)
			for (d[i] = 0.0, j = 0 ; j != m ; ++j)
				d[i] += Bi[i][j] * A[j][s];
		//check if bounded
		for (e = z = 0 ; e != n + m ; ++e)
			if (bs[e] && d[z++] > 0.00000001) break;
		if (e == n + m)
			return UNBOUNDED;
		//choose column to exit the base
		xd = x[e] / d[z-1];
		for (j = e + 1 ; z != m ; ++j)
			if (bs[j]) {
				if (d[z] > 0.00000001 && x[j] / d[z] < xd) {
					e = j;
					xd = x[j] / d[z];
				}
				z++;
			}
		//update values and base
		for (j = z = 0 ; z != m ; ++j)
			if (bs[j])
				x[j] -= xd * d[z++];
		x[s] = xd;
		bs[s] = 1;
		bs[e] = 0;
	}
}

int simplex(double **p, double *b, double *c, int m, int n, double *r)
{
	int i, j, u = (n < m ? 1 : 0), s = (u ? n : m);
	char *bs = (char*)malloc((n+m+1)*sizeof(char));
	double *ec = (double*)malloc((n+m+1)*sizeof(double));
	double *x = (double*)malloc((n+m+1)*sizeof(double));
	double *y = (double*)malloc(s*sizeof(double));
	double *d = (double*)malloc(s*sizeof(double));
	double **A = (double**)malloc(s*sizeof(double*));
	double **B = (double**)malloc(s*sizeof(double*));
	double **Bi = (double**)malloc(s*sizeof(double*));
	for (i = 0 ; i != s ; ++i) {
		A[i] = (double*)malloc((m+n+1)*sizeof(double));
		B[i] = (double*)malloc(s*sizeof(double));
		Bi[i] = (double*)malloc(s*sizeof(double));
	}
	//if constraints more than variable solve the dual
	if (!u)
		for (i = 0 ; i != m ; ++i)
			for (j = 0 ; j != n ; ++j)
				A[i][j] = p[i][j];
	else {
		for (i = 0 ; i != n ; ++i)
			for (j = 0 ; j != m ; ++j)
				A[i][j] = -p[j][i];
		n = m;
		m = i;
	}
	//fill in slack variables
	for (i = 0 ; i != m ; ++i) {
		for (j = 0 ; j != m ; ++j)
			A[i][j+n] = (i == j ? 1 : 0);
		ec[i+n] = 0.0;
	}
	//check if 2-phase simplex is required
	for (s = 0 ; s != m ; ++s)
		if ((u ? -c[s] : b[s]) < -0.00000001)
			break;
	if (s != m) {
		//find line with lowest negative bound
		for (i = s+1 ; i != m ; ++i)
			if (u ? c[i] > c[s] : b[i] < b[s])
				s = i;
		//create data for an extra simplex
		for (i = 0 ; i != m ; ++i)
			A[i][n+m] = ((u ? -c[i] : b[i]) < -0.00000001 ? -1.0 : 0.0);
		for (i = 0 ; i != n ; ++i) {
			ec[i] = x[i] = 0.0;
			bs[i] = 0;
		}
		for (i = 0 ; i != m ; ++i)
			if (i == s) {
				x[i+n] = 0.0;
				bs[i+n] = 0;
			} else if (A[i][n+m] == 0.0) {
				x[i+n] = (u ? -c[i] : b[i]);
				bs[i+n] = 1;
			} else {
				x[i+n] = (u ? c[s]-c[i] : b[i]-b[s]);
				bs[i+n] = 1;
			}
		ec[n+m] = -1.0;
		x[n+m] = (u ? c[s] : -b[s]);
		bs[n+m] = 1;
		//find a valid base by an extra simplex
		s = simplex_core(A, ec, m, n+1, x, bs, B, Bi, y, d);
		if (x[n+m] > 0.00000001) {
			s = (u ? UNDEFINED : UNFEASIBLE);
			goto end;
		}
	} else {
		//set slack variables as base
		for (i = 0 ; i != n ; ++i) {
			x[i] = 0.0;
			bs[i] = 0;
		}
		for (i = 0 ; i != m ; ++i) {
			x[i+n] = (u ? -c[i] : b[i]);
			bs[i+n] = 1;
		}
	}
	//fix objective factors
	if (!u)
		for (i = 0 ; i != n ; ++i)
			ec[i] = c[i];
	else
		for (i = 0 ; i != n ; ++i)
			ec[i] = -b[i];
	//run simplex and collect solution
	s = simplex_core(A, ec, m, n, x, bs, B, Bi, y, d);
	if (s == UNBOUNDED)
		s = (u ? UNFEASIBLE : UNBOUNDED);
	else if (!u)
		for (i = 0 ; i != n ; ++i)
			r[i] = x[i];
	else
		for (i = 0 ; i != m ; ++i)
			r[i] = y[i];
	end:
	for (i = 0 ; i != m ; ++i) {
		free(A[i]);
		free(B[i]);
		free(Bi[i]);
	}
	free(A);
	free(B);
	free(Bi);
	free(x);
	free(y);
	free(d);
	free(ec);
	free(bs);
	return s;
}


/* Testing mains */

#include <stdio.h>
#include <time.h>


#define TM 0

#if TM == 1

/* 2-phase example */

int main(void)
{
	double c[3] =  { 1, -1,  1};
	double a1[3] = { 2, -1,  2};
	double a2[3] = { 2, -3,  1};
	double a3[3] = {-1,  1, -2};
	double b[3] =  { 4, -5, -1};
	double *a[3] = {a1, a2, a3}, r[3];
	int s = simplex(a, b, c, 3, 3, r);
	if (s == OPTIMAL)
		printf("%.1f %.1f %.1f\n", r[0], r[1], r[2]);
	else if (s == UNFEASIBLE)
		printf("Unfeasible\n");
	else if (s == UNBOUNDED)
		printf("Unbounded\n");
	return EXIT_SUCCESS;
}

#elif TM == 2

/* Unfeasible example */

int main(void)
{
	double  c[2] = { 2, 3};
	double a1[2] = {-1,-1};
	double a2[2] = { 1, 4};
	double a3[2] = { 6, 1};
	double  b[3] = {-1, 2, 2};
	double *a[3] = {a1, a2, a3}, r[2];
	int s = simplex(a, b, c, 3, 2, r);
	if (s == OPTIMAL)
		printf("%.1f %.1f\n", r[0], r[1]);
	else if (s == UNFEASIBLE)
		printf("Unfeasible\n");
	else if (s == UNBOUNDED)
		printf("Unbounded\n");
	return EXIT_SUCCESS;
}

#elif TM == 3

/* Unbounded example */

int main(void)
{
	double b[2] = {1, 5};
	double c[1] = {1};
	double a1[1] = {-1};
	double a2[1] = {-2};
	double *a[2] = {a1, a2};
	double r[1];
	int s = simplex(a, b, c, 2, 1, r);
	if (s == OPTIMAL)
		printf("%.1f\n", r[0]);
	else if (s == UNFEASIBLE)
		printf("Unfeasible\n");
	else if (s == UNBOUNDED)
		printf("Unbounded\n");
	else if (s == UNDEFINED)
		printf("Unbounded or unfeasible\n");
	return EXIT_SUCCESS;
}

#else

/* Independent set */

typedef struct edge {
	int source;
	int dest;
} edge;

void swap(int a[], int i, int j)
{
	int t = a[i];
	a[i] = a[j];
	a[j] = t;
}

void random_graph(edge *g, int n, int m)
{
	int i, j, e, l = (n*n-n)/2;
	int *p = (int*)malloc(l*sizeof(int));
	for (i = e = 0 ; i != n ; ++i)
		for (j = i+1 ; j != n ; ++j)
			p[e++] = i*n+j;
	for (i = 0 ; i != m ; ++i) {
		swap(p, i, rand()%(l-i)+i);
		g[i].source = p[i]/n;
		g[i].dest = p[i]%n;
	}
	free(p);
}

int main(int argc, char **argv)
{
	int i, j, n = 20, m = 50;
	double **p, *b, *c, *r, a;
	edge *g;
	if (argc > 4) {
		fprintf(stderr, "Too many arguments\n");
		return EXIT_FAILURE;
	}
	if (argc > 1) {
		n = atoi(argv[1]);
		if (n <= 0) {
			fprintf(stderr, "Wrong number of nodes\n");
			return EXIT_FAILURE;
		}
	}
	if (argc > 2) {
		m = atoi(argv[2]);
		if (m < 0 || m > (n*n-n)/2) {
			fprintf(stderr, "Wrong number of edges\n");
			return EXIT_FAILURE;
		}
	}
	if (argc > 3)
		srand((unsigned int)atoi(argv[3]));
	else
		srand((unsigned int)time(NULL));
	g = (edge*)malloc(m*sizeof(edge));
	random_graph(g, n, m);
	p = (double**)malloc((m+n)*sizeof(double*));
	b = (double*)malloc((m+n)*sizeof(double));
	c = (double*)malloc(n*sizeof(double));
	r = (double*)malloc(n*sizeof(double));
	for (i = 0 ; i != m ; ++i) {
		p[i] = (double*)malloc(n*sizeof(double));
		for (j = 0 ; j != n ; ++j)
			p[i][j] = 0.0;
		p[i][g[i].source] = 1.0;
		p[i][g[i].dest] = 1.0;
		b[i] = 1.0;
	}
	for (i = 0 ; i != n ; ++i) {
		p[i+m] = (double*)malloc(n*sizeof(double));
		for (j = 0 ; j != n ; ++j)
			p[i+m][j] = 0.0;
		p[i+m][i] = 1.0;
		b[i+m] = 1.0;
	}
	for (i = 0 ; i != n ; ++i)
		c[i] = 1.0;
	j = simplex(p, b, c, m+n, n, r);
	if (j == UNBOUNDED)
		printf("\nUNBOUNDED\n");
	else if (j == UNFEASIBLE)
		printf("\nUNFEASIBLE\n");
	else if (j == OPTIMAL) {
		printf("\nOPTIMAL!\n\n");
		for (a = 0.0, i = 0 ; i != n ; ++i) {
			printf("%.1f  ", r[i]);
			a += r[i] * c[i];
		}
		printf("\n\nTotal objective value: %.1f\n", a);
	}
	for (i = 0 ; i != n+m ; ++i)
		free(p[i]);
	free(p);
	free(g);
	free(b);
	free(c);
	free(r);
	return EXIT_SUCCESS;
}

#endif

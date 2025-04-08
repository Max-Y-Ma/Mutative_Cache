#include <stdio.h>

//-----------------------------------------------------------------------------
// Gilbert-Johnson-Keerthi (GJK) collision detection algorithm in 2D
//-----------------------------------------------------------------------------

struct _vec2 { int x; int y; };
typedef struct _vec2 vec2;

//-----------------------------------------------------------------------------
// Basic vector arithmetic operations
int div_i( int a, int b) { return a/b; } 
size_t div_s( size_t a, size_t b) { return a/b; } 
vec2 subtract (vec2 a, vec2 b) { a.x -= b.x; a.y -= b.y; return a; }
vec2 negate (vec2 v) { v.x = -v.x; v.y = -v.y; return v; }
vec2 perpendicular (vec2 v) { vec2 p = { v.y, -v.x }; return p; }
vec2 mvp (int a, int b, int c, int d, int s, vec2 v) { vec2 p = { (a * v.x + b * v.y )>>s, (c * v.x + d * v.y)>>s }; return p; }
int dotProduct (vec2 a, vec2 b) { return a.x * b.x + a.y * b.y; }
int lengthSquared (vec2 v) { return v.x * v.x + v.y * v.y; }

//-----------------------------------------------------------------------------
// Triple product expansion is used to calculate perpendicular normal vectors 
// which kinda 'prefer' pointing towards the Origin in Minkowski space

vec2 tripleProduct (vec2 a, vec2 b, vec2 c) {
    
    vec2 r;
    
    int ac = a.x * c.x + a.y * c.y; // perform a.dot(c)
    int bc = b.x * c.x + b.y * c.y; // perform b.dot(c)
    
    // perform b * a.dot(c) - a * b.dot(c)
    r.x = b.x * ac - a.x * bc;
    r.y = b.y * ac - a.y * bc;
    return r;
}

//-----------------------------------------------------------------------------
// This is to compute average center (roughly). It might be different from
// Center of Gravity, especially for bodies with nonuniform density,
// but this is ok as initial direction of simplex search in GJK.

vec2 averagePoint (const vec2 * vertices, size_t count) {
    vec2 avg = { 0, 0 };
    for (size_t i = 0; i < count; i++) {
        avg.x += vertices[i].x;
        avg.y += vertices[i].y;
    }
    avg.x /= count;
    avg.y /= count;
    return avg;
}

//-----------------------------------------------------------------------------
// Get furthest vertex along a certain direction

size_t indexOfFurthestPoint (const vec2 * vertices, size_t count, vec2 d) {
    
    int maxProduct = dotProduct (d, vertices[0]);
    size_t index = 0;
    for (size_t i = 1; i < count; i++) {
        int product = dotProduct (d, vertices[i]);
        if (product > maxProduct) {
            maxProduct = product;
            index = i;
        }
    }
    return index;
}

//-----------------------------------------------------------------------------
// Minkowski sum support function for GJK

vec2 support (const vec2 * vertices1, size_t count1,
              const vec2 * vertices2, size_t count2, vec2 d) {

    // get furthest point of first body along an arbitrary direction
    size_t i = indexOfFurthestPoint (vertices1, count1, d);
    
    // get furthest point of second body along the opposite direction
    size_t j = indexOfFurthestPoint (vertices2, count2, negate (d));

    // subtract (Minkowski sum) the two points to see if bodies 'overlap'
    return subtract (vertices1[i], vertices2[j]);
}

//-----------------------------------------------------------------------------
// The GJK yes/no test

int iter_count = 0;

int gjk (const vec2 * vertices1, size_t count1,
         const vec2 * vertices2, size_t count2) {
    
    size_t index = 0; // index of current vertex of simplex
    vec2 a, b, c, d, ao, ab, ac, abperp, acperp, simplex[3];
    
    vec2 position1 = averagePoint (vertices1, count1); // not a CoG but
    vec2 position2 = averagePoint (vertices2, count2); // it's ok for GJK )

    // initial direction from the center of 1st body to the center of 2nd body
    d = subtract (position1, position2);
    
    // if initial direction is zero – set it to any arbitrary axis (we choose X)
    if ((d.x == 0) && (d.y == 0))
        d.x = 1;
    
    // set the first support as initial point of the new simplex
    a = simplex[0] = support (vertices1, count1, vertices2, count2, d);
    
    if (dotProduct (a, d) <= 0)
        return 0; // no collision
    
    d = negate (a); // The next search direction is always towards the origin, so the next search direction is negate(a)
    
    while (1) {
        iter_count++;
        
        a = simplex[++index] = support (vertices1, count1, vertices2, count2, d);
        
        if (dotProduct (a, d) <= 0)
            return 0; // no collision
        
        ao = negate (a); // from point A to Origin is just negative A
        
        // simplex has 2 points (a line segment, not a triangle yet)
        if (index < 2) {
            b = simplex[0];
            ab = subtract (b, a); // from point A to B
            d = tripleProduct (ab, ao, ab); // normal to AB towards Origin
            if (lengthSquared (d) == 0)
                d = perpendicular (ab);
            continue; // skip to next iteration
        }
        
        b = simplex[1];
        c = simplex[0];
        ab = subtract (b, a); // from point A to B
        ac = subtract (c, a); // from point A to C
        
        acperp = tripleProduct (ab, ac, ac);
        
        if (dotProduct (acperp, ao) >= 0) {
            
            d = acperp; // new direction is normal to AC towards Origin
            
        } else {
            
            abperp = tripleProduct (ac, ab, ab);
            
            if (dotProduct (abperp, ao) < 0)
                return 1; // collision
            
            simplex[0] = simplex[1]; // swap first element (point C)

            d = abperp; // new direction is normal to AB towards Origin
        }
        
        simplex[1] = simplex[2]; // swap element in the middle (point B)
        --index;
    }
    
    return 0;
}

//-----------------------------------------------------------------------------

#include <stdlib.h>

int main(int argc, const char * argv[]) {
    asm volatile ("slti x0, x0, 1");
    
    // Declare all variables uninitialized first
    int ma, mb, mc, md, s;
    vec2 vertices1[5], vertices2[3];
    size_t count1, count2;
    
    // Initialize values via assignment
    ma = 13;
    mb = -8;
    mc = 8;
    md = 13;
    s = 4;
    
    vertices1[0] = (vec2){ 40000, 800 };
    vertices1[1] = (vec2){ 55000, -20 };
    vertices1[2] = (vec2){ 32000, -300 };
    vertices1[3] = (vec2){ 41000, 200 };
    vertices1[4] = (vec2){ 37000, -100 };
    
    vertices2[0] = (vec2){ -60000, 800 };
    vertices2[1] = (vec2){ -55000, -200 };
    vertices2[2] = (vec2){ -32000, 300 };

    count1 = sizeof(vertices1) / sizeof(vec2);
    count2 = sizeof(vertices2) / sizeof(vec2);

    asm volatile ("slti x0, x0, 3");
	while (1) {
		vec2 a[count1];
		vec2 b[count2];

		for (size_t i = 0; i < count1; ++i) a[i] = (vertices1[i]);
		for (size_t i = 0; i < count2; ++i) b[i] = (vertices2[i]);

		int collisionDetected = gjk(a, count1, b, count2);
        if (collisionDetected) {
            break;
        }

        for (size_t k = 0; k < count1; k++) {
            vertices1[k] = mvp(ma, mb, mc, md, s, vertices1[k]);
        }

        for (size_t k = 0; k < count2; k++) {
            vertices2[k] = mvp(ma, mb, mc, md, s, vertices2[k]);
        }

		iter_count = 0;
	}
    asm volatile ("slti x0, x0, 4");
    asm volatile ("slti x0, x0, 2");
    return 0;
}

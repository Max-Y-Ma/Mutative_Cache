// adapted from team Decelerator Architecture, SP2023 ECE 498SJP

// to see the image output, do: 

// uncomment this:
// #define DEBUG


// run the follwing in your terminal:
// gcc raytracing.c -o main
// ./main > out.ppm
// convert out.ppm out.png

// and look at "out.png"

// you can change the resolution
#define IMAGE_WIDTH 16
#define IMAGE_HEIGHT 16

#ifdef DEBUG
#include <stdio.h>
#endif

#define FIXED_POINT_FRACTIONAL_BITS 12
#define TO_FIXED(var) (fixed_point_t)((float)(var) * (1 << FIXED_POINT_FRACTIONAL_BITS))
// #define TO_FIXED(var) var
#define FP_MAX 0x7fffffff
#define FP_MIN 0x80000000

#define VECTOR(name) fixed_point_t name[3]
#define TRIANGLE(name) VECTOR(name[3])
#define SCENE(name) TRIANGLE(name[])

#define NUM_OBJECTS 3

#define VIEWPORT_WIDTH 4096
#define VIEWPORT_HEIGHT 4096
#define FOCAL_LENGTH 4096

typedef int fixed_point_t;
// typedef float fixed_point_t;

void vec_sub(VECTOR(dest), VECTOR(src1), VECTOR(src2));
void vec_add(VECTOR(dest), VECTOR(src1), VECTOR(src2));
void vec_div(VECTOR(dest), VECTOR(src1), fixed_point_t src2);
void vec_mul(VECTOR(dest), VECTOR(src1), fixed_point_t src2);
void vec_cross(VECTOR(dest), VECTOR(src1), VECTOR(src2));
fixed_point_t vec_dot(VECTOR(src1), VECTOR(src2));

static fixed_point_t fp_div(fixed_point_t a, fixed_point_t b);
static fixed_point_t fp_mul(fixed_point_t a, fixed_point_t b);

inline fixed_point_t fp_div(fixed_point_t a, fixed_point_t b) {
    int ret;
    ret = a;
    ret <<= FIXED_POINT_FRACTIONAL_BITS;
    ret /= (int)b;
    return (fixed_point_t)ret;
    // return a / b;
}

inline fixed_point_t fp_mul(fixed_point_t a, fixed_point_t b) {
    int ret;
    ret = (int)a * (int)b;
    ret >>= (FIXED_POINT_FRACTIONAL_BITS);
    return (fixed_point_t)ret;
    // return a * b;
}

inline void vec_sub(VECTOR(dest), VECTOR(src1), VECTOR(src2)) {
    dest[0] = src1[0] - src2[0];
    dest[1] = src1[1] - src2[1];
    dest[2] = src1[2] - src2[2];
}

inline void vec_add(VECTOR(dest), VECTOR(src1), VECTOR(src2)) {
    dest[0] = src1[0] + src2[0];
    dest[1] = src1[1] + src2[1];
    dest[2] = src1[2] + src2[2];
}

inline void vec_div(VECTOR(dest), VECTOR(src1), fixed_point_t src2) {
    dest[0] = fp_div(src1[0], src2);
    dest[1] = fp_div(src1[1], src2);
    dest[2] = fp_div(src1[2], src2);
}

inline void vec_mul(VECTOR(dest), VECTOR(src1), fixed_point_t src2) {
    dest[0] = fp_mul(src1[0], src2);
    dest[1] = fp_mul(src1[1], src2);
    dest[2] = fp_mul(src1[2], src2);
}

inline void vec_cross(VECTOR(dest), VECTOR(src1), VECTOR(src2)) {
    dest[0] = fp_mul(src1[1], src2[2]) - fp_mul(src1[2], src2[1]);
    dest[1] = fp_mul(src1[2], src2[0]) - fp_mul(src1[0], src2[2]);
    dest[2] = fp_mul(src1[0], src2[1]) - fp_mul(src1[1], src2[0]);
}

inline fixed_point_t vec_dot(VECTOR(src1), VECTOR(src2)) {
    return fp_mul(src1[0], src2[0]) + fp_mul(src1[1], src2[1]) + fp_mul(src1[2], src2[2]);
}

fixed_point_t objects [3][3][3];

int main() {
    objects[0][0][0] = 1024;
    objects[0][0][1] = 1024;
    objects[0][0][2] = -4096;
    objects[0][1][0] = 2048;
    objects[0][1][1] = 2048;
    objects[0][1][2] = -4096;
    objects[0][2][0] = 819;
    objects[0][2][1] = 2048;
    objects[0][2][2] = -4096;
    objects[1][0][0] = -1024;
    objects[1][0][1] = -1024;
    objects[1][0][2] = -4096;
    objects[1][1][0] = 1843;
    objects[1][1][1] = -1843;
    objects[1][1][2] = -5324;
    objects[1][2][0] = 0;
    objects[1][2][1] = 1351;
    objects[1][2][2] = -6144;
    objects[2][0][0] = -1474;
    objects[2][0][1] = -1474;
    objects[2][0][2] = -6144;
    objects[2][1][0] = 1024;
    objects[2][1][1] = -2048;
    objects[2][1][2] = -6144;
    objects[2][2][0] = 819;
    objects[2][2][1] = 2457;
    objects[2][2][2] = -8192;

    VECTOR(temp1);
    VECTOR(temp2);
    VECTOR(temp3);

    // define origin vertex
    VECTOR(origin_ver) = {0, 0, 4096};

    // define viewport vectors
    VECTOR(view_hori_vec) = {VIEWPORT_WIDTH, 0, 0};
    VECTOR(view_vert_vec) = {0, VIEWPORT_HEIGHT, 0};
    VECTOR(view_direct_vec) = {0, 0, FOCAL_LENGTH}; // direction can be changed
    
    // define viewport lower-left-corner vertex
    // view_LLC = origin - view_hori/2 - view_vert/2 - view_direct_vec
    VECTOR(view_LLC_ver);

    vec_div(temp1, view_hori_vec, 8192);
    vec_sub(temp2, origin_ver, temp1);

    vec_div(temp1, view_vert_vec, 8192);
    vec_sub(view_LLC_ver, temp2, temp1);
    vec_sub(view_LLC_ver, view_LLC_ver, view_direct_vec);

    // ppm file header
    #ifdef DEBUG
        printf("P3\n");
        printf("%d %d 255\n", IMAGE_WIDTH, IMAGE_HEIGHT);
    #else
        volatile int output_ptr;
    #endif
    VECTOR(ray_origin_ver) = {origin_ver[0], origin_ver[1], origin_ver[2]};
    // direction = view_LLC_ver - origin + (view_hori_vec * (x / IMAGE_WIDTH)) + (view_vert_vec * (y / IMAGE_HEIGHT))
    VECTOR(orig_direct_vec);
    vec_sub(orig_direct_vec, view_LLC_ver, origin_ver);
    vec_mul(temp1, view_hori_vec, 0);
    vec_add(orig_direct_vec, orig_direct_vec, temp1);
    vec_mul(temp1, view_vert_vec, 0);
    vec_add(orig_direct_vec, orig_direct_vec, temp1);
    
    fixed_point_t x_offset, y_offset;

    VECTOR(ray_direct_vec) = {orig_direct_vec[0], orig_direct_vec[1], orig_direct_vec[2]};

    x_offset = fp_div(VIEWPORT_WIDTH, TO_FIXED(IMAGE_WIDTH));
    y_offset = fp_div(VIEWPORT_HEIGHT, TO_FIXED(IMAGE_HEIGHT));

    for (int y = 0; y < IMAGE_HEIGHT; ++y) {
        for (int x = 0; x < IMAGE_WIDTH; ++x) {
            // initialize ray
            // no bounces or shadows, so ray_origin = origin

            ray_direct_vec[0] += x_offset;

            unsigned int color[3] = {255, 255, 255};
            fixed_point_t t_old = -4096;
            for (int i=0; i < NUM_OBJECTS; ++i) {
                // n_vec = (b-a) X (c-b)
                VECTOR(n_vec);
                vec_sub(temp1, objects[i][1], objects[i][0]);
                vec_sub(temp2, objects[i][2], objects[i][1]);
                vec_cross(n_vec, temp1, temp2);

                // make sure the objects aren't perpendicular
                if (vec_dot(n_vec, ray_direct_vec) != 0) {
                    // d = n_vec . a
                    fixed_point_t d = vec_dot(n_vec, objects[i][0]);
                    
                    // t = (d - (n_vec . ray_origin_ver)) / (n_vec . ray_direct_vec)
                    fixed_point_t t = fp_div(d - vec_dot(n_vec, ray_origin_ver), vec_dot(n_vec, ray_direct_vec));
                    if (t_old < 0 || t < t_old) {
                        // q = ray_origin_ver + (ray_direct_vec * t)
                        VECTOR(q_ver);
                        vec_mul(temp1, ray_direct_vec, t);
                        vec_add(q_ver, temp1, ray_origin_ver);
                        // (b-a) X (q-a)
                        vec_sub(temp1, objects[i][1], objects[i][0]);
                        vec_sub(temp2, q_ver, objects[i][0]);
                        vec_cross(temp3, temp1, temp2);
                        if (vec_dot(temp3, n_vec) >= 0) {
                            // (c-b) X (q-b)
                            vec_sub(temp1, objects[i][2], objects[i][1]);
                            vec_sub(temp2, q_ver, objects[i][1]);
                            vec_cross(temp3, temp1, temp2);
                            if (vec_dot(temp3, n_vec) >= 0) {
                                // (a-c) X (q-c)
                                vec_sub(temp1, objects[i][0], objects[i][2]);
                                vec_sub(temp2, q_ver, objects[i][2]);
                                vec_cross(temp3, temp1, temp2);
                                if (vec_dot(temp3, n_vec) >= 0) {
                                    t_old = t;
                                    color[0] = 255;
                                    color[1] = i << 7;
                                    color[2] = 0;
                                }
                            }
                        }
                    } 
                }
            }
            #ifdef DEBUG
                printf("%d %d %d\n", color[0], color[1], color[2]);
            #else
                output_ptr = (color[0]<<16) | (color[1]<<8) | color[2];
            #endif
        }
        ray_direct_vec[0] = orig_direct_vec[0];
        ray_direct_vec[1] += y_offset;
    }

    return 0;
}

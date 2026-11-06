#ifndef NMM_BITBOARD_H
#define NMM_BITBOARD_H

#include <stdint.h>
#include <stdbool.h>

#define NUM_POINTS 24
#define ALL_POINTS_MASK 0x00FFFFFFU

typedef uint32_t bitboard_t;

typedef struct {
    bitboard_t white;
    bitboard_t black;
} nmm_board_t;

/* 16 Precomputed Mill Bitmasks */
static const bitboard_t MILL_MASKS[16] = {
    7U,        /* (0, 1, 2)   - Ring 0 Top */
    28U,       /* (2, 3, 4)   - Ring 0 Right */
    112U,      /* (4, 5, 6)   - Ring 0 Bottom */
    193U,      /* (0, 6, 7)   - Ring 0 Left */
    1792U,     /* (8, 9, 10)  - Ring 1 Top */
    7168U,     /* (10, 11, 12)- Ring 1 Right */
    28672U,    /* (12, 13, 14)- Ring 1 Bottom */
    49408U,    /* (8, 14, 15) - Ring 1 Left */
    458752U,   /* (16, 17, 18)- Ring 2 Top */
    1835008U,  /* (18, 19, 20)- Ring 2 Right */
    7340032U,  /* (20, 21, 22)- Ring 2 Bottom */
    12648448U, /* (16, 22, 23)- Ring 2 Left */
    131586U,   /* (1, 9, 17)  - Radial North */
    526344U,   /* (3, 11, 19) - Radial East */
    2105376U,  /* (5, 13, 21) - Radial South */
    8421504U   /* (7, 15, 23) - Radial West */
};

/* Exactly 2 mills for each of the 24 vertices */
static const int VERTEX_MILLS[24][2] = {
    {0, 3},   /* 0 */
    {0, 12},  /* 1 */
    {0, 1},   /* 2 */
    {1, 13},  /* 3 */
    {1, 2},   /* 4 */
    {2, 14},  /* 5 */
    {2, 3},   /* 6 */
    {3, 15},  /* 7 */
    {4, 7},   /* 8 */
    {4, 12},  /* 9 */
    {4, 5},   /* 10 */
    {5, 13},  /* 11 */
    {5, 6},   /* 12 */
    {6, 14},  /* 13 */
    {6, 7},   /* 14 */
    {7, 15},  /* 15 */
    {8, 11},  /* 16 */
    {8, 12},  /* 17 */
    {8, 9},   /* 18 */
    {9, 13},  /* 19 */
    {9, 10},  /* 20 */
    {10, 14}, /* 21 */
    {10, 11}, /* 22 */
    {11, 15}  /* 23 */
};

/* Adjacency Masks (32 undirected edges) */
static const bitboard_t ADJ_MASKS[24] = {
    (1U << 1) | (1U << 7),                         /* 0 */
    (1U << 0) | (1U << 2) | (1U << 9),             /* 1 */
    (1U << 1) | (1U << 3),                         /* 2 */
    (1U << 2) | (1U << 4) | (1U << 11),            /* 3 */
    (1U << 3) | (1U << 5),                         /* 4 */
    (1U << 4) | (1U << 6) | (1U << 13),            /* 5 */
    (1U << 5) | (1U << 7),                         /* 6 */
    (1U << 6) | (1U << 0) | (1U << 15),            /* 7 */
    (1U << 9) | (1U << 15),                        /* 8 */
    (1U << 8) | (1U << 10) | (1U << 1) | (1U << 17),/* 9 */
    (1U << 9) | (1U << 11),                        /* 10 */
    (1U << 10) | (1U << 12) | (1U << 3) | (1U << 19),/* 11 */
    (1U << 11) | (1U << 13),                       /* 12 */
    (1U << 12) | (1U << 14) | (1U << 5) | (1U << 21),/* 13 */
    (1U << 13) | (1U << 15),                       /* 14 */
    (1U << 14) | (1U << 8) | (1U << 7) | (1U << 23),/* 15 */
    (1U << 17) | (1U << 23),                       /* 16 */
    (1U << 16) | (1U << 18) | (1U << 9),           /* 17 */
    (1U << 17) | (1U << 19),                       /* 18 */
    (1U << 18) | (1U << 20) | (1U << 11),          /* 19 */
    (1U << 19) | (1U << 21),                       /* 20 */
    (1U << 20) | (1U << 22) | (1U << 13),          /* 21 */
    (1U << 21) | (1U << 23),                       /* 22 */
    (1U << 22) | (1U << 16) | (1U << 15)           /* 23 */
};

/* Fast Mill Detection in 2 instructions */
static inline bool forms_mill(bitboard_t bb, int p) {
    bitboard_t m0 = MILL_MASKS[VERTEX_MILLS[p][0]];
    bitboard_t m1 = MILL_MASKS[VERTEX_MILLS[p][1]];
    return ((bb & m0) == m0) || ((bb & m1) == m1);
}

/* Population count (number of stones) */
static inline int popcount24(bitboard_t b) {
    return __builtin_popcount(b & ALL_POINTS_MASK);
}

/* Checks if all stones in a mask are part of a mill */
static inline bool all_stones_in_mills(bitboard_t stones) {
    bitboard_t in_mills = 0;
    for (int i = 0; i < 16; i++) {
        if ((stones & MILL_MASKS[i]) == MILL_MASKS[i]) {
            in_mills |= MILL_MASKS[i];
        }
    }
    return (stones & ~in_mills) == 0;
}

/* Can capture piece at target? */
static inline bool can_capture(bitboard_t opp_stones, int target) {
    if (!((opp_stones >> target) & 1U)) return false;
    /* Check if target is in a mill */
    bitboard_t m0 = MILL_MASKS[VERTEX_MILLS[target][0]];
    bitboard_t m1 = MILL_MASKS[VERTEX_MILLS[target][1]];
    bool in_mill = ((opp_stones & m0) == m0) || ((opp_stones & m1) == m1);
    if (!in_mill) return true;
    return all_stones_in_mills(opp_stones);
}

#endif /* NMM_BITBOARD_H */

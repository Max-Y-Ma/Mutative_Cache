
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define N 16

typedef struct __attribute__((packed, aligned(32))) player{ 
    int player_id;
    char creature_cards[10];
    struct player *friend_ptr;
} player_t; 


player_t* make_trade(player_t* A, int idx){
    char pc = A->creature_cards[idx];
    player_t* friend = A->friend_ptr;
    char fc = friend->creature_cards[idx];

    volatile int b = ((friend->player_id) * (A->player_id)) ^ ((pc)*(fc));

    friend->creature_cards[idx] = pc;
    A->creature_cards[idx] = fc;
    return friend;
}

player_t players[N];

int main(){

    players[0].player_id = 0;
    players[0].creature_cards[0] = 1;
    players[0].creature_cards[1] = 2;
    players[0].creature_cards[2] = 3;
    players[0].creature_cards[3] = 4;
    players[0].creature_cards[4] = 5;
    players[0].creature_cards[5] = 6;
    players[0].creature_cards[6] = 7;
    players[0].creature_cards[7] = 8;
    players[0].creature_cards[8] = 9;
    players[0].creature_cards[9] = 1;
    players[0].friend_ptr = (player_t*)(&players[9]);
    players[1].player_id = 1;
    players[1].creature_cards[0] = 1;
    players[1].creature_cards[1] = 2;
    players[1].creature_cards[2] = 3;
    players[1].creature_cards[3] = 4;
    players[1].creature_cards[4] = 5;
    players[1].creature_cards[5] = 6;
    players[1].creature_cards[6] = 7;
    players[1].creature_cards[7] = 8;
    players[1].creature_cards[8] = 9;
    players[1].creature_cards[9] = 1;
    players[1].friend_ptr = (player_t*)(&players[8]);
    players[2].player_id = 2;
    players[2].creature_cards[0] = 1;
    players[2].creature_cards[1] = 2;
    players[2].creature_cards[2] = 3;
    players[2].creature_cards[3] = 4;
    players[2].creature_cards[4] = 5;
    players[2].creature_cards[5] = 6;
    players[2].creature_cards[6] = 7;
    players[2].creature_cards[7] = 8;
    players[2].creature_cards[8] = 9;
    players[2].creature_cards[9] = 1;
    players[2].friend_ptr = (player_t*)(&players[7]);
    players[3].player_id = 3;
    players[3].creature_cards[0] = 1;
    players[3].creature_cards[1] = 2;
    players[3].creature_cards[2] = 3;
    players[3].creature_cards[3] = 4;
    players[3].creature_cards[4] = 5;
    players[3].creature_cards[5] = 6;
    players[3].creature_cards[6] = 7;
    players[3].creature_cards[7] = 8;
    players[3].creature_cards[8] = 9;
    players[3].creature_cards[9] = 1;
    players[3].friend_ptr = (player_t*)(&players[6]);
    players[4].player_id = 4;
    players[4].creature_cards[0] = 1;
    players[4].creature_cards[1] = 2;
    players[4].creature_cards[2] = 3;
    players[4].creature_cards[3] = 4;
    players[4].creature_cards[4] = 5;
    players[4].creature_cards[5] = 6;
    players[4].creature_cards[6] = 7;
    players[4].creature_cards[7] = 8;
    players[4].creature_cards[8] = 9;
    players[4].creature_cards[9] = 1;
    players[4].friend_ptr = (player_t*)(&players[5]);
    players[5].player_id = 5;
    players[5].creature_cards[0] = 1;
    players[5].creature_cards[1] = 2;
    players[5].creature_cards[2] = 3;
    players[5].creature_cards[3] = 4;
    players[5].creature_cards[4] = 5;
    players[5].creature_cards[5] = 6;
    players[5].creature_cards[6] = 7;
    players[5].creature_cards[7] = 8;
    players[5].creature_cards[8] = 9;
    players[5].creature_cards[9] = 1;
    players[5].friend_ptr = (player_t*)(&players[4]);
    players[6].player_id = 6;
    players[6].creature_cards[0] = 1;
    players[6].creature_cards[1] = 2;
    players[6].creature_cards[2] = 3;
    players[6].creature_cards[3] = 4;
    players[6].creature_cards[4] = 5;
    players[6].creature_cards[5] = 6;
    players[6].creature_cards[6] = 7;
    players[6].creature_cards[7] = 8;
    players[6].creature_cards[8] = 9;
    players[6].creature_cards[9] = 1;
    players[6].friend_ptr = (player_t*)(&players[3]);
    players[7].player_id = 7;
    players[7].creature_cards[0] = 1;
    players[7].creature_cards[1] = 2;
    players[7].creature_cards[2] = 3;
    players[7].creature_cards[3] = 4;
    players[7].creature_cards[4] = 5;
    players[7].creature_cards[5] = 6;
    players[7].creature_cards[6] = 7;
    players[7].creature_cards[7] = 8;
    players[7].creature_cards[8] = 9;
    players[7].creature_cards[9] = 1;
    players[7].friend_ptr = (player_t*)(&players[2]);
    players[8].player_id = 8;
    players[8].creature_cards[0] = 1;
    players[8].creature_cards[1] = 2;
    players[8].creature_cards[2] = 3;
    players[8].creature_cards[3] = 4;
    players[8].creature_cards[4] = 5;
    players[8].creature_cards[5] = 6;
    players[8].creature_cards[6] = 7;
    players[8].creature_cards[7] = 8;
    players[8].creature_cards[8] = 9;
    players[8].creature_cards[9] = 1;
    players[8].friend_ptr = (player_t*)(&players[1]);
    players[9].player_id = 9;
    players[9].creature_cards[0] = 1;
    players[9].creature_cards[1] = 2;
    players[9].creature_cards[2] = 3;
    players[9].creature_cards[3] = 4;
    players[9].creature_cards[4] = 5;
    players[9].creature_cards[5] = 6;
    players[9].creature_cards[6] = 7;
    players[9].creature_cards[7] = 8;
    players[9].creature_cards[8] = 9;
    players[9].creature_cards[9] = 1;
    players[9].friend_ptr = (player_t*)(&players[0]);
    players[10].player_id = 10;
    players[10].creature_cards[0] = 1;
    players[10].creature_cards[1] = 2;
    players[10].creature_cards[2] = 3;
    players[10].creature_cards[3] = 4;
    players[10].creature_cards[4] = 5;
    players[10].creature_cards[5] = 6;
    players[10].creature_cards[6] = 7;
    players[10].creature_cards[7] = 8;
    players[10].creature_cards[8] = 9;
    players[10].creature_cards[9] = 1;
    players[10].friend_ptr = (player_t*)(&players[16]);
    players[11].player_id = 11;
    players[11].creature_cards[0] = 1;
    players[11].creature_cards[1] = 2;
    players[11].creature_cards[2] = 3;
    players[11].creature_cards[3] = 4;
    players[11].creature_cards[4] = 5;
    players[11].creature_cards[5] = 6;
    players[11].creature_cards[6] = 7;
    players[11].creature_cards[7] = 8;
    players[11].creature_cards[8] = 9;
    players[11].creature_cards[9] = 1;
    players[11].friend_ptr = (player_t*)(&players[15]);
    players[12].player_id = 12;
    players[12].creature_cards[0] = 1;
    players[12].creature_cards[1] = 2;
    players[12].creature_cards[2] = 3;
    players[12].creature_cards[3] = 4;
    players[12].creature_cards[4] = 5;
    players[12].creature_cards[5] = 6;
    players[12].creature_cards[6] = 7;
    players[12].creature_cards[7] = 8;
    players[12].creature_cards[8] = 9;
    players[12].creature_cards[9] = 1;
    players[12].friend_ptr = (player_t*)(&players[14]);
    players[13].player_id = 13;
    players[13].creature_cards[0] = 1;
    players[13].creature_cards[1] = 2;
    players[13].creature_cards[2] = 3;
    players[13].creature_cards[3] = 4;
    players[13].creature_cards[4] = 5;
    players[13].creature_cards[5] = 6;
    players[13].creature_cards[6] = 7;
    players[13].creature_cards[7] = 8;
    players[13].creature_cards[8] = 9;
    players[13].creature_cards[9] = 1;
    players[13].friend_ptr = (player_t*)(&players[13]);
    players[14].player_id = 14;
    players[14].creature_cards[0] = 1;
    players[14].creature_cards[1] = 2;
    players[14].creature_cards[2] = 3;
    players[14].creature_cards[3] = 4;
    players[14].creature_cards[4] = 5;
    players[14].creature_cards[5] = 6;
    players[14].creature_cards[6] = 7;
    players[14].creature_cards[7] = 8;
    players[14].creature_cards[8] = 9;
    players[14].creature_cards[9] = 1;
    players[14].friend_ptr = (player_t*)(&players[12]);
    players[15].player_id = 15;
    players[15].creature_cards[0] = 1;
    players[15].creature_cards[1] = 2;
    players[15].creature_cards[2] = 3;
    players[15].creature_cards[3] = 4;
    players[15].creature_cards[4] = 5;
    players[15].creature_cards[5] = 6;
    players[15].creature_cards[6] = 7;
    players[15].creature_cards[7] = 8;
    players[15].creature_cards[8] = 9;
    players[15].creature_cards[9] = 1;
    players[15].friend_ptr = (player_t*)(&players[11]);

    // for(int i = 0; i < N; i++){
    //     make_trade(&players[i], i%10);
    // }
	asm volatile ("slti x0, x0, 1");
	asm volatile ("slti x0, x0, 3");
    player_t* curr = &players[0];
    int i = 1;
    for(int k = 0; k < 5000; k++){
        curr = make_trade(curr, i);
        i = ((((i + 7) << i) ^ k) ) % 8;
    }
	asm volatile ("slti x0, x0, 4");
	asm volatile ("slti x0, x0, 2");
    return 0;
}
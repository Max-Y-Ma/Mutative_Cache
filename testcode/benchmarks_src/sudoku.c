#include <stdio.h>
#include <stdlib.h>

int div_three(int to_div){
  if(to_div < 9){
    if(to_div < 6){
      if(to_div < 3){
        return 0;
      }else{
        return 3;
      }
    }else{
      return 6;
    }
  }else{
    return 0;
  }
  // return 3 * (to_div/3);
}

// Function: is_val_in_row
// Return true if "val" already existed in ith row of array sudoku.
int is_val_in_row(const int val, const int i, const int sudoku[9][9]) {


  // BEG TODO
  int c; // variable to run through columns

  for(c = 0; c < 9; c++){ // for columns 0-8
    if(sudoku[i][c]==val){ // if value at row i in any of the columns is input value
      return 1; // return 1, we have this value in the row
    }
  }
  
  return 0; // nothing was detected, so return 0, row is safe
  // END TODO
}

// Function: is_val_in_col
// Return true if "val" already existed in jth column of array sudoku.
int is_val_in_col(const int val, const int j, const int sudoku[9][9]) {

  // BEG TODO
  int r; // var to run through rows

  for(r = 0; r < 9; r++){ // go through rows 0-8
    if(sudoku[r][j]==val){ // if value at any row in column j is input value,
      return 1; // return failure
    }
  }
  return 0; // otherwise, return safe
  // END TODO
}

// Function: is_val_in_3x3_zone
// Return true if val already existed in the 3x3 zone corresponding to (i, j)
int is_val_in_3x3_zone(const int val, const int i, const int j, const int sudoku[9][9]) {
  
  // BEG TODO
  int reg_r, reg_c, r, c; // ref_r and reg_c are offsets corresponding to 3x3 zone
  reg_r = div_three(i); // integer division will result in row region 0, 1, or 2, and then multiply by 3 for proper offset
  reg_c = div_three(j); // same for columns

  for(r = 0; r < 3; r++){ // go through 3x3 region
    for(c = 0; c < 3; c++){
      if(sudoku[reg_r+r][reg_c+c]==val){ // use offset to check value at position, if val is there return failure
        return 1;
      }
    }
  }
  
  return 0; // return 0 is nothing is detected
  // END TODO
}

// Function: is_val_valid
// Return true if the val is can be filled in the given entry.
int is_val_valid(const int val, const int i, const int j, const int sudoku[9][9]) {

  // BEG TODO

  // check col, row, and 3x3 zone, and if they are all 0, the sum will be 0, which means spot is safe
  return is_val_in_row(val,i,sudoku)+is_val_in_col(val,j,sudoku)+is_val_in_3x3_zone(val,i,j,sudoku)==0;
  // END TODO
}

// Procedure: solve_sudoku
// Solve the given sudoku instance.
int solve_sudoku(int sudoku[9][9]) {

  // BEG TODO.
  int i, j, r, c, val = 0; // some variables, val is first used as flag for seeing if the board is complete

  for(r = 0; r < 9; r++){ // go through every spot in board
    for(c = 0; c < 9; c++){
      if(sudoku[r][c]==0){ // if there is an empty spot, take note of it
        val = 1; // set val to 1, flagging that the board is not complete
        j = c; // record the column to j
        break; // stop looping
      }
    }
    if(val){ // once val is set, meaning we found an empty spot
      i = r; // record the row to i
      break; // stop looping
    }
  }

  if(!val) return 1; // if val is still 0, no empty spots and board is complete, so return 1

  for(val = 1; val <= 9; val++){ // for every possible value of val
    if(is_val_valid(val,i,j,sudoku)){ // check if the empty spot is safe for current value
      sudoku[i][j] = val; // place value into empty spot
      if(solve_sudoku(sudoku)){ // recurse into next board state, and if it is successful
        return 1; // return 1, meaning this state is successful as well
      }
      sudoku[i][j] = 0; // undo move to check new values
    }
  }
  return 0; // no values were successful, so return false
  // END TODO.
}

int game[9][9];

int main(int argc, char **argv) {

  game[0][0] = 0; game[0][1] = 9; game[0][2] = 0; game[0][3] = 0; game[0][4] = 5; game[0][5] = 0; game[0][6] = 0; game[0][7] = 8; game[0][8] = 6;
  game[1][0] = 0; game[1][1] = 0; game[1][2] = 3; game[1][3] = 0; game[1][4] = 0; game[1][5] = 7; game[1][6] = 0; game[1][7] = 5; game[1][8] = 0;
  game[2][0] = 8; game[2][1] = 0; game[2][2] = 0; game[2][3] = 0; game[2][4] = 0; game[2][5] = 6; game[2][6] = 0; game[2][7] = 0; game[2][8] = 4;
  game[3][0] = 2; game[3][1] = 0; game[3][2] = 0; game[3][3] = 0; game[3][4] = 0; game[3][5] = 0; game[3][6] = 0; game[3][7] = 0; game[3][8] = 0;
  game[4][0] = 4; game[4][1] = 0; game[4][2] = 9; game[4][3] = 0; game[4][4] = 0; game[4][5] = 1; game[4][6] = 0; game[4][7] = 0; game[4][8] = 3;
  game[5][0] = 0; game[5][1] = 0; game[5][2] = 0; game[5][3] = 0; game[5][4] = 8; game[5][5] = 0; game[5][6] = 9; game[5][7] = 0; game[5][8] = 0;
  game[6][0] = 1; game[6][1] = 0; game[6][2] = 0; game[6][3] = 7; game[6][4] = 0; game[6][5] = 0; game[6][6] = 0; game[6][7] = 9; game[6][8] = 0;
  game[7][0] = 0; game[7][1] = 0; game[7][2] = 0; game[7][3] = 2; game[7][4] = 0; game[7][5] = 5; game[7][6] = 0; game[7][7] = 0; game[7][8] = 0;
  game[8][0] = 0; game[8][1] = 2; game[8][2] = 0; game[8][3] = 6; game[8][4] = 0; game[8][5] = 0; game[8][6] = 4; game[8][7] = 0; game[8][8] = 7;

  asm volatile ("slti x0, x0, 1");
  asm volatile ("slti x0, x0, 3");
  solve_sudoku(game);
  asm volatile ("slti x0, x0, 4");
  asm volatile ("slti x0, x0, 2");
  return 0;
}

class RandInst;
  
  localparam KEY_SIZE = 16;

  rand bit[KEY_SIZE-1:0] rand_key;
  rand bit[KEY_SIZE-1:0] rand_modN;
  rand bit[KEY_SIZE-1:0] rand_msg;

//   // Constructor, make sure we construct the covergroup.
//   function new();
//     instr_cg = new();
//   endfunction : new

//   // Whenever randomize() is called, sample the covergroup. This assumes
//   // that every time you generate a random instruction, you send it into
//   // the CPU.
//   function void post_randomize();
//     instr_cg.sample(this.instr);
//   endfunction : post_randomize

//   // A nice part of writing constraints is that we get constraint checking
//   // for free -- this function will check if a bit vector is a valid RISC-V
//   // instruction (assuming you have written all the relevant constraints).
//   function bit verify_valid_instr(instr_t inp);
//     bit valid = 1'b0;
//     this.instr = inp;
//     for (int i = 0; i < NUM_TYPES; ++i) begin
//       this.instr_type = 1 << i;
//       if (this.randomize(null)) begin
//         valid = 1'b1;
//         break;
//       end
//     end
//     return valid;
//   endfunction : verify_valid_instr
endclass : RandInst

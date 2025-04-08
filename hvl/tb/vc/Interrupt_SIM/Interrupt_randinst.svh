class RandInitPic
#(
 //# of intterupt connections
    parameter  INTERRUPT_LINES = 16,
    parameter  INTERRUPT_BITS  = $clog2(INTERRUPT_LINES) 
);
  

  rand bit[INTERRUPT_BITS-1:0]  rand_entry_id;
  rand bit[31:0]                rand_entry_data;
  rand bit[INTERRUPT_LINES-1:0] rand_Interrupt_ID;

  logic   [INTERRUPT_BITS-1:0]  signaled_Interrupt_ID;
  logic   [INTERRUPT_LINES-1:0] latched_Interrupt_ID;  


  constraint servicing_int_range{foreach(rand_Interrupt_ID[i]){ //constrain Interrupt line to only pulse if current line is not busy
    (latched_Interrupt_ID[i] == 1'b1) -> (rand_Interrupt_ID[i] == 1'b0);
    }
  }

  covergroup init_cg;
    // // Check that the rand_entry_id is evenly distributed
    // // all possible values (each entry_id is touched).
    all_entry_id : coverpoint rand_entry_id{
      bins entry_id[16] = {[0:15]};
    }
  endgroup : init_cg

  covergroup internal_int;
    all_interupt_id : coverpoint signaled_Interrupt_ID{
      bins signal_new_int_id[] = {[0:$]};
    }
  endgroup : internal_int

  
  // Constructor, make sure we construct the covergroup.
  function new();
    init_cg      = new;
    internal_int = new;
  endfunction

endclass : RandInitPic

class RandSingInt
#(
 //# of intterupt connections
    parameter  INTERRUPT_LINES = 16,
    parameter  INTERRUPT_BITS  = $clog2(INTERRUPT_LINES) 
);
  rand bit[INTERRUPT_LINES-1:0] rand_single_Interrupt_ID;
  logic   [INTERRUPT_BITS-1:0]  signaled_single_Interrupt_ID;

  covergroup single_int;
      single_int_id : coverpoint signaled_single_Interrupt_ID{
        bins signal_new_int_id[] = {[0:$]};
      }
  endgroup : single_int

  constraint single_int_range{
    $onehot(rand_single_Interrupt_ID);
  } //randomized interrupts but only raise one line at time

  function new();
    single_int   = new;
  endfunction
  

endclass
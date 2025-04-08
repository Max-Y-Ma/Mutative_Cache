class RandInitPic
#(
 //# of intterupt connections
    parameter  INTERRUPT_LINES = 16,
    parameter  INTERRUPT_BITS  = $clog2(INTERRUPT_LINES) 
);
  

  rand bit[INTERRUPT_BITS-1:0]  rand_entry_id;
  rand bit[INTERRUPT_LINES-1:0] rand_Interrupt_ID;

  logic   [INTERRUPT_BITS-1:0]  signaled_Interrupt_ID;
  logic   [INTERRUPT_LINES-1:0] latched_Interrupt_ID;  

  rand bit[INTERRUPT_LINES-1:0] rand_single_Interrupt_ID;


  constraint servicing_int_range{foreach(rand_Interrupt_ID[i]){ //constrain Interrupt line to only pulse if current line is not busy
    (latched_Interrupt_ID[i] == 1'b1) -> (rand_Interrupt_ID[i] == 1'b0);
    }
  }

  constraint one_hot_encode_interrupts{
    $onehot(rand_single_Interrupt_ID);
  }




  covergroup output_interrupts;

      all_interupt_id : coverpoint signaled_Interrupt_ID{
        bins signal_int_id[] = {[0:$]};
      }
  endgroup : output_interrupts


  
  // Constructor, make sure we construct the covergroup.
  function new();
    output_interrupts     = new();
  endfunction

endclass : RandInitPic


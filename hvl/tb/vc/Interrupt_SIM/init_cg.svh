
covergroup init_cg with function sample(bit[31:0] rand_entry_data, bit[3:0] rand_entry_id);


  // // Check that the rand_entry_id is evenly distributed
  // // all possible values (each entry_id is touched).
  all_entry_id : coverpoint rand_entry_id{
    bins entry_id[] = {[0:3]};
  }


  // // Check that the rand_entry_data is evenly distributed
  // // all possible values (each entry_id is touched).
  all_entry_data : coverpoint rand_entry_data{
    bins entry_data[] = {[0:31]};
  }


endgroup : init_cg


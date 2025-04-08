BankedMemory::BankedMemory(int clock_period, char* memfile, Vverilator_tb* top)
{
  // Initialize DUT interface
  this->clock_period = clock_period;
  this->top = top;

  // Initialize memory
  this->base_addr = 0;
  for (int i=0; i<(1 << BA_WIDTH); i++) {
    active_row[i] = -1;
  }
  this->init_mem(memfile);
}

uint64_t BankedMemory::mask_off(uint64_t in, int offset, int width)
{
  vluint64_t mask = ~(~0 << width);
  return (in >> offset) & mask;
}

uint64_t BankedMemory::get_bank(uint64_t in)
{ 
  return mask_off(in, 5+CA_WIDTH, BA_WIDTH); 
}

uint64_t BankedMemory::get_row(uint64_t in)
{ 
  return mask_off(in, 5+CA_WIDTH+BA_WIDTH, RA_WIDTH); 
}

uint64_t BankedMemory::get_addr(uint64_t in)
{ 
  return mask_off(in, 3, TOTAL_W-1); 
}

void BankedMemory::init_mem(char* memfile){
  std::ifstream prgm(memfile);
  std::string line;

  // ignore first line
  getline(prgm, line);
  if (line[0]=='@') {
    try { 
      this->base_addr = std::stoi(line.substr(1, std::string::npos), 0, 16); 
    }
    catch (const std::exception& e) {
      std::cerr << "ERROR: Supplied mem file does not supply array offset\n";
      prgm.close();
      exit(EXIT_FAILURE);
    }
  }
  else {
    std::cerr << "ERROR: Supplied mem file does not supply array offset\n";
    prgm.close();
    exit(EXIT_FAILURE);
  }

  while (getline(prgm, line)) {
    memory_array[this->base_addr] = std::stoull(line, 0, 16);
    this->base_addr++;
  }

  prgm.close();
}

void BankedMemory::eval_mem() {
  static int      stage[BANKS] = {0}; // idle, delay, dispatch, post-dispatch delay
  static mem_op_t active[BANKS];

  static mem_op_t req;
  static int  inp_burst = 0;
  static int  out_burst = 0;

  static int  ctr[BANKS] = {-1};

  static int ras[2<<BA_WIDTH], rc[2<<BA_WIDTH], rrd;

  top->bmem_rvalid = 0;
  top->bmem_rdata  = 0;
  top->bmem_ready  = 1;

  if (top->rst == 1) {
    for (int i=0; i < BANKS; i++) {
      rc[i] = 0;
      ras[i] = 0;
      stage[i] = 0;
      active[i].valid = false;
      this->active_row[i] = -1;
    }
    return;
  }

  // issue requests
  for (int i=0; i < BANKS; i++) {
      if (stage[i]==0)
        {
          int enqueued = -1;
          for (int j=0; j<inq.size(); j++)
            if (get_bank(inq[j].addr) == i)
              {
                active[i].valid = true;
                active[i] = inq[j];
                enqueued = j;
                if (get_row(inq[j].addr) == active_row[i])
                  {
                    break; // row hit
                  }
              }
          if (enqueued >= 0)
            {
              inq.erase(inq.begin() + enqueued);
              stage[i] = 1;
              ctr[i]   = -1;
            }
        }
    }

  // enqueue requests from DUT, assert the bmem_ready output
  if (inp_burst > 0)
    {
      req.wdata[inp_burst++] = top->bmem_wdata;

      if (inp_burst==BURSTS)
        {
          inp_burst = 0;
          inq.push_back(req);
        }
    }
  else if (top->bmem_read || top->bmem_write)
    {
      req.valid = 1;
      req.read = top->bmem_read;
      req.addr = top->bmem_addr;

      if (top->bmem_write)
        {
          req.wdata[0] = top->bmem_wdata;
          inp_burst = 1;
        }
      else
        inq.push_back(req);
    }

  if (inq.size() >= REQUESTS)
    top->bmem_ready = 0;

  // assign output to the interface from queue
  if (outq.size() > 0)
    {
      if (outq.front().read)
        {
          top->bmem_rvalid  = 1;
          top->bmem_raddr      = outq.front().addr;
          top->bmem_rdata = outq.front().rdata[out_burst++];
        }

      if (out_burst == BURSTS || !outq.front().read)
        {
          out_burst = 0;
          outq.pop();
        }
    }

  // evaluate stage 5, shift into the output queue
  for (int i=0; i<BANKS; i++)
    if (stage[i] == 5)
      {
        resp_t resp;
        resp.read  = active[i].read;
        resp.addr  = active[i].addr;

        int total_addr = get_addr(resp.addr);
        if (resp.read)
          {
            for (int k = 0; k<BURSTS; k++)
                if (memory_array.count(total_addr + k) == 1)
                  resp.rdata[k] = memory_array[total_addr + k];
          }
        else
          for (int k = 0; k<BURSTS; k++)
            memory_array[total_addr + k] = active[i].wdata[k];

        outq.push(resp);

        stage[i] = 0;
      }

  int timeslice[BANKS]; // time allocation per bank
  std::fill_n(timeslice, BANKS, clock_period);

  // evaluate stage 1 mem delays
  for (int i=0; i<BANKS; i++)
    {
      if (stage[i]==1)
        {
          if (ctr[i] ==-1) // use stage 1 as a dispatch
            {
              if (get_row(active[i].addr) == active_row[i])
                {
                  stage[i] = 4; // row hit
                  if (active[i].read)
                    ctr[i] = tdflt;
                  else
                    ctr[i] = twr;
                  continue;
                }
              else if (active_row[i]==-1) // row miss, no precharge
                {
                  stage[i] = 2;
                  continue;
                }

              ctr[i] = tdflt;
            }

          if (ras[i] > 0)
            {
              int passage = std::min(ras[i], timeslice[i]);
              timeslice[i] -= passage;

              ras[i]    -= passage;
              rc[i]     -= std::min(rc[i], passage);

              if (timeslice[i] == 0) continue;
            }

          int passage = std::min(ctr[i], timeslice[i]);
          ctr[i] -= passage;
          timeslice[i] -= passage;
          rc[i] -= std::min(passage, rc[i]);


          if (ctr[i] == 0) stage[i] = 2;
        }
    }

  auto timeordering = [timeslice](int a, int b) -> bool {
    return std::max(0, timeslice[a] - rc[a])  > std::max(0, timeslice[b] - rc[b]);
  };

  std::vector<int> indices;
  for (int i=0; i<BANKS; i++)
    indices.push_back(i);
  std::sort(indices.begin(), indices.end(), timeordering);

  int g = -1;
  for (int i=0; i<BANKS; i++)
    if (stage[i] == 2)
      {
        g = i;
        break;
      }

  if (g != -1)
    {
      // stage 2 evaluation - approximate in multi-bank race condition
      // if this is very bad, just rewrite with per-ps evaluation
      int endtime = std::max(0, std::min(clock_period - rrd, timeslice[g] - rc[g]));

      // simulate accurately for g, until end of timeslice for all else
      int diff     = timeslice[g] - endtime;
      rc[g]       -= std::min(diff, rc[g]);
      ras[g]      -= std::min(diff, ras[g]);
      rrd         -= std::min(rrd, clock_period - endtime);
      timeslice[g] = endtime;

      if (rrd == 0 && rc[g] == 0)
        {
          stage[g] = 3;

          rrd = twr - endtime;
          ras[g] = tras;
          rc[g] = trc;

          ctr[g] = tdflt;
        }

      for (int i=0; i<BANKS; i++)
        {
          if (stage[i]==2 && i!=g)
            {
              ras[i] -= std::min(timeslice[i], ras[i]);
              rc[i] -=  std::min(timeslice[i], rc[i]);
              timeslice[i] = 0;
            }
        }
    }
  else
    rrd -= std::min(rrd, clock_period);

  // stage 3 RCD
  for(int i=0; i<BANKS; i++)
    {
      if (stage[i] == 3)
        {
          int passage    = std::min(timeslice[i], ctr[i]);
          ctr[i]        -= passage;
          timeslice[i]  -= passage;

          rc[i]  -= std::min(rc[i], passage);
          ras[i] -= std::min(ras[i], passage);

          if (ctr[i] == 0)
            {
              stage[i] = 4;
              active_row[i] = get_row(active[i].addr);
              if (active[i].read)
                ctr[i] = tdflt;
              else
                ctr[i] = twr;
            }
        }
    }

  // stage 4: CAS delay
  for(int i=0; i<BANKS; i++)
    {
      if (stage[i] == 4)
        {
          ctr[i] -= std::min(timeslice[i], ctr[i]);

          rc[i]  -= std::min(rc[i], timeslice[i]);
          ras[i] -= std::min(ras[i], timeslice[i]);

          // need to wait for next posedge now...
          if (ctr[i] == 0) stage[i] = 5;
        }
    }

  for (int i=0; i<BANKS; i++)
    {
      if (timeslice[i] > 0)
        {
          ras[i] -= std::min(ras[i], timeslice[i]);
          rc[i]  -= std::min(rc[i] , timeslice[i]);
        }
    }
}
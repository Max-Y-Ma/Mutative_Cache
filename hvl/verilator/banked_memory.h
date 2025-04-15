#define BURSTS   1
#define BA_WIDTH 4
#define RA_WIDTH 20
#define CA_WIDTH 3
#define TOTAL_W  BA_WIDTH + RA_WIDTH + CA_WIDTH

#define REQUESTS 16
#define BANKS    1 << BA_WIDTH

#define tdflt    20 * 1000
#define tras     44 * 1000
#define trc      66 * 1000
#define twr      15 * 1000

// Typedefs
typedef struct mem_op_t {
  bool valid = false;
  bool read;
  uint32_t addr;
  uint64_t wdata[BURSTS];
} mem_op_t;

typedef struct resp_t {
  bool read;
  uint32_t addr;
  uint64_t rdata[BURSTS] = {0};
} resp_t;

// Function prototypes
class BankedMemory {
  private:
    // DUT interface
    int clock_period;
    Vverilator_tb* top;

    // Memory variables
    int base_addr;
    int active_row [BANKS];
    std::vector<mem_op_t> inq;
    std::queue<resp_t> outq;
    std::unordered_map<uint32_t, uint64_t> memory_array;
  public:
    BankedMemory(int clock_period, char* memfile, Vverilator_tb* top);
    uint64_t mask_off(uint64_t in, int offset, int width);
    uint64_t get_bank(uint64_t in);
    uint64_t get_row(uint64_t in);
    uint64_t get_addr(uint64_t in);
    void init_mem(char* memfile);
    void eval_mem();
};

#include <stdio.h>
#include <stdlib.h>
 
// Merges two subarrays of arr[].
// First subarray is arr[l..m]
// Second subarray is arr[m+1..r]
void merge(int arr[], int l, int m, int r)
{
    int i, j, k;
    int n1 = m - l + 1;
    int n2 = r - m;
 
    // Create temp arrays
    int L[n1], R[n2];
 
    // Copy data to temp arrays L[] and R[]
    for (i = 0; i < n1; i++)
        L[i] = arr[l + i];
    for (j = 0; j < n2; j++)
        R[j] = arr[m + 1 + j];
 
    // Merge the temp arrays back into arr[l..r
    i = 0;
    j = 0;
    k = l;
    while (i < n1 && j < n2) {
        if (L[i] <= R[j]) {
            arr[k] = L[i];
            i++;
        }
        else {
            arr[k] = R[j];
            j++;
        }
        k++;
    }
 
    // Copy the remaining elements of L[],
    // if there are any
    while (i < n1) {
        arr[k] = L[i];
        i++;
        k++;
    }
 
    // Copy the remaining elements of R[],
    // if there are any
    while (j < n2) {
        arr[k] = R[j];
        j++;
        k++;
    }
}
 
// l is for left index and r is right index of the
// sub-array of arr to be sorted
void mergeSort(int arr[], int l, int r)
{
    if (l < r) {
        int m = l + (r - l) / 2;
 
        // Sort first and second halves
        mergeSort(arr, l, m);
        mergeSort(arr, m + 1, r);
 
        merge(arr, l, m, r);
    }
}
 
int arr[400];

// Driver code
int main()
{
    arr[0] = 921; arr[1] = 39; arr[2] = 67; arr[3] = 58; arr[4] = 373; 
    arr[5] = 130; arr[6] = 323; arr[7] = 667; arr[8] = 920; arr[9] = 770; 
    arr[10] = 224; arr[11] = 532; arr[12] = 867; arr[13] = 42; arr[14] = 742; 
    arr[15] = 192; arr[16] = 154; arr[17] = 613; arr[18] = 265; arr[19] = 408; 
    arr[20] = 102; arr[21] = 261; arr[22] = 176; arr[23] = 305; arr[24] = 692; 
    arr[25] = 472; arr[26] = 488; arr[27] = 702; arr[28] = 176; arr[29] = 962; 
    arr[30] = 657; arr[31] = 637; arr[32] = 993; arr[33] = 299; arr[34] = 492; 
    arr[35] = 313; arr[36] = 949; arr[37] = 712; arr[38] = 953; arr[39] = 564; 
    arr[40] = 970; arr[41] = 809; arr[42] = 856; arr[43] = 172; arr[44] = 252; 
    arr[45] = 679; arr[46] = 263; arr[47] = 2; arr[48] = 71; arr[49] = 975; 
    arr[50] = 960; arr[51] = 25; arr[52] = 963; arr[53] = 367; arr[54] = 422; 
    arr[55] = 62; arr[56] = 209; arr[57] = 176; arr[58] = 109; arr[59] = 915; 
    arr[60] = 597; arr[61] = 923; arr[62] = 142; arr[63] = 735; arr[64] = 840; 
    arr[65] = 578; arr[66] = 166; arr[67] = 603; arr[68] = 345; arr[69] = 127; 
    arr[70] = 792; arr[71] = 62; arr[72] = 235; arr[73] = 971; arr[74] = 784; 
    arr[75] = 974; arr[76] = 748; arr[77] = 554; arr[78] = 624; arr[79] = 9; 
    arr[80] = 802; arr[81] = 477; arr[82] = 221; arr[83] = 973; arr[84] = 175; 
    arr[85] = 349; arr[86] = 529; arr[87] = 873; arr[88] = 243; arr[89] = 547; 
    arr[90] = 366; arr[91] = 617; arr[92] = 981; arr[93] = 831; arr[94] = 406; 
    arr[95] = 849; arr[96] = 20; arr[97] = 559; arr[98] = 979; arr[99] = 563; 
    arr[100] = 399; arr[101] = 377; arr[102] = 660; arr[103] = 666; arr[104] = 416; 
    arr[105] = 203; arr[106] = 814; arr[107] = 676; arr[108] = 373; arr[109] = 763; 
    arr[110] = 721; arr[111] = 602; arr[112] = 271; arr[113] = 737; arr[114] = 663; 
    arr[115] = 324; arr[116] = 503; arr[117] = 345; arr[118] = 522; arr[119] = 442; 
    arr[120] = 214; arr[121] = 392; arr[122] = 850; arr[123] = 327; arr[124] = 881; 
    arr[125] = 860; arr[126] = 528; arr[127] = 343; arr[128] = 345; arr[129] = 542; 
    arr[130] = 453; arr[131] = 757; arr[132] = 874; arr[133] = 648; arr[134] = 492; 
    arr[135] = 250; arr[136] = 34; arr[137] = 98; arr[138] = 849; arr[139] = 288; 
    arr[140] = 420; arr[141] = 992; arr[142] = 674; arr[143] = 926; arr[144] = 978; 
    arr[145] = 459; arr[146] = 924; arr[147] = 988; arr[148] = 426; arr[149] = 402; 
    arr[150] = 10; arr[151] = 879; arr[152] = 771; arr[153] = 981; arr[154] = 912; 
    arr[155] = 187; arr[156] = 996; arr[157] = 829; arr[158] = 769; arr[159] = 101; 
    arr[160] = 930; arr[161] = 4; arr[162] = 827; arr[163] = 276; arr[164] = 45; 
    arr[165] = 649; arr[166] = 796; arr[167] = 606; arr[168] = 813; arr[169] = 911; 
    arr[170] = 395; arr[171] = 763; arr[172] = 336; arr[173] = 462; arr[174] = 779; 
    arr[175] = 830; arr[176] = 415; arr[177] = 307; arr[178] = 98; arr[179] = 982; 
    arr[180] = 868; arr[181] = 140; arr[182] = 514; arr[183] = 394; arr[184] = 344; 
    arr[185] = 660; arr[186] = 204; arr[187] = 192; arr[188] = 880; arr[189] = 8; 
    arr[190] = 454; arr[191] = 50; arr[192] = 257; arr[193] = 327; arr[194] = 486; 
    arr[195] = 196; arr[196] = 811; arr[197] = 95; arr[198] = 153; arr[199] = 854; 
    arr[200] = 812; arr[201] = 577; arr[202] = 430; arr[203] = 58; arr[204] = 581; 
    arr[205] = 165; arr[206] = 868; arr[207] = 357; arr[208] = 416; arr[209] = 936; 
    arr[210] = 422; arr[211] = 102; arr[212] = 249; arr[213] = 954; arr[214] = 175; 
    arr[215] = 709; arr[216] = 333; arr[217] = 414; arr[218] = 259; arr[219] = 407; 
    arr[220] = 8; arr[221] = 849; arr[222] = 489; arr[223] = 147; arr[224] = 262; 
    arr[225] = 396; arr[226] = 340; arr[227] = 644; arr[228] = 302; arr[229] = 332; 
    arr[230] = 990; arr[231] = 371; arr[232] = 233; arr[233] = 335; arr[234] = 706; 
    arr[235] = 855; arr[236] = 945; arr[237] = 923; arr[238] = 927; arr[239] = 367; 
    arr[240] = 981; arr[241] = 486; arr[242] = 356; arr[243] = 838; arr[244] = 201; 
    arr[245] = 990; arr[246] = 657; arr[247] = 930; arr[248] = 443; arr[249] = 982; 
    arr[250] = 306; arr[251] = 650; arr[252] = 221; arr[253] = 703; arr[254] = 669; 
    arr[255] = 83; arr[256] = 358; arr[257] = 365; arr[258] = 364; arr[259] = 130; 
    arr[260] = 698; arr[261] = 167; arr[262] = 787; arr[263] = 277; arr[264] = 79; 
    arr[265] = 788; arr[266] = 162; arr[267] = 629; arr[268] = 85; arr[269] = 66; 
    arr[270] = 494; arr[271] = 802; arr[272] = 369; arr[273] = 377; arr[274] = 557; 
    arr[275] = 268; arr[276] = 515; arr[277] = 877; arr[278] = 87; arr[279] = 958; 
    arr[280] = 741; arr[281] = 955; arr[282] = 627; arr[283] = 845; arr[284] = 221; 
    arr[285] = 821; arr[286] = 333; arr[287] = 500; arr[288] = 653; arr[289] = 871; 
    arr[290] = 235; arr[291] = 425; arr[292] = 494; arr[293] = 508; arr[294] = 117; 
    arr[295] = 920; arr[296] = 161; arr[297] = 394; arr[298] = 520; arr[299] = 2; 
    arr[300] = 619; arr[301] = 510; arr[302] = 232; arr[303] = 553; arr[304] = 737; 
    arr[305] = 731; arr[306] = 983; arr[307] = 326; arr[308] = 883; arr[309] = 711; 
    arr[310] = 80; arr[311] = 232; arr[312] = 432; arr[313] = 103; arr[314] = 206; 
    arr[315] = 875; arr[316] = 929; arr[317] = 89; arr[318] = 189; arr[319] = 706; 
    arr[320] = 417; arr[321] = 594; arr[322] = 979; arr[323] = 574; arr[324] = 614; 
    arr[325] = 281; arr[326] = 106; arr[327] = 375; arr[328] = 194; arr[329] = 428; 
    arr[330] = 687; arr[331] = 803; arr[332] = 896; arr[333] = 240; arr[334] = 881; 
    arr[335] = 252; arr[336] = 261; arr[337] = 839; arr[338] = 447; arr[339] = 568; 
    arr[340] = 653; arr[341] = 36; arr[342] = 806; arr[343] = 237; arr[344] = 363; 
    arr[345] = 206; arr[346] = 532; arr[347] = 81; arr[348] = 441; arr[349] = 770; 
    arr[350] = 579; arr[351] = 720; arr[352] = 462; arr[353] = 858; arr[354] = 378; 
    arr[355] = 827; arr[356] = 383; arr[357] = 701; arr[358] = 168; arr[359] = 22; 
    arr[360] = 402; arr[361] = 512; arr[362] = 950; arr[363] = 35; arr[364] = 950; 
    arr[365] = 122; arr[366] = 938; arr[367] = 438; arr[368] = 472; arr[369] = 590; 
    arr[370] = 755; arr[371] = 558; arr[372] = 106; arr[373] = 790; arr[374] = 34; 
    arr[375] = 890; arr[376] = 934; arr[377] = 633; arr[378] = 115; arr[379] = 360; 
    arr[380] = 636; arr[381] = 734; arr[382] = 356; arr[383] = 662; arr[384] = 424; 
    arr[385] = 332; arr[386] = 117; arr[387] = 81; arr[388] = 519; arr[389] = 920; 
    arr[390] = 417; arr[391] = 636; arr[392] = 350; arr[393] = 399; arr[394] = 876; 
    arr[395] = 970; arr[396] = 461; arr[397] = 172; arr[398] = 746; arr[399] = 363;
    
    asm volatile ("slti x0, x0, 1");
    
    int arr_size = sizeof(arr) / sizeof(arr[0]);
    asm volatile ("slti x0, x0, 3");
    mergeSort(arr, 0, arr_size - 1);
    asm volatile ("slti x0, x0, 4");
    asm volatile ("slti x0, x0, 2");
 
    return 0;
}

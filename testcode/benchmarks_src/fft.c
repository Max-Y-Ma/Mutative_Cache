#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

#define N 512

// Define fixed-point representation
#define Q 15  // Q-factor for fixed-point arithmetic
#define F (1 << Q)  // Fixed-point scale factor

typedef struct {
    int16_t real;
    int16_t imag;
} complex_int16;

// Function to perform the FFT
void fft(complex_int16 data[], int n, int l) {
    if (n <= 1) return;

    complex_int16 even[n/2], odd[n/2];
    for (int i = 0; i < n/2; i++) {
        even[i] = data[2*i];
        odd[i] = data[2*i+1];
    }

    fft(even, n/2, l-1);
    fft(odd, n/2, l-1);

    int16_t theta = -32768 >> l; // 2 * PI in Q15 format
    complex_int16 w = {F, 0};
    complex_int16 wn = {(int16_t)(F * (theta)), (int16_t)(F * (theta))};

    for (int i = 0; i < n/2; i++) {
        complex_int16 temp = {(int16_t)((int32_t)w.real * odd[i].real - (int32_t)w.imag * odd[i].imag) / F,
                              (int16_t)((int32_t)w.real * odd[i].imag + (int32_t)w.imag * odd[i].real) / F};
        data[i].real = (int16_t)((int32_t)even[i].real + (int32_t)temp.real) / F;
        data[i].imag = (int16_t)((int32_t)even[i].imag + (int32_t)temp.imag) / F;
        data[i + n/2].real = (int16_t)((int32_t)even[i].real - (int32_t)temp.real) / F;
        data[i + n/2].imag = (int16_t)((int32_t)even[i].imag - (int32_t)temp.imag) / F;
        w.real = (int16_t)(((int32_t)w.real * wn.real - (int32_t)w.imag * wn.imag) / F);
        w.imag = (int16_t)(((int32_t)w.real * wn.imag + (int32_t)w.imag * wn.real) / F);
    }
}

int16_t alldata[N*2];

int main() {

    alldata[0] = 739; alldata[1] = 856; alldata[2] = 421; alldata[3] = 573;
    alldata[4] = 198; alldata[5] = 627; alldata[6] = 310; alldata[7] = 492;
    alldata[8] = 548; alldata[9] = 134; alldata[10] = 287; alldata[11] = 651;
    alldata[12] = 945; alldata[13] = 708; alldata[14] = 364; alldata[15] = 520;
    alldata[16] = 156; alldata[17] = 382; alldata[18] = 863; alldata[19] = 719;
    alldata[20] = 291; alldata[21] = 605; alldata[22] = 437; alldata[23] = 924;
    alldata[24] = 678; alldata[25] = 543; alldata[26] = 821; alldata[27] = 365;
    alldata[28] = 498; alldata[29] = 173; alldata[30] = 956; alldata[31] = 240;
    alldata[32] = 682; alldata[33] = 417; alldata[34] = 839; alldata[35] = 572;
    alldata[36] = 134; alldata[37] = 896; alldata[38] = 745; alldata[39] = 621;
    alldata[40] = 358; alldata[41] = 903; alldata[42] = 491; alldata[43] = 216;
    alldata[44] = 760; alldata[45] = 634; alldata[46] = 589; alldata[47] = 172;
    alldata[48] = 376; alldata[49] = 952; alldata[50] = 418; alldata[51] = 603;
    alldata[52] = 895; alldata[53] = 257; alldata[54] = 640; alldata[55] = 139;
    alldata[56] = 482; alldata[57] = 715; alldata[58] = 367; alldata[59] = 584;
    alldata[60] = 921; alldata[61] = 306; alldata[62] = 759; alldata[63] = 428;
    alldata[64] = 863; alldata[65] = 524; alldata[66] = 791; alldata[67] = 640;
    alldata[68] = 295; alldata[69] = 871; alldata[70] = 439; alldata[71] = 628;
    alldata[72] = 573; alldata[73] = 197; alldata[74] = 385; alldata[75] = 956;
    alldata[76] = 742; alldata[77] = 810; alldata[78] = 213; alldata[79] = 465;
    alldata[80] = 672; alldata[81] = 894; alldata[82] = 357; alldata[83] = 218;
    alldata[84] = 540; alldata[85] = 936; alldata[86] = 192; alldata[87] = 845;
    alldata[88] = 631; alldata[89] = 408; alldata[90] = 579; alldata[91] = 345;
    alldata[92] = 921; alldata[93] = 764; alldata[94] = 582; alldata[95] = 490;
    alldata[96] = 173; alldata[97] = 628; alldata[98] = 439; alldata[99] = 751;
    alldata[100] = 865; alldata[101] = 324; alldata[102] = 507; alldata[103] = 982;
    alldata[104] = 618; alldata[105] = 375; alldata[106] = 429; alldata[107] = 564;
    alldata[108] = 893; alldata[109] = 156; alldata[110] = 704; alldata[111] = 261;
    alldata[112] = 927; alldata[113] = 840; alldata[114] = 517; alldata[115] = 364;
    alldata[116] = 692; alldata[117] = 841; alldata[118] = 253; alldata[119] = 618;
    alldata[120] = 450; alldata[121] = 739; alldata[122] = 596; alldata[123] = 183;
    alldata[124] = 247; alldata[125] = 501; alldata[126] = 876; alldata[127] = 329;
    alldata[128] = 592; alldata[129] = 814; alldata[130] = 386; alldata[131] = 750;
    alldata[132] = 923; alldata[133] = 468; alldata[134] = 579; alldata[135] = 310;
    alldata[136] = 641; alldata[137] = 257; alldata[138] = 834; alldata[139] = 495;
    alldata[140] = 176; alldata[141] = 326; alldata[142] = 981; alldata[143] = 509;
    alldata[144] = 432; alldata[145] = 695; alldata[146] = 871; alldata[147] = 548;
    alldata[148] = 314; alldata[149] = 769; alldata[150] = 638; alldata[151] = 205;
    alldata[152] = 489; alldata[153] = 732; alldata[154] = 976; alldata[155] = 540;
    alldata[156] = 217; alldata[157] = 865; alldata[158] = 743; alldata[159] = 591;
    alldata[160] = 827; alldata[161] = 459; alldata[162] = 673; alldata[163] = 925;
    alldata[164] = 384; alldata[165] = 567; alldata[166] = 318; alldata[167] = 896;
    alldata[168] = 204; alldata[169] = 741; alldata[170] = 356; alldata[171] = 982;
    alldata[172] = 520; alldata[173] = 687; alldata[174] = 193; alldata[175] = 645;
    alldata[176] = 826; alldata[177] = 179; alldata[178] = 934; alldata[179] = 617;
    alldata[180] = 250; alldata[181] = 563; alldata[182] = 498; alldata[183] = 743;
    alldata[184] = 895; alldata[185] = 137; alldata[186] = 672; alldata[187] = 581;
    alldata[188] = 415; alldata[189] = 329; alldata[190] = 984; alldata[191] = 276;
    alldata[192] = 613; alldata[193] = 785; alldata[194] = 249; alldata[195] = 417;
    alldata[196] = 836; alldata[197] = 594; alldata[198] = 367; alldata[199] = 982;
    alldata[200] = 541; alldata[201] = 920; alldata[202] = 305; alldata[203] = 768;
    alldata[204] = 439; alldata[205] = 612; alldata[206] = 175; alldata[207] = 483;
    alldata[208] = 897; alldata[209] = 346; alldata[210] = 529; alldata[211] = 714;
    alldata[212] = 208; alldata[213] = 685; alldata[214] = 972; alldata[215] = 461;
    alldata[216] = 835; alldata[217] = 275; alldata[218] = 673; alldata[219] = 194;
    alldata[220] = 518; alldata[221] = 629; alldata[222] = 743; alldata[223] = 890;
    alldata[224] = 425; alldata[225] = 681; alldata[226] = 937; alldata[227] = 502;
    alldata[228] = 364; alldata[229] = 815; alldata[230] = 239; alldata[231] = 586;
    alldata[232] = 701; alldata[233] = 324; alldata[234] = 879; alldata[235] = 450;
    alldata[236] = 568; alldata[237] = 937; alldata[238] = 194; alldata[239] = 821;
    alldata[240] = 538; alldata[241] = 970; alldata[242] = 286; alldata[243] = 614;
    alldata[244] = 729; alldata[245] = 495; alldata[246] = 186; alldata[247] = 853;
    alldata[248] = 421; alldata[249] = 768; alldata[250] = 519; alldata[251] = 342;
    alldata[252] = 697; alldata[253] = 854; alldata[254] = 271; alldata[255] = 613;

    complex_int16 signal[N];
    asm volatile ("slti x0, x0, 1");
    asm volatile ("slti x0, x0, 3");
    //initialize
    for(int i = 0; i < N; i++){
        complex_int16 temp = {alldata[(27*i)%N] << Q, alldata[(23*i)%N] << Q};
        signal[i] = temp;
    }
                                
    // compute
    fft(signal, N, 9);
    asm volatile ("slti x0, x0, 4");
    asm volatile ("slti x0, x0, 2");
    return 0;
}
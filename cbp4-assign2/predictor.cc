#include "predictor.h"
#define STRONG_NOT_TAKEN 0
#define WEAK_NOT_TAKEN 1
#define WEAK_TAKEN 2
#define STRONG_TAKEN 3
#define GaP_predictorTable_q3_1_size 1024
#define GaP_predictorTable_q3_2_size 16
#define chooser_q3_size 2048
#define PaP_historyTable_q3_size 1024
#define PaP_predictorTable_q3_1_size 1024
#define PaP_predictorTable_q3_2_size 32
#define PaP_predictorTable_binary_1 0b111111111100000 // history bit mask
#define PaP_predictorTable_binary_2 0b111111  // 
#define PaP_predictorTable_binary_3 0b11111   // num pattern table mask
#define GaP_predictorTable_binary_1 0b1111111111
#define GaP_predictorTable_binary_2 0b1111


/////////////////////////////////////////////////////////////
// 2bitsat
/////////////////////////////////////////////////////////////
static unsigned int predictorTable_q1[4096];


void InitPredictor_2bitsat() {
  for( int i = 0; i < 4096; i++){
    predictorTable_q1[i] = WEAK_NOT_TAKEN;
  }
}
bool GetPrediction_2bitsat(UINT32 PC) {
  // get lower bits of PC to address predictorTable_q1
  unsigned int currentPrediction = predictorTable_q1[PC % 4096];
  if (currentPrediction == STRONG_NOT_TAKEN || currentPrediction == WEAK_NOT_TAKEN){
     return NOT_TAKEN;
  }
  else if (currentPrediction == WEAK_TAKEN || currentPrediction == STRONG_TAKEN){
     return TAKEN;
  }
}
void UpdatePredictor_2bitsat(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  // get lower bits of PC to address predictorTable_q1
  unsigned int currentPrediction = predictorTable_q1[PC % 4096];
  // if result is not taken 
  if(resolveDir == NOT_TAKEN && currentPrediction != STRONG_NOT_TAKEN){
    predictorTable_q1[PC % 4096]--;
  } 
  else if(resolveDir == TAKEN && currentPrediction != STRONG_TAKEN){
    predictorTable_q1[PC % 4096]++;
  }
}




/////////////////////////////////////////////////////////////
// 2level
/////////////////////////////////////////////////////////////
// history table PC bits [11:3]
static unsigned int historyTable_q2[512];
// prediction table PC bits [2:0]
static unsigned int predictorTable_q2[64][8];
void InitPredictor_2level() {
  //init predictor table
  for( int i = 0; i < 64; i++){
    for( int j = 0; j < 8; j++){
      predictorTable_q2[i][j] = WEAK_NOT_TAKEN;
    }
  }
  //init history table
  for( int i = 0; i < 512; i++){
    historyTable_q2[i] = 0b000000;
  }
}
bool GetPrediction_2level(UINT32 PC) {
  // use PC to get history 
  unsigned int history = historyTable_q2[(0b111111111000 & PC) >> 3] & 0b111111;
  // use history and PC to get prediction
  unsigned int currentPrediction =  predictorTable_q2[history][0b111 & PC];
  if (currentPrediction == STRONG_NOT_TAKEN || currentPrediction == WEAK_NOT_TAKEN){
     return NOT_TAKEN;
  }
  else if (currentPrediction == WEAK_TAKEN || currentPrediction == STRONG_TAKEN){
     return TAKEN;
  }
}
void UpdatePredictor_2level(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  // use PC to get history 
  unsigned int history = historyTable_q2[(0b111111111000 & PC) >> 3] & 0b111111;
  // use history and PC to get prediction
  unsigned int currentPrediction =  predictorTable_q2[history][0b111 & PC];
  // if result is not taken 
  if(resolveDir == NOT_TAKEN && currentPrediction != STRONG_NOT_TAKEN){
    predictorTable_q2[history][0b111 & PC]--;
  } 
  else if(resolveDir == TAKEN && currentPrediction != STRONG_TAKEN){
    predictorTable_q2[history][0b111 & PC]++;
  }
  historyTable_q2[(0b111111111000 & PC) >> 3] = (historyTable_q2[(0b111111111000 & PC) >> 3] << 1) | resolveDir;

  
}

/////////////////////////////////////////////////////////////
// openend
/////////////////////////////////////////////////////////////
#define perceptron_predictorTable_size 512
#define perceptron_predictorThreshold 63
#define perceptron_predictorHistory_size 32
#define TABLE_BIT_MASK 0b111111111
static unsigned long int global_history_reg;
static int perceptronTable[perceptron_predictorTable_size][perceptron_predictorHistory_size];

static unsigned int perceptronSteps;

void perceptron_init() {
  //init predictor table
  for( int i = 0; i < perceptron_predictorTable_size; i++){
    for( int j = 0; j < perceptron_predictorHistory_size; j++){
      perceptronTable[i][j] = 0;
    }
  }

  
  global_history_reg = 0;
  perceptronSteps = 0;
}
bool perceptron_get(UINT32 PC) {
  int prediction = perceptronTable[PC & TABLE_BIT_MASK][0];
  int i;
  for (i = 1; i < perceptron_predictorHistory_size; i++){
    if (((global_history_reg >> (i)) & 0b1) == TAKEN){
      prediction += perceptronTable[PC & TABLE_BIT_MASK][i];
    }
    else{
      prediction -= perceptronTable[PC & TABLE_BIT_MASK][i];
    }
  }
  perceptronSteps = abs(prediction);
  return (prediction >= 0 ? TAKEN : NOT_TAKEN);

  
}

void perceptron_update(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {

  if(resolveDir != predDir || perceptronSteps <= perceptron_predictorThreshold){
    //update bias
    if(resolveDir == TAKEN && perceptronTable[PC & TABLE_BIT_MASK][0] != 63){
      perceptronTable[PC & TABLE_BIT_MASK][0]++;
    } 
    else if (resolveDir == NOT_TAKEN && perceptronTable[PC & TABLE_BIT_MASK][0] != -63) {
      perceptronTable[PC & TABLE_BIT_MASK][0]--;
    }

    
    // update weights
    for (int i = 1; i < perceptron_predictorHistory_size; i++){
      if(resolveDir == ((global_history_reg >> i) & 0b1)){
        perceptronTable[PC & TABLE_BIT_MASK][i]++;
      }
      else{
        perceptronTable[PC & TABLE_BIT_MASK][i]--;
      }
    }
  }
  global_history_reg = (global_history_reg << 1) | resolveDir;
}
void InitPredictor_openend() {
  perceptron_init();
}
bool GetPrediction_openend(UINT32 PC) {
  return perceptron_get(PC);
}
void UpdatePredictor_openend(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  perceptron_update(PC, resolveDir, predDir, branchTarget);
}

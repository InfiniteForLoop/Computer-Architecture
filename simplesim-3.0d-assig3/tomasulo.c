
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)  \
  myfprintf(out, "%d: %s", cycle, str);    \
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);  \
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/* ECE552 Assignment 3 - BEGIN CODE */

#define MAX_SIZE 10000000

/*
Inputs : Instruction
Functionality: Removes instruction from reservation stations
and function units
*/

void remove_from_RS_and_FU(instruction_t* instr){
  int i;
  
  for(i=0; i < RESERV_INT_SIZE; i++){
    if(instr == reservINT[i]){
      reservINT[i] = NULL;
    }
  }
  
  for(i=0; i < RESERV_FP_SIZE; i++){
    if(instr == reservFP[i]){
      reservFP[i] = NULL;
    }
  }
  
  for(i=0; i < FU_INT_SIZE; i++){
    if(instr == fuINT[i]){
      fuINT[i] = NULL;
    }
  }
  
  for(i=0; i < FU_FP_SIZE; i++){
    if(instr == fuFP[i]){
      fuFP[i] = NULL;
    }
  }
  
}

/*
Inputs : Instruction
Functionality: Removes instruction from reservation stations
and function units
*/
void remove_from_RS_and_FU_INT(instruction_t* instr){
  int i;
  
  for(i=0; i < RESERV_INT_SIZE; i++){
    if(instr == reservINT[i]){
      reservINT[i] = NULL;
    }
  }
  
  for(i=0; i < FU_INT_SIZE; i++){
    if(instr == fuINT[i]){
      fuINT[i] = NULL;
    }
  }
  
  
}


/*
Inputs : Instruction
Functionality: Removes instruction from reservation stations
and function units
*/
void remove_from_RS_and_FU_FP(instruction_t* instr){
  int i;
  
  for(i=0; i < RESERV_FP_SIZE; i++){
    if(instr == reservFP[i]){
      reservFP[i] = NULL;
    }
  }
  
  for(i=0; i < FU_FP_SIZE; i++){
    if(instr == fuFP[i]){
      fuFP[i] = NULL;
    }
  }
  
}

/*
Inputs : Instruction
Functionality: Removes instruction from reservation stations
and function units
*/
void update_RAWdependences_and_mapTable(instruction_t* curr_inst){
  //update RAW dependences in instruction
  int i, j;
  for(i=0; i<3; i++){
    if(curr_inst->r_in[i] != 0 && curr_inst->r_in[i] != DNA){
      if(map_table[curr_inst->r_in[i]] != NULL){
        curr_inst->Q[i] = map_table[curr_inst->r_in[i]];
       }
     else{
    curr_inst->Q[i] = NULL;
       }
    }
  }
          
  //update MAP table
  for(i=0; i<2; i++){
    if(curr_inst->r_out[i] != 0 && curr_inst->r_out[i] != DNA){
      map_table[curr_inst->r_out[i]] = curr_inst;
    }
  }
}


//Queue implementation
struct QueueNode{
  instruction_t* key;
  struct QueueNode* next;
};

struct Queue{
  struct QueueNode* first;
  struct QueueNode* last;
  unsigned int size;
};

static struct Queue* InsnFQ;

struct QueueNode* createNode(instruction_t* k){
  struct QueueNode* temp = (struct QueueNode*)malloc(sizeof(struct QueueNode));
  temp->key = k;
  temp->next = NULL;
  return temp;
}

void createQueue(){ 
  InsnFQ = (struct Queue*)malloc(sizeof(struct Queue));
  InsnFQ->first = NULL;
  InsnFQ->last = NULL;
  InsnFQ->size = 0;
  return;
}

void enQueue(instruction_t* k){ 

  struct QueueNode* temp = createNode(k);

  if (InsnFQ->last == NULL){
    InsnFQ->first = temp;
    InsnFQ->last = temp;
    return;
  }
  InsnFQ->last->next = temp;
  InsnFQ->last = temp;
}


void deQueue(){ 
  if (InsnFQ->first == NULL){
    return;
  }

  struct QueueNode* temp = InsnFQ->first;

  InsnFQ->first = InsnFQ->first->next;

  if (InsnFQ->first == NULL){
    InsnFQ->last = NULL;
  }
  free(temp);
}


void freeQueue(){ 
  if (InsnFQ->first == NULL){
    return;
  }

  struct QueueNode* temp = InsnFQ->first;
  struct QueueNode* temp_next = InsnFQ->first->next;

  while(temp != NULL){
    free(temp);
    temp = temp_next;
    if (temp_next != NULL){
      temp_next = temp_next->next;
    }
  }
  free(InsnFQ);
}

void ifq_init(){
  createQueue();
}

void ifq_push(instruction_t* curr_inst){
  InsnFQ->size++;
  return enQueue(curr_inst);
}

void ifq_pop(){
  InsnFQ->size--;
  return deQueue();
}


instruction_t* ifq_top(){
  if (InsnFQ->first == NULL)
    return NULL;
  return InsnFQ->first->key;
}
  
bool ifq_full(){
  if (InsnFQ->size > 16){
    return true;
  }
  else{
    return false;
  }
}

int ifq_size(){
    return InsnFQ->size;
}


instruction_t* is_ready_Exec_INT(int current_cycle){
  
  int oldest_num = MAX_SIZE;
  instruction_t* oldest_fp = NULL;
  
  int i;
  for(i = 0; i < RESERV_INT_SIZE; i++){
    //if valid intr and not yet in execute but has been in issue
    if (reservINT[i] != NULL && (reservINT[i]->tom_execute_cycle < reservINT[i]->tom_issue_cycle)){
    //load the three instr that are possibly being waited on
      instruction_t* dep_i_1 = reservINT[i]->Q[0];
      instruction_t* dep_i_2 = reservINT[i]->Q[1];
      instruction_t* dep_i_3 = reservINT[i]->Q[2];
      
      int is_busy_flag = 0;
      
      //if the instr is real and its not been in cbd or is currently in cbd its busy
      if (dep_i_1 != NULL && (dep_i_1->tom_cdb_cycle == 0 || dep_i_1->tom_cdb_cycle == current_cycle)){
        is_busy_flag += 1;
      }
      
      if (dep_i_2 != NULL && (dep_i_2->tom_cdb_cycle == 0 || dep_i_2->tom_cdb_cycle == current_cycle)){
        is_busy_flag += 1;
      }
      
      if (dep_i_3 != NULL && (dep_i_3->tom_cdb_cycle == 0 || dep_i_3->tom_cdb_cycle == current_cycle)){
        is_busy_flag += 1;
      }
      
      //none are busy
      if (is_busy_flag == 0){
        if (reservINT[i]->index < oldest_num){
          oldest_num = reservINT[i]->index;
          oldest_fp = reservINT[i];
        }
      }
    }
  }
  return oldest_fp;
}

instruction_t* is_ready_Exec_FP(int current_cycle){
  
  int oldest_num = MAX_SIZE;
  instruction_t* oldest_fp = NULL;
  
  int i;
  for(i = 0; i < RESERV_FP_SIZE; i++){
    //if valid intr and not yet in execute but has been in issue
    if (reservFP[i] != NULL && (reservFP[i]->tom_execute_cycle < reservFP[i]->tom_issue_cycle)){
    //load the three instr that are possibly being waited on
      instruction_t* dep_i_1 = reservFP[i]->Q[0];
      instruction_t* dep_i_2 = reservFP[i]->Q[1];
      instruction_t* dep_i_3 = reservFP[i]->Q[2];
      
      int is_busy_flag = 0;
      
      //if the instr is real and its not been in cbd or is currently in cbd its busy
      if (dep_i_1 != NULL && (dep_i_1->tom_cdb_cycle == 0 || dep_i_1->tom_cdb_cycle == current_cycle)){
        is_busy_flag += 1;
      }
      
      if (dep_i_2 != NULL && (dep_i_2->tom_cdb_cycle == 0 || dep_i_2->tom_cdb_cycle == current_cycle)){
        is_busy_flag += 1;
      }
      
      if (dep_i_3 != NULL && (dep_i_3->tom_cdb_cycle == 0 || dep_i_3->tom_cdb_cycle == current_cycle)){
        is_busy_flag += 1;
      }
      
      //none are busy
      if (is_busy_flag == 0){
        if (reservFP[i]->index < oldest_num){
          oldest_num = reservFP[i]->index;
          oldest_fp = reservFP[i];
        }
      }
    }
  }
  return oldest_fp;
}
/* ECE552 Assignment 3 - END CODE */

/* 
 * Description: 
 *   Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 *   sim_insn: the total number of instructions simulated
 * Returns:
 *   True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */
  int not_done = 0;
  int i;

  for(i = 0; i < RESERV_INT_SIZE; i++){
    if(reservINT[i] != NULL){
      not_done += 1;
    }
  }

  for(i = 0; i < RESERV_FP_SIZE; i++){
    if(reservFP[i] != NULL){
      not_done += 1;
    }
  }

  for(i = 0; i < FU_INT_SIZE; i++){
    if(fuINT[i] != NULL){
      not_done += 1;
    }
  }

  for(i = 0; i < FU_FP_SIZE; i++){
    if(fuFP[i] != NULL){
      not_done += 1;
    }
  }
  
  if (fetch_index < sim_insn){
    not_done += 1;
  }
  
  if(ifq_size() != 0){
    not_done += 1;
  }
  
  if(not_done == 0){
    return true;
  }
  else{
    return false; 
  }
  //return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 *   Retires the instruction from writing to the Common Data Bus
 * Inputs:
 *   current_cycle: the cycle we are at
 * Returns:
 *   None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  
  //if the cdb is not null and the insn is in cdb has finished after a cycle
  if(commonDataBus != NULL && current_cycle >= commonDataBus->tom_cdb_cycle+1){
    int i;
    //update map table
    for(i=0; i<2; i ++){
      if(commonDataBus->r_out[i] != DNA && commonDataBus == map_table[commonDataBus->r_out[i]]){
        map_table[commonDataBus->r_out[i]] = NULL;
      }
    }
    //remove from RS and FU
      remove_from_RS_and_FU(commonDataBus);
      commonDataBus = NULL;
  }
  //possibly need to resolve raw dependences?
  //printf("CDB to retire instr cycle %d\n",current_cycle);

}


/* 
 * Description: 
 *   Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 *   current_cycle: the cycle we are at
 * Returns:
 *   None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  int i;
  instruction_t* CDB_instr = NULL; 

    //check FU FP for instr that need CDB
  for(i=0; i<FU_INT_SIZE; i++){
      
    //check if there is FU entry
    if(fuINT[i] != NULL){
        
        //calculate cycle instr finishes
      int finish_cycle = fuINT[i]->tom_execute_cycle + FU_INT_LATENCY;
        
      if(current_cycle >= finish_cycle){
          
        //remove store instr
        if(!WRITES_CDB(fuINT[i]->op)){
            
          //remove instruction from RS and FU
          if (USES_FP_FU(fuINT[i]->op)){
            remove_from_RS_and_FU_FP(fuINT[i]);
          }

          else if (USES_INT_FU(fuINT[i]->op)){
            remove_from_RS_and_FU_INT(fuINT[i]);
          }
          else{
            remove_from_RS_and_FU_INT(fuINT[i]);
          }
        }
        else{
          if(CDB_instr == NULL || CDB_instr->index > fuINT[i]->index){
            CDB_instr = fuINT[i];
          }
        }
      }
        }
    }
    //check FU INT for instr that need CDB
    for(i=0; i<FU_FP_SIZE; i++){
      
      //check if there is FU entry
    if(fuFP[i] != NULL){
        
        //calculate cycle instr finishes
      int finish_cycle = fuFP[i]->tom_execute_cycle + FU_FP_LATENCY;
        
      if(current_cycle >= finish_cycle){
        if(!WRITES_CDB(fuFP[i]->op)){
          //remove instruction from RS and FU
          if (USES_FP_FU(fuFP[i]->op)){
            remove_from_RS_and_FU_FP(fuFP[i]);
          }
      
          else if (USES_INT_FU(fuFP[i]->op)){
            remove_from_RS_and_FU_INT(fuFP[i]);
          }
          else{
            remove_from_RS_and_FU_INT(fuFP[i]);
          }
        }
        else{
          if(CDB_instr == NULL || CDB_instr->index > fuFP[i]->index){
            CDB_instr = fuFP[i];
          }
        }
      }
    }
    }
  if(CDB_instr != NULL){
    CDB_instr->tom_cdb_cycle = current_cycle;
    commonDataBus = CDB_instr;
    if (USES_FP_FU(CDB_instr->op)){
      remove_from_RS_and_FU_FP(CDB_instr);
    }
    else if (USES_INT_FU(CDB_instr->op)){
      remove_from_RS_and_FU_INT(CDB_instr);
    }
    else{
      remove_from_RS_and_FU_INT(CDB_instr);
    }
  }
  //printf("ex to CDB instr cycle %d\n",current_cycle);
}

/* 
 * Description: 
 *   Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 *   current_cycle: the cycle we are at
 * Returns:
 *   None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  //2 integer functional units
  //check if there is RAW hazard
  
  
  int i;
  
  for(i = 0; i < FU_INT_SIZE; i++){
    instruction_t* oldest_instr = NULL;
    //find oldest instr that is ready to execute
    oldest_instr = is_ready_Exec_INT(current_cycle);
    if(fuINT[i] == NULL){
      if(oldest_instr !=NULL){
        oldest_instr->tom_execute_cycle = current_cycle;
        fuINT[i] = oldest_instr;
      }
    }
  }
  
  
  for(i = 0; i < FU_FP_SIZE; i++){
    instruction_t* oldest_instr = NULL;
    //find oldest instr that is ready to execute
    oldest_instr = is_ready_Exec_FP(current_cycle);
    
    if(fuFP[i] == NULL){
      if(oldest_instr !=NULL){
        oldest_instr->tom_execute_cycle = current_cycle;
        fuFP[i] = oldest_instr;
      }
    }
  }
  
  //printf("issue to ex instr cycle %d\n",current_cycle);

  
}

/* 
 * Description: 
 *   Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 *   current_cycle: the cycle we are at
 * Returns:
 *   None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  instruction_t* curr_inst = ifq_top();
  
  if (curr_inst == 0) return;
  int i, j;
      //printf("dispatch instr cycle %d instr value %d\n",current_cycle,curr_inst);

  
  //If IFQ has instr ready
  if(curr_inst != NULL){
    
    //If instr is FP
    if(USES_FP_FU(curr_inst->op)){
      for(i=0; i<RESERV_FP_SIZE; i++){
        
       //check if RS is available
        if(reservFP[i] == NULL){
         
          update_RAWdependences_and_mapTable(curr_inst);

          //allocate RS entry to instruction
          reservFP[i] = curr_inst;
          //remove instruction from IFQ
          ifq_pop();
          break; // only use one RS
        }
        
      }
      
    }else if(USES_INT_FU(curr_inst->op)){ //If instr is INT
      for(i=0; i<RESERV_INT_SIZE; i++){

       //check if RS is available
        if(reservINT[i] == NULL){

         
          update_RAWdependences_and_mapTable(curr_inst);
          
          //allocate RS entry to instruction
          reservINT[i] = curr_inst;
          //remove instruction from IFQ
          ifq_pop();
         
          break; // only use one RS
        }
        
      }
      
    }
  else if(IS_COND_CTRL(curr_inst->op) || IS_UNCOND_CTRL(curr_inst->op)){ //If instr is branch
      ifq_pop();
    }
    
  }
  
  for (i = 0; i < RESERV_INT_SIZE; i++){
    if (reservINT[i] != NULL){
      if (reservINT[i]->tom_issue_cycle == 0){
        reservINT[i]->tom_issue_cycle = current_cycle;
      }
    }
  }
  
  for (i = 0; i < RESERV_FP_SIZE; i++){
    if (reservFP[i] != NULL){
      if (reservFP[i]->tom_issue_cycle == 0){
        reservFP[i]->tom_issue_cycle = current_cycle;
      }
    }
  }
  return;
}

/* 
 * Description: 
 *   Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 *   None
 */
void fetch(instruction_trace_t* trace) {
  /* ECE552: YOUR CODE GOES HERE */

  if (!ifq_full() && fetch_index < sim_num_insn) {
    fetch_index++;
    instruction_t* curr_instr = get_instr(trace, fetch_index);

    while (curr_instr != NULL && IS_TRAP(curr_instr->op)) {
      fetch_index++;
      curr_instr = get_instr(trace, fetch_index);
    }

    if (curr_instr){
      ifq_push(curr_instr);
    }
  }
}

/* 
 * Description: 
 *   Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 *   current_cycle: the cycle we are at
 * Returns:
 *   None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);
  int ifq_s = ifq_size();
  if (ifq_s == 0) return;

  instruction_t *instr = ifq_top();
  instr->tom_dispatch_cycle = current_cycle;
}

/* 
 * Description: 
 *   Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 *   The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 *   sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  ifq_init();
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }
  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
    reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
    reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }

  int cycle = 1;
  while (true) {
     /* ECE552: YOUR CODE GOES HERE */
    CDB_To_retire(cycle);
    execute_To_CDB(cycle);
    issue_To_execute(cycle);
    dispatch_To_issue(cycle);
    fetch_To_dispatch(trace ,cycle);
    cycle++;
    if (is_simulation_done(sim_num_insn)){
      break;
    }
  }
  return cycle;
}

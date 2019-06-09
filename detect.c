/*
* detect.c - identify ACE and un-ACE instructions
*
* This file is part of the Sim-SODA tool suite written by Xin Fu
* 
* Copyright (C) 2006 by Xin Fu <xinfu@ufl.edu>
*
* This source file is distributed "as is" in the hope that it will be
* useful.  It is distributed with no warranty, and no author or
* distributor accepts any responsibility for the consequences of its
* use. 
*
* Everyone is granted permission to copy, modify and redistribute
* this source file under the following conditions:
*
*    This tool set is distributed for non-commercial use only.f-inter 
*    Please contact the maintainer for restrictions applying to 
*    commercial use of these tools.
*
*    Permission is granted to anyone to make or distribute copies
*    of this source code, either as received or modified, in any
*    medium, provided that all copyright notices, permission and
*    nonwarranty notices are preserved, and that the distributor
*    grants the recipient permission for further redistribution as
*    permitted by this document.
*
*    Permission is granted to distribute this file in compiled
*    or executable form under the same conditions that apply for
*    source code, provided that either:
*
*    A. it is accompanied by the corresponding machine-readable
*       source code,
*    B. it is accompanied by a written offer, with no time limit,
*       to give anyone a machine-readable copy of the corresponding
*       source code in return for reimbursement of the cost of
*       distribution.  This written offer must permit verbatim
*       duplication by anyone, or
*    C. it is distributed by someone who received only the
*       executable form, and is accompanied by a copy of the
*       written offer of source code that they received concurrently.
*
* In other words, you are welcome to use, share and improve this
* source file.  You are forbidden to forbid anyone else to use, share
* and improve what you give them.
*
* Copyright (C) 2006 by Xin Fu <xinfu@ufl.edu>
*/

#include "host.h"
#include "misc.h"
#include "alpha.h"
#include "options.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "eventq.h"
#include "syscall.h"
#include "stats.h"
#include "sim.h"
#include "issue.h"
#include "writeback.h"
#include "cache.h"
#include "resource.h"
#include "commit.h"
#include "bus.h"
#include "tlb.h"
#include "ssregs.h"
#include "dram.h"
#include "bpred.h"
#include "fetch.h"
#include "slot.h"
#include "map.h"
#include "tddfdd.h"







/* The analysis window is implemented as a linked list, has the head node (firstinst) and rear node (rearinst) */
LISTPTR firstinst;
LISTPTR rearinst;

/* Committed instructions are identified as FDD_reg, FDD_mem, TDD_reg, TDD_mem, ACE, NOP, prefetching and unknown 
 * One counter is set for each instruction category */ 
long fddregcounter=0;
long tddregcounter=0;
long fddmemcounter=0;
long tddmemcounter=0;
long unknown=0;
long acecounter=0;
long nop=0;
long prefetch=0;


FILE *sim_avffd;

/* Some ACE instructions are trivial instructions. Use an array to counter each type of trivial instructions */ 
unsigned long trivial[29];



/* Accumulate the number of ACE bits/cycle across the whole simulation in IQ, ROB and FU repectively */
tick_t IQACE_cycle1=0;
tick_t IQACE_cycle2=0;
tick_t IQACE_cycle3=0;
tick_t IQACE_cycle4=0;
tick_t IQACE_cycle5=0;

tick_t robACE_cycle1=0;
tick_t robACE_cycle2=0;
tick_t robACE_cycle3=0;
tick_t robACE_cycle4=0;
tick_t robACE_cycle5=0;

tick_t fuACE_cycle1=0;
tick_t fuACE_cycle2=0;
tick_t fuACE_cycle3=0;
tick_t fuACE_cycle4=0;
tick_t fuACE_cycle5=0;
tick_t fuACE_cycle6=0;

tick_t wakeup_cycle=0;

/* A register array list for register file AVF computation */
struct reg_time *reg_array;

/* The moment to end register AVF computation, a COOL DOWN period is required after this */
tick_t regend_cycle=0;
/* The moment to end the COOLDOWN period for register AVF computation */
tick_t regfinish_cycle=0;

/*A table is required to maintain the list of producers and consumers for the register and memory location */
/* The table head for INT registers */
REGMEMPTR reg_head;
/* The table head for FP registers */
REGMEMPTR fp_reg_head;
/* The table head and rear for memory loations */
REGMEMPTR headrm;
REGMEMPTR rearrm;

/* temp variables used to dump structures' AVF per interval */ 
tick_t fuACEcycle1=0;
tick_t fuACEcycle2=0;
tick_t fuACEcycle3=0;
tick_t fuACEcycle4=0;
tick_t fuACEcycle5=0;
tick_t fuACEcycle6=0;

tick_t ACEcycle1=0;
tick_t ACEcycle2=0;
tick_t ACEcycle3=0;
tick_t ACEcycle4=0;
tick_t ACEcycle5=0;

tick_t robACEcycle1=0;
tick_t robACEcycle2=0;
tick_t robACEcycle3=0;

tick_t IQ_ACEcycle=0;
tick_t ROB_ACEcycle=0;
tick_t FU_ACEcycle=0;

tick_t avg_cycle=0;

counter_t FDDreg_sum=0;
counter_t FDDmem_sum=0;
counter_t TDDreg_sum=0;
counter_t TDDmem_sum=0;
counter_t NOP_sum=0;
counter_t unknown_sum=0;
counter_t ACE_sum=0;
counter_t prefetch_sum=0;
float rf_AVF=0;



unsigned int interval_inst;
long tablecounter=0;
tick_t cycle_num=0;

counter_t IQ_idle_counter=0;

counter_t IQ_idle[4];

tick_t cycle_wakeup[4];



int rob_idle_counter=0;
 
int wakeup_idle_counter=0;

int fu_idle_counter=0;

/* whether interval dump is required */
int datadump;

/*****check whether the table (ONLY FOR MEMORY LOCATION) is empty********/

REGMEMPTR isnull(REGMEMPTR headrm)
{
	
	if(headrm==NULL)
	{
        headrm= (REGMEMPTR) calloc ( 1, sizeof ( REGMEM ) );
		headrm->former=NULL;
		return headrm;
	}
	else 
		return NULL;
}

	
/********create a new REGMEMPTR node in table (ONLY FOR MEMORY LOCATIONS) **********/

REGMEMPTR createnode(REGMEMPTR noderm,LISTPTR instnode, char DS/*destination or source*/)
{
	REGMEMPTR newnoderm;
	
	if((DS=='D')&&(instnode->des!=-1))
	{
		noderm->rminfo=instnode->des;
	}
	
	else return noderm;
    noderm->nextrm=NULL;
	noderm->firstpc=NULL;
	noderm->lastpc=NULL;
	newnoderm= (REGMEMPTR) calloc ( 1, sizeof ( REGMEM ) );
	noderm->nextrm=newnoderm;
	newnoderm->former=noderm;
	return newnoderm;
}


/*search des(producer for store, consumer for load) in MEMORY link list */

REGMEMPTR searchdes(REGMEMPTR rearrm,LISTPTR instnode)
{
	
	REGMEMPTR tempnode;
	tempnode=rearrm;
	/*rearrm is an empty node, search from its former node */
	while(tempnode!=NULL)
	{
		if(tempnode->rminfo==instnode->des)
			break;
		tempnode=tempnode->former;
		
	}
	if(tempnode==NULL)
	{
		return NULL;
	}
        if(tempnode->rminfo==instnode->des)
		return tempnode;
        else
               return NULL;
	
}


/***********insert producer or consumer node to the corresponding register/memory list*******/

PROCONPTR insertpc(REGMEMPTR insertnode,unsigned long instno,char PorC)
{
  PROCONPTR pc;
  //create a new producer/consumer node
  pc=(PROCONPTR) calloc ( 1, sizeof ( PROCON ) );
  if(PorC=='P')
	  //the node is producer
	  pc->PC='P';
      //the node is consumer
  else pc->PC='C';
  pc->instnumber=instno;
  pc->nextprocon=NULL;
  /*add MR, opcode info to every producer/consumer node for use fast producer/consumer search*/
  pc->MR = rearinst-> MR;
  pc->opcode = rearinst -> opcode;
  pc-> outreg = rearinst -> outreg;
  pc->op=rearinst->op;
  if(insertnode->firstpc==NULL)
	  insertnode->firstpc=pc;  
  else
	  insertnode->lastpc->nextprocon=pc; 
   insertnode->lastpc=pc;
 return pc;
}



/******delete producer or consumer node from the corresponding REGISTER/MEMORY list****/
/*check from the very beginning of the regmem node, because produce/consume nodes which are going to be 
deleted are always the first several nodes of the list. */

void deletepc(REGMEMPTR deletenode, LISTPTR analyzeinst, int delete_mem)
{
	PROCONPTR tempc,temppc;	
	unsigned long instno;
	temppc=deletenode->firstpc;
	tempc=temppc;
	instno=analyzeinst->instno;
	if(temppc->instnumber==instno)
	{
		deletenode->firstpc=temppc->nextprocon;
		free(temppc);		
	}
	else
	{
		/* the inst's producer and consumers should be inserted into the line 
		   together, so we don't need to search the whole line. Just delete one
		   when you find it. */
	    while(temppc->nextprocon!=NULL)
	    {
		  if(temppc->instnumber==instno)
		  //find the producer/consumer which should be deleted from the list
			break;
		 //instructions is ordered in each reg/mem producer/consumer list
		  assert(temppc->instnumber >= instno);
	      tempc=temppc;
		  temppc=temppc->nextprocon;
	    }
		if(temppc->instnumber==instno)
		{
         tempc->nextprocon=temppc->nextprocon;
		 free(temppc);
		 }
	}
	if(deletenode->firstpc==NULL)
	{
		if(delete_mem)
		{    /*there is no producer/consumer for this memory node,
		       delete this node to reduce the number of memory nodes */
			   if(deletenode!=headrm)
			   {
				  
				  deletenode->former->nextrm=deletenode->nextrm;
				  deletenode->nextrm->former=deletenode->former;
                  free(deletenode);
			   }
			   else
			   {
				  headrm=deletenode->nextrm;
				  headrm->former=NULL;
				  free(deletenode);
			   }
		}
	}
}



/* register initilization, build register array to hold each register file ACE time for AVF computation
   and create all the INT, FP register node for producer/consumer link list (the Table) */
void reg_init()
{
	int i=1;
	reg_array = (struct reg_time *) 
    calloc(regs_num_int_p_regs+31+8+1, sizeof(struct reg_time));
	for(i=1;i<regs_num_int_p_regs+31+8+1;i++)
	{
		reg_array[i].ACE_time=0;
        reg_array[i].unACE_time=0;
		reg_array[i].unknown_time=0;
		reg_array[i].now=0;
		reg_array[i].test_time=0;
		reg_array[i].state=0;
        
	}

	/*create integer register node for linked list */
	reg_head=(struct regmem *)
	calloc(regs_num_int_p_regs+31+8+1, sizeof(struct regmem));

    /*create floating point register node for linked list*/
	fp_reg_head=(struct regmem *)
	calloc(regs_num_fp_p_regs+31+8+1, sizeof(struct regmem));
	
}
	




/* accumulate ACE bits per cycle for IQ and ROB */
void sum_cycle(int inst_type, unsigned long residency,int trivial_flag, int structure_type)
{/* 6-bit opcode, 5-bit register specifier*/
	
	if(structure_type==INST_QUEUE)
    /*structure type is IQ.*/
	{
	switch(inst_type)
		{
		case FDDTDD:/* FDD and TDD instruction*/
           IQACE_cycle1=(6+5)*residency+IQACE_cycle1;
		   ACEcycle1=ACEcycle1+residency;
		   break;
		case NOP:/* NOP instruction*/
		case PREFETCH:/* prefetch instruction*/
	       IQACE_cycle2=6*residency+IQACE_cycle2;
		   ACEcycle2=ACEcycle2+residency;
		   break;
        case ACE:	/* ACE instruction*/
		case UNKNOWN: /* UNKNOW instruction*/
		  /* trivial ACE instructions contain some amount of unACE bits */
		   if(trivial_flag<22&&trivial_flag>0)
		    {
              IQACE_cycle3=27*residency+IQACE_cycle3;
			  ACEcycle3=ACEcycle3+residency;
			}
		   else if(trivial_flag>21&&trivial_flag<29)
		   {
              IQACE_cycle4=24*residency+IQACE_cycle4;
			  ACEcycle4=ACEcycle4+residency;
		   }
		   else
		   {  
			   IQACE_cycle5=32*residency+IQACE_cycle5;
			   ACEcycle5=ACEcycle5+residency;
		   }	   
	       break;
		default: break;
	    }
      /*accumlate the cycles each instruction stay in IQ */
      avg_cycle=avg_cycle+residency;
	 }
	if(structure_type==REORDER_BUFFER)
	{/*structure type is ROB */
		switch(inst_type)
	  {	
		case FDDTDD:/* FDD and TDD instruction*/	
           robACE_cycle1=(6+5+1)*residency+robACE_cycle1;
           robACEcycle1=robACEcycle1+residency;
		   break;
		case NOP:/* NOP instruction.*/
		case PREFETCH:/* prefetch instruction*/
	       robACE_cycle2=(6+1)*residency+robACE_cycle2;
		   robACEcycle2=robACEcycle2+residency;
		   break;
        case ACE:	/* ACE instruction*/
		case UNKNOWN: /* UNKNOW instruction.*/	  
	       robACE_cycle3=(6+5+1+64)*residency+robACE_cycle3;
		   robACEcycle3=robACEcycle3+residency;
	       break;
		default: break;
	  }
	}
}


/* accumulate ACE bits per cycle for function units */
void sum_fuACE_cycle(LISTPTR analyzeinst)
{
	/*input*/
	if((analyzeinst->trivial_flag>7)&&(analyzeinst->trivial_flag<22))
	  /* rb: unACE bits*/ 
	{
	  fuACE_cycle1=fuACE_cycle1+64*analyzeinst->fu_cycle;
	  fuACEcycle1=fuACEcycle1+analyzeinst->fu_cycle;
	}
	else if((analyzeinst->trivial_flag<8)&&(analyzeinst->trivial_flag>0))
       /*ra: unACE bits*/
	{
	   fuACE_cycle2=fuACE_cycle2+64*analyzeinst->fu_cycle;
	   fuACEcycle2=fuACEcycle2+analyzeinst->fu_cycle;
	}
	else if((analyzeinst->trivial_flag>21)&&(analyzeinst->trivial_flag<29))
	   /*immediate: unACE bits */
	{
	    fuACE_cycle3=fuACE_cycle3+64*analyzeinst->fu_cycle;
		fuACEcycle3=fuACEcycle3+analyzeinst->fu_cycle;
	}
	else 
		/*no unACE bits */
	{
	    fuACE_cycle4=fuACE_cycle4+64*2*analyzeinst->fu_cycle;
		fuACEcycle4=fuACEcycle4+analyzeinst->fu_cycle;
	}
    
	/*output*/
	if(reg_low_high(analyzeinst))
		/* only used the lower part of the datapath and register also */
	{
        fuACE_cycle5=fuACE_cycle5+32*analyzeinst->fu_cycle;
		fuACEcycle5=fuACEcycle5+analyzeinst->fu_cycle;
	}
	else
	{
        fuACE_cycle6=fuACE_cycle6+64*analyzeinst->fu_cycle;
		fuACEcycle6=fuACEcycle6+analyzeinst->fu_cycle;
	}
	
	 
}


/* create and update the table which is used to maintain the the list of
   producers and consumers for the register and memory locations */
void table()
{
	REGMEMPTR createhead;
	REGMEMPTR insertrm=NULL;
	PROCONPTR consume_rs=NULL;
	PROCONPTR consume_rt=NULL;
	PROCONPTR consume_load=NULL;
	PROCONPTR consume_des=NULL;
	createhead=isnull(headrm);
  if(rearinst->opcode!=NOP && rearinst->opcode!=PREFETCH)
  {
	/* NOP and prefetch instructions will not be inserted into the table
	   since they have no consumer */
	/* First insert consumer nodes and then producer nodes
	   because the source register may be the destination register */
    
   
    //insert the first source operand (consumer) information into the table
	 if((rearinst->rs!=-1)&&(rearinst->rs!=31))
	 { 
	  if(rearinst->src_reg1==INTEGER)
	     insertrm = reg_head+rearinst->rs;
	  else
		 insertrm = fp_reg_head+rearinst->rs;
      consume_rs = insertpc(insertrm,rearinst->instno,'C');
	 }

	 if((rearinst->rt!=-1)&&(rearinst->rt!=31))
	 {
     //insert the second source operand (consumer) information into the table
	 if(rearinst->src_reg2==INTEGER)
	   insertrm=reg_head+rearinst->rt;
	 else
        insertrm=fp_reg_head+rearinst->rt;
	 consume_rt = insertpc(insertrm,rearinst->instno,'C');
	 }
	
	 if(rearinst->opcode==LOAD)
	 /*load instruction consumes value from memory location*/
	 {
       if(createhead!=NULL)
	    {
		/***memory table is empty***/
		headrm=createhead;
		rearrm=createhead;
		insertrm=rearrm;
		rearrm=createnode(rearrm,rearinst,'D');  
	    }
	  else
	    {
		insertrm=searchdes(rearrm,rearinst);
	    if(insertrm==NULL)
	      {
		   insertrm=rearrm;
           rearrm=createnode(rearrm,rearinst,'D');
	      }	
	    }
	   consume_load = insertpc(insertrm,rearinst->instno,'C');
	   rearinst->load_mem= insertrm;
	 }


     if(rearinst->opcode==STORE)
	  /* store instruction produce value into memory location*/
	 {
      if(createhead!=NULL)
	  {
		/***memory table is empty***/
		headrm=createhead;
		rearrm=createhead;
		insertrm=rearrm;
		rearrm=createnode(rearrm,rearinst,'D');  
	  }
	  else
	  {
		insertrm=searchdes(rearrm,/*rearrm,*/rearinst);
	    if(insertrm==NULL)
	    {
		   insertrm=rearrm;
           rearrm=createnode(rearrm,rearinst,'D');
	    }
	  }
	  /* point the destination memory location in the table to the inst node */
	    rearinst->out_regmem = insertrm;
		consume_des = insertpc(insertrm,rearinst->instno,'P');
	  /* point the inst producer to the inst consumers*/
		if(consume_rs!=NULL)
			consume_rs->des_pro=consume_des;
		if(consume_rt!=NULL)
			consume_rt->des_pro=consume_des;
	    consume_des->des_pro = consume_des;
		rearinst->out_pro = consume_des;
		//the pointers above is used for quick data dependence check
          
	 }

	
    
     if(((rearinst->opcode==BRJS || rearinst->opcode==OTHER)&&(rearinst->outreg!=31)&&(rearinst->outreg!=-1))
		 ||(rearinst->opcode==LOAD))
     {
	 /* no-store instructions, add their producers into the table*/
	  if(rearinst->dest_reg==INTEGER)
	   insertrm=reg_head+rearinst->outreg;
	  else
       insertrm=fp_reg_head+rearinst->outreg;
	  /* point the destination register to the inst node */
	  rearinst->out_regmem = insertrm;
      consume_des = insertpc(insertrm,rearinst->instno,'P');
	  /* point the inst producer to the inst consumers*/
      if(consume_rs!=NULL)
			consume_rs->des_pro=consume_des;
	  if(consume_rt!=NULL)
			consume_rt->des_pro=consume_des;	
      consume_des-> des_pro = consume_des;
	  rearinst->out_pro = consume_des;
	  if(rearinst->opcode==LOAD)
          consume_load->des_pro = consume_des;
	  //the pointers above is used for quick data dependence check
     }

   }
	
}




/* Only called by TDD detection function, to do the width-prior traverse searching
   return NULL if the instruction is FDD, other returns mean the instruction 
   requires more deep search to identify whether it is ACE or not*/
PROCONPTR detectFDD(PROCONPTR nodepc)
{
     
		PROCONPTR temporarypc;		
		if(nodepc->opcode==BRJS)
	    {
		//branch, return, jump, syscall instructions are ACE instructions
		  temporarypc=(PROCONPTR)calloc(1,sizeof(PROCON));
		  temporarypc->instnumber=-1;
		  temporarypc->nextprocon=NULL;
		  return temporarypc;
		}
		  if(nodepc->nextprocon==NULL)
		  {  
		    /* UNKNOWN instruction */
		     return nodepc;
		  }
          else
		  {
			  if((nodepc->nextprocon)->PC=='P')
			  {
				 /* FDD instruction, return NULL */
                 return NULL;
			  }
			  else
				 return nodepc;
		  }
	  
}

/*Directly used for FDD detection, return NULL if the analyzed instruction is identified
  and no further analysis is required, other returns mean further analysis is required*/
PROCONPTR detectFDD_first(LISTPTR aninst)
{
    
	PROCONPTR nodepc;

		
	if(aninst->opcode==BRJS)
	{
		//branch, return, jump, syscall instructions are ACE instructions
		//ACE counter increases one
		acecounter++;
		//the analyzed instruction set its flag as ACE
		aninst->FT='A';
		//accumulate ACE bits per cycle in IQ, ROB and FU 
		sum_cycle(ACE,aninst->resident_cycle, aninst->trivial_flag, INST_QUEUE);
        sum_cycle(ACE,aninst->commit_time-aninst->rob_time, aninst->trivial_flag, REORDER_BUFFER);
        sum_fuACE_cycle(aninst);
		//the instruction identification is finished, no further analysis is required, return NULL
		return NULL;
	}
	//get the instruction's producer
    nodepc=aninst->out_pro;
	assert(aninst->instno==nodepc->instnumber);
	assert(nodepc->PC=='P');
	if(nodepc->nextprocon==NULL)
		  { 
		   // the analyzed instruction is UNKNOWN
		     if((aninst->counted==0)&&(aninst==firstinst))
			  {
				 aninst->FT='U';
				 unknown++;
				 sum_cycle(UNKNOWN,aninst->resident_cycle, aninst->trivial_flag,INST_QUEUE);
                 sum_cycle(UNKNOWN,aninst->commit_time-aninst->rob_time, aninst->trivial_flag,REORDER_BUFFER);
				 sum_fuACE_cycle(aninst);
			     aninst->counted=1;
				// return NULL;
			  }
		    //if(aninst->counted==1) 
                      return NULL;
			
		  }
      else
		  {
			  if((nodepc->nextprocon)->PC=='P')
			  {
			  /* the analyzed instruction is FDD, set its flag as FDD */
				  aninst->FT='F';
				  if(aninst->counted==0)
				  {
					sum_cycle(FDDTDD,aninst->resident_cycle,aninst->trivial_flag, INST_QUEUE);
					sum_cycle(FDDTDD,aninst->commit_time-aninst->rob_time, aninst->trivial_flag,REORDER_BUFFER);
					//determine whether it is FDD_reg or FDD_mem 
				    if(aninst->MR=='R')
					  {
				         fddregcounter++;
						 aninst->FDDTDDRM='r';
					  }
				    else 
					  {
						fddmemcounter++;	
						aninst->FDDTDDRM='m';
					  }
			        aninst->counted=1;
				  }
                 return NULL;
			  }
			  else
				 //cannot determine whether the analyzed inst is ACE or not, requires further analysis
				 return nodepc;
		  }
	  
	  
}



/* determine whether the analyzed instruction is TDD */
void detectTDD()
{
	TESTTDDPTR headtest, temptest;
    TESTTDDPTR middletest;
	TESTTDDPTR reartest;
	TESTTDDPTR nodetest;
	TESTTDDPTR checknode;
	PROCONPTR tempnodepc;
	PROCONPTR node_pc;
    long testcounter;
	headtest=(TESTTDDPTR)calloc(1,sizeof(TESTTDD));
	middletest=headtest;
	reartest=headtest;	
	headtest->insno=firstinst->instno;
	headtest->FTUA='N';
	node_pc=firstinst->out_pro;
	headtest->des_pro =node_pc;
	headtest->outreg=firstinst->outreg;
	headtest->opcode=firstinst->opcode;
	headtest->MR=firstinst->MR;
	headtest->nexttdd=NULL;
	//start dependence chain checking
	while(middletest!=NULL)
	{
	  
		if(middletest->opcode==BRJS)
			{
			/* branch, return, jump or syscall instructions, they are ACE */
			firstinst->FT='A';
			middletest->FTUA='A';
			break;
			}
		node_pc=middletest->des_pro;
        tempnodepc=detectFDD(node_pc);
		

	  if(tempnodepc==NULL)
		{
			 middletest->FTUA='F';
		}

	   else if(tempnodepc->nextprocon!=NULL)
	   {//the analyzed inst requires further detection, it's not FDD 
		   middletest->FTUA='N';
		  tempnodepc=tempnodepc->nextprocon;
		  checknode=headtest;
		  testcounter=0;
		  assert(tempnodepc->PC!='P');
	      while(tempnodepc!=NULL)
		   {
			  
			  if(tempnodepc->PC=='P')
				   break;
			  if(tempnodepc->PC=='C')
		       {
                while(checknode!=NULL)
					{
					if(checknode->insno==tempnodepc->instnumber)
						break;
					checknode=checknode->nexttdd;
				    }
				if((checknode==NULL)&&(testcounter<WINSIZE+1))
					{
				node_pc = tempnodepc-> des_pro;
				
			    nodetest=(TESTTDDPTR)calloc(1,sizeof(TESTTDD));
	            nodetest->insno=tempnodepc->instnumber;
				/* add pointer to the produce node */
				
				nodetest -> des_pro = node_pc;
			    nodetest->FTUA='N';
				nodetest->outreg=tempnodepc->outreg;
				nodetest->opcode=tempnodepc->opcode;
				nodetest->MR=tempnodepc->MR;
			    reartest->nexttdd=nodetest;
	            nodetest->nexttdd=NULL;
	            reartest=nodetest; 
                testcounter++;
			        }
				assert(testcounter<=WINSIZE+1);
				checknode=headtest;
				tempnodepc=tempnodepc->nextprocon;
		       }
			   
		   }
		 
	   }

	 
	  else /* ACE instruction */
		{
			 middletest->FTUA='A';
			 firstinst->FT='A';
			break;
		}
	
	  if(middletest->nexttdd!=NULL)
		    middletest=middletest->nexttdd;
	  else
			middletest=NULL;
		
	}
   //end of dependence chain checking
    
	if((middletest==NULL)&&(firstinst->FT!='A'))
	{
		 /* the anlyzed instruction is TDD, further detection is required to 
            decide whether it is TDD_reg or TDD_mem */
		 firstinst->FT='T';
		if(firstinst->counted==0)
		 {
		  middletest=headtest;
		  while(middletest!=NULL)
			{
			if(middletest->MR=='M')
				break;
			  middletest=middletest->nexttdd;
			}
		  if(middletest==NULL)
			{
			  tddregcounter++;
			  sum_cycle(FDDTDD,firstinst->resident_cycle,firstinst->trivial_flag, INST_QUEUE);
			  sum_cycle(FDDTDD,firstinst->commit_time-firstinst->rob_time, firstinst->trivial_flag,REORDER_BUFFER);
			  firstinst->FDDTDDRM='r';
			  }
		  else 
			{
			  tddmemcounter++;
			  sum_cycle(FDDTDD,firstinst->resident_cycle,firstinst->trivial_flag,INST_QUEUE);
			  sum_cycle(FDDTDD,firstinst->commit_time-firstinst->rob_time, firstinst->trivial_flag,REORDER_BUFFER);
			  firstinst->FDDTDDRM='m';
			}
		  firstinst->counted=1;
		 }
	}
	else 
	{
		
		//{
		 acecounter++;
		 sum_cycle(ACE,firstinst->resident_cycle,firstinst->trivial_flag, INST_QUEUE);
		 sum_cycle(ACE,firstinst->commit_time-firstinst->rob_time, firstinst->trivial_flag,REORDER_BUFFER);
		 sum_fuACE_cycle(firstinst);
		 firstinst->FT='A';
		//}
		/*else
		{
			firstinst->FT='T';
		 if(firstinst->counted==0)
		 {
		  middletest=headtest;
		  while(middletest!=NULL)
			{
			  if(middletest->MR=='M')
				  break;
			  middletest=middletest->nexttdd;
			}
		  if(middletest==NULL)
			{
			  tddregcounter++;
			  sum_cycle(3,firstinst->resident_cycle,firstinst->trivial_flag,1);
			  sum_cycle(3,firstinst->commit_time-firstinst->rob_time, firstinst->trivial_flag,0);
			  firstinst->FDDTDDRM='r';
			}
		  else 
			{
			  tddmemcounter++;
			  sum_cycle(3,firstinst->resident_cycle,firstinst->trivial_flag,1);
			  sum_cycle(3,firstinst->commit_time-firstinst->rob_time, firstinst->trivial_flag,0);
			  firstinst->FDDTDDRM='m';
			}
		  firstinst->counted=1;
		 }
	   }*/
	}
	 /* free the linked list used to detect TDD */
	 while(headtest!=NULL)
	{
		 temptest=headtest->nexttdd;
		 free(headtest);
		 headtest=temptest;
	}
			
}

/*check whether the high part of the register is occupied also */
int reg_low_high(LISTPTR analyzeinst)
{
	if((strcmp(MD_OP_NAME(analyzeinst->op),"addl")==0)
    ||(strcmp(MD_OP_NAME(analyzeinst->op),"s4addl")==0)
    ||(strcmp(MD_OP_NAME(analyzeinst->op),"subl")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"s4subl")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"s8addl")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"s8subl")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"addl/v (unimpl)")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"subl/v (unimpl)")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"mull")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"ldl")==0)
	||(strcmp(MD_OP_NAME(analyzeinst->op),"stl")==0))
		return 1;
	else return 0;
}




		
void reg_time_sum()
{
	tick_t ACE_time_sum=0;
    tick_t unACE_time_sum=0;
	tick_t unknown_time_sum=0;
	tick_t test_time_sum=0;
	


	
	int reg_no=1;
	
	for(reg_no=1;reg_no<regs_num_int_p_regs+31+8+1;reg_no++)
	{
		//sum=reg_array[reg_no].ACE_time+reg_array[reg_no].unACE_time+reg_array[reg_no].unknown_time+reg_array[reg_no].test_time;
	
		ACE_time_sum=ACE_time_sum+reg_array[reg_no].ACE_time;
        unACE_time_sum=unACE_time_sum+reg_array[reg_no].unACE_time;
        unknown_time_sum=unknown_time_sum+reg_array[reg_no].unknown_time;
		test_time_sum=test_time_sum+reg_array[reg_no].test_time;
        //original_unACE_sum=original_unACE_sum+reg_array[reg_no].original_unACE;

		//sum=reg_array[reg_no].ACEL_time+reg_array[reg_no].unACEL_time+reg_array[reg_no].unknownL_time+reg_array[reg_no].testL_time;
		
		
		//ACE_time_sum2=ACE_time_sum2+reg_array[reg_no].ACEL_time;
        //unACE_time_sum2=unACE_time_sum2+reg_array[reg_no].unACEL_time;
        //unknown_time_sum2=unknown_time_sum2+reg_array[reg_no].unknownL_time;
		//test_time_sum2=test_time_sum2+reg_array[reg_no].testL_time;
		//original_unACE_sum2=original_unACE_sum2+reg_array[reg_no].original_unACEL;
        
	}
 
	 
	   
	  rf_AVF=(float)(ACE_time_sum)/(float)(ACE_time_sum+unACE_time_sum+unknown_time_sum+test_time_sum);
	
	
	
}



	
void identifyFDDTDD()
{
      PROCONPTR isfdd;
      REGMEMPTR producerm;
	  LISTPTR analyzeinst;	  
	  analyzeinst=firstinst;
	 /* the instruction is NOP, it's unACE instruction, further identification is unnecessary */
   if(analyzeinst->opcode==NOP)
	 {
		  nop++;
		  analyzeinst->FT='O';
		  sum_cycle(NOP,analyzeinst->resident_cycle,0, INST_QUEUE);
		  sum_cycle(NOP,analyzeinst->commit_time-analyzeinst->rob_time, 0,REORDER_BUFFER);
	 }
	/* the instruction is prefetching, it's unACE instruction, further identification is unnecessary */
   else if(analyzeinst->opcode==PREFETCH)
	 {
		 prefetch++;
		 analyzeinst->FT='P';
		 sum_cycle(PREFETCH,analyzeinst->resident_cycle,0, INST_QUEUE);
		 sum_cycle(PREFETCH,analyzeinst->commit_time-analyzeinst->rob_time,0,REORDER_BUFFER);
	 }
   else
    {
	  /*
	  //the analyzed instruction is FDD, and hasn't been counted yet
      if((analyzeinst->FT=='F')&&(analyzeinst->FDDTDDRM=='r')&&(analyzeinst->counted==0))
	  { fddregcounter++;
	    sum_cycle(3,analyzeinst->resident_cycle,analyzeinst->trivial_flag, 1);
		sum_cycle(3,analyzeinst->commit_time-analyzeinst->rob_time, analyzeinst->trivial_flag,0);
	  }
      if((analyzeinst->FT=='F')&&(analyzeinst->FDDTDDRM=='m')&&(analyzeinst->counted==0))
	 {   fddmemcounter++;
	     sum_cycle(3,analyzeinst->resident_cycle,analyzeinst->trivial_flag,1);
		 sum_cycle(3,analyzeinst->commit_time-analyzeinst->rob_time, analyzeinst->trivial_flag,0);
	  }
	  //the analyzed instruction is TDD, and hasn't been counted yet
	  if((analyzeinst->FT=='T')&&(analyzeinst->FDDTDDRM=='m')&&(analyzeinst->counted==0))
	 {   tddmemcounter++;
	    sum_cycle(3,analyzeinst->resident_cycle,analyzeinst->trivial_flag,1);
		sum_cycle(3,analyzeinst->commit_time-analyzeinst->rob_time, analyzeinst->trivial_flag,0);
	 }
	  if((analyzeinst->FT=='T')&&(analyzeinst->FDDTDDRM=='r')&&(analyzeinst->counted==0))
	 {    tddregcounter++;
	     sum_cycle(3,analyzeinst->resident_cycle,analyzeinst->trivial_flag,1);
		 sum_cycle(3,analyzeinst->commit_time-analyzeinst->rob_time, analyzeinst->trivial_flag,0);
	 }
	 //the analyzed instruction is ACE, and hasn't been counted yet
	  if((analyzeinst->FT=='A')&&(analyzeinst->counted==0))
	 {	  acecounter++;
	    sum_cycle(4,analyzeinst->resident_cycle,analyzeinst->trivial_flag,1);
		sum_cycle(4,analyzeinst->commit_time-analyzeinst->rob_time, analyzeinst->trivial_flag,0);
		 sum_fuACE_cycle(analyzeinst);

	 }
	 */
	 /* identify whether the instruction is ACE or not */
	//  if(analyzeinst->FT=='N')
    // {
		
       /* detect whether the instruction is FDD */
		isfdd=detectFDD_first(analyzeinst);
		/* the instruction is not FDD, should detect whether it is TDD */
		if((isfdd!=NULL)&&(isfdd->PC!='U'))
			{
			detectTDD();	
		    }
		
	// }

   /*count the trivial instruction */
  if(analyzeinst->FT=='A')
	{
	  if((analyzeinst->trivial_flag>0)&&(analyzeinst->trivial_flag<30))
	  
	  trivial[analyzeinst->trivial_flag-1]++;
	 
	}

     /* identification finished, delete the nodes in the table*/
	 if((analyzeinst->rs!=-1)&&(analyzeinst->rs!=31))
	{
		 /*delete reg consumer node for all kinds of inst*/
		 if(analyzeinst->src_reg1==INTEGER)
	         producerm=reg_head+analyzeinst->rs;
		 else
             producerm=fp_reg_head+analyzeinst->rs;
		 if(((analyzeinst->trivial_flag<22)&&(analyzeinst->trivial_flag>7))||(analyzeinst->trivial_flag==29))
		  /* modify analyzeinst->FT to be FDD, because it doesn't matter if the value in 
	         this register is wrong, do this modification is for regsiter AVF computation */
	        analyzeinst->FT='F';
	     //reg_time_counter(analyzeinst->rs, analyzeinst, 'C');
	     deletepc(producerm,analyzeinst,0);
	}
	
	 if((analyzeinst->rt!=-1)&&(analyzeinst->rt!=31))
	{
		/*delete reg consumer node for all kinds of inst*/
		if(analyzeinst->src_reg2==INTEGER)
		    producerm=reg_head+analyzeinst->rt;
		else
           producerm=fp_reg_head+analyzeinst->rt;

		 if((analyzeinst->trivial_flag<8)&&(analyzeinst->trivial_flag>0))
		/* modify analyzeinst->FT to be FDD, because it doesn't matter if the value in 
	       this register is wrong, do this modification is for regsiter AVF computation */
			analyzeinst->FT='F';
	    /* if the first and the second register is the same, we don't need to consider its AVF */
		// if(analyzeinst->rs!=analyzeinst->rt)
		    //reg_time_counter(analyzeinst->rt, analyzeinst, 'C');
         deletepc(producerm,analyzeinst,0);
	}

	if(analyzeinst->opcode==LOAD)
	{
		/*delete mem consume node for load instruction */
		deletepc(analyzeinst->load_mem, analyzeinst, 1);
	}
	
	if(analyzeinst->opcode==STORE)
	{
		/* use the pointer to find out the producerm */
		/*delete mem produce node for store instruction*/
		producerm = analyzeinst-> out_regmem;
       assert(producerm!=NULL);
       deletepc(producerm,analyzeinst,1);

	}

	 if((analyzeinst->opcode!=STORE)&&(analyzeinst->outreg!=-1)&&(analyzeinst->outreg!=31))
	{
     /* delete the register producer nodes */
	  if(analyzeinst->dest_reg==INTEGER)
           producerm=reg_head+analyzeinst->outreg;
	  else
		  producerm=fp_reg_head+analyzeinst->outreg;
	 // reg_time_counter(analyzeinst->outreg, analyzeinst, 'P');
      deletepc(producerm,analyzeinst,0);
	}
}

     
	 firstinst=firstinst->nextinst;
     free(analyzeinst);
	

}



void data_dump()
{
	
	float IQ_AVF;
	float ROB_AVF;
	float FU_AVF;
	float wakeup_AVF;
	
  if(datadump)
  {
    //if(((sim_num_insn-WINSIZE)%(1000*interval_inst)==0)&&(sim_num_insn>WINSIZE))
    if((sim_num_insn>WINSIZE))
	{
		assert((1000*interval_inst)==(fddregcounter+fddmemcounter+tddregcounter+tddmemcounter+unknown+acecounter+nop+prefetch));
	  if(sim_avffd)
	   fprintf(sim_avffd,"%ld ", (signed long)((sim_num_insn-WINSIZE)/(1000*interval_inst)));
	  else
	    printf("%ld ", (signed long)((sim_num_insn-WINSIZE)/(1000*interval_inst)));
	
	  cycle_num=sim_cycle-cycle_num;  

      IQ_AVF=((float)(IQACE_cycle5+IQACE_cycle4+IQACE_cycle3+IQACE_cycle2+IQACE_cycle1))*100.0000/(cycle_num*32.0000*(float)map_int_issue_size);
	  ROB_AVF=((float)(robACE_cycle1+robACE_cycle2+robACE_cycle3))*100.0000/(cycle_num*76.0000*(float)map_rb_nelem);
	  FU_AVF=((float)(fuACE_cycle6+fuACE_cycle5+fuACE_cycle4+fuACE_cycle3+fuACE_cycle2+fuACE_cycle1))*100.0000/(cycle_num*64.0000*3.0000*(float)(res_ialu+res_imult+res_fpalu+res_fpmult));
	  wakeup_AVF=((float)cycle_wakeup[(sim_num_insn%WINSIZE)/(1000*interval_inst)])*100.0000/(cycle_num*(float)map_int_issue_size*2.0000);

     if(sim_avffd)
	  {
	  fprintf(sim_avffd,"%ld ",fddregcounter);
      fprintf(sim_avffd,"%ld ",fddmemcounter);
      fprintf(sim_avffd,"%ld ",tddregcounter);
      fprintf(sim_avffd,"%ld ",tddmemcounter);
      fprintf(sim_avffd,"%ld ",unknown);	
	  fprintf(sim_avffd,"%ld ", nop);    
      fprintf(sim_avffd,"%ld ", acecounter);
      fprintf(sim_avffd,"%ld ", prefetch);

	  fprintf(sim_avffd,"%f ",IQ_AVF);

      fprintf(sim_avffd,"%f ",ROB_AVF);

      fprintf(sim_avffd,"%f ",FU_AVF);
	  
//	  fprintf(sim_avffd,"%f ",wakeup_AVF);
      fprintf(sim_avffd,"\n");
	  }

    else
	 {
      printf("%ld ",fddregcounter);
      printf("%ld ",fddmemcounter);
      printf("%ld ",tddregcounter);
      printf("%ld ",tddmemcounter);
      printf("%ld ",unknown);	
	  printf("%ld ", nop);    
      printf("%ld ", acecounter);
      printf("%ld ", prefetch);

	  printf("%f ",IQ_AVF);

      printf("%f ",ROB_AVF);

      printf("%f ",FU_AVF);
	  
//	  printf("%f ",wakeup_AVF);
	  printf("\n");
	 }
     
	 IQ_ACEcycle=IQ_ACEcycle+IQACE_cycle5+IQACE_cycle4+IQACE_cycle3+IQACE_cycle2+IQACE_cycle1;
     ROB_ACEcycle=ROB_ACEcycle+robACE_cycle1+robACE_cycle2+robACE_cycle3;
     FU_ACEcycle=FU_ACEcycle+fuACE_cycle6+fuACE_cycle5+fuACE_cycle4+fuACE_cycle3+fuACE_cycle2+fuACE_cycle1;
	 FDDreg_sum=FDDreg_sum+fddregcounter;
     FDDmem_sum=FDDmem_sum+fddmemcounter;
     TDDreg_sum=TDDreg_sum+tddregcounter;
     TDDmem_sum=TDDmem_sum+tddmemcounter;
      NOP_sum=NOP_sum+nop;
      unknown_sum=unknown_sum+unknown;
      ACE_sum=ACE_sum+acecounter;
      prefetch_sum=prefetch_sum+prefetch;
      
	
	/* for AVF phase classification and prediction */
	
	/*reset counters to be zero, start a new interval */
	fddregcounter=fddmemcounter=tddregcounter=tddmemcounter=unknown=0;
	nop=acecounter=prefetch=0;
	IQACE_cycle1=IQACE_cycle2=IQACE_cycle3=IQACE_cycle4=IQACE_cycle5=0;
	robACE_cycle1=robACE_cycle2=robACE_cycle3=0;
	fuACE_cycle1=fuACE_cycle2=fuACE_cycle3=fuACE_cycle4=fuACE_cycle5=fuACE_cycle6=0;

	ACEcycle1=ACEcycle2=ACEcycle3=ACEcycle4=ACEcycle5=0;
	robACEcycle1=robACEcycle2=robACEcycle3=0;
	fuACEcycle1=fuACEcycle2=fuACEcycle3=fuACEcycle4=fuACEcycle5=fuACEcycle6=0;
	
	cycle_num=sim_cycle;
	
	 
	  
	}
  }  
}


void inform_dump()
{
 reg_time_sum();
 if(datadump)
	{
	
   if(sim_avffd)
	  {
      fprintf(sim_avffd,"Overall FDD_reg: %qu.\n",FDDreg_sum);
      fprintf(sim_avffd,"Overall FDD_mem: %qu.\n",FDDmem_sum);
      fprintf(sim_avffd,"Overall TDD_reg: %qu.\n",TDDreg_sum);
      fprintf(sim_avffd,"Overall TDD_mem: %qu.\n",TDDmem_sum);
      fprintf(sim_avffd,"Overall unknown instructions: %qu.\n",unknown_sum);	
	  fprintf(sim_avffd,"Overall NOP: %qu.\n", NOP_sum);    
      fprintf(sim_avffd,"Overall ACE instructions: %qu.\n", ACE_sum);
      fprintf(sim_avffd,"Overall Prefetching: %qu.\n", prefetch_sum);
	  fprintf(sim_avffd,"Overall IQAVF: %f.\n",((float)(IQ_ACEcycle))*100.0000/(sim_cycle*32.0000*(float)map_int_issue_size));	 
      fprintf(sim_avffd,"Overall ROBAVF: %f.\n",((float)(ROB_ACEcycle))*100.0000/(sim_cycle*76.0000*(float)map_rb_nelem));    
      fprintf(sim_avffd,"Overall FUAVF: %f.\n",((float)(FU_ACEcycle))*100.0000/(sim_cycle*64.0000*3.0000*(float)(res_ialu+res_imult+res_fpalu+res_fpmult)));
	  }
   else
	  {
	  printf("Overall FDD_reg: %qu.\n",FDDreg_sum);
      printf("Overall FDD_mem: %qu.\n",FDDmem_sum);
      printf("Overall TDD_reg: %qu.\n",TDDreg_sum);
      printf("Overall TDD_mem: %qu.\n",TDDmem_sum);
      printf("Overall unknown instructions: %qu.\n",unknown_sum);	
	  printf("Overall NOP: %qu.\n", NOP_sum);    
      printf("Overall ACE instructions: %qu.\n", ACE_sum);
      printf("Overall Prefetching: %qu.\n", prefetch_sum);
	  printf("Overall IQAVF: %f.\n",((float)(IQ_ACEcycle))*100.0000/(sim_cycle*32.0000*(float)map_int_issue_size));	 
      printf("Overall ROBAVF: %f.\n",((float)(ROB_ACEcycle))*100.0000/(sim_cycle*76.0000*(float)map_rb_nelem));    
      printf("Overall FUAVF: %f.\n",((float)(FU_ACEcycle))*100.0000/(sim_cycle*64.0000*3.0000*(float)(res_ialu+res_imult+res_fpalu+res_fpmult)));
      }

    
	}
else
	{   
    if(sim_avffd)
	  {
      fprintf(sim_avffd,"Overall FDD_reg: %ld.\n",fddregcounter);
      fprintf(sim_avffd,"Overall FDD_mem: %ld.\n",fddmemcounter);
      fprintf(sim_avffd,"Overall TDD_reg: %ld.\n",tddregcounter);
      fprintf(sim_avffd,"Overall TDD_mem: %ld.\n",tddmemcounter);
      fprintf(sim_avffd,"Overall unknown instructions: %ld.\n",unknown);	
	  fprintf(sim_avffd,"Overall NOP: %ld.\n", nop);    
      fprintf(sim_avffd,"Overall ACE instructions: %ld.\n", acecounter);
      fprintf(sim_avffd,"Overall Prefetching: %ld.\n", prefetch);

	  fprintf(sim_avffd,"Overall IQAVF: %f.\n",((float)(IQACE_cycle5+IQACE_cycle4+IQACE_cycle3+IQACE_cycle2+IQACE_cycle1))*100.0000/(sim_cycle*32.0000*(float)map_int_issue_size));
      fprintf(sim_avffd,"Overall ROBAVF: %f.\n",((float)(robACE_cycle1+robACE_cycle2+robACE_cycle3))*100.0000/(sim_cycle*76.0000*(float)map_rb_nelem));
      fprintf(sim_avffd,"Overall FUAVF: %f.\n",((float)(fuACE_cycle6+fuACE_cycle5+fuACE_cycle4+fuACE_cycle3+fuACE_cycle2+fuACE_cycle1))*100.0000/(sim_cycle*64.0000*3.0000*(float)(res_ialu+res_imult+res_fpalu+res_fpmult)));
	}
	else
	  {
	  printf("Overall FDD_reg: %ld.\n",fddregcounter);
      printf("Overall FDD_mem: %ld.\n",fddmemcounter);
      printf("Overall TDD_reg: %ld.\n",tddregcounter);
      printf("Overall TDD_mem: %ld.\n",tddmemcounter);
      printf("Overall unknown instructions: %ld.\n",unknown);	
	  printf("Overall NOP: %ld.\n", nop);    
      printf("Overall ACE instructions: %ld.\n", acecounter);
      printf("Overall Prefetching: %ld.\n", prefetch);

	  printf("Overall IQAVF: %f.\n",((float)(IQACE_cycle5+IQACE_cycle4+IQACE_cycle3+IQACE_cycle2+IQACE_cycle1))*100.0000/(sim_cycle*32.0000*(float)map_int_issue_size));
      printf("Overall ROBAVF: %f.\n",((float)(robACE_cycle1+robACE_cycle2+robACE_cycle3))*100.0000/(sim_cycle*76.0000*(float)map_rb_nelem));
      printf("Overall FUAVF: %f.\n",((float)(fuACE_cycle6+fuACE_cycle5+fuACE_cycle4+fuACE_cycle3+fuACE_cycle2+fuACE_cycle1))*100.0000/(sim_cycle*64.0000*3.0000*(float)(res_ialu+res_imult+res_fpalu+res_fpmult)));
	  }
	}

  if(sim_avffd)
   fprintf(sim_avffd,"Overall register files AVF: %f.\n", 100.0000*rf_AVF);
  else
   printf("Overall register files AVF: %f.\n", 100.0000*rf_AVF);

}


void rf_time_counter(int reg_no, char type, unsigned long long timestamp)
{
  if(reg_no>0 && reg_no!=31)
  {
	assert(timestamp -reg_array[reg_no].now>=0);
	
	if(type=='P')
	{
		reg_array[reg_no].unACE_time=timestamp -reg_array[reg_no].now + reg_array[reg_no].unACE_time;
		reg_array[reg_no].now=timestamp;
		//reg_array[reg_no].unACEL_time=timestamp -reg_array[reg_no].nowL + reg_array[reg_no].unACEL_time;
		//reg_array[reg_no].nowL=timestamp;
	}
	if(type=='C')
	{
		reg_array[reg_no].ACE_time=timestamp -reg_array[reg_no].now + reg_array[reg_no].ACE_time;
		reg_array[reg_no].now=timestamp;
		//reg_array[reg_no].ACEL_time=timestamp -reg_array[reg_no].nowL + reg_array[reg_no].ACEL_time;
		//reg_array[reg_no].nowL=timestamp;
	}
	
  }
}

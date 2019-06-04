/*
 * simulate.c - sample fast functional simulator implementation
 *
 * This file is part of the Alpha simulator tool suite written by
 * Raj Desikan as part of the Bullseye project.
 * It has been written by extending the SimpleScalar tool suite written by
 * Todd M. Austin as a part of the Multiscalar Research Project.
 *  
 * 
 * Copyright (C) 1994, 1995, 1996, 1997, 1998 by Todd M. Austin
 *
 * Copyright (C) 1999 by Raj Desikan
 *
 * This source file is distributed "as is" in the hope that it will be
 * useful.  The tool set comes with no warranty, and no author or
 * distributor accepts any responsibility for the consequences of its
 * use. 
 * 
 * Everyone is granted permission to copy, modify and redistribute
 * this tool set under the following conditions:
 * 
 *    This source code is distributed for non-commercial use only. 
 *    Please contact the maintainer for restrictions applying to 
 *    commercial use.
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
 *
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

/*
 * This file implements a very fast functional simulator.  This functional
 * simulator implementation is much more difficult to digest than the simpler,
 * cleaner sim-safe functional simulator.  By default, this simulator performs
 * no instruction error checking, as a result, any instruction errors will
 * manifest as simulator execution errors, possibly causing sim-fast to
 * execute incorrectly or dump core.  Such is the price we pay for speed!!!!
 *
 * The following options configure the bag of tricks used to make sim-fast
 * live up to its name.  For most machines, defining all the options results
 * in the fastest functional simulator.
 */

/* don't count instructions flag, enabled by default, disable for inst count */
#undef NO_INSN_COUNT

#ifdef __GNUC__
/* faster dispatch mechanism, requires GNU GCC C extensions, CAVEAT: some
   versions of GNU GCC core dump when optimizing the jump table code with
   optimization levels higher than -O1 */
/* #define USE_JUMP_TABLE */
#endif /* __GNUC__ */

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


/* simulated registers 
   struct regs_t regs;
   extern struct regs_t regs;*/

/* simulated memory 
   struct mem_t *mem = NULL;*/

#ifdef TARGET_ALPHA
/* predecoded text memory */
//static struct mem_t *dec = NULL;
#endif

int dl1_flag=0;
int dtlb_flag=0;
int dll_cool=0;
int dtlb_cool=0;
int reg_flag=0;
int reg_cool=0;
int wakeup_flag=0;

int datadump;

/* for load store queue AVF, by Xin Fu*/
int commit_sq_nelem;
int issue_lq_nelem;



//counter_t sim_total_insn;
tick_t end_cycle;
tick_t finish_cycle;

tick_t regend_cycle;
tick_t regfinish_cycle;
counter_t fastfwd_number;
counter_t IQ_idle_counter;
int rob_idle_counter;
int wakeup_idle_counter;
int fu_idle_counter;


unsigned int interval_inst;
unsigned int cycleInterval_inst;

tick_t current_cycle;

struct issue_window *IQ;	/* Integer issue queues */

/* register simulator-specific options */
void
sim_reg_options(struct opt_odb_t *odb)
{

  opt_reg_header(odb, 
		 "sim-alpha: This simulator implements a detailed out of order Alpha 21264 simulator.\n\n\n");
  
  /* general simulator options */
  /* instruction limit */
  
  opt_reg_uint(odb, "-max:inst", "maximum number of inst's to execute",
	       &opt_max_insts, /* default */0, /* print */TRUE, 
	       /* format */NULL);
//printf("maximum inst is %ldK.\n", opt_max_insts);
  /* set the interval size, by Xin Fu */
  opt_reg_uint(odb, "-interval", "interval size to dump AVF data, in the unit of 1K instruction",
	       &interval_inst, /* default */1000, /* print */TRUE, 
	       /* format */NULL);

  	opt_reg_uint(odb, "-cycleInterval", "interval size to dump AVF data, in the unit of 1K cycle",
	       &cycleInterval_inst, /* default */10, /* print */TRUE, 
	       /* format */NULL);

  opt_reg_uint(odb, "-datadump", "dump AVF per interval?",
	       &datadump, /* default */1, /* print */TRUE, 
	       /* format */NULL);
   
  opt_fastfwd_count=fastfwd_number;

  /* Processor core options */
  /* The clock frequency of simulated machine */
  opt_reg_int(odb, "-mach:freq", "frequency of simulated machine",
	      &alpha_cpu_freq, /* default */500000000, /* print */TRUE, /* format */NULL);
  /* fetch queue size */
  opt_reg_int(odb, "-fetch:ifqsize", "Instruction fetch queue size(in insts)", 
	      &fetch_ifq_size, /* default */4, 
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-fetch:speed","Number of discontinuous fetches per cycle", 
	      &fetch_speed, /* default */1,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-fetch:width","Number of instructions to fetch per access",
	      &fetch_width, /* default */4,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-slot:width", "Instruction slotting width(in insts)", 
	      &slot_width, /* default */4,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-map:width", "mapping width(in insts)", 
	      &map_width, /* default */4,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:intwidth", "Integer inst issue width(in insts)", 
	      &issue_int_width, /* default */4,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:fpwidth", "fp inst issue width(in insts)", 
	      &issue_fp_width, /* default */2,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-commit:width", "commit width(in insts)", 
	      &commit_width, /* default */11,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:int_reg_lat", "Latency of integer register read",
	      &int_reg_read_latency, /* default */ 1,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:fp_reg_lat", "Latency of fp register read",
	      &fp_reg_read_latency, /* default */ 1,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:int_size", "integer issue queue size",
	      &map_int_issue_size, /* default */ 20,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:fp_size", "fp issue queue size",
	      &map_fp_issue_size, /* default */ 15,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-reg:int_p_regs", "Number of integer physical registers",
	      &regs_num_int_p_regs, /* default */ 41,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-reg:fp_p_regs", "Number of fp physical registers",
	      &regs_num_fp_p_regs, /* default */ 41,
	      /* print */ TRUE, /* format */NULL);
  /* reorder buffer options */
  opt_reg_int(odb, "-rbuf:size",
	      "reorder buffer size (<number of entries>)",
	      &map_rb_nelem, /* default */ 80,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-lq:size",
	      "load queue size (<number of entries>)",
	      &issue_lq_nelem, /* default */ 32,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-sq:size",
	      "store queue size (<number of entries>)",
	      &commit_sq_nelem, /* default */ 32,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:ialu",
	      "Number of integer alus",
	      &res_ialu,/* default */4,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:imult",
	      "Number of integer multipliers/dividers",
	      &res_imult,/* default */4,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:fpalu",
	      "Number of fp alus",
	      &res_fpalu,/* default */1,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:fpmult",
	      "Number of fp multipliers",
	      &res_fpmult,/* default */1,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:iclus",
	      "Number of integer clusters",
	      &res_int_clusters,/* default */2,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:fpclus",
	      "Number of fp clusters",
	      &res_fp_clusters,/* default */1,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-res:delay",
	      "Minimum cross cluster delay",
	      &res_cross_clus_delay,/* default */1,
	      /* print */TRUE, /* format */NULL);
  
  /* Memory hierarchy options */
  /* cache options */
  opt_reg_string_list(odb, "-cache:define", "cache configuration",
		      cache_configs, MAX_NUM_CACHES, &cache_nelt, NULL,
		      /* print */TRUE, /* format */NULL, /* accrue */TRUE);
  opt_reg_note(odb,
	       "  The cache config parameter <config> has the following format:\n"
	       "\n"
	       "    <name>:<nsets>:<bsize>:<subblock>:<asso>:<repl>:<lat>:<trans>:<# resources>:<res code>"
	       "\n"
	       "    <name>   - name of the cache being defined\n"
	       "    <nsets>  - number of sets in the cache\n"
	       "    <bsize>  - block size of the cache\n"
	       "    <assoc>  - associativity of the cache\n"
	       "    <repl>   - block replacement strategy, 'l'-LRU, 'f'-FIFO, 'r'-random, 'F'-LFU\n"
	       "    <lat>    - hit latency\n"
	       "    <trans>  - Translation policy, vivt, vipt, pipt\n"
	       "    <pref>   - prefetch enabled if 1\n"
	       "\n"
	       "    Examples:   -cache:define           DL1:512:64:0:2:F:3:vipt:0:1"
	       "                -dtlb dtlb:128:4096:32:r\n"
	       );
  opt_reg_flag(odb, "-cache:flush", "flush caches on system calls",
	       &flush_on_syscalls, /* default */FALSE, /* print */TRUE, 
	       NULL);

  opt_reg_string(odb, "-cache:dcache",
		 "defines name of first-level data cache",
		 &dcache_name, /* default */NULL,
		 /* print */TRUE, /* format */NULL);

  

  opt_reg_string(odb, "-cache:icache",
		 "defines name of first-level instruction cache",
		 &icache_name, /* default */NULL,
		 /* print */TRUE, /* format */NULL);

  opt_reg_int(odb, "-cache:vbuf_lat", 
	      "Additional victim buffer latency", 
	      &victim_buf_lat, /* default */ 1,
	      /* print */TRUE, /* format */NULL);
  
  opt_reg_int(odb, "-cache:vbuf_ent",
	      "Number of entries in the victim buffer",
	      &victim_buf_ent, /* default */ 8,
	      /* print */TRUE, /* format */NULL);
  
  opt_reg_int(odb, "-cache:mshrs",
		 "Sets maximum number of MSHRs per cache",
		 &regular_mshrs, /* default */8,
		 /* print */TRUE, /* format */NULL);

  opt_reg_int(odb, "-cache:prefetch_mshrs",
		 "Sets maximum number of MSHRs per cache",
		 &prefetch_mshrs, /* default */2,
		 /* print */TRUE, /* format */NULL);

  opt_reg_int(odb, "-cache:mshr_targets",
		 "Sets number of allowable targets per mshr",
		 &mshr_targets, /* default */4,
		 /* print */TRUE, /* format */NULL);
  

		 /* bus options */
  opt_reg_string_list(odb, "-bus:define", "bus configuration",
		 bus_configs, MAX_NUM_BUSES, &bus_nelt, NULL,
		 /* print */TRUE, /* format */NULL, /* accrue */TRUE);

	      
  /* mem options */
  opt_reg_string_list(odb, "-mem:define", "memory bank name",
		 mem_configs, MAX_NUM_MEMORIES, &mem_nelt, NULL,
		 /* print */TRUE, /* format */NULL, /* accrue */TRUE);
  opt_reg_int(odb, "-mem:queuing_delay", "Queuing delay enabled in memory",
	      &mem_queuing_delay, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-bus:queuing_delay", "Queuing delay enabled in buses",
	      &bus_queuing_delay, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  /* Options for Vinodh Cuppu's code */
  opt_reg_int(odb, "-mem:clock_multiplier",
	      "cpu freq / dram freq", &clock_multiplier, 6, TRUE, NULL);
  opt_reg_int(odb, "-page_policy", "0 - openpage, 1 - closepage autoprecharge", 
	      &page_policy, 0, TRUE, NULL);
  opt_reg_int(odb, "-mem:ras_delay", "time between start of ras command and cas command",
	      &ras_delay, 1, TRUE, NULL);
  opt_reg_int(odb, "-mem:cas_delay", "time between start of cas command and data start",
	      &cas_delay, 1, TRUE, NULL);
  opt_reg_int(odb, "-mem:pre_delay", "time between start of precharge command and ras command",
	      &pre_delay, 1, TRUE, NULL);
  opt_reg_int(odb, "-mem:data_rate", "1 - single data rate. 2 - double data rate",
	      &data_rate, 1, TRUE, NULL);
  opt_reg_int(odb, "-mem:bus_width", "width of bus from cpu to dram",
	      &bus_width, 16, TRUE, NULL);
  opt_reg_int(odb, "-mem:chipset_delay_req", "delay in chipset for request path",
	      &chipset_delay_req, 2, TRUE, NULL);
  opt_reg_int(odb, "-mem:chipset_delay_return", "delay in chipset in data return path",
	      &chipset_delay_return, 2, TRUE, NULL);
  
/* End of remove block - HRISHI */
	      
  /* TLB options */

  opt_reg_string_list(odb, "-tlb:define",
		 "tlb configuration",
		 tlb_configs, MAX_NUM_TLBS, &tlb_nelt, NULL,
		 /* print */TRUE, /* format */NULL, /* accrue */TRUE);

  opt_reg_string(odb, "-tlb:itlb",
		 "Name of L1 ITLB",
		 &itlb_name, NULL, /* print */TRUE, NULL);

  opt_reg_string(odb, "-tlb:dtlb",
		 "name of L2 dtlb",
		 &dtlb_name, NULL, /* print */TRUE, NULL);
  
  /* Predictor options */
  opt_reg_int(odb, "-bpred:line_pred", 
	      "Line predictor", 
	      &line_predictor, /* default */ TRUE,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-line_pred:ini_value", "Initial value of line pred bits",
	      &line_pred_ini_value, /* default */ 0,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-line_pred:width", "Line predictor width",
	      &line_pred_width, /* default */ 4,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-way:pred",
	      "Way predictor latency",
	      &way_pred_latency, /* default */1,
	      /* print */TRUE, /* format */NULL);
  /* branch predictor options */
  
  opt_reg_note(odb, 
	       "  Branch predictor configuration examples for 2-level predictor:\n"
	       "  Configurations:   N, M, W, X\n"
	       "   N   # entries in first level (# of shift register(s))\n"
	       "   W   width of shift register(s)\n"
	       "   M   # entries in 2nd level (# of counters, or other FSM)\n"
	       "   X   (yes-1/no-0) xor history and address for 2nd level index\n"
	       "  Sample predictors:\n"
	       "   GAg     : 1, W, 2^W, 0\n"
	       "   GAp     : 1, W, M (M > 2^W), 0\n"
	       "   PAg     : N, W, 2^W, 0\n"
	       "   PAp     : N, W, M (M == 2^(N+W)), 0\n"
	       "   gshare  : 1, W, 2^W, 1\n"
	       "   Predictor `comb' combines a bimodal and a 2-level predictor.\n"
	       );

  opt_reg_string(odb, "-bpred",
		 "branch predictor type {nottaken|taken|perfect|bimod|2lev|comb|21264}",
		 &pred_type, /* default */"21264",
		 /* print */TRUE, /* format */NULL);

  opt_reg_int_list(odb, "-bpred:bimod",
		   "bimodal predictor config (<table size>)",
		   bimod_config, bimod_nelt, &bimod_nelt,
		   /* default */bimod_config,
		   /* print */TRUE, /* format */NULL, /* !accrue */FALSE);
  opt_reg_int_list(odb, "-bpred:2lev",
		   "2-level predictor config "
		   "(<l1size> <l2size> <hist_size> <xor>)",
		   twolev_config, twolev_nelt, &twolev_nelt,
		   /* default */twolev_config,
		   /* print */TRUE, /* format */NULL, /* !accrue */FALSE);

  opt_reg_int_list(odb, "-bpred:21264",
		   "21264 predictor config "
		   "(<l1size> <l2size> <lhist_size> <gsize> <ghist_size> <csize> <chist_size>)",
		   pred_21264_config, pred_21264_nelt, &pred_21264_nelt,
		   /* default */pred_21264_config,
		   /* print */TRUE, /* format */NULL, /* !accrue */FALSE);

  opt_reg_int_list(odb, "-bpred:comb",
		   "combining predictor config (<meta_table_size>)",
		   comb_config, comb_nelt, &comb_nelt,
		   /* default */comb_config,
		   /* print */TRUE, /* format */NULL, /* !accrue */FALSE);
  opt_reg_int(odb, "-bpred:ras",
              "return address stack size (0 for no return stack)",
              &ras_size, /* default */32,
              /* print */TRUE, /* format */NULL);

  opt_reg_int_list(odb, "-bpred:btb",
		   "BTB config (<num_sets> <associativity>)",
		   btb_config, btb_nelt, &btb_nelt,
		   /* default */btb_config,
		   /* print */TRUE, /* format */NULL, /* !accrue */FALSE);
  
  /* Alpha 21264 specific low level feature options */
  /* st wait table size */
  opt_reg_int(odb, "-fetch:stwait", "size of st wait table (0 for no table)", 
	      &fetch_st_table_size, /* default */1024,
	      /* print */ TRUE, /* format */NULL);

  opt_reg_int(odb, "-line_pred:spec_update", "Line predictor speculative update",
	      &line_pred_spec_update, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-bpred:spec_update", "branch predictor speculative update",
	      &bpred_spec_update, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-issue:no_slot_clus", "disable slotting and clustering",
	      &issue_no_slot_clus, /* default */ FALSE,
	      /* print */ TRUE, /* format */NULL);
  
  opt_reg_int(odb, "-slot:adder", "Adder for computing branch targets",
	      &slot_adder, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-slot:slotting", "Whether to use static slotting",
	      &static_slotting, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-map:early_retire", "Early inst. retire enabled",
	      &early_inst_retire, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-wb:load_trap", "Load traps enabled",
	      &load_replay_trap, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-wb:diffsize_trap", "Different size traps enabled",
	      &diffsize_trap, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-cache:target_trap", "Trap if two loads map to same MSHR target",
	      &cache_target_trap, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
  opt_reg_int(odb, "-cache:addr_trap", "Trap if two loads map to same cache line but have different addresses",
	      &cache_diff_addr_trap, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
   opt_reg_int(odb, "-cache:mshrfull_trap", "Trap if MSHRs are full",
	      &cache_mshrfull_trap, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
   opt_reg_int(odb, "-map:stall", "Stall for 3 cycles of map < 8 free regs",
	      &map_stall, /* default */ TRUE,
	      /* print */ TRUE, /* format */NULL);
   opt_reg_int(odb, "-cache:perfectl2", "simulate perfect L2 cache",
	      &perfectl2, /* default */ FALSE,
	      /* print */ TRUE, /* format */NULL);   
  opt_reg_int(odb, "-load:spec",
	      "Use load use speculation",
	      &wb_load_use_speculation, /* default */TRUE,
	      /* print */TRUE, /* format */NULL);
  opt_reg_int(odb, "-prefetch:dist",
	      "Number of blocks to prefetch on a icache miss",
	      &prefetch_dist, /* default */4,
	      /* print */TRUE, /* format */NULL);
}

/* --------------------------------------------------------------- */
/* Memory hierarchy setup code */

void *scan_resources(char *name, enum resource_type *type)
{
  int i;

  for (i=0; i<num_caches; i++)
  {
    if (!strcmp(name, caches[i]->name)) {
      *type = Cache;
      return((void *) caches[i]);
    }
  }
  for (i=0; i<num_tlbs; i++)
  {
    if (!strcmp(name, tlbs[i]->name)) {
      *type = Cache;
      return((void *) tlbs[i]);
    }
  }
  for (i=0; i<num_buses; i++)
  {
    if (!strcmp(name, buses[i]->name))
    {
      *type = Bus;
      return((void *) buses[i]);
    }
  }
  for (i=0; i<num_mem_banks; i++)
  {
    if (!strcmp(name, mem_banks[i]->name))
    {
      *type = Memory;
      return((void *) mem_banks[i]);
    }
  }
  return((void *) NULL);
}

void create_all_caches(int cache_num_caches)
{
  int i, j;
  char name[128], repl, *resource_name[MAX_NUM_RESOURCES];
  char trans[5];
  int nsets, bsize, assoc, hitl, prefetch, resources, resource_code, subblock;


  for (i=0; i<num_caches; i++)
    {
      if (sscanf(cache_configs[i], "%[^:]:%d:%d:%d:%d:%c:%d:%[^:]:%d:%d:%d",
		 name, &nsets, &bsize, &subblock, &assoc, &repl, &hitl, 
		 trans, &prefetch, &resources, &resource_code) != 11)
	fatal("bad cache parms: <name>:<nsets>:<bsize>:<subblock>:<assoc>:<repl>:<hitlatency>:<translation>:<prefetch>:<# resources>:<resource code>:[resource names]*");
      /* Read in resource names, have to do this later since # of names are variable */
      process_resources(cache_configs[i], resource_name, resources, 11);
     
	  /* for address-based AVF */
	  //printf("cache_configs :%c\n",cache_configs[i]);
	  //printf("cache configuration is :%s, %d, %d, %d.\n", name, nsets, bsize, assoc);

      caches[i] = cache_timing_create(name, nsets, bsize, subblock, 
				      /*balloc*/ FALSE,
				      /*usize*/ 0, assoc, hitl, 
				      cache_char2policy(repl), 
				      cache_string2trans(trans), 
				      prefetch, resources, resource_code,
				      resource_name); 
	  //printf("sucessfully create cache %s.\n",name);
            
      for (j=0; j<resources; j++) 
	free(resource_name[j]);
    }
  /* create victim buffer */
  if (victim_buf_lat > 0) {
    int i;
    struct cache_blk *blk;
    blk = (struct cache_blk *)malloc(sizeof(struct cache_blk));
    vbuf.way_tail = blk;
	/*for vbuf AVF computation, by Xin Fu */
	/*only set for L1 dcache, since Sim-alpha only caches blocks from L1 Dcache to vbuf.*/
	
	
    vbuf.way_tail->way_next = NULL;
    vbuf.way_head = blk;
	//printf("flag 1.\n");
	//avf_initial(dcache->bsize, dcache->tag_shift, blk);
    for (i=0;i<victim_buf_ent-1;i++) {
      blk = (struct cache_blk *)malloc(sizeof(struct cache_blk));
      vbuf.way_head->way_prev = blk;
	  /*for vbuf AVF computation, by Xin Fu */
	  //printf("flag 2.\n");
	  //avf_initial(dcache->bsize, dcache->tag_shift, blk);
      blk->way_next = vbuf.way_head;
      vbuf.way_head = blk;
    }
   //printf("flag 1.\n");
	avf_vbuf_initial();
  }
   //printf("sucessfully create victim cache.\n",name);
}

void create_all_buses(int num_buses)
{
  int i, j, width, arbitration, inf_bandwidth, resources, resource_code;
  float proc_cycles;
  char name[128];
  char *resource_name[MAX_NUM_RESOURCES];

  for (i=0; i<num_buses; i++)
    {
      if (sscanf(bus_configs[i], "%[^:]:%d:%f:%d:%d:%d:%d", name, &width, 
		 &proc_cycles, &arbitration, &inf_bandwidth, &resources, 
		 &resource_code) != 7)
	fatal("bad bus parameters: <name>:<width>:<cycle latency>:<arbitration penalty>:<inf bandwidth>:<# resources>:<resource code>:[resource names]*");
      process_resources(bus_configs[i], resource_name, resources, 7);
      buses[i] = bus_create(name, width, proc_cycles, arbitration, 
				inf_bandwidth, resources, resource_code, 
				resource_name); 
      for (j=0; j<resources; j++) 
	free(resource_name[j]);
    }
}

void create_all_mem_banks(int num_mem_banks)
{
  int i;
  char name[128];

  for (i=0; i<num_mem_banks; i++)
    {
      if (sscanf(mem_configs[i], "%[^:]", name) != 1)
	fatal("bad memory parameters: <name> - %s", mem_configs[i]);
      mem_banks[i] = mem_bank_create(name);
    }
}

void create_tlbs()
{
  int i, j;
  char name[128], repl, *resource_name[MAX_NUM_RESOURCES];
  char trans[5];
  int nsets, bsize, assoc, hitl, resources, resource_code, prefetch, subblock;
  
  
  for (i=0; i<num_tlbs; i++)
    {
      if (sscanf(tlb_configs[i], "%[^:]:%d:%d:%d:%d:%c:%d:%[^:]:%d:%d:%d",
		 name, &nsets, &bsize, &subblock, &assoc, &repl, &hitl, trans, 
		 &prefetch, &resources, &resource_code) != 11)
	fatal("bad tlb parms: <name>:<nsets>:<bsize>:<subblock>:<assoc>:<repl>:<hitlatency>:<translation>:<prefetch>:<# resources>:<resource code>:[resource names]*");

      /* Read in resource names, have to do this later since # of names are variable */
      process_resources(tlb_configs[i], resource_name, resources, 11);
      tlbs[i] = cache_timing_create(name, nsets, bsize, subblock, 
				    /*balloc*/ FALSE, /*usize*/ 0, assoc, 
				    hitl, cache_char2policy(repl), 
				    cache_string2trans(trans), prefetch, 
				    resources, resource_code, 
				    resource_name);
	   //printf("sucessfully create tlb cache %s.\n",name);
      for (j=0; j<resources; j++) 
	free(resource_name[j]);
    }
}

void link_memory_hierarchy()
{
  int i, j;
  struct cache *cp;
  struct bus *bp;
  enum resource_type type;
  //printf("link_memory_hierarchy is running.\n");
  for (i=0; i<num_caches; i++)
  {
    cp = caches[i];

    for (j=0; j<cp->num_resources; j++)
    {
      cp->resources[j] = scan_resources(cp->resource_names[j], &type);
	  //printf("scan_resources finished\n");
      if (!cp->resources[j])
      {
	fatal("Can't find resource name %s for cache %s\n", 
	      cp->resource_names[j], cp->name);
      }
      cp->resource_type[j] = type;

      /* This is a hack to link in the TLBs.  We assume that the dtlb is always
	 used in the hierarchy (wherever address translation needs to be done)
	 unless the cache is the icache and there is an itlb explicitly 
	 defined */

      if (cp->trans != VIVT)
	cp->tlb = ((cp == icache) && itlb) ? itlb : dtlb;
	  //printf("before free function.\n");
      free(cp->resource_names[j]);
/***************************************************************************************************************
      I make this statement to be comment when debugging, but I am not sure whether it is very important. 
***************************************************************************************************************/
	  //printf("finished free function.\n");
    }  
  }
  //printf("finished checking caches.\n");
  for (i=0; i<num_tlbs; i++)
  {
    cp = tlbs[i];

    for (j=0; j<cp->num_resources; j++)
    {
      cp->resources[j] = scan_resources(cp->resource_names[j], &type);
      if (!cp->resources[j])
      {
	fatal("Can't find resource name %s for tlb %s\n", 
	      cp->resource_names[j], cp->name);
      }
      cp->resource_type[j] = type;
      free(cp->resource_names[j]);
    }  
  }
  //printf("finished checking tlbs.\n");
  for (i=0; i<num_buses; i++)
  {
    bp = buses[i];
    for (j=0; j<bp->num_resources; j++)
    {
      bp->resources[j] = scan_resources(bp->resource_names[j], &type);
      if (!bp->resources[j])
      {
	fatal("Can't find resource name %s for bus %s\n", 
	      bp->resource_names[j], bp->name);
      }
      bp->resource_type[j] = type;
      free(bp->resource_names[j]);
    }  
  }
  //printf("finished checking buses.\n");
}


/* check simulator-specific option values */
void
sim_check_options(struct opt_odb_t *odb, int argc, char **argv)
{
  int i;
  struct opt_opt_t *an_opt;
  
  /* Check if clock frequency of simulated machine is specified correctly */ 
  if (alpha_cpu_freq < 0)
    fatal("Frequency of simulated machine should be positive");

  /* check for bpred options */
  if (!mystricmp(pred_type, "perfect"))
  {
    /* perfect predictor */
    pred = NULL;
    pred_perfect =TRUE;
  }/* end if */
  else if (!mystricmp(pred_type, "taken"))
  {
    /* static predictor, taken */
     pred = bpred_create(BPredTaken, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
  }/* end else if */
  else if (!mystricmp(pred_type, "nottaken"))
  {
    /* static predictor, nottaken */
     pred = bpred_create(BPredNotTaken, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
  }/* end else if */
  else if (!mystricmp(pred_type, "bimod"))
  {
    /* bimodal predictor, bpred_create() checks BTB_SIZE */
    if (bimod_nelt != 1)
      fatal("bad bimod predictor config (<table_size)");
    if (btb_nelt != 2)
      fatal("bad btb config (<num_sets> <associativity>)");

    pred = bpred_create(BPred2bit,
			/* bimod table size */bimod_config[0],
			/* 2lev l1 size */0,
			/* 2lev l2 size */0,
			/* meta table size */0,
			/* history reg size */0,
			/* history xor address */0,
			/* btb stes */btb_config[0],
			/* btb assoc */btb_config[1],
			/* ret-addr stack size */ras_size,
			0,
			0,
			0,
			0);
  }/* end else if */
  else if (!mystricmp(pred_type, "2lev"))
  {
    /* 2-level adaptive predictor, bpred_create() checks args */
    if (twolev_nelt != 4)
      fatal("bad   2-level pred config (<l1size> <l2size> <hist_size> <xor>)");
    if (btb_nelt != 2)
      fatal("bad btb config (<num_sets> <associativity>)");

    pred = bpred_create(BPred2Level,
			/* bimod table size */0,
			/* 2lev l1 size */twolev_config[0],
			/* 2lev l2 size */twolev_config[1],
			/* meta table size */0,
			/* history reg size */twolev_config[2],
			/* history xor address */twolev_config[3],
			/* btb stes */btb_config[0],
			/* btb assoc */btb_config[1],
			/* ret-addr stack size */ras_size,
			0,
			0,
			0,
			0);
  }/* end else if */
  else if (!mystricmp(pred_type, "21264"))
  {
    /* 21264 predictor, bpred_create() checks args */
    if (pred_21264_nelt != 7)
      fatal("bad   21264 pred config (<l1size> <l2size> <lhist_size> <gsize> <ghist_size> <csize> <chist_size>)");

    pred = bpred_create(BPred21264,
			/* bimod table size */0,
			/* 21264 l1 size */pred_21264_config[0],
			/* 21264 l2 size */pred_21264_config[1],
			/* meta table size */0,
			/* local history reg size */pred_21264_config[2],
			/* history xor address */0,
			/* btb stes */btb_config[0],
			/* btb assoc */btb_config[1],
			/* ret-addr stack size */ras_size,
			/* 21264 gsize */pred_21264_config[3],
			/* 21264 ghist_size */pred_21264_config[4],
			/* 21264 csize */pred_21264_config[5],
			/* 21264 chist_size */pred_21264_config[6]);
  }/* end else if */
  else if (!mystricmp(pred_type, "comb"))
  {
    /* combining predictor, bpred_create() checks args */
    if (twolev_nelt != 4)
      fatal("bad   2-level pred config (<l1size> <l2size> <hist_size> <xor>)");
    if (bimod_nelt != 1)
      fatal("bad bimod predictor config (<table_size)");
    if (comb_nelt != 1)
      fatal("bad combining predictor config (<meta_table_size>)");
    if (btb_nelt != 2)
      fatal("bad btb config (<num_sets> <associativity>)");

    pred = bpred_create(BPredComb,
			/* bimod table size */bimod_config[0],
			/* 2lev l1 size */twolev_config[0],
			/* 2lev l2 size */twolev_config[1],
			/* meta table size */comb_config[0],
			/* history reg size */twolev_config[2],
			/* history xor address */twolev_config[3],
			/* btb stes */btb_config[0],
			/* btb assoc */btb_config[1],
			/* ret-addr stack size */ras_size,
			0,
			0,
			0,
			0);
  }/* end else if */
  else
    fatal("cannot parse predictor type `%s'", pred_type); 
  if (fetch_ifq_size < 1 || (fetch_ifq_size & (fetch_ifq_size - 1)) != 0)
    fatal("inst fetch queue size must be positive > 0 and a power of two");
  if (fetch_width < 1 || (fetch_width & (fetch_width - 1)) != 0)
    fatal("inst fetch width must be positive > 0 and a power of two");
  if (fetch_width > fetch_ifq_size)
    fatal("fetch width cannot be greater than fetch queue size");
  if (slot_width < 1 || (slot_width & (slot_width - 1)) != 0)
    fatal("slotting width must be positive > 0 and a power of two");

  if (issue_int_width < 1 || (issue_int_width & (issue_int_width - 1)) != 0)
    fatal("integer issue width must be positive > 0 and a power of two");
  
  if (issue_fp_width < 1 || (issue_fp_width & (issue_fp_width - 1)) != 0)
    fatal("fp issue width must be positive > 0 and a power of two");

  if (map_width < 1 || (map_width & (map_width - 1)) != 0)
    fatal("map width must be positive > 0 and a power of two");
  
  /*if (commit_width < 1 || (commit_width & (commit_width - 1)) != 0)
    fatal("commit width must be positive > 0 and a power of two");*/
  
  if (commit_width < 1)
    fatal("commit width must be positive > 0");
  
  
  if (fetch_width < 1 || (fetch_width & (fetch_width - 1)) != 0)
    fatal("Fetch width must be positive > 0 and a power of two");
  /*if (fetch_st_table_size < 1 || (fetch_st_table_size & (fetch_st_table_size - 1)) != 0)
    fatal ("St wait table size must be positive > 0 and a power of two");*/
  if (res_ialu < 1)
    fatal("number of integer ALU's must be greater than zero");
  if (res_ialu > MAX_INSTS_PER_CLASS)
    fatal("number of integer ALU's must be <= MAX_INSTS_PER_CLASS");
  res_fu_config[FU_IALU_INDEX].quantity = res_ialu;
  
  if (res_imult < 1)
    fatal("number of integer multiplier/dividers must be greater than zero");
  if (res_imult > MAX_INSTS_PER_CLASS) 
    fatal("number of integer mult/div's must be <= MAX_INSTS_PER_CLASS");
    res_fu_config[FU_IMULT_INDEX].quantity = res_imult; 
  
  if (res_fpalu < 1)
    fatal("number of floating point ALU's must be greater than zero");
  if (res_fpalu > MAX_INSTS_PER_CLASS)
    fatal("number of floating point ALU's must be <= MAX_INSTS_PER_CLASS");
  res_fu_config[FU_FPALU_INDEX].quantity = res_fpalu;
    
  if (res_fpmult < 1)
    fatal("number of floating point multiplier/dividers must be > zero");
  if (res_fpmult > MAX_INSTS_PER_CLASS) 
    fatal("number of FP mult/div's must be <= MAX_INSTS_PER_CLASS");
  res_fu_config[FU_FPMULT_INDEX].quantity = res_fpmult;

  if (res_int_clusters < 1)
    fatal("number of integer clusters must be > zero");
  
  if (res_fp_clusters < 1)
    fatal("number of fp clusters must be > zero");

  if (res_int_clusters + res_fp_clusters > MAX_CLUSTERS)
    fatal("Total integer and fp clusters in the machine must bt <= MAX_CLUSTERS");
  /* load queue */
  if (issue_lq_nelem < 2 || (issue_lq_nelem & (issue_lq_nelem-1)) != 0)
    fatal("lq size must be a positive number > 1 and a power of two");

  if (commit_sq_nelem < 2 || (commit_sq_nelem & (commit_sq_nelem-1)) != 0)
    fatal("sq size must be a positive number > 1 and a power of two");
  
  if (line_pred_width < fetch_width)
    fatal("It doesn't really make sense to have line predictor width < fetch width");
  
  an_opt = opt_find_option(odb, "-cache:define");
  num_caches = *(an_opt->nelt);
  create_all_caches(num_caches);

  an_opt = opt_find_option(odb, "-tlb:define");
  num_tlbs = *(an_opt->nelt);
  create_tlbs(num_tlbs);
  //printf("finished creating caches.\n");
  /* Link L1 i and d tlbs */
  if (dtlb_name && (mystricmp(dtlb_name, "none")))
    {
      for (i=0; i<num_tlbs; i++)
	if (!mystricmp(tlbs[i]->name, dtlb_name))
	  {
	    dtlb = tlbs[i];
	    break;
	  }
      if (!dtlb)
	fatal("L1 dtlb defined but not found in tlb list");
    }
  //printf("finished creating caches.1\n");
  if (itlb_name && (mystricmp(itlb_name, "none")))
    {
      for (i=0; i<num_tlbs; i++)
	if (!mystricmp(tlbs[i]->name, itlb_name))
	  {
	    itlb = tlbs[i];
	    break;
	  }
      if (!itlb)
	fatal("L1 itlb defined but not found in tlb list");
    }
 //printf("finished creating caches.2\n");
  /* Link L1 i and d caches */
  if (dcache_name && (mystricmp(dcache_name, "none")))
    {
      for (i=0; i<num_caches; i++)
	if (!mystricmp(caches[i]->name, dcache_name))
	  {
	    dcache = caches[i];
	    break;
	  }
      if (!dcache)
	fatal("L1 dcache defined but not found in cache list");

      /* Link the dcache to the dtlb, or to the itlb if no dtlb exists */
      if (dtlb)
	dcache->tlb = dtlb;
      else if (itlb)
	dcache->tlb = itlb;
    }
 //printf("finished creating caches.3\n");
  if (icache_name && (mystricmp(icache_name, "none")))
    {
      for (i=0; i<num_caches; i++)
	if (!mystricmp(caches[i]->name, icache_name))
	  {
	    icache = caches[i];
	    break;
	  }
      if (!icache)
	fatal("L1 icache defined but not found in cache list");

      /* Link the icache to the itlb, or to the dtlb if no itlb exists */
      if (itlb)
	icache->tlb = itlb;
      else if (dtlb)
	icache->tlb = dtlb;
    }
 //printf("finished creating caches.4\n");
  an_opt = opt_find_option(odb, "-bus:define");
  num_buses = *(an_opt->nelt);
  create_all_buses(num_buses);
 //printf("finished creating buses.\n");
  an_opt = opt_find_option(odb, "-mem:define");
  num_mem_banks = *(an_opt->nelt);
  create_all_mem_banks(num_mem_banks);
 //printf("finished creating memory.\n");
  if ((regular_mshrs > MAX_REGULAR_MSHRS) || (regular_mshrs <= 0))
    fatal("number of regular mshrs must be 0 < x <= MAX_REGULAR_MSHRS");
  if ((prefetch_mshrs > MAX_PREFETCH_MSHRS) 
      || (prefetch_mshrs <= 0))
    fatal("number of prefetch mshrs must be 0 < x <= MAX_PREFETCH_MSHRS");
  if ((mshr_targets > MAX_TARGETS) || (mshr_targets <= 0))
    fatal("number of mshr targets must be 0 < x <= MAX_TARGETS");
 //printf("finished.\n");
  /* Link tlbs, caches, buses, and memory banks together */
  link_memory_hierarchy();
  /* Parameters for caches, buses, and banks are checked in their respective
     create functions (cache_timing_create, bus_create, bank_create) */
  /* Check line predictor */
 // if (line_predictor && !icache)
  //  fatal("Line predictor can be defined only with an I-cache");

  //printf("finished.1\n");
}



/* register simulator-specific statistics */
void
sim_reg_stats(struct stat_sdb_t *sdb)
{
  int i;
  //char buf[512], buf1[512];
  /* register baseline stats */
  stat_reg_counter(sdb, "sim_num_insn",
		   "total number of instructions committed",
		   &sim_num_insn, sim_num_insn, NULL);
  stat_reg_counter(sdb, "sim_num_refs",
		   "total number of loads and stores committed",
		   &sim_num_refs, 0, NULL);
  stat_reg_counter(sdb, "sim_num_loads",
		   "total number of loads committed",
		   &sim_num_loads, 0, NULL);
  stat_reg_formula(sdb, "sim_num_stores",
		   "total number of stores committed",
		   "sim_num_refs - sim_num_loads", NULL);
  stat_reg_counter(sdb, "sim_num_branches",
		   "total number of branches committed",
		   &sim_num_branches, /* initial value */0, /* format */NULL);
  stat_reg_int(sdb, "sim_elapsed_time",
	       "total simulation time in seconds",
	       &sim_elapsed_time, 0, NULL);
  stat_reg_formula(sdb, "sim_inst_rate",
		   "simulation speed (in insts/sec)", 
		   "sim_num_insn / sim_elapsed_time", NULL);
  stat_reg_counter(sdb, "sim_total_insn",
		   "total number of instructions executed",
		   &sim_total_insn, 0, NULL);
  stat_reg_counter(sdb, "sim_total_refs",
		   "total number of loads and stores executed",
		   &sim_total_refs, 0, NULL);
  stat_reg_counter(sdb, "sim_total_loads",
		   "total number of loads executed",
		   &sim_total_loads, 0, NULL);
  stat_reg_formula(sdb, "sim_total_stores",
		   "total number of stores executed",
		   "sim_total_refs - sim_total_loads", NULL);
  stat_reg_counter(sdb, "sim_total_branches",
		   "total number of branches executed",
		   &sim_total_branches, /* initial value */0, /* format */NULL);
   /* register performance stats */
  stat_reg_counter(sdb, "sim_cycle",
		   "total simulation time in cycles",
		   &sim_cycle, /* initial value */0, /* format */NULL);
  stat_reg_formula(sdb, "sim_IPC",
		   "instructions per cycle",
		   "sim_num_insn / sim_cycle",NULL);
  stat_reg_formula(sdb, "sim_CPI",
		   "cycles per instruction",
		   "sim_cycle / sim_num_insn", /* format */NULL);
  stat_reg_formula(sdb, "sim_exec_BW",
		   "total instructions (mis-spec + committed) per cycle",
		   "sim_total_insn / sim_cycle", /* format */NULL);
  stat_reg_formula(sdb, "sim_IPB",
		   "instruction per branch",
		   "sim_num_insn / sim_num_branches", /* format */NULL);

   
  /* register predictor stats */
  if (pred)
    bpred_reg_stats(pred, sdb);
  
  stat_reg_counter(sdb, "wb_load_replaytrap",
		   "total number of load replay traps",
		   &wb_load_replaytrap, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "cache_quadword_trap",
		   "traps due to missing loads to same address",
		   &cache_quadword_trap, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "cache_diffaddr_trap",
		   "traps due to diff addr. mappping to same line",
		   &cache_diffaddr_trap, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "wb_store_replaytrap",
		   "total number of store replay traps",
		   &wb_store_replaytrap, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "wb_diffsize_replaytrap",
		   "total number of different size  replay traps",
		   &wb_diffsize_replaytrap, /* initial value */0, /* format */NULL);
  /* BUGFIX 04/24/2004 - Start */
  /* Aamer Jaleel              */
  /* <ajaleel@umd.edu>         */
  stat_reg_counter(sdb, "wb_lsq_data_fwd",
		   "total number of data forwards from stq",
		   &wb_lsq_data_fwd, /* initial value */0, /* format */NULL);
  /* BUGFIX 04/24/2004 - End   */
  stat_reg_counter(sdb, "commit_ctrl_flushes",
		   "total number of control pipeline flushes",
		   &commit_ctrl_flushes, /* initial value */0, /* format */NULL);  
  stat_reg_counter(sdb, "commit_trap_flushes",
		   "total number of trap pipeline flushes",
		   &commit_trap_flushes, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "map_num_early_retire",
		   "Number of instructions which retired early",
		   &map_num_early_retire, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "victim buffer hits",
		   "Number of Victim buffer hits",
		   &victim_buf_hits, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "victim buffer misses",
		   "Number of victim buffer misses",
		   &victim_buf_misses, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "syscall_cycles",
		   "Number of cycles lost due to syscalls",
		   &sys_cycles_lost, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "trap_cycles",
		   "Number of cycles lost due to traps",
		   &wb_trap_cycles_lost, /* initial value */0, 
                   /* format */NULL);

  /* Number of register file reads and writes */
  stat_reg_counter(sdb, "integer_register_reads",
		   "Number of Integer register reads",
		   &stat_int_reg_reads, /* initial value */0, 
                   /* format */NULL);
  stat_reg_counter(sdb, "integer_register_writes",
		   "Number of Integer register writes",
		   &stat_int_reg_writes, /* initial value */0, 
                   /* format */NULL);
  stat_reg_counter(sdb, "fp_register_reads",
		   "Number of FP register reads",
		   &stat_fp_reg_reads, /* initial value */0, /* format */NULL);
  stat_reg_counter(sdb, "fp_register_writes",
		   "Number of FP register writes",
		   &stat_fp_reg_writes, /* initial value */0,/* format */NULL);
  /* LSQ reads and writes */
  stat_reg_counter(sdb, "lq_reads",
		   "Number of load queue reads",
		   &stat_lq_reads, /* initial value */0,/* format */NULL);
  stat_reg_counter(sdb, "lq_writes",
		   "Number of load queue writes",
		   &stat_lq_writes, /* initial value */0,/* format */NULL);
  stat_reg_counter(sdb, "sq_reads",
		   "Number of store queue reads",
		   &stat_sq_reads, /* initial value */0,/* format */NULL);
  stat_reg_counter(sdb, "sq_writes",
		   "Number of store queue writes",
		   &stat_sq_writes, /* initial value */0,/* format */NULL);

  /* register cache stats */
  for (i=0; i<num_caches; i++)
    cache_timing_reg_stats(caches[i], sdb);
  
  for (i=0; i<num_tlbs; i++)
    cache_timing_reg_stats(tlbs[i], sdb);

  for (i=0; i<num_buses; i++)
    bus_reg_stats(buses[i], sdb);

  for (i=0; i<num_mem_banks; i++)
    mem_bank_reg_stats(mem_banks[i], sdb);
  
  ld_reg_stats(sdb);
  mem_reg_stats(sdb);
}

/* initialize the simulator */
void
sim_init(void)
{
#if defined FUNC_DEBUG
  extern struct myregs_t myregs;
  void my_sim_load_prog(char *, int, char **, char **);
  extern md_addr_t my_ld_prog_entry;
  extern md_addr_t my_ld_environ_base;
  void my_sim_init(void);
  /* allocate and initialize register file */
  my_regs_init(&myregs);
  my_sim_init();
  regs_init(&regs);



  dram_init();
#else
  regs_init(&regs);
  dram_init();
#endif
}

/* load program into simulated state */
void
sim_load_prog(char *fname,		/* program to load */
	      int argc, char **argv,	/* program arguments */
	      char **envp)		/* program environment */
{
#if defined FUNC_DEBUG
  extern struct myregs_t myregs;
  void my_sim_load_prog(char *, int, char **, char **);
  extern md_addr_t my_ld_prog_entry;
  extern md_addr_t my_ld_environ_base;
#endif
  /* load program text and data, set up environment, memory, and regs */
  ld_load_prog(fname, argc, argv, envp, &regs, TRUE);
  mem_init1();
#if defined FUNC_DEBUG
  my_sim_load_prog(fname, argc, argv, envp);
  myregs.regs_R[MD_REG_SP] = my_ld_environ_base;
  myregs.regs_PC = my_ld_prog_entry;
#endif
}

/* print simulator-specific configuration information */
void
sim_aux_config(FILE *stream)
{
  /* nothing currently */
}

/* dump simulator-specific auxiliary simulator statistics */
void
sim_aux_stats(FILE *stream)
{
  /* nada */
}

/* un-initialize simulator-specific state */
void
sim_uninit(void)
{
  /* nada */
}

/*
 * configure the execution engine
 */

/* next program counter */
#define SET_NPC(EXPR)		(regs.regs_NPC = (EXPR))


/* general purpose registers */

#if defined(TARGET_PISA)

/* floating point registers, L->word, F->single-prec, D->double-prec */
#define FPR_L(N)		(regs.regs_F.l[fr_mapping[(N)].phy_reg])
#define SET_FPR_L(N,EXPR)	(regs.regs_F.l[fr_mapping[(N)].phy_reg] = (EXPR))
#define FPR_F(N)		(regs.regs_F.f[fr_mapping[(N)].phy_reg])
#define SET_FPR_F(N,EXPR)	(regs.regs_F.f[fr_mapping[(N)].phy_reg] = (EXPR))
#define FPR_D(N)		(regs.regs_F.d[fr_mapping[(N)].phy_reg >> 1])
#define SET_FPR_D(N,EXPR)	(regs.regs_F.d[fr_mapping[(N)].phy_reg >> 1] = (EXPR))

/* miscellaneous register accessors */
#define SET_HI(EXPR)		(regs.regs_C.hi = (EXPR))
#define HI			(regs.regs_C.hi)
#define SET_LO(EXPR)		(regs.regs_C.lo = (EXPR))
#define LO			(regs.regs_C.lo)
#define FCC			(regs.regs_C.fcc)
#define SET_FCC(EXPR)		(regs.regs_C.fcc = (EXPR))

#elif defined(TARGET_ALPHA)


/* miscellaneous register accessors */
#define FPCR			(regs.regs_C.fpcr)
#define UNIQ			(regs.regs_C.uniq)

#else
#error No ISA target defined...
#endif
#if 0
#define READ_HALF(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_HALF(mem, (SRC)))
#define READ_WORD(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_WORD(mem, (SRC)))
#ifdef HOST_HAS_QUAD
#define READ_QUAD(SRC, FAULT)						\
  ((FAULT) = md_fault_none, MEM_READ_QUAD(mem, (SRC)))
#endif /* HOST_HAS_QUAD */

#define WRITE_BYTE(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_BYTE(mem, (DST), (SRC)))
#define WRITE_HALF(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_HALF(mem, (DST), (SRC)))
#define WRITE_WORD(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_WORD(mem, (DST), (SRC)))
#ifdef HOST_HAS_QUAD
#define WRITE_QUAD(SRC, DST, FAULT)					\
  ((FAULT) = md_fault_none, MEM_WRITE_QUAD(mem, (DST), (SRC)))
#endif /* HOST_HAS_QUAD */

/* system call handler macro */
#endif
#ifndef NO_INSN_COUNT
#define INC_INSN_CTR()	sim_num_insn++
#else /* !NO_INSN_COUNT */
#define INC_INSN_CTR()	/* nada */
#endif /* NO_INSN_COUNT */

#ifdef TARGET_ALPHA
#define ZERO_FP_REG()	regs.regs_F.d[MD_REG_ZERO] = 0.0
#else
#define ZERO_FP_REG()	/* nada... */
#endif

/* start simulation, program loaded, processor precise state initialized */
void
sim_main(void) {
  //counter_t last_count = 0;
  //int prog_count = 1048576;
  void exit_now(int);
   
  /* must have natural byte/word ordering 
  if (sim_swap_bytes || sim_swap_words)
    fatal("sim: functional simulation cannot swap bytes or words");*/


/* For register AVF, by Xin Fu */
  reg_init();


  commit_stage_init();

  writeback_stage_init();

  issue_stage_init();

  map_stage_init();

  slot_stage_init();

  fetch_stage_init();

  regs.regs_NPC = regs.regs_PC + sizeof(md_inst_t);
  /* fast forward simulator loop, performs functional simulation for
     FASTFWD_COUNT insts, then turns on performance (timing) simulation */
  if (opt_fastfwd_count > 0) {
#undef SET_GPR
#undef SET_FPR_Q
#undef SET_FPR
#undef SET_FPR_L
#undef SET_FPR_F
#undef SET_FPR_D
#undef GPR
#undef FPR_Q
/* floating point registers, L->word, F->single-prec, D->double-prec */
#undef FPR_L
#undef SET_FPR_L
#undef FPR_F
#undef SET_FPR_F
#undef FPR_D
#undef SET_FPR_D
#undef FPR
#undef SET_FPR

#define SET_GPR(N,EXPR) (regs.regs_R[N] = (EXPR))
#define SET_FPR_Q(N,EXPR) (regs.regs_F.q[N]=(EXPR))
#define GPR(N) (regs.regs_R[(N)])
#define FPR_Q(N) (regs.regs_F.q[N])
/* floating point registers, L->word, F->single-prec, D->double-prec */
#define FPR_L(N)		(regs.regs_F.l[(N)])
#define SET_FPR_L(N,EXPR)	(regs.regs_F.l[(N)] = (EXPR))
#define FPR_F(N)		(regs.regs_F.f[(N)])
#define SET_FPR_F(N,EXPR)	(regs.regs_F.f[(N)] = (EXPR))
#define FPR_D(N)		(regs.regs_F.d[(N) >> 1])
#define SET_FPR_D(N,EXPR)	(regs.regs_F.d[(N) >> 1] = (EXPR))
#define FPR(N)			(regs.regs_F.d[N])
#define SET_FPR(N,EXPR)		(regs.regs_F.d[N] = (EXPR))
    unsigned long long int icount;
    md_inst_t inst;			/* actual instruction bits */
    enum md_opcode op;		/* decoded opcode enum */
    md_addr_t addr;			/* effective address, if load/store */
    int is_write;			/* store? */
    byte_t temp_byte = 0;		/* temp variable for spec mem access */
    half_t temp_half = 0;		/* " ditto " */
    word_t temp_word = 0;		/* " ditto " */
#ifdef HOST_HAS_QWORD
    quad_t temp_qword = 0;		/* " ditto " */
#endif /* HOST_HAS_QWORD */
    enum md_fault_type fault;
    static quad_t temp_quad;
    static int spec_mode=0;
    fprintf(stderr, "sim: ** fast forwarding %qi insts **\n", opt_fastfwd_count);
    
    for (icount=0; icount < opt_fastfwd_count; icount++)
      {
	/* maintain $r0 semantics */
	regs.regs_R[MD_REG_ZERO] = 0;
#ifdef TARGET_ALPHA
	regs.regs_F.d[MD_REG_ZERO] = 0.0;
#endif /* TARGET_ALPHA */

	/* get the next instruction to execute */
	MD_FETCH_INST(inst, regs.regs_PC);
	
	/* set default reference address */
	addr = 0; is_write = FALSE;
	
	/* set default fault - none */
	fault = md_fault_none;
	
	/* decode the instruction */
	MD_SET_OPCODE(op, inst);
	
	/* execute the instruction */
	switch (op)
	  {
#define DEFINST(OP,MSK,NAME,OPFORM,RES,FLAGS,O1,O2,I1,I2,I3)		\
	    case OP:							\
	      SYMCAT(OP,_IMPL);						\
	      break;
#define DEFLINK(OP,MSK,NAME,MASK,SHIFT)					\
	    case OP:							\
	      panic("attempted to execute a linking opcode");
#define CONNECT(OP)
#undef DECLARE_FAULT
#define DECLARE_FAULT(FAULT)						\
	      { fault = (FAULT); break; }
#include "ssmachine.def"
	  default:
	    panic("attempted to execute a bogus opcode");
	  }
	
	if (fault != md_fault_none)
	  fatal("fault (%d) detected @ 0x%08p", fault, regs.regs_PC);
	
	/* update memory access stats */
	if (MD_OP_FLAGS(op) & F_MEM)
	  {
	    if (MD_OP_FLAGS(op) & F_STORE)
	      is_write = TRUE;
	  }
	
	/* go to the next instruction */
	regs.regs_PC = regs.regs_NPC;
	regs.regs_NPC += sizeof(md_inst_t);
      }
  }

  /*Initialize the pipeline stages*/
  //execute_stage_init();
  fprintf(stderr, "sim: ** starting  performance simulation **\n");

  
  
  while (TRUE)
  {
    if (((map_rb_head+map_rb_num) % map_rb_nelem) != map_rb_tail)
      panic ("map_rb_head/map_rb_tail wedged");
    if (((issue_lq_head+issue_lq_num) % issue_lq_nelem) != issue_lq_tail)
      panic ("issue_lq_head/issue_lq_tail wedged");
    if (((commit_sq_head+commit_sq_num) % commit_sq_nelem) != commit_sq_tail)
      panic ("commit_sq_head/commit_sq_tail wedged");

    /* Service memory hierarchy events */
    
    eventq_service_events(sim_cycle);
    
    /*run through the pipeline stages*/
    
    /* call the commit stage */
    commit_stage();
    
    data_dump();
    
    /* call execute stage*/
    writeback_stage();
        
    /* call issue stage*/
    issue_stage();
    
    /*call map stage*/
    map_stage();
    
    /* call slot stage*/
    slot_stage();
        
    /* call fetch stage if not blocked */
    if (!fetch_istall_buf.stall)
      fetch_stage();
    
	current_cycle=sim_cycle;
    sim_cycle++;
	/*for address-based AVF */

	if(current_cycle!=sim_cycle)
	  {
		IQ_idle_counter=IQ_idle_counter+ map_int_issue_size-IQ->queue_num;
		rob_idle_counter=rob_idle_counter + map_rb_nelem-map_rb_num;
	  }
	else
	  {	printf("calculate twice.\n");
	    exit(0);
  }
    if(map_int_issue_size -IQ->queue_num>map_int_issue_size)
	  {
		printf("ERROR in IQ idle counter, bigger than %d.\n", map_int_issue_size);
		printf("IQ->queue_nelem is %d.\n",map_int_issue_size);
		printf("IQ->queue_num is %d.\n", IQ->queue_num);
		exit(0);
	  }
    
	if(sim_num_insn>=AVF_INSN)
	  {
		if(dl1_flag==0)
		{
		  end_cycle=sim_cycle;
          avf_data_end(dcache, sim_cycle);
		 // printf("DL1 data compuation.\n");
		  avf_tag_end(dcache, sim_cycle);
		  //printf("DL1 tag compuation.\n");
		  avf_data_end(dcache->tlb, sim_cycle);
		 // printf("DTLB data compuation.\n");
		  avf_tag_end(dcache->tlb, sim_cycle);
		//  printf("DTLB tag compuation.\n");
		  avf_vbuf_data_end(dcache, sim_cycle);
		 // printf("vbuf data compuation.\n");
		  avf_vbuf_tag_end(dcache, sim_cycle);
		 // printf("vbuf tag compuation.\n");
	      dl1_flag=1;
		}
      }
	if(sim_num_insn>=AVF_INSN+COOL_DOWN)
	  {
		if(dll_cool==0)
		{
		 finish_cycle=sim_cycle;
		 printf("\n");
                 avf_data_sum(dcache);
		 avf_tag_sum(dcache);
		 avf_tag_sum(dcache->tlb);
		 avf_data_sum(dcache->tlb);
		 avf_vbuf_data_sum(dcache);
		 avf_vbuf_tag_sum(dcache);
		// printf("end cycle is %d.\n", end_cycle);
		// printf("finished cache AVF compuation.\n");
		
		 dll_cool=1;
		}
	  }
   
	
	
	
		
    /* finish early? */
    if (opt_max_insts && sim_num_insn >= opt_max_insts)
      return;
  }
  exit_now(0);
}

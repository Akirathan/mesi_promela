/**
 * Implementation based on https://en.wikipedia.org/wiki/MESI_protocol.
 * Cache to cache transfer is not implemented.
 *
 * STATES:
 * - (M)odified: Contents different from main-memory, exclusive to this cache.
 * - (E)xclusive: Contents same with main-memory, exclusive to this cache.
 * - (S)hared
 * - (I)invalid
 *
 *
 * SIGNALS:
 * - PrRd:    (issued by processor) Processor READS from it's cache.
 * - PrWr:    (issued by processor) Processor WRITES to it's cache.
 * - BusRd:   Other processor READS cacheline that is NOT resident in it's cache.
 * - BusRdX:  Other processor WRITES to cacheline that is NOT resident in it's cache.
 * - BusUpgr: Other processor WRITES to cacheline that IS resident in it's cache.
 *            This signal is sent only if the cacheline is Shared.
 */

#define CPU_COUNT 2
#define CACHE_SIZE 2
#define MEMORY_SIZE 4
// Number of one CPU's writes and reads.
#define STEP_NUM 2
#define ASSERT_NOT_REACHABLE assert(false)
//#define RUN_WITH_MONITORS
//#define LTL_FORMULAS

// Cache state
mtype = {Modified, Exclusive, Shared, Invalid};
// Signals
mtype = {BusRd, BusRdX, BusUpgr};
// Intentions
mtype = {Read, Write};

/**
 * Every CPU is identified by integer. Let us describe the purpose of channels from
 * the perspective of one CPU identified by cpu_idx.
 *
 * In req_channel[cpu_idx] there are requests made by other CPUs. This CPU is
 * required to answer some of these requests via resp_channel[other_cpu_idx].
 *
 * Note that these requests do not require responses:
 *   TODO...
 */
chan req_channel[CPU_COUNT] = [CPU_COUNT] of {
    mtype, // Type of request
    int,   // memory address
    byte   // sender_idx
};
chan resp_channel[CPU_COUNT] = [CPU_COUNT] of {mtype, int};

// For signalling that a certain CPU ended its execution normally.
chan end_channel = [CPU_COUNT] of {bool};

#define ARE_ALL_CPUS_FINISHED \
    full(end_channel)

typedef cache_t {
    bit content[CACHE_SIZE];
    mtype cache_states[CACHE_SIZE];
    int tag[CACHE_SIZE]; // Tag is equal to memory address
}

typedef intention_t {
    mtype type;
    int memaddr;
}

bit memory[MEMORY_SIZE] = 0;
cache_t caches[CPU_COUNT];
bool cancels[CPU_COUNT] = false;

#define CACHE_ADDR(mem_addr) \
    mem_addr % CACHE_SIZE

#define CACHE_STATE(cpu_idx, memaddr) \
    caches[cpu_idx].cache_states[CACHE_ADDR(memaddr)]

#define CACHE_CONTENT(cpu_idx, memaddr) \
    caches[cpu_idx].content[CACHE_ADDR(memaddr)]

#define CACHE_TAG(cpu_idx, memaddr) \
    caches[cpu_idx].tag[CACHE_ADDR(memaddr)]

// This "getter" and "setter" for cache state is preferable over CACHE_STATE, because it
// also checks whether the tag of the cache entry corresponds.
#define GET_CACHE_STATE(cpu_idx, memaddr)                    \
    (CACHE_TAG(cpu_idx, memaddr) == memaddr ->  \
        CACHE_STATE(cpu_idx, memaddr) :         \
        Invalid)

#define SET_CACHE_STATE(cpu_idx, memaddr, state) \
    caches[cpu_idx].cache_states[CACHE_ADDR(memaddr)] = state


inline print_state(mypid) {
    atomic {
        printf("%d: CACHE = [\n", mypid)
        int j;
        for (j : 0 .. CACHE_SIZE - 1) {
            printf("  %d (%e, tag=%d),\n", CACHE_CONTENT(mypid, j),
                   CACHE_STATE(mypid, j), CACHE_TAG(mypid, j));
        }
        printf("]\n");
    }
}

inline print_memory() {
    atomic {
        printf("MEMORY = [\n");
        int j;
        for (j : 0 .. MEMORY_SIZE - 1) {
            printf("  %d,\n", memory[j]);
        }
        printf("]\n");
    }
}

inline check_for_two_modified_cachelines() {
    int cpu_idx;
    for (cpu_idx : 0 .. CPU_COUNT - 1) {
        int cache_addr;
        for (cache_addr : 0 .. CACHE_SIZE - 1) {
            if
                :: GET_CACHE_STATE(cpu_idx, cache_addr) == Modified -> {
                    // Check if other cpu has modified state
                    int tag = CACHE_TAG(cpu_idx, cache_addr);
                    assert tag != -1;
                    // TODO: Make more efficient.
                    atomic {
                        // We should not find any other cpu that has a Modified cache line
                        // with same tag.
                        int other_cpu_idx;
                        for (other_cpu_idx : (cpu_idx + 1) .. (CPU_COUNT - 1)) {
                            int other_cache_addr;
                            for (other_cache_addr : 0 .. CACHE_SIZE - 1) {
                                if
                                    :: GET_CACHE_STATE(other_cpu_idx, other_cache_addr) == Modified &&
                                    CACHE_TAG(other_cpu_idx, other_cache_addr) == tag -> 
two_modified:                       {
                                        printf("Monitor: At two_modified, printing state:\n");
                                        print_state(cpu_idx);
                                        print_state(other_cpu_idx);
                                        print_memory();
                                    }
                                    :: else -> skip;
                                fi
                            }
                        }
                    }
                }
                :: else -> skip;
            fi
        }
    }
}

/**
 * If there is a Modified cache entry, it should be written to memory in the future.
 */
inline write_not_lost(cpu_idx) {
    int cache_addr;
    for (cache_addr : 0 .. CACHE_SIZE - 1) {
        if
            :: CACHE_STATE(cpu_idx, cache_addr) == Modified -> {
                // In the future, the value should be written to memory.
                bit value = CACHE_CONTENT(cpu_idx, cache_addr);
                int mem_addr = CACHE_TAG(cpu_idx, cache_addr);
                printf("Monitor(%d): waiting for value %d to be written to mem_addr=%d\n",
                    cpu_idx, value, mem_addr);
                // TODO: This statement should be executable before the end.
                memory[mem_addr] == value;
            }
            :: else -> skip;
        fi
    }
}

proctype monitor(int cpu_idx) {
#ifdef RUN_WITH_MONITORS
    do
        :: write_not_lost(cpu_idx);
        :: ARE_ALL_CPUS_FINISHED -> break;
    od
#endif
    skip;
}

#ifdef LTL_FORMULAS
/**
 * If there is a Modified cache entry, it should be written to memory in the future.
 *
 * _8_1_mem_addr is an address of memory that we want to modify (defined in proctype CPU,
 * and passed to write).
 */
ltl ltl_write_not_lost {
    [](cpu[0]@modified -> <> (cpu[0]@flush && cpu[0]:_8_1_mem_addr == cpu[0]:_8_1_1_recved_mem_addr))
}

/**
 * If there is an Exclusive cache entry with a specific tag, there should not exist
 * Exclusive cache entry in any other CPU cache with such a tag.
 */
ltl ltl_one_exclusive {
    // If CPU 0 marks 0-th cache entry (with tag 0) as Exclusive,
    // then CPU 1 should not have 0-th cache entry markes as Exclusive.
    [] (cpu[0]@exclusive && cpu[0]:_8_1_mem_addr == 0 -> (
        CACHE_STATE(1, 0) != Exclusive
    ))
}
#endif // LTL_FORMULAS


/**
 * Send a request to all CPUs except self. More precisely, send a request_t to every
 * req_channel[i] for every i such that i != self_cpu_idx.
 */
inline signal_all(mypid, msgtype, mem_addr) {
    atomic {
        printf("%d: Signalling all {%e,%d}\n", mypid, msgtype, mem_addr);
        int _i;
        for(_i : 0 .. CPU_COUNT - 1) {
            if
                // Do not signal self
                :: _i == mypid -> skip;
                :: else -> {
                    req_channel[_i] ! msgtype, mem_addr, mypid;
                }
            fi
        }
    }
}

/**
 * Other CPU responding with Invalid means "acknowledgement" in certain situations.
 */
inline receive_acks(mypid) {
    int __i;
    for (__i : 0 .. CPU_COUNT - 2) {
        resp_channel[mypid] ? Invalid, _;
        printf("%d: Got Invalid (ack)\n", mypid);
    }
}

inline flush_and_invalidate(mypid, memaddr) {
    // TODO: Enclose in atomic?
    printf("%d: memory[%d] = %d\n", mypid, memaddr, CACHE_CONTENT(mypid, memaddr));
flush:    memory[memaddr] = CACHE_CONTENT(mypid, memaddr);
    change_state(mypid, memaddr, Invalid);
}

inline change_state(mypid, mem_addr, new_state) {
    mtype old_state = GET_CACHE_STATE(mypid, mem_addr);
    if
        :: old_state == new_state -> goto end;
        :: else -> skip;
    fi

    printf("%d: State %e --> %e, mem_addr=%d, cache_addr=%d\n",
        mypid, old_state, new_state, mem_addr, CACHE_ADDR(mem_addr));

    if 
        :: CACHE_TAG(mypid, mem_addr) == mem_addr -> {
           assert (old_state == Modified && (new_state == Shared || new_state == Invalid)) ||
           (old_state == Exclusive && (new_state == Modified || new_state == Shared || new_state == Invalid)) ||
           (old_state == Shared && (new_state == Modified || new_state == Invalid)) ||
           (old_state == Invalid && (new_state == Modified || new_state == Exclusive || new_state == Shared))
        }
        :: else -> skip;
    fi

    if
        :: new_state == Modified -> 
modified:   skip;
        :: new_state == Exclusive ->
exclusive:  skip;
        :: else -> skip;
    fi

    SET_CACHE_STATE(mypid, mem_addr, new_state);
end:
    skip;
}

inline cancel_operation(mypid, sender_pid, memaddr) {
    printf("%d: Cancelling operation.\n", mypid);
    // Invalidate cacheline.
    if
        :: GET_CACHE_STATE(mypid, memaddr) == Modified -> {
            flush_and_invalidate(mypid, memaddr);
        }
        :: else -> {
            change_state(mypid, memaddr, Invalid);
        }
    fi
    printf("%d: Sending msg={%e,%d} to %d\n", mypid, Invalid, memaddr, sender_pid);
    resp_channel[sender_pid] ! Invalid, memaddr;
    cancels[mypid] = true;
    goto respond_end;
}

/**
 * Respond to all requests of all other CPUs. More specifically, polls request channel
 * and if there are some requests, respond to them.
 */
inline respond(mypid, intention) {
    int recved_mem_addr;
    byte sender_pid;

    printf("%d: Starting responding to all...\n", mypid);
    if
        /**************  BusRd  ****************/
        :: req_channel[mypid] ? [BusRd, recved_mem_addr, sender_pid] -> {
            req_channel[mypid] ? BusRd, recved_mem_addr, sender_pid;
            // TODO: We have to check whether tag corresponds to recved_mem_addr.
            mtype my_old_cache_state = GET_CACHE_STATE(mypid, recved_mem_addr);
            printf("%d: Got msg={BusRd,%d} from %d, my_old_cache_state=%e\n",
                mypid, recved_mem_addr, mypid, my_old_cache_state);
            if
                // Some other CPU sent BusRd(addr) and we want to read addr.
                :: intention.type == Read && intention.memaddr == recved_mem_addr &&
                    my_old_cache_state != Modified ->
                {
                    // Other CPU want to read the same memory address.
                    change_state(mypid, recved_mem_addr, Shared);
                }
                // Some other CPU sent BusRd(addr), we want to read addr, and we have addr
                // as Modified. We need to flush addr first.
                :: intention.type == Read && intention.memaddr == recved_mem_addr &&
                    my_old_cache_state == Modified ->
                {
                    flush_and_invalidate(mypid, recved_mem_addr);
                    change_state(mypid, recved_mem_addr, Shared);
                }
                :: my_old_cache_state == Modified -> {
                    // [1.2] M|BusRd
                    flush_and_invalidate(mypid, recved_mem_addr);
                }
                :: my_old_cache_state == Exclusive -> {
                    // [1.2] E|BusRd
                    change_state(mypid, recved_mem_addr, Shared);
                }
                :: my_old_cache_state == Shared -> skip;
                :: my_old_cache_state == Invalid -> skip;
            fi

            mtype my_new_cache_state = CACHE_STATE(mypid, recved_mem_addr);
            printf("%d: Sending msg={%e,%d} to %d\n", mypid, my_new_cache_state, recved_mem_addr, sender_pid);
            resp_channel[sender_pid] ! my_new_cache_state, recved_mem_addr;
        }

        /**************  BusUpgr  ****************/
        :: req_channel[mypid] ? [BusUpgr, recved_mem_addr, sender_pid] -> {
            req_channel[mypid] ? BusUpgr, recved_mem_addr, sender_pid;
            printf("%d: Got msg={BusUpgr,%d} from %d\n", mypid, recved_mem_addr, sender_pid);
            mtype my_state = GET_CACHE_STATE(mypid, recved_mem_addr);
            assert my_state == Invalid || my_state == Shared;

            if
                :: intention.type == Write && intention.memaddr == recved_mem_addr -> {
                    // Some other CPU has this cache line as Shared, and wants to write to it.
                    // Note that it does not matter whater we have that cache line as Shared or as Invalid.
                    cancel_operation(mypid, sender_pid, recved_mem_addr);
                }
                :: my_state == Shared -> change_state(mypid, recved_mem_addr, Invalid);
                :: else -> skip;
            fi
            printf("%d: Sending msg={%e,%d} to %d\n", mypid, Invalid, recved_mem_addr, sender_pid);
            resp_channel[sender_pid] ! Invalid, recved_mem_addr;
        }

        /**************  BusRdX  ****************/
        :: req_channel[mypid] ? [BusRdX, recved_mem_addr, sender_pid] -> {
            req_channel[mypid] ? BusRdX, recved_mem_addr, sender_pid;
            printf("%d: Got msg={BusRdX,%d} from %d\n", mypid, recved_mem_addr, sender_pid)
            if
                :: intention.type == Write && intention.memaddr == recved_mem_addr -> {
                    // This CPU and some other CPU want to write to the same memory => clash.
                    cancel_operation(mypid, sender_pid, recved_mem_addr);
                }
                :: intention.type == Read && intention.memaddr == recved_mem_addr -> {
                    // Some other CPU wants to write to a cache line, and we want to read it => clash.
                    cancel_operation(mypid, sender_pid, recved_mem_addr);
                }
                :: else -> skip;
            fi

            mtype state = GET_CACHE_STATE(mypid, recved_mem_addr);
            if
                :: state == Invalid -> skip;
                :: state == Exclusive -> {
                    // [1.2] E|BusRdX
                    change_state(mypid, recved_mem_addr, Invalid);
                }
                :: state == Shared -> {
                    // [1.2] S|BusRdX
                    change_state(mypid, recved_mem_addr, Invalid);
                }
                :: state == Modified -> {
                    // [1.2] M|BusRdX
                    flush_and_invalidate(mypid, recved_mem_addr);
                }
            fi
            printf("%d: Sending msg={%e,%d} to %d\n", mypid, Invalid, recved_mem_addr, sender_pid);
            resp_channel[sender_pid] ! Invalid, recved_mem_addr;
        }
    fi
respond_end:
    printf("%d: Done responding to all.\n", mypid);
}

inline read(mypid, mem_addr) {
    printf("%d: Reading mem_addr %d\n", mypid, mem_addr);
    intention_t intention;
    intention.type = Read;
    intention.memaddr = mem_addr;

        atomic {
            signal_all(mypid, BusRd, mem_addr);
        respond(mypid, intention);
        }

    if
        :: GET_CACHE_STATE(mypid, mem_addr) == Modified -> {
            flush_and_invalidate(mypid, mem_addr);
        }
        :: else -> skip;
    fi

        // Receive states from other CPUs.
        mtype next_state = Exclusive;
        int other_cpu_idx;
        for (other_cpu_idx : 0 .. CPU_COUNT - 2) {
            if
            :: resp_channel[mypid] ? Invalid, mem_addr -> next_state = Exclusive;
                :: resp_channel[mypid] ? Shared, mem_addr -> next_state = Shared;
            // This should not happen.
            :: resp_channel[mypid] ? Exclusive, mem_addr -> ASSERT_NOT_REACHABLE;
            :: resp_channel[mypid] ? Modified, mem_addr -> ASSERT_NOT_REACHABLE;
            fi
        }
        assert next_state == Exclusive || next_state == Shared;

    if
        :: cancels[mypid] -> {
            // Operation was cancelled => do nothing.
            cancels[mypid] = false;
            goto read_end;
    }
        :: else -> skip;
    fi

    mtype curr_state = GET_CACHE_STATE(mypid, mem_addr);
    if
    :: curr_state == Exclusive || curr_state == Shared -> {
        // Reading cache line in mem_addr should be a cache hit.
        assert CACHE_CONTENT(mypid, mem_addr) == memory[mem_addr];
        assert CACHE_TAG(mypid, mem_addr) == mem_addr;
    }
        :: curr_state == Invalid -> {
            change_state(mypid, mem_addr, next_state);
            CACHE_CONTENT(mypid, mem_addr) = memory[mem_addr];
            CACHE_TAG(mypid, mem_addr) = mem_addr;
    }
        :: curr_state == Modified -> ASSERT_NOT_REACHABLE;
    fi

read_end:
    skip;
}

inline write(mypid, mem_address, value) {
    printf("%d: Writing %d to mem_address %d\n", mypid, value, mem_address);
    intention_t intention;
    intention.type = Write;
    intention.memaddr = mem_addr;

    if
        :: CACHE_TAG(mypid, mem_address) != mem_address &&
            GET_CACHE_STATE(mypid, mem_address) == Modified ->
        {
            // We want to rewrite contents of this cache line, however it is Modified, therefore
            // we need to flush it first.
            flush_and_invalidate(mypid, mem_address);
        }
        :: else -> skip;
    fi

        atomic {
            signal_all(mypid, BusRdX, mem_address);
        respond(mypid, intention);
        }
        receive_acks(mypid);
    if
        :: cancels[mypid] -> {
            // Operation was canceled => Do nothing.
            cancels[mypid] = false;
            goto write_end;
        }
        :: else -> skip;
    fi

    mtype curr_state = GET_CACHE_STATE(mypid, mem_address);
    if
        :: curr_state == Invalid -> skip;
        :: curr_state == Modified -> {
            assert CACHE_TAG(mypid, mem_address) == mem_address;
        }
        :: curr_state == Shared || curr_state == Exclusive -> {
            assert CACHE_TAG(mypid, mem_address) == mem_address;
            assert CACHE_CONTENT(mypid, mem_address) = memory[mem_address];
    }
    fi
            change_state(mypid, mem_address, Modified);
            CACHE_CONTENT(mypid, mem_address) = value;
            CACHE_TAG(mypid, mem_address) = mem_address;

write_end:
    skip;
}

/**
* Models one CPU. Should be instantiated as many times as there are CPUs.
* Writes and reads from random places at memory, and thus simulating some program.
*/ 
proctype cpu(int mypid) {
    int i;
    for (i : 0 .. STEP_NUM - 1) {
        byte mem_addr;
        select(mem_addr : 0 .. MEMORY_SIZE - 1);
        if
        :: skip -> read(mypid, mem_addr);
        :: skip -> {
            bit value;
            select(value : 0 .. 1);
            write(mypid, mem_addr, value);
        }
        fi
        print_state(mypid);
        print_memory();
    }

    // Signal end of execution
    end_channel ! true;
}

inline init_caches() {
    int cpu_idx;
    for (cpu_idx : 0 .. CPU_COUNT - 1) {
        int cache_addr;
        for (cache_addr : 0 .. CACHE_SIZE - 1) {
            CACHE_CONTENT(cpu_idx, cache_addr) = 0;
            SET_CACHE_STATE(cpu_idx, cache_addr, Invalid);
            CACHE_TAG(cpu_idx, cache_addr) = -1;
        }
    }
}

inline init_memory() {
    int mem_addr;
    for (mem_addr : 0 .. MEMORY_SIZE - 1) {
        memory[mem_addr] = (mem_addr % 2 == 0 -> 0 : 1);
    }
}

init {
    init_caches();
    init_memory();
    print_memory();

    int cpu_idx;
    atomic {
        for (cpu_idx : 0 .. CPU_COUNT - 1) {
#ifdef RUN_WITH_MONITORS
            run monitor(cpu_idx);
#endif
            run cpu(cpu_idx);
        }
    }

    // Wait for all CPUs to end their execution.
    ARE_ALL_CPUS_FINISHED;
    printf("Init: all CPUs finished execution.\n");
    print_memory();
}



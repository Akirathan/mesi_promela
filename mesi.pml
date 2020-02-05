/**
 * Implementation based on https://en.wikipedia.org/wiki/MESI_protocol.
 * Cache to cache transfer is not implemented.
 *
 * STATES:
 * - (M)odified: Contents different from main-memory, exclusive to this cache.
 * - (E)xclusive: Contents same with main-memory, exclusive to this cachee.
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
#define STEP_NUM 1
#define ASSERT_NOT_REACHABLE assert(false)

mtype:cache_state = {Modified, Exclusive, Shared, Invalid};
mtype:signal = {BusRd, BusRdX, BusUpgr};

chan req_channel[CPU_COUNT] = [0] of {mtype, int};
chan resp_channel[CPU_COUNT] = [0] of {mtype, int}

typedef cache_state_t {
    mtype:cache_state cache_states[CACHE_SIZE];
}

typedef cache_t {
    bit content[CACHE_SIZE];
}

bit memory[MEMORY_SIZE] = 0;
cache_t caches[CPU_COUNT];
cache_state_t cpu_states[CPU_COUNT];

#define CACHE_STATE(cpu_idx, address) \
    cpu_states[cpu_idx].cache_states[address]

#define CACHE_CONTENT(cpu_idx, adress) \
    caches[cpu_idx].content[address]


inline signal_all(msgtype, address) {
    printf("%d: Signalling all {%e,%d}\n", _pid, msgtype, address);
    int _i;
    for(_i : 0 .. CPU_COUNT) {
        if
        // Do not signal self
        :: _i == _pid -> skip;
        :: else -> req_channel[_i] ! msgtype, address;
        fi
    }
}

inline flush(address) {
    memory[address] = CACHE_CONTENT(_pid, address);
}

inline flush_and_invalidate(address) {
    printf("%d: Flushing and invalidating at %d\n", _pid, address);
    flush(address);
    CACHE_STATE(_pid, address) = Invalid;
}

inline change_state(address, new_state) {
    mtype:cache_state old_state = CACHE_STATE(_pid, address);
    printf("%d: Changing state from %e to %e\n", _pid, old_state, new_state);

    assert old_state == Modified && (new_state == Shared || new_state == Invalid);
    assert old_state == Exclusive && (new_state == Modified || new_state == Shared || new_state == Invalid);
    assert old_state == Shared && (new_state == Modified || new_state == Invalid);
    assert old_state == Invalid && (new_state == Modified || new_state == Exclusive || new_state == Shared);

    CACHE_STATE(_pid, address) = new_state;
}

// Signal BusRdX to all other processors.
inline signal_write_mem(address) {
    assert true;
}

/**
 * Respond to all requests of all other CPUs.
 */
inline respond() {
    int address = 0;

    printf("%d: Starting responding to all...\n", _pid);
    int cpu_idx;
    for (cpu_idx : 0 .. CPU_COUNT - 1) {
        if
        :: cpu_idx == _pid -> skip;
        :: else -> {
            if
            /**************  BusRd  ****************/
            :: req_channel[cpu_idx] ? BusRd, address -> {
                mtype:cache_state my_old_cache_state = CACHE_STATE(_pid, address);
                printf("%d: Got msg={BusRd,%d} from %d, my_old_cache_state=%e\n",
                    _pid, address, cpu_idx, my_old_cache_state);
                if
                :: my_old_cache_state == Modified -> {
                    // [1.2] M|BusRd
                    flush_and_invalidate(address);
                }
                :: my_old_cache_state == Exclusive -> {
                    // [1.2] E|BusRd
                    change_state(address, Shared);
                }
                :: my_old_cache_state == Shared -> skip;
                :: my_old_cache_state == Invalid -> skip;
                fi

                mtype:cache_state my_new_cache_state = CACHE_STATE(_pid, address);
                printf("%d: Sending msg={%e,%d} to %d",
                    _pid, my_new_cache_state, address, cpu_idx);
                resp_channel[cpu_idx] ! my_new_cache_state, address;
            }
            /**************  BusUpgr  ****************/
            :: req_channel[cpu_idx] ? BusUpgr, address -> {
                printf("%d: Got msg={BusUpgr,%d} from %d\n", _pid, address, cpu_idx);
                // TODO: There is no need to respond to this -> finaly our state will
                // be invalid.
                mtype:cache_state my_state = CACHE_STATE(_pid, address);
                assert my_state == Invalid || my_state == Shared;
                change_state(address, Invalid);
            }
            /**************  BusRdX  ****************/
            :: req_channel[cpu_idx] ? BusRdX, address -> {
                printf("%d: Got msg={BusRdX,%d} from %d\n", _pid, address, cpu_idx)
                // TODO: There is no need to respond to this -> finaly our state will
                // be invalid
                mtype:cache_state state = CACHE_STATE(_pid, address);
                if
                :: state == Invalid -> skip;
                :: state == Exclusive -> {
                    // [1.2] E|BusRdX
                    flush_and_invalidate(address);
                }
                :: state == Shared -> {
                    // [1.2] S|BusRdX
                    change_state(address, Invalid);
                }
                :: state == Modified -> {
                    // [1.2] M|BusRdX
                    flush_and_invalidate(address);
                }
                fi
            }
            fi
        }
        fi
    }
    printf("%d: Done responding to all.\n", _pid);
}

inline read(address) {
    printf("%d: Reading address %d\n", _pid, address);

    mtype:cache_state curr_state = CACHE_STATE(_pid, address);
    if
    :: curr_state == Invalid -> {
        // [1.1] I|PrRd
        signal_all(BusRd, address);
        // Receive states from other CPUs.
        mtype:cache_state next_state = Exclusive;
        int cpu_idx;
        for (cpu_idx : 0 .. CPU_COUNT - 1) {
            if
            :: cpu_idx == _pid -> skip;
            :: else -> {
                if
                :: resp_channel[cpu_idx] ? Invalid, address -> skip
                :: resp_channel[cpu_idx] ? Exclusive, address -> next_state = Shared;
                :: resp_channel[cpu_idx] ? Shared, address -> next_state = Shared;
                // TODO: This should not happen.
                :: resp_channel[cpu_idx] ? Modified, address -> next_state = Shared;
                fi
            }
            fi
        }
        assert next_state == Exclusive || next_state == Shared;
        change_state(address, next_state);
        CACHE_CONTENT(_pid, address) = memory[address];
    }
    :: curr_state == Exclusive || curr_state == Shared || curr_state == Modified -> {
        // [1.1] E|PrRd
        // Reading block in address should be a cache hit.
        // TODO: Does this assert make sense?
        assert CACHE_CONTENT(_pid, address) == memory[address];
    }
    :: else -> ASSERT_NOT_REACHABLE;
    fi
}

inline write(address, value) {
    printf("%d: Writing %d to address %d\n", _pid, value, address);

    mtype:cache_state curr_state = CACHE_STATE(_pid, address);
    if
    :: curr_state == Invalid -> {
        // [1.1] I|PrWr
        signal_all(BusRdX, address);
        change_state(address, Modified);
        CACHE_CONTENT(_pid, address) = value;
    }
    :: curr_state == Exclusive -> {
        // [1.1] E|PrWr
        change_state(address, Modified);
        CACHE_CONTENT(_pid, address) = value;
    }
    :: curr_state == Shared -> {
        // [1.1] S|PrWr
        signal_all(BusUpgr, address);
        change_state(address, Modified);
    }
    fi
}

inline init_cachestates() {
    int cpu_idx;
    for (cpu_idx : 0 .. CPU_COUNT - 1) {
        int cache_addr;
        for (cache_addr : 0 .. CACHE_SIZE - 1) {
            CACHE_STATE(cpu_idx, cache_addr) = Invalid;
        }
    }
}

inline init_caches() {
    int cpu_idx;
    for (cpu_idx : 0 .. CPU_COUNT - 1) {
        int i;
        for (i : 0 .. CACHE_SIZE - 1) {
            CACHE_CONTENT(cpu_idx, i) = 0;
        }
    }
}

/**
* Models one CPU. Should be instantiated as many times as there are CPUs.
* Writes and reads from random places at memory, and thus simulating some program.
*/ 
proctype cpu() {
    int i;
    for (i : 0 .. STEP_NUM) {
        // Tohle by melo byt v ifu
        respond();
        // ...
        byte address;
        select(address : 0 .. MEMORY_SIZE - 1);
        if
        :: skip -> read(address);
        :: skip -> {
            bit value;
            select(value : 0 .. 1);
            write(address, value);
        }
        fi
    }
}

init {
    init_cachestates();
    init_caches();

    int cpu_idx;
    for (cpu_idx : 0 .. CPU_COUNT - 1) {
        run cpu();
    }
}



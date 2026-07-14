#include <bits/stdc++.h>
using namespace std;
using u64 = uint64_t;
using i64 = int64_t;
using u128 = unsigned __int128;
using i128 = __int128;

const i64 CONST_I64 = (i64)9223372036854775821ULL; 

inline i64 step_r_signed(i64 r) {
    i64 bit = r & 1LL;
    r = (r >> 1) ^ (bit ? CONST_I64 : 0LL);
    return r;
}

// Author: Morteza Farrokhnejad, Ali Farrokhnejad

struct Mat64 {
    array<u64,64> row;
    Mat64() { row.fill(0ULL); }
};

Mat64 mat_mul(const Mat64 &A, const Mat64 &B) {
    Mat64 C;
    for (int i = 0; i < 64; ++i) {
        u64 r = A.row[i];
        u64 out = 0ULL;
        while (r) {
            unsigned k = __builtin_ctzll(r);
            out ^= B.row[k];
            r &= r - 1;
        }
        C.row[i] = out;
    }
    return C;
}

u64 mat_apply(const Mat64 &A, u64 vbits) {
    u64 res = 0ULL;
    for (int i = 0; i < 64; ++i) {
        if (__builtin_parityll(A.row[i] & vbits)) res |= (1ULL << i);
    }
    return res;
}

Mat64 mat_identity() {
    Mat64 I;
    for (int i = 0; i < 64; ++i) I.row[i] = (1ULL << i);
    return I;
}

Mat64 mat_xor(const Mat64 &A, const Mat64 &B) {
    Mat64 C;
    for (int i=0;i<64;++i) C.row[i] = A.row[i] ^ B.row[i];
    return C;
}

Mat64 mat_pow(Mat64 A, unsigned long long e) {
    Mat64 R = mat_identity();
    while (e) {
        if (e & 1ULL) R = mat_mul(R, A);
        A = mat_mul(A, A);
        e >>= 1ULL;
    }
    return R;
}

Mat64 build_transition_matrix() {
    Mat64 A;
    for (int j = 0; j < 64; ++j) {
        i64 r = (i64)(1ULL << j);
        i64 rp = step_r_signed(r);
        u64 rpbits = (u64)rp;
        for (int i = 0; i < 64; ++i) if ((rpbits >> i) & 1ULL) {
            A.row[i] |= (1ULL << j);
        }
    }
    return A;
}

vector<u64> nullspace_basis(vector<u64> Mrows) {
    int L = (int)Mrows.size();
    vector<int> pivot_col;
    pivot_col.reserve(64);
    int r = 0;
    for (int c = 0; c < 64 && r < L; ++c) {
        int pivot = -1;
        for (int i = r; i < L; ++i) if ((Mrows[i] >> c) & 1ULL) { pivot = i; break; }
        if (pivot == -1) continue;
        swap(Mrows[r], Mrows[pivot]);
        for (int i = 0; i < L; ++i) if (i != r && ((Mrows[i] >> c) & 1ULL)) Mrows[i] ^= Mrows[r];
        pivot_col.push_back(c);
        ++r;
    }
    int rank = (int)pivot_col.size();
    vector<int> is_pivot(64, 0);
    for (int x : pivot_col) is_pivot[x] = 1;
    vector<int> free_cols;
    for (int c = 0; c < 64; ++c) if (!is_pivot[c]) free_cols.push_back(c);
    vector<u64> basis;
    basis.reserve(free_cols.size());
    for (int fc : free_cols) {
        u64 vec = (1ULL << fc);
        for (int i = rank - 1; i >= 0; --i) {
            int pc = pivot_col[i];
            int parity = __builtin_parityll(Mrows[i] & vec);
            if (parity) vec |= (1ULL << pc);
        }
        basis.push_back(vec);
    }
    return basis;
}

vector<u64> build_krylov_basis(const Mat64 &A, i64 r0_signed) {
    vector<u64> basis; basis.reserve(64);
    vector<u64> rows; rows.reserve(64);
    u64 v = (u64)r0_signed;
    for (int iter=0; iter<64; ++iter) {
        u64 tmp = v;
        for (u64 row : rows) {
            int p = __builtin_ctzll(row);
            if ((tmp >> p) & 1ULL) tmp ^= row;
        }
        if (tmp) {
            int p = __builtin_ctzll(tmp);
            for (size_t i=0;i<rows.size();++i) if ((rows[i] >> p) & 1ULL) rows[i] ^= tmp;
            rows.push_back(tmp);
            sort(rows.begin(), rows.end(), [](u64 a, u64 b){ return __builtin_ctzll(a) < __builtin_ctzll(b); });
            basis.push_back(v);
        }
        v = mat_apply(A, v);
    }
    return basis;
}

u64 coords_in_basis(const vector<u64> &basis_cols, u64 v) {
    int k = (int)basis_cols.size();
    vector<u128> rows128(64, (u128)0);
    for (int i=0;i<64;++i) {
        u128 row = (u128)0;
        for (int j=0;j<k;++j) if ((basis_cols[j] >> i) & 1ULL) row |= ((u128)1 << j);
        if ((v >> i) & 1ULL) row |= ((u128)1 << k); // safe: 128-bit
        rows128[i] = row;
    }
    int r = 0;
    vector<int> pivot_col(k, -1);
    for (int c=0;c<k && r<64; ++c) {
        int pivot = -1;
        for (int i=r;i<64;++i) if (((rows128[i] >> c) & (u128)1) != (u128)0) { pivot = i; break; }
        if (pivot == -1) continue;
        swap(rows128[r], rows128[pivot]);
        for (int i=0;i<64;++i) if (i!=r && (((rows128[i] >> c) & (u128)1) != (u128)0) ) rows128[i] ^= rows128[r];
        pivot_col[r] = c;
        ++r;
    }
    u64 x = 0ULL;
    for (int i=0;i<r;++i) {
        int c = pivot_col[i];
        if (c >= 0) {
            u128 rhs128 = (rows128[i] >> k) & (u128)1;
            if (rhs128) x |= (1ULL << c);
        }
    }
    return x;
}

vector<u64> build_restricted_matrix(const Mat64 &A, const vector<u64> &basis_cols) {
    int k = (int)basis_cols.size();
    vector<u64> Trows(k, 0ULL);
    for (int j=0;j<k;++j) {
        u64 colp = mat_apply(A, basis_cols[j]);
        u64 coords = coords_in_basis(basis_cols, colp);
        for (int i=0;i<k;++i) if ((coords >> i) & 1ULL) Trows[i] |= (1ULL << j);
    }
    return Trows;
}

u64 T_apply(const vector<u64> &Trows, u64 v) {
    int k = (int)Trows.size();
    u64 res = 0ULL;
    for (int i=0;i<k;++i) {
        if (__builtin_parityll(Trows[i] & v)) res |= (1ULL << i);
    }
    return res;
}

u64 coords_to_state(const vector<u64> &basis_cols, u64 coords) {
    u64 r = 0ULL;
    while (coords) {
        unsigned j = __builtin_ctzll(coords);
        r ^= basis_cols[j];
        coords &= coords - 1;
    }
    return r;
}

struct KeyN {
    u64 coords;
    int n;
    bool operator==(KeyN const& o) const noexcept { return coords==o.coords && n==o.n; }
};
struct KeyNHash {
    size_t operator()(KeyN const& k) const noexcept {
        const uint64_t split = k.coords ^ (k.coords >> 33);
        return (size_t)(split ^ ((uint64_t)k.n * 0x9ddfea08eb382d69ULL));
    }
};

static unordered_map<KeyN, pair<vector<uint8_t>, u64>, KeyNHash> block_cache;
static unordered_map<KeyN, pair<u64,bool>, KeyNHash> step_cache;

pair<vector<uint8_t>, u64> generate_block(u64 coords, const vector<u64> &basis, const vector<u64> &Trows, int n) {
    KeyN key{coords, n};
    auto it = block_cache.find(key);
    if (it != block_cache.end()) return it->second;

    u64 original_coords = coords;
    vector<uint8_t> v;
    bool found = false;
    int skip_count = 0;
    const int SKIP_LIMIT = 1000000; 
    while (!found && skip_count < SKIP_LIMIT) {
        ++skip_count;
        int m = n;
        vector<uint8_t> temp;
        temp.reserve(max(4, n));

        while (m > 0) {
            u64 rbits = coords_to_state(basis, coords);
            uint8_t bit = (uint8_t)(rbits & 1ULL);
            temp.push_back(bit);
            coords = T_apply(Trows, coords);
            m -= 1 + bit;
        }

        if (m == 0) {
            v = std::move(temp);
            found = true;
        }
    }

    if (!found) {
        assert(false && "generate_block failed to find block within skip limit");
    }

    u64 coords_out = coords;
    block_cache.emplace(key, make_pair(v, coords_out));
    return {v, coords_out};
}

u64 advance_one_iteration(u64 coords, const vector<u64> &basis, const vector<u64> &Trows, int n, bool &e) {
    KeyN key{coords, n};
    auto it = step_cache.find(key);
    if (it != step_cache.end()) {
        e = it->second.second;
        return it->second.first;
    }

    auto [v0, coords1] = generate_block(coords, basis, Trows, n);
    auto [v1, coords2] = generate_block(coords1, basis, Trows, n);
    e = (v0 == v1);

    step_cache.emplace(key, make_pair(coords2, e));
    return coords2;
}

bool is_equal_prefix(const vector<uint8_t> &v0, const vector<uint8_t> &v1) {
    size_t min_len = min(v0.size(), v1.size());
    for (size_t i = 0; i < min_len; ++i) if (v0[i] != v1[i]) return false;
    return true;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int Tq;
    if (!(cin >> Tq)) return 0;
    vector<pair<string,int>> queries;
    queries.reserve(Tq);
    for (int i=0;i<Tq;++i) {
        string s_str; int n;
        cin >> s_str >> n;
        queries.emplace_back(s_str, n);
    }

    Mat64 A = build_transition_matrix();
    i64 r0 = -19LL;
    vector<u64> basis = build_krylov_basis(A, r0);
    if (basis.empty()) {
        for (int i=0;i<Tq;++i) cout << 0 << '\n';
        return 0;
    }
    vector<u64> Trows = build_restricted_matrix(A, basis);
    u64 coord0 = coords_in_basis(basis, (u64)r0);

    for (auto &q : queries) {

        string s_str = q.first;
        int n = q.second;

        u64 slow = coord0;
        u64 fast = coord0;
        bool limit_exceeded = false;
        unsigned long long safety = 0ULL;
        const unsigned long long MAX_STEPS = (1ULL << 25);
        bool dummy_e;

        while (true) {
            if (safety > MAX_STEPS) { limit_exceeded = true; break; }
            slow = advance_one_iteration(slow, basis, Trows, n, dummy_e);
            u64 fast1 = advance_one_iteration(fast, basis, Trows, n, dummy_e);
            fast = advance_one_iteration(fast1, basis, Trows, n, dummy_e);
            if (slow == fast) break;
            ++safety;
        }

        if (limit_exceeded) {
            cout << 0 << '\n';
            continue;
        }

        u64 tortoise = coord0;
        u64 hare = slow;
        unsigned long long mu = 0ULL;
        while (tortoise != hare) {
            tortoise = advance_one_iteration(tortoise, basis, Trows, n, dummy_e);
            hare     = advance_one_iteration(hare,     basis, Trows, n, dummy_e);
            mu++;
        }

        hare = advance_one_iteration(hare, basis, Trows, n, dummy_e);
        unsigned long long lam = 1ULL;
        while (tortoise != hare) {
            hare = advance_one_iteration(hare, basis, Trows, n, dummy_e);
            lam++;
        }

        vector<unsigned long long> eq_transient;
        u64 current = coord0;
        for (unsigned long long i = 0ULL; i < mu; ++i) {
            bool e;
            current = advance_one_iteration(current, basis, Trows, n, e);
            if (e) eq_transient.push_back(i);
        }

        vector<int> cycle_offsets;
        current = tortoise; 
        for (unsigned long long i = 0ULL; i < lam; ++i) {
            bool e;
            u64 next = advance_one_iteration(current, basis, Trows, n, e);
            if (e) cycle_offsets.push_back((int)i);
            current = next;
        }

        unsigned long long cycle_start = mu;
        unsigned long long events_per_cycle = cycle_offsets.size();

        if (eq_transient.empty() && cycle_offsets.empty()) {
            cout << 0 << '\n';
            continue;
        }

        i128 s = 0;
        for (char c : s_str) s = s * 10 + (c - '0');

        long double target_ld = (long double) s * (long double) s;
        long double target_scaled_ld = target_ld * 1919.0L;
        i128 a_scaled = -19LL * 1919LL;
        i128 jcount = 0;
        i128 f = 0;

        unsigned long long previous = 0ULL;
        bool finished = false;

        for (unsigned long long t : eq_transient) {
            unsigned long long gap = t - previous;
            a_scaled += (i128)gap + 1;
            if ((long double) a_scaled >= target_scaled_ld) { finished = true; break; }
            jcount += 1;
            unsigned long long na_count = t + 1ULL;
            i128 numer = 19 * s * jcount;
            i128 denom = (i128)na_count;
            i128 fnew = (numer + denom / 2) / denom;
            if (fnew != f) a_scaled = 0;
            f = fnew;
            previous = t + 1ULL;
        }

        if (finished) {
            string f_str;
            if (f == 0) f_str = "0";
            else {
                i128 tmp = f;
                while (tmp > 0) { f_str.push_back(char('0' + (tmp % 10))); tmp /= 10; }
                reverse(f_str.begin(), f_str.end());
            }
            cout << f_str << '\n';
            continue;
        }

        {
            unsigned long long gap = cycle_start - previous;
            a_scaled += (i128)gap;
            if ((long double)a_scaled >= target_scaled_ld) {
                string f_str;
                if (f == 0) f_str = "0";
                else {
                    i128 tmp = f;
                    while (tmp > 0) { f_str.push_back(char('0' + (tmp % 10))); tmp /= 10; }
                    reverse(f_str.begin(), f_str.end());
                }
                cout << f_str << '\n';
                continue;
            }
        }

        vector<unsigned long long> per_cycle_times;
        for (int off : cycle_offsets) per_cycle_times.push_back((unsigned long long)cycle_start + (unsigned long long)off);

        if (events_per_cycle == 0) {
            string f_str;
            if (f == 0) f_str = "0";
            else {
                i128 tmp = f;
                while (tmp > 0) { f_str.push_back(char('0' + (tmp % 10))); tmp /= 10; }
                reverse(f_str.begin(), f_str.end());
            }
            cout << f_str << '\n';
            continue;
        }

        unsigned long long cycles_done = 0ULL;
        const unsigned long long SAFE_LIMIT_CYCLES = 2000000ULL;
        bool terminated = false;

        while (cycles_done < SAFE_LIMIT_CYCLES) {
            i128 a_before = a_scaled;
            i128 f_before = f;

            for (unsigned long long off_time : per_cycle_times) {
                unsigned long long tglob = off_time + cycles_done * (unsigned long long)lam;
                unsigned long long gap = tglob - previous;
                a_scaled += (i128)gap + 1;
                if ((long double)a_scaled >= target_scaled_ld) { terminated = true; break; }
                jcount += 1;
                unsigned long long na_count = tglob + 1ULL;
                i128 numer = 19 * s * jcount;
                i128 denom = (i128)na_count;
                i128 fnew = (numer + denom / 2) / denom;
                if (fnew != f) a_scaled = 0;
                f = fnew;
                previous = tglob + 1ULL;
            }

            if (terminated) break;

            ++cycles_done;

            i128 delta = a_scaled - a_before;

            if (f == f_before && delta > 0) {
                long double remaining = target_scaled_ld - (long double)a_scaled;
                if (remaining <= 0.0L) { terminated = true; break; }
                long double need = remaining / (long double)delta;
                unsigned long long need_cycles = (unsigned long long)ceil(need - 1e-18L);
                if (need_cycles > 0) {
                    if (need_cycles > 1) {
                        unsigned long long skip = need_cycles - 1;
                        jcount += (i128)skip * events_per_cycle;
                        a_scaled += delta * (i128)skip;
                        cycles_done += skip;
                    }
                }
            }

            if (f == f_before && delta == 0) {
                break;
            }
        } 

        string f_str;
        if (f == 0) f_str = "0";
        else {
            i128 tmp = f;
            while (tmp > 0) { f_str.push_back(char('0' + (tmp % 10))); tmp /= 10; }
            reverse(f_str.begin(), f_str.end());
        }
        cout << f_str << '\n';

    } 
    return 0;
}
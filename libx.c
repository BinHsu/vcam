#include <linux/types.h>
#include <asm/bug.h>
#include "libx.h"

#ifndef MIN
#define MIN(a, b) (((a) < (b)) ? (a) : (b))
#endif

enum { READ_MODE, WRITE_MODE };

/* I/O abstraction layer */
typedef struct {
    __u32 *ptr; /* pointer to memory */
    void *end;
    __u32 b; /* bit buffer */
    size_t c;   /* bit counter */
} generic_io_t;

static struct context {
    size_t freq[256];    /* __u8 -> frequency */
    __u8 sorted[256]; /* index -> __u8 */
    __u8 order[256];  /* __u8 -> index */
} table[256];

static size_t opt_k;
static size_t symbol_sum, symbol_count; /* mean = symbol_sum / symbol_count */

/* Recompute Golomb-Rice codes after... */
#define RESET_INTERVAL 256

static void initiate(generic_io_t *io, void *ptr, void *end, int mode)
{
    BUG_ON(io == NULL);

    io->ptr = ptr;
    io->end = end ? (__u8 *) end - 3 : NULL;

    if (mode == READ_MODE) {
        io->c = 32;
    } else {
        io->b = 0;
        io->c = 0;
    }
}

static void flush_buffer(generic_io_t *io)
{
    BUG_ON(io == NULL);
    BUG_ON(io->ptr == NULL);

    *(io->ptr++) = io->b;
    io->b = 0;
    io->c = 0;
}

static void reload_buffer(generic_io_t *io)
{
    BUG_ON(io == NULL);
    BUG_ON(io->ptr == NULL);

    if ((void *) io->ptr < io->end)
        io->b = *(io->ptr++);
    else
        io->b = 0x80000000;

    io->c = 0;
}

static void put_nonzero_bit(generic_io_t *io)
{
    BUG_ON(io == NULL);
    BUG_ON(io->c >= 32);

    io->b |= (__u32) 1 << io->c;
    io->c++;

    if (io->c == 32)
        flush_buffer(io);
}

/* Count trailing zeros */
static inline size_t ctzu32(__u32 n)
{
    if (n == 0)
        return 32;

#ifdef __GNUC__
    return __builtin_ctz((unsigned) n);
#endif

    /* If we can not access hardware ctz, use branch-less algorithm
     * http://graphics.stanford.edu/~seander/bithacks.html
     */
    static const int lut[32] = {0,  1,  28, 2,  29, 14, 24, 3,  30, 22, 20,
                                15, 25, 17, 4,  8,  31, 27, 13, 23, 21, 19,
                                16, 7,  26, 12, 18, 6,  11, 5,  10, 9};
    return lut[((__u32)((n & -n) * 0x077CB531U)) >> 27];
}

static void write_bits(generic_io_t *io, __u32 b, size_t n)
{
    BUG_ON(n <= 32);
    int i = 0;
    for (; i < 2; ++i) {
        BUG_ON(io->c < 32);

        size_t m = MIN(32 - io->c, n);

        io->b |= (b & (((__u32) 1 << m) - 1)) << io->c;
        io->c += m;

        if (io->c == 32)
            flush_buffer(io);

        b >>= m;
        n -= m;

        if (n == 0)
            return;
    }
}

static void write_zero_bits(generic_io_t *io, size_t n)
{
    BUG_ON(n <= 32);
    size_t m;
    for (; n > 0; n -= m) {
        BUG_ON(io->c < 32);

        m = MIN(32 - io->c, n);

        io->c += m;

        if (io->c == 32)
            flush_buffer(io);
    }
}

static __u32 read_bits(generic_io_t *io, size_t n)
{
    if (io->c == 32)
        reload_buffer(io);

    /* Get the available least-significant bits */
    size_t s = MIN(32 - io->c, n);

    __u32 w = io->b & (((__u32) 1 << s) - 1);

    io->b >>= s;
    io->c += s;

    n -= s;

    /* Need more bits? If so, reload and get the most-significant bits */
    if (n > 0) {
        BUG_ON(io->c != 32);

        reload_buffer(io);

        w |= (io->b & (((__u32) 1 << n) - 1)) << s;

        io->b >>= n;
        io->c += n;
    }

    return w;
}

static void finalize(generic_io_t *io, int mode)
{
    BUG_ON(io == NULL);

    if (mode == WRITE_MODE && io->c > 0)
        flush_buffer(io);
}

static void write_unary(generic_io_t *io, __u32 N)
{
    for (; N > 32; N -= 32)
        write_zero_bits(io, 32);

    write_zero_bits(io, N);

    put_nonzero_bit(io);
}

static __u32 read_unary(generic_io_t *io)
{
    __u32 total_zeros = 0;

    BUG_ON(io == NULL);

    do {
        if (io->c == 32)
            reload_buffer(io);

        /* Get trailing zeros */
        size_t s = MIN(32 - io->c, ctzu32(io->b));

        io->b >>= s;
        io->c += s;

        total_zeros += s;
    } while (io->c == 32);

    /* ...and drop non-zero bit */
    BUG_ON(io->c >= 32);

    io->b >>= 1;
    io->c++;

    return total_zeros;
}

/* Golomb-Rice, encode non-negative integer N, parameter M = 2^k */
static void write_golomb(generic_io_t *io, size_t k, __u32 N)
{
    BUG_ON(k >= 32);

    write_unary(io, N >> k);
    write_bits(io, N, k);
}

static __u32 read_golom(generic_io_t *io, size_t k)
{
    __u32 N = read_unary(io) << k;
    N |= read_bits(io, k);
    return N;
}

void x_init(void)
{
    opt_k = 3;
    symbol_sum = 0;
    symbol_count = 0;
    int p = 0;
    for (; p < 256; ++p) {
        int i = 0;
        for (; i < 256; ++i) {
            table[p].sorted[i] = i;
            table[p].freq[i] = 0;
            table[p].order[i] = i;
        }
    }
}

static void swap_symbols(struct context *ctx, __u8 c, __u8 d)
{
    BUG_ON(ctx == NULL);

    __u8 ic = ctx->order[c], id = ctx->order[d];

    BUG_ON(ctx->sorted[ic] != c);
    BUG_ON(ctx->sorted[id] != d);

    ctx->sorted[ic] = d;
    ctx->sorted[id] = c;

    ctx->order[c] = id;
    ctx->order[d] = ic;
}

static void increment_frequency(struct context *ctx, __u8 c)
{
    BUG_ON(ctx == NULL);

    __u8 ic = ctx->order[c];
    size_t freq_c = ++(ctx->freq[c]);

    __u8 *pd;
    for (pd = ctx->sorted + ic - 1; pd >= ctx->sorted; --pd) {
        if (freq_c <= ctx->freq[*pd])
            break;
    }

    __u8 d = *(pd + 1);
    if (c != d)
        swap_symbols(ctx, c, d);
}

/* Geometric probability mode.
 * See https://ipnpr.jpl.nasa.gov/progress_report/42-159/159E.pdf
 */
static void update_model(__u8 delta)
{
    if (symbol_count == RESET_INTERVAL) {
        int k;

        /* 2^k <= E{r[k]} + 0 */
        for (k = 1; (symbol_count << k) <= symbol_sum; ++k)
            ;

        opt_k = k - 1;

        symbol_count = 0;
        symbol_sum = 0;
    }

    symbol_sum += delta;
    symbol_count++;
}

void *x_compress(void *iptr, size_t isize, void *optr)
{
    generic_io_t io;
    __u8 *end = (__u8 *) iptr + isize;
    struct context *ctx = table + 0;

    initiate(&io, optr, NULL, WRITE_MODE);
    __u8 *iptrc = iptr;
    for (; iptrc < end; ++iptrc) {
        __u8 c = *iptrc;

        /* get index */
        __u8 d = ctx->order[c];

        write_golomb(&io, opt_k, (__u32) d);
        BUG_ON(c != ctx->sorted[d]);

        /* Update context model */
        increment_frequency(ctx, c);

        /* Update Golomb-Rice model */
        update_model(d);
        ctx = table + c;
    }

    /* EOF symbol */
    write_golomb(&io, opt_k, 256);

    finalize(&io, WRITE_MODE);

    return io.ptr;
}

void *x_decompress(void *iptr, size_t isize, void *optr)
{
    generic_io_t io;
    __u8 *end = (__u8 *) iptr + isize;
    struct context *ctx = table + 0;

    initiate(&io, iptr, end, READ_MODE);

    __u8 *optrc = optr;

    for (;; ++optrc) {
        __u32 d = read_golom(&io, opt_k);

        if (d >= 256)
            break;

        __u8 c = ctx->sorted[d];
        *optrc = c;

        /* Update context model */
        increment_frequency(ctx, c);

        /* Update Golomb-Rice model */
        update_model(d);
        ctx = table + c;
    }

    finalize(&io, READ_MODE);

    return optrc;
}

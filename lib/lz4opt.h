/*
    lz4opt.h - Optimal Mode of LZ4
    Copyright (C) 2015-2017, Przemyslaw Skibinski <inikep@gmail.com>
    Note : this file is intended to be included within lz4hc.c

    BSD 2-Clause License (http://www.opensource.org/licenses/bsd-license.php)

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are
    met:

    * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above
    copyright notice, this list of conditions and the following disclaimer
    in the documentation and/or other materials provided with the
    distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
    A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
    OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
    SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
    LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
    DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
    (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
    OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    You can contact the author at :
       - LZ4 source repository : https://github.com/lz4/lz4
       - LZ4 public forum : https://groups.google.com/forum/#!forum/lz4c
*/

#define LZ4_OPT_NUM   (1<<12)


typedef struct {
    int price;
    int off;
    int mlen;
    int litlen;
} LZ4HC_optimal_t;


/* price in bytes */
LZ4_FORCE_INLINE size_t LZ4HC_literalsPrice(size_t litlen)
{
    size_t price = litlen;
    if (litlen >= (size_t)RUN_MASK)
        price += 1 + (litlen-RUN_MASK)/255;
    return price;
}


/* requires mlen >= MINMATCH */
LZ4_FORCE_INLINE size_t LZ4HC_sequencePrice(size_t litlen, size_t mlen)
{
    size_t price = 2 + 1; /* 16-bit offset + token */

    price += LZ4HC_literalsPrice(litlen);

    if (mlen >= (size_t)(ML_MASK+MINMATCH))
        price+= 1 + (mlen-(ML_MASK+MINMATCH))/255;

    return price;
}



LZ4_FORCE_INLINE int LZ4HC_InsertAndGetFartherMatch (
    LZ4HC_CCtx_internal* hc4,
    const BYTE* const ip,
    const BYTE* const iLowLimit,
    const BYTE* const iHighLimit,
    U32* offset,
    const BYTE** startpos,
    const int maxNbAttempts)
{
    U16* const chainTable = hc4->chainTable;
    U32* const HashTable = hc4->hashTable;
    const BYTE* const base = hc4->base;
    const U32 dictLimit = hc4->dictLimit;
    const BYTE* const lowPrefixPtr = base + dictLimit;
    U32 const current = (U32)(ip - base);
    U32 const lowLimit = (hc4->lowLimit + 64 KB > current) ? hc4->lowLimit : current - MAX_DISTANCE;
    const BYTE* const dictBase = hc4->dictBase;
    int nbAttempts = maxNbAttempts;
    reg_t const pattern = LZ4_read_ARCH(ip);
    U32 matchIndex;
    repeat_state_e repeat = rep_untested;
    size_t srcPatternLength = 0;
    U32 farther = MINMATCH-1;
    int longest = farther;

    /* First Match */
    LZ4HC_Insert(hc4, ip);
    matchIndex = HashTable[LZ4HC_hashPtr(ip)];

    while ((matchIndex>=lowLimit) && (nbAttempts)) {
        nbAttempts--;
        if (matchIndex >= dictLimit) {
            const BYTE* const matchPtr = base + matchIndex;
            if (*(ip + farther) == *(matchPtr + farther)) {
                assert(ip+4 <= iHighLimit);
                if (LZ4_read32(matchPtr) == (U32)pattern) {
                    U32 const mlt = MINMATCH + LZ4_count(ip+MINMATCH, matchPtr+MINMATCH, iHighLimit);
                    if (mlt > farther) {
                        int back = 0;   /* value <= 0 */
                        while ( (ip+back > iLowLimit)
                             && (matchPtr+back > lowPrefixPtr)
                             && (ip[back-1] == matchPtr[back-1])) {
                                back--;
                        }
                        farther = mlt;
                        longest = mlt - back;
                        assert (current > matchIndex);
                        *offset = current - matchIndex;
                        *startpos = ip+back;
                }   }
            }
        } else {   /* matchIndex < dictLimit */
            /* =========== TO REWRITE ============= */
            const BYTE* const matchPtr = dictBase + matchIndex;
            if (LZ4_read32(matchPtr) == (U32)pattern) {
                int mlt;
                int back=0;
                const BYTE* vLimit = ip + (dictLimit - matchIndex);
                if (vLimit > iHighLimit) vLimit = iHighLimit;
                mlt = LZ4_count(ip+MINMATCH, matchPtr+MINMATCH, vLimit) + MINMATCH;
                if ((ip+mlt == vLimit) && (vLimit < iHighLimit))
                    mlt += LZ4_count(ip+mlt, base+dictLimit, iHighLimit);
                while ( (ip+back > iLowLimit)
                     && (matchIndex+back > lowLimit)
                     && (ip[back-1] == matchPtr[back-1]))
                        back--;
                mlt -= back;
                if (mlt > longest) {
                    longest = mlt;
                    assert (current > matchIndex);
                    *offset = current - matchIndex;
                    *startpos = ip + back;
        }   }   }

        {   U32 const nextOffset = DELTANEXTU16(chainTable, matchIndex);
            matchIndex -= nextOffset;
            if (1 && (nextOffset==1)) {
                /* may be a repeated pattern */
                if (repeat == rep_untested) {
                    if (LZ4_read32(ip+4) == (U32)pattern) {  /* should check ip limit */
                        repeat = rep_confirmed;
                        srcPatternLength = LZ4HC_countPattern(ip+8, iHighLimit, pattern) + 8;
                    } else {
                        repeat = rep_not;
                }   }
                if ( (repeat == rep_confirmed)   /* proven repeated pattern (1-2-4) */
                  && (matchIndex >= dictLimit) ) {   /* same segment only */
                    const BYTE* const matchPtr = base + matchIndex;
                    if (LZ4_read_ARCH(matchPtr) == pattern) {  /* good candidate */
                        size_t const forwardPatternLength = LZ4HC_countPattern(matchPtr+sizeof(pattern), iHighLimit, pattern) + sizeof(pattern);
                        const BYTE* const maxLowPtr = (lowPrefixPtr + MAX_DISTANCE >= ip) ? lowPrefixPtr : ip - MAX_DISTANCE;
                        size_t const backLength = LZ4HC_reverseCountPattern(matchPtr, maxLowPtr, (U32)pattern);
                        size_t const currentSegmentLength = backLength + forwardPatternLength;

                        if ( (currentSegmentLength >= srcPatternLength)   /* current pattern segment large enough to contain full srcPatternLength */
                          && (forwardPatternLength <= srcPatternLength) ) { /* haven't reached this position yet */
                            matchIndex += (U32)forwardPatternLength - (U32)srcPatternLength;  /* best position, full pattern, might be followed by more match */
                        } else {
                            matchIndex -= (U32)backLength;   /* let's go to farthest segment position, will find a match of length currentSegmentLength + maybe some back */
                        }
        }   }   }   }
    }  /* while ((matchIndex>=lowLimit) && (nbAttempts)) */

    return longest;
}


#define SET_PRICE(pos, ml, offset, ll, cost)           \
{                                                      \
    while (last_pos < pos)  { opt[last_pos+1].price = 1<<30; last_pos++; } \
    opt[pos].mlen = (int)ml;                           \
    opt[pos].off = (int)offset;                        \
    opt[pos].litlen = (int)ll;                         \
    opt[pos].price = (int)cost;                        \
    DEBUGLOG(7, "cur:%3u => cost:%3u", (U32)(pos), (U32)(cost)); \
}

static int LZ4HC_compress_optimal (
    LZ4HC_CCtx_internal* ctx,
    const char* const source,
    char* dest,
    int inputSize,
    int maxOutputSize,
    limitedOutput_directive limit,
    size_t sufficient_len)
{
    LZ4HC_optimal_t opt[LZ4_OPT_NUM + 2];   /* this uses a bit too much stack memory to my taste ... */

    const BYTE* ip = (const BYTE*) source;
    const BYTE* anchor = ip;
    const BYTE* const iend = ip + inputSize;
    const BYTE* const mflimit = iend - MFLIMIT;
    const BYTE* const matchlimit = (iend - LASTLITERALS);
    BYTE* op = (BYTE*) dest;
    BYTE* const oend = op + maxOutputSize;

    /* init */
    DEBUGLOG(5, "LZ4HC_compress_optimal");
    if (sufficient_len >= LZ4_OPT_NUM) sufficient_len = LZ4_OPT_NUM-1;
    ctx->end += inputSize;
    ip++;

    /* Main Loop */
    while (ip < mflimit) {
        size_t const llen = ip - anchor;
        size_t last_pos = 0;
        size_t cur, best_mlen, best_off;
        const BYTE* matchPos = NULL;

        size_t curML = LZ4HC_InsertAndFindBestMatch(ctx, ip, matchlimit, &matchPos, ctx->searchNum);
        if (curML < MINMATCH) { ip++; continue; }
        DEBUGLOG(6, "found initial match of length %u", (U32)curML);
        memset(opt, 0, sizeof(LZ4HC_optimal_t));  /* memset only the first position */

        if (curML >= sufficient_len) {
            /* good enough solution : immediate encoding */
            best_mlen = curML;
            best_off = ip - matchPos;
            cur = 0;
            last_pos = 1;
            goto encode;
        }

        /* set prices using matches at position = 0 */
        {   size_t const offset = (size_t)(ip - matchPos);
            size_t mlen;
            for (mlen = 0 ; mlen < MINMATCH ; mlen++) {
                size_t const cost = LZ4HC_literalsPrice(llen + mlen) - LZ4HC_literalsPrice(llen);
                SET_PRICE(mlen, 1 /*mlen*/, 0 /*off*/, mlen /*ll*/, cost);
            }
            assert(curML < LZ4_OPT_NUM);  /* curML < sufficient_len < LZ4_OPT_NUM */
            for ( ; mlen <= curML ; mlen++) {
                size_t const cost = LZ4HC_sequencePrice(llen, mlen) - LZ4HC_literalsPrice(llen);
                SET_PRICE(mlen, mlen, offset, 0, cost);   /* updates last_pos and opt[pos] */
            }
            /* complete beyond current match */
            opt[curML+1].mlen = 1;  /* literal */
            opt[curML+1].off = 0;
            opt[curML+1].litlen = 1;
            opt[curML+1].price = (int)(opt[curML].price + LZ4HC_literalsPrice(1));
            opt[curML+2].mlen = 1;  /* literal */
            opt[curML+2].off = 0;
            opt[curML+2].litlen = 2;
            opt[curML+2].price = (int)(opt[curML].price + LZ4HC_literalsPrice(2));
        }
        assert(last_pos >= MINMATCH);
        assert(opt[0].mlen == 1);
        assert(opt[1].mlen == 1);

        /* check further positions */
        for ( ; ; ) {
            const BYTE* curPtr = ip + last_pos - 2;
            if (curPtr >= mflimit) break;

            {   U32 offset = 0;
                size_t const longerML = LZ4HC_InsertAndGetFartherMatch(ctx,
                                            curPtr, (ip + last_pos - curML), matchlimit,
                                            &offset, &curPtr,
                                            ctx->searchNum);
                cur = curPtr - ip;

                if (longerML <= curML) break;  /* no better position */
                DEBUGLOG(6, "found better match of length %u, starting at pos %u",
                        (U32)longerML, (U32)cur);

                if ( (longerML > sufficient_len)
                  || (cur+longerML>=LZ4_OPT_NUM-1) ) {
                    /* immediate encoding */
                    best_mlen = longerML;
                    best_off = offset;
                    last_pos = cur + 1;
                    goto encode;
                }

                /* set prices from position = cur */
                {   size_t ml;
                    /* not necessary to write for positions < cur+MINMATCH, they were already completed with additional literals */
                    for (ml = MINMATCH ; ml <= longerML ; ml++) {
                        size_t ll, price;
                        if (opt[cur].mlen == 1) {
                            ll = opt[cur].litlen;
                            if (cur > ll)
                                price = opt[cur - ll].price + LZ4HC_sequencePrice(ll, ml);
                            else
                                price = LZ4HC_sequencePrice(llen + ll, ml) - LZ4HC_literalsPrice(llen);
                        } else {
                            ll = 0;
                            price = opt[cur].price + LZ4HC_sequencePrice(0, ml);
                        }
                        assert(cur+ml < LZ4_OPT_NUM);  /* otherwise, immediate encoding */
                        if (cur + ml > last_pos || price < (size_t)opt[cur + ml].price) {
                            SET_PRICE(cur + ml, ml, offset, ll, price); /* updates last_pos and opt[pos] */
                }   }   }
                curML = longerML;  /* next attempt, find larger */
            }  /* matchPtr, longerML */
            /* complete costs beyond current match */
            opt[last_pos+1].mlen = 1;  /* literal */
            opt[last_pos+1].off = 0;
            opt[last_pos+1].litlen = 1;
            opt[last_pos+1].price = (int)(opt[last_pos].price + LZ4HC_literalsPrice(1));
            opt[last_pos+2].mlen = 1;  /* literal */
            opt[last_pos+2].off = 0;
            opt[last_pos+2].litlen = 2;
            opt[last_pos+2].price = (int)(opt[last_pos].price + LZ4HC_literalsPrice(2));
        }  /* for (cur = 1; cur <= last_pos; cur++) */

        best_mlen = opt[last_pos].mlen;
        best_off = opt[last_pos].off;
        cur = last_pos - best_mlen;

encode: /* cur, last_pos, best_mlen, best_off must be set */
        opt[0].mlen = 1;
        DEBUGLOG(6, "sequence reverse traversal");
        while (1) {  /* from end to beginning */
            size_t const ml = opt[cur].mlen;
            int const offset = opt[cur].off;
            opt[cur].mlen = (int)best_mlen;
            opt[cur].off = (int)best_off;
            DEBUGLOG(6, "cur:%3u, ml:%3u", (U32)cur, (U32)best_mlen);
            best_mlen = ml;
            best_off = offset;
            if (ml > cur) break;
            cur -= ml;
        }

        /* encode all recorded sequences */
        cur = 0;
        while (cur < last_pos) {
            int const ml = opt[cur].mlen;
            int const offset = opt[cur].off;
            if (ml == 1) { ip++; cur++; continue; }
            DEBUGLOG(6, "sending sequence from cur:%3u / %3u", (U32)cur, (U32)last_pos);
            cur += ml;
            if ( LZ4HC_encodeSequence(&ip, &op, &anchor, ml, ip - offset, limit, oend) ) return 0;
        }
    }  /* while (ip < mflimit) */

    /* Encode Last Literals */
    {   int lastRun = (int)(iend - anchor);
        if ((limit) && (((char*)op - dest) + lastRun + 1 + ((lastRun+255-RUN_MASK)/255) > (U32)maxOutputSize)) return 0;  /* Check output limit */
        if (lastRun>=(int)RUN_MASK) { *op++=(RUN_MASK<<ML_BITS); lastRun-=RUN_MASK; for(; lastRun > 254 ; lastRun-=255) *op++ = 255; *op++ = (BYTE) lastRun; }
        else *op++ = (BYTE)(lastRun<<ML_BITS);
        memcpy(op, anchor, iend - anchor);
        op += iend-anchor;
    }

    /* End */
    return (int) ((char*)op-dest);
}

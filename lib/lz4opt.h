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



LZ4_FORCE_INLINE int LZ4HC_FindWidestMatch (
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
    int longest = MINMATCH-1;

    /* First Match */
    DEBUGLOG(6, "LZ4HC_FindWidestMatch: d:%u", (U32)(ip-iLowLimit));
    LZ4HC_Insert(hc4, ip);
    matchIndex = HashTable[LZ4HC_hashPtr(ip)];

    while ((matchIndex>=lowLimit) && (nbAttempts)) {
        nbAttempts--;
        if (matchIndex >= dictLimit) {
            const BYTE* const matchPtr = base + matchIndex;
            assert(ip+4 <= iHighLimit);
            if (LZ4_read32(matchPtr) == (U32)pattern) {
                int mlt = MINMATCH + LZ4_count(ip+MINMATCH, matchPtr+MINMATCH, iHighLimit);
                int back = 0;   /* value <= 0 */
                while ( (ip+back > iLowLimit)
                     && (matchPtr+back > lowPrefixPtr)
                     && (ip[back-1] == matchPtr[back-1])) {
                        back--;
                }
                mlt -= back;
                if (mlt > longest) {
                    longest = mlt;
                    assert (current > matchIndex);
                    *offset = current - matchIndex;
                    *startpos = ip+back;
                    DEBUGLOG(7, "candidate : ml=%i, offset=%u, back=%i",
                        mlt, *offset, -back);
            }   }
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


/* LZ4HC_addCandidate() :
 * set prices from position = cur */
static int LZ4HC_addCandidate(LZ4HC_optimal_t* opt, size_t* last_match_pos_ptr,
                            size_t const startpos, size_t const matchLength, size_t const offset)
{
    int matchUseful = 1;
    size_t const last_match_pos = *last_match_pos_ptr;
    size_t ml;

    /* update base cost to compare to : add literals */
    assert(startpos+matchLength < LZ4_OPT_NUM);  /* otherwise, immediate encoding */
    assert(startpos+1 <= last_match_pos);
    for (ml = last_match_pos - startpos + 1; ml <= matchLength; ml++) {
        U32 const pos = (U32)(startpos + ml);
        opt[pos].mlen = 1;  /* literal */
        opt[pos].off = 0;
        assert(pos >= 1);
        if (opt[pos-1].mlen >= MINMATCH) { /* follows a match */
            opt[pos].litlen = 1;
            opt[pos].price = (int)(opt[pos-1].price + LZ4HC_literalsPrice(1));
        } else {
            opt[pos].litlen = opt[pos-1].litlen + 1;
            opt[pos].price = (int)(opt[pos-1].price - LZ4HC_literalsPrice(opt[pos-1].litlen) + LZ4HC_literalsPrice(opt[pos].litlen));
    }   }
    assert(matchLength >= MINMATCH);
    for (ml = MINMATCH ; ml <= matchLength ; ml++) {
        U32 const pos = (U32)(startpos + ml);
        size_t ll, price;
        if (opt[startpos].mlen == 1) {
            ll = opt[startpos].litlen;
            if (startpos > ll)
                price = opt[startpos - ll].price + LZ4HC_sequencePrice(ll, ml);
            else  /* some literals before ip */
                price = LZ4HC_sequencePrice(ll, ml);
        } else {
            ll = 0;
            price = opt[startpos].price + LZ4HC_sequencePrice(0, ml);
        }
        DEBUGLOG(7, "pos:%u - candidate cost %u vs existing %u",
            (U32)(pos), (U32)price, (U32)opt[pos].price);
        if (ml == matchLength)
            matchUseful = (price < (size_t)opt[pos].price);
        if (price < (size_t)opt[pos].price) {
            opt[pos].mlen = (int)ml;
            opt[pos].off = (int)offset;
            opt[pos].litlen = (int)ll;
            opt[pos].price = (int)price;
            DEBUGLOG(7, "cur:%3u => cost:%3u (ml=%u)",
                        pos, (U32)price, (U32)ml);
    }   }
    if (matchUseful) *last_match_pos_ptr = startpos + matchLength;
    return matchUseful;
}  /* matchUseful, ml */


static int LZ4HC_compress_optimal (
    LZ4HC_CCtx_internal* ctx,
    const char* const source,
    char* dest,
    int inputSize,
    int maxOutputSize,
    limitedOutput_directive const limit,
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
    ip++;

    /* Main Loop */
    while (ip < mflimit) {
        size_t const llen = ip - anchor;
        size_t last_match_pos = 0;
        size_t cur, best_mlen, best_off;

        const BYTE* matchPos = NULL;
        size_t const firstML = LZ4HC_InsertAndFindBestMatch(ctx, ip, matchlimit, &matchPos, ctx->searchNum);
        if (firstML < MINMATCH) {
            DEBUGLOG(6, "pos: %u : no match found", (U32)(ip-(const BYTE*)source));
            ip++;
            continue;
        }
        DEBUGLOG(6, "pos: %u : found initial match of length %u",
                    (U32)(ip-(const BYTE*)source), (U32)firstML);

        if (firstML >= sufficient_len) {
            /* good enough solution : immediate encoding */
            if ( LZ4HC_encodeSequence(&ip, &op, &anchor, (int)firstML, matchPos, limit, oend) )   /* updates ip, op and anchor */
                return 0;  /* error */
            continue;
        }

        /* set prices using matches at position = 0 */
        {   size_t const offset = (size_t)(ip - matchPos);
            size_t mlen;
            for (mlen = 0 ; mlen < MINMATCH ; mlen++) {
                size_t const cost = LZ4HC_literalsPrice(llen + mlen);
                opt[mlen].mlen = 1;
                opt[mlen].off = 0;
                opt[mlen].litlen = (int)(llen + mlen);
                opt[mlen].price = (int)(cost);
                DEBUGLOG(7, "rPos:%3u => cost:%3u (litlen=%i)",
                            (U32)mlen, (U32)(cost), opt[mlen].litlen);
            }
            assert(firstML < LZ4_OPT_NUM);  /* firstML < sufficient_len < LZ4_OPT_NUM */
            for ( ; mlen <= firstML ; mlen++) {
                size_t const cost = LZ4HC_sequencePrice(llen, mlen);
                opt[mlen].mlen = (int)mlen;
                opt[mlen].off = (int)offset;
                opt[mlen].litlen = (int)llen;
                opt[mlen].price = (int)cost;
                DEBUGLOG(7, "rPos:%3u => cost:%3u (ml=%u)",
                            (U32)mlen, (U32)cost, (U32)mlen);
        }   }
        last_match_pos = firstML;

        /* check further positions */
        assert(last_match_pos >= MINMATCH);
        for ( ; ip + last_match_pos - 2 < mflimit; ) {
            const BYTE* curPtr = ip + last_match_pos - 2;
            U32 offset = 0;
            size_t const newML = LZ4HC_FindWidestMatch(ctx,
                                        curPtr, ip, matchlimit,
                                        &offset, &curPtr,
                                        ctx->searchNum);
            cur = curPtr - ip;

            if (newML < MINMATCH) break;  /* no match */
            DEBUGLOG(6, "found match of length %u, starting at pos %u",
                    (U32)newML, (U32)cur);

            if ( (newML > sufficient_len)
              || (cur+newML >= LZ4_OPT_NUM-1) ) {
                /* immediate encoding */
                best_mlen = newML;
                best_off = offset;
                last_match_pos = cur + 1;
                goto encode;
            }

            if (!LZ4HC_addCandidate(opt, &last_match_pos, cur, newML, offset))
                break;  /* this match wasn't useful, let's stop the serie */

        }  /* check further positions */

        best_mlen = opt[last_match_pos].mlen;
        best_off = opt[last_match_pos].off;
        cur = last_match_pos - best_mlen;

encode: /* cur, last_match_pos, best_mlen, best_off must be set */
        assert(cur < LZ4_OPT_NUM);
        assert(last_match_pos >= 1);  /* == 1 when only one candidate */
        assert(best_mlen >= MINMATCH);
        assert((best_off >= 1) && (best_off <=65535));
        opt[0].mlen = 1;
        DEBUGLOG(6, "sequence reverse traversal");
        {   int candidate_pos = (int)cur;
            int selected_matchLength = (int)best_mlen;
            int selected_offset = (int)best_off;
            while (1) {  /* from end to beginning */
                int const next_matchLength = opt[candidate_pos].mlen;
                int const next_offset = opt[candidate_pos].off;
                assert(next_matchLength > 0); /* note : can be 1, means literal */
                opt[candidate_pos].mlen = selected_matchLength;
                opt[candidate_pos].off = selected_offset;
                DEBUGLOG(6, "rPos:%3i, matchLength:%3i", candidate_pos, selected_matchLength);
                selected_matchLength = next_matchLength;
                selected_offset = next_offset;
                if (next_matchLength > candidate_pos) break; /* last match elected, first match to encode */
                candidate_pos -= next_matchLength;
        }   }

        /* encode all recorded sequences in order */
        {   size_t rPos = 0;  /* relative position (to ip) */
            while (rPos < last_match_pos) {
                int const ml = opt[rPos].mlen;
                int const offset = opt[rPos].off;
                if (ml == 1) { ip++; rPos++; continue; }  /* literal */
                DEBUGLOG(6, "encoding sequence at rPos:%3u / %3u",
                            (U32)rPos, (U32)last_match_pos);
                rPos += ml;
                if ( LZ4HC_encodeSequence(&ip, &op, &anchor, ml, ip - offset, limit, oend) )   /* updates ip, op and anchor */
                    return 0;  /* error */
        }   }
    }  /* while (ip < mflimit) */

    /* Encode Last Literals */
    {   int lastRun = (int)(iend - anchor);
        if ( (limit)  /* Check output limit */
          && (((char*)op - dest) + lastRun + 1 + ((lastRun+255-RUN_MASK)/255) > (U32)maxOutputSize))
            return 0;
        if (lastRun >= (int)RUN_MASK) {
            *op++ = (RUN_MASK<<ML_BITS);
            lastRun -= RUN_MASK;
            for(; lastRun > 254 ; lastRun-=255) *op++ = 255;
            *op++ = (BYTE) lastRun;
        } else *op++ = (BYTE)(lastRun<<ML_BITS);
        memcpy(op, anchor, iend - anchor);
        op += iend-anchor;
    }

    /* End */
    return (int) ((char*)op-dest);
}
